import com.ibm.wala.classLoader.IMethod;
import com.ibm.wala.classLoader.Language;
import com.ibm.wala.ipa.callgraph.*;
import com.ibm.wala.ipa.callgraph.impl.AllApplicationEntrypoints;
import com.ibm.wala.ipa.callgraph.impl.Util;
import com.ibm.wala.ipa.callgraph.propagation.SSAPropagationCallGraphBuilder;
import com.ibm.wala.ipa.cha.ClassHierarchy;
import com.ibm.wala.ipa.cha.ClassHierarchyException;
import com.ibm.wala.ipa.cha.ClassHierarchyFactory;
import com.ibm.wala.shrikeCT.InvalidClassFileException;
import com.ibm.wala.types.ClassLoaderReference;
import com.ibm.wala.util.CancelException;
import com.ibm.wala.util.config.AnalysisScopeReader;


import java.io.*;
import java.util.*;
import java.util.stream.Collectors;
import java.util.stream.Stream;

public class TestSelection {

    //定义含有用例选择方法的接口
    private interface Selectable {
        Set<String> select(File change_info, TestSelection testSelection);
    }

    //允许传入的正确指令的集合，使用String而不是char方便以后扩展到多字符指令。
    private static Set<String> allowedCommands = Stream.of("c", "m").collect(Collectors.toSet());

    //定义指令和对应接口的映射Map.
    private static Map<String, Selectable> methodTable = new HashMap<>();

    //0-cfa算法生成的调用图
    private CallGraph cfaCg;
    private String project_name;

    /**
     * @discription 获取变更方法的签名和变更类的名字
     * */
    private static HashSet<String>[] getChangedMethodsAndClasses(File change_info){
        try {
            BufferedReader bufferedReader = new BufferedReader(new FileReader(change_info));
            String line = bufferedReader.readLine();
            HashSet<String> changed_methods = new HashSet<>();
            HashSet<String> changed_classes = new HashSet<>();
            while (line != null) {
                changed_methods.add(line.split(" ")[1]);
                changed_classes.add(line.split(" ")[0]);
                line = bufferedReader.readLine();
            }
            return new HashSet[]{changed_classes,changed_methods};
        } catch (IOException e) {
            e.printStackTrace();
        }
        return null;
    }


    /**
     * @param lines: 保存受影响的测试节点的信息：类名和方法签名
     * @param records: 记录调用链上的所有节点的方法签名，用来防止循环依赖导致的栈溢出
     * @discription 从某一节点开始，向上递归检测调用链，并将调用链上Test类的节点（受影响的测试节点）的信息：类名和方法签名保存下来。
     * */
    private static void selectTest(CGNode cgNode, CallGraph cg, Set<String> lines, Set<String> records){
        for(Iterator<CGNode> iterator = cg.getPredNodes(cgNode);iterator.hasNext();){
            CGNode curNode = iterator.next();
            IMethod curMethod = curNode.getMethod();
            //碰到此前到达过的节点，则重新选择一条路径继续
            if(records.contains(curMethod.getSignature())){
                continue;
            }
            String className = curMethod.toString().split(",")[1].substring(1);
            if(className.contains("Test")){
                lines.add(String.format("%s %s",className,curMethod.getSignature()));
            }
            records.add(curMethod.getSignature());  //递归前保存当前节点的信息
            selectTest(curNode,cg,lines,records);
            records.remove(curMethod.getSignature()); //回退后将它从记录中删除
        }
    }

    //构建指令和对应接口的映射关系，实现相应的测试用例选择方法。
    static {
        methodTable.put("m", new Selectable() {
            @Override
            public Set<String> select(File change_info, TestSelection testSelection) {
                Set<String> changed_methods = Objects.requireNonNull(getChangedMethodsAndClasses(change_info))[1];
                try {
                    BufferedWriter bufferedWriter=new BufferedWriter(new FileWriter("selection-method.txt"));
                    Set<String> selected_methods=new HashSet<>();
                    for(CGNode cgNode:testSelection.cfaCg){
                        IMethod method = cgNode.getMethod();
                        if(changed_methods.contains(method.getSignature())){
                            selectTest(cgNode, testSelection.cfaCg, selected_methods, new HashSet<>());
                        }
                    }
                    for(String line:selected_methods){
                        bufferedWriter.write(line+"\n");
                    }
                    bufferedWriter.flush();
                    bufferedWriter.close();
                    return selected_methods;
                } catch (IOException e) {
                    e.printStackTrace();
                }
                return null;
            }
        });
        methodTable.put("c", new Selectable() {
            @Override
            public Set<String> select(File change_info, TestSelection testSelection) {
                Set<String> changed_classes = Objects.requireNonNull(getChangedMethodsAndClasses(change_info))[0];
                try {
                    BufferedWriter bufferedWriter=new BufferedWriter(new FileWriter("selection-class.txt"));
                    Set<String> selected_methods=new HashSet<>();
                    for(CGNode cgNode:testSelection.cfaCg){
                        String classname=cgNode.getMethod().toString().split(",")[1].substring(1);
                        if(changed_classes.contains(classname)){
                            selectTest(cgNode,testSelection.cfaCg,selected_methods, new HashSet<>());
                        }
                    }
                    for(String line:selected_methods){
                        bufferedWriter.write(line+"\n");
                    }
                    bufferedWriter.flush();
                    bufferedWriter.close();
                    return selected_methods;
                } catch (IOException e) {
                    e.printStackTrace();
                }
                return null;
            }
        });
    }

    /**
     * @discription 递归的将项目目录dir下所有.class文件加入到分析域scope中
     * */
    private static void makeScope(AnalysisScope scope, File dir) throws InvalidClassFileException {
        for (File file : Objects.requireNonNull(dir.listFiles())) {
            if (file.isDirectory()) {
                makeScope(scope, file);
            } else {
                if (file.getName().endsWith(".class")) {
                    scope.addClassFileToScope(ClassLoaderReference.Application, file);
                }
            }
        }
    }



    /**
     * @param project_target: 根据目标目录确定测试用例选择的范围：该目录下所有.class文件
     * @discription 构造函数，构建分析域，生成类层次，确定进入点，使用0-CFA算法构建调用图
     * */
    public TestSelection(File project_target) throws IOException, InvalidClassFileException, CancelException, ClassHierarchyException {
        AnalysisScope scope = AnalysisScopeReader.readJavaScope("scope.txt", new File("exclusion.txt"),
                TestSelection.class.getClassLoader());
        makeScope(scope, project_target);
        ClassHierarchy ch = ClassHierarchyFactory.makeWithRoot(scope);
        AllApplicationEntrypoints entrypoints = new AllApplicationEntrypoints(scope, ch);
        AnalysisOptions option = new AnalysisOptions(scope, entrypoints);
        SSAPropagationCallGraphBuilder builder = Util.makeZeroCFABuilder(
                Language.JAVA, option, new AnalysisCacheImpl(), ch, scope
        );
        cfaCg = builder.makeCallGraph(option);
        project_name = project_target.getName().substring(2);
    }

    /**
     * @discription 程序执行的入口，先对输入指令的有效性进行检测，再执行测试用例的选择
     * */
    public static void main(String args[]) {
        String command = args[0].substring(1);
        //检查指令是否有误
        if (!args[0].startsWith("-") && !allowedCommands.contains(command)) {
            System.err.println("Wrong command!");
            return;
        }
        String arg2 = args[1];
        //项目路径后面的\应该去掉（Windows系统中）
        if (arg2.endsWith("\\")) {
            arg2 = arg2.substring(0, arg2.length() - 1);
        }
        File project_target = new File(arg2);
        if (!project_target.isDirectory()) {
            System.err.println("Wrong project_target!");
            return;
        }
        File change_info = new File(args[2]);
        if (!change_info.exists()) {
            System.err.println("change_info file not exists!");
            return;
        }

        TestSelection testSelection = null;
        try {
            testSelection = new TestSelection(project_target);
        } catch (IOException | InvalidClassFileException | CancelException | ClassHierarchyException e) {
            e.printStackTrace();
            return;
        }
        testSelection.cropCallGraph();
        //testSelection.createClassandMethodDot();
        testSelection.select(command, change_info);
    }

    /**
     * @discription 调用图的裁剪,将java原生方法和测试类的init<>方法从调用图中去掉
     * */
    public void cropCallGraph() {
        for (Iterator<CGNode> iterator = cfaCg.iterator(); iterator.hasNext(); ) {
            CGNode cgNode = iterator.next();
            String descriptor = cgNode.toString();
            if (descriptor.contains("Primordial") || (descriptor.contains("Test") && descriptor.contains("<init>()V"))) {
                for (CGNode i : cfaCg) {
                    if (cfaCg.hasEdge(cgNode, i)) {
                        cfaCg.removeEdge(cgNode, i);
                    }
                    if (cfaCg.hasEdge(i, cgNode)) {
                        cfaCg.removeEdge(i, cgNode);
                    }
                }
                iterator.remove();
            }
        }
    }


    /**
     * @discription 在方法层次和类层次分别生成dot文件
     * */
    public void createClassandMethodDot() {
        try {
            BufferedWriter bufferedWriter = new BufferedWriter(new FileWriter("method-" + project_name + ".dot"));
            bufferedWriter.write("digraph method {\r\n");

            //不同的方法依赖可能得到同一个类依赖，用集合来避免将重复的类依赖记录下来，最后根据集合里的内容再统一将所有类之间的依赖写进dot文件中
            Set<String> classDotLines = new HashSet<>();

            for (CGNode cgNode : cfaCg) {
                for (Iterator<CGNode> iterator = cfaCg.getPredNodes(cgNode); iterator.hasNext(); ) {
                    CGNode curNode = iterator.next();
                    IMethod method = cgNode.getMethod();
                    IMethod curMethod = curNode.getMethod();
                    bufferedWriter.write(String.format("\t\"%s\" -> \"%s\";\r\n", method.getSignature(), curMethod.getSignature()));
                    classDotLines.add(String.format("\t\"%s\" -> \"%s\";\r\n",
                            (method.toString().split(",")[1]).substring(1),
                            (curMethod.toString().split(",")[1]).substring(1)
                            )
                    );
                }
                bufferedWriter.flush();
            }
            bufferedWriter.write("}\r\n");
            bufferedWriter.flush();
            bufferedWriter.close();

            bufferedWriter = new BufferedWriter(new FileWriter("class-" + project_name + ".dot"));
            bufferedWriter.write("digraph class {\r\n");
            for (String line : classDotLines) {
                bufferedWriter.write(line);
            }
            bufferedWriter.write("}\r\n");
            bufferedWriter.flush();
            bufferedWriter.close();
        } catch (IOException e) {
            e.printStackTrace();
        }
    }

    /**
     * @discription 执行测试用例的选择
     * */
    public void select(String command, File change_info) {
        TestSelection.methodTable.get(command).select(change_info, this);
    }

}
