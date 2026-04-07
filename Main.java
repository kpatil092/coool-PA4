import soot.*;
import soot.options.Options;;

public class Main {
    public static void main(String[] args) {
        // Set up arguments for Soot
        String classPath = "./testcases/" + args[0];
        Options.v().set_keep_line_number(true);
        SceneTransformer pass = new AnalysisTransformer();
        PackManager.v().getPack("wjtp").add(new Transform("wjtp.dfa", pass));

        String[] sootArgs = {
                "-cp", classPath,
                "-pp",
                "-w",
                "-app",
                "-allow-phantom-refs",
                "-no-bodies-for-excluded",
                "-exclude", "java.*",
                "-exclude", "javax.*",
                "-exclude", "sun.*",
                "-exclude", "com.sun.*",
                "-exclude", "jdk.*",
                "-f", "J",
                "-t", "1",

                //  Call graph
                "-p", "cg.spark", "on",
                "-p", "cg.spark", "on-fly-cg:true",
                "-p", "cg.spark", "verbose:true",

                "-main-class", "Test",
                "-process-dir", classPath,
        };

        // Call Soot's main method with arguments
        soot.Main.main(sootArgs);
    }
}
