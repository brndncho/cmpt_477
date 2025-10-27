package sat;

import com.microsoft.z3.*;
import java.io.*;
import java.util.*;

public class GraphColoring {

    // edge struct
    static class Edge {
        int v, w;
        Edge(int v, int w){
            this.v = v;
            this.w = w;
        }
    }

    public static void main(String[] args) throws IOException {
        String inPath = args[0];
        String outPath = args[1];

        BufferedReader reader = new BufferedReader(new FileReader(inPath));

        // get N and M
        String[] firstLine;
        firstLine = reader.readLine().trim().split("\\s+");
        int N = Integer.parseInt(firstLine[0]);
        int M = Integer.parseInt(firstLine[1]);

        // get edges
        List<Edge> edges = new ArrayList<>();
        String line;
        while ((line = reader.readLine()) != null) {
            String[] parts = line.trim().split("\\s+");
            if (parts.length == 2) {
                int v = Integer.parseInt(parts[0]);
                int w = Integer.parseInt(parts[1]);
                edges.add(new Edge(v, w));
            }
        }

        reader.close();

        Context ctx = new Context();
        Solver solver = ctx.mkSolver();

        // boolean variable
        BoolExpr[][] p = new BoolExpr[N + 1][M + 1];
        for (int v = 1; v <= N; v++) {
            for (int c = 1; c <= M; c++) {
                p[v][c] = ctx.mkBoolConst("p" + v + "_" + c);
            }
        }

        // asserting every vertex is coloured
        for (int v = 1; v <= N; v++) {
            BoolExpr[] colorChoices = new BoolExpr[M];
            System.arraycopy(p[v], 1, colorChoices, 0, M);
            solver.add(ctx.mkOr(colorChoices));

            // asserting every vertex has at most one colour
            for (int c1 = 1; c1 <= M; c1++) {
                for (int c2 = c1 + 1; c2 <= M; c2++) {
                    solver.add(ctx.mkNot(ctx.mkAnd(p[v][c1], p[v][c2])));
                }
            }
        }

        // asserting that no two connected vertices have the same color
        for (Edge e : edges) {
            for (int c = 1; c <= M; c++) {
                BoolExpr p_v_c = p[e.v][c];
                BoolExpr p_w_c = p[e.w][c];
                solver.add(ctx.mkNot(ctx.mkAnd(p_v_c, p_w_c)));
            }
        }

        // use the solver
        BufferedWriter writer = new BufferedWriter(new FileWriter(outPath));
        Status result = solver.check();

        if (result == Status.SATISFIABLE) {
            Model model = solver.getModel();
            for (int v = 1; v <= N; v++) {
                for (int c = 1; c <= M; c++) {
                    Expr val = model.getConstInterp(p[v][c]);
                    if (val != null && val.isTrue()) {
                        writer.write(v + " " + c + "\n");
                        break;
                    }
                }
            }
        } else {
            writer.write("No Solution\n");
        }
        writer.close();
        ctx.close();
    }

}