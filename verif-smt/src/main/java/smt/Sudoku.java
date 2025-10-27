package smt;

import com.microsoft.z3.*;
import java.io.File;
import java.io.FileWriter;
import java.io.IOException;
import java.io.PrintWriter;
import java.util.Scanner;

public class Sudoku {

    public static void main(String[] args) {
        String inPath = args[0];
        String outPath = args[1];

        try (Context ctx = new Context()) {
            Solver solver = ctx.mkSolver();

            // get input text numbers in an array
            int[][] inputGrid = new int[9][9];
            File inputFile  = new File(inPath);
            try (Scanner scanner = new Scanner(inputFile)) {
                for (int i = 0; i < 9; i++) {
                    for (int j = 0; j < 9; j++) {
                        if (scanner.hasNextInt()) {
                            inputGrid[i][j] = scanner.nextInt();
                        } else {
                            throw new RuntimeException("Something is wrong with the input file");
                        }
                    }
                }
            } catch (IOException e) {
                System.err.println("Error reading the input file");
                return;
            }

            // create grid d_i_j
            IntExpr[][] d = new IntExpr[9][9];
            for (int i = 0; i < 9; i++) {
                for (int j = 0; j < 9; j++) {
                    d[i][j] = ctx.mkIntConst("d_" + i + "_" + j);
                }
            }

            // add input grid digits into grid d
            for (int i = 0; i < 9; i++) {
                for (int j = 0; j < 9; j++) {
                    // d_i_j must be (1 <= i <= 9, 1 <= j <= 9)
                    BoolExpr greaterEqualOne = ctx.mkGe(d[i][j], ctx.mkInt(1));
                    BoolExpr lesserEqualNine = ctx.mkLe(d[i][j], ctx.mkInt(9));
                    solver.add(ctx.mkAnd(greaterEqualOne, lesserEqualNine));

                    // fill the grid d if k != 0, else leave it blank
                    int k = inputGrid[i][j];
                    if (k != 0) {
                        solver.add(ctx.mkEq(d[i][j], ctx.mkInt(k)));
                    }
                }
            }

            // each row must contain each of the digits 1-9 exactly once
            for (int i = 0; i < 9; i++) {
                solver.add(ctx.mkDistinct(d[i])); // make sure each digit is distinct
            }

            // each column must contain each of the digits 1-9 exactly once
            for (int j = 0; j < 9; j++) {
                IntExpr[] columnDigits = new IntExpr[9]; // store column digits
                for (int i = 0; i < 9; i++) {
                    columnDigits[i] = d[i][j];
                }
                solver.add(ctx.mkDistinct(columnDigits)); // make sure each digit is distinct
            }

            // each of the nine 3x3 blocks must contain each of the digits 1-9 exactly once
            // separate into blocks of 3x3
            for (int i = 0; i < 9; i += 3) {
                for (int j = 0; j < 9; j += 3) {
                    IntExpr[] block = new IntExpr[9]; // store block digits
                    int k = 0;
                    // for each block get the 9 digits
                    for (int bi = i; bi < i + 3; bi++) {
                        for (int bj = j; bj < j + 3; bj++) {
                            block[k] = d[bi][bj];
                            k++;
                        }
                    }
                    solver.add(ctx.mkDistinct(block));
                }
            }

            // use the solver
            Status result = solver.check();

            try (PrintWriter writer = new PrintWriter(new FileWriter(outPath))) {
                if (result == Status.SATISFIABLE) {
                    Model model = solver.getModel();
                    for (int i = 0; i < 9; i++) {
                        for (int j = 0; j < 9; j++) {
                            Expr val = model.eval(d[i][j], false);
                            writer.print(val);

                            if (j < 8) {
                                writer.print(" ");
                            }
                        }
                        writer.println();
                    }
                } else {
                    writer.print("No Solution");
                }
            } catch (IOException e) {
                System.err.println("Error writing to output file");
            }

        } catch (Exception e) {
            System.err.println("An error occurred with the solver");
        }
    }
}