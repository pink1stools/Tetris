/*
 * TETRIS
 * Copyright (C) 2008 Michael Birken
 * 
 * This file is part of TETRIS.
 *
 * TETRIS is free software; you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published 
 * by the Free Software Foundation; either version 3 of the License, or
 * (at your option) any later version.
 *
 * TETRIS is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with this program.  If not, see <http://www.gnu.org/licenses/>.
 * 
 */

using System;
using System.Collections.Generic;
using System.ComponentModel;
using System.Data;
using System.Drawing;
using System.Drawing.Drawing2D;
using System.Text;
using System.Windows.Forms;
using System.Diagnostics;
using System.Runtime.InteropServices;
using System.Threading;

namespace Tetris {
  public partial class TetrisForm : Form {
 
    [StructLayout(LayoutKind.Sequential)]
    public struct PeekMsg {
      public IntPtr hWnd;
      public Message msg;
      public IntPtr wParam;
      public IntPtr lParam;
      public uint time;
      public System.Drawing.Point p;
    }

    [System.Security.SuppressUnmanagedCodeSecurity]
    [DllImport("User32.dll", CharSet = CharSet.Auto)]
    public static extern bool PeekMessage(out PeekMsg msg, IntPtr hWnd,
             uint messageFilterMin, uint messageFilterMax, uint flags);

    private int[][,,] tetrominoes = new int[7][,,];
    private int[][] tetrominoeCenters = new int[7][];

    private const int BLOCK_I = 0;
    private const int BLOCK_J = 1;
    private const int BLOCK_L = 2;
    private const int BLOCK_O = 3;
    private const int BLOCK_S = 4;
    private const int BLOCK_T = 5;
    private const int BLOCK_Z = 6;
    private const int BLOCK_EMPTY = 7;

    private const int DARK = 0;
    private const int LIGHT = 1;

    private const int WIDTH = 240;
    private const int HEIGHT = 480;
    private const int FRAMES_PER_SECOND = 60;

    private Pen[,] pens = new Pen[7, 3];
    private Brush[] brushes = new Brush[7];
    private int[,] board = new int[20, 10];

    private long FREQUENCY = Stopwatch.Frequency;
    private long TICKS_PER_FRAME = Stopwatch.Frequency / FRAMES_PER_SECOND;
    private Bitmap bitmap;
    private Graphics g;
    private Graphics graphics;
    private Stopwatch stopwatch = new Stopwatch();
    private long nextFrameStart;
    private bool enterKeyPressed;
    private bool leftKeyPressed;
    private bool rightKeyPressed;
    private bool upKeyPressed;
    private bool downKeyPressed;
    private bool lastLeftKeyPressed;
    private bool lastRightKeyPressed;
    private double normalDropSpeed;
    private double fastDropSpeed;
    private double dropSpeed;
    private int lockDownDelay = 15;
    private int lockDownCounter;
    private int xLag;
    private Random random = new Random();
    private int pieceType, pieceRotation;
    private double pieceX, pieceY;
    private int keyDelay;
    private int sideMoveDelay = 6;
    private List<FlyingBlock> flyingBlocks = new List<FlyingBlock>();
    private bool showRotated;
    private Matrix tempMatrix = new Matrix();
    private PointF tempPoint = new PointF();
    private int linesRemaining;
    private Font linesFont;
    private Font[] completedFonts = new Font[4];
    private string[] completedStrings;
    private int[] completedXs = new int[4];
    private int completedY;
    private int completedRows;
    private Brush[] completedBrushes = new Brush[64];
    private int completedAngle;
    private Font[] levelCompleteFonts = new Font[30];
    private int[,] levelCompleteXY = new int[30, 2];
    private int levelCompleteIndex;
    private int levelCompleteDelay;
    private int stage = 0, subStage = 0;
    private string stageName;
    private PointF stageNameLocation;
    private int stageNameDelay;
    private Font gameOverFont;
    private PointF gameOverLocation;
    private int gameOverDelay;
    private bool showingMenu = true;
    private PointF titleLocation;
    private Font titleFont;
    private int titleColorIndex;

    private string[] menuStrings = { "LEFT and RIGHT to move.", "UP to rotate.", "DOWN to drop.", "Select level (UP/DOWN):", "1-1", "ENTER to start." };
    private PointF[] menuLocations = new PointF[6];
    private Font menuFont;

    public TetrisForm() {
      InitializeComponent();
      InitFrame();
    }

    private void TetrisForm_Load(object sender, EventArgs e) {

      Text = "TET\u042fIS";

      InitImage();
      InitColorTable();
      InitTetrominoes();
      InitFonts();
      InitBrushes();
      ShowMenu();             

      stopwatch.Start();
      nextFrameStart = stopwatch.ElapsedTicks;
      Application.Idle += OnApplicationIdle;
    }

    private void AdvanceLevel() {
      subStage++;
      if (subStage == 5) {
        subStage = 0;
        stage++;
      }
      if (stage == 20) {
        stage = 0;
        subStage = 0;
      }
      InitStage();
    }

    private void InitStage() {
      stageName = (stage + 1) + "-" + (subStage + 1);
      Text = "TET\u042fIS " + stageName;
      stageName = "Level " + stageName;
      SizeF size = g.MeasureString(stageName, levelCompleteFonts[0]);
      stageNameLocation.X = (240 - size.Width) / 2f;
      stageNameLocation.Y = (480 - size.Height) / 2f;
      stageNameDelay = 90;

      normalDropSpeed = (stage + 1) / 4.0;
      fastDropSpeed = Math.Max(16, normalDropSpeed);
      ClearBoard(subStage * 2);
      linesRemaining = 25;
      dropSpeed = normalDropSpeed;
    }

    private void OnApplicationIdle(object sender, EventArgs e) {
      PeekMsg msg;
      while (!PeekMessage(out msg, IntPtr.Zero, 0, 0, 0)) {
        do {
          UpdateModel();
          nextFrameStart += TICKS_PER_FRAME;
        } while (nextFrameStart < stopwatch.ElapsedTicks);
        RenderFrame();        
        long remainingTicks = nextFrameStart - stopwatch.ElapsedTicks;
        if (remainingTicks > 0) {
          Thread.Sleep((int)(1000 * remainingTicks / FREQUENCY));
        }
      }
    }

    private void InitBrushes() {
      double angle = 0, angleInc = Math.PI / 32.0, greenOffset = 2.0 * Math.PI / 3.0, blueOffset = 4.0 * Math.PI / 3.0;
      for (int i = 0; i < 64; i++, angle += angleInc) {
        double red = 0.5 + (Math.Sin(angle) / 2.0);
        double green = 0.5 + (Math.Sin(greenOffset + angle) / 2.0);
        double blue = 0.5 + (Math.Sin(blueOffset + angle) / 2.0);
        red = Math.Pow(red, 0.25);
        green = Math.Pow(green, 0.25);
        blue = Math.Pow(blue, 0.25);
        completedBrushes[i] = new SolidBrush(Color.FromArgb(255, (int)(255 * red), (int)(255 * green), (int)(255 * blue)));
      }
    }

    private void InitFonts() {
      linesFont = new Font(Font.FontFamily, 10, FontStyle.Bold);
      completedStrings = new string[] { "SINGLE!", "DOUBLE!!", "TRIPLE!!!", "TET\u042fIS!!!!" };
      for (int i = 0; i < 4; i++) {
        completedFonts[i] = new Font(Font.FontFamily, 20 + i * 2, FontStyle.Bold);
        completedXs[i] = (int)((240 - g.MeasureString(completedStrings[i], completedFonts[i]).Width) / 2);
      }
      double angle = 0, angleInc = 2.0 * Math.PI / 30.0;
      for (int i = 0; i < 30; i++, angle += angleInc) {
        levelCompleteFonts[i] = new Font(Font.FontFamily, (int)(25 + 5 * Math.Sin(angle)), FontStyle.Bold);
        SizeF size = g.MeasureString("GOAL!", levelCompleteFonts[i]);
        levelCompleteXY[i, 0] = (int)((240 - size.Width) / 2);
        levelCompleteXY[i, 1] = (int)((480 - size.Height) / 2);
      }
      gameOverFont = new Font(Font.FontFamily, 200, FontStyle.Bold);
      SizeF gameOverSize = g.MeasureString(":(", gameOverFont);
      gameOverLocation = new PointF((240 - gameOverSize.Width) / 2f, (480 - gameOverSize.Height) / 2f);
      titleFont = new Font(Font.FontFamily, 25, FontStyle.Bold);
      SizeF titleSize = g.MeasureString("TET\u042fIS", titleFont);
      titleLocation = new PointF((240 - titleSize.Width) / 2f, 50);

      menuFont = new Font(Font.FontFamily, 11, FontStyle.Bold);
      for (int i = 0, y = 150; i < 6; i++) {
        SizeF size = g.MeasureString(menuStrings[i], menuFont);        
        menuLocations[i] = new PointF((240 - size.Width) / 2f, y);
        y += (int)(size.Height + 5);
        if (i == 2 || i == 4) {
          y += 50;
        }
      }
    }

    private void RemoveCompleteRows() {
      int totalY = 0;
      completedRows = 0;
      for (int i = 19; i >= 0; i--) {
        bool foundEmpty = false;
        for (int j = 0; j < 10; j++) {
          if (board[i, j] == BLOCK_EMPTY) {
            foundEmpty = true;
            break;
          }
        }
        if (!foundEmpty) {
          if (linesRemaining > 0) {
            linesRemaining--;
          }
          completedRows++;
          totalY += i * 24;
          for (int j = 0; j < 10; j++) {
            flyingBlocks.Add(new FlyingBlock(j * 24, i * 24, (random.NextDouble() - 0.5) * 5, -10 - 2.0 * random.NextDouble(), board[i, j]));
          }
          for (int k = i; k > 0; k--) {
            for (int j = 0; j < 10; j++) {
              board[k, j] = board[k - 1, j];
            }
          }
          for (int j = 0; j < 10; j++) {
            board[0, j] = BLOCK_EMPTY;
          }
          i++;
        }
      }
      if (completedRows > 0) {
        completedY = totalY / completedRows - 12;
        completedRows--;   
      }
    }

    private void ShowMenu() {
      showingMenu = true;
      keyDelay = 0;
      CenterStageMenu();
    }

    private void CenterStageMenu() {
      menuStrings[4] = (stage + 1) + "-" + (subStage + 1);
      menuLocations[4].X = (240 - g.MeasureString(menuStrings[4], menuFont).Width) / 2f;
    }

    private void UpdateModel() {

      if (showingMenu) {
        titleColorIndex++;
        if (titleColorIndex == 64) {
          titleColorIndex = 0;
        }
        if (enterKeyPressed) {
          showingMenu = false;
          InitStage();
        }
        if (keyDelay == 0) {
          keyDelay = 6;
          if (upKeyPressed) {
            subStage++;
            if (subStage == 5) {
              subStage = 0;
              stage++;
            }
            if (stage == 20) {
              stage = subStage = 0;
            }
            CenterStageMenu();
          } else if (downKeyPressed) {
            subStage--;
            if (subStage == -1) {
              subStage = 4;
              stage--;
            }
            if (stage == -1) {
              stage = 19;
              subStage = 4;
            }
            CenterStageMenu();
          }
        } else {
          keyDelay--;
        }
        return;
      }

      showRotated = false;

      if (gameOverDelay > 0) {
        gameOverDelay--;
        if (gameOverDelay == 0) {
          ShowMenu();
        }
        return;
      }

      if (stageNameDelay > 0) {
        stageNameDelay--;
        if (stageNameDelay == 0) {
          IntroduceNextPiece();
        }
        return;
      }

      if (levelCompleteDelay > 0) {
        levelCompleteDelay--;
        levelCompleteIndex++;
        if (levelCompleteIndex == 30) {
          levelCompleteIndex = 0;
        }
        if (levelCompleteDelay == 0) {
          AdvanceLevel();
        }
        return;
      }

      if (flyingBlocks.Count > 0) {
        for (int i = flyingBlocks.Count - 1; i >= 0; i--) {
          FlyingBlock flyingBlock = flyingBlocks[i];
          flyingBlock.vy += 0.2;
          flyingBlock.x += flyingBlock.vx;
          flyingBlock.y += flyingBlock.vy;
          if (flyingBlock.x > 240 || flyingBlock.x < -24 || flyingBlock.y > 480) {
            flyingBlocks.RemoveAt(i);
          }
        }
        completedY -= 4;
        completedAngle++;
        if (completedAngle == 64) {
          completedAngle = 0;
        }
        if (flyingBlocks.Count == 0 && linesRemaining == 0) {
          levelCompleteDelay = 300;
          levelCompleteIndex = 0;
        }
        return;
      } 

      xLag = 0;
      if (downKeyPressed) {
        dropSpeed = fastDropSpeed;
      } else {
        dropSpeed = normalDropSpeed;
      }

      int px = (int)pieceX;
      int py = (int)pieceY;
      double nextY = pieceY + dropSpeed;
      int[, ,] ts = tetrominoes[pieceType];
      bool moveDown = true;
      for (int i = 0; i < 4; i++) {
        if (Occupied(px + ts[pieceRotation, i, 0], (int)Math.Ceiling(nextY + ts[pieceRotation, i, 1]))) {
          pieceY = py = (((int)(Math.Ceiling(nextY)) + 23) / 24 - 1) * 24;
          moveDown = false;
          if (lockDownCounter == 0) {
            if (pieceY < 0) {
              gameOverDelay = 300;
            } else {
              keyDelay = 0;
              for (int j = 0; j < 4; j++) {
                int x = (px + ts[pieceRotation, j, 0]) / 24;
                int y = (py + ts[pieceRotation, j, 1]) / 24;
                board[y, x] = pieceType;
              }
              RemoveCompleteRows();
              if (linesRemaining > 0) {
                IntroduceNextPiece();
              }
            }
            return;
          } else {
            lockDownCounter--;            
          }
          break;
        }
      }
      if (moveDown) {
        lockDownCounter = lockDownDelay;
        pieceY = nextY;
      } 

      if (keyDelay == 0) {        
        if (upKeyPressed) {
          keyDelay = 15;          
          int nextRotation = pieceRotation + 1;
          if (nextRotation >= 4) {
            nextRotation = 0;
          }
          showRotated = true;
          for (int i = 0; i < 4; i++) {
            if (Occupied(px + ts[nextRotation, i, 0], py + ts[nextRotation, i, 1])) {
              showRotated = false;
              break;
            }
          }
          if (!showRotated) {
            showRotated = true;
            int nextX = px - 24;
            for (int i = 0; i < 4; i++) {
              if (Occupied(nextX + ts[nextRotation, i, 0], py + ts[nextRotation, i, 1])) {
                showRotated = false;
                break;
              }
            }
            if (showRotated) {
              pieceX = px = nextX;
            } else {
              showRotated = true;
              nextX = px + 24;
              for (int i = 0; i < 4; i++) {
                if (Occupied(nextX + ts[nextRotation, i, 0], py + ts[nextRotation, i, 1])) {
                  showRotated = false;
                  break;
                }
              }
              if (showRotated) {
                pieceX = px = nextX;
              } else if (pieceType == BLOCK_I) {
                showRotated = true;
                nextX = px - 48;
                for (int i = 0; i < 4; i++) {
                  if (Occupied(nextX + ts[nextRotation, i, 0], py + ts[nextRotation, i, 1])) {
                    showRotated = false;
                    break;
                  }
                }
                if (showRotated) {
                  pieceX = px = nextX;
                } else {
                  showRotated = true;
                  nextX = px + 48;
                  for (int i = 0; i < 4; i++) {
                    if (Occupied(nextX + ts[nextRotation, i, 0], py + ts[nextRotation, i, 1])) {
                      showRotated = false;
                      break;
                    }
                  }
                  if (showRotated) {
                    pieceX = px = nextX;
                  }
                }
              }
            }
          }
          if (showRotated) {
            pieceRotation = nextRotation;
          }
        } else if (leftKeyPressed) {
          if (lastLeftKeyPressed && sideMoveDelay > 1) {
            if (sideMoveDelay == 6) {
              sideMoveDelay = 3;
            } else {
              sideMoveDelay--;
            }
          }
          keyDelay = sideMoveDelay;
          int nextX = px - 24;
          int nextXLag = 12;
          for (int i = 0; i < 4; i++) {
            if (Occupied(nextX + ts[pieceRotation, i, 0], py + ts[pieceRotation, i, 1])) {
              nextX = px;
              nextXLag = 0;
              break;
            }
          }
          pieceX = nextX;
          xLag = nextXLag;
        } else if (rightKeyPressed) {
          if (lastRightKeyPressed && sideMoveDelay > 1) {
            if (sideMoveDelay == 6) {
              sideMoveDelay = 3;
            } else {
              sideMoveDelay--;
            }
          }
          keyDelay = sideMoveDelay;
          int nextX = px + 24;
          int nextXLag = -12;
          for (int i = 0; i < 4; i++) {
            if (Occupied(nextX + ts[pieceRotation, i, 0], py + ts[pieceRotation, i, 1])) {
              nextX = px;
              nextXLag = 0;
              break;
            }
          }
          pieceX = nextX;
          xLag = nextXLag;
        }
      } else {
        keyDelay--;
      }

      lastLeftKeyPressed = leftKeyPressed;
      lastRightKeyPressed = rightKeyPressed;
    }

    private void DrawBlock(Graphics g, int blockType, int x, int y) {
      g.FillRectangle(brushes[blockType], x + 2, y + 2, 20, 20);
      g.DrawLine(pens[blockType, LIGHT], x, y, x, y + 23);
      g.DrawLine(pens[blockType, DARK], x + 23, y, x + 23, y + 23);
      g.DrawLine(pens[blockType, LIGHT], x + 1, y + 1, x + 1, y + 22);
      g.DrawLine(pens[blockType, DARK], x + 22, y + 1, x + 22, y + 22);
      g.DrawLine(pens[blockType, LIGHT], x + 1, y, x + 22, y);
      g.DrawLine(pens[blockType, LIGHT], x + 2, y + 1, x + 21, y + 1);
      g.DrawLine(pens[blockType, DARK], x + 1, y + 23, x + 22, y + 23);
      g.DrawLine(pens[blockType, DARK], x + 2, y + 22, x + 21, y + 22);
    }

    private void DrawDroppingPieces() {
      int px = (int)pieceX;
      int py = (int)pieceY;
      int[, ,] ts = tetrominoes[pieceType];
      Matrix originalMatrix = null;
      if (showRotated) {
        originalMatrix = g.Transform;
        tempMatrix.Reset();
        tempPoint.X = px + tetrominoeCenters[pieceType][0];
        tempPoint.Y = py + tetrominoeCenters[pieceType][1];
        tempMatrix.RotateAt(-45, tempPoint);
        g.Transform = tempMatrix;
      }
      for (int i = 0; i < 4; i++) {
        DrawBlock(g, pieceType, px + ts[pieceRotation, i, 0] + xLag, py + ts[pieceRotation, i, 1]);
      }
      if (originalMatrix != null) {
        g.Transform = originalMatrix;
      }
    }

    private void RenderFrame() {
      g.FillRectangle(Brushes.Black, 0, 0, WIDTH, HEIGHT);

      if (showingMenu) {

        g.DrawString("TET\u042fIS", titleFont, completedBrushes[titleColorIndex], titleLocation);
        for (int i = 0; i < 6; i++) {
          g.DrawString(menuStrings[i], menuFont, i == 4 ? Brushes.Yellow : Brushes.White, menuLocations[i]);
        }

      } else {

        // Draw static blocks
        for (int i = 0, y = 0; i < 20; i++, y += 24) {
          for (int j = 0, x = 0; j < 10; j++, x += 24) {
            int blockType = board[i, j];
            if (blockType != BLOCK_EMPTY) {
              DrawBlock(g, blockType, x, y);
            }
          }
        }

        if (gameOverDelay > 0) {
          DrawDroppingPieces();
          g.DrawString(":(", gameOverFont, Brushes.White, gameOverLocation);
        } else if (stageNameDelay > 0) {
          g.DrawString(stageName, levelCompleteFonts[0], Brushes.White, stageNameLocation);
        } else if (levelCompleteDelay > 0) {
          g.DrawString("GOAL!", levelCompleteFonts[levelCompleteIndex], Brushes.White,
              levelCompleteXY[levelCompleteIndex, 0], levelCompleteXY[levelCompleteIndex, 1]);
        } else if (flyingBlocks.Count > 0) {
          // Draw flying blocks
          foreach (FlyingBlock flyingBlock in flyingBlocks) {
            DrawBlock(g, flyingBlock.type, (int)flyingBlock.x, (int)flyingBlock.y);
          }
          g.DrawString(completedStrings[completedRows], completedFonts[completedRows],
              completedBrushes[completedAngle], completedXs[completedRows], completedY);
        } else {
          DrawDroppingPieces();
        }

        g.DrawString("Remaining: " + linesRemaining, linesFont, Brushes.White, 5, 5);
      }

      graphics.DrawImageUnscaled(bitmap, 0, 0);
    }

    private void InitFrame() {
      ClientSize = new Size(WIDTH, HEIGHT);
      StartPosition = System.Windows.Forms.FormStartPosition.CenterScreen;
      SetStyle(ControlStyles.UserPaint, true);
      SetStyle(ControlStyles.AllPaintingInWmPaint, true);
    }

    private void InitModel() {
    }

    private void InitImage() {
      graphics = CreateGraphics();
      bitmap = new Bitmap(WIDTH, HEIGHT, graphics);
      g = Graphics.FromImage(bitmap);
    }

    private void TetrisForm_KeyDown(object sender, KeyEventArgs e) {
      switch (e.KeyCode) {
        case Keys.Left:
          leftKeyPressed = true;
          break;
        case Keys.Right:
          rightKeyPressed = true;
          break;
        case Keys.Up:
          upKeyPressed = true;
          break;
        case Keys.Down:
          downKeyPressed = true;
          break;
        case Keys.Enter:
          enterKeyPressed = true;
          break;
      }
    }

    private void InitColorTable() {

      Color[] cols = { Color.Cyan, Color.Blue, Color.Orange, Color.Yellow, Color.LimeGreen, Color.Purple, Color.Red };

      for (int i = 0; i < 7; i++) {
        Color color = cols[i];
        brushes[i] = new SolidBrush(cols[i]);
        pens[i, DARK] = new Pen(Color.FromArgb(255,
            Math.Max(0, color.R - 64), Math.Max(0, color.G - 64), Math.Max(0, color.B - 64)));
        pens[i, LIGHT] = new Pen(Color.FromArgb(255,
            Math.Min(255, color.R + 64), Math.Min(255, color.G + 64), Math.Min(255, color.B + 64)));
      }
    }

    private bool Occupied(int x, int y) {
      return TestPoint(x, y) || TestPoint(x, y + 23) || TestPoint(x + 23, y) || TestPoint(x + 23, y + 23);
    }

    private bool TestPoint(int x, int y) {
      if (x < 0 || x >= 240 || y >= 480) {
        return true;
      }
      if (y < 0) {
        return false;
      }

      x /= 24;
      y /= 24;

      return board[y, x] != BLOCK_EMPTY;
    }

    private void InitTetrominoes() {
      tetrominoes[BLOCK_I] = new int[,,] { { { 2, 0 }, { 2, 1 }, { 2, 2 }, { 2, 3 } },
                                           { { 0, 2 }, { 1, 2 }, { 2, 2 }, { 3, 2 } },
                                           { { 1, 0 }, { 1, 1 }, { 1, 2 }, { 1, 3 } },
                                           { { 0, 1 }, { 1, 1 }, { 2, 1 }, { 3, 1 } } };
      tetrominoes[BLOCK_J] = new int[,,] { { { 1, 0 }, { 1, 1 }, { 1, 2 }, { 2, 0 } },
                                           { { 0, 1 }, { 1, 1 }, { 2, 1 }, { 2, 2 } },
                                           { { 1, 0 }, { 1, 1 }, { 1, 2 }, { 0, 2 } },
                                           { { 0, 1 }, { 1, 1 }, { 2, 1 }, { 0, 0 } } };
      tetrominoes[BLOCK_L] = new int[,,] { { { 1, 0 }, { 1, 1 }, { 1, 2 }, { 0, 0 } },
                                           { { 0, 1 }, { 1, 1 }, { 2, 1 }, { 2, 0 } },
                                           { { 1, 0 }, { 1, 1 }, { 1, 2 }, { 2, 2 } },
                                           { { 0, 1 }, { 1, 1 }, { 2, 1 }, { 0, 2 } } };
      tetrominoes[BLOCK_O] = new int[,,] { { { 0, 0 }, { 0, 1 }, { 1, 0 }, { 1, 1 } },
                                           { { 0, 0 }, { 0, 1 }, { 1, 0 }, { 1, 1 } },
                                           { { 0, 0 }, { 0, 1 }, { 1, 0 }, { 1, 1 } },
                                           { { 0, 0 }, { 0, 1 }, { 1, 0 }, { 1, 1 } } };
      tetrominoes[BLOCK_S] = new int[,,] { { { 1, 0 }, { 2, 0 }, { 0, 1 }, { 1, 1 } },
                                           { { 1, 0 }, { 1, 1 }, { 2, 1 }, { 2, 2 } }, 
                                           { { 1, 1 }, { 2, 1 }, { 0, 2 }, { 1, 2 } },
                                           { { 0, 0 }, { 0, 1 }, { 1, 1 }, { 1, 2 } } };
      tetrominoes[BLOCK_T] = new int[,,] { { { 0, 1 }, { 1, 1 }, { 2, 1 }, { 1, 2 } },
                                           { { 1, 0 }, { 1, 1 }, { 1, 2 }, { 0, 1 } },
                                           { { 0, 1 }, { 1, 1 }, { 2, 1 }, { 1, 0 } },
                                           { { 1, 0 }, { 1, 1 }, { 1, 2 }, { 2, 1 } } };
      tetrominoes[BLOCK_Z] = new int[,,] { { { 0, 1 }, { 1, 1 }, { 1, 2 }, { 2, 2 } },
                                           { { 1, 0 }, { 0, 1 }, { 1, 1 }, { 0, 2 } },
                                           { { 0, 0 }, { 1, 0 }, { 1, 1 }, { 2, 1 } },
                                           { { 2, 0 }, { 1, 1 }, { 2, 1 }, { 1, 2 } } };

      tetrominoeCenters[BLOCK_I] = new int[] { 48, 48 };
      tetrominoeCenters[BLOCK_J] = new int[] { 36, 36 };
      tetrominoeCenters[BLOCK_L] = new int[] { 36, 36 };
      tetrominoeCenters[BLOCK_O] = new int[] { 24, 24 };
      tetrominoeCenters[BLOCK_S] = new int[] { 36, 36 };
      tetrominoeCenters[BLOCK_T] = new int[] { 36, 36 };
      tetrominoeCenters[BLOCK_Z] = new int[] { 36, 36 };

      for (int block = 0; block < 7; block++) {
        for (int rotation = 3; rotation >= 0; rotation--) {
          for (int i = 0; i < 4; i++) {
            for (int j = 0; j < 2; j++) {
              tetrominoes[block][rotation, i, j] *= 24;
            }
          }
        }
      }
    }

    private void ClearBoard(int junk) {
      int junkRow = 20 - junk;
      for (int i = 0; i < 20; i++) {
        for (int j = 0; j < 10; j++) {
          board[i, j] = (i < junkRow) ? BLOCK_EMPTY : random.Next(8);
        }
        board[i, random.Next(10)] = BLOCK_EMPTY;
        board[i, random.Next(10)] = BLOCK_EMPTY;
      }
    }

    private void TetrisForm_KeyUp(object sender, KeyEventArgs e) {
      switch (e.KeyCode) {
        case Keys.Left:
          sideMoveDelay = 6;
          keyDelay = 0;
          leftKeyPressed = false;
          break;
        case Keys.Right:
          sideMoveDelay = 6;
          keyDelay = 0;
          rightKeyPressed = false;
          break;
        case Keys.Up:
          keyDelay = 0;
          upKeyPressed = false;
          break;
        case Keys.Down:
          keyDelay = 0;
          downKeyPressed = false;
          break;
        case Keys.Enter:
          enterKeyPressed = false;
          break;
      }
    }

    private void IntroduceNextPiece() {
      pieceType = random.Next(7);
      pieceRotation = 0;
      int maxX = 0, maxY = 0, minX = Int32.MaxValue, minY = Int32.MaxValue;
      int[, ,] ts = tetrominoes[pieceType];
      for (int i = 0; i < 4; i++) {
        minX = Math.Min(minX, ts[0, i, 0]);
        minY = Math.Min(minY, ts[0, i, 1]);
        maxX = Math.Max(maxX, ts[0, i, 0] + 24);
        maxY = Math.Max(maxY, ts[0, i, 1] + 24);
      }
      int dx = maxX - minX;
      int dy = maxY - minY;
      pieceY = -minY - dy;
      pieceX = Math.Round(Math.Round((240 - dx) / 48.0) * 24 - minX);
    }
  }

  class FlyingBlock {
    public double x;
    public double y;
    public double vx;
    public double vy;
    public int type;

    public FlyingBlock(double x, double y, double vx, double vy, int type) {
      this.x = x;
      this.y = y;
      this.vx = vx;
      this.vy = vy;
      this.type = type;
    }
  }
}

