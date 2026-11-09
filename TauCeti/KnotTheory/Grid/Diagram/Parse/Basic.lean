/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.KnotTheory.Grid.Diagram.Basic
import TauCeti.KnotTheory.Grid.Diagram.Components

/-!
# Parsing grid diagrams

This file decodes box-drawing characters into edge data, pairs the endpoints in rows and columns,
alternates the markings along each link component, and reconstructs the two marking permutations.

## Main definitions

* `TauCeti.GridDiagram.parseDrawing`: parse a canonical box-drawing diagram, returning its size and
  grid diagram or `none`.
* `TauCeti.GridDiagram.parseGridDiagram`: a source-literal helper for `Repr` output, intended only
  for hardcoded diagrams of a specified size; it panics on invalid input or a size mismatch.
-/

public section

namespace TauCeti

namespace GridDiagram

private abbrev Point (height width : Nat) := Fin height × Fin width

private abbrev Pair (height width : Nat) := Point height width × Point height width

private structure BoxEdgePresence where
  up : Bool
  down : Bool
  left : Bool
  right : Bool
  deriving Inhabited

private def BoxEdgePresence.toChar : BoxEdgePresence → Char
  | ⟨false, false, false, false⟩ => ' '
  | ⟨false, false, false, true⟩ => '╶'
  | ⟨false, false, true, false⟩ => '╴'
  | ⟨false, false, true, true⟩ => '─'
  | ⟨false, true, false, false⟩ => '╷'
  | ⟨false, true, false, true⟩ => '┌'
  | ⟨false, true, true, false⟩ => '┐'
  | ⟨false, true, true, true⟩ => '┬'
  | ⟨true, false, false, false⟩ => '╵'
  | ⟨true, false, false, true⟩ => '└'
  | ⟨true, false, true, false⟩ => '┘'
  | ⟨true, false, true, true⟩ => '┴'
  | ⟨true, true, false, false⟩ => '│'
  | ⟨true, true, false, true⟩ => '├'
  | ⟨true, true, true, false⟩ => '┤'
  | ⟨true, true, true, true⟩ => '┼'

private def BoxEdgePresence.ofChar : Char → BoxEdgePresence
  | ' ' => ⟨false, false, false, false⟩
  | '╶' => ⟨false, false, false, true⟩
  | '╴' => ⟨false, false, true, false⟩
  | '─' => ⟨false, false, true, true⟩
  | '╷' => ⟨false, true, false, false⟩
  | '┌' => ⟨false, true, false, true⟩
  | '┐' => ⟨false, true, true, false⟩
  | '┬' => ⟨false, true, true, true⟩
  | '╵' => ⟨true, false, false, false⟩
  | '└' => ⟨true, false, false, true⟩
  | '┘' => ⟨true, false, true, false⟩
  | '┴' => ⟨true, false, true, true⟩
  | '│' => ⟨true, true, false, false⟩
  | '├' => ⟨true, true, false, true⟩
  | '┤' => ⟨true, true, true, false⟩
  | '┼' => ⟨true, true, true, true⟩
  | _ => default

private def verticalEnds {n m : Nat} (board : Vector (Vector BoxEdgePresence m) n) :
    Vector (Vector Bool m) n :=
  board.map fun row ↦ row.map fun edges ↦ edges.up ^^ edges.down

private def horizontalEnds {n m : Nat} (board : Vector (Vector BoxEdgePresence m) n) :
    Vector (Vector Bool m) n :=
  board.map fun row ↦ row.map fun edges ↦ edges.left ^^ edges.right

private def cornersFromEnds {width height : Nat} (horizontal vertical :
    Vector (Vector Bool width) height) :
    List (Point height width) :=
  (List.finRange height).flatMap fun row ↦
    (List.finRange width).filterMap fun col ↦
      if (horizontal.get row).get col && (vertical.get row).get col then some (row, col) else none

private def splitDrawingLines (source : String) : Option (List String) :=
  match source.toList with
  | '\n' :: rest =>
    let lines := (String.ofList rest).splitOn "\n"
    some <| if lines.getLast? == some "" then lines.dropLast else lines
  | _ => none

private def lineVector (line : String) (width : Nat) : Option (Vector Char width) := do
  let chars := line.toList
  if chars.length ≤ width then
    pure <| Vector.ofFn fun col ↦
      if hcol : col.val < chars.length then chars.get ⟨col.val, hcol⟩ else ' '
  else
    none

private def matrixOfLines (lines : List String) (width : Nat) :
    Option (Vector (Vector Char width) lines.length) :=
  Vector.ofFnM fun row ↦ lineVector (lines.get row) width

private def parseCharMatrix (source : String) :
    Option (Σ width height, Vector (Vector Char width) height) := do
  let lines := (← splitDrawingLines source).reverse
  let width := lines.foldl (fun width line ↦ max width line.length) 0
  let chars ← matrixOfLines lines width
  pure ⟨width, lines.length, chars⟩

private def isLabelChar (ch : Char) : Bool := ch == '○' || ch == '×'

private def decodeDrawingChar (ch : Char) : Option BoxEdgePresence :=
  if isLabelChar ch then
    some ⟨true, false, true, false⟩
  else
    let edges := BoxEdgePresence.ofChar ch
    if edges.toChar == ch then some edges else none

private def edgeBoardOfChars {width height : Nat}
    (chars : Vector (Vector Char width) height) :
    Option (Vector (Vector BoxEdgePresence width) height) :=
  Vector.ofFnM fun row ↦ Vector.ofFnM fun col ↦ decodeDrawingChar ((chars.get row).get col)

private def horizontalEdgesAtOverpasses {width height : Nat}
    (chars : Vector (Vector Char width) height)
    (board : Vector (Vector BoxEdgePresence width) height) :
    Vector (Vector BoxEdgePresence width) height :=
  Vector.ofFn fun row ↦ Vector.ofFn fun col ↦
    let edges := (board.get row).get col
    if (chars.get row).get col == '│' &&
        (if h : 0 < col.val then
          let prevCol : Fin width := ⟨col.val - 1, by omega⟩
          let prevChar := (chars.get row).get prevCol
          let prevEdges := (board.get row).get prevCol
          !isLabelChar prevChar && prevEdges.right
        else false) &&
        (if h : col.val + 1 < width then
          let nextCol : Fin width := ⟨col.val + 1, h⟩
          let nextChar := (chars.get row).get nextCol
          let nextEdges := (board.get row).get nextCol
          !isLabelChar nextChar && nextEdges.left
        else false) then
      { edges with left := true, right := true }
    else
      edges

private def edgeConnectionsMatch {width height : Nat}
    (chars : Vector (Vector Char width) height)
    (board : Vector (Vector BoxEdgePresence width) height) : Bool :=
  let board := horizontalEdgesAtOverpasses chars board
  (List.finRange height).all fun row ↦
    (List.finRange width).all fun col ↦
      let ch := (chars.get row).get col
      let edges := (board.get row).get col
      if isLabelChar ch then
        true
      else
        let left := col.val != 0 || !edges.left
        let right :=
          if h : col.val + 1 < width then
            let nextCol : Fin width := ⟨col.val + 1, h⟩
            let nextChar := (chars.get row).get nextCol
            let nextEdges := (board.get row).get nextCol
            isLabelChar nextChar || edges.right == nextEdges.left
          else
            !edges.right
        let down := row.val != 0 || !edges.down
        let up :=
          if h : row.val + 1 < height then
            let nextRow : Fin height := ⟨row.val + 1, h⟩
            let nextChar := (chars.get nextRow).get col
            let nextEdges := (board.get nextRow).get col
            isLabelChar nextChar || edges.up == nextEdges.down
          else
            !edges.up
        left && right && down && up

private def cornersInColumn {width height : Nat} (ends : Vector (Vector Bool width) height)
    (col : Fin width) : List (Point height width) :=
  (List.finRange height).filterMap fun row ↦
    if (ends.get row).get col then some (row, col) else none

private def cornersInRow {width height : Nat} (ends : Vector (Vector Bool width) height)
    (row : Fin height) : List (Point height width) :=
  (List.finRange width).filterMap fun col ↦
    if (ends.get row).get col then some (row, col) else none

private def pairCorners {height width : Nat} (corners : List (Point height width)) :
    Option (Option (Pair height width)) :=
  match corners with
  | [] => some none
  | [first, last] => some (some (first, last))
  | _ => none

private def columnPerfectMatching {width height : Nat}
    (ends : Vector (Vector Bool width) height) : Option (List (Pair height width)) := do
  let pairs ← (List.finRange width).mapM fun col ↦ pairCorners (cornersInColumn ends col)
  pure <| pairs.filterMap id

private def rowPerfectMatching {width height : Nat}
    (ends : Vector (Vector Bool width) height) : Option (List (Pair height width)) := do
  let pairs ← (List.finRange height).mapM fun row ↦ pairCorners (cornersInRow ends row)
  pure <| pairs.filterMap id

private structure PerfectMatchings (height width : Nat) where
  horizontal : List (Pair height width)
  vertical : List (Pair height width)
  rows : List (Fin height)
  cols : List (Fin width)
  size_eq : rows.length = cols.length

private def extractPerfectMatchings {width height : Nat}
    (horizontalEnds verticalEnds : Vector (Vector Bool width) height) :
    Option (PerfectMatchings height width) := do
  let horizontal ← rowPerfectMatching horizontalEnds
  let vertical ← columnPerfectMatching verticalEnds
  let rows := horizontal.map fun ((row, _), _) ↦ row
  let cols := vertical.map fun (_, (_, col)) ↦ col
  if h : rows.length = cols.length then
    pure ⟨horizontal, vertical, rows, cols, h⟩
  else
    none

private structure ColorTask (height width : Nat) where
  point : Point height width
  isO : Bool

private structure ColoredPoint (height width : Nat) where
  point : Point height width
  isO : Bool
  root : Point height width

private def mate? {height width : Nat} (pairs : List (Pair height width))
    (point : Point height width) : Option (Point height width) :=
  (pairs.find? fun (first, second) ↦ first == point || second == point).map
    fun (first, second) ↦ if first == point then second else first

private def colorComponent {height width : Nat} (horizontal vertical : List (Pair height width))
    (root : Point height width) : Nat → List (ColorTask height width) →
      List (ColoredPoint height width) → Option (List (ColoredPoint height width))
  | 0, [], colored => some colored
  | 0, _ :: _, _ => none
  | _ + 1, [], colored => some colored
  | fuel + 1, task :: rest, colored =>
    match colored.find? (fun point ↦ point.point == task.point) with
    | some old =>
      if old.root == root && old.isO == task.isO then
        colorComponent horizontal vertical root fuel rest colored
      else
        none
    | none =>
      match mate? horizontal task.point, mate? vertical task.point with
      | some horizontalMate, some verticalMate =>
        colorComponent horizontal vertical root fuel
          (⟨horizontalMate, !task.isO⟩ :: ⟨verticalMate, !task.isO⟩ :: rest)
          (⟨task.point, task.isO, root⟩ :: colored)
      | _, _ => none

private def deduceCornerColors {height width : Nat}
    (pairings : PerfectMatchings height width) (corners : List (Point height width)) :
    Option (List (ColoredPoint height width)) :=
  corners.foldlM (fun colored point ↦
    if colored.any (fun old ↦ old.point == point) then
      some colored
    else
      colorComponent pairings.horizontal pairings.vertical point (3 * corners.length + 1)
        [⟨point, true⟩] colored) []

private def labelsIn {width height : Nat} (chars : Vector (Vector Char width) height) :
    List (Point height width × Bool) :=
  (List.finRange height).flatMap fun row ↦
    (List.finRange width).filterMap fun col ↦
      let ch := (chars.get row).get col
      if ch == '○' then some ((row, col), true)
      else if ch == '×' then some ((row, col), false)
      else none

private def flipComponentsByLabels {height width : Nat}
    (colored : List (ColoredPoint height width)) (labels : List (Point height width × Bool)) :
    Option (List (ColoredPoint height width)) := do
  let roots := (colored.map ColoredPoint.root).eraseDups
  roots.foldlM (fun colored root ↦ do
    let members := colored.filter (fun point ↦ point.root == root)
    let points := members.map ColoredPoint.point
    let markers := labels.filter (fun (point, _) ↦ points.contains point)
    match markers with
    | [] => pure colored
    | [(point, wanted)] =>
      match members.find? (fun member ↦ member.point == point) with
      | some marker =>
        let flip := marker.isO != wanted
        pure <| colored.map fun member ↦
          if member.root == root && flip then { member with isO := !member.isO } else member
      | none => none
    | _ => none) colored

private structure IndexedPoint (size : Nat) where
  row : Fin size
  col : Fin size
  isO : Bool

private def indexColoredPoints {height width : Nat} (pairings : PerfectMatchings height width)
    (colored : List (ColoredPoint height width)) :
    Option (List (IndexedPoint pairings.rows.length)) :=
  colored.mapM fun point ↦ do
    let (pointRow, pointCol) := point.point
    let row ← pairings.rows.finIdxOf? pointRow
    let col ← pairings.cols.finIdxOf? pointCol
    pure ⟨row, Fin.cast pairings.size_eq.symm col, point.isO⟩

private def pointsOfColor {size : Nat} (points : List (IndexedPoint size)) (isO : Bool) :
    List (Point size size) :=
  points.filterMap fun point ↦
    if point.isO == isO then some (point.row, point.col) else none

private def permutationFromPoints {size : Nat} (points : List (Point size size)) :
    Option (Equiv.Perm (Fin size)) := do
  if points.length != size then none else do
    let rows ← Vector.ofFnM fun col ↦ do
      let point ← points.find? fun (_, pointCol) ↦ pointCol == col
      let (row, _) := point
      pure row
    let cols ← Vector.ofFnM fun row ↦ do
      let point ← points.find? fun (pointRow, _) ↦ pointRow == row
      let (_, col) := point
      pure col
    let f : Fin size → Fin size := rows.get
    let g : Fin size → Fin size := cols.get
    if h : (∀ col, g (f col) = col) ∧ (∀ row, f (g row) = row) then
      match h with
      | ⟨hgf, hfg⟩ => pure ⟨f, g, hgf, hfg⟩
    else
      none

private def makeGridDiagram {height width : Nat} (pairings : PerfectMatchings height width)
    (colored : List (ColoredPoint height width)) : Option (GridDiagram pairings.rows.length) := do
  let points ← indexColoredPoints pairings colored
  let o ← permutationFromPoints (pointsOfColor points true)
  let x ← permutationFromPoints (pointsOfColor points false)
  if hdis : ∀ col, o col ≠ x col then
    some ⟨⟨o⟩, ⟨x⟩, hdis⟩
  else
    none

private def reembedRow {width : Nat} (line : List Char) (cols : List (Fin width))
    (x : Fin width) : Char :=
  match line, cols with
  | center :: edge :: rest, col :: next :: cols =>
    if x == col then center
    else if col.val < x.val && x.val < next.val then edge
    else reembedRow rest (next :: cols) x
  | [center], [col] => if x == col then center else ' '
  | _, _ => ' '

private def reprMatchesDrawing {width height : Nat} (chars : Vector (Vector Char width) height)
    (pairings : PerfectMatchings height width) (G : GridDiagram pairings.rows.length) : Bool :=
  if pairings.rows = List.finRange height then
    let actual := chars.toList.map Vector.toList
    let lines := if G.reprString.isEmpty then [] else (G.reprString.splitOn "\n").reverse
    let rendered := lines.map fun line ↦
      List.ofFn fun x : Fin width ↦ reembedRow line.toList pairings.cols x
    actual == rendered
  else
    false

private def parseGrid {width height : Nat} (chars : Vector (Vector Char width) height) :
    Option (Σ n : ℕ, GridDiagram n) := do
  let board ← edgeBoardOfChars chars
  guard (edgeConnectionsMatch chars board)
  let horizontal := horizontalEnds board
  let vertical := verticalEnds board
  let corners := cornersFromEnds horizontal vertical
  guard (width == 0 || !corners.isEmpty)
  let pairings ← extractPerfectMatchings horizontal vertical
  let colored ← deduceCornerColors pairings corners
  let colored ← flipComponentsByLabels colored (labelsIn chars)
  let G ← makeGridDiagram pairings colored
  guard (reprMatchesDrawing chars pairings G)
  pure ⟨pairings.rows.length, G⟩

/-- Parse the canonical box-drawing representation of a grid diagram, returning its size and value
or `none` if the drawing is invalid. Each component's topmost-leftmost marking must be labeled `○`
or `×` to specify its coloring. -/
def parseDrawing (source : String) : Option (Σ n : ℕ, GridDiagram n) := do
  let source := if source.toList.head? == some '\n' then source else "\n" ++ source
  let ⟨_, _, chars⟩ ← parseCharMatrix source
  parseGrid chars

/-- Parse a canonical box-drawing grid diagram of size `n`, intended for hardcoded source strings
such as `Repr` output. Panics if the drawing is invalid or has a different size. Each component's
topmost-leftmost marking must be labeled `○` or `×` to specify its `O`/`X` coloring. -/
def parseGridDiagram (n : ℕ) (source : String) [Inhabited (GridDiagram n)] : GridDiagram n :=
  match parseDrawing source with
  | some ⟨m, G⟩ =>
    if h : m = n then
      h ▸ G
    else
      panic! s!"expected a grid diagram of size {n}"
  | none => panic! "invalid grid diagram"

end GridDiagram

end TauCeti
