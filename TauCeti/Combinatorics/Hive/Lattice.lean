/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Data.Fin.Tuple.NatAntidiagonal
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# The triangular lattice and its unit rhombi

The vertices of the size-`n` triangle are nonnegative barycentric triples of sum `n`.
`Vertex.rotate` and `Vertex.reflect` give its dihedral symmetries. The planar embedding
sends `(x,y,z)` to `(z + y/2, √3*y/2)`, so the corners `(n,0,0)`, `(0,n,0)`,
`(0,0,n)` occur clockwise.

`IsRhombus a b c d` records a unit rhombus in perimeter order, with **obtuse** corners
`a,c`. Its short diagonal has barycentric squared length 2 and its long diagonal has
squared length 6; the planar squared lengths are respectively 1 and 3. This ordering
is intended for the hive inequality `h b + h d ≤ h a + h c`.

The convention follows Knutson–Tao, *The honeycomb model of GLₙ(ℂ) tensor products I*,
Appendix 2. This file contains only lattice geometry, not hive inequalities.
-/

public section

namespace TauCeti.Hive

/-- A nonnegative barycentric lattice point in the triangle of side length `n`. -/
@[ext]
structure Vertex (n : ℕ) where
  /-- The coordinate at the first corner. -/
  x : ℕ
  /-- The coordinate at the second corner. -/
  y : ℕ
  /-- The coordinate at the third corner. -/
  z : ℕ
  /-- The barycentric coordinates have the prescribed sum. -/
  sum_eq : x + y + z = n
  deriving DecidableEq

namespace Vertex

variable {n : ℕ}

instance : Finite (Vertex n) := by
  let f (p : Vertex n) : ↥(Finset.Nat.antidiagonalTuple 3 n) :=
    ⟨![p.x, p.y, p.z], by
      rw [Finset.Nat.mem_antidiagonalTuple]
      simpa [Fin.sum_univ_succ, add_assoc] using p.sum_eq⟩
  apply Finite.of_injective f
  intro p q h
  have hc := congrArg Subtype.val h
  exact Vertex.ext (congrFun hc 0) (congrFun hc 1) (congrFun hc 2)

noncomputable instance : Fintype (Vertex n) := Fintype.ofFinite _

/-- The corner `A = (n,0,0)`. The other two corners are its rotations. -/
def cornerA (n : ℕ) : Vertex n := ⟨n, 0, 0, by omega⟩

@[simp] theorem cornerA_x (n : ℕ) : (cornerA n).x = n := (rfl)
@[simp] theorem cornerA_y (n : ℕ) : (cornerA n).y = 0 := (rfl)
@[simp] theorem cornerA_z (n : ℕ) : (cornerA n).z = 0 := (rfl)

/-- Clockwise rotation by one third of a turn: `(x,y,z) ↦ (z,x,y)`. -/
def rotate (p : Vertex n) : Vertex n := ⟨p.z, p.x, p.y, by have := p.sum_eq; omega⟩

/-- Reflection fixing `A` and interchanging the other two corners. -/
def reflect (p : Vertex n) : Vertex n := ⟨p.x, p.z, p.y, by have := p.sum_eq; omega⟩

@[simp] theorem rotate_x (p : Vertex n) : p.rotate.x = p.z := (rfl)
@[simp] theorem rotate_y (p : Vertex n) : p.rotate.y = p.x := (rfl)
@[simp] theorem rotate_z (p : Vertex n) : p.rotate.z = p.y := (rfl)
@[simp] theorem reflect_x (p : Vertex n) : p.reflect.x = p.x := (rfl)
@[simp] theorem reflect_y (p : Vertex n) : p.reflect.y = p.z := (rfl)
@[simp] theorem reflect_z (p : Vertex n) : p.reflect.z = p.y := (rfl)

/-- Three clockwise rotations return to the original vertex. -/
@[simp] theorem rotate_rotate_rotate (p : Vertex n) : p.rotate.rotate.rotate = p := by
  ext <;> rfl

/-- Reflection is an involution. -/
@[simp] theorem reflect_reflect (p : Vertex n) : p.reflect.reflect = p := by
  ext <;> rfl

/-- Reflection conjugates clockwise rotation to counterclockwise rotation. -/
@[simp] theorem reflect_rotate (p : Vertex n) :
    p.rotate.reflect = p.reflect.rotate.rotate := by
  ext <;> rfl

/-- Add barycentric coordinates, embedding translated lattice triangles. -/
def add {m : ℕ} (p : Vertex n) (q : Vertex m) : Vertex (n + m) :=
  ⟨p.x + q.x, p.y + q.y, p.z + q.z, by have := p.sum_eq; have := q.sum_eq; omega⟩

@[simp] theorem add_x {m : ℕ} (p : Vertex n) (q : Vertex m) : (p.add q).x = p.x + q.x := (rfl)
@[simp] theorem add_y {m : ℕ} (p : Vertex n) (q : Vertex m) : (p.add q).y = p.y + q.y := (rfl)
@[simp] theorem add_z {m : ℕ} (p : Vertex n) (q : Vertex m) : (p.add q).z = p.z + q.z := (rfl)

/-- Squared length in the ambient barycentric integer coordinates. -/
def sqDist (p q : Vertex n) : ℤ :=
  ((p.x : ℤ) - q.x) ^ 2 + ((p.y : ℤ) - q.y) ^ 2 + ((p.z : ℤ) - q.z) ^ 2

/-- Expand barycentric squared distance in coordinates. -/
theorem sqDist_def (p q : Vertex n) : sqDist p q =
    ((p.x : ℤ) - q.x) ^ 2 + ((p.y : ℤ) - q.y) ^ 2 + ((p.z : ℤ) - q.z) ^ 2 := (rfl)

@[simp] theorem sqDist_self (p : Vertex n) : sqDist p p = 0 := by simp [sqDist]

/-- Barycentric squared distance is symmetric. -/
theorem sqDist_comm (p q : Vertex n) : sqDist p q = sqDist q p := by
  unfold sqDist
  ring

@[simp] theorem sqDist_rotate (p q : Vertex n) : sqDist p.rotate q.rotate = sqDist p q := by
  simp only [sqDist, rotate_x, rotate_y, rotate_z]
  ring

@[simp] theorem sqDist_reflect (p q : Vertex n) :
    sqDist p.reflect q.reflect = sqDist p q := by
  simp only [sqDist, reflect_x, reflect_y, reflect_z]
  ring

/-- Translation of a lattice triangle preserves barycentric squared distances. -/
@[simp] theorem sqDist_add {m : ℕ} (p : Vertex m) (q r : Vertex n) :
    sqDist (p.add q) (p.add r) = sqDist q r := by
  simp only [sqDist, add_x, add_y, add_z, Nat.cast_add]
  ring

/-- The equilateral planar realization of the triangular lattice. -/
noncomputable def plane (p : Vertex n) : EuclideanSpace ℝ (Fin 2) :=
  !₂[(p.z : ℝ) + p.y / 2, Real.sqrt 3 * p.y / 2]

@[simp] theorem plane_zero (p : Vertex n) :
    p.plane 0 = (p.z : ℝ) + p.y / 2 := (rfl)

@[simp] theorem plane_one (p : Vertex n) :
    p.plane 1 = Real.sqrt 3 * p.y / 2 := (rfl)

/-- Planar squared distances are half the barycentric squared distances. -/
theorem dist_plane_sq (p q : Vertex n) :
    dist p.plane q.plane ^ 2 = (sqDist p q : ℝ) / 2 := by
  have hp : (p.x : ℝ) + p.y + p.z = n := by exact_mod_cast p.sum_eq
  have hq : (q.x : ℝ) + q.y + q.z = n := by exact_mod_cast q.sum_eq
  have hs : Real.sqrt 3 ^ 2 = (3 : ℝ) := Real.sq_sqrt (by norm_num)
  simp [EuclideanSpace.dist_sq_eq, plane, Fin.sum_univ_two, Real.dist_eq, sqDist]
  nlinarith [sq_nonneg ((p.x : ℝ) - q.x + (p.y - q.y) + (p.z - q.z))]

/-- The planar realization does not identify distinct lattice vertices. -/
theorem plane_injective : Function.Injective (plane (n := n)) := by
  intro p q h
  have hd := dist_plane_sq p q
  rw [h, dist_self] at hd
  simp only [sqDist, Int.cast_add, Int.cast_pow, Int.cast_sub, Int.cast_natCast] at hd
  have hx : (p.x : ℝ) = q.x := by
    nlinarith [sq_nonneg ((p.y : ℝ) - q.y), sq_nonneg ((p.z : ℝ) - q.z)]
  have hy : (p.y : ℝ) = q.y := by
    nlinarith [sq_nonneg ((p.x : ℝ) - q.x), sq_nonneg ((p.z : ℝ) - q.z)]
  have hz : (p.z : ℝ) = q.z := by
    nlinarith [sq_nonneg ((p.x : ℝ) - q.x), sq_nonneg ((p.y : ℝ) - q.y)]
  exact Vertex.ext (by exact_mod_cast hx) (by exact_mod_cast hy) (by exact_mod_cast hz)

end Vertex

/-- A unit rhombus in perimeter order, with `a,c` the obtuse (short-diagonal) corners.
All squared distances here use barycentric coordinates. -/
structure IsRhombus {n : ℕ} (a b c d : Vertex n) : Prop where
  /-- The diagonals have the same midpoint. -/
  midpoint_x : a.x + c.x = b.x + d.x
  /-- The diagonals have the same midpoint. -/
  midpoint_y : a.y + c.y = b.y + d.y
  /-- The diagonals have the same midpoint. -/
  midpoint_z : a.z + c.z = b.z + d.z
  /-- The diagonal joining the obtuse corners is short. -/
  short : a.sqDist c = 2
  /-- The diagonal joining the acute corners is long. -/
  long : b.sqDist d = 6
  /-- The first side is a unit lattice edge. -/
  side_ab : a.sqDist b = 2
  /-- The second side is a unit lattice edge. -/
  side_bc : b.sqDist c = 2
  /-- The third side is a unit lattice edge. -/
  side_cd : c.sqDist d = 2
  /-- The fourth side is a unit lattice edge. -/
  side_da : d.sqDist a = 2

namespace IsRhombus

variable {n : ℕ} {a b c d : Vertex n}

/-- Clockwise rotation preserves unit rhombi and their obtuse-corner ordering. -/
theorem rotate (h : IsRhombus a b c d) :
    IsRhombus a.rotate b.rotate c.rotate d.rotate where
  midpoint_x := h.midpoint_z
  midpoint_y := h.midpoint_x
  midpoint_z := h.midpoint_y
  short := by simpa using h.short
  long := by simpa using h.long
  side_ab := by simpa using h.side_ab
  side_bc := by simpa using h.side_bc
  side_cd := by simpa using h.side_cd
  side_da := by simpa using h.side_da

/-- Reflection preserves unit rhombi and their obtuse-corner ordering. -/
theorem reflect (h : IsRhombus a b c d) :
    IsRhombus a.reflect b.reflect c.reflect d.reflect where
  midpoint_x := h.midpoint_x
  midpoint_y := h.midpoint_z
  midpoint_z := h.midpoint_y
  short := by simpa using h.short
  long := by simpa using h.long
  side_ab := by simpa using h.side_ab
  side_bc := by simpa using h.side_bc
  side_cd := by simpa using h.side_cd
  side_da := by simpa using h.side_da

/-- Reverse the perimeter ordering without changing the short diagonal. -/
theorem reverse (h : IsRhombus a b c d) : IsRhombus a d c b where
  midpoint_x := by have := h.midpoint_x; omega
  midpoint_y := by have := h.midpoint_y; omega
  midpoint_z := by have := h.midpoint_z; omega
  short := h.short
  long := by rw [Vertex.sqDist_comm]; exact h.long
  side_ab := by rw [Vertex.sqDist_comm]; exact h.side_da
  side_bc := by rw [Vertex.sqDist_comm]; exact h.side_cd
  side_cd := by rw [Vertex.sqDist_comm]; exact h.side_bc
  side_da := by rw [Vertex.sqDist_comm]; exact h.side_ab

/-- A half-turn of the perimeter ordering exchanges both pairs of opposite corners. -/
theorem swap_opposite (h : IsRhombus a b c d) : IsRhombus c d a b where
  midpoint_x := by have := h.midpoint_x; omega
  midpoint_y := by have := h.midpoint_y; omega
  midpoint_z := by have := h.midpoint_z; omega
  short := by rw [Vertex.sqDist_comm]; exact h.short
  long := by rw [Vertex.sqDist_comm]; exact h.long
  side_ab := h.side_cd
  side_bc := h.side_da
  side_cd := h.side_ab
  side_da := h.side_bc

/-- A triangle admitting a unit rhombus has side length at least two. -/
theorem two_le (h : IsRhombus a b c d) : 2 ≤ n := by
  by_contra hn
  have hb := b.sum_eq
  have hd := d.sum_eq
  have hx : ((b.x : ℤ) - d.x) ^ 2 ≤ 1 := by
    simpa using (sq_le_sq' (a := (b.x : ℤ) - d.x) (b := 1) (by omega) (by omega))
  have hy : ((b.y : ℤ) - d.y) ^ 2 ≤ 1 := by
    simpa using (sq_le_sq' (a := (b.y : ℤ) - d.y) (b := 1) (by omega) (by omega))
  have hz : ((b.z : ℤ) - d.z) ^ 2 ≤ 1 := by
    simpa using (sq_le_sq' (a := (b.z : ℤ) - d.z) (b := 1) (by omega) (by omega))
  have hl := h.long
  simp only [Vertex.sqDist] at hl
  omega

/-- The planar squared lengths of the two diagonals are 1 and 3. -/
theorem diagonal_dist_sq (h : IsRhombus a b c d) :
    dist a.plane c.plane ^ 2 = 1 ∧ dist b.plane d.plane ^ 2 = 3 := by
  norm_num [Vertex.dist_plane_sq, h.short, h.long]

/-- Translating a rhombus into a larger triangle preserves it. -/
theorem add {m : ℕ} (h : IsRhombus a b c d) (p : Vertex m) :
    IsRhombus (p.add a) (p.add b) (p.add c) (p.add d) where
  midpoint_x := by simp only [Vertex.add_x]; have := h.midpoint_x; omega
  midpoint_y := by simp only [Vertex.add_y]; have := h.midpoint_y; omega
  midpoint_z := by simp only [Vertex.add_z]; have := h.midpoint_z; omega
  short := by simpa using h.short
  long := by simpa using h.long
  side_ab := by simpa using h.side_ab
  side_bc := by simpa using h.side_bc
  side_cd := by simpa using h.side_cd
  side_da := by simpa using h.side_da

end IsRhombus

/-- The finite type of ordered unit rhombi in the size-`n` triangular lattice.
The first and third entries are always the obtuse corners. -/
abbrev Rhombus (n : ℕ) :=
  {t : Vertex n × Vertex n × Vertex n × Vertex n // IsRhombus t.1 t.2.1 t.2.2.1 t.2.2.2}

instance (n : ℕ) : Finite (Rhombus n) := inferInstanceAs (Finite (Subtype _))

/-- The size-two rhombus adjacent to `A`, with obtuse corners at the midpoints of
`AB` and `CA`. Rotation gives the other two orientations; translation embeds it
in every larger triangular lattice. -/
theorem isRhombus_at_cornerA :
    IsRhombus (⟨1, 1, 0, rfl⟩ : Vertex 2) ⟨2, 0, 0, rfl⟩
      ⟨1, 0, 1, rfl⟩ ⟨0, 1, 1, rfl⟩ := by
  constructor <;> norm_num [Vertex.sqDist]

end TauCeti.Hive
