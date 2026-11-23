/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Toric.Delzant.CornerChop
public import TauCeti.Geometry.Toric.Delzant.Simplex

import TauCeti.Analysis.Normed.Module.FiniteDimension
import TauCeti.Geometry.Toric.Delzant.Equiv
import TauCeti.Topology.Algebra.Module.ContinuousLinearMap.Basic

/-!
# Hirzebruch trapezoids as Delzant polytopes

The moment polytopes of the Hirzebruch surfaces `H_k` (and of `S² × S²` when `k = 0`) are the
trapezoids

`Δ = {x ∈ (ℝ²)* | 0 ≤ x(e₁), 0 ≤ x(e₂) ≤ b, x(e₁) + k x(e₂) ≤ a}`

with vertices `(0, 0)`, `(a, 0)`, `(0, b)` and `(a - k b, b)` in the coordinates
`(x(e₁), x(e₂))`. In the standard lattice `ℤ² ⊂ ℝ²` (`(Int.castAddHom ℝ).compLeft (Fin 2)`) their
four facets have inward normals `(1, 0)`, `(0, 1)`, `(0, -1)`, `(-1, -k)` and support constants
`0`, `0`, `-b`, `-a` (`TauCeti.Toric.hirzebruchNormal`, `TauCeti.Toric.hirzebruchSupport`).

For an integer `k` and reals with `0 < b`, `0 < a` and `k b < a`, this presentation is Delzant
(`TauCeti.Toric.isDelzant_hirzebruch`). The opposite facets `{x(e₂) = 0}` and `{x(e₂) = b}` never
meet, and neither do `{x(e₁) = 0}` and `{x(e₁) + k x(e₂) = a}`, because `k x(e₂) < a` whenever
`0 ≤ x(e₂) ≤ b`. So at most two constraints are active at a point, and at a vertex exactly two
adjacent ones are, since one normal cannot span the plane. Each pair of adjacent normals has
determinant `±1`, so generates `ℤ²`, and hence is a lattice basis
(`TauCeti.Toric.isSmoothVertex_iff_span_eq_top`). The integer `k` may be negative.

The same analysis gives the vertices: they are exactly the four points `(0, 0)`, `(a, 0)`, `(0, b)`
and `(a - k b, b)` (`TauCeti.Toric.extremePoints_facetPolyhedron_hirzebruch`), which are distinct
(`TauCeti.Toric.ncard_extremePoints_facetPolyhedron_hirzebruch`). On the Hirzebruch surface they
are the moment images of the four fixed points of the torus action; for `k = 0` the trapezoid is
the rectangle `[0, a] × [0, b]` of `S² × S²`.

**The blowup of `ℂP²`.** Chopping a vertex off the triangle
`{0 ≤ x(e₁), 0 ≤ x(e₂), x(e₁) + x(e₂) ≤ a}` of `ℂP²` (`TauCeti.Toric.simplexNormal`,
`TauCeti.Toric.cornerChopNormal`) is the polytope operation of the toric symplectic blowup at the
fixed point over that vertex. At the vertex `(0, a)`, chopping at depth `ε` adds the facet
`{x(e₂) ≤ a - ε}`, with normal `e₁ - (e₁ + e₂) = -e₂`, and the result is, up to relabelling the
facets, the presentation of the Hirzebruch trapezoid with `k = 1` and `b = a - ε`
(`TauCeti.Toric.exists_equiv_cornerChop_simplex_eq_hirzebruch`,
`TauCeti.Toric.facetPolyhedron_cornerChop_simplex`). So the chopped triangle is a Delzant polytope
for every depth `0 < ε < a` (`TauCeti.Toric.isDelzant_cornerChop_simplex`), not only for the small
depths of `TauCeti.Toric.IsDelzant.eventually_isDelzant_cornerChop`. This is the polytope side of
the classical identification of the blowup of `ℂP²` at a fixed point with the Hirzebruch surface
`H₁`; the other two vertices of the triangle give the same polytope up to an integral affine
change of coordinates.

## Main definitions

* `TauCeti.Toric.hirzebruchNormal k`: the inward facet normals `(1, 0)`, `(0, 1)`, `(0, -1)`,
  `(-1, -k)`.
* `TauCeti.Toric.hirzebruchSupport a b`: the support constants `0`, `0`, `-b`, `-a`.

## Main results

* `TauCeti.Toric.mem_facetPolyhedron_hirzebruch_iff`: the polyhedron is the trapezoid.
* `TauCeti.Toric.isDelzant_hirzebruch`: for `0 < b`, `0 < a` and `k b < a` it is a Delzant
  polytope.
* `TauCeti.Toric.extremePoints_facetPolyhedron_hirzebruch`,
  `TauCeti.Toric.ncard_extremePoints_facetPolyhedron_hirzebruch`: its four vertices.
* `TauCeti.Toric.exists_equiv_cornerChop_simplex_eq_hirzebruch`,
  `TauCeti.Toric.isDelzant_cornerChop_simplex`: chopping a vertex off the triangle of `ℂP²` gives
  the trapezoid with `k = 1`, a Delzant polytope at every depth below `a`.

## References

* A. Cannas da Silva, *Lectures on Symplectic Geometry*, Lecture Notes in Mathematics 1764,
  Springer, 2001, Section 28.
* V. Guillemin, *Moment Maps and Combinatorial Invariants of Hamiltonian `T^n`-spaces*,
  Birkhäuser, 1994, Chapter 1.
-/

public section

noncomputable section

open Set

namespace TauCeti.Toric

/-- The inward facet normals `(1, 0)`, `(0, 1)`, `(0, -1)`, `(-1, -k)` of the Hirzebruch
trapezoid in the lattice `ℤ²`. -/
def hirzebruchNormal (k : ℤ) : Fin 4 → Fin 2 → ℤ :=
  ![![1, 0], ![0, 1], ![0, -1], ![-1, -k]]

/-- The support constants `0`, `0`, `-b`, `-a` of the Hirzebruch trapezoid
`{0 ≤ x(e₁), 0 ≤ x(e₂) ≤ b, x(e₁) + k x(e₂) ≤ a}`. -/
def hirzebruchSupport (a b : ℝ) : Fin 4 → ℝ :=
  ![0, 0, -b, -a]

theorem hirzebruchNormal_def (k : ℤ) :
    hirzebruchNormal k = ![![1, 0], ![0, 1], ![0, -1], ![-1, -k]] := (rfl)

theorem hirzebruchSupport_def (a b : ℝ) : hirzebruchSupport a b = ![0, 0, -b, -a] := (rfl)

variable {k : ℤ} {a b : ℝ}

/-- The four facet pairings of the Hirzebruch trapezoid, in the coordinates `x(e₁)`, `x(e₂)`. -/
theorem facetPairing_hirzebruch (x : StrongDual ℝ (Fin 2 → ℝ)) (j : Fin 4) :
    facetPairing ((Int.castAddHom ℝ).compLeft (Fin 2)) (hirzebruchNormal k) j x =
      ![x (Pi.single 0 1), x (Pi.single 1 1), -x (Pi.single 1 1),
        -x (Pi.single 0 1) - k * x (Pi.single 1 1)] j := by
  have h (v : Fin 2 → ℤ) : (Int.castAddHom ℝ).compLeft (Fin 2) v =
      (v 0 : ℝ) • Pi.single 0 1 + (v 1 : ℝ) • Pi.single 1 1 := by
    ext i
    fin_cases i <;> simp
  rw [facetPairing_apply, h, map_add, map_smul, map_smul, smul_eq_mul, smul_eq_mul]
  fin_cases j
  · simp [hirzebruchNormal_def]
  · simp [hirzebruchNormal_def]
  · simp [hirzebruchNormal_def]
  · simp [hirzebruchNormal_def]
    ring

/-- **The Hirzebruch trapezoid.** The polyhedron of the Hirzebruch presentation consists of the
functionals `x` with `0 ≤ x(e₁)`, `0 ≤ x(e₂) ≤ b` and `x(e₁) + k x(e₂) ≤ a`. -/
theorem mem_facetPolyhedron_hirzebruch_iff {x : StrongDual ℝ (Fin 2 → ℝ)} :
    x ∈ facetPolyhedron ((Int.castAddHom ℝ).compLeft (Fin 2)) (hirzebruchNormal k)
        (hirzebruchSupport a b) ↔
      0 ≤ x (Pi.single 0 1) ∧ 0 ≤ x (Pi.single 1 1) ∧ x (Pi.single 1 1) ≤ b ∧
        x (Pi.single 0 1) + k * x (Pi.single 1 1) ≤ a := by
  simp only [mem_facetPolyhedron, ← facetPairing_apply, facetPairing_hirzebruch,
    Fin.forall_fin_succ, IsEmpty.forall_iff, and_true]
  simp [hirzebruchSupport_def]

/-- The facet `{x(e₁) = 0}` is active exactly when `x(e₁) = 0`. -/
theorem zero_mem_activeSet_hirzebruch_iff {x : StrongDual ℝ (Fin 2 → ℝ)} :
    0 ∈ activeSet (facetPairing ((Int.castAddHom ℝ).compLeft (Fin 2)) (hirzebruchNormal k))
      (hirzebruchSupport a b) x ↔ x (Pi.single 0 1) = 0 := by
  rw [mem_activeSet, facetPairing_hirzebruch]
  simp [hirzebruchSupport_def]

/-- The facet `{x(e₂) = 0}` is active exactly when `x(e₂) = 0`. -/
theorem one_mem_activeSet_hirzebruch_iff {x : StrongDual ℝ (Fin 2 → ℝ)} :
    1 ∈ activeSet (facetPairing ((Int.castAddHom ℝ).compLeft (Fin 2)) (hirzebruchNormal k))
      (hirzebruchSupport a b) x ↔ x (Pi.single 1 1) = 0 := by
  rw [mem_activeSet, facetPairing_hirzebruch]
  simp [hirzebruchSupport_def]

/-- The facet `{x(e₂) = b}` is active exactly when `x(e₂) = b`. -/
theorem two_mem_activeSet_hirzebruch_iff {x : StrongDual ℝ (Fin 2 → ℝ)} :
    2 ∈ activeSet (facetPairing ((Int.castAddHom ℝ).compLeft (Fin 2)) (hirzebruchNormal k))
      (hirzebruchSupport a b) x ↔ x (Pi.single 1 1) = b := by
  rw [mem_activeSet, facetPairing_hirzebruch]
  simp [hirzebruchSupport_def]

/-- The facet `{x(e₁) + k x(e₂) = a}` is active exactly when `x(e₁) + k x(e₂) = a`. -/
theorem three_mem_activeSet_hirzebruch_iff {x : StrongDual ℝ (Fin 2 → ℝ)} :
    3 ∈ activeSet (facetPairing ((Int.castAddHom ℝ).compLeft (Fin 2)) (hirzebruchNormal k))
      (hirzebruchSupport a b) x ↔ x (Pi.single 0 1) + k * x (Pi.single 1 1) = a := by
  rw [mem_activeSet, facetPairing_hirzebruch]
  simp only [hirzebruchSupport_def, Matrix.cons_val]
  constructor <;> intro h <;> linarith

/-- For `0 < a` and `k b < a`, every point of the Hirzebruch trapezoid has `k x(e₂) < a`, so the
facets `{x(e₁) = 0}` and `{x(e₁) + k x(e₂) = a}` never meet. -/
theorem intCast_mul_lt_of_mem_facetPolyhedron_hirzebruch (ha : 0 < a) (hab : k * b < a)
    {x : StrongDual ℝ (Fin 2 → ℝ)}
    (hx : x ∈ facetPolyhedron ((Int.castAddHom ℝ).compLeft (Fin 2)) (hirzebruchNormal k)
      (hirzebruchSupport a b)) :
    k * x (Pi.single 1 1) < a := by
  obtain ⟨-, hq₀, hqb, -⟩ := mem_facetPolyhedron_hirzebruch_iff.1 hx
  rcases le_or_gt 0 k with hk | hk
  · exact (mul_le_mul_of_nonneg_left hqb (Int.cast_nonneg_iff.2 hk)).trans_lt hab
  · exact (mul_nonpos_of_nonpos_of_nonneg (by exact_mod_cast hk.le) hq₀).trans_lt ha

/-- For each facet, some nonzero functional vanishes on its normal. -/
private theorem exists_ne_zero_facetPairing_hirzebruch_eq_zero (j : Fin 4) :
    ∃ w : StrongDual ℝ (Fin 2 → ℝ), w ≠ 0 ∧
      facetPairing ((Int.castAddHom ℝ).compLeft (Fin 2)) (hirzebruchNormal k) j w = 0 := by
  have hne (w : StrongDual ℝ (Fin 2 → ℝ)) (l : Fin 2) (hl : w (Pi.single l 1) ≠ 0) : w ≠ 0 :=
    fun h ↦ hl (by simp [h])
  fin_cases j
  · exact ⟨ContinuousLinearMap.proj 1, hne _ 1 (by simp), by simp [hirzebruchNormal_def]⟩
  · exact ⟨ContinuousLinearMap.proj 0, hne _ 0 (by simp), by simp [hirzebruchNormal_def]⟩
  · exact ⟨ContinuousLinearMap.proj 0, hne _ 0 (by simp), by simp [hirzebruchNormal_def]⟩
  · exact ⟨(k : ℝ) • ContinuousLinearMap.proj 0 - ContinuousLinearMap.proj 1, hne _ 1 (by simp),
      by simp [hirzebruchNormal_def]⟩

/-- Two adjacent normals of the Hirzebruch trapezoid generate the lattice `ℤ²`. -/
private theorem span_pair_hirzebruchNormal_eq_top {i j : Fin 4}
    (hij : (i, j) = (0, 1) ∨ (i, j) = (0, 2) ∨ (i, j) = (1, 3) ∨ (i, j) = (2, 3)) :
    Submodule.span ℤ {hirzebruchNormal k i, hirzebruchNormal k j} = ⊤ := by
  set S := Submodule.span ℤ {hirzebruchNormal k i, hirzebruchNormal k j}
  have hi : hirzebruchNormal k i ∈ S := Submodule.subset_span (by simp)
  have hj : hirzebruchNormal k j ∈ S := Submodule.subset_span (by simp)
  -- Both standard basis vectors are integral combinations of the two normals.
  suffices h : Pi.single 0 1 ∈ S ∧ Pi.single 1 1 ∈ S by
    rw [eq_top_iff, ← (Pi.basisFun ℤ (Fin 2)).span_eq, Submodule.span_le]
    rintro _ ⟨l, rfl⟩
    fin_cases l
    · simpa using h.1
    · simpa using h.2
  obtain h | h | h | h := hij <;> obtain ⟨rfl, rfl⟩ := Prod.ext_iff.1 h
  -- Each standard basis vector is `±` one normal, or `-u₃ ∓ k u` for the normal `u = ±e₂`.
  · exact ⟨by convert hi using 1; ext l; fin_cases l <;> simp [hirzebruchNormal_def],
      by convert hj using 1; ext l; fin_cases l <;> simp [hirzebruchNormal_def]⟩
  · exact ⟨by convert hi using 1; ext l; fin_cases l <;> simp [hirzebruchNormal_def],
      by convert S.neg_mem hj using 1; ext l; fin_cases l <;> simp [hirzebruchNormal_def]⟩
  · refine ⟨?_, by convert hi using 1; ext l; fin_cases l <;> simp [hirzebruchNormal_def]⟩
    convert S.sub_mem (S.neg_mem hj) (S.smul_mem k hi) using 1
    ext l
    fin_cases l <;> simp [hirzebruchNormal_def]
  · refine ⟨?_, by convert S.neg_mem hi using 1; ext l; fin_cases l <;> simp [hirzebruchNormal_def]⟩
    convert S.add_mem (S.neg_mem hj) (S.smul_mem k hi) using 1
    ext l
    fin_cases l <;> simp [hirzebruchNormal_def]

/-- At a point of the trapezoid, the active constraints lie in a pair of adjacent facets: the
opposite facets `{x(e₂) = 0}`, `{x(e₂) = b}` and `{x(e₁) = 0}`, `{x(e₁) + k x(e₂) = a}` never
meet. -/
private theorem exists_activeSet_hirzebruch_subset_pair (hb : 0 < b) (ha : 0 < a)
    (hab : k * b < a) {x : StrongDual ℝ (Fin 2 → ℝ)}
    (hx : x ∈ facetPolyhedron ((Int.castAddHom ℝ).compLeft (Fin 2)) (hirzebruchNormal k)
      (hirzebruchSupport a b)) :
    ∃ i j : Fin 4, ((i, j) = (0, 1) ∨ (i, j) = (0, 2) ∨ (i, j) = (1, 3) ∨ (i, j) = (2, 3)) ∧
      activeSet (facetPairing ((Int.castAddHom ℝ).compLeft (Fin 2)) (hirzebruchNormal k))
        (hirzebruchSupport a b) x ⊆ {i, j} := by
  have hkq := intCast_mul_lt_of_mem_facetPolyhedron_hirzebruch ha hab hx
  have m₀ := fun h ↦ (zero_mem_activeSet_hirzebruch_iff (k := k) (a := a) (b := b) (x := x)).1 h
  have m₁ := fun h ↦ (one_mem_activeSet_hirzebruch_iff (k := k) (a := a) (b := b) (x := x)).1 h
  have m₂ := fun h ↦ (two_mem_activeSet_hirzebruch_iff (k := k) (a := a) (b := b) (x := x)).1 h
  have m₃ := fun h ↦ (three_mem_activeSet_hirzebruch_iff (k := k) (a := a) (b := b) (x := x)).1 h
  by_cases h₀ : x (Pi.single 0 1) = 0 <;> by_cases h₁ : x (Pi.single 1 1) = 0
  · refine ⟨0, 1, by simp, fun l hl ↦ ?_⟩
    fin_cases l
    · simp
    · simp
    · linarith [m₂ hl]
    · linarith [m₃ hl]
  · refine ⟨0, 2, by simp, fun l hl ↦ ?_⟩
    fin_cases l
    · simp
    · exact absurd (m₁ hl) h₁
    · simp
    · linarith [m₃ hl]
  · refine ⟨1, 3, by simp, fun l hl ↦ ?_⟩
    fin_cases l
    · exact absurd (m₀ hl) h₀
    · simp
    · linarith [m₂ hl]
    · simp
  · refine ⟨2, 3, by simp, fun l hl ↦ ?_⟩
    fin_cases l
    · exact absurd (m₀ hl) h₀
    · exact absurd (m₁ hl) h₁
    · simp
    · simp

/-- The Hirzebruch trapezoid is bounded: its points satisfy `0 ≤ x(e₁) ≤ a + |k| b` and
`0 ≤ x(e₂) ≤ b`. -/
private theorem isBounded_facetPolyhedron_hirzebruch (hb : 0 < b) (ha : 0 < a) :
    Bornology.IsBounded (facetPolyhedron ((Int.castAddHom ℝ).compLeft (Fin 2))
      (hirzebruchNormal k) (hirzebruchSupport a b)) := by
  refine (Pi.basisFun ℝ (Fin 2)).isBounded_of_norm_apply_le
    (M := a + |(k : ℝ)| * b + b) fun x hx ↦ ?_
  obtain ⟨hp₀, hq₀, hqb, hpq⟩ := mem_facetPolyhedron_hirzebruch_iff.1 hx
  have hkq : -(k * x (Pi.single 1 1)) ≤ |(k : ℝ)| * b := by
    calc -(k * x (Pi.single 1 1)) ≤ |k * x (Pi.single 1 1)| := neg_le_abs _
      _ = |(k : ℝ)| * x (Pi.single 1 1) := by rw [abs_mul, abs_of_nonneg hq₀]
      _ ≤ |(k : ℝ)| * b := mul_le_mul_of_nonneg_left hqb (abs_nonneg _)
  refine Fin.forall_fin_two.2 ⟨?_, ?_⟩
  · rw [Pi.basisFun_apply, Real.norm_of_nonneg hp₀]
    linarith
  · rw [Pi.basisFun_apply, Real.norm_of_nonneg hq₀]
    have := mul_nonneg (abs_nonneg (k : ℝ)) hb.le
    linarith

/-- Every facet of the Hirzebruch trapezoid has a point lying on no other facet: the midpoints of
the edges `{x(e₁) = 0}`, `{x(e₂) = 0}` and `{x(e₂) = b}`, and the point of `{x(e₁) + k x(e₂) = a}`
with `x(e₂) = b / 2`. -/
private theorem exists_activeSet_hirzebruch_eq_singleton (hb : 0 < b) (ha : 0 < a)
    (hab : k * b < a) (j : Fin 4) :
    ∃ x ∈ facetPolyhedron ((Int.castAddHom ℝ).compLeft (Fin 2)) (hirzebruchNormal k)
      (hirzebruchSupport a b), activeSet (facetPairing ((Int.castAddHom ℝ).compLeft (Fin 2))
        (hirzebruchNormal k)) (hirzebruchSupport a b) x = {j} := by
  let pt (p q : ℝ) : StrongDual ℝ (Fin 2 → ℝ) :=
    p • ContinuousLinearMap.proj 0 + q • ContinuousLinearMap.proj 1
  have hp (p q : ℝ) : pt p q (Pi.single 0 1) = p := by simp [pt]
  have hq (p q : ℝ) : pt p q (Pi.single 1 1) = q := by simp [pt]
  -- Each constraint active at `pt p q` gives an equation in `p` and `q`.
  have hact {p q : ℝ} {l : Fin 4} (hl : l ∈ activeSet (facetPairing
      ((Int.castAddHom ℝ).compLeft (Fin 2)) (hirzebruchNormal k)) (hirzebruchSupport a b)
        (pt p q)) :
      (l = 0 → p = 0) ∧ (l = 1 → q = 0) ∧ (l = 2 → q = b) ∧ (l = 3 → p + k * q = a) := by
    refine ⟨?_, ?_, ?_, ?_⟩ <;> rintro rfl
    · simpa only [hp] using zero_mem_activeSet_hirzebruch_iff.1 hl
    · simpa only [hq] using one_mem_activeSet_hirzebruch_iff.1 hl
    · simpa only [hq] using two_mem_activeSet_hirzebruch_iff.1 hl
    · simpa only [hp, hq] using three_mem_activeSet_hirzebruch_iff.1 hl
  fin_cases j
  · refine ⟨pt 0 (b / 2), mem_facetPolyhedron_hirzebruch_iff.2 ?_, eq_singleton_iff_unique_mem.2
      ⟨zero_mem_activeSet_hirzebruch_iff.2 (hp _ _), fun l hl ↦ ?_⟩⟩
    · rw [hp, hq]
      exact ⟨le_rfl, by positivity, by linarith, by linarith⟩
    obtain ⟨-, h₁, h₂, h₃⟩ := hact hl
    fin_cases l <;> simp at h₁ h₂ h₃ ⊢ <;> linarith
  · refine ⟨pt (a / 2) 0, mem_facetPolyhedron_hirzebruch_iff.2 ?_, eq_singleton_iff_unique_mem.2
      ⟨one_mem_activeSet_hirzebruch_iff.2 (hq _ _), fun l hl ↦ ?_⟩⟩
    · rw [hp, hq]
      exact ⟨by positivity, le_rfl, hb.le, by linarith⟩
    obtain ⟨h₀, -, h₂, h₃⟩ := hact hl
    fin_cases l <;> simp at h₀ h₂ h₃ ⊢ <;> linarith
  · refine ⟨pt ((a - k * b) / 2) b, mem_facetPolyhedron_hirzebruch_iff.2 ?_,
      eq_singleton_iff_unique_mem.2 ⟨two_mem_activeSet_hirzebruch_iff.2 (hq _ _), fun l hl ↦ ?_⟩⟩
    · rw [hp, hq]
      exact ⟨by linarith, hb.le, le_rfl, by linarith⟩
    obtain ⟨h₀, h₁, -, h₃⟩ := hact hl
    fin_cases l <;> simp at h₀ h₁ h₃ ⊢ <;> linarith
  · refine ⟨pt (a - k * (b / 2)) (b / 2), mem_facetPolyhedron_hirzebruch_iff.2 ?_,
      eq_singleton_iff_unique_mem.2 ⟨three_mem_activeSet_hirzebruch_iff.2 ?_, fun l hl ↦ ?_⟩⟩
    · rw [hp, hq]
      exact ⟨by linarith, by positivity, by linarith, by linarith⟩
    · rw [hp, hq]
      ring
    obtain ⟨h₀, h₁, h₂, -⟩ := hact hl
    fin_cases l <;> simp at h₀ h₁ h₂ ⊢ <;> linarith

/-- At a vertex of the trapezoid, the active constraints are exactly a pair of adjacent facets,
since a single normal does not span the plane. -/
private theorem exists_activeSet_hirzebruch_eq_pair (hb : 0 < b) (ha : 0 < a) (hab : k * b < a)
    {x : StrongDual ℝ (Fin 2 → ℝ)}
    (hx : x ∈ (facetPolyhedron ((Int.castAddHom ℝ).compLeft (Fin 2)) (hirzebruchNormal k)
      (hirzebruchSupport a b)).extremePoints ℝ) :
    ∃ i j : Fin 4, ((i, j) = (0, 1) ∨ (i, j) = (0, 2) ∨ (i, j) = (1, 3) ∨ (i, j) = (2, 3)) ∧
      activeSet (facetPairing ((Int.castAddHom ℝ).compLeft (Fin 2)) (hirzebruchNormal k))
        (hirzebruchSupport a b) x = {i, j} := by
  obtain ⟨i, j, hij, hsub⟩ :=
    exists_activeSet_hirzebruch_subset_pair hb ha hab (extremePoints_subset hx)
  have hmem {l m : Fin 4} (hsub' : activeSet (facetPairing ((Int.castAddHom ℝ).compLeft (Fin 2))
      (hirzebruchNormal k)) (hirzebruchSupport a b) x ⊆ {l, m}) :
      l ∈ activeSet (facetPairing ((Int.castAddHom ℝ).compLeft (Fin 2)) (hirzebruchNormal k))
        (hirzebruchSupport a b) x := by
    by_contra hl
    obtain ⟨w, hw, hwm⟩ := exists_ne_zero_facetPairing_hirzebruch_eq_zero (k := k) m
    refine not_activeSet_subset_of_mem_extremePoints hx hw (s := {m}) (by rintro _ rfl; exact hwm)
      fun n hn ↦ ?_
    rcases hsub' hn with rfl | rfl
    · exact absurd hn hl
    · rfl
  exact ⟨i, j, hij, hsub.antisymm (insert_subset (hmem hsub)
    (singleton_subset_iff.2 (hmem (pair_comm i j ▸ hsub))))⟩

/-- **Hirzebruch trapezoids are Delzant polytopes.** For an integer `k` and reals with `0 < b`,
`0 < a` and `k b < a`, the trapezoid `{0 ≤ x(e₁), 0 ≤ x(e₂) ≤ b, x(e₁) + k x(e₂) ≤ a}` in the
lattice `ℤ²`, with facet normals `(1, 0)`, `(0, 1)`, `(0, -1)`, `(-1, -k)`, is a Delzant
polytope. -/
theorem isDelzant_hirzebruch (hb : 0 < b) (ha : 0 < a) (hab : k * b < a) :
    IsDelzant ((Int.castAddHom ℝ).compLeft (Fin 2)) (hirzebruchNormal k)
      (hirzebruchSupport a b) := by
  refine ⟨isBounded_facetPolyhedron_hirzebruch hb ha, fun x hx ↦ ?_,
    exists_activeSet_hirzebruch_eq_singleton hb ha hab⟩
  obtain ⟨i, j, hij, hA⟩ := exists_activeSet_hirzebruch_eq_pair hb ha hab hx
  rw [isSmoothVertex_iff_span_eq_top, hA, image_pair, span_pair_hirzebruchNormal_eq_top hij,
    Module.finrank_fin_fun]
  exact ⟨rfl, (ncard_insert_le _ _).trans (by simp)⟩

/-! ### Vertices -/

/-- Every vertex of the trapezoid is one of `(0, 0)`, `(a, 0)`, `(0, b)` and `(a - k b, b)`: it is
the meeting point of a pair of adjacent facets. -/
private theorem extremePoints_facetPolyhedron_hirzebruch_subset (hb : 0 < b) (ha : 0 < a)
    (hab : k * b < a) :
    (facetPolyhedron ((Int.castAddHom ℝ).compLeft (Fin 2)) (hirzebruchNormal k)
        (hirzebruchSupport a b)).extremePoints ℝ ⊆
      {0, a • ContinuousLinearMap.proj 0, b • ContinuousLinearMap.proj 1,
        (a - k * b) • ContinuousLinearMap.proj 0 + b • ContinuousLinearMap.proj 1} := by
  intro x hx
  obtain ⟨i, j, hij, hA⟩ := exists_activeSet_hirzebruch_eq_pair hb ha hab hx
  have hi : i ∈ activeSet (facetPairing ((Int.castAddHom ℝ).compLeft (Fin 2))
      (hirzebruchNormal k)) (hirzebruchSupport a b) x := by rw [hA]; simp
  have hj : j ∈ activeSet (facetPairing ((Int.castAddHom ℝ).compLeft (Fin 2))
      (hirzebruchNormal k)) (hirzebruchSupport a b) x := by rw [hA]; simp
  obtain h | h | h | h := hij <;> obtain ⟨rfl, rfl⟩ := Prod.ext_iff.1 h
  · refine .inl ?_
    have h₀ := zero_mem_activeSet_hirzebruch_iff.1 hi
    have h₁ := one_mem_activeSet_hirzebruch_iff.1 hj
    exact ContinuousLinearMap.pi_ext_single_one fun l ↦ by fin_cases l <;> simp [h₀, h₁]
  · refine .inr <| .inr <| .inl ?_
    have h₀ := zero_mem_activeSet_hirzebruch_iff.1 hi
    have h₂ := two_mem_activeSet_hirzebruch_iff.1 hj
    exact ContinuousLinearMap.pi_ext_single_one fun l ↦ by fin_cases l <;> simp [h₀, h₂]
  · refine .inr <| .inl ?_
    have h₁ := one_mem_activeSet_hirzebruch_iff.1 hi
    have h₃ := three_mem_activeSet_hirzebruch_iff.1 hj
    rw [h₁] at h₃
    exact ContinuousLinearMap.pi_ext_single_one fun l ↦ by
      fin_cases l <;> simp [h₁, show x (Pi.single 0 1) = a by linarith]
  · refine .inr <| .inr <| .inr ?_
    have h₂ := two_mem_activeSet_hirzebruch_iff.1 hi
    have h₃ := three_mem_activeSet_hirzebruch_iff.1 hj
    rw [h₂] at h₃
    exact ContinuousLinearMap.pi_ext_single_one fun l ↦ by
      fin_cases l <;> simp [h₂, show x (Pi.single 0 1) = a - k * b by linarith]

/-- **The vertices of the Hirzebruch trapezoid.** For `0 < b`, `0 < a` and `k b < a`, the
trapezoid `{0 ≤ x(e₁), 0 ≤ x(e₂) ≤ b, x(e₁) + k x(e₂) ≤ a}` has exactly the four vertices
`(0, 0)`, `(a, 0)`, `(0, b)` and `(a - k b, b)` in the coordinates `(x(e₁), x(e₂))`, written with
the coordinate functionals `ContinuousLinearMap.proj`. -/
theorem extremePoints_facetPolyhedron_hirzebruch (hb : 0 < b) (ha : 0 < a) (hab : k * b < a) :
    (facetPolyhedron ((Int.castAddHom ℝ).compLeft (Fin 2)) (hirzebruchNormal k)
        (hirzebruchSupport a b)).extremePoints ℝ =
      {0, a • ContinuousLinearMap.proj 0, b • ContinuousLinearMap.proj 1,
        (a - k * b) • ContinuousLinearMap.proj 0 + b • ContinuousLinearMap.proj 1} := by
  refine (extremePoints_facetPolyhedron_hirzebruch_subset hb ha hab).antisymm fun x hx ↦ ?_
  -- Each listed point lies on a pair of adjacent facets, and a functional vanishing on their
  -- normals vanishes on `e₁` and `e₂`.
  refine mem_extremePoints_facetPolyhedron_iff.2 ⟨mem_facetPolyhedron_hirzebruch_iff.2 ?_,
    fun w hw ↦ ?_⟩
  · rcases hx with rfl | rfl | rfl | rfl
    · simp [hb.le, ha.le]
    · simp [hb.le, ha.le]
    · simp [hb.le, hab.le]
    · refine ⟨?_, ?_, ?_, ?_⟩ <;> simp <;> linarith
  have hw' (j : Fin 4) (hj : j ∈ activeSet (facetPairing ((Int.castAddHom ℝ).compLeft (Fin 2))
      (hirzebruchNormal k)) (hirzebruchSupport a b) x) :
      facetPairing ((Int.castAddHom ℝ).compLeft (Fin 2)) (hirzebruchNormal k) j w = 0 := by
    rw [facetPairing_apply]
    exact hw j hj
  -- A functional on `ℝ²` vanishing on `e₁` and `e₂` is zero.
  suffices w (Pi.single 0 1) = 0 ∧ w (Pi.single 1 1) = 0 from
    ContinuousLinearMap.pi_ext_single_one fun l ↦ by fin_cases l <;> simp [this.1, this.2]
  rcases hx with rfl | rfl | rfl | rfl
  · have h₀ := hw' 0 (zero_mem_activeSet_hirzebruch_iff.2 (by simp))
    have h₁ := hw' 1 (one_mem_activeSet_hirzebruch_iff.2 (by simp))
    simp only [facetPairing_hirzebruch, Matrix.cons_val] at h₀ h₁
    exact ⟨h₀, h₁⟩
  · have h₁ := hw' 1 (one_mem_activeSet_hirzebruch_iff.2 (by simp))
    have h₃ := hw' 3 (three_mem_activeSet_hirzebruch_iff.2 (by simp))
    simp only [facetPairing_hirzebruch, Matrix.cons_val] at h₁ h₃
    exact ⟨by rw [h₁] at h₃; linarith, h₁⟩
  · have h₀ := hw' 0 (zero_mem_activeSet_hirzebruch_iff.2 (by simp))
    have h₂ := hw' 2 (two_mem_activeSet_hirzebruch_iff.2 (by simp))
    simp only [facetPairing_hirzebruch, Matrix.cons_val] at h₀ h₂
    exact ⟨h₀, by linarith⟩
  · have h₂ := hw' 2 (two_mem_activeSet_hirzebruch_iff.2 (by simp))
    have h₃ := hw' 3 (three_mem_activeSet_hirzebruch_iff.2 (by simp))
    simp only [facetPairing_hirzebruch, Matrix.cons_val] at h₂ h₃
    have h₁ : w (Pi.single 1 1) = 0 := by linarith
    exact ⟨by rw [h₁] at h₃; linarith, h₁⟩

/-- **A Hirzebruch trapezoid has four vertices.** For `0 < b`, `0 < a` and `k b < a` its vertices
`(0, 0)`, `(a, 0)`, `(0, b)` and `(a - k b, b)` are distinct. -/
theorem ncard_extremePoints_facetPolyhedron_hirzebruch (hb : 0 < b) (ha : 0 < a)
    (hab : k * b < a) :
    ((facetPolyhedron ((Int.castAddHom ℝ).compLeft (Fin 2)) (hirzebruchNormal k)
        (hirzebruchSupport a b)).extremePoints ℝ).ncard = 4 := by
  have hkb : a - k * b ≠ 0 := by linarith
  rw [extremePoints_facetPolyhedron_hirzebruch hb ha hab,
    ncard_insert_of_notMem, ncard_insert_of_notMem, ncard_pair]
  · exact DFunLike.ne_iff.2 ⟨Pi.single 0 1, by simpa using hkb.symm⟩
  · simp only [mem_insert_iff, mem_singleton_iff, not_or]
    exact ⟨DFunLike.ne_iff.2 ⟨Pi.single 1 1, by simpa using hb.ne⟩,
      DFunLike.ne_iff.2 ⟨Pi.single 1 1, by simpa using hb.ne⟩⟩
  · simp only [mem_insert_iff, mem_singleton_iff, not_or]
    exact ⟨DFunLike.ne_iff.2 ⟨Pi.single 0 1, by simpa using ha.ne⟩,
      DFunLike.ne_iff.2 ⟨Pi.single 1 1, by simpa using hb.ne⟩,
      DFunLike.ne_iff.2 ⟨Pi.single 1 1, by simpa using hb.ne⟩⟩

/-! ### The blowup of the projective plane -/

/-- **The chopped triangle is a Hirzebruch trapezoid.** Chopping the vertex `(0, a)` off the
triangle `{0 ≤ x(e₁), 0 ≤ x(e₂), x(e₁) + x(e₂) ≤ a}` of `ℂP²`, where the facets `{x(e₁) = 0}` and
`{x(e₁) + x(e₂) = a}` meet, at depth `ε` gives, up to relabelling the facets, the presentation of
the Hirzebruch trapezoid with `k = 1` and `b = a - ε`: the new facet `{x(e₂) = a - ε}` has normal
`e₁ - (e₁ + e₂) = -e₂`. -/
theorem exists_equiv_cornerChop_simplex_eq_hirzebruch (a ε : ℝ) :
    ∃ e : Fin 4 ≃ Option (Option (Fin 2)),
      cornerChopNormal (simplexNormal (Fin 2)) {some 0, none} ∘ e = hirzebruchNormal 1 ∧
        cornerChopSupport (simplexSupport a) {some 0, none} ε ∘ e =
          hirzebruchSupport a (a - ε) := by
  -- The facets `x(e₁) ≥ 0`, `x(e₂) ≥ 0`, the new facet and the slanted facet of the triangle.
  refine ⟨⟨![some (some 0), some (some 1), none, some none], fun
    | none => 2
    | some none => 3
    | some (some l) => Fin.castLE (by decide) l, by decide, by decide⟩,
    funext fun j ↦ funext fun l ↦ ?_, funext fun j ↦ ?_⟩
  · fin_cases j <;> fin_cases l <;> simp [hirzebruchNormal_def]
  · fin_cases j <;> simp [hirzebruchSupport_def, add_comm, sub_eq_add_neg]

/-- **The blown-up triangle.** Chopping the vertex `(0, a)` off the triangle of `ℂP²` at depth `ε`
gives the Hirzebruch trapezoid `{0 ≤ x(e₁), 0 ≤ x(e₂) ≤ a - ε, x(e₁) + x(e₂) ≤ a}` with `k = 1`. -/
theorem facetPolyhedron_cornerChop_simplex (a ε : ℝ) :
    facetPolyhedron ((Int.castAddHom ℝ).compLeft (Fin 2))
        (cornerChopNormal (simplexNormal (Fin 2)) {some 0, none})
        (cornerChopSupport (simplexSupport a) {some 0, none} ε) =
      facetPolyhedron ((Int.castAddHom ℝ).compLeft (Fin 2)) (hirzebruchNormal 1)
        (hirzebruchSupport a (a - ε)) := by
  obtain ⟨e, hu, hc⟩ := exists_equiv_cornerChop_simplex_eq_hirzebruch a ε
  rw [← facetPolyhedron_comp e.surjective, hu, hc]

/-- **The blown-up triangle is Delzant at every depth.** Chopping the vertex `(0, a)` off the
triangle of `ℂP²` gives a Delzant polytope at every depth `0 < ε < a`, namely the Hirzebruch
trapezoid with `k = 1` and `b = a - ε`. Compare
`TauCeti.Toric.IsDelzant.eventually_isDelzant_cornerChop`, which only covers small depths. -/
theorem isDelzant_cornerChop_simplex {a ε : ℝ} (hε : 0 < ε) (hεa : ε < a) :
    IsDelzant ((Int.castAddHom ℝ).compLeft (Fin 2))
      (cornerChopNormal (simplexNormal (Fin 2)) {some 0, none})
      (cornerChopSupport (simplexSupport a) {some 0, none} ε) := by
  obtain ⟨e, hu, hc⟩ := exists_equiv_cornerChop_simplex_eq_hirzebruch a ε
  rw [← isDelzant_comp_equiv_iff e, hu, hc]
  exact isDelzant_hirzebruch (by linarith) (by linarith) (by simpa using hε)

end TauCeti.Toric
