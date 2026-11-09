/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Toric.Delzant.Basic

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

## Main definitions

* `TauCeti.Toric.hirzebruchNormal k`: the inward facet normals `(1, 0)`, `(0, 1)`, `(0, -1)`,
  `(-1, -k)`.
* `TauCeti.Toric.hirzebruchSupport a b`: the support constants `0`, `0`, `-b`, `-a`.

## Main results

* `TauCeti.Toric.mem_facetPolyhedron_hirzebruch_iff`: the polyhedron is the trapezoid.
* `TauCeti.Toric.isDelzant_hirzebruch`: for `0 < b`, `0 < a` and `k b < a` it is a Delzant
  polytope.

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
private theorem facetPairing_hirzebruch (x : StrongDual ℝ (Fin 2 → ℝ)) (j : Fin 4) :
    facetPairing ((Int.castAddHom ℝ).compLeft (Fin 2)) (hirzebruchNormal k) j x =
      ![x (Pi.single 0 1), x (Pi.single 1 1), -x (Pi.single 1 1),
        -x (Pi.single 0 1) - k * x (Pi.single 1 1)] j := by
  have h (v : Fin 2 → ℤ) : (Int.castAddHom ℝ).compLeft (Fin 2) v =
      (v 0 : ℝ) • Pi.single 0 1 + (v 1 : ℝ) • Pi.single 1 1 := by
    ext i
    fin_cases i <;> simp
  rw [facetPairing_apply, h, map_add, map_smul, map_smul, smul_eq_mul, smul_eq_mul]
  fin_cases j <;> simp [hirzebruchNormal_def]
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

/-- Under the hypotheses of the trapezoid, `k x(e₂) < a` whenever `0 ≤ x(e₂) ≤ b`. -/
private theorem intCast_mul_lt (ha : 0 < a) (hab : k * b < a) {q : ℝ} (hq₀ : 0 ≤ q)
    (hqb : q ≤ b) : k * q < a := by
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
  obtain ⟨-, hq₀, hqb, -⟩ := mem_facetPolyhedron_hirzebruch_iff.1 hx
  have hkq := intCast_mul_lt ha hab hq₀ hqb
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
  obtain ⟨C, -, hC⟩ := (Pi.basisFun ℝ (Fin 2)).exists_opNorm_le (F := ℝ)
  refine (Metric.isBounded_iff_subset_closedBall 0).2 ⟨C * (a + |(k : ℝ)| * b + b),
    fun x hx ↦ ?_⟩
  obtain ⟨hp₀, hq₀, hqb, hpq⟩ := mem_facetPolyhedron_hirzebruch_iff.1 hx
  have hkq : -(k * x (Pi.single 1 1)) ≤ |(k : ℝ)| * b := by
    calc -(k * x (Pi.single 1 1)) ≤ |k * x (Pi.single 1 1)| := neg_le_abs _
      _ = |(k : ℝ)| * x (Pi.single 1 1) := by rw [abs_mul, abs_of_nonneg hq₀]
      _ ≤ |(k : ℝ)| * b := mul_le_mul_of_nonneg_left hqb (abs_nonneg _)
  rw [Metric.mem_closedBall, dist_zero_right]
  refine hC (by positivity) (Fin.forall_fin_two.2 ⟨?_, ?_⟩)
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
  have hkq := intCast_mul_lt ha hab (half_pos hb).le (half_le_self hb.le)
  let pt (p q : ℝ) : StrongDual ℝ (Fin 2 → ℝ) :=
    p • ContinuousLinearMap.proj 0 + q • ContinuousLinearMap.proj 1
  have hp (p q : ℝ) : pt p q (Pi.single 0 1) = p := by simp [pt]
  have hq (p q : ℝ) : pt p q (Pi.single 1 1) = q := by simp [pt]
  fin_cases j
  · refine ⟨pt 0 (b / 2), mem_facetPolyhedron_hirzebruch_iff.2 ?_, eq_singleton_iff_unique_mem.2
      ⟨zero_mem_activeSet_hirzebruch_iff.2 (hp _ _), fun l hl ↦ ?_⟩⟩
    · rw [hp, hq]
      exact ⟨le_rfl, by positivity, by linarith, by linarith⟩
    fin_cases l
    · rfl
    · linarith [hq 0 (b / 2) ▸ one_mem_activeSet_hirzebruch_iff.1 hl]
    · linarith [hq 0 (b / 2) ▸ two_mem_activeSet_hirzebruch_iff.1 hl]
    · linarith [hp 0 (b / 2) ▸ hq 0 (b / 2) ▸ three_mem_activeSet_hirzebruch_iff.1 hl]
  · refine ⟨pt (a / 2) 0, mem_facetPolyhedron_hirzebruch_iff.2 ?_, eq_singleton_iff_unique_mem.2
      ⟨one_mem_activeSet_hirzebruch_iff.2 (hq _ _), fun l hl ↦ ?_⟩⟩
    · rw [hp, hq]
      exact ⟨by positivity, le_rfl, hb.le, by linarith⟩
    fin_cases l
    · linarith [hp (a / 2) 0 ▸ zero_mem_activeSet_hirzebruch_iff.1 hl]
    · rfl
    · linarith [hq (a / 2) 0 ▸ two_mem_activeSet_hirzebruch_iff.1 hl]
    · linarith [hp (a / 2) 0 ▸ hq (a / 2) 0 ▸ three_mem_activeSet_hirzebruch_iff.1 hl]
  · refine ⟨pt ((a - k * b) / 2) b, mem_facetPolyhedron_hirzebruch_iff.2 ?_,
      eq_singleton_iff_unique_mem.2 ⟨two_mem_activeSet_hirzebruch_iff.2 (hq _ _), fun l hl ↦ ?_⟩⟩
    · rw [hp, hq]
      exact ⟨by linarith, hb.le, le_rfl, by linarith⟩
    fin_cases l
    · linarith [hp ((a - k * b) / 2) b ▸ zero_mem_activeSet_hirzebruch_iff.1 hl]
    · linarith [hq ((a - k * b) / 2) b ▸ one_mem_activeSet_hirzebruch_iff.1 hl]
    · rfl
    · linarith [hp ((a - k * b) / 2) b ▸ hq ((a - k * b) / 2) b ▸
        three_mem_activeSet_hirzebruch_iff.1 hl]
  · refine ⟨pt (a - k * (b / 2)) (b / 2), mem_facetPolyhedron_hirzebruch_iff.2 ?_,
      eq_singleton_iff_unique_mem.2 ⟨three_mem_activeSet_hirzebruch_iff.2 ?_, fun l hl ↦ ?_⟩⟩
    · rw [hp, hq]
      exact ⟨by linarith, by positivity, by linarith, by linarith⟩
    · rw [hp, hq]
      ring
    fin_cases l
    · linarith [hp (a - k * (b / 2)) (b / 2) ▸ zero_mem_activeSet_hirzebruch_iff.1 hl]
    · linarith [hq (a - k * (b / 2)) (b / 2) ▸ one_mem_activeSet_hirzebruch_iff.1 hl]
    · linarith [hq (a - k * (b / 2)) (b / 2) ▸ two_mem_activeSet_hirzebruch_iff.1 hl]
    · rfl

/-- **Hirzebruch trapezoids are Delzant polytopes.** For an integer `k` and reals with `0 < b`,
`0 < a` and `k b < a`, the trapezoid `{0 ≤ x(e₁), 0 ≤ x(e₂) ≤ b, x(e₁) + k x(e₂) ≤ a}` in the
lattice `ℤ²`, with facet normals `(1, 0)`, `(0, 1)`, `(0, -1)`, `(-1, -k)`, is a Delzant
polytope. -/
theorem isDelzant_hirzebruch (hb : 0 < b) (ha : 0 < a) (hab : k * b < a) :
    IsDelzant ((Int.castAddHom ℝ).compLeft (Fin 2)) (hirzebruchNormal k)
      (hirzebruchSupport a b) := by
  refine ⟨isBounded_facetPolyhedron_hirzebruch hb ha, fun x hx ↦ ?_,
    exists_activeSet_hirzebruch_eq_singleton hb ha hab⟩
  -- At a vertex the active constraints are exactly a pair of adjacent facets, since a single
  -- normal does not span the plane.
  obtain ⟨-, hker⟩ := mem_extremePoints_facetPolyhedron_iff.1 hx
  obtain ⟨i, j, hij, hsub⟩ :=
    exists_activeSet_hirzebruch_subset_pair hb ha hab (extremePoints_subset hx)
  have hmem {l m : Fin 4} (hsub' : activeSet (facetPairing ((Int.castAddHom ℝ).compLeft (Fin 2))
      (hirzebruchNormal k)) (hirzebruchSupport a b) x ⊆ {l, m}) :
      l ∈ activeSet (facetPairing ((Int.castAddHom ℝ).compLeft (Fin 2)) (hirzebruchNormal k))
        (hirzebruchSupport a b) x := by
    by_contra hl
    obtain ⟨w, hw, hwm⟩ := exists_ne_zero_facetPairing_hirzebruch_eq_zero (k := k) m
    refine hw (hker w fun n hn ↦ ?_)
    rcases hsub' hn with rfl | rfl
    · exact absurd hn hl
    · rwa [← facetPairing_apply]
  have hA : activeSet (facetPairing ((Int.castAddHom ℝ).compLeft (Fin 2)) (hirzebruchNormal k))
      (hirzebruchSupport a b) x = {i, j} :=
    hsub.antisymm (insert_subset (hmem hsub)
      (singleton_subset_iff.2 (hmem (pair_comm i j ▸ hsub))))
  rw [isSmoothVertex_iff_span_eq_top, hA, image_pair, span_pair_hirzebruchNormal_eq_top hij,
    Module.finrank_fin_fun]
  exact ⟨rfl, (ncard_insert_le _ _).trans (by simp)⟩

end TauCeti.Toric
