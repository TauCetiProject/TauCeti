/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Finsupp.Defs
public import Mathlib.LinearAlgebra.Span.Basic
public import TauCeti.Algebra.Homology.Contraction.Linear.Basic
import Mathlib.Tactic.Abel
import TauCeti.Data.Finsupp.MapDomain

/-!
# Gaussian elimination in a free differential module

Let `d` be a square-zero endomorphism of the free module `ι →₀ R` over a ring `R`, and let
`x ≠ y` be two generators such that the coefficient `u = ⟨d x, y⟩` of `y` in `d x` is a unit.
Then the pair `x, y` can be cancelled: `d` contracts onto the free module on the remaining
generators `{x, y}ᶜ`, with the reduced differential

`d' w = d w - ⟨d w, y⟩ u⁻¹ d x`

restricted to `{x, y}ᶜ` (`LinearMap.gaussianElimination`). In matrix form, the coefficient of `j`
in `d' i` is the Schur complement `⟨d i, j⟩ - ⟨d i, y⟩ u⁻¹ ⟨d x, j⟩`
(`LinearMap.gaussianElimination_single_apply`).

The contraction (`LinearMap.gaussianEliminationContraction`) is a special one, with homotopy
`h z = ⟨z, y⟩ u⁻¹ x` (`LinearMap.gaussianEliminationHomotopy`). It satisfies `h² = 0` because
`x ≠ y`, and `h d h = h` because `u` is invertible. With `d² = 0` this makes `d h + h d` an
idempotent commuting with `d`, the projection onto the span of `x` and `d x` along the chains `z`
with `⟨z, y⟩ = ⟨d z, y⟩ = 0`. Writing `ψ = 1 - (d h + h d)` for the complementary idempotent, the
inclusion of the contraction is `ψ` on the generators other than `x` and `y`, and its projection is
`ψ` followed by restriction to these generators. In particular `d'` squares to zero
(`LinearMap.gaussianElimination_comp_self`), and its homology is that of `d`
(`TauCeti.LinearContraction.homologyEquiv` in
`TauCeti.Algebra.Homology.Contraction.Linear.Homology.Equiv`).

This is the algebraic model of how a based complex changes when a pair of generators joined by an
invertible coefficient is born or dies, as at a birth–death point of a generic one-parameter family
of Morse functions, whose two critical points of adjacent index are joined by a single trajectory.
Only the coefficients of `d` enter: if `d` lowers a degree on the generators by a fixed amount, so
does `d'` (`LinearMap.eq_add_of_gaussianElimination_single_apply_ne_zero`). This construction
produces the contraction over any ring without a grading. For a based homological complex over a
commutative ring, `HomologicalComplex.toMatrix_d_eq_of_cancel_of_invertible` computes the
reduced differential as a Schur complement. The two-periodic torsion identities are in
`TauCeti.Algebra.Homology.ReidemeisterTorsion.Cancellation`.

## Main definitions

* `LinearMap.gaussianEliminationHomotopy`: the homotopy `z ↦ ⟨z, y⟩ u⁻¹ x`.
* `LinearMap.gaussianElimination`: the reduced differential on the free module on `{x, y}ᶜ`.
* `LinearMap.gaussianEliminationContraction`: the special contraction of `d` onto it.

## Main results

* `LinearMap.gaussianElimination_single_apply`: its coefficients are the Schur complements of `u`.
* `LinearMap.gaussianElimination_comp_self`: it squares to zero.
* `LinearMap.eq_add_of_gaussianElimination_single_apply_ne_zero`: it lowers a degree on the
  generators when `d` does.

## References

* D. Bar-Natan, *Fast Khovanov homology computations*, J. Knot Theory Ramifications 16 (2007),
  Lemma 4.2 (Gaussian elimination).
* J. Cerf, *La stratification naturelle des espaces de fonctions différentiables réelles et le
  théorème de la pseudo-isotopie*, Publ. Math. IHÉS 39 (1970), for births and deaths of critical
  points.
-/

public section

open Finsupp
open scoped Ring

namespace LinearMap

variable {R ι : Type*} [Ring R] (d : Module.End R (ι →₀ R)) (x y : ι)

/-- The homotopy `z ↦ ⟨z, y⟩ u⁻¹ x` of Gaussian elimination, where `u = ⟨d x, y⟩`. -/
noncomputable def gaussianEliminationHomotopy : Module.End R (ι →₀ R) :=
  (toSpanSingleton R R (d (Finsupp.single x 1) y)⁻¹ʳ ∘ₗ lapply y).smulRight (Finsupp.single x 1)

/-- The **reduced differential** of Gaussian elimination at the pair `x, y`: on the free module
on the generators other than `x` and `y`, it is `w ↦ d w - ⟨d w, y⟩ u⁻¹ d x`, where
`u = ⟨d x, y⟩`, restricted to these generators. -/
noncomputable def gaussianElimination : Module.End R (({x, y}ᶜ : Set ι) →₀ R) :=
  lsubtypeDomain _ ∘ₗ (d - d ∘ₗ d.gaussianEliminationHomotopy x y ∘ₗ d) ∘ₗ
    lmapDomain R R ((↑) : ({x, y}ᶜ : Set ι) → ι)

variable {d x y}

/-- The homotopy of Gaussian elimination sends `z` to `⟨z, y⟩ u⁻¹ x`, where `u = ⟨d x, y⟩`. -/
@[simp]
theorem gaussianEliminationHomotopy_apply (z : ι →₀ R) :
    d.gaussianEliminationHomotopy x y z =
      (z y * (d (Finsupp.single x 1) y)⁻¹ʳ) • Finsupp.single x 1 := by
  simp [gaussianEliminationHomotopy]

/-- The coefficient of a generator `j` in the reduced differential of a chain `w`. -/
theorem gaussianElimination_apply (w : ({x, y}ᶜ : Set ι) →₀ R) (j : ({x, y}ᶜ : Set ι)) :
    d.gaussianElimination x y w j =
      d (w.mapDomain (↑)) j -
        d (w.mapDomain (↑)) y * (d (Finsupp.single x 1) y)⁻¹ʳ * d (Finsupp.single x 1) j := by
  simp only [gaussianElimination, comp_apply, LinearMap.sub_apply, lmapDomain_apply,
    lsubtypeDomain_apply, subtypeDomain_apply, Finsupp.sub_apply,
    gaussianEliminationHomotopy_apply, map_smul, Finsupp.smul_apply, smul_eq_mul, mul_assoc]

/-- The coefficients of the reduced differential are the **Schur complements**
`⟨d i, j⟩ - ⟨d i, y⟩ u⁻¹ ⟨d x, j⟩` of `u = ⟨d x, y⟩`. -/
@[simp]
theorem gaussianElimination_single_apply (i j : ({x, y}ᶜ : Set ι)) (a : R) :
    d.gaussianElimination x y (Finsupp.single i a) j =
      d (Finsupp.single i a) j -
        d (Finsupp.single i a) y * (d (Finsupp.single x 1) y)⁻¹ʳ * d (Finsupp.single x 1) j := by
  rw [gaussianElimination_apply, mapDomain_single]

/-- A coefficient `⟨d' i, j⟩` of the reduced differential vanishes when `⟨d i, j⟩` does and the
path from `i` to `j` through the cancelled pair is broken. -/
theorem gaussianElimination_single_apply_eq_zero {i j : ({x, y}ᶜ : Set ι)} {a : R}
    (hij : d (Finsupp.single i a) j = 0)
    (hy : d (Finsupp.single i a) y = 0 ∨ d (Finsupp.single x 1) j = 0) :
    d.gaussianElimination x y (Finsupp.single i a) j = 0 := by
  rcases hy with hy | hy <;> simp [hij, hy]

/-- If every nonzero coefficient `⟨d i, j⟩` has `deg i = deg j + k`, so that `d` lowers the
degree `deg` by `k`, and the cancelled pair is joined by a nonzero coefficient, then the reduced
differential also lowers `deg` by `k`. -/
theorem eq_add_of_gaussianElimination_single_apply_ne_zero {G : Type*} [Add G] {deg : ι → G}
    {k : G} (hdeg : ∀ i j a, d (Finsupp.single i a) j ≠ 0 → deg i = deg j + k)
    (hu : d (Finsupp.single x 1) y ≠ 0) {i j : ({x, y}ᶜ : Set ι)} {a : R}
    (h : d.gaussianElimination x y (Finsupp.single i a) j ≠ 0) : deg i = deg j + k := by
  by_cases hij : d (Finsupp.single i a) j = 0
  · by_cases hy : d (Finsupp.single i a) y = 0
    · exact absurd (gaussianElimination_single_apply_eq_zero hij (.inl hy)) h
    by_cases hj : d (Finsupp.single x 1) j = 0
    · exact absurd (gaussianElimination_single_apply_eq_zero hij (.inr hj)) h
    rw [hdeg _ _ _ hy, ← hdeg _ _ _ hu, hdeg _ _ _ hj]
  · exact hdeg _ _ _ hij

/-! ### The contraction -/

section Contraction

variable (d x y) in
/-- The complementary idempotent `1 - (d h + h d)` of Gaussian elimination. -/
private noncomputable def complement : Module.End R (ι →₀ R) :=
  LinearMap.id - (d ∘ₗ d.gaussianEliminationHomotopy x y + d.gaussianEliminationHomotopy x y ∘ₗ d)

private theorem complement_apply (z : ι →₀ R) :
    complement d x y z =
      z - d (d.gaussianEliminationHomotopy x y z) - d.gaussianEliminationHomotopy x y (d z) := by
  simp [complement, sub_sub]

private theorem homotopy_homotopy (hxy : x ≠ y) (z : ι →₀ R) :
    d.gaussianEliminationHomotopy x y (d.gaussianEliminationHomotopy x y z) = 0 := by
  simp [gaussianEliminationHomotopy_apply, single_eq_of_ne' hxy]

private theorem homotopy_d_homotopy (hu : IsUnit (d (Finsupp.single x 1) y)) (z : ι →₀ R) :
    d.gaussianEliminationHomotopy x y (d (d.gaussianEliminationHomotopy x y z)) =
      d.gaussianEliminationHomotopy x y z := by
  simp only [gaussianEliminationHomotopy_apply, map_smul]
  rw [Ring.mul_inverse_cancel _ hu, one_smul]

private theorem homotopy_mapDomain (w : ({x, y}ᶜ : Set ι) →₀ R) :
    d.gaussianEliminationHomotopy x y (w.mapDomain (↑)) = 0 := by
  rw [gaussianEliminationHomotopy_apply, mapDomain_of_notMem_range _ _ (by simp), zero_mul,
    zero_smul]

private theorem subtypeDomain_homotopy (z : ι →₀ R) :
    (d.gaussianEliminationHomotopy x y z).subtypeDomain (· ∈ ({x, y}ᶜ : Set ι)) = 0 := by
  ext ⟨j, hj⟩
  have hjx : j ≠ x := fun h ↦ hj (by simp [h])
  simp [gaussianEliminationHomotopy_apply, single_eq_of_ne hjx]

variable (hd : d ∘ₗ d = 0) (hxy : x ≠ y) (hu : IsUnit (d (Finsupp.single x 1) y))

include hxy hu in
private theorem complement_homotopy (z : ι →₀ R) :
    complement d x y (d.gaussianEliminationHomotopy x y z) = 0 := by
  rw [complement_apply, homotopy_homotopy hxy, homotopy_d_homotopy hu, map_zero]
  abel

include hxy hu in
private theorem homotopy_complement (z : ι →₀ R) :
    d.gaussianEliminationHomotopy x y (complement d x y z) = 0 := by
  rw [complement_apply, map_sub, map_sub, homotopy_d_homotopy hu, homotopy_homotopy hxy]
  abel

include hxy hu in
private theorem complement_apply_right (z : ι →₀ R) : complement d x y z y = 0 := by
  have hx : (Finsupp.single x 1 : ι →₀ R) y = 0 := single_eq_of_ne' hxy
  rw [complement_apply, gaussianEliminationHomotopy_apply, gaussianEliminationHomotopy_apply,
    map_smul]
  simp only [Finsupp.sub_apply, Finsupp.smul_apply, smul_eq_mul, hx, mul_zero, mul_assoc,
    Ring.inverse_mul_cancel _ hu, mul_one, sub_self]

include hxy hu in
private theorem complement_single_left (a : R) :
    complement d x y (Finsupp.single x a) = 0 := by
  rw [← smul_single_one, map_smul, complement_apply]
  simp [gaussianEliminationHomotopy_apply, single_eq_of_ne' hxy,
    Ring.mul_inverse_cancel _ hu]

include hd

private theorem d_d (z : ι →₀ R) : d (d z) = 0 := congr($hd z)

private theorem complement_d (z : ι →₀ R) : complement d x y (d z) = d (complement d x y z) := by
  simp [complement_apply, d_d hd]

private theorem gaussianElimination_eq (w : ({x, y}ᶜ : Set ι) →₀ R) :
    d.gaussianElimination x y w =
      (complement d x y (d (w.mapDomain (↑)))).subtypeDomain (· ∈ ({x, y}ᶜ : Set ι)) := by
  simp [gaussianElimination, complement_apply, d_d hd, lsubtypeDomain_apply]

include hxy hu

private theorem complement_complement (z : ι →₀ R) :
    complement d x y (complement d x y z) = complement d x y z := by
  rw [complement_apply (complement d x y z), homotopy_complement hxy hu, ← complement_d hd,
    homotopy_complement hxy hu, map_zero]
  abel

private theorem complement_mapDomain_subtypeDomain_complement (z : ι →₀ R) :
    complement d x y (((complement d x y z).subtypeDomain (· ∈ ({x, y}ᶜ : Set ι))).mapDomain (↑)) =
      complement d x y z := by
  rw [mapDomain_subtypeDomain_compl_pair hxy, complement_apply_right hxy hu, single_zero, sub_zero,
    map_sub, complement_complement hd hxy hu, complement_single_left hxy hu, sub_zero]

variable (d x y) in
/-- **Gaussian elimination.** If `d` squares to zero and the coefficient `⟨d x, y⟩` is a unit for
generators `x ≠ y`, then `d` contracts onto its reduced differential on the free module on the
remaining generators, by a special contraction with homotopy `z ↦ ⟨z, y⟩ ⟨d x, y⟩⁻¹ x`. -/
noncomputable def gaussianEliminationContraction :
    TauCeti.LinearSpecialContraction d (d.gaussianElimination x y) where
  incl := complement d x y ∘ₗ lmapDomain R R (↑)
  proj := lsubtypeDomain _ ∘ₗ complement d x y
  homotopy := d.gaussianEliminationHomotopy x y
  dM_comp_incl := by
    refine LinearMap.ext fun w ↦ ?_
    simp only [LinearMap.comp_apply, lmapDomain_apply]
    rw [gaussianElimination_eq hd, complement_mapDomain_subtypeDomain_complement hd hxy hu,
      complement_d hd]
  proj_comp_dM := by
    refine LinearMap.ext fun z ↦ ?_
    simp only [LinearMap.comp_apply, lsubtypeDomain_apply]
    rw [gaussianElimination_eq hd, complement_d hd, complement_d hd,
      complement_mapDomain_subtypeDomain_complement hd hxy hu]
  proj_comp_incl := by
    refine LinearMap.ext fun w ↦ ?_
    simp only [LinearMap.comp_apply, lmapDomain_apply, lsubtypeDomain_apply, LinearMap.id_apply,
      complement_complement hd hxy hu]
    rw [complement_apply, homotopy_mapDomain, map_zero, sub_zero, Finsupp.subtypeDomain_sub,
      subtypeDomain_homotopy, sub_zero, subtypeDomain_mapDomain_subtype]
  dM_comp_homotopy_add_homotopy_comp_dM := by
    refine LinearMap.ext fun z ↦ ?_
    simp only [LinearMap.add_apply, LinearMap.comp_apply, LinearMap.sub_apply, LinearMap.id_apply,
      lmapDomain_apply, lsubtypeDomain_apply]
    rw [complement_mapDomain_subtypeDomain_complement hd hxy hu, complement_apply]
    abel
  homotopy_comp_incl := by
    refine LinearMap.ext fun w ↦ ?_
    simp only [LinearMap.comp_apply, LinearMap.zero_apply, homotopy_complement hxy hu]
  proj_comp_homotopy := by
    refine LinearMap.ext fun z ↦ ?_
    simp only [LinearMap.comp_apply, LinearMap.zero_apply, lsubtypeDomain_apply,
      complement_homotopy hxy hu, subtypeDomain_zero]
  homotopy_comp_homotopy := by
    refine LinearMap.ext fun z ↦ ?_
    simp only [LinearMap.comp_apply, LinearMap.zero_apply, homotopy_homotopy hxy]

/-- The homotopy of Gaussian elimination is `z ↦ ⟨z, y⟩ u⁻¹ x`, where `u = ⟨d x, y⟩`. -/
@[simp]
theorem gaussianEliminationContraction_homotopy :
    (d.gaussianEliminationContraction x y hd hxy hu).homotopy =
      d.gaussianEliminationHomotopy x y :=
  (rfl)

/-- The inclusion of Gaussian elimination corrects a chain `w` on the remaining generators by a
multiple of `x`, so that the coefficient of `y` in its boundary vanishes. -/
@[simp]
theorem gaussianEliminationContraction_incl_apply (w : ({x, y}ᶜ : Set ι) →₀ R) :
    (d.gaussianEliminationContraction x y hd hxy hu).incl w =
      w.mapDomain (↑) -
        (d (w.mapDomain (↑)) y * (d (Finsupp.single x 1) y)⁻¹ʳ) • Finsupp.single x 1 := by
  simp only [gaussianEliminationContraction, LinearMap.comp_apply, lmapDomain_apply]
  rw [complement_apply, homotopy_mapDomain, map_zero, sub_zero, gaussianEliminationHomotopy_apply]

/-- The projection of Gaussian elimination removes from a chain `z` the multiple of `d x`
cancelling its coefficient of `y`, and restricts to the remaining generators. -/
@[simp]
theorem gaussianEliminationContraction_proj_apply (z : ι →₀ R) :
    (d.gaussianEliminationContraction x y hd hxy hu).proj z =
      z.subtypeDomain (· ∈ ({x, y}ᶜ : Set ι)) -
        (z y * (d (Finsupp.single x 1) y)⁻¹ʳ) •
          (d (Finsupp.single x 1)).subtypeDomain (· ∈ ({x, y}ᶜ : Set ι)) := by
  simp only [gaussianEliminationContraction, LinearMap.comp_apply, lsubtypeDomain_apply]
  rw [complement_apply, subtypeDomain_sub, subtypeDomain_sub, subtypeDomain_homotopy, sub_zero,
    gaussianEliminationHomotopy_apply, map_smul]
  ext j
  simp

/-- The reduced differential of Gaussian elimination squares to zero. -/
theorem gaussianElimination_comp_self :
    d.gaussianElimination x y ∘ₗ d.gaussianElimination x y = 0 :=
  (d.gaussianEliminationContraction x y hd hxy hu).dN_comp_dN_eq_zero hd

end Contraction

end LinearMap
