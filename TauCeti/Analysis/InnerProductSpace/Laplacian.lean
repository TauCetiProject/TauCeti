/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Analysis.InnerProductSpace.Laplacian
public import Mathlib.Analysis.Normed.Affine.Isometry

/-!
# Geometric invariance of the Laplacian

Mathlib's `Mathlib/Analysis/InnerProductSpace/Laplacian.lean` records that the Laplacian `Δ`
commutes with *left* composition by a continuous linear map or equivalence acting on the
*values* of a function (`ContDiffAt.laplacian_CLM_comp_left`, `laplacian_CLE_comp_left`).
This file supplies the complementary *right* composition, acting on the *domain* variable: the
geometric invariance of `Δ` under the rigid motions of a Euclidean space — affine isometry
equivalences, with orthogonal changes of variable (linear isometry equivalences) and translations
as special cases.

For an affine isometry equivalence `e : E ≃ᵃⁱ[ℝ] E'` and any `f : E' → F`,

`Δ (f ∘ e) = (Δ f) ∘ e`.

In particular, for a linear isometry equivalence `l : E ≃ₗᵢ[ℝ] E'`,

`Δ (f ∘ l) = (Δ f) ∘ l`,

and for a translation by `a : E`,

`Δ (fun y ↦ f (y + a)) = fun y ↦ (Δ f) (y + a)`.

All three identities hold with *no* differentiability hypothesis on `f`, because the underlying
`iteratedFDeriv` composition laws are unconditional (the iterated derivative is junk-valued off
the smooth locus, yet still transforms correctly under a linear change of variable). The harmonic
corollaries, where smoothness re-enters, live in
`TauCeti/Analysis/InnerProductSpace/HarmonicIsometry.lean`.

## Main declarations

* `TauCeti.laplacian_comp_affineIsometryEquiv_right`: `Δ (f ∘ e) = (Δ f) ∘ e` for an
  affine isometry equivalence `e`.
* `TauCeti.laplacian_comp_linearIsometryEquiv_right`: `Δ (f ∘ l) = (Δ f) ∘ l` for an
  isometry `l`.
* `TauCeti.laplacian_comp_add_right`: translation invariance of `Δ`.
-/

public section

namespace TauCeti

open InnerProductSpace Laplacian

variable
  {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  {E' : Type*} [NormedAddCommGroup E'] [InnerProductSpace ℝ E'] [FiniteDimensional ℝ E']
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

omit [FiniteDimensional ℝ E] [FiniteDimensional ℝ E'] in
/-- The iterated derivative transforms under a linear isometry equivalence on the right by
pulling the directions through the isometry. This is the unconditional engine behind the
geometric invariance of the Laplacian. -/
private theorem iteratedFDeriv_comp_linearIsometryEquiv_apply (l : E ≃ₗᵢ[ℝ] E') (f : E' → F)
    (i : ℕ) (x : E) (m : Fin i → E) :
    iteratedFDeriv ℝ i (f ∘ l) x m = iteratedFDeriv ℝ i f (l x) (fun j ↦ l (m j)) := by
  have h := l.toContinuousLinearEquiv.iteratedFDerivWithin_comp_right f uniqueDiffOn_univ
    (x := x) (Set.mem_univ _) i
  rw [Set.preimage_univ, iteratedFDerivWithin_univ, iteratedFDerivWithin_univ] at h
  rw [← LinearIsometryEquiv.coe_toContinuousLinearEquiv l]
  rw [h, ContinuousMultilinearMap.compContinuousLinearMap_apply]
  rfl

/-- **Geometric invariance of the Laplacian under isometries.** For a linear isometry
equivalence `l`, the Laplacian commutes with right composition by `l`:
`Δ (f ∘ l) = (Δ f) ∘ l`. No differentiability hypothesis is needed. -/
theorem laplacian_comp_linearIsometryEquiv_right (l : E ≃ₗᵢ[ℝ] E') (f : E' → F) :
    Δ (f ∘ l) = (Δ f) ∘ l := by
  ext x
  simp only [Function.comp_apply,
    laplacian_eq_iteratedFDeriv_orthonormalBasis (f ∘ l) (stdOrthonormalBasis ℝ E),
    laplacian_eq_iteratedFDeriv_orthonormalBasis f ((stdOrthonormalBasis ℝ E).map l)]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [iteratedFDeriv_comp_linearIsometryEquiv_apply l f 2 x]
  congr 1
  funext j
  fin_cases j <;> simp [OrthonormalBasis.map_apply]

/-- **Translation invariance of the Laplacian.** Shifting the argument by a constant `a`
commutes with the Laplacian: `Δ (fun y ↦ f (y + a)) = fun y ↦ (Δ f) (y + a)`. No
differentiability hypothesis is needed. -/
theorem laplacian_comp_add_right (f : E → F) (a : E) :
    Δ (fun y ↦ f (y + a)) = fun y ↦ (Δ f) (y + a) := by
  ext x
  simp only [laplacian_eq_iteratedFDeriv_orthonormalBasis _ (stdOrthonormalBasis ℝ E)]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [iteratedFDeriv_comp_add_right']

/-- **Geometric invariance of the Laplacian under affine isometries.** For an affine isometry
equivalence `e`, the Laplacian commutes with right composition by `e`:
`Δ (f ∘ e) = (Δ f) ∘ e`. No differentiability hypothesis is needed. -/
theorem laplacian_comp_affineIsometryEquiv_right (e : E ≃ᵃⁱ[ℝ] E') (f : E' → F) :
    Δ (f ∘ e) = (Δ f) ∘ e := by
  have hcomp : f ∘ e = (fun y ↦ f (y + e 0)) ∘ e.linearIsometryEquiv := by
    funext x
    have hx : e x = e.linearIsometryEquiv x + e 0 := by
      simpa using e.map_vadd (0 : E) x
    simp [Function.comp_apply, hx]
  rw [hcomp, laplacian_comp_linearIsometryEquiv_right e.linearIsometryEquiv
      (fun y ↦ f (y + e 0)),
    laplacian_comp_add_right f (e 0)]
  ext x
  have hx : e x = e.linearIsometryEquiv x + e 0 := by
    simpa using e.map_vadd (0 : E) x
  simp [Function.comp_apply, hx]

end TauCeti
