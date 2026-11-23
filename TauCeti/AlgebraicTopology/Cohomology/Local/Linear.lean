/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Cohomology.Local.Basic
public import TauCeti.AlgebraicTopology.Singular.LocalHomology.Linear

/-!
# Linear coordinate changes on local cohomology

An invertible real linear map acts on `Hⁿ(E, E ∖ {0}; R, N)` by the sign of its
determinant. Here the chain coefficient module `R` is projective, while the cochain
coefficient module `N` is arbitrary. The formula holds in every degree, including
for a zero-dimensional space.

In particular, orientation-preserving linear changes of coordinates fix every local
cohomology class, whereas orientation-reversing ones negate it. So two continuous linear
isomorphisms `f f' : V ≃ E` pull a class of `Hⁿ(E, E ∖ {0})` back to classes that differ by the
sign of the determinant of `f⁻¹ ≫ f'`
(`ContinuousLinearEquiv.singularCohomologyMap_complZeroPairIso_hom_eq_sign_det_smul`). This is
the transition formula needed to compare the local fibre generators of an oriented Thom class. In
odd dimension the antipodal map `x ↦ -x` therefore acts by `-1`
(`TauCeti.singularCohomologyMap_neg_complZeroPairIso_hom`).

The proof uses the determinant action on local homology in
`TauCeti.singularHomologyMap_continuousLinearMap_compl_zero` and the relative
Kronecker equivalence in `TauCeti.singularCohomologyComplSingletonKroneckerEquiv`.

## References

* J. W. Milnor, J. D. Stasheff, *Characteristic Classes*, Section 10 (oriented fibre
  generators of Thom classes).
* A. Hatcher, *Algebraic Topology*, Sections 3.1 and 3.3 (universal coefficients and
  local orientations).
-/

public noncomputable section

open CategoryTheory Module

universe w

namespace TauCeti

variable {k : Type*} [CommRing k] (R N : ModuleCat.{w} k) [Module.Projective k R]
  {E : Type w} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

/-- An invertible real linear map acts on local cohomology at zero by the sign of its
determinant, with arbitrary cochain coefficients and projective chain coefficients. -/
theorem singularCohomologyMap_continuousLinearMap_compl_zero (f : E →L[ℝ] E)
    (hf : Set.MapsTo f ({0}ᶜ : Set E) {0}ᶜ) (n : ℕ) :
    TopPair.singularCohomologyMap (R := R) (k := k) (M := N)
        (TopPair.ofSubsetMap (TopCat.ofHom (f : C(E, E))) hf) n =
      (SignType.sign f.det : ℤ) • 𝟙 _ := by
  have hx : (0 : E) ∈ (OpenPartialHomeomorph.refl E).source := by simp
  apply ModuleCat.hom_ext
  ext α
  simp only [ModuleCat.hom_zsmul, LinearMap.smul_apply, ModuleCat.hom_id,
    LinearMap.id_apply]
  apply (singularCohomologyComplSingletonKroneckerEquiv R N
    (OpenPartialHomeomorph.refl E) hx n).injective
  rw [singularCohomologyComplSingletonKroneckerEquiv_apply,
    singularCohomologyComplSingletonKroneckerEquiv_apply]
  rw [TopPair.singularKronecker_naturality,
    singularHomologyMap_continuousLinearMap_compl_zero]
  simp

variable {R N} in
/-- **Two linear isomorphisms onto `E` read local cohomology classes up to a sign.** For continuous
linear equivalences `f f' : V ≃L[ℝ] E`, pulling a class of `Hⁿ(E, E ∖ {0}; R, N)` back along `f'`
gives its pull-back along `f` multiplied by the sign of the determinant of `f⁻¹ ≫ f'`. -/
theorem _root_.ContinuousLinearEquiv.singularCohomologyMap_complZeroPairIso_hom_eq_sign_det_smul
    {V : Type w} [TopologicalSpace V] [AddCommMonoid V] [Module ℝ V] (f f' : V ≃L[ℝ] E) (n : ℕ)
    (c : (TopPair.ofSubset (X := TopCat.of E) ({0}ᶜ : Set E)).singularCohomology R k N n) :
    TopPair.singularCohomologyMap f'.complZeroPairIso.hom n c =
      (SignType.sign ((f.symm.trans f' : E ≃L[ℝ] E) : E →L[ℝ] E).det : ℤ) •
        TopPair.singularCohomologyMap f.complZeroPairIso.hom n c := by
  set A := f.symm.trans f'
  have hA : Set.MapsTo (A : E →L[ℝ] E) ({0}ᶜ : Set E) {0}ᶜ := A.mapsTo_compl_zero
  -- `f'` is `f` followed by the automorphism `A = f⁻¹ ≫ f'` of `E`, which acts by its sign.
  have hcomp : f'.complZeroPairIso.hom =
      f.complZeroPairIso.hom ≫
        TopPair.ofSubsetMap (TopCat.ofHom ((A : E →L[ℝ] E) : C(E, E))) hA := by
    have h : f' = f.trans A := by ext; simp [A]
    rw [h, ContinuousLinearEquiv.complZeroPairIso_trans, Iso.trans_hom]
    exact congrArg _ (ContinuousLinearEquiv.complZeroPairIso_hom _)
  rw [hcomp, TopPair.singularCohomologyMap_comp,
    singularCohomologyMap_continuousLinearMap_compl_zero, Preadditive.zsmul_comp, Category.id_comp]
  exact congr($(ModuleCat.hom_zsmul _ _) c)

/-- **The antipodal map acts by `-1` in odd dimension.** For `E` of odd finite dimension, `x ↦ -x`
acts as `-1` on `Hᵈ(E, E ∖ {0}; R, N)` in every degree `d`, by the sign of
`det (-1) = (-1) ^ finrank E = -1`. -/
@[simp]
theorem singularCohomologyMap_neg_complZeroPairIso_hom (d : ℕ) (hodd : Odd (finrank ℝ E)) :
    TopPair.singularCohomologyMap (R := R) (k := k) (M := N)
      (ContinuousLinearEquiv.neg ℝ : E ≃L[ℝ] E).complZeroPairIso.hom d = -𝟙 _ := by
  have hdet : ((ContinuousLinearEquiv.neg ℝ : E ≃L[ℝ] E) : E →L[ℝ] E).det = -1 := by
    have hneg : (((ContinuousLinearEquiv.neg ℝ : E ≃L[ℝ] E) : E →L[ℝ] E) : E →ₗ[ℝ] E) =
        (-1 : ℝ) • LinearMap.id := by
      ext; simp
    rw [ContinuousLinearMap.det, hneg, LinearMap.det_smul, LinearMap.det_id, mul_one,
      hodd.neg_one_pow]
  have hf : Set.MapsTo ((ContinuousLinearEquiv.neg ℝ : E ≃L[ℝ] E) : E →L[ℝ] E) ({0}ᶜ : Set E)
      {0}ᶜ :=
    (ContinuousLinearEquiv.neg ℝ : E ≃L[ℝ] E).mapsTo_compl_zero
  have hneg : (ContinuousLinearEquiv.neg ℝ : E ≃L[ℝ] E).complZeroPairIso.hom =
      TopPair.ofSubsetMap
        (TopCat.ofHom (((ContinuousLinearEquiv.neg ℝ : E ≃L[ℝ] E) : E →L[ℝ] E) : C(E, E))) hf :=
    ContinuousLinearEquiv.complZeroPairIso_hom _
  -- The determinant-sign action.
  have hact : TopPair.singularCohomologyMap (R := R) (k := k) (M := N)
      (TopPair.ofSubsetMap
        (TopCat.ofHom (((ContinuousLinearEquiv.neg ℝ : E ≃L[ℝ] E) : E →L[ℝ] E) : C(E, E))) hf)
      d = -𝟙 _ := by
    refine (singularCohomologyMap_continuousLinearMap_compl_zero R N _ hf d).trans ?_
    simp [hdet]
  rw [hneg, hact]

end TauCeti
