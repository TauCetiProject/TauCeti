/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.VectorBundle.Orientation.Complex.EulerClass
public import TauCeti.Topology.VectorBundle.Orientation.FiberwiseEquiv

/-!
# The Euler class of a complex vector bundle under complex- and conjugate-linear isomorphisms

Let `E → B` and `E' → B'` be complex vector bundles of complex rank `r + 1`, with model fibres
`F` and `F'` (which may differ), and let `φ b' : E'_{b'} ≃ E_{g b'}` be a fibrewise isomorphism over
a continuous map `g : B' → B`, continuous on total spaces.

* If every `φ b'` is complex linear, it carries the canonical orientation of `E'_{b'}` to that of
  `E_{g b'}` (`TauCeti.VectorBundleOrientation.map_complex`), so the Euler class of `E'` is the
  pull-back of that of `E` (`TauCeti.complexEulerClass_eq_singularCohomologyMap_of_fiberwise`).
  Over the identity of the base, **isomorphic complex vector bundles have the same Euler class**
  (`TauCeti.complexEulerClass_eq_of_fiberwise`).
* If every `φ b'` is conjugate linear, it multiplies the canonical orientation by `(-1) ^ (r + 1)`
  (`TauCeti.VectorBundleOrientation.map_restrictScalarsₛₗ_complex`: it reverses one real direction
  in each complex line), so the Euler class acquires the sign `(-1) ^ (r + 1)`
  (`TauCeti.complexEulerClass_eq_neg_one_pow_smul_singularCohomologyMap_of_conjugateFiberwise`,
  `TauCeti.complexEulerClass_eq_neg_one_pow_smul_of_conjugateFiberwise`). In rank one this is
  `e(conj L) = -e(L)` for the conjugate `conj L` of a complex line bundle `L`
  (`TauCeti.complexEulerClass_eq_neg_of_finrank_eq_one_of_conjugateFiberwise`).

The conjugate-linear statements are phrased for an abstract fibrewise conjugate-linear isomorphism
`E'_{b} ≃L⋆[ℂ] E_{b}`, with no relation required between the model fibres of `E'` and `E` beyond
their dimension, so they apply to any model of the conjugate bundle, for instance one whose fibres
are the conjugate spaces of the fibres of `E` with the identity as conjugate-linear isomorphism.

## Main results

* `TauCeti.complexEulerClass_eq_of_fiberwise`: isomorphic complex vector bundles have the same Euler
  class.
* `TauCeti.complexEulerClass_eq_neg_one_pow_smul_of_conjugateFiberwise`: a conjugate-linear
  isomorphism `E' ≅ E` gives `e(E') = (-1) ^ (r + 1) • e(E)`.

## References

* J. W. Milnor, J. D. Stasheff, *Characteristic Classes*, Annals of Mathematics Studies 76,
  Princeton (1974), §9, Property 9.1 (naturality of the Euler class under orientation-preserving
  bundle maps), §14, Lemma 14.9 (the conjugate bundle and its Chern classes).
-/

public section

noncomputable section

open Bundle Module

universe w

namespace TauCeti

/-! ### The Euler class under fibrewise isomorphisms -/

variable {B : Type w} [TopologicalSpace B] {B' : Type w} [TopologicalSpace B']
  {F : Type w} [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedSpace ℂ F] [IsScalarTower ℝ ℂ F]
  [FiniteDimensional ℂ F]
  {E : B → Type w} [TopologicalSpace (TotalSpace F E)] [∀ b, AddCommGroup (E b)]
  [∀ b, Module ℝ (E b)] [∀ b, Module ℂ (E b)] [∀ b, IsScalarTower ℝ ℂ (E b)]
  [∀ b, TopologicalSpace (E b)] [FiberBundle F E] [VectorBundle ℂ F E]
  {r : ℕ}

local instance instVectorBundleRealComplexEulerClassFiberwise : VectorBundle ℝ F E :=
  VectorBundle.restrictScalars ℝ ℂ F E

/-- The canonical orientation reindexed by `Fin (2r + 2)`, as in `complexEulerClass_def`. -/
private abbrev complexFin (hF : finrank ℂ F = r + 1) (E : B → Type w)
    [TopologicalSpace (TotalSpace F E)] [∀ b, AddCommGroup (E b)] [∀ b, Module ℝ (E b)]
    [∀ b, Module ℂ (E b)] [∀ b, IsScalarTower ℝ ℂ (E b)] [∀ b, TopologicalSpace (E b)]
    [FiberBundle F E] [VectorBundle ℂ F E] :
    letI : VectorBundle ℝ F E := VectorBundle.restrictScalars ℝ ℂ F E
    VectorBundleOrientation F E (Fin (2 * r + 1 + 1)) :=
  letI : VectorBundle ℝ F E := VectorBundle.restrictScalars ℝ ℂ F E
  VectorBundleOrientation.reindex (finCongr (by omega)) (VectorBundleOrientation.complex F E)

variable (hF : finrank ℂ F = r + 1)

section BaseMap

variable {F' : Type w} [NormedAddCommGroup F'] [NormedSpace ℝ F'] [NormedSpace ℂ F']
  [IsScalarTower ℝ ℂ F'] [FiniteDimensional ℂ F']
  {E' : B' → Type w} [TopologicalSpace (TotalSpace F' E')] [∀ b, AddCommGroup (E' b)]
  [∀ b, Module ℝ (E' b)] [∀ b, Module ℂ (E' b)] [∀ b, IsScalarTower ℝ ℂ (E' b)]
  [∀ b, TopologicalSpace (E' b)] [FiberBundle F' E'] [VectorBundle ℂ F' E']
  (hF' : finrank ℂ F' = r + 1)

local instance instVectorBundleRealComplexEulerClassFiberwise' : VectorBundle ℝ F' E' :=
  VectorBundle.restrictScalars ℝ ℂ F' E'

/-- **Naturality of the Euler class of a complex vector bundle under complex-linear bundle maps.**
For a fibrewise complex-linear isomorphism `φ b' : E'_{b'} ≃ E_{g b'}` over a continuous map
`g : B' → B`, continuous on total spaces, the Euler class of `E'` is the pull-back along `g` of the
Euler class of `E`. -/
theorem complexEulerClass_eq_singularCohomologyMap_of_fiberwise {g : C(B', B)}
    {φ : ∀ b', E' b' ≃L[ℂ] E (g b')}
    (hφ : Continuous fun v : TotalSpace F' E' ↦ TotalSpace.mk' F (g v.proj) (φ v.proj v.2)) :
    complexEulerClass F' E' hF' =
      TopCat.singularCohomologyMap (TopCat.ofHom g) (2 * r + 2) (complexEulerClass F E hF) := by
  rw [complexEulerClass_def, complexEulerClass_def]
  refine (complexFin hF E).eulerClass_eq_singularCohomologyMap_of_fiberwise _ (complexFin hF' E')
    _ (φ := fun b' ↦
      { (φ b').toLinearEquiv.restrictScalars ℝ with
        continuous_toFun := (φ b').continuous
        continuous_invFun := (φ b').symm.continuous }) hφ fun b' ↦ ?_
  rw [VectorBundleOrientation.reindex_apply, VectorBundleOrientation.reindex_apply,
    Orientation.map_reindex]
  refine (congrArg _ (VectorBundleOrientation.map_complex (F := F) (E := E) (F' := F') (E' := E')
    (φ b').toLinearEquiv)).trans ?_
  rw [← Orientation.reindex_trans]
  exact congrArg (Orientation.reindex ℝ _ · _) (Equiv.ext fun _ ↦ by simp)

/-- **Conjugate-linear bundle maps multiply the Euler class by `(-1) ^ (r + 1)`.** For a fibrewise
conjugate-linear isomorphism `φ b' : E'_{b'} ≃ E_{g b'}` over a continuous map `g : B' → B`,
continuous on total spaces, between complex vector bundles of complex rank `r + 1`, the Euler class
of `E'` is `(-1) ^ (r + 1)` times the pull-back along `g` of the Euler class of `E`. -/
theorem complexEulerClass_eq_neg_one_pow_smul_singularCohomologyMap_of_conjugateFiberwise
    {g : C(B', B)} {φ : ∀ b', E' b' ≃L⋆[ℂ] E (g b')}
    (hφ : Continuous fun v : TotalSpace F' E' ↦ TotalSpace.mk' F (g v.proj) (φ v.proj v.2)) :
    complexEulerClass F' E' hF' =
      (-1 : ℤ) ^ (r + 1) •
        TopCat.singularCohomologyMap (TopCat.ofHom g) (2 * r + 2) (complexEulerClass F E hF) := by
  rw [complexEulerClass_def, complexEulerClass_def]
  -- The real-linear continuous isomorphisms underlying the `φ b'`.
  let ψ : ∀ b', E' b' ≃L[ℝ] E (g b') := fun b' ↦
    { (φ b').toLinearEquiv.restrictScalarsₛₗ ℝ with
      continuous_toFun := by simpa using (φ b').continuous
      continuous_invFun := by simpa using (φ b').symm.continuous }
  have hψ : Continuous fun v : TotalSpace F' E' ↦ TotalSpace.mk' F (g v.proj) (ψ v.proj v.2) := by
    have h : ∀ b' v, ψ b' v = φ b' v := fun b' v ↦
      congrFun (LinearEquiv.coe_restrictScalarsₛₗ ℝ (φ b').toLinearEquiv) v
    simp only [h]
    exact hφ
  have ho : ∀ b',
      Orientation.map (Fin (2 * r + 1 + 1)) (ψ b').toLinearEquiv (complexFin hF' E' b') =
        (-1 : ℝˣ) ^ (r + 1) • complexFin hF E (g b') := fun b' ↦ by
    rw [VectorBundleOrientation.reindex_apply, VectorBundleOrientation.reindex_apply,
      Orientation.map_reindex]
    have h := VectorBundleOrientation.map_restrictScalarsₛₗ_complex (F := F) (E := E) (F' := F')
      (E' := E') (φ b').toLinearEquiv
    have hn : (-1 : ℝˣ) ^ finrank ℂ F' = (-1) ^ (r + 1) := by rw [hF']
    rw [hn] at h
    refine (congrArg _ h).trans ?_
    rw [Orientation.reindex_units_smul, ← Orientation.reindex_trans]
    exact congrArg (fun e ↦ _ • Orientation.reindex ℝ _ e _) (Equiv.ext fun _ ↦ by simp)
  rcases Nat.even_or_odd (r + 1) with hr | hr
  · rw [hr.neg_one_pow, one_smul]
    refine (complexFin hF E).eulerClass_eq_singularCohomologyMap_of_fiberwise _ (complexFin hF' E')
      _ (φ := ψ) hψ fun b' ↦ ?_
    rw [ho, hr.neg_one_pow, one_smul]
  · rw [hr.neg_one_pow, neg_one_zsmul]
    refine (complexFin hF E).eulerClass_eq_neg_singularCohomologyMap_of_fiberwise _
      (complexFin hF' E') _ (φ := ψ) hψ fun b' ↦ ?_
    rw [ho, hr.neg_one_pow, Module.Ray.neg_units_smul, one_smul]

end BaseMap

section Isomorphism

variable {F' : Type w} [NormedAddCommGroup F'] [NormedSpace ℝ F'] [NormedSpace ℂ F']
  [IsScalarTower ℝ ℂ F'] [FiniteDimensional ℂ F']
  {E' : B → Type w} [TopologicalSpace (TotalSpace F' E')] [∀ b, AddCommGroup (E' b)]
  [∀ b, Module ℝ (E' b)] [∀ b, Module ℂ (E' b)] [∀ b, IsScalarTower ℝ ℂ (E' b)]
  [∀ b, TopologicalSpace (E' b)] [FiberBundle F' E'] [VectorBundle ℂ F' E']
  (hF' : finrank ℂ F' = r + 1)

/-- **Isomorphic complex vector bundles have the same Euler class.** For a fibrewise complex-linear
isomorphism `φ b : E'_b ≃ E_b` over the same base, continuous on total spaces, the Euler classes of
`E'` and `E` agree. -/
theorem complexEulerClass_eq_of_fiberwise {φ : ∀ b, E' b ≃L[ℂ] E b}
    (hφ : Continuous fun v : TotalSpace F' E' ↦ TotalSpace.mk' F v.proj (φ v.proj v.2)) :
    complexEulerClass F' E' hF' = complexEulerClass F E hF :=
  (complexEulerClass_eq_singularCohomologyMap_of_fiberwise hF hF' (g := ContinuousMap.id B)
    hφ).trans (CategoryTheory.ConcreteCategory.congr_hom (TopCat.singularCohomologyMap_id _ _) _)

/-- **The Euler class of a conjugate bundle.** For a fibrewise conjugate-linear isomorphism
`φ b : E'_b ≃ E_b` over the same base, continuous on total spaces, between complex vector bundles of
complex rank `r + 1`, the Euler class of `E'` is `(-1) ^ (r + 1)` times that of `E`:
`e(conj E) = (-1) ^ (r + 1) e(E)`. -/
theorem complexEulerClass_eq_neg_one_pow_smul_of_conjugateFiberwise {φ : ∀ b, E' b ≃L⋆[ℂ] E b}
    (hφ : Continuous fun v : TotalSpace F' E' ↦ TotalSpace.mk' F v.proj (φ v.proj v.2)) :
    complexEulerClass F' E' hF' = (-1 : ℤ) ^ (r + 1) • complexEulerClass F E hF := by
  rw [complexEulerClass_eq_neg_one_pow_smul_singularCohomologyMap_of_conjugateFiberwise hF hF'
    (g := ContinuousMap.id B) hφ]
  exact congrArg _ (CategoryTheory.ConcreteCategory.congr_hom
    (TopCat.singularCohomologyMap_id _ _) _)

/-- **The Euler class of the conjugate of a complex line bundle is the negative**: for a fibrewise
conjugate-linear isomorphism `φ b : E'_b ≃ E_b` between complex line bundles, continuous on total
spaces, `e(E') = -e(E)`, that is `e(conj L) = -e(L)`. -/
theorem complexEulerClass_eq_neg_of_finrank_eq_one_of_conjugateFiberwise
    (hF : finrank ℂ F = 0 + 1) (hF' : finrank ℂ F' = 0 + 1) {φ : ∀ b, E' b ≃L⋆[ℂ] E b}
    (hφ : Continuous fun v : TotalSpace F' E' ↦ TotalSpace.mk' F v.proj (φ v.proj v.2)) :
    complexEulerClass F' E' hF' = -complexEulerClass F E hF := by
  rw [complexEulerClass_eq_neg_one_pow_smul_of_conjugateFiberwise hF hF' hφ, pow_one,
    neg_one_zsmul]

end Isomorphism

end TauCeti
