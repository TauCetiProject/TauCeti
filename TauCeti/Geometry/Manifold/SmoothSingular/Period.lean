/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Singular.ModuleChains.HomologyCross
public import TauCeti.Geometry.Manifold.DeRham.Map
public import TauCeti.Geometry.Manifold.SmoothSingular.Smoothing
public import TauCeti.Geometry.Manifold.SmoothSingular.Stokes

/-!
# Periods of closed forms on integral singular homology

Let `M` be a Hausdorff `σ`-compact smooth manifold modelled on a finite-dimensional real space.
A closed smooth real `k`-form `φ` on `M` has a **period** on every integral singular homology
class `c ∈ H_k(M; ℤ)`, the integral of `φ` over a smooth cycle representing `c`:

`TauCeti.homologyIntegral φ : H_k(M; ℤ) →+ ℝ`.

It is built in two steps. On integral smooth singular chains, integration of `φ` over each smooth
simplex extends linearly to the cochain `TauCeti.intIntegrationCochain φ`. By Stokes' theorem it
vanishes on boundaries when `φ` is closed, so it descends to the integral smooth singular homology
of `M` (`TauCeti.smoothHomologyIntegral φ`). The smoothing theorem identifies smooth singular
homology with singular homology (`TauCeti.smoothSingularHomologyIso`); precomposing with the inverse
of this identification gives the period on `H_k(M; ℤ)`. On the image of the class of a smooth
cycle `Σ nᵢ σᵢ` the period is `Σ nᵢ ∫_{σᵢ} φ`
(`TauCeti.homologyIntegral_homologyMap_ι_homologyπ`).

The period is additive and homogeneous in the form, vanishes for exact forms, and is natural: for a
smooth map `f : M → N`, the periods of `f^* φ` are those of `φ` composed with the induced map
`f_* : H_k(M; ℤ) → H_k(N; ℤ)` (`TauCeti.homologyIntegral_mpullback`). Combined with the vanishing
of `pr₂_* (a × b)` for a class `a` of positive degree
(`TopCat.singularHomologyMap_snd_singularHomologyCrossBilinear_eq_zero`), naturality shows that a
closed form pulled back from the second factor of a product `A × B` has zero period on every cross
product `a × b` with `a` of positive degree
(`TauCeti.homologyIntegral_mpullback_snd_singularHomologyCrossBilinear`). For instance, on
`S¹ × Y` such a form pairs to zero with the summand `[S¹] × H_(k-1)(Y; ℤ)` of `H_k(S¹ × Y; ℤ)`.

In degree one, `TauCeti.homologyPeriodHom` instead integrates closed one-forms along the
continuous paths traced by singular `1`-simplices, which needs no smoothing; this file does not
compare the two constructions.

## Main definitions

* `TauCeti.intIntegrationCochain φ`: integration of a form over integral smooth singular chains.
* `TauCeti.smoothHomologyIntegral φ`: the period of a closed form on integral smooth singular
  homology.
* `TauCeti.homologyIntegral φ`: the period of a closed form on integral singular homology.

## Main results

* `TauCeti.homologyIntegral_homologyMap_ι_homologyπ`: the period on the class of a smooth cycle
  is the integral over the cycle.
* `TauCeti.homologyIntegral_add`, `TauCeti.homologyIntegral_smul`: linearity in the form.
* `TauCeti.homologyIntegral_eq_zero_of_mem_exactForms`: exact forms have zero periods.
* `TauCeti.homologyIntegral_mpullback`: naturality under smooth maps.
* `TauCeti.homologyIntegral_mpullback_snd_singularHomologyCrossBilinear`: a closed form pulled
  back from the second factor has zero period on cross products with a positive-degree class of
  the first factor.

## References

* John M. Lee, *Introduction to Smooth Manifolds*, 2nd ed., Chapter 18 (integration over smooth
  chains, the smoothing theorem and the de Rham homomorphism).
* A. Hatcher, *Algebraic Topology*, Section 3.B (the homology cross product).
-/

public section

noncomputable section

open CategoryTheory Opposite Simplicial
open scoped Manifold ContDiff

namespace TauCeti

variable {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} {M : Type} [TopologicalSpace M] [ChartedSpace H M] {k : ℕ}

/-! ### Integration over integral smooth chains -/

section Cochain

/-- Integration of a real `k`-form over integral smooth singular `k`-chains: the integer linear
extension of the integral over smooth simplices. -/
def intIntegrationCochain (φ : RoughForm I M ℝ k) :
    ((smoothSingularSubcomplex I M : SSet).chainComplex (ModuleCat.of ℤ ℤ)).X k ⟶
      ModuleCat.of ℤ ℝ :=
  ModuleCat.ofHom ((Finsupp.linearCombination ℤ (fun σ : SmoothSimplex I M k ↦ σ.integral φ)).comp
    (SSet.chainsLinearEquivFinsupp _ ℤ k).toLinearMap)

/-- The integral cochain takes a simplex with coefficient `n` to `n` times its integral. -/
@[simp]
theorem intIntegrationCochain_ιChainComplex (φ : RoughForm I M ℝ k) (σ : SmoothSimplex I M k)
    (n : ℤ) :
    (intIntegrationCochain φ).hom (((smoothSingularSubcomplex I M : SSet).ιChainComplex
      (R := ModuleCat.of ℤ ℤ) σ).hom n) = n • σ.integral φ := by
  rw [intIntegrationCochain, ModuleCat.hom_ofHom, LinearMap.comp_apply,
    LinearEquiv.coe_toLinearMap, SSet.chainsLinearEquivFinsupp_ιChainComplex,
    Finsupp.linearCombination_single]

/-- On the summand of a simplex, the integral cochain is multiplication by its integral. -/
@[reassoc (attr := simp)]
theorem ιChainComplex_intIntegrationCochain (φ : RoughForm I M ℝ k) (σ : SmoothSimplex I M k) :
    (smoothSingularSubcomplex I M : SSet).ιChainComplex (R := ModuleCat.of ℤ ℤ) σ ≫
      intIntegrationCochain φ = ModuleCat.ofHom (LinearMap.toSpanSingleton ℤ ℝ (σ.integral φ)) :=
  ModuleCat.hom_ext (LinearMap.ext_ring (by simpa using intIntegrationCochain_ιChainComplex φ σ 1))

/-- Integrating the zero form gives the zero cochain. -/
@[simp]
theorem intIntegrationCochain_zero : intIntegrationCochain (0 : RoughForm I M ℝ k) = 0 :=
  SSet.chainComplex_hom_ext fun σ ↦ by
    rw [ιChainComplex_intIntegrationCochain, SmoothSimplex.integral_zero, Limits.comp_zero,
      LinearMap.toSpanSingleton_zero, ModuleCat.ofHom_zero]

/-- Integration over integral smooth chains is homogeneous in the form. -/
theorem intIntegrationCochain_smul_apply (a : ℝ) (φ : RoughForm I M ℝ k)
    (c : ((smoothSingularSubcomplex I M : SSet).chainComplex (ModuleCat.of ℤ ℤ)).X k) :
    (intIntegrationCochain (a • φ)).hom c = a • (intIntegrationCochain φ).hom c := by
  refine LinearMap.congr_fun ((smoothSingularSubcomplex I M : SSet).chainComplex_linearMap_ext
    (L' := a • (intIntegrationCochain φ).hom) fun σ n ↦ ?_) c
  rw [LinearMap.smul_apply, intIntegrationCochain_ιChainComplex,
    intIntegrationCochain_ιChainComplex, SmoothSimplex.integral_smul, smul_comm]

/-- Integration over integral smooth chains is additive on continuous forms. -/
theorem intIntegrationCochain_add [IsManifold I 1 M] {φ ψ : RoughForm I M ℝ k}
    (hφ : IsSmoothForm I 0 φ) (hψ : IsSmoothForm I 0 ψ) :
    intIntegrationCochain (φ + ψ) = intIntegrationCochain φ + intIntegrationCochain ψ := by
  refine SSet.chainComplex_hom_ext fun σ ↦ ?_
  rw [Preadditive.comp_add, ιChainComplex_intIntegrationCochain,
    ιChainComplex_intIntegrationCochain, ιChainComplex_intIntegrationCochain,
    SmoothSimplex.integral_add σ hφ hψ, LinearMap.toSpanSingleton_add, ModuleCat.ofHom_add]

/-- **Stokes' theorem on integral smooth chains.** Integrating a `C¹` form over the boundary of an
integral smooth chain is integrating its exterior derivative over the chain. -/
theorem d_comp_intIntegrationCochain [IsManifold I 2 M] {φ : RoughForm I M ℝ k}
    (hφ : IsSmoothForm I 1 φ) :
    ((smoothSingularSubcomplex I M : SSet).chainComplex (ModuleCat.of ℤ ℤ)).d (k + 1) k ≫
      intIntegrationCochain φ = intIntegrationCochain (mextDeriv φ) := by
  refine SSet.chainComplex_hom_ext fun σ ↦ ModuleCat.hom_ext (LinearMap.ext_ring ?_)
  simp only [SSet.ιChainComplex_d_assoc, Preadditive.sum_comp, Preadditive.zsmul_comp,
    ιChainComplex_intIntegrationCochain, ModuleCat.hom_sum, ModuleCat.hom_zsmul,
    ModuleCat.hom_ofHom, LinearMap.sum_apply, LinearMap.smul_apply,
    LinearMap.toSpanSingleton_apply, one_smul, SmoothSimplex.integral_mextDeriv σ hφ]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [zsmul_eq_mul, smul_eq_mul, Int.cast_pow, Int.cast_neg, Int.cast_one]

/-- The integral cochain of a closed smooth form vanishes on boundaries. -/
theorem d_comp_intIntegrationCochain_eq_zero [IsManifold I 2 M] (φ : closedForms I M k) :
    ((smoothSingularSubcomplex I M : SSet).chainComplex (ModuleCat.of ℤ ℤ)).d (k + 1) k ≫
      intIntegrationCochain φ.1.1 = 0 := by
  rw [d_comp_intIntegrationCochain (φ.1.isSmoothForm.of_le (by exact_mod_cast le_top)),
    (mem_closedForms I φ.1).mp φ.2, intIntegrationCochain_zero]

variable {E' H' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E'] [TopologicalSpace H']
  {J : ModelWithCorners ℝ E' H'} {N : Type} [TopologicalSpace N] [ChartedSpace H' N]

/-- The integral cochain is natural for the chain map induced by a smooth map. -/
@[reassoc]
theorem intIntegrationCochain_naturality {f : M → N} (hf : ContMDiff I J ∞ f)
    (ψ : RoughForm J N ℝ k) :
    (SSet.chainComplexMap (smoothSingularSubcomplexMap f hf) (ModuleCat.of ℤ ℤ)).f k ≫
      intIntegrationCochain ψ = intIntegrationCochain (mpullback I J f ψ) := by
  refine SSet.chainComplex_hom_ext fun σ ↦ ?_
  rw [SSet.ι_chainComplexMap_f_assoc, ιChainComplex_intIntegrationCochain,
    ιChainComplex_intIntegrationCochain, SmoothSimplex.integral_smoothSingularSubcomplexMap_app]

end Cochain

/-! ### Periods on smooth singular homology -/

section Smooth

variable [IsManifold I 2 M]

/-- The **period of a closed form on integral smooth singular homology**: integration over smooth
cycles, which is well defined on homology classes by Stokes' theorem. -/
def smoothHomologyIntegral (φ : closedForms I M k) :
    (smoothSingularSubcomplex I M : SSet).homology (ModuleCat.of ℤ ℤ) k ⟶ ModuleCat.of ℤ ℝ :=
  ((smoothSingularSubcomplex I M : SSet).chainComplex (ModuleCat.of ℤ ℤ)).homologyι k ≫
    ((smoothSingularSubcomplex I M : SSet).chainComplex (ModuleCat.of ℤ ℤ)).descOpcycles
      (intIntegrationCochain φ.1.1) (k + 1) (by simp) (d_comp_intIntegrationCochain_eq_zero φ)

/-- The period of a closed form on the class of a smooth cycle is its integral over the cycle. -/
@[reassoc (attr := simp)]
theorem homologyπ_smoothHomologyIntegral (φ : closedForms I M k) :
    ((smoothSingularSubcomplex I M : SSet).chainComplex (ModuleCat.of ℤ ℤ)).homologyπ k ≫
        smoothHomologyIntegral φ =
      ((smoothSingularSubcomplex I M : SSet).chainComplex (ModuleCat.of ℤ ℤ)).iCycles k ≫
        intIntegrationCochain φ.1.1 := by
  rw [smoothHomologyIntegral, HomologicalComplex.homology_π_ι_assoc,
    HomologicalComplex.p_descOpcycles]

omit [IsManifold I 2 M] in
/-- Every class of integral smooth singular homology is the class of a cycle. -/
private theorem smoothHomologyπ_surjective :
    Function.Surjective (((smoothSingularSubcomplex I M : SSet).chainComplex
      (ModuleCat.of ℤ ℤ)).homologyπ k).hom :=
  (ModuleCat.epi_iff_surjective _).1 inferInstance

/-- The periods of a sum of closed forms are the sums of their periods. -/
theorem smoothHomologyIntegral_add (φ ψ : closedForms I M k) :
    smoothHomologyIntegral (φ + ψ) = smoothHomologyIntegral φ + smoothHomologyIntegral ψ := by
  rw [← cancel_epi (((smoothSingularSubcomplex I M : SSet).chainComplex
    (ModuleCat.of ℤ ℤ)).homologyπ k), Preadditive.comp_add, homologyπ_smoothHomologyIntegral,
    homologyπ_smoothHomologyIntegral, homologyπ_smoothHomologyIntegral, ← Preadditive.comp_add]
  exact congrArg _ (intIntegrationCochain_add (φ.1.isSmoothForm.of_le (by simp))
    (ψ.1.isSmoothForm.of_le (by simp)))

/-- The periods of a real multiple of a closed form are the multiples of its periods. -/
theorem smoothHomologyIntegral_smul_apply (a : ℝ) (φ : closedForms I M k)
    (c : ((smoothSingularSubcomplex I M : SSet).chainComplex (ModuleCat.of ℤ ℤ)).homology k) :
    (smoothHomologyIntegral (a • φ)).hom c = a • (smoothHomologyIntegral φ).hom c := by
  obtain ⟨z, rfl⟩ := smoothHomologyπ_surjective c
  rw [← ModuleCat.comp_apply, homologyπ_smoothHomologyIntegral, ← ModuleCat.comp_apply,
    homologyπ_smoothHomologyIntegral, ModuleCat.comp_apply, ModuleCat.comp_apply]
  exact intIntegrationCochain_smul_apply a φ.1.1 _

/-- Exact forms have zero periods on smooth singular homology. -/
theorem smoothHomologyIntegral_eq_zero_of_mem_exactForms (φ : closedForms I M k)
    (hφ : φ.1 ∈ exactForms I M k) : smoothHomologyIntegral φ = 0 := by
  rw [← cancel_epi (((smoothSingularSubcomplex I M : SSet).chainComplex
    (ModuleCat.of ℤ ℤ)).homologyπ k), homologyπ_smoothHomologyIntegral, Limits.comp_zero]
  cases k with
  | zero =>
    rw [exactForms_zero, Submodule.mem_bot] at hφ
    rw [hφ, ZeroMemClass.coe_zero, intIntegrationCochain_zero, Limits.comp_zero]
  | succ k =>
    rw [exactForms_succ, LinearMap.mem_range] at hφ
    obtain ⟨ψ, hψ⟩ := hφ
    rw [← hψ, mextDerivₗ_apply, ← d_comp_intIntegrationCochain
      (ψ.isSmoothForm.of_le (by exact_mod_cast le_top)), HomologicalComplex.iCycles_d_assoc,
      Limits.zero_comp]

variable {E' H' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E'] [TopologicalSpace H']
  {J : ModelWithCorners ℝ E' H'} {N : Type} [TopologicalSpace N] [ChartedSpace H' N]
  [IsManifold J 2 N]

/-- The periods on smooth singular homology are natural under smooth maps. -/
@[reassoc]
theorem homologyMap_smoothHomologyIntegral {f : M → N} (hf : ContMDiff I J ∞ f)
    (φ : closedForms J N k) :
    SSet.homologyMap (smoothSingularSubcomplexMap f hf) (ModuleCat.of ℤ ℤ) k ≫
        smoothHomologyIntegral φ =
      smoothHomologyIntegral (closedForms.mpullback f hf k φ) := by
  rw [← cancel_epi (((smoothSingularSubcomplex I M : SSet).chainComplex
    (ModuleCat.of ℤ ℤ)).homologyπ k), HomologicalComplex.homologyπ_naturality_assoc,
    homologyπ_smoothHomologyIntegral, homologyπ_smoothHomologyIntegral,
    HomologicalComplex.cyclesMap_i_assoc, intIntegrationCochain_naturality,
    closedForms.coe_mpullback, SmoothForm.coe_mpullback]

end Smooth

/-! ### Periods on singular homology -/

section Singular

variable [FiniteDimensional ℝ E] [T2Space M] [SigmaCompactSpace M] [IsManifold I ∞ M]

/-- The **period of a closed form on integral singular homology** `H_k(M; ℤ)`: the period on
smooth singular homology, transported along the smoothing isomorphism. On the class of a smooth
cycle `Σ nᵢ σᵢ` it is `Σ nᵢ ∫_{σᵢ} φ`. -/
def homologyIntegral (φ : closedForms I M k) :
    ((singularChains ℤ).obj (TopCat.of M)).homology k →+ ℝ :=
  ((smoothSingularHomologyIso I M (ModuleCat.of ℤ ℤ) k).inv ≫
    smoothHomologyIntegral φ).hom.toAddMonoidHom

/-- The period of a closed form on `H_k(M; ℤ)` is its period on smooth singular homology,
evaluated on the preimage under the smoothing isomorphism. -/
theorem homologyIntegral_apply (φ : closedForms I M k)
    (c : ((singularChains ℤ).obj (TopCat.of M)).homology k) :
    homologyIntegral φ c =
      (smoothHomologyIntegral φ).hom
        ((smoothSingularHomologyIso I M (ModuleCat.of ℤ ℤ) k).inv.hom c) :=
  (rfl)

/-- The period of a closed form on the image of a smooth singular homology class is its period on
that class. -/
@[simp]
theorem homologyIntegral_homologyMap_ι (φ : closedForms I M k)
    (c : ((smoothSingularSubcomplex I M : SSet).chainComplex (ModuleCat.of ℤ ℤ)).homology k) :
    homologyIntegral φ
        ((SSet.homologyMap (smoothSingularSubcomplex I M).ι (ModuleCat.of ℤ ℤ) k).hom c) =
      (smoothHomologyIntegral φ).hom c := by
  rw [← smoothSingularHomologyIso_hom]
  -- The singular chains `singularChains ℤ` are by definition the simplicial chains of the singular
  -- simplicial set, so `homologyIntegral_apply` applies to the image of the smoothing isomorphism.
  exact (homologyIntegral_apply φ _).trans <| by simp only [Iso.hom_inv_id_apply]

/-- The period of a closed form on the class of a smooth cycle `z` is the integral of the form
over `z`. -/
theorem homologyIntegral_homologyMap_ι_homologyπ (φ : closedForms I M k)
    (z : ((smoothSingularSubcomplex I M : SSet).chainComplex (ModuleCat.of ℤ ℤ)).cycles k) :
    homologyIntegral φ ((SSet.homologyMap (smoothSingularSubcomplex I M).ι (ModuleCat.of ℤ ℤ) k).hom
        ((((smoothSingularSubcomplex I M : SSet).chainComplex
          (ModuleCat.of ℤ ℤ)).homologyπ k).hom z)) =
      (intIntegrationCochain φ.1.1).hom ((((smoothSingularSubcomplex I M : SSet).chainComplex
        (ModuleCat.of ℤ ℤ)).iCycles k).hom z) := by
  rw [homologyIntegral_homologyMap_ι, ← ModuleCat.comp_apply,
    homologyπ_smoothHomologyIntegral, ModuleCat.comp_apply]

/-- The periods of a sum of closed forms are the sums of their periods. -/
@[simp]
theorem homologyIntegral_add (φ ψ : closedForms I M k) :
    homologyIntegral (φ + ψ) = homologyIntegral φ + homologyIntegral ψ := by
  ext c
  rw [AddMonoidHom.add_apply, homologyIntegral_apply, homologyIntegral_apply,
    homologyIntegral_apply, smoothHomologyIntegral_add, ModuleCat.hom_add, LinearMap.add_apply]

/-- The periods of a real multiple of a closed form are the multiples of its periods. -/
@[simp]
theorem homologyIntegral_smul (a : ℝ) (φ : closedForms I M k) :
    homologyIntegral (a • φ) = a • homologyIntegral φ := by
  ext c
  rw [AddMonoidHom.smul_apply, homologyIntegral_apply, homologyIntegral_apply,
    smoothHomologyIntegral_smul_apply]

/-- **Exact forms have zero periods.** -/
theorem homologyIntegral_eq_zero_of_mem_exactForms (φ : closedForms I M k)
    (hφ : φ.1 ∈ exactForms I M k) : homologyIntegral φ = 0 := by
  ext c
  rw [homologyIntegral_apply, smoothHomologyIntegral_eq_zero_of_mem_exactForms φ hφ,
    ModuleCat.hom_zero, LinearMap.zero_apply, AddMonoidHom.zero_apply]

variable {E' H' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E'] [FiniteDimensional ℝ E']
  [TopologicalSpace H'] {J : ModelWithCorners ℝ E' H'} {N : Type} [TopologicalSpace N]
  [ChartedSpace H' N] [T2Space N] [SigmaCompactSpace N] [IsManifold J ∞ N]

/-- **Naturality of the periods.** For a smooth map `f : M → N`, the periods of the pullback
`f^* φ` are the periods of `φ` on the images under `f_* : H_k(M; ℤ) → H_k(N; ℤ)`. -/
theorem homologyIntegral_mpullback {f : M → N} (hf : ContMDiff I J ∞ f) (φ : closedForms J N k)
    (c : ((singularChains ℤ).obj (TopCat.of M)).homology k) :
    homologyIntegral (closedForms.mpullback f hf k φ) c =
      homologyIntegral φ (ContinuousMap.singularHomologyMap ℤ k ⟨f, hf.continuous⟩ c) := by
  have h := ConcreteCategory.congr_hom
    (smoothSingularHomologyIso_inv_naturality (ModuleCat.of ℤ ℤ) hf k) c
  rw [homologyIntegral_apply, ← homologyMap_smoothHomologyIntegral hf, ModuleCat.comp_apply]
  -- The singular chains `singularChains ℤ` are by definition the simplicial chains of the singular
  -- simplicial set, so the simplicial homology map in `h` is `singularHomologyMap`.
  exact (congrArg (smoothHomologyIntegral φ).hom h).trans (homologyIntegral_apply φ _).symm

variable {E'' H'' : Type*} [NormedAddCommGroup E''] [NormedSpace ℝ E''] [FiniteDimensional ℝ E'']
  [TopologicalSpace H''] {K : ModelWithCorners ℝ E'' H''} {A : Type} [TopologicalSpace A]
  [ChartedSpace H'' A] [T2Space A] [SigmaCompactSpace A] [IsManifold K ∞ A]

/-- **A form pulled back from the second factor vanishes on cross products.** On a product
`A × B`, a closed form `pr₂^* φ` pulled back from `B` has zero period on every cross product
`a × b` of a class `a ∈ H_p(A; ℤ)` of positive degree with a class `b ∈ H_q(B; ℤ)`. -/
@[simp]
theorem homologyIntegral_mpullback_snd_singularHomologyCrossBilinear {p q : ℕ} (h : p + q = k)
    (hp : p ≠ 0) (φ : closedForms J N k) (a : ((singularChains ℤ).obj (TopCat.of A)).homology p)
    (b : ((singularChains ℤ).obj (TopCat.of N)).homology q) :
    homologyIntegral (closedForms.mpullback Prod.snd (contMDiff_snd (I := K)) k φ)
      (TopCat.singularHomologyCrossBilinear ℤ (TopCat.of A) (TopCat.of N) p q k h a b) = 0 := by
  rw [homologyIntegral_mpullback]
  exact (congrArg (homologyIntegral φ)
    (TopCat.singularHomologyMap_snd_singularHomologyCrossBilinear_eq_zero ℤ h hp a b)).trans
      (map_zero _)

end Singular

end TauCeti
