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

`TauCeti.closedFormHomologyPeriod φ : H_k(M; ℤ) →+ ℝ`.

It is built in two steps. On integral smooth singular chains, integration of `φ` is the integration
cochain `TauCeti.integrationCochain (R := ℤ) φ`. By Stokes' theorem it vanishes on boundaries when
`φ` is closed, so it descends to the integral smooth singular homology of `M`
(`TauCeti.smoothHomologyPeriod φ`). The smoothing theorem identifies smooth singular homology with
singular homology (`TauCeti.smoothSingularHomologyIso`); precomposing with the inverse of this
identification gives the period on `H_k(M; ℤ)`. On the image of the class of a smooth cycle
`Σ nᵢ σᵢ` the period is `Σ nᵢ ∫_{σᵢ} φ`
(`TauCeti.closedFormHomologyPeriod_homologyMap_ι_homologyπ`).

The period is additive and homogeneous in the form, vanishes for exact forms, and is natural: for a
smooth map `f : M → N`, the periods of `f^* φ` are those of `φ` composed with the induced map
`f_* : H_k(M; ℤ) → H_k(N; ℤ)` (`TauCeti.closedFormHomologyPeriod_mpullback`). Combined with the
vanishing of `pr₂_* (a × b)` for a class `a` of positive degree
(`TopCat.singularHomologyMap_snd_singularHomologyCrossBilinear_eq_zero`), naturality shows that a
closed form pulled back from the second factor of a product `A × B` has zero period on every cross
product `a × b` with `a` of positive degree
(`TauCeti.closedFormHomologyPeriod_mpullback_snd_singularHomologyCrossBilinear_eq_zero`). For
instance, on `S¹ × Y` such a form pairs to zero with the summand `[S¹] × H_(k-1)(Y; ℤ)` of
`H_k(S¹ × Y; ℤ)`.

In degree one, `TauCeti.homologyPeriodHom` instead integrates closed one-forms along the
continuous paths traced by singular `1`-simplices, which needs no smoothing; this file does not
compare the two constructions.

## Main definitions

* `TauCeti.smoothHomologyPeriod φ`: the period of a closed form on integral smooth singular
  homology.
* `TauCeti.closedFormHomologyPeriod φ`: the period of a closed form on integral singular homology.

## Main results

* `TauCeti.closedFormHomologyPeriod_homologyMap_ι_homologyπ`: the period on the class of a smooth
  cycle is the integral over the cycle.
* `TauCeti.closedFormHomologyPeriod_add`, `TauCeti.closedFormHomologyPeriod_smul`: linearity in the
  form.
* `TauCeti.closedFormHomologyPeriod_eq_zero_of_mem_exactForms`: exact forms have zero periods.
* `TauCeti.closedFormHomologyPeriod_mpullback`: naturality under smooth maps.
* `TauCeti.closedFormHomologyPeriod_mpullback_snd_singularHomologyCrossBilinear_eq_zero`: a closed
  form pulled back from the second factor has zero period on cross products with a positive-degree
  class of the first factor.

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

/-! ### Periods on smooth singular homology -/

section Smooth

variable [IsManifold I 2 M]

/-- The **period of a closed form on integral smooth singular homology**: integration over smooth
cycles, which is well defined on homology classes by Stokes' theorem. -/
def smoothHomologyPeriod (φ : closedForms I M k) :
    (smoothSingularSubcomplex I M : SSet).homology (ModuleCat.of ℤ ℤ) k ⟶ ModuleCat.of ℤ ℝ :=
  ((smoothSingularSubcomplex I M : SSet).chainComplex (ModuleCat.of ℤ ℤ)).homologyι k ≫
    ((smoothSingularSubcomplex I M : SSet).chainComplex (ModuleCat.of ℤ ℤ)).descOpcycles
      (integrationCochain φ.1.1) (k + 1) (by simp)
      (d_comp_integrationCochain_eq_zero (φ.1.isSmoothForm.of_le (by exact_mod_cast le_top))
        ((mem_closedForms I φ.1).mp φ.2))

/-- The period of a closed form on the class of a smooth cycle is its integral over the cycle. -/
@[reassoc (attr := simp)]
theorem homologyπ_smoothHomologyPeriod (φ : closedForms I M k) :
    ((smoothSingularSubcomplex I M : SSet).chainComplex (ModuleCat.of ℤ ℤ)).homologyπ k ≫
        smoothHomologyPeriod φ =
      ((smoothSingularSubcomplex I M : SSet).chainComplex (ModuleCat.of ℤ ℤ)).iCycles k ≫
        integrationCochain φ.1.1 := by
  simp [smoothHomologyPeriod]

omit [IsManifold I 2 M] in
/-- Every class of integral smooth singular homology is the class of a cycle. -/
private theorem smoothHomologyπ_surjective :
    Function.Surjective (((smoothSingularSubcomplex I M : SSet).chainComplex
      (ModuleCat.of ℤ ℤ)).homologyπ k).hom :=
  (ModuleCat.epi_iff_surjective _).1 inferInstance

/-- The periods of a sum of closed forms are the sums of their periods. -/
theorem smoothHomologyPeriod_add (φ ψ : closedForms I M k) :
    smoothHomologyPeriod (φ + ψ) = smoothHomologyPeriod φ + smoothHomologyPeriod ψ := by
  rw [← cancel_epi (((smoothSingularSubcomplex I M : SSet).chainComplex
    (ModuleCat.of ℤ ℤ)).homologyπ k)]
  simp [integrationCochain_add (φ.1.isSmoothForm.of_le (by simp))
    (ψ.1.isSmoothForm.of_le (by simp))]

/-- The periods of a real multiple of a closed form are the multiples of its periods. -/
theorem smoothHomologyPeriod_smul_apply (a : ℝ) (φ : closedForms I M k)
    (c : ((smoothSingularSubcomplex I M : SSet).chainComplex (ModuleCat.of ℤ ℤ)).homology k) :
    (smoothHomologyPeriod (a • φ)).hom c = a • (smoothHomologyPeriod φ).hom c := by
  obtain ⟨z, rfl⟩ := smoothHomologyπ_surjective c
  rw [← ModuleCat.comp_apply, homologyπ_smoothHomologyPeriod, ← ModuleCat.comp_apply,
    homologyπ_smoothHomologyPeriod, ModuleCat.comp_apply, ModuleCat.comp_apply]
  exact integrationCochain_smul_apply a φ.1.1 _

/-- Exact forms have zero periods on smooth singular homology. -/
theorem smoothHomologyPeriod_eq_zero_of_mem_exactForms (φ : closedForms I M k)
    (hφ : φ.1 ∈ exactForms I M k) : smoothHomologyPeriod φ = 0 := by
  rw [← cancel_epi (((smoothSingularSubcomplex I M : SSet).chainComplex
    (ModuleCat.of ℤ ℤ)).homologyπ k), homologyπ_smoothHomologyPeriod, Limits.comp_zero]
  cases k with
  | zero =>
    rw [exactForms_zero, Submodule.mem_bot] at hφ
    simp [hφ]
  | succ k =>
    rw [exactForms_succ, LinearMap.mem_range] at hφ
    obtain ⟨ψ, hψ⟩ := hφ
    rw [← hψ, mextDerivₗ_apply, ← d_comp_integrationCochain
      (ψ.isSmoothForm.of_le (by exact_mod_cast le_top)), HomologicalComplex.iCycles_d_assoc,
      Limits.zero_comp]

variable {E' H' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E'] [TopologicalSpace H']
  {J : ModelWithCorners ℝ E' H'} {N : Type} [TopologicalSpace N] [ChartedSpace H' N]
  [IsManifold J 2 N]

/-- The periods on smooth singular homology are natural under smooth maps. -/
@[reassoc]
theorem homologyMap_smoothHomologyPeriod {f : M → N} (hf : ContMDiff I J ∞ f)
    (φ : closedForms J N k) :
    SSet.homologyMap (smoothSingularSubcomplexMap f hf) (ModuleCat.of ℤ ℤ) k ≫
        smoothHomologyPeriod φ =
      smoothHomologyPeriod (closedForms.mpullback f hf k φ) := by
  rw [← cancel_epi (((smoothSingularSubcomplex I M : SSet).chainComplex
    (ModuleCat.of ℤ ℤ)).homologyπ k), HomologicalComplex.homologyπ_naturality_assoc,
    homologyπ_smoothHomologyPeriod, homologyπ_smoothHomologyPeriod,
    HomologicalComplex.cyclesMap_i_assoc, integrationCochain_naturality,
    closedForms.coe_mpullback, SmoothForm.coe_mpullback]

end Smooth

/-! ### Periods on singular homology -/

/-- The map induced on singular homology by a continuous map is the map induced on the homology of
the singular simplicial sets: `singularChains k` is by definition the simplicial chain complex of
`TopCat.toSSet`. This identifies the smoothing isomorphism, stated for `TopCat.toSSet`, with
singular homology. -/
theorem _root_.ContinuousMap.singularHomologyMap_eq_homologyMap_toSSet_map {R : Type} [Ring R]
    {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y] (g : C(X, Y)) :
    ContinuousMap.singularHomologyMap R k g =
      (SSet.homologyMap (TopCat.toSSet.map (TopCat.ofHom g)) (ModuleCat.of R R) k).hom :=
  rfl

section Singular

variable [FiniteDimensional ℝ E] [T2Space M] [SigmaCompactSpace M] [IsManifold I ∞ M]

/-- The **period of a closed form on integral singular homology** `H_k(M; ℤ)`: the period on
smooth singular homology, transported along the smoothing isomorphism. On the class of a smooth
cycle `Σ nᵢ σᵢ` it is `Σ nᵢ ∫_{σᵢ} φ`. -/
def closedFormHomologyPeriod (φ : closedForms I M k) :
    ((singularChains ℤ).obj (TopCat.of M)).homology k →+ ℝ :=
  ((smoothSingularHomologyIso I M (ModuleCat.of ℤ ℤ) k).inv ≫
    smoothHomologyPeriod φ).hom.toAddMonoidHom

/-- The period of a closed form on `H_k(M; ℤ)` is its period on smooth singular homology,
evaluated on the preimage under the smoothing isomorphism. -/
theorem closedFormHomologyPeriod_apply (φ : closedForms I M k)
    (c : ((singularChains ℤ).obj (TopCat.of M)).homology k) :
    closedFormHomologyPeriod φ c =
      (smoothHomologyPeriod φ).hom
        ((smoothSingularHomologyIso I M (ModuleCat.of ℤ ℤ) k).inv.hom c) :=
  (rfl)

/-- The period of a closed form on the image of a smooth singular homology class is its period on
that class. -/
@[simp]
theorem closedFormHomologyPeriod_homologyMap_ι (φ : closedForms I M k)
    (c : ((smoothSingularSubcomplex I M : SSet).chainComplex (ModuleCat.of ℤ ℤ)).homology k) :
    closedFormHomologyPeriod φ
        ((SSet.homologyMap (smoothSingularSubcomplex I M).ι (ModuleCat.of ℤ ℤ) k).hom c) =
      (smoothHomologyPeriod φ).hom c := by
  rw [← smoothSingularHomologyIso_hom]
  -- The class lies in the homology of `TopCat.toSSet`, which is the homology of `singularChains ℤ`
  -- by definition; this is the identification that types the statement itself.
  exact (closedFormHomologyPeriod_apply φ _).trans (congrArg _ (Iso.hom_inv_id_apply _ _))

/-- The period of a closed form on the class of a smooth cycle `z` is the integral of the form
over `z`. -/
theorem closedFormHomologyPeriod_homologyMap_ι_homologyπ (φ : closedForms I M k)
    (z : ((smoothSingularSubcomplex I M : SSet).chainComplex (ModuleCat.of ℤ ℤ)).cycles k) :
    closedFormHomologyPeriod φ
        ((SSet.homologyMap (smoothSingularSubcomplex I M).ι (ModuleCat.of ℤ ℤ) k).hom
          ((((smoothSingularSubcomplex I M : SSet).chainComplex
            (ModuleCat.of ℤ ℤ)).homologyπ k).hom z)) =
      (integrationCochain φ.1.1).hom ((((smoothSingularSubcomplex I M : SSet).chainComplex
        (ModuleCat.of ℤ ℤ)).iCycles k).hom z) := by
  rw [closedFormHomologyPeriod_homologyMap_ι, ← ModuleCat.comp_apply,
    homologyπ_smoothHomologyPeriod, ModuleCat.comp_apply]

/-- The periods of a sum of closed forms are the sums of their periods. -/
@[simp]
theorem closedFormHomologyPeriod_add (φ ψ : closedForms I M k) :
    closedFormHomologyPeriod (φ + ψ) = closedFormHomologyPeriod φ + closedFormHomologyPeriod ψ := by
  ext c
  simp [closedFormHomologyPeriod_apply, smoothHomologyPeriod_add]

/-- The periods of a real multiple of a closed form are the multiples of its periods. -/
@[simp]
theorem closedFormHomologyPeriod_smul (a : ℝ) (φ : closedForms I M k) :
    closedFormHomologyPeriod (a • φ) = a • closedFormHomologyPeriod φ := by
  ext c
  rw [AddMonoidHom.smul_apply, closedFormHomologyPeriod_apply, closedFormHomologyPeriod_apply]
  exact smoothHomologyPeriod_smul_apply a φ _

/-- **Exact forms have zero periods.** -/
theorem closedFormHomologyPeriod_eq_zero_of_mem_exactForms (φ : closedForms I M k)
    (hφ : φ.1 ∈ exactForms I M k) : closedFormHomologyPeriod φ = 0 := by
  ext c
  simp [closedFormHomologyPeriod_apply, smoothHomologyPeriod_eq_zero_of_mem_exactForms φ hφ]

variable {E' H' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E'] [FiniteDimensional ℝ E']
  [TopologicalSpace H'] {J : ModelWithCorners ℝ E' H'} {N : Type} [TopologicalSpace N]
  [ChartedSpace H' N] [T2Space N] [SigmaCompactSpace N] [IsManifold J ∞ N]

/-- **Naturality of the periods.** For a smooth map `f : M → N`, the periods of the pullback
`f^* φ` are the periods of `φ` on the images under `f_* : H_k(M; ℤ) → H_k(N; ℤ)`. -/
theorem closedFormHomologyPeriod_mpullback {f : M → N} (hf : ContMDiff I J ∞ f)
    (φ : closedForms J N k) (c : ((singularChains ℤ).obj (TopCat.of M)).homology k) :
    closedFormHomologyPeriod (closedForms.mpullback f hf k φ) c =
      closedFormHomologyPeriod φ (ContinuousMap.singularHomologyMap ℤ k ⟨f, hf.continuous⟩ c) := by
  rw [ContinuousMap.singularHomologyMap_eq_homologyMap_toSSet_map, closedFormHomologyPeriod_apply,
    closedFormHomologyPeriod_apply, ← homologyMap_smoothHomologyPeriod hf]
  exact congrArg (smoothHomologyPeriod φ).hom
    (ConcreteCategory.congr_hom (smoothSingularHomologyIso_inv_naturality _ hf k) c)

variable {E'' H'' : Type*} [NormedAddCommGroup E''] [NormedSpace ℝ E''] [FiniteDimensional ℝ E'']
  [TopologicalSpace H''] {K : ModelWithCorners ℝ E'' H''} {A : Type} [TopologicalSpace A]
  [ChartedSpace H'' A] [T2Space A] [SigmaCompactSpace A] [IsManifold K ∞ A]

/-- **A form pulled back from the second factor vanishes on cross products.** On a product
`A × B`, a closed form `pr₂^* φ` pulled back from `B` has zero period on every cross product
`a × b` of a class `a ∈ H_p(A; ℤ)` of positive degree with a class `b ∈ H_q(B; ℤ)`. -/
@[simp]
theorem closedFormHomologyPeriod_mpullback_snd_singularHomologyCrossBilinear_eq_zero {p q : ℕ}
    (h : p + q = k) (hp : p ≠ 0) (φ : closedForms J N k)
    (a : ((singularChains ℤ).obj (TopCat.of A)).homology p)
    (b : ((singularChains ℤ).obj (TopCat.of N)).homology q) :
    closedFormHomologyPeriod (closedForms.mpullback Prod.snd (contMDiff_snd (I := K)) k φ)
      (TopCat.singularHomologyCrossBilinear ℤ (TopCat.of A) (TopCat.of N) p q k h a b) = 0 := by
  rw [closedFormHomologyPeriod_mpullback]
  exact (congrArg (closedFormHomologyPeriod φ)
    (TopCat.singularHomologyMap_snd_singularHomologyCrossBilinear_eq_zero ℤ h hp a b)).trans
      (map_zero _)

end Singular

end TauCeti
