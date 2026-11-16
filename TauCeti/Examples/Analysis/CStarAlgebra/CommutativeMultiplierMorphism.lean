/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.Topology.UnitInterval
public import TauCeti.Analysis.CStarAlgebra.Multiplier.CommutativeMorphism
import Mathlib.Topology.Compactness.LocallyCompact

/-!
# Examples of commutative multiplier algebras and multiplier morphisms

This file illustrates the identification `𝓜(ℂ, C₀(X, ℂ)) ≃⋆ₐ[ℂ] (X →ᵇ ℂ)` and the
contravariant correspondence between continuous maps `C(X, Y)` and nondegenerate multiplier
homomorphisms `C₀(Y, ℂ) →⋆ₙₐ[ℂ] 𝓜(ℂ, C₀(X, ℂ))`:

* The open-to-closed interval inclusion `(0, 1) ↪ [0, 1]` induces a nondegenerate multiplier
  morphism sending the constant function `1 ∈ C₀([0, 1], ℂ)` to `1 ∈ 𝓜(ℂ, C₀((0, 1), ℂ))`, which
  does not lie in the canonical image of `C₀((0, 1), ℂ)` because `(0, 1)` is noncompact;
  correspondingly, the inclusion is not proper.
* Empty spaces behave consistently at both ends: for any weakly locally compact Hausdorff `Y`, the
  zero homomorphism `C₀(Y, ℂ) →⋆ₙₐ[ℂ] 𝓜(ℂ, C₀(Empty, ℂ))` is nondegenerate and corresponds to the
  proper empty map `Empty → Y`, whereas for any nonempty weakly locally compact `R₁` space `X`,
  there is no nondegenerate multiplier morphism `C₀(Empty, ℂ) →⋆ₙₐ[ℂ] 𝓜(ℂ, C₀(X, ℂ))`.
* On `ℝ`, the identity map induces the canonical inclusion `DoubleCentralizer.coeHom` (proper,
  landing in `C₀(ℝ, ℂ)`), whereas the constant map `0` induces the scalar-valued nondegenerate
  morphism `f ↦ f 0 • 1` (non-proper, not landing in `C₀(ℝ, ℂ)`).
* The bounded sine function `t ↦ (Real.sin t : ℂ)` defines a norm-one multiplier in
  `𝓜(ℂ, C₀(ℝ, ℂ))` outside the canonical image of `C₀(ℝ, ℂ)`.
-/

public section

noncomputable section

open Filter Topology
open scoped BoundedContinuousFunction CStarAlgebra MultiplierAlgebra ZeroAtInfty

namespace TauCeti.CommutativeMultiplierMorphismExample

/-! ### Non-proper inclusion `(0, 1) ↪ [0, 1]` -/

/-- The continuous inclusion of the open interval `(0, 1)` into the unit interval `[0, 1]`. -/
def inclusionIooUnitInterval : C(Set.Ioo (0 : ℝ) 1, unitInterval) where
  toFun x := ⟨x.1, x.2.1.le, x.2.2.le⟩
  continuous_toFun := continuous_subtype_val.subtype_mk _

/-- The constant function `1` in `C₀([0, 1], ℂ)`. -/
def constOneUnitInterval : C₀(unitInterval, ℂ) where
  toFun _ := 1
  continuous_toFun := continuous_const
  zero_at_infty' := by simp [Filter.cocompact_eq_bot]

/-- Pullback along `(0, 1) ↪ [0, 1]` is a nondegenerate multiplier morphism. -/
theorem isMultiplierNondegenerate_inclusionIooUnitInterval :
    (inclusionIooUnitInterval.compZeroAtInftyToMultiplier ℂ ℂ).IsMultiplierNondegenerate :=
  inclusionIooUnitInterval.isMultiplierNondegenerate_compZeroAtInftyToMultiplier

/-- Pullback along `(0, 1) ↪ [0, 1]` sends `1 ∈ C₀([0, 1], ℂ)` to `1 ∈ 𝓜(ℂ, C₀((0, 1), ℂ))`. -/
theorem inclusionIooUnitInterval_compZeroAtInftyToMultiplier_constOne :
    inclusionIooUnitInterval.compZeroAtInftyToMultiplier ℂ ℂ constOneUnitInterval = 1 :=
  DoubleCentralizer.ext_fst_snd
    (fun _ => ZeroAtInftyContinuousMap.ext fun _ => by simp [constOneUnitInterval])
    (fun _ => ZeroAtInftyContinuousMap.ext fun _ => by simp [constOneUnitInterval])

/-- The unit `1 ∈ 𝓜(ℂ, C₀((0, 1), ℂ))` does not lie in the canonical image of `C₀((0, 1), ℂ)`. -/
theorem one_notMem_range_coe_Ioo :
    (1 : 𝓜(ℂ, C₀(Set.Ioo (0 : ℝ) 1, ℂ))) ∉
      Set.range (DoubleCentralizer.coe ℂ : C₀(Set.Ioo (0 : ℝ) 1, ℂ) →
        𝓜(ℂ, C₀(Set.Ioo (0 : ℝ) 1, ℂ))) := by
  have : LocallyCompactSpace (Set.Ioo (0 : ℝ) 1) := isOpen_Ioo.locallyCompactSpace
  have hnc : NoncompactSpace (Set.Ioo (0 : ℝ) 1) := by
    refine ⟨fun hcompact => ?_⟩
    have hIoo : IsCompact (Set.Ioo (0 : ℝ) 1) := by
      have himg := hcompact.image continuous_subtype_val
      rwa [Set.image_univ, Subtype.range_coe_subtype] at himg
    have h0 : (0 : ℝ) ∈ Set.Ioo (0 : ℝ) 1 := by
      rw [← hIoo.isClosed.closure_eq, closure_Ioo zero_ne_one]
      exact ⟨le_rfl, zero_le_one⟩
    exact lt_irrefl 0 h0.1
  have : NeBot (cocompact (Set.Ioo (0 : ℝ) 1)) := Filter.cocompact_neBot_iff.2 hnc
  rw [DoubleCentralizer.mem_range_coe_iff_tendsto_cocompact_nhds_zero]
  intro h
  have h1 : Tendsto (fun _ : Set.Ioo (0 : ℝ) 1 => (1 : ℂ))
      (cocompact (Set.Ioo (0 : ℝ) 1)) (𝓝 0) := by
    rw [DoubleCentralizer.toBCF_one] at h
    exact h
  exact one_ne_zero (tendsto_const_nhds_iff.1 h1)

/-- The pullback along `(0, 1) ↪ [0, 1]` does not land in the canonical image of
`C₀((0, 1), ℂ)`. -/
theorem not_range_inclusionIooUnitInterval_subset :
    ¬ Set.range (inclusionIooUnitInterval.compZeroAtInftyToMultiplier ℂ ℂ) ⊆
      Set.range (DoubleCentralizer.coe ℂ : C₀(Set.Ioo (0 : ℝ) 1, ℂ) →
        𝓜(ℂ, C₀(Set.Ioo (0 : ℝ) 1, ℂ))) := by
  intro hsub
  exact one_notMem_range_coe_Ioo <|
    hsub ⟨constOneUnitInterval, inclusionIooUnitInterval_compZeroAtInftyToMultiplier_constOne⟩

/-- Consequently, the inclusion `(0, 1) ↪ [0, 1]` is not proper. -/
theorem not_isProperMap_inclusionIooUnitInterval :
    ¬ IsProperMap inclusionIooUnitInterval := by
  have : LocallyCompactSpace (Set.Ioo (0 : ℝ) 1) := isOpen_Ioo.locallyCompactSpace
  rw [ContinuousMap.isProperMap_iff_range_compZeroAtInftyToMultiplier_subset ℂ ℂ]
  exact not_range_inclusionIooUnitInterval_subset

/-! ### Empty domain and empty codomain -/

/-- The unique continuous map from `Empty` into any topological space `Y`. -/
def emptyMap (Y : Type*) [TopologicalSpace Y] : C(Empty, Y) where
  toFun := Empty.elim
  continuous_toFun := continuous_of_discreteTopology

/-- The zero homomorphism `C₀(Y, ℂ) →⋆ₙₐ[ℂ] 𝓜(ℂ, C₀(Empty, ℂ))` is nondegenerate. -/
theorem isMultiplierNondegenerate_zero_emptyDomain (Y : Type*) [TopologicalSpace Y] :
    (0 : C₀(Y, ℂ) →⋆ₙₐ[ℂ] 𝓜(ℂ, C₀(Empty, ℂ))).IsMultiplierNondegenerate := by
  rw [NonUnitalStarAlgHom.isMultiplierNondegenerate_iff_dense]
  intro g
  have hg : g = 0 := ZeroAtInftyContinuousMap.ext fun x => x.elim
  rw [hg]
  exact subset_closure (Submodule.zero_mem _)

/-- Under `multiplierMorphismEquiv`, the zero homomorphism into `𝓜(ℂ, C₀(Empty, ℂ))` corresponds
to the unique empty map `Empty → Y`. -/
theorem multiplierMorphismEquiv_symm_zero_emptyDomain (Y : Type*) [TopologicalSpace Y]
    [WeaklyLocallyCompactSpace Y] [T2Space Y] :
    (ContinuousMap.multiplierMorphismEquiv Empty Y).symm
      ⟨0, isMultiplierNondegenerate_zero_emptyDomain Y⟩ = emptyMap Y :=
  ContinuousMap.ext fun x => x.elim

/-- For any nonempty weakly locally compact `R₁` space `X`, the zero map
`C₀(Empty, ℂ) →⋆ₙₐ[ℂ] 𝓜(ℂ, C₀(X, ℂ))` is not nondegenerate. -/
theorem not_isMultiplierNondegenerate_zero_emptyCodomain (X : Type*) [TopologicalSpace X]
    [WeaklyLocallyCompactSpace X] [R1Space X] [Nonempty X] :
    ¬ (0 : C₀(Empty, ℂ) →⋆ₙₐ[ℂ] 𝓜(ℂ, C₀(X, ℂ))).IsMultiplierNondegenerate := by
  intro hφ
  obtain ⟨f, hf⟩ := hφ.exists_toBCF_ne_zero (Classical.arbitrary X)
  simp at hf

/-- For any nonempty weakly locally compact `R₁` space `X`, there are no nondegenerate multiplier
morphisms `C₀(Empty, ℂ) →⋆ₙₐ[ℂ] 𝓜(ℂ, C₀(X, ℂ))`. -/
theorem isEmpty_multiplierMorphism_emptyCodomain (X : Type*) [TopologicalSpace X]
    [WeaklyLocallyCompactSpace X] [R1Space X] [Nonempty X] :
    IsEmpty {φ : C₀(Empty, ℂ) →⋆ₙₐ[ℂ] 𝓜(ℂ, C₀(X, ℂ)) // φ.IsMultiplierNondegenerate} :=
  ⟨fun φ => ((ContinuousMap.multiplierMorphismEquiv X Empty).symm φ (Classical.arbitrary X)).elim⟩

/-! ### Identity versus constant map on `ℝ` -/

/-- Pullback along the identity on `ℝ` lands in the canonical image of `C₀(ℝ, ℂ)` since the
identity is proper. -/
theorem range_idReal_subset :
    Set.range ((ContinuousMap.id ℝ).compZeroAtInftyToMultiplier ℂ ℂ) ⊆
      Set.range (DoubleCentralizer.coe ℂ : C₀(ℝ, ℂ) → 𝓜(ℂ, C₀(ℝ, ℂ))) :=
  (ContinuousMap.isProperMap_iff_range_compZeroAtInftyToMultiplier_subset ℂ ℂ
    (ContinuousMap.id ℝ)).1 isProperMap_id

/-- Pullback along the constant map `0 : C(ℝ, ℝ)` sends `f` to the scalar multiplier `f 0 • 1`. -/
theorem constZeroReal_compZeroAtInftyToMultiplier (f : C₀(ℝ, ℂ)) :
    (ContinuousMap.const ℝ (0 : ℝ)).compZeroAtInftyToMultiplier ℂ ℂ f =
      algebraMap ℂ 𝓜(ℂ, C₀(ℝ, ℂ)) (f 0) := by
  apply DoubleCentralizer.toBCF_injective
  ext x
  simp [Algebra.algebraMap_eq_smul_one]

/-- Pullback along the constant map `0 : C(ℝ, ℝ)` is nondegenerate. -/
theorem isMultiplierNondegenerate_constZeroReal :
    ((ContinuousMap.const ℝ (0 : ℝ)).compZeroAtInftyToMultiplier ℂ ℂ).IsMultiplierNondegenerate :=
  (ContinuousMap.const ℝ (0 : ℝ)).isMultiplierNondegenerate_compZeroAtInftyToMultiplier

/-- Pullback along the constant map `0 : C(ℝ, ℝ)` does not land in `C₀(ℝ, ℂ)`. -/
theorem not_range_constZeroReal_subset :
    ¬ Set.range ((ContinuousMap.const ℝ (0 : ℝ)).compZeroAtInftyToMultiplier ℂ ℂ) ⊆
      Set.range (DoubleCentralizer.coe ℂ : C₀(ℝ, ℂ) → 𝓜(ℂ, C₀(ℝ, ℂ))) := by
  rw [← ContinuousMap.isProperMap_iff_range_compZeroAtInftyToMultiplier_subset ℂ ℂ]
  intro hproper
  have huniv : IsCompact (Set.univ : Set ℝ) := by
    have hpre :=
      (isProperMap_iff_isCompact_preimage.1 hproper).2 (isCompact_singleton (x := (0 : ℝ)))
    simpa [Set.preimage] using hpre
  exact not_compactSpace_iff.2 inferInstance (isCompact_univ_iff.1 huniv)

/-! ### A norm-one oscillatory multiplier on `ℝ` outside `C₀(ℝ, ℂ)` -/

/-- The bounded continuous function `t ↦ (Real.sin t : ℂ)` on `ℝ`. -/
def sinBCF : ℝ →ᵇ ℂ :=
  BoundedContinuousFunction.ofNormedAddCommGroup (fun t => (Real.sin t : ℂ))
    (Complex.continuous_ofReal.comp Real.continuous_sin) 1 fun t => by
      rw [Complex.norm_real]
      exact Real.abs_sin_le_one t

/-- The multiplier of `C₀(ℝ, ℂ)` given by pointwise multiplication by `Real.sin`. -/
def sinMultiplier : 𝓜(ℂ, C₀(ℝ, ℂ)) :=
  sinBCF.toDoubleCentralizer ℂ

/-- The oscillatory multiplier `sinMultiplier` has norm `1`. -/
@[simp]
theorem norm_sinMultiplier : ‖sinMultiplier‖ = 1 := by
  rw [sinMultiplier, BoundedContinuousFunction.norm_toDoubleCentralizer]
  refine le_antisymm ?_ ?_
  · exact BoundedContinuousFunction.norm_ofNormedAddCommGroup_le _ zero_le_one _
  · simpa [sinBCF] using sinBCF.norm_coe_le_norm (Real.pi / 2)

/-- The oscillatory multiplier `sinMultiplier` does not lie in the canonical image of
`C₀(ℝ, ℂ)`. -/
theorem sinMultiplier_notMem_range_coe :
    sinMultiplier ∉ Set.range (DoubleCentralizer.coe ℂ : C₀(ℝ, ℂ) → 𝓜(ℂ, C₀(ℝ, ℂ))) := by
  rw [DoubleCentralizer.mem_range_coe_iff_tendsto_cocompact_nhds_zero]
  intro h
  obtain ⟨K, hK, hKsin⟩ := mem_cocompact.1 (Metric.tendsto_nhds.1 h 1 zero_lt_one)
  obtain ⟨C, hC⟩ := hK.isBounded.subset_closedBall (0 : ℝ)
  obtain ⟨n, hn⟩ := exists_nat_gt (C / (2 * Real.pi))
  let t : ℝ := 2 * (n : ℝ) * Real.pi + Real.pi / 2
  have htK : t ∉ K := by
    intro hmem
    have hle : |t| ≤ C := by simpa [Real.dist_eq] using hC hmem
    have htpos : 0 < t := by positivity
    have h2pi : 0 < 2 * Real.pi := by positivity
    have h1 : C < (n : ℝ) * (2 * Real.pi) := (div_lt_iff₀ h2pi).1 hn
    have habs : t ≤ C := by rwa [abs_of_pos htpos] at hle
    have ht_def : t = 2 * (n : ℝ) * Real.pi + Real.pi / 2 := rfl
    linarith [Real.pi_pos]
  have hlt : ‖sinMultiplier.toBCF t‖ < 1 := by simpa [dist_zero_right] using hKsin htK
  have hsin : Real.sin t = 1 := by
    have ht : t = Real.pi / 2 + (n : ℝ) * (2 * Real.pi) := by ring
    rw [ht, Real.sin_add_nat_mul_two_pi, Real.sin_pi_div_two]
  simp [sinMultiplier, sinBCF, -Complex.ofReal_sin, hsin] at hlt

end TauCeti.CommutativeMultiplierMorphismExample
