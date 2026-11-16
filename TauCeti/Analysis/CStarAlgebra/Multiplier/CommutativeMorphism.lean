/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.CStarAlgebra.ContinuousMap
public import Mathlib.Analysis.RCLike.Basic
public import Mathlib.Topology.Maps.Proper.Basic
public import TauCeti.Analysis.CStarAlgebra.Multiplier.Nondegenerate
public import TauCeti.Analysis.CStarAlgebra.Multiplier.ZeroAtInfty
import Mathlib.Analysis.CStarAlgebra.ApproximateUnit
import Mathlib.Analysis.Normed.Algebra.Spectrum
import Mathlib.Topology.Algebra.Support
import Mathlib.Topology.ContinuousMap.Ideals
import Mathlib.Topology.ContinuousMap.ZeroAtInftyUnitization
import Mathlib.Topology.Maps.Proper.CompactlyGenerated
import Mathlib.Topology.UrysohnsLemma

/-!
# Commutative multiplier morphisms

For a continuous map `h : C(X, Y)`, precomposition defines a non-unital `⋆`-algebra homomorphism
`ContinuousMap.compZeroAtInftyToBCF : C₀(Y, A) →⋆ₙₐ[𝕜] (X →ᵇ A)` and, via
`BoundedContinuousFunction.toDoubleCentralizer`, a multiplier homomorphism
`ContinuousMap.compZeroAtInftyToMultiplier : C₀(Y, A) →⋆ₙₐ[𝕜] 𝓜(𝕜, C₀(X, A))`. No properness of
`h` is required for the image to land in `X →ᵇ A` or `𝓜(𝕜, C₀(X, A))`.

When `Y` is weakly locally compact `R₁` and `A` is any (possibly non-unital) C⋆-algebra, Urysohn
cutoffs on compact images `h '' K` paired with an approximate unit of `A` show that
`h.compZeroAtInftyToMultiplier ℂ A` is nondegenerate
(`ContinuousMap.isMultiplierNondegenerate_compZeroAtInftyToMultiplier`), and composition of
multiplier morphisms through `extendToMultiplier` corresponds contravariantly to composition of
continuous maps (`ContinuousMap.extendToMultiplier_comp_compZeroAtInftyToMultiplier`). When `A` is
unital, the unique extension `extendToMultiplier` acts on `𝓜(ℂ, C₀(Y, A))` by precomposing the
representing bounded continuous function with `h`
(`ContinuousMap.extendToMultiplier_compZeroAtInftyToMultiplier`).

In the scalar case `A = ℂ` (with `X` weakly locally compact `R₁` and `Y` weakly locally compact
Hausdorff), every nondegenerate `φ : C₀(Y, ℂ) →⋆ₙₐ[ℂ] 𝓜(ℂ, C₀(X, ℂ))` yields a nonzero character
`f ↦ (φ f).toBCF x` at every `x : X`. Lifting through the one-point compactification recovers a
unique continuous map `h : C(X, Y)` with `(φ f).toBCF = f ∘ h`, establishing the contravariant
bijection `ContinuousMap.multiplierMorphismEquiv` between `C(X, Y)` and nondegenerate multiplier
homomorphisms `C₀(Y, ℂ) →⋆ₙₐ[ℂ] 𝓜(ℂ, C₀(X, ℂ))`, as well as the `RCLike`-scalar version
`ContinuousMap.bcfMorphismEquiv` into `X →ᵇ 𝕜`. Finally, `h.compZeroAtInftyToMultiplier` lands in
the canonical image of `C₀(X, A)` if and only if `h` is proper
(`ContinuousMap.isProperMap_iff_range_compZeroAtInftyToMultiplier_subset`).

## Main definitions

* `ContinuousMap.compZeroAtInftyToBCF`: pullback `C₀(Y, A) →⋆ₙₐ[𝕜] (X →ᵇ A)` along `h : C(X, Y)`.
* `ContinuousMap.compZeroAtInftyToMultiplier`: pullback `C₀(Y, A) →⋆ₙₐ[𝕜] 𝓜(𝕜, C₀(X, A))`.
* `ContinuousMap.bcfMorphismEquiv`: bijection between `C(X, Y)` and pointwise-nonvanishing
  `⋆`-homomorphisms `C₀(Y, 𝕜) →⋆ₙₐ[𝕜] (X →ᵇ 𝕜)`.
* `ContinuousMap.multiplierMorphismEquiv`: bijection between `C(X, Y)` and nondegenerate
  `⋆`-homomorphisms `C₀(Y, ℂ) →⋆ₙₐ[ℂ] 𝓜(ℂ, C₀(X, ℂ))`.

## Main results

* `ContinuousMap.isMultiplierNondegenerate_compZeroAtInftyToMultiplier`: pullbacks along
  continuous maps are nondegenerate.
* `ContinuousMap.extendToMultiplier_compZeroAtInftyToMultiplier` and
  `ContinuousMap.extendToMultiplier_comp_compZeroAtInftyToMultiplier`: formula for the multiplier
  extension and contravariant composition.
* `NonUnitalStarAlgHom.isMultiplierNondegenerate_iff_forall_exists_toBCF_ne_zero`: nondegeneracy
  of `φ : A →⋆ₙₐ[ℂ] 𝓜(ℂ, C₀(X, ℂ))` for any (possibly non-unital) C⋆-algebra `A` is equivalent
  to pointwise nonvanishing of `a ↦ (φ a).toBCF x`.
* `ContinuousMap.isProperMap_iff_forall_tendsto_zeroAtInfty`,
  `ContinuousMap.isProperMap_iff_range_compZeroAtInftyToBCF_subset`,
  `ContinuousMap.isProperMap_iff_range_compZeroAtInftyToMultiplier_subset`: characterization of
  proper maps as those whose pullback lands in `C₀(X, A)`.

## References

* E. Christopher Lance, *Hilbert C*-Modules*, Chapter 2 (morphisms of C*-algebras).
* S. L. Woronowicz, *Unbounded elements affiliated with C*-algebras and non-compact quantum
  groups*, Comm. Math. Phys. 136 (1991), 399–432.
* Dana Williams, *Crossed Products of C*-Algebras*, Section 2.3.
-/

public section

noncomputable section

open Filter Topology
open scoped BoundedContinuousFunction CStarAlgebra MultiplierAlgebra ZeroAtInfty

namespace ContinuousMap

section Pullback

variable {𝕜 X Y A : Type*} [TopologicalSpace X] [TopologicalSpace Y]

section ToBCF

variable [SeminormedRing 𝕜] [NonUnitalSeminormedRing A] [StarRing A] [NormedStarGroup A]
  [Module 𝕜 A] [IsBoundedSMul 𝕜 A]

variable (𝕜 A) in
/-- Precomposition by a continuous map `h : C(X, Y)` defines a non-unital `⋆`-algebra homomorphism
`C₀(Y, A) →⋆ₙₐ[𝕜] (X →ᵇ A)`. -/
def compZeroAtInftyToBCF (h : C(X, Y)) : C₀(Y, A) →⋆ₙₐ[𝕜] (X →ᵇ A) where
  toFun f := f.toBCF.compContinuous h
  map_smul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl
  map_mul' _ _ := rfl
  map_star' _ := rfl

/-- Applying `compZeroAtInftyToBCF` precomposes `f.toBCF` with `h`. -/
@[simp]
theorem compZeroAtInftyToBCF_apply (h : C(X, Y)) (f : C₀(Y, A)) :
    h.compZeroAtInftyToBCF 𝕜 A f = f.toBCF.compContinuous h :=
  (rfl)

/-- Pullback along the identity map is the canonical inclusion `C₀(X, A) →⋆ₙₐ[𝕜] (X →ᵇ A)`. -/
@[simp]
theorem compZeroAtInftyToBCF_id :
    (ContinuousMap.id X).compZeroAtInftyToBCF 𝕜 A =
      ZeroAtInftyContinuousMap.toBCFNonUnitalStarAlgHom 𝕜 X A := by
  ext f x
  simp

end ToBCF

section ToMultiplier

variable [NontriviallyNormedField 𝕜] [StarRing 𝕜] [NonUnitalNormedRing A] [StarRing A]
  [NormedStarGroup A] [NormedSpace 𝕜 A] [SMulCommClass 𝕜 A A] [IsScalarTower 𝕜 A A]
  [StarModule 𝕜 A]

variable (𝕜 A) in
/-- Precomposition by a continuous map `h : C(X, Y)` defines a multiplier `⋆`-homomorphism
`C₀(Y, A) →⋆ₙₐ[𝕜] 𝓜(𝕜, C₀(X, A))`. -/
def compZeroAtInftyToMultiplier (h : C(X, Y)) : C₀(Y, A) →⋆ₙₐ[𝕜] 𝓜(𝕜, C₀(X, A)) where
  toFun f := (f.toBCF.compContinuous h).toDoubleCentralizer 𝕜
  map_smul' c f := BoundedContinuousFunction.toDoubleCentralizer_smul c (f.toBCF.compContinuous h)
  map_zero' := BoundedContinuousFunction.toDoubleCentralizer_zero
  map_add' f₁ f₂ :=
    BoundedContinuousFunction.toDoubleCentralizer_add
      (f₁.toBCF.compContinuous h) (f₂.toBCF.compContinuous h)
  map_mul' f₁ f₂ :=
    BoundedContinuousFunction.toDoubleCentralizer_mul
      (f₁.toBCF.compContinuous h) (f₂.toBCF.compContinuous h)
  map_star' f := BoundedContinuousFunction.toDoubleCentralizer_star (f.toBCF.compContinuous h)

/-- Applying `compZeroAtInftyToMultiplier` yields the multiplier attached to
`f.toBCF.compContinuous h`. -/
@[simp]
theorem compZeroAtInftyToMultiplier_apply (h : C(X, Y)) (f : C₀(Y, A)) :
    h.compZeroAtInftyToMultiplier 𝕜 A f =
      (f.toBCF.compContinuous h).toDoubleCentralizer 𝕜 :=
  (rfl)

/-- Pullback along the identity map is the canonical inclusion `DoubleCentralizer.coeHom`. -/
@[simp]
theorem compZeroAtInftyToMultiplier_id :
    (ContinuousMap.id X).compZeroAtInftyToMultiplier 𝕜 A =
      DoubleCentralizer.coeHom (𝕜 := 𝕜) := by
  ext f : 1
  refine DoubleCentralizer.ext_fst_snd
    (fun g => ZeroAtInftyContinuousMap.ext fun x => by simp)
    (fun g => ZeroAtInftyContinuousMap.ext fun x => by simp)

/-- On a cocompact map `h : CocompactMap X Y`, pullback into the multiplier algebra agrees with
`ZeroAtInftyContinuousMap.comp` composed with `DoubleCentralizer.coe`. -/
theorem compZeroAtInftyToMultiplier_cocompact (h : CocompactMap X Y) (f : C₀(Y, A)) :
    h.toContinuousMap.compZeroAtInftyToMultiplier 𝕜 A f = (f.comp h : 𝓜(𝕜, C₀(X, A))) :=
  DoubleCentralizer.ext_fst_snd
    (fun _ => ZeroAtInftyContinuousMap.ext fun _ => by simp)
    (fun _ => ZeroAtInftyContinuousMap.ext fun _ => by simp)

end ToMultiplier

end Pullback

section Nondegenerate

variable {X Y Z A : Type*} [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]

private theorem exists_approx_unit_on_compact [NonUnitalCStarAlgebra A]
    {K : Set A} (hK : IsCompact K) {δ : ℝ} (hδ : 0 < δ) :
    ∃ e : A, ‖e‖ ≤ 1 ∧ ∀ a ∈ K, ‖e * a - a‖ < δ := by
  have hδ3 : 0 < δ / 3 := by positivity
  obtain ⟨s, hs⟩ := hK.elim_finite_subcover
    (fun a : A => Metric.ball a (δ / 3)) (fun _ => Metric.isOpen_ball)
    (fun y _ => Set.mem_iUnion.2 ⟨y, Metric.mem_ball_self hδ3⟩)
  let := CStarAlgebra.spectralOrder A
  have := CStarAlgebra.spectralOrderedRing A
  have hl := CStarAlgebra.increasingApproximateUnit A
  have := hl.neBot
  have hev : ∀ᶠ e in CStarAlgebra.approximateUnit A,
      ‖e‖ ≤ 1 ∧ ∀ a ∈ s, ‖e * a - a‖ < δ / 3 :=
    hl.eventually_norm.and <| (Filter.eventually_all_finset s).2 fun a _ => by
      simpa [dist_eq_norm] using Metric.tendsto_nhds.1 (hl.tendsto_mul_right a) (δ / 3) hδ3
  obtain ⟨e, he_norm, he_mul⟩ := hev.exists
  refine ⟨e, he_norm, fun y hy => ?_⟩
  obtain ⟨a, ha, hya⟩ := Set.mem_iUnion₂.1 (hs hy)
  rw [Metric.mem_ball, dist_eq_norm] at hya
  have hdecomp : e * y - y = e * (y - a) + (e * a - a) - (y - a) := by rw [mul_sub]; abel
  have h1 : ‖e * (y - a)‖ ≤ δ / 3 :=
    (norm_mul_le _ _).trans <| by
      simpa using mul_le_mul he_norm hya.le (norm_nonneg _) zero_le_one
  have h2 : ‖e * y - y‖ ≤ ‖e * (y - a)‖ + ‖e * a - a‖ + ‖y - a‖ := by
    rw [hdecomp]
    exact (norm_sub_le _ _).trans (by gcongr; exact norm_add_le _ _)
  linarith [he_mul a ha]

/-- Pullback along any continuous map `h : C(X, Y)` into a weakly locally compact `R₁` space is a
nondegenerate multiplier homomorphism `C₀(Y, A) →⋆ₙₐ[ℂ] 𝓜(ℂ, C₀(X, A))` for every (possibly
non-unital) C⋆-algebra `A`. -/
theorem isMultiplierNondegenerate_compZeroAtInftyToMultiplier [WeaklyLocallyCompactSpace Y]
    [R1Space Y] [NonUnitalCStarAlgebra A] (h : C(X, Y)) :
    (h.compZeroAtInftyToMultiplier ℂ A).IsMultiplierNondegenerate := by
  rw [NonUnitalStarAlgHom.isMultiplierNondegenerate_iff_dense, Metric.dense_iff]
  intro g ε hε
  obtain ⟨K, hK, hKg⟩ := mem_cocompact.1 <|
    Metric.tendsto_nhds.1 (zero_at_infty g) (ε / 4) (by positivity)
  obtain ⟨e, he_norm, he_mul⟩ :=
    exists_approx_unit_on_compact (hK.image g.continuous) (half_pos hε)
  obtain ⟨χ, hχK, -, hχ_supp, hχ_range⟩ :=
    exists_continuous_one_zero_of_isCompact (hK.image h.continuous) isClosed_empty
      (Set.disjoint_empty _)
  let f : C₀(Y, A) :=
    ⟨⟨fun y => χ y • e, χ.continuous.smul continuous_const⟩,
      (hχ_supp.comp_left (g := fun r : ℝ => r • e) (zero_smul ℝ e)).is_zero_at_infty⟩
  refine ⟨(h.compZeroAtInftyToMultiplier ℂ A f).fst g, ?_,
    Submodule.subset_span <| Set.mem_iUnion.2 ⟨f, g, rfl⟩⟩
  rw [Metric.mem_ball, dist_eq_norm]
  have hle : ‖(h.compZeroAtInftyToMultiplier ℂ A f).fst g - g‖ ≤ ε / 2 := by
    rw [← ZeroAtInftyContinuousMap.norm_toBCF_eq_norm,
      BoundedContinuousFunction.norm_le (half_pos hε).le]
    intro x
    have hval : ((h.compZeroAtInftyToMultiplier ℂ A f).fst g - g) x =
        (χ (h x) • e) * g x - g x := by simp [f]
    rw [ZeroAtInftyContinuousMap.toBCF_apply, hval]
    by_cases hx : x ∈ K
    · rw [hχK ⟨x, hx, rfl⟩, Pi.one_apply, one_smul]
      exact (he_mul (g x) ⟨x, hx, rfl⟩).le
    · have hdist : ‖g x‖ < ε / 4 := by simpa [dist_zero_right] using hKg hx
      have hχe : ‖χ (h x) • e‖ ≤ 1 := by
        rw [norm_smul, Real.norm_of_nonneg (hχ_range (h x)).1]
        simpa using mul_le_mul (hχ_range (h x)).2 he_norm (norm_nonneg e) zero_le_one
      have hmul : ‖(χ (h x) • e) * g x‖ ≤ ‖g x‖ :=
        (norm_mul_le _ _).trans <| by simpa using mul_le_mul_of_nonneg_right hχe (norm_nonneg (g x))
      linarith [norm_sub_le ((χ (h x) • e) * g x) (g x)]
  exact hle.trans_lt (half_lt_self hε)

/-- The unique multiplier extension of `h.compZeroAtInftyToMultiplier ℂ A` acts on
`m : 𝓜(ℂ, C₀(Y, A))` by precomposing `m.toBCF` with `h`. -/
@[simp]
theorem extendToMultiplier_compZeroAtInftyToMultiplier [WeaklyLocallyCompactSpace Y] [R1Space Y]
    [CStarAlgebra A] (h : C(X, Y))
    (hφ : (h.compZeroAtInftyToMultiplier ℂ A).IsMultiplierNondegenerate)
    (m : 𝓜(ℂ, C₀(Y, A))) :
    (h.compZeroAtInftyToMultiplier ℂ A).extendToMultiplier hφ m =
      (m.toBCF.compContinuous h).toDoubleCentralizer ℂ := by
  refine ((NonUnitalStarAlgHom.eq_extendToMultiplier_iff hφ).2 fun f => ?_).symm
  rw [compZeroAtInftyToMultiplier_apply, compZeroAtInftyToMultiplier_apply,
    ← BoundedContinuousFunction.toDoubleCentralizer_mul]
  congr 1
  ext x
  exact (DoubleCentralizer.fst_apply_eq_toBCF_mul m f (h x)).symm

/-- Contravariant functoriality of pullbacks into multiplier algebras under `extendToMultiplier`. -/
@[simp]
theorem extendToMultiplier_comp_compZeroAtInftyToMultiplier [NonUnitalCStarAlgebra A]
    (h₁ : C(X, Y)) (h₂ : C(Y, Z))
    (hφ₁ : (h₁.compZeroAtInftyToMultiplier ℂ A).IsMultiplierNondegenerate) :
    ((h₁.compZeroAtInftyToMultiplier ℂ A).extendToMultiplier hφ₁).toNonUnitalStarAlgHom.comp
      (h₂.compZeroAtInftyToMultiplier ℂ A) =
        (h₂.comp h₁).compZeroAtInftyToMultiplier ℂ A := by
  ext f : 1
  refine ((NonUnitalStarAlgHom.eq_extendToMultiplier_iff hφ₁).2 fun g => ?_).symm
  rw [compZeroAtInftyToMultiplier_apply, compZeroAtInftyToMultiplier_apply,
    compZeroAtInftyToMultiplier_apply, ← BoundedContinuousFunction.toDoubleCentralizer_mul]
  congr 1
  ext x
  simp

end Nondegenerate

section CharacterRecovery

variable {𝕜 X Y : Type*} [RCLike 𝕜] [TopologicalSpace X] [TopologicalSpace Y]
  [WeaklyLocallyCompactSpace Y] [T2Space Y]

/-- Every nonzero algebra character `C₀(Y, 𝕜) →ₙₐ[𝕜] 𝕜` on a weakly locally compact Hausdorff space
is point evaluation at a unique point of `Y`. -/
private theorem existsUnique_eval_of_ne_zero (ψ : C₀(Y, 𝕜) →ₙₐ[𝕜] 𝕜) (hψ : ψ ≠ 0) :
    ∃! y : Y, ∀ f : C₀(Y, 𝕜), ψ f = f y := by
  let χ : C(OnePoint Y, 𝕜) →ₐ[𝕜] 𝕜 :=
    (Unitization.lift ψ).comp (ZeroAtInftyContinuousMap.unitizationAlgEquiv Y 𝕜 𝕜).symm.toAlgHom
  obtain ⟨z, hz⟩ :=
    (WeakDual.CharacterSpace.continuousMapEval_bijective (OnePoint Y) 𝕜).2
      (WeakDual.CharacterSpace.equivAlgHom.symm χ)
  have hval (f : C₀(Y, 𝕜)) : ψ f = f.toOnePoint z := by
    have h1 := congr($hz f.toOnePoint)
    simp only [WeakDual.CharacterSpace.continuousMapEval_apply_apply,
      WeakDual.CharacterSpace.equivAlgHom_symm_coe] at h1
    rw [h1]
    simp only [χ, AlgHom.comp_apply, AlgEquiv.toAlgHom_apply,
      ZeroAtInftyContinuousMap.coe_unitizationAlgEquiv_symm]
    rw [← ZeroAtInftyContinuousMap.unitizationEquiv_inr, Equiv.symm_apply_apply]
    simp [Unitization.lift]
  cases z with
  | infty =>
    exfalso
    apply hψ
    ext f
    simpa using hval f
  | coe y =>
    refine ⟨y, fun f => by simpa using hval f, fun y' hy' => ?_⟩
    by_contra hne
    obtain ⟨u, hu1, hu0, hu_supp, -⟩ :=
      exists_continuous_one_zero_of_isCompact (isCompact_singleton (x := y))
        isClosed_singleton (Set.disjoint_singleton.2 (Ne.symm hne))
    let f : C₀(Y, 𝕜) :=
      ⟨⟨fun w => (u w : 𝕜), RCLike.continuous_ofReal.comp u.continuous⟩,
        (hu_supp.comp_left (g := RCLike.ofReal) (map_zero _)).is_zero_at_infty⟩
    have hf : f y = f y' := by
      have hy : ψ f = f y := by simpa using hval f
      rw [← hy, hy' f]
    simp [f, hu1 rfl, hu0 rfl] at hf

private def recoverFun (φ : C₀(Y, 𝕜) →⋆ₙₐ[𝕜] (X →ᵇ 𝕜)) (hφ : ∀ x, ∃ f, φ f x ≠ 0) (x : X) :
    Y :=
  let ev : C₀(Y, 𝕜) →ₙₐ[𝕜] 𝕜 :=
    { toFun f := φ f x
      map_smul' c f := by simp
      map_zero' := by simp
      map_add' f g := by simp
      map_mul' f g := by simp }
  (existsUnique_eval_of_ne_zero ev fun hev => by
    obtain ⟨f, hf⟩ := hφ x
    exact hf (congr($hev f))).choose

private theorem recoverFun_spec (φ : C₀(Y, 𝕜) →⋆ₙₐ[𝕜] (X →ᵇ 𝕜)) (hφ : ∀ x, ∃ f, φ f x ≠ 0)
    (f : C₀(Y, 𝕜)) (x : X) : φ f x = f (recoverFun φ hφ x) :=
  (existsUnique_eval_of_ne_zero
    ({ toFun f := φ f x
       map_smul' _ _ := by simp
       map_zero' := by simp
       map_add' _ _ := by simp
       map_mul' _ _ := by simp } : C₀(Y, 𝕜) →ₙₐ[𝕜] 𝕜)
    fun hev => let ⟨g, hg⟩ := hφ x; hg (congr($hev g))).choose_spec.1 f

private theorem continuous_recoverFun (φ : C₀(Y, 𝕜) →⋆ₙₐ[𝕜] (X →ᵇ 𝕜))
    (hφ : ∀ x, ∃ f, φ f x ≠ 0) : Continuous (recoverFun φ hφ) := by
  rw [continuous_iff_continuousAt]
  intro x
  rw [ContinuousAt, tendsto_nhds]
  intro U hU hxU
  obtain ⟨u, hu1, hu0, hu_supp, -⟩ :=
    exists_continuous_one_zero_of_isCompact (isCompact_singleton (x := recoverFun φ hφ x))
      hU.isClosed_compl (Set.disjoint_singleton_left.2 (Set.notMem_compl_iff.2 hxU))
  let f : C₀(Y, 𝕜) :=
    ⟨⟨fun w => (u w : 𝕜), RCLike.continuous_ofReal.comp u.continuous⟩,
      (hu_supp.comp_left (g := RCLike.ofReal) (map_zero _)).is_zero_at_infty⟩
  have hmem : {x' : X | φ f x' ≠ 0} ∈ 𝓝 x :=
    (isOpen_ne.preimage (φ f).continuous).mem_nhds <| by
      simp only [Set.mem_preimage, Set.mem_ofPred]
      rw [recoverFun_spec φ hφ f x]
      simp [f, hu1 rfl]
  filter_upwards [hmem] with x' hx'
  by_contra hx'U
  apply hx'
  rw [recoverFun_spec φ hφ f x']
  simp [f, hu0 hx'U]

private theorem exists_apply_ne_zero_of_compZeroAtInftyToBCF (h : C(X, Y)) (x : X) :
    ∃ f : C₀(Y, 𝕜), h.compZeroAtInftyToBCF 𝕜 𝕜 f x ≠ 0 := by
  obtain ⟨u, hu1, -, hu_supp, -⟩ :=
    exists_continuous_one_zero_of_isCompact (isCompact_singleton (x := h x)) isClosed_empty
      (Set.disjoint_empty _)
  let f : C₀(Y, 𝕜) :=
    ⟨⟨fun w => (u w : 𝕜), RCLike.continuous_ofReal.comp u.continuous⟩,
      (hu_supp.comp_left (g := RCLike.ofReal) (map_zero _)).is_zero_at_infty⟩
  exact ⟨f, by simp [f, hu1 rfl]⟩

variable (𝕜 X Y) in
/-- Bijection between continuous maps `C(X, Y)` and pointwise-nonvanishing `⋆`-homomorphisms
`C₀(Y, 𝕜) →⋆ₙₐ[𝕜] (X →ᵇ 𝕜)` for an `RCLike` field `𝕜`, any topological space `X`, and a weakly
locally compact Hausdorff space `Y`. -/
def bcfMorphismEquiv :
    C(X, Y) ≃ {φ : C₀(Y, 𝕜) →⋆ₙₐ[𝕜] (X →ᵇ 𝕜) // ∀ x, ∃ f, φ f x ≠ 0} where
  toFun h := ⟨h.compZeroAtInftyToBCF 𝕜 𝕜, exists_apply_ne_zero_of_compZeroAtInftyToBCF h⟩
  invFun φ := ⟨recoverFun φ.1 φ.2, continuous_recoverFun φ.1 φ.2⟩
  left_inv h := by
    ext x
    let ev : C₀(Y, 𝕜) →ₙₐ[𝕜] 𝕜 :=
      { toFun f := f (h x)
        map_smul' _ _ := by simp
        map_zero' := by simp
        map_add' _ _ := by simp
        map_mul' _ _ := by simp }
    have hev : ev ≠ 0 := fun h0 => by
      obtain ⟨f, hf⟩ := exists_apply_ne_zero_of_compZeroAtInftyToBCF (𝕜 := 𝕜) h x
      exact hf (congr($h0 f))
    exact (existsUnique_eval_of_ne_zero ev hev).unique
      (fun f => recoverFun_spec (h.compZeroAtInftyToBCF 𝕜 𝕜)
        (exists_apply_ne_zero_of_compZeroAtInftyToBCF h) f x)
      (fun _ => rfl)
  right_inv φ := by
    apply Subtype.ext
    ext f x
    exact (recoverFun_spec φ.1 φ.2 f x).symm

/-- Applying `bcfMorphismEquiv` gives `ContinuousMap.compZeroAtInftyToBCF`. -/
@[simp]
theorem bcfMorphismEquiv_apply (h : C(X, Y)) :
    (bcfMorphismEquiv 𝕜 X Y h : C₀(Y, 𝕜) →⋆ₙₐ[𝕜] (X →ᵇ 𝕜)) = h.compZeroAtInftyToBCF 𝕜 𝕜 :=
  (rfl)

/-- Evaluating `f` at the recovered continuous map `(bcfMorphismEquiv 𝕜 X Y).symm φ x` returns
`φ.1 f x`. -/
@[simp]
theorem bcfMorphismEquiv_symm_apply_spec
    (φ : {φ : C₀(Y, 𝕜) →⋆ₙₐ[𝕜] (X →ᵇ 𝕜) // ∀ x, ∃ f, φ f x ≠ 0}) (f : C₀(Y, 𝕜)) (x : X) :
    f ((bcfMorphismEquiv 𝕜 X Y).symm φ x) = φ.1 f x :=
  (recoverFun_spec φ.1 φ.2 f x).symm

end CharacterRecovery

end ContinuousMap

namespace NonUnitalStarAlgHom

section CommutativeNondegenerate

/-- Non-unital polynomial iterate `q_n = 1 - (1 - q)^n`, defined recursively by
`q_0 = 0` and `q_{n+1} = q + q_n - q * q_n`. -/
private def oneSubPow {A : Type*} [NonUnitalRing A] (q : A) : ℕ → A
  | 0 => 0
  | n + 1 => q + oneSubPow q n - q * oneSubPow q n

variable {X A : Type*} [TopologicalSpace X] [WeaklyLocallyCompactSpace X] [R1Space X]
  [NonUnitalCStarAlgebra A]

private theorem one_sub_map_oneSubPow (φ : A →⋆ₙₐ[ℂ] 𝓜(ℂ, C₀(X, ℂ))) (q : A) (x : X) (n : ℕ) :
    1 - (φ (oneSubPow q n)).toBCF x = (1 - (φ q).toBCF x) ^ n := by
  induction n with
  | zero => simp [oneSubPow]
  | succ n ih =>
    simp only [oneSubPow, map_sub, map_add, map_mul, DoubleCentralizer.toBCF_sub,
      DoubleCentralizer.toBCF_add, DoubleCentralizer.toBCF_mul, sub_apply, add_apply, mul_apply]
    linear_combination (1 - (φ q).toBCF x) * ih

private theorem exists_real_pos_on_compact (φ : A →⋆ₙₐ[ℂ] 𝓜(ℂ, C₀(X, ℂ)))
    (h : ∀ x : X, ∃ a : A, (φ a).toBCF x ≠ 0) {K : Set X} (hK : IsCompact K) (hKne : K.Nonempty) :
    ∃ q : A, ∃ c ∈ Set.Ioo (0 : ℝ) 1,
      ∀ z : X, ∃ t ∈ Set.Icc (0 : ℝ) 1, (φ q).toBCF z = (t : ℂ) ∧ (z ∈ K → c ≤ t) := by
  choose a ha using h
  obtain ⟨s, hs⟩ := hK.elim_finite_subcover
    (fun x : X => {z : X | (φ (a x)).toBCF z ≠ 0})
    (fun x => isOpen_ne.preimage (φ (a x)).toBCF.continuous)
    (fun x _ => Set.mem_iUnion.2 ⟨x, ha x⟩)
  let b : A := ∑ x ∈ s, star (a x) * a x
  let r : X → ℝ := fun z => ∑ x ∈ s, ‖(φ (a x)).toBCF z‖ ^ 2
  have hφb (z : X) : (φ b).toBCF z = (r z : ℂ) := by
    have hsum : (φ b).toBCF = ∑ x ∈ s, star ((φ (a x)).toBCF) * (φ (a x)).toBCF := by
      rw [← DoubleCentralizer.coe_toBCFStarAlgEquiv (𝕜 := ℂ)]
      simp only [b, map_sum, map_mul, map_star, DoubleCentralizer.coe_toBCFStarAlgEquiv]
    rw [hsum]
    simp [r, Complex.conj_mul']
  have hr_nonneg (z : X) : 0 ≤ r z := Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hr_pos {z : X} (hz : z ∈ K) : 0 < r z := by
    obtain ⟨x, hx, hzx⟩ := Set.mem_iUnion₂.1 (hs hz)
    exact Finset.sum_pos' (fun _ _ => sq_nonneg _) ⟨x, hx, sq_pos_of_pos (norm_pos_iff.2 hzx)⟩
  have hr_cont : Continuous r := by
    have : r = fun z => ((φ b).toBCF z).re := funext fun z => by simp [hφb z]
    rw [this]
    exact Complex.continuous_re.comp (φ b).toBCF.continuous
  obtain ⟨z₀, hz₀K, hz₀⟩ := hK.exists_isMinOn hKne hr_cont.continuousOn
  let M : ℝ := ‖(φ b).toBCF‖ + 1
  have hM : 0 < M := by positivity
  have hr_lt (z : X) : r z < M := by
    have hnorm : r z = ‖(φ b).toBCF z‖ := by
      rw [hφb z, Complex.norm_real, Real.norm_of_nonneg (hr_nonneg z)]
    linarith [(φ b).toBCF.norm_coe_le_norm z]
  refine ⟨((M⁻¹ : ℝ) : ℂ) • b, r z₀ / M,
    ⟨div_pos (hr_pos hz₀K) hM, (div_lt_one hM).2 (hr_lt z₀)⟩, fun z =>
    ⟨r z / M, ⟨div_nonneg (hr_nonneg z) hM.le, (div_le_one hM).2 (hr_lt z).le⟩, ?_,
      fun hz => div_le_div_of_nonneg_right (hz₀ hz) hM.le⟩⟩
  simp only [map_smul, DoubleCentralizer.toBCF_smul, smul_apply, hφb z, smul_eq_mul,
    Complex.ofReal_div, Complex.ofReal_inv]
  ring

/-- Every nondegenerate `φ : A →⋆ₙₐ[ℂ] 𝓜(ℂ, C₀(X, ℂ))` is pointwise nonvanishing on `X`:
for each `x : X`, there exists `a : A` with `(φ a).toBCF x ≠ 0`. -/
theorem IsMultiplierNondegenerate.exists_toBCF_ne_zero
    {φ : A →⋆ₙₐ[ℂ] 𝓜(ℂ, C₀(X, ℂ))} (hφ : φ.IsMultiplierNondegenerate) (x : X) :
    ∃ a : A, (φ a).toBCF x ≠ 0 := by
  by_contra h
  push Not at h
  have hclosed : IsClosed {g : C₀(X, ℂ) | g x = 0} :=
    isClosed_eq ((BoundedContinuousFunction.evalCLM ℂ x).continuous.comp
      ZeroAtInftyContinuousMap.isometry_toBCF.continuous) continuous_const
  have hsub : (Submodule.span ℂ (⋃ a, Set.range (φ a).fst) : Set C₀(X, ℂ)) ⊆
      {g : C₀(X, ℂ) | g x = 0} := by
    intro g hg
    induction hg using Submodule.span_induction with
    | mem _ hz =>
      obtain ⟨a, b, rfl⟩ := Set.mem_iUnion.1 hz
      rw [Set.mem_ofPred, DoubleCentralizer.fst_apply_eq_toBCF_mul, h a, zero_mul]
    | zero => simp
    | add _ _ _ _ hu hv => simpa using congr($(hu) + $(hv))
    | smul c _ _ hu => simpa using congr(c * $(hu))
  have hall : ∀ g : C₀(X, ℂ), g x = 0 := fun g =>
    hclosed.closure_subset_iff.2 hsub (isMultiplierNondegenerate_iff_dense.1 hφ g)
  obtain ⟨u, hu1, -, hu_supp, -⟩ :=
    exists_continuous_one_zero_of_isCompact (isCompact_singleton (x := x)) isClosed_empty
      (Set.disjoint_empty _)
  let e : C₀(X, ℂ) :=
    ⟨⟨fun w => (u w : ℂ), Complex.continuous_ofReal.comp u.continuous⟩,
      (hu_supp.comp_left (g := Complex.ofReal) Complex.ofReal_zero).is_zero_at_infty⟩
  have he1 : e x = 1 := by simp [e, hu1 rfl]
  exact one_ne_zero (he1.symm.trans (hall e))

/-- When `X` is weakly locally compact `R₁`, a homomorphism `φ : A →⋆ₙₐ[ℂ] 𝓜(ℂ, C₀(X, ℂ))` from
any (possibly non-unital) C⋆-algebra `A` is nondegenerate if and only if `a ↦ (φ a).toBCF x` is
nonzero at every `x : X`. -/
theorem isMultiplierNondegenerate_iff_forall_exists_toBCF_ne_zero
    (φ : A →⋆ₙₐ[ℂ] 𝓜(ℂ, C₀(X, ℂ))) :
    φ.IsMultiplierNondegenerate ↔ ∀ x : X, ∃ a : A, (φ a).toBCF x ≠ 0 := by
  refine ⟨fun hφ => hφ.exists_toBCF_ne_zero, fun h => ?_⟩
  rw [isMultiplierNondegenerate_iff_dense, Metric.dense_iff]
  intro g ε hε
  obtain ⟨K, hK, hKg⟩ := mem_cocompact.1 <|
    Metric.tendsto_nhds.1 (zero_at_infty g) (ε / 2) (half_pos hε)
  rcases K.eq_empty_or_nonempty with rfl | hKne
  · refine ⟨0, ?_, Submodule.zero_mem _⟩
    rw [Metric.mem_ball, dist_eq_norm, zero_sub, norm_neg]
    have hle : ‖g‖ ≤ ε / 2 := by
      rw [← ZeroAtInftyContinuousMap.norm_toBCF_eq_norm,
        BoundedContinuousFunction.norm_le (half_pos hε).le]
      intro x
      exact (by simpa [dist_zero_right] using hKg (Set.notMem_empty x) : ‖g x‖ < ε / 2).le
    exact hle.trans_lt (half_lt_self hε)
  · obtain ⟨q, c, ⟨hc0, hc1⟩, hq⟩ := exists_real_pos_on_compact φ h hK hKne
    have hlim : Tendsto (fun n : ℕ => (1 - c) ^ n * ‖g‖) atTop (𝓝 0) := by
      simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one (by linarith) (by linarith)).mul_const ‖g‖
    obtain ⟨n, hn⟩ := (Metric.tendsto_nhds.1 hlim (ε / 2) (half_pos hε)).exists
    have hn' : (1 - c) ^ n * ‖g‖ < ε / 2 := by
      simpa [Real.dist_eq, abs_of_nonneg (sub_nonneg.2 hc1.le)] using hn
    refine ⟨(φ (oneSubPow q n)).fst g, ?_,
      Submodule.subset_span <| Set.mem_iUnion.2 ⟨oneSubPow q n, g, rfl⟩⟩
    rw [Metric.mem_ball, dist_eq_norm]
    have hle : ‖(φ (oneSubPow q n)).fst g - g‖ ≤ ε / 2 := by
      rw [← ZeroAtInftyContinuousMap.norm_toBCF_eq_norm,
        BoundedContinuousFunction.norm_le (half_pos hε).le]
      intro z
      obtain ⟨t, ⟨ht0, ht1⟩, hqt, hKct⟩ := hq z
      have hval : ((φ (oneSubPow q n)).fst g - g) z = -(((1 - t) ^ n : ℝ) : ℂ) * g z := by
        have h1 : (φ (oneSubPow q n)).toBCF z - 1 = -(((1 - t) ^ n : ℝ) : ℂ) := by
          have := one_sub_map_oneSubPow φ q z n
          rw [hqt] at this
          push_cast
          linear_combination -this
        simp only [FunLike.coe_sub, Pi.sub_apply, DoubleCentralizer.fst_apply_eq_toBCF_mul]
        linear_combination g z * h1
      rw [ZeroAtInftyContinuousMap.toBCF_apply, hval, norm_mul, norm_neg, Complex.norm_real,
        Real.norm_of_nonneg (pow_nonneg (by linarith) n)]
      by_cases hz : z ∈ K
      · have hpow : (1 - t) ^ n ≤ (1 - c) ^ n :=
          pow_le_pow_left₀ (by linarith) (by linarith [hKct hz]) n
        exact (mul_le_mul hpow (g.toBCF.norm_coe_le_norm z) (norm_nonneg _)
          (pow_nonneg (by linarith) n)).trans hn'.le
      · have hdist : ‖g z‖ < ε / 2 := by simpa [dist_zero_right] using hKg hz
        have hpow : (1 - t) ^ n ≤ 1 := pow_le_one₀ (by linarith) (by linarith)
        exact (mul_le_mul_of_nonneg_right hpow (norm_nonneg _)).trans (by simpa using hdist.le)
    exact hle.trans_lt (half_lt_self hε)

end CommutativeNondegenerate

end NonUnitalStarAlgHom

namespace ContinuousMap

section MultiplierMorphismEquiv

variable {X Y Z : Type*} [TopologicalSpace X] [WeaklyLocallyCompactSpace X] [R1Space X]
  [TopologicalSpace Y] [WeaklyLocallyCompactSpace Y] [T2Space Y]

variable (X Y) in
/-- Bijection between continuous maps `C(X, Y)` and nondegenerate multiplier homomorphisms
`C₀(Y, ℂ) →⋆ₙₐ[ℂ] 𝓜(ℂ, C₀(X, ℂ))` for weakly locally compact `R₁` `X` and weakly locally compact
Hausdorff `Y`. -/
def multiplierMorphismEquiv :
    C(X, Y) ≃ {φ : C₀(Y, ℂ) →⋆ₙₐ[ℂ] 𝓜(ℂ, C₀(X, ℂ)) // φ.IsMultiplierNondegenerate} where
  toFun h := ⟨h.compZeroAtInftyToMultiplier ℂ ℂ,
    h.isMultiplierNondegenerate_compZeroAtInftyToMultiplier⟩
  invFun φ := (bcfMorphismEquiv ℂ X Y).symm
    ⟨(DoubleCentralizer.toBCFStarAlgEquiv ℂ X ℂ).toNonUnitalStarAlgHom.comp φ.1,
      fun x => by simpa using φ.2.exists_toBCF_ne_zero x⟩
  left_inv h := by
    dsimp only
    apply (bcfMorphismEquiv ℂ X Y).injective
    apply Subtype.ext
    ext f x
    simp
  right_inv φ := by
    apply Subtype.ext
    ext f : 1
    apply DoubleCentralizer.toBCF_injective
    ext x
    simp

/-- Applying `multiplierMorphismEquiv` gives `ContinuousMap.compZeroAtInftyToMultiplier`. -/
@[simp]
theorem multiplierMorphismEquiv_apply (h : C(X, Y)) :
    (multiplierMorphismEquiv X Y h : C₀(Y, ℂ) →⋆ₙₐ[ℂ] 𝓜(ℂ, C₀(X, ℂ))) =
      h.compZeroAtInftyToMultiplier ℂ ℂ :=
  (rfl)

/-- Evaluating `f : C₀(Y, ℂ)` at the recovered map `(multiplierMorphismEquiv X Y).symm φ x` returns
`(φ.1 f).toBCF x`. -/
@[simp]
theorem multiplierMorphismEquiv_symm_apply_spec
    (φ : {φ : C₀(Y, ℂ) →⋆ₙₐ[ℂ] 𝓜(ℂ, C₀(X, ℂ)) // φ.IsMultiplierNondegenerate})
    (f : C₀(Y, ℂ)) (x : X) :
    f ((multiplierMorphismEquiv X Y).symm φ x) = (φ.1 f).toBCF x := by
  simp [multiplierMorphismEquiv]

/-- Under `multiplierMorphismEquiv`, composition of continuous maps corresponds contravariantly to
composition of multiplier morphisms through `extendToMultiplier`. -/
theorem multiplierMorphismEquiv_comp [TopologicalSpace Z] [WeaklyLocallyCompactSpace Z]
    [T2Space Z] (h₁ : C(X, Y)) (h₂ : C(Y, Z)) :
    (multiplierMorphismEquiv X Z (h₂.comp h₁) : C₀(Z, ℂ) →⋆ₙₐ[ℂ] 𝓜(ℂ, C₀(X, ℂ))) =
      ((multiplierMorphismEquiv X Y h₁).1.extendToMultiplier
        (multiplierMorphismEquiv X Y h₁).2).toNonUnitalStarAlgHom.comp
          (multiplierMorphismEquiv Y Z h₂).1 :=
  (extendToMultiplier_comp_compZeroAtInftyToMultiplier h₁ h₂ _).symm

/-- The inverse of `multiplierMorphismEquiv` turns composition of nondegenerate multiplier morphisms
through `extendToMultiplier` into contravariant composition of continuous maps. -/
@[simp]
theorem multiplierMorphismEquiv_symm_extendToMultiplier_comp [TopologicalSpace Z]
    [WeaklyLocallyCompactSpace Z] [T2Space Z]
    (φ₁ : {φ : C₀(Y, ℂ) →⋆ₙₐ[ℂ] 𝓜(ℂ, C₀(X, ℂ)) // φ.IsMultiplierNondegenerate})
    (φ₂ : {φ : C₀(Z, ℂ) →⋆ₙₐ[ℂ] 𝓜(ℂ, C₀(Y, ℂ)) // φ.IsMultiplierNondegenerate}) :
    (multiplierMorphismEquiv X Z).symm
      ⟨(φ₁.1.extendToMultiplier φ₁.2).toNonUnitalStarAlgHom.comp φ₂.1,
        φ₁.2.extendToMultiplier_comp φ₂.2⟩ =
      ((multiplierMorphismEquiv Y Z).symm φ₂).comp ((multiplierMorphismEquiv X Y).symm φ₁) := by
  apply (multiplierMorphismEquiv X Z).injective
  apply Subtype.ext
  rw [Equiv.apply_symm_apply, multiplierMorphismEquiv_comp]
  simp only [Equiv.apply_symm_apply]

end MultiplierMorphismEquiv

section MultiplierMorphismEquivId

variable {X : Type*} [TopologicalSpace X] [WeaklyLocallyCompactSpace X] [T2Space X]

/-- Under `multiplierMorphismEquiv`, the identity map corresponds to `DoubleCentralizer.coeHom`. -/
theorem multiplierMorphismEquiv_id :
    (multiplierMorphismEquiv X X (ContinuousMap.id X) : C₀(X, ℂ) →⋆ₙₐ[ℂ] 𝓜(ℂ, C₀(X, ℂ))) =
      DoubleCentralizer.coeHom (𝕜 := ℂ) :=
  compZeroAtInftyToMultiplier_id

/-- The inverse of `multiplierMorphismEquiv` sends `DoubleCentralizer.coeHom` to the identity
map. -/
@[simp]
theorem multiplierMorphismEquiv_symm_coeHom :
    (multiplierMorphismEquiv X X).symm
      ⟨DoubleCentralizer.coeHom (𝕜 := ℂ),
        NonUnitalStarAlgHom.isMultiplierNondegenerate_coeHom⟩ =
      ContinuousMap.id X := by
  apply (multiplierMorphismEquiv X X).injective
  apply Subtype.ext
  simp

end MultiplierMorphismEquivId

section Properness

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
  [WeaklyLocallyCompactSpace Y] [T2Space Y]

/-- A continuous map `h : C(X, Y)` into a weakly locally compact Hausdorff space is proper if and
only if `f ∘ h` vanishes at infinity for every `f : C₀(Y, A)`. -/
theorem isProperMap_iff_forall_tendsto_zeroAtInfty (A : Type*) [NormedAddCommGroup A]
    [NormedSpace ℝ A] [Nontrivial A] (h : C(X, Y)) :
    IsProperMap h ↔ ∀ f : C₀(Y, A), Tendsto (f ∘ h) (cocompact X) (𝓝 0) := by
  refine ⟨fun hh f => (zero_at_infty f).comp (isProperMap_iff_tendsto_cocompact.1 hh).2,
    fun H => ?_⟩
  rw [isProperMap_iff_isCompact_preimage]
  refine ⟨h.continuous, fun K hK => ?_⟩
  obtain ⟨a, ha⟩ := exists_ne (0 : A)
  obtain ⟨χ, hχK, -, hχ_supp, -⟩ :=
    exists_continuous_one_zero_of_isCompact hK isClosed_empty (Set.disjoint_empty K)
  let f : C₀(Y, A) :=
    ⟨⟨fun y => χ y • a, χ.continuous.smul continuous_const⟩,
      (hχ_supp.comp_left (g := fun r : ℝ => r • a) (zero_smul ℝ a)).is_zero_at_infty⟩
  have hapos : 0 < ‖a‖ := norm_pos_iff.2 ha
  obtain ⟨L, hL, hLf⟩ := mem_cocompact.1 (Metric.tendsto_nhds.1 (H f) ‖a‖ hapos)
  refine hL.of_isClosed_subset (hK.isClosed.preimage h.continuous) fun x hx => ?_
  by_contra hxL
  have hlt : ‖f (h x)‖ < ‖a‖ := by simpa [dist_zero_right] using hLf hxL
  have heq : f (h x) = a := by simp [f, hχK hx]
  exact hlt.ne (congrArg norm heq)

/-- A continuous map `h : C(X, Y)` into a weakly locally compact Hausdorff space is proper if and
only if `h.compZeroAtInftyToBCF 𝕜 A` lands in the canonical image of `C₀(X, A)` inside `X →ᵇ A`. -/
theorem isProperMap_iff_range_compZeroAtInftyToBCF_subset (𝕜 A : Type*) [SeminormedRing 𝕜]
    [NonUnitalNormedRing A] [StarRing A] [NormedStarGroup A] [Module 𝕜 A] [IsBoundedSMul 𝕜 A]
    [NormedSpace ℝ A] [Nontrivial A] (h : C(X, Y)) :
    IsProperMap h ↔
      Set.range (h.compZeroAtInftyToBCF 𝕜 A) ⊆
        Set.range (ZeroAtInftyContinuousMap.toBCF : C₀(X, A) → (X →ᵇ A)) := by
  rw [isProperMap_iff_forall_tendsto_zeroAtInfty A h]
  refine ⟨fun H _ ⟨f, hf⟩ => hf ▸ ⟨⟨f.toContinuousMap.comp h, H f⟩, by ext x; rfl⟩,
    fun H f => ?_⟩
  obtain ⟨g, hg⟩ := H ⟨f, rfl⟩
  have heq : (f ∘ h : X → A) = g := funext fun x => (congr($hg x)).symm
  rw [heq]
  exact zero_at_infty g

/-- For weakly locally compact `R₁` `X` and weakly locally compact Hausdorff `Y`, a continuous map
`h : C(X, Y)` is proper if and only if `h.compZeroAtInftyToMultiplier 𝕜 A` lands in the canonical
image of `C₀(X, A)` inside `𝓜(𝕜, C₀(X, A))`. -/
theorem isProperMap_iff_range_compZeroAtInftyToMultiplier_subset [WeaklyLocallyCompactSpace X]
    [R1Space X] (𝕜 A : Type*) [NontriviallyNormedField 𝕜] [StarRing 𝕜] [NormedRing A]
    [NormedAlgebra 𝕜 A] [NormedSpace ℝ A] [StarRing A] [NormedStarGroup A] [StarModule 𝕜 A]
    [Nontrivial A] (h : C(X, Y)) :
    IsProperMap h ↔
      Set.range (h.compZeroAtInftyToMultiplier 𝕜 A) ⊆
        Set.range (DoubleCentralizer.coe 𝕜 : C₀(X, A) → 𝓜(𝕜, C₀(X, A))) := by
  rw [isProperMap_iff_forall_tendsto_zeroAtInfty A h]
  refine ⟨fun H _ ⟨f, hf⟩ => ?_, fun H f => ?_⟩
  · rw [← hf, DoubleCentralizer.mem_range_coe_iff_tendsto_cocompact]
    simpa [Function.comp_def] using H f
  · have hmem := H ⟨f, rfl⟩
    rw [DoubleCentralizer.mem_range_coe_iff_tendsto_cocompact] at hmem
    simpa [Function.comp_def] using hmem

/-- Under `multiplierMorphismEquiv`, the recovered continuous map
`(multiplierMorphismEquiv X Y).symm φ` is proper if and only if `φ` lands in the canonical image
of `C₀(X, ℂ)` inside `𝓜(ℂ, C₀(X, ℂ))`. -/
theorem isProperMap_multiplierMorphismEquiv_symm_iff [WeaklyLocallyCompactSpace X] [R1Space X]
    (φ : {φ : C₀(Y, ℂ) →⋆ₙₐ[ℂ] 𝓜(ℂ, C₀(X, ℂ)) // φ.IsMultiplierNondegenerate}) :
    IsProperMap ((multiplierMorphismEquiv X Y).symm φ) ↔
      Set.range φ.1 ⊆ Set.range (DoubleCentralizer.coe ℂ : C₀(X, ℂ) → 𝓜(ℂ, C₀(X, ℂ))) := by
  rw [isProperMap_iff_range_compZeroAtInftyToMultiplier_subset ℂ ℂ]
  have h : ((multiplierMorphismEquiv X Y).symm φ).compZeroAtInftyToMultiplier ℂ ℂ = φ.1 :=
    congrArg Subtype.val ((multiplierMorphismEquiv X Y).apply_symm_apply φ)
  rw [h]

end Properness

end ContinuousMap
