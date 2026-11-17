/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.CStarAlgebra.ContinuousMap
public import Mathlib.Topology.Maps.Proper.Basic
public import TauCeti.Analysis.CStarAlgebra.Multiplier.Nondegenerate
public import TauCeti.Analysis.CStarAlgebra.Multiplier.ZeroAtInfty
public import TauCeti.Topology.ContinuousMap.ZeroAtInfty.Pullback
import TauCeti.Analysis.CStarAlgebra.ApproximateUnit

/-!
# Commutative multiplier morphisms

For a continuous map `h : C(X, Y)`, precomposition defines a pullback into bounded continuous
functions `ContinuousMap.compZeroAtInftyToBCF : C₀(Y, A) →⋆ₙₐ[𝕜] (X →ᵇ A)` (in
`TauCeti.Topology.ContinuousMap.ZeroAtInfty.Pullback`) and, by composing with
`BoundedContinuousFunction.toDoubleCentralizerNonUnitalStarAlgHom`, a multiplier homomorphism
`ContinuousMap.compZeroAtInftyToMultiplier : C₀(Y, A) →⋆ₙₐ[𝕜] 𝓜(𝕜, C₀(X, A))`
(`ContinuousMap.compZeroAtInftyToMultiplier_eq_comp`). No properness of `h` is required for the
image to land in `𝓜(𝕜, C₀(X, A))`.

When `Y` is weakly locally compact `R₁` and `A` is any (possibly non-unital) C⋆-algebra, Urysohn
cutoffs on compact images `h '' K` paired with an approximate unit of `A` show that
`h.compZeroAtInftyToMultiplier ℂ A` is nondegenerate
(`ContinuousMap.isMultiplierNondegenerate_compZeroAtInftyToMultiplier`), and composition of
multiplier morphisms through `extendToMultiplier` corresponds contravariantly to composition of
continuous maps (`ContinuousMap.extendToMultiplier_comp_compZeroAtInftyToMultiplier`). When `A` is
unital, the unique extension `extendToMultiplier` acts on `𝓜(ℂ, C₀(Y, A))` by precomposing the
representing bounded continuous function with `h`
(`ContinuousMap.extendToMultiplier_compZeroAtInftyToMultiplier`).

When `X` is weakly locally compact `R₁` and `A` is any (possibly non-unital) C⋆-algebra,
nondegeneracy of `φ : A →⋆ₙₐ[ℂ] 𝓜(ℂ, C₀(X, ℂ))` is equivalent to pointwise nonvanishing of
`a ↦ (φ a).toBCF x`
(`NonUnitalStarAlgHom.isMultiplierNondegenerate_iff_forall_exists_toBCF_ne_zero`). Specializing to
`A = C₀(Y, ℂ)` for a weakly locally compact Hausdorff space `Y` and combining this with
`ContinuousMap.bcfMorphismEquiv` establishes the contravariant bijection
`ContinuousMap.multiplierMorphismEquiv` between `C(X, Y)` and nondegenerate multiplier
homomorphisms `C₀(Y, ℂ) →⋆ₙₐ[ℂ] 𝓜(ℂ, C₀(X, ℂ))`. Finally, for weakly locally compact `R₁` `X`,
weakly locally compact Hausdorff `Y`, and nontrivial unital `A`, `h.compZeroAtInftyToMultiplier`
lands in the canonical image of `C₀(X, A)` if and only if `h` is proper
(`ContinuousMap.isProperMap_iff_range_compZeroAtInftyToMultiplier_subset`).

## Main definitions

* `ContinuousMap.compZeroAtInftyToMultiplier`: pullback `C₀(Y, A) →⋆ₙₐ[𝕜] 𝓜(𝕜, C₀(X, A))`.
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
* `ContinuousMap.isProperMap_iff_range_compZeroAtInftyToMultiplier_subset` and
  `ContinuousMap.isProperMap_multiplierMorphismEquiv_symm_iff`: characterization of proper maps as
  those whose multiplier pullback lands in `C₀(X, A)`.

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

/-- Shared cocompact ε-approximation criterion for proving `φ.IsMultiplierNondegenerate` when
`φ` takes values in `𝓜(ℂ, C₀(X, A))`: it suffices that on every compact set `K` and for every
`g : C₀(X, A)` and `δ > 0`, some `φ b` acts by left multiplication by a bounded continuous function
`u` of pointwise norm at most `1` satisfying `‖u x * g x - g x‖ ≤ δ` on `K`. -/
private theorem isMultiplierNondegenerate_of_compact_approx
    {X A B : Type*} [TopologicalSpace X] [NonUnitalCStarAlgebra A] [NonUnitalCStarAlgebra B]
    {φ : B →⋆ₙₐ[ℂ] 𝓜(ℂ, C₀(X, A))}
    (happrox : ∀ (g : C₀(X, A)) (K : Set X), IsCompact K → ∀ δ > 0,
      ∃ (b : B) (u : X →ᵇ A), φ b = u.toDoubleCentralizer ℂ ∧
        (∀ x, ‖u x‖ ≤ 1) ∧ ∀ x ∈ K, ‖u x * g x - g x‖ ≤ δ) :
    φ.IsMultiplierNondegenerate := by
  rw [NonUnitalStarAlgHom.isMultiplierNondegenerate_iff_dense, Metric.dense_iff]
  intro g ε hε
  obtain ⟨K, hK, hKg⟩ := mem_cocompact.1 <|
    Metric.tendsto_nhds.1 (zero_at_infty g) (ε / 4) (by positivity)
  obtain ⟨b, u, hφb, hu_norm, huK⟩ := happrox g K hK (ε / 2) (half_pos hε)
  refine ⟨(φ b).fst g, ?_, Submodule.subset_span <| Set.mem_iUnion.2 ⟨b, g, rfl⟩⟩
  rw [Metric.mem_ball, dist_eq_norm]
  have hle : ‖(φ b).fst g - g‖ ≤ ε / 2 := by
    rw [ZeroAtInftyContinuousMap.norm_le (half_pos hε).le]
    intro x
    have hval : ((φ b).fst g - g) x = u x * g x - g x := by simp [hφb]
    rw [hval]
    by_cases hx : x ∈ K
    · exact huK x hx
    · have hdist : ‖g x‖ < ε / 4 := by simpa [dist_zero_right] using hKg hx
      have hmul : ‖u x * g x‖ ≤ ‖g x‖ :=
        (norm_mul_le _ _).trans <| by
          simpa using mul_le_mul_of_nonneg_right (hu_norm x) (norm_nonneg _)
      linarith [norm_sub_le (u x * g x) (g x)]
  exact hle.trans_lt (half_lt_self hε)

namespace ContinuousMap

section Pullback

variable {𝕜 X Y A : Type*} [TopologicalSpace X] [TopologicalSpace Y]
  [NontriviallyNormedField 𝕜] [StarRing 𝕜] [NonUnitalNormedRing A] [StarRing A]
  [NormedStarGroup A] [NormedSpace 𝕜 A] [SMulCommClass 𝕜 A A] [IsScalarTower 𝕜 A A]
  [StarModule 𝕜 A]

variable (𝕜 A) in
/-- Precomposition by a continuous map `h : C(X, Y)` defines a multiplier `⋆`-homomorphism
`C₀(Y, A) →⋆ₙₐ[𝕜] 𝓜(𝕜, C₀(X, A))`. -/
def compZeroAtInftyToMultiplier (h : C(X, Y)) : C₀(Y, A) →⋆ₙₐ[𝕜] 𝓜(𝕜, C₀(X, A)) :=
  (BoundedContinuousFunction.toDoubleCentralizerNonUnitalStarAlgHom 𝕜 X A).comp
    (h.compZeroAtInftyToBCF 𝕜 A)

/-- `compZeroAtInftyToMultiplier` is the composition of
`BoundedContinuousFunction.toDoubleCentralizerNonUnitalStarAlgHom` with `compZeroAtInftyToBCF`. -/
theorem compZeroAtInftyToMultiplier_eq_comp (h : C(X, Y)) :
    h.compZeroAtInftyToMultiplier 𝕜 A =
      (BoundedContinuousFunction.toDoubleCentralizerNonUnitalStarAlgHom 𝕜 X A).comp
        (h.compZeroAtInftyToBCF 𝕜 A) :=
  (rfl)

/-- Applying `compZeroAtInftyToMultiplier` yields the multiplier attached to
`f.toBCF.compContinuous h`. -/
@[simp]
theorem compZeroAtInftyToMultiplier_apply (h : C(X, Y)) (f : C₀(Y, A)) :
    h.compZeroAtInftyToMultiplier 𝕜 A f =
      (f.toBCF.compContinuous h).toDoubleCentralizer 𝕜 := by
  simp [compZeroAtInftyToMultiplier_eq_comp]

/-- Pullback along the identity map is the canonical inclusion `DoubleCentralizer.coeHom`. -/
@[simp]
theorem compZeroAtInftyToMultiplier_id :
    (ContinuousMap.id X).compZeroAtInftyToMultiplier 𝕜 A =
      DoubleCentralizer.coeHom (𝕜 := 𝕜) := by
  rw [compZeroAtInftyToMultiplier_eq_comp, compZeroAtInftyToBCF_id,
    BoundedContinuousFunction.toDoubleCentralizerNonUnitalStarAlgHom_comp_toBCFNonUnitalStarAlgHom]

/-- On a cocompact map `h : CocompactMap X Y`, pullback into the multiplier algebra agrees with
`ZeroAtInftyContinuousMap.comp` composed with `DoubleCentralizer.coe`. -/
theorem compZeroAtInftyToMultiplier_apply_eq_coe_comp (h : CocompactMap X Y) (f : C₀(Y, A)) :
    h.toContinuousMap.compZeroAtInftyToMultiplier 𝕜 A f = (f.comp h : 𝓜(𝕜, C₀(X, A))) :=
  DoubleCentralizer.ext_fst_snd
    (fun _ => ZeroAtInftyContinuousMap.ext fun _ => by simp)
    (fun _ => ZeroAtInftyContinuousMap.ext fun _ => by simp)

end Pullback

section PullbackUnital

variable {𝕜 X Y A : Type*} [TopologicalSpace X] [WeaklyLocallyCompactSpace X] [R1Space X]
  [TopologicalSpace Y] [NontriviallyNormedField 𝕜] [StarRing 𝕜] [NormedRing A]
  [NormedAlgebra 𝕜 A] [NormedSpace ℝ A] [StarRing A] [NormedStarGroup A] [StarModule 𝕜 A]

/-- Under `DoubleCentralizer.toBCF`, the multiplier pullback `compZeroAtInftyToMultiplier` recovers
the bounded continuous function pullback `compZeroAtInftyToBCF`. -/
theorem toBCF_compZeroAtInftyToMultiplier (h : C(X, Y)) (f : C₀(Y, A)) :
    (h.compZeroAtInftyToMultiplier 𝕜 A f).toBCF = h.compZeroAtInftyToBCF 𝕜 A f := by
  simp

end PullbackUnital

section Nondegenerate

variable {X Y Z A : Type*} [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]

/-- Pullback along any continuous map `h : C(X, Y)` into a weakly locally compact `R₁` space is a
nondegenerate multiplier homomorphism `C₀(Y, A) →⋆ₙₐ[ℂ] 𝓜(ℂ, C₀(X, A))` for every (possibly
non-unital) C⋆-algebra `A`. -/
theorem isMultiplierNondegenerate_compZeroAtInftyToMultiplier [WeaklyLocallyCompactSpace Y]
    [R1Space Y] [NonUnitalCStarAlgebra A] (h : C(X, Y)) :
    (h.compZeroAtInftyToMultiplier ℂ A).IsMultiplierNondegenerate := by
  refine isMultiplierNondegenerate_of_compact_approx fun g K hK δ hδ => ?_
  let := CStarAlgebra.spectralOrder A
  have := CStarAlgebra.spectralOrderedRing A
  have hl := CStarAlgebra.increasingApproximateUnit A
  have := hl.neBot
  obtain ⟨e, he_norm, he_mul⟩ := (hl.eventually_norm.and <|
    Metric.tendstoUniformlyOn_iff.1 (hl.tendstoUniformlyOn_mul_right (hK.image g.continuous))
      δ hδ).exists
  obtain ⟨f, hfK, -, hf_norm⟩ :=
    ZeroAtInftyContinuousMap.exists_eqOn_const_of_isCompact (hK.image h.continuous) e
  refine ⟨f, h.compZeroAtInftyToBCF ℂ A f, by simp,
    fun x => by simpa using (f.norm_coe_le_norm (h x)).trans (hf_norm.trans he_norm),
    fun x hx => ?_⟩
  simp only [compZeroAtInftyToBCF_apply, BoundedContinuousFunction.compContinuous_apply,
    ZeroAtInftyContinuousMap.toBCF_apply]
  rw [hfK ⟨x, hx, rfl⟩, norm_sub_rev]
  simpa [dist_eq_norm] using (he_mul (g x) ⟨x, hx, rfl⟩).le

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
  obtain ⟨e, he1, -⟩ := ZeroAtInftyContinuousMap.exists_apply_eq_norm_le x (1 : ℂ)
  exact one_ne_zero (he1.symm.trans (hall e))

/-- When `X` is weakly locally compact `R₁`, a homomorphism `φ : A →⋆ₙₐ[ℂ] 𝓜(ℂ, C₀(X, ℂ))` from
any (possibly non-unital) C⋆-algebra `A` is nondegenerate if and only if `a ↦ (φ a).toBCF x` is
nonzero at every `x : X`. -/
theorem isMultiplierNondegenerate_iff_forall_exists_toBCF_ne_zero
    (φ : A →⋆ₙₐ[ℂ] 𝓜(ℂ, C₀(X, ℂ))) :
    φ.IsMultiplierNondegenerate ↔ ∀ x : X, ∃ a : A, (φ a).toBCF x ≠ 0 := by
  refine ⟨fun hφ => hφ.exists_toBCF_ne_zero, fun h => ?_⟩
  refine isMultiplierNondegenerate_of_compact_approx fun g K hK δ hδ => ?_
  -- If `K` is empty, `b = 0` satisfies the compact-approximation hypothesis vacuously.
  rcases K.eq_empty_or_nonempty with rfl | hKne
  · exact ⟨0, 0, by simp, fun _ => by simp, fun _ hx => hx.elim⟩
  -- Compact subcover: combine pointwise nonvanishing into `q : A` with `(φ q).toBCF ∈ [c, 1]`
  -- on `K`.
  obtain ⟨q, c, ⟨hc0, hc1⟩, hq⟩ := exists_real_pos_on_compact φ h hK hKne
  -- Polynomial iterate: choose `n` so `(1 - c) ^ n * ‖g‖ < δ`.
  have hlim : Tendsto (fun n : ℕ => (1 - c) ^ n * ‖g‖) atTop (𝓝 0) := by
    simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one (by linarith) (by linarith)).mul_const ‖g‖
  obtain ⟨n, hn⟩ := (Metric.tendsto_nhds.1 hlim δ hδ).exists
  have hn' : (1 - c) ^ n * ‖g‖ < δ := by
    simpa [Real.dist_eq, abs_of_nonneg (sub_nonneg.2 hc1.le)] using hn
  have honeSub (z : X) {t : ℝ} (hqt : (φ q).toBCF z = (t : ℂ)) :
      1 - (φ (oneSubPow q n)).toBCF z = (((1 - t) ^ n : ℝ) : ℂ) := by
    simpa [hqt] using one_sub_map_oneSubPow φ q z n
  refine ⟨oneSubPow q n, (φ (oneSubPow q n)).toBCF,
    (DoubleCentralizer.toDoubleCentralizer_toBCF _).symm, fun z => ?_, fun z hz => ?_⟩
  · -- Everywhere on `X`, `(φ (oneSubPow q n)).toBCF z = 1 - (1 - t) ^ n ∈ [0, 1]`.
    obtain ⟨t, ⟨ht0, ht1⟩, hqt, -⟩ := hq z
    have hval : (φ (oneSubPow q n)).toBCF z = ((1 - (1 - t) ^ n : ℝ) : ℂ) := by
      rw [Complex.ofReal_sub, Complex.ofReal_one]
      linear_combination -honeSub z hqt
    rw [hval, Complex.norm_real,
      Real.norm_of_nonneg (sub_nonneg.2 (pow_le_one₀ (by linarith) (by linarith)))]
    linarith [pow_nonneg (show 0 ≤ 1 - t by linarith) n]
  · -- On `K`, `1 - t ≤ 1 - c`, so `‖((φ (oneSubPow q n)).toBCF z - 1) * g z‖ ≤ (1 - c) ^ n * ‖g‖`.
    obtain ⟨t, ⟨-, ht1⟩, hqt, hKct⟩ := hq z
    have hval : (φ (oneSubPow q n)).toBCF z * g z - g z = -(((1 - t) ^ n : ℝ) : ℂ) * g z := by
      linear_combination -(g z * honeSub z hqt)
    rw [hval, norm_mul, norm_neg, Complex.norm_real,
      Real.norm_of_nonneg (pow_nonneg (by linarith) n)]
    have hpow : (1 - t) ^ n ≤ (1 - c) ^ n :=
      pow_le_pow_left₀ (by linarith) (by linarith [hKct hz]) n
    exact (mul_le_mul hpow (g.norm_coe_le_norm z) (norm_nonneg _)
      (pow_nonneg (by linarith) n)).trans hn'.le

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
  rw [isProperMap_iff_forall_tendsto_cocompact_nhds_zero A h]
  refine ⟨fun H _ ⟨f, hf⟩ => ?_, fun H f => ?_⟩
  · rw [← hf, DoubleCentralizer.mem_range_coe_iff_tendsto_cocompact_nhds_zero]
    simpa [Function.comp_def] using H f
  · have hmem := H ⟨f, rfl⟩
    rw [DoubleCentralizer.mem_range_coe_iff_tendsto_cocompact_nhds_zero] at hmem
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
