/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.InnerProductSpace.PointSpectrum
public import TauCeti.Analysis.InnerProductSpace.Positive.FunctionalCalculus
import TauCeti.Analysis.InnerProductSpace.FunctionalCalculusComparison

/-!
# Smooth positive and negative spectral projections

For an invertible self-adjoint operator `A` on a finite-dimensional real inner product space,
the orthogonal projections onto its negative and positive spectral subspaces are
`(1 - A * (A * A) ^ (-(1 / 2))) / 2` and
`(1 + A * (A * A) ^ (-(1 / 2))) / 2`, respectively.
Consequently these native spectral projections depend smoothly, even real analytically, on
`A` as long as it remains self-adjoint and invertible. No smoothly varying eigenbasis is needed.

These formulas supply smooth local projections for splitting a nondegenerate symmetric form
into its positive and negative subbundles. They concern the existing
`Module.End.pointSpectralSubspace` and `Submodule.starProjection`, not new choices of subspaces
or projections. The invertibility hypothesis excludes eigenvalues crossing zero; dimension zero
is allowed.

Continuity of the spectral projections of a family of operators at a point `x₀` lets a basis of
a spectral subspace at `x₀` be transported to nearby points: its projections stay linearly
independent (`TauCeti.eventually_linearIndependent_starProjection_apply`). For injective symmetric
operators, counting the dimensions of the complementary negative and positive spectral subspaces
shows that the projected basis of the negative spectral subspace is again a basis
(`TauCeti.eventually_linearIndependent_and_span_starProjection_Iio`). These give local frames of
the spectral subbundles of a symmetric bundle endomorphism.

## References

* R. Bhatia, *Matrix Analysis*, Springer, 1997, Chapter V (matrix functions).
* R. Bott, *Nondegenerate critical manifolds*, Annals of Mathematics 60 (1954), 248–261.
-/

public section

noncomputable section

open Set
open scoped ContDiff

namespace ContinuousLinearMap

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

/-- The negative spectral projection of an invertible self-adjoint operator, expressed using
its inverse absolute value. This formula requires no choice of eigenbasis. -/
theorem starProjection_pointSpectralSubspace_Iio_zero_eq (A : E →L[ℝ] E) (hA : IsSelfAdjoint A)
    (hunit : IsUnit A) :
    (Module.End.pointSpectralSubspace A.toLinearMap (Iio 0)).starProjection =
      (1 / 2 : ℝ) • (1 - A * (A * A) ^ (-(1 / 2) : ℝ)) := by
  have hs := isSelfAdjoint_iff_isSymmetric.mp hA
  apply coe_injective
  rw [hs.coe_starProjection_pointSpectralSubspace]
  symm
  apply (hs.eq_cfc_iff _).mpr
  intro μ v hv
  simp only [coe_coe, RCLike.ofReal_real_eq_id, id_eq] at hv
  by_cases hv0 : v = 0
  · simp [hv0]
  have hμ : μ ≠ 0 := by
    intro hμ
    apply hv0
    exact (isUnit_iff_bijective.mp hunit).injective (by simpa [hμ] using hv)
  -- The inverse square root of `A²` acts by `|μ|⁻¹` on a `μ`-eigenvector.
  have hpos : 0 ≤ A * A := by simpa only [hA.star_eq] using star_mul_self_nonneg A
  have heig : (A * A) v = μ ^ 2 • v := by
    simp only [mul_apply_eq_comp, hv, map_smul, smul_smul, pow_two]
  have hpow : ((A * A) ^ (-(1 / 2) : ℝ)) v = |μ|⁻¹ • v := by
    rw [CFC.rpow_eq_cfc_real hpos,
      cfc_apply_of_apply_eq_smul (fun r : ℝ ↦ r ^ (-(1 / 2) : ℝ)) heig
        (nonneg_iff_isPositive.mp hpos).isSelfAdjoint]
    simp only [RCLike.ofReal_real_eq_id, id_eq]
    congr 1
    exact (Real.rpow_neg (sq_nonneg μ) (1 / 2)).trans
      (congrArg Inv.inv ((Real.sqrt_eq_rpow (μ ^ 2)).symm.trans (Real.sqrt_sq_eq_abs μ)))
  simp only [toLinearMap_smul, toLinearMap_sub, toLinearMap_one, LinearMap.smul_apply,
    LinearMap.sub_apply, one_apply_eq_self, coe_coe, mul_apply_eq_comp, hpow, map_smul, hv,
    smul_smul, RCLike.ofReal_real_eq_id, id_eq]
  by_cases hneg : μ < 0
  · rw [indicator_of_mem hneg, Pi.one_apply, abs_of_neg hneg]
    have hratio : (-μ)⁻¹ * μ = -1 := by simp [hμ]
    rw [hratio]
    module
  · rw [indicator_of_notMem hneg, abs_of_pos (lt_of_le_of_ne (le_of_not_gt hneg) hμ.symm),
      inv_mul_cancel₀ hμ]
    module

/-- The positive spectral projection of an invertible self-adjoint operator, expressed using
its inverse absolute value. -/
theorem starProjection_pointSpectralSubspace_Ioi_zero_eq (A : E →L[ℝ] E) (hA : IsSelfAdjoint A)
    (hunit : IsUnit A) :
    (Module.End.pointSpectralSubspace A.toLinearMap (Ioi 0)).starProjection =
      (1 / 2 : ℝ) • (1 + A * (A * A) ^ (-(1 / 2) : ℝ)) := by
  simpa only [toLinearMap_neg, Module.End.pointSpectralSubspace_neg, neg_Iio, neg_zero,
    neg_mul_neg, neg_mul, mul_neg, neg_neg, sub_neg_eq_add] using
    starProjection_pointSpectralSubspace_Iio_zero_eq (-A) hA.neg hunit.neg

variable {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
  {n : ℕ∞ω} {A : P → E →L[ℝ] E} {s : Set P}

/-- The negative spectral projections of a smooth family of invertible self-adjoint operators
form a smooth family, including at real analytic regularity. -/
theorem _root_.ContDiffOn.starProjection_pointSpectralSubspace_Iio_zero (hA : ContDiffOn ℝ n A s)
    (hself : ∀ x ∈ s, IsSelfAdjoint (A x)) (hunit : ∀ x ∈ s, IsUnit (A x)) :
    ContDiffOn ℝ n
      (fun x ↦ (Module.End.pointSpectralSubspace (A x).toLinearMap (Iio 0)).starProjection) s := by
  have hpos (x) (hx : x ∈ s) : IsStrictlyPositive (A x * A x) :=
    ((hunit x hx).mul (hunit x hx)).isStrictlyPositive (by
      simpa only [(hself x hx).star_eq] using star_mul_self_nonneg (A x))
  have hpow := (contDiffOn_rpow (E := E) (n := n) (-(1 / 2))).comp (hA.mul hA) hpos
  exact (((contDiffOn_const (c := (1 : E →L[ℝ] E))).sub (hA.mul hpow)).const_smul
    (1 / 2 : ℝ)).congr
    fun x hx ↦ starProjection_pointSpectralSubspace_Iio_zero_eq (A x) (hself x hx) (hunit x hx)

/-- The positive spectral projections of a smooth family of invertible self-adjoint operators
form a smooth family, including at real analytic regularity. -/
theorem _root_.ContDiffOn.starProjection_pointSpectralSubspace_Ioi_zero (hA : ContDiffOn ℝ n A s)
    (hself : ∀ x ∈ s, IsSelfAdjoint (A x)) (hunit : ∀ x ∈ s, IsUnit (A x)) :
    ContDiffOn ℝ n
      (fun x ↦ (Module.End.pointSpectralSubspace (A x).toLinearMap (Ioi 0)).starProjection) s := by
  simpa only [Pi.neg_apply, toLinearMap_neg, Module.End.pointSpectralSubspace_neg,
    neg_Iio, neg_zero] using hA.neg.starProjection_pointSpectralSubspace_Iio_zero
      (fun x hx ↦ (hself x hx).neg) (fun x hx ↦ (hunit x hx).neg)

end ContinuousLinearMap

namespace TauCeti

open Filter Module
open scoped Topology

section ProjectedBasis

variable {X : Type*} [TopologicalSpace X]
  {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  {S : X → E →L[ℝ] E} {x₀ : X}

/-- Projecting linearly independent vectors of a point-spectral subspace of `S x₀` onto the same
point-spectral subspace of `S x` keeps them linearly independent for `x` near `x₀`, when the
spectral projections are continuous at `x₀`. -/
theorem eventually_linearIndependent_starProjection_apply {Ω : Set ℝ}
    (hP : ContinuousAt
      (fun x ↦ (Module.End.pointSpectralSubspace (S x).toLinearMap Ω).starProjection) x₀)
    {ι : Type*} [Finite ι] {b : ι → E} (hb : LinearIndependent ℝ b)
    (hbΩ : ∀ i, b i ∈ Module.End.pointSpectralSubspace (S x₀).toLinearMap Ω) :
    ∀ᶠ x in 𝓝 x₀, LinearIndependent ℝ fun i ↦
      (Module.End.pointSpectralSubspace (S x).toLinearMap Ω).starProjection (b i) := by
  have h₀ : (fun i ↦
      (Module.End.pointSpectralSubspace (S x₀).toLinearMap Ω).starProjection (b i)) = b :=
    funext fun i ↦ Submodule.starProjection_eq_self_iff.mpr (hbΩ i)
  have hb' := hb.eventually
  rw [← h₀] at hb'
  exact (continuousAt_pi.2 fun i ↦ hP.clm_apply continuousAt_const).eventually hb'

/-- For injective symmetric operators `S x` whose negative and positive spectral projections are
continuous at `x₀`, projecting a basis of the negative spectral subspace of `S x₀` gives, for every
`x` near `x₀`, a basis of the negative spectral subspace of `S x`. -/
theorem eventually_linearIndependent_and_span_starProjection_Iio
    (hS : ∀ᶠ x in 𝓝 x₀,
      (S x).toLinearMap.IsSymmetric ∧ LinearMap.ker (S x).toLinearMap = ⊥)
    (hN : ContinuousAt
      (fun x ↦ (Module.End.pointSpectralSubspace (S x).toLinearMap (Iio 0)).starProjection) x₀)
    (hP : ContinuousAt
      (fun x ↦ (Module.End.pointSpectralSubspace (S x).toLinearMap (Ioi 0)).starProjection) x₀)
    {k : ℕ} (b : Basis (Fin k) ℝ (Module.End.pointSpectralSubspace (S x₀).toLinearMap (Iio 0))) :
    ∀ᶠ x in 𝓝 x₀, LinearIndependent ℝ (fun i ↦
        (Module.End.pointSpectralSubspace (S x).toLinearMap (Iio 0)).starProjection (b i)) ∧
      Submodule.span ℝ (range fun i ↦
        (Module.End.pointSpectralSubspace (S x).toLinearMap (Iio 0)).starProjection (b i)) =
        Module.End.pointSpectralSubspace (S x).toLinearMap (Iio 0) := by
  -- The negative and positive spectral subspaces are complementary.
  have hcompl : ∀ᶠ x in 𝓝 x₀,
      finrank ℝ (Module.End.pointSpectralSubspace (S x).toLinearMap (Iio 0)) +
        finrank ℝ (Module.End.pointSpectralSubspace (S x).toLinearMap (Ioi 0)) = finrank ℝ E :=
    hS.mono fun x hx ↦
      Submodule.finrank_add_eq_of_isCompl (hx.1.isCompl_pointSpectralSubspace_Iio_Ioi hx.2)
  have hk := Module.finrank_eq_card_basis b
  obtain ⟨bP⟩ : Nonempty (Basis (Fin (finrank ℝ
      (Module.End.pointSpectralSubspace (S x₀).toLinearMap (Ioi 0)))) ℝ
      (Module.End.pointSpectralSubspace (S x₀).toLinearMap (Ioi 0))) :=
    ⟨Module.finBasis ℝ _⟩
  have hN' := eventually_linearIndependent_starProjection_apply (b := fun i ↦ (b i : E)) hN
    (b.linearIndependent.map'
      (Module.End.pointSpectralSubspace (S x₀).toLinearMap (Iio 0)).subtype
      (Submodule.ker_subtype _)) fun i ↦ (b i).2
  have hbP : LinearIndependent ℝ (fun i ↦ (bP i : E)) :=
    LinearIndependent.map' bP.linearIndependent
      (Module.End.pointSpectralSubspace (S x₀).toLinearMap (Ioi 0)).subtype
      (Submodule.ker_subtype _)
  have hP' := eventually_linearIndependent_starProjection_apply (b := fun i ↦ (bP i : E)) hP hbP
    fun i ↦ (bP i).2
  filter_upwards [hN', hP', hcompl] with x hliN hliP hx
  have hle (Ω : Set ℝ) {ι : Type} (c : ι → E) :
      Submodule.span ℝ (range fun i ↦
        (Module.End.pointSpectralSubspace (S x).toLinearMap Ω).starProjection (c i)) ≤
        Module.End.pointSpectralSubspace (S x).toLinearMap Ω :=
    Submodule.span_le.mpr <| range_subset_iff.mpr fun i ↦ Submodule.starProjection_apply_mem _ _
  -- Both projected families are linearly independent, so they fill the complementary spectral
  -- subspaces, whose dimensions add up to `finrank ℝ E`.
  have hleN := hle (Iio 0) fun i ↦ (b i : E)
  have h₁ := (finrank_span_eq_card hliN).symm.trans_le (Submodule.finrank_mono hleN)
  have h₂ := (finrank_span_eq_card hliP).symm.trans_le
    (Submodule.finrank_mono (hle (Ioi 0) fun i ↦ (bP i : E)))
  have h₀ := hcompl.self_of_nhds
  rw [Fintype.card_fin] at h₁ h₂ hk
  refine ⟨hliN, Submodule.eq_of_le_of_finrank_eq hleN ?_⟩
  rw [finrank_span_eq_card hliN, Fintype.card_fin]
  omega

end ProjectedBasis

end TauCeti
