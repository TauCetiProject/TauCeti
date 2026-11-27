/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Convex.Join
public import Mathlib.Analysis.CStarAlgebra.PositiveLinearFunctional
public import Mathlib.Topology.Algebra.Module.Spaces.WeakDual
public import TauCeti.Analysis.CStarAlgebra.State.Space
import Mathlib.Analysis.LocallyConvex.Separation
import Mathlib.LinearAlgebra.Complex.Module
import Mathlib.Topology.Algebra.Star.LinearMap
import TauCeti.Analysis.CStarAlgebra.State.Spectrum
import TauCeti.Analysis.Convex.Topology
import TauCeti.Analysis.LocallyConvex.WeakDual.Basic
import TauCeti.Analysis.Normed.Module.HahnBanach.Basic
import TauCeti.Analysis.Normed.Operator.IntrinsicStar
import TauCeti.Topology.Algebra.Module.WeakSpace.Basic

/-!
# Jordan and four-positive decompositions of bounded functionals

Every bounded self-adjoint (Hermitian) linear functional `φ : A →L[ℂ] ℂ` on a (possibly nonunital)
C⋆-algebra `A` admits a norm-preserving Jordan decomposition `φ = ω₁ - ω₂` with
`ω₁, ω₂ : A →P[ℂ] ℂ` and `‖ω₁‖ + ‖ω₂‖ = ‖φ‖`
(`ContinuousLinearMap.exists_sub_positiveContinuousLinearMap_of_map_star`). For unital algebras,
a nonzero Hermitian `φ` is first normalized to norm `1` before separating it from the weak-*
compact convex set `convexJoin ℝ (TauCeti.stateSpace D) (-TauCeti.stateSpace D)` via Hahn–Banach
and testing against a spectral norm-attaining state
(`ContinuousLinearMap.toWeakDual_mem_convexJoin_stateSpace_of_norm_eq_one`); the nonunital case
follows by norm-preserving Hahn–Banach extension to `Unitization ℂ A` and symmetrization via
`realPart`.

Splitting an arbitrary `φ : A →L[ℂ] ℂ` into its real and imaginary parts gives the four-positive
decomposition (`ContinuousLinearMap.exists_four_positiveContinuousLinearMap`). Consequently, a net
in `A` converges weakly if and only if it converges under every positive continuous linear
functional (`TauCeti.CStarAlgebra.tendsto_toWeakSpace_iff_forall_positiveContinuousLinearMap`).

## References

* B. Blackadar, *Operator Algebras*, II.6.3.4.
* R. V. Kadison and J. R. Ringrose, *Fundamentals of the Theory of Operator Algebras, Vol. I*,
  Theorem 4.3.6.
-/

public section

noncomputable section

open Filter Set Topology Unitization
open scoped CStarAlgebra ComplexOrder NNReal Pointwise

namespace ContinuousLinearMap

section JordanDecomposition

/-- Every norm-one Hermitian continuous linear functional on a unital C⋆-algebra lies in the
convex join of `TauCeti.stateSpace D` and `-TauCeti.stateSpace D` in the weak-* dual. -/
theorem toWeakDual_mem_convexJoin_stateSpace_of_norm_eq_one
    {D : Type*} [CStarAlgebra D] [PartialOrder D] [StarOrderedRing D]
    {ψ : D →L[ℂ] ℂ} (hψ_norm : ‖ψ‖ = 1) (hψ_star : ∀ a, ψ (star a) = star (ψ a)) :
    StrongDual.toWeakDual ψ ∈ convexJoin ℝ (TauCeti.stateSpace D) (-TauCeti.stateSpace D) := by
  have : Nontrivial D := by
    by_contra h
    rw [not_nontrivial_iff_subsingleton] at h
    have h0 : ψ = 0 := ext fun a => by simp [Subsingleton.elim a 0]
    simp [h0] at hψ_norm
  by_contra hnot
  have hconv : Convex ℝ (convexJoin ℝ (TauCeti.stateSpace D) (-TauCeti.stateSpace D)) :=
    TauCeti.convex_stateSpace.convexJoin TauCeti.convex_stateSpace.neg
  have hcomp : IsCompact (convexJoin ℝ (TauCeti.stateSpace D) (-TauCeti.stateSpace D)) :=
    TauCeti.isCompact_stateSpace.convexJoin TauCeti.isCompact_stateSpace.neg
  obtain ⟨L, u, hLu, huψ⟩ :=
    RCLike.geometric_hahn_banach_closed_point (𝕜 := ℂ) (E := WeakDual ℂ D)
      (by exact hconv) hcomp.isClosed hnot
  obtain ⟨x, hx⟩ := WeakDual.exists_forall_apply_eq_apply L
  let h : D := (realPart x : D)
  have hh_sa : IsSelfAdjoint h := (realPart x).property
  have hre_eq : ∀ (η : D →L[ℂ] ℂ), (∀ a, η (star a) = star (η a)) →
      (η h).re = (η x).re := fun η hη => by
    have h1 : η h = ((η x).re : ℂ) := by
      dsimp only [h]
      rw [realPart_apply_coe x, map_smul_of_tower, map_add, hη x, Complex.star_def,
        Complex.add_conj, Complex.real_smul]
      push_cast
      ring
    rw [h1, Complex.ofReal_re]
  have hψ_re : u < (ψ h).re := by
    rw [hre_eq ψ hψ_star]
    simpa [hx, StrongDual.toWeakDual_apply] using huψ
  have hstate_lt : ∀ ω : D →P[ℂ] ℂ, ‖(ω : D →L[ℂ] ℂ)‖ = 1 → |(ω h).re| < u := fun ω hω => by
    have hω_mem : StrongDual.toWeakDual (ω : D →L[ℂ] ℂ) ∈ TauCeti.stateSpace D :=
      ω.toWeakDual_mem_stateSpace_iff.mpr hω
    have hω_re : (ω h).re = (ω x).re := hre_eq (ω : D →L[ℂ] ℂ) (map_star ω)
    have h1 : (ω h).re < u := by
      have := hLu _ (subset_convexJoin_left TauCeti.stateSpace_nonempty.neg hω_mem)
      simpa [hx, StrongDual.toWeakDual_apply, hω_re] using this
    have h2 : -(ω h).re < u := by
      have := hLu _ (subset_convexJoin_right TauCeti.stateSpace_nonempty
        (Set.neg_mem_neg.mpr hω_mem))
      rw [hx, RCLike.re_to_complex, ← map_neg, StrongDual.toWeakDual_apply, neg_apply,
        Complex.neg_re] at this
      simpa [hω_re] using this
    exact abs_lt.mpr ⟨by linarith, h1⟩
  obtain ⟨ω, -, hω_norm, hωh⟩ :=
    TauCeti.CStarAlgebra.exists_positiveContinuousLinearMap_abs_re_apply_eq_norm hh_sa
  have hnorm_lt : ‖h‖ < u := hωh ▸ hstate_lt ω hω_norm
  have hle : (ψ h).re ≤ ‖h‖ :=
    (Complex.re_le_norm (ψ h)).trans <| by simpa [hψ_norm] using ψ.le_opNorm h
  linarith

/-- Nonnegative real scalar multiple of a weak-* state as a `PositiveContinuousLinearMap`. -/
private def smulState {D : Type*} [CStarAlgebra D] [PartialOrder D] [StarOrderedRing D]
    {c : ℝ} (_hc : 0 ≤ c) {η : WeakDual ℂ D} (hη : η ∈ TauCeti.stateSpace D) : D →P[ℂ] ℂ :=
  c.toNNReal • PositiveContinuousLinearMap.mk₀ (WeakDual.toStrongDual η) fun _ ha => by
    simpa [WeakDual.toStrongDual_apply] using TauCeti.map_nonneg_of_mem_stateSpace hη ha

private theorem smulState_apply {D : Type*} [CStarAlgebra D] [PartialOrder D] [StarOrderedRing D]
    {c : ℝ} (hc : 0 ≤ c) {η : WeakDual ℂ D} (hη : η ∈ TauCeti.stateSpace D) (a : D) :
    smulState hc hη a = (c : ℂ) * η a := by
  simp [smulState, NNReal.smul_def, hc, Complex.real_smul, WeakDual.toStrongDual_apply]

private theorem opNorm_smulState {D : Type*} [CStarAlgebra D] [PartialOrder D] [StarOrderedRing D]
    {c : ℝ} (hc : 0 ≤ c) {η : WeakDual ℂ D} (hη : η ∈ TauCeti.stateSpace D) :
    ‖(smulState hc hη : D →L[ℂ] ℂ)‖ = c := by
  rw [smulState, PositiveContinuousLinearMap.opNorm_smul,
    PositiveContinuousLinearMap.toContinuousLinearMap_mk₀,
    TauCeti.norm_toStrongDual_of_mem_stateSpace hη, mul_one, Real.coe_toNNReal c hc]

/-- On a unital C⋆-algebra, every bounded Hermitian functional admits a norm-preserving Jordan
decomposition `φ = ω₁ - ω₂` into positive functionals with `‖ω₁‖ + ‖ω₂‖ = ‖φ‖`. -/
private theorem exists_sub_positiveContinuousLinearMap_unital
    {D : Type*} [CStarAlgebra D] [PartialOrder D] [StarOrderedRing D]
    (φ : D →L[ℂ] ℂ) (hφ : ∀ a, φ (star a) = star (φ a)) :
    ∃ ω₁ ω₂ : D →P[ℂ] ℂ, (∀ a, φ a = ω₁ a - ω₂ a) ∧
      ‖(ω₁ : D →L[ℂ] ℂ)‖ + ‖(ω₂ : D →L[ℂ] ℂ)‖ = ‖φ‖ := by
  by_cases hφ0 : φ = 0
  · refine ⟨0, 0, fun a => by simp [hφ0], by simp [hφ0]⟩
  have hφ_pos : 0 < ‖φ‖ := norm_pos_iff.mpr hφ0
  set ψ : D →L[ℂ] ℂ := (‖φ‖⁻¹ : ℂ) • φ
  have hψ_norm : ‖ψ‖ = 1 := by simp [ψ, norm_smul, inv_mul_cancel₀ hφ_pos.ne']
  have hψ_star : ∀ a, ψ (star a) = star (ψ a) := fun a => by
    simp [ψ, hφ a, Complex.conj_ofReal]
  obtain ⟨η₁, hη₁, θ, hθ, s, t, hs, ht, hst, hcomb⟩ :=
    mem_convexJoin.mp (toWeakDual_mem_convexJoin_stateSpace_of_norm_eq_one hψ_norm hψ_star)
  let η₂ : WeakDual ℂ D := -θ
  have hη₂ : η₂ ∈ TauCeti.stateSpace D := Set.mem_neg.mp hθ
  let ω₁ : D →P[ℂ] ℂ := smulState (mul_nonneg (norm_nonneg φ) hs) hη₁
  let ω₂ : D →P[ℂ] ℂ := smulState (mul_nonneg (norm_nonneg φ) ht) hη₂
  refine ⟨ω₁, ω₂, fun a => ?_, ?_⟩
  · have hη₂_apply : η₂ a = -(θ a) := by
      rw [← WeakDual.toStrongDual_apply, map_neg, neg_apply, WeakDual.toStrongDual_apply]
    have h1 : (s : ℂ) * η₁ a - (t : ℂ) * η₂ a = (‖φ‖ : ℂ)⁻¹ * φ a := by
      have h0 := DFunLike.congr_fun hcomb a
      rw [hη₂_apply, mul_neg, sub_neg_eq_add]
      simpa only [add_apply, smul_apply, Complex.real_smul, StrongDual.toWeakDual_apply, ψ,
        smul_eq_mul] using h0
    have h2 : φ a = (‖φ‖ : ℂ) * ((s : ℂ) * η₁ a - (t : ℂ) * η₂ a) := by
      rw [h1, ← mul_assoc, ← Complex.ofReal_inv, ← Complex.ofReal_mul,
        mul_inv_cancel₀ hφ_pos.ne', Complex.ofReal_one, one_mul]
    rw [h2, smulState_apply, smulState_apply]
    push_cast
    ring
  · rw [opNorm_smulState, opNorm_smulState, ← mul_add, hst, mul_one]

variable {A : Type*} [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

/-- **Jordan decomposition of bounded Hermitian functionals.** Every continuous linear functional
`φ : A →L[ℂ] ℂ` on a (possibly nonunital) C⋆-algebra satisfying `φ (star a) = star (φ a)` is the
difference `ω₁ - ω₂` of two positive continuous linear functionals with `‖ω₁‖ + ‖ω₂‖ = ‖φ‖`. -/
theorem exists_sub_positiveContinuousLinearMap_of_map_star (φ : A →L[ℂ] ℂ)
    (hφ : ∀ a, φ (star a) = star (φ a)) :
    ∃ ω₁ ω₂ : A →P[ℂ] ℂ, (∀ a, φ a = ω₁ a - ω₂ a) ∧
      ‖(ω₁ : A →L[ℂ] ℂ)‖ + ‖(ω₂ : A →L[ℂ] ℂ)‖ = ‖φ‖ := by
  let i : A →ₗᵢ[ℂ] Unitization ℂ A :=
    ⟨Unitization.inrHom ℂ ℂ A, fun a => Unitization.norm_inr a⟩
  have hi_apply : ∀ a : A, i.toContinuousLinearMap a = (a : A⁺¹) := fun _ => rfl
  obtain ⟨ψ₀, hψ₀_ext, hψ₀_norm⟩ := i.exists_extension_norm_eq φ
  have hψ₀_apply : ∀ a : A, ψ₀ (a : A⁺¹) = φ a := fun a => by
    simpa only [ContinuousLinearMap.comp_apply, hi_apply] using DFunLike.congr_fun hψ₀_ext a
  let ψ : Unitization ℂ A →L[ℂ] ℂ :=
    (realPart (WithConv.toConv ψ₀) : WithConv (Unitization ℂ A →L[ℂ] ℂ)).ofConv
  have hψ_star : ∀ x, ψ (star x) = star (ψ x) :=
    (IntrinsicStar.isSelfAdjoint_iff_map_star _).mp (realPart (WithConv.toConv ψ₀)).property
  have hψ_ext : ∀ a : A, ψ (a : A⁺¹) = φ a := fun a => by
    have hval := congrArg (fun f : WithConv (Unitization ℂ A →L[ℂ] ℂ) => f.ofConv (a : A⁺¹))
      (realPart_apply_coe (WithConv.toConv ψ₀))
    have hstar : (star (WithConv.toConv ψ₀)).ofConv (a : A⁺¹) = φ a := by
      rw [intrinsicStar_apply, ← Unitization.inr_star, hψ₀_apply (star a), hφ a, star_star]
    simpa [ψ, WithConv.ofConv_smul, WithConv.ofConv_add, hψ₀_apply a, hstar,
      Complex.real_smul, ← two_mul] using hval
  have hψ_norm : ‖ψ‖ = ‖φ‖ := le_antisymm
    ((norm_ofConv_realPart_toConv_le ψ₀).trans_eq hψ₀_norm)
    (opNorm_le_bound _ (norm_nonneg ψ) fun a => by
      rw [← hψ_ext a]
      exact (ψ.le_opNorm (a : A⁺¹)).trans_eq (by rw [Unitization.norm_inr]))
  obtain ⟨η₁, η₂, hη_eq, hη_norm⟩ := exists_sub_positiveContinuousLinearMap_unital ψ hψ_star
  let j : A →P[ℂ] Unitization ℂ A := .ofClass (Unitization.inrNonUnitalStarAlgHom ℂ A)
  have hj_apply : ∀ a : A, j a = (a : A⁺¹) := fun _ => rfl
  let ω₁ : A →P[ℂ] ℂ := η₁.comp j
  let ω₂ : A →P[ℂ] ℂ := η₂.comp j
  have hω₁_apply : ∀ a : A, ω₁ a = η₁ (a : A⁺¹) := fun a => by
    rw [PositiveContinuousLinearMap.comp_apply, hj_apply]
  have hω₂_apply : ∀ a : A, ω₂ a = η₂ (a : A⁺¹) := fun a => by
    rw [PositiveContinuousLinearMap.comp_apply, hj_apply]
  have hω_eq : ∀ a, φ a = ω₁ a - ω₂ a := fun a => by
    rw [hω₁_apply, hω₂_apply, ← hψ_ext a, hη_eq (a : A⁺¹)]
  have hω_le : ∀ η : Unitization ℂ A →P[ℂ] ℂ,
      ‖((η.comp j : A →P[ℂ] ℂ) : A →L[ℂ] ℂ)‖ ≤ ‖(η : Unitization ℂ A →L[ℂ] ℂ)‖ := fun η =>
    opNorm_le_bound _ (norm_nonneg _) fun a => by
      rw [PositiveContinuousLinearMap.coe_toContinuousLinearMap,
        PositiveContinuousLinearMap.comp_apply, hj_apply,
        ← Unitization.norm_inr (𝕜 := ℂ) a]
      exact (η : Unitization ℂ A →L[ℂ] ℂ).le_opNorm (a : A⁺¹)
  have hsum_le : ‖(ω₁ : A →L[ℂ] ℂ)‖ + ‖(ω₂ : A →L[ℂ] ℂ)‖ ≤ ‖φ‖ :=
    (add_le_add (hω_le η₁) (hω_le η₂)).trans (by rw [hη_norm, hψ_norm])
  have hφ_le : ‖φ‖ ≤ ‖(ω₁ : A →L[ℂ] ℂ)‖ + ‖(ω₂ : A →L[ℂ] ℂ)‖ := by
    have heq : φ = (ω₁ : A →L[ℂ] ℂ) - (ω₂ : A →L[ℂ] ℂ) := ext hω_eq
    rw [heq]
    exact norm_sub_le _ _
  exact ⟨ω₁, ω₂, hω_eq, le_antisymm hsum_le hφ_le⟩

/-- **Four-positive decomposition of bounded linear functionals.** Every continuous linear
functional `φ : A →L[ℂ] ℂ` on a (possibly nonunital) C⋆-algebra is a complex linear combination
`φ = (ω₁ - ω₂) + i (ω₃ - ω₄)` of four positive continuous linear functionals with
`‖ω₁‖ + ‖ω₂‖ ≤ ‖φ‖` and `‖ω₃‖ + ‖ω₄‖ ≤ ‖φ‖`. -/
theorem exists_four_positiveContinuousLinearMap (φ : A →L[ℂ] ℂ) :
    ∃ ω₁ ω₂ ω₃ ω₄ : A →P[ℂ] ℂ,
      (∀ a, φ a = (ω₁ a - ω₂ a) + Complex.I * (ω₃ a - ω₄ a)) ∧
      ‖(ω₁ : A →L[ℂ] ℂ)‖ + ‖(ω₂ : A →L[ℂ] ℂ)‖ ≤ ‖φ‖ ∧
      ‖(ω₃ : A →L[ℂ] ℂ)‖ + ‖(ω₄ : A →L[ℂ] ℂ)‖ ≤ ‖φ‖ := by
  let φR : A →L[ℂ] ℂ := (realPart (WithConv.toConv φ) : WithConv (A →L[ℂ] ℂ)).ofConv
  let φI : A →L[ℂ] ℂ := (imaginaryPart (WithConv.toConv φ) : WithConv (A →L[ℂ] ℂ)).ofConv
  have hφR_star : ∀ a, φR (star a) = star (φR a) :=
    (IntrinsicStar.isSelfAdjoint_iff_map_star _).mp (realPart (WithConv.toConv φ)).property
  have hφI_star : ∀ a, φI (star a) = star (φI a) :=
    (IntrinsicStar.isSelfAdjoint_iff_map_star _).mp (imaginaryPart (WithConv.toConv φ)).property
  obtain ⟨ω₁, ω₂, hR_eq, hR_norm⟩ := φR.exists_sub_positiveContinuousLinearMap_of_map_star hφR_star
  obtain ⟨ω₃, ω₄, hI_eq, hI_norm⟩ := φI.exists_sub_positiveContinuousLinearMap_of_map_star hφI_star
  refine ⟨ω₁, ω₂, ω₃, ω₄, fun a => ?_,
    hR_norm.trans_le (norm_ofConv_realPart_toConv_le φ),
    hI_norm.trans_le (norm_ofConv_imaginaryPart_toConv_le φ)⟩
  have hsplit := congrArg (fun f : WithConv (A →L[ℂ] ℂ) => f.ofConv a)
    (realPart_add_I_smul_imaginaryPart (WithConv.toConv φ))
  rw [← hR_eq a, ← hI_eq a]
  simpa [φR, φI, WithConv.ofConv_add, WithConv.ofConv_smul] using hsplit.symm

end JordanDecomposition

end ContinuousLinearMap

namespace TauCeti.CStarAlgebra

variable {A : Type*} [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

/-- A net in a C⋆-algebra converges weakly if and only if its image under every positive continuous
linear functional converges. -/
theorem tendsto_toWeakSpace_iff_forall_positiveContinuousLinearMap
    {ι : Type*} {l : Filter ι} {u : ι → A} {x : A} :
    Tendsto (fun i => toWeakSpace ℂ A (u i)) l (𝓝 (toWeakSpace ℂ A x)) ↔
      ∀ ω : A →P[ℂ] ℂ, Tendsto (fun i => ω (u i)) l (𝓝 (ω x)) := by
  rw [TauCeti.tendsto_toWeakSpace_iff_forall_eval_tendsto]
  refine ⟨fun h ω => by simpa using h (ω : A →L[ℂ] ℂ), fun h φ => ?_⟩
  obtain ⟨ω₁, ω₂, ω₃, ω₄, hφ, -, -⟩ := φ.exists_four_positiveContinuousLinearMap
  simp_rw [hφ]
  exact ((h ω₁).sub (h ω₂)).add (((h ω₃).sub (h ω₄)).const_mul Complex.I)

end TauCeti.CStarAlgebra

end
