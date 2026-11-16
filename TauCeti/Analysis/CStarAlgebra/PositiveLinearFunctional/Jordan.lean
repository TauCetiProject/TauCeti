/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Normed.Operator.NormedSpace
public import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Positive
import Mathlib.Analysis.Convex.Join
import Mathlib.Analysis.LocallyConvex.Separation
import Mathlib.LinearAlgebra.Complex.Module
import Mathlib.Topology.Algebra.Star.LinearMap
import TauCeti.Analysis.CStarAlgebra.State.Space
import TauCeti.Analysis.CStarAlgebra.State.Spectrum
import TauCeti.Analysis.LocallyConvex.WeakDual.Basic
import TauCeti.Analysis.Normed.Module.HahnBanach

/-!
# Jordan decomposition of continuous linear functionals on C⋆-algebras

Every continuous linear functional `φ : A →L[ℂ] ℂ` on a (possibly nonunital) C⋆-algebra decomposes
into a linear combination of four positive continuous linear functionals, and every Hermitian
(`star`-preserving) continuous linear functional is a difference `φ₁ - φ₂` of two positive
functionals with `‖φ₁‖ + ‖φ₂‖ = ‖φ‖`.

On a nontrivial unital C⋆-algebra `M`, the convex join
`K = convexJoin ℝ (stateSpace M) (-stateSpace M)` is weak-⋆ compact and convex. If a Hermitian
contraction `φ` lay outside `K`, Hahn–Banach separation in `WeakDual ℂ M` would produce an element
`a : M` whose real part `b = realPart a` strictly separates `φ` from `K`, contradicting that some
state attains `±‖b‖` at `b`. Passing to the unitization `A⁺¹` via Hahn–Banach extension and taking
the Hermitian part extends the decomposition to arbitrary nonunital C⋆-algebras while preserving
the norm identity `‖φ₁‖ + ‖φ₂‖ = ‖φ‖`.

## Main results

* `ContinuousLinearMap.exists_map_star_add_I_smul`: Cartesian decomposition of a continuous linear
  map between normed complex star spaces into two `star`-preserving maps of norm at most `‖φ‖`.
* `ContinuousLinearMap.exists_positiveContinuousLinearMap_sub_of_map_star`: Jordan decomposition of
  a `star`-preserving continuous linear functional on a C⋆-algebra as `φ₁ - φ₂` with
  `‖φ₁‖ + ‖φ₂‖ = ‖φ‖`.
* `ContinuousLinearMap.exists_positiveContinuousLinearMap_sub_add_I_smul_sub`: decomposition of an
  arbitrary continuous linear functional on a C⋆-algebra into four positive functionals with norm
  bounds.

## References

* B. Blackadar, *Operator Algebras*, Proposition II.6.3.4.
* G. J. Murphy, *C⋆-Algebras and Operator Theory*, Theorem 4.3.6.
-/

public section

open Filter Set WeakDual
open scoped CStarAlgebra ComplexOrder Pointwise Topology

namespace ContinuousLinearMap

section Cartesian

variable {E F : Type*}
  [SeminormedAddCommGroup E] [NormedSpace ℂ E] [StarAddMonoid E] [StarModule ℂ E]
  [NormedStarGroup E]
  [SeminormedAddCommGroup F] [NormedSpace ℂ F] [StarAddMonoid F] [StarModule ℂ F]
  [NormedStarGroup F]

/-- Cartesian decomposition of a continuous linear map between normed complex star spaces:
every `φ : E →L[ℂ] F` is `φ₁ + I • φ₂` with `φ₁, φ₂` star-preserving and bounded in norm by
`‖φ‖`. -/
theorem exists_map_star_add_I_smul (φ : E →L[ℂ] F) :
    ∃ φ₁ φ₂ : E →L[ℂ] F,
      (∀ x, φ₁ (star x) = star (φ₁ x)) ∧
      (∀ x, φ₂ (star x) = star (φ₂ x)) ∧
      φ₁ + Complex.I • φ₂ = φ ∧
      ‖φ₁‖ ≤ ‖φ‖ ∧ ‖φ₂‖ ≤ ‖φ‖ := by
  have hnorm_realPart : ∀ ψ : E →L[ℂ] F,
      ‖(realPart (WithConv.toConv ψ) : WithConv (E →L[ℂ] F)).ofConv‖ ≤ ‖ψ‖ := fun ψ => by
    have hstar : ‖(star (WithConv.toConv ψ)).ofConv‖ ≤ ‖ψ‖ :=
      opNorm_le_bound _ (norm_nonneg ψ) fun x => by
        have hx : (star (WithConv.toConv ψ)).ofConv x = star (ψ (star x)) :=
          intrinsicStar_apply (WithConv.toConv ψ) x
        rw [hx, norm_star, ← norm_star x]
        exact ψ.le_opNorm (star x)
    rw [realPart_apply_coe, WithConv.ofConv_smul, WithConv.ofConv_add, WithConv.ofConv_toConv,
      norm_smul, Real.norm_of_nonneg (by positivity)]
    calc
      2⁻¹ * ‖ψ + (star (WithConv.toConv ψ)).ofConv‖
          ≤ 2⁻¹ * (‖ψ‖ + ‖(star (WithConv.toConv ψ)).ofConv‖) :=
        mul_le_mul_of_nonneg_left (norm_add_le _ _) (by positivity)
      _ ≤ 2⁻¹ * (‖ψ‖ + ‖ψ‖) :=
        mul_le_mul_of_nonneg_left (add_le_add_right hstar _) (by positivity)
      _ = ‖ψ‖ := by ring
  refine ⟨(realPart (WithConv.toConv φ) : WithConv (E →L[ℂ] F)).ofConv,
    (imaginaryPart (WithConv.toConv φ) : WithConv (E →L[ℂ] F)).ofConv,
    (IntrinsicStar.isSelfAdjoint_iff_map_star _).1 (realPart (WithConv.toConv φ)).2,
    (IntrinsicStar.isSelfAdjoint_iff_map_star _).1 (imaginaryPart (WithConv.toConv φ)).2,
    congrArg WithConv.ofConv (realPart_add_I_smul_imaginaryPart (WithConv.toConv φ)),
    hnorm_realPart φ, ?_⟩
  have him : (imaginaryPart (WithConv.toConv φ) : WithConv (E →L[ℂ] F)) =
      realPart (WithConv.toConv (-Complex.I • φ)) := by
    rw [WithConv.toConv_smul, neg_smul, map_neg, realPart_I_smul, neg_neg]
  simpa [him, norm_smul] using hnorm_realPart (-Complex.I • φ)

end Cartesian

section Unital

variable {M : Type*} [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M]

private theorem isCompact_convexJoin_stateSpace_neg :
    IsCompact (convexJoin ℝ (TauCeti.stateSpace M) (-TauCeti.stateSpace M)) := by
  let f : ℝ × WeakDual ℂ M × WeakDual ℂ M → WeakDual ℂ M :=
    fun p => (1 - p.1) • p.2.1 + p.1 • p.2.2
  have hf : Continuous f := by
    have hsmul : Continuous (fun q : ℝ × WeakDual ℂ M => q.1 • q.2) := by
      have heq : (fun q : ℝ × WeakDual ℂ M => q.1 • q.2) =
          fun q => (q.1 : ℂ) • q.2 :=
        funext fun q => WeakDual.real_smul_eq_coe_smul q.1 q.2
      rw [heq]
      exact (Complex.continuous_ofReal.comp continuous_fst).smul continuous_snd
    exact (hsmul.comp ((continuous_const.sub continuous_fst).prodMk
      (continuous_fst.comp continuous_snd))).add
      (hsmul.comp (continuous_fst.prodMk (continuous_snd.comp continuous_snd)))
  have hK : convexJoin ℝ (TauCeti.stateSpace M) (-TauCeti.stateSpace M) =
      f '' (Icc (0 : ℝ) 1 ×ˢ TauCeti.stateSpace M ×ˢ (-TauCeti.stateSpace M)) := by
    ext ψ
    simp only [mem_convexJoin, segment, mem_ofPred_eq, mem_image, mem_prod, mem_Icc, Prod.exists,
      f]
    constructor
    · rintro ⟨ω₁, hω₁, ω₂, hω₂, a, b, ha, hb, hab, rfl⟩
      have h1b : 1 - b = a := by linarith
      exact ⟨b, ω₁, ω₂, ⟨⟨hb, by linarith⟩, hω₁, hω₂⟩, by rw [h1b]⟩
    · rintro ⟨t, ω₁, ω₂, ⟨⟨ht0, ht1⟩, hω₁, hω₂⟩, rfl⟩
      exact ⟨ω₁, hω₁, ω₂, hω₂, 1 - t, t, by linarith, ht0, by ring, rfl⟩
  rw [hK]
  exact (isCompact_Icc.prod (TauCeti.isCompact_stateSpace.prod
    TauCeti.isCompact_stateSpace.neg)).image hf

private theorem mem_convexJoin_stateSpace_neg_of_map_star [Nontrivial M]
    (φ : M →L[ℂ] ℂ) (hφ_star : ∀ a, φ (star a) = star (φ a)) (hφ_norm : ‖φ‖ ≤ 1) :
    StrongDual.toWeakDual φ ∈ convexJoin ℝ (TauCeti.stateSpace M) (-TauCeti.stateSpace M) := by
  by_contra hnotmem
  have hconv : Convex ℝ (convexJoin ℝ (TauCeti.stateSpace M) (-TauCeti.stateSpace M)) :=
    TauCeti.convex_stateSpace.convexJoin TauCeti.convex_stateSpace.neg
  have hclosed : IsClosed (convexJoin ℝ (TauCeti.stateSpace M) (-TauCeti.stateSpace M)) :=
    isCompact_convexJoin_stateSpace_neg.isClosed
  -- Pass `WeakDual.instLocallyConvexSpaceReal` explicitly: `Complex.instModuleReal` differs
  -- syntactically from `RCLike.toNormedAlgebra.toModule` during typeclass lookup.
  obtain ⟨l, u, hlK, hlφ⟩ :=
    @RCLike.geometric_hahn_banach_closed_point ℂ (WeakDual ℂ M) _ _ _ _ _ _ _ _ _ _
      WeakDual.instLocallyConvexSpaceReal hconv hclosed hnotmem
  obtain ⟨a, ha⟩ := WeakDual.exists_forall_apply_eq_apply l
  let b : M := (realPart a : M)
  have hb_sa : IsSelfAdjoint b := (realPart a).2
  have hre_eq : ∀ ψ : M →L[ℂ] ℂ, (∀ x, ψ (star x) = star (ψ x)) → (ψ b).re = (ψ a).re := by
    intro ψ hψ
    have hψb : ψ b = (2⁻¹ : ℝ) • (ψ a + star (ψ a)) := by
      simp [b, realPart_apply_coe, map_add, hψ]
    rw [hψb, Complex.real_smul, Complex.star_def, Complex.add_conj]
    simp
  obtain ⟨ω, -, hω_norm, hωb⟩ :=
    TauCeti.CStarAlgebra.exists_positiveContinuousLinearMap_apply_eq_norm_or_neg_norm hb_sa
  have hω_mem : StrongDual.toWeakDual (ω : M →L[ℂ] ℂ) ∈ TauCeti.stateSpace M :=
    ω.toWeakDual_mem_stateSpace_iff.2 hω_norm
  have hω_re : ((ω : M →L[ℂ] ℂ) b).re = ((ω : M →L[ℂ] ℂ) a).re :=
    hre_eq (ω : M →L[ℂ] ℂ) fun x => map_star ω x
  have hpos_lt : ((ω : M →L[ℂ] ℂ) b).re < u := by
    rw [hω_re]
    simpa [ha] using hlK _ (subset_convexJoin_left TauCeti.stateSpace_nonempty.neg hω_mem)
  have hneg_lt : -((ω : M →L[ℂ] ℂ) b).re < u := by
    rw [hω_re]
    have hneg_mem : -StrongDual.toWeakDual (ω : M →L[ℂ] ℂ) ∈ -TauCeti.stateSpace M := by
      simpa using hω_mem
    have hneg_apply : (-StrongDual.toWeakDual (ω : M →L[ℂ] ℂ)) a = -(ω a) := by
      rw [← WeakDual.toStrongDual_apply, map_neg, neg_apply, WeakDual.toStrongDual_apply]
      rfl
    simpa [ha, hneg_apply] using
      hlK _ (subset_convexJoin_right TauCeti.stateSpace_nonempty hneg_mem)
  have hnorm_lt : ‖b‖ < u := by
    rcases hωb with h | h
    · simpa [h] using hpos_lt
    · simpa [h] using hneg_lt
  have hu_lt : u < (φ b).re := by
    rw [hre_eq φ hφ_star]
    simpa [ha] using hlφ
  have hφb_le : (φ b).re ≤ ‖b‖ :=
    (Complex.re_le_norm (φ b)).trans <|
      (φ.le_opNorm b).trans (mul_le_of_le_one_left (norm_nonneg b) hφ_norm)
  linarith

private theorem exists_positiveContinuousLinearMap_sub_of_map_star_unital
    (φ : M →L[ℂ] ℂ) (hφ_star : ∀ a, φ (star a) = star (φ a)) :
    ∃ φ₁ φ₂ : M →P[ℂ] ℂ,
      (φ₁ : M →L[ℂ] ℂ) - (φ₂ : M →L[ℂ] ℂ) = φ ∧
      ‖(φ₁ : M →L[ℂ] ℂ)‖ + ‖(φ₂ : M →L[ℂ] ℂ)‖ = ‖φ‖ := by
  by_cases hφ0 : φ = 0
  · exact ⟨0, 0, by simp [hφ0], by simp [hφ0]⟩
  have hnorm_pos : 0 < ‖φ‖ := norm_pos_iff.2 hφ0
  have : Nontrivial M := by
    by_contra h
    rw [not_nontrivial_iff_subsingleton] at h
    exact hφ0 (ext fun x => by simp [Subsingleton.elim x 0])
  let φ₀ : M →L[ℂ] ℂ := ‖φ‖⁻¹ • φ
  have hφ₀_norm : ‖φ₀‖ ≤ 1 := by
    rw [norm_smul, Real.norm_of_nonneg (inv_nonneg.2 hnorm_pos.le), inv_mul_cancel₀ hnorm_pos.ne']
  obtain ⟨ω₁, hω₁, ω₂', hω₂', c₁, c₂, hc₁, hc₂, hc_sum, hcomb⟩ :=
    mem_convexJoin.1 (mem_convexJoin_stateSpace_neg_of_map_star φ₀
      (fun a => by simp [φ₀, hφ_star a]) hφ₀_norm)
  let ω₂ : WeakDual ℂ M := -ω₂'
  have hω₂ : ω₂ ∈ TauCeti.stateSpace M := by simpa [ω₂] using hω₂'
  let φ₁ : M →P[ℂ] ℂ :=
    .mk₀ ((‖φ‖ * c₁) • WeakDual.toStrongDual ω₁) fun a ha => by
      simpa using smul_nonneg (mul_nonneg hnorm_pos.le hc₁)
        (TauCeti.map_nonneg_of_mem_stateSpace hω₁ ha)
  let φ₂ : M →P[ℂ] ℂ :=
    .mk₀ ((‖φ‖ * c₂) • WeakDual.toStrongDual ω₂) fun a ha => by
      simpa using smul_nonneg (mul_nonneg hnorm_pos.le hc₂)
        (TauCeti.map_nonneg_of_mem_stateSpace hω₂ ha)
  refine ⟨φ₁, φ₂, ?_, ?_⟩
  · ext a
    have ha : (c₁ : ℂ) * ω₁ a + (c₂ : ℂ) * ω₂' a = φ₀ a := by
      simpa [WeakDual.real_smul_apply] using congrArg (fun ψ : WeakDual ℂ M => ψ a) hcomb
    have hneg : ω₂ a = -ω₂' a := by
      rw [← WeakDual.toStrongDual_apply, map_neg, neg_apply, WeakDual.toStrongDual_apply]
    have hφa : φ a = (‖φ‖ : ℂ) * φ₀ a := by
      simp [φ₀, Complex.real_smul, ← mul_assoc,
        mul_inv_cancel₀ (Complex.ofReal_ne_zero.2 hnorm_pos.ne')]
    simp only [sub_apply, PositiveContinuousLinearMap.coe_toContinuousLinearMap,
      PositiveContinuousLinearMap.mk₀_apply, smul_apply, WeakDual.toStrongDual_apply,
      Complex.real_smul, φ₁, φ₂]
    rw [hφa, ← ha, hneg]
    push_cast
    ring
  · simp only [PositiveContinuousLinearMap.toContinuousLinearMap_mk₀, norm_smul,
      Real.norm_of_nonneg (mul_nonneg hnorm_pos.le hc₁),
      Real.norm_of_nonneg (mul_nonneg hnorm_pos.le hc₂),
      TauCeti.norm_toStrongDual_of_mem_stateSpace hω₁,
      TauCeti.norm_toStrongDual_of_mem_stateSpace hω₂, φ₁, φ₂]
    calc
      ‖φ‖ * c₁ * 1 + ‖φ‖ * c₂ * 1 = ‖φ‖ * (c₁ + c₂) := by ring
      _ = ‖φ‖ := by rw [hc_sum, mul_one]

end Unital

section NonUnital

variable {A : Type*} [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

/-- **Jordan decomposition for Hermitian functionals on C⋆-algebras.** Every `star`-preserving
continuous linear functional `φ : A →L[ℂ] ℂ` on a (possibly nonunital) C⋆-algebra is a difference
`φ₁ - φ₂` of two positive continuous linear functionals satisfying `‖φ₁‖ + ‖φ₂‖ = ‖φ‖`. -/
theorem exists_positiveContinuousLinearMap_sub_of_map_star
    (φ : A →L[ℂ] ℂ) (hφ_star : ∀ a, φ (star a) = star (φ a)) :
    ∃ φ₁ φ₂ : A →P[ℂ] ℂ,
      (φ₁ : A →L[ℂ] ℂ) - (φ₂ : A →L[ℂ] ℂ) = φ ∧
      ‖(φ₁ : A →L[ℂ] ℂ)‖ + ‖(φ₂ : A →L[ℂ] ℂ)‖ = ‖φ‖ := by
  let ι : A →ₗᵢ[ℂ] A⁺¹ :=
    { Unitization.inrHom (R := ℂ) (S := ℂ) (A := A) with
      norm_map' := fun a => Unitization.norm_inr (𝕜 := ℂ) a }
  obtain ⟨ψ, hψ_ext, hψ_norm⟩ := ι.exists_extension_norm_eq φ
  obtain ⟨ψh, ψim, hψh_star, hψim_star, hψ_cart, hψh_norm, -⟩ := ψ.exists_map_star_add_I_smul
  have hψh_ext : ∀ a : A, ψh (a : A⁺¹) = φ a := fun a => by
    have h1 : ψh (a : A⁺¹) + Complex.I * ψim (a : A⁺¹) = φ a := by
      have h := congrArg (fun f : A⁺¹ →L[ℂ] ℂ => f (a : A⁺¹)) hψ_cart
      have he : ψ (a : A⁺¹) = φ a := congrArg (fun f : A →L[ℂ] ℂ => f a) hψ_ext
      simpa [he] using h
    have h2 : star (ψh (a : A⁺¹)) + Complex.I * star (ψim (a : A⁺¹)) = star (φ a) := by
      have h := congrArg (fun f : A⁺¹ →L[ℂ] ℂ => f (star (a : A⁺¹))) hψ_cart
      have he : ψ (star (a : A⁺¹)) = star (φ a) := by
        rw [← Unitization.inr_star, ← hφ_star a]
        exact congrArg (fun f : A →L[ℂ] ℂ => f (star a)) hψ_ext
      simpa [hψh_star, hψim_star, he] using h
    have h2' : ψh (a : A⁺¹) - Complex.I * ψim (a : A⁺¹) = φ a := by
      simpa [Complex.star_def, sub_eq_add_neg] using congrArg star h2
    have hsum : ψh (a : A⁺¹) + ψh (a : A⁺¹) = φ a + φ a := by
      calc
        ψh (a : A⁺¹) + ψh (a : A⁺¹)
            = (ψh (a : A⁺¹) + Complex.I * ψim (a : A⁺¹)) +
                (ψh (a : A⁺¹) - Complex.I * ψim (a : A⁺¹)) := by ring
        _ = φ a + φ a := by rw [h1, h2']
    have hmul : (2 : ℂ) * ψh (a : A⁺¹) = (2 : ℂ) * φ a := by
      simpa [two_mul] using hsum
    exact mul_left_cancel₀ two_ne_zero hmul
  obtain ⟨ψ₁, ψ₂, hψ_sub, hψ_sum⟩ :=
    exists_positiveContinuousLinearMap_sub_of_map_star_unital ψh hψh_star
  let inrP : A →P[ℂ] A⁺¹ :=
    PositiveContinuousLinearMap.ofClass (Unitization.inrNonUnitalStarAlgHom ℂ A)
  let φ₁ : A →P[ℂ] ℂ := ψ₁.comp inrP
  let φ₂ : A →P[ℂ] ℂ := ψ₂.comp inrP
  have hsub : (φ₁ : A →L[ℂ] ℂ) - (φ₂ : A →L[ℂ] ℂ) = φ := by
    ext a
    simpa [φ₁, φ₂, inrP, hψh_ext a] using congrArg (fun f : A⁺¹ →L[ℂ] ℂ => f (a : A⁺¹)) hψ_sub
  have hle₁ : ‖(φ₁ : A →L[ℂ] ℂ)‖ ≤ ‖(ψ₁ : A⁺¹ →L[ℂ] ℂ)‖ :=
    opNorm_le_bound _ (norm_nonneg _) fun a => by
      simpa [φ₁, inrP, Unitization.norm_inr] using (ψ₁ : A⁺¹ →L[ℂ] ℂ).le_opNorm (a : A⁺¹)
  have hle₂ : ‖(φ₂ : A →L[ℂ] ℂ)‖ ≤ ‖(ψ₂ : A⁺¹ →L[ℂ] ℂ)‖ :=
    opNorm_le_bound _ (norm_nonneg _) fun a => by
      simpa [φ₂, inrP, Unitization.norm_inr] using (ψ₂ : A⁺¹ →L[ℂ] ℂ).le_opNorm (a : A⁺¹)
  refine ⟨φ₁, φ₂, hsub, le_antisymm ?_ ?_⟩
  · exact (add_le_add hle₁ hle₂).trans (hψ_sum.trans_le (hψh_norm.trans hψ_norm.le))
  · rw [← hsub]
    exact norm_sub_le _ _

/-- **Jordan decomposition of continuous linear functionals on C⋆-algebras.** Every continuous
linear functional `φ : A →L[ℂ] ℂ` on a (possibly nonunital) C⋆-algebra decomposes as
`(φ₁ - φ₂) + I • (φ₃ - φ₄)` with `φ₁, φ₂, φ₃, φ₄` positive continuous linear functionals
satisfying `‖φ₁‖ + ‖φ₂‖ ≤ ‖φ‖` and `‖φ₃‖ + ‖φ₄‖ ≤ ‖φ‖`. -/
theorem exists_positiveContinuousLinearMap_sub_add_I_smul_sub (φ : A →L[ℂ] ℂ) :
    ∃ φ₁ φ₂ φ₃ φ₄ : A →P[ℂ] ℂ,
      ((φ₁ : A →L[ℂ] ℂ) - (φ₂ : A →L[ℂ] ℂ)) +
        Complex.I • ((φ₃ : A →L[ℂ] ℂ) - (φ₄ : A →L[ℂ] ℂ)) = φ ∧
      ‖(φ₁ : A →L[ℂ] ℂ)‖ + ‖(φ₂ : A →L[ℂ] ℂ)‖ ≤ ‖φ‖ ∧
      ‖(φ₃ : A →L[ℂ] ℂ)‖ + ‖(φ₄ : A →L[ℂ] ℂ)‖ ≤ ‖φ‖ := by
  obtain ⟨ψ_re, ψ_im, hre_star, him_star, hsum, hre_norm, him_norm⟩ :=
    exists_map_star_add_I_smul φ
  obtain ⟨φ₁, φ₂, h12, hn12⟩ := exists_positiveContinuousLinearMap_sub_of_map_star ψ_re hre_star
  obtain ⟨φ₃, φ₄, h34, hn34⟩ := exists_positiveContinuousLinearMap_sub_of_map_star ψ_im him_star
  exact ⟨φ₁, φ₂, φ₃, φ₄, by rw [h12, h34, hsum], hn12.trans_le hre_norm, hn34.trans_le him_norm⟩

end NonUnital

end ContinuousLinearMap
