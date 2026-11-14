/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Basic
public import TauCeti.Analysis.CStarAlgebra.Stinespring.Uniqueness
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Commute
import Mathlib.Analysis.LocallyConvex.SeparatingDual
import Mathlib.Analysis.Normed.Operator.Extend
import Mathlib.Analysis.Normed.Operator.Mul

/-!
# Arveson's Radon–Nikodym theorem for completely positive maps

Given a minimal Stinespring dilation `(K, π, V)` of `φ : A →CP (H →L[ℂ] H)`, completely positive
maps `ψ ≤ φ` correspond order-isomorphically (`CompletelyPositiveMap.radonNikodymOrderIso`) to
positive contractions `T : K →L[ℂ] K` (`0 ≤ T ≤ 1`) in the commutant of `π(A)` via
`ψ a = V† ∘L T ∘L π a ∘L V` (`CompletelyPositiveMap.radonNikodym_nonUnital`,
`CompletelyPositiveMap.cp_radonNikodym`).

As a boundary check on `φ = id_{B(H)}`, the commutant of `B(H)` is `ℂ • 1`
(`ContinuousLinearMap.commute_forall_iff`), so `Set.Icc 0 id` consists of `[0, 1]`-multiples of `id`
(`CompletelyPositiveMap.mem_Icc_zero_id_iff`), whereas `a ↦ T * a` preserves positivity iff
`T = t • 1` for `t : ℝ≥0` (`ContinuousLinearMap.forall_nonneg_mul_nonneg_iff`).

## References

* W. B. Arveson, *Subalgebras of C⋆-algebras*, Acta Math. 123 (1969), 141–224, Theorem 1.4.2.
* V. Paulsen, *Completely Bounded Maps and Operator Algebras*, Theorem 4.4.
-/

public section

universe u v w

open Filter Topology TensorProduct
open scoped CStarAlgebra ComplexOrder InnerProductSpace NNReal

namespace CompletelyPositiveMap

section Forward

variable {A : Type u} [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  {H : Type v} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {K : Type w} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
  (π : A →⋆ₙₐ[ℂ] (K →L[ℂ] K)) (V : H →L[ℂ] K)

/-- The completely positive map `(conjAdjoint (CFC.sqrt T ∘L V)).comp π` associated with
`T : K →L[ℂ] K`, evaluating to `a ↦ V† ∘L T ∘L π a ∘L V` when `0 ≤ T` commutes with `π(A)`. -/
noncomputable def radonNikodymMap (T : K →L[ℂ] K) : A →CP (H →L[ℂ] H) :=
  (conjAdjoint ((CFC.sqrt T).comp V)).comp
    (CompletelyPositiveMapClass.toCompletelyPositiveLinearMap π)

theorem radonNikodymMap_apply {T : K →L[ℂ] K} (hT : 0 ≤ T)
    (hcomm : ∀ a, Commute T (π a)) (a : A) :
    radonNikodymMap π V T a = V.adjoint.comp (T.comp ((π a).comp V)) := by
  have hsqrt_comm : Commute (CFC.sqrt T) (π a) := by
    rw [CFC.sqrt_eq_cfc]; exact (hcomm a).cfc_nnreal NNReal.sqrt
  have hsqrt_adj : (CFC.sqrt T).adjoint = CFC.sqrt T :=
    ContinuousLinearMap.star_eq_adjoint (CFC.sqrt T) ▸
      (IsSelfAdjoint.of_nonneg (CFC.sqrt_nonneg T)).star_eq
  have hmul : (CFC.sqrt T).comp ((π a).comp (CFC.sqrt T)) = T.comp (π a) := by
    change CFC.sqrt T * (π a * CFC.sqrt T) = T * π a
    rw [← hsqrt_comm.eq, ← mul_assoc, CFC.sqrt_mul_sqrt_self T hT]
  rw [radonNikodymMap, comp_apply, conjAdjoint_apply]
  change ((CFC.sqrt T).comp V).adjoint.comp ((π a).comp ((CFC.sqrt T).comp V)) = _
  rw [ContinuousLinearMap.adjoint_comp, hsqrt_adj]
  simpa only [ContinuousLinearMap.comp_assoc] using
    congrArg (fun S => V.adjoint.comp (S.comp V)) hmul

@[simp] theorem radonNikodymMap_zero : radonNikodymMap π V 0 = 0 := by
  ext a; simp [radonNikodymMap_apply π V le_rfl (fun _ => Commute.zero_left _) a]

theorem radonNikodymMap_one {φ : A →CP (H →L[ℂ] H)}
    (hφ : ∀ a, φ a = V.adjoint.comp ((π a).comp V)) : radonNikodymMap π V 1 = φ := by
  ext a
  rw [radonNikodymMap_apply π V zero_le_one (fun _ => Commute.one_left _) a, hφ a,
    ContinuousLinearMap.one_def, ContinuousLinearMap.id_comp]

theorem radonNikodymMap_add {T₁ T₂ : K →L[ℂ] K} (hT₁ : 0 ≤ T₁) (hT₂ : 0 ≤ T₂)
    (hcomm₁ : ∀ a, Commute T₁ (π a)) (hcomm₂ : ∀ a, Commute T₂ (π a)) :
    radonNikodymMap π V (T₁ + T₂) = radonNikodymMap π V T₁ + radonNikodymMap π V T₂ := by
  ext a
  rw [add_apply, radonNikodymMap_apply π V (add_nonneg hT₁ hT₂)
      (fun b => (hcomm₁ b).add_left (hcomm₂ b)) a,
    radonNikodymMap_apply π V hT₁ hcomm₁ a, radonNikodymMap_apply π V hT₂ hcomm₂ a,
    ContinuousLinearMap.add_comp, ContinuousLinearMap.comp_add]

theorem radonNikodymMap_smul (c : ℝ≥0) {T : K →L[ℂ] K} (hT : 0 ≤ T)
    (hcomm : ∀ a, Commute T (π a)) :
    radonNikodymMap π V (c • T) = c • radonNikodymMap π V T := by
  have hcT : 0 ≤ c • T := NNReal.smul_def c T ▸ smul_nonneg c.2 hT
  have hccomm : ∀ a, Commute (c • T) (π a) := fun a => by
    simp only [Commute, SemiconjBy, smul_mul_assoc, mul_smul_comm, (hcomm a).eq]
  ext a
  simp [radonNikodymMap_apply π V hcT hccomm a, radonNikodymMap_apply π V hT hcomm a]

theorem radonNikodymMap_mono {T₁ T₂ : K →L[ℂ] K} (hT₁ : 0 ≤ T₁) (h12 : T₁ ≤ T₂)
    (hcomm₁ : ∀ a, Commute T₁ (π a)) (hcomm₂ : ∀ a, Commute T₂ (π a)) :
    radonNikodymMap π V T₁ ≤ radonNikodymMap π V T₂ :=
  ⟨radonNikodymMap π V (T₂ - T₁), by
    rw [← radonNikodymMap_add π V hT₁ (sub_nonneg.mpr h12) hcomm₁
      (fun a => (hcomm₂ a).sub_left (hcomm₁ a)), add_sub_cancel]⟩

theorem radonNikodymMap_mem_Icc {φ : A →CP (H →L[ℂ] H)}
    (hφ : ∀ a, φ a = V.adjoint.comp ((π a).comp V))
    {T : K →L[ℂ] K} (hT : T ∈ Set.Icc 0 1) (hcomm : ∀ a, Commute T (π a)) :
    radonNikodymMap π V T ∈ Set.Icc 0 φ :=
  ⟨zero_le _, radonNikodymMap_one π V hφ ▸
    radonNikodymMap_mono π V hT.1 hT.2 hcomm fun _ => Commute.one_left _⟩

end Forward

section NonUnital

variable {A : Type u} [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  {H : Type v} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {K : Type w} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

omit [PartialOrder A] [StarOrderedRing A] in
/-- In a minimal Stinespring dilation `(K, π, V)`, `T` in the commutant of `π(A)` is uniquely
determined by `a ↦ V† ∘L T ∘L π a ∘L V`. -/
theorem radonNikodym_unique (π : A →⋆ₙₐ[ℂ] (K →L[ℂ] K)) (V : H →L[ℂ] K)
    (hmin : (Submodule.span ℂ {x : K | ∃ (a : A) (ξ : H), x = π a (V ξ)}).topologicalClosure = ⊤)
    {T₁ T₂ : K →L[ℂ] K} (hcomm₁ : ∀ a, Commute T₁ (π a)) (hcomm₂ : ∀ a, Commute T₂ (π a))
    (heq : ∀ a, V.adjoint.comp (T₁.comp ((π a).comp V)) =
      V.adjoint.comp (T₂.comp ((π a).comp V))) : T₁ = T₂ := by
  have key (T : K →L[ℂ] K) (hT : ∀ c, Commute T (π c)) (a b : A) (ξ η : H) :
      ⟪π a (V ξ), T (π b (V η))⟫_ℂ =
        ⟪ξ, (V.adjoint.comp (T.comp ((π (star a * b)).comp V))) η⟫_ℂ := by
    have hTb : (π a).adjoint (T (π b (V η))) = T (π (star a * b) (V η)) := by
      rw [← ContinuousLinearMap.star_eq_adjoint, ← map_star, ← ContinuousLinearMap.comp_apply,
        ← ContinuousLinearMap.mul_def, (hT (star a)).symm.eq, ContinuousLinearMap.mul_def,
        ContinuousLinearMap.comp_apply, map_mul, ContinuousLinearMap.mul_def,
        ContinuousLinearMap.comp_apply]
    rw [← ContinuousLinearMap.adjoint_inner_right (π a), hTb]
    simp [ContinuousLinearMap.adjoint_inner_right]
  have hlift (s t : A ⊗[ℂ] H) :
      ⟪stinespringLiftLinear π V s, T₁ (stinespringLiftLinear π V t)⟫_ℂ =
        ⟪stinespringLiftLinear π V s, T₂ (stinespringLiftLinear π V t)⟫_ℂ := by
    induction s using TensorProduct.inductionOn with
    | tmul a ξ =>
      induction t using TensorProduct.inductionOn with
      | tmul b η =>
        simp only [stinespringLiftLinear_tmul, key T₁ hcomm₁, key T₂ hcomm₂, heq (star a * b)]
      | add t₁ t₂ ht₁ ht₂ =>
        rw [map_add, map_add, map_add, inner_add_right, inner_add_right, ht₁, ht₂]
    | add s₁ s₂ hs₁ hs₂ => rw [map_add, inner_add_left, inner_add_left, hs₁, hs₂]
  have hdense := denseRange_stinespringLiftLinear π V hmin
  ext v
  refine ext_inner_left ℂ fun u =>
    hdense.induction_on u (isClosed_eq (by fun_prop) (by fun_prop)) fun s =>
      hdense.induction_on v
        (isClosed_eq (continuous_const.inner T₁.continuous) (continuous_const.inner T₂.continuous))
        (hlift s)

/-- **Arveson's Radon–Nikodym theorem (nonunital domain)**. -/
theorem radonNikodym_nonUnital (φ ψ : A →CP (H →L[ℂ] H))
    (π : A →⋆ₙₐ[ℂ] (K →L[ℂ] K)) (V : H →L[ℂ] K)
    (hφ : ∀ a, φ a = V.adjoint.comp ((π a).comp V))
    (hmin : (Submodule.span ℂ {x : K | ∃ (a : A) (ξ : H), x = π a (V ξ)}).topologicalClosure = ⊤)
    (hdom : ψ ≤ φ) :
    ∃! T : K →L[ℂ] K, 0 ≤ T ∧ T ≤ 1 ∧ (∀ a, Commute T (π a)) ∧
      ∀ a, ψ a = V.adjoint.comp (T.comp ((π a).comp V)) := by
  have hdense := denseRange_stinespringLiftLinear π V hmin
  have hbound (t : A ⊗[ℂ] H) :
      ‖ψ.toStinespringLinearMap t‖ ≤ 1 * ‖stinespringLiftLinear π V t‖ := by
    rw [one_mul, φ.norm_stinespringLiftLinear_eq π V hφ t]
    exact norm_toStinespringLinearMap_le_of_le hdom t
  let W : K →L[ℂ] ψ.Stinespring := ψ.toStinespringLinearMap.extendOfNorm (stinespringLiftLinear π V)
  have hW_apply (a : A) (ξ : H) : W (π a (V ξ)) = ψ.toStinespring a ξ := by
    simpa only [W, stinespringLiftLinear_tmul, toStinespringLinearMap_apply,
      toStinespring_apply] using LinearMap.extendOfNorm_eq hdense ⟨1, hbound⟩ (a ⊗ₜ[ℂ] ξ)
  have hW_norm (x : K) : ‖W x‖ ≤ ‖x‖ := by
    simpa only [W, one_mul] using LinearMap.norm_extendOfNorm_apply_le hdense 1 hbound x
  have hWπ (a : A) : W.comp (π a) = (ψ.stinespringHom a).comp W := by
    refine ContinuousLinearMap.ext fun x =>
      hdense.induction_on x (isClosed_eq (by fun_prop) (by fun_prop)) fun t => ?_
    induction t using TensorProduct.inductionOn with
    | tmul b ξ =>
      have hab : π a (π b (V ξ)) = π (a * b) (V ξ) := by
        rw [map_mul, ContinuousLinearMap.mul_def, ContinuousLinearMap.comp_apply]
      simp only [ContinuousLinearMap.comp_apply, stinespringLiftLinear_tmul, hab, hW_apply,
        stinespringHom_toStinespring]
    | add s₁ s₂ hs₁ hs₂ => rw [map_add, map_add, map_add, hs₁, hs₂]
  have hWV : W.comp V = ψ.stinespringOp := ContinuousLinearMap.ext fun ξ => by
    have hl := CStarAlgebra.increasingApproximateUnit A
    have := hl.neBot
    have h₁ : Tendsto (fun e => W (π e (V ξ))) (CStarAlgebra.approximateUnit A) (𝓝 (W (V ξ))) :=
      (W.continuous.tendsto _).comp ((NonUnitalStarAlgHom.isNondegenerate_iff_tendsto hl).mp
        (isNondegenerate_of_minimal π V hmin) (V ξ))
    exact tendsto_nhds_unique h₁
      (by simpa only [hW_apply] using ψ.tendsto_toStinespring_approximateUnit ξ)
  have hcommW (a : A) : Commute (W.adjoint.comp W) (π a) := by
    have hadj : (π a).comp W.adjoint = W.adjoint.comp (ψ.stinespringHom a) := by
      simpa only [ContinuousLinearMap.adjoint_comp, ← ContinuousLinearMap.star_eq_adjoint,
        ← map_star, star_star] using congrArg ContinuousLinearMap.adjoint (hWπ (star a))
    change (W.adjoint.comp W).comp (π a) = (π a).comp (W.adjoint.comp W)
    rw [ContinuousLinearMap.comp_assoc, hWπ a, ← ContinuousLinearMap.comp_assoc, ← hadj,
      ContinuousLinearMap.comp_assoc]
  have hψW (a : A) : ψ a = V.adjoint.comp ((W.adjoint.comp W).comp ((π a).comp V)) := by
    have hadjV : V.adjoint.comp W.adjoint = ψ.stinespringOp.adjoint := by
      simpa only [ContinuousLinearMap.adjoint_comp] using congrArg ContinuousLinearMap.adjoint hWV
    have hWaV : W.comp ((π a).comp V) = (ψ.stinespringHom a).comp ψ.stinespringOp := by
      rw [← ContinuousLinearMap.comp_assoc, hWπ a, ContinuousLinearMap.comp_assoc, hWV]
    rw [← ψ.stinespring_eq a, ← hadjV, ← hWaV]
    simp only [ContinuousLinearMap.comp_assoc]
  exact ⟨W.adjoint.comp W,
    ⟨ContinuousLinearMap.nonneg_iff_isPositive.mpr
      (ContinuousLinearMap.isPositive_adjoint_comp_self W),
      (ContinuousLinearMap.norm_map_le_norm_iff_le W).mp hW_norm, hcommW, hψW⟩,
    fun T' ⟨_, _, hT'comm, hT'ψ⟩ =>
      radonNikodym_unique π V hmin hT'comm hcommW fun a => (hT'ψ a).symm.trans (hψW a)⟩

/-- **Arveson's Radon–Nikodym order isomorphism** onto `Set.Icc 0 φ`. -/
noncomputable def radonNikodymOrderIso (φ : A →CP (H →L[ℂ] H))
    (π : A →⋆ₙₐ[ℂ] (K →L[ℂ] K)) (V : H →L[ℂ] K)
    (hφ : ∀ a, φ a = V.adjoint.comp ((π a).comp V))
    (hmin : (Submodule.span ℂ {x : K | ∃ (a : A) (ξ : H), x = π a (V ξ)}).topologicalClosure = ⊤) :
    {T : K →L[ℂ] K // T ∈ Set.Icc 0 1 ∧ ∀ a, Commute T (π a)} ≃o
      Set.Icc (0 : A →CP (H →L[ℂ] H)) φ where
  toFun T := ⟨radonNikodymMap π V T.1, radonNikodymMap_mem_Icc π V hφ T.2.1 T.2.2⟩
  invFun ψ :=
    let h := (φ.radonNikodym_nonUnital ψ.1 π V hφ hmin ψ.2.2).choose_spec.1
    ⟨(φ.radonNikodym_nonUnital ψ.1 π V hφ hmin ψ.2.2).choose, ⟨h.1, h.2.1⟩, h.2.2.1⟩
  left_inv T := Subtype.ext <|
    ((φ.radonNikodym_nonUnital (radonNikodymMap π V T.1) π V hφ hmin
      (radonNikodymMap_mem_Icc π V hφ T.2.1 T.2.2).2).choose_spec.2 T.1
      ⟨T.2.1.1, T.2.1.2, T.2.2, fun a => radonNikodymMap_apply π V T.2.1.1 T.2.2 a⟩).symm
  right_inv ψ := Subtype.ext <| CompletelyPositiveMap.ext fun a =>
    let h := (φ.radonNikodym_nonUnital ψ.1 π V hφ hmin ψ.2.2).choose_spec.1
    (radonNikodymMap_apply π V h.1 h.2.2.1 a).trans (h.2.2.2 a).symm
  map_rel_iff' {T₁ T₂} := ⟨fun hle => by
    obtain ⟨θ, hθ⟩ := Subtype.mk_le_mk.mp hle
    have hθ_le : θ ≤ φ := le_trans ⟨radonNikodymMap π V T₁.1, add_comm θ _ ▸ hθ⟩
      (radonNikodymMap_mem_Icc π V hφ T₂.2.1 T₂.2.2).2
    obtain ⟨S, ⟨hS0, _, hScomm, hSθ⟩, _⟩ := φ.radonNikodym_nonUnital θ π V hφ hmin hθ_le
    have hθ_eq : θ = radonNikodymMap π V S :=
      CompletelyPositiveMap.ext fun a => (hSθ a).trans (radonNikodymMap_apply π V hS0 hScomm a).symm
    have hsum : radonNikodymMap π V T₂.1 = radonNikodymMap π V (T₁.1 + S) := by
      rw [hθ, hθ_eq, ← radonNikodymMap_add π V T₁.2.1.1 hS0 T₁.2.2 hScomm]
    have hT₂_eq : T₂.1 = T₁.1 + S :=
      radonNikodym_unique π V hmin T₂.2.2 (fun a => (T₁.2.2 a).add_left (hScomm a)) fun a => by
        rw [← radonNikodymMap_apply π V T₂.2.1.1 T₂.2.2 a, hsum,
          radonNikodymMap_apply π V (add_nonneg T₁.2.1.1 hS0)
            (fun b => (T₁.2.2 b).add_left (hScomm b)) a]
    exact Subtype.mk_le_mk.mpr (hT₂_eq ▸ le_add_of_nonneg_right hS0), fun h12 =>
    Subtype.mk_le_mk.mpr
      (radonNikodymMap_mono π V T₁.2.1.1 (Subtype.mk_le_mk.mp h12) T₁.2.2 T₂.2.2)⟩

@[simp] theorem coe_radonNikodymOrderIso_apply (φ : A →CP (H →L[ℂ] H))
    (π : A →⋆ₙₐ[ℂ] (K →L[ℂ] K)) (V : H →L[ℂ] K)
    (hφ : ∀ a, φ a = V.adjoint.comp ((π a).comp V))
    (hmin : (Submodule.span ℂ {x : K | ∃ (a : A) (ξ : H), x = π a (V ξ)}).topologicalClosure = ⊤)
    (T : {T : K →L[ℂ] K // T ∈ Set.Icc 0 1 ∧ ∀ a, Commute T (π a)}) :
    (φ.radonNikodymOrderIso π V hφ hmin T : A →CP (H →L[ℂ] H)) = radonNikodymMap π V T.1 := (rfl)

end NonUnital

section Unital

variable {D : Type u} [CStarAlgebra D] [PartialOrder D] [StarOrderedRing D]
  {H : Type v} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {K : Type w} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

/-- **Arveson's Radon–Nikodym theorem** (Arveson 1969, Theorem 1.4.2). -/
theorem cp_radonNikodym (φ ψ : D →CP (H →L[ℂ] H))
    (π : D →⋆ₐ[ℂ] (K →L[ℂ] K)) (V : H →L[ℂ] K)
    (hφ : ∀ a, φ a = V.adjoint.comp ((π a).comp V))
    (hminimal : (Submodule.span ℂ
      {x : K | ∃ (a : D) (ξ : H), x = π a (V ξ)}).topologicalClosure = ⊤)
    (hdom : ∃ θ : D →CP (H →L[ℂ] H), ∀ a, φ a = ψ a + θ a) :
    ∃! T : K →L[ℂ] K, 0 ≤ T ∧ T ≤ 1 ∧ (∀ a, Commute T (π a)) ∧
      ∀ a, ψ a = V.adjoint.comp (T.comp ((π a).comp V)) :=
  φ.radonNikodym_nonUnital ψ π.toNonUnitalStarAlgHom V hφ hminimal
    (le_iff_exists_forall_add.mpr hdom)

end Unital

end CompletelyPositiveMap

namespace ContinuousLinearMap

variable {H : Type v} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

/-- The commutant of `H →L[ℂ] H` consists of scalar multiples of `1`. -/
theorem commute_forall_iff {T : H →L[ℂ] H} :
    (∀ a : H →L[ℂ] H, Commute T a) ↔ ∃ c : ℂ, T = c • 1 := by
  have hmem : (∀ a : H →L[ℂ] H, Commute T a) ↔ T ∈ Subalgebra.center ℂ (H →L[ℂ] H) := by
    rw [Subalgebra.mem_center_iff]
    exact forall_congr' fun _ => by simp [Commute, SemiconjBy, eq_comm]
  rw [hmem, Algebra.IsCentral.mem_center_iff (K := ℂ)]
  exact exists_congr fun _ => by simp [Algebra.algebraMap_eq_smul_one]

/-- On a nontrivial Hilbert space, `0 ≤ c • 1` implies `c` comes from `ℝ≥0`. -/
theorem exists_nnreal_of_nonneg_smul_one [Nontrivial H] {c : ℂ}
    (hc : 0 ≤ c • (1 : H →L[ℂ] H)) : ∃ t : ℝ≥0, c = t := by
  obtain ⟨ξ, hξ⟩ := exists_ne (0 : H)
  have hpos : 0 < ‖ξ‖ ^ 2 := pow_pos (norm_pos_iff.mpr hξ) 2
  have hinner : 0 ≤ c * (‖ξ‖ ^ 2 : ℂ) := by
    simpa [inner_self_eq_norm_sq_to_K] using
      (ContinuousLinearMap.nonneg_iff_isPositive.mp hc).inner_nonneg_right ξ
  obtain ⟨hre, him⟩ := RCLike.nonneg_iff.mp hinner
  have hc_re : 0 ≤ c.re :=
    nonneg_of_mul_nonneg_left (by simpa [← Complex.ofReal_pow] using hre) hpos
  have hc_im : c.im = 0 :=
    (mul_eq_zero.mp (by simpa [← Complex.ofReal_pow] using him)).resolve_right hpos.ne'
  exact ⟨⟨c.re, hc_re⟩, Complex.ext rfl hc_im⟩

/-- Left multiplication `a ↦ T * a` on `H →L[ℂ] H` preserves positivity iff `T = t • 1` for some
`t : ℝ≥0`. -/
theorem forall_nonneg_mul_nonneg_iff [CompleteSpace H] {T : H →L[ℂ] H} :
    (∀ a : H →L[ℂ] H, 0 ≤ a → 0 ≤ T * a) ↔ ∃ t : ℝ≥0, T = t • 1 := by
  refine ⟨fun h => ?_, ?_⟩
  · by_cases hH : Subsingleton H
    · exact ⟨0, Subsingleton.elim _ _⟩
    rw [not_subsingleton_iff_nontrivial] at hH
    have hT0 : 0 ≤ T := by simpa only [mul_one] using h 1 zero_le_one
    have hTsa : star T = T := (IsSelfAdjoint.of_nonneg hT0).star_eq
    let D : (H →L[ℂ] H) →ₗ[ℂ] (H →L[ℂ] H) :=
      { toFun x := T * x - x * T
        map_add' _ _ := by simp only [mul_add, add_mul]; abel
        map_smul' _ _ := by simp [smul_sub] }
    have hD0 : D = 0 := LinearMap.ext_on CStarAlgebra.span_nonneg fun a ha => by
      have hasa := (IsSelfAdjoint.of_nonneg (Set.mem_ofPred.mp ha)).star_eq
      have hTasa := (IsSelfAdjoint.of_nonneg (h a (Set.mem_ofPred.mp ha))).star_eq
      simp [D, hTasa.symm.trans (by rw [star_mul, hasa, hTsa])]
    obtain ⟨c, rfl⟩ := commute_forall_iff.mp fun x =>
      sub_eq_zero.mp (by simpa [D] using LinearMap.congr_fun hD0 x)
    obtain ⟨t, rfl⟩ := exists_nnreal_of_nonneg_smul_one hT0
    exact ⟨t, by simp [NNReal.smul_def, ← Complex.coe_smul]⟩
  · rintro ⟨t, rfl⟩ a ha
    rw [smul_mul_assoc, one_mul, NNReal.smul_def]
    exact smul_nonneg t.2 ha

end ContinuousLinearMap

namespace CompletelyPositiveMap

variable {H : Type v} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- On a nontrivial `H`, `Set.Icc 0 (CompletelyPositiveMap.id (H →L[ℂ] H))` consists strictly of
`[0, 1]`-multiples of `id`. -/
theorem mem_Icc_zero_id_iff [Nontrivial H] {ψ : (H →L[ℂ] H) →CP (H →L[ℂ] H)} :
    ψ ∈ Set.Icc 0 (CompletelyPositiveMap.id (H →L[ℂ] H)) ↔
      ∃ t ∈ Set.Icc (0 : ℝ≥0) 1, ψ = t • CompletelyPositiveMap.id (H →L[ℂ] H) := by
  refine ⟨?_, ?_⟩
  · rintro ⟨_, hψ⟩
    obtain ⟨T, ⟨hT0, hT1, hTcomm, hTψ⟩, _⟩ :=
      (CompletelyPositiveMap.id (H →L[ℂ] H)).cp_radonNikodym ψ
        (StarAlgHom.id ℂ (H →L[ℂ] H)) (ContinuousLinearMap.id ℂ H)
        (id_dilation_eq H) (id_dilation_minimal H) (le_iff_exists_forall_add.mp hψ)
    obtain ⟨c, rfl⟩ := ContinuousLinearMap.commute_forall_iff.mp hTcomm
    obtain ⟨t, rfl⟩ := ContinuousLinearMap.exists_nnreal_of_nonneg_smul_one hT0
    obtain ⟨s, hs⟩ := ContinuousLinearMap.exists_nnreal_of_nonneg_smul_one
      (by simpa only [sub_smul, one_smul] using sub_nonneg.mpr hT1 :
        0 ≤ ((1 : ℂ) - t) • (1 : H →L[ℂ] H))
    have ht1 : t ≤ 1 := by
      have hsre := congrArg Complex.re hs
      simp only [Complex.sub_re, Complex.one_re, Complex.ofReal_re] at hsre
      rw [← NNReal.coe_le_coe, NNReal.coe_one]; linarith [NNReal.coe_nonneg s]
    refine ⟨t, ⟨by positivity, ht1⟩, CompletelyPositiveMap.ext fun a => ?_⟩
    simp [hTψ a, ContinuousLinearMap.adjoint_id, ContinuousLinearMap.one_def, NNReal.smul_def,
      ← Complex.coe_smul]
  · rintro ⟨t, ⟨_, ht1⟩, rfl⟩
    exact ⟨zero_le _, ⟨(1 - t) • CompletelyPositiveMap.id (H →L[ℂ] H), by
      rw [← add_smul, add_tsub_cancel_of_le ht1, one_smul]⟩⟩

end CompletelyPositiveMap
