/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Basic
public import TauCeti.Analysis.CStarAlgebra.Stinespring.Uniqueness
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Commute
import Mathlib.Analysis.Normed.Operator.Extend
import TauCeti.Analysis.InnerProductSpace.Positive.Basic
import TauCeti.Analysis.LocallyConvex.SeparatingDual

/-!
# Arveson's Radon–Nikodym theorem for completely positive maps

Given a minimal Stinespring dilation `(K, π, V)` of `φ : A →CP (H →L[ℂ] H)`, completely positive
maps `ψ ≤ φ` correspond order-isomorphically (`CompletelyPositiveMap.radonNikodymOrderIso`) to
positive contractions `T : K →L[ℂ] K` (`0 ≤ T ≤ 1`) in the commutant of `π(A)` via
`ψ a = V† ∘L T ∘L π a ∘L V` (`NonUnitalStarAlgHom.radonNikodymMap`,
`CompletelyPositiveMap.radonNikodym_nonUnital`, `CompletelyPositiveMap.cp_radonNikodym`).

As a boundary check on `φ = id_{B(H)}`, the commutant of `B(H)` is `ℂ • 1`
(`ContinuousLinearMap.commute_forall_iff`), so `Set.Icc 0 id` consists of `[0, 1]`-multiples of `id`
(`CompletelyPositiveMap.mem_Icc_zero_id_iff`).

## References

* W. B. Arveson, *Subalgebras of C⋆-algebras*, Acta Math. 123 (1969), 141–224, Theorem 1.4.2.
* V. Paulsen, *Completely Bounded Maps and Operator Algebras*, Theorem 4.4.
-/

public section

universe u v w

open Filter Topology TensorProduct
open scoped CStarAlgebra ComplexOrder InnerProductSpace NNReal

namespace NonUnitalStarAlgHom

section RadonNikodymForward

variable {A : Type u} [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  {H : Type v} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {K : Type w} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
  (π : A →⋆ₙₐ[ℂ] (K →L[ℂ] K)) (V : H →L[ℂ] K)

/-- The completely positive map `((CFC.sqrt T).comp V).conjAdjoint.comp π` associated with
`T : K →L[ℂ] K`, evaluating to `a ↦ V† ∘L T ∘L π a ∘L V` when `0 ≤ T` commutes with `π(A)`. -/
noncomputable def radonNikodymMap (T : K →L[ℂ] K) : A →CP (H →L[ℂ] H) :=
  (((CFC.sqrt T).comp V).conjAdjoint).comp
    (CompletelyPositiveMapClass.toCompletelyPositiveLinearMap π)

theorem radonNikodymMap_apply {T : K →L[ℂ] K} (hT : 0 ≤ T)
    (hcomm : ∀ a, Commute T (π a)) (a : A) :
    π.radonNikodymMap V T a = V.adjoint.comp (T.comp ((π a).comp V)) := by
  have hsqrt_comm : Commute (CFC.sqrt T) (π a) := by
    rw [CFC.sqrt_eq_cfc]; exact (hcomm a).cfc_nnreal NNReal.sqrt
  have hsqrt_adj : (CFC.sqrt T).adjoint = CFC.sqrt T :=
    ContinuousLinearMap.star_eq_adjoint (CFC.sqrt T) ▸
      (IsSelfAdjoint.of_nonneg (CFC.sqrt_nonneg T)).star_eq
  have hmul : (CFC.sqrt T).comp ((π a).comp (CFC.sqrt T)) = T.comp (π a) := by
    simp only [← ContinuousLinearMap.mul_def]
    rw [← hsqrt_comm.eq, ← mul_assoc, CFC.sqrt_mul_sqrt_self T hT]
  rw [radonNikodymMap, CompletelyPositiveMap.comp_apply,
    CompletelyPositiveMapClass.coe_toCompletelyPositiveLinearMap,
    ContinuousLinearMap.conjAdjoint_apply, ContinuousLinearMap.adjoint_comp, hsqrt_adj]
  simpa only [ContinuousLinearMap.comp_assoc] using
    congrArg (fun S => V.adjoint.comp (S.comp V)) hmul

@[simp] theorem radonNikodymMap_zero : π.radonNikodymMap V 0 = 0 := by
  ext a; simp [π.radonNikodymMap_apply V le_rfl (fun _ => Commute.zero_left _) a]

theorem radonNikodymMap_one {φ : A →CP (H →L[ℂ] H)}
    (hφ : ∀ a, φ a = V.adjoint.comp ((π a).comp V)) : π.radonNikodymMap V 1 = φ := by
  ext a
  rw [π.radonNikodymMap_apply V zero_le_one (fun _ => Commute.one_left _) a, hφ a,
    ContinuousLinearMap.one_def, ContinuousLinearMap.id_comp]

theorem radonNikodymMap_add {T₁ T₂ : K →L[ℂ] K} (hT₁ : 0 ≤ T₁) (hT₂ : 0 ≤ T₂)
    (hcomm₁ : ∀ a, Commute T₁ (π a)) (hcomm₂ : ∀ a, Commute T₂ (π a)) :
    π.radonNikodymMap V (T₁ + T₂) = π.radonNikodymMap V T₁ + π.radonNikodymMap V T₂ := by
  ext a
  rw [add_apply, π.radonNikodymMap_apply V (add_nonneg hT₁ hT₂)
      (fun b => (hcomm₁ b).add_left (hcomm₂ b)) a,
    π.radonNikodymMap_apply V hT₁ hcomm₁ a, π.radonNikodymMap_apply V hT₂ hcomm₂ a,
    ContinuousLinearMap.add_comp, ContinuousLinearMap.comp_add]

theorem radonNikodymMap_smul (c : ℝ≥0) {T : K →L[ℂ] K} (hT : 0 ≤ T)
    (hcomm : ∀ a, Commute T (π a)) :
    π.radonNikodymMap V (c • T) = c • π.radonNikodymMap V T := by
  have hcT : 0 ≤ c • T := NNReal.smul_def c T ▸ smul_nonneg c.property hT
  have hccomm : ∀ a, Commute (c • T) (π a) := fun a => by
    simp only [Commute, SemiconjBy, smul_mul_assoc, mul_smul_comm, (hcomm a).eq]
  ext a
  simp [π.radonNikodymMap_apply V hcT hccomm a, π.radonNikodymMap_apply V hT hcomm a]

theorem radonNikodymMap_mono {T₁ T₂ : K →L[ℂ] K} (hT₁ : 0 ≤ T₁) (h12 : T₁ ≤ T₂)
    (hcomm₁ : ∀ a, Commute T₁ (π a)) (hcomm₂ : ∀ a, Commute T₂ (π a)) :
    π.radonNikodymMap V T₁ ≤ π.radonNikodymMap V T₂ :=
  ⟨π.radonNikodymMap V (T₂ - T₁), by
    rw [← π.radonNikodymMap_add V hT₁ (sub_nonneg.mpr h12) hcomm₁
      (fun a => (hcomm₂ a).sub_left (hcomm₁ a)), add_sub_cancel]⟩

theorem radonNikodymMap_mem_Icc {φ : A →CP (H →L[ℂ] H)}
    (hφ : ∀ a, φ a = V.adjoint.comp ((π a).comp V))
    {T : K →L[ℂ] K} (hT : T ∈ Set.Icc 0 1) (hcomm : ∀ a, Commute T (π a)) :
    π.radonNikodymMap V T ∈ Set.Icc 0 φ :=
  ⟨CompletelyPositiveMap.zero_le _, π.radonNikodymMap_one V hφ ▸
    π.radonNikodymMap_mono V hT.1 hT.2 hcomm fun _ => Commute.one_left _⟩

end RadonNikodymForward

section RadonNikodymUnique

variable {A : Type u} [NonUnitalCStarAlgebra A]
  {H : Type v} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {K : Type w} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

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
      ⟪π.stinespringLiftLinear V s, T₁ (π.stinespringLiftLinear V t)⟫_ℂ =
        ⟪π.stinespringLiftLinear V s, T₂ (π.stinespringLiftLinear V t)⟫_ℂ := by
    induction s using TensorProduct.inductionOn with
    | tmul a ξ =>
      induction t using TensorProduct.inductionOn with
      | tmul b η =>
        simp only [stinespringLiftLinear_tmul, key T₁ hcomm₁, key T₂ hcomm₂, heq (star a * b)]
      | add t₁ t₂ ht₁ ht₂ =>
        rw [map_add, map_add, map_add, inner_add_right, inner_add_right, ht₁, ht₂]
    | add s₁ s₂ hs₁ hs₂ => rw [map_add, inner_add_left, inner_add_left, hs₁, hs₂]
  have hdense := π.denseRange_stinespringLiftLinear V hmin
  ext v
  refine ext_inner_left ℂ fun u =>
    hdense.induction_on u (isClosed_eq (by fun_prop) (by fun_prop)) fun s =>
      hdense.induction_on v
        (isClosed_eq (continuous_const.inner T₁.continuous) (continuous_const.inner T₂.continuous))
        (hlift s)

end RadonNikodymUnique

end NonUnitalStarAlgHom

namespace CompletelyPositiveMap

section NonUnital

variable {A : Type u} [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  {H : Type v} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {K : Type w} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

/-- **Arveson's Radon–Nikodym theorem (nonunital domain)**. -/
theorem radonNikodym_nonUnital (φ ψ : A →CP (H →L[ℂ] H))
    (π : A →⋆ₙₐ[ℂ] (K →L[ℂ] K)) (V : H →L[ℂ] K)
    (hφ : ∀ a, φ a = V.adjoint.comp ((π a).comp V))
    (hmin : (Submodule.span ℂ {x : K | ∃ (a : A) (ξ : H), x = π a (V ξ)}).topologicalClosure = ⊤)
    (hdom : ψ ≤ φ) :
    ∃! T : K →L[ℂ] K, 0 ≤ T ∧ T ≤ 1 ∧ (∀ a, Commute T (π a)) ∧
      ∀ a, ψ a = V.adjoint.comp (T.comp ((π a).comp V)) := by
  have hdense := π.denseRange_stinespringLiftLinear V hmin
  have hbound (t : A ⊗[ℂ] H) :
      ‖ψ.toStinespringLinearMap t‖ ≤ 1 * ‖π.stinespringLiftLinear V t‖ := by
    rw [one_mul, φ.norm_stinespringLiftLinear_eq π V hφ t]
    exact norm_toStinespringLinearMap_le_of_le hdom t
  let W : K →L[ℂ] ψ.Stinespring :=
    ψ.toStinespringLinearMap.extendOfNorm (π.stinespringLiftLinear V)
  have hW_apply (a : A) (ξ : H) : W (π a (V ξ)) = ψ.toStinespring a ξ := by
    simpa only [W, NonUnitalStarAlgHom.stinespringLiftLinear_tmul, toStinespringLinearMap_apply,
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
      simp only [ContinuousLinearMap.comp_apply, NonUnitalStarAlgHom.stinespringLiftLinear_tmul,
        hab, hW_apply, stinespringHom_toStinespring]
    | add s₁ s₂ hs₁ hs₂ => rw [map_add, map_add, map_add, hs₁, hs₂]
  have hWV : W.comp V = ψ.stinespringOp := ContinuousLinearMap.ext fun ξ => by
    have hl := CStarAlgebra.increasingApproximateUnit A
    have := hl.neBot
    have h₁ : Tendsto (fun e => W (π e (V ξ))) (CStarAlgebra.approximateUnit A) (𝓝 (W (V ξ))) :=
      (W.continuous.tendsto _).comp ((NonUnitalStarAlgHom.isNondegenerate_iff_tendsto
        hl.eventually_norm hl.tendsto_mul_right).mp (π.isNondegenerate_of_minimal V hmin) (V ξ))
    exact tendsto_nhds_unique h₁
      (by simpa only [hW_apply] using ψ.tendsto_toStinespring_approximateUnit ξ)
  have hcommW (a : A) : Commute (W.adjoint.comp W) (π a) := by
    have hadj : (π a).comp W.adjoint = W.adjoint.comp (ψ.stinespringHom a) := by
      simpa only [ContinuousLinearMap.adjoint_comp, ← ContinuousLinearMap.star_eq_adjoint,
        ← map_star, star_star] using congrArg ContinuousLinearMap.adjoint (hWπ (star a))
    rw [Commute, SemiconjBy, ContinuousLinearMap.mul_def, ContinuousLinearMap.mul_def,
      ContinuousLinearMap.comp_assoc, hWπ a, ← ContinuousLinearMap.comp_assoc, ← hadj,
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
      π.radonNikodym_unique V hmin hT'comm hcommW fun a => (hT'ψ a).symm.trans (hψW a)⟩

/-- **Arveson's Radon–Nikodym order isomorphism** onto `Set.Icc 0 φ`. -/
noncomputable def radonNikodymOrderIso (φ : A →CP (H →L[ℂ] H))
    (π : A →⋆ₙₐ[ℂ] (K →L[ℂ] K)) (V : H →L[ℂ] K)
    (hφ : ∀ a, φ a = V.adjoint.comp ((π a).comp V))
    (hmin : (Submodule.span ℂ {x : K | ∃ (a : A) (ξ : H), x = π a (V ξ)}).topologicalClosure = ⊤) :
    {T : K →L[ℂ] K // T ∈ Set.Icc 0 1 ∧ ∀ a, Commute T (π a)} ≃o
      Set.Icc (0 : A →CP (H →L[ℂ] H)) φ where
  toFun T := ⟨π.radonNikodymMap V T.val, π.radonNikodymMap_mem_Icc V hφ T.property.1 T.property.2⟩
  invFun ψ :=
    let h := (φ.radonNikodym_nonUnital ψ.val π V hφ hmin ψ.property.2).choose_spec.1
    ⟨(φ.radonNikodym_nonUnital ψ.val π V hφ hmin ψ.property.2).choose, ⟨h.1, h.2.1⟩, h.2.2.1⟩
  left_inv T := Subtype.ext <|
    ((φ.radonNikodym_nonUnital (π.radonNikodymMap V T.val) π V hφ hmin
      (π.radonNikodymMap_mem_Icc V hφ T.property.1 T.property.2).2).choose_spec.2 T.val
      ⟨T.property.1.1, T.property.1.2, T.property.2, fun a => π.radonNikodymMap_apply V
          T.property.1.1 T.property.2 a⟩).symm
  right_inv ψ := Subtype.ext <| CompletelyPositiveMap.ext fun a =>
    let h := (φ.radonNikodym_nonUnital ψ.val π V hφ hmin ψ.property.2).choose_spec.1
    (π.radonNikodymMap_apply V h.1 h.2.2.1 a).trans (h.2.2.2 a).symm
  map_rel_iff' {T₁ T₂} := ⟨fun hle => by
    obtain ⟨θ, hθ⟩ := Subtype.mk_le_mk.mp hle
    have hθ_le : θ ≤ φ := le_trans ⟨π.radonNikodymMap V T₁.val, add_comm θ _ ▸ hθ⟩
      (π.radonNikodymMap_mem_Icc V hφ T₂.property.1 T₂.property.2).2
    obtain ⟨S, ⟨hS0, _, hScomm, hSθ⟩, _⟩ := φ.radonNikodym_nonUnital θ π V hφ hmin hθ_le
    have hθ_eq : θ = π.radonNikodymMap V S :=
      CompletelyPositiveMap.ext fun a =>
        (hSθ a).trans (π.radonNikodymMap_apply V hS0 hScomm a).symm
    have hsum : π.radonNikodymMap V T₂.val = π.radonNikodymMap V (T₁.val + S) := by
      rw [hθ, hθ_eq, ← π.radonNikodymMap_add V T₁.property.1.1 hS0 T₁.property.2 hScomm]
    have hT₂_eq : T₂.val = T₁.val + S :=
      π.radonNikodym_unique V hmin T₂.property.2
        (fun a => (T₁.property.2 a).add_left (hScomm a)) fun a => by
        rw [← π.radonNikodymMap_apply V T₂.property.1.1 T₂.property.2 a, hsum,
          π.radonNikodymMap_apply V (add_nonneg T₁.property.1.1 hS0)
            (fun b => (T₁.property.2 b).add_left (hScomm b)) a]
    exact Subtype.mk_le_mk.mpr (hT₂_eq ▸ le_add_of_nonneg_right hS0), fun h12 =>
    Subtype.mk_le_mk.mpr
      (π.radonNikodymMap_mono V T₁.property.1.1 (Subtype.mk_le_mk.mp h12) T₁.property.2
          T₂.property.2)⟩

@[simp] theorem coe_radonNikodymOrderIso_apply (φ : A →CP (H →L[ℂ] H))
    (π : A →⋆ₙₐ[ℂ] (K →L[ℂ] K)) (V : H →L[ℂ] K)
    (hφ : ∀ a, φ a = V.adjoint.comp ((π a).comp V))
    (hmin : (Submodule.span ℂ {x : K | ∃ (a : A) (ξ : H), x = π a (V ξ)}).topologicalClosure = ⊤)
    (T : {T : K →L[ℂ] K // T ∈ Set.Icc 0 1 ∧ ∀ a, Commute T (π a)}) :
    (φ.radonNikodymOrderIso π V hφ hmin T : A →CP (H →L[ℂ] H)) = π.radonNikodymMap V T.val := (rfl)

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

section IdentityOrderInterval

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
    obtain ⟨hc_re, hc_im⟩ := RCLike.nonneg_iff.mp (ContinuousLinearMap.smul_one_nonneg_iff.mp hT0)
    obtain ⟨t, rfl⟩ : ∃ t : ℝ≥0, c = t := ⟨⟨c.re, hc_re⟩, Complex.ext rfl hc_im⟩
    have hc1 : 0 ≤ (1 : ℂ) - t := (ContinuousLinearMap.smul_one_nonneg_iff (E := H)).mp <| by
      rw [sub_smul, one_smul]
      exact sub_nonneg.mpr hT1
    have ht1 : t ≤ 1 :=
      NNReal.coe_le_coe.mp (by simpa using (RCLike.nonneg_iff.mp hc1).1)
    refine ⟨t, ⟨by positivity, ht1⟩, CompletelyPositiveMap.ext fun a => ?_⟩
    simp [hTψ a, ContinuousLinearMap.adjoint_id, ContinuousLinearMap.one_def, NNReal.smul_def,
      ← Complex.coe_smul]
  · rintro ⟨t, ⟨_, ht1⟩, rfl⟩
    exact ⟨zero_le _, ⟨(1 - t) • CompletelyPositiveMap.id (H →L[ℂ] H), by
      rw [← add_smul, add_tsub_cancel_of_le ht1, one_smul]⟩⟩

end IdentityOrderInterval

end CompletelyPositiveMap
