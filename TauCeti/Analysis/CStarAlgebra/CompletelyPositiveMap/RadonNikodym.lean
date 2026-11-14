/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Order.Hom.Basic
public import TauCeti.Analysis.CStarAlgebra.CompletelyPositiveMap.Stinespring
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Commute
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Basic

/-!
# Arveson's Radon–Nikodym theorem for completely positive maps

Given a completely positive map `φ : A →CP (H →L[ℂ] H)` from a (possibly nonunital) C⋆-algebra `A`
into the bounded operators on a complex Hilbert space `H` and any minimal Stinespring dilation
`(K, π, V)` of `φ`, Arveson's Radon–Nikodym theorem identifies the order interval `[0, φ]` in the
completely positive cone with the operator interval `[0, 1]` inside the commutant `π(A)'`:

* every positive operator `T : K →L[ℂ] K` commuting with `π(A)` induces a completely positive map
  `compressCommutant π V T hT hcomm : A →CP (H →L[ℂ] H)` sending `a` to `V† ∘L T ∘L π a ∘L V`,
  monotone in `T`;
* for every `ψ ≤ φ`, there exists a unique `T : K →L[ℂ] K` with `0 ≤ T`, `T ≤ 1`,
  `∀ a, Commute T (π a)`, and `∀ a, ψ a = V† ∘L T ∘L π a ∘L V`
  (`existsUnique_commutant_of_le`, `existsUnique_commutant_of_le_unital`, `radonNikodym`);
* the assignment `T ↦ compressCommutant π V T` is an order isomorphism
  `{T : K →L[ℂ] K // 0 ≤ T ∧ T ≤ 1 ∧ ∀ a, Commute T (π a)} ≃o Set.Icc 0 φ`
  (`radonNikodymOrderIso`).

## Main declarations

* `NonUnitalStarAlgHom.eq_of_forall_adjoint_comp_eq`: an operator in the commutant `π(A)'` of a
  minimal dilation `(K, π, V)` is uniquely determined by the compressed family
  `a ↦ V† ∘L T ∘L π a ∘L V`.
* `CompletelyPositiveMap.compressCommutant`: completely positive map `a ↦ V† ∘L T ∘L π a ∘L V`
  associated to `0 ≤ T` commuting with `π`.
* `CompletelyPositiveMap.existsUnique_commutant_of_le`,
  `CompletelyPositiveMap.existsUnique_commutant_of_le_unital`: Arveson's Radon–Nikodym theorem in
  nonunital and unital `ψ ≤ φ` form.
* `CompletelyPositiveMap.radonNikodym`: unital existential-complement formulation
  `(∃ θ, ∀ a, φ a = ψ a + θ a) → ∃! T, ...`.
* `CompletelyPositiveMap.radonNikodymOrderIso`: canonical order isomorphism between `[0, 1]_{π(A)'}`
  and `Set.Icc 0 φ`.

## References

* W. B. Arveson, *Subalgebras of C*-algebras*, Acta Math. 123 (1969), 141–224, Theorem 1.4.2.
* V. Paulsen, *Completely Bounded Maps and Operator Algebras*, Theorem 12.7.
-/

public section

noncomputable section

open Filter Topology ContinuousLinearMap UniformSpace
open scoped CStarAlgebra ComplexOrder InnerProductSpace NNReal TensorProduct

universe u v w

namespace NonUnitalStarAlgHom

variable {A : Type u} {H : Type v} {K : Type w}
  [NonUnitalCStarAlgebra A]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

/-- On a minimal dilation `(K, π, V)`, an operator in the commutant `π(A)'` is uniquely determined
by the compressed family `a ↦ V† ∘L T ∘L π a ∘L V`. -/
theorem eq_of_forall_adjoint_comp_eq
    (π : A →⋆ₙₐ[ℂ] (K →L[ℂ] K)) (V : H →L[ℂ] K)
    (hmin : (Submodule.span ℂ {x : K | ∃ (a : A) (ξ : H), x = π a (V ξ)}).topologicalClosure = ⊤)
    {T₁ T₂ : K →L[ℂ] K}
    (hcomm₁ : ∀ a, Commute T₁ (π a)) (hcomm₂ : ∀ a, Commute T₂ (π a))
    (heq : ∀ a, V.adjoint.comp (T₁.comp ((π a).comp V)) =
      V.adjoint.comp (T₂.comp ((π a).comp V))) :
    T₁ = T₂ := by
  have hinner {T : K →L[ℂ] K} (hcomm : ∀ a, Commute T (π a)) (a b : A) (ξ η : H) :
      ⟪π a (V ξ), T (π b (V η))⟫_ℂ =
        ⟪ξ, (V.adjoint.comp (T.comp ((π (star a * b)).comp V))) η⟫_ℂ := by
    have hstar : π (star a) (T (π b (V η))) = T (π (star a * b) (V η)) := by
      simpa [ContinuousLinearMap.mul_def, map_mul] using
        congr($((hcomm (star a)).eq) (π b (V η))).symm
    calc
      ⟪π a (V ξ), T (π b (V η))⟫_ℂ
        = ⟪V ξ, (π a).adjoint (T (π b (V η)))⟫_ℂ :=
          (ContinuousLinearMap.adjoint_inner_right (π a) (V ξ) _).symm
      _ = ⟪V ξ, π (star a) (T (π b (V η)))⟫_ℂ := by
          rw [← ContinuousLinearMap.star_eq_adjoint, ← map_star]
      _ = ⟪V ξ, T (π (star a * b) (V η))⟫_ℂ := by rw [hstar]
      _ = ⟪ξ, (V.adjoint.comp (T.comp ((π (star a * b)).comp V))) η⟫_ℂ := by
          simp [ContinuousLinearMap.adjoint_inner_right]
  let S : Submodule ℂ K := Submodule.span ℂ {x : K | ∃ (a : A) (ξ : H), x = π a (V ξ)}
  have hdense : Dense (S : Set K) := Submodule.dense_iff_topologicalClosure_eq_top.mpr hmin
  have hspan : ∀ u ∈ S, ∀ v ∈ S, ⟪u, T₁ v⟫_ℂ = ⟪u, T₂ v⟫_ℂ := by
    intro u hu
    refine Submodule.span_induction ?_ ?_ ?_ ?_ hu
    · rintro _ ⟨a, ξ, rfl⟩ v hv
      refine Submodule.span_induction ?_ ?_ ?_ ?_ hv
      · rintro _ ⟨b, η, rfl⟩
        rw [hinner hcomm₁, hinner hcomm₂, heq]
      · simp
      · intro v₁ v₂ _ _ hv₁ hv₂
        rw [map_add, map_add, inner_add_right, inner_add_right, hv₁, hv₂]
      · intro c v _ hv
        rw [map_smul, map_smul, inner_smul_right, inner_smul_right, hv]
    · intro v _; simp
    · intro u₁ u₂ _ _ hu₁ hu₂ v hv
      rw [inner_add_left, inner_add_left, hu₁ v hv, hu₂ v hv]
    · intro c u _ hu v hv
      rw [inner_smul_left, inner_smul_left, hu v hv]
  have hright (u : K) (hu : u ∈ S) (v : K) : ⟪u, T₁ v⟫_ℂ = ⟪u, T₂ v⟫_ℂ :=
    (isClosed_eq ((innerSL ℂ u).comp T₁).continuous
      ((innerSL ℂ u).comp T₂).continuous).closure_subset_iff.mpr (hspan u hu) (hdense v)
  ext v
  refine ext_inner_right ℂ fun u => ?_
  have hleft : ∀ w ∈ (S : Set K), ⟪T₁ v, w⟫_ℂ = ⟪T₂ v, w⟫_ℂ := fun w hw => by
    rw [← inner_conj_symm (T₁ v) w, ← inner_conj_symm (T₂ v) w, hright w hw v]
  exact (isClosed_eq (innerSL ℂ (T₁ v)).continuous
    (innerSL ℂ (T₂ v)).continuous).closure_subset_iff.mpr hleft (hdense u)

end NonUnitalStarAlgHom

namespace CompletelyPositiveMap

section NonUnital

variable {A : Type u} {H : Type v} {K : Type w}
  [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

/-- A positive operator `T : K →L[ℂ] K` commuting with a ⋆-representation `π` compresses to a
completely positive map `a ↦ V† ∘L T ∘L π a ∘L V`. -/
def compressCommutant
    (π : A →⋆ₙₐ[ℂ] (K →L[ℂ] K)) (V : H →L[ℂ] K) (T : K →L[ℂ] K)
    (hT : 0 ≤ T) (hcomm : ∀ a, Commute T (π a)) : A →CP (H →L[ℂ] H) :=
  let f : A →ₗ[ℂ] (H →L[ℂ] H) :=
    { toFun a := V.adjoint.comp (T.comp ((π a).comp V))
      map_add' a b := by ext ξ; simp
      map_smul' c a := by ext ξ; simp }
  { toLinearMap := f
    map_cstarMatrix_nonneg' _ M hM := by
      let ψ : A →CP (H →L[ℂ] H) :=
        (conjCLM (CFC.sqrt T ∘L V)).comp (π : A →CP (K →L[ℂ] K))
      have hsqrt_adj : (CFC.sqrt T).adjoint = CFC.sqrt T := by
        rw [← ContinuousLinearMap.star_eq_adjoint]
        exact (IsSelfAdjoint.of_nonneg (CFC.sqrt_nonneg T)).star_eq
      have hEq : M.map f = M.map ψ := by
        ext i j ξ
        have hsqrt_comm : Commute (CFC.sqrt T) (π (M i j)) := by
          rw [CFC.sqrt_eq_nnrpow, CFC.nnrpow_def]
          exact (hcomm (M i j)).cfcₙ_nnreal _
        have hmid : (CFC.sqrt T).adjoint * (π (M i j) * CFC.sqrt T) = T * π (M i j) := by
          rw [hsqrt_adj, ← hsqrt_comm.eq, ← mul_assoc, CFC.sqrt_mul_sqrt_self T hT]
        simpa [f, ψ, CStarMatrix.map_apply, ContinuousLinearMap.adjoint_comp,
          ContinuousLinearMap.mul_def] using (congrArg V.adjoint congr($hmid (V ξ))).symm
      rw [hEq]
      exact ψ.map_cstarMatrix_nonneg M hM }

@[simp]
theorem compressCommutant_apply
    (π : A →⋆ₙₐ[ℂ] (K →L[ℂ] K)) (V : H →L[ℂ] K) (T : K →L[ℂ] K)
    (hT : 0 ≤ T) (hcomm : ∀ a, Commute T (π a)) (a : A) :
    compressCommutant π V T hT hcomm a = V.adjoint.comp (T.comp ((π a).comp V)) :=
  (rfl)

/-- `compressCommutant` is additive in the positive commuting operator `T`. -/
theorem compressCommutant_add
    (π : A →⋆ₙₐ[ℂ] (K →L[ℂ] K)) (V : H →L[ℂ] K) {T₁ T₂ : K →L[ℂ] K}
    (hT₁ : 0 ≤ T₁) (hT₂ : 0 ≤ T₂)
    (hcomm₁ : ∀ a, Commute T₁ (π a)) (hcomm₂ : ∀ a, Commute T₂ (π a)) :
    compressCommutant π V (T₁ + T₂) (add_nonneg hT₁ hT₂) (fun a => (hcomm₁ a).add_left (hcomm₂ a)) =
      compressCommutant π V T₁ hT₁ hcomm₁ + compressCommutant π V T₂ hT₂ hcomm₂ := by
  ext a ξ
  simp

/-- `compressCommutant` is monotone in `T` with respect to the completely positive order. -/
theorem compressCommutant_mono
    (π : A →⋆ₙₐ[ℂ] (K →L[ℂ] K)) (V : H →L[ℂ] K) {T₁ T₂ : K →L[ℂ] K}
    (hT₁ : 0 ≤ T₁) (hcomm₁ : ∀ a, Commute T₁ (π a)) (hcomm₂ : ∀ a, Commute T₂ (π a))
    (h12 : T₁ ≤ T₂) :
    compressCommutant π V T₁ hT₁ hcomm₁ ≤
      compressCommutant π V T₂ (hT₁.trans h12) hcomm₂ := by
  refine le_iff_exists_add.mpr ⟨compressCommutant π V (T₂ - T₁) (sub_nonneg.mpr h12)
    (fun a => (hcomm₂ a).sub_left (hcomm₁ a)), ?_⟩
  ext a ξ
  simp

private theorem compressCommutant_le_of_le_one
    {φ : A →CP (H →L[ℂ] H)} (π : A →⋆ₙₐ[ℂ] (K →L[ℂ] K)) (V : H →L[ℂ] K)
    (hφ : ∀ a, φ a = V.adjoint.comp ((π a).comp V))
    {T : K →L[ℂ] K} (hT0 : 0 ≤ T) (hT1 : T ≤ 1) (hcomm : ∀ a, Commute T (π a)) :
    compressCommutant π V T hT0 hcomm ≤ φ := by
  have h1 : compressCommutant π V 1 zero_le_one (fun _ => Commute.one_left _) = φ := by
    ext a ξ
    simp [hφ a]
  exact h1 ▸ compressCommutant_mono π V hT0 hcomm (fun _ => Commute.one_left _) hT1

private theorem norm_preStinespring_le_of_le
    {ψ φ : A →CP (H →L[ℂ] H)} (h : ψ ≤ φ) (x : φ.PreStinespring) :
    ‖ψ.toPreStinespring x.ofPreStinespring‖ ≤ 1 * ‖x‖ := by
  rw [one_mul]
  obtain ⟨θ, rfl⟩ := le_iff_exists_add.mp h
  obtain ⟨k, a, ξ, hx⟩ := TensorProduct.exists_sum_tmul_eq x.ofPreStinespring
  have hxφ : x = ∑ i, (ψ + θ).toPreStinespring (a i ⊗ₜ[ℂ] ξ i) :=
    PreStinespring.ext (by simpa using hx)
  have hθ : 0 ≤ (∑ i, ∑ j, ⟪ξ i, θ (star (a i) * a j) (ξ j)⟫_ℂ).re := by
    simpa [CStarMatrix.map_apply, CStarMatrix.gram_apply] using
      (Complex.nonneg_iff.mp (CStarMatrix.sum_inner_nonneg
        (θ.map_cstarMatrix_nonneg _ (CStarMatrix.gram_nonneg a)) ξ)).1
  have hdiff :
      ‖x‖ ^ 2 - ‖ψ.toPreStinespring x.ofPreStinespring‖ ^ 2 =
        (∑ i, ∑ j, ⟪ξ i, θ (star (a i) * a j) (ξ j)⟫_ℂ).re := by
    rw [(ψ + θ).preStinespring_norm_sq_re x, ψ.preStinespring_norm_sq_re, hx, hxφ]
    simp only [map_sum, sum_inner, inner_sum, preStinespring_inner_tmul, _root_.add_apply,
      inner_add_right, Complex.re_sum, Complex.add_re, Finset.sum_add_distrib, add_sub_cancel_left]
    exact Finset.sum_comm
  have hsq : ‖ψ.toPreStinespring x.ofPreStinespring‖ ^ 2 ≤ ‖x‖ ^ 2 := by linarith
  exact (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp hsq

/-- Contractive intertwining operator `φ.Stinespring →L[ℂ] ψ.Stinespring` induced by `ψ ≤ φ`. -/
private def stinespringDomMap {ψ φ : A →CP (H →L[ℂ] H)} (h : ψ ≤ φ) :
    φ.Stinespring →L[ℂ] ψ.Stinespring :=
  (LinearMap.mkContinuous
    { toFun x := ψ.toPreStinespring x.ofPreStinespring
      map_add' x y := by simp
      map_smul' c x := by simp }
    1 (norm_preStinespring_le_of_le h)).completion

@[simp]
private theorem stinespringDomMap_stinespringTmul
    {ψ φ : A →CP (H →L[ℂ] H)} (h : ψ ≤ φ) (a : A) (ξ : H) :
    stinespringDomMap h (φ.stinespringTmul a ξ) = ψ.stinespringTmul a ξ := by
  simp [stinespringDomMap, stinespringTmul_def]

private theorem norm_stinespringDomMap_apply_le
    {ψ φ : A →CP (H →L[ℂ] H)} (h : ψ ≤ φ) (w : φ.Stinespring) :
    ‖stinespringDomMap h w‖ ≤ ‖w‖ := by
  induction w using Completion.induction_on with
  | hp =>
    exact isClosed_le (continuous_norm.comp (stinespringDomMap h).continuous) continuous_norm
  | ih x =>
    simpa [stinespringDomMap] using norm_preStinespring_le_of_le h x

private theorem stinespringDomMap_intertwines
    {ψ φ : A →CP (H →L[ℂ] H)} (h : ψ ≤ φ) (a : A) (w : φ.Stinespring) :
    stinespringDomMap h (φ.stinespringNonUnitalStarAlgHom a w) =
      ψ.stinespringNonUnitalStarAlgHom a (stinespringDomMap h w) := by
  induction w using Completion.induction_on with
  | hp =>
    exact isClosed_eq
      ((stinespringDomMap h).continuous.comp (φ.stinespringNonUnitalStarAlgHom a).continuous)
      ((ψ.stinespringNonUnitalStarAlgHom a).continuous.comp (stinespringDomMap h).continuous)
  | ih x =>
    obtain ⟨t, rfl⟩ : ∃ t, φ.toPreStinespring t = x :=
      ⟨x.ofPreStinespring, φ.toPreStinespring_ofPreStinespring x⟩
    induction t using TensorProduct.inductionOn with
    | tmul b ξ =>
      rw [← stinespringTmul_def]
      simp
    | add t₁ t₂ ht₁ ht₂ =>
      simp [map_add, UniformSpace.Completion.coe_add, ht₁, ht₂]

private theorem stinespringDomMap_stinespringOp
    {ψ φ : A →CP (H →L[ℂ] H)} (h : ψ ≤ φ) (ξ : H) :
    stinespringDomMap h (φ.stinespringOp ξ) = ψ.stinespringOp ξ := by
  have hl := CStarAlgebra.increasingApproximateUnit A
  have := hl.neBot
  have h₁ :
      Tendsto (fun e : A => stinespringDomMap h (φ.stinespringTmul e ξ))
        (CStarAlgebra.approximateUnit A) (𝓝 (stinespringDomMap h (φ.stinespringOp ξ))) :=
    (stinespringDomMap h).continuous.continuousAt.tendsto.comp
      (φ.tendsto_stinespringTmul_approximateUnit ξ)
  exact tendsto_nhds_unique (by simpa using h₁) (ψ.tendsto_stinespringTmul_approximateUnit ξ)

/-- **Arveson's Radon–Nikodym theorem** (nonunital form): for any minimal Stinespring dilation
`(K, π, V)` of `φ : A →CP (H →L[ℂ] H)` and any completely positive map `ψ ≤ φ`, there is a unique
operator `T : K →L[ℂ] K` with `0 ≤ T ≤ 1` in the commutant of `π(A)` such that
`ψ a = V† ∘L T ∘L π a ∘L V` for all `a : A`. -/
theorem existsUnique_commutant_of_le
    (φ : A →CP (H →L[ℂ] H)) {ψ : A →CP (H →L[ℂ] H)}
    (π : A →⋆ₙₐ[ℂ] (K →L[ℂ] K)) (V : H →L[ℂ] K)
    (hφ : ∀ a, φ a = V.adjoint.comp ((π a).comp V))
    (hmin : (Submodule.span ℂ {x : K | ∃ (a : A) (ξ : H), x = π a (V ξ)}).topologicalClosure = ⊤)
    (hle : ψ ≤ φ) :
    ∃! T : K →L[ℂ] K,
      0 ≤ T ∧ T ≤ 1 ∧ (∀ a, Commute T (π a)) ∧
      ∀ a, ψ a = V.adjoint.comp (T.comp ((π a).comp V)) := by
  let U : φ.Stinespring ≃ₗᵢ[ℂ] K := φ.stinespringEquiv π V hφ hmin
  let W : K →L[ℂ] ψ.Stinespring :=
    (stinespringDomMap hle).comp U.symm.toLinearIsometry.toContinuousLinearMap
  have hW_norm (y : K) : ‖W y‖ ≤ ‖y‖ := by
    simpa [W] using
      (norm_stinespringDomMap_apply_le hle (U.symm y)).trans_eq (U.symm.norm_map y)
  have hW_inter (a : A) : W.comp (π a) = (ψ.stinespringNonUnitalStarAlgHom a).comp W := by
    ext y
    simpa [W, U] using stinespringDomMap_intertwines hle a (U.symm y)
  have hWV : W.comp V = ψ.stinespringOp := by
    ext ξ
    simpa [W, U] using stinespringDomMap_stinespringOp hle ξ
  let T : K →L[ℂ] K := W.adjoint.comp W
  have hT_comm (a : A) : Commute T (π a) := by
    have hadj : (π a).comp W.adjoint = W.adjoint.comp (ψ.stinespringNonUnitalStarAlgHom a) := by
      have hstar := congrArg ContinuousLinearMap.adjoint (hW_inter (star a))
      simpa [ContinuousLinearMap.adjoint_comp, ← ContinuousLinearMap.star_eq_adjoint,
        ← map_star] using hstar
    rw [commute_iff_eq]
    ext y
    have h1 := congr($(hW_inter a) y)
    have h2 := congr($hadj (W y))
    simpa [T, ContinuousLinearMap.mul_def] using (congrArg W.adjoint h1).trans h2.symm
  have hT_dil (a : A) : ψ a = V.adjoint.comp (T.comp ((π a).comp V)) := by
    have hstep :
        V.adjoint.comp (T.comp ((π a).comp V)) =
          (W.comp V).adjoint.comp ((ψ.stinespringNonUnitalStarAlgHom a).comp (W.comp V)) := by
      ext ξ
      simpa [T, ContinuousLinearMap.adjoint_comp] using
        congrArg (V.adjoint.comp W.adjoint) congr($(hW_inter a) (V ξ))
    rw [hstep, hWV, ψ.stinespringOp_adjoint_comp_stinespringNonUnitalStarAlgHom_comp a]
  refine ⟨T, ⟨ContinuousLinearMap.nonneg_iff_isPositive.mpr W.isPositive_adjoint_comp_self,
    W.norm_map_le_norm_iff_le.mp hW_norm, hT_comm, hT_dil⟩, ?_⟩
  rintro T' ⟨_, _, hT'_comm, hT'_dil⟩
  exact π.eq_of_forall_adjoint_comp_eq V hmin hT'_comm hT_comm fun a =>
    (hT'_dil a).symm.trans (hT_dil a)

/-- **Arveson's Radon–Nikodym order isomorphism**: for any minimal dilation `(K, π, V)` of `φ`,
compression `T ↦ (a ↦ V† ∘L T ∘L π a ∘L V)` is an order isomorphism from the unit interval
`[0, 1]` of the commutant `π(A)'` onto the order interval `[0, φ]` in `A →CP (H →L[ℂ] H)`. -/
def radonNikodymOrderIso
    (φ : A →CP (H →L[ℂ] H)) (π : A →⋆ₙₐ[ℂ] (K →L[ℂ] K)) (V : H →L[ℂ] K)
    (hφ : ∀ a, φ a = V.adjoint.comp ((π a).comp V))
    (hmin : (Submodule.span ℂ {x : K | ∃ (a : A) (ξ : H), x = π a (V ξ)}).topologicalClosure = ⊤) :
    {T : K →L[ℂ] K // 0 ≤ T ∧ T ≤ 1 ∧ ∀ a, Commute T (π a)} ≃o
      Set.Icc (0 : A →CP (H →L[ℂ] H)) φ where
  toFun T :=
    ⟨compressCommutant π V T.1 T.2.1 T.2.2.2, bot_le,
      compressCommutant_le_of_le_one π V hφ T.2.1 T.2.2.1 T.2.2.2⟩
  invFun ψ :=
    let h := φ.existsUnique_commutant_of_le π V hφ hmin ψ.2.2
    ⟨h.choose, h.choose_spec.1.1, h.choose_spec.1.2.1, h.choose_spec.1.2.2.1⟩
  left_inv T := by
    ext : 1
    let h := φ.existsUnique_commutant_of_le π V hφ hmin
      (compressCommutant_le_of_le_one π V hφ T.2.1 T.2.2.1 T.2.2.2)
    exact (h.unique ⟨T.2.1, T.2.2.1, T.2.2.2, fun _ => rfl⟩ h.choose_spec.1).symm
  right_inv ψ := by
    ext a : 2
    exact ((φ.existsUnique_commutant_of_le π V hφ hmin ψ.2.2).choose_spec.1.2.2.2 a).symm
  map_rel_iff' {T₁ T₂} := by
    constructor
    · intro hle
      obtain ⟨θ, hθ⟩ := le_iff_exists_add.mp (Subtype.mk_le_mk.mp hle)
      have hθ_le : θ ≤ φ :=
        (le_iff_exists_add.mpr ⟨compressCommutant π V T₁.1 T₁.2.1 T₁.2.2.2,
          by rw [add_comm]; exact hθ⟩).trans
          (compressCommutant_le_of_le_one π V hφ T₂.2.1 T₂.2.2.1 T₂.2.2.2)
      obtain ⟨D, ⟨hD0, _, hDcomm, hDdil⟩, -⟩ :=
        φ.existsUnique_commutant_of_le π V hφ hmin hθ_le
      have hsum : T₁.1 + D = T₂.1 :=
        π.eq_of_forall_adjoint_comp_eq V hmin
          (fun a => (T₁.2.2.2 a).add_left (hDcomm a)) T₂.2.2.2 fun a => by
            have ha := congrArg (fun f : A →CP (H →L[ℂ] H) => f a) hθ.symm
            simpa [hDdil a] using ha
      exact Subtype.mk_le_mk.mpr (hsum ▸ le_add_of_nonneg_right hD0)
    · intro hle
      exact Subtype.mk_le_mk.mpr (compressCommutant_mono π V T₁.2.1 T₁.2.2.2 T₂.2.2.2 hle)

@[simp]
theorem coe_radonNikodymOrderIso_apply
    (φ : A →CP (H →L[ℂ] H)) (π : A →⋆ₙₐ[ℂ] (K →L[ℂ] K)) (V : H →L[ℂ] K)
    (hφ : ∀ a, φ a = V.adjoint.comp ((π a).comp V))
    (hmin : (Submodule.span ℂ {x : K | ∃ (a : A) (ξ : H), x = π a (V ξ)}).topologicalClosure = ⊤)
    (T : {T : K →L[ℂ] K // 0 ≤ T ∧ T ≤ 1 ∧ ∀ a, Commute T (π a)}) (a : A) :
    (φ.radonNikodymOrderIso π V hφ hmin T : A →CP (H →L[ℂ] H)) a =
      V.adjoint.comp (T.1.comp ((π a).comp V)) :=
  (rfl)

end NonUnital

section Unital

variable {D : Type u} {H : Type v} {K : Type w}
  [CStarAlgebra D] [PartialOrder D] [StarOrderedRing D]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

/-- **Arveson's Radon–Nikodym theorem** (unital `ψ ≤ φ` form). -/
theorem existsUnique_commutant_of_le_unital
    (φ : D →CP (H →L[ℂ] H)) {ψ : D →CP (H →L[ℂ] H)}
    (π : D →⋆ₐ[ℂ] (K →L[ℂ] K)) (V : H →L[ℂ] K)
    (hφ : ∀ a, φ a = V.adjoint.comp ((π a).comp V))
    (hmin : (Submodule.span ℂ {x : K | ∃ (a : D) (ξ : H), x = π a (V ξ)}).topologicalClosure = ⊤)
    (hle : ψ ≤ φ) :
    ∃! T : K →L[ℂ] K,
      0 ≤ T ∧ T ≤ 1 ∧ (∀ a, Commute T (π a)) ∧
      ∀ a, ψ a = V.adjoint.comp (T.comp ((π a).comp V)) :=
  φ.existsUnique_commutant_of_le π.toNonUnitalStarAlgHom V hφ hmin hle

/-- **Arveson's Radon–Nikodym theorem** (unital existential-complement form): if `φ` decomposes as
`ψ + θ` for a completely positive map `θ`, then `ψ` corresponds to a unique operator `0 ≤ T ≤ 1` in
the commutant of any minimal Stinespring representation `(K, π, V)` of `φ`. -/
theorem radonNikodym
    (φ ψ : D →CP (H →L[ℂ] H)) (π : D →⋆ₐ[ℂ] (K →L[ℂ] K)) (V : H →L[ℂ] K)
    (hφ : ∀ a, φ a = V.adjoint.comp ((π a).comp V))
    (hmin : (Submodule.span ℂ {x : K | ∃ (a : D) (ξ : H), x = π a (V ξ)}).topologicalClosure = ⊤)
    (hle : ∃ θ : D →CP (H →L[ℂ] H), ∀ a, φ a = ψ a + θ a) :
    ∃! T : K →L[ℂ] K,
      0 ≤ T ∧ T ≤ 1 ∧ (∀ a, Commute T (π a)) ∧
      ∀ a, ψ a = V.adjoint.comp (T.comp ((π a).comp V)) := by
  rcases hle with ⟨θ, hθ⟩
  exact φ.existsUnique_commutant_of_le_unital π V hφ hmin
    (le_iff_exists_add.mpr ⟨θ, ext hθ⟩)

end Unital

end CompletelyPositiveMap
