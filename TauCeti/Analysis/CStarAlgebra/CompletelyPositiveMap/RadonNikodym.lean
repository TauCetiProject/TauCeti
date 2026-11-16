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
  have hcl {f g : K →L[ℂ] ℂ} (hfg : ∀ a ξ, f (π a (V ξ)) = g (π a (V ξ))) : f = g := by
    have htop :
        (Submodule.span ℂ {x : K | ∃ (a : A) (ξ : H), x = π a (V ξ)}).topologicalClosure ≤
          (f - g).ker :=
      Submodule.topologicalClosure_minimal _
        (Submodule.span_le.mpr (by rintro _ ⟨a, ξ, rfl⟩; exact sub_eq_zero.mpr (hfg a ξ)))
        (isClosed_singleton.preimage (f - g).continuous)
    rw [hmin] at htop
    ext x
    exact sub_eq_zero.mp (htop trivial)
  have hinner {T : K →L[ℂ] K} (hcomm : ∀ a, Commute T (π a)) (a b : A) (ξ η : H) :
      ⟪π a (V ξ), T (π b (V η))⟫_ℂ =
        ⟪ξ, (V.adjoint.comp (T.comp ((π (star a * b)).comp V))) η⟫_ℂ := by
    have hstar : π (star a) (T (π b (V η))) = T (π (star a * b) (V η)) := by
      simpa [ContinuousLinearMap.mul_def, map_mul] using
        congr($((hcomm (star a)).eq) (π b (V η))).symm
    rw [← ContinuousLinearMap.adjoint_inner_right, ← ContinuousLinearMap.star_eq_adjoint,
      ← map_star, hstar]
    simp [ContinuousLinearMap.adjoint_inner_right]
  have hright (a : A) (ξ : H) (v : K) : ⟪π a (V ξ), T₁ v⟫_ℂ = ⟪π a (V ξ), T₂ v⟫_ℂ :=
    congr($(hcl (f := (innerSL ℂ (π a (V ξ))).comp T₁) (g := (innerSL ℂ (π a (V ξ))).comp T₂)
      fun b η => by
        simp only [ContinuousLinearMap.comp_apply, innerSL_apply_apply,
          hinner hcomm₁, hinner hcomm₂, heq]) v)
  ext v
  refine ext_inner_right ℂ fun u => congr($(hcl (f := innerSL ℂ (T₁ v)) (g := innerSL ℂ (T₂ v))
    fun a ξ => by
      simp only [innerSL_apply_apply]
      rw [← inner_conj_symm, hright a ξ v, inner_conj_symm]) u)

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
    (hT : 0 ≤ T) (hcomm : ∀ a, Commute T (π a)) : A →CP (H →L[ℂ] H) where
  toLinearMap :=
    { toFun a := V.adjoint.comp (T.comp ((π a).comp V))
      map_add' _ _ := by ext ξ; simp
      map_smul' _ _ := by ext ξ; simp }
  map_cstarMatrix_nonneg' _ M hM := by
    let ψ : A →CP (H →L[ℂ] H) :=
      (conjCLM (CFC.sqrt T ∘L V)).comp (π : A →CP (K →L[ℂ] K))
    have hsqrt_adj : (CFC.sqrt T).adjoint = CFC.sqrt T :=
      ContinuousLinearMap.star_eq_adjoint (CFC.sqrt T) ▸
        (IsSelfAdjoint.of_nonneg (CFC.sqrt_nonneg T)).star_eq
    have hEq : M.map
        ({ toFun a := V.adjoint.comp (T.comp ((π a).comp V))
           map_add' _ _ := by ext ξ; simp
           map_smul' _ _ := by ext ξ; simp } : A →ₗ[ℂ] (H →L[ℂ] H)) = M.map ψ := by
      ext i j ξ
      have hsqrt_comm : Commute (CFC.sqrt T) (π (M i j)) := by
        rw [CFC.sqrt_eq_nnrpow, CFC.nnrpow_def]
        exact (hcomm (M i j)).cfcₙ_nnreal _
      have hmid : (CFC.sqrt T).adjoint * (π (M i j) * CFC.sqrt T) = T * π (M i j) := by
        rw [hsqrt_adj, ← hsqrt_comm.eq, ← mul_assoc, CFC.sqrt_mul_sqrt_self T hT]
      simpa [ψ, CStarMatrix.map_apply, ContinuousLinearMap.adjoint_comp,
        ContinuousLinearMap.mul_def] using (congrArg V.adjoint congr($hmid (V ξ))).symm
    exact hEq ▸ ψ.map_cstarMatrix_nonneg M hM

@[simp] theorem compressCommutant_apply
    (π : A →⋆ₙₐ[ℂ] (K →L[ℂ] K)) (V : H →L[ℂ] K) (T : K →L[ℂ] K)
    (hT : 0 ≤ T) (hcomm : ∀ a, Commute T (π a)) (a : A) :
    compressCommutant π V T hT hcomm a = V.adjoint.comp (T.comp ((π a).comp V)) := (rfl)

/-- `compressCommutant` is additive in the positive commuting operator `T`. -/
theorem compressCommutant_add
    (π : A →⋆ₙₐ[ℂ] (K →L[ℂ] K)) (V : H →L[ℂ] K) {T₁ T₂ : K →L[ℂ] K}
    (hT₁ : 0 ≤ T₁) (hT₂ : 0 ≤ T₂)
    (hcomm₁ : ∀ a, Commute T₁ (π a)) (hcomm₂ : ∀ a, Commute T₂ (π a)) :
    compressCommutant π V (T₁ + T₂) (add_nonneg hT₁ hT₂) (fun a => (hcomm₁ a).add_left (hcomm₂ a)) =
      compressCommutant π V T₁ hT₁ hcomm₁ + compressCommutant π V T₂ hT₂ hcomm₂ := by
  ext a ξ; simp

/-- `compressCommutant` is monotone in `T` with respect to the completely positive order. -/
theorem compressCommutant_mono
    (π : A →⋆ₙₐ[ℂ] (K →L[ℂ] K)) (V : H →L[ℂ] K) {T₁ T₂ : K →L[ℂ] K}
    (hT₁ : 0 ≤ T₁) (hcomm₁ : ∀ a, Commute T₁ (π a)) (hcomm₂ : ∀ a, Commute T₂ (π a))
    (h12 : T₁ ≤ T₂) :
    compressCommutant π V T₁ hT₁ hcomm₁ ≤
      compressCommutant π V T₂ (hT₁.trans h12) hcomm₂ :=
  le_iff_exists_add.mpr ⟨compressCommutant π V (T₂ - T₁) (sub_nonneg.mpr h12)
    (fun a => (hcomm₂ a).sub_left (hcomm₁ a)), by ext a ξ; simp⟩

private theorem compressCommutant_le_of_le_one
    {φ : A →CP (H →L[ℂ] H)} (π : A →⋆ₙₐ[ℂ] (K →L[ℂ] K)) (V : H →L[ℂ] K)
    (hφ : ∀ a, φ a = V.adjoint.comp ((π a).comp V))
    {T : K →L[ℂ] K} (hT0 : 0 ≤ T) (hT1 : T ≤ 1) (hcomm : ∀ a, Commute T (π a)) :
    compressCommutant π V T hT0 hcomm ≤ φ := by
  have h1 : compressCommutant π V 1 zero_le_one (fun _ => Commute.one_left _) = φ := by
    ext a ξ; simp [hφ a]
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
  have hdiff : ‖x‖ ^ 2 - ‖ψ.toPreStinespring x.ofPreStinespring‖ ^ 2 =
      (∑ i, ∑ j, ⟪ξ i, θ (star (a i) * a j) (ξ j)⟫_ℂ).re := by
    rw [(ψ + θ).preStinespring_norm_sq_re x, ψ.preStinespring_norm_sq_re, hx, hxφ]
    simp only [map_sum, sum_inner, inner_sum, preStinespring_inner_tmul, _root_.add_apply,
      inner_add_right, Complex.re_sum, Complex.add_re, Finset.sum_add_distrib, add_sub_cancel_left]
    exact Finset.sum_comm
  exact (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp (by linarith)

/-- Contractive intertwining operator `φ.Stinespring →L[ℂ] ψ.Stinespring` induced by `ψ ≤ φ`. -/
private def stinespringDomMap {ψ φ : A →CP (H →L[ℂ] H)} (h : ψ ≤ φ) :
    φ.Stinespring →L[ℂ] ψ.Stinespring :=
  (LinearMap.mkContinuous
    { toFun x := ψ.toPreStinespring x.ofPreStinespring
      map_add' _ _ := by simp
      map_smul' _ _ := by simp }
    1 (norm_preStinespring_le_of_le h)).completion

@[simp] private theorem stinespringDomMap_stinespringTmul
    {ψ φ : A →CP (H →L[ℂ] H)} (h : ψ ≤ φ) (a : A) (ξ : H) :
    stinespringDomMap h (φ.stinespringTmul a ξ) = ψ.stinespringTmul a ξ := by
  simp [stinespringDomMap, stinespringTmul_def]

private theorem norm_stinespringDomMap_apply_le
    {ψ φ : A →CP (H →L[ℂ] H)} (h : ψ ≤ φ) (w : φ.Stinespring) :
    ‖stinespringDomMap h w‖ ≤ ‖w‖ := by
  induction w using Completion.induction_on with
  | hp => exact isClosed_le (continuous_norm.comp (stinespringDomMap h).continuous) continuous_norm
  | ih x => simpa [stinespringDomMap] using norm_preStinespring_le_of_le h x

private theorem stinespringDomMap_intertwines
    {ψ φ : A →CP (H →L[ℂ] H)} (h : ψ ≤ φ) (a : A) (w : φ.Stinespring) :
    stinespringDomMap h (φ.stinespringNonUnitalStarAlgHom a w) =
      ψ.stinespringNonUnitalStarAlgHom a (stinespringDomMap h w) :=
  congr($(φ.ext_stinespring
    (f := (stinespringDomMap h).comp (φ.stinespringNonUnitalStarAlgHom a))
    (g := (ψ.stinespringNonUnitalStarAlgHom a).comp (stinespringDomMap h))
    fun b ξ => by simp) w)

private theorem stinespringDomMap_stinespringOp
    {ψ φ : A →CP (H →L[ℂ] H)} (h : ψ ≤ φ) (ξ : H) :
    stinespringDomMap h (φ.stinespringOp ξ) = ψ.stinespringOp ξ := by
  have := (CStarAlgebra.increasingApproximateUnit A).neBot
  have h₁ := (stinespringDomMap h).continuous.continuousAt.tendsto.comp
    (φ.tendsto_stinespringTmul_approximateUnit ξ)
  exact tendsto_nhds_unique (by simpa [Function.comp_def] using h₁)
    (ψ.tendsto_stinespringTmul_approximateUnit ξ)

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
  let U := φ.stinespringEquiv π V hφ hmin
  let W : K →L[ℂ] ψ.Stinespring :=
    (stinespringDomMap hle).comp U.symm.toLinearIsometry.toContinuousLinearMap
  have hW_norm (y : K) : ‖W y‖ ≤ ‖y‖ := by
    simpa [W] using
      (norm_stinespringDomMap_apply_le hle (U.symm y)).trans_eq (U.symm.norm_map y)
  have hW_inter (a : A) : W.comp (π a) = (ψ.stinespringNonUnitalStarAlgHom a).comp W := by
    ext y; simpa [W, U] using stinespringDomMap_intertwines hle a (U.symm y)
  have hWV : W.comp V = ψ.stinespringOp := by
    ext ξ; simpa [W, U] using stinespringDomMap_stinespringOp hle ξ
  let T : K →L[ℂ] K := W.adjoint.comp W
  have hT_comm (a : A) : Commute T (π a) := by
    have hadj : (π a).comp W.adjoint = W.adjoint.comp (ψ.stinespringNonUnitalStarAlgHom a) := by
      simpa [ContinuousLinearMap.adjoint_comp, ← ContinuousLinearMap.star_eq_adjoint, ← map_star]
        using congrArg ContinuousLinearMap.adjoint (hW_inter (star a))
    rw [commute_iff_eq]
    ext y
    simpa [T, ContinuousLinearMap.mul_def] using
      (congrArg W.adjoint congr($(hW_inter a) y)).trans (congr($hadj (W y))).symm
  have hT_dil (a : A) : ψ a = V.adjoint.comp (T.comp ((π a).comp V)) := by
    have hstep : V.adjoint.comp (T.comp ((π a).comp V)) =
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
  toFun T := ⟨compressCommutant π V T.1 T.2.1 T.2.2.2, bot_le,
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
    refine ⟨fun hle => ?_, fun hle =>
      Subtype.mk_le_mk.mpr (compressCommutant_mono π V T₁.2.1 T₁.2.2.2 T₂.2.2.2 hle)⟩
    obtain ⟨θ, hθ⟩ := le_iff_exists_add.mp (Subtype.mk_le_mk.mp hle)
    have hθ_le : θ ≤ φ := (le_iff_exists_add.mpr ⟨compressCommutant π V T₁.1 T₁.2.1 T₁.2.2.2,
      by rw [add_comm]; exact hθ⟩).trans
      (compressCommutant_le_of_le_one π V hφ T₂.2.1 T₂.2.2.1 T₂.2.2.2)
    obtain ⟨D, ⟨hD0, _, hDcomm, hDdil⟩, -⟩ := φ.existsUnique_commutant_of_le π V hφ hmin hθ_le
    have hsum : T₁.1 + D = T₂.1 := π.eq_of_forall_adjoint_comp_eq V hmin
      (fun a => (T₁.2.2.2 a).add_left (hDcomm a)) T₂.2.2.2 fun a => by
        simpa [hDdil a] using congrArg (fun f : A →CP (H →L[ℂ] H) => f a) hθ.symm
    exact Subtype.mk_le_mk.mpr (hsum ▸ le_add_of_nonneg_right hD0)

@[simp] theorem coe_radonNikodymOrderIso_apply
    (φ : A →CP (H →L[ℂ] H)) (π : A →⋆ₙₐ[ℂ] (K →L[ℂ] K)) (V : H →L[ℂ] K)
    (hφ : ∀ a, φ a = V.adjoint.comp ((π a).comp V))
    (hmin : (Submodule.span ℂ {x : K | ∃ (a : A) (ξ : H), x = π a (V ξ)}).topologicalClosure = ⊤)
    (T : {T : K →L[ℂ] K // 0 ≤ T ∧ T ≤ 1 ∧ ∀ a, Commute T (π a)}) (a : A) :
    (φ.radonNikodymOrderIso π V hφ hmin T : A →CP (H →L[ℂ] H)) a =
      V.adjoint.comp (T.1.comp ((π a).comp V)) := (rfl)

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
  exact φ.existsUnique_commutant_of_le_unital π V hφ hmin (le_iff_exists_add.mpr ⟨θ, ext hθ⟩)

end Unital

end CompletelyPositiveMap
