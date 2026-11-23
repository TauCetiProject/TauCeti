/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.Positive
public import TauCeti.Analysis.InnerProductSpace.LinearPMap.Friedrichs
public import TauCeti.Analysis.InnerProductSpace.LinearPMap.Resolvent

/-!
# Extremality of the Friedrichs extension

Let `S` be a densely defined symmetric partial operator on a Hilbert space `E` over `𝕜`
(`[RCLike 𝕜]`) with lower bound `γ`. Among the self-adjoint extensions `T` of `S` with the same
lower bound, the Friedrichs extension `S_F` is the largest in form order (Krein's theorem). This
file proves it in resolvent order: for every real `t < γ`,
`T.resolvent t ≤ S_F.resolvent t` in the Loewner order, for Tau Ceti's resolvent
`R(t) = (t I - ·)⁻¹`. Equivalently `(S_F - t)⁻¹ ≤ (T - t)⁻¹`.

The proof is variational and needs no separability. Put `g = -h` for `h : E`, and let `y_T` and
`y_F` solve `(T - t) y = g` and `(S_F - t) y = g`, so that `⟪h, R(t) h⟫ = -⟪g, y⟫`.

* For `u` in the domain of `T`, positivity of `T - t` at `y_T - u` gives
  `2 re ⟪g, u⟫ - re ⟪(T - t) u, u⟫ ≤ re ⟪g, y_T⟫`
  (`LinearPMap.IsFormalAdjoint.two_mul_re_inner_sub_le`). Since `S ≤ T`, this holds for `u` in
  the domain of `S`, where `T u = S u`.
* `y_F` is the image of a vector `w` of the form completion of `S`, and the left side, written
  through the closed form of `S_F` and the inclusion of the form completion, is a continuous
  function of the form-completion vector. The domain of `S` is dense there, so the inequality
  holds at `w`, where its left side is `re ⟪g, y_F⟫`.

Hence `re ⟪g, y_F⟫ ≤ re ⟪g, y_T⟫`, which is the resolvent inequality.

## Main results

* `IsSelfAdjoint.ofReal_mem_resolventSet_of_lt`: a real number below a lower bound of a
  self-adjoint operator is a resolvent point.
* `LinearPMap.resolvent_le_resolvent_friedrichsExtension`: Krein's extremal property of the
  Friedrichs extension in resolvent order.
* `LinearPMap.exists_isSelfAdjoint_extension_forall_resolvent_le`: existence of a self-adjoint
  extension with the same lower bound that is extremal in resolvent order.

## References

* J. Eckhardt, F. Gesztesy, R. Nichols and G. Teschl, *Weyl–Titchmarsh theory for Sturm–Liouville
  operators with distributional potentials*, arXiv:1208.4677v3, Theorem 12.1 and (12.8).
* T. Kato, *Perturbation Theory for Linear Operators*, Springer (1995), Chapter VI, §2.3.
-/

public section

open scoped InnerProductSpace

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]

/-- **A real number below a lower bound is a resolvent point.** If a self-adjoint operator `T`
satisfies `γ ‖x‖ ^ 2 ≤ re ⟪T x, x⟫` on its domain and `t < γ`, then `t` lies in the resolvent set
of `T`. -/
theorem IsSelfAdjoint.ofReal_mem_resolventSet_of_lt [CompleteSpace E] {T : E →ₗ.[𝕜] E}
    (hT : IsSelfAdjoint T) {γ t : ℝ}
    (hγ : ∀ x : T.domain, γ * ‖(x : E)‖ ^ 2 ≤ RCLike.re ⟪T x, (x : E)⟫_𝕜) (ht : t < γ) :
    (t : 𝕜) ∈ T.resolventSet := by
  refine hT.mem_resolventSet_of_norm_le (sub_pos.2 ht) fun x => ?_
  have hre : RCLike.re ⟪T x - (t : 𝕜) • (x : E), (x : E)⟫_𝕜 =
      RCLike.re ⟪T x, (x : E)⟫_𝕜 - t * ‖(x : E)‖ ^ 2 := by
    rw [inner_sub_left, inner_smul_left, RCLike.conj_ofReal, map_sub, RCLike.re_ofReal_mul,
      inner_self_eq_norm_sq (𝕜 := 𝕜)]
  have hle := re_inner_le_norm (𝕜 := 𝕜) (T x - (t : 𝕜) • (x : E)) (x : E)
  rw [hre, norm_sub_rev] at hle
  have key : (γ - t) * ‖(x : E)‖ * ‖(x : E)‖ ≤ ‖(t : 𝕜) • (x : E) - T x‖ * ‖(x : E)‖ := by
    nlinarith [hγ x]
  rcases (norm_nonneg (x : E)).eq_or_lt with h0 | hpos
  · rw [← h0, mul_zero]
    exact norm_nonneg _
  · exact le_of_mul_le_mul_right key hpos

namespace LinearPMap

/-- **The variational inequality of a semibounded symmetric operator.** If `T` is symmetric with
`t ‖x‖ ^ 2 ≤ re ⟪T x, x⟫` on its domain, then for `y, u` in the domain,
`2 re ⟪(T - t) y, u⟫ - re ⟪(T - t) u, u⟫ ≤ re ⟪(T - t) y, y⟫`: the quadratic form of `T - t` is
nonnegative at `y - u`. -/
theorem IsFormalAdjoint.two_mul_re_inner_sub_le {T : E →ₗ.[𝕜] E} (hT : T.IsFormalAdjoint T)
    {t : ℝ} (ht : ∀ x : T.domain, t * ‖(x : E)‖ ^ 2 ≤ RCLike.re ⟪T x, (x : E)⟫_𝕜)
    (y u : T.domain) :
    2 * RCLike.re ⟪T y - (t : 𝕜) • (y : E), (u : E)⟫_𝕜 -
        RCLike.re ⟪T u - (t : 𝕜) • (u : E), (u : E)⟫_𝕜 ≤
      RCLike.re ⟪T y - (t : 𝕜) • (y : E), (y : E)⟫_𝕜 := by
  have hz := ht (y - u)
  have hsym : RCLike.re ⟪T u, (y : E)⟫_𝕜 = RCLike.re ⟪T y, (u : E)⟫_𝕜 := by
    rw [hT u y, ← inner_conj_symm, RCLike.conj_re]
  have hyu : RCLike.re ⟪(u : E), (y : E)⟫_𝕜 = RCLike.re ⟪(y : E), (u : E)⟫_𝕜 := by
    rw [← inner_conj_symm, RCLike.conj_re]
  rw [LinearPMap.map_sub, Submodule.coe_sub, @norm_sub_sq 𝕜] at hz
  simp only [inner_sub_left, inner_sub_right, inner_smul_left, RCLike.conj_ofReal, _root_.map_sub,
    RCLike.re_ofReal_mul, inner_self_eq_norm_sq (𝕜 := 𝕜)] at hz ⊢
  linarith

variable [CompleteSpace E] {S : E →ₗ.[𝕜] E} {γ : ℝ}

/-- **Krein's extremal property of the Friedrichs extension**, in resolvent order. Let `S` be
densely defined and symmetric with lower bound `γ`, and `T` a self-adjoint extension of `S` with
the same lower bound. For every real `t < γ`, `T.resolvent t ≤ S_F.resolvent t` in the Loewner
order, where `R(t) = (t I - ·)⁻¹`; equivalently `(S_F - t)⁻¹ ≤ (T - t)⁻¹`. -/
theorem resolvent_le_resolvent_friedrichsExtension (hS : S.IsSymmetricBoundedBelow γ)
    (hdense : Dense (S.domain : Set E)) {T : E →ₗ.[𝕜] E} (hT : IsSelfAdjoint T) (hST : S ≤ T)
    (hTγ : ∀ x : T.domain, γ * ‖(x : E)‖ ^ 2 ≤ RCLike.re ⟪T x, (x : E)⟫_𝕜) {t : ℝ}
    (ht : t < γ) :
    T.resolvent (t : 𝕜) ≤ (friedrichsExtension hS hdense).resolvent (t : 𝕜) := by
  set F := friedrichsExtension hS hdense
  have hF : IsSelfAdjoint F := isSelfAdjoint_friedrichsExtension hS hdense
  have hTt := hT.ofReal_mem_resolventSet_of_lt hTγ ht
  have hFt := hF.ofReal_mem_resolventSet_of_lt
    (mul_norm_sq_le_re_inner_friedrichsExtension hS hdense) ht
  rw [ContinuousLinearMap.le_def, ContinuousLinearMap.isPositive_def']
  refine ⟨(hF.isSelfAdjoint_resolvent hFt (RCLike.ofReal_im t)).sub
    (hT.isSelfAdjoint_resolvent hTt (RCLike.ofReal_im t)), fun h => ?_⟩
  rw [ContinuousLinearMap.reApplyInnerSelf_apply, _root_.sub_apply, inner_sub_left,
    _root_.map_sub, sub_nonneg]
  -- The solutions `y_T`, `y_F` of `(T - t) y = -h` and `(S_F - t) y = -h`.
  set yT : T.domain := ⟨T.resolvent t h, resolvent_mem_domain hTt h⟩
  set yF : F.domain := ⟨F.resolvent t h, resolvent_mem_domain hFt h⟩
  have hyT : T yT - (t : 𝕜) • (yT : E) = -h := by
    rw [apply_resolvent hTt]
    abel
  have hyF : F yF - (t : 𝕜) • (yF : E) = -h := by
    rw [apply_resolvent hFt]
    abel
  -- The variational inequality for `T`, at vectors of the domain of `S`.
  have hTu (u : S.domain) :
      2 * RCLike.re ⟪-h, (u : E)⟫_𝕜 - RCLike.re ⟪S u - (t : 𝕜) • (u : E), (u : E)⟫_𝕜 ≤
        RCLike.re ⟪-h, (yT : E)⟫_𝕜 := by
    have hu := hT.isFormalAdjoint.two_mul_re_inner_sub_le
      (fun x => (mul_le_mul_of_nonneg_right ht.le (sq_nonneg _)).trans (hTγ x)) yT
      ⟨u, hST.1 u.property⟩
    rwa [hyT, ← hST.2 (x := u) rfl] at hu
  -- `y_F` is the image of a vector `w` of the form completion.
  obtain ⟨w, hw, -⟩ := (mem_domain_friedrichsExtension_iff hS hdense).mp yF.property
  set j := friedrichsInclusion hS
  have hg (v : FriedrichsSpace S γ hS) :
      ⟪-h, j v⟫_𝕜 = friedrichsForm hS w v - (t : 𝕜) * ⟪j w, j v⟫_𝕜 := by
    rw [← hyF, inner_sub_left, inner_smul_left, RCLike.conj_ofReal,
      inner_friedrichsExtension hS hdense hw, hw]
  -- The inequality extends from the domain of `S` to its form completion by density.
  have hclosed : _root_.IsClosed {z : FriedrichsSpace S γ hS | 2 * RCLike.re ⟪-h, j z⟫_𝕜 -
      RCLike.re (friedrichsForm hS z z - (t : 𝕜) * ⟪j z, j z⟫_𝕜) ≤
        RCLike.re ⟪-h, (yT : E)⟫_𝕜} :=
    isClosed_le (by fun_prop) continuous_const
  have hw' : 2 * RCLike.re ⟪-h, j w⟫_𝕜 -
      RCLike.re (friedrichsForm hS w w - (t : 𝕜) * ⟪j w, j w⟫_𝕜) ≤
        RCLike.re ⟪-h, (yT : E)⟫_𝕜 :=
    (denseRange_toFriedrichsSpace hS).induction_on w hclosed fun u => by
      simpa only [Set.mem_ofPred_eq, friedrichsForm_toFriedrichsSpace_left, j,
        friedrichsInclusion_toFriedrichsSpace, inner_sub_left, inner_smul_left,
        RCLike.conj_ofReal] using hTu u
  rw [← hg, hw] at hw'
  have hT' : RCLike.re ⟪T.resolvent t h, h⟫_𝕜 = -RCLike.re ⟪-h, (yT : E)⟫_𝕜 := by
    rw [inner_neg_left, _root_.map_neg, neg_neg, ← inner_conj_symm, RCLike.conj_re]
  have hF' : RCLike.re ⟪F.resolvent t h, h⟫_𝕜 = -RCLike.re ⟪-h, (yF : E)⟫_𝕜 := by
    rw [inner_neg_left, _root_.map_neg, neg_neg, ← inner_conj_symm, RCLike.conj_re]
  rw [hT', hF']
  linarith

/-- **The Friedrichs extension is extremal** (UO-D06 `friedrichs_extension_extremal`). A densely
defined symmetric partial operator `S` with lower bound `γ` has a self-adjoint extension `S_F`
with the same lower bound such that every self-adjoint extension `T` of `S` with lower bound `γ`
satisfies `T.resolvent t ≤ S_F.resolvent t` for every real `t < γ`. -/
theorem exists_isSelfAdjoint_extension_forall_resolvent_le (S : E →ₗ.[𝕜] E)
    (hdense : Dense (S.domain : Set E)) (hsym : S.IsFormalAdjoint S) (γ : ℝ)
    (hγ : ∀ x : S.domain, γ * ‖(x : E)‖ ^ 2 ≤ RCLike.re ⟪S x, (x : E)⟫_𝕜) :
    ∃ SF : E →ₗ.[𝕜] E, IsSelfAdjoint SF ∧ S ≤ SF ∧
      (∀ x : SF.domain, γ * ‖(x : E)‖ ^ 2 ≤ RCLike.re ⟪SF x, (x : E)⟫_𝕜) ∧
      ∀ T : E →ₗ.[𝕜] E, IsSelfAdjoint T → S ≤ T →
        (∀ x : T.domain, γ * ‖(x : E)‖ ^ 2 ≤ RCLike.re ⟪T x, (x : E)⟫_𝕜) →
        ∀ t : ℝ, t < γ → T.resolvent (t : 𝕜) ≤ SF.resolvent (t : 𝕜) :=
  let hS : S.IsSymmetricBoundedBelow γ := ⟨hsym, hγ⟩
  ⟨friedrichsExtension hS hdense, isSelfAdjoint_friedrichsExtension hS hdense,
    le_friedrichsExtension hS hdense, mul_norm_sq_le_re_inner_friedrichsExtension hS hdense,
    fun _ hT hST hTγ _ ht => resolvent_le_resolvent_friedrichsExtension hS hdense hT hST hTγ ht⟩

end LinearPMap
