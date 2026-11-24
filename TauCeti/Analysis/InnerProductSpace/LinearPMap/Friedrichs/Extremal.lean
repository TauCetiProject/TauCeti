/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.Positive
public import TauCeti.Analysis.InnerProductSpace.LinearPMap.Friedrichs.Basic
public import TauCeti.Analysis.InnerProductSpace.LinearPMap.Resolvent

/-!
# Extremality of the Friedrichs extension

Let `S` be a densely defined symmetric partial operator on a Hilbert space `E` over `𝕜`
(`[RCLike 𝕜]`) with lower bound `γ`. Among the semibounded self-adjoint extensions `T` of `S`,
the Friedrichs extension `S_F` is the largest in form order (Krein's theorem). This file proves it
in resolvent order: if `T` has lower bound `γ'`, then for every real `t` below `γ` and `γ'`,
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
  holds at `w` (`LinearPMap.two_mul_re_inner_sub_le_friedrichsExtension`), where its left side is
  `re ⟪g, y_F⟫`.

Hence `re ⟪g, y_F⟫ ≤ re ⟪g, y_T⟫`, which is the resolvent inequality.

## Main results

* `LinearPMap.two_mul_re_inner_sub_le_friedrichsExtension`: the variational inequality passes
  from the domain of `S` to the domain of `S_F`.
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

namespace LinearPMap

variable [CompleteSpace E] {S : E →ₗ.[𝕜] E} {γ : ℝ}

/-- **The variational inequality passes to the Friedrichs extension.** If
`2 re ⟪g, u⟫ - re ⟪(S - t) u, u⟫ ≤ c` for every `u` in the domain of `S`, then the same bound
holds with `S_F` in place of `S` at every `x` in the domain of the Friedrichs extension `S_F`. -/
theorem two_mul_re_inner_sub_le_friedrichsExtension (hS : S.IsSymmetricBoundedBelow γ)
    (hdense : Dense (S.domain : Set E)) {t c : ℝ} {g : E}
    (h : ∀ u : S.domain,
      2 * RCLike.re ⟪g, (u : E)⟫_𝕜 - RCLike.re ⟪S u - (t : 𝕜) • (u : E), (u : E)⟫_𝕜 ≤ c)
    (x : (friedrichsExtension hS hdense).domain) :
    2 * RCLike.re ⟪g, (x : E)⟫_𝕜 -
        RCLike.re ⟪friedrichsExtension hS hdense x - (t : 𝕜) • (x : E), (x : E)⟫_𝕜 ≤ c := by
  -- `x` is the image of a vector `w` of the form completion.
  obtain ⟨w, hw, -⟩ := (mem_domain_friedrichsExtension_iff hS hdense).mp x.property
  set j := friedrichsInclusion hS
  -- The inequality, written through the closed form, extends from the domain of `S` to the form
  -- completion by density.
  have hclosed : _root_.IsClosed {z : FriedrichsSpace S γ hS |
      2 * RCLike.re ⟪g, j z⟫_𝕜 - (RCLike.re (friedrichsForm hS z z) - t * ‖j z‖ ^ 2) ≤ c} :=
    isClosed_le (by fun_prop) continuous_const
  have hw' : 2 * RCLike.re ⟪g, j w⟫_𝕜 - (RCLike.re (friedrichsForm hS w w) - t * ‖j w‖ ^ 2) ≤ c :=
    (denseRange_toFriedrichsSpace hS).induction_on w hclosed fun u => by
      simpa only [Set.mem_ofPred_eq, friedrichsForm_toFriedrichsSpace_left, j,
        friedrichsInclusion_toFriedrichsSpace, re_inner_apply_sub_smul_self] using h u
  rwa [re_inner_apply_sub_smul_self, ← hw, inner_friedrichsExtension hS hdense hw]

/-- **Krein's extremal property of the Friedrichs extension**, in resolvent order. Let `S` be
densely defined and symmetric with lower bound `γ`, and `T` a self-adjoint extension of `S` with
some lower bound `γ'`. For every real `t` below both `γ` and `γ'`, `T.resolvent t ≤ S_F.resolvent t`
in the Loewner order, where `R(t) = (t I - ·)⁻¹`; equivalently `(S_F - t)⁻¹ ≤ (T - t)⁻¹`. -/
theorem resolvent_le_resolvent_friedrichsExtension (hS : S.IsSymmetricBoundedBelow γ)
    (hdense : Dense (S.domain : Set E)) {T : E →ₗ.[𝕜] E} (hT : IsSelfAdjoint T) (hST : S ≤ T)
    {γ' : ℝ} (hTγ : ∀ x : T.domain, γ' * ‖(x : E)‖ ^ 2 ≤ RCLike.re ⟪T x, (x : E)⟫_𝕜) {t : ℝ}
    (ht : t < γ) (ht' : t < γ') :
    T.resolvent (t : 𝕜) ≤ (friedrichsExtension hS hdense).resolvent (t : 𝕜) := by
  set F := friedrichsExtension hS hdense
  have hF : IsSelfAdjoint F := isSelfAdjoint_friedrichsExtension hS hdense
  have hTt := hT.ofReal_mem_resolventSet_of_lt hTγ ht'
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
  -- The variational inequality for `T`, at vectors of the domain of `S`, where `T u = S u`.
  have hTu (u : S.domain) :
      2 * RCLike.re ⟪-h, (u : E)⟫_𝕜 - RCLike.re ⟪S u - (t : 𝕜) • (u : E), (u : E)⟫_𝕜 ≤
        RCLike.re ⟪-h, (yT : E)⟫_𝕜 := by
    have hu := hT.isFormalAdjoint.two_mul_re_inner_sub_le
      (fun x => (mul_le_mul_of_nonneg_right ht'.le (sq_nonneg _)).trans (hTγ x)) yT
      ⟨u, hST.1 u.property⟩
    rwa [hyT, ← hST.2 (x := u) rfl] at hu
  -- It passes to `y_F`, where its left side is `re ⟪-h, y_F⟫`.
  have hFu := two_mul_re_inner_sub_le_friedrichsExtension hS hdense hTu yF
  rw [hyF] at hFu
  have hre (y : E) : RCLike.re ⟪y, h⟫_𝕜 = -RCLike.re ⟪-h, y⟫_𝕜 := by
    rw [inner_neg_left, _root_.map_neg, neg_neg, ← inner_conj_symm, RCLike.conj_re]
  rw [hre, hre]
  linarith

/-- **The Friedrichs extension is extremal.** A densely defined symmetric partial operator `S`
with lower bound `γ` has a self-adjoint extension `S_F` with the same lower bound such that every
self-adjoint extension `T` of `S` with lower bound `γ` satisfies `T.resolvent t ≤ S_F.resolvent t`
for every real `t < γ`. -/
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
    fun _ hT hST hTγ _ ht =>
      resolvent_le_resolvent_friedrichsExtension hS hdense hT hST hTγ ht ht⟩

end LinearPMap
