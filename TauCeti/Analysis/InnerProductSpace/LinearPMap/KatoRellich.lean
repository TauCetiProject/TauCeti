/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.InnerProductSpace.LinearPMap.PairShift
public import TauCeti.Analysis.Normed.Operator.LinearPMap.RelativeBound
public import TauCeti.Analysis.Normed.Operator.Surjective

/-!
# The Kato–Rellich theorem

Let `A` be a self-adjoint partial linear map on a Hilbert space and `V` a symmetric partial linear
map that is relatively bounded with respect to `A`: `dom A ⊆ dom V` and
`‖V x‖ ≤ a * ‖x‖ + b * ‖A x‖` on `dom A`. If `b < 1`, then `A + V` is self-adjoint on `dom A`
(`IsSelfAdjoint.add_of_isRelativelyBounded`). The scalar field is any `RCLike` field, so the real
case is included.

Over `ℂ` the classical proof perturbs the deficiency operators `A ± i μ`. To treat real and
complex scalars uniformly we use their real form, the pair shift
`B.pairShift μ (x, y) = (μ • x - B y, B x + μ • y)` of
`TauCeti.Analysis.InnerProductSpace.LinearPMap.PairShift`: a symmetric `B` is self-adjoint exactly
when its pair shift is surjective for some `μ ≠ 0`. The perturbation `V` changes the pair shift of
`A` by a map whose norm is at most `(a / μ + b)` times that of the pair shift, and `a / μ + b < 1`
once `μ` is large, so surjectivity survives (`LinearMap.surjective_add_of_norm_le`).

## Main declarations

* `IsSelfAdjoint.surjective_pairShift_add`: the pair shift of `A + V` is surjective when
  `a / μ + b < 1`.
* `IsSelfAdjoint.add_of_isRelativelyBounded`: the **Kato–Rellich theorem**.

## References

* T. Kato, *Perturbation Theory for Linear Operators*, 2nd ed., Springer (1976), Theorem V.4.3.
* M. Reed and B. Simon, *Methods of Modern Mathematical Physics II: Fourier Analysis,
  Self-Adjointness*, Academic Press (1975), Theorem X.12.
* K. Schmüdgen, *Unbounded Self-adjoint Operators on Hilbert Space*, Springer (2012),
  Theorem 8.5.
-/

public section

noncomputable section

open scoped InnerProductSpace

namespace LinearPMap

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]

/-- A relative bound in the form used for the pair shift: if `‖V x‖ ≤ a * ‖x‖ + b * ‖A x‖` with
`a, b ≥ 0` and `μ > 0`, then `‖V x‖² ≤ (a / μ + b)² (μ² ‖x‖² + ‖A x‖²)`. -/
private theorem sq_norm_apply_le_of_isRelativelyBounded {A V : E →ₗ.[𝕜] E} {a b : ℝ}
    (hAV : V.IsRelativelyBounded A a b) (ha : 0 ≤ a) (hb : 0 ≤ b) {μ : ℝ} (hμ : 0 < μ)
    (x : A.domain) :
    ‖V ⟨x, hAV.domain_le x.2⟩‖ ^ 2 ≤ (a / μ + b) ^ 2 * (μ ^ 2 * ‖(x : E)‖ ^ 2 + ‖A x‖ ^ 2) := by
  have hp : 0 ≤ a / μ := by positivity
  have hX : 0 ≤ μ * ‖(x : E)‖ := by positivity
  have h₁ : ‖V ⟨x, hAV.domain_le x.2⟩‖ ≤ a / μ * (μ * ‖(x : E)‖) + b * ‖A x‖ := by
    rw [← mul_assoc, div_mul_cancel₀ _ hμ.ne']
    exact hAV.norm_apply_le x
  calc ‖V ⟨x, hAV.domain_le x.2⟩‖ ^ 2 ≤ (a / μ * (μ * ‖(x : E)‖) + b * ‖A x‖) ^ 2 :=
        pow_le_pow_left₀ (norm_nonneg _) h₁ 2
    _ ≤ (a / μ + b) ^ 2 * ((μ * ‖(x : E)‖) ^ 2 + ‖A x‖ ^ 2) := by
        nlinarith [mul_nonneg (mul_nonneg hp hb) (sq_nonneg (μ * ‖(x : E)‖ - ‖A x‖)),
          mul_nonneg (sq_nonneg (a / μ)) (sq_nonneg ‖A x‖),
          mul_nonneg (sq_nonneg b) (sq_nonneg (μ * ‖(x : E)‖)),
          mul_nonneg (mul_nonneg hp hb) (mul_nonneg hX (norm_nonneg (A x)))]
    _ = _ := by ring

open WithLp in
/-- **The pair shift survives a relatively bounded perturbation.** Let `A` be self-adjoint and let
`‖V x‖ ≤ a * ‖x‖ + b * ‖A x‖` on `dom A ⊆ dom V`, with `a, b ≥ 0`. If `μ > 0` and
`a / μ + b < 1`, then the pair shift of `A + V` is surjective. -/
theorem _root_.IsSelfAdjoint.surjective_pairShift_add [CompleteSpace E] {A V : E →ₗ.[𝕜] E}
    (hA : IsSelfAdjoint A) {a b : ℝ} (hAV : V.IsRelativelyBounded A a b) (ha : 0 ≤ a)
    (hb : 0 ≤ b) {μ : ℝ} (hμ : 0 < μ) (hθ : a / μ + b < 1) :
    Function.Surjective ((A + V).pairShift μ) := by
  -- In the `L²` product, the pair shift of `A + V` is that of `A` plus `K (x, y) = (-V y, V x)`,
  -- and `‖K z‖ ≤ (a / μ + b) ‖A.pairShift μ z‖`.
  let e := (WithLp.linearEquiv 2 𝕜 (E × E)).symm
  let Vd : A.domain →ₗ[𝕜] E := V.toFun ∘ₗ Submodule.inclusion hAV.domain_le
  let K : A.domain × A.domain →ₗ[𝕜] E × E :=
    (-(Vd ∘ₗ LinearMap.snd 𝕜 _ _)).prod (Vd ∘ₗ LinearMap.fst 𝕜 _ _)
  have hVd (x : A.domain) :
      ‖Vd x‖ ^ 2 ≤ (a / μ + b) ^ 2 * (μ ^ 2 * ‖(x : E)‖ ^ 2 + ‖A x‖ ^ 2) :=
    sq_norm_apply_le_of_isRelativelyBounded hAV ha hb hμ x
  have hQK : Function.Surjective (e.toLinearMap ∘ₗ A.pairShift μ + e.toLinearMap ∘ₗ K) := by
    refine LinearMap.surjective_add_of_norm_le _ _
      (e.surjective.comp (hA.surjective_pairShift hμ.ne')) hθ fun z ↦ ?_
    refine (sq_le_sq₀ (norm_nonneg _) (by positivity)).1 ?_
    have he (p : E × E) : ‖(e : E × E →ₗ[𝕜] WithLp 2 (E × E)) p‖ ^ 2 = ‖p.1‖ ^ 2 + ‖p.2‖ ^ 2 := by
      simp [e, prod_norm_sq_eq_of_L2]
    rw [LinearMap.comp_apply, LinearMap.comp_apply, mul_pow, he, he, pairShift_apply,
      hA.isFormalAdjoint.norm_smul_sub_sq_add_norm_add_smul_sq]
    simp only [K, LinearMap.prod_apply, Function.prod, LinearMap.neg_apply, LinearMap.comp_apply,
      LinearMap.coe_fst, LinearMap.coe_snd, norm_neg]
    nlinarith [hVd z.1, hVd z.2]
  intro w
  obtain ⟨z, hz⟩ := hQK (e w)
  have hdom : A.domain ≤ (A + V).domain := hAV.domain_add.ge
  refine ⟨(Submodule.inclusion hdom z.1, Submodule.inclusion hdom z.2), e.injective ?_⟩
  rw [← hz, LinearMap.add_apply, LinearMap.comp_apply, LinearMap.comp_apply, ← _root_.map_add]
  refine congrArg e (Prod.ext ?_ ?_) <;>
    simp only [K, Vd, Submodule.inclusion_apply, pairShift_apply, add_apply, Subtype.coe_eta,
      LinearMap.prod_apply, LinearMap.coe_neg, LinearMap.coe_comp, coe_toFun_eq_coe,
      LinearMap.coe_snd, LinearMap.coe_fst, Function.prod_apply, Pi.neg_apply, Function.comp_apply,
      Prod.mk_add_mk] <;>
    abel

/-- **The Kato–Rellich theorem.** Let `A` be a self-adjoint partial linear map on a Hilbert space
and `V` a symmetric partial linear map that is relatively bounded with respect to `A` with
constants `a` and `b < 1`, that is `dom A ⊆ dom V` and `‖V x‖ ≤ a * ‖x‖ + b * ‖A x‖` on `dom A`.
Then `A + V`, whose domain is `dom A`, is self-adjoint. -/
theorem _root_.IsSelfAdjoint.add_of_isRelativelyBounded [CompleteSpace E] {A V : E →ₗ.[𝕜] E}
    (hA : IsSelfAdjoint A) (hV : V.IsFormalAdjoint V) {a b : ℝ}
    (hAV : V.IsRelativelyBounded A a b) (hb : b < 1) : IsSelfAdjoint (A + V) := by
  have hsym : (A + V).IsFormalAdjoint (A + V) := hA.isFormalAdjoint.add hV
  -- Pass to nonnegative constants `a', b'` and choose `μ` with `a' / μ + b' < 1`.
  have hb' : max b 0 < 1 := max_lt hb one_pos
  set μ : ℝ := (max a 0 + 1) / (1 - max b 0)
  have hμ : 0 < μ := div_pos (by positivity) (by linarith)
  have hθ : max a 0 / μ + max b 0 < 1 := by
    have hμ' : (1 - max b 0) * μ = max a 0 + 1 := mul_div_cancel₀ _ (by linarith)
    have : max a 0 / μ < 1 - max b 0 := by
      rw [div_lt_iff₀ hμ, hμ']
      linarith
    linarith
  exact hsym.isSelfAdjoint_of_surjective_pairShift hμ.ne' <|
    hA.surjective_pairShift_add (hAV.mono (le_max_left a 0) (le_max_left b 0))
      (le_max_right _ _) (le_max_right _ _) hμ hθ

end LinearPMap
