/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.ProdL2
public import TauCeti.Analysis.InnerProductSpace.LinearPMap.SelfAdjoint
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
complex scalars uniformly we use their real form instead. For a partial linear map `B` and
`μ : ℝ`, the *pair shift* is

`B.pairShift μ (x, y) = (μ • x - B y, B x + μ • y)`,

which is the operator `μ + i B` on the complexification `E ⊕ i E` written in real coordinates,
so it makes sense over every `RCLike` field. For symmetric `B` it satisfies

`‖μ • x - B y‖² + ‖B x + μ • y‖² = μ² (‖x‖² + ‖y‖²) + ‖B x‖² + ‖B y‖²`,

and for `μ ≠ 0` it characterizes self-adjointness: a symmetric `B` is self-adjoint exactly when
`B.pairShift μ` is surjective (`LinearPMap.IsFormalAdjoint.isSelfAdjoint_iff_surjective_pairShift`).
Surjectivity of the pair shift of a self-adjoint `A` comes from the orthogonal decomposition of the
`L²` product along the closed graph of `A`. For Kato–Rellich, the perturbation `V` changes the pair
shift of `A` by a map whose norm is at most `(a / μ + b)` times that of the pair shift, and
`a / μ + b < 1` once `μ` is large, so surjectivity survives
(`LinearMap.surjective_add_of_norm_le`).

## Main declarations

* `LinearPMap.pairShift`: the pair shift `(x, y) ↦ (μ • x - B y, B x + μ • y)`.
* `LinearPMap.IsFormalAdjoint.norm_smul_sub_sq_add_norm_add_smul_sq`: its norm identity.
* `LinearPMap.IsFormalAdjoint.dense_domain_of_surjective_pairShift`: a symmetric map with a
  surjective pair shift is densely defined.
* `LinearPMap.IsFormalAdjoint.isSelfAdjoint_of_surjective_pairShift` and
  `IsSelfAdjoint.surjective_pairShift`: the self-adjointness criterion and its converse, combined
  in `LinearPMap.IsFormalAdjoint.isSelfAdjoint_iff_surjective_pairShift`.
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

/-- The *pair shift* `(x, y) ↦ (μ • x - B y, B x + μ • y)` of a partial linear map `B`, defined on
pairs of vectors in the domain of `B`. It is the operator `μ + i B` on the complexification of `E`,
written in real coordinates. -/
def pairShift (B : E →ₗ.[𝕜] E) (μ : ℝ) : B.domain × B.domain →ₗ[𝕜] E × E :=
  ((μ : 𝕜) • (B.domain.subtype ∘ₗ LinearMap.fst 𝕜 _ _) - B.toFun ∘ₗ LinearMap.snd 𝕜 _ _).prod
    (B.toFun ∘ₗ LinearMap.fst 𝕜 _ _ + (μ : 𝕜) • (B.domain.subtype ∘ₗ LinearMap.snd 𝕜 _ _))

@[simp]
theorem pairShift_apply (B : E →ₗ.[𝕜] E) (μ : ℝ) (z : B.domain × B.domain) :
    B.pairShift μ z = ((μ : 𝕜) • (z.1 : E) - B z.2, B z.1 + (μ : 𝕜) • (z.2 : E)) :=
  (rfl)

namespace IsFormalAdjoint

variable {B : E →ₗ.[𝕜] E}

/-- The norm identity of the pair shift of a symmetric partial linear map:
`‖μ • x - B y‖² + ‖B x + μ • y‖² = μ² (‖x‖² + ‖y‖²) + ‖B x‖² + ‖B y‖²`. -/
theorem norm_smul_sub_sq_add_norm_add_smul_sq (hB : B.IsFormalAdjoint B) (μ : ℝ)
    (x y : B.domain) :
    ‖(μ : 𝕜) • (x : E) - B y‖ ^ 2 + ‖B x + (μ : 𝕜) • (y : E)‖ ^ 2 =
      μ ^ 2 * (‖(x : E)‖ ^ 2 + ‖(y : E)‖ ^ 2) + (‖B x‖ ^ 2 + ‖B y‖ ^ 2) := by
  have hxy : RCLike.re ⟪B x, (y : E)⟫_𝕜 = RCLike.re ⟪(x : E), B y⟫_𝕜 := by rw [hB x y]
  rw [@norm_sub_sq 𝕜, @norm_add_sq 𝕜, inner_smul_left, inner_smul_right, norm_smul, norm_smul,
    RCLike.conj_ofReal, RCLike.re_ofReal_mul, RCLike.re_ofReal_mul, hxy, RCLike.norm_ofReal,
    mul_pow, mul_pow, sq_abs]
  ring

/-- A symmetric partial linear map whose pair shift is surjective, for some `μ ≠ 0`, is densely
defined. -/
theorem dense_domain_of_surjective_pairShift [CompleteSpace E] (hB : B.IsFormalAdjoint B)
    {μ : ℝ} (hμ : μ ≠ 0) (h : Function.Surjective (B.pairShift μ)) :
    Dense (B.domain : Set E) := by
  rw [Submodule.dense_iff_topologicalClosure_eq_top, Submodule.topologicalClosure_eq_top_iff,
    Submodule.eq_bot_iff]
  intro w hw
  obtain ⟨⟨x, y⟩, hxy⟩ := h (w, w)
  simp only [pairShift_apply, Prod.mk.injEq] at hxy
  obtain ⟨h₁, h₂⟩ := hxy
  have hx : ⟪(x : E), w⟫_𝕜 = 0 := Submodule.inner_right_of_mem_orthogonal x.2 hw
  have hy : ⟪(y : E), w⟫_𝕜 = 0 := Submodule.inner_right_of_mem_orthogonal y.2 hw
  rw [← h₁] at hx
  rw [← h₂] at hy
  have hsym : RCLike.re ⟪(y : E), B x⟫_𝕜 = RCLike.re ⟪(x : E), B y⟫_𝕜 := by
    rw [← inner_conj_symm, RCLike.conj_re, hB x y]
  have hre : RCLike.re (⟪(x : E), (μ : 𝕜) • (x : E) - B y⟫_𝕜 +
      ⟪(y : E), B x + (μ : 𝕜) • (y : E)⟫_𝕜) = 0 := by
    rw [hx, hy, add_zero, _root_.map_zero]
  simp only [inner_sub_right, inner_add_right, inner_smul_right, _root_.map_add, _root_.map_sub,
    RCLike.re_ofReal_mul, inner_self_eq_norm_sq, hsym] at hre
  have hsum : ‖(x : E)‖ ^ 2 + ‖(y : E)‖ ^ 2 = 0 :=
    (mul_eq_zero.1 (by linear_combination hre)).resolve_left hμ
  rw [add_eq_zero_iff_of_nonneg (sq_nonneg _) (sq_nonneg _), sq_eq_zero_iff, sq_eq_zero_iff,
    norm_eq_zero, norm_eq_zero] at hsum
  have hy0 : y = 0 := Subtype.ext hsum.2
  rw [← h₁, hsum.1, hy0, map_zero, smul_zero, sub_zero]

/-- **A self-adjointness criterion.** A symmetric partial linear map on a Hilbert space whose pair
shift is surjective for some `μ ≠ 0` is self-adjoint. This is the real form of von Neumann's
criterion that `B ± i μ` be surjective. -/
theorem isSelfAdjoint_of_surjective_pairShift [CompleteSpace E] (hB : B.IsFormalAdjoint B)
    {μ : ℝ} (hμ : μ ≠ 0) (h : Function.Surjective (B.pairShift μ)) : IsSelfAdjoint B := by
  have hdense := hB.dense_domain_of_surjective_pairShift hμ h
  have hle : B ≤ B† := hB.le_adjoint hdense
  refine (eq_of_le_of_domain_eq hle (le_antisymm hle.1 fun z hz ↦ ?_)).symm
  -- Write `B† z = w`. Solve `μ x - B y = μ z` and `B x + μ y = w`; then `d = (z - x, -y)` is
  -- orthogonal to itself, so `z = x` lies in the domain of `B`.
  have hadj : ∀ q : B.domain, ⟪B† ⟨z, hz⟩, (q : E)⟫_𝕜 = ⟪z, B q⟫_𝕜 :=
    fun q ↦ adjoint_isFormalAdjoint hdense ⟨z, hz⟩ q
  obtain ⟨⟨x, y⟩, hxy⟩ := h ((μ : 𝕜) • z, B† ⟨z, hz⟩)
  simp only [pairShift_apply, Prod.mk.injEq] at hxy
  obtain ⟨h₁, h₂⟩ := hxy
  obtain ⟨⟨x', y'⟩, hxy'⟩ := h (z - x, y)
  simp only [pairShift_apply, Prod.mk.injEq] at hxy'
  obtain ⟨h₁', h₂'⟩ := hxy'
  have hF₁ : ⟪z - (x : E), B y'⟫_𝕜 = (μ : 𝕜) * ⟪(y : E), y'⟫_𝕜 := by
    rw [inner_sub_left, ← hadj y', ← hB x y', ← h₂, inner_add_left, inner_smul_left,
      RCLike.conj_ofReal]
    ring
  have hF₂ : ⟪-(y : E), B x'⟫_𝕜 = (μ : 𝕜) * ⟪z - (x : E), x'⟫_𝕜 := by
    rw [inner_neg_left, ← hB y x', ← inner_neg_left, show -B y = (μ : 𝕜) • (z - x) by
      rw [smul_sub, ← h₁]; abel, inner_smul_left, RCLike.conj_ofReal]
  have hkey : ⟪z - (x : E), z - x⟫_𝕜 + ⟪-(y : E), -(y : E)⟫_𝕜 = 0 := by
    have e₁ : ⟪z - (x : E), z - x⟫_𝕜 = ⟪z - (x : E), (μ : 𝕜) • (x' : E) - B y'⟫_𝕜 := by rw [h₁']
    have e₂ : ⟪-(y : E), -(y : E)⟫_𝕜 = ⟪-(y : E), -(B x' + (μ : 𝕜) • (y' : E))⟫_𝕜 := by rw [h₂']
    rw [e₁, e₂, inner_sub_right, inner_smul_right, hF₁, inner_neg_right, inner_add_right, hF₂,
      inner_smul_right, inner_neg_left]
    ring
  rw [inner_self_eq_norm_sq_to_K, inner_self_eq_norm_sq_to_K, ← RCLike.ofReal_pow,
    ← RCLike.ofReal_pow, ← RCLike.ofReal_add, RCLike.ofReal_eq_zero,
    add_eq_zero_iff_of_nonneg (sq_nonneg _) (sq_nonneg _), sq_eq_zero_iff, norm_eq_zero,
    sub_eq_zero] at hkey
  exact hkey.1 ▸ x.2

end IsFormalAdjoint

open WithLp in
/-- The pair shift of a self-adjoint partial linear map is surjective for every `μ ≠ 0`. -/
theorem _root_.IsSelfAdjoint.surjective_pairShift [CompleteSpace E] {A : E →ₗ.[𝕜] E}
    (hA : IsSelfAdjoint A) {μ : ℝ} (hμ : μ ≠ 0) : Function.Surjective (A.pairShift μ) := by
  rintro ⟨u, v⟩
  have hμ' : (μ : 𝕜) ≠ 0 := RCLike.ofReal_ne_zero.2 hμ
  -- Decompose `(u, v)` along the closed subspace `K = {(μ x, A x)}` of the `L²` product.
  let L : WithLp 2 (E × E) →L[𝕜] E × E :=
    ((((μ : 𝕜)⁻¹ • ContinuousLinearMap.id 𝕜 E).prodMap (ContinuousLinearMap.id 𝕜 E))).comp
      (prodContinuousLinearEquiv 2 𝕜 E E).toContinuousLinearMap
  have hL : ∀ w, L w = ((μ : 𝕜)⁻¹ • (ofLp w).1, (ofLp w).2) := fun w ↦
    Prod.ext (by simp [L]) (by simp [L])
  let K : Submodule 𝕜 (WithLp 2 (E × E)) := A.graph.comap (L : WithLp 2 (E × E) →ₗ[𝕜] E × E)
  have hK : _root_.IsClosed (K : Set (WithLp 2 (E × E))) := hA.isClosed.preimage L.continuous
  have : CompleteSpace K := hK.completeSpace_coe
  obtain ⟨k, hk, z, hz, hkz⟩ := K.exists_add_mem_mem_orthogonal (toLp 2 (u, v))
  obtain ⟨x, hx₁, hx₂⟩ := A.mem_graph_iff.1 (Submodule.mem_comap.1 hk)
  simp only [ContinuousLinearMap.coe_coe, hL] at hx₁ hx₂
  -- The orthogonal component is `(-μ⁻¹ A y₀, y₀)` for some `y₀` in the domain of `A`.
  have hzq : ∀ q : A.domain, ⟪-(μ : 𝕜) • (ofLp z).1, (q : E)⟫_𝕜 = ⟪(ofLp z).2, A q⟫_𝕜 := by
    intro q
    have hmem : toLp 2 ((μ : 𝕜) • (q : E), A q) ∈ K := by
      rw [Submodule.mem_comap, ContinuousLinearMap.coe_coe, hL, ofLp_toLp, smul_smul,
        inv_mul_cancel₀ hμ', one_smul]
      exact A.mem_graph q
    have h0 := Submodule.inner_right_of_mem_orthogonal hmem hz
    simp only [prod_inner_apply, inner_smul_left, RCLike.conj_ofReal] at h0
    have h1 := congrArg (starRingEnd 𝕜) h0
    rw [_root_.map_add, _root_.map_mul, RCLike.conj_ofReal, _root_.map_zero] at h1
    rw [inner_smul_left, _root_.map_neg, RCLike.conj_ofReal, ← inner_conj_symm (ofLp z).1,
      ← inner_conj_symm (ofLp z).2]
    linear_combination -h1
  have hz₂ : (ofLp z).2 ∈ A†.domain := mem_adjoint_domain_of_exists _ ⟨_, hzq⟩
  have hgraph : ((ofLp z).2, -(μ : 𝕜) • (ofLp z).1) ∈ A.graph := by
    rw [← LinearPMap.isSelfAdjoint_def.1 hA, ← adjoint_apply_eq hA.dense_domain ⟨_, hz₂⟩ hzq]
    exact A†.mem_graph ⟨_, hz₂⟩
  obtain ⟨y₀, hy₁, hy₂⟩ := A.mem_graph_iff.1 hgraph
  have hu : u = (ofLp k).1 + (ofLp z).1 := by simpa using congrArg (fun w ↦ (ofLp w).1) hkz
  have hv : v = (ofLp k).2 + (ofLp z).2 := by simpa using congrArg (fun w ↦ (ofLp w).2) hkz
  simp only at hy₁ hy₂
  refine ⟨(x, (μ : 𝕜)⁻¹ • y₀), Prod.ext ?_ ?_⟩
  · simp only [pairShift_apply, LinearPMap.map_smul, hy₂, hx₁, hu]
    rw [neg_smul, smul_neg, smul_smul, smul_smul, mul_inv_cancel₀ hμ', inv_mul_cancel₀ hμ',
      one_smul, one_smul, sub_neg_eq_add]
  · simp [hx₂, hy₁, hv, smul_smul, hμ']

/-- **Self-adjointness through the pair shift.** For `μ ≠ 0`, a symmetric partial linear map on a
Hilbert space is self-adjoint exactly when its pair shift is surjective. -/
theorem IsFormalAdjoint.isSelfAdjoint_iff_surjective_pairShift [CompleteSpace E]
    {B : E →ₗ.[𝕜] E} (hB : B.IsFormalAdjoint B) {μ : ℝ} (hμ : μ ≠ 0) :
    IsSelfAdjoint B ↔ Function.Surjective (B.pairShift μ) :=
  ⟨fun h ↦ h.surjective_pairShift hμ, hB.isSelfAdjoint_of_surjective_pairShift hμ⟩

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
  have hdom : A.domain ≤ (A + V).domain := le_inf le_rfl hAV.domain_le
  refine ⟨(Submodule.inclusion hdom z.1, Submodule.inclusion hdom z.2), e.injective ?_⟩
  rw [← hz, LinearMap.add_apply, LinearMap.comp_apply, LinearMap.comp_apply, ← _root_.map_add]
  refine congrArg e (Prod.ext ?_ ?_)
  · simp [K, Vd, add_apply, Submodule.inclusion_apply]
    abel
  · simp [K, Vd, add_apply, Submodule.inclusion_apply]
    abel

/-- **The Kato–Rellich theorem.** Let `A` be a self-adjoint partial linear map on a Hilbert space
and `V` a symmetric partial linear map that is relatively bounded with respect to `A` with
constants `a` and `b < 1`, that is `dom A ⊆ dom V` and `‖V x‖ ≤ a * ‖x‖ + b * ‖A x‖` on `dom A`.
Then `A + V`, whose domain is `dom A`, is self-adjoint. -/
theorem _root_.IsSelfAdjoint.add_of_isRelativelyBounded [CompleteSpace E] {A V : E →ₗ.[𝕜] E}
    (hA : IsSelfAdjoint A) (hV : V.IsFormalAdjoint V) {a b : ℝ}
    (hAV : V.IsRelativelyBounded A a b) (hb : b < 1) : IsSelfAdjoint (A + V) := by
  have hsym : (A + V).IsFormalAdjoint (A + V) := fun x y ↦ by
    rw [add_apply, add_apply, inner_add_left, inner_add_right,
      hA.isFormalAdjoint ⟨x, x.2.1⟩ ⟨y, y.2.1⟩, hV ⟨x, x.2.2⟩ ⟨y, y.2.2⟩]
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
