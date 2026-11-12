/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.ProdL2
public import TauCeti.Analysis.InnerProductSpace.LinearPMap.SelfAdjoint

/-!
# The pair shift and a self-adjointness criterion

Over `ℂ` the classical self-adjointness criterion of von Neumann asks that the deficiency operators
`B ± i μ` of a symmetric operator be surjective. To treat real and complex scalars uniformly we use
their real form instead. For a partial linear map `B` and `μ : ℝ`, the *pair shift* is

`B.pairShift μ (x, y) = (μ • x - B y, B x + μ • y)`,

which is the operator `μ + i B` on the complexification `E ⊕ i E` written in real coordinates,
so it makes sense over every `RCLike` field. For symmetric `B` it satisfies

`‖μ • x - B y‖² + ‖B x + μ • y‖² = μ² (‖x‖² + ‖y‖²) + ‖B x‖² + ‖B y‖²`,

and for `μ ≠ 0` it characterizes self-adjointness: a symmetric `B` is self-adjoint exactly when
`B.pairShift μ` is surjective (`LinearPMap.IsFormalAdjoint.isSelfAdjoint_iff_surjective_pairShift`).
Surjectivity of the pair shift of a self-adjoint `A` comes from the orthogonal decomposition of the
`L²` product along the closed graph of `A`.

## Main declarations

* `LinearPMap.pairShift`: the pair shift `(x, y) ↦ (μ • x - B y, B x + μ • y)`.
* `LinearPMap.IsFormalAdjoint.norm_smul_sub_sq_add_norm_add_smul_sq`: its norm identity.
* `LinearPMap.IsFormalAdjoint.re_inner_pairShift`: its real-part identity
  `re (⟪x, (B.pairShift μ (x, y)).1⟫ + ⟪y, (B.pairShift μ (x, y)).2⟫) = μ (‖x‖² + ‖y‖²)`.
* `LinearPMap.IsFormalAdjoint.dense_domain_of_surjective_pairShift`: a symmetric map with a
  surjective pair shift is densely defined.
* `LinearPMap.IsFormalAdjoint.isSelfAdjoint_of_surjective_pairShift` and
  `IsSelfAdjoint.surjective_pairShift`: the self-adjointness criterion and its converse, combined
  in `LinearPMap.IsFormalAdjoint.isSelfAdjoint_iff_surjective_pairShift`.

## References

* M. Reed and B. Simon, *Methods of Modern Mathematical Physics I: Functional Analysis*,
  Academic Press (1980), Theorem VIII.3 (the basic criterion for self-adjointness).
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
  simp only [@norm_sub_sq 𝕜, @norm_add_sq 𝕜, inner_smul_left, inner_smul_right, norm_smul,
    RCLike.conj_ofReal, RCLike.re_ofReal_mul, hxy, RCLike.norm_ofReal, mul_pow, sq_abs]
  ring

/-- The real-part identity of the pair shift of a symmetric partial linear map:
`re (⟪x, μ • x - B y⟫ + ⟪y, B x + μ • y⟫) = μ (‖x‖² + ‖y‖²)`. -/
theorem re_inner_pairShift (hB : B.IsFormalAdjoint B) (μ : ℝ) (x y : B.domain) :
    RCLike.re (⟪(x : E), (B.pairShift μ (x, y)).1⟫_𝕜 + ⟪(y : E), (B.pairShift μ (x, y)).2⟫_𝕜) =
      μ * (‖(x : E)‖ ^ 2 + ‖(y : E)‖ ^ 2) := by
  have hsym : RCLike.re ⟪(y : E), B x⟫_𝕜 = RCLike.re ⟪(x : E), B y⟫_𝕜 := by
    rw [← inner_conj_symm, RCLike.conj_re, hB x y]
  simp only [pairShift_apply, inner_sub_right, inner_add_right, inner_smul_right, _root_.map_add,
    _root_.map_sub, RCLike.re_ofReal_mul, inner_self_eq_norm_sq, hsym]
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
  have hre := hB.re_inner_pairShift μ x y
  simp only [hxy, Submodule.inner_right_of_mem_orthogonal x.2 hw,
    Submodule.inner_right_of_mem_orthogonal y.2 hw, add_zero, _root_.map_zero] at hre
  obtain ⟨hx, hy⟩ := sq_add_sq_eq_zero.1 ((mul_eq_zero.1 hre.symm).resolve_left hμ)
  rw [norm_eq_zero, ZeroMemClass.coe_eq_zero] at hx hy
  subst hx hy
  simpa [eq_comm] using congrArg Prod.fst hxy

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
  have hn := congrArg RCLike.re hkey
  rw [_root_.map_add, inner_self_eq_norm_sq, inner_self_eq_norm_sq, _root_.map_zero] at hn
  exact sub_eq_zero.1 (norm_eq_zero.1 (sq_add_sq_eq_zero.1 hn).1) ▸ x.2

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
  · simp [LinearPMap.map_smul, hy₂, hx₁, hu, smul_smul, hμ']
  · simp [hx₂, hy₁, hv, smul_smul, hμ']

/-- **Self-adjointness through the pair shift.** For `μ ≠ 0`, a symmetric partial linear map on a
Hilbert space is self-adjoint exactly when its pair shift is surjective. -/
theorem IsFormalAdjoint.isSelfAdjoint_iff_surjective_pairShift [CompleteSpace E]
    {B : E →ₗ.[𝕜] E} (hB : B.IsFormalAdjoint B) {μ : ℝ} (hμ : μ ≠ 0) :
    IsSelfAdjoint B ↔ Function.Surjective (B.pairShift μ) :=
  ⟨fun h ↦ h.surjective_pairShift hμ, hB.isSelfAdjoint_of_surjective_pairShift hμ⟩

end LinearPMap
