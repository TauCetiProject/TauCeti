/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Operator.Basic
public import Mathlib.Analysis.Normed.Module.HahnBanach
public import Mathlib.LinearAlgebra.LinearPMap

/-!
# Relatively bounded partial linear maps

A partial linear map `V` is *relatively bounded* with respect to a partial linear map `A`, with
constants `a` and `b`, when the domain of `A` lies in the domain of `V` and

`‖V x‖ ≤ a * ‖x‖ + b * ‖A x‖` for every `x` in the domain of `A`.

This is the size condition of perturbation theory for unbounded operators: the perturbation is
controlled by the graph of `A` rather than by `‖x‖` alone, and the Kato–Rellich theorem asks for
`b < 1`. The infimum of the admissible `b` is Kato's *`A`-bound* of `V`.

This file sets up the predicate and its elementary calculus: the zero map is relatively bounded
with constants `0, 0`; the constants may be increased; relative bounds add under sums and
differences, scale under scalar multiplication and are unchanged by negation; and the restriction
of a bounded operator `T` to a subspace containing the domain of `A` is relatively bounded with
constants `‖T‖, 0`. Sums and differences use Mathlib's addition of partial linear maps, whose
domain is the intersection of the two domains.

The predicate only compares norms, so `V` and `A` may be semilinear over different ring
homomorphisms out of a common scalar ring, and their codomains need no compatibility between norm
and scalar multiplication.

## Main declarations

* `LinearPMap.IsRelativelyBounded V A a b`: `V` is `A`-bounded with constants `a, b`.
* `LinearPMap.IsRelativelyBounded.mono`: increasing the constants.
* `LinearPMap.IsRelativelyBounded.domain_add`: the domain of `A + V` is the domain of `A`.
* `LinearPMap.IsRelativelyBounded.add`, `.sub`, `.neg`, `.smul`: the linear calculus.
* `LinearPMap.IsRelativelyBounded.isRelativelyBounded_self_add`: for `A`-bound `b < 1`, `A` is
  `(A + V)`-bounded.
* `LinearPMap.isRelativelyBounded_zero`, `ContinuousLinearMap.isRelativelyBounded_toPMap`: the
  zero map and restrictions of bounded operators.
* `LinearPMap.exists_normalized_of_not_isRelativelyBounded`: over a normed `ℝ`-algebra, a relative
  bound that fails, fails at a vector of graph norm `‖x‖ + ‖A x‖ = 1`.
* `LinearPMap.exists_dual_apply_eq_of_isRelativelyBounded`: by Hahn–Banach on the graph of `A`,
  every functional of `V x` for an `A`-bounded `V` is a continuous functional of `(x, A x)`.

## References

* T. Kato, *Perturbation Theory for Linear Operators*, 2nd ed., Springer (1976), §IV.1.1.
* M. Reed and B. Simon, *Methods of Modern Mathematical Physics II: Fourier Analysis,
  Self-Adjointness*, Academic Press (1975), §X.2.
-/

public section

namespace LinearPMap

variable {R S T E F G : Type*} [Ring R] [Ring S] [Ring T] {σ : R →+* S} {τ : R →+* T}
  [SeminormedAddCommGroup E] [Module R E] [SeminormedAddCommGroup F] [Module T F]
  [SeminormedAddCommGroup G] [Module S G]

/-- A partial linear map `V` is *relatively bounded* with respect to `A`, with constants `a` and
`b`, when `A.domain ≤ V.domain` and `‖V x‖ ≤ a * ‖x‖ + b * ‖A x‖` for every `x` in the domain of
`A`. -/
structure IsRelativelyBounded (V : E →ₛₗ.[σ] G) (A : E →ₛₗ.[τ] F) (a b : ℝ) : Prop where
  /-- The domain of `A` lies in the domain of `V`. -/
  domain_le : A.domain ≤ V.domain
  /-- The relative bound `‖V x‖ ≤ a * ‖x‖ + b * ‖A x‖` on the domain of `A`. -/
  norm_apply_le : ∀ x : A.domain, ‖V ⟨x, domain_le x.property⟩‖ ≤ a * ‖(x : E)‖ + b * ‖A x‖

namespace IsRelativelyBounded

variable {V W : E →ₛₗ.[σ] G} {A : E →ₛₗ.[τ] F} {a b a' b' : ℝ}

/-- A relative bound holds at any larger pair of constants. -/
theorem mono (h : V.IsRelativelyBounded A a b) (ha : a ≤ a') (hb : b ≤ b') :
    V.IsRelativelyBounded A a' b' where
  domain_le := h.domain_le
  norm_apply_le x := (h.norm_apply_le x).trans (by gcongr)

/-- A relative bound with constants `a, b` bounds `‖V x‖` by `(|a| + |b|)` times the larger of
`‖x‖` and `‖A x‖`. -/
theorem norm_apply_le_abs_add_abs_mul_max (h : V.IsRelativelyBounded A a b) (x : A.domain) :
    ‖V ⟨x, h.domain_le x.property⟩‖ ≤ (|a| + |b|) * max ‖(x : E)‖ ‖A x‖ := by
  have h₁ : a * ‖(x : E)‖ ≤ |a| * max ‖(x : E)‖ ‖A x‖ :=
    (mul_le_mul_of_nonneg_right (le_abs_self a) (norm_nonneg _)).trans
      (mul_le_mul_of_nonneg_left (le_max_left _ _) (abs_nonneg a))
  have h₂ : b * ‖A x‖ ≤ |b| * max ‖(x : E)‖ ‖A x‖ :=
    (mul_le_mul_of_nonneg_right (le_abs_self b) (norm_nonneg _)).trans
      (mul_le_mul_of_nonneg_left (le_max_right _ _) (abs_nonneg b))
  linarith [h.norm_apply_le x]

/-- If `V` is relatively bounded with respect to `A`, then `A + V` has the same domain as `A`. -/
theorem domain_add {V : E →ₛₗ.[τ] F} (h : V.IsRelativelyBounded A a b) :
    (A + V).domain = A.domain :=
  inf_eq_left.2 h.domain_le

/-- Relative bounds add under the sum of two partial linear maps. -/
theorem add (hV : V.IsRelativelyBounded A a b) (hW : W.IsRelativelyBounded A a' b') :
    (V + W).IsRelativelyBounded A (a + a') (b + b') where
  domain_le := le_inf hV.domain_le hW.domain_le
  norm_apply_le x := by
    rw [add_apply]
    exact (norm_add_le _ _).trans (by linarith [hV.norm_apply_le x, hW.norm_apply_le x])

/-- Negation does not change a relative bound. -/
theorem neg (h : V.IsRelativelyBounded A a b) : (-V).IsRelativelyBounded A a b where
  domain_le := h.domain_le
  norm_apply_le x := by
    rw [neg_apply, norm_neg]
    exact h.norm_apply_le x

/-- Relative bounds add under the difference of two partial linear maps. -/
theorem sub (hV : V.IsRelativelyBounded A a b) (hW : W.IsRelativelyBounded A a' b') :
    (V - W).IsRelativelyBounded A (a + a') (b + b') :=
  sub_eq_add_neg V W ▸ hV.add hW.neg

/-- A scalar multiple `c • V` is relatively bounded with the constants scaled by `‖c‖`. -/
theorem smul {M : Type*} [SeminormedRing M] [DistribMulAction M G] [IsBoundedSMul M G]
    [SMulCommClass S M G] (h : V.IsRelativelyBounded A a b) (c : M) :
    (c • V).IsRelativelyBounded A (‖c‖ * a) (‖c‖ * b) where
  domain_le := h.domain_le
  norm_apply_le x := by
    rw [smul_apply]
    calc ‖c • V ⟨x, h.domain_le x.property⟩‖ ≤ ‖c‖ * (a * ‖(x : E)‖ + b * ‖A x‖) :=
          (norm_smul_le _ _).trans (by gcongr; exact h.norm_apply_le x)
      _ = _ := by ring

/-- If `V` is `A`-bounded with `A`-bound `b < 1`, then `A` is `(A + V)`-bounded: the graph norm
of `A + V` dominates that of `A` up to a constant factor. -/
theorem isRelativelyBounded_self_add {V : E →ₛₗ.[τ] F} (h : V.IsRelativelyBounded A a b)
    (hb : b < 1) : A.IsRelativelyBounded (A + V) (a / (1 - b)) (1 - b)⁻¹ where
  domain_le := h.domain_add.le
  norm_apply_le x := by
    let y : A.domain := ⟨x, h.domain_add.le x.property⟩
    have hAV : (A + V) x = A y + V ⟨x, h.domain_le y.property⟩ := add_apply A V x
    have hVy : ‖V ⟨x, h.domain_le y.property⟩‖ ≤ a * ‖(x : E)‖ + b * ‖A y‖ := h.norm_apply_le y
    have h₁ : ‖A y‖ ≤ ‖(A + V) x‖ + ‖V ⟨x, h.domain_le y.property⟩‖ := by
      rw [hAV]
      exact norm_le_add_norm_add _ _
    have h₂ : (1 - b) * ‖A y‖ ≤ a * ‖(x : E)‖ + ‖(A + V) x‖ := by linarith
    have hb' : 0 < 1 - b := by linarith
    have hsum : a / (1 - b) * ‖(x : E)‖ + (1 - b)⁻¹ * ‖(A + V) x‖ =
        (a * ‖(x : E)‖ + ‖(A + V) x‖) / (1 - b) := by ring
    rw [hsum, le_div_iff₀' hb']
    exact h₂

end IsRelativelyBounded

/-- The zero map is relatively bounded with constants `0, 0`. -/
theorem isRelativelyBounded_zero (A : E →ₛₗ.[τ] F) :
    (0 : E →ₛₗ.[σ] G).IsRelativelyBounded A 0 0 where
  domain_le := le_top
  norm_apply_le x := by simp

section Normalized

variable {𝕜 E F G : Type*} [NormedField 𝕜] [NormedAlgebra ℝ 𝕜] [NormedAddCommGroup E]
  [NormedSpace 𝕜 E] [SeminormedAddCommGroup F] [NormedSpace 𝕜 F] [SeminormedAddCommGroup G]
  [NormedSpace 𝕜 G]

/-- If a relative bound fails, it fails at a vector of graph norm `‖x‖ + ‖A x‖ = 1`. -/
theorem exists_normalized_of_not_isRelativelyBounded {A : E →ₗ.[𝕜] F} {V : E →ₗ.[𝕜] G}
    (hle : A.domain ≤ V.domain) {a b : ℝ} (h : ¬ V.IsRelativelyBounded A a b) :
    ∃ u : A.domain, ‖(u : E)‖ + ‖A u‖ = 1 ∧
      a * ‖(u : E)‖ + b * ‖A u‖ < ‖V ⟨u, hle u.property⟩‖ := by
  obtain ⟨x, hx⟩ : ∃ x : A.domain, a * ‖(x : E)‖ + b * ‖A x‖ < ‖V ⟨x, hle x.property⟩‖ := by
    by_contra! hall
    exact h ⟨hle, hall⟩
  have hx0 : (x : E) ≠ 0 := by
    intro h0
    have hV0 : V ⟨x, hle x.property⟩ = 0 := by
      rw [← V.map_zero]
      exact congrArg V (Subtype.ext h0)
    have hA0 : A x = 0 := by
      rw [← A.map_zero]
      exact congrArg A (Subtype.ext h0)
    rw [hV0, hA0, h0] at hx
    simp at hx
  set s := ‖(x : E)‖ + ‖A x‖
  have hs : 0 < s := by positivity
  set c : 𝕜 := algebraMap ℝ 𝕜 s⁻¹
  have hc : ‖c‖ = s⁻¹ := by rw [norm_algebraMap', Real.norm_of_nonneg (inv_nonneg.2 hs.le)]
  have hV : V ⟨((c • x : A.domain) : E), hle (c • x).property⟩ = c • V ⟨x, hle x.property⟩ := by
    rw [← V.map_smul]
    exact congrArg V (Subtype.ext (by simp))
  refine ⟨c • x, ?_, ?_⟩
  · rw [A.map_smul, Submodule.coe_smul, norm_smul, norm_smul, hc, ← mul_add]
    exact inv_mul_cancel₀ hs.ne'
  · rw [hV, A.map_smul, Submodule.coe_smul, norm_smul, norm_smul, norm_smul, hc]
    have := mul_lt_mul_of_pos_left hx (inv_pos.2 hs)
    linarith

end Normalized

section Dual

variable {𝕜 E F G : Type*} [NontriviallyNormedField 𝕜] [IsRCLikeNormedField 𝕜]
  [SeminormedAddCommGroup E] [NormedSpace 𝕜 E] [SeminormedAddCommGroup F] [NormedSpace 𝕜 F]
  [SeminormedAddCommGroup G] [NormedSpace 𝕜 G]

/-- For an `A`-bounded `V`, every functional of `V x` is a continuous functional of `(x, A x)`,
by Hahn–Banach on the graph of `A`. -/
theorem exists_dual_apply_eq_of_isRelativelyBounded {A : E →ₗ.[𝕜] F} {V : E →ₗ.[𝕜] G}
    {a b : ℝ} (hV : V.IsRelativelyBounded A a b) (f : StrongDual 𝕜 G) :
    ∃ g : StrongDual 𝕜 (E × F), ∀ x : A.domain,
      f (V ⟨x, hV.domain_le x.property⟩) = g ((x : E), A x) := by
  let L : A.domain →ₗ[𝕜] E × F := A.domain.subtype.prod A.toFun
  have hL : Function.Injective L := fun x y h ↦ Subtype.ext (congrArg Prod.fst h)
  let Φ : A.domain →ₗ[𝕜] 𝕜 :=
    (f : G →ₗ[𝕜] 𝕜) ∘ₗ V.toFun ∘ₗ Submodule.inclusion hV.domain_le
  let ψ : LinearMap.range L →ₗ[𝕜] 𝕜 := Φ ∘ₗ (LinearEquiv.ofInjective L hL).symm.toLinearMap
  have hψ (x : A.domain) : ψ ⟨L x, x, rfl⟩ = f (V ⟨x, hV.domain_le x.property⟩) := by
    have hx : (LinearEquiv.ofInjective L hL).symm ⟨L x, x, rfl⟩ = x :=
      (LinearEquiv.ofInjective L hL).symm_apply_eq.2
        (Subtype.ext (LinearEquiv.ofInjective_apply L x).symm)
    simp only [ψ, Φ, LinearMap.comp_apply, LinearEquiv.coe_coe, hx, ContinuousLinearMap.coe_coe,
      LinearPMap.toFun_eq_coe, Submodule.inclusion_apply]
  have hbound (s : LinearMap.range L) : ‖ψ s‖ ≤ ‖f‖ * (|a| + |b|) * ‖s‖ := by
    obtain ⟨_, x, rfl⟩ := s
    have hLx : L x = ((x : E), A x) := by simp [L]
    have hn : ‖(⟨L x, x, rfl⟩ : LinearMap.range L)‖ = max ‖(x : E)‖ ‖A x‖ := by
      rw [← Submodule.norm_coe]
      dsimp only
      rw [hLx, Prod.norm_def]
    rw [hψ, hn]
    refine (f.le_opNorm _).trans ?_
    rw [mul_assoc]
    gcongr
    exact hV.norm_apply_le_abs_add_abs_mul_max x
  obtain ⟨g, hg, -⟩ := exists_extension_norm_eq (LinearMap.range L) (ψ.mkContinuous _ hbound)
  refine ⟨g, fun x ↦ ?_⟩
  rw [← hψ, ← LinearMap.mkContinuous_apply ψ _ hbound, ← hg]
  simp [L]

end Dual

end LinearPMap

namespace ContinuousLinearMap

variable {𝕜 𝕜₂ R E F G : Type*} [NontriviallyNormedField 𝕜] [NontriviallyNormedField 𝕜₂] [Ring R]
  {σ : 𝕜 →+* 𝕜₂} [RingHomIsometric σ] {τ : 𝕜 →+* R}
  [SeminormedAddCommGroup E] [NormedSpace 𝕜 E] [SeminormedAddCommGroup F] [Module R F]
  [SeminormedAddCommGroup G] [NormedSpace 𝕜₂ G]

/-- The restriction of a bounded operator `T` to a subspace `p` containing the domain of a partial
linear map `A` is relatively bounded with respect to `A`, with constants `‖T‖, 0`. -/
theorem isRelativelyBounded_toPMap (T : E →SL[σ] G) {A : E →ₛₗ.[τ] F} {p : Submodule 𝕜 E}
    (hp : A.domain ≤ p) : ((T : E →ₛₗ[σ] G).toPMap p).IsRelativelyBounded A ‖T‖ 0 where
  domain_le := hp
  norm_apply_le x := by simpa using T.le_opNorm x

end ContinuousLinearMap
