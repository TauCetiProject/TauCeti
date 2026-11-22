/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Operator.Compact.Basic
public import TauCeti.Analysis.Normed.Operator.LinearPMap.Relative.Bound
public import TauCeti.Topology.Algebra.Module.LinearPMap.Resolvent.Basic

/-!
# Relatively compact partial linear maps

A partial linear map `V` is *relatively compact* with respect to a partial linear map `A`
(*`A`-compact*) when the domain of `A` lies in the domain of `V` and `V` maps every set of the
domain of `A` that is bounded for the graph norm `‖x‖ + ‖A x‖` into a compact set (Kato,
§IV.1.3). At a point `z` of the resolvent set of `A` this says exactly that `dom A ⊆ dom V` and
`V (z I - A)⁻¹` is a compact operator
(`LinearPMap.isRelativelyCompact_iff_isCompactOperator_compResolvent`), which is the form used by
Teschl.

The perturbation theory of this file is the part of Kato's relative-compactness theory that
needs no Hilbert-space structure:

* relative compactness is stable under sums, negation, differences and scalar multiplication,
  passes to extensions of `V` and restrictions of `A`, and the restriction of a compact operator
  to a subspace containing `dom A` is `A`-compact;
* an `A`-compact map stays compact relative to every `B` for which `A` is `B`-bounded
  (`LinearPMap.IsRelativelyCompact.of_isRelativelyBounded`), in particular relative to `A + V`
  when `V` is `A`-bounded with `A`-bound less than one
  (`LinearPMap.IsRelativelyCompact.add_right_of_isRelativelyBounded`);
* for an `A`-compact `V` the resolvents of `A + V` and `A` differ by a compact operator at every
  common resolvent point (`LinearPMap.IsRelativelyCompact.isCompactOperator_resolvent_add_sub`),
  through the second resolvent identity `R_{A+V}(z) - R_A(z) = R_{A+V}(z) V R_A(z)`
  (`LinearPMap.resolvent_add_sub_apply`, in
  `TauCeti.Topology.Algebra.Module.LinearPMap.Resolvent.Basic`).

That an `A`-compact map has `A`-bound zero when `A` is closable on Hilbert spaces, so that
symmetric relatively compact perturbations preserve self-adjointness, is in
`TauCeti.Analysis.InnerProductSpace.LinearPMap.RelativeCompact`.

## Main declarations

* `LinearPMap.IsRelativelyCompact V A`: `V` is `A`-compact, and
  `LinearPMap.isRelativelyCompact_iff_exists_isCompact_of_pos`: one radius suffices.
* `LinearPMap.isRelativelyCompact_iff_isCompactOperator_compResolvent`: the resolvent
  characterization, and `LinearPMap.IsRelativelyCompact.exists_isCompactOperator_compResolvent`,
  its bundled compact operator.
* `LinearPMap.IsRelativelyCompact.add`, `.neg`, `.sub`, `.smul`,
  `LinearPMap.isRelativelyCompact_zero`, `LinearPMap.isRelativelyCompact_neg_iff`,
  `LinearPMap.isRelativelyCompact_neg_right_iff` and
  `IsCompactOperator.isRelativelyCompact_toPMap`: the linear calculus and bounded compact maps.
* `LinearPMap.IsRelativelyCompact.mono_left`, `.mono_right`, `.of_isRelativelyBounded` and
  `.add_right_of_isRelativelyBounded`: changing `V` and `A`.
* `LinearPMap.IsRelativelyCompact.exists_isRelativelyBounded_const`: an `A`-compact map is
  `A`-bounded.
* `LinearPMap.IsRelativelyCompact.isCompactOperator_resolvent_add_sub`: compactness of the
  resolvent difference.

## References

* T. Kato, *Perturbation Theory for Linear Operators*, 2nd ed., Springer (1976), §IV.1.3.
* G. Teschl, *Mathematical Methods in Quantum Mechanics*, AMS (2009), §6.5.
-/

public section

open Pointwise

namespace LinearPMap

section Definition

variable {R S T U E F G H : Type*} [Ring R] [Ring S] [Ring T] [Ring U] {σ : R →+* S}
  {τ : R →+* T} {ρ : R →+* U}
  [SeminormedAddCommGroup E] [Module R E] [SeminormedAddCommGroup F] [Module T F]
  [AddCommGroup G] [TopologicalSpace G] [Module S G] [SeminormedAddCommGroup H] [Module U H]

/-- A partial linear map `V` is *relatively compact* with respect to `A`, or *`A`-compact*, when
`A.domain ≤ V.domain` and, for every `C`, the values of `V` on the vectors `x` of the domain of
`A` with `‖x‖ + ‖A x‖ ≤ C` lie in a compact set. -/
structure IsRelativelyCompact (V : E →ₛₗ.[σ] G) (A : E →ₛₗ.[τ] F) : Prop where
  /-- The domain of `A` lies in the domain of `V`. -/
  domain_le : A.domain ≤ V.domain
  /-- `V` maps sets of `dom A` that are bounded in the graph norm into compact sets. -/
  exists_isCompact (C : ℝ) : ∃ K : Set G, IsCompact K ∧
    ∀ x : A.domain, ‖(x : E)‖ + ‖A x‖ ≤ C → V ⟨x, domain_le x.property⟩ ∈ K

/-- The zero map is relatively compact with respect to every partial linear map. -/
@[simp]
theorem isRelativelyCompact_zero (A : E →ₛₗ.[τ] F) : (0 : E →ₛₗ.[σ] G).IsRelativelyCompact A where
  domain_le := le_top
  exists_isCompact _ := ⟨{0}, isCompact_singleton, fun _ _ ↦ by simp⟩

namespace IsRelativelyCompact

variable {V W : E →ₛₗ.[σ] G} {A : E →ₛₗ.[τ] F}

/-- If `V` is `A`-compact, then `A + V` has the same domain as `A`. -/
theorem domain_add {V : E →ₛₗ.[τ] F} (hV : V.IsRelativelyCompact A) :
    (A + V).domain = A.domain :=
  inf_eq_left.2 hV.domain_le

/-- Relative compactness is stable under sums. -/
theorem add [ContinuousAdd G] (hV : V.IsRelativelyCompact A) (hW : W.IsRelativelyCompact A) :
    (V + W).IsRelativelyCompact A where
  domain_le := le_inf hV.domain_le hW.domain_le
  exists_isCompact C := by
    obtain ⟨K, hK, hKV⟩ := hV.exists_isCompact C
    obtain ⟨L, hL, hLW⟩ := hW.exists_isCompact C
    exact ⟨K + L, hK.add hL, fun x hx ↦ by
      rw [add_apply]
      exact Set.add_mem_add (hKV x hx) (hLW x hx)⟩

/-- Relative compactness is stable under negation. -/
theorem neg [ContinuousNeg G] (hV : V.IsRelativelyCompact A) : (-V).IsRelativelyCompact A where
  domain_le := hV.domain_le
  exists_isCompact C := by
    obtain ⟨K, hK, hKV⟩ := hV.exists_isCompact C
    exact ⟨-K, hK.neg, fun x hx ↦ by
      rw [neg_apply]
      exact Set.neg_mem_neg.2 (hKV x hx)⟩

/-- Relative compactness is stable under differences. -/
theorem sub [IsTopologicalAddGroup G] (hV : V.IsRelativelyCompact A)
    (hW : W.IsRelativelyCompact A) : (V - W).IsRelativelyCompact A :=
  sub_eq_add_neg V W ▸ hV.add hW.neg

/-- Relative compactness is stable under scalar multiplication. -/
theorem smul {M : Type*} [Monoid M] [DistribMulAction M G] [ContinuousConstSMul M G]
    [SMulCommClass S M G] (hV : V.IsRelativelyCompact A) (c : M) :
    (c • V).IsRelativelyCompact A where
  domain_le := hV.domain_le
  exists_isCompact C := by
    obtain ⟨K, hK, hKV⟩ := hV.exists_isCompact C
    exact ⟨c • K, hK.smul c, fun x hx ↦ by
      rw [smul_apply]
      exact Set.smul_mem_smul_set (hKV x hx)⟩

/-- An extension of an `A`-compact map is `A`-compact. -/
theorem mono_left {V' : E →ₛₗ.[σ] G} (hV : V.IsRelativelyCompact A) (h : V ≤ V') :
    V'.IsRelativelyCompact A where
  domain_le := hV.domain_le.trans h.1
  exists_isCompact C := by
    obtain ⟨K, hK, hKV⟩ := hV.exists_isCompact C
    exact ⟨K, hK, fun x hx ↦ by
      rw [← h.2 (x := ⟨x, hV.domain_le x.property⟩) rfl]
      exact hKV x hx⟩

/-- **Relative compactness passes along relative bounds.** If `W` is `A`-compact and `A` is
`B`-bounded, then `W` is `B`-compact. -/
theorem of_isRelativelyBounded (hW : W.IsRelativelyCompact A) {B : E →ₛₗ.[ρ] H} {a b : ℝ}
    (hA : A.IsRelativelyBounded B a b) : W.IsRelativelyCompact B where
  domain_le := hA.domain_le.trans hW.domain_le
  exists_isCompact C := by
    set C₀ := max C 0
    obtain ⟨K, hK, hKW⟩ := hW.exists_isCompact ((1 + |a| + |b|) * C₀)
    refine ⟨K, hK, fun x hx ↦ hKW ⟨x, hA.domain_le x.property⟩ ?_⟩
    have hx₀ : ‖(x : E)‖ ≤ C₀ := le_max_of_le_left (by linarith [norm_nonneg (B x)])
    have hBx : ‖B x‖ ≤ C₀ := le_max_of_le_left (by linarith [norm_nonneg (x : E)])
    have hAx := hA.norm_apply_le x
    have h₁ : a * ‖(x : E)‖ ≤ |a| * C₀ :=
      (mul_le_mul_of_nonneg_right (le_abs_self a) (norm_nonneg _)).trans
        (mul_le_mul_of_nonneg_left hx₀ (abs_nonneg a))
    have h₂ : b * ‖B x‖ ≤ |b| * C₀ :=
      (mul_le_mul_of_nonneg_right (le_abs_self b) (norm_nonneg _)).trans
        (mul_le_mul_of_nonneg_left hBx (abs_nonneg b))
    simp only at hAx ⊢
    nlinarith

/-- A map compact relative to `A` is compact relative to every restriction of `A`. -/
theorem mono_right (hV : V.IsRelativelyCompact A) {A' : E →ₛₗ.[τ] F} (h : A' ≤ A) :
    V.IsRelativelyCompact A' :=
  hV.of_isRelativelyBounded (a := 0) (b := 1)
    { domain_le := h.1
      norm_apply_le x := by
        rw [← h.2 (x := x) (y := ⟨x, h.1 x.property⟩) rfl]
        simp }

/-- **Relative compactness survives a perturbation of relative bound less than one.** If `W` is
`A`-compact and `V` is `A`-bounded, `‖V x‖ ≤ a ‖x‖ + b ‖A x‖` with `b < 1`, then `W` is
`(A + V)`-compact. -/
theorem add_right_of_isRelativelyBounded (hW : W.IsRelativelyCompact A) {V : E →ₛₗ.[τ] F}
    {a b : ℝ} (hV : V.IsRelativelyBounded A a b) (hb : b < 1) : W.IsRelativelyCompact (A + V) :=
  hW.of_isRelativelyBounded (hV.isRelativelyBounded_self_add hb)

end IsRelativelyCompact

variable {V : E →ₛₗ.[σ] G} {A : E →ₛₗ.[τ] F}

/-- Negating `V` does not change relative compactness. -/
@[simp]
theorem isRelativelyCompact_neg_iff [ContinuousNeg G] :
    (-V).IsRelativelyCompact A ↔ V.IsRelativelyCompact A :=
  ⟨fun h ↦ neg_neg V ▸ h.neg, .neg⟩

/-- Negating `A` does not change relative compactness. -/
@[simp]
theorem isRelativelyCompact_neg_right_iff :
    V.IsRelativelyCompact (-A) ↔ V.IsRelativelyCompact A := by
  have key (B : E →ₛₗ.[τ] F) : B.IsRelativelyBounded (-B) 0 1 :=
    { domain_le := le_rfl
      norm_apply_le x := by simp [neg_apply] }
  exact ⟨fun h ↦ neg_neg A ▸ h.of_isRelativelyBounded (key (-A)),
    fun h ↦ h.of_isRelativelyBounded (key A)⟩

end Definition

section Radius

variable {𝕜 E F G : Type*} [NontriviallyNormedField 𝕜] [SeminormedAddCommGroup E]
  [NormedSpace 𝕜 E] [SeminormedAddCommGroup F] [NormedSpace 𝕜 F] [AddCommGroup G]
  [TopologicalSpace G] [Module 𝕜 G] [ContinuousConstSMul 𝕜 G] {V : E →ₗ.[𝕜] G} {A : E →ₗ.[𝕜] F}

/-- **One radius suffices for relative compactness.** For any `r > 0`, the map `V` is `A`-compact
exactly when `dom A ⊆ dom V` and `V` maps the vectors of graph norm at most `r` into a compact
set. -/
theorem isRelativelyCompact_iff_exists_isCompact_of_pos {r : ℝ} (hr : 0 < r) :
    V.IsRelativelyCompact A ↔ ∃ h : A.domain ≤ V.domain, ∃ K : Set G, IsCompact K ∧
      ∀ x : A.domain, ‖(x : E)‖ + ‖A x‖ ≤ r → V ⟨x, h x.property⟩ ∈ K := by
  refine ⟨fun hV ↦ ⟨hV.domain_le, hV.exists_isCompact r⟩, fun ⟨h, K, hK, hKV⟩ ↦ ⟨h, fun C ↦ ?_⟩⟩
  obtain ⟨c, hc⟩ := NormedField.exists_lt_norm 𝕜 (max (C / r) 0)
  have hc0 : 0 < ‖c‖ := (le_max_right _ _).trans_lt hc
  have hc' : c ≠ 0 := norm_pos_iff.1 hc0
  have hCr : C ≤ ‖c‖ * r := (div_le_iff₀ hr).1 ((le_max_left (C / r) 0).trans hc.le)
  refine ⟨c • K, hK.smul c, fun x hx ↦ ?_⟩
  set y : A.domain := c⁻¹ • x
  have hy : ‖(y : E)‖ + ‖A y‖ ≤ r := by
    rw [A.map_smul, Submodule.coe_smul, norm_smul, norm_smul, ← mul_add, norm_inv,
      inv_mul_le_iff₀ hc0]
    linarith
  have hVx : V ⟨x, h x.property⟩ = c • V ⟨y, h y.property⟩ := by
    rw [← V.map_smul]
    exact congrArg V (Subtype.ext (by simp [y, smul_smul, mul_inv_cancel₀ hc']))
  rw [hVx]
  exact Set.smul_mem_smul_set (hKV y hy)

end Radius

section Bounded

variable {𝕜 E F G : Type*} [NormedField 𝕜] [NormedAlgebra ℝ 𝕜] [NormedAddCommGroup E]
  [NormedSpace 𝕜 E] [SeminormedAddCommGroup F] [NormedSpace 𝕜 F] [SeminormedAddCommGroup G]
  [NormedSpace 𝕜 G] {V : E →ₗ.[𝕜] G} {A : E →ₗ.[𝕜] F}

/-- A relatively compact map is relatively bounded, with equal constants. -/
theorem IsRelativelyCompact.exists_isRelativelyBounded_const (hV : V.IsRelativelyCompact A) :
    ∃ M, V.IsRelativelyBounded A M M := by
  obtain ⟨K, hK, hKV⟩ := hV.exists_isCompact 1
  obtain ⟨M, hM⟩ := hK.isBounded.exists_norm_le
  refine ⟨M, by_contra fun h ↦ ?_⟩
  obtain ⟨u, hu1, hu2⟩ := exists_normalized_of_not_isRelativelyBounded hV.domain_le h
  have := hM _ (hKV u hu1.le)
  rw [← mul_add, hu1, mul_one] at hu2
  linarith

end Bounded

section Resolvent

variable {𝕜 𝕜₂ E G : Type*} [NontriviallyNormedField 𝕜] [SeminormedAddCommGroup E]
  [NormedSpace 𝕜 E] {A : E →ₗ.[𝕜] E} {z : 𝕜}

section Characterization

variable [SeminormedRing 𝕜₂] {σ : 𝕜 →+* 𝕜₂} [AddCommGroup G] [TopologicalSpace G]
  [Module 𝕜₂ G] [ContinuousConstSMul 𝕜₂ G] {V : E →ₛₗ.[σ] G}

/-- **The resolvent characterization of relative compactness.** At a point `z` of the resolvent
set of `A`, the map `V` is `A`-compact exactly when `dom A ⊆ dom V` and `V (z I - A)⁻¹` is a
compact operator. -/
theorem isRelativelyCompact_iff_isCompactOperator_compResolvent (hz : z ∈ A.resolventSet) :
    V.IsRelativelyCompact A ↔
      ∃ h : A.domain ≤ V.domain, IsCompactOperator (compResolvent h hz) := by
  set R := A.resolvent z
  constructor
  · intro hV
    refine ⟨hV.domain_le, ?_⟩
    obtain ⟨K, hK, hKV⟩ := hV.exists_isCompact (‖R‖ + (‖z‖ * ‖R‖ + 1))
    refine (isCompactOperator_iff_image_ball_subset_compact (compResolvent hV.domain_le hz)
      one_pos).2 ⟨K, hK, ?_⟩
    rintro _ ⟨y, hy, rfl⟩
    rw [mem_ball_zero_iff] at hy
    rw [compResolvent_apply]
    refine hKV ⟨R y, resolvent_mem_domain hz y⟩ ?_
    have hRy : ‖R y‖ ≤ ‖R‖ := (R.le_opNorm y).trans (by nlinarith [norm_nonneg R])
    rw [apply_resolvent hz]
    calc ‖R y‖ + ‖z • R y - y‖ ≤ ‖R y‖ + (‖z‖ * ‖R y‖ + ‖y‖) := by
          gcongr
          exact (norm_sub_le _ _).trans (by rw [norm_smul])
      _ ≤ ‖R‖ + (‖z‖ * ‖R‖ + 1) := by gcongr
  · rintro ⟨h, hc⟩
    refine ⟨h, fun C ↦ ?_⟩
    obtain ⟨K, hK, hKV⟩ := hc.image_closedBall_subset_compact ((‖z‖ + 1) * C)
    refine ⟨K, hK, fun x hx ↦ hKV ⟨z • (x : E) - A x, ?_, ?_⟩⟩
    · rw [mem_closedBall_zero_iff]
      calc ‖z • (x : E) - A x‖ ≤ ‖z‖ * ‖(x : E)‖ + ‖A x‖ :=
            (norm_sub_le _ _).trans (by rw [norm_smul])
        _ ≤ (‖z‖ + 1) * (‖(x : E)‖ + ‖A x‖) := by
            nlinarith [norm_nonneg z, norm_nonneg (x : E), norm_nonneg (A x)]
        _ ≤ (‖z‖ + 1) * C := by gcongr
    · rw [compResolvent_apply]
      congr 2
      exact resolvent_smul_sub_apply hz x

end Characterization

/-- At a point `z` of the resolvent set of `A`, an `A`-compact map `V` composed with the
resolvent `(z I - A)⁻¹` is a compact operator `K : E →SL[σ] G`. -/
theorem IsRelativelyCompact.exists_isCompactOperator_compResolvent [NontriviallyNormedField 𝕜₂]
    {σ : 𝕜 →+* 𝕜₂} [RingHomIsometric σ] [AddCommGroup G] [TopologicalSpace G] [Module 𝕜₂ G]
    [IsTopologicalAddGroup G] [ContinuousSMul 𝕜₂ G] {V : E →ₛₗ.[σ] G}
    (hV : V.IsRelativelyCompact A) (hz : z ∈ A.resolventSet) :
    ∃ K : E →SL[σ] G, IsCompactOperator K ∧
      ∀ y, V ⟨A.resolvent z y, hV.domain_le (resolvent_mem_domain hz y)⟩ = K y := by
  obtain ⟨h, hc⟩ := (isRelativelyCompact_iff_isCompactOperator_compResolvent hz).1 hV
  refine ⟨.mkOfIsCompactOperator hc, ?_, fun y ↦ ?_⟩
  · rw [ContinuousLinearMap.coe_mkOfIsCompactOperator]
    exact hc
  · rw [ContinuousLinearMap.coe_mkOfIsCompactOperator, compResolvent_apply]

/-- **Compact resolvent difference.** If `V : E →ₗ.[𝕜] E` is `A`-compact, then at every point `z`
of the resolvent sets of both `A` and `A + V` the difference `R_{A+V}(z) - R_A(z)` is a compact
operator. -/
theorem IsRelativelyCompact.isCompactOperator_resolvent_add_sub {V : E →ₗ.[𝕜] E}
    (hV : V.IsRelativelyCompact A) (hz : z ∈ A.resolventSet) (hz' : z ∈ (A + V).resolventSet) :
    IsCompactOperator ((A + V).resolvent z - A.resolvent z) := by
  obtain ⟨h, hc⟩ := (isRelativelyCompact_iff_isCompactOperator_compResolvent hz).1 hV
  have heq : ⇑((A + V).resolvent z - A.resolvent z) =
      (A + V).resolvent z ∘ compResolvent h hz :=
    funext (resolvent_add_sub_apply h hz hz')
  rw [heq]
  exact hc.clm_comp ((A + V).resolvent z)

end Resolvent

end LinearPMap

namespace IsCompactOperator

variable {𝕜 𝕜₂ R E F G : Type*} [NontriviallyNormedField 𝕜] [SeminormedRing 𝕜₂] [Ring R]
  {σ : 𝕜 →+* 𝕜₂} {τ : 𝕜 →+* R}
  [SeminormedAddCommGroup E] [NormedSpace 𝕜 E] [SeminormedAddCommGroup F] [Module R F]
  [AddCommGroup G] [TopologicalSpace G] [Module 𝕜₂ G] [ContinuousConstSMul 𝕜₂ G]

/-- The restriction of a compact operator `T` to a subspace containing the domain of `A` is
`A`-compact. -/
theorem isRelativelyCompact_toPMap {T : E →ₛₗ[σ] G} (hT : IsCompactOperator T)
    {A : E →ₛₗ.[τ] F} {p : Submodule 𝕜 E} (hp : A.domain ≤ p) :
    (T.toPMap p).IsRelativelyCompact A where
  domain_le := hp
  exists_isCompact C := by
    obtain ⟨K, hK, hKT⟩ := hT.image_closedBall_subset_compact C
    exact ⟨K, hK, fun x hx ↦ hKT ⟨x, mem_closedBall_zero_iff.2 (by linarith [norm_nonneg (A x)]),
      (T.toPMap_apply p ⟨x, hp x.property⟩).symm⟩⟩

end IsCompactOperator
