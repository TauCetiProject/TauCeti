/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Operator.Compact.Basic
public import TauCeti.Analysis.Normed.Operator.LinearPMap.RelativeBound
public import TauCeti.Topology.Algebra.Module.LinearPMap.Resolvent.Basic

/-!
# Relatively compact partial linear maps

A partial linear map `V` is *relatively compact* with respect to a partial linear map `A`
(*`A`-compact*) when the domain of `A` lies in the domain of `V` and `V` maps every set of the
domain of `A` that is bounded for the graph norm `‖x‖ + ‖A x‖` into a compact set (Kato,
§IV.1.3). At a point `z` of the resolvent set of `A` this says exactly that `dom A ⊆ dom V` and
`V (z I - A)⁻¹` is a compact operator (`LinearPMap.isRelativelyCompact_iff_isCompactOperator`),
which is the form used by Teschl.

The perturbation theory of this file is the part of Kato's relative-compactness theory that
needs no Hilbert-space structure:

* relative compactness is stable under sums, negation and differences, and the restriction of a
  compact operator to a subspace containing `dom A` is `A`-compact;
* an `A`-compact map stays compact relative to `A + V` when `V` is `A`-bounded with `A`-bound
  less than one, because the graph norms of `A` and `A + V` are then equivalent
  (`LinearPMap.IsRelativelyCompact.add_of_isRelativelyBounded`);
* for an `A`-compact `V` the resolvents of `A + V` and `A` differ by a compact operator at every
  common resolvent point (`LinearPMap.IsRelativelyCompact.isCompactOperator_resolvent_add_sub`):
  `R_{A+V}(z) - R_A(z) = R_{A+V}(z) V R_A(z)`.

That an `A`-compact map has `A`-bound zero on a Hilbert space, so that symmetric relatively
compact perturbations preserve self-adjointness, is in
`TauCeti.Analysis.InnerProductSpace.LinearPMap.RelativeCompact`.

## Main declarations

* `LinearPMap.IsRelativelyCompact V A`: `V` is `A`-compact.
* `LinearPMap.isRelativelyCompact_iff_isCompactOperator`: the resolvent characterization, and
  `LinearPMap.IsRelativelyCompact.exists_isCompactOperator`, its bundled compact operator.
* `LinearPMap.IsRelativelyCompact.add`, `.neg`, `.sub`, `LinearPMap.isRelativelyCompact_zero` and
  `IsCompactOperator.isRelativelyCompact_toPMap`: the linear calculus and bounded compact maps.
* `LinearPMap.IsRelativelyCompact.add_of_isRelativelyBounded`: stability under perturbations of
  `A` with relative bound less than one.
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

variable {R S T E F G : Type*} [Ring R] [Ring S] [Ring T] {σ : R →+* S} {τ : R →+* T}
  [SeminormedAddCommGroup E] [Module R E] [SeminormedAddCommGroup F] [Module T F]
  [SeminormedAddCommGroup G] [Module S G]

/-- A partial linear map `V` is *relatively compact* with respect to `A`, or *`A`-compact*, when
`A.domain ≤ V.domain` and, for every `C`, the values of `V` on the vectors `x` of the domain of
`A` with `‖x‖ + ‖A x‖ ≤ C` lie in a compact set. -/
structure IsRelativelyCompact (V : E →ₛₗ.[σ] G) (A : E →ₛₗ.[τ] F) : Prop where
  /-- The domain of `A` lies in the domain of `V`. -/
  domain_le : A.domain ≤ V.domain
  /-- `V` maps sets of `dom A` that are bounded in the graph norm into compact sets. -/
  exists_isCompact (C : ℝ) : ∃ K : Set G, IsCompact K ∧
    ∀ x : A.domain, ‖(x : E)‖ + ‖A x‖ ≤ C → V ⟨x, domain_le x.2⟩ ∈ K

/-- The zero map is relatively compact with respect to every partial linear map. -/
theorem isRelativelyCompact_zero (A : E →ₛₗ.[τ] F) : (0 : E →ₛₗ.[σ] G).IsRelativelyCompact A where
  domain_le := le_top
  exists_isCompact _ := ⟨{0}, isCompact_singleton, fun _ _ ↦ rfl⟩

namespace IsRelativelyCompact

variable {V W : E →ₛₗ.[σ] G} {A : E →ₛₗ.[τ] F}

/-- Relative compactness is stable under sums. -/
theorem add (hV : V.IsRelativelyCompact A) (hW : W.IsRelativelyCompact A) :
    (V + W).IsRelativelyCompact A where
  domain_le := le_inf hV.domain_le hW.domain_le
  exists_isCompact C := by
    obtain ⟨K, hK, hKV⟩ := hV.exists_isCompact C
    obtain ⟨L, hL, hLW⟩ := hW.exists_isCompact C
    exact ⟨K + L, hK.add hL, fun x hx ↦ by
      rw [add_apply]
      exact Set.add_mem_add (hKV x hx) (hLW x hx)⟩

/-- Relative compactness is stable under negation. -/
theorem neg (hV : V.IsRelativelyCompact A) : (-V).IsRelativelyCompact A where
  domain_le := hV.domain_le
  exists_isCompact C := by
    obtain ⟨K, hK, hKV⟩ := hV.exists_isCompact C
    exact ⟨-K, hK.neg, fun x hx ↦ by
      rw [neg_apply]
      exact Set.neg_mem_neg.2 (hKV x hx)⟩

/-- Relative compactness is stable under differences. -/
theorem sub (hV : V.IsRelativelyCompact A) (hW : W.IsRelativelyCompact A) :
    (V - W).IsRelativelyCompact A :=
  sub_eq_add_neg V W ▸ hV.add hW.neg

/-- **Relative compactness survives a perturbation of relative bound less than one.** If `W` is
`A`-compact and `V` is `A`-bounded, `‖V x‖ ≤ a ‖x‖ + b ‖A x‖` with `b < 1`, then `W` is
`(A + V)`-compact: the graph norm of `A + V` dominates that of `A`. -/
theorem add_of_isRelativelyBounded (hW : W.IsRelativelyCompact A) {V : E →ₛₗ.[τ] F} {a b : ℝ}
    (hV : V.IsRelativelyBounded A a b) (hb : b < 1) : W.IsRelativelyCompact (A + V) where
  domain_le := hV.domain_add.le.trans hW.domain_le
  exists_isCompact C := by
    set C₀ := max C 0
    obtain ⟨K, hK, hKW⟩ := hW.exists_isCompact (C₀ + (1 + |a|) * C₀ / (1 - b))
    refine ⟨K, hK, fun x hx ↦ ?_⟩
    let y : A.domain := ⟨x, hV.domain_add.le x.2⟩
    have hAV : (A + V) x = A y + V ⟨x, hV.domain_le y.2⟩ := add_apply A V x
    have hx₀ : ‖(x : E)‖ ≤ C₀ := le_max_of_le_left (by linarith [norm_nonneg ((A + V) x)])
    have hAVx : ‖(A + V) x‖ ≤ C₀ := le_max_of_le_left (by linarith [norm_nonneg (x : E)])
    have hVy := hV.norm_apply_le y
    have hAy : (1 - b) * ‖A y‖ ≤ (1 + |a|) * C₀ := by
      have h₁ : ‖A y‖ ≤ ‖(A + V) x‖ + ‖V ⟨x, hV.domain_le y.2⟩‖ := by
        rw [hAV]
        calc ‖A y‖ = ‖(A y + V ⟨x, hV.domain_le y.2⟩) - V ⟨x, hV.domain_le y.2⟩‖ := by
              rw [add_sub_cancel_right]
          _ ≤ _ := norm_sub_le _ _
      have h₂ : a * ‖(x : E)‖ ≤ |a| * C₀ :=
        (mul_le_mul_of_nonneg_right (le_abs_self a) (norm_nonneg _)).trans
          (mul_le_mul_of_nonneg_left hx₀ (abs_nonneg a))
      change ‖V ⟨x, hV.domain_le y.2⟩‖ ≤ a * ‖(x : E)‖ + b * ‖A y‖ at hVy
      linarith
    exact hKW y (by
      have : ‖A y‖ ≤ (1 + |a|) * C₀ / (1 - b) := by
        rw [le_div_iff₀ (by linarith)]
        linarith
      change ‖(x : E)‖ + ‖A y‖ ≤ _
      linarith)

end IsRelativelyCompact

end Definition

section Resolvent

variable {𝕜 E G : Type*} [NontriviallyNormedField 𝕜] [SeminormedAddCommGroup E] [NormedSpace 𝕜 E]
  [SeminormedAddCommGroup G] [NormedSpace 𝕜 G] {A : E →ₗ.[𝕜] E} {V : E →ₗ.[𝕜] G} {z : 𝕜}

/-- The composite `y ↦ V (R_A(z) y)` as a linear map, when `dom A ⊆ dom V`. -/
private noncomputable def compResolvent (h : A.domain ≤ V.domain) (hz : z ∈ A.resolventSet) :
    E →ₗ[𝕜] G :=
  V.toFun ∘ₗ Submodule.inclusion h ∘ₗ
    (A.resolvent z : E →ₗ[𝕜] E).codRestrict A.domain (resolvent_mem_domain hz)

private theorem compResolvent_apply (h : A.domain ≤ V.domain) (hz : z ∈ A.resolventSet)
    (y : E) : compResolvent h hz y = V ⟨A.resolvent z y, h (resolvent_mem_domain hz y)⟩ :=
  rfl

/-- **The resolvent characterization of relative compactness.** At a point `z` of the resolvent
set of `A`, the map `V` is `A`-compact exactly when `dom A ⊆ dom V` and `V (z I - A)⁻¹` is a
compact operator. -/
theorem isRelativelyCompact_iff_isCompactOperator (hz : z ∈ A.resolventSet) :
    V.IsRelativelyCompact A ↔ ∃ h : A.domain ≤ V.domain,
      IsCompactOperator fun y ↦ V ⟨A.resolvent z y, h (resolvent_mem_domain hz y)⟩ := by
  set R := A.resolvent z
  constructor
  · intro hV
    refine ⟨hV.domain_le, ?_⟩
    obtain ⟨K, hK, hKV⟩ := hV.exists_isCompact (‖R‖ + (‖z‖ * ‖R‖ + 1))
    refine (isCompactOperator_iff_image_ball_subset_compact (compResolvent hV.domain_le hz)
      one_pos).2 ⟨K, hK, ?_⟩
    rintro _ ⟨y, hy, rfl⟩
    rw [mem_ball_zero_iff] at hy
    refine hKV ⟨R y, resolvent_mem_domain hz y⟩ ?_
    have hRy : ‖R y‖ ≤ ‖R‖ := (R.le_opNorm y).trans (by nlinarith [norm_nonneg R])
    rw [apply_resolvent hz]
    calc ‖R y‖ + ‖z • R y - y‖ ≤ ‖R y‖ + (‖z‖ * ‖R y‖ + ‖y‖) := by
          gcongr
          exact (norm_sub_le _ _).trans (by rw [norm_smul])
      _ ≤ ‖R‖ + (‖z‖ * ‖R‖ + 1) := by gcongr
  · rintro ⟨h, hc⟩
    refine ⟨h, fun C ↦ ?_⟩
    obtain ⟨K, hK, hKV⟩ :=
      hc.image_closedBall_subset_compact (f := compResolvent h hz) ((‖z‖ + 1) * C)
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

/-- At a point `z` of the resolvent set of `A`, an `A`-compact map `V` composed with the
resolvent `(z I - A)⁻¹` is a compact operator `K : E →L[𝕜] G`. -/
theorem IsRelativelyCompact.exists_isCompactOperator (hV : V.IsRelativelyCompact A)
    (hz : z ∈ A.resolventSet) : ∃ K : E →L[𝕜] G, IsCompactOperator K ∧
      ∀ y, V ⟨A.resolvent z y, hV.domain_le (resolvent_mem_domain hz y)⟩ = K y := by
  obtain ⟨h, hc⟩ := (isRelativelyCompact_iff_isCompactOperator hz).1 hV
  have hc' : IsCompactOperator (compResolvent h hz) := hc
  exact ⟨.mkOfIsCompactOperator hc', hc', fun _ ↦ rfl⟩

/-- **Compact resolvent difference.** If `V : E →ₗ.[𝕜] E` is `A`-compact, then at every point `z`
of the resolvent sets of both `A` and `A + V` the difference `R_{A+V}(z) - R_A(z)` is a compact
operator; indeed it equals `R_{A+V}(z) V R_A(z)`. -/
theorem IsRelativelyCompact.isCompactOperator_resolvent_add_sub {V : E →ₗ.[𝕜] E}
    (hV : V.IsRelativelyCompact A) (hz : z ∈ A.resolventSet) (hz' : z ∈ (A + V).resolventSet) :
    IsCompactOperator ((A + V).resolvent z - A.resolvent z) := by
  obtain ⟨h, hc⟩ := (isRelativelyCompact_iff_isCompactOperator hz).1 hV
  convert hc.clm_comp ((A + V).resolvent z) using 1
  ext y
  set x := A.resolvent z y
  have hx : x ∈ (A + V).domain := ⟨resolvent_mem_domain hz y, h (resolvent_mem_domain hz y)⟩
  have hsolve := resolvent_smul_sub_apply hz' ⟨x, hx⟩
  have hAx : A ⟨x, resolvent_mem_domain hz y⟩ = z • x - y := apply_resolvent hz y
  have hsplit : z • x - (A + V) ⟨x, hx⟩ = y - V ⟨x, h (resolvent_mem_domain hz y)⟩ := by
    rw [add_apply]
    change z • x - (A ⟨x, resolvent_mem_domain hz y⟩ + V ⟨x, h (resolvent_mem_domain hz y)⟩) = _
    rw [hAx]
    abel
  rw [hsplit, ContinuousLinearMap.map_sub] at hsolve
  simp only [_root_.sub_apply, Function.comp_apply]
  rw [← sub_eq_iff_eq_add'.2 (sub_eq_iff_eq_add.1 hsolve)]

end Resolvent

end LinearPMap

namespace IsCompactOperator

variable {𝕜 𝕜₂ R E F G : Type*} [NontriviallyNormedField 𝕜] [NormedField 𝕜₂] [Ring R]
  {σ : 𝕜 →+* 𝕜₂} {τ : 𝕜 →+* R}
  [SeminormedAddCommGroup E] [NormedSpace 𝕜 E] [SeminormedAddCommGroup F] [Module R F]
  [SeminormedAddCommGroup G] [NormedSpace 𝕜₂ G]

/-- The restriction of a compact operator `T` to a subspace containing the domain of `A` is
`A`-compact. -/
theorem isRelativelyCompact_toPMap {T : E →ₛₗ[σ] G} (hT : IsCompactOperator T)
    {A : E →ₛₗ.[τ] F} {p : Submodule 𝕜 E} (hp : A.domain ≤ p) :
    (T.toPMap p).IsRelativelyCompact A where
  domain_le := hp
  exists_isCompact C := by
    obtain ⟨K, hK, hKT⟩ := hT.image_closedBall_subset_compact C
    exact ⟨K, hK, fun x hx ↦ hKT ⟨x, mem_closedBall_zero_iff.2 (by
      linarith [norm_nonneg (A x)]), rfl⟩⟩

end IsCompactOperator
