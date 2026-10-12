/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Polynomial.Reverse
public import TauCeti.Analysis.Polynomial.RealRoots.Normalization
import TauCeti.Topology.Connected.FiniteFamily
import Mathlib.Analysis.Analytic.Constructions
import Mathlib.Algebra.Polynomial.Taylor

/-!
# Analytic real roots in reciprocal coordinates

An analytic enumeration of the distinct real roots of a fixed-bound reflection descends
locally to an ordered analytic enumeration of the original polynomial's roots. The original
fibers must have nonzero constant coefficient and constant degree. The excess of the reflection
bound over that degree produces a zero root, which is discarded before taking reciprocals. All
remaining roots retain their multiplicities.

This allows a monic root construction in reciprocal coordinates to give finite root sections
of a nonmonic family, even when its degree is smaller than the formal reflection bound.
The root sections of the reflected family are inputs; no root enumeration of the original
family is assumed. No continuity of the coefficients is needed for this transport.

The integral-normalization variant descends directly from monic reciprocal preparation.
Its only analytic coefficient hypothesis is the value at the translation center, which is
the reflected leading coefficient. It allows the original degree to be below the reflection
bound and removes the artificial zero root after undoing normalization.

## References

S. McCallum, *An improved projection operation for cylindrical algebraic decomposition*,
Springer (1998), Sections 2–3 (local delineability in reciprocal coordinates).
-/

public section

open Filter Function Polynomial Set Topology

namespace TauCeti

private theorem eventually_root_eq_zero_iff_of_reflect
    {E ι : Type*} [TopologicalSpace E] [Finite ι]
    {F : E → ℝ[X]} {r : ι → E → ℝ} {x₀ : E} {N d : ℕ}
    (hr : ∀ i, ContinuousAt (r i) x₀)
    (hinj : Injective (fun i ↦ r i x₀)) (hdN : d ≤ N)
    (hF : ∀ᶠ x in 𝓝 x₀, F x ≠ 0 ∧ (F x).natDegree = d)
    (hroots : ∀ᶠ x in 𝓝 x₀, ∀ t,
      ((F x).reflect N).IsRoot t ↔ ∃ i, r i x = t) :
    ∀ᶠ x in 𝓝 x₀, ∀ i, r i x = 0 ↔ r i x₀ = 0 := by
  rw [eventually_all]
  intro i
  by_cases hi : r i x₀ = 0
  · have hpos : 0 < N - d := by
      have hroot := (hroots.self_of_nhds 0).2 ⟨i, hi⟩
      have hm := (rootMultiplicity_pos
        (reflect_eq_zero_iff.not.2 hF.self_of_nhds.1)).2 hroot
      rwa [rootMultiplicity_reflect_zero _ hF.self_of_nhds.1
        (hF.self_of_nhds.2 ▸ hdN), hF.self_of_nhds.2] at hm
    have hmem : ∀ᶠ x in 𝓝 x₀, (0 : ℝ) ∈ range (fun j ↦ r j x) := by
      filter_upwards [hF, hroots] with x hx hxr
      apply (hxr 0).1
      apply (rootMultiplicity_pos (reflect_eq_zero_iff.not.2 hx.1)).1
      rwa [rootMultiplicity_reflect_zero _ hx.1 (hx.2 ▸ hdN), hx.2]
    have heq := eventuallyEq_of_continuousAt_mem_range hr continuousAt_const hmem hi
      (fun j hj ↦ by obtain rfl := hinj hj; exact .rfl)
    exact heq.mono fun x hx ↦ by simp [hx, hi]
  · exact ((hr i).eventually_ne hi).mono fun x hx ↦ by simp [hx, hi]

variable {E ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [Finite ι]
  {F : E → ℝ[X]} {r : ι → E → ℝ} {x₀ : E} {N d : ℕ}

/-- Descend analytic distinct real root sections of a fixed-bound reflection by discarding
its zero section and taking reciprocals. On a common open neighborhood the resulting roots
are strictly ordered, cover every real root of the original family, and have constant positive
multiplicities. Constant fibers and an empty list of finite roots are included. -/
theorem exists_analyticOnNhd_ordered_roots_of_reflect
    (hr : ∀ i, AnalyticAt ℝ (r i) x₀)
    (hinj : Injective (fun i ↦ r i x₀)) (hdN : d ≤ N)
    (hdeg : ∀ᶠ x in 𝓝 x₀, (F x).natDegree = d)
    (hzero : ∀ᶠ x in 𝓝 x₀, (F x).eval 0 ≠ 0)
    (hroots : ∀ᶠ x in 𝓝 x₀, ∀ t,
      ((F x).reflect N).IsRoot t ↔ ∃ i, r i x = t)
    (hmult : ∀ᶠ x in 𝓝 x₀, ∀ i, r i x₀ ≠ 0 →
      ((F x).reflect N).rootMultiplicity (r i x) =
        ((F x₀).reflect N).rootMultiplicity (r i x₀)) :
    ∃ k : ℕ, ∃ s : Fin k → E → ℝ, ∃ U : Set E, IsOpen U ∧ x₀ ∈ U ∧
      (∀ i, AnalyticOnNhd ℝ (s i) U) ∧
      (∀ x ∈ U, StrictMono (fun i ↦ s i x)) ∧
      (∀ x ∈ U, ∀ t, (F x).IsRoot t ↔ ∃ i, s i x = t) ∧
      (∀ i, 0 < (F x₀).rootMultiplicity (s i x₀)) ∧
      ∀ x ∈ U, ∀ i,
        (F x).rootMultiplicity (s i x) = (F x₀).rootMultiplicity (s i x₀) := by
  classical
  have hF : ∀ᶠ x in 𝓝 x₀, F x ≠ 0 ∧ (F x).natDegree = d := by
    filter_upwards [hdeg, hzero] with x hx hx0
    exact ⟨fun hz ↦ hx0 (by simp [hz]), hx⟩
  -- Retain exactly the sections that stay away from the reciprocal origin.
  let J := {i : ι // r i x₀ ≠ 0}
  let f : J → E → ℝ := fun i x ↦ (r i x)⁻¹
  have hf (i : J) : AnalyticAt ℝ (f i) x₀ := (hr i).inv i.property
  have hfi : Injective (fun i : J ↦ f i x₀) := fun i j hij ↦
    Subtype.ext (hinj (inv_injective hij))
  obtain ⟨k, e, V, hV, hxV, ha, horder⟩ :=
    exists_analyticOnNhd_strictMono_range_eq hf
      (fun i j hij ↦ by obtain rfl := hfi hij; exact .rfl)
  have hzeroRoots := eventually_root_eq_zero_iff_of_reflect
    (fun i ↦ (hr i).continuousAt) hinj hdN hF hroots
  -- Reflection preserves multiplicity at every retained section.
  have htransport : ∀ᶠ x in 𝓝 x₀, ∀ i : J,
      (F x).rootMultiplicity (f i x) = (F x₀).rootMultiplicity (f i x₀) := by
    filter_upwards [hF, hzeroRoots, hmult] with x hx hzr hmx i
    have hi : r i x ≠ 0 := (hzr i).not.2 i.property
    have hm (x : E) (hx : (F x).natDegree ≤ N) (hi : r i x ≠ 0) :
        (F x).rootMultiplicity (f i x) =
          ((F x).reflect N).rootMultiplicity (r i x) := by
      have h := (F x).rootMultiplicity_reflect hx (Units.mk0 (r i x)⁻¹ (inv_ne_zero hi))
      simpa only [Units.val_inv_eq_inv_val, Units.val_mk0, inv_inv, f] using h.symm
    rw [hm x (hx.2 ▸ hdN) hi, hm x₀ (hF.self_of_nhds.2 ▸ hdN) i.property]
    exact hmx i i.property
  -- The original zero coordinate is excluded by the nonvanishing constant coefficient.
  have hcover : ∀ᶠ x in 𝓝 x₀, ∀ t,
      (F x).IsRoot t ↔ ∃ i : J, f i x = t := by
    filter_upwards [hF, hzero, hroots, hzeroRoots] with x hx hx0 hxr hzr t
    have hroot (t : ℝ) (ht : t ≠ 0) :
        (F x).IsRoot t ↔ ((F x).reflect N).IsRoot t⁻¹ := by
      have hm := (F x).rootMultiplicity_reflect (hx.2 ▸ hdN) (Units.mk0 t ht)
      simp only [Units.val_inv_eq_inv_val, Units.val_mk0] at hm
      rw [← rootMultiplicity_pos hx.1,
        ← rootMultiplicity_pos (reflect_eq_zero_iff.not.2 hx.1), hm]
    constructor
    · intro ht
      have ht0 : t ≠ 0 := fun hz ↦ hx0 (hz ▸ ht.eq_zero)
      obtain ⟨i, hi⟩ := (hxr _).1 ((hroot t ht0).1 ht)
      have hi0 : r i x ≠ 0 := hi ▸ inv_ne_zero ht0
      refine ⟨⟨i, (hzr i).not.1 hi0⟩, ?_⟩
      simp only [f, hi, inv_inv]
    · rintro ⟨i, rfl⟩
      have hi : r i x ≠ 0 := (hzr i).not.2 i.property
      apply (hroot _ (inv_ne_zero hi)).2
      exact (hxr _).2 ⟨i, by simp⟩
  -- Intersect the transport neighborhood with the neighborhood for a fixed ordering.
  obtain ⟨U, hU, hopen, hxU⟩ := eventually_nhds_iff.1
    (Filter.Eventually.and (hV.mem_nhds hxV) (hcover.and htransport))
  refine ⟨k, fun i ↦ f (e i), U, hopen, hxU,
    fun i ↦ (ha i).mono (fun x hx ↦ (hU x hx).1),
    fun x hx ↦ (horder x (hU x hx).1).1, ?_, ?_,
    fun x hx i ↦ (hU x hx).2.2 (e i)⟩
  · intro x hx t
    rw [(hU x hx).2.1 t]
    exact (congrArg (t ∈ ·) (horder x (hU x hx).1).2).symm.to_iff
  · intro i
    apply (rootMultiplicity_pos hF.self_of_nhds.1).2
    exact hcover.self_of_nhds _ |>.2 ⟨e i, rfl⟩

/-- Descend from translated reciprocal coordinates. The translation center `τ` is chosen
away from the roots of the original fibers. Reflection uses a fixed bound `N`, allowing
fiber degrees strictly below that bound. The finite roots of the original family form a
strictly ordered analytic list with constant positive multiplicities on a neighborhood. -/
theorem exists_analyticOnNhd_ordered_roots_of_reflect_comp_X_add_C {τ : ℝ}
    (hr : ∀ i, AnalyticAt ℝ (r i) x₀)
    (hinj : Injective (fun i ↦ r i x₀)) (hdN : d ≤ N)
    (hdeg : ∀ᶠ x in 𝓝 x₀, (F x).natDegree = d)
    (hτ : ∀ᶠ x in 𝓝 x₀, (F x).eval τ ≠ 0)
    (hroots : ∀ᶠ x in 𝓝 x₀, ∀ t,
      (((F x).comp (X + C τ)).reflect N).IsRoot t ↔ ∃ i, r i x = t)
    (hmult : ∀ᶠ x in 𝓝 x₀, ∀ i, r i x₀ ≠ 0 →
      (((F x).comp (X + C τ)).reflect N).rootMultiplicity (r i x) =
        (((F x₀).comp (X + C τ)).reflect N).rootMultiplicity (r i x₀)) :
    ∃ k : ℕ, ∃ s : Fin k → E → ℝ, ∃ U : Set E, IsOpen U ∧ x₀ ∈ U ∧
      (∀ i, AnalyticOnNhd ℝ (s i) U) ∧
      (∀ x ∈ U, StrictMono (fun i ↦ s i x)) ∧
      (∀ x ∈ U, ∀ t, (F x).IsRoot t ↔ ∃ i, s i x = t) ∧
      (∀ i, 0 < (F x₀).rootMultiplicity (s i x₀)) ∧
      ∀ x ∈ U, ∀ i,
        (F x).rootMultiplicity (s i x) = (F x₀).rootMultiplicity (s i x₀) := by
  have hG : ∀ᶠ x in 𝓝 x₀, ((F x).comp (X + C τ)).natDegree = d := by
    simpa only [← taylor_apply, natDegree_taylor] using hdeg
  have hG0 : ∀ᶠ x in 𝓝 x₀, ((F x).comp (X + C τ)).eval 0 ≠ 0 := by
    simpa only [eval_comp, eval_add, eval_X, eval_C, zero_add] using hτ
  obtain ⟨k, s, U, hU, hxU, ha, hmono, hcover, hpos, hm⟩ :=
    exists_analyticOnNhd_ordered_roots_of_reflect hr hinj hdN hG hG0 hroots hmult
  have hmult_trans (x : E) (t : ℝ) :
      ((F x).comp (X + C τ)).rootMultiplicity t = (F x).rootMultiplicity (t + τ) := by
    simpa only [C_1, one_mul] using
      (F x).rootMultiplicity_comp_C_mul_X_add_C 1 τ t isUnit_one
  refine ⟨k, fun i x ↦ s i x + τ, U, hU, hxU,
    fun i ↦ (ha i).add analyticOnNhd_const,
    ?_, ?_,
    fun i ↦ hmult_trans x₀ (s i x₀) ▸ hpos i, ?_⟩
  · intro x hx i j hij
    simpa only [add_comm] using (add_lt_add_right (hmono x hx hij) τ)
  · intro x hx t
    have hc := hcover x hx (t - τ)
    simpa only [IsRoot.def, eval_comp, eval_add, eval_X, eval_C, sub_add_cancel,
      eq_sub_iff_add_eq] using hc
  · intro x hx i
    rw [← hmult_trans x (s i x), ← hmult_trans x₀ (s i x₀)]
    exact hm x hx i

/-- Descend analytic roots of the integral normalization of a translated reflection.
Undo monic normalization, discard the reflected zero root, and take translated reciprocals.
The original family may have degree below the fixed reflection bound; its finite real roots
have a strictly ordered analytic enumeration with constant positive multiplicities locally. -/
theorem exists_analyticOnNhd_ordered_roots_of_integralNormalization_reflect_comp_X_add_C
    {τ : ℝ} (hr : ∀ i, AnalyticAt ℝ (r i) x₀)
    (hinj : Injective (fun i ↦ r i x₀)) (hdN : d ≤ N)
    (hdeg : ∀ᶠ x in 𝓝 x₀, (F x).natDegree = d)
    (hτA : AnalyticAt ℝ (fun x ↦ (F x).eval τ) x₀) (hτ0 : (F x₀).eval τ ≠ 0)
    (hroots : ∀ᶠ x in 𝓝 x₀, ∀ t,
      (((F x).comp (X + C τ)).reflect N).integralNormalization.IsRoot t ↔
        ∃ i, r i x = t)
    (hmult : ∀ᶠ x in 𝓝 x₀, ∀ i,
      (((F x).comp (X + C τ)).reflect N).integralNormalization.rootMultiplicity (r i x) =
        (((F x₀).comp (X + C τ)).reflect N).integralNormalization.rootMultiplicity (r i x₀)) :
    ∃ k : ℕ, ∃ s : Fin k → E → ℝ, ∃ U : Set E, IsOpen U ∧ x₀ ∈ U ∧
      (∀ i, AnalyticOnNhd ℝ (s i) U) ∧
      (∀ x ∈ U, StrictMono (fun i ↦ s i x)) ∧
      (∀ x ∈ U, ∀ t, (F x).IsRoot t ↔ ∃ i, s i x = t) ∧
      (∀ i, 0 < (F x₀).rootMultiplicity (s i x₀)) ∧
      ∀ x ∈ U, ∀ i,
        (F x).rootMultiplicity (s i x) = (F x₀).rootMultiplicity (s i x₀) := by
  let G : E → ℝ[X] := fun x ↦ ((F x).comp (X + C τ)).reflect N
  have hτ : ∀ᶠ x in 𝓝 x₀, (F x).eval τ ≠ 0 := hτA.continuousAt.eventually_ne hτ0
  have htop (x : E) : (G x).coeff N = (F x).eval τ := by
    simp only [G, coeff_reflect, revAt_le le_rfl, Nat.sub_self,
      ← taylor_apply, taylor_coeff_zero]
  -- The nonroot center makes the reflected leading coefficient analytic even when
  -- reflection introduces a zero root because its bound exceeds the fiber degree.
  have hlc : (fun x ↦ (F x).eval τ) =ᶠ[𝓝 x₀] fun x ↦ (G x).leadingCoeff := by
    filter_upwards [hdeg, hτ] with x hx hxτ
    have hbound : ((F x).comp (X + C τ)).natDegree ≤ N := by
      simpa only [← taylor_apply, natDegree_taylor, hx] using hdN
    have hGbound : (G x).natDegree ≤ N :=
      natDegree_reflect_le.trans_eq (max_eq_left hbound)
    have hGdeg : (G x).natDegree = N :=
      natDegree_eq_of_le_of_coeff_ne_zero hGbound (by rwa [htop])
    rw [← htop x, ← hGdeg, coeff_natDegree]
  have hG0 : G x₀ ≠ 0 := by
    intro hz
    exact hτ0 (by rw [← htop, hz]; simp)
  obtain ⟨k, e, U, hU, hxU, ha, hmono, hcover, -, hm⟩ :=
    exists_analyticOnNhd_ordered_roots_of_integralNormalization
      (hτA.congr hlc) hG0 hr hinj hroots hmult
  have hmem : ∀ᶠ x in 𝓝 x₀, x ∈ U := hU.mem_nhds hxU
  apply exists_analyticOnNhd_ordered_roots_of_reflect_comp_X_add_C
    (fun i ↦ ha i x₀ hxU) (hmono x₀ hxU).injective hdN hdeg hτ
  · exact hmem.mono fun x hx ↦ hcover x hx
  · exact hmem.mono fun x hx i _ ↦ hm x hx i

end TauCeti
