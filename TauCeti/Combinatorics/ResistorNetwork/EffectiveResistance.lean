/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.ResistorNetwork.Basic
public import Mathlib.LinearAlgebra.Trace

/-!
# Effective resistance and Foster's theorem

When a unit current enters a connected resistor network at `a` and leaves it at `b`, Kirchhoff's
laws determine the potential `f` up to an additive constant: it solves `L f = 𝟙_a - 𝟙_b` for the
weighted Laplacian `L`. The **effective resistance** `R(a, b)` between `a` and `b` is the
resulting voltage drop `f a - f b`. It is the energy dissipated by the unit current, hence
nonnegative, and it is symmetric in `a` and `b`. Across an edge it is at most the resistance of
that edge, which carries part of the current while the rest of the network carries the remainder.

Foster's theorem says that on a connected network with `n` vertices the edges carry, in total,
`n - 1` units of the normalized resistance: `∑ₑ R(src e, tgt e) / rₑ = n - 1`. Consequently the
numbers `1 - R(src e, tgt e) / rₑ`, which lie in `[0, 1]`, add up to the cyclomatic number
`#E - #V + 1` of the network. On a metrized graph of genus `g` with vertex genera, Zhang's
admissible measure gives an edge `e` the mass `(1 - R(src e, tgt e) / rₑ) / g`, so by this identity
the edges carry in total the mass `b₁ / g`, with `b₁` the cyclomatic number.

## Main definitions

* `TauCeti.ResistorNetwork.effectiveResistance`: the effective resistance between two vertices.
  When no current can flow from `a` to `b`, that is when `a` and `b` lie in different components,
  it takes the junk value `0`.

## Main results

* `TauCeti.ResistorNetwork.effectiveResistance_eq`: the effective resistance is the voltage drop
  of any potential solving the Kirchhoff equations for a unit current, which exist on a
  preconnected network (`TauCeti.ResistorNetwork.exists_laplacian_eq_single_sub_single`).
* `TauCeti.ResistorNetwork.effectiveResistance_eq_sum`: it is the energy of that potential.
* `TauCeti.ResistorNetwork.effectiveResistance_le_resistance`: across an edge it is at most the
  resistance of the edge.
* `TauCeti.ResistorNetwork.effectiveResistance_eq_inv_sum_inv_resistance`: on a network all of
  whose edges join `a` and `b ≠ a`, the effective resistance is the inverse of the total
  conductance (parallel law).
* `TauCeti.ResistorNetwork.sum_effectiveResistance_div_resistance`: **Foster's theorem**.
* `TauCeti.ResistorNetwork.sum_one_sub_effectiveResistance_div_resistance`: the complementary
  edge masses add up to the cyclomatic number.

## References

* R. M. Foster, *The average impedance of an electrical network*, Contributions to Applied
  Mechanics (Reissner Anniversary Volume), 1949, 333–340.
* P. Tetali, *Random walks and the effective resistance of networks*, J. Theoret. Probab. 4
  (1991), 101–109.
* M. Baker and X. Faber, *Metrized graphs, Laplacian operators, and electrical networks*,
  Quantum graphs and their applications, Contemp. Math. 415 (2006), §§1–2.
* X. Yuan, *Arithmetic bigness and a uniform Bogomolov-type result*, Appendix A.5.
-/

public section

open Finset Module

namespace TauCeti

namespace ResistorNetwork

variable {V E : Type*} (N : ResistorNetwork V E) [Fintype E] [DecidableEq V]

open scoped Classical in
/-- The effective resistance between `a` and `b`: the voltage drop `f a - f b` of a potential `f`
driving a unit current from `a` to `b`, that is with `L f = 𝟙_a - 𝟙_b`. It does not depend on the
choice of `f` (`TauCeti.ResistorNetwork.effectiveResistance_eq`). When there is no such potential,
because `a` and `b` lie in different components, it takes the junk value `0`. -/
noncomputable def effectiveResistance (a b : V) : ℝ :=
  if h : ∃ f : V → ℝ, N.laplacian f = Pi.single a 1 - Pi.single b 1 then
    h.choose a - h.choose b
  else 0

/-- The effective resistance takes the junk value `0` when no current can flow from `a` to `b`. -/
theorem effectiveResistance_eq_zero_of_forall_ne {a b : V}
    (h : ∀ f : V → ℝ, N.laplacian f ≠ Pi.single a 1 - Pi.single b 1) :
    N.effectiveResistance a b = 0 := by
  rw [effectiveResistance, dite_eq_right (not_exists.2 h)]

/-- The effective resistance between a vertex and itself vanishes. -/
@[simp] theorem effectiveResistance_self (a : V) : N.effectiveResistance a a = 0 := by
  rw [effectiveResistance]
  split_ifs <;> simp

/-- Pairing a potential with the unit current from `a` to `b` gives its voltage drop. -/
private theorem sum_mul_single_sub_single [Fintype V] (g : V → ℝ) (a b : V) :
    ∑ v, g v * (Pi.single a 1 - Pi.single b 1 : V → ℝ) v = g a - g b := by
  simp [mul_sub, Finset.sum_sub_distrib, Pi.single_apply]

section Finite

variable [Finite V]

/-- The effective resistance is the voltage drop of any potential driving a unit current from `a`
to `b`. -/
theorem effectiveResistance_eq {a b : V} {f : V → ℝ}
    (hf : N.laplacian f = Pi.single a 1 - Pi.single b 1) :
    N.effectiveResistance a b = f a - f b := by
  have h : ∃ f : V → ℝ, N.laplacian f = Pi.single a 1 - Pi.single b 1 := ⟨f, hf⟩
  have := Fintype.ofFinite V
  rw [effectiveResistance, dite_eq_left h]
  -- Two potentials driving the same current have the same voltage drop, by symmetry of `L`.
  calc h.choose a - h.choose b = ∑ v, h.choose v * N.laplacian f v := by
        rw [hf, sum_mul_single_sub_single]
    _ = ∑ v, f v * N.laplacian h.choose v := N.sum_mul_laplacian_apply_comm _ _
    _ = f a - f b := by rw [h.choose_spec, sum_mul_single_sub_single]

/-- On a preconnected network the unit current from `a` to `b` is the Laplacian of a potential. -/
theorem single_sub_single_mem_range_laplacian (hN : N.toSimpleGraph.Preconnected) (a b : V) :
    (Pi.single a 1 - Pi.single b 1 : V → ℝ) ∈ LinearMap.range N.laplacian := by
  have := Fintype.ofFinite V
  rw [N.mem_range_laplacian_iff hN]
  simp [Finset.sum_sub_distrib]

/-- On a preconnected network a unit current can be driven between any two vertices. -/
theorem exists_laplacian_eq_single_sub_single (hN : N.toSimpleGraph.Preconnected) (a b : V) :
    ∃ f : V → ℝ, N.laplacian f = Pi.single a 1 - Pi.single b 1 :=
  LinearMap.mem_range.1 (N.single_sub_single_mem_range_laplacian hN a b)

/-- The effective resistance is the energy dissipated by a unit current from `a` to `b`. -/
theorem effectiveResistance_eq_sum {a b : V} {f : V → ℝ}
    (hf : N.laplacian f = Pi.single a 1 - Pi.single b 1) :
    N.effectiveResistance a b = ∑ e, (f (N.src e) - f (N.tgt e)) ^ 2 / N.resistance e := by
  have := Fintype.ofFinite V
  rw [← N.sum_mul_laplacian_apply_self, hf, N.effectiveResistance_eq hf,
    sum_mul_single_sub_single]

/-- The effective resistance is nonnegative. -/
theorem effectiveResistance_nonneg (a b : V) : 0 ≤ N.effectiveResistance a b := by
  by_cases h : ∃ f : V → ℝ, N.laplacian f = Pi.single a 1 - Pi.single b 1
  · obtain ⟨f, hf⟩ := h
    have := Fintype.ofFinite V
    rw [N.effectiveResistance_eq_sum hf, ← N.sum_mul_laplacian_apply_self]
    exact N.sum_mul_laplacian_apply_self_nonneg f
  · rw [N.effectiveResistance_eq_zero_of_forall_ne (not_exists.1 h)]

/-- The effective resistance is symmetric. -/
theorem effectiveResistance_comm (a b : V) :
    N.effectiveResistance a b = N.effectiveResistance b a := by
  by_cases h : ∃ f : V → ℝ, N.laplacian f = Pi.single a 1 - Pi.single b 1
  · obtain ⟨f, hf⟩ := h
    have hf' : N.laplacian (-f) = Pi.single b 1 - Pi.single a 1 := by
      rw [map_neg, hf, neg_sub]
    rw [N.effectiveResistance_eq hf, N.effectiveResistance_eq hf']
    simp only [Pi.neg_apply]
    ring
  · have h' : ∀ f : V → ℝ, N.laplacian f ≠ Pi.single b 1 - Pi.single a 1 := by
      intro f hf
      exact h ⟨-f, by rw [map_neg, hf, neg_sub]⟩
    rw [N.effectiveResistance_eq_zero_of_forall_ne (not_exists.1 h),
      N.effectiveResistance_eq_zero_of_forall_ne h']

/-- The effective resistance across an edge is at most the resistance of the edge. -/
theorem effectiveResistance_le_resistance (e : E) :
    N.effectiveResistance (N.src e) (N.tgt e) ≤ N.resistance e := by
  by_cases h : ∃ f : V → ℝ, N.laplacian f = Pi.single (N.src e) 1 - Pi.single (N.tgt e) 1
  · obtain ⟨f, hf⟩ := h
    -- The energy of the unit current is at least the energy dissipated in `e` alone.
    have hR := N.effectiveResistance_eq hf
    have hle : (f (N.src e) - f (N.tgt e)) ^ 2 / N.resistance e ≤
        N.effectiveResistance (N.src e) (N.tgt e) := by
      rw [N.effectiveResistance_eq_sum hf]
      exact Finset.single_le_sum (f := fun e => (f (N.src e) - f (N.tgt e)) ^ 2 / N.resistance e)
        (fun e _ => N.sq_div_resistance_nonneg _ e) (Finset.mem_univ e)
    rw [← hR, div_le_iff₀ (N.resistance_pos e)] at hle
    have := N.effectiveResistance_nonneg (N.src e) (N.tgt e)
    rw [hR] at this ⊢
    nlinarith [N.resistance_pos e]
  · rw [N.effectiveResistance_eq_zero_of_forall_ne (not_exists.1 h)]
    exact (N.resistance_pos e).le

/-- **Parallel resistors.** If every edge joins `a` and `b ≠ a`, in either direction, the
effective resistance between `a` and `b` is the inverse of the total conductance `∑ₑ 1 / rₑ`. -/
theorem effectiveResistance_eq_inv_sum_inv_resistance {a b : V} (hab : a ≠ b)
    (hends : ∀ e, (N.src e = a ∧ N.tgt e = b) ∨ (N.src e = b ∧ N.tgt e = a)) :
    N.effectiveResistance a b = (∑ e, (N.resistance e)⁻¹)⁻¹ := by
  cases isEmpty_or_nonempty E with
  | inl _ =>
    refine (N.effectiveResistance_eq_zero_of_forall_ne fun f hf => ?_).trans (by simp)
    have := congrFun hf a
    simp [N.laplacian_apply, hab] at this
  | inr _ =>
    set c := ∑ e, (N.resistance e)⁻¹
    have hc : 0 < c :=
      Finset.sum_pos (fun e _ => inv_pos.2 (N.resistance_pos e)) Finset.univ_nonempty
    -- The potential `c⁻¹ • 𝟙_a` drives a unit current from `a` to `b`: whatever its
    -- orientation, each edge `e` carries the current `c⁻¹ / rₑ` from `a` to `b`.
    have hf : N.laplacian (Pi.single a c⁻¹) = Pi.single a 1 - Pi.single b 1 := by
      have he (e : E) : ((Pi.single (M := fun _ => ℝ) a c⁻¹ (N.src e) -
          Pi.single (M := fun _ => ℝ) a c⁻¹ (N.tgt e)) / N.resistance e) •
            (Pi.single (N.src e) 1 - Pi.single (N.tgt e) 1 : V → ℝ) =
          (c⁻¹ * (N.resistance e)⁻¹) • (Pi.single a 1 - Pi.single b 1) := by
        rcases hends e with ⟨hs, ht⟩ | ⟨hs, ht⟩ <;> rw [hs, ht]
        · simp [Pi.single_eq_of_ne' hab, div_eq_mul_inv]
        · rw [← neg_sub (Pi.single a 1), smul_neg, ← neg_smul]
          simp [Pi.single_eq_of_ne' hab, div_eq_mul_inv]
      rw [N.laplacian_apply, Finset.sum_congr rfl fun e _ => he e, ← Finset.sum_smul,
        ← Finset.mul_sum, inv_mul_cancel₀ hc.ne', one_smul]
    rw [N.effectiveResistance_eq hf, Pi.single_eq_same, Pi.single_eq_of_ne' hab, sub_zero]

end Finite

variable [Fintype V]

/-- **Foster's theorem**: on a connected network the effective resistances across the edges,
each divided by the resistance of its edge, add up to one less than the number of vertices. -/
theorem sum_effectiveResistance_div_resistance (hN : N.toSimpleGraph.Connected) :
    ∑ e, N.effectiveResistance (N.src e) (N.tgt e) / N.resistance e = Fintype.card V - 1 := by
  -- For a right inverse `G` of the Laplacian on its range, the trace of `T = G ∘ L` is the trace
  -- of `L ∘ G = id` on the range, that is the rank `n - 1` of `L`. Writing `L` as the sum over
  -- the edges of rank-one maps computes the same trace as the sum of the normalized effective
  -- resistances.
  set L := N.laplacian
  -- A right inverse `G` of the Laplacian on its range.
  obtain ⟨G, hG⟩ := L.rangeRestrict.exists_rightInverse_of_surjective L.range_rangeRestrict
  have hLG (w : LinearMap.range L) : L (G w) = w :=
    congrArg Subtype.val (LinearMap.congr_fun hG w)
  set T := G ∘ₗ L.rangeRestrict with hT_def
  have htrace : LinearMap.trace ℝ _ T = (Fintype.card V - 1 : ℕ) := by
    rw [hT_def, LinearMap.trace_comp_comm', hG, LinearMap.trace_id,
      N.finrank_range_laplacian hN.preconnected]
  -- Each edge contributes the rank-one map sending `f` to the current through it.
  have hmem (e : E) := N.single_sub_single_mem_range_laplacian hN.preconnected (N.src e) (N.tgt e)
  have hTsum : T = ∑ e, (N.resistance e)⁻¹ •
      ((LinearMap.proj (N.src e) : (V → ℝ) →ₗ[ℝ] ℝ) - LinearMap.proj (N.tgt e)).smulRight
        (G ⟨_, hmem e⟩) := by
    refine LinearMap.ext fun f => ?_
    have hrr : L.rangeRestrict f =
        ∑ e, ((f (N.src e) - f (N.tgt e)) / N.resistance e) • ⟨_, hmem e⟩ := by
      ext1
      simp [L, N.laplacian_apply]
    rw [hT_def, LinearMap.comp_apply, hrr, map_sum, LinearMap.sum_apply]
    refine Finset.sum_congr rfl fun e _ => ?_
    rw [map_smul, LinearMap.smul_apply, LinearMap.smulRight_apply, smul_smul]
    simp [div_eq_inv_mul]
  rw [hTsum, map_sum] at htrace
  have hR (e : E) : (G ⟨_, hmem e⟩) (N.src e) - (G ⟨_, hmem e⟩) (N.tgt e) =
      N.effectiveResistance (N.src e) (N.tgt e) :=
    (N.effectiveResistance_eq (hLG _)).symm
  simp only [map_smul, LinearMap.trace_smulRight, LinearMap.sub_apply, LinearMap.coe_proj,
    Function.eval, hR, smul_eq_mul] at htrace
  have hV : 1 ≤ Fintype.card V := Fintype.card_pos_iff.2 hN.nonempty
  rw [Nat.cast_sub hV, Nat.cast_one] at htrace
  simpa [div_eq_inv_mul] using htrace

/-- On a connected network the complementary normalized resistances `1 - R(src e, tgt e) / rₑ`
of the edges add up to the cyclomatic number `#E - #V + 1`. -/
theorem sum_one_sub_effectiveResistance_div_resistance (hN : N.toSimpleGraph.Connected) :
    ∑ e, (1 - N.effectiveResistance (N.src e) (N.tgt e) / N.resistance e) =
      Fintype.card E - Fintype.card V + 1 := by
  rw [Finset.sum_sub_distrib, N.sum_effectiveResistance_div_resistance hN]
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one]
  ring

end ResistorNetwork

end TauCeti
