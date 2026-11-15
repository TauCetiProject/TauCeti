/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.Hypergraph.Polyad.Coarsening
public import TauCeti.Combinatorics.Hypergraph.Polyad.Energy.Basic
import Mathlib.Data.Rat.BigOperators
import Mathlib.Tactic.Linarith

/-!
# Stability of polyad energy under recoloring the lower skeleton

* `TauCeti.Colored3Graph.polyadEnergy_sub_le_of_injective`: injective polyad map energy drop bound.
* `TauCeti.Colored3Graph.polyadEnergy_sub_le_of_pairRecoloring`: pair-recoloring energy drop bound.
-/

public section

open Finset

namespace TauCeti.Colored3Graph

variable {κ κ₂ κ₂' V : Type*} [Fintype V] [DecidableEq V] [Fintype κ] [DecidableEq κ] (H :
  Colored3Graph κ V)
open Classical in
/-- **Polyad energy drop under an injective polyad map.** -/
theorem polyadEnergy_sub_le_of_injective {S : PairSkeleton3 κ₂ V} {T : PairSkeleton3 κ₂' V} {f :
    Polyad3 S → Polyad3 T} (hf : Function.Injective f) : H.polyadEnergy S - H.polyadEnergy T ≤ 2 *
    #{x | Polyad3.ofTriple T x ≠ f (Polyad3.ofTriple S x)} / (Fintype.card V).descFactorial 3 := by
  let e (x : {x : Fin 3 → V // Function.Injective x}) := H.color (Set.powersetCard.ofFinEmb 3 V
    ⟨x.1, x.2⟩)
  let a (c : κ) (x : {x : Fin 3 → V // Function.Injective x}) : ℝ := H.relativeDensity c
    (Polyad3.ofTriple S x)
  let gPoly (Q : Polyad3 T) (c : κ) : ℝ := if h : ∃ P : Polyad3 S, f P = Q then H.relativeDensity c
    (Classical.choose h) else 0
  let g (c : κ) (x : {x : Fin 3 → V // Function.Injective x}) : ℝ := gPoly (Polyad3.ofTriple T x) c
  let b (c : κ) (x : {x : Fin 3 → V // Function.Injective x}) : ℝ := H.relativeDensity c
    (Polyad3.ofTriple T x)
  let M : Finset _ := {x | Polyad3.ofTriple T x ≠ f (Polyad3.ofTriple S x)}
  have hg_eq (c : κ) {x} (hx : x ∉ M) : g c x = a c x := by
    have hfx : Polyad3.ofTriple T x = f (Polyad3.ofTriple S x) := (by simpa [M] using hx)
    have hex : ∃ P, f P = Polyad3.ofTriple T x := ⟨_, hfx.symm⟩
    simp [g, gPoly, hex, hf ((Classical.choose_spec hex).trans hfx), a]
  have hg_props (x) : 0 ≤ g (e x) x ∧ ∑ c, g c x ^ 2 ≤ 1 := by
    dsimp [g, gPoly]; by_cases hex : ∃ P, f P = Polyad3.ofTriple T x
    · simp only [dite_eq_left hex]; set P := Classical.choose hex
      refine ⟨mod_cast H.relativeDensity_nonneg _ P, (sum_le_sum fun c _ ↦ pow_le_of_le_one
        (mod_cast H.relativeDensity_nonneg c P) (mod_cast H.relativeDensity_le_one c P)
        two_ne_zero).trans ?_⟩
      obtain hP | hP := P.support.eq_empty_or_nonempty
      · simp [H.relativeDensity_of_support_eq_empty _ hP]
      · exact (mod_cast H.sum_relativeDensity hP : ∑ c, (H.relativeDensity c P : ℝ) = 1).le
    · simp [dite_eq_right hex]
  have hsum_col (w : κ → {x : Fin 3 → V // Function.Injective x} → ℝ) :
      ∑ c, ∑ x with e x = c, w c x = ∑ x, w (e x) x := by simp_rw [sum_filter]; rw [sum_comm]; simp
  have ha_sum : ∑ x, ∑ c, a c x ^ 2 = ∑ x, (2 * a (e x) x - ∑ c, a c x ^ 2) := by
    have h1 : ∑ c, ∑ x, a c x ^ 2 = ∑ x, a (e x) x := by
      rw [← hsum_col a]; refine sum_congr rfl fun c _ ↦ ?_
      simpa only [sq, a, e] using
        H.sum_relativeDensity_ofTriple_mul (S := S) c (a c) fun _ _ hxy ↦ by simp [a, hxy]
    rw [sum_comm] at h1; simp_rw [sum_sub_distrib, ← mul_sum]; linarith
  have hb_sum : ∑ x, (2 * g (e x) x - ∑ c, g c x ^ 2) ≤ ∑ x, ∑ c, b c x ^ 2 := by
    have h1 : ∑ c, ∑ x, b c x * g c x = ∑ x, g (e x) x := by
      rw [← hsum_col g]; refine sum_congr rfl fun c _ ↦ ?_
      simpa only [b, e] using
        H.sum_relativeDensity_ofTriple_mul (S := T) c (g c) fun _ _ hxy ↦ by simp [g, hxy]
    have h2 : ∑ x, ∑ c, (2 * (b c x * g c x) - g c x ^ 2) ≤ ∑ x, ∑ c, b c x ^ 2 :=
      sum_le_sum fun x _ ↦ sum_le_sum fun c _ ↦ by nlinarith [sq_nonneg (b c x - g c x)]
    simp_rw [sum_sub_distrib, ← mul_sum] at h2 ⊢
    rwa [sum_comm (f := fun x c ↦ b c x * g c x), h1] at h2
  rw [polyadEnergy_def, polyadEnergy_def, ← sub_div]
  refine div_le_div_of_nonneg_right ((by rw [sum_sub_distrib]; linarith : _ ≤
    ∑ x, ((2 * a (e x) x - ∑ c, a c x ^ 2) - (2 * g (e x) x - ∑ c, g c x ^ 2))).trans ?_)
    (Nat.cast_nonneg _)
  rw [← sum_subset (subset_univ M) fun x _ hx ↦ by simp [hg_eq _ hx]]
  exact (sum_le_sum (g := fun _ ↦ (2 : ℝ)) fun x _ ↦ by
    nlinarith [single_le_sum (fun c _ ↦ sq_nonneg (a c x)) (mem_univ (e x)), sq_nonneg (1 - a (e x)
      x), (hg_props x).1, (hg_props x).2]).trans_eq
    (by rw [sum_const, nsmul_eq_mul, mul_comm])
open Classical in
/-- **Polyad energy drop under vertex refinement and pair recoloring.** -/
theorem polyadEnergy_sub_le_of_pairRecoloring {S : PairSkeleton3 κ₂ V} {T : PairSkeleton3 κ₂' V}
    (hV : T.vertexPart ≤ S.vertexPart) {g : κ₂ → κ₂'} (hg : Function.Injective g) : H.polyadEnergy
    S - H.polyadEnergy T ≤ (6 * #{p | T.pairColors.color p ≠ g (S.pairColors.color p)} *
    Fintype.card V : ℕ) / (Fintype.card V).descFactorial 3 := by
  let S' : PairSkeleton3 κ₂ V := ⟨T.vertexPart, S.pairColors⟩
  have href : H.polyadEnergy S ≤ H.polyadEnergy S' := H.polyadEnergy_mono_of_refines (S := S) (T :=
    S') fun x y hxy ↦ by
      have hc := Polyad3.coarsen_ofTriple (S := S) (T := S') hV id (fun _ ↦ rfl)
      rw [← hc x, ← hc y, hxy]
  exact (sub_le_sub_right href _).trans ((H.polyadEnergy_sub_le_of_injective (S := S') (T := T)
    (Polyad3.coarsen_injective (S := T) (T := S') rfl hg)).trans <| (div_le_div_of_nonneg_right
    (mul_le_mul_of_nonneg_left (Nat.cast_le (α := ℝ).2
    (Polyad3.card_filter_ofTriple_ne_coarsen_ofTriple_le (S := T) (T := S') rfl.le g)) zero_le_two)
    (Nat.cast_nonneg _)).trans_eq (by push_cast; ring))
end TauCeti.Colored3Graph
