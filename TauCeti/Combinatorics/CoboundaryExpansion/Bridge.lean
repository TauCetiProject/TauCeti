/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.CoboundaryExpansion.Cochain
public import TauCeti.Combinatorics.CoboundaryExpansion.Sym3.Constant
public import Mathlib.Data.Finset.Sort

/-!
# Bridge between `Defs` and the `Fin k` model of `Sym3`

`Sym3` works with bare functions `Fin k → Fin k → Sym(3)` read on `u < v`, natural-number
moved-point counts and minima. This file transports the definitions of `Defs`, unchanged, along an
order isomorphism `e : Fin k ≃o V`:

* `Sym3.moved_eq_movedNorm`: `moved σ = movedNorm (Fin 3) σ`;
* `defect_eq`, `cost_eq`, `gaugeDist_eq`: defect, cost and gauge distance of a cochain
  are those of its pullback `toFin e α`;
* `defect_ofFin`, `gaugeDist_ofFin`: a bare function gives a cochain `ofFin e f` with the
  same defect and gauge distance;
* `h1_eq`: `h1 (complete V) (movedNorm (Fin 3)) = Sym3.h1 (card V)`.

An order isomorphism preserves the orientation `u < v < w` used by every sum, so no
orientation-independence lemma is needed.
-/

public section

open Finset Equiv Equiv.Perm
open TauCeti.TwoComplex

namespace TauCeti.CoboundaryExpansion.Bridge

variable {V : Type*} [Fintype V] [LinearOrder V]

variable {k : ℕ}

/-- The pullback of a cochain to `Fin k`. -/
def toFin (e : Fin k ≃o V) (α : Cochain (complete V) (Perm (Fin 3))) :
    Fin k → Fin k → Sym3.S3 :=
  fun i j => α.toFun (e i) (e j)

/-- A bare function on `Fin k`, read on `u < v`, inverted on `u > v` and `1` on the diagonal, as
a cochain. -/
def ofFin (e : Fin k ≃o V) (f : Fin k → Fin k → Sym3.S3) :
    Cochain (complete V) (Perm (Fin 3)) where
  toFun u v := if u = v then 1 else Sym3.val f (e.symm u) (e.symm v)
  inv_symm _ _ h := by
    have huv := TwoComplex.ne_of_pair_mem_edges h
    rw [ite_eq_right huv, ite_eq_right huv.symm, Sym3.val_swap f (e.symm.injective.ne huv)]
  one_of_not_mem u v h := ite_eq_left (not_not.1 fun huv => h (pair_mem_edges_complete huv))

theorem defect_eq (e : Fin k ≃o V) (α : Cochain (complete V) (Perm (Fin 3))) :
    α.defect (movedNorm (Fin 3)) = (Sym3.defect (toFin e α) : ℝ) := by
  unfold Cochain.defect
  rw [Sym3.defect_eq_sum]
  have hfilt : (univ.filter fun p : V × V × V =>
      p.1 < p.2.1 ∧ p.2.1 < p.2.2 ∧ ({p.1, p.2.1, p.2.2} : Finset V) ∈ (complete V).triangles) =
      univ.filter fun p : V × V × V => p.1 < p.2.1 ∧ p.2.1 < p.2.2 := by
    apply Finset.filter_congr
    intro p _
    exact ⟨fun h => ⟨h.1, h.2.1⟩, fun h =>
      ⟨h.1, h.2, triple_mem_triangles_complete h.1.ne (h.1.trans h.2).ne h.2.ne⟩⟩
  rw [hfilt, Finset.sum_filter, Fintype.sum_prod_type]
  simp only [Fintype.sum_prod_type]
  push_cast
  rw [← e.toEquiv.sum_comp]
  refine Finset.sum_congr rfl fun u _ => ?_
  rw [← e.toEquiv.sum_comp]
  refine Finset.sum_congr rfl fun v _ => ?_
  rw [← e.toEquiv.sum_comp]
  refine Finset.sum_congr rfl fun w _ => ?_
  simp only [OrderIso.coe_toEquiv, e.lt_iff_lt]
  split_ifs with h
  · obtain ⟨huv, hvw⟩ := h
    have huw : u < w := huv.trans hvw
    rw [← Sym3.moved_eq_movedNorm,
      α.inv_symm (e u) (e w) (pair_mem_edges_complete (e.injective.ne huw.ne))]
    simp [Sym3.hol, Sym3.val, toFin, huv, hvw, not_lt.mpr huw.le]
  · rfl

theorem cost_eq (e : Fin k ≃o V) (α : Cochain (complete V) (Perm (Fin 3))) (β : V → Perm (Fin 3)) :
    α.cost (movedNorm (Fin 3)) β = (Sym3.cost (toFin e α) (β ∘ e) : ℝ) := by
  unfold Cochain.cost
  rw [Sym3.cost_eq_sum]
  have hfilt : (univ.filter fun p : V × V =>
      p.1 < p.2 ∧ ({p.1, p.2} : Finset V) ∈ (complete V).edges) =
      univ.filter fun p : V × V => p.1 < p.2 := by
    apply Finset.filter_congr
    intro p _
    exact ⟨fun h => h.1, fun h => ⟨h, pair_mem_edges_complete h.ne⟩⟩
  rw [hfilt, Finset.sum_filter, Fintype.sum_prod_type]
  push_cast
  rw [← e.toEquiv.sum_comp]
  refine Finset.sum_congr rfl fun u _ => ?_
  rw [← e.toEquiv.sum_comp]
  refine Finset.sum_congr rfl fun v _ => ?_
  simp only [OrderIso.coe_toEquiv, e.lt_iff_lt]
  split_ifs with h
  · rw [← Sym3.moved_eq_movedNorm]; rfl
  · rfl

theorem gaugeDist_eq (e : Fin k ≃o V) (α : Cochain (complete V) (Perm (Fin 3))) :
    α.gaugeDist (movedNorm (Fin 3)) = (Sym3.gaugeDist (toFin e α) : ℝ) := by
  apply le_antisymm
  · obtain ⟨β₀, hβ₀⟩ := Sym3.exists_cost_eq_gaugeDist (toFin e α)
    refine (α.gaugeDist_le_cost _ (β₀ ∘ e.symm)).trans_eq ?_
    rw [cost_eq e, ← hβ₀]
    congr 2
    funext i; simp
  · exact le_ciInf fun β => by rw [cost_eq e]; exact_mod_cast Sym3.gaugeDist_le _ _

theorem toFin_ofFin (e : Fin k ≃o V) (f : Fin k → Fin k → Sym3.S3) {i j : Fin k} (h : i < j) :
    toFin e (ofFin e f) i j = f i j := by
  simp [toFin, ofFin, h.ne, Sym3.val, h]

theorem defect_ofFin (e : Fin k ≃o V) (f : Fin k → Fin k → Sym3.S3) :
    (ofFin e f).defect (movedNorm (Fin 3)) = (Sym3.defect f : ℝ) := by
  rw [defect_eq e, Sym3.defect_congr fun _ _ => toFin_ofFin e f]

theorem gaugeDist_ofFin (e : Fin k ≃o V) (f : Fin k → Fin k → Sym3.S3) :
    (ofFin e f).gaugeDist (movedNorm (Fin 3)) = (Sym3.gaugeDist f : ℝ) := by
  rw [gaugeDist_eq e, Sym3.gaugeDist_congr fun _ _ => toFin_ofFin e f]

/-- **The bridge.** The `Sym(3)` constant of `complete V` is the `Fin k` constant of
`Sym3` at `k = card V` (any order isomorphism `Fin k ≃o V` witnesses this). -/
theorem h1_eq (e : Fin k ≃o V) :
    h1 (complete V) (movedNorm (Fin 3)) = Sym3.h1 k := by
  unfold h1 Sym3.h1
  congr 1
  ext r
  constructor
  · rintro ⟨α, hα, rfl⟩
    rw [gaugeDist_eq e] at hα ⊢
    rw [defect_eq e]
    exact ⟨toFin e α, by exact_mod_cast hα, rfl⟩
  · rintro ⟨f, hf, rfl⟩
    refine ⟨ofFin e f, ?_, ?_⟩
    · rw [gaugeDist_ofFin]; exact_mod_cast hf
    · rw [defect_ofFin, gaugeDist_ofFin]

/-- The bridge at `k = card V`. -/
theorem h1_eq_card :
    h1 (complete V) (movedNorm (Fin 3)) = Sym3.h1 (Fintype.card V) :=
  h1_eq (Fintype.orderIsoFinOfCardEq V rfl)

end TauCeti.CoboundaryExpansion.Bridge
