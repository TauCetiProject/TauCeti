/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.CoboundaryExpansion.Defs
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
orientation-independence lemma (roadmap 2.3) is needed.
-/

public section

open Finset Equiv Equiv.Perm
open TauCeti.TwoComplex

namespace TauCeti.CoboundaryExpansion.Bridge

variable {V : Type*} [Fintype V] [LinearOrder V]

private theorem pair_mem_edges {u v : V} (h : u ≠ v) : ({u, v} : Finset V) ∈ (complete V).edges :=
  (mem_edges_complete _).2 (Finset.card_pair h)

theorem ne_of_pair_mem_edges {u v : V} (h : ({u, v} : Finset V) ∈ (complete V).edges) : u ≠ v := by
  rintro rfl
  have := (mem_edges_complete _).1 h
  simp at this

private theorem triple_mem_triangles {u v w : V} (h1 : u < v) (h2 : v < w) :
    ({u, v, w} : Finset V) ∈ (complete V).triangles :=
  (mem_triangles_complete _).2
    (Finset.card_eq_three.mpr ⟨u, v, w, h1.ne, (h1.trans h2).ne, h2.ne, rfl⟩)

variable {k : ℕ}

/-- The pullback of a cochain to `Fin k`. -/
@[expose] def toFin (e : Fin k ≃o V) (α : Cochain (complete V) (Perm (Fin 3))) :
    Fin k → Fin k → Sym3.S3 :=
  fun i j => α.toFun (e i) (e j)

/-- A bare function on `Fin k`, read on `u < v` and inverted on `u > v`, as a roadmap cochain. -/
@[expose] def ofFin (e : Fin k ≃o V) (f : Fin k → Fin k → Sym3.S3) :
    Cochain (complete V) (Perm (Fin 3)) where
  toFun u v := Sym3.val f (e.symm u) (e.symm v)
  inv_symm _ _ h :=
    Sym3.val_swap f (fun huv => ne_of_pair_mem_edges h (e.symm.injective huv))

theorem defect_eq (e : Fin k ≃o V) (α : Cochain (complete V) (Perm (Fin 3))) :
    α.defect (movedNorm (Fin 3)) = (Sym3.defect (toFin e α) : ℝ) := by
  unfold Cochain.defect
  rw [Sym3.defect_eq_sum]
  have hfilt : (univ.filter fun p : V × V × V =>
      p.1 < p.2.1 ∧ p.2.1 < p.2.2 ∧ ({p.1, p.2.1, p.2.2} : Finset V) ∈ (complete V).triangles) =
      univ.filter fun p : V × V × V => p.1 < p.2.1 ∧ p.2.1 < p.2.2 := by
    apply Finset.filter_congr
    intro p _
    exact ⟨fun h => ⟨h.1, h.2.1⟩, fun h => ⟨h.1, h.2, triple_mem_triangles h.1 h.2⟩⟩
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
    rw [← Sym3.moved_eq_movedNorm, α.inv_symm (e u) (e w) (pair_mem_edges (e.injective.ne huw.ne))]
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
    exact ⟨fun h => h.1, fun h => ⟨h, pair_mem_edges h.ne⟩⟩
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

private theorem cost_nonneg (α : Cochain (complete V) (Perm (Fin 3))) (β : V → Perm (Fin 3)) :
    0 ≤ α.cost (movedNorm (Fin 3)) β :=
  Finset.sum_nonneg fun _ _ => apply_nonneg _ _

theorem gaugeDist_eq (e : Fin k ≃o V) (α : Cochain (complete V) (Perm (Fin 3))) :
    α.gaugeDist (movedNorm (Fin 3)) = (Sym3.gaugeDist (toFin e α) : ℝ) := by
  unfold Cochain.gaugeDist
  apply le_antisymm
  · obtain ⟨β₀, hβ₀⟩ := Sym3.exists_cost_eq_gaugeDist (toFin e α)
    refine (ciInf_le ⟨0, ?_⟩ (β₀ ∘ e.symm)).trans ?_
    · rintro _ ⟨β, rfl⟩
      exact cost_nonneg α β
    · rw [cost_eq e, ← hβ₀]
      have : (β₀ ∘ e.symm) ∘ e = β₀ := by funext i; simp
      rw [this]
  · refine le_ciInf fun β => ?_
    rw [cost_eq e]
    exact_mod_cast Sym3.gaugeDist_le _ _

/-- Reading a bare function through `val` changes neither its defect nor its gauge distance. -/
private theorem defect_val (f : Fin k → Fin k → Sym3.S3) :
    Sym3.defect (fun i j => Sym3.val f i j) = Sym3.defect f := by
  rw [Sym3.defect_eq_sum, Sym3.defect_eq_sum]
  refine Finset.sum_congr rfl fun u _ => Finset.sum_congr rfl fun v _ =>
    Finset.sum_congr rfl fun w _ => ?_
  split_ifs with h
  · obtain ⟨huv, hvw⟩ := h
    have huw : u < w := huv.trans hvw
    simp [Sym3.hol, Sym3.val, huv, hvw, huw, not_lt.mpr huw.le]
  · rfl

theorem cost_val (f : Fin k → Fin k → Sym3.S3) (β : Fin k → Sym3.S3) :
    Sym3.cost (fun i j => Sym3.val f i j) β = Sym3.cost f β := by
  rw [Sym3.cost_eq_sum, Sym3.cost_eq_sum]
  refine Finset.sum_congr rfl fun u _ => Finset.sum_congr rfl fun v _ => ?_
  split_ifs with h
  · simp [Sym3.val, h]
  · rfl

private theorem gaugeDist_val (f : Fin k → Fin k → Sym3.S3) :
    Sym3.gaugeDist (fun i j => Sym3.val f i j) = Sym3.gaugeDist f := by
  unfold Sym3.gaugeDist
  simp only [cost_val]

theorem toFin_ofFin (e : Fin k ≃o V) (f : Fin k → Fin k → Sym3.S3) :
    toFin e (ofFin e f) = fun i j => Sym3.val f i j := by
  funext i j
  simp [toFin, ofFin]

theorem defect_ofFin (e : Fin k ≃o V) (f : Fin k → Fin k → Sym3.S3) :
    (ofFin e f).defect (movedNorm (Fin 3)) = (Sym3.defect f : ℝ) := by
  rw [defect_eq e, toFin_ofFin, defect_val]

theorem gaugeDist_ofFin (e : Fin k ≃o V) (f : Fin k → Fin k → Sym3.S3) :
    (ofFin e f).gaugeDist (movedNorm (Fin 3)) = (Sym3.gaugeDist f : ℝ) := by
  rw [gaugeDist_eq e, toFin_ofFin, gaugeDist_val]

/-- **The bridge.** The roadmap's `Sym(3)` constant of `complete V` is the `Fin k` constant of
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
