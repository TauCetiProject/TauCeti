/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Module.LinearMap.End
public import Mathlib.Algebra.Module.Submodule.Range
public import Mathlib.LinearAlgebra.LinearIndependent.Defs
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise

/-!
# Spanning and linear independence of iterates of nilpotent endomorphisms

For a nilpotent endomorphism `d : Module.End R M` with `d ^ p = 0` and a submodule `W` of `M`,
this file proves spanning and linear-independence criteria for the iterates `d ^ r` (`r < p`)
applied to `W`.

## Main results

* `Module.End.iSup_map_pow_eq_top_of_codisjoint`: iterates `W.map (d ^ r)` (`r < p`) span `M`
  when `d ^ p = 0` and `Codisjoint (LinearMap.range d) W`.
* `Module.End.eq_zero_of_sum_pow_eq_zero`: `∑ r : Fin p, (d ^ r) (w r) = 0` forces `w r = 0` when
  `Disjoint (LinearMap.range d) W` and `ker (d ^ (p - 1)) ≤ range d`.
* `Module.End.linearIndependent_pow_of_disjoint`: linear independence of `(i, r) ↦ (d ^ r) (v i)`
  from linear independence of `v : ι → W` over a ring.
-/

public section

namespace Module.End

section Semiring

variable {R M : Type*} [Semiring R] [AddCommMonoid M] [Module R M]

/-- If `d ^ p = 0` and `W` is codisjoint from `LinearMap.range d`, then the images `W.map (d ^ r)`
for `r : Fin p` span `M`. -/
theorem iSup_map_pow_eq_top_of_codisjoint (d : Module.End R M) {W : Submodule R M}
    (hW : Codisjoint (LinearMap.range d) W) {p : ℕ} (hd : d ^ p = 0) :
    ⨆ r : Fin p, W.map (d ^ (r : ℕ)) = ⊤ := by
  refine top_unique ?_
  have hstep : ∀ m ≤ p, (⊤ : Submodule R M) ≤
      (⨆ (r : Fin p) (_ : (r : ℕ) < m), W.map (d ^ (r : ℕ))) ⊔ LinearMap.range (d ^ m) := by
    intro m hm
    induction m with
    | zero => simp [Module.End.one_eq_id]
    | succ m ih =>
      refine (ih (by omega)).trans (sup_le ?_ ?_)
      · exact le_sup_of_le_left <| iSup₂_mono' fun r hr ↦ ⟨r, by omega, le_rfl⟩
      · rintro _ ⟨x, rfl⟩
        rcases Submodule.mem_sup.mp (hW.eq_top ▸ Submodule.mem_top : x ∈ LinearMap.range d ⊔ W)
          with ⟨_, ⟨y, rfl⟩, w, hw, rfl⟩
        rw [_root_.map_add]
        exact add_mem
          (Submodule.mem_sup_right ⟨y, by rw [pow_succ, mul_apply_eq_comp]⟩)
          (Submodule.mem_sup_left <|
            (le_iSup₂ (f := fun (r : Fin p) (_ : (r : ℕ) < m + 1) ↦ W.map (d ^ (r : ℕ)))
              ⟨m, hm⟩ (Nat.lt_succ_self m)) ⟨w, hw, rfl⟩)
  simpa [hd] using hstep p le_rfl

/-- If `d ^ p = 0`, `W` is disjoint from `LinearMap.range d`, and `ker (d ^ (p - 1)) ≤ range d`,
then `∑ r : Fin p, (d ^ r) (w r) = 0` for `w : Fin p → W` forces `w r = 0` for every `r`. -/
theorem eq_zero_of_sum_pow_eq_zero (d : Module.End R M) {W : Submodule R M}
    (hW : Disjoint (LinearMap.range d) W) {p : ℕ} (hd : d ^ p = 0)
    (hker : LinearMap.ker (d ^ (p - 1)) ≤ LinearMap.range d)
    {w : Fin p → W} (hsum : ∑ r : Fin p, (d ^ (r : ℕ)) (w r : M) = 0) (r : Fin p) :
    w r = 0 := by
  suffices h : ∀ n (hn : n < p), w ⟨n, hn⟩ = 0 from h r.val r.isLt
  intro n
  induction n using Nat.strong_induction_on with
  | ind n ih =>
    intro hn
    have happ := congrArg (d ^ (p - 1 - n)) hsum
    rw [_root_.map_zero, _root_.map_sum] at happ
    have hsingle : ∑ t : Fin p, (d ^ (p - 1 - n)) ((d ^ (t : ℕ)) (w t : M)) =
        (d ^ (p - 1)) (w ⟨n, hn⟩ : M) := by
      rw [Finset.sum_eq_single ⟨n, hn⟩]
      · rw [← mul_apply_eq_comp, ← pow_add, show p - 1 - n + n = p - 1 by omega]
      · intro t _ htne
        rcases lt_trichotomy (t : ℕ) n with hlt | heq | hgt
        · simp [ih t hlt t.isLt]
        · exact absurd (Fin.ext heq) htne
        · rw [← mul_apply_eq_comp, ← pow_add,
            pow_eq_zero_of_le (by omega : p ≤ p - 1 - n + t) hd, LinearMap.zero_apply]
      · simp
    rw [hsingle] at happ
    exact Subtype.ext <| (Submodule.mem_bot R).mp <| hW.eq_bot ▸
      (⟨hker (LinearMap.mem_ker.mpr happ), (w ⟨n, hn⟩).property⟩ :
        (w ⟨n, hn⟩ : M) ∈ LinearMap.range d ⊓ W)

end Semiring

section Ring

variable {R M : Type*} [Ring R] [AddCommGroup M] [Module R M]

/-- If `d ^ p = 0`, `W` is disjoint from `LinearMap.range d`, and `ker (d ^ (p - 1)) ≤ range d`,
then any linearly independent family `v : ι → W` produces a linearly independent family
`(i, r) ↦ (d ^ r) (v i)` indexed by `ι × Fin p`. -/
theorem linearIndependent_pow_of_disjoint (d : Module.End R M) {W : Submodule R M}
    (hW : Disjoint (LinearMap.range d) W) {p : ℕ} (hd : d ^ p = 0)
    (hker : LinearMap.ker (d ^ (p - 1)) ≤ LinearMap.range d)
    {ι : Type*} {v : ι → W} (hv : LinearIndependent R v) :
    LinearIndependent R (fun ir : ι × Fin p ↦ (d ^ (ir.2 : ℕ)) (v ir.1 : M)) := by
  classical
  rw [linearIndependent_iff']
  intro s c hc ir hir
  let w : Fin p → W := fun r ↦
    ∑ i ∈ s.image Prod.fst, (if (i, r) ∈ s then c (i, r) else 0) • v i
  have hsum : ∑ r : Fin p, (d ^ (r : ℕ)) (w r : M) = 0 := by
    have h1 : ∑ r : Fin p, (d ^ (r : ℕ)) (w r : M) = ∑ i ∈ s.image Prod.fst, ∑ r : Fin p,
        (if (i, r) ∈ s then c (i, r) • (d ^ (r : ℕ)) (v i : M) else 0) := by
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun r _ ↦ ?_
      simp only [w, Submodule.coe_sum, Submodule.coe_smul_of_tower, _root_.map_sum, map_smul]
      exact Finset.sum_congr rfl fun i _ ↦ by split_ifs <;> simp
    rw [h1, ← Finset.sum_product', ← Finset.sum_subset (fun x hx ↦
      Finset.mem_product.mpr ⟨Finset.mem_image_of_mem _ hx, Finset.mem_univ _⟩)
      (fun _ _ hx ↦ by simp [hx])]
    simpa using hc
  have hwir := d.eq_zero_of_sum_pow_eq_zero hW hd hker hsum ir.2
  simpa [hir] using linearIndependent_iff'.mp hv (s.image Prod.fst)
    (fun i ↦ if (i, ir.2) ∈ s then c (i, ir.2) else 0) hwir ir.1
    (Finset.mem_image_of_mem Prod.fst hir)

end Ring

end Module.End
