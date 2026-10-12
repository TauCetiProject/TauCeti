/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Module.Submodule.Bilinear
public import TauCeti.Topology.Algebra.Group.LowerCentralSeries.Graded.Pow
public import TauCeti.Topology.Algebra.Group.LowerCentralSeries.Graded.Span

/-!
# The bracket span of the graded pieces of the lower `p`-series

Let `G` be a topological group with lower `p`-series `λ_k = λ_k(G)` and graded pieces
`gr_k(G) = λ_k ⧸ λ_{k+1}`. The **bracket span** `C_{k+1}(G) ≤ gr_{k+1}(G)`
(`TauCeti.gradedBracketSpan`) is the `ZMod p`-submodule spanned by the brackets `[x, y]` with
`x ∈ gr_k(G)` and `y ∈ gr_0(G)`, that is by the classes of the commutators `⁅a, b⁆` with `a ∈ λ_k`
and `b ∈ G` (`TauCeti.gradedBracketSpan_eq_span`); membership in it is eliminated by the induction
principle `TauCeti.gradedBracketSpan_induction`. Every element of it is the class of an element of
`λ_{k+1}` lying in the commutator subgroup
(`TauCeti.exists_mem_commutator_gradedMk_eq_of_mem_gradedBracketSpan`), and the `p`-power
operator `π` carries `C_{k+1}(G)` into `C_{k+2}(G)` (`TauCeti.gradedPow_mem_gradedBracketSpan`).

One identity on the iterated `p`-powers `π^j x` of degree-zero classes accompanies it: the
symmetrised bracket `[π^{k+1} x, y] + [π^{k+1} y, x]` lies in the span of the brackets `[c, z]` with
`c ∈ C_{k+1}(G)` and `z ∈ gr_0(G)` (`TauCeti.gradedBracket_gradedPowIter_add_swap_mem_map₂`). In
degree `k = 0`, expanding `[π (x + y), x + y] = 0` with the additivity defect
`π (x + y) = π x + π y + (p choose 2) • [y, x]` (`TauCeti.gradedPow_add_zero`) gives the sum as
`-(p choose 2) • ([[y, x], x] + [[y, x], y])`, brackets with the class `[y, x] ∈ C_1(G)`; this is
why the statement is a membership rather than a vanishing. The vanishing `[π^j x, x] = 0` that it
rests on is `TauCeti.gradedBracket_gradedPowIter_self` in `Graded/Pow.lean`.

Finally, when `λ_{k+2}` is open, `gr_{k+1}(G)` is the sum of `C_{k+1}(G)` and the span of the
iterated `p`-powers `π^{k+1} x` of the degree-zero classes
(`TauCeti.gradedBracketSpan_sup_span_range_gradedPowIter_eq_top`): this is the graded form of
`λ_{k+1} = closure (λ_kᵖ ⬝ [λ_k, G])`, iterated down to degree zero.

For the free pro-`p` group `F` of finite rank and `k ≥ 1`, the bracket span `C_{k+1}(F)` is the
image of the basis-modification map `δ_ρ` of every relator class `ρ ∈ gr_1(F)` without `p`-power
part whose partial derivatives span `gr_0(F)`
(`TauCeti.freeProP.range_basisModificationDelta_eq_span_of_repr_inl_eq_zero`); the statements here
are what the pivot-constrained span statement of the classification of Demushkin groups uses.

## Main definitions

* `TauCeti.gradedBracketSpan`: the bracket span `C_{k+1}(G) ≤ gr_{k+1}(G)`.

## Main results

* `TauCeti.gradedBracketSpan_eq_span` and `TauCeti.gradedBracketSpan_induction`: the bracket span
  as a span, and induction on its elements.
* `TauCeti.exists_mem_commutator_gradedMk_eq_of_mem_gradedBracketSpan`: every element of
  `C_{k+1}(G)` is the class of an element of `λ_{k+1}` in the commutator subgroup.
* `TauCeti.gradedPow_mem_gradedBracketSpan`: `π C_{k+1}(G) ≤ C_{k+2}(G)`.
* `TauCeti.gradedBracket_gradedPowIter_add_swap_mem_map₂`:
  `[π^{k+1} x, y] + [π^{k+1} y, x] ∈ [C_{k+1}(G), gr_0(G)]`.
* `TauCeti.gradedBracketSpan_sup_span_range_gradedPowIter_eq_top`:
  `gr_{k+1}(G) = C_{k+1}(G) + span {π^{k+1} x}` when `λ_{k+2}` is open.

## References

* J. Labute, *Classification of Demushkin groups*, Canadian J. Math. 19 (1967), §1,
  Propositions 1 and 2, and §3.
-/

public section

namespace TauCeti

open Subgroup Submodule
open scoped commutatorElement

universe u

variable {p : ℕ} {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

/-! ### The bracket span -/

variable (p G) in
/-- **The bracket span** `C_{k+1}(G) ≤ gr_{k+1}(G)`: the `ZMod p`-submodule spanned by the brackets
`[x, y]` with `x ∈ gr_k(G)` and `y ∈ gr_0(G)`, that is by the classes of the commutators `⁅a, b⁆`
with `a ∈ λ_k(G)` and `b ∈ G`; it is the bilinear image `Submodule.map₂` of the bracket
`TauCeti.gradedBracketLinear` on the whole of `gr_k(G) × gr_0(G)`
(`TauCeti.gradedBracketSpan_eq_span` restates it as a span). Its elements are classes of
elements of the commutator subgroup
(`TauCeti.exists_mem_commutator_gradedMk_eq_of_mem_gradedBracketSpan`), and `π` carries it into
`C_{k+2}(G)` (`TauCeti.gradedPow_mem_gradedBracketSpan`). -/
def gradedBracketSpan (k : ℕ) : Submodule (ZMod p) (gradedPiece p G (k + 1)) :=
  Submodule.map₂ (gradedBracketLinear p G k 0) ⊤ ⊤

/-- A bracket `[x, y]` with `y` of degree zero lies in the bracket span. -/
@[simp]
theorem gradedBracket_mem_gradedBracketSpan {k : ℕ} (x : gradedPiece p G k)
    (y : gradedPiece p G 0) : gradedBracket p G k 0 x y ∈ gradedBracketSpan p G k := by
  rw [← gradedBracketLinear_apply]
  exact Submodule.apply_mem_map₂ _ Submodule.mem_top Submodule.mem_top

/-- **The bracket span as a span**: `C_{k+1}(G)` is the span of the brackets `[x, y]` with
`x ∈ gr_k(G)` and `y ∈ gr_0(G)`. -/
theorem gradedBracketSpan_eq_span (k : ℕ) :
    gradedBracketSpan p G k =
      span (ZMod p) (Set.range fun xy : gradedPiece p G k × gradedPiece p G 0 ↦
        gradedBracket p G k 0 xy.1 xy.2) := by
  rw [gradedBracketSpan, Submodule.map₂_eq_span_image2]
  congr 1
  ext z
  simp only [Set.mem_image2, Submodule.top_coe, Set.mem_univ, true_and, Set.mem_range, Prod.exists,
    gradedBracketLinear_apply]

/-- **Induction on the bracket span**: a predicate that holds on the brackets `[x, y]` with `y` of
degree zero and on `0`, and is closed under addition and scalar multiplication, holds on all of
`C_{k+1}(G)`. -/
@[elab_as_elim]
theorem gradedBracketSpan_induction {k : ℕ}
    {motive : (z : gradedPiece p G (k + 1)) → z ∈ gradedBracketSpan p G k → Prop}
    (bracket : ∀ (x : gradedPiece p G k) (y : gradedPiece p G 0),
      motive (gradedBracket p G k 0 x y) (gradedBracket_mem_gradedBracketSpan x y))
    (zero : motive 0 (zero_mem _))
    (add : ∀ x y hx hy, motive x hx → motive y hy → motive (x + y) (add_mem hx hy))
    (smul : ∀ (c : ZMod p) x hx, motive x hx → motive (c • x) (smul_mem _ c hx))
    {z : gradedPiece p G (k + 1)} (hz : z ∈ gradedBracketSpan p G k) : motive z hz := by
  have hz' : z ∈ span (ZMod p) (Set.range fun xy : gradedPiece p G k × gradedPiece p G 0 ↦
      gradedBracket p G k 0 xy.1 xy.2) := (gradedBracketSpan_eq_span k).le hz
  refine span_induction (p := fun z h ↦ motive z ((gradedBracketSpan_eq_span k).ge h))
    ?_ zero ?_ ?_ hz'
  · rintro _ ⟨⟨x, y⟩, rfl⟩
    exact bracket x y
  · intro x y _ _ ihx ihy
    exact add x y _ _ ihx ihy
  · intro c x _ ih
    exact smul c x _ ih

/-- A submodule contains the bracket span if and only if it contains every bracket `[x, y]` with
`y` of degree zero. -/
@[simp]
theorem gradedBracketSpan_le_iff {k : ℕ} {W : Submodule (ZMod p) (gradedPiece p G (k + 1))} :
    gradedBracketSpan p G k ≤ W ↔
      ∀ (x : gradedPiece p G k) (y : gradedPiece p G 0), gradedBracket p G k 0 x y ∈ W := by
  simp only [gradedBracketSpan, Submodule.map₂_le, Submodule.mem_top, true_implies,
    gradedBracketLinear_apply]

/-- **Elements of the bracket span have representatives in the commutator subgroup**: every
element of `C_{k+1}(G)` is the class of an element of `λ_{k+1}(G)` lying in the commutator subgroup
of `G`. -/
theorem exists_mem_commutator_gradedMk_eq_of_mem_gradedBracketSpan {k : ℕ}
    {y : gradedPiece p G (k + 1)} (hy : y ∈ gradedBracketSpan p G k) :
    ∃ z : pLowerCentralSeries p G (k + 1), (z : G) ∈ commutator G ∧ gradedMk p G (k + 1) z = y := by
  induction hy using gradedBracketSpan_induction with
  | bracket x y =>
    obtain ⟨x, rfl⟩ := gradedMk_surjective k x
    obtain ⟨y, rfl⟩ := gradedMk_surjective 0 y
    refine ⟨⟨⁅(x : G), (y : G)⁆, commutator_mem_pLowerCentralSeries x.2 y.2⟩, ?_,
      (gradedBracket_gradedMk x y).symm⟩
    rw [commutator_def]
    exact commutator_mem_commutator (mem_top _) (mem_top _)
  | zero => exact ⟨1, one_mem _, gradedMk_one _⟩
  | add x y _ _ hx hy =>
    obtain ⟨z, hz, rfl⟩ := hx
    obtain ⟨z', hz', rfl⟩ := hy
    exact ⟨z * z', mul_mem hz hz', gradedMk_mul z z'⟩
  | smul c x _ hx =>
    obtain ⟨z, hz, rfl⟩ := hx
    refine ⟨z ^ (c.cast : ℤ), zpow_mem hz _, ?_⟩
    rw [gradedMk_zpow, ← Int.cast_smul_eq_zsmul (ZMod p), ZMod.intCast_zmod_cast]

/-- **`π` carries the bracket span into the next bracket span**: `π C_{k+1}(G) ≤ C_{k+2}(G)`. Away
from degree zero `π [x, y] = [π x, y]`, and in degree zero
`π [x, y] = [π x, y] + (p choose 2) • [[x, y], x]` is again a sum of brackets. -/
theorem gradedPow_mem_gradedBracketSpan {k : ℕ} {x : gradedPiece p G (k + 1)}
    (hx : x ∈ gradedBracketSpan p G k) :
    gradedPow p G (k + 1) x ∈ gradedBracketSpan p G (k + 1) := by
  have h : (gradedBracketSpan p G k).map
      ((gradedPowAddMonoidHom p G (Nat.le_add_left 1 k)).toZModLinearMap p) ≤
        gradedBracketSpan p G (k + 1) := by
    rw [Submodule.map_le_iff_le_comap]
    refine Submodule.map₂_le.mpr fun x _ y _ ↦ ?_
    rw [Submodule.mem_comap, AddMonoidHom.coe_toZModLinearMap, gradedPowAddMonoidHom_apply,
      gradedBracketLinear_apply]
    cases k with
    | zero =>
      rw [gradedPow_gradedBracket_zero_zero]
      exact add_mem (gradedBracket_mem_gradedBracketSpan _ _)
        (nsmul_mem (gradedBracket_mem_gradedBracketSpan _ _) _)
    | succ k =>
      rw [gradedPow_gradedBracket_left_zero (Nat.le_add_left 1 k)]
      exact gradedBracket_mem_gradedBracketSpan _ _
  exact h ⟨x, hx, by rw [AddMonoidHom.coe_toZModLinearMap, gradedPowAddMonoidHom_apply]⟩

/-- **`π` carries brackets with the bracket span into brackets with the next bracket span**: if
`w` is a sum of brackets `[c, z]` with `c ∈ C_{k+1}(G)` and `z ∈ gr_0(G)`, then `π w` is a sum of
brackets `[c', z]` with `c' ∈ C_{k+2}(G)`. -/
theorem gradedPow_mem_map₂_gradedBracketLinear_gradedBracketSpan {k : ℕ}
    {w : gradedPiece p G (k + 1 + 1)}
    (hw : w ∈ Submodule.map₂ (gradedBracketLinear p G (k + 1) 0) (gradedBracketSpan p G k) ⊤) :
    gradedPow p G (k + 1 + 1) w ∈
      Submodule.map₂ (gradedBracketLinear p G (k + 1 + 1) 0) (gradedBracketSpan p G (k + 1)) ⊤ := by
  have h : (Submodule.map₂ (gradedBracketLinear p G (k + 1) 0) (gradedBracketSpan p G k) ⊤).map
      ((gradedPowAddMonoidHom p G (Nat.le_add_left 1 (k + 1))).toZModLinearMap p) ≤
        Submodule.map₂ (gradedBracketLinear p G (k + 1 + 1) 0)
          (gradedBracketSpan p G (k + 1)) ⊤ := by
    rw [Submodule.map_le_iff_le_comap]
    refine Submodule.map₂_le.mpr fun c hc z _ ↦ ?_
    rw [Submodule.mem_comap, AddMonoidHom.coe_toZModLinearMap, gradedPowAddMonoidHom_apply,
      gradedBracketLinear_apply, gradedPow_gradedBracket_left_zero (Nat.le_add_left 1 k),
      ← gradedBracketLinear_apply]
    exact Submodule.apply_mem_map₂ _ (gradedPow_mem_gradedBracketSpan hc) Submodule.mem_top
  exact h ⟨w, hw, by rw [AddMonoidHom.coe_toZModLinearMap, gradedPowAddMonoidHom_apply]⟩

/-- **The symmetrised bracket of iterated `p`-powers**: for `x, y ∈ gr_0(G)`,
`[π^{k+1} x, y] + [π^{k+1} y, x]` is a sum of brackets `[c, z]` with `c ∈ C_{k+1}(G)` and
`z ∈ gr_0(G)`. -/
theorem gradedBracket_gradedPowIter_add_swap_mem_map₂ (k : ℕ) (x y : gradedPiece p G 0) :
    gradedBracket p G (k + 1) 0 (gradedPowIter p G (k + 1) x) y +
        gradedBracket p G (k + 1) 0 (gradedPowIter p G (k + 1) y) x ∈
      Submodule.map₂ (gradedBracketLinear p G (k + 1) 0) (gradedBracketSpan p G k) ⊤ := by
  induction k with
  | zero =>
    -- Expand `[π (x + y), x + y] = 0` with the degree-zero formula for `π (x + y)`: the sum is
    -- `-(p choose 2) • ([[y, x], x] + [[y, x], y])`, brackets with the class `[y, x] ∈ C_1(G)`.
    have h := gradedBracket_gradedPow_self (x + y)
    simp only [gradedPowIter_succ, gradedPowIter_zero]
    rw [gradedPow_add_zero, ← gradedBracketLinear_apply] at h
    simp only [map_add, LinearMap.add_apply, map_nsmul, LinearMap.smul_apply,
      gradedBracketLinear_apply, gradedBracket_gradedPow_self, zero_add, add_zero] at h
    have hsum : gradedBracket p G 1 0 (gradedPow p G 0 x) y +
        gradedBracket p G 1 0 (gradedPow p G 0 y) x =
          -(p.choose 2 • gradedBracket p G 1 0 (gradedBracket p G 0 0 y x) x +
            p.choose 2 • gradedBracket p G 1 0 (gradedBracket p G 0 0 y x) y) := by
      rw [eq_neg_iff_add_eq_zero, ← h]
      abel
    rw [hsum]
    refine neg_mem (add_mem (nsmul_mem ?_ _) (nsmul_mem ?_ _)) <;>
      rw [← gradedBracketLinear_apply] <;>
      exact Submodule.apply_mem_map₂ _ (gradedBracket_mem_gradedBracketSpan y x) Submodule.mem_top
  | succ k ih =>
    -- Away from degree zero `π` commutes with the bracket, so `π` propagates the statement.
    rw [gradedPowIter_succ (k + 1) x, gradedPowIter_succ (k + 1) y,
      ← gradedPow_gradedBracket_left_zero (Nat.le_add_left 1 k) (gradedPowIter p G (k + 1) x) y,
      ← gradedPow_gradedBracket_left_zero (Nat.le_add_left 1 k) (gradedPowIter p G (k + 1) y) x,
      ← gradedPow_add_of_one_le (Nat.le_add_left 1 (k + 1))]
    exact gradedPow_mem_map₂_gradedBracketLinear_gradedBracketSpan ih

/-! ### The bracket span and the iterated `p`-powers span the graded piece -/

/-- **The bracket span and the iterated `p`-powers span the graded piece**: when `λ_{k+2}` is open,
`gr_{k+1}(G) = C_{k+1}(G) + span {π^{k+1} x | x ∈ gr_0(G)}`. This is the graded form of
`λ_{k+1} = closure (λ_kᵖ ⬝ [λ_k, G])` iterated down to degree zero. -/
theorem gradedBracketSpan_sup_span_range_gradedPowIter_eq_top {k : ℕ}
    (h : IsOpen (pLowerCentralSeries p G (k + 1 + 1) : Set G)) :
    gradedBracketSpan p G k ⊔ span (ZMod p) (Set.range (gradedPowIter p G (k + 1))) = ⊤ := by
  induction k with
  | zero =>
    refine eq_top_of_forall_gradedPow_mem_of_forall_gradedBracket_mem h
      (fun v ↦ mem_sup_right (subset_span ⟨v, ?_⟩))
      fun v y ↦ mem_sup_left (gradedBracket_mem_gradedBracketSpan v y)
    rw [gradedPowIter_succ, gradedPowIter_zero]
  | succ k ih =>
    have ih := ih (Subgroup.isOpen_mono (pLowerCentralSeries_antitone (by omega)) h)
    refine eq_top_of_forall_gradedPow_mem_of_forall_gradedBracket_mem h (fun v ↦ ?_)
      fun v y ↦ mem_sup_left (gradedBracket_mem_gradedBracketSpan v y)
    have hv : v ∈ gradedBracketSpan p G k ⊔
        span (ZMod p) (Set.range (gradedPowIter p G (k + 1))) := by
      rw [ih]
      exact mem_top
    obtain ⟨c, hc, t, ht, rfl⟩ := mem_sup.mp hv
    rw [gradedPow_add_of_one_le (Nat.le_add_left 1 k)]
    refine add_mem (mem_sup_left (gradedPow_mem_gradedBracketSpan hc)) (mem_sup_right ?_)
    exact gradedPow_mem_span_range_gradedPowIter_succ id (Nat.le_add_left 1 k) ht

end TauCeti
