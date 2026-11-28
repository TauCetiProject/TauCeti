/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Data.Fintype.Card
public import Mathlib.GroupTheory.Coset.Defs
import Mathlib.Algebra.BigOperators.Module
import Mathlib.Data.Fintype.BigOperators
import Mathlib.GroupTheory.Index

/-!
# Right stabilizers and left-translation-invariant sums over coset representatives

For a function `f : G → W` on a group `G`, its right stabilizer `TauCeti.rightStabilizer f` is the
subgroup `{k : G | ∀ g, f (g * k) = f g}`. For any finite-index subgroup `H ≤ G` and any right
`H`-invariant function `f : G → B` valued in an additive commutative monoid, the sum of `f` over
left coset representatives `q.out` (`q : G ⧸ H`) is independent of the choice of section
(`TauCeti.sum_coset_eq_sum_out`) and invariant under left translation
(`TauCeti.sum_mul_out_eq_sum_out`).

## Main definitions and results

* `TauCeti.rightStabilizer`: the subgroup of elements `k : G` with `f (g * k) = f g` for all `g`.
* `TauCeti.mem_rightStabilizer_iff`: membership characterization of `rightStabilizer f`.
* `TauCeti.sum_coset_eq_sum_out`: independence of coset representatives for right `H`-invariant `f`.
* `TauCeti.sum_mul_out_eq_sum_out`: left-translation invariance `∑ q : G ⧸ H, f (a * q.out) =
  ∑ q : G ⧸ H, f q.out`.
* `TauCeti.card_subgroup_nsmul_sum_out`: for finite `G`, `|H| • ∑ q : G ⧸ H, f q.out = ∑ g, f g`.

## Provenance

Adapted from `New.rightStabilizer` and `New.sum_mul_out` in `grh-lean`
(https://github.com/lsernau/grh-lean, commit `72fead102f663d5c7a407964a13dc0cf9d977207`,
file `src/Lib/Adelic/Hecke/ClassSums.lean`).
-/

public section

namespace TauCeti

variable {G W B : Type*} [Group G]

/-- The right stabilizer of `f : G → W`: the subgroup of elements `k : G` such that
`f (g * k) = f g` for all `g : G`. -/
def rightStabilizer (f : G → W) : Subgroup G where
  carrier := {k : G | ∀ g : G, f (g * k) = f g}
  mul_mem' {a b} ha hb g := by rw [← mul_assoc, hb, ha]
  one_mem' g := by rw [mul_one]
  inv_mem' {a} ha g := by rw [← ha, inv_mul_cancel_right]

/-- Membership in `rightStabilizer f` says `f (g * k) = f g` for all `g : G`. -/
@[simp]
theorem mem_rightStabilizer_iff {f : G → W} {k : G} :
    k ∈ rightStabilizer f ↔ ∀ g : G, f (g * k) = f g :=
  Iff.rfl

/-- For a right `H`-invariant function `f : G → B`, summing `f` over any section `s : G ⧸ H → G`
of the quotient projection equals the sum over the chosen representatives `q.out`. -/
theorem sum_coset_eq_sum_out [AddCommMonoid B] (H : Subgroup G) [Fintype (G ⧸ H)]
    {f : G → B} (hf : H ≤ rightStabilizer f) {s : G ⧸ H → G}
    (hs : ∀ q : G ⧸ H, (s q : G ⧸ H) = q) :
    ∑ q : G ⧸ H, f (s q) = ∑ q : G ⧸ H, f q.out := by
  refine Finset.sum_congr rfl fun q _ ↦ ?_
  have hmem : q.out⁻¹ * s q ∈ H :=
    QuotientGroup.eq.mp ((Quotient.out_eq q).trans (hs q).symm)
  have hmul : q.out * (q.out⁻¹ * s q) = s q := mul_inv_cancel_left q.out (s q)
  rw [← hmul, hf hmem]

/-- A sum over coset representatives of `G ⧸ H` of a right `H`-invariant function does not change
under left translation by any `a : G`. -/
theorem sum_mul_out_eq_sum_out [AddCommMonoid B] (H : Subgroup G) [Fintype (G ⧸ H)]
    {f : G → B} (hf : H ≤ rightStabilizer f) (a : G) :
    ∑ q : G ⧸ H, f (a * q.out) = ∑ q : G ⧸ H, f q.out := by
  refine Fintype.sum_equiv (MulAction.toPerm a) _ _ fun q ↦ ?_
  obtain ⟨y, hy⟩ := QuotientGroup.mk_out_eq_mul H (a * q.out)
  rw [MulAction.toPerm_apply, ← MulAction.Quotient.mk_smul_out, smul_eq_mul, hy, hf y.property]

/-- For a finite group `G` and a right `H`-invariant function `f : G → B`, summing `f` over `G`
equals `|H|` times the sum over coset representatives `G ⧸ H`. -/
theorem card_subgroup_nsmul_sum_out [AddCommMonoid B] [Fintype G] (H : Subgroup G)
    [Fintype H] [Fintype (G ⧸ H)] {f : G → B} (hf : H ≤ rightStabilizer f) :
    Fintype.card H • ∑ q : G ⧸ H, f q.out = ∑ g : G, f g := by
  let e : (G ⧸ H) × H ≃ G :=
    { toFun := fun p ↦ p.fst.out * (p.snd : G)
      invFun := fun g ↦
        (g, ⟨((g : G ⧸ H).out)⁻¹ * g, QuotientGroup.eq.mp (Quotient.out_eq (g : G ⧸ H))⟩)
      left_inv := fun ⟨q, h⟩ ↦ by
        have hq : ((q.out * (h : G) : G) : G ⧸ H) = q := by
          rw [← Quotient.out_eq q]
          exact QuotientGroup.eq.mpr (by simp [h.property])
        ext
        · exact hq
        · simp [hq]
      right_inv := fun g ↦ mul_inv_cancel_left _ g }
  have hprod : ∑ p : (G ⧸ H) × H, f (p.fst.out * (p.snd : G)) = ∑ g : G, f g :=
    Fintype.sum_equiv e _ _ fun _ ↦ rfl
  rw [← hprod, Fintype.sum_prod_type]
  calc Fintype.card H • ∑ q : G ⧸ H, f q.out
      = ∑ _h : H, ∑ q : G ⧸ H, f q.out := by simp
    _ = ∑ q : G ⧸ H, ∑ _h : H, f q.out := Finset.sum_comm
    _ = ∑ q : G ⧸ H, ∑ h : H, f (q.out * (h : G)) :=
      Finset.sum_congr rfl fun q _ ↦ Finset.sum_congr rfl fun h _ ↦ (hf h.property q.out).symm

end TauCeti
