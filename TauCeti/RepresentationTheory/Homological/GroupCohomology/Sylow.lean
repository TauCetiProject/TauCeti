/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.GroupTheory.Sylow
public import TauCeti.RepresentationTheory.Homological.GroupCohomology.Corestriction

/-!
# Torsion of group cohomology and restriction to Sylow subgroups

For a finite group `G`, the composite `Cor ∘ Res : Hⁿ(G, A) ⟶ Hⁿ(S, A) ⟶ Hⁿ(G, A)` is
multiplication by the index `[G : S]`. Taking `S` trivial shows that `Hⁿ(G, A)` is killed by the
order of `G` for `n ≥ 1`; taking `S` a Sylow `p`-subgroup shows that restriction to `S` is
injective on the `p`-primary part of `Hⁿ(G, A)`, because `[G : S]` is prime to `p`. Consequently
`Hⁿ(G, A)` vanishes for `n ≥ 1` as soon as, for every prime `p`, `Hⁿ(P, A)` vanishes for some
Sylow `p`-subgroup `P`, which is the reduction step of Tate's cohomological triviality criterion.

## Main statements

* `groupCohomology.natCard_nsmul_eq_zero`: `Nat.card G • x = 0` for `x ∈ Hⁿ⁺¹(G, A)`.
* `TauCeti.groupCohomology.eq_zero_of_map_sylow_eq_zero`: an element of `Hⁿ(G, A)` killed by a
  power of `p` and by restriction to a Sylow `p`-subgroup is zero.
* `TauCeti.groupCohomology.isZero_of_isZero_sylow`: `Hⁿ⁺¹(G, A) = 0` if, for every prime `p`,
  `Hⁿ⁺¹(P, A) = 0` for some Sylow `p`-subgroup `P`.

## References

* J. S. Milne, *Class Field Theory*, Chapter II, Corollaries 1.31 and 1.33 and Theorem 3.10.
* The same facts appear as `torsion_of_finite_of_neZero` and `groupCohomology_Sylow` in
  `ClassFieldTheory/Cohomology/Functors/Corestriction.lean` and in the Sylow step of
  `ClassFieldTheory/Cohomology/TrivialityCriterion.lean` in `kbuzzard/ClassFieldTheory`, commit
  `ccc3323c6750abca25b49b35106f54eb3a398509`; they are reimplemented here on Tau Ceti's
  corestriction API.
-/

public noncomputable section

universe u

open CategoryTheory Limits Rep

variable {k G : Type u} [CommRing k] [Group G] [Finite G]

namespace groupCohomology

/-- Positive-degree cohomology of a finite group is killed by the order of the group (Milne II
1.31). -/
theorem natCard_nsmul_eq_zero {A : Rep k G} {n : ℕ} (x : groupCohomology A (n + 1)) :
    Nat.card G • x = 0 := by
  -- Restriction to the trivial subgroup lands in the vanishing cohomology of the trivial group.
  simpa using TauCeti.groupCohomology.index_nsmul_eq_zero_of_map_eq_zero ⊥ <|
    (ModuleCat.subsingleton_of_isZero
      (isZero_groupCohomology_succ_of_subsingleton (res (⊥ : Subgroup G).subtype A) n)).allEq _ _

end groupCohomology

namespace TauCeti.groupCohomology

open _root_.groupCohomology

variable (A : Rep k G) (n : ℕ)

/-- **Restriction to a Sylow `p`-subgroup is injective on the `p`-primary part** (Milne II 1.33):
an element of `Hⁿ(G, A)` killed by a power of `p` whose restriction to a Sylow `p`-subgroup `P`
vanishes is zero. -/
theorem eq_zero_of_map_sylow_eq_zero (p : ℕ) [Fact p.Prime] (P : Sylow p G)
    {x : groupCohomology A n} {j : ℕ} (hx : p ^ j • x = 0)
    (h : map (P : Subgroup G).subtype (𝟙 (res (P : Subgroup G).subtype A)) n x = 0) :
    x = 0 := by
  -- `[G : P]` kills `x` and is prime to `p`, hence to `p ^ j`; the two annihilators force `x = 0`.
  exact (nsmul_eq_zero_iff_of_coprime <| Nat.Coprime.pow_left j <|
    (Nat.Prime.coprime_iff_not_dvd ‹Fact p.Prime›.out).2 (Sylow.not_dvd_index P)).1
    ⟨hx, index_nsmul_eq_zero_of_map_eq_zero (P : Subgroup G) h⟩

/-- **The Sylow reduction of Tate's triviality criterion** (Milne II 3.10, last paragraph): if,
for every prime `p`, `Hⁿ⁺¹(P, A) = 0` for some Sylow `p`-subgroup `P`, then `Hⁿ⁺¹(G, A) = 0`. -/
theorem isZero_of_isZero_sylow (h : ∀ (p : ℕ) [Fact p.Prime], ∃ P : Sylow p G,
      IsZero (groupCohomology (res (P : Subgroup G).subtype A) (n + 1))) :
    IsZero (groupCohomology A (n + 1)) := by
  suffices hsub : ∀ (m : ℕ) (x : groupCohomology A (n + 1)), 0 < m → m • x = 0 → x = 0 by
    have : Subsingleton (groupCohomology A (n + 1)) :=
      subsingleton_of_forall_eq 0 fun x ↦ hsub _ x Nat.card_pos (natCard_nsmul_eq_zero x)
    exact ModuleCat.isZero_of_subsingleton _
  intro m
  -- Peel the primes off `m`: an element killed by `p ^ m * a` with `p ∤ a` has `a • x` killed by
  -- `p ^ m` and by restriction to a Sylow `p`-subgroup, hence `a • x = 0`.
  induction m using Nat.recOnPrimePow with
  | zero => exact fun _ h0 _ ↦ absurd h0 (lt_irrefl 0)
  | one => exact fun x _ hx ↦ by simpa using hx
  | prime_pow_mul a p m hp hpa hm ih =>
    intro x hpos hx
    have : Fact p.Prime := ⟨hp⟩
    obtain ⟨P, hP⟩ := h p
    exact ih x (Nat.pos_of_mul_pos_left hpos)
      (eq_zero_of_map_sylow_eq_zero A (n + 1) p P (j := m) (by rw [← mul_smul, hx])
        ((ModuleCat.subsingleton_of_isZero hP).allEq _ _))

end TauCeti.groupCohomology
