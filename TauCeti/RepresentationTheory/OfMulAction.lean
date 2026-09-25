/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RepresentationTheory.Basic

/-!
# Commuting permutation representations

If monoids `G` and `H` act on a type `X` and the two actions commute, then the permutation
representations `Representation.ofMulAction k G X` and `Representation.ofMulAction k H X` on the
free `k`-module `k[X]` commute with each other. For the left and right multiplication actions of
a group `G`, that is, commuting actions of `G` and `Gᵐᵒᵖ`, this makes `k[X]` a `k[G]`-bimodule.

When `G` and `H` are groups, `G` permutes the `H`-orbits, and the orbit sums of `k[X]` along the
`H`-orbits are equivariant: the sum of the coefficients of `g • v` along the `H`-orbit of `g • x`
is the sum of the coefficients of `v` along the `H`-orbit of `x`. Hence if `g` fixes
`∑ i ∈ s, h i • v` for a family `h : ι → H` and `#s` is cancellable in `k`, then the `H`-orbit
sums of `v` are invariant under `g`. The orbit sums of `v` are the finitely supported function
`v.coeff.mapDomain (Quotient.mk (MulAction.orbitRel H X))` on the orbit space.

## Main results

* `TauCeti.commute_ofMulAction`: commuting actions on `X` give commuting permutation
  representations on `k[X]`.
* `TauCeti.mapDomain_orbitRel_mk_coeff_ofMulAction`: the orbit sums of `k[X]` are invariant
  under the permutation representation.
* `TauCeti.mapDomain_orbitRel_mk_coeff_ofMulAction_smul`: for commuting actions of `G` and `H`,
  the `H`-orbit sums of `g • v` at `g • x` are those of `v` at `x`.
* `TauCeti.mapDomain_orbitRel_mk_coeff_smul_of_ofMulAction_sum`: if `g` fixes
  `∑ i ∈ s, h i • v` and `#s` is cancellable, the `H`-orbit sums of `v` are `g`-invariant.

## References

* A. Popa and D. Zagier, *An elementary proof of the Eichler–Selberg trace formula*,
  J. Reine Angew. Math. **762** (2020), 105–122, arXiv:1711.00327. The right coset sums
  `⟨ξ, K⟩` of §3 Theorem 2(a) are the orbit sums for the right action of `PSL(2, ℤ)` on the
  integral matrices of positive determinant, which commutes with the left action.
-/

public section

namespace TauCeti

open Representation

variable {k G H X : Type*} [Semiring k] [Monoid G] [Monoid H] [MulAction G X] [MulAction H X]

/-- If the actions of `G` and `H` on `X` commute, then so do the permutation representations of
`G` and `H` on `k[X]`. -/
theorem commute_ofMulAction [SMulCommClass G H X] (g : G) (h : H) :
    Commute (ofMulAction k G X g) (ofMulAction k H X h) := by
  ext
  simp [smul_comm g h]

/-! ### Orbit sums -/

open MonoidAlgebra MulAction

/-- The orbit sums `k[X] → (X ⧸ G →₀ k)` are invariant under the permutation representation. -/
@[simp]
theorem mapDomain_orbitRel_mk_coeff_ofMulAction {G : Type*} [Group G] [MulAction G X] (g : G)
    (v : k[X]) :
    (ofMulAction k G X g v).coeff.mapDomain (Quotient.mk (orbitRel G X)) =
      v.coeff.mapDomain (Quotient.mk (orbitRel G X)) := by
  induction v using induction_linear with
  | zero => simp
  | add v w hv hw => simp [Finsupp.mapDomain_add, hv, hw]
  | single y r => simp [Quotient.sound (s := orbitRel G X) (mem_orbit y g)]

section Commuting

variable {G H : Type*} [Group G] [Group H] [MulAction G X] [MulAction H X] [SMulCommClass G H X]

open scoped Finset

/-- **Equivariance of orbit sums.** If the actions of `G` and `H` on `X` commute, then the sum of
the coefficients of `g • v` along the `H`-orbit of `g • x` is the sum of the coefficients of `v`
along the `H`-orbit of `x`. -/
@[simp]
theorem mapDomain_orbitRel_mk_coeff_ofMulAction_smul (g : G) (v : k[X]) (x : X) :
    (ofMulAction k G X g v).coeff.mapDomain (Quotient.mk (orbitRel H X)) ⟦g • x⟧ =
      v.coeff.mapDomain (Quotient.mk (orbitRel H X)) ⟦x⟧ := by
  classical
  -- `g` maps distinct `H`-orbits to distinct `H`-orbits
  have hmk (y : X) : Quotient.mk (orbitRel H X) (g • y) = Quotient.mk _ (g • x) ↔
      Quotient.mk (orbitRel H X) y = Quotient.mk _ x := by
    simp [Quotient.eq, orbitRel_apply, mem_orbit_iff, ← smul_comm g]
  induction v using induction_linear with
  | zero => simp
  | add v w hv hw => simp [Finsupp.mapDomain_add, hv, hw]
  | single y r => simp [Finsupp.single_apply, hmk]

/-- If the actions of `G` and `H` on `X` commute, `h : ι → H`, `#s` is cancellable in `k` and
`g • w = w` for `w = ∑ i ∈ s, h i • v`, then the `H`-orbit sums of `v` are invariant under `g`:
the coefficients of `v` have the same sum along the `H`-orbits of `g • x` and of `x`. -/
theorem mapDomain_orbitRel_mk_coeff_smul_of_ofMulAction_sum {ι : Type*} {s : Finset ι} {h : ι → H}
    {g : G} {v : k[X]} (hs : IsSMulRegular k #s)
    (hfix : ofMulAction k G X g (∑ i ∈ s, ofMulAction k H X (h i) v) =
      ∑ i ∈ s, ofMulAction k H X (h i) v) (x : X) :
    v.coeff.mapDomain (Quotient.mk (orbitRel H X)) ⟦g • x⟧ =
      v.coeff.mapDomain (Quotient.mk (orbitRel H X)) ⟦x⟧ := by
  -- the `H`-orbit sums of `∑ i ∈ s, h i • v` are `#s` times those of `v`
  exact hs <| by simpa [hfix, Finsupp.mapDomain_finsetSum] using
    mapDomain_orbitRel_mk_coeff_ofMulAction_smul (H := H) g (∑ i ∈ s, ofMulAction k H X (h i) v) x

end Commuting

end TauCeti
