/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Flat.TorsionFree
public import TauCeti.RingTheory.Almost.BasicSetup
public import TauCeti.RingTheory.Valuation.IdempotentMaximalIdeal

/-!
# The basic setup of a valuation ring

Let `V` be a valuation domain whose maximal ideal `m` is not finitely generated, for instance
the ring of integers of a perfectoid field or of `ℂ_p`. Then `(V, m)` is a basic setup for almost
mathematics, the setup `(K°, K°°)` of Scholze's *Perfectoid spaces*, §4: `m` is idempotent, and
`m` is torsion-free, hence flat over the Bézout domain `V`, so `m ⊗[V] m` is flat and
multiplication identifies it with `m`. No completeness and no rank-one hypothesis is needed.

Any two elements of a valuation ring are comparable for divisibility, so every basic setup over
it, this one included, satisfies condition (A).
Since `m` is not principal, a quotient `V ⧸ (x)` is almost zero only when `x` is a unit; for
example, for `V = 𝓞_ℂ_[p]` the residue field is almost zero while `V ⧸ (p)` is not.

## Main definitions

* `TauCeti.Almost.BasicSetup.ofValuationRing`: the basic setup `(V, m)` of a valuation domain
  whose maximal ideal is not finitely generated.

## Main results

* `TauCeti.Almost.BasicSetup.flat_ofValuationRing_ideal`: the maximal ideal is a flat
  `V`-module.
* `TauCeti.Almost.BasicSetup.ofValuationRing_tildeToIdeal_bijective`: multiplication
  `m ⊗[V] m → m` is bijective.
* `TauCeti.Almost.BasicSetup.isFilteredPrincipal_of_preValuationRing`: every basic setup over a
  valuation ring satisfies condition (A).
* `TauCeti.Almost.BasicSetup.ofValuationRing_isAlmostZero_quotient_span_singleton_iff`:
  `V ⧸ (x)` is almost zero iff `x` is a unit.
* `TauCeti.Almost.BasicSetup.ofValuationRing_isAlmostZero_residueField`: the residue field is
  almost zero.

## References

* O. Gabber, L. Ramero, *Almost ring theory*, Lecture Notes in Mathematics 1800, §2.1,
  Example 2.1.2(i).
* P. Scholze, *Perfectoid spaces*, Publ. Math. IHÉS 116 (2012), §4, Lemma 4.2 and its proof.
-/

public section

open IsLocalRing

namespace TauCeti.Almost.BasicSetup

/-- Every basic setup over a ring whose elements are totally ordered by divisibility, such as a
valuation ring, satisfies condition (A): of two elements of `m`, one divides the other. -/
@[simp]
theorem isFilteredPrincipal_of_preValuationRing {V : Type*} [CommRing V] [PreValuationRing V]
    (S : BasicSetup V) : S.IsFilteredPrincipal := by
  refine isFilteredPrincipal_iff.mpr fun x hx y hy ↦ ?_
  rcases _root_.ValuationRing.dvd_total x y with hxy | hyx
  · exact ⟨x, hx, dvd_rfl, hxy⟩
  · exact ⟨y, hy, hyx, dvd_rfl⟩

variable {V : Type*} [CommRing V] [IsDomain V] [ValuationRing V]
  (h : ¬ (maximalIdeal V).FG)

/-- The basic setup `(V, m)` of a valuation domain `V` whose maximal ideal `m` is not finitely
generated (Gabber–Ramero Example 2.1.2(i), Scholze, *Perfectoid spaces*, §4): `m` is
idempotent, and `m ⊗[V] m` is flat because `m` is torsion-free, hence flat over the Bézout
domain `V`. -/
def ofValuationRing : BasicSetup V where
  ideal := maximalIdeal V
  isIdempotentElem := ValuationRing.isIdempotentElem_maximalIdeal_of_not_fg h
  flat_tilde :=
    have : Module.Flat V (maximalIdeal V) := Module.Flat.flat_iff_torsion_eq_bot_of_isBezout.mpr
      (Submodule.isTorsionFree_iff_torsion_eq_bot.mp inferInstance)
    inferInstance

@[simp]
theorem ofValuationRing_ideal : (ofValuationRing h).ideal = maximalIdeal V :=
  (rfl)

/-- The ideal of the basic setup of a valuation domain is a flat module: it is torsion-free, and
torsion-free modules over a Bézout domain are flat. -/
instance flat_ofValuationRing_ideal : Module.Flat V (ofValuationRing h).ideal :=
  Module.Flat.flat_iff_torsion_eq_bot_of_isBezout.mpr
    (Submodule.isTorsionFree_iff_torsion_eq_bot.mp inferInstance)

/-- For the basic setup of a valuation domain, multiplication `m ⊗[V] m → m` is bijective, since
`m` is flat. -/
theorem ofValuationRing_tildeToIdeal_bijective :
    Function.Bijective (ofValuationRing h).tildeToIdeal :=
  tildeToIdeal_bijective_of_flat _

/-- For the basic setup of a valuation domain, `V ⧸ (x)` is almost zero exactly when `x` is a unit:
for a nonunit `x`, the inclusions `m ⊆ (x) ⊆ m` would make `m` principal. -/
@[simp]
theorem ofValuationRing_isAlmostZero_quotient_span_singleton_iff {x : V} :
    (ofValuationRing h).IsAlmostZero (V ⧸ Ideal.span {x}) ↔ IsUnit x := by
  refine ⟨fun hx ↦ ?_, fun hx ↦ ?_⟩
  · by_contra hu
    have hle : maximalIdeal V ≤ Ideal.span {x} := fun ε hε ↦ by
      simpa using (Module.isTorsionBySet_quotient_iff _ _).mp
        (isAlmostZero_iff_isTorsionBySet.mp hx) 1 ε hε
    apply h
    rw [le_antisymm hle ((Ideal.span_singleton_le_iff_mem _).mpr
      ((mem_maximalIdeal x).mpr hu))]
    exact Submodule.fg_span_singleton x
  · rw [Ideal.span_singleton_eq_top.mpr hx]
    exact isAlmostZero_of_subsingleton _

/-- The residue field of a valuation domain is almost zero for its basic setup. -/
@[simp]
theorem ofValuationRing_isAlmostZero_residueField :
    (ofValuationRing h).IsAlmostZero (ResidueField V) :=
  -- `ResidueField V` is by definition the quotient `V ⧸ maximalIdeal V`, with its `V`-module
  -- structure coming from the quotient algebra structure.
  (ofValuationRing h).isAlmostZero_quotient

end TauCeti.Almost.BasicSetup
