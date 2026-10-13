/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Localization.Away.Basic
public import TauCeti.RingTheory.Syntomic.Composition
import TauCeti.RingTheory.Syntomic.Smooth

/-!
# Standard syntomic algebras and localization

Standard syntomic algebras of relative dimension `n` are stable under composition with
localizations away from an element, on either side:

* if `S` is standard syntomic of relative dimension `n` over `R` and `g ∈ S`, then so is `S[1/g]`;
* if `r ∈ R` and `T` is standard syntomic of relative dimension `n` over `R[1/r]`, then `T` is
  standard syntomic of relative dimension `n` over `R`.

A localization away from an element is standard syntomic of relative dimension zero: it is flat,
has one generator `x` and one relation `rx - 1`, and every nonempty residue-field fibre is
isomorphic to the residue field. Both stability results therefore follow from dimension-additive
composition of standard syntomic algebras.

These two stability properties, together with stability under base change, are what make
"locally standard syntomic of relative dimension `n`" a property of ring maps that is local on the
source and the target, and hence define syntomic morphisms of schemes of relative dimension `n`.

## Main results

* `TauCeti.Algebra.IsStandardSyntomicOfRelativeDimension.localization_away`: a localization away
  from one element is standard syntomic of relative dimension zero.
* `TauCeti.Algebra.IsStandardSyntomicOfRelativeDimension.trans_localization_away`: if `S` is
  standard syntomic of relative dimension `n` over `R`, so is every localization `S[1/g]`.
* `TauCeti.Algebra.IsStandardSyntomicOfRelativeDimension.localization_away_trans`: an algebra that
  is standard syntomic of relative dimension `n` over `R[1/r]` is standard syntomic of relative
  dimension `n` over `R`.

## References

* The Stacks Project, Commutative Algebra, Section *Syntomic morphisms*: the stability of relative
  global complete intersections under localization `S → S_g`, and the locality of syntomic ring
  maps.
-/

public section

namespace TauCeti

namespace Algebra.IsStandardSyntomicOfRelativeDimension

universe u v w

/-- A localization away from one element is standard syntomic of relative dimension zero. -/
theorem localization_away {R : Type*} [CommRing R] (S : Type*) [CommRing S] [Algebra R S]
    (r : R) [IsLocalization.Away r S] : IsStandardSyntomicOfRelativeDimension 0 R S := by
  have := _root_.Algebra.IsStandardSmoothOfRelativeDimension.localization_away (S := S) r
  infer_instance

variable {n : ℕ} {R : Type u} {S : Type v} {T : Type w}
  [CommRing R] [CommRing S] [CommRing T] [Algebra R S]
  [Algebra S T] [Algebra R T] [IsScalarTower R S T]

/-- If `S` is standard syntomic of relative dimension `n` over `R`, then so is its localization
`S[1/g]` away from any `g ∈ S`. -/
theorem trans_localization_away [IsStandardSyntomicOfRelativeDimension n R S] (g : S)
    [IsLocalization.Away g T] : IsStandardSyntomicOfRelativeDimension n R T := by
  have := localization_away T g
  simpa only [add_zero] using (trans (n := n) (m := 0) (R := R) (S := S) (T := T))

/-- If `T` is standard syntomic of relative dimension `n` over the localization `S = R[1/r]` of `R`
away from `r`, then `T` is standard syntomic of relative dimension `n` over `R`. -/
theorem localization_away_trans (r : R) [IsLocalization.Away r S]
    [IsStandardSyntomicOfRelativeDimension n S T] :
    IsStandardSyntomicOfRelativeDimension n R T := by
  have := localization_away S r
  simpa only [zero_add] using (trans (n := 0) (m := n) (R := R) (S := S) (T := T))

end Algebra.IsStandardSyntomicOfRelativeDimension

end TauCeti
