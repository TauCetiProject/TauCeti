/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Algebra.Bilinear
public import Mathlib.Algebra.Algebra.Subalgebra.Basic
public import Mathlib.Algebra.Lie.Abelian
public import Mathlib.Algebra.Lie.AdjointAction.Basic
public import Mathlib.Algebra.Lie.OfAssociative
public import Mathlib.Data.Nat.Choose.Sum
public import Mathlib.LinearAlgebra.Semisimple

/-!
# The iterated adjoint action of an associative algebra

Let `A` be an associative `R`-algebra, bracketed by its ring commutator, and let
`ad R A a : Module.End R A` be the inner derivation `b ↦ ⁅a, b⁆`.  Two powers are in play and
they must not be confused: `a ^ n` is a power in the ring `A`, while `ad R A a ^ n` is a power in
the endomorphism ring `Module.End R A`, that is, the `n`-fold iterated commutator with `a`.

This file expands the second kind over an arbitrary commutative ring `R`.  Since `ad R A a` is the
difference of the commuting endomorphisms `LinearMap.mulLeft R a` and `LinearMap.mulRight R a`, the
`n`-fold iterated commutator is their binomial expansion: a sum of the products
`a ^ m * b * (-a) ^ (n - m)`, with the sign absorbed into `(-a) ^ (n - m)` rather than carried as a
separate `(-1) ^ k`.  Alongside it, `ad_eq_zero_iff_mem_center` records that the adjoint action of
`a` vanishes exactly when `a` is central, so shifting `a` by a central element does not change
`ad R A a`; in particular a central element plus a nilpotent element has nilpotent adjoint action.

Over an algebra of exponential characteristic `p` the expansion collapses at `n = p ^ e`, which is
the subject of `TauCeti.Algebra.Lie.AdjointAction.Frobenius`.

In a center-free Lie algebra, an element whose adjoint is polynomial in `ad x` centralizes
every element centralizing `x` (`TauCeti.LieAlgebra.lie_eq_zero_of_ad_mem_adjoin`).

Adjoint semisimplicity, like adjoint nilpotence, passes from a Lie algebra to its Lie subalgebras
(`LieSubalgebra.isSemisimple_ad_of_isSemisimple_ad`, over any commutative ring).
For an ideal, adjoint nilpotence also passes back to the ambient Lie algebra
(`LieIdeal.isNilpotent_ad_iff`), because `ad x` maps the ambient Lie algebra into the ideal.

## Main statements

* `TauCeti.LieAlgebra.ad_pow_eq_sum` and `TauCeti.LieAlgebra.ad_pow_apply`: the
  iterated-commutator expansion of `ad R A a ^ n`, at operator level and evaluated.
* `TauCeti.LieAlgebra.ad_eq_zero_iff_mem_center`: `ad R A a` vanishes exactly on the centre.
* `TauCeti.LieAlgebra.isNilpotent_ad_of_isNilpotent_sub_of_mem_center`: a central element plus a
  nilpotent element has nilpotent adjoint action.
* `LieSubalgebra.isSemisimple_ad_of_isSemisimple_ad`: an element of a Lie subalgebra that is
  ad-semisimple in the ambient Lie algebra is ad-semisimple in the subalgebra.
* `LieIdeal.isNilpotent_ad_iff`: an element of an ideal is ad-nilpotent in the ideal exactly when
  it is ad-nilpotent in the ambient Lie algebra.
* `TauCeti.LieAlgebra.ad_eq_zero_iff`: the adjoint action of `z` vanishes exactly when `z` is
  central, so adding a central element does not change the adjoint action
  (`TauCeti.LieAlgebra.ad_add_of_mem_center_left`) or ad-nilpotence
  (`TauCeti.LieAlgebra.isNilpotent_ad_add_iff_of_mem_center_left`).
* `TauCeti.LieAlgebra.commute_ad_of_lie_eq_zero`: elements with vanishing bracket have commuting
  adjoint actions.

## References

* N. Jacobson, *Lie Algebras*, Interscience (1962), Chapter V.
-/

public section

attribute [local instance 100] LieRing.ofAssociativeRing

namespace TauCeti.LieAlgebra

open Finset

variable {R A : Type*} [CommRing R] [Ring A] [Algebra R A]

/-- **The iterated-commutator expansion, at operator level.**  Left and right multiplication by
`a` commute by associativity, so the `n`-fold commutator with `a` is their binomial expansion.
The sign that usually accompanies such an expansion is absorbed into `(-a) ^ (n - m)`. -/
theorem ad_pow_eq_sum (a : A) (n : ℕ) :
    LieAlgebra.ad R A a ^ n =
      ∑ m ∈ range (n + 1),
        n.choose m • (LinearMap.mulLeft R (a ^ m) * LinearMap.mulRight R ((-a) ^ (n - m))) := by
  have hneg : LinearMap.mulRight R (-a) = -LinearMap.mulRight R a := by
    ext b
    simp
  have hcomm : Commute (LinearMap.mulLeft R a) (LinearMap.mulRight R (-a)) :=
    LinearMap.commute_mulLeft_right a (-a)
  rw [LieAlgebra.ad_eq_lmul_left_sub_lmul_right, Pi.sub_apply, sub_eq_add_neg, ← hneg,
    hcomm.add_pow n]
  refine Finset.sum_congr rfl fun m _ ↦ ?_
  rw [LinearMap.pow_mulLeft, LinearMap.pow_mulRight, nsmul_eq_mul]
  exact (Nat.cast_commute (n.choose m) _).eq.symm

/-- **The iterated-commutator expansion, evaluated.**  This is `ad_pow_eq_sum` applied to an
element: the `n`-fold commutator of `a` with `b` is the binomial sum of the products
`a ^ m * b * (-a) ^ (n - m)`. -/
theorem ad_pow_apply (a b : A) (n : ℕ) :
    (LieAlgebra.ad R A a ^ n) b =
      ∑ m ∈ range (n + 1), n.choose m • (a ^ m * b * (-a) ^ (n - m)) := by
  rw [ad_pow_eq_sum, LinearMap.sum_apply]
  refine Finset.sum_congr rfl fun m _ ↦ ?_
  simp only [LinearMap.smul_apply, mul_apply_eq_comp, LinearMap.mulLeft_apply,
    LinearMap.mulRight_apply, mul_assoc]

/-- The adjoint action of `a` vanishes exactly when `a` is central. -/
@[simp]
theorem ad_eq_zero_iff_mem_center (a : A) :
    LieAlgebra.ad R A a = 0 ↔ a ∈ Subalgebra.center R A := by
  rw [LinearMap.ext_iff, Subalgebra.mem_center_iff]
  refine forall_congr' fun b ↦ ?_
  rw [LieAlgebra.ad_apply, Ring.lie_def, LinearMap.zero_apply, sub_eq_zero, eq_comm]

/-- Shifting by a central element does not change the adjoint action, so a central element plus a
nilpotent element of an associative algebra has nilpotent adjoint action. -/
theorem isNilpotent_ad_of_isNilpotent_sub_of_mem_center {a z : A} (h : IsNilpotent (a - z))
    (hz : z ∈ Subalgebra.center R A) : IsNilpotent (LieAlgebra.ad R A a) := by
  have hz' : LieAlgebra.ad R A z = 0 := (ad_eq_zero_iff_mem_center z).mpr hz
  simpa [hz'] using LieAlgebra.ad_nilpotent_of_nilpotent (R := R) h

end TauCeti.LieAlgebra

namespace LieSubalgebra

open LieAlgebra Module.End

/-- An element of a Lie subalgebra whose adjoint action on the ambient Lie algebra is semisimple
also has semisimple adjoint action on the subalgebra. This is the semisimple analogue of
`LieSubalgebra.isNilpotent_ad_of_isNilpotent_ad`. -/
theorem isSemisimple_ad_of_isSemisimple_ad {R L : Type*} [CommRing R] [LieRing L] [LieAlgebra R L]
    (L' : LieSubalgebra R L) {x : L'} (h : (ad R L x).IsSemisimple) : (ad R L' x).IsSemisimple := by
  have hp : L'.toSubmodule ∈ (ad R L x).invtSubmodule :=
    (mem_invtSubmodule_iff_forall_mem_of_mem _).2 fun y hy ↦ L'.lie_mem x.property hy
  -- The restriction of `ad x` to `L'` is, elementwise by definition, the adjoint action on `L'`.
  exact (LinearEquiv.isSemisimple_iff _ _ (LinearEquiv.refl R L') (by ext; rfl)).1 (h.restrict hp)

end LieSubalgebra

namespace LieIdeal

open LieAlgebra

variable {R L : Type*} [CommRing R] [LieRing L] [LieAlgebra R L]

/-- **Ad-nilpotence in an ideal.** An element `x` of an ideal `I` acts nilpotently on `I` exactly
when it acts nilpotently on the whole Lie algebra: `ad x` maps `L` into `I`, where its powers are
those of the adjoint action of `I`. For a subalgebra which is not an ideal only the implication
`LieSubalgebra.isNilpotent_ad_of_isNilpotent_ad` holds. -/
@[simp]
theorem isNilpotent_ad_iff (I : LieIdeal R L) {x : I} :
    IsNilpotent (ad R I x) ↔ IsNilpotent (ad R L x) := by
  refine ⟨fun ⟨n, hn⟩ ↦ ⟨n + 1, LinearMap.ext fun y ↦ ?_⟩,
    I.toLieSubalgebra.isNilpotent_ad_of_isNilpotent_ad⟩
  -- `ad x` maps `L` into `I`, where its powers are those of the adjoint action of `I`
  have h : ((ad R I x ^ n) ⟨⁅(x : L), y⁆, _root_.lie_mem_left R L I _ _ x.property⟩ : L) =
      (ad R L x ^ n) ⁅(x : L), y⁆ :=
    LieSubalgebra.coe_ad_pow R L I.toLieSubalgebra x _ n
  simpa [pow_succ, hn] using h.symm

end LieIdeal

namespace TauCeti.LieAlgebra

open _root_.LieAlgebra

variable {R L : Type*} [CommRing R] [LieRing L] [LieAlgebra R L]

/-- The adjoint action of `z` vanishes exactly when `z` is central. -/
theorem ad_eq_zero_iff {z : L} : ad R L z = 0 ↔ z ∈ center R L := by
  rw [← LieHom.mem_ker, ad_ker_eq_self_module_ker, self_module_ker_eq_center]

/-- Adding a central element on the left does not change the adjoint action. -/
theorem ad_add_of_mem_center_left {z : L} (hz : z ∈ center R L) (y : L) :
    ad R L (z + y) = ad R L y := by
  rw [map_add, ad_eq_zero_iff.mpr hz, zero_add]

/-- Adding a central element on the right does not change the adjoint action. -/
theorem ad_add_of_mem_center_right (y : L) {z : L} (hz : z ∈ center R L) :
    ad R L (y + z) = ad R L y := by
  rw [add_comm, ad_add_of_mem_center_left hz]

/-- Adding a central element on the left does not change `ad`-nilpotence. -/
theorem isNilpotent_ad_add_iff_of_mem_center_left {z : L} (hz : z ∈ center R L) (y : L) :
    IsNilpotent (ad R L (z + y)) ↔ IsNilpotent (ad R L y) := by
  rw [ad_add_of_mem_center_left hz]

/-- Adding a central element on the right does not change `ad`-nilpotence. -/
theorem isNilpotent_ad_add_iff_of_mem_center_right (y : L) {z : L} (hz : z ∈ center R L) :
    IsNilpotent (ad R L (y + z)) ↔ IsNilpotent (ad R L y) := by
  rw [ad_add_of_mem_center_right y hz]

/-- Elements whose bracket vanishes have commuting adjoint actions. -/
theorem commute_ad_of_lie_eq_zero {x y : L} (h : ⁅x, y⁆ = 0) :
    Commute (ad R L x) (ad R L y) := by
  rw [commute_iff_lie_eq, ← LieHom.map_lie, h, map_zero]

/-- In a center-free Lie algebra, an element whose adjoint is polynomial in `ad x` commutes
with every element commuting with `x`. -/
theorem lie_eq_zero_of_ad_mem_adjoin [LieModule.IsFaithful R L L] {x y z : L}
    (hz : ad R L z ∈ Algebra.adjoin R {ad R L x}) (hxy : ⁅x, y⁆ = 0) : ⁅z, y⁆ = 0 := by
  have hzy := Algebra.commute_of_mem_adjoin_singleton_of_commute hz
    (commute_ad_of_lie_eq_zero hxy).symm
  apply (LieModule.toEnd_eq_iff R L L).mp
  rw [map_zero, LieHom.map_lie]
  -- The bracket on endomorphisms is the commutator.
  exact sub_eq_zero.mpr hzy.symm.eq

end TauCeti.LieAlgebra
