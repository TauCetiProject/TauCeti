/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.BigOperators.Finprod
public import Mathlib.Algebra.BigOperators.GroupWithZero.Action
public import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
public import Mathlib.RingTheory.Invariant.Basic
import Mathlib.RingTheory.IntegralClosure.Algebra.Basic

/-!
# Orbit products and stable subrings of finite group actions

Let a finite group `G` act on a commutative ring `A`. Two products over the group produce
invariant data from an arbitrary element `a`:

* the *orbit product* `N(a) = ∏ g : G, g • a`, which lies in the fixed subring `Aᴳ`;
* the orbit polynomial `∏ g : G, (X - C (g • a))`, Mathlib's `MulSemiringAction.charpoly`, whose
  coefficients lie in `Aᴳ`.

The orbit product is defined for any multiplicative action on a commutative monoid. It is indexed
by the group, not by the orbit: a nonfaithful action repeats factors, and for the trivial action
`N(a) = a ^ |G|`. So it is not the norm of a finite free extension. Its use is to manufacture
invariant elements with a prescribed multiplicative property, such as an invariant
pseudouniformiser of a Tate ring with a continuous action
(`TauCeti.Huber.IsPseudoUniformizer.orbitProd`).

The orbit polynomial shows that a `G`-stable subring `R ⊆ A` is integral over its invariants
`R ∩ Aᴳ`: if `a ∈ R`, every translate of `a` lies in `R`, so the coefficients of the orbit
polynomial lie in `R ∩ Aᴳ`. When `R` is integrally closed in `A`, it is therefore exactly the
integral closure of `R ∩ Aᴳ` in `A`. This recovers a ring of integral elements `A⁺` from its
invariants (Hansen, *Quotients of adic spaces by finite groups*, Step 3 of the proof of
Theorem 3.1).

## Main definitions

* `TauCeti.MulDistribMulAction.orbitProd G a`: the orbit product `∏ g : G, g • a`.

## Main results

* `TauCeti.MulDistribMulAction.smul_orbitProd`: the orbit product is `G`-invariant.
* `TauCeti.MulDistribMulAction.orbitProd_mul`: it is multiplicative.
* `TauCeti.MulDistribMulAction.orbitProd_eq_pow_card`: for an element fixed by `G` it is the
  `|G|`-th power; in particular it is the element itself for the trivial group
  (`TauCeti.MulDistribMulAction.orbitProd_of_subsingleton`).
* `TauCeti.MulDistribMulAction.orbitProd_mem_fixedPoints`: for a ring, it lies in
  `FixedPoints.subring A G`.
* `Subring.isIntegral_inf_fixedPoints`: a `G`-stable subring is integral over its invariants.
* `Subring.integralClosure_inf_fixedPoints`: a `G`-stable subring that is integrally closed in
  `A` is the integral closure of its invariants.

## References

* D. Hansen, *Quotients of adic spaces by finite groups*, Math. Res. Lett. 28 (2021), proof of
  Theorem 3.1.
-/

public section

open Polynomial

/-- Membership in the fixed subring. -/
theorem FixedPoints.mem_subring {B G : Type*} [Ring B] [Monoid G] [MulSemiringAction G B]
    {x : B} : x ∈ FixedPoints.subring B G ↔ ∀ g : G, g • x = x :=
  Iff.rfl

namespace TauCeti.MulDistribMulAction

section CommMonoid

variable (G : Type*) {M : Type*} [Group G] [CommMonoid M] [MulDistribMulAction G M]

/-- The *orbit product* `N(a) = ∏ g : G, g • a` of an element of a commutative monoid under a
group action. It is meant for finite groups, where it is `G`-invariant
(`TauCeti.MulDistribMulAction.smul_orbitProd`). The product is indexed by the group, so a
nonfaithful action repeats factors. -/
noncomputable def orbitProd (a : M) : M :=
  ∏ᶠ g : G, g • a

/-- Unfolding lemma for `TauCeti.MulDistribMulAction.orbitProd`. -/
theorem orbitProd_def (a : M) : orbitProd G a = ∏ᶠ g : G, g • a :=
  (rfl)

/-- For a finite group with a chosen `Fintype` structure, the orbit product is a `Finset`
product. -/
theorem orbitProd_eq_prod [Fintype G] (a : M) : orbitProd G a = ∏ g : G, g • a :=
  finprod_eq_prod_of_fintype _

/-- **The orbit product is invariant.** -/
@[simp]
theorem smul_orbitProd [Finite G] (g : G) (a : M) : g • orbitProd G a = orbitProd G a :=
  smul_finprod_perm a g

@[simp]
theorem orbitProd_one : orbitProd G (1 : M) = 1 := by
  simp [orbitProd_def]

/-- **The orbit product is multiplicative.** -/
theorem orbitProd_mul [Finite G] (a b : M) :
    orbitProd G (a * b) = orbitProd G a * orbitProd G b := by
  simp only [orbitProd_def, smul_mul']
  exact finprod_mul_distrib (Set.toFinite _) (Set.toFinite _)

/-- The orbit product of an element fixed by every group element is its `|G|`-th power. This
covers the trivial action, where `N(a) = a ^ |G|`. -/
theorem orbitProd_eq_pow_card [Finite G] {a : M} (ha : ∀ g : G, g • a = a) :
    orbitProd G a = a ^ Nat.card G := by
  cases nonempty_fintype G
  simp [orbitProd_eq_prod, ha, Nat.card_eq_fintype_card]

/-- For the trivial group, the orbit product of `a` is `a`. -/
@[simp]
theorem orbitProd_of_subsingleton [Subsingleton G] (a : M) : orbitProd G a = a := by
  have : Finite G := Finite.of_subsingleton
  rw [orbitProd_eq_pow_card G fun g ↦ by rw [Subsingleton.elim g 1, one_smul],
    Nat.card_of_subsingleton (1 : G), pow_one]

end CommMonoid

section Ring

variable (G : Type*) {R : Type*} [Group G] [Finite G]

/-- The orbit product of zero is zero, the product having at least one factor. -/
@[simp]
theorem orbitProd_zero [CommSemiring R] [MulSemiringAction G R] : orbitProd G (0 : R) = 0 := by
  rw [orbitProd_eq_pow_card G fun g ↦ smul_zero g, zero_pow Nat.card_pos.ne']

/-- The orbit product lies in the fixed subring. -/
theorem orbitProd_mem_fixedPoints [CommRing R] [MulSemiringAction G R] (a : R) :
    orbitProd G a ∈ FixedPoints.subring R G :=
  FixedPoints.mem_subring.mpr fun g ↦ smul_orbitProd G g a

end Ring

end TauCeti.MulDistribMulAction

namespace Subring

variable {A G : Type*} [CommRing A] [Group G] [Finite G] [MulSemiringAction G A]

/-- **A stable subring is integral over its invariants.** If a finite group `G` maps the subring
`R ⊆ A` into itself, every element of `R` is integral over `R ∩ Aᴳ`: it is a root of its orbit
polynomial `∏ g : G, (X - C (g • a))`, whose coefficients are invariant and, the translates of `a`
lying in `R`, belong to `R`. -/
theorem isIntegral_inf_fixedPoints (R : Subring A) (hR : ∀ g : G, ∀ a ∈ R, g • a ∈ R) {a : A}
    (ha : a ∈ R) : IsIntegral ↥(R ⊓ FixedPoints.subring A G) a := by
  cases nonempty_fintype G
  -- The orbit polynomial, computed in `R[X]`.
  let p : R[X] := ∏ g : G, (X - C ⟨g • a, hR g a ha⟩)
  have hp : p.map R.subtype = MulSemiringAction.charpoly G a := by
    simp [p, Polynomial.map_prod, MulSemiringAction.charpoly_eq]
  have hlifts : MulSemiringAction.charpoly G a ∈
      Polynomial.lifts (algebraMap ↥(R ⊓ FixedPoints.subring A G) A) := by
    refine (Polynomial.lifts_iff_coeff_lifts _).mpr fun n ↦
      ⟨⟨(MulSemiringAction.charpoly G a).coeff n, ?_, ?_⟩, rfl⟩
    · rw [← hp, coeff_map]
      exact (p.coeff n).2
    · exact FixedPoints.mem_subring.mpr (MulSemiringAction.smul_coeff_charpoly a n)
  obtain ⟨q, hq, -, hmonic⟩ :=
    Polynomial.lifts_and_natDegree_eq_and_monic hlifts (MulSemiringAction.monic_charpoly G a)
  exact ⟨q, hmonic, by rw [← eval_map, hq, MulSemiringAction.eval_charpoly]⟩

/-- **A stable integrally closed subring is the integral closure of its invariants.** If a finite
group `G` maps the subring `R ⊆ A` into itself and `R` is integrally closed in `A`, then `R` is
the integral closure of `R ∩ Aᴳ` in `A`. -/
theorem integralClosure_inf_fixedPoints (R : Subring A) (hR : ∀ g : G, ∀ a ∈ R, g • a ∈ R)
    [IsIntegrallyClosedIn R A] :
    (integralClosure ↥(R ⊓ FixedPoints.subring A G) A).toSubring = R := by
  ext a
  refine ⟨fun ha ↦ Subring.isIntegrallyClosedIn_iff.mp ‹_› ?_,
    fun ha ↦ R.isIntegral_inf_fixedPoints hR ha⟩
  -- An element integral over `R ∩ Aᴳ` is integral over the larger ring `R`.
  exact IsIntegral.map_of_comp_eq (Subring.inclusion inf_le_left) (RingHom.id A) (RingHom.ext
    fun _ ↦ rfl) ((mem_integralClosure_iff _ _).mp (Subalgebra.mem_toSubring.mp ha))

end Subring
