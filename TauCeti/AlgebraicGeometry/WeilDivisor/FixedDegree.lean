/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Data.Finsupp.Multiset
public import Mathlib.Data.Sym.Basic
public import TauCeti.AlgebraicGeometry.WeilDivisor.FiniteSum

/-!
# Effective Weil divisors of fixed degree

This file packages the fixed-degree part of the effective Weil-divisor monoid.  For a type of
points `X`, the type `EffectiveDivisorOfDegree X d` consists of effective formal divisors of
degree `d`.  It is equivalent to Mathlib's symmetric power `Sym X d`, by reading a multiset as
its finitely supported multiplicity function and conversely reading an effective divisor by its
natural-number coefficients.

This is the formal divisor model behind the Jacobian roadmap's Layer C symmetric-power lane:
the scheme-level construction of `Symᵈ X` and relative effective Cartier divisors is later
geometry, but the Abel-map input already needs the divisor represented by an unordered
degree-`d` collection of points.

This advances `TauCetiRoadmap/JacobianChallenge/README.md`, Layer C, "Relative effective
Cartier divisors and symmetric powers `Symᵈ X`", as a small prerequisite built from the
existing Layer A `WeilDivisor` API.  No external mathematics is vendored.
-/

public section

namespace TauCeti

namespace AlgebraicGeometry

namespace WeilDivisor

variable {X Y : Type*}

noncomputable section

/-- The effective Weil divisors of degree `d`. -/
abbrev EffectiveDivisorOfDegree (X : Type*) (d : ℕ) : Type _ :=
  {D : WeilDivisor X // IsEffective D ∧ degree D = d}

namespace EffectiveDivisorOfDegree

@[ext]
lemma ext {D E : EffectiveDivisorOfDegree X d} (h : (D : WeilDivisor X) = E) : D = E :=
  Subtype.ext h

@[simp]
lemma isEffective (D : EffectiveDivisorOfDegree X d) : IsEffective (D : WeilDivisor X) :=
  D.property.1

@[simp]
lemma degree_eq (D : EffectiveDivisorOfDegree X d) : degree (D : WeilDivisor X) = d :=
  D.property.2

lemma mem_effectiveSubmonoid (D : EffectiveDivisorOfDegree X d) :
    (D : WeilDivisor X) ∈ effectiveSubmonoid X :=
  (WeilDivisor.mem_effectiveSubmonoid _).mpr D.isEffective

/-- An effective divisor of degree `d` from finitely supported natural multiplicities whose
total multiplicity is `d`. -/
@[expose]
def ofFinsupp (m : X →₀ ℕ) (hm : m.sum (fun _ n => n) = d) :
    EffectiveDivisorOfDegree X d :=
  ⟨WeilDivisor.ofFinsupp m, isEffective_ofFinsupp m, by
    rw [degree_ofFinsupp]
    exact_mod_cast hm⟩

@[simp]
lemma coe_ofFinsupp (m : X →₀ ℕ) (hm : m.sum (fun _ n => n) = d) :
    (ofFinsupp m hm : WeilDivisor X) = WeilDivisor.ofFinsupp m :=
  rfl

lemma coeff_ofFinsupp (m : X →₀ ℕ) (hm : m.sum (fun _ n => n) = d) (x : X) :
    coeff (ofFinsupp m hm : WeilDivisor X) x = m x :=
  WeilDivisor.coeff_ofFinsupp m x

/-- The finitely supported natural multiplicity function underlying an effective divisor. -/
@[expose]
def multiplicityFinsupp (D : EffectiveDivisorOfDegree X d) : X →₀ ℕ :=
  Finsupp.onFinset (D : WeilDivisor X).support
    (fun x => (coeff (D : WeilDivisor X) x).toNat)
    (fun x hx => by
      rw [Finsupp.mem_support_iff]
      intro hcoeff
      rw [coeff, hcoeff] at hx
      exact hx rfl)

@[simp]
lemma multiplicityFinsupp_apply (D : EffectiveDivisorOfDegree X d) (x : X) :
    D.multiplicityFinsupp x = (coeff (D : WeilDivisor X) x).toNat :=
  Finsupp.onFinset_apply

@[simp]
lemma ofFinsupp_multiplicityFinsupp (D : EffectiveDivisorOfDegree X d) :
    WeilDivisor.ofFinsupp D.multiplicityFinsupp = (D : WeilDivisor X) := by
  ext x
  rw [WeilDivisor.coeff_ofFinsupp, multiplicityFinsupp_apply]
  exact Int.toNat_of_nonneg ((isEffective_iff (D : WeilDivisor X)).mp D.property.1 x)

lemma sum_multiplicityFinsupp (D : EffectiveDivisorOfDegree X d) :
    D.multiplicityFinsupp.sum (fun _ n => n) = d := by
  have hcast :
      (D.multiplicityFinsupp.sum fun _ n => (n : ℤ)) = degree (D : WeilDivisor X) := by
    rw [← ofFinsupp_multiplicityFinsupp D, degree_ofFinsupp]
    simp [Finsupp.sum]
  exact_mod_cast hcast.trans D.degree_eq

@[simp]
lemma ofFinsupp_multiplicityFinsupp_eq (D : EffectiveDivisorOfDegree X d) :
    ofFinsupp D.multiplicityFinsupp D.sum_multiplicityFinsupp = D := by
  exact Subtype.ext (ofFinsupp_multiplicityFinsupp D)

@[simp]
lemma multiplicityFinsupp_ofFinsupp (m : X →₀ ℕ) (hm : m.sum (fun _ n => n) = d) :
    (ofFinsupp m hm).multiplicityFinsupp = m := by
  ext x
  simp

section Sym

variable [DecidableEq X]

/-- The effective divisor associated to an unordered degree-`d` collection of points. -/
@[expose]
def ofSym (s : Sym X d) : EffectiveDivisorOfDegree X d :=
  ofFinsupp (Multiset.toFinsupp (s : Multiset X)) (by
    change (Multiset.toFinsupp (s : Multiset X)).sum (fun _ => id) = d
    rw [Multiset.toFinsupp_sum_eq, Sym.card_coe])

@[simp]
lemma coe_ofSym (s : Sym X d) :
    (ofSym s : WeilDivisor X) = WeilDivisor.ofFinsupp (Multiset.toFinsupp (s : Multiset X)) :=
  rfl

lemma coeff_ofSym (s : Sym X d) (x : X) :
    coeff (ofSym s : WeilDivisor X) x = (s : Multiset X).count x := by
  rw [coe_ofSym, WeilDivisor.coeff_ofFinsupp, Multiset.toFinsupp_apply]

/-- Effective degree-`d` divisors are the same data as the `d`-th symmetric power of the
underlying point type. -/
@[expose]
def equivSym : EffectiveDivisorOfDegree X d ≃ Sym X d where
  toFun D :=
    Sym.mk (Finsupp.toMultiset D.multiplicityFinsupp) (by
      rw [Finsupp.card_toMultiset]
      change D.multiplicityFinsupp.sum (fun _ n => n) = d
      exact D.sum_multiplicityFinsupp)
  invFun := ofSym
  left_inv D := by
    apply Subtype.ext
    rw [coe_ofSym]
    change WeilDivisor.ofFinsupp
        (Multiset.toFinsupp (Finsupp.toMultiset D.multiplicityFinsupp)) = (D : WeilDivisor X)
    rw [Finsupp.toMultiset_toFinsupp, ofFinsupp_multiplicityFinsupp]
  right_inv s := by
    apply Sym.ext
    change Finsupp.toMultiset (ofSym s).multiplicityFinsupp = (s : Multiset X)
    rw [show (ofSym s).multiplicityFinsupp = Multiset.toFinsupp (s : Multiset X) by
      exact multiplicityFinsupp_ofFinsupp _ _]
    exact Multiset.toFinsupp_toMultiset (s : Multiset X)

end Sym

/-- Pushing forward a fixed-degree effective divisor preserves its degree. -/
@[expose]
def pushforward (f : X → Y) (D : EffectiveDivisorOfDegree X d) :
    EffectiveDivisorOfDegree Y d :=
  ⟨WeilDivisor.pushforward f D, D.isEffective.pushforward f, by
    rw [degree_pushforward, D.degree_eq]⟩

@[simp]
lemma coe_pushforward (f : X → Y) (D : EffectiveDivisorOfDegree X d) :
    (D.pushforward f : WeilDivisor Y) = WeilDivisor.pushforward f D :=
  rfl

@[simp]
lemma pushforward_id (D : EffectiveDivisorOfDegree X d) :
    D.pushforward (fun x : X => x) = D := by
  ext
  rw [coe_pushforward, WeilDivisor.pushforward_id]
  rfl

/-- The zero divisor is the unique effective divisor of degree zero. -/
def zeroEquivPUnit : EffectiveDivisorOfDegree X 0 ≃ PUnit where
  toFun _ := PUnit.unit
  invFun _ := ⟨0, isEffective_zero, degree_zero⟩
  left_inv D := by
    have hzero : (D : WeilDivisor X) = 0 :=
      D.isEffective.eq_zero_of_degree_eq_zero D.degree_eq
    exact Subtype.ext hzero.symm
  right_inv _ := rfl

end EffectiveDivisorOfDegree

end

end WeilDivisor

end AlgebraicGeometry

end TauCeti
