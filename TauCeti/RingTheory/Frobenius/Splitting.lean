/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.FieldTheory.Perfect
public import Mathlib.RingTheory.Ideal.Quotient.Nilpotent

/-!
# Frobenius splittings and compatible ideals

For a prime `p`, a Frobenius splitting of a commutative ring of characteristic `p` is an
additive map `σ`
with `σ(a ^ p * b) = a * σ(b)` and `σ(1) = 1`. The scalar identity expresses linearity
from the Frobenius pushforward: its underlying additive group is the ring, with scalar
multiplication `a • b = a ^ p * b`. The equation `(p : R) = 0` is stored rather than
an exact-characteristic instance, so the zero ring and quotients by the unit ideal are included.

An ideal is compatible with a specified splitting when `σ(I) ⊆ I`. Compatible ideals are
closed under sums and intersections and are radical. Thus the scheme-theoretic intersection
and union of two compatibly split affine closed subschemes are reduced. Compatibility is
with one fixed splitting; radical ideals alone need not have radical sums.

The splitting descends to every compatible quotient. Perfect rings supply examples by
inverse Frobenius; no perfection, finiteness or Noetherian hypothesis is used in the ideal
theorems.

## References

* M. Brion and S. Kumar, *Frobenius splitting methods in geometry and representation theory*,
  Birkhäuser (2005), §1.1.
-/

public section

namespace TauCeti

variable (R : Type*) [CommRing R] (p : ℕ)

/-- A retraction of Frobenius that is linear for the Frobenius-twisted scalar action
on its source. -/
structure FrobeniusSplitting (R : Type*) [CommRing R] (p : ℕ) [Fact p.Prime] where
  /-- The ring has characteristic dividing `p`, including the zero ring. -/
  char_eq_zero : (p : R) = 0
  /-- The additive map underlying the splitting. -/
  toAddMonoidHom : R →+ R
  /-- Linearity for the scalar action on the Frobenius pushforward. -/
  map_pow_mul' (a b : R) : toAddMonoidHom (a ^ p * b) = a * toAddMonoidHom b
  /-- The splitting is normalized at one. -/
  map_one' : toAddMonoidHom 1 = 1

namespace FrobeniusSplitting

variable {R p} [Fact p.Prime]

instance : FunLike (FrobeniusSplitting R p) R R where
  coe σ := σ.toAddMonoidHom
  coe_injective σ τ h := by
    cases σ
    cases τ
    congr
    exact DFunLike.coe_injective h

instance : AddMonoidHomClass (FrobeniusSplitting R p) R R where
  map_zero σ := σ.toAddMonoidHom.map_zero
  map_add σ := σ.toAddMonoidHom.map_add

instance : OneHomClass (FrobeniusSplitting R p) R R where
  map_one σ := σ.map_one'

@[simp]
theorem coe_toAddMonoidHom (σ : FrobeniusSplitting R p) : ⇑σ.toAddMonoidHom = σ := (rfl)

@[ext]
theorem ext {σ τ : FrobeniusSplitting R p} (h : ∀ a, σ a = τ a) : σ = τ :=
  DFunLike.ext _ _ h

variable (σ : FrobeniusSplitting R p)

/-- Linearity for the Frobenius-twisted scalar action. -/
@[simp]
theorem map_pow_mul (a b : R) : σ (a ^ p * b) = a * σ b := σ.map_pow_mul' a b

/-- A Frobenius splitting retracts the `p`-th power map. -/
@[simp]
theorem apply_pow (a : R) : σ (a ^ p) = a := by
  have h := σ.map_pow_mul a 1
  simp only [mul_one, map_one] at h
  exact h

variable [CharP R p] in
/-- The underlying function is a left inverse to Frobenius. -/
theorem leftInverse_frobenius : Function.LeftInverse σ (frobenius R p) :=
  σ.apply_pow

variable [CharP R p] in
include σ in
/-- Frobenius is injective on a Frobenius-split ring. -/
theorem frobenius_injective : Function.Injective (frobenius R p) :=
  (leftInverse_frobenius σ).injective

/-- An ideal is compatible with `σ` if the splitting preserves it. -/
def IsCompatible (I : Ideal R) : Prop := ∀ a ∈ I, σ a ∈ I

/-- Compatibility means preservation of ideal membership by the splitting. -/
theorem isCompatible_iff (I : Ideal R) :
    σ.IsCompatible I ↔ ∀ a ∈ I, σ a ∈ I := Iff.rfl

/-- The zero ideal is compatible with every splitting. -/
@[simp]
theorem isCompatible_bot : σ.IsCompatible ⊥ := by
  intro a ha
  simp only [Ideal.mem_bot, (Ideal.mem_bot.mp ha), map_zero]

/-- The unit ideal is compatible with every splitting. -/
@[simp]
theorem isCompatible_top : σ.IsCompatible ⊤ := fun _ _ ↦ Submodule.mem_top

namespace IsCompatible

variable {σ} {I J : Ideal R}

/-- Intersections preserve compatibility with the same splitting. -/
theorem inf (hI : σ.IsCompatible I) (hJ : σ.IsCompatible J) :
    σ.IsCompatible (I ⊓ J) :=
  fun a ha ↦ ⟨hI a ha.1, hJ a ha.2⟩

/-- Sums preserve compatibility with the same splitting. -/
theorem sup (hI : σ.IsCompatible I) (hJ : σ.IsCompatible J) :
    σ.IsCompatible (I ⊔ J) := by
  intro a ha
  obtain ⟨x, hx, y, hy, rfl⟩ := Submodule.mem_sup.mp ha
  rw [map_add]
  exact (I ⊔ J).add_mem (Submodule.mem_sup_left (hI x hx))
    (Submodule.mem_sup_right (hJ y hy))

/-- Arbitrary intersections preserve compatibility, including the empty intersection. -/
theorem iInf {ι : Sort*} {I : ι → Ideal R} (hI : ∀ i, σ.IsCompatible (I i)) :
    σ.IsCompatible (⨅ i, I i) := by
  intro a ha
  simp only [Ideal.mem_iInf] at ha ⊢
  exact fun i ↦ hI i a (ha i)

/-- A compatible ideal is closed under taking `p`-th roots. -/
theorem mem_of_pow_mem (hI : σ.IsCompatible I) {a : R} (ha : a ^ p ∈ I) : a ∈ I := by
  simpa only [σ.apply_pow] using hI (a ^ p) ha

/-- Compatibly split ideals are radical. -/
theorem isRadical (hI : σ.IsCompatible I) : I.IsRadical :=
  (Ideal.isRadical_iff_pow_one_lt p (Fact.out : p.Prime).one_lt).mpr
    fun _ ha ↦ hI.mem_of_pow_mem ha

/-- A compatible closed subscheme is reduced. -/
theorem isReduced_quotient (hI : σ.IsCompatible I) : IsReduced (R ⧸ I) :=
  (Ideal.isRadical_iff_quotient_reduced I).mp hI.isRadical

/-- Descend a splitting to a compatible quotient. The additive quotient map is used;
the splitting itself is not a ring homomorphism. -/
def quotient (hI : σ.IsCompatible I) : FrobeniusSplitting (R ⧸ I) p where
  char_eq_zero := by
    rw [← map_natCast (Ideal.Quotient.mk I) p, σ.char_eq_zero, map_zero]
  toAddMonoidHom := QuotientAddGroup.map I.toAddSubgroup I.toAddSubgroup σ.toAddMonoidHom hI
  map_pow_mul' a b := by
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective a
    obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective b
    -- The ring quotient and additive quotient have the same representatives.
    exact congrArg (Ideal.Quotient.mk I) (σ.map_pow_mul a b)
  map_one' := congrArg (Ideal.Quotient.mk I) (map_one σ)

/-- The descended splitting acts on a residue class by splitting a representative. -/
@[simp]
theorem quotient_mk (hI : σ.IsCompatible I) (a : R) :
    hI.quotient (Ideal.Quotient.mk I a) = Ideal.Quotient.mk I (σ a) := (rfl)

/-- Compatibility of an ideal in a compatible quotient is equivalent to compatibility
of its inverse image in the original ring. -/
theorem quotient_isCompatible_iff (hI : σ.IsCompatible I) (J : Ideal (R ⧸ I)) :
    hI.quotient.IsCompatible J ↔ σ.IsCompatible (J.comap (Ideal.Quotient.mk I)) := by
  constructor
  · intro h a ha
    exact h (Ideal.Quotient.mk I a) ha
  · intro h a ha
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective a
    exact h a ha

end IsCompatible

include σ in
/-- Every Frobenius-split ring is reduced. -/
theorem isReduced : IsReduced R :=
  Ideal.isRadical_bot_iff.mp (IsCompatible.isRadical (isCompatible_bot σ))

section Perfect

variable [CharP R p] [PerfectRing R p]

/-- Inverse Frobenius gives the canonical splitting of a perfect ring. -/
noncomputable def ofPerfect : FrobeniusSplitting R p where
  char_eq_zero := CharP.cast_eq_zero R p
  toAddMonoidHom := (frobeniusEquiv R p).symm.toAddMonoidHom
  map_pow_mul' a b := by
    -- The additive homomorphism here is the underlying map of inverse Frobenius.
    exact ((frobeniusEquiv R p).symm.map_mul (a ^ p) b).trans
      (congrArg (· * (frobeniusEquiv R p).symm b) (frobeniusEquiv_symm_pow R p a))
  map_one' := (frobeniusEquiv R p).symm.map_one

/-- The canonical perfect-ring splitting is inverse Frobenius. -/
@[simp]
theorem ofPerfect_apply (a : R) :
    ofPerfect (R := R) (p := p) a = (frobeniusEquiv R p).symm a := (rfl)

/-- On a perfect ring, compatibility with inverse Frobenius is exactly radicality. -/
theorem ofPerfect_isCompatible_iff (I : Ideal R) :
    (ofPerfect (R := R) (p := p)).IsCompatible I ↔ I.IsRadical := by
  refine ⟨fun h ↦ h.isRadical, fun h a ha ↦ ?_⟩
  apply (Ideal.isRadical_iff_pow_one_lt p (Fact.out : p.Prime).one_lt).mp h
  simpa only [ofPerfect_apply, frobeniusEquiv_symm_pow_p] using ha

end Perfect

end FrobeniusSplitting

end TauCeti
