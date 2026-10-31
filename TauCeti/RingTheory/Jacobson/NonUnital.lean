/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Algebra.Spectrum.Quasispectrum
public import Mathlib.RingTheory.TwoSidedIdeal.Operations
public import Mathlib.RingTheory.Jacobson.Radical

import TauCeti.RingTheory.Jacobson.Basic

/-!
# The Jacobson radical of a nonunital algebra

The radical is the inverse image of the Jacobson radical of the external unitization.
We provide both its two-sided ring ideal and its scalar submodule, so scalar closure is
retained even without an identity. Quasiregularity characterizes membership and shows
that this construction agrees with `Ring.jacobson` when the algebra already has a unit.

For a two-sided ideal `J` of `A`, given as a `NonUnitalSubalgebra` closed under multiplication
by `A` on both sides, the radical of `J`, viewed as a nonunital algebra in its own right, is
`J ∩ rad A`. This is the identity `rad J = J ∩ rad A` used in the structure theory of ideals of
Banach algebras; in particular ideals of semisimple algebras are semisimple, and an ideal is a
radical algebra exactly when it lies in `rad A`.

These constructions are algebraic; no completeness or norm is required.

## Main results

* `TauCeti.mem_nonUnitalJacobson_iff_isQuasiregular_smul_add_mul`: radical membership by
  quasiregularity.
* `TauCeti.jacobson_unitization_eq_bot_iff`: over a base ring with zero radical, the unitization
  is semisimple exactly when the algebra is.
* `NonUnitalSubalgebra.coe_mem_nonUnitalJacobson_iff`: an element of a two-sided ideal `J` lies
  in `rad A` exactly when it lies in `rad J`.
* `NonUnitalSubalgebra.image_coe_nonUnitalJacobson`: `rad J = J ∩ rad A`, as subsets of `A`.

## References

* Dales, *Banach Algebras and Automatic Continuity*, §§1.3–1.5.
* The unitization and quasiregularity interfaces are Mathlib's `Unitization` and
  `isQuasiregular_iff_isUnit'`. Radical membership uses
  `TauCeti.Ring.mem_jacobson_iff_isUnit_one_add_mul_left`.
-/

public section

namespace TauCeti

variable (R A : Type*) [CommRing R] [NonUnitalRing A] [Module R A]
  [IsScalarTower R A A] [SMulCommClass R A A]

/-- The Jacobson radical of a nonunital algebra, defined through its external unitization. -/
def nonUnitalJacobson : TwoSidedIdeal A :=
  (Ring.jacobson (Unitization R A)).toTwoSided.comap (Unitization.inrNonUnitalAlgHom R A)

@[simp]
theorem mem_nonUnitalJacobson {a : A} :
    a ∈ nonUnitalJacobson R A ↔
      (a : Unitization R A) ∈ Ring.jacobson (Unitization R A) := by
  simp [nonUnitalJacobson, TwoSidedIdeal.mem_comap]

/-- The scalar submodule underlying the nonunital Jacobson radical. -/
def nonUnitalJacobsonSubmodule : Submodule R A :=
  ((Ring.jacobson (Unitization R A)).restrictScalars R).comap (Unitization.inrHom R R A)

@[simp]
theorem mem_nonUnitalJacobsonSubmodule {a : A} :
    a ∈ nonUnitalJacobsonSubmodule R A ↔ a ∈ nonUnitalJacobson R A := by
  simp [nonUnitalJacobsonSubmodule, Submodule.mem_comap]

/-- The two carriers of the radical have exactly the same elements. -/
@[simp]
theorem coe_nonUnitalJacobsonSubmodule :
    (nonUnitalJacobsonSubmodule R A : Set A) = nonUnitalJacobson R A := by
  ext a
  exact mem_nonUnitalJacobsonSubmodule R A

/-- The nonunital Jacobson radical is closed under scalar multiplication. -/
theorem smul_mem_nonUnitalJacobson (r : R) {a : A} (ha : a ∈ nonUnitalJacobson R A) :
    r • a ∈ nonUnitalJacobson R A := by
  exact (mem_nonUnitalJacobsonSubmodule R A).mp <|
    (nonUnitalJacobsonSubmodule R A).smul_mem r <|
      (mem_nonUnitalJacobsonSubmodule R A).mpr ha

/-- Membership in the nonunital radical is equivalent to quasiregularity of all
scalar-plus-left multiples. The scalar term comes from reading left multiplication
in the external unitization. -/
theorem mem_nonUnitalJacobson_iff_isQuasiregular_smul_add_mul {a : A} :
    a ∈ nonUnitalJacobson R A ↔ ∀ (r : R) (b : A), IsQuasiregular (r • a + b * a) := by
  rw [mem_nonUnitalJacobson, Ring.mem_jacobson_iff_isUnit_one_add_mul_left]
  constructor
  · intro h r b
    rw [isQuasiregular_iff_isUnit' R]
    convert h (Unitization.inl r + (b : Unitization R A)) using 1
    ext <;> simp [Unitization.snd_mul]
  · intro h x
    have hx := (h x.fst x.snd).isUnit' R
    convert hx using 1
    ext <;> simp [Unitization.snd_mul]

variable {R A} in
/-- Over a base ring with zero Jacobson radical, the external unitization of a nonunital algebra
has zero Jacobson radical exactly when the algebra does. The radical of the unitization lies in
the kernel of the augmentation `Unitization.fst`, because its image under the augmentation lies
in the radical of the base ring. -/
theorem jacobson_unitization_eq_bot_iff (hR : Ring.jacobson R = ⊥) :
    Ring.jacobson (Unitization R A) = ⊥ ↔ nonUnitalJacobson R A = ⊥ := by
  refine ⟨fun h ↦ ?_, fun h ↦ eq_bot_iff.2 fun x hx ↦ ?_⟩
  · ext a
    simpa [h] using (Unitization.inr_injective (R := R)).eq_iff' (Unitization.inr_zero R)
  have : RingHomSurjective (Unitization.fstHom R A).toRingHom :=
    ⟨fun r ↦ ⟨Unitization.inl r, Unitization.fst_inl A r⟩⟩
  have hfst : x.fst = 0 := by
    simpa [hR] using Ring.le_comap_jacobson (Unitization.fstHom R A).toRingHom hx
  have hx' : x = x.snd := Unitization.ext (by simp [hfst]) rfl
  have hsnd : x.snd ∈ nonUnitalJacobson R A := (mem_nonUnitalJacobson R A).2 (hx' ▸ hx)
  rw [h, TwoSidedIdeal.mem_bot] at hsnd
  rw [Submodule.mem_bot, hx', hsnd, Unitization.inr_zero]

section Unital

variable (B : Type*) [Ring B] [Algebra R B]

/-- For an algebra that already has an identity, the external-unitization definition
recovers its ordinary Jacobson radical. The external unitization itself is not identified
with the original algebra. -/
@[simp]
theorem nonUnitalJacobson_eq_toTwoSided_jacobson :
    nonUnitalJacobson R B = (Ring.jacobson B).toTwoSided := by
  ext a
  rw [Ideal.mem_toTwoSided, mem_nonUnitalJacobson_iff_isQuasiregular_smul_add_mul,
    Ring.mem_jacobson_iff_isUnit_one_add_mul_left]
  constructor
  · intro h b
    simpa only [zero_smul, zero_add] using (h 0 b).isUnit_one_add
  · intro h r b
    rw [isQuasiregular_iff_isUnit]
    simpa only [add_mul, Algebra.smul_def] using h (algebraMap R B r + b)

end Unital

end TauCeti

/-- Quasiregularity of an element of a right ideal may be tested in the ambient ring: its
quasi-inverse `y` satisfies `y = -(x + x * y)`, so it lies in the ideal again. -/
theorem NonUnitalSubringClass.isQuasiregular_coe_iff {S A : Type*} [NonUnitalRing A]
    [SetLike S A] [NonUnitalSubringClass S A] {s : S}
    (hr : ∀ (b : A) {y : A}, y ∈ s → y * b ∈ s) {x : s} :
    IsQuasiregular (x : A) ↔ IsQuasiregular x := by
  refine ⟨fun hx ↦ ?_, IsQuasiregular.map (NonUnitalSubringClass.subtype s)⟩
  obtain ⟨y, hy₁, hy₂⟩ := isQuasiregular_iff.mp hx
  have hyS : y ∈ s := by
    rw [show y = -((x : A) + x * y) by rw [eq_neg_iff_add_eq_zero, ← add_assoc, hy₁]]
    exact neg_mem (add_mem x.2 (hr y x.2))
  refine isQuasiregular_iff.mpr ⟨⟨y, hyS⟩, ?_, ?_⟩ <;> ext <;> simpa

namespace NonUnitalSubalgebra

open TauCeti

variable {R A : Type*} [CommRing R] [NonUnitalRing A] [Module R A]
  [IsScalarTower R A A] [SMulCommClass R A A] {S : NonUnitalSubalgebra R A}

/-- An element of a right ideal `S` that lies in the radical of the ambient algebra lies in the
radical of `S`, viewed as a nonunital algebra. -/
theorem mem_nonUnitalJacobson_of_coe_mem (hr : ∀ (b : A) {y : A}, y ∈ S → y * b ∈ S) {a : S}
    (ha : (a : A) ∈ nonUnitalJacobson R A) : a ∈ nonUnitalJacobson R S := by
  rw [mem_nonUnitalJacobson_iff_isQuasiregular_smul_add_mul] at ha ⊢
  intro r b
  rw [← NonUnitalSubringClass.isQuasiregular_coe_iff hr]
  simpa using ha r b

/-- For a two-sided ideal `S`, an element of `S` lies in the radical of the ambient algebra
exactly when it lies in the radical of `S`, viewed as a nonunital algebra. -/
theorem coe_mem_nonUnitalJacobson_iff (hl : ∀ (b : A) {y : A}, y ∈ S → b * y ∈ S)
    (hr : ∀ (b : A) {y : A}, y ∈ S → y * b ∈ S) {a : S} :
    (a : A) ∈ nonUnitalJacobson R A ↔ a ∈ nonUnitalJacobson R S := by
  refine ⟨mem_nonUnitalJacobson_of_coe_mem hr, fun ha ↦ ?_⟩
  rw [mem_nonUnitalJacobson_iff_isQuasiregular_smul_add_mul] at ha ⊢
  intro r b
  -- `c = r • a + b * a` lies in `S`, and `c * c = x * a` with `x = r • c + c * b ∈ S`.
  set c : A := r • (a : A) + b * a with hc
  have hcS : c ∈ S := add_mem (S.smul_mem r a.2) (hl b a.2)
  have hxS : -(r • c + c * b) ∈ S := neg_mem (add_mem (S.smul_mem r hcS) (hr b hcS))
  have hsq : IsQuasiregular (-(c * c)) := by
    have := (ha 0 ⟨_, hxS⟩).map (NonUnitalSubalgebraClass.subtype S)
    convert this using 1
    simp [hc, add_mul, mul_add, smul_mul_assoc, mul_smul_comm, mul_assoc]
  -- In the unitization, `1 - c * c = (1 + c) * (1 - c)` with commuting factors.
  rw [isQuasiregular_iff_isUnit' R] at hsq ⊢
  have hcomm : Commute (1 + (c : Unitization R A)) (1 - c) :=
    (Commute.one_left _).add_left ((Commute.one_right _).sub_right (Commute.refl _))
  have hfac : (1 + ((-(c * c) : A) : Unitization R A)) = (1 + c) * (1 - c) := by
    simp only [Unitization.inr_neg, Unitization.inr_mul]
    noncomm_ring
  exact (hcomm.isUnit_mul_iff.mp (hfac ▸ hsq)).1

/-- **The radical of an ideal.** For a two-sided ideal `S`, the radical of `S`, viewed as a
nonunital algebra, is `S ∩ rad A`. -/
theorem image_coe_nonUnitalJacobson (hl : ∀ (b : A) {y : A}, y ∈ S → b * y ∈ S)
    (hr : ∀ (b : A) {y : A}, y ∈ S → y * b ∈ S) :
    ((↑) : S → A) '' (nonUnitalJacobson R S : Set S) = (S : Set A) ∩ nonUnitalJacobson R A := by
  ext x
  constructor
  · rintro ⟨a, ha, rfl⟩
    exact ⟨a.2, (coe_mem_nonUnitalJacobson_iff hl hr).mpr ha⟩
  · rintro ⟨hxS, hx⟩
    exact ⟨⟨x, hxS⟩, (coe_mem_nonUnitalJacobson_iff hl hr).mp hx, rfl⟩

/-- A two-sided ideal is a radical algebra exactly when it is contained in the radical of the
ambient algebra. -/
theorem nonUnitalJacobson_eq_top_iff (hl : ∀ (b : A) {y : A}, y ∈ S → b * y ∈ S)
    (hr : ∀ (b : A) {y : A}, y ∈ S → y * b ∈ S) :
    nonUnitalJacobson R S = ⊤ ↔ (S : Set A) ⊆ nonUnitalJacobson R A := by
  refine ⟨fun h a ha ↦ ?_, fun h ↦ eq_top_iff.mpr fun a _ ↦ ?_⟩
  · exact (coe_mem_nonUnitalJacobson_iff (a := ⟨a, ha⟩) hl hr).mpr (h ▸ TwoSidedIdeal.mem_top _)
  · exact mem_nonUnitalJacobson_of_coe_mem hr (h a.2)

/-- Every two-sided ideal of a semisimple algebra is semisimple as a nonunital algebra. -/
theorem nonUnitalJacobson_eq_bot_of_eq_bot (hl : ∀ (b : A) {y : A}, y ∈ S → b * y ∈ S)
    (hr : ∀ (b : A) {y : A}, y ∈ S → y * b ∈ S) (h : nonUnitalJacobson R A = ⊥) :
    nonUnitalJacobson R S = ⊥ := by
  refine eq_bot_iff.mpr fun a ha ↦ (TwoSidedIdeal.mem_bot _).mpr ?_
  have := (coe_mem_nonUnitalJacobson_iff hl hr).mpr ha
  rw [h, TwoSidedIdeal.mem_bot] at this
  exact Subtype.ext this

end NonUnitalSubalgebra
