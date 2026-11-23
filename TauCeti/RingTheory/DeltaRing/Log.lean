/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.DeltaRing.Basic

/-!
# `δ_log`-rings

Fix a prime `p`, a `δ`-ring `A` and a prelog structure on `A`, that is a monoid `M` with a
monoid homomorphism `α : M →* A` into the multiplicative monoid of `A` (elements of `M` may map
to zero). A `δ_log`-structure on `(A, δ, α)` (Koshikawa, Definition 2.2) is a map
`δ_log : M → A` with

* `δ_log 1 = 0`;
* `α m ^ p * δ_log m = δ (α m)`;
* `δ_log (m * m') = δ_log m + δ_log m' + p * δ_log m * δ_log m'`.

These are the logarithmic analogues of the `δ`-ring axioms: the Frobenius lift
`φ x = x ^ p + p * δ x` satisfies `φ (α m) = α m ^ p * (1 + p * δ_log m)`, and the correction
factor `m ↦ 1 + p * δ_log m` is a monoid homomorphism `M →* A`. They are the input for log prisms
and for the monoid Frobenius of a `δ_log` log ring.

When `α` takes values in the nonzerodivisors of `A`, a `δ_log`-structure is unique, and it exists
if and only if `α m ^ p` divides `δ (α m)` for every `m`. In particular the units of any `δ`-ring
carry a unique `δ_log`-structure, `δ_log u = δ u * u⁻¹ ^ p`. If `δ` vanishes on the image of `α`
then `δ_log = 0` is a `δ_log`-structure, and the structures with `δ_log = 0` are those of
rank one.

## Main definitions

* `TauCeti.DeltaLogStructure p α`: a `δ_log`-structure on the prelog `δ`-ring `α : M →* A`.
* `TauCeti.DeltaLogStructure.correction`: the monoid homomorphism `m ↦ 1 + p * δ_log m`.
* `TauCeti.DeltaLogStructure.IsRankOne`: the predicate `δ_log = 0`.
* `TauCeti.DeltaLogStructure.ofDeltaEqZero`: the rank-one structure when `δ ∘ α = 0`.
* `TauCeti.DeltaLogStructure.ofPowDvd`: the structure of a prelog structure by nonzerodivisors
  with `α m ^ p ∣ δ (α m)`.
* `TauCeti.DeltaLogStructure.units`: the `δ_log`-structure on the units of a `δ`-ring.
* `TauCeti.DeltaLogStructure.map`: base change of a `δ_log`-structure along a map of `δ`-rings.
* `TauCeti.DeltaLogStructure.Hom`: morphisms of `δ_log`-rings, with identities and composition.

## Main statements

* `TauCeti.DeltaLogStructure.frobenius_apply`: `φ (α m) = α m ^ p * (1 + p * δ_log m)`.
* `TauCeti.DeltaLogStructure.exists_frobenius_iterate_eq`:
  `φ^[n] (α m) ∈ α m ^ p ^ n * (1 + p * A)`.
* `TauCeti.DeltaLogStructure.subsingleton_of_mem_nonZeroDivisors` and
  `TauCeti.DeltaLogStructure.nonempty_iff_forall_pow_dvd`: uniqueness and the existence
  criterion for prelog structures by nonzerodivisors.

## References

* T. Koshikawa, *Logarithmic prismatic cohomology I*, §2, Definition 2.2, Remark 2.3 and
  Example 2.4.
-/

public section

namespace TauCeti

open DeltaRing

/-- A `δ_log`-structure on the prelog `δ`-ring `(A, δ, α)` for the prime `p` (Koshikawa,
*Logarithmic prismatic cohomology I*, Definition 2.2): a map `deltaLog : M → A` with
`deltaLog 1 = 0`, `α m ^ p * deltaLog m = δ (α m)` and
`deltaLog (m * m') = deltaLog m + deltaLog m' + p * deltaLog m * deltaLog m'`.

The prelog structure is the monoid homomorphism `α : M →* A` to the multiplicative monoid of `A`;
no integrality or unit condition is imposed on it. -/
@[ext]
structure DeltaLogStructure (p : ℕ) {A M : Type*} [CommRing A] [DeltaRing p A] [Monoid M]
    (α : M →* A) where
  /-- The logarithmic `δ`-operation `δ_log : M → A`. -/
  deltaLog : M → A
  deltaLog_one : deltaLog 1 = 0
  pow_mul_deltaLog (m : M) : α m ^ p * deltaLog m = delta p (α m)
  deltaLog_mul (m m' : M) :
    deltaLog (m * m') = deltaLog m + deltaLog m' + p * deltaLog m * deltaLog m'

namespace DeltaLogStructure

attribute [simp] deltaLog_one

variable {p : ℕ} {A M : Type*} [CommRing A] [DeltaRing p A] [Monoid M] {α : M →* A}

/-- The image of each element of the monoid has `p`-th power dividing its `δ`. -/
theorem pow_dvd_delta (D : DeltaLogStructure p α) (m : M) : α m ^ p ∣ delta p (α m) :=
  ⟨D.deltaLog m, (D.pow_mul_deltaLog m).symm⟩

section Correction

/-- The correction factor `m ↦ 1 + p * δ_log m` of a `δ_log`-structure, a monoid homomorphism
`M →* A`. It measures the failure of the Frobenius to be the `p`-th power on the image of `α`
(`frobenius_apply`). -/
def correction (D : DeltaLogStructure p α) : M →* A where
  toFun m := 1 + p * D.deltaLog m
  map_one' := by simp
  map_mul' m m' := by
    rw [D.deltaLog_mul]
    ring

@[simp]
theorem correction_apply (D : DeltaLogStructure p α) (m : M) :
    D.correction m = 1 + p * D.deltaLog m :=
  (rfl)

end Correction

section Frobenius

variable [Fact p.Prime]

/-- `φ (α m) - α m ^ p = p * α m ^ p * δ_log m`. -/
theorem frobenius_sub_pow (D : DeltaLogStructure p α) (m : M) :
    frobenius p A (α m) - α m ^ p = p * α m ^ p * D.deltaLog m := by
  rw [DeltaRing.frobenius_sub_pow, ← D.pow_mul_deltaLog, mul_assoc]

/-- The Frobenius on the image of a prelog structure with a `δ_log`-structure:
`φ (α m) = α m ^ p * (1 + p * δ_log m)` (Koshikawa, after Definition 2.2). -/
theorem frobenius_apply (D : DeltaLogStructure p α) (m : M) :
    frobenius p A (α m) = α m ^ p * D.correction m := by
  rw [correction_apply, DeltaRing.frobenius_apply, ← D.pow_mul_deltaLog]
  ring

/-- Iterates of the Frobenius on the image of `α` lie in `α m ^ p ^ n * (1 + p * A)`. -/
theorem exists_frobenius_iterate_eq (D : DeltaLogStructure p α) (m : M) (n : ℕ) :
    ∃ a : A, (frobenius p A)^[n] (α m) = α m ^ p ^ n * (1 + p * a) := by
  induction n with
  | zero => exact ⟨0, by simp⟩
  | succ n ih =>
    obtain ⟨a, ha⟩ := ih
    -- `φ^[n + 1] (α m) = α m ^ p ^ (n + 1) * (c (m ^ p ^ n) * φ (1 + p * a))`, and the
    -- product of two elements of `1 + p * A` lies in `1 + p * A`.
    have h : (frobenius p A)^[n + 1] (α m) =
        α m ^ p ^ (n + 1) * (D.correction (m ^ p ^ n) * frobenius p A (1 + p * a)) := by
      simp only [Function.iterate_succ_apply', ha, map_mul, map_pow, D.frobenius_apply]
      ring
    refine ⟨D.deltaLog (m ^ p ^ n) + frobenius p A a +
      p * D.deltaLog (m ^ p ^ n) * frobenius p A a, h.trans ?_⟩
    simp only [correction_apply, map_add, map_one, map_mul, map_natCast]
    ring

end Frobenius

section Uniqueness

/-- If `α` takes values in the nonzerodivisors of `A`, two `δ_log`-structures on `α`
coincide. -/
theorem eq_of_mem_nonZeroDivisors (hα : ∀ m, α m ∈ nonZeroDivisors A)
    (D D' : DeltaLogStructure p α) : D = D' := by
  ext m
  rw [← mul_cancel_left_mem_nonZeroDivisors (pow_mem (hα m) p), D.pow_mul_deltaLog,
    D'.pow_mul_deltaLog]

/-- If `α` takes values in the nonzerodivisors of `A`, there is at most one `δ_log`-structure
on `α`. -/
theorem subsingleton_of_mem_nonZeroDivisors (hα : ∀ m, α m ∈ nonZeroDivisors A) :
    Subsingleton (DeltaLogStructure p α) :=
  ⟨eq_of_mem_nonZeroDivisors hα⟩

end Uniqueness

section OfPowDvd

/-- The `δ_log`-structure of a prelog structure `α` by nonzerodivisors such that `α m ^ p`
divides `δ (α m)` for every `m`: `δ_log m` is the quotient `δ (α m) / α m ^ p`. No
`p`-torsion-freeness of `A` is needed. -/
noncomputable def ofPowDvd (hα : ∀ m, α m ∈ nonZeroDivisors A)
    (hdvd : ∀ m, α m ^ p ∣ delta p (α m)) : DeltaLogStructure p α where
  deltaLog m := (hdvd m).choose
  deltaLog_one := by
    have h := (hdvd 1).choose_spec
    generalize (hdvd 1).choose = c at h ⊢
    simpa using h.symm
  pow_mul_deltaLog m := (hdvd m).choose_spec.symm
  deltaLog_mul m m' := by
    have h := (hdvd (m * m')).choose_spec
    have hm := (hdvd m).choose_spec
    have hm' := (hdvd m').choose_spec
    generalize (hdvd (m * m')).choose = c at h ⊢
    generalize (hdvd m).choose = a at hm ⊢
    generalize (hdvd m').choose = b at hm' ⊢
    have hreg : α m ^ p * α m' ^ p ∈ nonZeroDivisors A := by
      rw [← mul_pow, ← map_mul]
      exact pow_mem (hα (m * m')) p
    rw [map_mul, delta_mul, hm, hm', mul_pow] at h
    refine (mul_cancel_left_mem_nonZeroDivisors hreg).mp ?_
    linear_combination -h

/-- For a prelog structure by nonzerodivisors, a `δ_log`-structure exists if and only if
`α m ^ p` divides `δ (α m)` for every `m`. -/
theorem nonempty_iff_forall_pow_dvd (hα : ∀ m, α m ∈ nonZeroDivisors A) :
    Nonempty (DeltaLogStructure p α) ↔ ∀ m, α m ^ p ∣ delta p (α m) :=
  ⟨fun ⟨D⟩ => D.pow_dvd_delta, fun hdvd => ⟨ofPowDvd hα hdvd⟩⟩

end OfPowDvd

section RankOne

/-- A `δ_log`-structure is of rank one if `δ_log = 0`. -/
def IsRankOne (D : DeltaLogStructure p α) : Prop :=
  D.deltaLog = 0

theorem isRankOne_iff (D : DeltaLogStructure p α) : D.IsRankOne ↔ ∀ m, D.deltaLog m = 0 :=
  funext_iff

/-- A rank-one `δ_log`-structure forces `δ` to vanish on the image of `α`. -/
theorem IsRankOne.delta_eq_zero {D : DeltaLogStructure p α} (hD : D.IsRankOne) (m : M) :
    delta p (α m) = 0 := by
  rw [← D.pow_mul_deltaLog, (D.isRankOne_iff.mp hD m), mul_zero]

/-- For a rank-one `δ_log`-structure the Frobenius is the `p`-th power on the image of `α`. -/
theorem IsRankOne.frobenius_apply [Fact p.Prime] {D : DeltaLogStructure p α} (hD : D.IsRankOne)
    (m : M) : frobenius p A (α m) = α m ^ p := by
  rw [DeltaRing.frobenius_apply, hD.delta_eq_zero, mul_zero, add_zero]

/-- The rank-one `δ_log`-structure `δ_log = 0`, when `δ` vanishes on the image of `α`
(Koshikawa, Example 2.4). -/
def ofDeltaEqZero (h : ∀ m, delta p (α m) = 0) : DeltaLogStructure p α where
  deltaLog := 0
  deltaLog_one := rfl
  pow_mul_deltaLog m := by rw [Pi.zero_apply, mul_zero, h]
  deltaLog_mul _ _ := by simp

@[simp]
theorem deltaLog_ofDeltaEqZero (h : ∀ m, delta p (α m) = 0) (m : M) :
    (ofDeltaEqZero h).deltaLog m = 0 :=
  (rfl)

theorem isRankOne_ofDeltaEqZero (h : ∀ m, delta p (α m) = 0) : (ofDeltaEqZero h).IsRankOne :=
  (isRankOne_iff _).mpr (deltaLog_ofDeltaEqZero h)

/-- A `δ_log`-structure is of rank one if and only if it is `ofDeltaEqZero`. -/
theorem isRankOne_iff_eq_ofDeltaEqZero (D : DeltaLogStructure p α) :
    D.IsRankOne ↔ ∃ h, D = ofDeltaEqZero h :=
  ⟨fun hD => ⟨hD.delta_eq_zero, DeltaLogStructure.ext (funext fun m => by
    rw [D.isRankOne_iff.mp hD m, deltaLog_ofDeltaEqZero])⟩,
    fun ⟨_, hD⟩ => hD ▸ isRankOne_ofDeltaEqZero _⟩

/-- On a subsingleton monoid there is exactly one `δ_log`-structure, the rank-one one. -/
instance instUniqueOfSubsingleton [Subsingleton M] : Unique (DeltaLogStructure p α) where
  default := ofDeltaEqZero fun m => by rw [Subsingleton.elim m 1, map_one, delta_one]
  uniq D := by
    ext m
    rw [Subsingleton.elim m 1, deltaLog_one, deltaLog_ofDeltaEqZero]

end RankOne

section Units

variable (p A) in
/-- The `δ_log`-structure on the units of a `δ`-ring, `δ_log u = δ u * u⁻¹ ^ p`. It is the
only one (`instUniqueUnits`). -/
def units : DeltaLogStructure p (Units.coeHom A) where
  deltaLog u := delta p (u : A) * ((u⁻¹ : Aˣ) : A) ^ p
  deltaLog_one := by simp
  pow_mul_deltaLog u := by simp [mul_left_comm _ (delta p _), ← mul_pow]
  deltaLog_mul u v := by
    have hu : ((u : A) * ((u⁻¹ : Aˣ) : A)) ^ p = 1 := by rw [Units.mul_inv, one_pow]
    have hv : ((v : A) * ((v⁻¹ : Aˣ) : A)) ^ p = 1 := by rw [Units.mul_inv, one_pow]
    rw [Units.val_mul, mul_inv, Units.val_mul, delta_mul]
    linear_combination delta p (v : A) * ((v⁻¹ : Aˣ) : A) ^ p * hu +
      delta p (u : A) * ((u⁻¹ : Aˣ) : A) ^ p * hv

@[simp]
theorem deltaLog_units (u : Aˣ) :
    (units p A).deltaLog u = delta p (u : A) * ((u⁻¹ : Aˣ) : A) ^ p :=
  (rfl)

/-- The units of a `δ`-ring carry exactly one `δ_log`-structure. -/
instance instUniqueUnits : Unique (DeltaLogStructure p (Units.coeHom A)) where
  default := units p A
  uniq D := eq_of_mem_nonZeroDivisors (fun u => u.isUnit.mem_nonZeroDivisors) D _

end Units

section Map

variable {B : Type*} [CommRing B] [DeltaRing p B]

/-- Base change of a `δ_log`-structure along a map of `δ`-rings `f : A →+* B`: the prelog
structure `f ∘ α` on `B` with `δ_log = f ∘ δ_log` (Koshikawa, Example 2.4(4)). -/
def map (D : DeltaLogStructure p α) (f : A →+* B)
    (hf : ∀ x, f (delta p x) = delta p (f x)) :
    DeltaLogStructure p ((f : A →* B).comp α) where
  deltaLog m := f (D.deltaLog m)
  deltaLog_one := by simp
  pow_mul_deltaLog m := by simp [← hf, ← D.pow_mul_deltaLog]
  deltaLog_mul m m' := by simp [D.deltaLog_mul]

@[simp]
theorem deltaLog_map (D : DeltaLogStructure p α) (f : A →+* B)
    (hf : ∀ x, f (delta p x) = delta p (f x)) (m : M) :
    (D.map f hf).deltaLog m = f (D.deltaLog m) :=
  (rfl)

end Map

section Hom

variable {B N : Type*} [CommRing B] [DeltaRing p B] [Monoid N] {β : N →* B}
  {C L : Type*} [CommRing C] [DeltaRing p C] [Monoid L] {γ : L →* C}

/-- A morphism of `δ_log`-rings `(A, M, D) → (B, N, E)` (Koshikawa, Definition 2.2): a ring
homomorphism commuting with `δ` and a monoid homomorphism forming a map of prelog rings, which
together intertwine the two `δ_log`-operations. Two morphisms are equal when their ring and monoid
homomorphisms are (`Hom.ext`). -/
@[ext]
structure Hom (D : DeltaLogStructure p α) (E : DeltaLogStructure p β) where
  /-- The ring homomorphism of a morphism of `δ_log`-rings. -/
  ringHom : A →+* B
  /-- The monoid homomorphism of a morphism of `δ_log`-rings. -/
  monoidHom : M →* N
  map_delta (x : A) : ringHom (delta p x) = delta p (ringHom x)
  apply_monoidHom (m : M) : β (monoidHom m) = ringHom (α m)
  deltaLog_monoidHom (m : M) : E.deltaLog (monoidHom m) = ringHom (D.deltaLog m)

namespace Hom

attribute [simp] map_delta apply_monoidHom deltaLog_monoidHom

/-- The identity morphism of a `δ_log`-ring. -/
def id (D : DeltaLogStructure p α) : Hom D D where
  ringHom := RingHom.id A
  monoidHom := MonoidHom.id M
  map_delta _ := rfl
  apply_monoidHom _ := rfl
  deltaLog_monoidHom _ := rfl

@[simp]
theorem id_ringHom (D : DeltaLogStructure p α) : (id D).ringHom = RingHom.id A :=
  (rfl)

@[simp]
theorem id_monoidHom (D : DeltaLogStructure p α) : (id D).monoidHom = MonoidHom.id M :=
  (rfl)

variable {D : DeltaLogStructure p α} {E : DeltaLogStructure p β} {F : DeltaLogStructure p γ}

/-- The composition of morphisms of `δ_log`-rings. -/
def comp (g : Hom E F) (f : Hom D E) : Hom D F where
  ringHom := g.ringHom.comp f.ringHom
  monoidHom := g.monoidHom.comp f.monoidHom
  map_delta x := by simp [f.map_delta, g.map_delta]
  apply_monoidHom m := by simp [f.apply_monoidHom, g.apply_monoidHom]
  deltaLog_monoidHom m := by simp [f.deltaLog_monoidHom, g.deltaLog_monoidHom]

@[simp]
theorem comp_ringHom (g : Hom E F) (f : Hom D E) :
    (g.comp f).ringHom = g.ringHom.comp f.ringHom :=
  (rfl)

@[simp]
theorem comp_monoidHom (g : Hom E F) (f : Hom D E) :
    (g.comp f).monoidHom = g.monoidHom.comp f.monoidHom :=
  (rfl)

@[simp]
theorem id_comp (f : Hom D E) : (id E).comp f = f := by
  ext <;> rfl

@[simp]
theorem comp_id (f : Hom D E) : f.comp (id D) = f := by
  ext <;> rfl

theorem comp_assoc {K R : Type*} [CommRing R] [DeltaRing p R] [Monoid K] {ρ : K →* R}
    {G : DeltaLogStructure p ρ} (h : Hom F G) (g : Hom E F) (f : Hom D E) :
    (h.comp g).comp f = h.comp (g.comp f) := by
  ext <;> rfl

/-- A morphism of `δ_log`-rings commutes with the Frobenius lifts. -/
theorem map_frobenius [Fact p.Prime] (f : Hom D E) (x : A) :
    f.ringHom (frobenius p A x) = frobenius p B (f.ringHom x) :=
  DeltaRing.map_frobenius f.ringHom f.map_delta x

/-- A morphism of `δ_log`-rings intertwines the correction factors. -/
theorem correction_monoidHom (f : Hom D E) (m : M) :
    E.correction (f.monoidHom m) = f.ringHom (D.correction m) := by
  simp [f.deltaLog_monoidHom]

end Hom

variable {B : Type*} [CommRing B] [DeltaRing p B]

/-- The canonical morphism of `δ_log`-rings from a `δ_log`-ring to its base change along a map
of `δ`-rings, the identity on the monoid. -/
def toMap (D : DeltaLogStructure p α) (f : A →+* B)
    (hf : ∀ x, f (delta p x) = delta p (f x)) : Hom D (D.map f hf) where
  ringHom := f
  monoidHom := MonoidHom.id M
  map_delta := hf
  apply_monoidHom m := by simp
  deltaLog_monoidHom m := by simp

@[simp]
theorem toMap_ringHom (D : DeltaLogStructure p α) (f : A →+* B)
    (hf : ∀ x, f (delta p x) = delta p (f x)) : (D.toMap f hf).ringHom = f :=
  (rfl)

@[simp]
theorem toMap_monoidHom (D : DeltaLogStructure p α) (f : A →+* B)
    (hf : ∀ x, f (delta p x) = delta p (f x)) : (D.toMap f hf).monoidHom = MonoidHom.id M :=
  (rfl)

end Hom

end DeltaLogStructure

end TauCeti
