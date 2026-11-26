/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Jacobson.Radical
public import TauCeti.Algebra.Group.Units.Basic
public import TauCeti.RingTheory.DeltaRing.Log.Basic

/-!
# The monoid Frobenius of a `δ_log` log ring

Let `(A, α : M →* A, δ_log)` be a `δ_log`-ring over a commutative monoid `M`. The Frobenius lift
`φ x = x ^ p + p * δ x` of `A` satisfies `φ (α m) = α m ^ p * (1 + p * δ_log m)`. If `p` lies in
the Jacobson radical of `A`, the correction factor `1 + p * δ_log m` is a unit of `A`. If moreover
`(A, M)` is a log ring, so that `α` identifies the units of `M` with the units of `A`, the
correction factor has a unique preimage among the units of `M`, and

```text
φ_M m = m ^ p * α⁻¹ (1 + p * δ_log m)
```

is a monoid endomorphism of `M` lifting `φ` along `α` (Koshikawa, Remark 2.3): the pair `(φ, φ_M)`
is an endomorphism of the log ring `(A, M)`. Of the log-ring condition only the bijectivity of
`Units.map α : Mˣ →* Aˣ` is used; in a log ring `α⁻¹(Aˣ) = Mˣ`, so this is the condition that
`α⁻¹(Aˣ) → Aˣ` is an isomorphism.

When `δ_log = 0` the monoid Frobenius is the `p`-th power map, and for a rank-one `δ_log`-structure
the `p`-th power map lifts `φ` along `α` for every prelog structure, with no log-ring or Jacobson
radical hypothesis. On the units of `M` the monoid Frobenius is the Frobenius of `A`, transported
along `Mˣ ≃* Aˣ`, and morphisms of `δ_log`-rings commute with the monoid Frobenius.

## Main definitions

* `TauCeti.DeltaLogStructure.monoidFrobenius`: the monoid Frobenius
  `φ_M m = m ^ p * α⁻¹ (1 + p * δ_log m)` of a `δ_log` log ring with `p` in the Jacobson radical.

## Main statements

* `TauCeti.DeltaLogStructure.apply_monoidFrobenius`: `α (φ_M m) = φ (α m)`.
* `TauCeti.DeltaLogStructure.IsRankOne.monoidFrobenius_eq`: if `δ_log = 0` then `φ_M m = m ^ p`.
* `TauCeti.DeltaLogStructure.IsRankOne.comp_powMonoidHom`: for a rank-one structure the `p`-th
  power map of `M` lifts `φ` along any prelog structure.
* `TauCeti.DeltaLogStructure.units_map_monoidFrobenius`: on `Mˣ ≃* Aˣ`, `φ_M` is the restriction
  of `φ`.
* `TauCeti.DeltaLogStructure.Hom.monoidHom_monoidFrobenius`: morphisms of `δ_log`-rings commute
  with the monoid Frobenius.

## References

* T. Koshikawa, *Logarithmic prismatic cohomology I*, §2, Remark 2.3.
-/

public section

namespace TauCeti

namespace DeltaLogStructure

open DeltaRing

variable {p : ℕ} {A M : Type*} [CommRing A] [DeltaRing p A]

/-- If `p` lies in the Jacobson radical of `A`, the correction factor `1 + p * δ_log m` is a
unit. -/
theorem isUnit_correction [Monoid M] {α : M →* A} (D : DeltaLogStructure p α)
    (hp : (p : A) ∈ Ring.jacobson A) (m : M) : IsUnit (D.correction m) := by
  rw [correction_apply, add_comm]
  exact Ring.mem_jacobson_iff.mp hp _

section MonoidFrobenius

variable [CommMonoid M] {α : M →* A}

/-- The monoid Frobenius `φ_M m = m ^ p * α⁻¹ (1 + p * δ_log m)` of a `δ_log`-ring
(Koshikawa, Remark 2.3), for `p` in the Jacobson radical of `A` and a prelog structure `α`
identifying the units of `M` with those of `A` (as in a log ring). Here `α⁻¹` is the inverse of
`Units.map α : Mˣ ≃* Aˣ`, applied to the unit `1 + p * δ_log m` (`isUnit_correction`).

It is characterized by `monoidFrobenius_apply_eq_pow_mul`, and it lifts the Frobenius of `A`
along `α` (`apply_monoidFrobenius`). -/
noncomputable def monoidFrobenius (D : DeltaLogStructure p α) (hp : (p : A) ∈ Ring.jacobson A)
    (hα : Function.Bijective (Units.map α)) : M →* M :=
  powMonoidHom p * (Units.coeHom M).comp
    ((MulEquiv.ofBijective (Units.map α) hα).symm.toMonoidHom.comp
      (IsUnit.liftRight D.correction (D.isUnit_correction hp)))

/-- The monoid Frobenius sends `m` to `m ^ p * u` for the unit `u` of `M` with
`α u = 1 + p * δ_log m`; since `Units.map α` is bijective there is exactly one such unit. -/
theorem monoidFrobenius_apply_eq_pow_mul (D : DeltaLogStructure p α)
    (hp : (p : A) ∈ Ring.jacobson A) (hα : Function.Bijective (Units.map α)) {m : M} {u : Mˣ}
    (hu : α u = D.correction m) : D.monoidFrobenius hp hα m = m ^ p * u := by
  have h : IsUnit.liftRight D.correction (D.isUnit_correction hp) m =
      MulEquiv.ofBijective (Units.map α) hα u :=
    Units.ext (by simp [IsUnit.coe_liftRight, hu])
  simp only [monoidFrobenius, MonoidHom.mul_apply, powMonoidHom_apply, MonoidHom.comp_apply, h,
    MulEquiv.toMonoidHom_eq_coe, MonoidHom.coe_ofClass, MulEquiv.symm_apply_apply,
    Units.coeHom_apply]

/-- For a `δ_log` log ring with `p` in the Jacobson radical, some unit of `M` maps to the
correction factor `1 + p * δ_log m`. -/
private theorem exists_units_apply_eq_correction (D : DeltaLogStructure p α)
    (hp : (p : A) ∈ Ring.jacobson A) (hα : Function.Bijective (Units.map α)) (m : M) :
    ∃ u : Mˣ, α u = D.correction m := by
  obtain ⟨u, hu⟩ := hα.2 (D.isUnit_correction hp m).unit
  exact ⟨u, by simpa using congrArg Units.val hu⟩

/-- The monoid Frobenius lifts the Frobenius of `A` along `α`: `α (φ_M m) = φ (α m)`, so that
`(φ, φ_M)` is an endomorphism of the log ring `(A, M)` (Koshikawa, Remark 2.3). -/
@[simp]
theorem apply_monoidFrobenius [Fact p.Prime] (D : DeltaLogStructure p α)
    (hp : (p : A) ∈ Ring.jacobson A) (hα : Function.Bijective (Units.map α)) (m : M) :
    α (D.monoidFrobenius hp hα m) = frobenius p A (α m) := by
  obtain ⟨u, hu⟩ := D.exists_units_apply_eq_correction hp hα m
  rw [D.monoidFrobenius_apply_eq_pow_mul hp hα hu, map_mul, map_pow, hu, D.frobenius_apply]

/-- The monoid Frobenius intertwines the prelog structure with the Frobenius of `A`. -/
theorem comp_monoidFrobenius [Fact p.Prime] (D : DeltaLogStructure p α)
    (hp : (p : A) ∈ Ring.jacobson A) (hα : Function.Bijective (Units.map α)) :
    α.comp (D.monoidFrobenius hp hα) = (frobenius p A : A →* A).comp α :=
  MonoidHom.ext (D.apply_monoidFrobenius hp hα)

/-- On the units of `M` the monoid Frobenius is the Frobenius of `A`, transported along the
isomorphism `Units.map α : Mˣ ≃* Aˣ`. -/
theorem units_map_monoidFrobenius [Fact p.Prime] (D : DeltaLogStructure p α)
    (hp : (p : A) ∈ Ring.jacobson A) (hα : Function.Bijective (Units.map α)) (u : Mˣ) :
    Units.map (D.monoidFrobenius hp hα) u = (MulEquiv.ofBijective (Units.map α) hα).symm
      (Units.map (frobenius p A : A →* A) (Units.map α u)) := by
  rw [MulEquiv.eq_symm_apply]
  ext
  simp [D.apply_monoidFrobenius hp hα]

/-- If `δ_log = 0`, the monoid Frobenius is the `p`-th power map of `M`. -/
theorem IsRankOne.monoidFrobenius_eq {D : DeltaLogStructure p α} (hD : D.IsRankOne)
    (hp : (p : A) ∈ Ring.jacobson A) (hα : Function.Bijective (Units.map α)) :
    D.monoidFrobenius hp hα = powMonoidHom p :=
  MonoidHom.ext fun m => by
    rw [D.monoidFrobenius_apply_eq_pow_mul hp hα (u := 1)
      (by simp [(D.isRankOne_iff.mp hD m)]), Units.val_one, mul_one, powMonoidHom_apply]

/-- For a rank-one `δ_log`-structure the `p`-th power map of `M` lifts the Frobenius of `A` along
`α`: `α (m ^ p) = φ (α m)`. Unlike `monoidFrobenius`, this lift needs neither the log-ring
condition nor `p` in the Jacobson radical. -/
theorem IsRankOne.comp_powMonoidHom [Fact p.Prime] {D : DeltaLogStructure p α}
    (hD : D.IsRankOne) : α.comp (powMonoidHom p) = (frobenius p A : A →* A).comp α :=
  MonoidHom.ext fun m => by simp [hD.frobenius_apply]

/-- The trivial log structure `Aˣ → A`: the monoid Frobenius of the units of a `δ`-ring is the
Frobenius of `A` restricted to the units. The bijectivity hypothesis holds by
`Units.map_coeHom_bijective`. -/
@[simp]
theorem monoidFrobenius_units [Fact p.Prime] (hp : (p : A) ∈ Ring.jacobson A)
    (hα : Function.Bijective (Units.map (Units.coeHom A))) (u : Aˣ) :
    (units p A).monoidFrobenius hp hα u = Units.map (frobenius p A : A →* A) u :=
  Units.ext (by
    simpa only [Units.coeHom_apply, Units.coe_map, MonoidHom.coe_ofClass] using
      (units p A).apply_monoidFrobenius hp hα u)

variable {B N : Type*} [CommRing B] [DeltaRing p B] [CommMonoid N] {β : N →* B}

/-- A morphism of `δ_log`-rings commutes with the monoid Frobenius:
`f (φ_M m) = φ_N (f m)`. -/
theorem Hom.monoidHom_monoidFrobenius {D : DeltaLogStructure p α} {E : DeltaLogStructure p β}
    (f : Hom D E) (hpA : (p : A) ∈ Ring.jacobson A) (hα : Function.Bijective (Units.map α))
    (hpB : (p : B) ∈ Ring.jacobson B) (hβ : Function.Bijective (Units.map β)) (m : M) :
    f.monoidHom (D.monoidFrobenius hpA hα m) = E.monoidFrobenius hpB hβ (f.monoidHom m) := by
  obtain ⟨u, hu⟩ := D.exists_units_apply_eq_correction hpA hα m
  rw [D.monoidFrobenius_apply_eq_pow_mul hpA hα hu,
    E.monoidFrobenius_apply_eq_pow_mul hpB hβ (u := Units.map f.monoidHom u)
      (by simp [f.apply_monoidHom, hu, f.correction_monoidHom]),
    map_mul, map_pow, Units.coe_map]

end MonoidFrobenius

end DeltaLogStructure

end TauCeti
