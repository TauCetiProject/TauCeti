/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Derivation.Basic
public import TauCeti.Algebra.Homology.DG.Algebra.Augmentation
public import TauCeti.Algebra.TrivSqZeroExt.Grading

/-!
# The differential graded algebra of a derivation

For a commutative `S`-algebra `R`, a symmetric `R`-module `M` and an `S`-linear derivation
`D : R → M`, the trivial square-zero extension `R ⊕ M` (Mathlib's `TrivSqZeroExt R M`), with `R` in
degree `0` and `M` in degree `1`, is a differential graded algebra for the differential
`(r, m) ↦ (0, D r)`; the grading is `TauCeti.trivSqZeroExtGrading`
(`TauCeti.Algebra.TrivSqZeroExt.Grading`).  It is the two-term complex `R → M` made
multiplicative: the Leibniz rule for `d` is exactly the Leibniz rule for `D`, and `M · M = 0`
makes it graded-commutative.

Its cohomology is `ker D` in degree `0` and `coker D` in degree `1`.  This file records the
consequence used for interval objects: the unit `S → R ⊕ M` is a quasi-isomorphism exactly when
`S → R` is injective, `ker D` consists of scalars and `D` is surjective, and then so is every
augmentation `R ⊕ M → S`.  The basic example is the polynomial interval `Λ(t, dt)` of rational
homotopy theory, where `R = M = K[t]` and `D` is differentiation
(`TauCeti.AlgebraicTopology.RationalHomotopy.PolynomialInterval`).

## Main definitions

* `Derivation.trivSqZeroExtDifferential`: the differential `(r, m) ↦ (0, D r)` of a derivation.
* `Derivation.trivSqZeroExtAugmentation`: the augmentation `(r, m) ↦ φ r` of a character
  `φ : R → S`.

## Main results

* `Derivation.isDGAlgebra_trivSqZeroExtDifferential`: `R ⊕ M` is a differential graded algebra.
* `Derivation.trivSqZeroExtUnitHom_cohomologyMap_bijective_iff`: the unit `S → R ⊕ M` is a
  quasi-isomorphism exactly when `S → R` is injective and `D` is surjective with kernel the
  scalars.
* `Derivation.trivSqZeroExtAugmentation_cohomologyMap_bijective_iff`: the same criterion for
  every augmentation.
-/

public section

open TauCeti

@[inherit_doc] local notation "tsze" => TrivSqZeroExt

namespace Derivation

open TrivSqZeroExt

variable {S R M : Type*} [CommRing S] [CommRing R] [AddCommGroup M] [Algebra S R]
  [Module S M] [Module R M] [Module Rᵐᵒᵖ M] [IsCentralScalar R M] [IsScalarTower S R M]
  [IsScalarTower S Rᵐᵒᵖ M] (D : Derivation S R M)

/-- The differential `(r, m) ↦ (0, D r)` on the trivial square-zero extension `R ⊕ M` defined by a
derivation `D : R → M`. -/
def trivSqZeroExtDifferential : tsze R M →ₗ[S] tsze R M where
  toFun x := inr (D x.fst)
  map_add' x y := by simp
  map_smul' s x := by simp

omit [Module Rᵐᵒᵖ M] [IsCentralScalar R M] [IsScalarTower S R M] [IsScalarTower S Rᵐᵒᵖ M] in
@[simp]
theorem trivSqZeroExtDifferential_apply (x : tsze R M) :
    D.trivSqZeroExtDifferential x = inr (D x.fst) :=
  (rfl)

/-- The trivial square-zero extension `R ⊕ M`, with `R` in degree `0` and `M` in degree `1`, is a
differential graded algebra for the differential `(r, m) ↦ (0, D r)` of a derivation
`D : R → M`. -/
theorem isDGAlgebra_trivSqZeroExtDifferential :
    IsDGAlgebra (trivSqZeroExtGrading S R M) D.trivSqZeroExtDifferential where
  map_mem {p} x hx := by
    by_cases hp : p = 0
    · subst hp
      simp
    · simp [fst_eq_zero_of_mem_trivSqZeroExtGrading hx hp]
  sq_zero x := by simp
  leibniz {p} x hx y := by
    by_cases hp : p = 0
    · subst hp
      have hx₂ : x.snd = 0 := mem_trivSqZeroExtGrading_zero_iff.mp hx
      ext <;> simp [hx₂, mul_comm, add_comm]
    · ext <;> simp [fst_eq_zero_of_mem_trivSqZeroExtGrading hx hp, Units.smul_def]

/-- The augmentation `(r, m) ↦ φ r` of the differential graded algebra `R ⊕ M` of a derivation,
defined by an `S`-algebra map `φ : R → S`. -/
def trivSqZeroExtAugmentation (φ : R →ₐ[S] S) :
    DGAlgAugmentation D.isDGAlgebra_trivSqZeroExtDifferential where
  toGradedAlgHom :=
    { toAlgHom := φ.comp (fstHom S R M)
      map_mem := fun {p} {x} hx ↦ by
        rw [mem_trivialGrading_iff]
        by_cases hp : p = 0
        · exact Or.inl hp
        · exact Or.inr (by simp [fst_eq_zero_of_mem_trivSqZeroExtGrading hx hp]) }
  map_d' x := by simp

@[simp]
theorem trivSqZeroExtAugmentation_apply (φ : R →ₐ[S] S) (x : tsze R M) :
    D.trivSqZeroExtAugmentation φ x = φ x.fst :=
  (rfl)

/-- The unit morphism sends the class of a scalar `s` to the class of a cycle `z` exactly when
`algebraMap s - z` is a boundary `(0, D r)`. -/
private theorem cohomologyMap_unitHom_mk_eq_iff (s : S)
    (z : D.isDGAlgebra_trivSqZeroExtDifferential.cycles) :
    D.isDGAlgebra_trivSqZeroExtDifferential.unitHom.cohomologyMap
        (Ideal.Quotient.mk _ ⟨s, by simp⟩) = Ideal.Quotient.mk _ z ↔
      ∃ r : R, inr (D r) = inl (algebraMap S R s) - (z : tsze R M) := by
  rw [DGAlgHom.cohomologyMap_mk, Ideal.Quotient.eq, TwoSidedIdeal.mem_asIdeal,
    IsDGAlgebra.mem_boundaries]
  simp only [LinearMap.mem_range, trivSqZeroExtDifferential_apply, AddSubgroupClass.coe_sub,
    DGAlgHom.cyclesMap_apply_coe, IsDGAlgebra.unitHom_apply, algebraMap_eq_inl']
  exact ⟨fun ⟨y, hy⟩ ↦ ⟨y.fst, hy⟩, fun ⟨r, hr⟩ ↦ ⟨inl r, hr⟩⟩

/-- The unit `S → R ⊕ M` of the differential graded algebra of a derivation `D : R → M` is a
quasi-isomorphism exactly when `S → R` is injective, every `r` with `D r = 0` is a scalar, and `D`
is surjective: the cohomology of `R ⊕ M` is `ker D` in degree `0` and `coker D` in degree `1`. -/
theorem trivSqZeroExtUnitHom_cohomologyMap_bijective_iff :
    Function.Bijective D.isDGAlgebra_trivSqZeroExtDifferential.unitHom.cohomologyMap ↔
      Function.Injective (algebraMap S R) ∧ (∀ r, D r = 0 → ∃ s, algebraMap S R s = r) ∧
        Function.Surjective D := by
  set h := D.isDGAlgebra_trivSqZeroExtDifferential
  have h₀ := isDGAlgebra_trivialGrading S
  -- Every class of the ground ring is the class of a scalar.
  have hmk : ∀ c : h₀.Cohomology, ∃ s : S, Ideal.Quotient.mk _ ⟨s, by simp⟩ = c := fun c ↦ by
    obtain ⟨⟨s, hs⟩, rfl⟩ := Ideal.Quotient.mk_surjective c
    exact ⟨s, rfl⟩
  constructor
  · rintro ⟨hinj, hsurj⟩
    -- Every cycle is cohomologous to a scalar.
    have key : ∀ z : h.cycles,
        ∃ (s : S) (r : R), inr (D r) = inl (algebraMap S R s) - (z : tsze R M) := fun z ↦ by
      obtain ⟨c, hc⟩ := hsurj (Ideal.Quotient.mk _ z)
      obtain ⟨s, rfl⟩ := hmk c
      exact ⟨s, (D.cohomologyMap_unitHom_mk_eq_iff s z).mp hc⟩
    refine ⟨(injective_iff_map_eq_zero _).mpr fun s hs ↦ ?_, fun r hr ↦ ?_, fun m ↦ ?_⟩
    · have hzero := (D.cohomologyMap_unitHom_mk_eq_iff s 0).mpr ⟨0, by simp [hs]⟩
      rw [map_zero, ← map_zero h.unitHom.cohomologyMap] at hzero
      have := h₀.mem_boundaries.mp ((h₀.quotientMk_eq_zero_iff).mp (hinj hzero))
      simpa [eq_comm] using this
    · obtain ⟨s, r', hr'⟩ := key ⟨inl r, by simp [hr]⟩
      exact ⟨s, sub_eq_zero.mp (by simpa [eq_comm] using congrArg fst hr')⟩
    · obtain ⟨s, r', hr'⟩ := key ⟨inr m, by simp⟩
      exact ⟨-r', by simpa [neg_eq_iff_eq_neg] using congrArg snd hr'⟩
  · rintro ⟨hinj, hker, hsurj⟩
    refine ⟨(injective_iff_map_eq_zero _).mpr fun c hc ↦ ?_, fun c ↦ ?_⟩
    · obtain ⟨s, rfl⟩ := hmk c
      rw [← map_zero (Ideal.Quotient.mk h.boundaries.asIdeal),
        D.cohomologyMap_unitHom_mk_eq_iff] at hc
      obtain ⟨r, hr⟩ := hc
      have hs : algebraMap S R s = 0 := by simpa [eq_comm] using congrArg fst hr
      rw [h₀.quotientMk_eq_zero_iff, h₀.mem_boundaries]
      exact ⟨0, by simpa using (hinj (hs.trans (map_zero _).symm)).symm⟩
    · obtain ⟨z, rfl⟩ := Ideal.Quotient.mk_surjective c
      obtain ⟨s, hs⟩ := hker _ (by simpa using congrArg snd (h.mem_cycles.mp z.property))
      obtain ⟨r, hr⟩ := hsurj (z : tsze R M).snd
      refine ⟨_, (D.cohomologyMap_unitHom_mk_eq_iff s z).mpr ⟨-r, TrivSqZeroExt.ext ?_ ?_⟩⟩ <;>
        simp [hs, hr]

/-- An augmentation of the differential graded algebra `R ⊕ M` of a derivation `D : R → M` is a
quasi-isomorphism exactly when `S → R` is injective, every `r` with `D r = 0` is a scalar, and `D`
is surjective. -/
theorem trivSqZeroExtAugmentation_cohomologyMap_bijective_iff (φ : R →ₐ[S] S) :
    Function.Bijective (D.trivSqZeroExtAugmentation φ).cohomologyMap ↔
      Function.Injective (algebraMap S R) ∧ (∀ r, D r = 0 → ∃ s, algebraMap S R s = r) ∧
        Function.Surjective D :=
  (DGAlgAugmentation.cohomologyMap_bijective_iff _).trans
    D.trivSqZeroExtUnitHom_cohomologyMap_bijective_iff

end Derivation
