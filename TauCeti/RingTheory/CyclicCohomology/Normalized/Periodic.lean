/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.CyclicCohomology.Normalized.Basic
public import TauCeti.Algebra.Homology.ModuleCat.Basic
public import Mathlib.Data.ZMod.Defs
public import Mathlib.LinearAlgebra.DFinsupp
public import TauCeti.Data.DFinsupp.ExtendDomain

/-!
# The periodic `(b, B)` complex of normalized cochains

The normalized Hochschild cochains `Cⁿ` of a unital algebra form a mixed complex: the
Hochschild coboundary `b : Cⁿ → Cⁿ⁺¹` and Connes' operator `B : Cⁿ⁺¹ → Cⁿ` satisfy
`b² = 0`, `B² = 0` and `bB + Bb = 0`. The stabilized `(b, B)` bicomplex of this mixed complex
repeats the same columns in every even shift, and its direct-sum totalization is the
two-periodic complex

`⨁ₖ C²ᵏ ⇄ ⨁ₖ C²ᵏ⁺¹`

with differential `b + B` in both directions. Its elements have only finitely many nonzero
components. Its cohomology is periodic cyclic cohomology in the `(b, B)` description; this file
does not compare it with the direct limit of cyclic cohomology under `S`
(`TauCeti.periodicCyclicCohomology`).

The differential `b + B` is first defined on all finitely supported families `(φₙ)ₙ` of
normalized cochains (`TauCeti.normalizedMixedDifferential`); it squares to zero and changes the
parity of degrees. The families indexed by the degrees of parity `i : ZMod 2` form
`TauCeti.normalizedPeriodicCochains`, and these give a homological complex for the shape
`ComplexShape.up (ZMod 2)` of two-periodic complexes, whose homology is
`TauCeti.normalizedPeriodicCohomology`.

A cyclic normalized cochain `ψ` satisfies `Bψ = 0`, so placing it in its own degree is
compatible with the differential: `(b + B) ψ = b ψ`. Hence a normalized cyclic cocycle is a
periodic cocycle, and the coboundary of a normalized cyclic cochain is a periodic coboundary.
Up to a scalar in each degree, which is not chosen here, this is the homogeneous column map
from normalized cyclic cocycles to periodic cocycles.

For the ground ring `R` every normalized cochain of positive degree vanishes, so the complex
is concentrated in degree zero: the even periodic cohomology of `R` with coefficients in `M`
is `M`, and the odd one vanishes.

## Main definitions

* `TauCeti.normalizedMixedDifferential`: the differential `b + B` on finitely supported
  families of normalized cochains.
* `TauCeti.normalizedPeriodicCochains`: the families in the degrees of a given parity.
* `TauCeti.normalizedPeriodicDifferential`: the components of `b + B` between parities.
* `TauCeti.normalizedPeriodicCochainComplex`: the two-periodic direct-sum totalization of the
  stabilized `(b, B)` bicomplex.
* `TauCeti.normalizedPeriodicCohomology`: its cohomology.
* `TauCeti.normalizedPeriodicCocycles`, `TauCeti.normalizedPeriodicCohomology.mk`: the periodic
  cocycles of a given parity and their cohomology classes.
* `TauCeti.normalizedPeriodicCohomologySelfZeroEquiv`: the even periodic cohomology of the
  ground ring is the coefficient module.

## Main results

* `TauCeti.normalizedMixedDifferential_normalizedMixedDifferential`: `(b + B)² = 0`.
* `TauCeti.normalizedMixedDifferential_apply_zero`,
  `TauCeti.normalizedMixedDifferential_apply_succ`: the components of `(b + B) φ`.
* `TauCeti.normalizedMixedDifferential_single_of_mem_cyclicCochains`,
  `TauCeti.normalizedPeriodicDifferential_single_of_mem_cyclicCochains`: on a cyclic
  normalized cochain the differential is `b`.
* `TauCeti.single_mem_normalizedPeriodicCocycles_of_mem_cyclicCochains`: a normalized cyclic
  cocycle, placed in its own degree, is a periodic cocycle.
* `TauCeti.normalizedPeriodicCohomology.mk_surjective`,
  `TauCeti.normalizedPeriodicCohomology.mk_eq_zero_iff`: every class is the class of a cocycle,
  and the classes that vanish are those of the images of `b + B`.
* `TauCeti.isZero_normalizedPeriodicCohomology_self_one`: the odd periodic cohomology of the
  ground ring vanishes.

## References

* J.-L. Loday, *Cyclic Homology*, §§2.1, 2.5 and 5.1 (normalized mixed complexes, the
  `(b, B)` bicomplex and periodic cyclic cohomology).
* A. Connes, *Noncommutative Geometry*, Chapter III, §1.
-/

public section

namespace TauCeti

open CategoryTheory Limits

section Differential

variable (R A M : Type*) [Semiring R] [NonAssocSemiring A] [Module R A]
  [IsScalarTower R A A] [SMulCommClass R A A] [AddCommGroup M] [Module R M]
  [SMulCommClass R R M]

/-- The image of a single normalized `n`-cochain under `b + B`, as a family of cochains. -/
private def normalizedMixedDifferentialAux :
    ∀ n, normalizedHochschildCochains R A M n →ₗ[R] Π₀ k, normalizedHochschildCochains R A M k
  | 0 => (DFinsupp.lsingle 1).comp (normalizedHochschildCoboundary R A M 0)
  | n + 1 => (DFinsupp.lsingle (n + 2)).comp (normalizedHochschildCoboundary R A M (n + 1)) +
      (DFinsupp.lsingle n).comp (normalizedConnesB R A M n)

/-- The differential `b + B` of the normalized mixed complex, acting on finitely supported
families `(φₙ)ₙ` of normalized cochains: the degree-`n` component of the image is
`b φₙ₋₁ + B φₙ₊₁`, with no `b` term in degree zero. -/
def normalizedMixedDifferential :
    (Π₀ n, normalizedHochschildCochains R A M n) →ₗ[R]
      Π₀ n, normalizedHochschildCochains R A M n :=
  DFinsupp.lsum ℕ (normalizedMixedDifferentialAux R A M)

variable {R A M}

/-- On a degree-zero cochain the differential `b + B` is `b`. -/
@[simp]
theorem normalizedMixedDifferential_single_zero (φ : normalizedHochschildCochains R A M 0) :
    normalizedMixedDifferential R A M (DFinsupp.single 0 φ) =
      DFinsupp.single 1 (normalizedHochschildCoboundary R A M 0 φ) := by
  simp [normalizedMixedDifferential, normalizedMixedDifferentialAux]

/-- On a cochain of positive degree the differential `b + B` has a `b` and a `B` term. -/
@[simp]
theorem normalizedMixedDifferential_single_succ {n : ℕ}
    (φ : normalizedHochschildCochains R A M (n + 1)) :
    normalizedMixedDifferential R A M (DFinsupp.single (n + 1) φ) =
      DFinsupp.single (n + 2) (normalizedHochschildCoboundary R A M (n + 1) φ) +
        DFinsupp.single n (normalizedConnesB R A M n φ) := by
  simp [normalizedMixedDifferential, normalizedMixedDifferentialAux]

/-- The degree-zero component of `(b + B) φ` is `B φ₁`. -/
theorem normalizedMixedDifferential_apply_zero (φ : Π₀ n, normalizedHochschildCochains R A M n) :
    normalizedMixedDifferential R A M φ 0 = normalizedConnesB R A M 0 (φ 1) := by
  induction φ using DFinsupp.induction with
  | h0 => simp
  | ha m x φ _ _ ih =>
    rw [map_add, DFinsupp.add_apply, ih, DFinsupp.add_apply, map_add]
    congr 1
    rcases m with _ | _ | m
    · simp
    · simp
    · simp

/-- The degree-`n + 1` component of `(b + B) φ` is `b φₙ + B φₙ₊₂`. -/
theorem normalizedMixedDifferential_apply_succ (φ : Π₀ n, normalizedHochschildCochains R A M n)
    (n : ℕ) :
    normalizedMixedDifferential R A M φ (n + 1) =
      normalizedHochschildCoboundary R A M n (φ n) +
        normalizedConnesB R A M (n + 1) (φ (n + 2)) := by
  induction φ using DFinsupp.induction with
  | h0 => simp
  | ha m x φ _ _ ih =>
    rw [map_add, DFinsupp.add_apply, ih, DFinsupp.add_apply, DFinsupp.add_apply, map_add,
      map_add, add_add_add_comm]
    congr 1
    rcases m with _ | m
    · rcases eq_or_ne n 0 with rfl | hn
      · simp
      · simp [hn, Ne.symm hn]
    · rcases eq_or_ne n (m + 1) with rfl | h₁
      · simp [show m ≠ m + 1 + 1 by omega]
      rcases eq_or_ne m (n + 1) with rfl | h₂
      · simp [show n + 1 + 1 ≠ n by omega]
      simp [h₂, Ne.symm h₁]

/-- On a cyclic normalized cochain, placed in its own degree, the differential `b + B` is `b`:
the `B` term vanishes because `B` kills cyclic cochains. -/
theorem normalizedMixedDifferential_single_of_mem_cyclicCochains {n : ℕ}
    {ψ : normalizedHochschildCochains R A M n}
    (hψ : (ψ : MultilinearMap R (fun _ : Fin (n + 1) ↦ A) M) ∈ cyclicCochains R A M n) :
    normalizedMixedDifferential R A M (DFinsupp.single n ψ) =
      DFinsupp.single (n + 1) (normalizedHochschildCoboundary R A M n ψ) := by
  cases n with
  | zero => simp
  | succ n => simp [normalizedConnesB_eq_zero_of_mem_cyclicCochains hψ]

/-- A cyclic normalized cocycle, placed in its own degree, is a cocycle for `b + B`. -/
theorem normalizedMixedDifferential_single_eq_zero_of_mem_cyclicCochains {n : ℕ}
    {ψ : normalizedHochschildCochains R A M n}
    (hψ : (ψ : MultilinearMap R (fun _ : Fin (n + 1) ↦ A) M) ∈ cyclicCochains R A M n)
    (hb : hochschildCoboundary R A M n ψ = 0) :
    normalizedMixedDifferential R A M (DFinsupp.single n ψ) = 0 := by
  rw [normalizedMixedDifferential_single_of_mem_cyclicCochains hψ,
    normalizedHochschildCoboundary_eq_zero_iff.2 hb, DFinsupp.single_zero]

end Differential

section Square

variable {R A M : Type*} [Semiring R] [Semiring A] [Module R A]
  [IsScalarTower R A A] [SMulCommClass R A A] [AddCommGroup M] [Module R M]
  [SMulCommClass R R M]

/-- The differential `b + B` squares to zero: this combines `b² = 0`, `B² = 0` and
`bB + Bb = 0`. -/
@[simp]
theorem normalizedMixedDifferential_normalizedMixedDifferential
    (φ : Π₀ n, normalizedHochschildCochains R A M n) :
    normalizedMixedDifferential R A M (normalizedMixedDifferential R A M φ) = 0 := by
  ext n : 1
  rcases n with _ | _ | n <;>
    simp only [normalizedMixedDifferential_apply_zero, normalizedMixedDifferential_apply_succ,
      map_add, normalizedConnesB_normalizedConnesB,
      normalizedConnesB_normalizedHochschildCoboundary_zero,
      normalizedHochschildCoboundary_normalizedHochschildCoboundary, DFinsupp.coe_zero,
      Pi.zero_apply, add_zero, zero_add] <;>
    exact normalizedHochschildCoboundary_normalizedConnesB_add _

end Square

section Parity

variable (R A M : Type*) [Semiring R] [AddCommMonoid A] [One A] [Module R A]
  [AddCommMonoid M] [Module R M] [SMulCommClass R R M]

/-- The finitely supported families of normalized cochains in the degrees of parity `i`: the
degree-`i` term of the direct-sum totalization of the stabilized `(b, B)` bicomplex. -/
abbrev normalizedPeriodicCochains (i : ZMod 2) : Type _ :=
  Π₀ n : {n : ℕ // (n : ZMod 2) = i}, normalizedHochschildCochains R A M n

/-- A family of normalized cochains of parity `i`, regarded as a family in all degrees by
extending it by zero. -/
def normalizedPeriodicCochainsι (i : ZMod 2) :
    normalizedPeriodicCochains R A M i →ₗ[R] Π₀ n, normalizedHochschildCochains R A M n :=
  DFinsupp.extendDomainLinearMap R (fun n : ℕ ↦ normalizedHochschildCochains R A M n)
    (fun n : ℕ ↦ (n : ZMod 2) = i)

variable {R A M} {i : ZMod 2}

/-- The inclusion of the parity-`i` families is the extension by zero. -/
theorem normalizedPeriodicCochainsι_apply (φ : normalizedPeriodicCochains R A M i) :
    normalizedPeriodicCochainsι R A M i φ =
      DFinsupp.extendDomain (β := fun n : ℕ ↦ normalizedHochschildCochains R A M n) φ := by
  rw [normalizedPeriodicCochainsι, DFinsupp.extendDomainLinearMap_apply]

/-- In degrees of the other parity, the extension by zero vanishes. -/
@[simp]
theorem normalizedPeriodicCochainsι_apply_of_ne (φ : normalizedPeriodicCochains R A M i)
    {m : ℕ} (hm : (m : ZMod 2) ≠ i) : normalizedPeriodicCochainsι R A M i φ m = 0 := by
  rw [normalizedPeriodicCochainsι_apply]
  exact DFinsupp.extendDomain_apply_of_not (β := fun n : ℕ ↦ normalizedHochschildCochains R A M n)
    (p := fun n : ℕ ↦ (n : ZMod 2) = i) φ hm

/-- In degrees of parity `i`, the extension by zero is the given family. -/
@[simp]
theorem normalizedPeriodicCochainsι_apply_of_eq (φ : normalizedPeriodicCochains R A M i)
    {m : ℕ} (hm : (m : ZMod 2) = i) : normalizedPeriodicCochainsι R A M i φ m = φ ⟨m, hm⟩ := by
  rw [normalizedPeriodicCochainsι_apply]
  exact DFinsupp.extendDomain_apply_subtype (β := fun n : ℕ ↦ normalizedHochschildCochains R A M n)
    (p := fun n : ℕ ↦ (n : ZMod 2) = i) φ ⟨m, hm⟩

end Parity

section ParityDifferential

variable {R A M : Type*} [Semiring R] [NonAssocSemiring A] [Module R A]
  [IsScalarTower R A A] [SMulCommClass R A A] [AddCommGroup M] [Module R M]
  [SMulCommClass R R M]

/-- The differential `b + B` changes the parity of degrees. -/
@[simp]
theorem normalizedMixedDifferential_normalizedPeriodicCochainsι_apply_of_ne {i : ZMod 2}
    (φ : normalizedPeriodicCochains R A M i) {m : ℕ} (hm : (m : ZMod 2) ≠ i + 1) :
    normalizedMixedDifferential R A M (normalizedPeriodicCochainsι R A M i φ) m = 0 := by
  have key₀ : ∀ b : ZMod 2, 0 ≠ b + 1 → 1 ≠ b := by decide
  have key : ∀ a b : ZMod 2, a + 1 ≠ b + 1 → a ≠ b ∧ a + 2 ≠ b := by decide
  rcases m with _ | n
  · rw [normalizedMixedDifferential_apply_zero, normalizedPeriodicCochainsι_apply_of_ne _
      (by simpa using key₀ i (by simpa using hm)), map_zero]
  · have h := key n i (by simpa using hm)
    rw [normalizedMixedDifferential_apply_succ, normalizedPeriodicCochainsι_apply_of_ne _ h.1,
      normalizedPeriodicCochainsι_apply_of_ne _ (by simpa using h.2), map_zero, map_zero,
      add_zero]

variable (R A M) in
/-- The component `b + B` of the periodic complex from parity `i` to parity `j`. It vanishes
unless `j = i + 1`. -/
def normalizedPeriodicDifferential (i j : ZMod 2) :
    normalizedPeriodicCochains R A M i →ₗ[R] normalizedPeriodicCochains R A M j :=
  DFinsupp.subtypeDomainLinearMap R (fun n : ℕ ↦ normalizedHochschildCochains R A M n)
      (fun n : ℕ ↦ (n : ZMod 2) = j) ∘ₗ normalizedMixedDifferential R A M ∘ₗ
    normalizedPeriodicCochainsι R A M i

/-- The periodic differential is `b + B`, restricted to the degrees of the target parity. -/
theorem normalizedPeriodicDifferential_apply (i j : ZMod 2)
    (φ : normalizedPeriodicCochains R A M i) :
    normalizedPeriodicDifferential R A M i j φ =
      DFinsupp.subtypeDomain (fun n : ℕ ↦ (n : ZMod 2) = j)
        (normalizedMixedDifferential R A M (normalizedPeriodicCochainsι R A M i φ)) := (rfl)

/-- The degree-zero component of the periodic differential is `B φ₁`. -/
theorem normalizedPeriodicDifferential_apply_zero {i : ZMod 2}
    (φ : normalizedPeriodicCochains R A M i) (h : ((1 : ℕ) : ZMod 2) = i) :
    normalizedPeriodicDifferential R A M i (i + 1) φ ⟨0, by rw [← h]; decide⟩ =
      normalizedConnesB R A M 0 (φ ⟨1, h⟩) := by
  rw [normalizedPeriodicDifferential_apply, DFinsupp.subtypeDomain_apply,
    normalizedMixedDifferential_apply_zero, normalizedPeriodicCochainsι_apply_of_eq _ h]

/-- The degree-`n + 1` component of the periodic differential is `b φₙ + B φₙ₊₂`. -/
theorem normalizedPeriodicDifferential_apply_succ {i : ZMod 2}
    (φ : normalizedPeriodicCochains R A M i) (n : ℕ) (h : (n : ZMod 2) = i) :
    normalizedPeriodicDifferential R A M i (i + 1) φ ⟨n + 1, by rw [Nat.cast_succ, h]⟩ =
      normalizedHochschildCoboundary R A M n (φ ⟨n, h⟩) +
        normalizedConnesB R A M (n + 1)
          (φ ⟨n + 2, by rw [← h, Nat.cast_add, add_eq_left]; decide⟩) := by
  rw [normalizedPeriodicDifferential_apply, DFinsupp.subtypeDomain_apply,
    normalizedMixedDifferential_apply_succ, normalizedPeriodicCochainsι_apply_of_eq _ h,
    normalizedPeriodicCochainsι_apply_of_eq]

/-- Extending the periodic differential by zero gives `b + B` of the extension by zero. -/
@[simp]
theorem normalizedPeriodicCochainsι_normalizedPeriodicDifferential (i : ZMod 2)
    (φ : normalizedPeriodicCochains R A M i) :
    normalizedPeriodicCochainsι R A M (i + 1) (normalizedPeriodicDifferential R A M i (i + 1) φ) =
      normalizedMixedDifferential R A M (normalizedPeriodicCochainsι R A M i φ) := by
  rw [normalizedPeriodicCochainsι_apply, normalizedPeriodicDifferential_apply]
  exact DFinsupp.extendDomain_subtypeDomain fun _ hm ↦
    normalizedMixedDifferential_normalizedPeriodicCochainsι_apply_of_ne φ hm

/-- The periodic differential vanishes between degrees of equal parity. -/
theorem normalizedPeriodicDifferential_eq_zero {i j : ZMod 2} (h : i + 1 ≠ j) :
    normalizedPeriodicDifferential R A M i j = 0 := by
  refine LinearMap.ext fun φ ↦ DFinsupp.ext fun ⟨m, hm⟩ ↦ ?_
  rw [normalizedPeriodicDifferential_apply, DFinsupp.subtypeDomain_apply, LinearMap.zero_apply,
    DFinsupp.zero_apply]
  exact normalizedMixedDifferential_normalizedPeriodicCochainsι_apply_of_ne φ
    (by rw [hm]; exact Ne.symm h)

/-- On a cyclic normalized `n`-cochain the periodic differential is `b`. -/
theorem normalizedPeriodicDifferential_single_of_mem_cyclicCochains {n : ℕ}
    {ψ : normalizedHochschildCochains R A M n}
    (hψ : (ψ : MultilinearMap R (fun _ : Fin (n + 1) ↦ A) M) ∈ cyclicCochains R A M n) :
    normalizedPeriodicDifferential R A M n (n + 1) (DFinsupp.single ⟨n, rfl⟩ ψ) =
      DFinsupp.single ⟨n + 1, Nat.cast_succ n⟩ (normalizedHochschildCoboundary R A M n ψ) := by
  rw [normalizedPeriodicDifferential_apply, normalizedPeriodicCochainsι_apply,
    DFinsupp.extendDomain_single, normalizedMixedDifferential_single_of_mem_cyclicCochains hψ]
  ext ⟨m, hm⟩ : 1
  rw [DFinsupp.subtypeDomain_apply]
  rcases eq_or_ne m (n + 1) with rfl | h
  · simp
  · rw [DFinsupp.single_eq_of_ne h,
      DFinsupp.single_eq_of_ne fun h' ↦ h (congrArg Subtype.val h')]

end ParityDifferential

section ParitySquare

variable (R A M : Type*) [Semiring R] [Semiring A] [Module R A]
  [IsScalarTower R A A] [SMulCommClass R A A] [AddCommGroup M] [Module R M]
  [SMulCommClass R R M]

/-- The periodic differential squares to zero. -/
@[simp]
theorem normalizedPeriodicDifferential_normalizedPeriodicDifferential (i : ZMod 2)
    (φ : normalizedPeriodicCochains R A M i) :
    normalizedPeriodicDifferential R A M (i + 1) (i + 1 + 1)
      (normalizedPeriodicDifferential R A M i (i + 1) φ) = 0 := by
  rw [normalizedPeriodicDifferential_apply,
    normalizedPeriodicCochainsι_normalizedPeriodicDifferential,
    normalizedMixedDifferential_normalizedMixedDifferential, DFinsupp.subtypeDomain_zero]

end ParitySquare

section Complex

variable (R A M : Type*) [CommRing R] [Semiring A] [Module R A]
  [IsScalarTower R A A] [SMulCommClass R A A] [AddCommGroup M] [Module R M]

/-- The `ℤ/2`-graded periodic complex of normalized cochains: the direct-sum totalization of
the stabilized `(b, B)` bicomplex, with differential `b + B` in both directions. -/
def normalizedPeriodicCochainComplex :
    HomologicalComplex (ModuleCat R) (ComplexShape.up (ZMod 2)) where
  X i := ModuleCat.of R (normalizedPeriodicCochains R A M i)
  d i j := ModuleCat.ofHom (normalizedPeriodicDifferential R A M i j)
  shape i j h := by simp [normalizedPeriodicDifferential_eq_zero h]
  d_comp_d' i j k hij hjk := by
    subst hij hjk
    refine ModuleCat.hom_ext (LinearMap.ext fun φ ↦ ?_)
    exact normalizedPeriodicDifferential_normalizedPeriodicDifferential R A M i φ

/-- Periodic cyclic cohomology in the `(b, B)` description: the cohomology of the direct-sum
totalization of the stabilized `(b, B)` bicomplex of normalized cochains, in parity `i`. -/
noncomputable abbrev normalizedPeriodicCohomology (i : ZMod 2) : ModuleCat R :=
  (normalizedPeriodicCochainComplex R A M).homology i

/-- The parity-`i` term of the periodic complex is the module of families of parity `i`. -/
def normalizedPeriodicCochainComplexXIso (i : ZMod 2) :
    (normalizedPeriodicCochainComplex R A M).X i ≅
      ModuleCat.of R (normalizedPeriodicCochains R A M i) := Iso.refl _

/-- The periodic complex has the periodic differential `b + B`. -/
@[reassoc, elementwise]
theorem normalizedPeriodicCochainComplex_d (i j : ZMod 2) :
    (normalizedPeriodicCochainComplex R A M).d i j ≫
        (normalizedPeriodicCochainComplexXIso R A M j).hom =
      (normalizedPeriodicCochainComplexXIso R A M i).hom ≫
        ModuleCat.ofHom (normalizedPeriodicDifferential R A M i j) := by
  simp [normalizedPeriodicCochainComplex, normalizedPeriodicCochainComplexXIso]

end Complex

section Cocycles

variable (R A M : Type*) [CommRing R] [Semiring A] [Module R A]
  [IsScalarTower R A A] [SMulCommClass R A A] [AddCommGroup M] [Module R M]

/-- The periodic cocycles of parity `i`: the families of parity `i` killed by `b + B`. -/
def normalizedPeriodicCocycles (i : ZMod 2) : Submodule R (normalizedPeriodicCochains R A M i) :=
  LinearMap.ker (normalizedPeriodicDifferential R A M i (i + 1))

variable {R A M}

/-- A family of parity `i` is a periodic cocycle exactly when `b + B` kills it. -/
@[simp]
theorem mem_normalizedPeriodicCocycles_iff {i : ZMod 2}
    {φ : normalizedPeriodicCochains R A M i} :
    φ ∈ normalizedPeriodicCocycles R A M i ↔
      normalizedPeriodicDifferential R A M i (i + 1) φ = 0 :=
  LinearMap.mem_ker

/-- A family of parity `i` is a periodic cocycle exactly when the differential of the periodic
complex kills it. -/
theorem mem_normalizedPeriodicCocycles_iff_complex (i : ZMod 2)
    (φ : normalizedPeriodicCochains R A M i) :
    φ ∈ normalizedPeriodicCocycles R A M i ↔
      (normalizedPeriodicCochainComplex R A M).d i (i + 1)
        ((normalizedPeriodicCochainComplexXIso R A M i).inv φ) = 0 := by
  rw [mem_normalizedPeriodicCocycles_iff,
    ← (normalizedPeriodicCochainComplexXIso R A M (i + 1)).toLinearEquiv.map_eq_zero_iff,
    Iso.toLinearEquiv_apply, normalizedPeriodicCochainComplex_d_apply, Iso.inv_hom_id_apply]

/-- A cyclic normalized `n`-cocycle, placed in its own degree, is a periodic cocycle. -/
theorem single_mem_normalizedPeriodicCocycles_of_mem_cyclicCochains {n : ℕ}
    {ψ : normalizedHochschildCochains R A M n}
    (hψ : (ψ : MultilinearMap R (fun _ : Fin (n + 1) ↦ A) M) ∈ cyclicCochains R A M n)
    (hb : hochschildCoboundary R A M n ψ = 0) :
    DFinsupp.single ⟨n, rfl⟩ ψ ∈ normalizedPeriodicCocycles R A M n := by
  rw [mem_normalizedPeriodicCocycles_iff,
    normalizedPeriodicDifferential_single_of_mem_cyclicCochains hψ,
    normalizedHochschildCoboundary_eq_zero_iff.2 hb, DFinsupp.single_zero]

/-- The periodic cocycles form an additive group. Instance search does not find
`Submodule.addCommGroup` through the dependent family of cochain modules, so it is given here. -/
instance (i : ZMod 2) : AddCommGroup (normalizedPeriodicCocycles R A M i) :=
  @Submodule.addCommGroup R (normalizedPeriodicCochains R A M i) _ _ _ _

namespace normalizedPeriodicCohomology

variable (R A M) in
/-- The periodic cohomology class of a periodic cocycle. -/
noncomputable def mk (i : ZMod 2) :
    normalizedPeriodicCocycles R A M i →ₗ[R] normalizedPeriodicCohomology R A M i :=
  (normalizedPeriodicCochainComplex R A M).moduleCatHomologyClass (ComplexShape.next_eq' _ rfl)
    ((normalizedPeriodicCochainComplexXIso R A M i).inv.hom ∘ₗ
      (normalizedPeriodicCocycles R A M i).subtype)
    fun φ : normalizedPeriodicCocycles R A M i ↦
      (mem_normalizedPeriodicCocycles_iff_complex i φ.1).1 φ.2

/-- The class of a periodic cocycle `φ` is the homology class of any cycle of the periodic
complex whose underlying family is `φ`. -/
theorem mk_eq_homologyπ {i : ZMod 2} (φ : normalizedPeriodicCocycles R A M i)
    (z : (normalizedPeriodicCochainComplex R A M).cycles i)
    (hz : (normalizedPeriodicCochainComplexXIso R A M i).hom
      ((normalizedPeriodicCochainComplex R A M).iCycles i z) = φ) :
    mk R A M i φ = (normalizedPeriodicCochainComplex R A M).homologyπ i z := by
  refine ((normalizedPeriodicCochainComplex R A M).moduleCatHomologyClass_apply _ _ _ φ).trans ?_
  congr 1
  apply (normalizedPeriodicCochainComplex R A M).moduleCat_iCycles_injective i
  refine ((normalizedPeriodicCochainComplex R A M).iCycles_moduleCatCyclesMk _ _ _ _ _).trans ?_
  rw [LinearMap.comp_apply, Submodule.subtype_apply, ← hz]
  exact Iso.hom_inv_id_apply _ _

/-- Every periodic cohomology class is the class of a periodic cocycle. -/
theorem mk_surjective (i : ZMod 2) : Function.Surjective (mk R A M i) :=
  (normalizedPeriodicCochainComplex R A M).moduleCatHomologyClass_surjective _ _ _
    fun x hx ↦ ⟨⟨(normalizedPeriodicCochainComplexXIso R A M i).hom x,
      (mem_normalizedPeriodicCocycles_iff_complex i _).2 hx⟩, rfl⟩

/-- A periodic cocycle has zero class exactly when it is the image under `b + B` of a family of
the other parity. -/
theorem mk_eq_zero_iff {i : ZMod 2} (φ : normalizedPeriodicCocycles R A M i) :
    mk R A M i φ = 0 ↔
      ∃ ψ : normalizedPeriodicCochains R A M (i + 1),
        normalizedPeriodicDifferential R A M (i + 1) i ψ = φ :=
  (normalizedPeriodicCochainComplex R A M).moduleCatHomologyClass_eq_zero_iff _ _ _
    (ComplexShape.prev_eq' _
      (show i + 1 + 1 = i by rw [add_assoc, add_eq_left]; decide)) φ

end normalizedPeriodicCohomology

end Cocycles

section GroundRing

variable (R M : Type*) [CommSemiring R] [AddCommMonoid M] [Module R M]

/-- On the ground ring there are no nonzero periodic cochains of odd parity. -/
instance : Subsingleton (normalizedPeriodicCochains R R M 1) where
  allEq φ ψ := DFinsupp.ext fun
    | ⟨0, h⟩ => absurd h (by decide)
    | ⟨_ + 1, _⟩ => Subsingleton.elim _ _

/-- On the ground ring a periodic cochain of even parity is its degree-zero cochain, which is
the product cochain of its value at `1`. -/
noncomputable def normalizedPeriodicCochainsSelfZeroEquiv :
    normalizedPeriodicCochains R R M 0 ≃ₗ[R] M where
  toFun φ := (φ ⟨0, Nat.cast_zero⟩ : MultilinearMap R (fun _ : Fin 1 ↦ R) M) fun _ ↦ 1
  map_add' φ ψ := by simp
  map_smul' r φ := by simp
  invFun m := DFinsupp.single ⟨0, Nat.cast_zero⟩
    ⟨MultilinearMap.mkPiRing R (Fin 1) m, by simp [normalizedHochschildCochains_zero]⟩
  left_inv φ := by
    ext ⟨_ | n, hn⟩ : 1
    · exact Subtype.ext (MultilinearMap.mkPiRing_apply_one_eq_self _)
    · exact Subsingleton.elim _ _
  right_inv m := by simp

/-- The isomorphism with `M` evaluates the degree-zero cochain at `1`. -/
@[simp]
theorem normalizedPeriodicCochainsSelfZeroEquiv_apply (φ : normalizedPeriodicCochains R R M 0) :
    normalizedPeriodicCochainsSelfZeroEquiv R M φ =
      (φ ⟨0, Nat.cast_zero⟩ : MultilinearMap R (fun _ : Fin 1 ↦ R) M) fun _ ↦ 1 := (rfl)

end GroundRing

section GroundRingCohomology

variable (R M : Type*) [CommRing R] [AddCommGroup M] [Module R M]

/-- On the ground ring the periodic complex vanishes in odd parity. -/
theorem isZero_normalizedPeriodicCochainComplex_self_X_one :
    IsZero ((normalizedPeriodicCochainComplex R R M).X 1) :=
  (ModuleCat.isZero_of_subsingleton (ModuleCat.of R (normalizedPeriodicCochains R R M 1))).of_iso
    (normalizedPeriodicCochainComplexXIso R R M 1)

/-- The odd periodic cohomology of the ground ring vanishes. -/
theorem isZero_normalizedPeriodicCohomology_self_one :
    IsZero (normalizedPeriodicCohomology R R M 1) :=
  ShortComplex.isZero_homology_of_isZero_X₂ _
    (isZero_normalizedPeriodicCochainComplex_self_X_one R M)

/-- The even periodic cohomology of the ground ring is the coefficient module: the complex is
concentrated in degree zero, where every cochain is the product cochain of its value at `1`. -/
noncomputable def normalizedPeriodicCohomologySelfZeroEquiv :
    normalizedPeriodicCohomology R R M 0 ≃ₗ[R] M :=
  (((normalizedPeriodicCochainComplex R R M).isoHomologyπ 1 0
      (ComplexShape.prev_eq' _ (show (1 : ZMod 2) + 1 = 0 from rfl))
      ((isZero_normalizedPeriodicCochainComplex_self_X_one R M).eq_of_src _ _)).symm ≪≫
    (normalizedPeriodicCochainComplex R R M).iCyclesIso 0 1
      (ComplexShape.next_eq' _ (show (0 : ZMod 2) + 1 = 1 from rfl))
      ((isZero_normalizedPeriodicCochainComplex_self_X_one R M).eq_of_tgt _ _) ≪≫
    normalizedPeriodicCochainComplexXIso R R M 0).toLinearEquiv ≪≫ₗ
    normalizedPeriodicCochainsSelfZeroEquiv R M

/-- The class of an even periodic cocycle of the ground ring corresponds to the value at `1` of
its degree-zero cochain. -/
@[simp]
theorem normalizedPeriodicCohomologySelfZeroEquiv_homologyπ
    (x : (normalizedPeriodicCochainComplex R R M).cycles 0) :
    normalizedPeriodicCohomologySelfZeroEquiv R M
        ((normalizedPeriodicCochainComplex R R M).homologyπ 0 x) =
      normalizedPeriodicCochainsSelfZeroEquiv R M
        ((normalizedPeriodicCochainComplexXIso R R M 0).hom
          ((normalizedPeriodicCochainComplex R R M).iCycles 0 x)) := by
  -- The isomorphism `cycles ≅ homology` inverts `homologyπ` in degree zero.
  rw [normalizedPeriodicCohomologySelfZeroEquiv, LinearEquiv.trans_apply,
    Iso.toLinearEquiv_apply, ← ConcreteCategory.comp_apply]
  simp

end GroundRingCohomology

end TauCeti
