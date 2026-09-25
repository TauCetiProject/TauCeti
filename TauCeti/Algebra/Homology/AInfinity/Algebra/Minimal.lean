/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.AInfinity.Algebra.Hom.Cohomology

/-!
# Minimal A∞ algebras

An A∞ algebra is minimal when its unary operation vanishes. Every element is then a cycle and
there are no nonzero boundaries, giving a linear equivalence with its cohomology. Between minimal
algebras, a morphism is a quasi-isomorphism exactly when its linear part is bijective.

## Main definitions

* `TauCeti.AInfinityAlgebra.IsMinimal`: the unary operation vanishes.
* `TauCeti.AInfinityAlgebra.IsMinimal.cohomologyEquiv`: identification with cohomology.

## Main results

* `TauCeti.AInfinityAlgebra.isMinimal_iff_cycles_eq_top` and
  `TauCeti.AInfinityAlgebra.isMinimal_iff_boundaries_eq_bot`: minimality in terms of cycles and
  boundaries.
* `TauCeti.IsNonUnitalDGAlgebra.isMinimal_toAInfinityAlgebra_iff`: the `A∞` algebra of a DG
  algebra is minimal exactly when the differential vanishes.
* `TauCeti.AInfinityAlgebra.isMinimal_cohomologyAInfinityAlgebra`: the cohomology `A∞` algebra is
  minimal.
* `TauCeti.AInfinityHom.isQuasiIso_iff_linearPart_bijective`: between minimal algebras, a
  quasi-isomorphism has bijective linear part.

## References

* B. Keller, *Introduction to A-infinity algebras and modules*, Sections 3.3 and 3.4.
* T. Kadeishvili, *The algebraic structure in the homology of an `A(∞)`-algebra*.
-/

public section

namespace TauCeti

universe uR uA uB

variable {R : Type uR} {A : Type uA} {B : Type uB} [CommRing R]
  [AddCommGroup A] [Module R A] [AddCommGroup B] [Module R B]

namespace AInfinityAlgebra

/-! ### Minimal `A∞` algebras -/

/-- An `A∞` algebra is **minimal** when its unary operation `m₁` vanishes. -/
def IsMinimal (𝒜 : AInfinityAlgebra R A) : Prop :=
  𝒜.differential = 0

/-- An `A∞` algebra is minimal exactly when its differential vanishes. -/
theorem isMinimal_def (𝒜 : AInfinityAlgebra R A) : 𝒜.IsMinimal ↔ 𝒜.differential = 0 := Iff.rfl

/-- An `A∞` algebra is minimal exactly when `m₁` vanishes on every input. -/
theorem isMinimal_iff_m_one_eq_zero (𝒜 : AInfinityAlgebra R A) :
    𝒜.IsMinimal ↔ ∀ x : A, 𝒜.m 1 ![x] = 0 := by
  simp only [isMinimal_def, LinearMap.ext_iff, differential_apply, LinearMap.zero_apply]

/-- An `A∞` algebra is minimal exactly when every element is a cycle. -/
theorem isMinimal_iff_cycles_eq_top (𝒜 : AInfinityAlgebra R A) :
    𝒜.IsMinimal ↔ 𝒜.cycles = ⊤ := by
  have hcycles : 𝒜.cycles = LinearMap.ker 𝒜.differential := by
    ext x
    rw [mem_cycles, LinearMap.mem_ker, differential_apply]
  rw [isMinimal_def]
  rw [hcycles, LinearMap.ker_eq_top]

/-- An `A∞` algebra is minimal exactly when zero is its only boundary. -/
theorem isMinimal_iff_boundaries_eq_bot (𝒜 : AInfinityAlgebra R A) :
    𝒜.IsMinimal ↔ 𝒜.boundaries = ⊥ := by
  have hboundaries : 𝒜.boundaries = LinearMap.range 𝒜.differential := by
    ext x
    rw [mem_boundaries, LinearMap.mem_range]
    simp only [differential_apply]
  rw [isMinimal_def]
  rw [hboundaries, LinearMap.range_eq_bot]

namespace IsMinimal

variable {𝒜 : AInfinityAlgebra R A}

/-- The unary operation of a minimal `A∞` algebra vanishes. -/
@[simp]
theorem m_one (h : 𝒜.IsMinimal) (x : Fin 1 → A) : 𝒜.m 1 x = 0 := by
  obtain ⟨y, rfl⟩ : ∃ y, x = ![y] := ⟨x 0, funext fun i ↦ by fin_cases i; rfl⟩
  exact (isMinimal_iff_m_one_eq_zero 𝒜).1 h y

/-- Every element of a minimal `A∞` algebra is a cycle. -/
theorem mem_cycles (h : 𝒜.IsMinimal) (x : A) : x ∈ 𝒜.cycles := by
  rw [AInfinityAlgebra.mem_cycles, h.m_one]

/-- In a minimal `A∞` algebra, the boundaries inside the cycles are trivial. -/
theorem boundariesInCycles_eq_bot (h : 𝒜.IsMinimal) : 𝒜.boundariesInCycles = ⊥ := by
  rw [Submodule.eq_bot_iff]
  intro x hx
  rw [mem_boundariesInCycles, (isMinimal_iff_boundaries_eq_bot 𝒜).1 h,
    Submodule.mem_bot] at hx
  exact Subtype.ext hx

/-- A minimal `A∞` algebra is linearly equivalent to its cohomology: every element is a cycle,
and no nonzero element is a boundary. -/
noncomputable def cohomologyEquiv (h : 𝒜.IsMinimal) : A ≃ₗ[R] 𝒜.Cohomology :=
  𝒜.cohomologyEquivOfCyclesEqTopOfBoundariesInCyclesEqBot
    ((isMinimal_iff_cycles_eq_top 𝒜).1 h) h.boundariesInCycles_eq_bot

/-- The identification of a minimal algebra with its cohomology sends an element to its class. -/
@[simp]
theorem cohomologyEquiv_apply (h : 𝒜.IsMinimal) (x : A) :
    h.cohomologyEquiv x = 𝒜.cohomologyClass (h.mem_cycles x) := by
  exact 𝒜.cohomologyEquivOfCyclesEqTopOfBoundariesInCyclesEqBot_apply
    ((isMinimal_iff_cycles_eq_top 𝒜).1 h) h.boundariesInCycles_eq_bot x (h.mem_cycles x)

/-- The identification of a minimal algebra with its cohomology carries `m₂` to the cohomology
product. -/
theorem cohomologyEquiv_m_two (h : 𝒜.IsMinimal) (x y : A) :
    h.cohomologyEquiv (𝒜.m 2 ![x, y]) = h.cohomologyEquiv x * h.cohomologyEquiv y := by
  simp only [cohomologyEquiv_apply, cohomology_mul_eq_cohomologyMul,
    cohomologyMul_cohomologyClass]

/-- The identification of a minimal algebra with its cohomology preserves degrees. -/
theorem isHomogeneous_cohomologyEquiv (h : 𝒜.IsMinimal) :
    LinearMap.IsHomogeneous h.cohomologyEquiv.toLinearMap 𝒜.grading.piece
      𝒜.cohomologyGrading.piece 0 := by
  rw [LinearMap.isHomogeneous_def]
  intro p x hx
  rw [add_zero, LinearEquiv.coe_coe, cohomologyEquiv_apply]
  exact 𝒜.cohomologyClass_mem_cohomologyGrading_piece _ hx

end IsMinimal

end AInfinityAlgebra

/-- The `A∞` algebra of a nonunital DG algebra is minimal exactly when the differential
vanishes. -/
theorem IsNonUnitalDGAlgebra.isMinimal_toAInfinityAlgebra_iff {A : Type uA} [NonUnitalRing A]
    [Module R A] [IsScalarTower R A A] [SMulCommClass R A A] {𝒜 : ℤ → Submodule R A}
    [SetLike.GradedMul 𝒜] [DirectSum.Decomposition 𝒜] {d : A →ₗ[R] A}
    (h : IsNonUnitalDGAlgebra 𝒜 d) : h.toAInfinityAlgebra.IsMinimal ↔ d = 0 := by
  rw [AInfinityAlgebra.isMinimal_def, toAInfinityAlgebra_differential]

namespace AInfinityAlgebra

/-- The cohomology `A∞` algebra is minimal. -/
theorem isMinimal_cohomologyAInfinityAlgebra (𝒜 : AInfinityAlgebra R A) :
    𝒜.cohomologyAInfinityAlgebra.IsMinimal :=
  (isMinimal_iff_m_one_eq_zero _).2 fun _ ↦ 𝒜.cohomologyAInfinityAlgebra_m_one_apply _

end AInfinityAlgebra

namespace AInfinityHom

variable {AA : AInfinityAlgebra R A} {BB : AInfinityAlgebra R B}

/-- Between minimal algebras, the map induced on cohomology is the linear part, transported along
the identifications of the algebras with their cohomology. -/
theorem cohomologyMap_cohomologyEquiv (hA : AA.IsMinimal) (hB : BB.IsMinimal)
    (f : AInfinityHom AA BB) (x : A) :
    f.cohomologyMap (hA.cohomologyEquiv x) = hB.cohomologyEquiv (f.linearPart x) := by
  simp only [AInfinityAlgebra.IsMinimal.cohomologyEquiv_apply, cohomologyMap_cohomologyClass]

/-- An `A∞` morphism between minimal algebras is a quasi-isomorphism exactly when its linear part
is bijective. -/
theorem isQuasiIso_iff_linearPart_bijective (hA : AA.IsMinimal) (hB : BB.IsMinimal)
    (f : AInfinityHom AA BB) :
    f.IsQuasiIso ↔ Function.Bijective f.linearPart := by
  have hcomm : ⇑f.cohomologyMap ∘ ⇑hA.cohomologyEquiv = ⇑hB.cohomologyEquiv ∘ ⇑f.linearPart :=
    funext (cohomologyMap_cohomologyEquiv hA hB f)
  rw [isQuasiIso_def, ← EquivLike.bijective_comp hA.cohomologyEquiv, hcomm,
    EquivLike.comp_bijective]

end AInfinityHom

end TauCeti
