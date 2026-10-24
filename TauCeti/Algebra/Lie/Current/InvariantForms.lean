/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.Current.ContinuousCohomology

import TauCeti.Algebra.Lie.Killing.Basic

/-!
# Invariant forms classify the continuous second cohomology of formal currents

The residue class `[c_Φ]` of an invariant symmetric form `Φ` on a Lie algebra `L` is the class of
the residue cocycle `(f ⊗ x, g ⊗ y) ↦ Res(f dg) Φ(x, y)` in the continuous second cohomology of
the formal currents `R⸨X⸩ ⊗[R] L` with trivial coefficients. This file shows that `[c_Φ]` depends
linearly on `Φ`, and packages it as a linear map
`TauCeti.CurrentAlgebra.invariantFormsResidueClass` on the submodule
`TauCeti.LieModule.invariantForms R L L` of invariant symmetric forms.

Over a characteristic-zero domain this map is injective for every Lie algebra `L`: a continuous
cohomology class determines the form whose residue cocycle represents it. When `L` is
finite-dimensional with nondegenerate Killing form over a field of characteristic zero and the
invariant forms are the multiples of one form `Ψ` which is nonzero on some bracket, the map is
also surjective. For a simple Lie algebra over an algebraically closed field of characteristic
zero, `Φ ↦ [c_Φ]` is therefore a linear equivalence from the invariant symmetric forms on `L` onto
the continuous second cohomology of its formal loop algebra
(`TauCeti.CurrentAlgebra.invariantFormsResidueClassEquiv`).

The residue cocycle uses Mathlib's sign convention `Res(f dg) Φ(x, y)`. The affine cocycle
`c_κ = -κ(x, y) Res(f dg)` of a level form `κ` is the residue cocycle of `Φ = -κ`, so the map
`κ ↦ [c_κ]` of the affine convention is the residue class map precomposed with negation of
forms.

## Main definitions

* `TauCeti.CurrentAlgebra.invariantFormsResidueClass`: the linear map `Φ ↦ [c_Φ]`.
* `TauCeti.CurrentAlgebra.invariantFormsResidueClassEquiv`: for a simple Lie algebra, the linear
  equivalence from invariant symmetric forms onto continuous second cohomology.

## Main results

* `TauCeti.CurrentAlgebra.residueClass_add`, `TauCeti.CurrentAlgebra.residueClass_smul`: the
  residue class is linear in the form.
* `TauCeti.CurrentAlgebra.invariantFormsResidueClass_injective` and
  `TauCeti.CurrentAlgebra.residueClass_inj`: over a characteristic-zero domain, distinct forms have
  distinct residue classes.
* `TauCeti.CurrentAlgebra.invariantFormsResidueClass_surjective`: every continuous class is the
  residue class of an invariant symmetric form.

## References

* E. Frenkel, *Langlands Correspondence for Loop Groups*, §1.3, for the classification of central
  extensions of the formal loop algebra by its continuous second cohomology.
* V. G. Kac, *Infinite-Dimensional Lie Algebras*, 3rd ed., Chapter 7, for the affine central
  extension attached to an invariant form.
-/

public section

noncomputable section

namespace TauCeti.CurrentAlgebra

open _root_.LieModule.Cohomology TauCeti.LieModule.Cohomology TauCeti.LieModule

section CommRing

variable {R L : Type*} [CommRing R] [LieRing L] [LieAlgebra R L]

/-- The residue class is additive in the form. -/
theorem residueClass_add {Φ Ψ : LinearMap.BilinForm R L} (hΦ : Φ.lieInvariant L)
    (hΦs : Φ.IsSymm) (hΨ : Ψ.lieInvariant L) (hΨs : Ψ.IsSymm) (hΦΨ : (Φ + Ψ).lieInvariant L)
    (hΦΨs : (Φ + Ψ).IsSymm) :
    residueClass R L (Φ + Ψ) hΦΨ hΦΨs =
      residueClass R L Φ hΦ hΦs + residueClass R L Ψ hΨ hΨs := by
  simp only [residueClass_eq_mk, ← map_add]
  congr 1
  refine Subtype.ext <| Subtype.ext <| LinearMap.ext₂ fun u v ↦ ?_
  simp

/-- Rescaling the form rescales its residue class. -/
theorem residueClass_smul (r : R) {Φ : LinearMap.BilinForm R L} (hΦ : Φ.lieInvariant L)
    (hΦs : Φ.IsSymm) (hrΦ : (r • Φ).lieInvariant L) (hrΦs : (r • Φ).IsSymm) :
    residueClass R L (r • Φ) hrΦ hrΦs = r • residueClass R L Φ hΦ hΦs := by
  simp only [residueClass_eq_mk, ← map_smul]
  congr 1
  refine Subtype.ext ?_
  simpa using congrArg Subtype.val (twoCocycleOfBilinear_smul R L r Φ hΦ hΦs hrΦ hrΦs)

variable (R L) in
/-- **The residue class map.** The linear map `Φ ↦ [c_Φ]` from the invariant symmetric forms on
`L` to the continuous second cohomology of formal currents with trivial coefficients, where
`c_Φ` is the residue cocycle `(f ⊗ x, g ⊗ y) ↦ Res(f dg) Φ(x, y)`. -/
def invariantFormsResidueClass :
    invariantForms R L L →ₗ[R] continuousSecondCohomology R (currentAlgebra R L)
      (TrivialLieModule R (currentAlgebra R L) R) where
  toFun Φ := residueClass R L Φ (mem_invariantForms_iff.mp Φ.2).1 (mem_invariantForms_iff.mp Φ.2).2
  map_add' _ _ := residueClass_add _ _ _ _ _ _
  map_smul' r _ := residueClass_smul r _ _ _ _

@[simp]
theorem invariantFormsResidueClass_apply (Φ : invariantForms R L L) :
    invariantFormsResidueClass R L Φ =
      residueClass R L Φ (mem_invariantForms_iff.mp Φ.2).1 (mem_invariantForms_iff.mp Φ.2).2 :=
  (rfl)

/-- **A continuous class determines its form.** Over a characteristic-zero domain, two invariant
symmetric forms have the same residue class exactly when they are equal. -/
theorem residueClass_inj [IsDomain R] [CharZero R] {Φ Ψ : LinearMap.BilinForm R L}
    (hΦ : Φ.lieInvariant L) (hΦs : Φ.IsSymm) (hΨ : Ψ.lieInvariant L) (hΨs : Ψ.IsSymm) :
    residueClass R L Φ hΦ hΦs = residueClass R L Ψ hΨ hΨs ↔ Φ = Ψ := by
  refine ⟨fun h ↦ ?_, fun h ↦ by subst h; rfl⟩
  -- The residue class of `Φ - Ψ`, written `Φ + (-1) • Ψ`, vanishes, so `Φ - Ψ` is zero.
  have hΨ' : (-1 : R) • Ψ ∈ invariantForms R L L :=
    Submodule.smul_mem _ _ (mem_invariantForms_iff.mpr ⟨hΨ, hΨs⟩)
  have hD : Φ + (-1 : R) • Ψ ∈ invariantForms R L L :=
    add_mem (mem_invariantForms_iff.mpr ⟨hΦ, hΦs⟩) hΨ'
  by_contra hne
  refine residueClass_ne_zero (mem_invariantForms_iff.mp hD).1 (mem_invariantForms_iff.mp hD).2
    (fun h0 ↦ hne (LinearMap.ext₂ fun x y ↦ by
      linear_combination (by simpa using LinearMap.congr_fun₂ h0 x y : Φ x y + -Ψ x y = 0))) ?_
  rw [residueClass_add hΦ hΦs (mem_invariantForms_iff.mp hΨ').1 (mem_invariantForms_iff.mp hΨ').2,
    residueClass_smul (-1) hΨ hΨs, h, neg_one_smul, add_neg_cancel]

/-- Over a characteristic-zero domain, the residue class map on invariant symmetric forms is
injective. -/
theorem invariantFormsResidueClass_injective [IsDomain R] [CharZero R] :
    Function.Injective (invariantFormsResidueClass R L) := fun _ _ h ↦
  Subtype.ext ((residueClass_inj _ _ _ _).mp h)

end CommRing

section Field

variable {K L : Type*} [Field K] [CharZero K] [LieRing L] [LieAlgebra K L] [FiniteDimensional K L]
  [_root_.LieAlgebra.IsKilling K L]

/-- **Every continuous class is a residue class.** Let `L` be a finite-dimensional Lie algebra with
nondegenerate Killing form over a field of characteristic zero, whose invariant forms are the
multiples of an invariant symmetric form `Ψ` which is nonzero on some bracket. Then every class in
the continuous second cohomology of formal currents with trivial coefficients is the residue class
of an invariant symmetric form. -/
theorem invariantFormsResidueClass_surjective {Ψ : LinearMap.BilinForm K L}
    (hΨ : Ψ.lieInvariant L) (hΨs : Ψ.IsSymm)
    (hspan : ∀ Φ : LinearMap.BilinForm K L, Φ.lieInvariant L → ∃ t : K, Φ = t • Ψ)
    (hne : ∃ x y z : L, Ψ ⁅x, y⁆ z ≠ 0) :
    Function.Surjective (invariantFormsResidueClass K L) := fun a ↦ by
  obtain ⟨t, rfl⟩ := exists_eq_smul_residueClass hΨ hΨs hspan hne a
  exact ⟨t • ⟨Ψ, mem_invariantForms_iff.mpr ⟨hΨ, hΨs⟩⟩,
    by rw [map_smul, invariantFormsResidueClass_apply]⟩

variable (K L) [IsAlgClosed K] [_root_.LieModule.IsIrreducible K L L]

/-- **Invariant forms classify the continuous second cohomology of formal loops.** For a
finite-dimensional Lie algebra over an algebraically closed field of characteristic zero whose
adjoint module is irreducible and whose Killing form is nondegenerate, for instance a simple Lie
algebra, `Φ ↦ [c_Φ]` is a linear equivalence from the invariant symmetric forms on `L` onto the
continuous second cohomology of formal currents with trivial coefficients. -/
def invariantFormsResidueClassEquiv :
    invariantForms K L L ≃ₗ[K] continuousSecondCohomology K (currentAlgebra K L)
      (TrivialLieModule K (currentAlgebra K L) K) :=
  have _i := _root_.LieModule.nontrivial_of_isIrreducible K L L
  LinearEquiv.ofBijective (invariantFormsResidueClass K L)
    ⟨invariantFormsResidueClass_injective,
      invariantFormsResidueClass_surjective (_root_.LieModule.traceForm_lieInvariant K L L)
        (LinearMap.BilinForm.isSymm_iff.mpr (_root_.LieModule.traceForm_isSymm K L L))
        (fun _ hΦ ↦ TauCeti.LieAlgebra.exists_eq_smul_killingForm hΦ)
        exists_killingForm_lie_ne_zero⟩

variable {K L}

@[simp]
theorem invariantFormsResidueClassEquiv_apply (Φ : invariantForms K L L) :
    invariantFormsResidueClassEquiv K L Φ =
      residueClass K L Φ (mem_invariantForms_iff.mp Φ.2).1 (mem_invariantForms_iff.mp Φ.2).2 :=
  (rfl)

/-- The inverse of `invariantFormsResidueClassEquiv` recovers the form from its residue class. -/
@[simp]
theorem invariantFormsResidueClassEquiv_symm_residueClass {Φ : LinearMap.BilinForm K L}
    (hΦ : Φ.lieInvariant L) (hΦs : Φ.IsSymm) :
    (invariantFormsResidueClassEquiv K L).symm (residueClass K L Φ hΦ hΦs) =
      ⟨Φ, mem_invariantForms_iff.mpr ⟨hΦ, hΦs⟩⟩ :=
  (LinearEquiv.symm_apply_eq _).mpr (rfl)

end Field

end TauCeti.CurrentAlgebra
