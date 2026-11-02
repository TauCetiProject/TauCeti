/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.Current.ContinuousCohomology

/-!
# Invariant forms classify the continuous second cohomology of formal currents

The residue class `[c_Φ]` of an invariant symmetric form `Φ` on a Lie algebra `L` is the class of
the residue cocycle `(f ⊗ x, g ⊗ y) ↦ Res(f dg) Φ(x, y)` in the continuous second cohomology of
the formal currents `R⸨X⸩ ⊗[R] L` with trivial coefficients. Since `[c_Φ]` depends linearly on
`Φ`, this file packages it as a linear map
`TauCeti.CurrentAlgebra.invariantFormsResidueClass` on the submodule
`TauCeti.LieModule.invariantForms R L L` of invariant symmetric forms.

Over every commutative ring this map is injective for every Lie algebra `L`: a continuous
cohomology class determines the form whose residue cocycle represents it. When `L` is
finite-dimensional with nondegenerate Killing form over a field of characteristic zero, that is,
when `L` is semisimple, the map is also surjective. So for every semisimple Lie algebra, including
a finite product of simple ones (`LieAlgebra.IsKilling.instProd`), `Φ ↦ [c_Φ]` is a linear
equivalence from the invariant symmetric forms on `L` onto the continuous second cohomology of its
formal loop algebra (`TauCeti.CurrentAlgebra.invariantFormsResidueClassEquiv`). No algebraic
closedness and no simplicity is needed.

The residue cocycle uses Mathlib's sign convention `Res(f dg) Φ(x, y)`. The affine cocycle
`c_κ = -κ(x, y) Res(f dg)` of a level form `κ` is the residue cocycle of `Φ = -κ`, so the map
`κ ↦ [c_κ]` of the affine convention is the residue class map precomposed with negation of
forms.

## Main definitions

* `TauCeti.CurrentAlgebra.invariantFormsResidueClass`: the linear map `Φ ↦ [c_Φ]`.
* `TauCeti.CurrentAlgebra.invariantFormsResidueClassEquiv`: for a semisimple Lie algebra, the
  linear equivalence from invariant symmetric forms onto continuous second cohomology.

## Main results

* `TauCeti.CurrentAlgebra.invariantFormsResidueClass_injective`: distinct invariant symmetric
  forms have distinct residue classes.
* `TauCeti.CurrentAlgebra.invariantFormsResidueClass_surjective`: every continuous class is the
  residue class of an invariant symmetric form.
* `TauCeti.CurrentAlgebra.exists_eq_smul_residueClass`: the residue class of a spanning form spans
  continuous second cohomology.

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

/-- The residue class map on invariant symmetric forms is injective, over every commutative
ring. -/
theorem invariantFormsResidueClass_injective :
    Function.Injective (invariantFormsResidueClass R L) := fun _ _ h ↦
  Subtype.ext ((residueClass_inj _ _ _ _).mp h)

end CommRing

section Field

variable {K L : Type*} [Field K] [CharZero K] [LieRing L] [LieAlgebra K L] [FiniteDimensional K L]
  [_root_.LieAlgebra.IsKilling K L]

/-- **Every continuous class is a residue class.** Let `L` be a finite-dimensional Lie algebra with
nondegenerate Killing form over a field of characteristic zero, for instance a semisimple Lie
algebra. Then every class in the continuous second cohomology of formal currents with trivial
coefficients is the residue class of an invariant symmetric form. -/
theorem invariantFormsResidueClass_surjective :
    Function.Surjective (invariantFormsResidueClass K L) := fun a ↦ by
  obtain ⟨c, rfl⟩ := continuousSecondCohomologyMk_surjective a
  obtain ⟨Ψ, hΨ, hΨs, f, hf, hc⟩ := exists_eq_twoCochainOfBilinear_add_d₁₂ c.2
  refine ⟨⟨Ψ, mem_invariantForms_iff.mpr ⟨hΨ, hΨs⟩⟩, ?_⟩
  rw [invariantFormsResidueClass_apply, residueClass_eq_mk, continuousSecondCohomologyMk_eq_iff]
  exact ⟨-f, neg_mem hf, by
    simp only [map_neg, AddSubgroupClass.coe_sub, hc]
    abel⟩

/-- **The continuous second cohomology of formal currents is spanned by the residue class.**
Under the hypotheses of `invariantFormsResidueClass_surjective`, let `Ψ` be an invariant symmetric
form on `L` spanning the invariant forms. Then every class in the continuous second cohomology of
formal currents with trivial coefficients is a multiple of the residue class of `Ψ`. -/
theorem exists_eq_smul_residueClass {Ψ : LinearMap.BilinForm K L} (hΨ : Ψ.lieInvariant L)
    (hΨs : Ψ.IsSymm)
    (hspan : ∀ Φ : LinearMap.BilinForm K L, Φ.lieInvariant L → ∃ t : K, Φ = t • Ψ)
    (a : continuousSecondCohomology K (currentAlgebra K L)
      (TrivialLieModule K (currentAlgebra K L) K)) :
    ∃ t : K, a = t • residueClass K L Ψ hΨ hΨs := by
  obtain ⟨⟨Φ, hΦ⟩, rfl⟩ := invariantFormsResidueClass_surjective a
  obtain ⟨hΦi, hΦs⟩ := mem_invariantForms_iff.mp hΦ
  obtain ⟨t, rfl⟩ := hspan Φ hΦi
  exact ⟨t, residueClass_smul t hΨ hΨs _ _⟩

variable (K L)

/-- **Invariant forms classify the continuous second cohomology of formal loops.** For a
finite-dimensional Lie algebra with nondegenerate Killing form over a field of characteristic
zero, for instance a semisimple Lie algebra, `Φ ↦ [c_Φ]` is a linear equivalence from the
invariant symmetric forms on `L` onto the continuous second cohomology of formal currents with
trivial coefficients. -/
def invariantFormsResidueClassEquiv :
    invariantForms K L L ≃ₗ[K] continuousSecondCohomology K (currentAlgebra K L)
      (TrivialLieModule K (currentAlgebra K L) K) :=
  LinearEquiv.ofBijective (invariantFormsResidueClass K L)
    ⟨invariantFormsResidueClass_injective, invariantFormsResidueClass_surjective⟩

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
