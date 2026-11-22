/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicGeometry.Scheme

/-!
# The section of the spectrum defined by an augmentation

For a commutative ring `R` and a commutative `R`-algebra `A`, an augmentation `f : A →ₐ[R] R` is a
retraction of the structure map `algebraMap R A`. Hence `Spec f : Spec R ⟶ Spec A` is a section of
the structure morphism `Spec A ⟶ Spec R`.

For example, the projection `TrivSqZeroExt.fstHom R R R` from the dual numbers `R[ε]` to `R`,
`ε ↦ 0`, splits `Spec R[ε] ⟶ Spec R`. Base change along this projection is the trivial
first-order deformation of a scheme over `R`, and base change along its section is reduction
modulo `ε`; `TauCeti.AlgebraicGeometry.PrestableMap.infinitesimalAut` uses this splitting.

## Main definitions

* `AlgHom.specSplitEpi`: the structure morphism `Spec A ⟶ Spec R`, split by the section induced
  by an augmentation `A →ₐ[R] R`.
-/

public section

noncomputable section

open CategoryTheory AlgebraicGeometry

namespace AlgHom

universe u

variable {R A : Type u} [CommRing R] [CommRing A] [Algebra R A]

/-- The structure morphism `Spec A ⟶ Spec R` of a commutative `R`-algebra `A`, split by the
section `Spec R ⟶ Spec A` induced by an augmentation `f : A →ₐ[R] R`. -/
def specSplitEpi (f : A →ₐ[R] R) :
    SplitEpi (Spec.map (CommRingCat.ofHom (algebraMap R A))) where
  section_ := Spec.map (CommRingCat.ofHom (f : A →+* R))
  id := by
    rw [← Spec.map_comp, ← Spec.map_id]
    refine congrArg Spec.map ?_
    ext r
    exact f.commutes r

/-- The section of `f.specSplitEpi` is induced by the augmentation `f`. -/
@[simp]
theorem specSplitEpi_section (f : A →ₐ[R] R) :
    f.specSplitEpi.section_ = Spec.map (CommRingCat.ofHom (f : A →+* R)) :=
  (rfl)

end AlgHom
