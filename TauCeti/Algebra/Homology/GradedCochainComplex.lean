/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Basic
public import Mathlib.Algebra.Homology.HomologicalComplex
public import TauCeti.LinearAlgebra.Graded.LinearMap

/-!
# The cochain complex of a family of submodules with a differential

A `ℤ`-indexed family `ℳ` of submodules of an `R`-module `M`, together with an `R`-linear
endomorphism `dM` which carries `ℳ p` into `ℳ (p + 1)` and squares to zero on each `ℳ p`,
assembles into a cochain complex of `R`-modules: the degree-`p` term is the submodule `ℳ p` and
the differential is the restriction of `dM`.  This file performs that assembly.  No decomposition
or exhaustiveness hypothesis on `ℳ` is required, and the differential is not assumed to come
from a module action.

In practice `ℳ` is the internal grading in which the differential graded algebras and modules of
`TauCeti.Algebra.Homology.DG` store their structure, because a product or an action is easier to
write on one carrier than on a family of summands.  Statements which compare such an object with
a genuine complex — quasi-isomorphisms, Hom complexes, cohomology computed by Mathlib's
homological algebra — need the complex on the other side, and that is what this construction
supplies: it serves the underlying complex of a DG algebra and of a DG module on either side.

## Main definitions

* `TauCeti.gradedCochainComplex`: the cochain complex whose degree-`p` term is the submodule
  `ℳ p` and whose differential is the restriction of `dM`.

## Implementation notes

`gradedCochainComplex` is opaque.  Its component, differential, and element-level differential
lemmas below are the public interface to the construction.
-/

public section

open CategoryTheory

namespace TauCeti

universe uR uM

variable {R : Type uR} {M : Type uM} [Ring R] [AddCommGroup M] [Module R M]

/-- The cochain complex of `R`-modules assembled from a `ℤ`-indexed family `ℳ` of submodules of
`M` and an `R`-linear endomorphism `dM` carrying `ℳ p` into `ℳ (p + 1)` and square-zero on
each `ℳ p`. -/
def gradedCochainComplex (ℳ : ℤ → Submodule R M) (dM : M →ₗ[R] M)
    (hdeg : LinearMap.IsHomogeneous dM ℳ ℳ 1) (hsq : ∀ p (x : ℳ p), dM (dM x) = 0) :
    CochainComplex (ModuleCat R) ℤ :=
  CochainComplex.of (fun p ↦ ModuleCat.of R (ℳ p))
    (fun p ↦ ModuleCat.ofHom (dM.restrict (p := ℳ p) (q := ℳ (p + 1))
      fun _ hx ↦ hdeg.map_mem hx))
    fun p ↦ ModuleCat.hom_ext (LinearMap.ext fun x ↦ Subtype.ext (hsq p x))

variable {ℳ : ℤ → Submodule R M} {dM : M →ₗ[R] M}
  {hdeg : LinearMap.IsHomogeneous dM ℳ ℳ 1} {hsq : ∀ p (x : ℳ p), dM (dM x) = 0}

@[simp]
theorem gradedCochainComplex_X (p : ℤ) :
    (gradedCochainComplex ℳ dM hdeg hsq).X p = ModuleCat.of R (ℳ p) :=
  (rfl)

private theorem gradedCochainComplex_X_proof_eq_rfl (p : ℤ) :
    gradedCochainComplex_X (hdeg := hdeg) (hsq := hsq) p = rfl :=
  Subsingleton.elim _ _

@[simp]
theorem gradedCochainComplex_d (p : ℤ) :
    (gradedCochainComplex ℳ dM hdeg hsq).d p (p + 1) =
      eqToHom (gradedCochainComplex_X (hdeg := hdeg) (hsq := hsq) p) ≫
        ModuleCat.ofHom
          (dM.restrict (p := ℳ p) (q := ℳ (p + 1)) fun _ hx ↦ hdeg.map_mem hx) ≫
            eqToHom (gradedCochainComplex_X (hdeg := hdeg) (hsq := hsq) (p + 1)).symm := by
  rw [gradedCochainComplex_X_proof_eq_rfl, gradedCochainComplex_X_proof_eq_rfl]
  unfold gradedCochainComplex
  simp only [CochainComplex.of_d, eqToHom_refl, Category.id_comp, Category.comp_id]

/-- The differential of `gradedCochainComplex` on an element. This is intentionally not a simp
lemma: `gradedCochainComplex_d` already simplifies its left-hand side, so registering both rules
would fail the `simpNF` linter. -/
theorem gradedCochainComplex_d_apply (p : ℤ) (x : ℳ p) :
    eqToHom (gradedCochainComplex_X (hdeg := hdeg) (hsq := hsq) (p + 1))
        ((gradedCochainComplex ℳ dM hdeg hsq).d p (p + 1)
          (eqToHom (gradedCochainComplex_X (hdeg := hdeg) (hsq := hsq) p).symm x)) =
      (⟨dM x, hdeg.map_mem x.2⟩ : ℳ (p + 1)) :=
  by
    rw [gradedCochainComplex_d]
    rw [gradedCochainComplex_X_proof_eq_rfl, gradedCochainComplex_X_proof_eq_rfl]
    rfl

end TauCeti
