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
endomorphism `dM` which carries `ℳ p` into `ℳ (p + 1)` and squares to zero, assembles into a
cochain complex of `R`-modules: the degree-`p` term is the submodule `ℳ p` and the differential is
the restriction of `dM`.  This file performs that assembly.  No decomposition or exhaustiveness
hypothesis on `ℳ` is required, and the differential is not assumed to come from a module action.

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

`gradedCochainComplex` exposes its body so that the component types in
`TauCeti.gradedCochainComplex_d_apply` reduce to the advertised submodules `ℳ p`.  The
element-level API is that lemma; nothing downstream should unfold the construction further.
-/

public section

namespace TauCeti

universe uR uM

variable {R : Type uR} {M : Type uM} [Ring R] [AddCommGroup M] [Module R M]

/-- The cochain complex of `R`-modules assembled from a `ℤ`-indexed family `ℳ` of submodules of
`M` and a square-zero `R`-linear endomorphism `dM` carrying `ℳ p` into `ℳ (p + 1)`. -/
@[expose]
def gradedCochainComplex (ℳ : ℤ → Submodule R M) (dM : M →ₗ[R] M)
    (hdeg : LinearMap.IsHomogeneous dM ℳ ℳ 1) (hsq : ∀ x, dM (dM x) = 0) :
    CochainComplex (ModuleCat R) ℤ :=
  CochainComplex.of (fun p ↦ ModuleCat.of R (ℳ p))
    (fun p ↦ ModuleCat.ofHom (dM.restrict (p := ℳ p) (q := ℳ (p + 1))
      fun _ hx ↦ hdeg.map_mem hx))
    fun _ ↦ ModuleCat.hom_ext (LinearMap.ext fun x ↦ Subtype.ext (hsq x))

variable {ℳ : ℤ → Submodule R M} {dM : M →ₗ[R] M}
  {hdeg : LinearMap.IsHomogeneous dM ℳ ℳ 1} {hsq : ∀ x, dM (dM x) = 0}

@[simp]
theorem gradedCochainComplex_X (p : ℤ) :
    (gradedCochainComplex ℳ dM hdeg hsq).X p = ModuleCat.of R (ℳ p) :=
  (rfl)

@[simp]
theorem gradedCochainComplex_d (p : ℤ) :
    (gradedCochainComplex ℳ dM hdeg hsq).d p (p + 1) =
      ModuleCat.ofHom (dM.restrict (p := ℳ p) (q := ℳ (p + 1)) fun _ hx ↦ hdeg.map_mem hx) := by
  apply CochainComplex.of_d

theorem gradedCochainComplex_d_apply (p : ℤ) (x : ℳ p) :
    ((gradedCochainComplex ℳ dM hdeg hsq).d p (p + 1)).hom x =
      (⟨dM x, hdeg.map_mem x.2⟩ : ℳ (p + 1)) := by
  rw [gradedCochainComplex_d]
  rfl

end TauCeti
