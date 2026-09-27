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

The component, differential, and element-level differential lemmas below are the intended public
interface to `gradedCochainComplex`.
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

variable {N : Type uM} [AddCommGroup N] [Module R N]
  {𝒩 : ℤ → Submodule R N} {dN : N →ₗ[R] N}
  {hdegN : LinearMap.IsHomogeneous dN 𝒩 𝒩 1}
  {hsqN : ∀ p (x : 𝒩 p), dN (dN x) = 0}

/-- A degree-preserving linear map commuting with differentials induces a map between the
cochain complexes assembled from graded modules. -/
def gradedCochainComplexMap (f : M →ₗ[R] N)
    (hf : LinearMap.IsHomogeneous f ℳ 𝒩 0)
    (hcomm : ∀ p (x : ℳ p), dN (f x) = f (dM x)) :
  gradedCochainComplex ℳ dM hdeg hsq ⟶ gradedCochainComplex 𝒩 dN hdegN hsqN where
  f n := eqToHom (gradedCochainComplex_X n) ≫
    ModuleCat.ofHom (f.restrict (fun _ hx ↦ by
      simpa only [add_zero] using hf.map_mem hx)) ≫
      eqToHom (gradedCochainComplex_X n).symm
  comm' i j hij := by
    obtain rfl : j = i + 1 := hij.symm
    dsimp [gradedCochainComplex]
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    apply Subtype.ext
    simpa [CochainComplex.of_d, ModuleCat.hom_comp, LinearMap.comp_apply,
      gradedCochainComplex_X, eqToHom]
      using hcomm i x

/-- On a homogeneous element, the induced cochain map is the original linear map. -/
@[simp]
theorem gradedCochainComplexMap_f_apply (f : M →ₗ[R] N)
    (hf : LinearMap.IsHomogeneous f ℳ 𝒩 0)
    (hcomm : ∀ p (x : ℳ p), dN (f x) = f (dM x)) (n : ℤ) (x : ℳ n) :
    (eqToHom (gradedCochainComplex_X n)
      ((gradedCochainComplexMap (hdeg := hdeg) (hsq := hsq) (hdegN := hdegN)
        (hsqN := hsqN) f hf hcomm).f n
          (eqToHom (gradedCochainComplex_X n).symm x)) : N) = f x := by
  simp only [gradedCochainComplexMap]
  rw [gradedCochainComplex_X_proof_eq_rfl (hdeg := hdeg) (hsq := hsq) n,
    gradedCochainComplex_X_proof_eq_rfl (hdeg := hdegN) (hsq := hsqN) n]
  rfl

/-- The induced cochain map depends only on the underlying linear map. -/
theorem gradedCochainComplexMap_congr {f g : M →ₗ[R] N} (h : f = g)
    (hf : LinearMap.IsHomogeneous f ℳ 𝒩 0)
    (hg : LinearMap.IsHomogeneous g ℳ 𝒩 0)
    (hcommf : ∀ p (x : ℳ p), dN (f x) = f (dM x))
    (hcommg : ∀ p (x : ℳ p), dN (g x) = g (dM x)) :
    gradedCochainComplexMap (hdeg := hdeg) (hsq := hsq)
      (hdegN := hdegN) (hsqN := hsqN) f hf hcommf =
    gradedCochainComplexMap (hdeg := hdeg) (hsq := hsq)
      (hdegN := hdegN) (hsqN := hsqN) g hg hcommg := by
  subst g
  rfl

/-- The cochain map induced by the identity linear map is the identity. -/
@[simp]
theorem gradedCochainComplexMap_id :
    gradedCochainComplexMap (hdeg := hdeg) (hsq := hsq)
      (hdegN := hdeg) (hsqN := hsq) (LinearMap.id : M →ₗ[R] M)
      (LinearMap.isHomogeneous_id ℳ) (fun _ _ ↦ rfl) =
        𝟙 (gradedCochainComplex ℳ dM hdeg hsq) := by
  apply HomologicalComplex.hom_ext
  intro n
  simp only [gradedCochainComplexMap]
  rw [gradedCochainComplex_X_proof_eq_rfl (hdeg := hdeg) (hsq := hsq) n]
  rfl

variable {P : Type uM} [AddCommGroup P] [Module R P]
  {𝒦 : ℤ → Submodule R P} {dP : P →ₗ[R] P}
  {hdegP : LinearMap.IsHomogeneous dP 𝒦 𝒦 1}
  {hsqP : ∀ p (x : 𝒦 p), dP (dP x) = 0}

/-- Cochain maps assembled from graded linear maps preserve composition. -/
theorem gradedCochainComplexMap_comp (f : M →ₗ[R] N) (g : N →ₗ[R] P)
    (hf : LinearMap.IsHomogeneous f ℳ 𝒩 0)
    (hg : LinearMap.IsHomogeneous g 𝒩 𝒦 0)
    (hcommf : ∀ p (x : ℳ p), dN (f x) = f (dM x))
    (hcommg : ∀ p (x : 𝒩 p), dP (g x) = g (dN x)) :
    gradedCochainComplexMap (hdeg := hdeg) (hsq := hsq)
      (hdegN := hdegP) (hsqN := hsqP) (g.comp f)
        (LinearMap.isHomogeneous_def.mpr fun _ _ hx ↦ by
          simpa only [LinearMap.comp_apply, add_zero] using hg.map_mem (hf.map_mem hx))
        (fun p x ↦ by
          have hfx : f x ∈ 𝒩 p := by
            simpa only [add_zero] using hf.map_mem x.2
          rw [LinearMap.comp_apply, hcommg p ⟨f x, hfx⟩,
            hcommf p x, LinearMap.comp_apply]) =
        gradedCochainComplexMap (hdeg := hdeg) (hsq := hsq)
          (hdegN := hdegN) (hsqN := hsqN) f hf hcommf ≫
        gradedCochainComplexMap (hdeg := hdegN) (hsq := hsqN)
          (hdegN := hdegP) (hsqN := hsqP) g hg hcommg := by
  apply HomologicalComplex.hom_ext
  intro n
  rfl

end TauCeti
