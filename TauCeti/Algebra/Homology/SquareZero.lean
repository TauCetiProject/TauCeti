/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat

/-!
# The homology of a square-zero linear endomorphism

A linear endomorphism `d` of a module `M` with `d ∘ d = 0` is a differential module, and its
homology is the kernel of `d` modulo its image. This file names that quotient concretely as
`d.homology hd = ker d ⧸ im d`, where `hd : d ∘ₗ d = 0`, and identifies it with Mathlib's
categorical homology of the
short complex `M ⟶ M ⟶ M` whose two maps are `d` (`LinearMap.homologyIso`).

The concrete quotient is what one needs to transport extra structure to homology that the category
of modules over the ring of `d` does not see, for instance an internal grading over a smaller
coefficient ring by which `d` is homogeneous: the elements of `d.homology hd` are classes of
elements of `M`, on which such structure is defined. The image is represented inside the kernel by
`boundariesInKer`.

## Main definitions

* `LinearMap.boundariesInKer`: the image of `d` as a submodule of the kernel of `d`.
* `LinearMap.homology`: for square-zero `d`, the kernel of `d` modulo its image.
* `LinearMap.homologyπ`: the class of an element of the kernel.
* `LinearMap.homologyIso`: for `d ∘ d = 0`, Mathlib's homology of the short complex with both maps
  `d` is `d.homology hd`.

## Main results

* `LinearMap.mem_boundariesInKer`: an element of the kernel is a boundary exactly when it lies in
  the image of `d`.
* `LinearMap.range_moduleCatToCycles_eq_boundariesInKer`: for `d ∘ d = 0`, the boundaries used by
  Mathlib's explicit homology of a short complex of modules are `d.boundariesInKer`.
-/

public section

open CategoryTheory

namespace LinearMap

variable {S M : Type*} [Ring S] [AddCommGroup M] [Module S M] (d : M →ₗ[S] M)

/-- The intersection of the image and kernel of a linear endomorphism `d`, viewed as a submodule
of the kernel. For a square-zero endomorphism, this is its full image. -/
abbrev boundariesInKer : Submodule S (ker d) :=
  (range d).comap (ker d).subtype

/-- An element of the kernel of `d` is a boundary exactly when it is a value of `d`. -/
theorem mem_boundariesInKer {z : ker d} : z ∈ d.boundariesInKer ↔ (z : M) ∈ range d :=
  Iff.rfl

/-- The homology `ker d ⧸ im d` of a square-zero linear endomorphism `d`. -/
abbrev homology (_hd : d ∘ₗ d = 0) : Type _ :=
  ker d ⧸ d.boundariesInKer

/-- The class in the homology of `d` of an element of the kernel of `d`. -/
noncomputable def homologyπ (hd : d ∘ₗ d = 0) : ker d →ₗ[S] d.homology hd :=
  d.boundariesInKer.mkQ

/-- The class of an element of the kernel is its class modulo the boundaries. -/
@[simp]
theorem homologyπ_apply (hd : d ∘ₗ d = 0) (z : ker d) :
    d.homologyπ hd z = Submodule.Quotient.mk z :=
  (rfl)

/-- Every homology class is the class of an element of the kernel. -/
theorem homologyπ_surjective (hd : d ∘ₗ d = 0) : Function.Surjective (d.homologyπ hd) :=
  Submodule.mkQ_surjective _

/-- An element of the kernel has zero class exactly when it is a value of `d`. -/
theorem homologyπ_eq_zero_iff (hd : d ∘ₗ d = 0) (z : ker d) :
    d.homologyπ hd z = 0 ↔ (z : M) ∈ range d :=
  Submodule.Quotient.mk_eq_zero _

/-- The short complex `M ⟶ M ⟶ M` of `S`-modules whose two maps are a square-zero endomorphism
`d`. -/
abbrev shortComplex (hd : d ∘ₗ d = 0) : ShortComplex (ModuleCat S) :=
  ShortComplex.mk (ModuleCat.ofHom d) (ModuleCat.ofHom d) (by
    rw [← ModuleCat.ofHom_comp, hd, ModuleCat.ofHom_zero])

/-- For a square-zero endomorphism `d`, the boundaries of Mathlib's explicit homology of the short
complex `M ⟶ M ⟶ M` with both maps `d` are the image of `d` inside its kernel. -/
theorem range_moduleCatToCycles_eq_boundariesInKer (hd : d ∘ₗ d = 0) :
    range (d.shortComplex hd).moduleCatToCycles = d.boundariesInKer := by
  ext z
  rw [mem_boundariesInKer, mem_range, mem_range]
  exact exists_congr fun _ ↦ Subtype.ext_iff

/-- For a square-zero endomorphism `d`, Mathlib's homology of the short complex `M ⟶ M ⟶ M` with
both maps `d` is the concrete homology `ker d ⧸ im d`. -/
noncomputable def homologyIso (hd : d ∘ₗ d = 0) :
    (d.shortComplex hd).homology ≅ ModuleCat.of S (d.homology hd) :=
  (d.shortComplex hd).moduleCatHomologyIso ≪≫
    (Submodule.quotEquivOfEq _ _ (d.range_moduleCatToCycles_eq_boundariesInKer hd)).toModuleIso

end LinearMap
