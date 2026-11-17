/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.ModuleCat.Basic
public import TauCeti.LinearAlgebra.Basis.Exact

/-!
# Bases of the cycles and of the homology of complexes of modules

Let `C` be a homological complex of modules over a ring. In each degree `i`, the boundaries `Bᵢ`,
the cycles `Zᵢ` and the homology `Hᵢ` form a short exact sequence `0 → Bᵢ → Zᵢ → Hᵢ → 0`
(`HomologicalComplex.exact_inclusion_moduleCatKerHomologyClass`). So a basis `b` of `Bᵢ` and
cycles `y` representing a basis `h` of `Hᵢ` combine into the basis `(b, y)` of `Zᵢ`
(`HomologicalComplex.kerBasisOfHomology`), with the cycles taken as the kernel of the outgoing
differential. The determinant of one such basis with respect to another is the product of the
determinants of the bases of `Bᵢ` and of `Hᵢ`
(`HomologicalComplex.kerBasisOfHomology_det_kerBasisOfHomology`).

Conversely, a linear map `j` into `C.X i` whose values are cycles has a homology class map
(`HomologicalComplex.moduleCatHomologyClass`). If `j` carries a basis `g` of its source to cycles
representing a basis of `Hᵢ`, the class map is bijective
(`HomologicalComplex.moduleCatHomologyClass_bijective_of_basis`).

## Main declarations

* `HomologicalComplex.kerBasisOfHomology`: the basis of the cycles made of a basis of the
  boundaries followed by cycles representing a basis of the homology.
* `HomologicalComplex.kerBasisOfHomology_det_kerBasisOfHomology`: the determinant of one such basis
  of the cycles with respect to another is the product of the determinants of the bases of the
  boundaries and of the homology.
* `HomologicalComplex.moduleCatHomologyClass_bijective_of_basis`: a homology class map carrying a
  basis to cycles representing a basis of the homology is bijective.
-/

public section

noncomputable section

open CategoryTheory Module

namespace HomologicalComplex

variable {ι : Type*} {c : ComplexShape ι}

section KerBasis

variable {R : Type*} [Ring R] {C : HomologicalComplex (ModuleCat R) c} {l i k : ι}
  (hl : c.prev i = l) (hk : c.next i = k) {κ σ : Type*}
  (b : Basis κ R (LinearMap.range (C.d l i).hom)) (h : Basis σ R (C.homology i))
  (y : σ → C.cycles i) (hy : ∀ t, C.homologyπ i (y t) = h t)

/-- For a homological complex `C` of modules, the basis `(b, y)` of the cycles `Zᵢ`, the kernel of
the differential `C.d i k` out of degree `i`, made of a basis `b` of the boundaries `Bᵢ`, the image
of the differential `C.d l i` into degree `i`, followed by cycles `y` representing a basis `h` of
the homology `Hᵢ`. -/
def kerBasisOfHomology : Basis (κ ⊕ σ) R (LinearMap.ker (C.d i k).hom) :=
  Basis.ofExactLift (Submodule.inclusion_injective _)
    (C.exact_inclusion_moduleCatKerHomologyClass hk hl) b h (C.moduleCatCyclesToKer i k ∘ y)
    fun t ↦ by rw [Function.comp_apply, moduleCatKerHomologyClass_moduleCatCyclesToKer, hy]

/-- On the left summand, `kerBasisOfHomology` is the basis of the boundaries. -/
@[simp]
theorem coe_kerBasisOfHomology_inl (t : κ) :
    (kerBasisOfHomology hl hk b h y hy (.inl t) : C.X i) = b t := by
  simp [kerBasisOfHomology]

/-- On the right summand, `kerBasisOfHomology` is the family of cycles representing the homology
basis. -/
@[simp]
theorem coe_kerBasisOfHomology_inr (t : σ) :
    (kerBasisOfHomology hl hk b h y hy (.inr t) : C.X i) = C.iCycles i (y t) := by
  simp [kerBasisOfHomology]

end KerBasis

section KerBasisDet

variable {R : Type*} [CommRing R] {C : HomologicalComplex (ModuleCat R) c} {l i k : ι}
  (hl : c.prev i = l) (hk : c.next i = k) {κ σ : Type*} [Fintype κ] [DecidableEq κ] [Fintype σ]
  [DecidableEq σ] (b b' : Basis κ R (LinearMap.range (C.d l i).hom))
  (h h' : Basis σ R (C.homology i)) (y y' : σ → C.cycles i)
  (hy : ∀ t, C.homologyπ i (y t) = h t) (hy' : ∀ t, C.homologyπ i (y' t) = h' t)

/-- The determinant of one basis `kerBasisOfHomology` of the cycles with respect to another is the
product of the determinants of the bases of the boundaries and of the homology; in particular it
does not depend on the cycles representing the homology bases. -/
theorem kerBasisOfHomology_det_kerBasisOfHomology :
    (kerBasisOfHomology hl hk b h y hy).det (kerBasisOfHomology hl hk b' h' y' hy') =
      b.det b' * h.det h' :=
  Basis.ofExactLift_det_ofExactLift ..

end KerBasisDet

section HomologyClass

variable {R : Type*} [Ring R] (K : HomologicalComplex (ModuleCat R) c) {n m : ι}
  (hm : c.next n = m) {Z : Type*} [AddCommGroup Z] [Module R Z] (j : Z →ₗ[R] K.X n)
  (hj : ∀ z, K.d n m (j z) = 0)
  {σ : Type*} (g : Basis σ R Z) (h : Basis σ R (K.homology n)) (y : σ → K.cycles n)
  (hy : ∀ t, K.homologyπ n (y t) = h t) (hjy : ∀ t, K.iCycles n (y t) = j (g t))

include hy hjy in
/-- If a linear map `j` into the degree-`n` term of a complex of modules carries a basis `g` of its
source to cycles `y` representing a basis `h` of the homology `Hₙ`, then its homology class map is
bijective: it carries the basis `g` to the basis `h`. -/
theorem moduleCatHomologyClass_bijective_of_basis :
    Function.Bijective (K.moduleCatHomologyClass hm j hj) := by
  have : K.moduleCatHomologyClass hm j hj = (g.equiv h (Equiv.refl _)).toLinearMap :=
    g.ext fun t ↦ by
      rw [moduleCatHomologyClass_apply, LinearEquiv.coe_coe, Basis.equiv_apply, Equiv.refl_apply,
        ← hy]
      congr 1
      apply K.moduleCat_iCycles_injective n
      rw [iCycles_moduleCatCyclesMk, hjy]
  rw [this]
  exact (g.equiv h (Equiv.refl _)).bijective

end HomologyClass

end HomologicalComplex
