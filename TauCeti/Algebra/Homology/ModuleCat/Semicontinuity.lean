/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Homology.Additive
public import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex
public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
public import TauCeti.Algebra.Category.ModuleCat.ChangeOfRings
public import TauCeti.LinearAlgebra.Submodule.Quotient
public import TauCeti.RingTheory.Spectrum.Prime.Semicontinuity

/-!
# Semicontinuity of the fibre homology of a complex of modules

Let `K` be a complex of modules over a commutative ring `R`. For a prime `p` of `R`, extending
scalars to the residue field `κ(p)` gives the fibre `κ(p) ⊗_R K`, a complex of `κ(p)`-vector
spaces. This file shows that if the term of `K` in degree `j` is a finite `R`-module and the next
term is projective, then the dimension of the homology of `κ(p) ⊗_R K` in degree `j` is an upper
semicontinuous function of `p ∈ Spec R`
(`HomologicalComplex.upperSemicontinuous_finrank_homology_extendScalars`).

This is the form in which the algebraic semicontinuity theorem
`LinearMap.upperSemicontinuous_finrank_fiber_homology` applies to a complex in `ModuleCat R`,
whose base change is taken with `ModuleCat.extendScalars`. In particular it applies in every degree
to a complex of finite projective modules, such as one computing the cohomology of the fibres of a
flat family of coherent sheaves.

The homology in degree `j` is the homology of the short complex of the terms in degrees
`c.prev j`, `j` and `c.next j` (`HomologicalComplex.homologyIsoSc'`); after extension of scalars
this is identified, through `ModuleCat.extendScalarsAlgebraMapIso`, with the short complex of the
base changes `κ(p) ⊗_R K.X i` of the terms, whose homology is computed by kernels and ranges
(`CategoryTheory.ShortComplex.moduleCatHomologyIso`).

## Main results

* `HomologicalComplex.nonempty_linearEquiv_homology_extendScalars`: the homology of `S ⊗_R K` as
  the image of the kernel of `S ⊗_R d` in the cokernel of the previous `S ⊗_R d`.
* `HomologicalComplex.upperSemicontinuous_finrank_homology_extendScalars`: upper semicontinuity
  of the dimension of the fibre homology.

## References

* R. Hartshorne, *Algebraic Geometry*, GTM 52, Springer, 1977, the proof of Theorem III.12.8.
* D. Mumford, *Abelian Varieties*, §5, Corollary (a).
-/

public section

noncomputable section

open CategoryTheory Limits Module

universe u

namespace HomologicalComplex

variable {R : Type u} [CommRing R] {ι : Type*} {c : ComplexShape ι}
  (K : HomologicalComplex (ModuleCat.{u} R) c)

/-- Over an `R`-algebra `S`, the homology in degree `j` of the complex `S ⊗_R K` obtained by
extension of scalars is the image of the kernel of `S ⊗_R d : S ⊗_R K.X j → S ⊗_R K.X k` in the
cokernel of `S ⊗_R d : S ⊗_R K.X i → S ⊗_R K.X j`, where `i` and `k` are the degrees before and
after `j`. -/
theorem nonempty_linearEquiv_homology_extendScalars (S : Type u) [CommRing S] [Algebra R S]
    {i j k : ι} (hi : c.prev j = i) (hk : c.next j = k) :
    Nonempty ((((ModuleCat.extendScalars (algebraMap R S)).mapHomologicalComplex c).obj
      K).homology j ≃ₗ[S] (LinearMap.ker ((K.d j k).hom.baseChange S)).map
        (LinearMap.range ((K.d i j).hom.baseChange S)).mkQ) := by
  let F := ModuleCat.extendScalars.{u, u, u} (algebraMap R S)
  let e (n : ι) := ModuleCat.extendScalarsAlgebraMapIso (S := S) (K.X n)
  have hd (n m : ι) : (ModuleCat.ofHom ((K.d n m).hom.baseChange S)) =
      (e n).inv ≫ F.map (K.d n m) ≫ (e m).hom := by
    rw [ModuleCat.extendScalarsAlgebraMapIso_hom_naturality, Iso.inv_hom_id_assoc]
  -- The short complex of the base changes `S ⊗[R] K.X n` of the terms in degrees `i`, `j`, `k`.
  let T : ShortComplex (ModuleCat.{u} S) :=
    ShortComplex.mk (ModuleCat.ofHom ((K.d i j).hom.baseChange S))
      (ModuleCat.ofHom ((K.d j k).hom.baseChange S)) (by
        rw [hd, hd]
        simp only [Category.assoc, Iso.hom_inv_id_assoc, ← F.map_comp_assoc, K.d_comp_d,
          F.map_zero, zero_comp, comp_zero])
  let E : ((F.mapHomologicalComplex c).obj K).sc' i j k ≅ T :=
    ShortComplex.isoMk (e i) (e j) (e k)
      (ModuleCat.extendScalarsAlgebraMapIso_hom_naturality (K.d i j)).symm
      (ModuleCat.extendScalarsAlgebraMapIso_hom_naturality (K.d j k)).symm
  exact ⟨(((F.mapHomologicalComplex c).obj K).homologyIsoSc' i j k hi hk ≪≫
    ShortComplex.homologyMapIso E ≪≫ T.moduleCatHomologyIso).toLinearEquiv ≪≫ₗ
      LinearMap.mapMkQKerEquiv _ _ _⟩

/-- **Semicontinuity of fibre homology.** Let `K` be a complex of modules over a commutative ring
`R` whose term in degree `j` is finite and whose term in the next degree is projective. Then the
dimension of the homology in degree `j` of the fibre `κ(p) ⊗_R K` is an upper semicontinuous
function of `p ∈ Spec R`. -/
theorem upperSemicontinuous_finrank_homology_extendScalars {j k : ι} (hk : c.next j = k)
    [Module.Finite R (K.X j)] [Module.Projective R (K.X k)] :
    UpperSemicontinuous fun p : PrimeSpectrum R ↦ finrank p.asIdeal.ResidueField
      ((((ModuleCat.extendScalars (algebraMap R p.asIdeal.ResidueField)).mapHomologicalComplex
        c).obj K).homology j) := by
  convert LinearMap.upperSemicontinuous_finrank_fiber_homology (K.d (c.prev j) j).hom
    (K.d j k).hom (by rw [← ModuleCat.hom_comp, K.d_comp_d, ModuleCat.hom_zero]) using 2 with p
  obtain ⟨e⟩ := K.nonempty_linearEquiv_homology_extendScalars p.asIdeal.ResidueField rfl hk
  exact e.finrank_eq

end HomologicalComplex
