/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.Cohomology.ProjectiveSpectrum
public import TauCeti.AlgebraicGeometry.ProjectiveSpectrum.SymmetricAlgebra

/-!
# Cohomology above the dimension of projective space

A quasi-coherent sheaf on projective `d`-space over any ring has zero cohomology in degrees
strictly greater than `d`. More generally, if `r` linear forms span a module `M`, then every
scheme affine over `Proj (Sym M)` has vanishing quasi-coherent cohomology in degrees at least
`r`. No freeness of `M`, Noetherianity of the base, or finiteness of the coefficients is needed.

The spanning forms give an affine cover with `r` members. Separatedness makes its finite
intersections affine, so the finite Leray-cover bound applies. This supplies the high-degree
vanishing part of the cohomology calculation for twisting sheaves, and also applies to closed
subschemes of projective space with arbitrary quasi-coherent coefficients. The same bound holds
for the higher direct images to the coefficient spectrum, by applying the bound after restriction
to affine opens of the base.

## References

* R. Hartshorne, *Algebraic Geometry*, Theorem III.5.1 and Exercise III.4.8.
* The Stacks Project, Lemma 30.4.2 (tag 01XD).
-/

public section

open CategoryTheory Limits AlgebraicGeometry
open TauCeti TauCeti.AlgebraicGeometry.Scheme.Modules

universe u

namespace AlgebraicGeometry.Scheme.Hom

/-- A scheme affine over `Proj (Sym M)` has no quasi-coherent cohomology in degrees at least
the size of a nonempty finite spanning family of `M`. In particular this applies to any closed
subscheme of projective space, without a flatness hypothesis. -/
theorem subsingleton_cohomology_of_card_le_of_isAffineHom_to_projSymmetricAlgebra
    {R M : Type u} [CommRing R] [AddCommMonoid M] [Module R M]
    {X : Scheme.{u}} (f : X ⟶ Proj (SymmetricAlgebra.homogeneousSubmodule R M))
    [IsAffineHom f] {κ : Type*} [Fintype κ] [Nonempty κ] (v : κ → M)
    (hv : Submodule.span R (Set.range v) = ⊤)
    (F : X.Modules) [F.IsQuasicoherent]
    (q : ℕ) (hq : Fintype.card κ ≤ q) : Subsingleton (Cohomology F q) := by
  classical
  refine f.subsingleton_cohomology_of_card_le_of_isAffineHom_to_proj Finset.univ_nonempty
    (fun i ↦ _root_.SymmetricAlgebra.ι R M (v i))
    (fun i _ ↦ ⟨1, by decide, SymmetricAlgebra.ι_mem_homogeneousSubmodule R M (v i)⟩)
    ?_ F q (by simpa using hq)
  simpa using SymmetricAlgebra.iSup_basicOpen_ι_eq_top R M v hv

/-- For a scheme affine over `Proj (Sym M)`, the higher direct images of any quasi-coherent
sheaf to `Spec R` vanish in degrees at least the size of a nonempty finite spanning family of
`M`. No flatness or Noetherian hypothesis is required. -/
theorem isZero_higherDirectImage_of_card_le_of_isAffineHom_to_projSymmetricAlgebra
    {R M : Type u} [CommRing R] [AddCommMonoid M] [Module R M]
    {X : Scheme.{u}} (f : X ⟶ Proj (SymmetricAlgebra.homogeneousSubmodule R M))
    [IsAffineHom f] {κ : Type*} [Fintype κ] [Nonempty κ] (v : κ → M)
    (hv : Submodule.span R (Set.range v) = ⊤)
    (F : X.Modules) [F.IsQuasicoherent] (q : ℕ) (hq : Fintype.card κ ≤ q) :
    IsZero (((f ≫ SymmetricAlgebra.projToSpec R M).higherDirectImage q).obj F) := by
  classical
  refine f.isZero_higherDirectImage_of_card_le_of_isAffineHom_to_proj
    (SymmetricAlgebra.projToSpec R M) Finset.univ_nonempty
    (fun i ↦ _root_.SymmetricAlgebra.ι R M (v i))
    (fun i _ ↦ ⟨1, by decide, SymmetricAlgebra.ι_mem_homogeneousSubmodule R M (v i)⟩)
    ?_ F q (by simpa using hq)
  simpa using SymmetricAlgebra.iSup_basicOpen_ι_eq_top R M v hv

end AlgebraicGeometry.Scheme.Hom

namespace Module.Basis

open TauCeti.SymmetricAlgebra

variable {R M : Type u} [CommRing R] [AddCommMonoid M] [Module R M]

/-- If `M` has a finite basis indexed by `κ`, then quasi-coherent cohomology on `Proj (Sym M)`
vanishes in degrees at least `card κ`, that is, above the relative projective dimension.
The basis is required to be nonempty; no hypothesis on the coefficient ring is imposed. -/
theorem subsingleton_cohomology_proj_of_card_le {κ : Type*} [Fintype κ] [Nonempty κ]
    (b : Module.Basis κ R M) (F : (Proj (homogeneousSubmodule R M)).Modules)
    [F.IsQuasicoherent] (q : ℕ) (hq : Fintype.card κ ≤ q) :
    Subsingleton (Cohomology F q) :=
  Scheme.Hom.subsingleton_cohomology_of_card_le_of_isAffineHom_to_projSymmetricAlgebra
    (𝟙 _) b b.span_eq F q hq

/-- For a nonempty finite basis of `M`, the higher direct images of a quasi-coherent sheaf
under `Proj (Sym M) ⟶ Spec R` vanish in degrees at least the size of the basis. -/
theorem isZero_higherDirectImage_projToSpec_of_card_le
    {κ : Type*} [Fintype κ] [Nonempty κ]
    (b : Module.Basis κ R M) (F : (Proj (homogeneousSubmodule R M)).Modules)
    [F.IsQuasicoherent] (q : ℕ) (hq : Fintype.card κ ≤ q) :
    IsZero (((projToSpec R M).higherDirectImage q).obj F) := by
  simpa only [Category.id_comp] using
    Scheme.Hom.isZero_higherDirectImage_of_card_le_of_isAffineHom_to_projSymmetricAlgebra
      (𝟙 _) b b.span_eq F q hq

end Module.Basis
