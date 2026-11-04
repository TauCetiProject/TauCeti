/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.GroupScheme.Degree
public import TauCeti.CategoryTheory.Monoidal.Cartesian.CommGrp
import TauCeti.AlgebraicGeometry.GroupScheme.Cokernel

/-!
# The factorisation dual of an isogeny of commutative group schemes

For a locally finitely presented isogeny `f : A ⟶ B` of commutative group schemes of
constant degree `n`, its kernel is killed by `n`.
Multiplication by `n` therefore factors uniquely through `f`, giving a homomorphism
`factorisationDual f hf : B ⟶ A`. Both composites are multiplication by `n`, on their
respective group schemes. The construction uses fpqc descent, so also applies in
characteristics dividing the degree and over nonreduced bases.

For elliptic curves, apply this API to `A = E.toCommGrp` and `B = E'.toCommGrp`;
local finite presentation is automatic. This gives the factorisation construction before
comparison with the Picard dual.

## References

* N. M. Katz and B. Mazur, *Arithmetic Moduli of Elliptic Curves*, §2.4.
-/

public section

open CategoryTheory Limits AlgebraicGeometry MonObj

universe u

namespace TauCeti.GroupScheme

variable {S : Scheme.{u}} {A B : CommGrp (Over S)}
  (f : A ⟶ B) [LocallyOfFinitePresentation f.hom.hom.hom.left] {n : ℕ}

private theorem kernel_ι_comp_natCast_eq_zero (hf : IsogenyOfDegree f.hom n) :
    kernel.ι f.hom ≫ (n : End A).asHom.hom = 0 := by
  apply Grp.hom_ext
  rw [Grp.comp_hom_hom, CommGrp.natCast_hom_hom_hom, MonObj.comp_pow,
    Category.comp_id, hf.kernel_ι_pow_eq_one]
  simp [CategoryTheory.Hom.one_def]

private noncomputable def factorisationLift (hf : IsogenyOfDegree f.hom n) :=
  have := hf.isIsogeny.isFinite
  have := hf.isIsogeny.flat
  have := hf.isIsogeny.surjective
  CokernelCofork.IsColimit.desc' (isColimitKernelCofork f.hom)
    (n : End A).asHom.hom (kernel_ι_comp_natCast_eq_zero f hf)

/-- The factorisation dual of a constant-degree isogeny, characterized by
`comp_factorisationDual`. It is a homomorphism from `B` to `A`. -/
noncomputable def factorisationDual (hf : IsogenyOfDegree f.hom n) :
    B ⟶ A :=
  InducedCategory.homMk (factorisationLift f hf).1

/-- Composing `f : A ⟶ B` with its factorisation dual `B ⟶ A` is `[n]` on `A`. -/
@[reassoc (attr := simp)]
theorem comp_factorisationDual (hf : IsogenyOfDegree f.hom n) :
    f ≫ factorisationDual f hf = (n : End A).asHom :=
  InducedCategory.hom_ext (factorisationLift f hf).2

/-- A homomorphism `B ⟶ A` whose composite with `f` is `[n]` equals the factorisation dual. -/
theorem eq_factorisationDual (hf : IsogenyOfDegree f.hom n)
    (g : B ⟶ A) (hg : f ≫ g = (n : End A).asHom) :
    g = factorisationDual f hf := by
  have := hf.isIsogeny.flat
  have := hf.isIsogeny.surjective
  have := Flat.epi_of_flat_of_surjective f.hom.hom.hom.left
  apply CommGrp.hom_ext
  apply Over.OverMorphism.ext
  apply (cancel_epi f.hom.hom.hom.left).mp
  exact congrArg (fun k ↦ k.hom.hom.hom.left) (hg.trans (comp_factorisationDual f hf).symm)

/-- Composing the factorisation dual `B ⟶ A` with `f : A ⟶ B` is `[n]` on `B`. -/
@[reassoc (attr := simp)]
theorem factorisationDual_comp (hf : IsogenyOfDegree f.hom n) :
    factorisationDual f hf ≫ f = (n : End B).asHom := by
  have := hf.isIsogeny.flat
  have := hf.isIsogeny.surjective
  have := Flat.epi_of_flat_of_surjective f.hom.hom.hom.left
  have : Epi f.hom.hom.hom := Over.epi_of_epi_left _
  apply CommGrp.hom_ext
  apply (cancel_epi f.hom.hom.hom).mp
  have h := congrArg (fun k ↦ k.hom.hom.hom)
    (congrArg (fun k ↦ k ≫ f) (comp_factorisationDual f hf))
  simpa only [CommGrp.comp_hom, Grp.comp_hom_hom, Category.assoc,
    CommGrp.natCast_hom_hom_hom, MonObj.pow_comp, MonObj.comp_pow,
    Category.id_comp, Category.comp_id] using h

end TauCeti.GroupScheme
