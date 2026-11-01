/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.EllipticCurve.Scheme.Geom.Isogeny
import TauCeti.AlgebraicGeometry.GroupScheme.Cokernel

/-!
# The factorisation dual of an isogeny

For an isogeny `f : E ⟶ E'` of constant degree `n`, its kernel is killed by `n`.
Multiplication by `n` therefore factors uniquely through `f`, giving a homomorphism
`factorisationDual f hf : E' ⟶ E`. Both composites are multiplication by `n`, on their
respective elliptic curves. The construction uses fpqc descent, so also applies in
characteristics dividing the degree and over nonreduced bases.

This is the factorisation construction, before comparison with the Picard dual.

## References

* N. M. Katz and B. Mazur, *Arithmetic Moduli of Elliptic Curves*, §2.4.
-/

public section

open CategoryTheory Limits AlgebraicGeometry MonObj

universe u

namespace TauCeti.AlgebraicGeometry.EllipticCurveGeom

variable {S : Scheme.{u}} {E E' : EllipticCurveGeom S}
  (f : E.toCommGrp ⟶ E'.toCommGrp) {n : ℕ}

private theorem kernel_ι_comp_natCast_eq_zero (hf : GroupScheme.IsogenyOfDegree f.hom n) :
    kernel.ι f.hom ≫ (n : End E.toCommGrp).asHom.hom = 0 := by
  apply Grp.hom_ext
  rw [Grp.comp_hom_hom, CommGrp.natCast_hom_hom_hom, MonObj.comp_pow,
    Category.comp_id, hf.kernel_ι_pow_eq_one]
  simp [CategoryTheory.Hom.one_def]

private noncomputable def factorisationLift (hf : GroupScheme.IsogenyOfDegree f.hom n) :=
  have := hf.isIsogeny.isFinite
  have := hf.isIsogeny.flat
  have := hf.isIsogeny.surjective
  CokernelCofork.IsColimit.desc' (GroupScheme.isColimitKernelCofork f.hom)
    (n : End E.toCommGrp).asHom.hom (kernel_ι_comp_natCast_eq_zero f hf)

/-- The factorisation dual of a constant-degree isogeny, characterized by
`comp_factorisationDual`. It is a homomorphism from `E'` to `E`. -/
noncomputable def factorisationDual (hf : GroupScheme.IsogenyOfDegree f.hom n) :
    E'.toCommGrp ⟶ E.toCommGrp :=
  InducedCategory.homMk (factorisationLift f hf).1

/-- Composing `f : E ⟶ E'` with its factorisation dual `E' ⟶ E` is `[n]` on `E`. -/
@[reassoc (attr := simp)]
theorem comp_factorisationDual (hf : GroupScheme.IsogenyOfDegree f.hom n) :
    f ≫ factorisationDual f hf = (n : End E.toCommGrp).asHom :=
  InducedCategory.hom_ext (factorisationLift f hf).2

/-- A homomorphism `E' ⟶ E` whose composite with `f` is `[n]` equals the factorisation dual. -/
theorem eq_factorisationDual (hf : GroupScheme.IsogenyOfDegree f.hom n)
    (g : E'.toCommGrp ⟶ E.toCommGrp) (hg : f ≫ g = (n : End E.toCommGrp).asHom) :
    g = factorisationDual f hf := by
  have := hf.isIsogeny.flat
  have := hf.isIsogeny.surjective
  have := Flat.epi_of_flat_of_surjective f.hom.hom.hom.left
  apply hom_ext_left
  apply (cancel_epi f.hom.hom.hom.left).mp
  exact congrArg (fun k ↦ k.hom.hom.hom.left) (hg.trans (comp_factorisationDual f hf).symm)

/-- Composing the factorisation dual `E' ⟶ E` with `f : E ⟶ E'` is `[n]` on `E'`. -/
@[reassoc (attr := simp)]
theorem factorisationDual_comp (hf : GroupScheme.IsogenyOfDegree f.hom n) :
    factorisationDual f hf ≫ f = (n : End E'.toCommGrp).asHom := by
  have := hf.isIsogeny.flat
  have := hf.isIsogeny.surjective
  have := Flat.epi_of_flat_of_surjective f.hom.hom.hom.left
  apply hom_ext_left
  apply (cancel_epi f.hom.hom.hom.left).mp
  have h := congrArg (fun k ↦ k.hom.hom.hom.left)
    (congrArg (fun k ↦ k ≫ f) (comp_factorisationDual f hf))
  simpa only [CommGrp.comp_hom, Grp.comp_hom_hom, Over.comp_left, Category.assoc,
    natCast_hom_hom_hom, mulBy_comp] using h

end TauCeti.AlgebraicGeometry.EllipticCurveGeom
