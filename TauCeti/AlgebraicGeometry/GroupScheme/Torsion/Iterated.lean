/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.GroupScheme.Torsion.Basic

/-!
# Iterated torsion of commutative group schemes

For a commutative group scheme `G` over an arbitrary base, the `m`-torsion of `G[mn]`
is canonically `G[m]`. The comparison identifies the kernel inclusion with the usual
inclusion `G[m] ⟶ G[mn]`, not just the abstract group schemes. In particular, with
`m = p^r` and `n = p`, this gives the kernel condition in the prime-power torsion tower
of an elliptic curve. No invertibility or nonvanishing hypothesis on the indices is needed.

## References

* N. M. Katz and B. Mazur, *Arithmetic Moduli of Elliptic Curves*, 2.3.1 and Chapter 5.
-/

public section

open CategoryTheory Limits MonObj
open AlgebraicGeometry

namespace TauCeti.GroupScheme

universe u

variable {S : Scheme.{u}} (G : CommGrp (Over S)) (m n : ℤ)

/-- The map from the iterated torsion to `G[m]`, obtained by forgetting the intermediate
membership in `G[mn]`. -/
private noncomputable def iteratedToTorsion :
    (torsion (torsionCommGrp G (m * n)) m).X ⟶ (torsion G m).X :=
  torsionLift (torsionι (torsionCommGrp G (m * n)) m ≫ torsionι G (m * n)) (by
    rw [← GrpObj.zpow_comp, torsionι_zpow, one_comp])

/-- The lift of the usual torsion inclusion to the iterated torsion. -/
private noncomputable def torsionToIterated :
    (torsion G m).X ⟶ (torsion (torsionCommGrp G (m * n)) m).X :=
  torsionLift (torsionInclusion G m n) (torsionInclusion_zpow G m n)

private instance : IsMonHom (iteratedToTorsion G m n) := by
  unfold iteratedToTorsion
  infer_instance

/-- The `m`-torsion of `G[mn]` is canonically the `m`-torsion of `G`, including over
nonreduced bases and when the residue characteristic divides either index. -/
noncomputable def torsionIteratedIso :
    torsion (torsionCommGrp G (m * n)) m ≅ torsion G m :=
  Grp.mkIso' {
    hom := iteratedToTorsion G m n
    inv := torsionToIterated G m n
    hom_inv_id := by
      apply torsion_hom_ext (torsionCommGrp G (m * n))
      apply torsion_hom_ext G
      simp [iteratedToTorsion, torsionToIterated]
    inv_hom_id := by
      apply torsion_hom_ext G
      simp [iteratedToTorsion, torsionToIterated] }

/-- Forgetting both torsion conditions is the same as applying the comparison and then
forgetting the single torsion condition. -/
@[reassoc (attr := simp)]
theorem torsionIteratedIso_hom_hom_hom_torsionι :
    (torsionIteratedIso G m n).hom.hom.hom ≫ torsionι G m =
      torsionι (torsionCommGrp G (m * n)) m ≫ torsionι G (m * n) :=
  torsionLift_ι _ _

/-- Under the inverse comparison, the kernel inclusion is the usual inclusion of torsion
levels. -/
@[reassoc (attr := simp)]
theorem torsionIteratedIso_inv_hom_hom_torsionι :
    (torsionIteratedIso G m n).inv.hom.hom ≫
      torsionι (torsionCommGrp G (m * n)) m = torsionInclusion G m n :=
  torsionLift_ι _ _

/-- The usual inclusion of torsion levels realizes `G[m]` as the scheme-theoretic kernel
of multiplication by `m` on `G[mn]`. -/
theorem isPullback_torsionInclusion_zpow :
    IsPullback (torsionInclusion G m n) (CartesianMonoidalCategory.toUnit _)
      (𝟙 (torsion G (m * n)).X ^ m) η[(torsion G (m * n)).X] := by
  let e : (torsion G m).X ≅ (torsion (torsionCommGrp G (m * n)) m).X :=
    (Grp.forget (Over S)).mapIso (torsionIteratedIso G m n).symm
  apply (isPullback_torsionι (torsionCommGrp G (m * n)) m).of_iso'
    e (Iso.refl _) (Iso.refl _) (Iso.refl _)
  · simpa only [e, Functor.mapIso_hom, Iso.symm_hom, Grp.forget_map,
      Iso.refl_hom, Category.comp_id] using torsionIteratedIso_inv_hom_hom_torsionι G m n
  · simp only [Iso.refl_hom, Category.comp_id, CartesianMonoidalCategory.comp_toUnit]
  · simp
  · simp

/-- The iterated-torsion comparison commutes with every homomorphism of commutative group
schemes. -/
@[reassoc]
theorem torsionIteratedIso_hom_hom_hom_naturality {H : CommGrp (Over S)} (f : G ⟶ H) :
    torsionMap (CommGrp.homMk (torsionMap f (m * n))) m ≫
        (torsionIteratedIso H m n).hom.hom.hom =
      (torsionIteratedIso G m n).hom.hom.hom ≫ torsionMap f m := by
  apply torsion_hom_ext H
  simp only [Category.assoc, torsionIteratedIso_hom_hom_hom_torsionι,
    torsionIteratedIso_hom_hom_hom_torsionι_assoc, torsionMap_ι, torsionMap_ι_assoc,
    CommGrp.homMk_hom_hom_hom]

end TauCeti.GroupScheme
