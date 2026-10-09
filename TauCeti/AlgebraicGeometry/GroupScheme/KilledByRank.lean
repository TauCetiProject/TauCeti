/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.GroupScheme.FiniteFlat
import TauCeti.Algebra.AlgebraicGroup.CommHopfAlgCat.SchemePoints
import TauCeti.Algebra.AlgebraicGroup.KilledByRank
import TauCeti.AlgebraicGeometry.AffineGroupScheme.CartierDuality.Rank

/-!
# Finite locally free commutative group schemes are killed by their rank

Let `G` be a finite locally free commutative group scheme over an arbitrary scheme `S`, of
constant rank `n`. Then every point of `G` is killed by `n`: for every scheme `X` over `S` and
every `x : X ⟶ G` over `S`, the `n`-th power of `x` in the group of `X`-valued points is the
unit. This is Deligne's theorem. It is what makes a point of exact order `n` of an elliptic curve
an `n`-torsion point, and the kernel of an isogeny of degree `n` a subgroup killed by `n`.

The affine case is `TauCeti.AlgHom.convPow_eq_one_of_rankAtStalk`, stated for a commutative and
cocommutative Hopf algebra which is finite projective of constant rank. Over `Spec R`, the
group scheme `G` is the Hopf spectrum of its coordinate Hopf algebra
(`TauCeti.FiniteLocallyFreeCommAffineGroupSchemeCat.hopfSpecCoordinateHopfAlgebraIso`), whose
local rank is the rank of `G` (`finrank_eq_rankAtStalk_coordinateHopfAlgebra`), and Mathlib's
`AlgebraicGeometry.Spec.mapMulEquiv` identifies the points of a Hopf spectrum with the
convolution group. Over a general base, it suffices to show that the identity of `G` is killed
by `n`. This is checked on the cover of `G` by its base changes to the affine opens of `S`:
base change is a monoidal functor, so it commutes with powers in the groups of points.

## Main results

* `TauCeti.AlgebraicGeometry.FiniteFlatCommGroupScheme.pow_eq_one_of_finrank`: a finite locally
  free commutative group scheme of constant rank `n` is killed by `n`.

## References

* J. Tate and F. Oort, *Group schemes of prime order*, Ann. Sci. École Norm. Sup. (4) 3 (1970),
  1–21, §1.
* N. M. Katz and B. Mazur, *Arithmetic Moduli of Elliptic Curves*, §1.12.
-/

public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite WithConv
open scoped CategoryTheory.MonObj CategoryTheory.Obj

universe u

namespace TauCeti.AlgebraicGeometry

namespace FiniteFlatCommGroupScheme

/-- The identity of the Hopf spectrum of a commutative and cocommutative Hopf algebra which is
finite projective of constant rank `n` is killed by `n`. -/
private theorem pow_id_spec_eq_one {R H : Type u} [CommRing R] [CommRing H] [HopfAlgebra R H]
    [Coalgebra.IsCocomm R H] [Module.Finite R H] [Module.Projective R H] {n : ℕ}
    (hn : ∀ p, Module.rankAtStalk (R := R) H p = n) :
    (𝟙 ((Spec (CommRingCat.of H)).asOver (Spec (CommRingCat.of R)))) ^ n = 1 := by
  have h : AlgebraicGeometry.Spec.mapMulEquiv (toConv (AlgHom.id R H)) = 𝟙 _ := by
    apply Over.OverMorphism.ext
    rw [CommHopfAlgCat.mapMulEquiv_left]
    simp
    -- Both sides are the identity of `Spec H`, the underlying scheme of `(Spec H).asOver _`.
    rfl
  rw [← h, ← map_pow, TauCeti.AlgHom.convPow_eq_one_of_rankAtStalk hn, map_one]

/-- The identity of a finite locally free commutative group scheme of constant rank `n` over an
affine base is killed by `n`. -/
private theorem pow_id_eq_one_of_isAffine {R : CommRingCat.{u}} (A : Grp (Over (Spec R)))
    [IsFinite A.X.hom] [Flat A.X.hom] [LocallyOfFinitePresentation A.X.hom] [IsCommMonObj A.X]
    {n : ℕ} (hn : ∀ s, A.X.hom.finrank s = n) : (𝟙 A.X) ^ n = 1 := by
  have : IsAffine A.X.left := isAffine_of_isAffineHom A.X.hom
  let G' : FiniteLocallyFreeCommAffineGroupSchemeCat (CommRingCat.of R) :=
    ⟨⟨A, (affineGroupSchemeProperty_iff _).mpr ‹_›⟩,
      (finiteLocallyFreeCommAffineGroupSchemeProperty_iff _ _).mpr
        ⟨‹_›, ‹_›, ‹_›, ‹_›⟩⟩
  let H := FiniteLocallyFreeCommAffineGroupSchemeCat.coordinateHopfAlgebra R G'
  -- `A` is the Hopf spectrum of its coordinate Hopf algebra `H`.
  let e : (hopfSpec (CommRingCat.of R)).obj (op H.obj) ≅ A :=
    ((commHopfAlgCatOpEquivAffineGroupSchemeCat.functorCompιIso _).app (op H.obj)).symm ≪≫
      (affineGroupSchemeProperty _).ι.mapIso
        (FiniteLocallyFreeCommAffineGroupSchemeCat.hopfSpecCoordinateHopfAlgebraIso R G')
  have hH : ∀ p, Module.rankAtStalk (R := R) H p = n := fun p => by
    rw [← FiniteLocallyFreeCommAffineGroupSchemeCat.finrank_eq_rankAtStalk_coordinateHopfAlgebra
      R G' p]
    exact hn p
  -- The Hopf spectrum is the group object on `(Spec H).asOver (Spec R)` by
  -- `hopfSpec_obj_eq_asOver`, which holds by `rfl`; rewriting along it is blocked by the
  -- dependent group-object instance, so the comparison is made by `exact`.
  have h1 : (𝟙 ((hopfSpec (CommRingCat.of R)).obj (op H.obj)).X) ^ n = 1 :=
    pow_id_spec_eq_one (H := H) hH
  have hφ : e.hom.hom.hom ^ n = 1 := by
    rw [← Category.id_comp e.hom.hom.hom, ← MonObj.pow_comp, h1, MonObj.one_comp]
  calc (𝟙 A.X) ^ n = (e.inv.hom.hom ≫ e.hom.hom.hom) ^ n := by
        rw [← Grp.comp_hom_hom, e.inv_hom_id, Grp.id_hom_hom]
    _ = e.inv.hom.hom ≫ e.hom.hom.hom ^ n := (MonObj.comp_pow _ _ _).symm
    _ = 1 := by rw [hφ, MonObj.comp_one]

/-- **Deligne's theorem.** Let `G` be a finite locally free commutative group scheme over `S`
whose rank is `n` at every point of `S`. Then every point `x : X ⟶ G` over `S` is killed by
`n`: its `n`-th power in the group of `X`-valued points of `G` is the unit. -/
theorem pow_eq_one_of_finrank {S : Scheme.{u}} (G : FiniteFlatCommGroupScheme S) {n : ℕ}
    (hn : ∀ s, G.structureMap.finrank s = n) {X : Over S} (x : X ⟶ G.toOver) : x ^ n = 1 := by
  -- It suffices to treat the universal point, the identity of `G`.
  suffices h : (𝟙 G.toOver) ^ n = 1 by
    rw [← Category.comp_id x, ← MonObj.comp_pow, h, MonObj.comp_one]
  apply Over.OverMorphism.ext
  -- Check the equality on the base changes of `G` to the affine opens of `S`.
  refine Scheme.Cover.hom_ext (S.affineCover.pullback₁ G.structureMap) _ _ fun i => ?_
  let g := S.affineCover.f i
  let A := (Over.pullback g).mapGrp.obj (Grp.mk G.toOver)
  have hfin : IsFinite A.X.hom :=
    inferInstanceAs (IsFinite (pullback.snd G.structureMap g))
  have hflat : Flat A.X.hom :=
    inferInstanceAs (Flat (pullback.snd G.structureMap g))
  have hlfp : LocallyOfFinitePresentation A.X.hom :=
    inferInstanceAs (LocallyOfFinitePresentation (pullback.snd G.structureMap g))
  have hcomm : IsCommMonObj A.X :=
    Functor.isCommMonObj_obj (F := Over.pullback g) (M := G.toOver)
  -- The instances are passed explicitly: they are stated for the let-bound `A`.
  have hG : (𝟙 A.X) ^ n = 1 := @pow_id_eq_one_of_isAffine _ A hfin hflat hlfp hcomm n fun y =>
    (Scheme.Hom.finrank_pullback_snd G.structureMap g y).trans (hn _)
  have key : (Over.pullback g).map ((𝟙 G.toOver) ^ n) = (Over.pullback g).map 1 := by
    rw [← Functor.homMonoidHom_apply, map_pow, Functor.homMonoidHom_apply,
      CategoryTheory.Functor.map_id, Functor.map_one]
    exact hG
  have := congrArg (fun k => k.left ≫ pullback.fst G.structureMap g) key
  simp only [Over.pullback_map_left, Over.mk_hom, pullback.lift_fst] at this
  -- The `i`-th map of the pulled-back cover is the first projection `pullback.fst _ g`.
  exact this

end FiniteFlatCommGroupScheme

end TauCeti.AlgebraicGeometry
