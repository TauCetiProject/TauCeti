/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.QuadraticOrthogonal.Similitude
public import TauCeti.Algebra.AlgebraicGroup.HopfIdeal.Points.Kernel
public import TauCeti.Algebra.AlgebraicGroup.HopfIdeal.Points.Naturality
public import TauCeti.Algebra.AlgebraicGroup.CommHopfAlgCat.Yoneda
public import TauCeti.Algebra.AlgebraicGroup.MultiplicativeGroup.Basic

/-!
# The orthogonal group scheme is the kernel of the multiplier

For a commutative ring `R` and a quadratic form `q` on `Rⁿ`, the orthogonal group scheme `O(q)`
(`TauCeti.QuadraticOrthogonal`) is the kernel of the multiplier character
`ν : GO(q) → 𝔾_m` of the orthogonal similitude group scheme (`TauCeti.QuadraticSimilitude`), as
group schemes and not only on points. The kernel of `ν` is the closed subgroup scheme of `GO(q)`
cut out by the kernel Hopf ideal of its coordinate morphism
(`TauCeti.CommHopfAlgCat.kernelHopfIdeal`), and its coordinate Hopf algebra is isomorphic to that
of `O(q)`.

The isomorphism is built on functors of points. A point of `GO(q)` kills the kernel Hopf ideal
exactly when its similitude `(g, c)` has `c = 1`
(`TauCeti.CommHopfAlgCat.mapPointsFunctor_app_eq_one_iff`), and `(g, 1) ↦ g` identifies these
with the points of `O(q)` (`TauCeti.QuadraticSimilitude.kerMultiplierPointsMulEquiv`), naturally
in the value algebra. By Yoneda (`TauCeti.CommHopfAlgCat.pointsFunctor` is fully faithful) the
natural isomorphism of functors of points comes from an isomorphism of coordinate Hopf algebras.
Nothing is assumed of `q` or of `2`.

## Main declarations

* `TauCeti.QuadraticSimilitude.multiplierKernelHopfIdeal`: the Hopf ideal of `ker ν` in `O(GO(q))`.
* `TauCeti.QuadraticSimilitude.mem_quotientPointsSubgroup_multiplierKernelHopfIdeal_iff`: its
  points are the similitudes with multiplier `1`.
* `TauCeti.QuadraticSimilitude.multiplierKernelPointsIso`: the functor of points of `ker ν` is
  that of `O(q)`.
* `TauCeti.QuadraticSimilitude.multiplierKernelCoordinateIso`: `O(O(q)) ≅ O(GO(q)) ⧸ I_{ker ν}`.

## References

* B. Conrad, *Reductive group schemes*, Appendix C, for orthogonal group schemes of quadratic
  spaces over rings.
-/

public section

open CategoryTheory WithConv

namespace TauCeti.QuadraticSimilitude

universe u

variable (R : Type u) [CommRing R] (n : ℕ) (q : QuadraticForm R (Fin n → R))

/-- The Hopf ideal of `GO(q)` cutting out the kernel of the multiplier `ν : GO(q) → 𝔾_m`: the
kernel Hopf ideal of the multiplier coordinate morphism. -/
noncomputable def multiplierKernelHopfIdeal : HopfIdeal R (coordinateHopfAlgebra R n q) :=
  CommHopfAlgCat.kernelHopfIdeal (multiplierCoordinateMap R n q)

/-- `multiplierKernelHopfIdeal` is the kernel Hopf ideal of the multiplier coordinate morphism. -/
theorem multiplierKernelHopfIdeal_def :
    multiplierKernelHopfIdeal R n q =
      CommHopfAlgCat.kernelHopfIdeal (multiplierCoordinateMap R n q) :=
  (rfl)

/-- A point of `GO(q)` lies in the kernel of the multiplier, as cut out by
`multiplierKernelHopfIdeal`, exactly when its similitude has multiplier `1`. -/
@[simp]
theorem mem_quotientPointsSubgroup_multiplierKernelHopfIdeal_iff {A : Type u} [CommRing A]
    [Algebra R A]
    (f : HopfAlgebra.points (R := R) (H := coordinateHopfAlgebra R n q) (CommAlgCat.of R A)) :
    f ∈ CommHopfAlgCat.quotientPointsSubgroup (coordinateHopfAlgebra R n q)
        (multiplierKernelHopfIdeal R n q) (CommAlgCat.of R A) ↔
      pointsMulEquiv R n q (A := A) f ∈ (multiplierPoints R n q A).ker := by
  rw [multiplierKernelHopfIdeal_def, ← CommHopfAlgCat.mapPointsFunctor_app_eq_one_iff,
    ← MulEquiv.map_eq_one_iff MultiplicativeGroup.pointsMulEquiv, MonoidHom.mem_ker,
    ← Units.val_eq_one, ← Units.val_eq_one, multiplierPoints_pointsMulEquiv,
    MultiplicativeGroup.pointsMulEquiv_apply, laurentEvalEquiv_symm_apply, ofConv_toConv,
    AlgHom.comp_apply, BialgHom.coe_toAlgHom]

/-- The points of `GO(q)` whose similitude has multiplier `1`. -/
noncomputable def multiplierKernelPoints (A : CommAlgCat.{u} R) :
    Subgroup (HopfAlgebra.points (R := R) (H := coordinateHopfAlgebra R n q) A) :=
  (multiplierPoints R n q A).ker.comap (pointsMulEquiv R n q (A := A)).toMonoidHom

/-- Membership in `multiplierKernelPoints` means having multiplier `1`. -/
@[simp]
theorem mem_multiplierKernelPoints_iff (A : CommAlgCat.{u} R)
    (f : HopfAlgebra.points (R := R) (H := coordinateHopfAlgebra R n q) A) :
    f ∈ multiplierKernelPoints R n q A ↔
      pointsMulEquiv R n q (A := A) f ∈ (multiplierPoints R n q A).ker :=
  Iff.rfl

/-- The points of `O(q)` attached to the points of `GO(q)` with multiplier `1`. -/
noncomputable def multiplierKernelPointsMulEquiv (A : CommAlgCat.{u} R) :
    multiplierKernelPoints R n q A ≃*
      HopfAlgebra.points (R := R) (H := QuadraticOrthogonal.coordinateHopfAlgebra R n q) A :=
  (((pointsMulEquiv R n q (A := A)).subgroupMap (multiplierKernelPoints R n q A)).trans
    (MulEquiv.subgroupCongr (Subgroup.map_comap_eq_self_of_surjective
      (pointsMulEquiv R n q (A := A)).surjective _))).trans
    ((kerMultiplierPointsMulEquiv R n q A).trans
      (QuadraticOrthogonal.pointsMulEquiv R n q A).symm)

/-- The point of `O(q)` attached to a point of `GO(q)` with multiplier `1` is its matrix. -/
@[simp]
theorem coe_pointsMulEquiv_multiplierKernelPointsMulEquiv (A : CommAlgCat.{u} R)
    (f : multiplierKernelPoints R n q A) :
    (QuadraticOrthogonal.pointsMulEquiv R n q A (multiplierKernelPointsMulEquiv R n q A f) :
        GL (Fin n) A) =
      ((pointsMulEquiv R n q (A := A) f : pointsSubgroup R n q A) : GL (Fin n) A × Aˣ).1 := by
  simp only [multiplierKernelPointsMulEquiv, MulEquiv.trans_apply, MulEquiv.apply_symm_apply,
    coe_kerMultiplierPointsMulEquiv]
  exact congrArg (fun p : pointsSubgroup R n q A ↦ (p : GL (Fin n) A × Aˣ).1)
    ((MulEquiv.subgroupCongr_apply _ _).trans (MulEquiv.coe_subgroupMap_apply _ _ f))

/-- The point of `GO(q)` attached to a point `g` of `O(q)` is the similitude `(g, 1)`. -/
@[simp]
theorem coe_pointsMulEquiv_multiplierKernelPointsMulEquiv_symm (A : CommAlgCat.{u} R)
    (g : HopfAlgebra.points (R := R) (H := QuadraticOrthogonal.coordinateHopfAlgebra R n q) A) :
    ((pointsMulEquiv R n q (A := A) ((multiplierKernelPointsMulEquiv R n q A).symm g :
        HopfAlgebra.points (R := R) (H := coordinateHopfAlgebra R n q) A) :
          pointsSubgroup R n q A) : GL (Fin n) A × Aˣ) =
      ((QuadraticOrthogonal.pointsMulEquiv R n q A g : GL (Fin n) A), 1) := by
  rw [← coe_kerMultiplierPointsMulEquiv_symm]
  simp only [multiplierKernelPointsMulEquiv, MulEquiv.symm_trans_apply, MulEquiv.symm_symm]
  rw [← MulEquiv.coe_subgroupMap_apply, MulEquiv.apply_symm_apply]
  exact congrArg (fun p : pointsSubgroup R n q A ↦ (p : GL (Fin n) A × Aˣ))
    (MulEquiv.subgroupCongr_symm_apply _ _)

/-- `multiplierKernelPointsMulEquiv` commutes with change of value algebra. -/
private theorem multiplierKernelPointsMulEquiv_natural {A B : CommAlgCat.{u} R} (φ : A ⟶ B)
    (f : multiplierKernelPoints R n q A)
    (hf : AlgHom.mapValue φ.hom (f : HopfAlgebra.points (R := R)
      (H := coordinateHopfAlgebra R n q) A) ∈ multiplierKernelPoints R n q B) :
    multiplierKernelPointsMulEquiv R n q B ⟨_, hf⟩ =
      HopfAlgebra.mapPoints φ (multiplierKernelPointsMulEquiv R n q A f) := by
  apply (QuadraticOrthogonal.pointsMulEquiv R n q B).injective
  apply Subtype.ext
  rw [coe_pointsMulEquiv_multiplierKernelPointsMulEquiv,
    QuadraticOrthogonal.coe_pointsMulEquiv_mapPoints,
    coe_pointsMulEquiv_multiplierKernelPointsMulEquiv]
  have h := congrArg (fun p : pointsSubgroup R n q B ↦ (p : GL (Fin n) B × Bˣ).1)
    (pointsMulEquiv_mapValue R n q φ.hom (f : multiplierKernelPoints R n q A).val)
  rw [coe_pointsSubgroupMap] at h
  exact h

/-- **`O(q)` represents the kernel of the multiplier on `GO(q)`**: the functor of points of the
quotient of `O(GO(q))` by `multiplierKernelHopfIdeal` is naturally isomorphic to that of `O(q)`. -/
noncomputable def multiplierKernelPointsIso :
    HopfAlgebra.pointsFunctor (R := R) (H := CommHopfAlgCat.quotient
        (coordinateHopfAlgebra R n q) (multiplierKernelHopfIdeal R n q)) ≅
      HopfAlgebra.pointsFunctor (R := R) (H := QuadraticOrthogonal.coordinateHopfAlgebra R n q) :=
  (CommHopfAlgCat.quotientPointsSubgroupRepresentingIso _ _ (multiplierKernelPoints R n q)
      fun A f ↦ mem_quotientPointsSubgroup_multiplierKernelHopfIdeal_iff R n q f).trans
    (NatIso.ofComponents (fun A ↦ (multiplierKernelPointsMulEquiv R n q A).toGrpIso)
      fun {A B} φ ↦ by
      ext f
      -- Both composites compute as `multiplierKernelPointsMulEquiv` and postcomposition with
      -- `φ`; the explicitly typed naturality theorem avoids unfolding them.
      exact multiplierKernelPointsMulEquiv_natural R n q φ f _)

/-- **`O(q)` is the kernel of the multiplier `ν : GO(q) → 𝔾_m`**: the coordinate Hopf algebra of
`O(q)` is isomorphic to the quotient of that of `GO(q)` by the kernel Hopf ideal of `ν`. The
isomorphism is the Hopf morphism whose map on points is `multiplierKernelPointsIso`. -/
noncomputable def multiplierKernelCoordinateIso :
    QuadraticOrthogonal.coordinateHopfAlgebra R n q ≅
      CommHopfAlgCat.quotient (coordinateHopfAlgebra R n q) (multiplierKernelHopfIdeal R n q) :=
  ((CommHopfAlgCat.pointsFunctor (R := R)).preimageIso (multiplierKernelPointsIso R n q)).unop

/-- On points, `multiplierKernelCoordinateIso` is `multiplierKernelPointsIso`. -/
theorem mapPointsFunctor_multiplierKernelCoordinateIso_hom :
    CommHopfAlgCat.Hom.mapPointsFunctor.{u, u, u} (multiplierKernelCoordinateIso R n q).hom =
      (multiplierKernelPointsIso R n q).hom :=
  -- `mapPointsFunctor` of a coordinate morphism is by definition the map of the functor of
  -- points on its opposite, so this is `map_preimage` for that fully faithful functor.
  (CommHopfAlgCat.pointsFunctor (R := R)).map_preimage (multiplierKernelPointsIso R n q).hom

end TauCeti.QuadraticSimilitude
