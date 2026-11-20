/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Monoidal.Rigid.Basic
public import TauCeti.Algebra.AlgebraicGroup.Representation.Tannaka.Monoidal
public import TauCeti.Algebra.Coalgebra.Subcomodule.PointsAction
public import TauCeti.Algebra.HopfAlgebra.OfBijectiveEndOfPoint
import Mathlib.RingTheory.FiniteType
import TauCeti.CategoryTheory.Monoidal.Rigid.Functor

/-!
# Antipodes from rigidity of finite comodules

Let `B` be a commutative bialgebra over a commutative semiring `R`, projective as an `R`-module,
whose underlying semiring has the Orzech property (for instance, `B` a commutative ring; this
covers any commutative bialgebra over a field). If every finitely generated `B`-comodule
has a left dual in the monoidal category `FGComoduleCat R B`, then `B` has an antipode, so it is a
Hopf algebra (`TauCeti.Tannaka.hopfAlgebraOfLeftRigid`). This is the step of neutral Tannakian
reconstruction that produces the inverse of the reconstructed monoid scheme from the duals of
the category, before tensor endomorphisms are identified with tensor automorphisms.

The argument runs through the point actions of `TauCeti.Comodule.endOfPoint`. An `A`-valued point
`g` of a bialgebra `H` acts on the scalar extension `A ⊗[R] M` of every comodule `M`, naturally in
`M` and compatibly with tensor products (`TauCeti.Tannaka.endOfPointNatTrans`, a monoidal natural
endomorphism of scalar extension). A monoidal natural transformation between strong monoidal
functors is compatible with the comparisons of duals
(`CategoryTheory.NatTrans.app_comp_mapRightDualIso_hom_comp_rightAdjointMate`), so on an object `M`
with a left dual `ᘁM` the point action has a left inverse, built from the action on `ᘁM`. Over a
commutative semiring with the Orzech property (such as a commutative ring), a left-invertible
endomorphism of a finite module is bijective, so the point action on `M` is bijective
(`TauCeti.Tannaka.bijective_endOfPoint_of_hasLeftDual`).

The regular comodule `B` is the directed union of its finite subcomodules. When `B` is projective,
so that finite subcomodules cover every element, and the value algebra is flat, bijectivity
passes from finite subcomodules to the whole comodule
(`TauCeti.Comodule.bijective_endOfPoint_of_forall_finite`, in
`TauCeti.Algebra.Coalgebra.Subcomodule.PointsAction`). Applied to the universal point
`AlgHom.id R B`, this makes the universal point action on `B` bijective, and
`TauCeti.HopfAlgebra.ofBijective` turns its inverse into an antipode.

## Main declarations

* `TauCeti.Tannaka.endOfPointNatTrans`: the action of a point as a natural endomorphism of
  scalar extension of finite comodules, monoidal by
  `TauCeti.Tannaka.isMonoidal_endOfPointNatTrans`.
* `TauCeti.Tannaka.bijective_endOfPoint_of_hasLeftDual`: every point acts bijectively on a
  finite comodule with a left dual.
* `TauCeti.Tannaka.bijective_endOfPoint_id_of_leftRigid`: the universal point acts bijectively on
  the regular comodule of a left-rigid commutative bialgebra with the Orzech property.
* `TauCeti.Tannaka.hopfAlgebraOfLeftRigid`: the resulting Hopf algebra structure.
* `TauCeti.Tannaka.exists_antipode_of_rigid_finite_comodules`: the two antipode identities.

## References

* P. Deligne and J. S. Milne, *Tannakian categories*, in *Hodge cycles, motives, and Shimura
  varieties*, Lecture Notes in Math. 900 (1982), Proposition 2.16 and the proof of
  Theorem 2.11, pp. 125–131.
* J. S. Milne, *Algebraic Groups* (2017), §9.4.
-/

public section

open CategoryTheory MonoidalCategory
open scoped TensorProduct

namespace TauCeti

universe u v w x

namespace Tannaka

section NatTrans

variable (R : Type u) [CommSemiring R]
variable (H : Type v) [Semiring H] [Bialgebra R H]
variable (A : Type x) [CommSemiring A] [Algebra R A]

/-- An `A`-valued point `g` of a bialgebra acts on the scalar extension of every finite comodule
by `TauCeti.Comodule.endOfPoint`; these actions form a natural endomorphism of scalar extension.
For a Hopf algebra this is the underlying natural transformation of the automorphism
`TauCeti.Tannaka.fgPointNatIsoHom R H A g`; here no antipode is required. -/
noncomputable def endOfPointNatTrans (g : H →ₐ[R] A) :
    FGComoduleCat.scalarExtensionFunctor.{u, v, w, x} R H A ⟶
      FGComoduleCat.scalarExtensionFunctor R H A where
  app M := eqToHom (FGComoduleCat.scalarExtensionFunctor_obj R H A M) ≫
    SemimoduleCat.ofHom (Comodule.endOfPoint M g) ≫
      eqToHom (FGComoduleCat.scalarExtensionFunctor_obj R H A M).symm
  naturality M N f := by
    rw [FGComoduleCat.scalarExtensionFunctor_map]
    simp only [Category.assoc, eqToHom_trans_assoc, eqToHom_refl, Category.id_comp]
    rw [cancel_epi]
    simp only [← Category.assoc]
    rw [cancel_mono]
    simp only [← SemimoduleCat.ofHom_comp]
    exact congrArg SemimoduleCat.ofHom (Comodule.baseChange_comp_endOfPoint f.hom g).symm

/-- The components of `TauCeti.Tannaka.endOfPointNatTrans` are the point actions, transported to
the objects chosen by the scalar-extension functor. -/
theorem endOfPointNatTrans_app (g : H →ₐ[R] A) (M : FGComoduleCat.{u, v, w} R H) :
    (endOfPointNatTrans R H A g).app M =
      eqToHom (FGComoduleCat.scalarExtensionFunctor_obj R H A M) ≫
        SemimoduleCat.ofHom (Comodule.endOfPoint M g) ≫
          eqToHom (FGComoduleCat.scalarExtensionFunctor_obj R H A M).symm :=
  (rfl)

variable (A : Type u) [CommSemiring A] [Algebra R A]

/-- The action of a point is a monoidal natural endomorphism of scalar extension: it is the
identity on the tensor unit and acts diagonally on tensor products. -/
instance isMonoidal_endOfPointNatTrans (g : H →ₐ[R] A) :
    NatTrans.IsMonoidal (endOfPointNatTrans.{u, v, u, u} R H A g) := by
  have hunit : (endOfPointNatTrans.{u, v, u, u} R H A g).app (𝟙_ (FGComoduleCat R H)) = 𝟙 _ := by
    rw [endOfPointNatTrans_app]
    -- The tensor unit carries the trivial coaction, on which every point acts as the identity.
    have h : Comodule.endOfPoint (𝟙_ (FGComoduleCat.{u, v, u} R H)) g = LinearMap.id :=
      Comodule.endOfPoint_trivial (V := R) g
    rw [h]
    simp
  have : Epi ((endOfPointNatTrans.{u, v, u, u} R H A g).app (𝟙_ (FGComoduleCat R H))) := by
    rw [hunit]
    infer_instance
  exact isMonoidal_of_endomorphism_components R H A (fun M ↦ Comodule.endOfPoint M g) _
    (endOfPointNatTrans_app R H A g) fun _ _ ↦ Comodule.endOfPoint_tensor g

end NatTrans

/-- Every point of a bialgebra acts bijectively on the scalar extension of a finite comodule with a
left dual. The action on the left dual supplies a left inverse, by compatibility of monoidal
natural transformations with duals, and a left-invertible endomorphism of a finite module over a
commutative semiring with the Orzech property (for instance, a commutative ring) is bijective. -/
theorem bijective_endOfPoint_of_hasLeftDual {R : Type u} [CommSemiring R] {H : Type v}
    [Semiring H] [Bialgebra R H] {A : Type u} [CommSemiring A] [OrzechProperty A] [Algebra R A]
    (M : FGComoduleCat.{u, v, u} R H) [HasLeftDual M] (g : H →ₐ[R] A) :
    Function.Bijective (Comodule.endOfPoint M g) := by
  let F := FGComoduleCat.scalarExtensionFunctor.{u, v, u, u} R H A
  let τ := endOfPointNatTrans.{u, v, u, u} R H A g
  let _ : HasRightDual (F.obj (ᘁM)) := F.mapHasRightDual (ᘁM)
  -- `M` is the right dual of `ᘁM`, so compatibility with duals exhibits a left inverse `r` of
  -- the component of `τ` at `M`.
  let r : F.obj M ⟶ F.obj M :=
    (F.mapRightDualIso (ᘁM)).hom ≫ (τ.app (ᘁM))ᘁ ≫ (F.mapRightDualIso (ᘁM)).inv
  have hr : τ.app M ≫ r = 𝟙 _ := by
    -- The right dual `(ᘁM)ᘁ` is `M` by definition (`CategoryTheory.rightDual_leftDual` is `rfl`),
    -- so the compatibility at `ᘁM` is a statement about the component at `M`.
    have key : τ.app M ≫ (F.mapRightDualIso (ᘁM)).hom ≫ (τ.app (ᘁM))ᘁ =
        (F.mapRightDualIso (ᘁM)).hom :=
      NatTrans.app_comp_mapRightDualIso_hom_comp_rightAdjointMate τ (ᘁM)
    simp only [r, ← Category.assoc]
    rw [Category.assoc (τ.app M), key, Iso.hom_inv_id]
  -- Transport the left inverse to the explicit scalar extension `A ⊗[R] M`.
  let hM := FGComoduleCat.scalarExtensionFunctor_obj R H A M
  let r' : A ⊗[R] M →ₗ[A] A ⊗[R] M := (eqToHom hM.symm ≫ r ≫ eqToHom hM).hom
  have hr' : r' ∘ₗ Comodule.endOfPoint M g = LinearMap.id := by
    have h := congrArg (fun φ ↦ eqToHom hM.symm ≫ φ ≫ eqToHom hM) hr
    simp only [τ, endOfPointNatTrans_app, Category.assoc, eqToHom_trans_assoc, eqToHom_refl,
      Category.id_comp, eqToHom_trans] at h
    have h' := congrArg SemimoduleCat.Hom.hom h
    simpa only [r', SemimoduleCat.hom_comp, SemimoduleCat.hom_ofHom, SemimoduleCat.hom_id,
      Category.assoc] using h'
  have hleft (y : A ⊗[R] M) : r' (Comodule.endOfPoint M g y) = y :=
    LinearMap.congr_fun hr' y
  have hsurj : Function.Surjective r' := fun y ↦ ⟨_, hleft y⟩
  have hinj := OrzechProperty.injective_of_surjective_endomorphism r' hsurj
  refine ⟨Function.LeftInverse.injective hleft, fun y ↦ ⟨r' y, hinj ?_⟩⟩
  rw [hleft]

variable (R : Type u) [CommSemiring R] (B : Type u) [CommSemiring B] [OrzechProperty B]
  [Bialgebra R B] [Module.Projective R B] [LeftRigidCategory (FGComoduleCat.{u, u, u} R B)]

/-- If every finite comodule over a projective commutative bialgebra `B` with the Orzech property
(for instance, `B` a commutative ring) has a left dual, the universal point `AlgHom.id R B` acts
bijectively on the regular comodule `B`. -/
theorem bijective_endOfPoint_id_of_leftRigid :
    Function.Bijective (Comodule.endOfPoint B (AlgHom.id R B)) :=
  Comodule.bijective_endOfPoint_of_forall_finite _ fun N hN ↦
    bijective_endOfPoint_of_hasLeftDual
      (⟨ComoduleCat.of R B N, hN⟩ : FGComoduleCat.{u, u, u} R B) (AlgHom.id R B)

/-- A projective commutative bialgebra with the Orzech property (for instance, a commutative ring)
whose finite comodules have left duals is a Hopf algebra. Its antipode is
`TauCeti.HopfAlgebra.antipodeOfBijective`, the counit evaluation of the inverse universal point
action. This is not an instance, since `B` may already carry an antipode. -/
-- Exposed so that, once installed with `letI`, its bialgebra structure is recognised as the given
-- one by instance synthesis.
@[expose, instance_reducible]
noncomputable def hopfAlgebraOfLeftRigid : HopfAlgebra R B :=
  HopfAlgebra.ofBijective (bijective_endOfPoint_id_of_leftRigid R B)

/-- The antipode of `TauCeti.Tannaka.hopfAlgebraOfLeftRigid` is
`TauCeti.HopfAlgebra.antipodeOfBijective`. -/
@[simp]
theorem antipode_hopfAlgebraOfLeftRigid :
    letI := hopfAlgebraOfLeftRigid R B
    HopfAlgebra.antipode R (A := B) =
      HopfAlgebra.antipodeOfBijective (bijective_endOfPoint_id_of_leftRigid R B) :=
  rfl

/-- A projective commutative bialgebra with the Orzech property (for instance, a commutative
bialgebra over a field, whose underlying semiring is a commutative ring) whose finite comodules
have left duals, in particular one whose category of finite comodules is rigid, has an antipode
satisfying both convolution identities. -/
theorem exists_antipode_of_rigid_finite_comodules :
    ∃ S : B →ₗ[R] B,
      LinearMap.mul' R B ∘ₗ S.rTensor B ∘ₗ Coalgebra.comul =
        Algebra.linearMap R B ∘ₗ Coalgebra.counit ∧
      LinearMap.mul' R B ∘ₗ S.lTensor B ∘ₗ Coalgebra.comul =
        Algebra.linearMap R B ∘ₗ Coalgebra.counit :=
  ⟨_, HopfAlgebra.mul_antipodeOfBijective_rTensor_comul _,
    HopfAlgebra.mul_antipodeOfBijective_lTensor_comul (bijective_endOfPoint_id_of_leftRigid R B)⟩

end Tannaka

end TauCeti
