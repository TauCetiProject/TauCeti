/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.IntegralModel.Basic
public import TauCeti.Algebra.AlgebraicGroup.Trivial

/-!
# The integral model of the trivial group

The trivial affine group over `K` has coordinate Hopf algebra `K`. For any algebra map `O → K` of
commutative rings, the base ring `O`, as a Hopf `O`-algebra, is a smooth affine `O`-model of it:
its generic fiber is `K ⊗[O] O ≅ K` (`TauCeti.IntegralModel.SmoothModel.trivial`). Its group of
integral points is trivial, as is the group of integral points of every model of the trivial group,
since the trivial group has a single `K`-point (`WithConv.convPoint_eq_one`). Every model of the
trivial group maps to the model `O`, via the unit `O → O[𝒢]` of coordinate algebras. When `O → K`
is injective, this morphism is an isomorphism: a model `𝒢` is flat, so `O[𝒢]` embeds in
`K ⊗[O] O[𝒢] ≅ K`, and compatibility with the counits then forces the unit `O → O[𝒢]` to be
bijective. So the trivial group has the unique model `O`, up to unique isomorphism.

## Main declarations

* `TauCeti.IntegralModel.SmoothModel.trivial`: the model `O` of the trivial group.
* `TauCeti.IntegralModel.SmoothModel.integralPoints_eq_bot_of_trivial`: every model of the trivial
  group has trivial integral points.
* `TauCeti.IntegralModel.SmoothModel.homTrivial`: the morphism from any model of the trivial group
  to the model `O`.
* `TauCeti.IntegralModel.SmoothModel.isIso_homTrivial`: when `O → K` is injective, that morphism
  is an isomorphism.
-/

public section

open CategoryTheory TensorProduct

namespace TauCeti.IntegralModel.SmoothModel

universe u

variable (O K : Type u) [CommRing O] [CommRing K] [Algebra O K]

/-- The generic fiber isomorphism `K ⊗[O] O ≅ K` of the trivial model. -/
noncomputable def trivialGenericFiberIso :
    FiniteTypeCommHopfAlgCat.baseChange (K := K) (FiniteTypeCommHopfAlgCat.of O O) ≅
      TrivialGroup.finiteTypeCoordinateHopfAlgebra K :=
  ObjectProperty.isoMk _ (CommHopfAlgCat.isoMk (Bialgebra.TensorProduct.rid O K K))

/-- On pure tensors, the generic fiber isomorphism of the trivial model is multiplication. -/
@[simp]
theorem toBialgHom_trivialGenericFiberIso_hom_tmul (a : K) (b : O) :
    FiniteTypeCommHopfAlgCat.toBialgHom (trivialGenericFiberIso O K).hom (a ⊗ₜ[O] b) =
      b • a :=
  (rfl)

/-- **The trivial model**: the base ring `O` is a smooth affine `O`-model of the trivial group
over `K`. -/
noncomputable def trivial : SmoothModel O K (TrivialGroup.finiteTypeCoordinateHopfAlgebra K) where
  coord := FiniteTypeCommHopfAlgCat.of O O
  smooth := inferInstanceAs (Algebra.Smooth O O)
  genericFiberIso := trivialGenericFiberIso O K

/-- The coordinate algebra of the trivial model is `O`. -/
@[simp]
theorem trivial_coord : (trivial O K).coord = FiniteTypeCommHopfAlgCat.of O O :=
  (rfl)

/-- The generic fiber isomorphism of the trivial model is `trivialGenericFiberIso`, transported
along `trivial_coord`. -/
@[simp]
theorem trivial_genericFiberIso :
    (trivial O K).genericFiberIso =
      eqToIso (congrArg (FiniteTypeCommHopfAlgCat.baseChange (K := K)) (trivial_coord O K)) ≪≫
        trivialGenericFiberIso O K := by
  -- `trivial_coord` holds by `rfl`, so the transport `eqToHom` is the identity.
  ext1
  exact (Category.id_comp _).symm

variable {O K}

/-- **Every model of the trivial group has trivial integral points**, since the trivial group
has a single `K`-point. -/
@[simp]
theorem integralPoints_eq_bot_of_trivial
    (𝒢 : SmoothModel O K (TrivialGroup.finiteTypeCoordinateHopfAlgebra K)) :
    𝒢.integralPoints = ⊥ :=
  (Subgroup.eq_bot_iff_forall _).2 fun g _ ↦ WithConv.convPoint_eq_one g

variable (O K)

/-- The trivial model has trivial integral points. -/
theorem integralPoints_trivial : (trivial O K).integralPoints = ⊥ :=
  integralPoints_eq_bot_of_trivial _

variable {O K}

/-- The unit `O → O[𝒢]` of a model of the trivial group, as a morphism of Hopf `O`-algebras. -/
noncomputable def trivialCoordHom
    (𝒢 : SmoothModel O K (TrivialGroup.finiteTypeCoordinateHopfAlgebra K)) :
    FiniteTypeCommHopfAlgCat.of O O ⟶ 𝒢.coord :=
  ObjectProperty.homMk (CommHopfAlgCat.ofHom (Bialgebra.unitBialgHom O 𝒢.coord))

/-- The underlying bialgebra map of `trivialCoordHom 𝒢` is the unit `O → O[𝒢]`. -/
@[simp]
theorem toBialgHom_trivialCoordHom
    (𝒢 : SmoothModel O K (TrivialGroup.finiteTypeCoordinateHopfAlgebra K)) :
    FiniteTypeCommHopfAlgCat.toBialgHom (trivialCoordHom 𝒢) = Bialgebra.unitBialgHom O 𝒢.coord :=
  (rfl)

/-- **Every model of the trivial group maps to the trivial model**: the unit `O → O[𝒢]` is a
morphism `𝒢 → trivial O K` of models, that is, a Hopf map of coordinate algebras over the
identity of `K`. Following the contravariant convention of `Hom`, it is an arrow
`(trivial O K).toCostructuredArrow ⟶ 𝒢.toCostructuredArrow`. -/
noncomputable def homTrivial
    (𝒢 : SmoothModel O K (TrivialGroup.finiteTypeCoordinateHopfAlgebra K)) :
    Hom (trivial O K) 𝒢 :=
  -- Both sides are `K`-algebra maps `K ⊗[O] O → K`, which agree on both factors.
  CostructuredArrow.homMk (trivialCoordHom 𝒢) (by ext)

/-- The underlying Hopf map of `homTrivial 𝒢` is `trivialCoordHom 𝒢`, transported along
`trivial_coord`. -/
@[simp]
theorem homTrivial_left
    (𝒢 : SmoothModel O K (TrivialGroup.finiteTypeCoordinateHopfAlgebra K)) :
    (homTrivial 𝒢).left = eqToHom (trivial_coord O K) ≫ trivialCoordHom 𝒢 :=
  -- `trivial_coord` holds by `rfl`, so the transport `eqToHom` is the identity.
  (Category.id_comp _).symm

/-- When `O → K` is injective, the unit `O → O[𝒢]` of any model of the trivial group is
bijective. -/
theorem algebraMap_coord_bijective_of_trivial [FaithfulSMul O K]
    (𝒢 : SmoothModel O K (TrivialGroup.finiteTypeCoordinateHopfAlgebra K)) :
    Function.Bijective (algebraMap O 𝒢.coord) := by
  -- `O[𝒢]` is flat, so it embeds in its generic fiber `K ⊗[O] O[𝒢] ≅ K`, on which the image of
  -- `a` is the counit of `a`. Hence the counit of `O[𝒢]` is injective, and it is a retraction of
  -- the unit.
  have hε : Function.Injective (Coalgebra.counit (R := O) (A := 𝒢.coord)) := by
    intro a b hab
    apply Algebra.TensorProduct.includeRight_injective (FaithfulSMul.algebraMap_injective O K)
    -- The generic fiber isomorphism is a coalgebra map to `K`, whose counit is the identity.
    have hφ (x : K ⊗[O] 𝒢.coord) : FiniteTypeCommHopfAlgCat.toBialgHom 𝒢.genericFiberIso.hom x =
        Coalgebra.counit (R := K) x :=
      CoalgHomClass.counit_comp_apply (FiniteTypeCommHopfAlgCat.toBialgHom 𝒢.genericFiberIso.hom) x
    rw [Algebra.TensorProduct.includeRight_apply, Algebra.TensorProduct.includeRight_apply,
      ← FiniteTypeCommHopfAlgCat.toBialgHom_inv_hom_apply 𝒢.genericFiberIso (1 ⊗ₜ a),
      ← FiniteTypeCommHopfAlgCat.toBialgHom_inv_hom_apply 𝒢.genericFiberIso (1 ⊗ₜ b), hφ, hφ]
    simp [hab]
  refine ⟨fun x y h ↦ by simpa using congrArg (Coalgebra.counit (R := O)) h, fun a ↦
    ⟨Coalgebra.counit a, hε ?_⟩⟩
  simp

/-- **The trivial group has the unique model `O`**: when `O → K` is injective, the morphism
`homTrivial 𝒢` from any model `𝒢` of the trivial group to the model `O` is an isomorphism,
so `asIso (homTrivial 𝒢) : (trivial O K).toCostructuredArrow ≅ 𝒢.toCostructuredArrow`. -/
instance isIso_homTrivial [FaithfulSMul O K]
    (𝒢 : SmoothModel O K (TrivialGroup.finiteTypeCoordinateHopfAlgebra K)) :
    IsIso (homTrivial 𝒢) := by
  let e : (trivial O K).toCostructuredArrow ≅ 𝒢.toCostructuredArrow :=
    CostructuredArrow.isoMk (ObjectProperty.isoMk _ (CommHopfAlgCat.isoMk
      (BialgEquiv.ofBijective (Bialgebra.unitBialgHom O 𝒢.coord)
        (algebraMap_coord_bijective_of_trivial 𝒢)))) (by ext)
  -- Morphisms of models are unique when `O → K` is injective.
  rw [Subsingleton.elim (homTrivial 𝒢) e.hom]
  infer_instance

end TauCeti.IntegralModel.SmoothModel
