/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Limits.Types.Pullbacks
public import TauCeti.RingTheory.Deformation.ArtinLocalAlg
public import TauCeti.RingTheory.Derivation.TrivSqZeroExt

import Mathlib.CategoryTheory.Limits.Yoneda

/-!
# Predeformation functors and Schlessinger's conditions

A *predeformation functor* is a functor `F : C_Λ ⥤ Type w` on the Artinian coefficient category
whose value `F(k)` on the residue field is a point (Stacks, Definition 90.6.2 (06GS) and
Remark 90.6.3 (06GT)). Deformation problems over `k` are of this shape: `F(A)` collects the
deformations over the Artinian thickening `A` of `k`.

Schlessinger's conditions compare `F` on a fibre product with `F` on its factors. For morphisms
`f : A' ⟶ A` and `g : A'' ⟶ A` of `C_Λ` with `g` surjective there is a comparison map
`θ : F(A' ×_A A'') → F(A') ×_{F(A)} F(A'')`, and the conditions ask `θ` to be surjective or
bijective for various `f`, `g`: (H1), (H2) and (H4) of Schlessinger, and the Rim–Schlessinger
condition (RS), which makes `F` a *deformation functor* (Stacks, Definitions 90.10.1 (06HW),
90.16.1 (06J2), 90.16.8 (06J9)). Condition (H3), finiteness of the tangent space, is a condition
on the vector space below and is not defined here.

The *tangent space* of `F` is `T_F = F(k[ε])`. Under (H2), `F(k[ε] ×_k k[ε]) ≃ T_F × T_F`, and the
addition map `k[ε] ×_k k[ε] → k[ε]` makes `T_F` an abelian group; the scalings `ε ↦ cε` of `k[ε]`
make it a `k`-vector space (Stacks, Lemma 90.12.2 (06IH)). Each axiom is reduced to an identity of
morphisms into `k[ε]`, checked on `ε`-coefficients.

The basic examples are the functors `h_R` of morphisms out of a `Λ`-algebra `R` over `k`: these
satisfy (RS), as morphisms out of `R` turn the pullback squares of `C_Λ` into pullback squares of
types, and their tangent space is the space of `Λ`-derivations `R → k` (Stacks, Example 90.11.11
(06IC)).

## Main definitions

* `TauCeti.Deformation.PredeformationFunctor Λ k`: the category of predeformation functors.
* `TauCeti.Deformation.PredeformationFunctor.fiberProductMap`: the comparison map `θ`.
* `TauCeti.Deformation.PredeformationFunctor.SatisfiesH1`, `SatisfiesH2`, `SatisfiesH4`: the
  conditions (H1), (H2) and (H4).
* `TauCeti.Deformation.PredeformationFunctor.IsDeformationFunctor`: the condition (RS).
* `TauCeti.Deformation.PredeformationFunctor.TangentSpace`: the tangent space `F(k[ε])`, a
  `k`-vector space under (H2).
* `TauCeti.Deformation.prorep R`: the predeformation functor `h_R`.

## Main results

* `TauCeti.Deformation.PredeformationFunctor.isDeformationFunctor_iff_isPullback`: (RS) says that
  `F` takes the fibre product squares of `C_Λ` to pullback squares of types.
* `TauCeti.Deformation.PredeformationFunctor.IsDeformationFunctor.satisfiesH1` and its siblings:
  (RS) implies (H1), (H2) and (H4) (Stacks, Lemma 90.16.6 (06J7)).
* `TauCeti.Deformation.PredeformationFunctor.prodEquiv`: under (H2),
  `F(A' ×_k k[ε]) ≃ F(A') × T_F`.
* `TauCeti.Deformation.PredeformationFunctor.map_add_map`: the sum of two tangent vectors coming
  from one point of `F(B)` is the image of that point under the pointwise sum of the two maps.
* `TauCeti.Deformation.prorepTangentSpaceEquiv`: the tangent space of `h_R` is `Der_Λ(R, k)`.

## References

* [Stacks Project, Chapter 90 (06G7)](https://stacks.math.columbia.edu/tag/06G7)
* M. Schlessinger, *Functors of Artin rings*, Trans. Amer. Math. Soc. 130 (1968), 208–222.
-/

public section

open CategoryTheory Limits Opposite

universe w u v

namespace TauCeti.Deformation

open ArtinLocalAlg

variable (Λ : Type u) [CommRing Λ] (k : Type v) [Field k] [Algebra Λ k]

/-- A functor `F : C_Λ ⥤ Type w` is a *predeformation functor* if its value `F(k)` on the residue
field is a point. Stacks, Definition 90.6.2 (06GS) and Remark 90.6.3 (06GT). -/
structure IsPredeformationFunctor (F : ArtinLocalAlg Λ k ⥤ Type w) : Prop where
  /-- The value of `F` on the residue field has at most one element. -/
  subsingleton : Subsingleton (F.obj (residue Λ k))
  /-- The value of `F` on the residue field is nonempty. -/
  nonempty : Nonempty (F.obj (residue Λ k))

/-- The category of *predeformation functors*: functors `F : C_Λ ⥤ Type w` with `F(k)` a point,
and natural transformations between them. -/
abbrev PredeformationFunctor := ObjectProperty.FullSubcategory (IsPredeformationFunctor.{w} Λ k)

namespace PredeformationFunctor

variable {Λ k} (F : PredeformationFunctor.{w} Λ k)

instance : Subsingleton (F.obj.obj (residue Λ k)) := F.property.subsingleton

instance : Nonempty (F.obj.obj (residue Λ k)) := F.property.nonempty

section FiberProduct

variable {A' A'' A : ArtinLocalAlg Λ k} (f : A' ⟶ A) (g : A'' ⟶ A)
  (hg : Function.Surjective g.hom.left.hom)

/-- The comparison map `θ : F(A' ×_A A'') → F(A') ×_{F(A)} F(A'')` for morphisms `f : A' ⟶ A` and
`g : A'' ⟶ A` of `C_Λ` with `g` surjective, induced by the two projections of the fibre product.
Schlessinger's conditions ask for this map to be surjective or bijective. -/
def fiberProductMap :
    F.obj.obj (pullback f g hg) → Types.PullbackObj (F.obj.map f) (F.obj.map g) :=
  (PullbackCone.mk (F.obj.map (pullbackFst f g hg)) (F.obj.map (pullbackSnd f g hg))
    (by rw [← F.obj.map_comp, ← F.obj.map_comp, pullback_condition])).toPullbackObj

/-- The first component of `θ x` is the image of `x` under the first projection. -/
@[simp]
theorem fiberProductMap_fst (x : F.obj.obj (pullback f g hg)) :
    (F.fiberProductMap f g hg x).val.1 = F.obj.map (pullbackFst f g hg) x :=
  (rfl)

/-- The second component of `θ x` is the image of `x` under the second projection. -/
@[simp]
theorem fiberProductMap_snd (x : F.obj.obj (pullback f g hg)) :
    (F.fiberProductMap f g hg x).val.2 = F.obj.map (pullbackSnd f g hg) x :=
  (rfl)

/-- The comparison map `θ` is bijective exactly when `F` takes the fibre product square of `f`
and `g` to a pullback square of types. -/
theorem bijective_fiberProductMap_iff :
    Function.Bijective (F.fiberProductMap f g hg) ↔
      IsPullback (F.obj.map (pullbackFst f g hg)) (F.obj.map (pullbackSnd f g hg))
        (F.obj.map f) (F.obj.map g) :=
  ⟨fun h ↦ .of_isLimit ((PullbackCone.isLimitEquivBijective _).symm h),
    fun h ↦ PullbackCone.isLimitEquivBijective _ h.isLimit⟩

end FiberProduct

section Conditions

/-- Schlessinger's condition (H1): the comparison map `θ` is surjective whenever `A'' ⟶ A` is a
small extension. Stacks, Definition 90.10.1 (06HW) and Remark 90.10.3 (06HY). -/
class SatisfiesH1 : Prop where
  surjective_fiberProductMap ⦃A' A'' A : ArtinLocalAlg Λ k⦄ (f : A' ⟶ A) (g : A'' ⟶ A)
    (hg : IsSmallExtension g) : Function.Surjective (F.fiberProductMap f g hg.surjective)

/-- Schlessinger's condition (H2): the comparison map `θ` is bijective for `A = k` and
`A'' = k[ε]`. Stacks, Definition 90.10.1 (06HW) and Remark 90.10.3 (06HY). -/
class SatisfiesH2 : Prop where
  bijective_fiberProductMap (A' : ArtinLocalAlg Λ k) : Function.Bijective
    (F.fiberProductMap (toResidue A') (toResidue (dualNumbers Λ k)) (toResidue_surjective _))

/-- Schlessinger's condition (H4): the comparison map `θ` is bijective for `A' = A''` and
`f = g` a small extension. Stacks, Definition 90.16.1 (06J2). -/
class SatisfiesH4 : Prop where
  bijective_fiberProductMap ⦃A' A : ArtinLocalAlg Λ k⦄ (f : A' ⟶ A) (hf : IsSmallExtension f) :
    Function.Bijective (F.fiberProductMap f f hf.surjective)

/-- The Rim–Schlessinger condition (RS): the comparison map `θ` is bijective whenever `A'' ⟶ A`
is surjective. A predeformation functor satisfying (RS) is a *deformation functor*. Stacks,
Definition 90.16.8 (06J9) and Remark 90.16.9 (06JA). -/
class IsDeformationFunctor : Prop where
  bijective_fiberProductMap ⦃A' A'' A : ArtinLocalAlg Λ k⦄ (f : A' ⟶ A) (g : A'' ⟶ A)
    (hg : Function.Surjective g.hom.left.hom) : Function.Bijective (F.fiberProductMap f g hg)

variable {F}

/-- A predeformation functor is a deformation functor exactly when it takes the fibre product
square of every pair of morphisms `f`, `g` of `C_Λ` with `g` surjective to a pullback square of
types. -/
theorem isDeformationFunctor_iff_isPullback : F.IsDeformationFunctor ↔
    ∀ ⦃A' A'' A : ArtinLocalAlg Λ k⦄ (f : A' ⟶ A) (g : A'' ⟶ A)
      (hg : Function.Surjective g.hom.left.hom),
      IsPullback (F.obj.map (pullbackFst f g hg)) (F.obj.map (pullbackSnd f g hg))
        (F.obj.map f) (F.obj.map g) :=
  ⟨fun ⟨h⟩ _ _ _ f g hg ↦ (F.bijective_fiberProductMap_iff f g hg).mp (h f g hg),
    fun h ↦ ⟨fun _ _ _ f g hg ↦ (F.bijective_fiberProductMap_iff f g hg).mpr (h f g hg)⟩⟩

/-- A deformation functor satisfies (H1). Stacks, Lemma 90.16.6 (06J7). -/
instance (priority := 100) IsDeformationFunctor.satisfiesH1 [F.IsDeformationFunctor] :
    F.SatisfiesH1 :=
  ⟨fun _ _ _ f g hg ↦ (IsDeformationFunctor.bijective_fiberProductMap f g hg.surjective).2⟩

/-- A deformation functor satisfies (H2). Stacks, Lemma 90.16.6 (06J7). -/
instance (priority := 100) IsDeformationFunctor.satisfiesH2 [F.IsDeformationFunctor] :
    F.SatisfiesH2 :=
  ⟨fun _ ↦ IsDeformationFunctor.bijective_fiberProductMap _ _ (toResidue_surjective _)⟩

/-- A deformation functor satisfies (H4). -/
instance (priority := 100) IsDeformationFunctor.satisfiesH4 [F.IsDeformationFunctor] :
    F.SatisfiesH4 :=
  ⟨fun _ _ f hf ↦ IsDeformationFunctor.bijective_fiberProductMap f f hf.surjective⟩

end Conditions

section TangentSpace

/-- The *tangent space* `T_F = F(k[ε])` of a predeformation functor `F`. Under (H2) it is a
`k`-vector space. Stacks, Definition 90.12.1 (06IG). -/
abbrev TangentSpace : Type w :=
  F.obj.obj (dualNumbers Λ k)

/-- Scalar multiplication on the tangent space: `c • v` is the image of `v` under the scaling
`a + bε ↦ a + cbε` of `k[ε]`. -/
instance : SMul k F.TangentSpace where
  smul c v := F.obj.map (dualNumbersSMul Λ k c) v

/-- The zero of the tangent space is the image of the point of `F(k)` under `k → k[ε]`. -/
noncomputable instance : Zero F.TangentSpace where
  zero := F.obj.map (residueToDualNumbers Λ k) (Classical.arbitrary _)

/-- Scalar multiplication by `c` is the map of `F` along the scaling `ε ↦ cε`. -/
theorem smul_def (c : k) (v : F.TangentSpace) : c • v = F.obj.map (dualNumbersSMul Λ k c) v :=
  (rfl)

/-- The image of the point of `F(k)` under `k → k[ε]` is the zero tangent vector. -/
@[simp]
theorem map_residueToDualNumbers (x : F.obj.obj (residue Λ k)) :
    F.obj.map (residueToDualNumbers Λ k) x = (0 : F.TangentSpace) :=
  congrArg _ (Subsingleton.elim _ _)

/-- A morphism `B ⟶ k[ε]` factoring through `k` takes every point of `F(B)` to zero. -/
theorem map_comp_residueToDualNumbers {B : ArtinLocalAlg Λ k} (ψ : B ⟶ residue Λ k)
    (x : F.obj.obj B) : F.obj.map (ψ ≫ residueToDualNumbers Λ k) x = (0 : F.TangentSpace) := by
  rw [F.obj.map_comp, types_comp_apply]
  exact F.map_residueToDualNumbers _

/-- Scalar multiplication of an image of a point of `F(B)` is its image under the composite with
the scaling of `k[ε]`. -/
theorem smul_map {B : ArtinLocalAlg Λ k} (c : k) (φ : B ⟶ dualNumbers Λ k)
    (x : F.obj.obj B) :
    c • (F.obj.map φ x : F.TangentSpace) = F.obj.map (φ ≫ dualNumbersSMul Λ k c) x := by
  rw [smul_def, F.obj.map_comp, types_comp_apply]

/-- Negation on the tangent space is scalar multiplication by `-1`. -/
noncomputable instance : Neg F.TangentSpace where
  neg v := (-1 : k) • v

variable [F.SatisfiesH2]

/-- Under (H2), the identification `F(A' ×_k k[ε]) ≃ F(A') × T_F` induced by the two
projections. -/
noncomputable def prodEquiv (A' : ArtinLocalAlg Λ k) :
    F.obj.obj (pullback (toResidue A') (toResidue (dualNumbers Λ k)) (toResidue_surjective _)) ≃
      F.obj.obj A' × F.TangentSpace :=
  (Equiv.ofBijective _ (SatisfiesH2.bijective_fiberProductMap A')).trans
    (Equiv.subtypeUnivEquiv fun _ ↦ Subsingleton.elim _ _)

/-- The identification `F(A' ×_k k[ε]) ≃ F(A') × T_F` is given by the two projections. -/
@[simp]
theorem prodEquiv_apply (A' : ArtinLocalAlg Λ k)
    (x : F.obj.obj (pullback (toResidue A') (toResidue (dualNumbers Λ k))
      (toResidue_surjective _))) :
    F.prodEquiv A' x = (F.obj.map (pullbackFst _ _ _) x, F.obj.map (pullbackSnd _ _ _) x) :=
  (rfl)

/-- Under (H2), the image of a point of `F(B)` under `liftResidue φ ψ` is determined by its
images under `φ` and `ψ`. -/
theorem prodEquiv_map_liftResidue {B A' : ArtinLocalAlg Λ k} (φ : B ⟶ A')
    (ψ : B ⟶ dualNumbers Λ k) (x : F.obj.obj B) :
    F.prodEquiv A' (F.obj.map (liftResidue φ ψ) x) = (F.obj.map φ x, F.obj.map ψ x) := by
  rw [prodEquiv_apply, ← types_comp_apply, ← types_comp_apply, ← F.obj.map_comp,
    ← F.obj.map_comp, liftResidue_pullbackFst, liftResidue_pullbackSnd]

/-- Under (H2), addition on the tangent space: `v + w` is the image of the point of
`F(k[ε] ×_k k[ε])` over `(v, w)` under the addition map `k[ε] ×_k k[ε] → k[ε]`. -/
noncomputable instance : Add F.TangentSpace where
  add v w := F.obj.map (dualNumbersAdd Λ k) ((F.prodEquiv (dualNumbers Λ k)).symm (v, w))

/-- The sum of two tangent vectors is the image of the point over them under the addition map. -/
theorem add_def (v w : F.TangentSpace) :
    v + w = F.obj.map (dualNumbersAdd Λ k) ((F.prodEquiv (dualNumbers Λ k)).symm (v, w)) :=
  (rfl)

/-- The sum of the images of a point of `F(B)` under two morphisms `φ, ψ : B ⟶ k[ε]` is its image
under the pointwise sum `B → k[ε] ×_k k[ε] → k[ε]`. -/
theorem map_add_map {B : ArtinLocalAlg Λ k} (φ ψ : B ⟶ dualNumbers Λ k) (x : F.obj.obj B) :
    (F.obj.map φ x : F.TangentSpace) + F.obj.map ψ x =
      F.obj.map (liftResidue φ ψ ≫ dualNumbersAdd Λ k) x := by
  rw [add_def, F.obj.map_comp, types_comp_apply, ← F.prodEquiv_map_liftResidue φ ψ x,
    Equiv.symm_apply_apply]

/-- Every pair of tangent vectors comes from a single point of `F(k[ε] ×_k k[ε])`. -/
private theorem exists_map_pullbackFst_eq_and (v w : F.TangentSpace) :
    ∃ x : F.obj.obj (dualNumbersPullback Λ k),
      F.obj.map (pullbackFst _ _ _) x = v ∧ F.obj.map (pullbackSnd _ _ _) x = w := by
  have := (F.prodEquiv _).apply_symm_apply (v, w)
  rw [prodEquiv_apply, Prod.ext_iff] at this
  exact ⟨_, this⟩

/-- A sum of images of a point of `F(B)` under morphisms to `k[ε]` is its image under any morphism
whose `ε`-components are the sums of theirs. -/
private theorem map_add_map_eq {B : ArtinLocalAlg Λ k} (φ ψ χ : B ⟶ dualNumbers Λ k)
    (x : F.obj.obj B)
    (h : ∀ b, epsCoeff (χ.hom.left.hom b) = epsCoeff (φ.hom.left.hom b) +
      epsCoeff (ψ.hom.left.hom b)) :
    (F.obj.map φ x : F.TangentSpace) + F.obj.map ψ x = F.obj.map χ x := by
  rw [map_add_map]
  exact congrArg (F.obj.map · x) (dualNumbers_hom_ext fun b ↦ by simp [h])

/-- Under (H2), the tangent space is an abelian group. Stacks, Lemma 90.12.2 (06IH). -/
noncomputable instance : AddCommGroup F.TangentSpace where
  add_assoc u v w := by
    obtain ⟨x, rfl, rfl⟩ := F.exists_map_pullbackFst_eq_and u v
    obtain ⟨z, hz⟩ : ∃ z, F.prodEquiv (dualNumbersPullback Λ k) z = (x, w) :=
      ⟨_, Equiv.apply_symm_apply _ _⟩
    simp only [prodEquiv_apply, Prod.mk.injEq] at hz
    obtain ⟨rfl, rfl⟩ := hz
    simp only [← types_comp_apply, ← F.obj.map_comp, map_add_map]
    exact congrArg (F.obj.map · _) (dualNumbers_hom_ext fun b ↦ by simp [add_assoc])
  zero_add v := by
    have h := F.map_add_map_eq (toResidue _ ≫ residueToDualNumbers Λ k) (𝟙 _) (𝟙 _) v
      fun b ↦ by rw [epsCoeff_comp_residueToDualNumbers_hom_left_hom_apply, zero_add]
    rwa [map_comp_residueToDualNumbers, F.obj.map_id, types_id_apply] at h
  add_zero v := by
    have h := F.map_add_map_eq (𝟙 _) (toResidue _ ≫ residueToDualNumbers Λ k) (𝟙 _) v
      fun b ↦ by rw [epsCoeff_comp_residueToDualNumbers_hom_left_hom_apply, add_zero]
    rwa [map_comp_residueToDualNumbers, F.obj.map_id, types_id_apply] at h
  add_comm v w := by
    obtain ⟨x, rfl, rfl⟩ := F.exists_map_pullbackFst_eq_and v w
    rw [map_add_map, F.map_add_map_eq _ _
      (liftResidue (pullbackFst _ _ _) (pullbackSnd _ _ _) ≫ dualNumbersAdd Λ k) x
      fun b ↦ by simp [add_comm]]
  neg_add_cancel v := by
    have h := F.map_add_map_eq (dualNumbersSMul Λ k (-1)) (𝟙 _)
      (toResidue _ ≫ residueToDualNumbers Λ k) v fun b ↦ by
        rw [epsCoeff_comp_residueToDualNumbers_hom_left_hom_apply]; simp
    rwa [map_comp_residueToDualNumbers, F.obj.map_id, types_id_apply] at h
  nsmul := nsmulRec
  zsmul := zsmulRec

/-- Under (H2), the tangent space is a `k`-vector space. Stacks, Lemma 90.12.2 (06IH). -/
noncomputable instance : Module k F.TangentSpace where
  one_smul v := by
    rw [smul_def, dualNumbers_hom_ext (ψ₁ := dualNumbersSMul Λ k 1) (ψ₂ := 𝟙 _) fun b ↦ by simp,
      F.obj.map_id, types_id_apply]
  mul_smul c d v := by
    rw [smul_def, smul_def, smul_def, ← types_comp_apply, ← F.obj.map_comp]
    exact congrArg (F.obj.map · v) (dualNumbers_hom_ext fun b ↦ by simp [mul_assoc])
  smul_zero c := by
    rw [smul_def, ← map_residueToDualNumbers F (Classical.arbitrary _), ← types_comp_apply,
      ← F.obj.map_comp]
    exact congrArg (F.obj.map · _) (dualNumbers_hom_ext fun b ↦ by simp)
  smul_add c v w := by
    obtain ⟨x, rfl, rfl⟩ := F.exists_map_pullbackFst_eq_and v w
    rw [map_add_map, smul_map, smul_map, smul_map,
      F.map_add_map_eq _ _ (liftResidue (pullbackFst _ _ _) (pullbackSnd _ _ _) ≫
        dualNumbersAdd Λ k ≫ dualNumbersSMul Λ k c) x
        fun b ↦ by simp [mul_add], Category.assoc]
  add_smul c d v := by
    rw [smul_def, smul_def, smul_def,
      F.map_add_map_eq _ _ (dualNumbersSMul Λ k (c + d)) v fun b ↦ by simp [add_mul]]
  zero_smul v := by
    rw [smul_def, ← F.map_comp_residueToDualNumbers (toResidue _) v]
    exact congrArg (F.obj.map · v) (dualNumbers_hom_ext fun b ↦ by
      rw [epsCoeff_comp_residueToDualNumbers_hom_left_hom_apply]; simp)

end TangentSpace

end PredeformationFunctor

section Prorep

variable {Λ k} (R : Over (CommAlgCat.of Λ k))

/-- The functor `h_R : C_Λ ⥤ Type v` of a `Λ`-algebra `R` over `k`, taking `A` to the `Λ`-algebra
maps `R → A` compatible with the maps to `k`. -/
-- Exposed because the values of `prorep R` are hom-sets of `Over (CommAlgCat.of Λ k)` by
-- definitional unfolding.
@[expose] def prorep : PredeformationFunctor.{v} Λ k where
  obj := ObjectProperty.ι _ ⋙ coyoneda.obj (op R)
  property :=
    { subsingleton := ⟨fun φ ψ ↦ Over.OverMorphism.ext (CommAlgCat.hom_ext <|
        (congrArg CommAlgCat.Hom.hom (Over.w φ)).trans
          (congrArg CommAlgCat.Hom.hom (Over.w ψ)).symm)⟩
      nonempty := ⟨Over.homMk (CommAlgCat.ofHom R.hom.hom) (rfl)⟩ }

/-- The map of `h_R` along `φ : A ⟶ B` is composition with `φ`. -/
@[simp]
theorem prorep_obj_map_apply {A B : ArtinLocalAlg Λ k} (φ : A ⟶ B) (x : (prorep R).obj.obj A) :
    (prorep R).obj.map φ x = x ≫ φ.hom :=
  (rfl)

/-- The algebra map of the image of a point `x` of `h_R` under `φ` is the composite of the algebra
maps of `x` and `φ`. Not a `simp` lemma, as `prorep_obj_map_apply` rewrites its left side; it is
used before that rewrite, because `Over.comp_left` does not apply to `x ≫ φ.hom`, in which `x` is
an `Over` morphism only after unfolding `prorep`. -/
theorem prorep_obj_map_left_hom_apply {A B : ArtinLocalAlg Λ k} (φ : A ⟶ B)
    (x : (prorep R).obj.obj A) (r : R.left) :
    ((prorep R).obj.map φ x).left.hom r = φ.hom.left.hom (x.left.hom r) :=
  (rfl)

/-- A point of `h_R` at `A` is a `Λ`-algebra map `R → A` compatible with the maps to `k`. -/
def prorepObjEquiv (A : ArtinLocalAlg Λ k) :
    (prorep R).obj.obj A ≃ {φ : R.left →ₐ[Λ] A.obj.left // A.augmentation.comp φ = R.hom.hom} where
  toFun x := ⟨x.left.hom, by rw [augmentation_def]; exact congrArg CommAlgCat.Hom.hom (Over.w x)⟩
  invFun φ := Over.homMk (CommAlgCat.ofHom φ.val)
    (CommAlgCat.hom_ext ((congrArg (·.comp φ.val) (augmentation_def A)).symm.trans φ.property))
  left_inv _ := rfl
  right_inv _ := rfl

/-- The algebra map of a point of `h_R` is its underlying map. -/
@[simp]
theorem coe_prorepObjEquiv_apply (A : ArtinLocalAlg Λ k) (x : (prorep R).obj.obj A) :
    (prorepObjEquiv R A x : R.left →ₐ[Λ] A.obj.left) = x.left.hom :=
  (rfl)

/-- The point of `h_R` given by an algebra map has that map as its underlying map. -/
@[simp]
theorem prorepObjEquiv_symm_apply_left_hom (A : ArtinLocalAlg Λ k)
    (φ : {φ : R.left →ₐ[Λ] A.obj.left // A.augmentation.comp φ = R.hom.hom}) :
    ((prorepObjEquiv R A).symm φ).left.hom = φ.val :=
  (rfl)

/-- The functor `h_R` is a deformation functor: it satisfies the Rim–Schlessinger condition. -/
instance : (prorep R).IsDeformationFunctor :=
  PredeformationFunctor.isDeformationFunctor_iff_isPullback.mpr fun _ _ _ f g hg ↦
    (isPullback_hom f g hg).map (coyoneda.obj (op R))

end Prorep

section Tangent

variable {Λ k} (R : Type v) [CommRing R] [Algebra Λ R] [Algebra R k] [IsScalarTower Λ R k]

/-- The bijection underlying `prorepTangentSpaceEquiv`. -/
private def prorepTangentSpaceEquivAux :
    (prorep (Over.mk (CommAlgCat.ofHom (IsScalarTower.toAlgHom Λ R k)))).TangentSpace ≃
      Derivation Λ R k :=
  -- After `augmentation_dualNumbers`, the two sides differ only by unfolding `Over.mk` (whose
  -- left object is `R`) and `CommAlgCat.ofHom`. `Over.mk_hom` and `CommAlgCat.hom_ofHom` handle
  -- the structure map, but cannot change the carrier `(Over.mk _).left`, so `rfl` closes it.
  (prorepObjEquiv _ _).trans <| (Equiv.subtypeEquivRight fun _ ↦ by
    rw [augmentation_dualNumbers]; rfl).trans
      (derivationToTrivSqZeroExtEquivLift Λ R k (M := k)).symm

private theorem prorepTangentSpaceEquivAux_apply
    (v : (prorep (Over.mk (CommAlgCat.ofHom (IsScalarTower.toAlgHom Λ R k)))).TangentSpace)
    (r : R) : prorepTangentSpaceEquivAux R v r = epsCoeff (v.left.hom r) :=
  (derivationToTrivSqZeroExtEquivLift_symm_apply _ r).trans (epsCoeff_def _).symm

/-- The tangent space of `h_R`, for a `Λ`-algebra `R` with a point `R → k`, is the `k`-vector
space of `Λ`-derivations `R → k`: a tangent vector `R → k[ε]` corresponds to its `ε`-coefficient.
Stacks, Example 90.11.11 (06IC). -/
noncomputable def prorepTangentSpaceEquiv :
    (prorep (Over.mk (CommAlgCat.ofHom (IsScalarTower.toAlgHom Λ R k)))).TangentSpace ≃ₗ[k]
      Derivation Λ R k where
  __ := prorepTangentSpaceEquivAux R
  map_add' v w := by
    obtain ⟨x, hx⟩ : ∃ x, (prorep _).prodEquiv (dualNumbers Λ k) x = (v, w) :=
      ⟨_, Equiv.apply_symm_apply _ _⟩
    simp only [PredeformationFunctor.prodEquiv_apply, Prod.mk.injEq] at hx
    obtain ⟨rfl, rfl⟩ := hx
    ext r
    rw [PredeformationFunctor.map_add_map, _root_.add_apply, Equiv.toFun_as_coe,
      prorepTangentSpaceEquivAux_apply, prorepTangentSpaceEquivAux_apply,
      prorepTangentSpaceEquivAux_apply, prorep_obj_map_left_hom_apply,
      prorep_obj_map_left_hom_apply, prorep_obj_map_left_hom_apply, comp_hom_left_hom_apply,
      epsCoeff_dualNumbersAdd_hom_left_hom_apply, liftResidue_hom_left_hom_apply_fst,
      liftResidue_hom_left_hom_apply_snd]
  map_smul' c v := by
    ext r
    rw [PredeformationFunctor.smul_def, _root_.smul_apply, Equiv.toFun_as_coe,
      prorepTangentSpaceEquivAux_apply, prorepTangentSpaceEquivAux_apply,
      prorep_obj_map_left_hom_apply, epsCoeff_dualNumbersSMul_hom_left_hom_apply, smul_eq_mul,
      RingHom.id_apply]

/-- The derivation of a tangent vector `v : R → k[ε]` of `h_R` takes `r` to the `ε`-coefficient of
`v r`. -/
@[simp]
theorem prorepTangentSpaceEquiv_apply
    (v : (prorep (Over.mk (CommAlgCat.ofHom (IsScalarTower.toAlgHom Λ R k)))).TangentSpace)
    (r : R) : prorepTangentSpaceEquiv R v r = epsCoeff (v.left.hom r) :=
  prorepTangentSpaceEquivAux_apply R v r

end Tangent

end TauCeti.Deformation
