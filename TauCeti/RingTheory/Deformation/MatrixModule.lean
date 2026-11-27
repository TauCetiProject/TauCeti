/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Charpoly.ToMatrix
public import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv
public import TauCeti.RingTheory.Deformation.Module

import TauCeti.RingTheory.Ideal.Operations

/-!
# Module deformations are lifts up to strict conjugation

Let `ρbar : G →* GL n k` be a residual representation and `A` an object of the Artinian
coefficient category `C_Λ`. Deformations of `ρbar` to `A` have a matrix description, by lifts
`G →* GL n A` and their strict classes (`TauCeti.Deformation.Lift`,
`TauCeti.Deformation.StrictClass`), and a module description, by free `A`-modules with an action
of `G` and an identification of their reduction with `kⁿ`
(`TauCeti.Deformation.ModuleDeformation`). This file shows that the two descriptions agree: there
are bijections, natural in `A`,
* between lifts of `ρbar` to `A` and isomorphism classes of framed module deformations, and
* between strict classes of lifts and isomorphism classes of module deformations.

A basis `b` of a module deformation `V` lifting the standard basis of `kⁿ` turns the action of `G`
into the lift `g ↦ [ρ(g)]_b` of matrices in `b`: these matrices reduce to `ρbar g`, and since `A`
is local they are invertible, even when `G` is only a monoid. Conversely a lift `ρ` acts on the
free module of rank `n` through its matrices in the standard basis, which reduces to the standard
basis of `kⁿ`. Isomorphisms of module deformations reduce to the identity of `kⁿ`, so they
preserve the matrices in bases lifting the standard basis; this is why framed module deformations
up to isomorphism are exactly lifts. Two bases `b`, `b'` lifting the standard basis differ by the
change-of-basis matrix `b'.toMatrix b`, which reduces to the identity, so it lies in the strict
kernel `Γ̂ₙ(A)` and conjugates the lift in `b` to the lift in `b'`; conversely every element of
the strict kernel arises in this way. Forgetting the framing therefore matches isomorphism classes
of module deformations with strict classes of lifts, and not with the coarser `GL n A`-conjugacy
classes.

The underlying module of the framed module deformation of a lift is `Fin (Fintype.card n) → A`,
with its standard basis reindexed by `n`, rather than `n → A`: the carrier of a module deformation
lives in the universe of `k`, while `n` may live in a larger universe. For the same reason the
functors of module deformations take values in a larger universe than the functors of lifts, and
the natural isomorphisms of functors are stated after lifting universes along `uliftFunctor`.

## Main definitions

* `TauCeti.Deformation.ModuleDeformation.toLift D b hb`: the lift given by the matrices of the
  action of a module deformation in a basis `b` lifting the standard basis of `kⁿ`.
* `TauCeti.Deformation.FramedModuleDeformation.toLift D`: the lift of a framed module deformation,
  in its framing.
* `TauCeti.Deformation.FramedModuleDeformation.ofLift ρ`: the framed module deformation of a lift.
* `TauCeti.Deformation.liftEquivFramedModuleDeformationClass ρbar A`: the bijection between lifts
  and isomorphism classes of framed module deformations.
* `TauCeti.Deformation.strictClassEquivModuleDeformationClass ρbar A`: the bijection between
  strict classes of lifts and isomorphism classes of module deformations.
* `TauCeti.Deformation.liftFunctorIsoFramedModuleDeformationFunctor Λ ρbar` and
  `TauCeti.Deformation.strictClassFunctorIsoModuleDeformationFunctor Λ ρbar`: the corresponding
  natural isomorphisms `Lift_ρbar ≅ Def^{mod,□}_ρbar` and `Def_ρbar ≅ Def^mod_ρbar`.

## Main results

* `TauCeti.Deformation.ModuleDeformation.toLift_map_equiv`: an isomorphism of module deformations
  preserves the lift in a basis and its image.
* `TauCeti.Deformation.ModuleDeformation.toLift_baseChange`: the lift of a base change is the
  pushforward of the lift.
* `TauCeti.Deformation.ModuleDeformation.exists_smul_toLift_eq`: changing the basis conjugates the
  lift by the change-of-basis matrix, an element of the strict kernel, and
  `TauCeti.Deformation.ModuleDeformation.exists_toLift_eq_smul`: every strict conjugate of the
  lift arises from a change of basis.
* `TauCeti.Deformation.FramedModuleDeformation.nonempty_equiv_iff`: two framed module deformations
  are isomorphic exactly when they have the same lift.
* `TauCeti.Deformation.strictClassEquivModuleDeformationClass_mk`: the strict class of a lift
  corresponds to the class of the module deformation obtained by forgetting the framing, and
  `TauCeti.Deformation.strictClassEquivModuleDeformationClass_symm_mk`: the class of a module
  deformation corresponds to the strict class of its lift in any basis lifting the standard basis
  of `kⁿ`.
* `TauCeti.Deformation.ModuleDeformation.det_toLift_apply`,
  `TauCeti.Deformation.ModuleDeformation.trace_toLift_apply` and
  `TauCeti.Deformation.ModuleDeformation.charpoly_toLift_apply`: the determinant, trace and
  characteristic polynomial of the lift in any basis are those of the action.

## References

* B. Mazur, *Deforming Galois representations*, in *Galois groups over `ℚ`*, MSRI Publ. 16
  (1989), 385–437, §1.2.
* M. Kisin, *Lectures on deformations of Galois representations* (Clay Mathematics Institute
  summer school notes), Lecture 1, Remark (1.1.2)(1),
  https://people.math.harvard.edu/~kisin/notes/notes.pdf.
-/

public section

open CategoryTheory Matrix IsLocalRing

universe u v w x

namespace TauCeti.Deformation

variable {Λ : Type u} [CommRing Λ] {k : Type v} [Field k] [Algebra Λ k]
  {n : Type x} [Fintype n] [DecidableEq n] {G : Type w} [Monoid G] [TopologicalSpace G]

open ArtinLocalAlg

namespace ModuleDeformation

variable {ρbar : G →* GL n k} {A B : ArtinLocalAlg Λ k}

section ToLift

variable (D : ModuleDeformation ρbar A) (b : Module.Basis n A.obj.left D)
  (hb : ∀ i, D.reduction (b i) = Pi.single i 1)

include hb in
/-- The augmentation of a coordinate in a basis lifting the standard basis of `kⁿ` is the
corresponding coordinate of the reduction. -/
private theorem augmentation_repr (v : D) (i : n) :
    A.augmentation (b.repr v i) = D.reduction v i :=
  (congrFun (D.reduction_eq_augmentation_repr b hb v) i).symm

include hb in
/-- In a basis lifting the standard basis of `kⁿ`, the matrix of the action of `g` reduces to
`ρbar g`. -/
theorem map_augmentation_toMatrix_action (g : G) :
    (LinearMap.toMatrix b b (D.action g)).map A.augmentation = (ρbar g : Matrix n n k) := by
  ext i j
  simp [LinearMap.toMatrix_apply, D.augmentation_repr b hb, D.reduction_action, hb]

include hb in
/-- In a basis lifting the standard basis of `kⁿ`, the matrix of the action of `g` is invertible:
its determinant reduces to the nonzero determinant of `ρbar g`. -/
private theorem isUnit_toMatrix_action (g : G) : IsUnit (LinearMap.toMatrix b b (D.action g)) := by
  rw [isUnit_iff_isUnit_det, isUnit_iff_augmentation_ne_zero]
  have h := (A.augmentation : A.obj.left →+* k).map_det (LinearMap.toMatrix b b (D.action g))
  simp only [RingHom.coe_coe, RingHom.mapMatrix_apply,
    D.map_augmentation_toMatrix_action b hb g] at h
  rw [h]
  exact ((isUnit_iff_isUnit_det _).mp (ρbar g).isUnit).ne_zero

/-- The *lift of a module deformation in a basis* `b` lifting the standard basis of `kⁿ`: `g`
goes to the matrix of its action in `b`. -/
noncomputable def toLift : Lift ρbar A where
  toMonoidHom := IsUnit.liftRight ((LinearMap.toMatrixAlgEquiv b).toMonoidHom.comp D.action)
    fun g ↦ D.isUnit_toMatrix_action b hb g
  isLocallyConstant' := by
    refine IsLocallyConstant.desc _ Units.val ?_ Units.val_injective
    have h : Units.val ∘ IsUnit.liftRight
        ((LinearMap.toMatrixAlgEquiv b).toMonoidHom.comp D.action)
        (fun g ↦ D.isUnit_toMatrix_action b hb g) = (LinearMap.toMatrixAlgEquiv b) ∘ D.action :=
      funext fun g ↦ IsUnit.coe_liftRight _ _ g
    rw [h]
    exact D.isLocallyConstant_action.comp _
  map_augmentation_comp' := MonoidHom.ext fun g ↦ GeneralLinearGroup.ext fun i j ↦ by
    rw [MonoidHom.comp_apply, GeneralLinearGroup.map_apply]
    -- The matrix of the unit `IsUnit.liftRight _ _ g` is the matrix of the action of `g`.
    exact congrFun₂ (D.map_augmentation_toMatrix_action b hb g) i j

/-- The matrix of the lift `D.toLift b hb` at `g` is the matrix of the action of `g` in `b`. -/
@[simp]
theorem coe_toLift_apply (g : G) :
    (D.toLift b hb g : Matrix n n A.obj.left) = LinearMap.toMatrix b b (D.action g) :=
  IsUnit.coe_liftRight _ _ g

/-- The determinant of the lift of a module deformation in a basis is the determinant of the
action. -/
theorem det_toLift_apply (g : G) :
    (D.toLift b hb g : Matrix n n A.obj.left).det = LinearMap.det (D.action g) := by
  rw [coe_toLift_apply, LinearMap.det_toMatrix]

/-- The trace of the lift of a module deformation in a basis is the trace of the action. -/
theorem trace_toLift_apply (g : G) :
    (D.toLift b hb g : Matrix n n A.obj.left).trace =
      LinearMap.trace A.obj.left D (D.action g) := by
  rw [coe_toLift_apply, LinearMap.trace_eq_matrix_trace A.obj.left b]

/-- The characteristic polynomial of the lift of a module deformation in a basis is the
characteristic polynomial of the action. -/
theorem charpoly_toLift_apply (g : G) :
    (D.toLift b hb g : Matrix n n A.obj.left).charpoly = (D.action g).charpoly := by
  rw [coe_toLift_apply, LinearMap.charpoly_toMatrix]

end ToLift

/-- The lift of a module deformation in a basis depends only on the basis. -/
private theorem toLift_congr (D : ModuleDeformation ρbar A) {b b' : Module.Basis n A.obj.left D}
    (h : b = b') (hb : ∀ i, D.reduction (b i) = Pi.single i 1)
    (hb' : ∀ i, D.reduction (b' i) = Pi.single i 1) : D.toLift b hb = D.toLift b' hb' := by
  subst h
  rfl

/-- An isomorphism `e` of module deformations sends the lift in a basis `b` to the lift in the
basis `e ∘ b`. -/
theorem toLift_map_equiv {D D' : ModuleDeformation ρbar A} (e : D.Equiv D')
    (b : Module.Basis n A.obj.left D) (hb : ∀ i, D.reduction (b i) = Pi.single i 1) :
    D'.toLift (b.map e.toLinearEquiv) (fun i ↦ by simpa using hb i) = D.toLift b hb := by
  ext g : 1
  refine Units.ext (Matrix.ext fun i j ↦ ?_)
  -- `e` is equivariant, so `e⁻¹ (g • e (b j)) = g • b j`.
  have h : e.toLinearEquiv.symm (D'.action g (e.toLinearEquiv (b j))) = D.action g (b j) :=
    e.toLinearEquiv.symm_apply_eq.mpr (e.map_action g (b j)).symm
  simp only [coe_toLift_apply, LinearMap.toMatrix_apply, Module.Basis.map_apply,
    Module.Basis.map_repr, LinearEquiv.trans_apply, h]

/-- The lift of the base change of a module deformation, in the base change of a basis, is the
pushforward of the lift. -/
theorem toLift_baseChange (f : A ⟶ B) (D : ModuleDeformation ρbar A)
    (b : Module.Basis n A.obj.left D) (hb : ∀ i, D.reduction (b i) = Pi.single i 1) :
    (D.baseChange f).toLift (D.baseChangeBasis f b) (fun i ↦ by simp [hb]) =
      Lift.map f (D.toLift b hb) := by
  ext g : 1
  refine Units.ext (Matrix.ext fun i j ↦ ?_)
  simp [LinearMap.toMatrix_apply]

section ChangeOfBasis

variable (D : ModuleDeformation ρbar A) {b b' : Module.Basis n A.obj.left D}
  (hb : ∀ i, D.reduction (b i) = Pi.single i 1) (hb' : ∀ i, D.reduction (b' i) = Pi.single i 1)

/-- Changing the basis conjugates the lift of a module deformation by the change-of-basis matrix,
an element of the strict kernel. -/
theorem exists_smul_toLift_eq :
    ∃ a : A.strictKernel n, ((a : GL n A.obj.left) : Matrix n n A.obj.left) = b'.toMatrix b ∧
      a • D.toLift b hb = D.toLift b' hb' := by
  let := b'.invertibleToMatrix b
  -- The change-of-basis matrix reduces to the identity.
  have hmem : unitOfInvertible (b'.toMatrix b) ∈ A.strictKernel n :=
    mem_strictKernel_iff_apply.mpr fun i j ↦ by
      simp [Module.Basis.toMatrix_apply, D.augmentation_repr b' hb', hb, Pi.single_apply,
        Matrix.one_apply]
  refine ⟨⟨_, hmem⟩, val_unitOfInvertible _, ?_⟩
  ext g : 1
  refine Units.ext ?_
  rw [Lift.smul_apply, Units.val_mul, Units.val_mul, coe_toLift_apply, coe_toLift_apply]
  exact basis_toMatrix_mul_linearMap_toMatrix_mul_basis_toMatrix b' b b' b (D.action g)

include hb in
/-- Every conjugate of the lift of a module deformation by an element of the strict kernel is the
lift in another basis lifting the standard basis of `kⁿ`. -/
theorem exists_toLift_eq_smul (a : A.strictKernel n) :
    ∃ (b' : Module.Basis n A.obj.left D) (hb' : ∀ i, D.reduction (b' i) = Pi.single i 1),
      D.toLift b' hb' = a • D.toLift b hb := by
  -- The basis `b'` has change-of-basis matrix `b.toMatrix b' = a⁻¹`.
  let M : Matrix n n A.obj.left := ((a⁻¹ : A.strictKernel n) : GL n A.obj.left)
  have hM : IsUnit M.det := (isUnit_iff_isUnit_det _).mp (Units.isUnit _)
  let b' := b.map (Matrix.toLinearEquiv b M hM)
  have hrepr (i j : n) : b.repr (b' j) i = M i j := by
    rw [Module.Basis.map_apply, Matrix.toLinearEquiv_apply, ← LinearMap.toMatrix_apply,
      LinearMap.toMatrix_toLin]
  have hb' (j : n) : D.reduction (b' j) = Pi.single j 1 := funext fun i ↦ by
    -- The matrix `M = a⁻¹` lies in the strict kernel, so it reduces to the identity.
    rw [← D.augmentation_repr b hb, hrepr, mem_strictKernel_iff_apply.mp (a⁻¹).property,
      Matrix.one_apply, Pi.single_apply]
  obtain ⟨a', ha', h⟩ := D.exists_smul_toLift_eq hb hb'
  refine ⟨b', hb', h.symm.trans (congrArg (· • D.toLift b hb) (Subtype.ext (Units.ext ?_)))⟩
  have hM' : b.toMatrix b' = M := Matrix.ext fun i j ↦ hrepr i j
  -- Both `b'.toMatrix b` and `a` are inverse to `b.toMatrix b' = M = a⁻¹`.
  have hinv : M * ((a : GL n A.obj.left) : Matrix n n A.obj.left) = 1 := by
    simp [M]
  rw [ha', ← Matrix.inv_eq_right_inv hinv, ← hM', Matrix.inv_eq_left_inv
    (b'.toMatrix_mul_toMatrix_flip b)]

end ChangeOfBasis

end ModuleDeformation

namespace FramedModuleDeformation

variable {ρbar : G →* GL n k} {A B : ArtinLocalAlg Λ k}

/-- The *lift of a framed module deformation*: the matrices of the action in the framing. -/
-- An abbreviation, so that the lemmas about `ModuleDeformation.toLift` apply to it.
noncomputable abbrev toLift (D : FramedModuleDeformation ρbar A) : Lift ρbar A :=
  D.toModuleDeformation.toLift D.basis D.reduction_basis

/-- The lift of the base change of a framed module deformation is the pushforward of its lift. -/
@[simp]
theorem toLift_baseChange (f : A ⟶ B) (D : FramedModuleDeformation ρbar A) :
    (D.baseChange f).toLift = Lift.map f D.toLift :=
  D.toModuleDeformation.toLift_baseChange f D.basis D.reduction_basis

/-- Isomorphic framed module deformations have the same lift. -/
theorem toLift_eq_of_equiv {D D' : FramedModuleDeformation ρbar A} (e : D.Equiv D') :
    D.toLift = D'.toLift := by
  have h : D.basis.map e.toLinearEquiv = D'.basis := Module.Basis.eq_of_apply_eq fun i ↦ by
    simp
  exact (D.toModuleDeformation.toLift_map_equiv e.toModuleDeformationEquiv D.basis
    D.reduction_basis).symm.trans (D'.toModuleDeformation.toLift_congr h _ _)

/-- The isomorphism between framed module deformations with the same lift, sending one framing to
the other. -/
noncomputable def equivOfToLiftEq {D D' : FramedModuleDeformation ρbar A}
    (h : D.toLift = D'.toLift) : D.Equiv D' where
  toRepresentationEquiv := .mk (basisEquiv D D') fun g ↦
    (LinearMap.toMatrix D.basis D'.basis).injective <| by
      have hg := congrArg (fun ρ : Lift ρbar A ↦ (ρ g : Matrix n n A.obj.left)) h
      simp only [ModuleDeformation.coe_toLift_apply] at hg
      have he : LinearMap.toMatrix D.basis D'.basis (basisEquiv D D').toLinearMap = 1 :=
        Matrix.ext fun i j ↦ by
          simp [LinearMap.toMatrix_apply, Matrix.one_apply, Finsupp.single_apply, eq_comm]
      rw [LinearMap.toMatrix_comp D.basis D.basis D'.basis,
        LinearMap.toMatrix_comp D.basis D'.basis D'.basis, he, hg,
        Matrix.one_mul, Matrix.mul_one]
  reduction_apply' := reduction_basisEquiv D D'
  map_basis' := basisEquiv_basis D D'

/-- Two framed module deformations are isomorphic exactly when they have the same lift. -/
theorem nonempty_equiv_iff {D D' : FramedModuleDeformation ρbar A} :
    Nonempty (D.Equiv D') ↔ D.toLift = D'.toLift :=
  ⟨fun ⟨e⟩ ↦ toLift_eq_of_equiv e, fun h ↦ ⟨equivOfToLiftEq h⟩⟩

section OfLift

variable (n) in
/-- The standard basis of `Fin (Fintype.card n) → A`, reindexed by `n`. -/
private noncomputable def stdBasis (A : ArtinLocalAlg Λ k) :
    Module.Basis n A.obj.left (Fin (Fintype.card n) → A.obj.left) :=
  (Pi.basisFun A.obj.left (Fin (Fintype.card n))).reindex (Fintype.equivFin n).symm

variable (n) in
/-- The reduction map `Fin (Fintype.card n) → A` to `kⁿ`: the augmentations of the coordinates in
the standard basis reindexed by `n`. -/
private noncomputable def stdReduction (A : ArtinLocalAlg Λ k) :
    (Fin (Fintype.card n) → A.obj.left) →ₛₗ[(A.augmentation : A.obj.left →+* k)] n → k where
  toFun v i := A.augmentation ((stdBasis n A).repr v i)
  map_add' v w := funext fun i ↦ by simp
  map_smul' a v := funext fun i ↦ by simp

omit [DecidableEq n] in
variable (n) in
private theorem stdReduction_apply (A : ArtinLocalAlg Λ k) (v : Fin (Fintype.card n) → A.obj.left)
    (i : n) : stdReduction n A v i = A.augmentation ((stdBasis n A).repr v i) :=
  rfl

/-- The *framed module deformation of a lift* `ρ`: the free module `Fin (Fintype.card n) → A`,
on which `g` acts by the matrix `ρ g` in the standard basis reindexed by `n`, framed by that
basis. -/
noncomputable def ofLift (ρ : Lift ρbar A) : FramedModuleDeformation ρbar A where
  carrier := Fin (Fintype.card n) → A.obj.left
  action :=
    { toFun g := Matrix.toLin (stdBasis n A) (stdBasis n A) (ρ g : Matrix n n A.obj.left)
      map_one' := by rw [map_one, Units.val_one, Matrix.toLin_one, Module.End.one_eq_id]
      map_mul' g g' := by
        rw [map_mul, Units.val_mul, Matrix.toLin_mul _ (stdBasis n A), Module.End.mul_eq_comp] }
  isLocallyConstant_action := ρ.isLocallyConstant.comp fun M : GL n A.obj.left ↦
    Matrix.toLin (stdBasis n A) (stdBasis n A) (M : Matrix n n A.obj.left)
  reduction := stdReduction n A
  surjective_reduction y := by
    refine ⟨(stdBasis n A).equivFun.symm fun i ↦ Function.surjInv A.augmentation_surjective (y i),
      funext fun i ↦ ?_⟩
    rw [stdReduction_apply, ← Module.Basis.equivFun_apply, LinearEquiv.apply_symm_apply]
    exact Function.surjInv_eq A.augmentation_surjective (y i)
  ker_reduction_le v hv := (stdBasis n A).mem_smul_top_iff.mpr fun i ↦
    augmentation_eq_zero_iff.mp (congrFun (LinearMap.mem_ker.mp hv) i)
  reduction_action g v := funext fun i ↦ by
    -- The coordinates of `ρ g • v` are those of `v` multiplied by the matrix `ρ g`, and the
    -- matrix `ρ g` reduces to `ρbar g`.
    have hρ : (ρ g : Matrix n n A.obj.left).map A.augmentation = ρbar g :=
      congrArg Units.val (ρ.map_augmentation_apply g)
    have hv : stdReduction n A v = A.augmentation ∘ (stdBasis n A).repr v :=
      funext (stdReduction_apply n A v)
    simpa [stdReduction_apply, Matrix.repr_toLin, ← hρ, hv] using
      RingHom.map_mulVec (A.augmentation : A.obj.left →+* k) (ρ g : Matrix n n A.obj.left)
        ((stdBasis n A).repr v) i
  basis := stdBasis n A
  reduction_basis i := funext fun j ↦ by
    simp [stdReduction_apply, Finsupp.single_apply, Pi.single_apply, eq_comm]

/-- In the framed module deformation of a lift `ρ`, `g` acts by the matrix `ρ g` in the
framing. -/
@[simp]
theorem ofLift_action_apply (ρ : Lift ρbar A) (g : G) :
    (ofLift ρ).action g =
      Matrix.toLin (ofLift ρ).basis (ofLift ρ).basis (ρ g : Matrix n n A.obj.left) :=
  (rfl)

/-- The lift of the framed module deformation of a lift `ρ` is `ρ`. -/
@[simp]
theorem toLift_ofLift (ρ : Lift ρbar A) : (ofLift ρ).toLift = ρ := by
  ext g : 1
  refine Units.ext ?_
  rw [ModuleDeformation.coe_toLift_apply, ofLift_action_apply, LinearMap.toMatrix_toLin]

end OfLift

end FramedModuleDeformation

namespace ModuleDeformation

variable {ρbar : G →* GL n k} {A : ArtinLocalAlg Λ k}

/-- The lifts of a module deformation in two bases lifting the standard basis of `kⁿ` have the same
strict class. -/
theorem mk_toLift_eq_mk_toLift (D : ModuleDeformation ρbar A) {b b' : Module.Basis n A.obj.left D}
    (hb : ∀ i, D.reduction (b i) = Pi.single i 1) (hb' : ∀ i, D.reduction (b' i) = Pi.single i 1) :
    StrictClass.mk (D.toLift b hb) = StrictClass.mk (D.toLift b' hb') := by
  obtain ⟨a, -, h⟩ := D.exists_smul_toLift_eq hb hb'
  exact StrictClass.mk_eq_mk_iff.mpr ⟨a, h⟩

/-- Isomorphic module deformations have lifts with the same strict class, in any bases lifting the
standard basis of `kⁿ`. -/
theorem mk_toLift_eq_of_equiv {D D' : ModuleDeformation ρbar A} (e : D.Equiv D')
    {b : Module.Basis n A.obj.left D} {b' : Module.Basis n A.obj.left D'}
    (hb : ∀ i, D.reduction (b i) = Pi.single i 1) (hb' : ∀ i, D'.reduction (b' i) = Pi.single i 1) :
    StrictClass.mk (D.toLift b hb) = StrictClass.mk (D'.toLift b' hb') := by
  rw [← toLift_map_equiv e b hb]
  exact D'.mk_toLift_eq_mk_toLift _ hb'

end ModuleDeformation

section Comparison

variable (ρbar : G →* GL n k) (A : ArtinLocalAlg Λ k)

/-- Lifts of `ρbar` to `A` are isomorphism classes of framed module deformations: a lift goes to
the class of its framed module deformation, and the class of a framed module deformation goes to
its lift. -/
noncomputable def liftEquivFramedModuleDeformationClass :
    Lift ρbar A ≃ FramedModuleDeformationClass ρbar A where
  toFun ρ := .mk (.ofLift ρ)
  invFun := FramedModuleDeformationClass.lift FramedModuleDeformation.toLift fun _ _ e ↦
    FramedModuleDeformation.toLift_eq_of_equiv e
  left_inv ρ :=
    (FramedModuleDeformationClass.lift_mk _ _ _).trans (FramedModuleDeformation.toLift_ofLift ρ)
  right_inv c := by
    obtain ⟨D, rfl⟩ := FramedModuleDeformationClass.mk_surjective c
    rw [FramedModuleDeformationClass.lift_mk]
    exact FramedModuleDeformationClass.mk_eq_mk
      (FramedModuleDeformation.equivOfToLiftEq (FramedModuleDeformation.toLift_ofLift _))

variable {ρbar A}

/-- The bijection sends a lift to the class of its framed module deformation. -/
@[simp]
theorem liftEquivFramedModuleDeformationClass_apply (ρ : Lift ρbar A) :
    liftEquivFramedModuleDeformationClass ρbar A ρ = .mk (.ofLift ρ) :=
  (rfl)

/-- The inverse bijection sends the class of a framed module deformation to its lift. -/
@[simp]
theorem liftEquivFramedModuleDeformationClass_symm_mk (D : FramedModuleDeformation ρbar A) :
    (liftEquivFramedModuleDeformationClass ρbar A).symm (.mk D) = D.toLift :=
  FramedModuleDeformationClass.lift_mk _ _ D

/-- The bijection between lifts and classes of framed module deformations commutes with
pushforward and base change. -/
theorem liftEquivFramedModuleDeformationClass_map {B : ArtinLocalAlg Λ k} (f : A ⟶ B)
    (ρ : Lift ρbar A) :
    liftEquivFramedModuleDeformationClass ρbar B (Lift.map f ρ) =
      FramedModuleDeformationClass.map f (liftEquivFramedModuleDeformationClass ρbar A ρ) := by
  apply (liftEquivFramedModuleDeformationClass ρbar B).symm.injective
  simp

/-- Conjugating a lift by an element of the strict kernel does not change the isomorphism class
of the underlying module deformation of its framed module deformation. -/
private theorem forget_mk_ofLift_smul (a : A.strictKernel n) (ρ : Lift ρbar A) :
    FramedModuleDeformationClass.forget (.mk (.ofLift (a • ρ))) =
      FramedModuleDeformationClass.forget (.mk (.ofLift ρ)) := by
  obtain ⟨b, hb, h⟩ := (FramedModuleDeformation.ofLift ρ).toModuleDeformation.exists_toLift_eq_smul
    (FramedModuleDeformation.ofLift ρ).reduction_basis a
  let D : FramedModuleDeformation ρbar A :=
    ⟨(FramedModuleDeformation.ofLift ρ).toModuleDeformation, b, hb⟩
  have hD : D.toLift = (FramedModuleDeformation.ofLift (a • ρ)).toLift := by
    rw [FramedModuleDeformation.toLift_ofLift]
    exact h.trans (congrArg (a • ·) (FramedModuleDeformation.toLift_ofLift ρ))
  rw [← FramedModuleDeformationClass.mk_eq_mk (FramedModuleDeformation.equivOfToLiftEq hD),
    FramedModuleDeformationClass.forget_mk, FramedModuleDeformationClass.forget_mk]

variable (ρbar A) in
/-- Strict classes of lifts of `ρbar` to `A` are isomorphism classes of module deformations: the
strict class of a lift goes to the class of its module deformation, and the class of a module
deformation goes to the strict class of its lift in any basis lifting the standard basis of
`kⁿ`. -/
noncomputable def strictClassEquivModuleDeformationClass :
    StrictClass ρbar A ≃ ModuleDeformationClass ρbar A where
  toFun := StrictClass.lift (fun ρ ↦ FramedModuleDeformationClass.forget (.mk (.ofLift ρ)))
    forget_mk_ofLift_smul
  invFun := ModuleDeformationClass.lift
    (fun D ↦ StrictClass.mk (D.toLift D.exists_basis.choose D.exists_basis.choose_spec))
    fun _ _ e ↦ ModuleDeformation.mk_toLift_eq_of_equiv e _ _
  left_inv c := by
    obtain ⟨ρ, rfl⟩ := StrictClass.mk_surjective c
    rw [StrictClass.lift_mk, FramedModuleDeformationClass.forget_mk, ModuleDeformationClass.lift_mk,
      ModuleDeformation.mk_toLift_eq_mk_toLift _ _
        (FramedModuleDeformation.ofLift ρ).reduction_basis]
    exact congrArg StrictClass.mk (FramedModuleDeformation.toLift_ofLift ρ)
  right_inv c := by
    obtain ⟨D, rfl⟩ := ModuleDeformationClass.mk_surjective c
    rw [ModuleDeformationClass.lift_mk, StrictClass.lift_mk]
    let D' : FramedModuleDeformation ρbar A :=
      ⟨D, D.exists_basis.choose, D.exists_basis.choose_spec⟩
    rw [FramedModuleDeformationClass.mk_eq_mk (FramedModuleDeformation.equivOfToLiftEq
      (D := .ofLift D'.toLift) (D' := D') (FramedModuleDeformation.toLift_ofLift _)),
      FramedModuleDeformationClass.forget_mk]

/-- The strict class of a lift corresponds to the class of the module deformation obtained by
forgetting the framing of its framed module deformation. -/
@[simp]
theorem strictClassEquivModuleDeformationClass_mk (ρ : Lift ρbar A) :
    strictClassEquivModuleDeformationClass ρbar A (StrictClass.mk ρ) =
      (liftEquivFramedModuleDeformationClass ρbar A ρ).forget :=
  StrictClass.lift_mk _ _ ρ

/-- The inverse of `strictClassEquivModuleDeformationClass` sends the class of a module deformation
to the strict class of its lift in any basis lifting the standard basis of `kⁿ`. -/
theorem strictClassEquivModuleDeformationClass_symm_mk (D : ModuleDeformation ρbar A)
    (b : Module.Basis n A.obj.left D) (hb : ∀ i, D.reduction (b i) = Pi.single i 1) :
    (strictClassEquivModuleDeformationClass ρbar A).symm (.mk D) =
      StrictClass.mk (D.toLift b hb) :=
  (ModuleDeformationClass.lift_mk _ _ D).trans (D.mk_toLift_eq_mk_toLift _ hb)

/-- The bijection between strict classes and classes of module deformations commutes with
pushforward and base change. -/
theorem strictClassEquivModuleDeformationClass_map {B : ArtinLocalAlg Λ k} (f : A ⟶ B)
    (c : StrictClass ρbar A) :
    strictClassEquivModuleDeformationClass ρbar B (StrictClass.map f c) =
      ModuleDeformationClass.map f (strictClassEquivModuleDeformationClass ρbar A c) := by
  obtain ⟨ρ, rfl⟩ := StrictClass.mk_surjective c
  rw [StrictClass.map_mk, strictClassEquivModuleDeformationClass_mk,
    strictClassEquivModuleDeformationClass_mk, liftEquivFramedModuleDeformationClass_map,
    FramedModuleDeformationClass.forget_map]

end Comparison

variable (Λ) (ρbar : G →* GL n k)

/-- The natural isomorphism `Lift_ρbar ≅ Def^{mod,□}_ρbar` between the framed lifting functor and
the framed module deformation functor, after lifting the universe of the former. -/
noncomputable def liftFunctorIsoFramedModuleDeformationFunctor :
    liftFunctor Λ ρbar ⋙ uliftFunctor.{v + 1} ≅ framedModuleDeformationFunctor Λ ρbar :=
  NatIso.ofComponents
    (fun A ↦ (Equiv.ulift.trans (liftEquivFramedModuleDeformationClass ρbar A)).toIso)
    fun f ↦ by
      ext ⟨ρ⟩ : 3
      exact liftEquivFramedModuleDeformationClass_map f ρ

/-- The components of `liftFunctorIsoFramedModuleDeformationFunctor` are the bijections
`liftEquivFramedModuleDeformationClass`. -/
@[simp]
theorem liftFunctorIsoFramedModuleDeformationFunctor_hom_app_apply (A : ArtinLocalAlg Λ k)
    (ρ : Lift ρbar A) :
    ConcreteCategory.hom (X := ULift.{v + 1} ((liftFunctor Λ ρbar).obj A))
        ((liftFunctorIsoFramedModuleDeformationFunctor Λ ρbar).hom.app A) (ULift.up ρ) =
      liftEquivFramedModuleDeformationClass ρbar A ρ :=
  (rfl)

/-- The inverse components of `liftFunctorIsoFramedModuleDeformationFunctor` are the inverses of
the bijections `liftEquivFramedModuleDeformationClass`. -/
@[simp]
theorem liftFunctorIsoFramedModuleDeformationFunctor_inv_app_apply (A : ArtinLocalAlg Λ k)
    (c : FramedModuleDeformationClass ρbar A) :
    ConcreteCategory.hom (Y := ULift.{v + 1} ((liftFunctor Λ ρbar).obj A))
        ((liftFunctorIsoFramedModuleDeformationFunctor Λ ρbar).inv.app A) c =
      ULift.up ((liftEquivFramedModuleDeformationClass ρbar A).symm c) :=
  (rfl)

/-- The natural isomorphism `Def_ρbar ≅ Def^mod_ρbar` between the deformation functor of strict
classes and the module deformation functor, after lifting the universe of the former. -/
noncomputable def strictClassFunctorIsoModuleDeformationFunctor :
    strictClassFunctor Λ ρbar ⋙ uliftFunctor.{v + 1} ≅ moduleDeformationFunctor Λ ρbar :=
  NatIso.ofComponents
    (fun A ↦ (Equiv.ulift.trans (strictClassEquivModuleDeformationClass ρbar A)).toIso)
    fun f ↦ by
      ext ⟨c⟩ : 3
      exact strictClassEquivModuleDeformationClass_map f c

/-- The components of `strictClassFunctorIsoModuleDeformationFunctor` are the bijections
`strictClassEquivModuleDeformationClass`. -/
@[simp]
theorem strictClassFunctorIsoModuleDeformationFunctor_hom_app_apply (A : ArtinLocalAlg Λ k)
    (c : StrictClass ρbar A) :
    ConcreteCategory.hom (X := ULift.{v + 1} ((strictClassFunctor Λ ρbar).obj A))
        ((strictClassFunctorIsoModuleDeformationFunctor Λ ρbar).hom.app A) (ULift.up c) =
      strictClassEquivModuleDeformationClass ρbar A c :=
  (rfl)

/-- The inverse components of `strictClassFunctorIsoModuleDeformationFunctor` are the inverses of
the bijections `strictClassEquivModuleDeformationClass`. -/
@[simp]
theorem strictClassFunctorIsoModuleDeformationFunctor_inv_app_apply (A : ArtinLocalAlg Λ k)
    (c : ModuleDeformationClass ρbar A) :
    ConcreteCategory.hom (Y := ULift.{v + 1} ((strictClassFunctor Λ ρbar).obj A))
        ((strictClassFunctorIsoModuleDeformationFunctor Λ ρbar).inv.app A) c =
      ULift.up ((strictClassEquivModuleDeformationClass ρbar A).symm c) :=
  (rfl)

end TauCeti.Deformation
