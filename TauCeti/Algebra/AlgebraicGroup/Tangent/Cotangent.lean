/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.Tangent.Naturality
public import Mathlib.LinearAlgebra.Contraction
public import Mathlib.RingTheory.Ideal.Cotangent

/-!
# The cotangent space at the identity

For a commutative bialgebra `A` over `R`, the cotangent space at the identity is
the augmentation ideal modulo its square. Its `R`-linear dual represents
counit-valued derivations, hence the tangent space at the identity.

When this cotangent space is finite projective, the usual tensor–Hom
comparison identifies `B ⊗[R] Module.Dual R (CotangentSpace R A)` with the
`B`-valued tangent space. For a group scheme, this dual is `Lie(G)(R)`.
The coefficient algebra `B` may be noncommutative: the image of `R` is central in `B`.
On pure tensors the comparison sends `b ⊗ f` to the derivation
`a ↦ b * algebraMap R B (f (cotangentMap R A a))`. This is the scalar-extension comparison needed
to turn the coefficient-natural adjoint action into an action on one fixed finite module.

## Main declarations

* `TauCeti.Bialgebra.CotangentSpace`: the augmentation ideal modulo its square.
* `TauCeti.Bialgebra.cotangentMap`: the universal first-order displacement from
  the identity.
* `Derivation.cotangentLinearEquiv`: the duality between the cotangent
  space and counit-valued derivations.
* `Derivation.tangentScalarExtensionEquiv`: scalar extension of the
  cotangent dual when the cotangent space is finite projective.

## References

* J. S. Milne, *Algebraic Groups* (2017), §12 and §14.

The construction uses `Ideal.Cotangent.lift` to descend through the square of the
augmentation ideal and `dualTensorHomEquiv` for the finite projective tensor–Hom comparison.
-/

public section

namespace TauCeti

open _root_.Coalgebra TensorProduct

namespace Bialgebra

variable (R A : Type*) [CommRing R] [CommRing A] [Bialgebra R A]

/-- The augmentation ideal of a commutative bialgebra, the kernel of its counit. -/
abbrev AugmentationIdeal :=
  RingHom.ker (_root_.Bialgebra.counitAlgHom R A : A →+* R)

/-- The cotangent space at the identity of the affine monoid represented by `A`:
the augmentation ideal `ker ε` modulo its square. -/
abbrev CotangentSpace := (AugmentationIdeal R A).Cotangent

/-- The linear displacement of an element from the scalar selected by the counit. -/
private noncomputable def counitDisplacement : A →ₗ[R] A :=
  LinearMap.id - (Algebra.linearMap R A).comp (counit (R := R))

/-- The counit displacement regarded as an element of the augmentation ideal. -/
private noncomputable def augmentationProjection : A →ₗ[R] AugmentationIdeal R A :=
  (counitDisplacement R A).codRestrict ((AugmentationIdeal R A).restrictScalars R)
    fun a => by simp [AugmentationIdeal, counitDisplacement]

/-- The first-order displacement from the identity, sending `a` to the class of
`a - ε(a)` in the augmentation ideal modulo its square. -/
noncomputable def cotangentMap : A →ₗ[R] CotangentSpace R A where
  __ := ((AugmentationIdeal R A).toCotangent.restrictScalars R).comp
    (augmentationProjection R A)

/-- The cotangent map is the class of the displacement from the counit. -/
lemma cotangentMap_apply (a : A) :
    cotangentMap R A a =
      (AugmentationIdeal R A).toCotangent
        ⟨a - algebraMap R A (counit (R := R) a), by simp⟩ := by
  rw [cotangentMap, LinearMap.comp_apply, LinearMap.restrictScalars_apply]
  apply (AugmentationIdeal R A).toCotangent.congr_arg
  apply Subtype.ext
  calc
    ((augmentationProjection R A a : AugmentationIdeal R A) : A) =
        counitDisplacement R A a := LinearMap.codRestrict_apply _ _ a
    _ = _ := by
      rw [counitDisplacement, LinearMap.sub_apply, LinearMap.id_apply,
        LinearMap.comp_apply, Algebra.linearMap_apply]

/-- The cotangent map vanishes on the unit of the coordinate algebra. -/
@[simp]
lemma cotangentMap_one : cotangentMap R A 1 = 0 := by
  rw [cotangentMap_apply]
  apply ((AugmentationIdeal R A).toCotangent_eq_zero _).mpr
  simp

/-- On the augmentation ideal, the cotangent map is the quotient map. -/
@[simp]
lemma cotangentMap_augmentation (x : AugmentationIdeal R A) :
    cotangentMap R A (x : A) = (AugmentationIdeal R A).toCotangent x := by
  rw [cotangentMap_apply]
  have hx : counit (R := R) (x : A) = 0 := by
    exact x.prop
  apply (AugmentationIdeal R A).toCotangent.congr_arg
  ext
  simp [hx]

/-- The cotangent displacement of a product satisfies the Leibniz rule for the
action through the counit. -/
lemma cotangentMap_mul (a b : A) :
    cotangentMap R A (a * b) =
      counit (R := R) a • cotangentMap R A b +
        counit (R := R) b • cotangentMap R A a := by
  rw [cotangentMap_apply, cotangentMap_apply, cotangentMap_apply]
  apply (AugmentationIdeal R A).toCotangent_eq.mpr
  rw [pow_two]
  let x : AugmentationIdeal R A :=
    ⟨a - algebraMap R A (counit (R := R) a), by simp⟩
  let y : AugmentationIdeal R A :=
    ⟨b - algebraMap R A (counit (R := R) b), by simp⟩
  have hxy : (x : A) * (y : A) ∈
      AugmentationIdeal R A * AugmentationIdeal R A :=
    Ideal.mul_mem_mul x.prop y.prop
  convert hxy using 1
  · dsimp [x, y]
    simp only [_root_.Bialgebra.counit_mul, Algebra.smul_def, map_mul]
    ring

end Bialgebra

end TauCeti

namespace Derivation

open TauCeti _root_.Coalgebra TensorProduct

variable {R A B : Type*} [CommRing R] [CommRing A] [Bialgebra R A]

section Ring

variable [Ring B] [Algebra R B]

/-- Construct a counit-valued derivation from a linear map out of the cotangent space. -/
private noncomputable def ofCotangentLinearMap
    (f : Bialgebra.CotangentSpace R A →ₗ[R] B) :
    Derivation R A (Bialgebra.CounitAlgebra R A B) :=
  Derivation.mk'
    ((Bialgebra.CounitAlgebra.algEquivSelf R A B).symm.toLinearMap.comp
      (f.comp (Bialgebra.cotangentMap R A)))
    fun a b => by
      apply (Bialgebra.CounitAlgebra.algEquivSelf R A B).injective
      simp only [LinearMap.comp_apply, AlgEquiv.toLinearMap_apply,
        Bialgebra.cotangentMap_mul, map_add, _root_.map_smul,
        AlgEquiv.apply_symm_apply]
      rw [Bialgebra.CounitAlgebra.algEquivSelf_smul,
        Bialgebra.CounitAlgebra.algEquivSelf_smul]
      simp only [AlgEquiv.apply_symm_apply, Algebra.smul_def]

private lemma algEquivSelf_ofCotangentLinearMap_apply
    (f : Bialgebra.CotangentSpace R A →ₗ[R] B) (a : A) :
    Bialgebra.CounitAlgebra.algEquivSelf R A B (ofCotangentLinearMap f a) =
      f (Bialgebra.cotangentMap R A a) := by
  simp only [ofCotangentLinearMap, Derivation.coe_mk', LinearMap.comp_apply,
    AlgEquiv.toLinearMap_apply, AlgEquiv.apply_symm_apply]

/-- Factor a counit-valued derivation through the cotangent space. -/
private noncomputable def toCotangentLinearMap
    (d : Derivation R A (Bialgebra.CounitAlgebra R A B)) :
    Bialgebra.CotangentSpace R A →ₗ[R] B :=
  Ideal.Cotangent.lift
    ((Bialgebra.CounitAlgebra.algEquivSelf R A B).toLinearMap.comp
      ((d : A →ₗ[R] Bialgebra.CounitAlgebra R A B).comp
        ((Bialgebra.AugmentationIdeal R A).subtype.restrictScalars R)))
    fun x y => by
      simp only [LinearMap.comp_apply, AlgEquiv.toLinearMap_apply,
        LinearMap.restrictScalars_apply, Submodule.coe_subtype, Derivation.coeFn_coe,
        MulMemClass.coe_mul]
      have hx : counit (R := R) (x : A) = 0 := by
        exact x.prop
      have hy : counit (R := R) (y : A) = 0 := by
        exact y.prop
      rw [Bialgebra.CounitAlgebra.algEquivSelf_apply_mul]
      simp only [hx, hy, map_zero, zero_mul, zero_add]

@[simp]
private lemma toCotangentLinearMap_toCotangent
    (d : Derivation R A (Bialgebra.CounitAlgebra R A B))
    (x : Bialgebra.AugmentationIdeal R A) :
    toCotangentLinearMap d ((Bialgebra.AugmentationIdeal R A).toCotangent x) =
      Bialgebra.CounitAlgebra.algEquivSelf R A B (d x) := by
  simp only [toCotangentLinearMap, Ideal.Cotangent.lift_toCotangent,
    LinearMap.comp_apply, AlgEquiv.toLinearMap_apply,
    LinearMap.restrictScalars_apply, Submodule.coe_subtype, Derivation.coeFn_coe]

/-- Linear functionals on the cotangent space are naturally equivalent to
counit-valued derivations, i.e. tangent vectors at the identity. The equivalence
is linear over the coefficient ring, which may be noncommutative. -/
noncomputable def cotangentLinearEquiv :
    (Bialgebra.CotangentSpace R A →ₗ[R] B) ≃ₗ[B]
      Derivation R A (Bialgebra.CounitAlgebra R A B) where
  toFun := ofCotangentLinearMap
  invFun := toCotangentLinearMap
  left_inv f := by
    ext x
    obtain ⟨x, rfl⟩ :=
      (Bialgebra.AugmentationIdeal R A).toCotangent_surjective x
    rw [toCotangentLinearMap_toCotangent,
      algEquivSelf_ofCotangentLinearMap_apply,
      Bialgebra.cotangentMap_augmentation]
  right_inv d := by
    ext a
    apply (Bialgebra.CounitAlgebra.algEquivSelf R A B).injective
    rw [algEquivSelf_ofCotangentLinearMap_apply, Bialgebra.cotangentMap_apply,
      toCotangentLinearMap_toCotangent]
    simp only [map_sub, d.map_algebraMap, sub_zero]
  map_add' f g := by
    ext a
    apply (Bialgebra.CounitAlgebra.algEquivSelf R A B).injective
    simp only [algEquivSelf_ofCotangentLinearMap_apply, LinearMap.add_apply,
      Derivation.add_apply, map_add]
  map_smul' b f := by
    ext a
    apply (Bialgebra.CounitAlgebra.algEquivSelf R A B).injective
    simp only [algEquivSelf_ofCotangentLinearMap_apply, LinearMap.smul_apply,
      RingHom.id_apply, TauCeti.algEquivSelf_derivation_smul_apply, smul_eq_mul]

private lemma cotangentLinearEquiv_apply
    (f : Bialgebra.CotangentSpace R A →ₗ[R] B) :
    cotangentLinearEquiv (R := R) (A := A) (B := B) f =
      ofCotangentLinearMap f := rfl

/-- The cotangent-duality equivalence sends a functional to its value on the
first-order displacement. -/
@[simp]
lemma cotangentLinearEquiv_apply_apply
    (f : Bialgebra.CotangentSpace R A →ₗ[R] B) (a : A) :
    cotangentLinearEquiv f a = f (Bialgebra.cotangentMap R A a) := by
  rw [cotangentLinearEquiv_apply]
  apply (Bialgebra.CounitAlgebra.algEquivSelf R A B).injective
  rw [algEquivSelf_ofCotangentLinearMap_apply]
  -- The functional's `B`-value is transported back to the coefficient synonym.
  exact (Bialgebra.CounitAlgebra.algEquivSelf_apply
    (R := R) (A := A) (B := B)
    (f (Bialgebra.cotangentMap R A a) : Bialgebra.CounitAlgebra R A B)).symm

/-- The inverse cotangent-duality equivalence evaluates a derivation on a
representative in the augmentation ideal. -/
@[simp]
lemma cotangentLinearEquiv_symm_toCotangent
    (d : Derivation R A (Bialgebra.CounitAlgebra R A B))
    (x : Bialgebra.AugmentationIdeal R A) :
    (cotangentLinearEquiv (R := R) (A := A) (B := B)).symm d
        ((Bialgebra.AugmentationIdeal R A).toCotangent x) =
      Bialgebra.CounitAlgebra.algEquivSelf R A B (d x) := by
  exact toCotangentLinearMap_toCotangent d x

end Ring

section ScalarExtension

variable [Ring B] [Algebra R B]
  [Module.Finite R (Bialgebra.CotangentSpace R A)]
  [Module.Projective R (Bialgebra.CotangentSpace R A)]

/-- The tensor–Hom comparison followed by cotangent duality, before extending linearity
from the base ring to the coefficient ring. -/
private noncomputable def tangentScalarExtensionEquivBase :
    B ⊗[R] Module.Dual R (Bialgebra.CotangentSpace R A) ≃ₗ[R]
      Derivation R A (Bialgebra.CounitAlgebra R A B) :=
  TensorProduct.comm R B _ ≪≫ₗ
    dualTensorHomEquiv R (Bialgebra.CotangentSpace R A) B ≪≫ₗ
    (cotangentLinearEquiv (R := R) (A := A) (B := B)).restrictScalars R

private lemma algEquivSelf_tangentScalarExtensionEquivBase_tmul_apply
    (b : B) (f : Module.Dual R (Bialgebra.CotangentSpace R A)) (a : A) :
    Bialgebra.CounitAlgebra.algEquivSelf R A B
        (tangentScalarExtensionEquivBase (R := R) (A := A) (B := B) (b ⊗ₜ[R] f) a) =
      b * algebraMap R B (f (Bialgebra.cotangentMap R A a)) := by
  simp only [tangentScalarExtensionEquivBase, LinearEquiv.trans_apply,
    LinearEquiv.restrictScalars_apply, TensorProduct.comm_tmul,
    cotangentLinearEquiv_apply, algEquivSelf_ofCotangentLinearMap_apply,
    dualTensorHomEquiv_tmul, Algebra.smul_def]
  exact Algebra.commutes _ _

private lemma tangentScalarExtensionEquivBase_map_smul
    (b : B) (x : B ⊗[R] Module.Dual R (Bialgebra.CotangentSpace R A)) :
    tangentScalarExtensionEquivBase (R := R) (A := A) (B := B) (b • x) =
      b • tangentScalarExtensionEquivBase (R := R) (A := A) (B := B) x := by
  induction x using TensorProduct.inductionOn with
  | tmul b' f =>
      ext a
      apply (Bialgebra.CounitAlgebra.algEquivSelf R A B).injective
      rw [TauCeti.algEquivSelf_derivation_smul_apply,
        TensorProduct.smul_tmul', algEquivSelf_tangentScalarExtensionEquivBase_tmul_apply,
        algEquivSelf_tangentScalarExtensionEquivBase_tmul_apply]
      exact smul_mul_assoc b b' _
  | add x y hx hy => simp [smul_add, hx, hy]

/-- Scalar extension of tangent vectors. If the cotangent space is finite projective,
`B` tensored with its dual is naturally the space of `B`-valued tangent vectors.
The equivalence is linear over the coefficient ring, which may be noncommutative. -/
noncomputable def tangentScalarExtensionEquiv :
    B ⊗[R] Module.Dual R (Bialgebra.CotangentSpace R A) ≃ₗ[B]
      Derivation R A (Bialgebra.CounitAlgebra R A B) :=
  { (tangentScalarExtensionEquivBase (R := R) (A := A) (B := B)).toEquiv with
    map_add' := (tangentScalarExtensionEquivBase
      (R := R) (A := A) (B := B)).map_add
    map_smul' := tangentScalarExtensionEquivBase_map_smul }

/-- On pure tensors, scalar extension evaluates the cotangent functional and
multiplies it by the coefficient. The bundled pure-tensor simp rule is
`tangentScalarExtensionEquiv_tmul`. -/
lemma tangentScalarExtensionEquiv_tmul_apply
    (b : B) (f : Module.Dual R (Bialgebra.CotangentSpace R A)) (a : A) :
    tangentScalarExtensionEquiv (R := R) (A := A) (B := B) (b ⊗ₜ[R] f) a =
      b * algebraMap R B (f (Bialgebra.cotangentMap R A a)) := by
  apply (Bialgebra.CounitAlgebra.algEquivSelf R A B).injective
  -- The comparison is computed in `B`, then transported to the coefficient synonym.
  exact (algEquivSelf_tangentScalarExtensionEquivBase_tmul_apply b f a).trans
    (Bialgebra.CounitAlgebra.algEquivSelf_apply
      (R := R) (A := A) (B := B)
      (b * algebraMap R B (f (Bialgebra.cotangentMap R A a)) :
        Bialgebra.CounitAlgebra R A B)).symm

/-- On pure tensors, scalar extension is coefficient change of the cotangent-dual tangent
vector, followed by multiplication by the tensor coefficient. -/
@[simp]
theorem tangentScalarExtensionEquiv_tmul
    (b : B) (f : Module.Dual R (Bialgebra.CotangentSpace R A)) :
    tangentScalarExtensionEquiv (R := R) (A := A) (B := B) (b ⊗ₜ[R] f) =
      b • mapValue (A := A) (Algebra.ofId R B)
        (cotangentLinearEquiv (R := R) (A := A) (B := R) f) := by
  ext a
  apply (Bialgebra.CounitAlgebra.algEquivSelf R A B).injective
  rw [TauCeti.algEquivSelf_derivation_smul_apply,
    mapValue_apply, cotangentLinearEquiv_apply_apply]
  simp only [Algebra.ofId_apply]
  rw [Bialgebra.CounitAlgebra.algEquivSelf_apply
      (R := R) (A := A) (B := B)
      (algebraMap R B (f (Bialgebra.cotangentMap R A a)) :
        Bialgebra.CounitAlgebra R A B)]
  exact algEquivSelf_tangentScalarExtensionEquivBase_tmul_apply b f a

end ScalarExtension

end Derivation
