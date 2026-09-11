/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.QuadraticForm.TensorProduct
public import TauCeti.LinearAlgebra.QuadraticForm.Representation
import Mathlib.LinearAlgebra.TensorProduct.Prod
public import Mathlib.RingTheory.Flat.Basic
import TauCeti.LinearAlgebra.BilinearForm.BaseChange

/-!
# Base change of quadratic forms

This file supplies the functorial API for extending quadratic spaces along a commutative algebra.
It lifts isometries and isometric equivalences by extending their underlying linear maps, records
the interaction with the additive operations on forms, and proves that finite-dimensional
nondegenerate forms remain nondegenerate over a field extension.

These results complement Mathlib's construction `QuadraticForm.baseChange` and its pure-tensor
evaluation theorem.  They allow localizations of a quadratic space to inherit maps, injective
representations, isotropy, and regularity from the original space without choosing bases in each
completion.
-/

public section
noncomputable section

open scoped TensorProduct

universe uR uA uM uN uP

section CommRing

variable {R : Type uR} {A : Type uA} [CommRing R] [CommRing A] [Algebra R A]
variable [Invertible (2 : R)]
variable {M : Type uM} {N : Type uN} {P : Type uP}
variable [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
variable [AddCommGroup P] [Module R P]

variable {Q₁ : _root_.QuadraticForm R M} {Q₂ : _root_.QuadraticForm R N}
variable {Q₃ : _root_.QuadraticForm R P}

/-- Base change of an isometry of quadratic forms.

Unlike `QuadraticMap.Isometry.tmul`, this construction is heterobasic: the original forms are
over `R`, while their base changes are over the possibly different algebra `A`. -/
def QuadraticMap.Isometry.baseChange (f : Q₁ →qᵢ Q₂) (A : Type uA)
    [CommRing A] [Algebra R A] :
    Q₁.baseChange A →qᵢ Q₂.baseChange A where
  toLinearMap := f.toLinearMap.baseChange A
  map_app' x := by
    have h : (Q₂.baseChange A).comp (f.toLinearMap.baseChange A) = Q₁.baseChange A := by
      apply _root_.baseChange_ext
      intro m
      simp
    exact DFunLike.congr_fun h x

/-- On pure tensors, base change of an isometry applies the original isometry to the vector. -/
@[simp]
theorem QuadraticMap.Isometry.baseChange_tmul (f : Q₁ →qᵢ Q₂) (a : A) (m : M) :
    QuadraticMap.Isometry.baseChange f A (a ⊗ₜ m) = a ⊗ₜ f m :=
  LinearMap.baseChange_tmul f.toLinearMap a m

/-- The linear map underlying a base-changed isometry is the base change of the original linear
map. -/
@[simp]
theorem QuadraticMap.Isometry.baseChange_toLinearMap (f : Q₁ →qᵢ Q₂) :
    (QuadraticMap.Isometry.baseChange f A).toLinearMap = f.toLinearMap.baseChange A := by
  apply TensorProduct.AlgebraTensorModule.ext
  intro a m
  simp

/-- Base change sends the identity isometry to the identity isometry. -/
@[simp]
theorem QuadraticMap.Isometry.baseChange_id (Q : _root_.QuadraticForm R M) :
    QuadraticMap.Isometry.baseChange (_root_.QuadraticMap.Isometry.id Q) A =
      _root_.QuadraticMap.Isometry.id (Q.baseChange A) := by
  apply _root_.QuadraticMap.Isometry.ext
  intro x
  have h : (QuadraticMap.Isometry.baseChange
      (_root_.QuadraticMap.Isometry.id Q) A).toLinearMap =
      (_root_.QuadraticMap.Isometry.id (Q.baseChange A)).toLinearMap :=
    LinearMap.baseChange_id
  exact DFunLike.congr_fun h x

/-- Base change commutes with composition of isometries. -/
@[simp]
theorem QuadraticMap.Isometry.baseChange_comp (g : Q₂ →qᵢ Q₃) (f : Q₁ →qᵢ Q₂) :
    QuadraticMap.Isometry.baseChange (g.comp f) A =
      (QuadraticMap.Isometry.baseChange g A).comp
        (QuadraticMap.Isometry.baseChange f A) := by
  apply _root_.QuadraticMap.Isometry.ext
  intro x
  have h : (QuadraticMap.Isometry.baseChange (g.comp f) A).toLinearMap =
      ((QuadraticMap.Isometry.baseChange g A).comp
        (QuadraticMap.Isometry.baseChange f A)).toLinearMap :=
    LinearMap.baseChange_comp f.toLinearMap g.toLinearMap
  exact DFunLike.congr_fun h x

/-- Base change of an isometric equivalence of quadratic forms. -/
def QuadraticMap.IsometryEquiv.baseChange (f : Q₁.IsometryEquiv Q₂) (A : Type uA)
    [CommRing A] [Algebra R A] : (Q₁.baseChange A).IsometryEquiv (Q₂.baseChange A) where
  toLinearEquiv := f.toLinearEquiv.baseChange R A
  map_app' x := (QuadraticMap.Isometry.baseChange f.toIsometry A).map_app x

/-- On pure tensors, base change of an isometric equivalence applies the original equivalence to
the vector. -/
@[simp]
theorem QuadraticMap.IsometryEquiv.baseChange_tmul
    (f : Q₁.IsometryEquiv Q₂) (a : A) (m : M) :
    QuadraticMap.IsometryEquiv.baseChange f A (a ⊗ₜ m) = a ⊗ₜ f m := by
  exact _root_.LinearEquiv.baseChange_tmul R A M N (e := f.toLinearEquiv) a m

/-- The linear equivalence underlying a base-changed isometric equivalence is the base change of
the original linear equivalence. -/
@[simp]
theorem QuadraticMap.IsometryEquiv.baseChange_toLinearEquiv (f : Q₁.IsometryEquiv Q₂) :
    (QuadraticMap.IsometryEquiv.baseChange f A).toLinearEquiv =
      f.toLinearEquiv.baseChange R A := by
  apply LinearEquiv.toLinearMap_injective
  apply TensorProduct.AlgebraTensorModule.ext
  intro a m
  simp

/-- Passing from a base-changed isometric equivalence to an isometry commutes with base change. -/
@[simp]
theorem QuadraticMap.IsometryEquiv.baseChange_toIsometry (f : Q₁.IsometryEquiv Q₂) :
    (QuadraticMap.IsometryEquiv.baseChange f A).toIsometry =
      QuadraticMap.Isometry.baseChange f.toIsometry A := by
  apply _root_.QuadraticMap.Isometry.ext
  intro x
  rw [_root_.QuadraticMap.IsometryEquiv.toIsometry_apply]
  have hbase : (f.toLinearEquiv.baseChange R A M N).toLinearMap =
      f.toLinearEquiv.toLinearMap.baseChange A :=
    _root_.LinearEquiv.coe_baseChange R A M N f.toLinearEquiv
  have h : f.toLinearEquiv.toLinearMap = f.toIsometry.toLinearMap := by
    apply LinearMap.ext
    intro m
    exact (_root_.QuadraticMap.IsometryEquiv.toIsometry_apply f m).symm
  have hmaps :
      (QuadraticMap.IsometryEquiv.baseChange f A).toLinearEquiv.toLinearMap =
        (QuadraticMap.Isometry.baseChange f.toIsometry A).toLinearMap := by
    rw [QuadraticMap.IsometryEquiv.baseChange_toLinearEquiv,
      QuadraticMap.Isometry.baseChange_toLinearMap, hbase, h]
  exact DFunLike.congr_fun hmaps x

/-- Base change sends the identity isometric equivalence to the identity equivalence. -/
@[simp]
theorem QuadraticMap.IsometryEquiv.baseChange_refl (Q : _root_.QuadraticForm R M) :
    QuadraticMap.IsometryEquiv.baseChange (_root_.QuadraticMap.IsometryEquiv.refl Q) A =
      _root_.QuadraticMap.IsometryEquiv.refl (Q.baseChange A) := by
  apply DFunLike.ext _ _
  intro x
  have h : (QuadraticMap.IsometryEquiv.baseChange
      (_root_.QuadraticMap.IsometryEquiv.refl Q) A).toLinearEquiv.toLinearMap =
      (_root_.QuadraticMap.IsometryEquiv.refl (Q.baseChange A)).toLinearEquiv.toLinearMap :=
    LinearMap.baseChange_id
  exact DFunLike.congr_fun h x

/-- Base change commutes with composition of isometric equivalences. -/
@[simp]
theorem QuadraticMap.IsometryEquiv.baseChange_trans
    (f : Q₁.IsometryEquiv Q₂) (g : Q₂.IsometryEquiv Q₃) :
    QuadraticMap.IsometryEquiv.baseChange (f.trans g) A =
      (QuadraticMap.IsometryEquiv.baseChange f A).trans
        (QuadraticMap.IsometryEquiv.baseChange g A) := by
  apply DFunLike.ext _ _
  intro x
  have h : (QuadraticMap.IsometryEquiv.baseChange (f.trans g) A).toLinearEquiv =
      ((QuadraticMap.IsometryEquiv.baseChange f A).trans
        (QuadraticMap.IsometryEquiv.baseChange g A)).toLinearEquiv :=
    LinearEquiv.baseChange_trans R A M N f.toLinearEquiv g.toLinearEquiv
  exact DFunLike.congr_fun h x

/-- Base change commutes with inversion of isometric equivalences. -/
@[simp]
theorem QuadraticMap.IsometryEquiv.baseChange_symm (f : Q₁.IsometryEquiv Q₂) :
    QuadraticMap.IsometryEquiv.baseChange f.symm A =
      (QuadraticMap.IsometryEquiv.baseChange f A).symm := by
  apply DFunLike.ext _ _
  intro x
  have h : (QuadraticMap.IsometryEquiv.baseChange f.symm A).toLinearEquiv =
      ((QuadraticMap.IsometryEquiv.baseChange f A).symm).toLinearEquiv :=
    LinearEquiv.baseChange_symm R A M N f.toLinearEquiv
  exact DFunLike.congr_fun h x

/-- Isometric quadratic forms remain isometric after base change. -/
theorem QuadraticMap.Equivalent.baseChange (h : Q₁.Equivalent Q₂) (A : Type uA)
    [CommRing A] [Algebra R A] : (Q₁.baseChange A).Equivalent (Q₂.baseChange A) :=
  h.elim fun f ↦ ⟨QuadraticMap.IsometryEquiv.baseChange f A⟩

/-- A scalar represented by a quadratic form remains represented after base change. -/
theorem QuadraticMap.Represents.baseChange {Q : _root_.QuadraticForm R M} {a : R}
    (h : _root_.QuadraticMap.Represents Q a) :
    _root_.QuadraticMap.Represents (Q.baseChange A) (algebraMap R A a) := by
  rw [_root_.QuadraticMap.represents_iff] at h ⊢
  obtain ⟨v, hv⟩ := h
  exact ⟨1 ⊗ₜ v, by simp [hv, Algebra.smul_def]⟩

namespace QuadraticForm

/-- The canonical equivalence distributing tensor product over a product identifies the base
change of an orthogonal sum with the orthogonal sum of the base changes. -/
def baseChangeProd (Q : _root_.QuadraticForm R M) (Q' : _root_.QuadraticForm R N) :
    (_root_.QuadraticForm.baseChange A (Q.prod Q')).IsometryEquiv
      ((Q.baseChange A).prod (Q'.baseChange A)) where
  toLinearEquiv := TensorProduct.prodRight R A A M N
  map_app' x := by
    have h : ((Q.baseChange A).prod (Q'.baseChange A)).comp
        (TensorProduct.prodRight R A A M N).toLinearMap =
          _root_.QuadraticForm.baseChange A (Q.prod Q') := by
      apply _root_.baseChange_ext
      intro m
      simp [Algebra.smul_def]
    exact DFunLike.congr_fun h x

/-- On pure tensors, the equivalence identifying base change with an orthogonal sum separates the
two components. -/
@[simp]
theorem baseChangeProd_tmul (Q : _root_.QuadraticForm R M)
    (Q' : _root_.QuadraticForm R N) (a : A) (m : M × N) :
    baseChangeProd (A := A) Q Q' (a ⊗ₜ m) = (a ⊗ₜ m.1, a ⊗ₜ m.2) :=
  TensorProduct.prodRight_tmul R A A M N a m

/-- The inverse equivalence identifying an orthogonal sum with a base change combines a pair of
pure tensors with the same scalar into a pure tensor of the paired vectors. -/
@[simp]
theorem baseChangeProd_symm_tmul (Q : _root_.QuadraticForm R M)
    (Q' : _root_.QuadraticForm R N) (a : A) (m : M) (n : N) :
    (baseChangeProd (A := A) Q Q').symm (a ⊗ₜ m, a ⊗ₜ n) = a ⊗ₜ (m, n) :=
  TensorProduct.prodRight_symm_tmul R A A M N a m n

/-- Base change sends the zero quadratic form to the zero quadratic form. -/
@[simp]
theorem baseChange_zero : (0 : _root_.QuadraticForm R M).baseChange A = 0 := by
  apply _root_.baseChange_ext
  simp

/-- Base change commutes with addition of quadratic forms. -/
@[simp]
theorem baseChange_add (Q Q' : _root_.QuadraticForm R M) :
    (Q + Q').baseChange A = Q.baseChange A + Q'.baseChange A := by
  apply _root_.baseChange_ext
  simp [Algebra.smul_def]

/-- Base change commutes with negation of quadratic forms. -/
@[simp]
theorem baseChange_neg (Q : _root_.QuadraticForm R M) :
    (-Q).baseChange A = -(Q.baseChange A) := by
  apply _root_.baseChange_ext
  simp

/-- Base change commutes with subtraction of quadratic forms. -/
@[simp]
theorem baseChange_sub (Q Q' : _root_.QuadraticForm R M) :
    (Q - Q').baseChange A = Q.baseChange A - Q'.baseChange A := by
  apply _root_.baseChange_ext
  simp [Algebra.smul_def]

/-- Scaling before base change agrees with scaling by the image of the scalar afterward. -/
@[simp]
theorem baseChange_smul (r : R) (Q : _root_.QuadraticForm R M) :
    (r • Q).baseChange A = algebraMap R A r • Q.baseChange A := by
  apply _root_.baseChange_ext
  simp [Algebra.smul_def, mul_comm]

/-- Isotropy is preserved by a faithful scalar extension when the underlying module is flat. -/
theorem not_anisotropic_baseChange [FaithfulSMul R A] [Module.Flat R M]
    {Q : _root_.QuadraticForm R M} (hQ : ¬ Q.Anisotropic) :
    ¬ (Q.baseChange A).Anisotropic := by
  rw [QuadraticMap.not_anisotropic_iff_exists] at hQ ⊢
  obtain ⟨x, hx, hQx⟩ := hQ
  refine ⟨1 ⊗ₜ x, ?_, by simp [hQx]⟩
  intro hzero
  apply hx
  apply Module.Flat.tensorProduct_mk_injective R M A
  simpa using hzero

end QuadraticForm

/-- Representation of one quadratic form by another is preserved by flat base change. -/
theorem QuadraticMap.IsRepresentedBy.baseChange [Module.Flat R A]
    {Q : _root_.QuadraticForm R M} {Q' : _root_.QuadraticForm R N}
    (h : Q.IsRepresentedBy Q') :
    (Q.baseChange A).IsRepresentedBy (Q'.baseChange A) := by
  rw [QuadraticMap.isRepresentedBy_iff] at h ⊢
  obtain ⟨f, hf, hQ⟩ := h
  let g : Q →qᵢ Q' := ⟨f, hQ⟩
  refine ⟨(g.baseChange A).toLinearMap, ?_, g.baseChange A |>.map_app⟩
  have hinjective : Function.Injective (f.lTensor A) :=
    Module.Flat.lTensor_preserves_injective_linearMap f hf
  intro x y hxy
  apply hinjective
  simpa only [QuadraticMap.Isometry.baseChange_toLinearMap,
    LinearMap.baseChange_eq_ltensor] using hxy

end CommRing

section Field

variable {K : Type uR} {L : Type uA} [Field K] [Field L] [Algebra K L]
variable {V : Type uM} [AddCommGroup V] [Module K V]

namespace QuadraticForm

/-- A finite-dimensional nondegenerate quadratic form stays nondegenerate after extending its
base field. -/
theorem Nondegenerate.baseChange [Invertible (2 : K)]
    [FiniteDimensional K V] {Q : _root_.QuadraticForm K V} (hQ : Q.Nondegenerate) :
    (Q.baseChange L).Nondegenerate := by
  let : Invertible (2 : L) :=
    (Invertible.map (algebraMap K L) 2).copy 2 (map_ofNat _ _).symm
  let b := Module.Free.chooseBasis K V
  rw [← QuadraticMap.nondegenerate_associated_iff]
  rw [_root_.QuadraticForm.associated_baseChange]
  exact (TauCeti.nondegenerate_baseChange_iff (QuadraticMap.associated Q) b).2
    (QuadraticMap.nondegenerate_associated_iff.mpr hQ)

end QuadraticForm

end Field
