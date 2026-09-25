/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.QuadraticForm.TensorProduct
public import Mathlib.LinearAlgebra.Charpoly.BaseChange
public import Mathlib.LinearAlgebra.TensorProduct.Pi
public import Mathlib.LinearAlgebra.TensorProduct.Tower
public import TauCeti.LinearAlgebra.QuadraticForm.OrthogonalGroup
public import TauCeti.LinearAlgebra.QuadraticForm.Representation
import Mathlib.LinearAlgebra.TensorProduct.Prod
public import Mathlib.RingTheory.Flat.Basic
import TauCeti.LinearAlgebra.BilinearForm.BaseChange
import TauCeti.LinearAlgebra.TensorProduct.Basis

/-!
# Base change of quadratic forms

This file supplies the functorial API for extending quadratic spaces along a commutative algebra.
It lifts isometries and isometric equivalences by extending their underlying linear maps, records
the interaction with the additive operations on forms, compares direct and successive extension
through a scalar tower, and proves that finite-dimensional nondegenerate forms remain
nondegenerate over a field extension. It also identifies the base change of a diagonal form with
the diagonal form obtained by mapping its coefficients into the target algebra, extends
orthogonal and special orthogonal automorphisms so a quadratic space's rational symmetries act on
each scalar extension, and shows that extending scalars carries the reflection in a vector `v` to
the reflection in `1 ⊗ₜ v`.

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

/-- Polarization after base change, evaluated on pure tensors. -/
@[simp]
theorem polar_baseChange_tmul (Q : _root_.QuadraticForm R M) (a b : A) (x y : M) :
    QuadraticMap.polar (Q.baseChange A) (a ⊗ₜ x) (b ⊗ₜ y) =
      (QuadraticMap.polar Q x y) • (a * b) := by
  let : Invertible (2 : A) := (Invertible.map (algebraMap R A) 2).copy 2
    (map_ofNat _ _).symm
  rw [← QuadraticMap.polarBilin_apply_apply, _root_.QuadraticForm.polarBilin_baseChange,
    LinearMap.BilinForm.baseChange_tmul, QuadraticMap.polarBilin_apply_apply]

section Diagonal

variable {ι : Type*} [Fintype ι]

/-- The canonical coordinate equivalence identifies the base change of a diagonal quadratic form
with the diagonal form obtained by mapping each coefficient into the target algebra. -/
def baseChangeWeightedSumSquares (w : ι → R) :
    (_root_.QuadraticForm.baseChange A
      (QuadraticMap.weightedSumSquares R w)).IsometryEquiv
      (QuadraticMap.weightedSumSquares A fun i => algebraMap R A (w i)) := by
  classical
  refine
    { toLinearEquiv := TensorProduct.piScalarRight R A A ι
      map_app' := fun x => ?_ }
  have h :
      (QuadraticMap.weightedSumSquares A fun i => algebraMap R A (w i)).comp
          (TensorProduct.piScalarRight R A A ι).toLinearMap =
        _root_.QuadraticForm.baseChange A (QuadraticMap.weightedSumSquares R w) := by
    apply _root_.baseChange_ext
    intro x
    simp only [QuadraticMap.comp_apply, LinearEquiv.coe_coe,
      TensorProduct.piScalarRight_apply, TensorProduct.piScalarRightHom_tmul,
      _root_.QuadraticForm.baseChange_tmul, mul_one]
    simp [QuadraticMap.weightedSumSquares_apply, Algebra.smul_def]
  exact DFunLike.congr_fun h x

/-- The underlying linear equivalence for diagonal base change is the canonical distribution of
tensor product over the finite coordinate space. -/
@[simp]
theorem baseChangeWeightedSumSquares_apply (w : ι → R) (x : A ⊗[R] (ι → R)) :
    baseChangeWeightedSumSquares (A := A) w x =
      TensorProduct.piScalarRightHom R A A ι x := by
  classical
  rfl

end Diagonal

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

/-- A quadratic form vanishes after a faithful scalar extension exactly when it vanishes.
This is the quadratic-form analogue of Mathlib's
`LinearMap.BilinForm.baseChange_eq_zero_iff`. -/
@[simp]
theorem baseChange_eq_zero_iff [FaithfulSMul R A] {Q : _root_.QuadraticForm R M} :
    Q.baseChange A = 0 ↔ Q = 0 := by
  refine ⟨fun h ↦ QuadraticMap.ext fun x ↦ ?_, fun h ↦ h ▸ baseChange_zero⟩
  have hx := congrArg (fun F : _root_.QuadraticForm A (A ⊗[R] M) ↦ F (1 ⊗ₜ x)) h
  simp only [baseChange_tmul, mul_one, zero_apply, Algebra.smul_def] at hx
  exact FaithfulSMul.algebraMap_injective R A (hx.trans (map_zero _).symm)

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

namespace TauCeti

namespace QuadraticMap

/-! ### Orthogonal groups -/

/-- Extending scalars carries an orthogonal automorphism of `Q` to an orthogonal automorphism of
`Q.baseChange A`.  Over a field extension this is the map that compares the rational and local
orthogonal groups. -/
noncomputable def orthogonalGroupBaseChange (Q : _root_.QuadraticForm R M) :
    orthogonalGroup Q →* orthogonalGroup (Q.baseChange A) where
  toFun g := ⟨LinearEquiv.baseChange R A M M (g : M ≃ₗ[R] M), by
    apply mem_orthogonalGroup_iff.mpr
    intro x
    let e := (orthogonalGroupEquivIsometryEquiv Q g).toIsometry
    have he : e.toLinearMap = (g : M ≃ₗ[R] M).toLinearMap := by
      ext m
      exact congrFun (coe_orthogonalGroupEquivIsometryEquiv Q g) m
    -- The target is written through a linear equivalence, while the isometry base-change API is
    -- stated through its underlying linear map.
    change (Q.baseChange A) (((g : M ≃ₗ[R] M).toLinearMap.baseChange A) x) = (Q.baseChange A) x
    rw [← he, ← QuadraticMap.Isometry.baseChange_toLinearMap]
    exact (QuadraticMap.Isometry.baseChange e A).map_app x⟩
  map_one' := Subtype.ext (by simp)
  map_mul' g h := Subtype.ext (by simp [LinearEquiv.baseChange_mul])

/-- The linear equivalence underlying an orthogonal automorphism after scalar extension is the
base change of its original linear equivalence. -/
theorem coe_orthogonalGroupBaseChange (Q : _root_.QuadraticForm R M)
    (g : orthogonalGroup Q) :
    (orthogonalGroupBaseChange (A := A) Q g :
      A ⊗[R] M ≃ₗ[A] A ⊗[R] M) = LinearEquiv.baseChange R A M M (g : M ≃ₗ[R] M) := by
  rfl

/-- On a pure tensor, base change of an orthogonal automorphism applies the automorphism to the
second tensor factor. -/
@[simp]
theorem orthogonalGroupBaseChange_apply_tmul (Q : _root_.QuadraticForm R M)
    (g : orthogonalGroup Q) (a : A) (m : M) :
    ((orthogonalGroupBaseChange (A := A) Q g : A ⊗[R] M ≃ₗ[A] A ⊗[R] M) (a ⊗ₜ m)) =
      a ⊗ₜ (g : M ≃ₗ[R] M) m := by
  rw [coe_orthogonalGroupBaseChange]
  exact LinearEquiv.baseChange_tmul R A M M a m

/-- The determinant of a base-changed orthogonal automorphism is the image of its original
determinant. -/
@[simp]
theorem det_orthogonalGroupBaseChange [Module.Free R M] [Module.Finite R M]
    (Q : _root_.QuadraticForm R M) (g : orthogonalGroup Q) :
    LinearEquiv.det (orthogonalGroupBaseChange (A := A) Q g :
      A ⊗[R] M ≃ₗ[A] A ⊗[R] M) = (LinearEquiv.det (g : M ≃ₗ[R] M)).map (algebraMap R A) := by
  rw [coe_orthogonalGroupBaseChange, LinearEquiv.det_baseChange]

/-- Scalar extension of orthogonal automorphisms is injective whenever the extension is faithful
and the original module is flat.  In particular, this applies to extensions of fields. -/
theorem orthogonalGroupBaseChange_injective [FaithfulSMul R A] [Module.Flat R M]
    (Q : _root_.QuadraticForm R M) :
    Function.Injective (orthogonalGroupBaseChange (A := A) Q) := by
  intro g h hgh
  apply Subtype.ext
  apply LinearEquiv.toLinearMap_injective
  apply LinearMap.baseChangeHom_injective (R := R) (S := A) (M := M) (N := M)
  simpa only [LinearMap.baseChangeHom_apply, coe_orthogonalGroupBaseChange,
    LinearEquiv.coe_baseChange] using
    congrArg LinearEquiv.toLinearMap (congrArg Subtype.val hgh)

/-- Base change preserves the determinant-one condition, giving the corresponding map on special
orthogonal groups. -/
noncomputable def specialOrthogonalGroupBaseChange [Module.Free R M] [Module.Finite R M]
    (Q : _root_.QuadraticForm R M) :
    specialOrthogonalGroup Q →* specialOrthogonalGroup (Q.baseChange A) where
  toFun g := ⟨orthogonalGroupBaseChange (A := A) Q
      ⟨g, specialOrthogonalGroup_le_orthogonalGroup Q g.2⟩, by
    apply mem_specialOrthogonalGroup_iff.mpr
    refine ⟨(orthogonalGroupBaseChange (A := A) Q
      ⟨g, specialOrthogonalGroup_le_orthogonalGroup Q g.2⟩).2, ?_⟩
    have hg := (mem_specialOrthogonalGroup_iff.mp g.2).2
    rw [det_orthogonalGroupBaseChange, hg, map_one]⟩
  map_one' := Subtype.ext (by simp [orthogonalGroupBaseChange])
  map_mul' g h := Subtype.ext (by simp [orthogonalGroupBaseChange, LinearEquiv.baseChange_mul])

/-- The linear equivalence underlying a base-changed special orthogonal automorphism is the base
change of its underlying linear equivalence. -/
theorem coe_specialOrthogonalGroupBaseChange [Module.Free R M] [Module.Finite R M]
    (Q : _root_.QuadraticForm R M) (g : specialOrthogonalGroup Q) :
    (specialOrthogonalGroupBaseChange (A := A) Q g :
      A ⊗[R] M ≃ₗ[A] A ⊗[R] M) = LinearEquiv.baseChange R A M M (g : M ≃ₗ[R] M) := by
  rfl

/-- The special-orthogonal base-change map is the orthogonal base-change map restricted to the
determinant-one subgroup. -/
theorem specialOrthogonalGroupBaseChange_to_orthogonalGroup [Module.Free R M] [Module.Finite R M]
    (Q : _root_.QuadraticForm R M) (g : specialOrthogonalGroup Q) :
    Subgroup.inclusion (specialOrthogonalGroup_le_orthogonalGroup (Q.baseChange A))
        (specialOrthogonalGroupBaseChange (A := A) Q g) =
      orthogonalGroupBaseChange (A := A) Q
        (Subgroup.inclusion (specialOrthogonalGroup_le_orthogonalGroup Q) g) := by
  rfl

/-- On pure tensors, base change of a special orthogonal automorphism acts on the second factor. -/
@[simp]
theorem specialOrthogonalGroupBaseChange_apply_tmul [Module.Free R M] [Module.Finite R M]
    (Q : _root_.QuadraticForm R M) (g : specialOrthogonalGroup Q) (a : A) (m : M) :
    ((specialOrthogonalGroupBaseChange (A := A) Q g : A ⊗[R] M ≃ₗ[A] A ⊗[R] M) (a ⊗ₜ m)) =
      a ⊗ₜ (g : M ≃ₗ[R] M) m := by
  rw [coe_specialOrthogonalGroupBaseChange]
  exact LinearEquiv.baseChange_tmul R A M M a m

/-- Scalar extension of special orthogonal automorphisms is injective whenever the extension is
faithful and the original module is flat. -/
theorem specialOrthogonalGroupBaseChange_injective [FaithfulSMul R A] [Module.Flat R M]
    [Module.Free R M] [Module.Finite R M] (Q : _root_.QuadraticForm R M) :
    Function.Injective (specialOrthogonalGroupBaseChange (A := A) Q) := by
  intro g h hgh
  have hO : Subgroup.inclusion (specialOrthogonalGroup_le_orthogonalGroup Q) g =
      Subgroup.inclusion (specialOrthogonalGroup_le_orthogonalGroup Q) h :=
    orthogonalGroupBaseChange_injective (A := A) Q <| by
      calc
        orthogonalGroupBaseChange (A := A) Q
            (Subgroup.inclusion (specialOrthogonalGroup_le_orthogonalGroup Q) g) =
            Subgroup.inclusion (specialOrthogonalGroup_le_orthogonalGroup (Q.baseChange A))
              (specialOrthogonalGroupBaseChange (A := A) Q g) :=
          (specialOrthogonalGroupBaseChange_to_orthogonalGroup (A := A) Q g).symm
        _ = Subgroup.inclusion (specialOrthogonalGroup_le_orthogonalGroup (Q.baseChange A))
              (specialOrthogonalGroupBaseChange (A := A) Q h) :=
          congrArg (Subgroup.inclusion
            (specialOrthogonalGroup_le_orthogonalGroup (Q.baseChange A))) hgh
        _ = orthogonalGroupBaseChange (A := A) Q
            (Subgroup.inclusion (specialOrthogonalGroup_le_orthogonalGroup Q) h) :=
          specialOrthogonalGroupBaseChange_to_orthogonalGroup (A := A) Q h
  apply Subtype.ext
  exact congrArg (fun x : orthogonalGroup Q => (x : M ≃ₗ[R] M)) hO

/-- Extending scalars carries the reflection in `v` to the reflection in `1 ⊗ₜ v`: the base change
of `τ_v` is `τ_{1 ⊗ v}` for `Q.baseChange A`. -/
theorem reflection_baseChange (Q : _root_.QuadraticForm R M) (v : M) [Invertible (Q v)]
    [Invertible (Q.baseChange A (1 ⊗ₜ v))] :
    reflection (Q.baseChange A) (1 ⊗ₜ v) = LinearEquiv.baseChange R A M M (reflection Q v) := by
  have hinv : ⅟(Q.baseChange A (1 ⊗ₜ v)) = algebraMap R A ⅟(Q v) :=
    invOf_eq_left_inv (by
      rw [_root_.QuadraticForm.baseChange_tmul, mul_one, Algebra.smul_def, mul_one, ← map_mul,
        invOf_mul_self, map_one])
  ext x
  induction x using TensorProduct.inductionOn with
  | tmul a m =>
    rw [reflection_apply, LinearEquiv.baseChange_tmul, reflection_apply, hinv,
      _root_.QuadraticForm.polar_baseChange_tmul]
    simp [TensorProduct.tmul_sub, TensorProduct.smul_tmul', Algebra.smul_def, mul_assoc]
  | add x y hx hy => simp only [map_add, hx, hy]

end QuadraticMap

end TauCeti

end CommRing

section ScalarTower

variable {R : Type uR} {A : Type uA} {B : Type uN}
variable [CommRing R] [CommRing A] [CommRing B]
variable [Algebra R A] [Algebra A B] [Algebra R B] [IsScalarTower R A B]
variable [Invertible (2 : R)]
variable {M : Type uM} [AddCommGroup M] [Module R M]

namespace QuadraticForm

/-- Direct base change through a scalar tower is isometric to successive base change.

The underlying linear equivalence is the inverse of Mathlib's canonical cancellation
`B ⊗[A] (A ⊗[R] M) ≃ B ⊗[R] M`. -/
def baseChangeBaseChange (Q : _root_.QuadraticForm R M) :
    letI : Invertible (2 : A) :=
      (Invertible.map (algebraMap R A) 2).copy 2 (map_ofNat _ _).symm
    (Q.baseChange B).IsometryEquiv ((Q.baseChange A).baseChange B) :=
  letI : Invertible (2 : A) :=
    (Invertible.map (algebraMap R A) 2).copy 2 (map_ofNat _ _).symm
  { toLinearEquiv :=
      (TensorProduct.AlgebraTensorModule.cancelBaseChange R A B B M).symm
    map_app' x := by
      have h : ((Q.baseChange A).baseChange B).comp
          (TensorProduct.AlgebraTensorModule.cancelBaseChange R A B B M).symm.toLinearMap =
          Q.baseChange B := by
        apply _root_.baseChange_ext
        intro m
        simp only [QuadraticMap.comp_apply, LinearEquiv.coe_coe,
          TensorProduct.AlgebraTensorModule.cancelBaseChange_symm_tmul,
          _root_.QuadraticForm.baseChange_tmul, mul_one, smul_assoc, one_smul]
      exact DFunLike.congr_fun h x }

/-- The linear equivalence underlying repeated base change is Mathlib's canonical tensor-product
cancellation, read in the direction from direct to successive base change. -/
@[simp]
theorem baseChangeBaseChange_toLinearEquiv (Q : _root_.QuadraticForm R M) :
    (baseChangeBaseChange (A := A) (B := B) Q).toLinearEquiv =
      (TensorProduct.AlgebraTensorModule.cancelBaseChange R A B B M).symm :=
  (rfl)

/-- On a pure tensor, the scalar-tower base-change equivalence inserts the intermediate unit
tensor. -/
@[simp]
theorem baseChangeBaseChange_tmul (Q : _root_.QuadraticForm R M) (b : B) (m : M) :
    baseChangeBaseChange (A := A) Q (b ⊗ₜ m) = b ⊗ₜ (1 ⊗ₜ m) :=
  TensorProduct.AlgebraTensorModule.cancelBaseChange_symm_tmul R A B b m

/-- The inverse scalar-tower base-change equivalence multiplies the intermediate scalar into
the outer tensor factor. -/
@[simp]
theorem baseChangeBaseChange_symm_tmul (Q : _root_.QuadraticForm R M)
    (b : B) (a : A) (m : M) :
    (baseChangeBaseChange (A := A) Q).symm (b ⊗ₜ (a ⊗ₜ m)) = (a • b) ⊗ₜ m :=
  TensorProduct.AlgebraTensorModule.cancelBaseChange_tmul R A B b m a

end QuadraticForm

namespace TauCeti.QuadraticMap

/-- Conjugating a directly extended orthogonal automorphism by the canonical scalar-tower
equivalence agrees with extending it successively. -/
@[simp]
theorem orthogonalGroupBaseChange_baseChange (Q : _root_.QuadraticForm R M)
    (g : orthogonalGroup Q) :
    letI : Invertible (2 : A) :=
      (Invertible.map (algebraMap R A) 2).copy 2 (map_ofNat _ _).symm
    orthogonalGroupCongr (QuadraticForm.baseChangeBaseChange (A := A) (B := B) Q)
        (orthogonalGroupBaseChange (A := B) Q g) =
      orthogonalGroupBaseChange (A := B) (Q.baseChange A)
        (orthogonalGroupBaseChange (A := A) Q g) := by
  apply Subtype.ext
  apply LinearEquiv.ext
  intro x
  simp only [coe_orthogonalGroupCongr_apply,
    QuadraticForm.baseChangeBaseChange_toLinearEquiv,
    coe_orthogonalGroupBaseChange]
  have h := LinearMap.baseChange_baseChange (R := R) (A := A) (B := B)
    ((g : M ≃ₗ[R] M).toLinearMap)
  have hx := congrArg (fun f => f x) h
  convert hx.symm using 1
  · have hB (y : B ⊗[R] M) :
        LinearEquiv.baseChange R B M M (g : M ≃ₗ[R] M) y =
          (g : M ≃ₗ[R] M).toLinearMap.baseChange B y :=
      DFunLike.congr_fun (LinearEquiv.coe_baseChange R B M M (g : M ≃ₗ[R] M)) y
    rw [hB]
    simp only [LinearMap.coe_comp, Function.comp_apply, LinearEquiv.coe_coe,
      LinearEquiv.symm_symm]
  · exact congrArg (fun f => f x)
      (LinearEquiv.coe_baseChange A B (A ⊗[R] M) (A ⊗[R] M)
        (LinearEquiv.baseChange R A M M (g : M ≃ₗ[R] M)))

/-- The special-orthogonal scalar-extension maps satisfy the same scalar-tower law, read through
the canonical inclusion into the orthogonal group. -/
@[simp]
theorem specialOrthogonalGroupBaseChange_baseChange [Module.Free R M] [Module.Finite R M]
    (Q : _root_.QuadraticForm R M) (g : specialOrthogonalGroup Q) :
    letI : Invertible (2 : A) :=
      (Invertible.map (algebraMap R A) 2).copy 2 (map_ofNat _ _).symm
    orthogonalGroupCongr (QuadraticForm.baseChangeBaseChange (A := A) (B := B) Q)
        (Subgroup.inclusion (specialOrthogonalGroup_le_orthogonalGroup (Q.baseChange B))
          (specialOrthogonalGroupBaseChange (A := B) Q g)) =
      Subgroup.inclusion
        (specialOrthogonalGroup_le_orthogonalGroup ((Q.baseChange A).baseChange B))
        (specialOrthogonalGroupBaseChange (A := B) (Q.baseChange A)
          (specialOrthogonalGroupBaseChange (A := A) Q g)) := by
  simpa only [specialOrthogonalGroupBaseChange_to_orthogonalGroup] using
    orthogonalGroupBaseChange_baseChange Q
      (Subgroup.inclusion (specialOrthogonalGroup_le_orthogonalGroup Q) g)

end TauCeti.QuadraticMap

end ScalarTower

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

/-- On a space of dimension at most one, a quadratic form is anisotropic exactly when its
extension to a nontrivial ring without zero divisors is anisotropic.  Dimension one is sharp:
`⟨1, 1⟩` over `ℚ` is anisotropic, while its extension to `ℂ` is not. -/
@[simp]
theorem anisotropic_baseChange_iff_of_finrank_le_one [Invertible (2 : K)]
    {A : Type*} [CommRing A] [Nontrivial A] [NoZeroDivisors A] [Algebra K A]
    [FiniteDimensional K V]
    {Q : _root_.QuadraticForm K V} (hV : Module.finrank K V ≤ 1) :
    (Q.baseChange A).Anisotropic ↔ Q.Anisotropic := by
  refine ⟨fun hQA ↦ ?_, fun hQ x hx ↦ ?_⟩
  · by_contra hQ
    exact not_anisotropic_baseChange hQ hQA
  let b := Module.finBasis K V
  have : Subsingleton (Fin (Module.finrank K V)) := Fin.subsingleton_iff_le_one.mpr hV
  refine (b.baseChange A).ext_elem fun i ↦ ?_
  rw [b.eq_baseChange_repr_tmul_of_subsingleton x i, baseChange_tmul, Algebra.smul_def,
    mul_eq_zero, mul_self_eq_zero] at hx
  rw [map_zero, Finsupp.zero_apply]
  refine hx.resolve_left fun h ↦ b.ne_zero i (hQ _ ?_)
  exact (FaithfulSMul.algebraMap_injective K A).eq_iff.mp (h.trans (map_zero _).symm)

end QuadraticForm

end Field
