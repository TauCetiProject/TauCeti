/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Coalgebra.Subcoalgebra.Basic
public import Mathlib.RingTheory.Flat.Basic
import Mathlib.RingTheory.Coalgebra.CoassocSimps

/-!
# Coalgebra structures on flat subcoalgebras

A flat subcoalgebra of a flat coalgebra inherits comultiplication and counit from the ambient
coalgebra: flatness makes the inclusion of its tensor square injective. The induced structure
is supplied as a definition, with formulas relating its operations to those of the ambient
coalgebra. This construction supplies the coalgebra underlying a flat Hopf subalgebra.

## References

* M. E. Sweedler, *Hopf Algebras* (1969), Chapter 2.
-/

public section

open scoped TensorProduct

namespace TauCeti.Subcoalgebra

variable {R C : Type*} [CommSemiring R] [AddCommMonoid C] [Module R C] [Coalgebra R C]
variable (D : Subcoalgebra R C) [Module.Flat R C] [Module.Flat R D.toSubmodule]

local notation "D₀" => D.toSubmodule

/-- The comultiplication of a flat subcoalgebra, valued in its own tensor square. -/
noncomputable def comulLinearMap : D.toSubmodule →ₗ[R] D.toSubmodule ⊗[R] D.toSubmodule :=
  (LinearEquiv.ofInjective (TensorProduct.map D.toSubmodule.subtype D.toSubmodule.subtype)
    (TensorProduct.map_injective_of_flat_flat _ _ Subtype.val_injective
      Subtype.val_injective)).symm.toLinearMap ∘ₗ
    ((Coalgebra.comul (R := R) (A := C)) ∘ₗ D.toSubmodule.subtype).codRestrict _
      (fun x ↦ D.comul_mem x.2)

/-- Including the comultiplication of a subcoalgebra recovers the ambient comultiplication. -/
@[simp]
theorem map_subtype_comulLinearMap (x : D.toSubmodule) :
    TensorProduct.map D.toSubmodule.subtype D.toSubmodule.subtype (D.comulLinearMap x) =
      Coalgebra.comul (R := R) (x : C) := by
  simp only [comulLinearMap, LinearMap.comp_apply, LinearEquiv.coe_coe,
    LinearEquiv.ofInjective_symm_apply]
  rfl

private theorem coassoc_comulLinearMap :
    TensorProduct.assoc R D₀ D₀ D₀ ∘ₗ D.comulLinearMap.rTensor D₀ ∘ₗ D.comulLinearMap =
      D.comulLinearMap.lTensor D₀ ∘ₗ D.comulLinearMap := by
  let ι := D.toSubmodule.subtype
  have hcomul : TensorProduct.map ι ι ∘ₗ D.comulLinearMap =
      (Coalgebra.comul (R := R) (A := C)) ∘ₗ ι :=
    LinearMap.ext D.map_subtype_comulLinearMap
  have hleft (t : D₀ ⊗[R] D₀) :
      TensorProduct.map ι (TensorProduct.map ι ι)
          (TensorProduct.assoc R D₀ D₀ D₀ (D.comulLinearMap.rTensor D₀ t)) =
        TensorProduct.assoc R C C C
          ((Coalgebra.comul (R := R) (A := C)).rTensor C (TensorProduct.map ι ι t)) := by
    rw [TensorProduct.map_map_assoc, LinearMap.map_rTensor, hcomul]
    simp only [LinearMap.rTensor, TensorProduct.map_map, LinearMap.id_comp]
  have hright (t : D₀ ⊗[R] D₀) :
      TensorProduct.map ι (TensorProduct.map ι ι) (D.comulLinearMap.lTensor D₀ t) =
        (Coalgebra.comul (R := R) (A := C)).lTensor C (TensorProduct.map ι ι t) := by
    rw [LinearMap.map_lTensor, hcomul]
    simp only [LinearMap.lTensor, TensorProduct.map_map, LinearMap.id_comp]
  ext x
  apply TensorProduct.map_injective_of_flat_flat D.toSubmodule.subtype
    (TensorProduct.map D.toSubmodule.subtype D.toSubmodule.subtype) Subtype.val_injective
    (TensorProduct.map_injective_of_flat_flat _ _ Subtype.val_injective Subtype.val_injective)
  simp only [LinearMap.comp_apply, LinearEquiv.coe_coe]
  rw [hleft, hright, map_subtype_comulLinearMap, Coalgebra.coassoc_apply]

private theorem rTensor_counit_comulLinearMap :
    (Coalgebra.counit (R := R) (A := C) ∘ₗ D.toSubmodule.subtype).rTensor D₀ ∘ₗ
        D.comulLinearMap = TensorProduct.mk R R D₀ 1 := by
  have h (t : D₀ ⊗[R] D₀) :
      (TensorProduct.lid R D₀
          ((Coalgebra.counit (R := R) (A := C) ∘ₗ D.toSubmodule.subtype).rTensor D₀ t) : C) =
        TensorProduct.lid R C ((Coalgebra.counit (R := R) (A := C)).rTensor C
          (TensorProduct.map D.toSubmodule.subtype D.toSubmodule.subtype t)) := by
    let ι := D.toSubmodule.subtype
    let ε := Coalgebra.counit (R := R) (A := C)
    -- `CoassocSimps.lid_comp_map` is stated for linear maps. Expose the subtype
    -- coercion as `ι` and the counit as `ε` to match its two sides.
    change ι (TensorProduct.lid R D₀ (((ε ∘ₗ ι).rTensor D₀) t)) =
      TensorProduct.lid R C (ε.rTensor C (TensorProduct.map ι ι t))
    simpa only [LinearMap.rTensor, TensorProduct.map_map, LinearMap.id_comp,
      LinearMap.comp_apply, LinearEquiv.coe_coe] using
      (LinearMap.congr_fun (CoassocSimps.lid_comp_map (ε ∘ₗ ι) ι) t).symm
  ext x
  apply (TensorProduct.lid R D₀).injective
  apply Subtype.val_injective
  simp [h, map_subtype_comulLinearMap]

private theorem lTensor_counit_comulLinearMap :
    (Coalgebra.counit (R := R) (A := C) ∘ₗ D.toSubmodule.subtype).lTensor D₀ ∘ₗ
        D.comulLinearMap = (TensorProduct.mk R D₀ R).flip 1 := by
  have h (t : D₀ ⊗[R] D₀) :
      (TensorProduct.rid R D₀
          ((Coalgebra.counit (R := R) (A := C) ∘ₗ D.toSubmodule.subtype).lTensor D₀ t) : C) =
        TensorProduct.rid R C ((Coalgebra.counit (R := R) (A := C)).lTensor C
          (TensorProduct.map D.toSubmodule.subtype D.toSubmodule.subtype t)) := by
    let ι := D.toSubmodule.subtype
    let ε := Coalgebra.counit (R := R) (A := C)
    -- `CoassocSimps.rid_comp_map` likewise uses linear maps; identify the subtype
    -- coercion with `ι` before applying that lemma to the right counit law.
    change ι (TensorProduct.rid R D₀ (((ε ∘ₗ ι).lTensor D₀) t)) =
      TensorProduct.rid R C (ε.lTensor C (TensorProduct.map ι ι t))
    simpa only [LinearMap.lTensor, TensorProduct.map_map, LinearMap.id_comp,
      LinearMap.comp_apply, LinearEquiv.coe_coe] using
      (LinearMap.congr_fun (CoassocSimps.rid_comp_map ι (ε ∘ₗ ι)) t).symm
  ext x
  apply (TensorProduct.rid R D₀).injective
  apply Subtype.val_injective
  simp [h, map_subtype_comulLinearMap]

/-- A flat subcoalgebra of a flat coalgebra inherits a coalgebra structure.
This is a definition rather than a global instance, so its carrier remains a submodule. -/
@[instance_reducible]
noncomputable def coalgebra : Coalgebra R D.toSubmodule where
  comul := D.comulLinearMap
  counit := Coalgebra.counit (R := R) (A := C) ∘ₗ D.toSubmodule.subtype
  coassoc := D.coassoc_comulLinearMap
  rTensor_counit_comp_comul := D.rTensor_counit_comulLinearMap
  lTensor_counit_comp_comul := D.lTensor_counit_comulLinearMap

/-- The comultiplication of the induced coalgebra is the restricted linear map. -/
@[simp]
theorem comul_apply (x : D.toSubmodule) :
    letI : Coalgebra R D.toSubmodule := D.coalgebra
    Coalgebra.comul (R := R) x = D.comulLinearMap x :=
  (rfl)

/-- The counit of the induced coalgebra is the ambient counit. -/
@[simp]
theorem counit_apply (x : D.toSubmodule) :
    letI : Coalgebra R D.toSubmodule := D.coalgebra
    Coalgebra.counit (R := R) x = Coalgebra.counit (R := R) (x : C) :=
  (rfl)

end TauCeti.Subcoalgebra
