/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Action.Monoidal
public import Mathlib.RepresentationTheory.FDRep
public import TauCeti.Algebra.Category.FGModuleCat.Rigid
public import TauCeti.RepresentationTheory.Dual
public import TauCeti.RepresentationTheory.FDRep.Basic
import TauCeti.CategoryTheory.Monoidal.Rigid.Preadditive

/-!
# Duals of finite-dimensional group representations

For a field `k` and a group `G`, the monoidal category `FDRep k G` of finite-dimensional
representations inherits right and left duals as `Action (FGModuleCat k) G` from the rigid
structure on `FGModuleCat k`. On underlying vector spaces, both `Vᘁ` and `ᘁV` have carrier
`Module.Dual k V`, and a group element `g` acts through the adjoint mate of `V.ρ g⁻¹`
(`Action.rightDual_ρ` and `Action.leftDual_ρ`). Since both right and left adjoint mates in
`FGModuleCat k` are linear transposes (`FGModuleCat.rightAdjointMate_hom` and
`FGModuleCat.leftAdjointMate_hom`), both categorical duals carry the contragredient representation
`Representation.dual V.ρ`.

## Main results

* `FDRep.rightDual_ρ`: the right dual `Vᘁ` carries `Representation.dual V.ρ`;
* `FDRep.leftDual_ρ`: the left dual `ᘁV` carries `Representation.dual V.ρ`.
* `FDRep.leftDualIso`, `FDRep.isoLeftDualOfEquivDual`, `FDRep.tensorLeftHomLinearEquivOfEquivDual`,
  `FDRep.finrank_hom_tensor_leftDual`, and `FDRep.finrank_hom_tensor_comm_of_equiv_dual`:
  categorical left duals `ᘁV ≅ FDRep.of V.ρ.dual` and Frobenius reciprocity in `FDRep k G`.

## References

* P. Etingof, S. Gelaki, D. Nikshych, V. Ostrik, *Tensor Categories*, Mathematical Surveys and
  Monographs 205, Section 2.10, for duals of group representations.
-/

public section

open CategoryTheory MonoidalCategory Module

namespace FDRep

universe u v

variable {k : Type u} {G : Type v} [Field k] [Group G]

/-- The right dual of a finite-dimensional representation carries the contragredient
representation `Representation.dual V.ρ`. -/
@[simp]
theorem rightDual_ρ (V : FDRep k G) : (Vᘁ : FDRep k G).ρ = Representation.dual V.ρ := by
  ext g φ
  have h := congrArg (fun u : V.Vᘁ ⟶ V.Vᘁ => u.hom.hom) (Action.rightDual_ρ V g)
  rw [FGModuleCat.rightAdjointMate_hom, FDRep.hom_hom_action_ρ V, LinearMap.dualMap_def] at h
  -- The carrier of `Vᘁ` is `V.Vᘁ` by `Action.rightDual_v`, which is `Module.Dual k V` by
  -- `FGModuleCat.FGModuleCatDual_coe`.
  exact (LinearMap.congr_fun (FDRep.hom_hom_action_ρ (Vᘁ : FDRep k G) g).symm φ).trans
    ((LinearMap.congr_fun h φ).trans
      (LinearMap.congr_fun (Representation.dual_apply (ρV := V.ρ) g).symm φ))

/-- The left dual of a finite-dimensional representation carries the contragredient
representation `Representation.dual V.ρ`. -/
@[simp]
theorem leftDual_ρ (V : FDRep k G) : (ᘁV : FDRep k G).ρ = Representation.dual V.ρ := by
  ext g φ
  have h := congrArg (fun u : (ᘁV.V : FGModuleCat k) ⟶ ᘁV.V => u.hom.hom) (Action.leftDual_ρ V g)
  rw [FGModuleCat.leftAdjointMate_hom, FDRep.hom_hom_action_ρ V, LinearMap.dualMap_def] at h
  -- The carrier of `ᘁV` is `ᘁV.V` by `Action.leftDual_v`, which is `Module.Dual k V` by
  -- `FGModuleCat.leftDual_eq` and `FGModuleCat.FGModuleCatDual_coe`.
  exact (LinearMap.congr_fun (FDRep.hom_hom_action_ρ (ᘁV : FDRep k G) g).symm φ).trans
    ((LinearMap.congr_fun h φ).trans
      (LinearMap.congr_fun (Representation.dual_apply (ρV := V.ρ) g).symm φ))

/-- **The categorical left dual `ᘁV` in `FDRep k G` is `FDRep.of (Representation.dual V.ρ)`.** -/
protected noncomputable def leftDualIso (V : FDRep k G) :
    (ᘁV : FDRep k G) ≅ FDRep.of (Representation.dual V.ρ) :=
  (LinearEquiv.refl k (Module.Dual k V)).toFDRepIso fun g φ ↦ by
    rw [FDRep.leftDual_ρ, FDRep.of_ρ']
    rfl

@[simp]
theorem isoToLinearEquiv_leftDualIso (V : FDRep k G) :
    isoToLinearEquiv (FDRep.leftDualIso V) = LinearEquiv.refl k (Module.Dual k V) :=
  isoToLinearEquiv_toFDRepIso _ _

/-- The categorical left dual `ᘁV` in `FDRep k G` has the same dimension as `V`. -/
-- Match before `Action.leftDual_v` rewrites the carrier `(ᘁV).V` to `ᘁV.V`.
@[simp↓]
theorem finrank_leftDual (V : FDRep k G) : finrank k (ᘁV : FDRep k G) = finrank k V := by
  rw [(isoToLinearEquiv (FDRep.leftDualIso V)).finrank_eq, finrank_of, Subspace.dual_finrank_eq]

/-- **An equivalence `V.ρ.Equiv V.ρ.dual` makes `V` isomorphic to `ᘁV` in `FDRep k G`.** -/
noncomputable def isoLeftDualOfEquivDual {V : FDRep k G}
    (e : _root_.Representation.Equiv V.ρ (Representation.dual V.ρ)) : V ≅ (ᘁV : FDRep k G) :=
  (e.toLinearEquiv.toFDRepIso fun g x ↦ by
      rw [FDRep.of_ρ']; exact LinearMap.congr_fun (e.isIntertwining' g) x) ≪≫
    (FDRep.leftDualIso V).symm

@[simp]
theorem isoToLinearEquiv_isoLeftDualOfEquivDual {V : FDRep k G}
    (e : _root_.Representation.Equiv V.ρ (Representation.dual V.ρ)) :
    isoToLinearEquiv (isoLeftDualOfEquivDual e) = e.toLinearEquiv := by
  ext x
  rw [isoLeftDualOfEquivDual, isoToLinearEquiv_trans, LinearEquiv.trans_apply,
    isoToLinearEquiv_toFDRepIso, isoToLinearEquiv_symm, LinearEquiv.symm_apply_eq]
  exact (DFunLike.congr_fun (isoToLinearEquiv_leftDualIso V) (e.toLinearEquiv x)).symm.trans
    (LinearEquiv.refl_apply (R := k) _)

/-- **Frobenius reciprocity `(V ⊗ X ⟶ Y) ≃ₗ[k] (X ⟶ V ⊗ Y)` along a self-duality of `V`.** -/
noncomputable def tensorLeftHomLinearEquivOfEquivDual {V : FDRep k G}
    (e : _root_.Representation.Equiv V.ρ (Representation.dual V.ρ)) (X Y : FDRep k G) :
    (V ⊗ X ⟶ Y) ≃ₗ[k] (X ⟶ V ⊗ Y) :=
  (TauCeti.tensorLeftHomLinearEquiv k X (ᘁV) V Y).trans
    (Linear.homCongr k (Iso.refl X) (whiskerRightIso (isoLeftDualOfEquivDual e).symm Y))

@[simp]
theorem tensorLeftHomLinearEquivOfEquivDual_apply {V : FDRep k G}
    (e : _root_.Representation.Equiv V.ρ (Representation.dual V.ρ)) (X Y : FDRep k G)
    (f : V ⊗ X ⟶ Y) :
    tensorLeftHomLinearEquivOfEquivDual e X Y f =
      tensorLeftHomEquiv X (ᘁV) V Y f ≫ (isoLeftDualOfEquivDual e).inv ▷ Y := by
  simp [tensorLeftHomLinearEquivOfEquivDual, Linear.homCongr_apply]

@[simp]
theorem tensorLeftHomLinearEquivOfEquivDual_symm_apply {V : FDRep k G}
    (e : _root_.Representation.Equiv V.ρ (Representation.dual V.ρ)) (X Y : FDRep k G)
    (g : X ⟶ V ⊗ Y) :
    (tensorLeftHomLinearEquivOfEquivDual e X Y).symm g =
      (tensorLeftHomEquiv X (ᘁV) V Y).symm (g ≫ (isoLeftDualOfEquivDual e).hom ▷ Y) := by
  simp [tensorLeftHomLinearEquivOfEquivDual, Linear.homCongr_symm_apply]

/-- **Frobenius reciprocity for tensor Hom-dimensions.** When `|G|` is invertible in `k`,
`dim_k (X ⟶ V ⊗ Y) = dim_k (Y ⟶ (ᘁV) ⊗ X)` (becoming a multiplicity identity for simple `X`, `Y`
in the split semisimple case). -/
theorem finrank_hom_tensor_leftDual [Invertible (Nat.card G : k)] (V X Y : FDRep k G) :
    finrank k (X ⟶ V ⊗ Y) = finrank k (Y ⟶ (ᘁV) ⊗ X) := by
  rw [finrank_hom_comm X (V ⊗ Y), (TauCeti.tensorLeftHomLinearEquiv k Y (ᘁV) V X).finrank_eq]

/-- **Symmetry of tensor Hom-dimensions for a self-dual representation** (becoming multiplicity
symmetry for simple `X`, `Y` in the split semisimple case). -/
theorem finrank_hom_tensor_comm_of_equiv_dual [Invertible (Nat.card G : k)] {V : FDRep k G}
    (he : Nonempty (_root_.Representation.Equiv V.ρ (Representation.dual V.ρ)))
    (X Y : FDRep k G) : finrank k (X ⟶ V ⊗ Y) = finrank k (Y ⟶ V ⊗ X) := by
  obtain ⟨e⟩ := he
  exact (finrank_hom_tensor_leftDual V X Y).trans
    (Linear.homCongr k (Iso.refl Y) (whiskerRightIso (isoLeftDualOfEquivDual e).symm X)).finrank_eq

end FDRep
