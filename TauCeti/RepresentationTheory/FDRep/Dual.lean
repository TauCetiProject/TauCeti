/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Action.Monoidal
public import TauCeti.Algebra.Category.FGModuleCat.Rigid
public import TauCeti.RepresentationTheory.FDRep.Basic
import TauCeti.CategoryTheory.Monoidal.Rigid.Preadditive
import TauCeti.RepresentationTheory.Dual

/-!
# Categorical left duals and Frobenius reciprocity in `FDRep k G`

For a field `k` and a group `G`, the categorical left dual `ᘁV` of `V : FDRep k G` carries the
underlying vector space `Module.Dual k V`, and the left dual action `ᘁ(V.ρ g⁻¹)` in `FGModuleCat k`
is the transpose `(V.ρ g⁻¹).dualMap` (`FGModuleCat.leftAdjointMate_hom`). `FDRep.leftDualIso`
packages this identification as an isomorphism
`(ᘁV : FDRep k G) ≅ FDRep.of (Representation.dual V.ρ)`.

Combining Frobenius reciprocity (`TauCeti.tensorLeftHomLinearEquiv`) with `FDRep.finrank_hom_comm`
when `|G|` is invertible in `k` relates tensor multiplicities for `V` and for `ᘁV`:
`dim_k Hom_G(X, V ⊗ Y) = dim_k Hom_G(Y, (ᘁV) ⊗ X)` (`FDRep.finrank_hom_tensor_leftDual`). When `V`
admits a self-duality `V.ρ.Equiv (Representation.dual V.ρ)`, `FDRep.isoLeftDualOfEquivDual` produces
`V ≅ ᘁV`, giving the `k`-linear Frobenius reciprocity `(V ⊗ X ⟶ Y) ≃ₗ[k] (X ⟶ V ⊗ Y)`
(`FDRep.tensorLeftHomLinearEquivOfEquivDual`) and symmetry of the tensor multiplicity pairing
(`FDRep.finrank_hom_tensor_comm_of_equiv_dual`).

## Main definitions

* `FDRep.leftDualIso`: the canonical isomorphism `ᘁV ≅ FDRep.of (Representation.dual V.ρ)` in
  `FDRep k G`.
* `FDRep.isoLeftDualOfEquivDual`: the isomorphism `V ≅ ᘁV` attached to
  `V.ρ.Equiv (Representation.dual V.ρ)`.
* `FDRep.tensorLeftHomLinearEquivOfEquivDual`: Frobenius reciprocity `(V ⊗ X ⟶ Y) ≃ₗ[k] (X ⟶ V ⊗ Y)`
  along a self-duality of `V`.

## Main results

* `FDRep.finrank_leftDual`: `dim_k (ᘁV) = dim_k V`.
* `FDRep.finrank_hom_tensor_leftDual`: `dim_k (X ⟶ V ⊗ Y) = dim_k (Y ⟶ (ᘁV) ⊗ X)` when `|G|` is
  invertible in `k`.
* `FDRep.finrank_hom_tensor_comm_of_equiv_dual`: `dim_k (X ⟶ V ⊗ Y) = dim_k (Y ⟶ V ⊗ X)` for
  self-dual `V` when `|G|` is invertible in `k`.
-/

public section

open CategoryTheory MonoidalCategory

universe u v

namespace FDRep

variable {k : Type u} {G : Type v} [Field k] [Group G]

/-- **The categorical left dual `ᘁV` in `FDRep k G` is `FDRep.of (Representation.dual V.ρ)`.** Both
have underlying vector space `Module.Dual k V`, and the left dual action `ᘁ(V.ρ g⁻¹)` in
`FGModuleCat k` is the transpose `(V.ρ g⁻¹).dualMap` (`FGModuleCat.leftAdjointMate_hom`). -/
protected noncomputable def leftDualIso (V : FDRep k G) :
    (ᘁV : FDRep k G) ≅ FDRep.of (Representation.dual V.ρ) :=
  (LinearEquiv.refl k (Module.Dual k V)).toFDRepIso fun g φ ↦ by
    have hρ := congrArg (fun f : (ᘁV.V) ⟶ ᘁV.V ↦ f.hom.hom φ) (Action.leftDual_ρ V g)
    rw [FGModuleCat.leftAdjointMate_hom, FDRep.hom_hom_action_ρ] at hρ
    exact hρ

/-- `FDRep.leftDualIso` acts as the identity on `Module.Dual k V`. -/
@[simp]
theorem isoToLinearEquiv_leftDualIso (V : FDRep k G) :
    isoToLinearEquiv (FDRep.leftDualIso V) = LinearEquiv.refl k (Module.Dual k V) := by
  rw [FDRep.leftDualIso]
  exact isoToLinearEquiv_toFDRepIso _ _

/-- The categorical left dual `ᘁV` in `FDRep k G` has the same dimension as `V`. -/
-- Match before `Action.leftDual_v` rewrites the carrier `(ᘁV).V` to `ᘁV.V`.
@[simp↓]
theorem finrank_leftDual (V : FDRep k G) :
    Module.finrank k (ᘁV : FDRep k G) = Module.finrank k V := by
  rw [(isoToLinearEquiv (FDRep.leftDualIso V)).finrank_eq, finrank_of, Subspace.dual_finrank_eq]

/-- **An equivalence `V.ρ.Equiv (Representation.dual V.ρ)` makes `V` isomorphic to its categorical
left dual `ᘁV` in `FDRep k G`.** -/
noncomputable def isoLeftDualOfEquivDual {V : FDRep k G}
    (e : _root_.Representation.Equiv V.ρ (Representation.dual V.ρ)) :
    V ≅ (ᘁV : FDRep k G) :=
  (e.toLinearEquiv.toFDRepIso fun g x ↦ by
      rw [FDRep.of_ρ']
      exact LinearMap.congr_fun (e.isIntertwining' g) x) ≪≫
    (FDRep.leftDualIso V).symm

/-- `FDRep.isoLeftDualOfEquivDual e` has underlying linear equivalence `e.toLinearEquiv`. -/
@[simp]
theorem isoToLinearEquiv_isoLeftDualOfEquivDual {V : FDRep k G}
    (e : _root_.Representation.Equiv V.ρ (Representation.dual V.ρ)) :
    isoToLinearEquiv (isoLeftDualOfEquivDual e) = e.toLinearEquiv := by
  rw [isoLeftDualOfEquivDual, isoToLinearEquiv_trans, isoToLinearEquiv_toFDRepIso,
    isoToLinearEquiv_symm, isoToLinearEquiv_leftDualIso]
  ext x
  rfl

/-- **Frobenius reciprocity `(V ⊗ X ⟶ Y) ≃ₗ[k] (X ⟶ V ⊗ Y)` along a self-duality of `V`.** -/
noncomputable def tensorLeftHomLinearEquivOfEquivDual {V : FDRep k G}
    (e : _root_.Representation.Equiv V.ρ (Representation.dual V.ρ)) (X Y : FDRep k G) :
    (V ⊗ X ⟶ Y) ≃ₗ[k] (X ⟶ V ⊗ Y) :=
  (TauCeti.tensorLeftHomLinearEquiv k X (ᘁV) V Y).trans
    (Linear.homCongr k (Iso.refl X) (whiskerRightIso (isoLeftDualOfEquivDual e).symm Y))

/-- Evaluation of `FDRep.tensorLeftHomLinearEquivOfEquivDual` via `tensorLeftHomEquiv`. -/
@[simp]
theorem tensorLeftHomLinearEquivOfEquivDual_apply {V : FDRep k G}
    (e : _root_.Representation.Equiv V.ρ (Representation.dual V.ρ)) (X Y : FDRep k G)
    (f : V ⊗ X ⟶ Y) :
    tensorLeftHomLinearEquivOfEquivDual e X Y f =
      tensorLeftHomEquiv X (ᘁV) V Y f ≫ (isoLeftDualOfEquivDual e).inv ▷ Y := by
  simp [tensorLeftHomLinearEquivOfEquivDual, Linear.homCongr_apply]

/-- Evaluation of `(FDRep.tensorLeftHomLinearEquivOfEquivDual e X Y).symm`. -/
@[simp]
theorem tensorLeftHomLinearEquivOfEquivDual_symm_apply {V : FDRep k G}
    (e : _root_.Representation.Equiv V.ρ (Representation.dual V.ρ)) (X Y : FDRep k G)
    (g : X ⟶ V ⊗ Y) :
    (tensorLeftHomLinearEquivOfEquivDual e X Y).symm g =
      (tensorLeftHomEquiv X (ᘁV) V Y).symm (g ≫ (isoLeftDualOfEquivDual e).hom ▷ Y) := by
  simp [tensorLeftHomLinearEquivOfEquivDual, Linear.homCongr_symm_apply]

/-- **Frobenius reciprocity for tensor multiplicities.** When `|G|` is invertible in `k`,
`dim_k (X ⟶ V ⊗ Y) = dim_k (Y ⟶ (ᘁV) ⊗ X)` for all `V, X, Y : FDRep k G`. -/
theorem finrank_hom_tensor_leftDual [Invertible (Nat.card G : k)] (V X Y : FDRep k G) :
    Module.finrank k (X ⟶ V ⊗ Y) = Module.finrank k (Y ⟶ (ᘁV) ⊗ X) := by
  rw [FDRep.finrank_hom_comm X (V ⊗ Y), (TauCeti.tensorLeftHomLinearEquiv k Y (ᘁV) V X).finrank_eq]

/-- **Symmetry of tensor multiplicities for a self-dual representation.** When `|G|` is invertible
in `k` and `V` is self-dual, `dim_k (X ⟶ V ⊗ Y) = dim_k (Y ⟶ V ⊗ X)` for all `X, Y : FDRep k G`. -/
theorem finrank_hom_tensor_comm_of_equiv_dual [Invertible (Nat.card G : k)] {V : FDRep k G}
    (he : Nonempty (_root_.Representation.Equiv V.ρ (Representation.dual V.ρ)))
    (X Y : FDRep k G) :
    Module.finrank k (X ⟶ V ⊗ Y) = Module.finrank k (Y ⟶ V ⊗ X) := by
  obtain ⟨e⟩ := he
  rw [finrank_hom_tensor_leftDual V X Y]
  exact (Linear.homCongr k (Iso.refl Y)
    (whiskerRightIso (isoLeftDualOfEquivDual e).symm X)).finrank_eq

end FDRep
