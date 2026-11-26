/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Algebra.ContinuousMonoidHom
public import TauCeti.CategoryTheory.Monoidal.Subcategory
public import TauCeti.RepresentationTheory.RepresentationRing.Continuous
public import TauCeti.RepresentationTheory.RepresentationRing.Restriction

/-!
# Restriction of continuous representations along continuous homomorphisms

Let `φ : G →ₜ* H` be a continuous homomorphism of topological monoids and `k` a topological field.
Restricting a finite-dimensional representation of `H` along `φ` keeps its matrix coefficients
continuous, since they are the matrix coefficients of the original representation precomposed with
`φ` (`FDRep.isContinuous_res`). So restriction along `φ` is a functor
`TauCeti.ContFDRep.res k φ : ContFDRep k H ⥤ ContFDRep k G` between the categories of continuous
finite-dimensional representations. Like restriction of all finite-dimensional representations, it
preserves biproducts and tensor products on the nose, so it induces a ring homomorphism of the
representation rings of continuous representations,

`TauCeti.contRepRingRes k φ : R(H) →+* R(G)`.

Restriction is contravariantly functorial in `φ`, and forgetting continuity intertwines it with the
restriction `TauCeti.repRingRes` of all finite-dimensional representations
(`TauCeti.contRepRingToRepRing_contRepRingRes`). For a closed subgroup of a compact Lie group,
restriction along its inclusion is the restriction map of equivariant K-theory at a point.

## Main definitions

* `TauCeti.ContFDRep.res`: restriction of continuous finite-dimensional representations along a
  continuous homomorphism.
* `TauCeti.contRepRingRes`: the induced ring homomorphism of representation rings.

## Main statements

* `FDRep.isContinuous_res`: the restriction of a continuous representation along a continuous
  homomorphism is continuous.
* `TauCeti.contRepRingRes_of`, `TauCeti.contRepRingRes_id` and `TauCeti.contRepRingRes_comp`: the
  value on classes and the functoriality of restriction.
* `TauCeti.contRepRingToRepRing_contRepRingRes`: forgetting continuity commutes with restriction.

## References

* G. Segal, *Equivariant K-theory*, Publ. Math. IHÉS 34 (1968), §2, for the representation ring
  `R(G)` of continuous representations and its restriction homomorphisms.
-/

public section

open CategoryTheory

universe u v v' v''

namespace FDRep

variable {k : Type u} [Field k] [TopologicalSpace k] {G : Type v} {H : Type v'} [Monoid G]
  [TopologicalSpace G] [Monoid H] [TopologicalSpace H]

/-- **The restriction of a continuous representation along a continuous homomorphism is
continuous**: its matrix coefficients are those of the original representation precomposed with
the homomorphism. -/
theorem isContinuous_res {φ : G →* H} (hφ : Continuous φ) {V : FDRep k H}
    (hV : isContinuous k H V) : isContinuous k G ((Action.res (FGModuleCat.{u} k) φ).obj V) :=
  isContinuous_iff.2 fun f v ↦ (isContinuous_iff.1 hV f v).comp hφ

end FDRep

namespace TauCeti

variable (k : Type u) [Field k] [TopologicalSpace k] {G : Type v} {H : Type v'} {K : Type v''}
  [Monoid G] [TopologicalSpace G] [Monoid H] [TopologicalSpace H] [Monoid K] [TopologicalSpace K]

/-- **Restriction of continuous finite-dimensional representations** along a continuous
homomorphism `φ : G →ₜ* H`: Mathlib's restriction functor `CategoryTheory.Action.res` along `φ`,
lifted to the categories of continuous representations by `FDRep.isContinuous_res`. -/
noncomputable def ContFDRep.res (φ : G →ₜ* H) : ContFDRep k H ⥤ ContFDRep k G :=
  (FDRep.isContinuous k G).lift
    ((FDRep.isContinuous k H).ι ⋙ Action.res (FGModuleCat.{u} k) φ.toMonoidHom)
    fun V ↦ FDRep.isContinuous_res φ.continuous V.property

variable {k}

/-- The underlying representation of a restricted continuous representation is the restriction of
the underlying representation. -/
@[simp]
theorem ContFDRep.res_obj_obj (φ : G →ₜ* H) (V : ContFDRep k H) :
    ((ContFDRep.res k φ).obj V).obj = (Action.res (FGModuleCat.{u} k) φ.toMonoidHom).obj V.obj :=
  (rfl)

variable [ContinuousAdd k]

/-- Restriction of continuous representations is additive. -/
instance (φ : G →ₜ* H) : (ContFDRep.res k φ).Additive :=
  inferInstanceAs ((FDRep.isContinuous k G).lift
    ((FDRep.isContinuous k H).ι ⋙ Action.res (FGModuleCat.{u} k) φ.toMonoidHom)
    fun V ↦ FDRep.isContinuous_res φ.continuous V.property).Additive

variable [ContinuousMul k]

/-- Restriction of continuous representations is monoidal, with the comparison isomorphisms of
`CategoryTheory.Action.res`. -/
noncomputable instance (φ : G →ₜ* H) : (ContFDRep.res k φ).Monoidal :=
  inferInstanceAs ((FDRep.isContinuous k G).lift
    ((FDRep.isContinuous k H).ι ⋙ Action.res (FGModuleCat.{u} k) φ.toMonoidHom)
    fun V ↦ FDRep.isContinuous_res φ.continuous V.property).Monoidal

variable (k) in
/-- **Restriction of continuous representations, on the representation ring**: the ring
homomorphism `R(H) →+* R(G)` induced by a continuous homomorphism `φ : G →ₜ* H`, sending the class
of a continuous representation of `H` to the class of its restriction along `φ`. It is a ring
homomorphism because the restriction functor `TauCeti.ContFDRep.res` is monoidal, with the
comparison isomorphisms of `CategoryTheory.Action.res`. -/
noncomputable def contRepRingRes (φ : G →ₜ* H) : contRepRing k H →+* contRepRing k G :=
  SplitK0.mapRingHom (ContFDRep.res k φ)

/-- Restriction sends the class of a continuous representation to the class of its restriction. -/
@[simp]
theorem contRepRingRes_of (φ : G →ₜ* H) (V : ContFDRep k H) :
    contRepRingRes k φ (SplitK0.of V) = SplitK0.of ((ContFDRep.res k φ).obj V) :=
  SplitK0.mapRingHom_of _ V

/-- **Restricting along the identity does nothing.** -/
@[simp]
theorem contRepRingRes_id : contRepRingRes k (ContinuousMonoidHom.id G) = RingHom.id _ :=
  SplitK0.ringHom_ext fun V ↦ by
    rw [contRepRingRes_of, RingHom.id_apply]
    exact SplitK0.of_congr ((FDRep.isContinuous k G).isoMk ((Action.resId _).app V.obj))

/-- **Restriction is contravariantly functorial**: restricting along a composite is restricting
twice over. -/
@[simp]
theorem contRepRingRes_comp (φ : G →ₜ* H) (ψ : H →ₜ* K) :
    contRepRingRes k (ψ.comp φ) = (contRepRingRes k φ).comp (contRepRingRes k ψ) :=
  SplitK0.ringHom_ext fun V ↦ by
    rw [RingHom.comp_apply, contRepRingRes_of, contRepRingRes_of, contRepRingRes_of]
    exact SplitK0.of_congr ((FDRep.isContinuous k G).isoMk
      ((Action.resComp _ φ.toMonoidHom ψ.toMonoidHom).app V.obj).symm)

/-- **Forgetting continuity commutes with restriction**: the square formed by the restrictions of
continuous and of all finite-dimensional representations and the two forgetful homomorphisms
commutes. -/
theorem contRepRingToRepRing_comp_contRepRingRes (φ : G →ₜ* H) :
    (contRepRingToRepRing k G).comp (contRepRingRes k φ) =
      (repRingRes k φ.toMonoidHom).comp (contRepRingToRepRing k H) :=
  SplitK0.ringHom_ext fun V ↦ by
    simp only [RingHom.comp_apply, contRepRingRes_of, contRepRingToRepRing_of, repRingRes_of,
      ContFDRep.res_obj_obj]

/-- **Forgetting continuity commutes with restriction**, elementwise. -/
@[simp]
theorem contRepRingToRepRing_contRepRingRes (φ : G →ₜ* H) (x : contRepRing k H) :
    contRepRingToRepRing k G (contRepRingRes k φ x) =
      repRingRes k φ.toMonoidHom (contRepRingToRepRing k H x) :=
  RingHom.congr_fun (contRepRingToRepRing_comp_contRepRingRes φ) x

end TauCeti
