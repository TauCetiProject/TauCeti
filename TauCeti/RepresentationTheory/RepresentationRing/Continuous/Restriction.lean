/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.FDRep.Continuous.Restriction
public import TauCeti.RepresentationTheory.RepresentationRing.Continuous
public import TauCeti.RepresentationTheory.RepresentationRing.Restriction

/-!
# Restriction of continuous representations along continuous homomorphisms

Let `φ : G →ₜ* H` be a continuous homomorphism of topological monoids and `k` a topological field.
Restriction along `φ` is a functor
`TauCeti.ContFDRep.res k φ : ContFDRep k H ⥤ ContFDRep k G` between the categories of continuous
finite-dimensional representations
(`TauCeti/RepresentationTheory/FDRep/Continuous/Restriction.lean`). Like restriction of all
finite-dimensional representations, it preserves biproducts and tensor products on the nose, so it
induces a ring homomorphism of the representation rings of continuous representations,

`TauCeti.contRepRingRes k φ : R(H) →+* R(G)`.

Restriction is contravariantly functorial in `φ`, and forgetting continuity intertwines it with the
restriction `TauCeti.repRingRes` of all finite-dimensional representations
(`TauCeti.contRepRingToRepRing_contRepRingRes`). For a closed subgroup of a compact Lie group,
restriction along its inclusion is the restriction map of equivariant K-theory at a point.

## Main definitions

* `TauCeti.contRepRingRes`: the ring homomorphism of representation rings induced by restriction.

## Main statements

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

namespace TauCeti

variable {k : Type u} [Field k] [TopologicalSpace k] {G : Type v} {H : Type v'} {K : Type v''}
  [Monoid G] [TopologicalSpace G] [Monoid H] [TopologicalSpace H] [Monoid K] [TopologicalSpace K]
  [ContinuousAdd k] [ContinuousMul k]

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
    refine SplitK0.of_congr ((FDRep.isContinuous k G).isoMk ?_)
    rw [ContFDRep.res_obj_obj]
    exact (Action.resId _).app V.obj

/-- **Restriction is contravariantly functorial**: restricting along a composite is restricting
twice over. -/
@[simp]
theorem contRepRingRes_comp (φ : G →ₜ* H) (ψ : H →ₜ* K) :
    contRepRingRes k (ψ.comp φ) = (contRepRingRes k φ).comp (contRepRingRes k ψ) :=
  SplitK0.ringHom_ext fun V ↦ by
    rw [RingHom.comp_apply, contRepRingRes_of, contRepRingRes_of, contRepRingRes_of]
    refine SplitK0.of_congr ((FDRep.isContinuous k G).isoMk ?_)
    rw [ContFDRep.res_obj_obj, ContFDRep.res_obj_obj, ContFDRep.res_obj_obj]
    exact ((Action.resComp _ φ.toMonoidHom ψ.toMonoidHom).app V.obj).symm

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
