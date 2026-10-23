/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Induction.Clifford.Obstruction
public import TauCeti.RepresentationTheory.Intertwining
import Mathlib.LinearAlgebra.TensorProduct.Basis
import TauCeti.RepresentationTheory.Irreducible

/-!
# Representations of the inertia group as twisted tensor products

Let `N` be a normal subgroup of `G`, let `A` be a finite-dimensional representation of `N`, and
let `ρ` be a projective extension of `A` to its inertia group `T = inertia A`, compatible with `N`,
whose factor set is inflated from a factor set `β` on the inertia quotient `T/N`
(`TauCeti.IsProjectiveInertiaExtension`). This file shows how an irreducible representation `σ` of
`T` on a space `W` lying over `A` is assembled from `A` and a projective representation of `T/N`.

The multiplicity space is `Hom_N(A, W)`, the `N`-intertwiners from `A` to the restriction of `σ`.
The inertia group acts on it by conjugation, `t • φ = σ t ∘ φ ∘ (ρ t)⁻¹`. This is not a linear
action: the factor set of `ρ` makes it projective with the **inverse** factor set `β⁻¹`, and
because `ρ` restricts to `A` on `N` the elements of `N` act trivially. So the action descends to a
projective representation `TauCeti.IsProjectiveInertiaExtension.homAction` of the inertia quotient
`T/N` with factor set `β⁻¹` (`TauCeti.IsProjectiveInertiaExtension.isProjectiveRep_homAction`).

Tensoring `ρ` with any projective representation `U` of `T/N` with factor set `β⁻¹` cancels the
factor sets: `t ↦ ρ t ⊗ U t` is a linear representation
`TauCeti.IsProjectiveInertiaExtension.tensorRep` of `T` on `A ⊗ X`. For `U` the action on
`Hom_N(A, W)` this is a representation on `A ⊗ Hom_N(A, W)`, and evaluation `x ⊗ φ ↦ φ x`
intertwines it with `σ` (`TauCeti.IsProjectiveInertiaExtension.evalTensor`). Over an
algebraically closed field and for an irreducible `A`, evaluation is injective by Burnside's
density theorem; if moreover `σ` is irreducible and lies over `A`, that is, admits a nonzero
`N`-intertwiner from `A`, its image is a nonzero subrepresentation and hence everything. Thus every
irreducible representation of the inertia group lying over `A` is `A ⊗ U` for a projective
representation `U` of `T/N` whose factor set is `β⁻¹`
(`TauCeti.IsProjectiveInertiaExtension.tensorRepEquiv`); in this setting the class of `β` is the
Clifford obstruction `TauCeti.cliffordObstruction A`.

The converse, that `A ⊗ U` is irreducible exactly when `U` is and that `U` is recovered from
`A ⊗ U`, is in `TauCeti/RepresentationTheory/Induction/Clifford/ProjectiveCorrespondence.lean`.

## Main definitions

* `TauCeti.IsProjectiveInertiaExtension.homAction`: the projective action of the inertia quotient
  on `Hom_N(A, W)`.
* `TauCeti.IsProjectiveInertiaExtension.tensorRep`: the representation `ρ ⊗ U` of the inertia
  group on `A ⊗ X`, for a projective representation `U` of the inertia quotient with factor set
  `β⁻¹`; in particular `ρ ⊗ homAction` on `A ⊗ Hom_N(A, W)`.
* `TauCeti.IsProjectiveInertiaExtension.evalTensor`: the evaluation intertwiner
  `A ⊗ Hom_N(A, W) → W`.
* `TauCeti.IsProjectiveInertiaExtension.tensorRepEquiv`: the equivalence
  `A ⊗ Hom_N(A, W) ≃ W` given by evaluation.

## Main results

* `TauCeti.IsProjectiveInertiaExtension.isProjectiveRep_homAction`: `Hom_N(A, W)` is a projective
  representation of the inertia quotient with factor set `β⁻¹`.
* `TauCeti.IsProjectiveInertiaExtension.evalTensor_injective`: evaluation is injective when `A`
  is irreducible over an algebraically closed field.
* `TauCeti.IsProjectiveInertiaExtension.evalTensor_surjective`: evaluation is surjective when `σ`
  is irreducible and lies over `A`.
* `TauCeti.IsProjectiveInertiaExtension.tensorRepEquiv`: together, an irreducible `σ` lying over an
  irreducible `A` is equivalent to `A ⊗ Hom_N(A, W)`.

## References

* I. M. Isaacs, *Character Theory of Finite Groups*, AMS Chelsea (1976), Chapter 11.
* G. Karpilovsky, *Projective Representations of Finite Groups*, Marcel Dekker (1985).
-/

public section

namespace TauCeti

open CategoryTheory _root_.Representation TensorProduct

universe u v w

namespace IsProjectiveInertiaExtension

section Tensor

variable {k : Type u} {G : Type v} [CommRing k] [Group G] {N : Subgroup G} [N.Normal]
  {A : FDRep k N} {ρ : inertia A → A ≃ₗ[k] A}
  {β : inertia A ⧸ N.subgroupOf (inertia A) → inertia A ⧸ N.subgroupOf (inertia A) → kˣ}
  (h : IsProjectiveInertiaExtension A ρ β)
  {X : Type w} [AddCommMonoid X] [Module k X]
  {U : inertia A ⧸ N.subgroupOf (inertia A) → X ≃ₗ[k] X}

include h

/-- The factor set of `ρ` and the inverse factor set of `U`, inflated to the inertia group, cancel
in the tensor product. -/
private theorem isProjectiveRep_tensor (hU : IsProjectiveRep U fun a b ↦ (β a b)⁻¹) :
    IsProjectiveRep (fun t : inertia A ↦ TensorProduct.congr (ρ t) (U t)) 1 := by
  have hβ : ((fun s t : inertia A ↦ β s t) * fun s t : inertia A ↦ (β s t)⁻¹) = 1 := by
    funext s t
    simp
  exact hβ ▸ h.isProjectiveRep.tensorProduct (hU.comp (QuotientGroup.mk' _))

/-- **The representation `ρ ⊗ U` of the inertia group on `A ⊗ X`**, for a projective
representation `U` of the inertia quotient whose factor set is the inverse of that of `ρ`: the
element `t` acts by `ρ t ⊗ U t`. Each factor is only a projective representation, but their factor
sets `β` and `β⁻¹` cancel, so this is a linear representation. -/
noncomputable def tensorRep (hU : IsProjectiveRep U fun a b ↦ (β a b)⁻¹) :
    Representation k (inertia A) (A ⊗[k] X) :=
  LinearEquiv.automorphismGroup.toLinearMapMonoidHom.comp (h.isProjectiveRep_tensor hU).toMonoidHom

/-- `t` acts on a pure tensor `x ⊗ y` by `ρ t x ⊗ U t y`. -/
@[simp]
theorem tensorRep_tmul (hU : IsProjectiveRep U fun a b ↦ (β a b)⁻¹) (t : inertia A) (x : A)
    (y : X) : h.tensorRep hU t (x ⊗ₜ y) = ρ t x ⊗ₜ U t y := by
  simp [tensorRep]

end Tensor

section Action

variable {k : Type u} {G : Type v} [CommRing k] [Group G] {N : Subgroup G} [N.Normal]
  {A : FDRep k N} {ρ : inertia A → A ≃ₗ[k] A}
  {β : inertia A ⧸ N.subgroupOf (inertia A) → inertia A ⧸ N.subgroupOf (inertia A) → kˣ}
  (h : IsProjectiveInertiaExtension A ρ β)
  {W : Type w} [AddCommMonoid W] [Module k W] (σ : Representation k (inertia A) W)

include h

/-- Conjugating an `N`-intertwiner by `σ t` and `ρ t` gives an `N`-intertwiner again, because `ρ t`
implements conjugation by `t` on `N`. -/
private theorem comp_symm_isIntertwining (t : inertia A)
    (φ : Representation.IntertwiningMap A.ρ (σ.comp (Subgroup.inclusion (le_inertia A))))
    (n : N) (x : A) :
    σ t (φ ((ρ t).symm (A.ρ n x))) =
      σ (Subgroup.inclusion (le_inertia A) n) (σ t (φ ((ρ t).symm x))) := by
  set n' : N := MulAut.conjNormal ((t : G)⁻¹) n with hn'
  have hsymm : (ρ t).symm (A.ρ n x) = A.ρ n' ((ρ t).symm x) := by
    rw [LinearEquiv.symm_apply_eq, h.apply_apply_conjNormal, LinearEquiv.apply_symm_apply, hn']
    simp
  have hmul : t * Subgroup.inclusion (le_inertia A) n' =
      Subgroup.inclusion (le_inertia A) n * t :=
    Subtype.ext (by simp [hn', mul_assoc])
  rw [hsymm, φ.isIntertwining, MonoidHom.comp_apply, ← Module.End.mul_apply, ← map_mul, hmul,
    map_mul, Module.End.mul_apply]

/-- The inverse conjugation of an `N`-intertwiner is an `N`-intertwiner. -/
private theorem comp_isIntertwining (t : inertia A)
    (ψ : Representation.IntertwiningMap A.ρ (σ.comp (Subgroup.inclusion (le_inertia A))))
    (n : N) (x : A) :
    σ t⁻¹ (ψ (ρ t (A.ρ n x))) =
      σ (Subgroup.inclusion (le_inertia A) n) (σ t⁻¹ (ψ (ρ t x))) := by
  have hmul : t⁻¹ * Subgroup.inclusion (le_inertia A) (MulAut.conjNormal (t : G) n) =
      Subgroup.inclusion (le_inertia A) n * t⁻¹ :=
    Subtype.ext (by simp [mul_assoc])
  rw [h.apply_apply_conjNormal, ψ.isIntertwining, MonoidHom.comp_apply, ← Module.End.mul_apply,
    ← map_mul, hmul, map_mul, Module.End.mul_apply]

/-- The action of an element `t` of the inertia group on `Hom_N(A, W)` by conjugation,
`φ ↦ σ t ∘ φ ∘ (ρ t)⁻¹`, before descending to the inertia quotient. -/
private noncomputable def homActionAux (t : inertia A) :
    Representation.IntertwiningMap A.ρ (σ.comp (Subgroup.inclusion (le_inertia A))) ≃ₗ[k]
      Representation.IntertwiningMap A.ρ (σ.comp (Subgroup.inclusion (le_inertia A))) where
  toFun φ := LinearMap.intertwiningMap_of_isIntertwiningMap _ _
    ((σ t).comp (φ.toLinearMap.comp (ρ t).symm.toLinearMap)) (h.comp_symm_isIntertwining σ t φ)
  invFun ψ := LinearMap.intertwiningMap_of_isIntertwiningMap _ _
    ((σ t⁻¹).comp (ψ.toLinearMap.comp (ρ t).toLinearMap)) (h.comp_isIntertwining σ t ψ)
  map_add' φ ψ := by ext; simp
  map_smul' c φ := by ext; simp
  left_inv φ := by
    ext x
    simp [← Module.End.mul_apply, ← map_mul]
  right_inv ψ := by
    ext x
    simp [← Module.End.mul_apply, ← map_mul]

private theorem homActionAux_apply (t : inertia A)
    (φ : Representation.IntertwiningMap A.ρ (σ.comp (Subgroup.inclusion (le_inertia A))))
    (x : A) :
    h.homActionAux σ t φ x = σ t (φ ((ρ t).symm x)) :=
  (rfl)

/-- Elements of `N` act trivially: `ρ` agrees with `A` on `N`, so conjugating an `N`-intertwiner by
an element of `N` returns it. -/
private theorem homActionAux_mul_inclusion (t : inertia A) (n : N) :
    h.homActionAux σ (t * Subgroup.inclusion (le_inertia A) n) = h.homActionAux σ t := by
  refine LinearEquiv.ext fun φ ↦ IntertwiningMap.ext (LinearMap.ext fun x ↦ ?_)
  simp only [IntertwiningMap.toLinearMap_apply]
  have hsymm : (ρ (t * Subgroup.inclusion (le_inertia A) n)).symm x =
      A.ρ n⁻¹ ((ρ t).symm x) := by
    rw [LinearEquiv.symm_apply_eq, h.apply_mul_inclusion, ← Module.End.mul_apply, ← map_mul,
      mul_inv_cancel, map_one, Module.End.one_apply, LinearEquiv.apply_symm_apply]
  rw [homActionAux_apply, hsymm, φ.isIntertwining, MonoidHom.comp_apply, ← Module.End.mul_apply,
    ← map_mul, mul_assoc, ← map_mul, mul_inv_cancel, map_one, mul_one, homActionAux_apply]

/-- The conjugation action of the inertia group on `Hom_N(A, W)` is projective with the inverse of
the factor set of `ρ`. -/
private theorem isProjectiveRep_homActionAux :
    IsProjectiveRep (h.homActionAux σ) fun s t ↦ (β s t)⁻¹ where
  isFactorSet := h.isProjectiveRep.isFactorSet.inv
  map_one := by
    ext φ x
    simp [homActionAux_apply, h.isProjectiveRep.map_one, LinearEquiv.one_eq_refl]
  mul_apply s t φ := by
    ext x
    have hsymm : (ρ (s * t)).symm x = (β s t : k) • (ρ t).symm ((ρ s).symm x) := by
      rw [LinearEquiv.symm_apply_eq, map_smul, ← h.isProjectiveRep.mul_apply]
      simp
    simp [homActionAux_apply, hsymm, smul_smul, ← Module.End.mul_apply, ← map_mul]

/-- **The projective action of the inertia quotient on `Hom_N(A, W)`**: the coset of `t` acts by
`φ ↦ σ t ∘ φ ∘ (ρ t)⁻¹`. Elements of `N` act trivially, so this is well defined on
`inertia A ⧸ N`; it is a projective representation whose factor set is the inverse of `β`
(`TauCeti.IsProjectiveInertiaExtension.isProjectiveRep_homAction`). -/
noncomputable def homAction (q : inertia A ⧸ N.subgroupOf (inertia A)) :
    Representation.IntertwiningMap A.ρ (σ.comp (Subgroup.inclusion (le_inertia A))) ≃ₗ[k]
      Representation.IntertwiningMap A.ρ (σ.comp (Subgroup.inclusion (le_inertia A))) :=
  Quotient.liftOn' q (h.homActionAux σ) fun a b hab ↦ by
    rw [QuotientGroup.leftRel_apply] at hab
    obtain ⟨n, hn⟩ : ∃ n : N, Subgroup.inclusion (le_inertia A) n = a⁻¹ * b :=
      ⟨⟨_, Subgroup.mem_subgroupOf.1 hab⟩, Subtype.ext rfl⟩
    rw [← mul_inv_cancel_left a b, ← hn, h.homActionAux_mul_inclusion]

/-- The coset of `t` acts by `φ ↦ σ t ∘ φ ∘ (ρ t)⁻¹`. -/
@[simp]
theorem homAction_mk_apply (t : inertia A)
    (φ : Representation.IntertwiningMap A.ρ (σ.comp (Subgroup.inclusion (le_inertia A))))
    (x : A) :
    h.homAction σ t φ x = σ t (φ ((ρ t).symm x)) := by
  rw [homAction, QuotientGroup.mk, Quotient.liftOn'_mk'', homActionAux_apply]

/-- **`Hom_N(A, W)` is a projective representation of the inertia quotient whose factor set is the
inverse of `β`.** Over an algebraically closed field and for an irreducible `A`, the class of `β`
is the Clifford obstruction of `A`
(`TauCeti.IsProjectiveInertiaExtension.cohomologyClass_factorSet_eq_cliffordObstruction`). -/
theorem isProjectiveRep_homAction :
    IsProjectiveRep (h.homAction σ) fun a b ↦ (β a b)⁻¹ where
  isFactorSet := h.isFactorSet.inv
  map_one := (h.isProjectiveRep_homActionAux σ).map_one
  mul_apply a b φ := by
    induction a using QuotientGroup.induction_on with | H s =>
    induction b using QuotientGroup.induction_on with | H t =>
    exact (h.isProjectiveRep_homActionAux σ).mul_apply s t φ

/-- **Evaluation `A ⊗ Hom_N(A, W) → W`**, `x ⊗ φ ↦ φ x`, as an intertwiner to `σ` from
`TauCeti.IsProjectiveInertiaExtension.tensorRep` of the conjugation action on `Hom_N(A, W)`. -/
noncomputable def evalTensor :
    (h.tensorRep (h.isProjectiveRep_homAction σ)).IntertwiningMap σ :=
  (TensorProduct.lift (LinearMap.mk₂ k
    (fun (x : A) (φ : Representation.IntertwiningMap A.ρ
      (σ.comp (Subgroup.inclusion (le_inertia A)))) ↦ φ x)
    (fun x y φ ↦ map_add φ x y) (fun c x φ ↦ map_smul φ c x) (fun _ _ _ ↦ rfl)
    (fun _ _ _ ↦ rfl))).intertwiningMap_of_isIntertwiningMap _ _ fun t z ↦ by
      induction z using TensorProduct.inductionOn with
      | tmul x φ => simp
      | add z z' hz hz' => simp only [map_add, hz, hz']

/-- Evaluation sends `x ⊗ φ` to `φ x`. -/
@[simp]
theorem evalTensor_tmul (x : A)
    (φ : Representation.IntertwiningMap A.ρ (σ.comp (Subgroup.inclusion (le_inertia A)))) :
    h.evalTensor σ (x ⊗ₜ φ) = φ x := by
  rw [evalTensor, LinearMap.toIntertwiningMap, TensorProduct.lift.tmul, LinearMap.mk₂_apply]

end Action

section Field

variable {k : Type u} {G : Type v} [Field k] [Group G] {N : Subgroup G} [N.Normal]
  {A : FDRep k N} {ρ : inertia A → A ≃ₗ[k] A}
  {β : inertia A ⧸ N.subgroupOf (inertia A) → inertia A ⧸ N.subgroupOf (inertia A) → kˣ}
  (h : IsProjectiveInertiaExtension A ρ β)
  {W : Type w} [AddCommGroup W] [Module k W] (σ : Representation k (inertia A) W)

include h

/-- **Evaluation onto an irreducible representation lying over `A` is surjective**: if `σ` is
irreducible and some `N`-intertwiner `A → W` is nonzero, the image of evaluation is a nonzero
subrepresentation of `σ`. -/
theorem evalTensor_surjective [σ.IsIrreducible]
    {φ : Representation.IntertwiningMap A.ρ (σ.comp (Subgroup.inclusion (le_inertia A)))}
    (hφ : φ ≠ 0) : Function.Surjective (h.evalTensor σ) := by
  refine (IsIrreducible.surjective_or_eq_zero (h.evalTensor σ)).resolve_right fun h0 ↦ hφ ?_
  refine IntertwiningMap.ext (LinearMap.ext fun x ↦ ?_)
  simpa using congr($h0 (x ⊗ₜ φ))

variable [IsAlgClosed k] [Simple A]

/-- **Evaluation `A ⊗ Hom_N(A, W) → W` is injective** for an irreducible `A` over an algebraically
closed field. -/
theorem evalTensor_injective : Function.Injective (h.evalTensor σ) := by
  -- Evaluation intertwines the action of `k[N]` on the left tensor factor with that on `W`.
  have hev (r : MonoidAlgebra k N)
      (z : A ⊗[k] Representation.IntertwiningMap A.ρ (σ.comp (Subgroup.inclusion (le_inertia A)))) :
      h.evalTensor σ ((Representation.asAlgebraHom A.ρ r).rTensor _ z) =
        Representation.asAlgebraHom (σ.comp (Subgroup.inclusion (le_inertia A))) r
          (h.evalTensor σ z) := by
    induction z using TensorProduct.inductionOn with
    | tmul x φ =>
      rw [LinearMap.rTensor_tmul, evalTensor_tmul, evalTensor_tmul, φ.apply_asAlgebraHom]
    | add z z' hz hz' => simp only [map_add, hz, hz']
  refine (injective_iff_map_eq_zero (h.evalTensor σ)).2 fun z hz ↦ by_contra fun hz0 ↦ ?_
  -- By density, `k[N]` moves `z` to `v ⊗ φ` for every `v`, with one fixed `φ ≠ 0`; evaluating,
  -- `φ v = 0` for every `v`.
  obtain ⟨φ, hφ, hr⟩ := Representation.exists_ne_zero_forall_exists_rTensor_asAlgebraHom_eq_tmul
    A.ρ (FDRep.isIrreducible_of_simple A) hz0
  refine hφ (IntertwiningMap.ext (LinearMap.ext fun v ↦ ?_))
  obtain ⟨r, hr⟩ := hr v
  have := hev r z
  rwa [hr, hz, map_zero, evalTensor_tmul] at this

/-- **An irreducible representation of the inertia group lying over `A` is `A ⊗ Hom_N(A, W)`.**
Here `A` is irreducible over an algebraically closed field, `σ` is irreducible and admits a nonzero
`N`-intertwiner from `A`, and the inertia group acts on `A ⊗ Hom_N(A, W)` by `ρ ⊗ homAction`,
where `homAction` is a projective representation of the inertia quotient whose factor set is
inverse to that of `ρ`. -/
noncomputable def tensorRepEquiv [σ.IsIrreducible]
    {φ : Representation.IntertwiningMap A.ρ (σ.comp (Subgroup.inclusion (le_inertia A)))}
    (hφ : φ ≠ 0) : (h.tensorRep (h.isProjectiveRep_homAction σ)).Equiv σ :=
  (h.evalTensor σ).ofBijective ⟨h.evalTensor_injective σ, h.evalTensor_surjective σ hφ⟩

/-- The equivalence `A ⊗ Hom_N(A, W) ≃ W` is evaluation. -/
@[simp]
theorem tensorRepEquiv_tmul [σ.IsIrreducible]
    {φ : Representation.IntertwiningMap A.ρ (σ.comp (Subgroup.inclusion (le_inertia A)))}
    (hφ : φ ≠ 0) (x : A)
    (ψ : Representation.IntertwiningMap A.ρ (σ.comp (Subgroup.inclusion (le_inertia A)))) :
    h.tensorRepEquiv σ hφ (x ⊗ₜ ψ) = ψ x :=
  (congrFun (IntertwiningMap.coe_ofBijective _ _ (h.evalTensor σ) _) _).trans
    (h.evalTensor_tmul σ x ψ)

end Field

end IsProjectiveInertiaExtension

end TauCeti
