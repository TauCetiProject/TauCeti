/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Module.Submodule.OrbitRelQuotient
public import TauCeti.Algebra.Module.ZLattice.Family.Fiber
public import TauCeti.Topology.Algebra.Module.Quotient
public import TauCeti.Topology.Category.TopCat.Fiber
import Mathlib.Topology.Homeomorph.Quotient

/-!
# Lattice re-marking of period quotients

Precomposing a period family `P : Y → Λ →ₗ[ℤ] E` with a `ℤ`-linear equivalence `α : Λ' ≃ₗ[ℤ] Λ`
leaves `LinearMap.range (P y)` and the orbits on `Y × E` unchanged, without requiring any basis,
injectivity, discreteness, or fullness hypothesis:

* `TauCeti.torusFamilyRemarkHomeomorph`: the homeomorphism `(Y × E)/Λ' ≃ₜ (Y × E)/Λ` over `Y`.
* `TauCeti.torusFamilyProjection_remarkHomeomorph`, `TauCeti.torusFamilyRemarkCommSq`:
  compatibility with `torusFamilyProjection` and commutative square over `𝟙 (TopCat.of Y)`.
* `TauCeti.torusFamilyRemarkCommSq_fiberMap_fiberHomeomorph`,
  `TauCeti.torusFamilyRemarkCommSq_fiberMap_comp_fiberHomeomorph`,
  `TauCeti.isIso_torusFamilyRemarkCommSq_fiberMap`: compatibility with
  `TauCeti.torusFamilyFiberHomeomorph` and fiber isomorphism in `TopCat`.

## References

* C. Birkenhake and H. Lange, *Complex Abelian Varieties*, 2nd ed., Springer, 2004, Chapter 8.
-/

public section

noncomputable section

open CategoryTheory

universe u

namespace TauCeti

section Remark

variable {Y Λ Λ' E : Type*} [AddCommGroup Λ] [AddCommGroup Λ'] [AddCommGroup E]
  (P : Y → Λ →ₗ[ℤ] E) (α : Λ' ≃ₗ[ℤ] Λ)

private theorem mem_orbit_period_comp_equiv_iff {p q : Y × E} :
    (letI := periodAddAction fun y ↦ (P y).comp α.toLinearMap; q ∈ AddAction.orbit Λ' p) ↔
      (letI := periodAddAction P; q ∈ AddAction.orbit Λ p) := by
  rw [mem_orbit_periodAddAction_iff, mem_orbit_periodAddAction_iff, LinearEquiv.range_comp]

/-- **Re-marking homeomorphism.** Precomposing every period map with a `ℤ`-linear equivalence
`α : Λ' ≃ₗ[ℤ] Λ` leaves the orbits on `Y × E` unchanged, inducing the identity homeomorphism
`[y, v] ↦ [y, v]` between the period quotients over `Y`. -/
def torusFamilyRemarkHomeomorph [TopologicalSpace Y] [TopologicalSpace E] :
    letI := periodAddAction fun y ↦ (P y).comp α.toLinearMap
    letI := periodAddAction P
    AddAction.orbitRel.Quotient Λ' (Y × E) ≃ₜ AddAction.orbitRel.Quotient Λ (Y × E) :=
  letI := periodAddAction fun y ↦ (P y).comp α.toLinearMap
  letI := periodAddAction P
  Homeomorph.Quotient.congrRight fun _ _ ↦ mem_orbit_period_comp_equiv_iff P α

@[simp]
theorem torusFamilyRemarkHomeomorph_mk [TopologicalSpace Y] [TopologicalSpace E] (p : Y × E) :
    torusFamilyRemarkHomeomorph P α (Quotient.mk _ p) = Quotient.mk _ p :=
  (rfl)

@[simp]
theorem torusFamilyRemarkHomeomorph_symm_mk [TopologicalSpace Y] [TopologicalSpace E] (p : Y × E) :
    (torusFamilyRemarkHomeomorph P α).symm (Quotient.mk _ p) = Quotient.mk _ p :=
  (rfl)

@[simp]
theorem torusFamilyProjection_remarkHomeomorph [TopologicalSpace Y] [TopologicalSpace E]
    (x : letI := periodAddAction fun y ↦ (P y).comp α.toLinearMap
      AddAction.orbitRel.Quotient Λ' (Y × E)) :
    torusFamilyProjection P (torusFamilyRemarkHomeomorph P α x) =
      torusFamilyProjection (fun y ↦ (P y).comp α.toLinearMap) x := by
  induction x using Quotient.inductionOn
  simp

end Remark

section RemarkSquare

variable {Y E : Type u} {Λ Λ' : Type*} [TopologicalSpace Y] [AddCommGroup Λ] [AddCommGroup Λ']
  [AddCommGroup E] [TopologicalSpace E] (P : Y → Λ →ₗ[ℤ] E) (α : Λ' ≃ₗ[ℤ] Λ)

/-- The commutative square in `TopCat` over `𝟙 (TopCat.of Y)` induced by re-marking the lattice by
`α : Λ' ≃ₗ[ℤ] Λ`. -/
theorem torusFamilyRemarkCommSq :
    letI := periodAddAction fun y ↦ (P y).comp α.toLinearMap
    letI := periodAddAction P
    CommSq
      (TopCat.ofHom (torusFamilyRemarkHomeomorph P α : C(_, _)))
      (TopCat.ofHom ⟨torusFamilyProjection fun y ↦ (P y).comp α.toLinearMap,
        continuous_torusFamilyProjection _⟩)
      (TopCat.ofHom ⟨torusFamilyProjection P, continuous_torusFamilyProjection P⟩)
      (𝟙 (TopCat.of Y)) where
  w := by
    let _ := periodAddAction fun y ↦ (P y).comp α.toLinearMap
    let _ := periodAddAction P
    ext x
    exact torusFamilyProjection_remarkHomeomorph P α x

/-- On the fiber over `y`, `torusFamilyRemarkCommSq` intertwines the canonical fiber homeomorphisms
via the identity map of `E` between the equal period lattices. -/
theorem torusFamilyRemarkCommSq_fiberMap_fiberHomeomorph [ContinuousAdd E]
    (hcont : ∀ l, Continuous fun y ↦ P y l) (y : Y)
    (x : AddAction.orbitRel.Quotient (LinearMap.range ((P y).comp α.toLinearMap)) E) :
    (torusFamilyRemarkCommSq P α).fiberMap y
        (torusFamilyFiberHomeomorph (fun y ↦ (P y).comp α.toLinearMap) y
          (fun l' ↦ hcont (α l')) x) =
      torusFamilyFiberHomeomorph P y hcont
        ((LinearMap.range ((P y).comp α.toLinearMap)).orbitRelQuotientMap (LinearMap.range (P y))
          LinearMap.id (by simp) x) := by
  let _ := periodAddAction fun y ↦ (P y).comp α.toLinearMap
  let _ := periodAddAction P
  induction x using Quotient.inductionOn with | h v =>
  apply Subtype.ext
  refine ((torusFamilyRemarkCommSq P α).fiberMap_apply_coe y _).trans ?_
  -- Align `Subtype.val` on `(TopCat.ofHom _).fiber _` with `{w | torusFamilyProjection _ w = y}`.
  change torusFamilyRemarkHomeomorph P α
      (torusFamilyFiberHomeomorph (fun y ↦ (P y).comp α.toLinearMap) y
        (fun l' ↦ hcont (α l')) (Quotient.mk _ v)).1 =
    (torusFamilyFiberHomeomorph P y hcont _).1
  simp

/-- Read through `TauCeti.torusFamilyFiberHomeomorph`, the fiber map of `torusFamilyRemarkCommSq`
over `y` is the `Submodule.orbitRelQuotientMap` induced by `LinearMap.id` between the equal period
lattices. -/
theorem torusFamilyRemarkCommSq_fiberMap_comp_fiberHomeomorph [ContinuousAdd E]
    (hcont : ∀ l, Continuous fun y ↦ P y l) (y : Y) :
    (ContinuousMap.mk (fun x ↦ (torusFamilyFiberHomeomorph P y hcont).symm x)
        (torusFamilyFiberHomeomorph P y hcont).continuous_symm).comp
        (((torusFamilyRemarkCommSq P α).fiberMap y).hom.comp
          ⟨fun x ↦ torusFamilyFiberHomeomorph (fun y ↦ (P y).comp α.toLinearMap) y
              (fun l' ↦ hcont (α l')) x,
            (torusFamilyFiberHomeomorph (fun y ↦ (P y).comp α.toLinearMap) y
              (fun l' ↦ hcont (α l'))).continuous⟩) =
      ⟨(LinearMap.range ((P y).comp α.toLinearMap)).orbitRelQuotientMap (LinearMap.range (P y))
          LinearMap.id (by simp),
        (LinearMap.range ((P y).comp α.toLinearMap)).continuous_orbitRelQuotientMap
          (LinearMap.range (P y)) (by simp) continuous_id⟩ := by
  ext x
  exact (Homeomorph.symm_apply_eq (torusFamilyFiberHomeomorph P y hcont)).mpr
    (torusFamilyRemarkCommSq_fiberMap_fiberHomeomorph P α hcont y x)

/-- Re-marking the lattice induces an isomorphism on every fiber in `TopCat`. -/
instance isIso_torusFamilyRemarkCommSq_fiberMap (y : Y) :
    IsIso ((torusFamilyRemarkCommSq P α).fiberMap y) := by
  let _ := periodAddAction fun y ↦ (P y).comp α.toLinearMap
  let _ := periodAddAction P
  let p' : TopCat.of (AddAction.orbitRel.Quotient Λ' (Y × E)) ⟶ TopCat.of Y :=
    TopCat.ofHom ⟨torusFamilyProjection fun y ↦ (P y).comp α.toLinearMap,
      continuous_torusFamilyProjection _⟩
  let p : TopCat.of (AddAction.orbitRel.Quotient Λ (Y × E)) ⟶ TopCat.of Y :=
    TopCat.ofHom ⟨torusFamilyProjection P, continuous_torusFamilyProjection P⟩
  let e : p'.fiber y ≃ₜ p.fiber ((𝟙 (TopCat.of Y)) y) :=
    (torusFamilyRemarkHomeomorph P α).subtype fun x ↦ by
      simp [p', p, torusFamilyProjection_remarkHomeomorph]
  have heq : (torusFamilyRemarkCommSq P α).fiberMap y = (TopCat.isoOfHomeo e).hom := by
    ext x
    exact (torusFamilyRemarkCommSq P α).fiberMap_apply_coe y x
  rw [heq]
  infer_instance

end RemarkSquare

end TauCeti
