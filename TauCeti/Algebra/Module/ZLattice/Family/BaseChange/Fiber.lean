/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Module.ZLattice.Family.BaseChange.Basic
public import TauCeti.Algebra.Module.ZLattice.Family.Fiber
public import TauCeti.Topology.Category.TopCat.Fiber

/-!
# Categorical base-change square and fiber isomorphism of period quotients

For a period family `P : Y → Λ →ₗ[ℤ] E` and `f : C(Z, Y)`, `TauCeti.torusFamilyBaseChangeMap P f`
forms a commutative square `TauCeti.torusFamilyBaseChangeCommSq` in `TopCat` over `f`. When addition
on `E` and the periods of `P` are continuous, `CategoryTheory.CommSq.fiberMap` over `z : Z`
intertwines `TauCeti.torusFamilyFiberHomeomorph` of `P ∘ f` at `z` and of `P` at `f z`
(`TauCeti.torusFamilyBaseChangeCommSq_fiberMap_fiberHomeomorph`,
`TauCeti.torusFamilyBaseChangeCommSq_fiberMap_comp_fiberHomeomorph`) and is an isomorphism in
`TopCat` (`TauCeti.isIso_torusFamilyBaseChangeCommSq_fiberMap`).

## References

* C. Birkenhake and H. Lange, *Complex Abelian Varieties*, 2nd ed., Springer, 2004, Chapter 8.
-/

public section

noncomputable section

open CategoryTheory

universe u

namespace TauCeti

variable {Y Z E : Type u} {Λ : Type*} [TopologicalSpace Y] [TopologicalSpace Z]
  [AddCommGroup Λ] [AddCommGroup E] [TopologicalSpace E]
  (P : Y → Λ →ₗ[ℤ] E) (f : C(Z, Y))

/-- The commutative square in `TopCat` comparing the pulled-back torus family `(Z × E)/Λ → Z` with
`(Y × E)/Λ → Y` along `f : C(Z, Y)`. -/
theorem torusFamilyBaseChangeCommSq :
    letI := periodAddAction P
    letI := periodAddAction (P ∘ f)
    CommSq
      (TopCat.ofHom
        ⟨torusFamilyBaseChangeMap P f, continuous_torusFamilyBaseChangeMap P f f.continuous⟩)
      (TopCat.ofHom ⟨torusFamilyProjection (P ∘ f), continuous_torusFamilyProjection (P ∘ f)⟩)
      (TopCat.ofHom ⟨torusFamilyProjection P, continuous_torusFamilyProjection P⟩)
      (TopCat.ofHom f) where
  w := by
    let _ := periodAddAction P
    let _ := periodAddAction (P ∘ f)
    ext x
    exact torusFamilyProjection_baseChangeMap P f x

/-- On the fiber over `z`, `torusFamilyBaseChangeCommSq` intertwines the canonical fiber
homeomorphisms of `P ∘ f` at `z` and of `P` at `f z`. -/
theorem torusFamilyBaseChangeCommSq_fiberMap_fiberHomeomorph [ContinuousAdd E]
    (hcont : ∀ l, Continuous fun y ↦ P y l) (z : Z)
    (x : AddAction.orbitRel.Quotient (LinearMap.range ((P ∘ f) z)) E) :
    (torusFamilyBaseChangeCommSq P f).fiberMap z
        (torusFamilyFiberHomeomorph (P ∘ f) z (fun l ↦ (hcont l).comp f.continuous) x) =
      torusFamilyFiberHomeomorph P (f z) hcont x := by
  let _ := periodAddAction P
  let _ := periodAddAction (P ∘ f)
  induction x using Quotient.inductionOn with | h v =>
  apply Subtype.ext
  refine ((torusFamilyBaseChangeCommSq P f).fiberMap_apply_coe z _).trans ?_
  -- Align `Subtype.val` on `(TopCat.ofHom _).fiber _` with `{w | torusFamilyProjection _ w = _}`.
  change torusFamilyBaseChangeMap P f
      (torusFamilyFiberHomeomorph (P ∘ f) z (fun l ↦ (hcont l).comp f.continuous)
        (Quotient.mk _ v)).1 =
    (torusFamilyFiberHomeomorph P (f z) hcont (Quotient.mk _ v)).1
  rw [coe_torusFamilyFiberHomeomorph, coe_torusFamilyFiberHomeomorph,
    torusFamilyFiberMap_mk, torusFamilyFiberMap_mk, torusFamilyBaseChangeMap_mk]

/-- Read through `TauCeti.torusFamilyFiberHomeomorph`, the fiber map of
`torusFamilyBaseChangeCommSq` over `z` is the identity map of `E / range (P (f z))`. -/
theorem torusFamilyBaseChangeCommSq_fiberMap_comp_fiberHomeomorph [ContinuousAdd E]
    (hcont : ∀ l, Continuous fun y ↦ P y l) (z : Z) :
    (ContinuousMap.mk (fun x ↦ (torusFamilyFiberHomeomorph P (f z) hcont).symm x)
        (torusFamilyFiberHomeomorph P (f z) hcont).continuous_symm).comp
        (((torusFamilyBaseChangeCommSq P f).fiberMap z).hom.comp
          ⟨fun x ↦ torusFamilyFiberHomeomorph (P ∘ f) z (fun l ↦ (hcont l).comp f.continuous) x,
            (torusFamilyFiberHomeomorph (P ∘ f) z
              (fun l ↦ (hcont l).comp f.continuous)).continuous⟩) =
      ContinuousMap.id _ := by
  ext x
  exact (Homeomorph.symm_apply_eq (torusFamilyFiberHomeomorph P (f z) hcont)).mpr
    (torusFamilyBaseChangeCommSq_fiberMap_fiberHomeomorph P f hcont z x)

/-- Base change of a continuous period family induces an isomorphism on every fiber in `TopCat`. -/
theorem isIso_torusFamilyBaseChangeCommSq_fiberMap [ContinuousAdd E]
    (hcont : ∀ l, Continuous fun y ↦ P y l) (z : Z) :
    IsIso ((torusFamilyBaseChangeCommSq P f).fiberMap z) := by
  let _ := periodAddAction P
  let _ := periodAddAction (P ∘ f)
  let e := (torusFamilyFiberHomeomorph (P ∘ f) z (fun l ↦ (hcont l).comp f.continuous)).symm.trans
    (torusFamilyFiberHomeomorph P (f z) hcont)
  have heq : (torusFamilyBaseChangeCommSq P f).fiberMap z = (TopCat.isoOfHomeo e).hom := by
    ext x
    obtain ⟨w, rfl⟩ :=
      (torusFamilyFiberHomeomorph (P ∘ f) z (fun l ↦ (hcont l).comp f.continuous)).surjective x
    -- Compare the underlying elements in `AddAction.orbitRel.Quotient Λ (Y × E)`.
    change ((torusFamilyBaseChangeCommSq P f).fiberMap z _ :
        AddAction.orbitRel.Quotient Λ (Y × E)) =
      (e _ : AddAction.orbitRel.Quotient Λ (Y × E))
    rw [torusFamilyBaseChangeCommSq_fiberMap_fiberHomeomorph P f hcont z w]
    simp [e]
  rw [heq]
  infer_instance

end TauCeti
