/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kimi K3
-/
module

public import Mathlib.Algebra.DirectSum.Decomposition

/-!
# Homogeneous piece projections on an internally decomposed module

For a family of submodules with a direct-sum decomposition, `TauCeti.homogeneousProj` is the linear
projection `M →ₗ[R] ℳ η` onto the `η`-th homogeneous piece, and `TauCeti.homogeneousComponent`
composes it with the submodule inclusion to give an endomorphism of the ambient module. These
projections are idempotent and pairwise orthogonal, acting as the identity on their own piece and as
zero on every other piece. We also record the subtype-valued evaluations
`TauCeti.decompose_apply_of_mem_same` and `TauCeti.decompose_apply_of_mem_ne` of
`DirectSum.decompose` for any `AddSubmonoidClass` decomposition.

Adapted from `yuma-mizuno-lean/Mei`, commit
`bac6f02d25746bc1c2ec808601d4e9284911c475` (Apache 2.0),
`Mei/Algebra/DirectSum/Component.lean`.
-/

public noncomputable section

namespace TauCeti

section AddCommMonoid

variable {ι M σ : Type*} [DecidableEq ι] [AddCommMonoid M]
  [SetLike σ M] [AddSubmonoidClass σ M] (ℳ : ι → σ) [DirectSum.Decomposition ℳ]

/-- Evaluating `DirectSum.decompose ℳ` at degree `i` on an element `hx : x ∈ ℳ i` returns the
bundled element `⟨x, hx⟩`. -/
theorem decompose_apply_of_mem_same {i : ι} {x : M} (hx : x ∈ ℳ i) :
    DirectSum.decompose ℳ x i = ⟨x, hx⟩ :=
  Subtype.ext (DirectSum.decompose_of_mem_same ℳ hx)

/-- Evaluating `DirectSum.decompose ℳ` at degree `j` on an element of a distinct piece `ℳ i`
(`i ≠ j`) returns `0` in `ℳ j`. -/
theorem decompose_apply_of_mem_ne {i j : ι} {x : M} (hx : x ∈ ℳ i) (hij : i ≠ j) :
    DirectSum.decompose ℳ x j = 0 :=
  Subtype.ext (DirectSum.decompose_of_mem_ne ℳ hx hij)

end AddCommMonoid

variable {R M ι : Type*} [Semiring R] [AddCommMonoid M] [Module R M]
  [DecidableEq ι] (ℳ : ι → Submodule R M) [DirectSum.Decomposition ℳ]

/-- Linear projection onto the `η`-th homogeneous piece of an internal direct-sum decomposition,
sending `a` to `DirectSum.decompose ℳ a η`. -/
def homogeneousProj (η : ι) : M →ₗ[R] ℳ η :=
  (DirectSum.component R ι (fun i => ℳ i) η).comp
    (DirectSum.decomposeLinearEquiv ℳ).toLinearMap

/-- Applying `homogeneousProj` evaluates `DirectSum.decompose` at the selected degree. -/
@[simp]
theorem homogeneousProj_apply (η : ι) (a : M) :
    homogeneousProj ℳ η a = DirectSum.decompose ℳ a η := by
  rw [homogeneousProj, LinearMap.comp_apply, LinearEquiv.coe_coe,
    DirectSum.decomposeLinearEquiv_apply, ← DirectSum.apply_eq_component]

/-- `homogeneousProj` returns a homogeneous input of its own degree bundled in `ℳ η`. -/
theorem homogeneousProj_apply_of_mem {η : ι} {a : M} (ha : a ∈ ℳ η) :
    homogeneousProj ℳ η a = ⟨a, ha⟩ := by
  rw [homogeneousProj_apply, decompose_apply_of_mem_same ℳ ha]

/-- `homogeneousProj` annihilates homogeneous inputs of any other degree. -/
theorem homogeneousProj_apply_of_mem_ne {i η : ι} {a : M} (ha : a ∈ ℳ i) (h : i ≠ η) :
    homogeneousProj ℳ η a = 0 := by
  rw [homogeneousProj_apply, decompose_apply_of_mem_ne ℳ ha h]

/-- `homogeneousProj` is a left inverse to the submodule inclusion `(ℳ η).subtype`. -/
@[simp]
theorem homogeneousProj_comp_subtype (η : ι) :
    (homogeneousProj ℳ η).comp (ℳ η).subtype = LinearMap.id := by
  ext x
  simp [DirectSum.decompose_coe]

/-- Selection of a whole homogeneous piece as an endomorphism of the ambient
module: the `η`-component of the direct-sum decomposition, included back into
`M`. -/
def homogeneousComponent (η : ι) : Module.End R M :=
  (ℳ η).subtype.comp (homogeneousProj ℳ η)

/-- Selecting a piece takes the corresponding component of the decomposition. -/
@[simp]
theorem homogeneousComponent_apply (η : ι) (a : M) :
    homogeneousComponent ℳ η a = (DirectSum.decompose ℳ a η : M) := by
  rw [homogeneousComponent, LinearMap.comp_apply, Submodule.coe_subtype, homogeneousProj_apply]

/-- Every selected output lies in the selected piece. -/
theorem homogeneousComponent_mem (η : ι) (a : M) :
    homogeneousComponent ℳ η a ∈ ℳ η :=
  Subtype.property _

/-- Selection is the identity on its own homogeneous piece. -/
theorem homogeneousComponent_apply_of_mem {η : ι} {a : M} (ha : a ∈ ℳ η) :
    homogeneousComponent ℳ η a = a := by
  rw [homogeneousComponent_apply, DirectSum.decompose_of_mem_same ℳ ha]

/-- A homogeneous input of a different piece is annihilated by the selection. -/
theorem homogeneousComponent_apply_of_mem_ne {i η : ι} {a : M} (ha : a ∈ ℳ i)
    (h : i ≠ η) :
    homogeneousComponent ℳ η a = 0 := by
  rw [homogeneousComponent_apply, DirectSum.decompose_of_mem_ne ℳ ha h]

/-- Piece selection is a projection: selecting the same piece twice has no
further effect. -/
@[simp]
theorem homogeneousComponent_idem (η : ι) :
    (homogeneousComponent ℳ η).comp (homogeneousComponent ℳ η) =
      homogeneousComponent ℳ η := by
  ext a
  simp only [LinearMap.comp_apply, homogeneousComponent_apply]
  exact DirectSum.decompose_of_mem_same ℳ (Subtype.property (DirectSum.decompose ℳ a η))

/-- Selections of two different pieces are orthogonal. -/
@[simp]
theorem homogeneousComponent_comp_of_ne {i j : ι} (h : i ≠ j) :
    (homogeneousComponent ℳ i).comp (homogeneousComponent ℳ j) = 0 := by
  ext a
  simp only [LinearMap.comp_apply, LinearMap.zero_apply]
  exact homogeneousComponent_apply_of_mem_ne ℳ (homogeneousComponent_mem ℳ j a) (Ne.symm h)

end TauCeti
