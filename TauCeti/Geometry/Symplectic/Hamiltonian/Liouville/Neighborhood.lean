/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.RegularValue
public import TauCeti.Geometry.Symplectic.Hamiltonian.Complete
public import TauCeti.Geometry.Symplectic.Manifold.Opens
import TauCeti.Topology.ConnectedComponents

/-!
# Commuting Hamiltonian flows are complete near a compact component of a level

Let `σ` be a nondegenerate two-form on a finite-dimensional boundaryless Hausdorff manifold `M`,
with the conventions `ι_{X_f} σ = df` and `{f, g} = σ(X_f, X_g) = df(X_g)`, and let
`F : M → (ι → ℝ)` be a family of pairwise Poisson-commuting `C²` functions. Their Hamiltonian
vector fields need not be complete on `M`. This file shows that they become complete after
restriction to a suitable open neighbourhood of any compact connected component `L` of a level
`F⁻¹(c₀)`.

Indeed `L` has an open neighbourhood `W` meeting every level of `F` in a compact set
(`Continuous.exists_isOpen_forall_isCompact_inter_preimage_singleton`). On the open submanifold
`W`, with the restriction of `σ`, the restricted functions still Poisson-commute
(`TauCeti.SmoothTwoForm.IsNondegenerate.poissonBracket_comp_subtype_val`), so each of them is a
first integral of the others. Every maximal integral curve of their Hamiltonian vector fields
therefore stays in one compact level of `F` in `W`, and these vector fields are complete
(`TauCeti.SmoothTwoForm.IsNondegenerate.exists_opens_isCompleteVectorField_hamiltonianVectorField`).
Since `L ⊆ W`, the set `L` is also the connected component of its level in `W`
(`TauCeti.image_val_connectedComponentIn_preimage_val`).

This is how the theorems about the action of complete commuting Hamiltonian flows, such as the
Liouville–Arnold theorem near a compact regular component of a level, hold with no global
completeness hypothesis: they are applied on `W` and transported along the inclusion `W → M`.

## Main results

In the namespace `TauCeti.SmoothTwoForm.IsNondegenerate`:

* `poissonBracket_comp_subtype_val`: restriction to an open submanifold preserves Poisson
  brackets.
* `exists_opens_isCompleteVectorField_hamiltonianVectorField`: a compact component of a level of
  a family of commuting functions has an open neighbourhood with compact levels on which their
  Hamiltonian vector fields are complete.

## References

* V. I. Arnold, *Mathematical Methods of Classical Mechanics*, 2nd ed., Graduate Texts in
  Mathematics 60, Springer, 1989, Section 49.
-/

public section

open Set TopologicalSpace
open scoped ContDiff Manifold

namespace TauCeti

namespace SmoothTwoForm

namespace IsNondegenerate

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] {σ : SmoothTwoForm I M} (hσ : σ.IsNondegenerate)
include hσ

/-- **Poisson brackets restrict to open submanifolds.** For a nondegenerate form `σ` and an open
set `U`, the Poisson bracket of the restrictions of `f` and `g` to `U`, for the restriction of `σ`
to `U`, is the restriction of their Poisson bracket. -/
theorem poissonBracket_comp_subtype_val (U : Opens M) {f g : M → ℝ} {x : U}
    (hf : MDifferentiableAt I 𝓘(ℝ) f x) (hg : MDifferentiableAt I 𝓘(ℝ) g x) :
    SmoothTwoForm.poissonBracket
        (SmoothForm.mpullback (Subtype.val : U → M) contMDiff_subtype_val σ)
        (f ∘ Subtype.val) (g ∘ Subtype.val) x =
      σ.poissonBracket f g x :=
  (hσ.mpullback_subtype_val U).poissonBracket_comp hσ contMDiff_subtype_val rfl
    (isRegularPoint_iff.1 (isRegularPoint_subtype_val x)) hf hg

/-- **Commuting Hamiltonian flows are complete near a compact component of a level.** Let `F` be
a family of pairwise Poisson-commuting `C²` functions for a nondegenerate form `σ` on a
finite-dimensional boundaryless Hausdorff manifold, and let the connected component of `x` in its
level `F⁻¹(F x)` be compact. Then this component lies in an open set `W` which meets every level
of `F` in a compact set. On the open submanifold `W`, with the restriction of `σ`, the restrictions
of the functions `F_i` still Poisson-commute, and their Hamiltonian vector fields are complete. -/
theorem exists_opens_isCompleteVectorField_hamiltonianVectorField [T2Space M]
    [BoundarylessManifold I M] {ι : Type*} [Fintype ι] {F : M → ι → ℝ}
    (hF : ContMDiff I 𝓘(ℝ, ι → ℝ) 2 F) (hcomm : ∀ i j x, σ.poissonBracket (F · i) (F · j) x = 0)
    {x : M} (hK : IsCompact (connectedComponentIn (F ⁻¹' {F x}) x)) :
    ∃ W : Opens M, connectedComponentIn (F ⁻¹' {F x}) x ⊆ W ∧
      (∀ c, IsCompact ((fun y : W ↦ F y) ⁻¹' {c})) ∧
      (∀ i j y, SmoothTwoForm.poissonBracket
        (SmoothForm.mpullback (Subtype.val : W → M) contMDiff_subtype_val σ)
        (fun y : W ↦ F y i) (fun y : W ↦ F y j) y = 0) ∧
      ∀ i, IsCompleteVectorField (SmoothTwoForm.hamiltonianVectorField
        (SmoothForm.mpullback (Subtype.val : W → M) contMDiff_subtype_val σ)
        fun y : W ↦ F y i) := by
  have := Manifold.locallyCompact_of_finiteDimensional (M := M) I
  obtain ⟨W, hWo, hLW, hWc⟩ :=
    hF.continuous.exists_isOpen_forall_isCompact_inter_preimage_singleton hK
  set U : Opens M := ⟨W, hWo⟩
  have hFi (j : ι) : ContMDiff I 𝓘(ℝ) 2 (F · j) := contMDiff_pi_module_iff.1 hF j
  -- the levels of `F` in `U` are the compact sets `W ∩ F⁻¹(c)`
  have hlev (c : ι → ℝ) : IsCompact ((fun y : U ↦ F y) ⁻¹' {c}) := by
    rw [Subtype.isCompact_iff]
    convert hWc c using 1
    ext y
    exact ⟨fun ⟨z, hz, hzy⟩ ↦ hzy ▸ ⟨z.2, hz⟩, fun ⟨hyW, hy⟩ ↦ ⟨⟨y, hyW⟩, hy, rfl⟩⟩
  have hcommU (i j : ι) (y : U) := (hσ.poissonBracket_comp_subtype_val U
    ((hFi i).mdifferentiable (by simp) y) ((hFi j).mdifferentiable (by simp) y)).trans
    (hcomm i j y)
  refine ⟨U, hLW, hlev, hcommU, fun i ↦ ?_⟩
  have hσU := hσ.mpullback_subtype_val U
  -- each restricted `F_j` is a first integral of the restricted `F_i`
  exact hσU.isCompleteVectorField_hamiltonianVectorField_of_isCompact_preimage_singleton
    ((hFi i).comp contMDiff_subtype_val) hlev (fun j ↦ isFirstIntegral_iff.2 (hcommU j i))
    fun j ↦ ((hFi j).comp contMDiff_subtype_val).mdifferentiable (by simp)

end IsNondegenerate

end SmoothTwoForm

end TauCeti
