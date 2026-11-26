/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.DeRham.Map
public import TauCeti.Geometry.Manifold.DeRham.PoincarePairing.Basic

/-!
# Integrals of pullbacks of forms that are exact near the image

Let `M` be a compact oriented boundaryless manifold of dimension `n` and `f : M → N` a smooth map.
Stokes' theorem on `M` says that an exact top form integrates to zero
(`TauCeti.integralTopForm_eq_zero_of_mem_exactForms`), and pullback preserves exactness. So

`∫_M f^*φ = 0`

for every exact `n`-form `φ` on `N` (`TauCeti.integralTopForm_mpullback_eq_zero_of_mem_exactForms`).
Only the restriction of `φ` to a neighbourhood of the image matters: if `f` maps `M` into an open
subset `U` of `N` on which `φ` is exact, that is, if the restriction `φ|_U` is the exterior
derivative of a smooth form on `U`, then again `∫_M f^*φ = 0`
(`TauCeti.integralTopForm_mpullback_eq_zero_of_range_subset`). The primitive on `U` need not
extend to `N`. For a closed form `φ`, this applies whenever the de Rham cohomology of `U` vanishes
in the degree of `φ`
(`TauCeti.integralTopForm_mpullback_eq_zero_of_subsingleton_deRhamCohomology`), for instance when
`U` is smoothly contractible
(`TauCeti.subsingleton_deRhamCohomology_of_contraction`).

This is how the symplectic area of a closed curve lying in a region where the symplectic form is
exact is seen to vanish.

## Main results

* `TauCeti.integralTopForm_mpullback_eq_zero_of_mem_exactForms`: a closed manifold pulls an exact
  top form back to a form of integral zero.
* `TauCeti.integralTopForm_mpullback_eq_zero_of_range_subset`: the same when the form is only exact
  on an open set containing the image.
* `TauCeti.integralTopForm_mpullback_eq_zero_of_subsingleton_deRhamCohomology`: the same for a
  closed form and an open set containing the image whose de Rham cohomology vanishes in the
  degree of the form.

## References

* John M. Lee, *Introduction to Smooth Manifolds*, 2nd ed., Graduate Texts in Mathematics 218,
  Springer, 2013, Chapter 16 (Stokes' theorem) and Chapter 17 (de Rham cohomology).
-/

public section

noncomputable section

open TopologicalSpace
open scoped ContDiff Manifold

namespace TauCeti

variable {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} {M : Type*} [TopologicalSpace M]
  [ChartedSpace H M] [IsManifold I ∞ M] [BoundarylessManifold I M] [T2Space M]
  [SigmaCompactSpace M] [CompactSpace M]
  {E' H' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E'] [TopologicalSpace H']
  {I' : ModelWithCorners ℝ E' H'} {N : Type*} [TopologicalSpace N] [ChartedSpace H' N]
  [IsManifold I' ∞ N] {n : ℕ}

/-- **Stokes' theorem for pullbacks of exact forms.** A smooth map from a compact oriented
boundaryless `n`-manifold pulls every exact `n`-form back to a form of integral zero:
`∫_M f^*φ = 0`. -/
theorem integralTopForm_mpullback_eq_zero_of_mem_exactForms
    (o : Manifold.Orientation I M (Fin n)) {f : M → N} (hf : ContMDiff I I' ∞ f)
    {φ : SmoothForm I' N ℝ n} (hφ : φ ∈ exactForms I' N n) :
    integralTopForm o (mpullback I I' f φ.val) = 0 := by
  have h := closedForms.mpullback_mem_exactForms f hf n ⟨φ, exactForms_le_closedForms I' n hφ⟩ hφ
  rw [closedForms.coe_mpullback] at h
  simpa using integralTopForm_eq_zero_of_mem_exactForms o h

/-- **Stokes' theorem for forms that are exact near the image.** Let `f` map a compact oriented
boundaryless `n`-manifold `M` into an open subset `U` of `N`, and let the restriction of the
`n`-form `φ` to `U` be exact. Then `∫_M f^*φ = 0`. The primitive of `φ` on `U` need not extend to
`N`. -/
theorem integralTopForm_mpullback_eq_zero_of_range_subset
    (o : Manifold.Orientation I M (Fin n)) {f : M → N} (hf : ContMDiff I I' ∞ f) (U : Opens N)
    (hfU : Set.range f ⊆ U) {φ : SmoothForm I' N ℝ n}
    (hφ : SmoothForm.mpullback ((↑) : U → N) contMDiff_subtypeVal φ ∈ exactForms I' U n) :
    integralTopForm o (mpullback I I' f φ.val) = 0 := by
  -- `f` is its corestriction `g` to `U` followed by the inclusion of `U`.
  set g : M → U := fun x ↦ ⟨f x, hfU ⟨x, rfl⟩⟩
  have hg : ContMDiff I I' ∞ g := fun x ↦ (ContMDiffAt.subtypeVal_comp_iff U g x).1 (hf x)
  have hfg : f = (↑) ∘ g := rfl
  rw [hfg, mpullback_comp ((hg.of_le (by simp)).mdifferentiable one_ne_zero)
    ((contMDiff_subtypeVal (n := 1)).mdifferentiable one_ne_zero),
    ← SmoothForm.coe_mpullback _ contMDiff_subtypeVal]
  exact integralTopForm_mpullback_eq_zero_of_mem_exactForms o hg hφ

/-- **Stokes' theorem for closed forms near an acyclic image.** Let `f` map a compact oriented
boundaryless `n`-manifold `M` into an open subset `U` of `N` with `H^n_dR(U) = 0`, such as a
smoothly contractible one when `n ≠ 0`. Then every closed `n`-form `φ` on `N` satisfies
`∫_M f^*φ = 0`. -/
theorem integralTopForm_mpullback_eq_zero_of_subsingleton_deRhamCohomology
    (o : Manifold.Orientation I M (Fin n)) {f : M → N} (hf : ContMDiff I I' ∞ f) (U : Opens N)
    [Subsingleton (deRhamCohomology I' U n)] (hfU : Set.range f ⊆ U) {φ : SmoothForm I' N ℝ n}
    (hφ : φ ∈ closedForms I' N n) :
    integralTopForm o (mpullback I I' f φ.val) = 0 := by
  refine integralTopForm_mpullback_eq_zero_of_range_subset o hf U hfU ?_
  have h := (deRhamCohomology.mk_eq_zero_iff I' n
    (closedForms.mpullback ((↑) : U → N) contMDiff_subtypeVal n ⟨φ, hφ⟩)).1
    (Subsingleton.elim _ _)
  rwa [closedForms.coe_mpullback] at h

end TauCeti
