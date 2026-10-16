/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.RealAlgebraic.Stack.Delineation
public import TauCeti.Analysis.Polynomial.MultipleRoots.Submanifold
public import TauCeti.Analysis.Analytic.Submanifold.Graph

/-!
# Analytic root sections of delineations

A delineation of a polynomial family with intrinsically analytic coefficients over an analytic
submanifold has intrinsically analytic root functions. Multiplicities may be greater than one:
constant positive multiplicity, already part of a delineation, suffices. Consequently every
ambient section of the stack is an analytic submanifold of the same dimension as the base.

The analyticity statement is expressed using any ambient function agreeing with the root
function on the base. This matches `AnalyticOnSubmanifold`, which depends only on values on the
submanifold, and imposes no regularity on the function away from the base.

## References

S. McCallum, *An improved projection operation for cylindrical algebraic decomposition*,
Springer (1998), 242–268 (analytic delineability and lifting).
-/

public section

open Filter Function Polynomial Set Topology

namespace TauCeti

/-- An ambient section whose defining function is analytic on the base is an analytic
submanifold of the same dimension. Only the values of the extension on the base matter. -/
theorem isAnalyticSubmanifold_image_cylinder_sectionSet {𝕜 : Type*}
    [NontriviallyNormedField 𝕜] {n d k : ℕ}
    {S : Set (Fin n → 𝕜)} {θ : Fin k → S → 𝕜} (hS : IsAnalyticSubmanifold d S)
    (i : Fin k) {r : (Fin n → 𝕜) → 𝕜} (hr : ∀ x : S, r x = θ i x)
    (ha : AnalyticOnSubmanifold (𝕜 := 𝕜) d r S) :
    IsAnalyticSubmanifold d (cylinder S '' sectionSet θ i) := by
  convert hS.graph ha using 1
  ext v
  simp only [mem_image_cylinder, mem_sectionSet, mem_ofPred_eq]
  constructor
  · rintro ⟨hv, heq⟩
    exact ⟨hv, (heq.symm.trans (hr ⟨Fin.tail v, hv⟩).symm)⟩
  · rintro ⟨hv, heq⟩
    exact ⟨hv, (heq.trans (hr ⟨Fin.tail v, hv⟩)).symm⟩

namespace Delineation

variable {n d : ℕ} {S : Set (Fin n → ℝ)} {ι : Type*}
  {P : ι → (Fin n → ℝ) → ℝ[X]} (D : Delineation fun k (x : S) ↦ P k x)

/-- The root functions of a delineation with intrinsically analytic coefficients over an
analytic submanifold are intrinsically analytic, including roots of multiplicity greater than
one. Any ambient extension of a root function gives the same conclusion. -/
theorem analyticOnSubmanifold_root (hS : IsAnalyticSubmanifold d S)
    (hcoeff : ∀ k j, AnalyticOnSubmanifold d (fun x ↦ (P k x).coeff j) S)
    (i : Fin D.count) {r : (Fin n → ℝ) → ℝ} (hr : ∀ x : S, r x = D.root i x) :
    AnalyticOnSubmanifold d r S := by
  obtain ⟨k, hk⟩ := D.exists_multiplicity_pos i
  apply hS.analyticOnSubmanifold_of_rootMultiplicity_eq (hcoeff k) ?_ ?_ ?_
  · intro x hx
    refine ⟨(P k x).natDegree, ?_⟩
    filter_upwards [self_mem_nhdsWithin] with y hy
    exact (D.natDegree_eq k ⟨y, hy⟩ ⟨x, hx⟩).le
  · rw [continuousOn_iff_continuous_domRestrict]
    exact (D.continuous_root i).congr fun x ↦ (hr x).symm
  · intro x _
    refine ⟨D.multiplicity k i, hk, ?_⟩
    filter_upwards [self_mem_nhdsWithin] with y hy
    rw [hr ⟨y, hy⟩]
    exact D.rootMultiplicity_root k i ⟨y, hy⟩

/-- Every ambient section of a delineation with intrinsically analytic coefficients is an
analytic submanifold with the dimension of its base. -/
theorem isAnalyticSubmanifold_sectionSet (hS : IsAnalyticSubmanifold d S)
    (hcoeff : ∀ k j, AnalyticOnSubmanifold d (fun x ↦ (P k x).coeff j) S)
    (i : Fin D.count) :
    IsAnalyticSubmanifold d (cylinder S '' sectionSet D.root i) := by
  let r := Function.extend Subtype.val (D.root i) (fun _ ↦ 0)
  have hr (x : S) : r x = D.root i x := Subtype.val_injective.extend_apply _ _ x
  exact isAnalyticSubmanifold_image_cylinder_sectionSet hS i hr
    (D.analyticOnSubmanifold_root hS hcoeff i hr)

end Delineation
end TauCeti
