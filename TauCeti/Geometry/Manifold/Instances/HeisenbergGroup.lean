/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.Algebra.Group.Heisenberg
public import Mathlib.Geometry.Manifold.Algebra.LieGroup
public import TauCeti.Geometry.Manifold.PullbackGroupoid

/-!
# The canonical Heisenberg manifold and Lie group

The Heisenberg carrier has global coordinates in `R × R × R`. Over a normed vector space,
the coordinate homeomorphism is a diffeomorphism at every differentiability order. Over a normed
algebra, the canonical Heisenberg group is analytic, with its usual polynomial multiplication
and inversion. For finite-dimensional real coefficients, this structure supplies the Lie algebra
and Lie-group exponential. The global chart reduces smoothness of group-valued maps to
smoothness of their three coordinate functions.

## Main declarations

* `TauCeti.HeisenbergGroup.instChartedSpace`, `chartAt_eq`: the full coordinate charts.
* `TauCeti.HeisenbergGroup.instIsManifold`: the coordinate manifold.
* `TauCeti.HeisenbergGroup.diffeomorphProd`, `diffeomorphProd_apply`,
  `diffeomorphProd_symm_apply`, `diffeomorphProd_toHomeomorph`, `diffeomorphProd_toEquiv`:
  the coordinate diffeomorphism and its computation rules.
* `TauCeti.HeisenbergGroup.contMDiffWithinAt_iff`, `contMDiffAt_iff`, `contMDiffOn_iff`,
  `contMDiff_iff`: local and global coordinate criteria for smooth maps.
* `TauCeti.HeisenbergGroup.contMDiff_x`, `contMDiff_y`, `contMDiff_z`: smooth coordinates.
* `TauCeti.HeisenbergGroup.instLieGroup`: the analytic group structure.

## References

* B. C. Hall, *Lie Groups, Lie Algebras, and Representations*, second edition, GTM 222
  (2015), Section 1.2.6, equation (1.13), for the real Heisenberg group.
* `Homeomorph.pullbackChartedSpace` and `Homeomorph.pullbackDiffeomorph` supply the
  coordinate manifold and its smooth identification with the product.
-/

public noncomputable section

open scoped ContDiff Manifold
open Manifold

universe u v

namespace TauCeti.HeisenbergGroup

/-- The global coordinate chart on the canonical Heisenberg carrier. -/
@[instance_reducible]
instance instChartedSpace (R : Type v) [TopologicalSpace R] :
    ChartedSpace (R × R × R) (HeisenbergGroup R) :=
  homeomorphProd.pullbackChartedSpace

/-- Every Heisenberg chart is the full coordinate homeomorphism. -/
@[simp high, mfld_simps]
theorem chartAt_eq {R : Type v} [TopologicalSpace R] (g : HeisenbergGroup R) :
    chartAt (R × R × R) g = homeomorphProd.toOpenPartialHomeomorph := by
  rw [Homeomorph.pullbackChartedSpace_chartAt]
  ext x <;> simp

variable {𝕜 : Type u} [NontriviallyNormedField 𝕜]

section Manifold

variable {R : Type v} [NormedAddCommGroup R] [NormedSpace 𝕜 R]

/-- The coordinate manifold on the canonical Heisenberg carrier. -/
instance instIsManifold {n : ℕ∞ω} :
    IsManifold 𝓘(𝕜, R × R × R) n (HeisenbergGroup R) :=
  homeomorphProd.pullback_isManifold _ n

variable (𝕜) in
/-- The coordinate diffeomorphism of the canonical Heisenberg carrier. -/
def diffeomorphProd (n : ℕ∞ω) :
    Diffeomorph 𝓘(𝕜, R × R × R) 𝓘(𝕜, R × R × R) (HeisenbergGroup R) (R × R × R) n :=
  homeomorphProd.pullbackDiffeomorph _ n

/-- The coordinate diffeomorphism sends an element to its three coordinates. -/
@[simp]
theorem diffeomorphProd_apply {n : ℕ∞ω} (g : HeisenbergGroup R) :
    diffeomorphProd (𝕜 := 𝕜) (n := n) g = (g.x, g.y, g.z) := by
  simp only [diffeomorphProd, Homeomorph.coe_pullbackDiffeomorph, homeomorphProd_apply]

/-- The inverse coordinate diffeomorphism forms an element from its coordinates. -/
@[simp]
theorem diffeomorphProd_symm_apply {n : ℕ∞ω} (a : R × R × R) :
    (diffeomorphProd (𝕜 := 𝕜) (n := n)).symm a = ⟨a.1, a.2.1, a.2.2⟩ := by
  simp only [diffeomorphProd, Homeomorph.coe_pullbackDiffeomorph_symm, homeomorphProd_symm_apply]

/-- The coordinate diffeomorphism has the original coordinate homeomorphism. -/
@[simp]
theorem diffeomorphProd_toHomeomorph {n : ℕ∞ω} :
    (diffeomorphProd 𝕜 n (R := R)).toHomeomorph = homeomorphProd := by
  apply Homeomorph.ext
  intro g
  simp only [Diffeomorph.coe_toHomeomorph, diffeomorphProd_apply, homeomorphProd_apply]

/-- The coordinate diffeomorphism has the original coordinate equivalence. -/
@[simp]
theorem diffeomorphProd_toEquiv {n : ℕ∞ω} :
    (diffeomorphProd 𝕜 n (R := R)).toEquiv = equivProd := by
  apply Equiv.ext
  intro g
  simp only [Diffeomorph.coe_toEquiv, diffeomorphProd_apply, equivProd_apply]

section CoordinateCriterion

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  {n : ℕ∞ω} {f : M → HeisenbergGroup R}

/-- A map into the Heisenberg manifold is smooth within a set at a point exactly when
its coordinates are. -/
theorem contMDiffWithinAt_iff {s : Set M} {a : M} :
    ContMDiffWithinAt I 𝓘(𝕜, R × R × R) n f s a ↔
      ContMDiffWithinAt I 𝓘(𝕜, R) n (fun x ↦ (f x).x) s a ∧
        ContMDiffWithinAt I 𝓘(𝕜, R) n (fun x ↦ (f x).y) s a ∧
          ContMDiffWithinAt I 𝓘(𝕜, R) n (fun x ↦ (f x).z) s a := by
  rw [← (diffeomorphProd 𝕜 n (R := R)).contMDiffWithinAt_diffeomorph_comp_iff le_rfl]
  simp only [Function.comp_def, diffeomorphProd_apply, contMDiffWithinAt_prod_module_iff]

/-- A map into the Heisenberg manifold is smooth at a point exactly when its coordinates are. -/
theorem contMDiffAt_iff {a : M} :
    ContMDiffAt I 𝓘(𝕜, R × R × R) n f a ↔
      ContMDiffAt I 𝓘(𝕜, R) n (fun x ↦ (f x).x) a ∧
        ContMDiffAt I 𝓘(𝕜, R) n (fun x ↦ (f x).y) a ∧
          ContMDiffAt I 𝓘(𝕜, R) n (fun x ↦ (f x).z) a := by
  rw [← (diffeomorphProd 𝕜 n (R := R)).contMDiffAt_diffeomorph_comp_iff le_rfl]
  simp only [Function.comp_def, diffeomorphProd_apply, contMDiffAt_prod_module_iff]

/-- A map into the Heisenberg manifold is smooth on a set exactly when its coordinates are. -/
theorem contMDiffOn_iff {s : Set M} :
    ContMDiffOn I 𝓘(𝕜, R × R × R) n f s ↔
      ContMDiffOn I 𝓘(𝕜, R) n (fun x ↦ (f x).x) s ∧
        ContMDiffOn I 𝓘(𝕜, R) n (fun x ↦ (f x).y) s ∧
          ContMDiffOn I 𝓘(𝕜, R) n (fun x ↦ (f x).z) s := by
  rw [← (diffeomorphProd 𝕜 n (R := R)).contMDiffOn_diffeomorph_comp_iff le_rfl]
  simp only [Function.comp_def, diffeomorphProd_apply, contMDiffOn_prod_module_iff]

/-- A map into the Heisenberg manifold is smooth globally exactly when its coordinates are. -/
theorem contMDiff_iff :
    ContMDiff I 𝓘(𝕜, R × R × R) n f ↔
      ContMDiff I 𝓘(𝕜, R) n (fun x ↦ (f x).x) ∧
        ContMDiff I 𝓘(𝕜, R) n (fun x ↦ (f x).y) ∧
          ContMDiff I 𝓘(𝕜, R) n (fun x ↦ (f x).z) := by
  rw [← (diffeomorphProd 𝕜 n (R := R)).contMDiff_diffeomorph_comp_iff le_rfl]
  simp only [Function.comp_def, diffeomorphProd_apply, contMDiff_prod_module_iff]

end CoordinateCriterion

/-- The first Heisenberg coordinate is smooth. -/
theorem contMDiff_x {n : ℕ∞ω} :
    ContMDiff 𝓘(𝕜, R × R × R) 𝓘(𝕜, R) n (HeisenbergGroup.x : HeisenbergGroup R → R) :=
  (contMDiff_iff (f := id).mp contMDiff_id).1

/-- The second Heisenberg coordinate is smooth. -/
theorem contMDiff_y {n : ℕ∞ω} :
    ContMDiff 𝓘(𝕜, R × R × R) 𝓘(𝕜, R) n (HeisenbergGroup.y : HeisenbergGroup R → R) :=
  (contMDiff_iff (f := id).mp contMDiff_id).2.1

/-- The central Heisenberg coordinate is smooth. -/
theorem contMDiff_z {n : ℕ∞ω} :
    ContMDiff 𝓘(𝕜, R × R × R) 𝓘(𝕜, R) n (HeisenbergGroup.z : HeisenbergGroup R → R) :=
  (contMDiff_iff (f := id).mp contMDiff_id).2.2

end Manifold

section Group

variable {R : Type v} [NormedRing R] [NormedAlgebra 𝕜 R]

/-- The canonical Heisenberg group over a normed algebra is a Lie group at every regularity. -/
instance instLieGroup {n : ℕ∞ω} :
    LieGroup 𝓘(𝕜, R × R × R) n (HeisenbergGroup R) := by
  have hm : ContMDiff 𝓘(𝕜, R × R) 𝓘(𝕜, R) n (fun a : R × R => a.1 * a.2) :=
    contDiff_mul.contMDiff
  refine { contMDiff_mul := contMDiff_iff.mpr ?_, contMDiff_inv := contMDiff_iff.mpr ?_ }
  · have hf : ContMDiff ((𝓘(𝕜, R × R × R)).prod 𝓘(𝕜, R × R × R))
        𝓘(𝕜, R × R × R) n (Prod.fst : HeisenbergGroup R × HeisenbergGroup R → _) :=
      contMDiff_fst
    have hg : ContMDiff ((𝓘(𝕜, R × R × R)).prod 𝓘(𝕜, R × R × R))
        𝓘(𝕜, R × R × R) n (Prod.snd : HeisenbergGroup R × HeisenbergGroup R → _) :=
      contMDiff_snd
    have hx₁ := (contMDiff_x (𝕜 := 𝕜) (R := R) (n := n)).comp hf
    have hx₂ := (contMDiff_x (𝕜 := 𝕜) (R := R) (n := n)).comp hg
    have hy₁ := (contMDiff_y (𝕜 := 𝕜) (R := R) (n := n)).comp hf
    have hy₂ := (contMDiff_y (𝕜 := 𝕜) (R := R) (n := n)).comp hg
    have hz₁ := (contMDiff_z (𝕜 := 𝕜) (R := R) (n := n)).comp hf
    have hz₂ := (contMDiff_z (𝕜 := 𝕜) (R := R) (n := n)).comp hg
    refine ⟨?_, ?_, ?_⟩
    · simpa only [HeisenbergGroup.mul_x, Function.comp_def, Pi.add_def] using hx₁.add hx₂
    · simpa only [HeisenbergGroup.mul_y, Function.comp_def, Pi.add_def] using hy₁.add hy₂
    · simpa only [HeisenbergGroup.mul_z, Function.comp_def, Pi.add_def] using
        (hz₁.add hz₂).add (hm.comp (hx₁.prodMk_space hy₂))
  · refine ⟨?_, ?_, ?_⟩
    · simpa only [HeisenbergGroup.inv_x] using
        (contMDiff_x (𝕜 := 𝕜) (R := R) (n := n)).neg
    · simpa only [HeisenbergGroup.inv_y] using
        (contMDiff_y (𝕜 := 𝕜) (R := R) (n := n)).neg
    · simpa only [HeisenbergGroup.inv_z, Function.comp_def, Pi.add_def, Pi.neg_def] using
        (contMDiff_z (𝕜 := 𝕜) (R := R) (n := n)).neg.add
          (hm.comp ((contMDiff_x (𝕜 := 𝕜) (R := R) (n := n)).prodMk_space
            (contMDiff_y (𝕜 := 𝕜) (R := R) (n := n))))

end Group
end TauCeti.HeisenbergGroup
