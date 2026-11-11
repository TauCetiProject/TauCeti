/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.Algebra.Group.Heisenberg
public import Mathlib.Geometry.Manifold.Algebra.LieGroup
public import Mathlib.Geometry.Manifold.Diffeomorph

/-!
# The canonical Heisenberg manifold and Lie group

The Heisenberg carrier has global coordinates in `R × R × R`. Over a normed vector space,
the coordinate homeomorphism is a diffeomorphism at every differentiability order. Over a normed
algebra, the canonical Heisenberg group is analytic, with its usual polynomial multiplication
and inversion. Over the real numbers, this structure supplies the native Lie algebra and
exponential map. The global chart reduces smoothness of group-valued maps to smoothness of
their three coordinate functions.

## Main declarations

* `TauCeti.HeisenbergGroup.instChartedSpace`, `chartAt_eq`: the global coordinate chart.
* `TauCeti.HeisenbergGroup.instIsManifold`: the coordinate manifold.
* `TauCeti.HeisenbergGroup.diffeomorphProd`: the coordinate diffeomorphism.
* `TauCeti.HeisenbergGroup.contMDiff_iff`: coordinate criterion for smooth maps.
* `TauCeti.HeisenbergGroup.contMDiff_x`, `contMDiff_y`, `contMDiff_z`: smooth coordinates.
* `TauCeti.HeisenbergGroup.instLieGroup`: the analytic group structure.

## References

* B. C. Hall, *Lie Groups, Lie Algebras, and Representations*, second edition, GTM 222
  (2015), Section 1.2.6, equation (1.13), for the real Heisenberg group.
* Mathlib, `Geometry/Manifold/ContMDiff/Basic.lean`, for smooth open-embedding charts.
-/

public noncomputable section

open scoped ContDiff Manifold
open Manifold

universe u v

namespace TauCeti.HeisenbergGroup

/-- The global coordinate chart on the canonical Heisenberg carrier. -/
@[instance_reducible]
instance instChartedSpace (R : Type v) [TopologicalSpace R] [Nonempty R] :
    ChartedSpace (R × R × R) (HeisenbergGroup R) :=
  homeomorphProd.isOpenEmbedding.singletonChartedSpace

/-- Every coordinate chart has the coordinate homeomorphism as its underlying map. -/
theorem chartAt_eq {R : Type v} [TopologicalSpace R] [Nonempty R] (g : HeisenbergGroup R) :
    ⇑(chartAt (R × R × R) g) = (homeomorphProd : HeisenbergGroup R → R × R × R) :=
  homeomorphProd.isOpenEmbedding.singletonChartedSpace_chartAt_eq

/-- The coordinate charts are defined on the whole Heisenberg carrier. -/
theorem chartAt_source {R : Type v} [TopologicalSpace R] [Nonempty R] (g : HeisenbergGroup R) :
    (chartAt (R × R × R) g).source = Set.univ := by
  simp

variable {𝕜 : Type u} [NontriviallyNormedField 𝕜]

section Manifold

variable {R : Type v} [NormedAddCommGroup R] [NormedSpace 𝕜 R]

/-- The coordinate manifold on the canonical Heisenberg carrier. -/
instance instIsManifold {n : ℕ∞ω} :
    IsManifold 𝓘(𝕜, R × R × R) n (HeisenbergGroup R) := by
  exact homeomorphProd.isOpenEmbedding.isManifold_singleton

/-- The Heisenberg coordinate map is smooth. -/
theorem contMDiff_homeomorphProd {n : ℕ∞ω} :
    ContMDiff 𝓘(𝕜, R × R × R) 𝓘(𝕜, R × R × R) n
      (homeomorphProd : HeisenbergGroup R → R × R × R) := by
  exact contMDiff_isOpenEmbedding homeomorphProd.isOpenEmbedding

/-- The inverse Heisenberg coordinate map is smooth. -/
theorem contMDiff_homeomorphProd_symm {n : ℕ∞ω} :
    ContMDiff 𝓘(𝕜, R × R × R) 𝓘(𝕜, R × R × R) n
      (homeomorphProd.symm : R × R × R → HeisenbergGroup R) := by
  apply ContMDiff.of_comp_isOpenEmbedding homeomorphProd.isOpenEmbedding
  rw [Homeomorph.self_comp_symm]
  exact contMDiff_id

/-- The coordinate diffeomorphism of the canonical Heisenberg carrier. -/
def diffeomorphProd {n : ℕ∞ω} :
    Diffeomorph 𝓘(𝕜, R × R × R) 𝓘(𝕜, R × R × R) (HeisenbergGroup R) (R × R × R) n where
  toEquiv := homeomorphProd.toEquiv
  contMDiff_toFun := contMDiff_homeomorphProd (n := n)
  contMDiff_invFun := contMDiff_homeomorphProd_symm (n := n)

/-- The coordinate diffeomorphism sends an element to its three coordinates. -/
@[simp]
theorem diffeomorphProd_apply {n : ℕ∞ω} (g : HeisenbergGroup R) :
    diffeomorphProd (𝕜 := 𝕜) (n := n) g = (g.x, g.y, g.z) := by
  unfold diffeomorphProd
  -- The diffeomorphism constructor retains the homeomorphism's equivalence and underlying map.
  exact homeomorphProd_apply g

/-- The inverse coordinate diffeomorphism forms an element from its coordinates. -/
@[simp]
theorem diffeomorphProd_symm_apply {n : ℕ∞ω} (a : R × R × R) :
    (diffeomorphProd (𝕜 := 𝕜) (n := n)).symm a = ⟨a.1, a.2.1, a.2.2⟩ := by
  unfold diffeomorphProd
  -- Both inverse coercions use the inverse map of the same coordinate equivalence.
  exact homeomorphProd_symm_apply a

/-- The first Heisenberg coordinate is smooth. -/
theorem contMDiff_x {n : ℕ∞ω} :
    ContMDiff 𝓘(𝕜, R × R × R) 𝓘(𝕜, R) n (HeisenbergGroup.x : HeisenbergGroup R → R) := by
  have hp : ContMDiff 𝓘(𝕜, R × R × R) 𝓘(𝕜, R) n (fun a : R × R × R => a.1) :=
    contDiff_fst.contMDiff
  simpa only [Function.comp_def, homeomorphProd_apply] using
    hp.comp (contMDiff_homeomorphProd (𝕜 := 𝕜) (R := R) (n := n))

/-- The second Heisenberg coordinate is smooth. -/
theorem contMDiff_y {n : ℕ∞ω} :
    ContMDiff 𝓘(𝕜, R × R × R) 𝓘(𝕜, R) n (HeisenbergGroup.y : HeisenbergGroup R → R) := by
  have hp : ContMDiff 𝓘(𝕜, R × R × R) 𝓘(𝕜, R) n (fun a : R × R × R => a.2.1) :=
    (contDiff_fst.comp contDiff_snd).contMDiff
  simpa only [Function.comp_def, homeomorphProd_apply] using
    hp.comp (contMDiff_homeomorphProd (𝕜 := 𝕜) (R := R) (n := n))

/-- The central Heisenberg coordinate is smooth. -/
theorem contMDiff_z {n : ℕ∞ω} :
    ContMDiff 𝓘(𝕜, R × R × R) 𝓘(𝕜, R) n (HeisenbergGroup.z : HeisenbergGroup R → R) := by
  have hp : ContMDiff 𝓘(𝕜, R × R × R) 𝓘(𝕜, R) n (fun a : R × R × R => a.2.2) :=
    (contDiff_snd.comp contDiff_snd).contMDiff
  simpa only [Function.comp_def, homeomorphProd_apply] using
    hp.comp (contMDiff_homeomorphProd (𝕜 := 𝕜) (R := R) (n := n))

/-- A map into the Heisenberg manifold is smooth exactly when its three coordinates are. -/
theorem contMDiff_iff {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    {n : ℕ∞ω} {f : M → HeisenbergGroup R} :
    ContMDiff I 𝓘(𝕜, R × R × R) n f ↔
      ContMDiff I 𝓘(𝕜, R) n (fun a ↦ (f a).x) ∧
        ContMDiff I 𝓘(𝕜, R) n (fun a ↦ (f a).y) ∧
          ContMDiff I 𝓘(𝕜, R) n (fun a ↦ (f a).z) := by
  refine ⟨fun hf ↦ ⟨contMDiff_x.comp hf, contMDiff_y.comp hf, contMDiff_z.comp hf⟩, ?_⟩
  rintro ⟨hx, hy, hz⟩
  apply ContMDiff.of_comp_isOpenEmbedding homeomorphProd.isOpenEmbedding
  simpa only [Function.comp_def, homeomorphProd_apply] using
    hx.prodMk_space (hy.prodMk_space hz)

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
