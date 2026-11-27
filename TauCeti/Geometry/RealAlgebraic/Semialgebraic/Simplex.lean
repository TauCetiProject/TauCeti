/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Convex.Intrinsic
public import Mathlib.LinearAlgebra.AffineSpace.Independent
public import TauCeti.Analysis.Convex.StdSimplex.Boundary
public import TauCeti.Geometry.RealAlgebraic.Semialgebraic.Basic
import Mathlib.LinearAlgebra.AffineSpace.FiniteDimensional
import TauCeti.Analysis.Convex.OpenSimplex
import TauCeti.Analysis.Normed.Affine.AddTorsor.Bases
import TauCeti.Geometry.RealAlgebraic.Semialgebraic.Affine
import TauCeti.Geometry.RealAlgebraic.Semialgebraic.Function

/-!
# Semialgebraicity of standard simplices and open simplices

The closed standard simplex in `σ → R` (`Finite σ`) together with its open part
`TauCeti.openStdSimplex R σ`, its open facets `TauCeti.openStdSimplexFacet R i`, and its relative
boundary `TauCeti.stdSimplexBoundary R σ` are semialgebraic.  Over `ℝ`, intersecting the
affine span of an affinely independent finite family (`AffineSubspace.isSemialgebraic`) with the
open half-spaces of its continuous barycentric coordinates (`AffineMap.isSemialgebraic_pos`) shows
that every open simplex `intrinsicInterior ℝ (convexHull ℝ (range p))` is semialgebraic.

## Main results

* `TauCeti.isSemialgebraic_range_toFun_comp_weights`, `TauCeti.isSemialgebraic_openStdSimplex`,
  `TauCeti.isSemialgebraic_openStdSimplexFacet`, `TauCeti.isSemialgebraic_stdSimplexBoundary`: the
  standard simplex and its open part, open facets, and relative boundary are semialgebraic.
* `AffineIndependent.isSemialgebraic_intrinsicInterior_convexHull`: open simplices in `σ → ℝ` are
  semialgebraic.

## References

* J. Bochnak, M. Coste, M.-F. Roy, *Real Algebraic Geometry*, Ergebnisse der Mathematik und ihrer
  Grenzgebiete 36, Springer, 1998, §§2.1, 9.2.
-/

public section

open MvPolynomial Set Convexity

section CommRing

/-! ### Standard simplex coordinate sets -/

namespace TauCeti

variable {σ R : Type*} [CommRing R] [LinearOrder R]

/-- The closed standard simplex of weight vectors in `σ → R` (`Finite σ`) is semialgebraic. -/
theorem isSemialgebraic_range_toFun_comp_weights [Finite σ] :
    IsSemialgebraic (range fun s : StdSimplex R σ => ⇑s.weights) := by
  cases nonempty_fintype σ
  have h : (range fun s : StdSimplex R σ => ⇑s.weights) =
      (⋂ i : σ, {x | 0 ≤ eval x (X i)}) ∩ {x | eval x ((∑ i : σ, X i) - 1) = 0} := by
    ext x
    rw [StdSimplex.mem_range_toFun_comp_weights_iff]
    simp [sub_eq_zero]
  rw [h]
  exact (IsSemialgebraic.iInter fun i => isSemialgebraic_eval_nonneg (X i)).inter
    (isSemialgebraic_eval_eq_zero _)

/-- The open standard simplex `openStdSimplex R σ` in `σ → R` (`Finite σ`) is semialgebraic. -/
theorem isSemialgebraic_openStdSimplex [Finite σ] :
    IsSemialgebraic (openStdSimplex R σ) := by
  have h : openStdSimplex R σ =
      (range fun s : StdSimplex R σ => ⇑s.weights) ∩ ⋂ i : σ, {x | 0 < eval x (X i)} := by
    ext x
    simp
  rw [h]
  exact isSemialgebraic_range_toFun_comp_weights.inter
    (.iInter fun i => isSemialgebraic_eval_pos (X i))

/-- Each open facet `openStdSimplexFacet R i` of the standard simplex in `σ → R` (`Finite σ`) is
semialgebraic. -/
theorem isSemialgebraic_openStdSimplexFacet [Finite σ] (i : σ) :
    IsSemialgebraic (openStdSimplexFacet R i) := by
  have h : openStdSimplexFacet R i =
      (range fun s : StdSimplex R σ => ⇑s.weights) ∩
        ({y | eval y (X i) = 0} ∩ ⋂ j : {j : σ // j ≠ i}, {y | 0 < eval y (X j.val)}) := by
    ext y
    simp
  rw [h]
  exact isSemialgebraic_range_toFun_comp_weights.inter
    ((isSemialgebraic_eval_eq_zero (X i)).inter
      (.iInter fun j => isSemialgebraic_eval_pos (X j.val)))

/-- The relative boundary `stdSimplexBoundary R σ` of the standard simplex in `σ → R` (`Finite σ`)
is semialgebraic. -/
theorem isSemialgebraic_stdSimplexBoundary [Finite σ] :
    IsSemialgebraic (stdSimplexBoundary R σ) := by
  have h : stdSimplexBoundary R σ =
      (range fun s : StdSimplex R σ => ⇑s.weights) ∩ ⋃ i : σ, {x | eval x (X i) = 0} := by
    ext x
    simp
  rw [h]
  exact isSemialgebraic_range_toFun_comp_weights.inter
    (.iUnion fun i => isSemialgebraic_eval_eq_zero (X i))

end TauCeti

end CommRing

/-! ### Open simplices over `ℝ` -/

section Real

variable {σ : Type*} [Finite σ]

/-- **Open simplices are semialgebraic.** The intrinsic interior of the convex hull of a finite
affinely independent family `p : ι → σ → ℝ` (`Finite σ`) is semialgebraic. -/
theorem AffineIndependent.isSemialgebraic_intrinsicInterior_convexHull {ι : Type*} [Finite ι]
    {p : ι → σ → ℝ} (hp : AffineIndependent ℝ p) :
    TauCeti.IsSemialgebraic (intrinsicInterior ℝ (convexHull ℝ (range p))) := by
  cases nonempty_fintype σ
  cases nonempty_fintype ι
  rcases isEmpty_or_nonempty ι with hι | _
  · rw [range_eq_empty]
    simp
  · obtain ⟨f, hf, -, -⟩ := hp.exists_continuousAffineMap_apply_affineCombination
    have heq : intrinsicInterior ℝ (convexHull ℝ (range p)) =
        (affineSpan ℝ (range p) : Set (σ → ℝ)) ∩ ⋂ i : ι, {x | 0 < f i x} := by
      ext x
      rw [hp.mem_intrinsicInterior_convexHull_iff]
      simp only [mem_inter_iff, SetLike.mem_coe, mem_iInter, mem_ofPred_eq]
      constructor
      · rintro ⟨w, hw₀, hw₁, rfl⟩
        exact ⟨affineCombination_mem_affineSpan hw₁ p, fun i => by simpa [hf w hw₁ i] using hw₀ i⟩
      · rintro ⟨hxA, hpos⟩
        obtain ⟨w, hw₁, rfl⟩ := eq_affineCombination_of_mem_affineSpan_of_fintype hxA
        exact ⟨w, fun i => by simpa [hf w hw₁ i] using hpos i, hw₁, rfl⟩
    rw [heq]
    exact (affineSpan ℝ (range p)).isSemialgebraic.inter
      (.iInter fun i => (f i).toAffineMap.isSemialgebraic_pos)

end Real
