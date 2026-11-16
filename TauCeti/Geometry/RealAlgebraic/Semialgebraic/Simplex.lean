/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Convex.Intrinsic
public import Mathlib.LinearAlgebra.AffineSpace.Independent
public import TauCeti.Analysis.Convex.StdSimplex
public import TauCeti.Geometry.RealAlgebraic.Semialgebraic.Function
import Mathlib.LinearAlgebra.AffineSpace.FiniteDimensional
import TauCeti.Analysis.Convex.OpenSimplex
import TauCeti.Analysis.Normed.Affine.AddTorsor.Bases

/-!
# Semialgebraicity of affine maps, standard simplices, and open simplices

Every affine map from a finite-dimensional coordinate space `σ → R` into `τ → R` has
degree-at-most-one polynomial coordinates, and so is semialgebraic and pulls semialgebraic sets
back to semialgebraic sets without assuming projection closure (`HasSemialgebraicProjections R`).
In particular, strict scalar affine positivity conditions cut out semialgebraic open half-spaces,
and the closed standard simplex in `σ → R` together with its open part, open facets, and (over `ℝ`)
relative boundary are semialgebraic.

Over any ordered field `K`, every linear subspace and every affine subspace of `σ → K` (`Finite σ`)
is the inverse image of `{0}` or of its direction under an affine map and is therefore
semialgebraic; over `ℝ`, intersecting the affine span of an affinely independent finite family
with the open half-spaces of its continuous barycentric coordinates shows that every open simplex
`intrinsicInterior ℝ (convexHull ℝ (range p))` is semialgebraic.

## Main results

* `AffineMap.isSemialgebraicOn`, `AffineMap.isSemialgebraicMap`,
  `TauCeti.IsSemialgebraic.preimage_affineMap`, `AffineMap.isSemialgebraic_pos`: affine maps are
  semialgebraic, pull semialgebraic sets back to semialgebraic sets, and cut out semialgebraic open
  half-spaces, without assuming projection closure.
* `TauCeti.isSemialgebraic_range_stdSimplex_weights`, `TauCeti.isSemialgebraic_openStdSimplex`,
  `TauCeti.isSemialgebraic_openStdSimplexFacet`, `TauCeti.isSemialgebraic_stdSimplexBoundary`: the
  standard simplex and its open part, open facets, and relative boundary are semialgebraic.
* `Submodule.isSemialgebraic`, `AffineSubspace.isSemialgebraic`: linear and affine subspaces of
  `σ → K` are semialgebraic.
* `AffineIndependent.isSemialgebraic_intrinsicInterior_convexHull`: open simplices in `σ → ℝ` are
  semialgebraic.

## References

* J. Bochnak, M. Coste, M.-F. Roy, *Real Algebraic Geometry*, Ergebnisse der Mathematik und ihrer
  Grenzgebiete 36, Springer, 1998, §§2.1, 9.2.
-/

public section

open MvPolynomial Set Convexity

section CommRing

/-! ### Linear and affine maps -/

/-- Every linear map out of a finite-dimensional coordinate space `σ → S` over a commutative
semiring has homogeneous linear polynomial coordinates. -/
theorem LinearMap.exists_mvPolynomial_eval_eq {σ τ S : Type*} [CommSemiring S] [Finite σ]
    (L : (σ → S) →ₗ[S] (τ → S)) :
    ∃ p : τ → MvPolynomial σ S, ∀ x, L x = fun i => eval x (p i) := by
  classical
  cases nonempty_fintype σ
  refine ⟨fun i => ∑ j : σ, C (L (Pi.single j 1) i) * X j, fun x => funext fun i => ?_⟩
  conv_lhs => rw [pi_eq_sum_univ' x]
  simp [map_sum, Finset.sum_apply, mul_comm]

variable {σ τ R : Type*} [CommRing R]

/-- Every affine map out of a finite-dimensional coordinate space `σ → R` has degree-at-most-one
polynomial coordinates. -/
theorem AffineMap.exists_mvPolynomial_eval_eq [Finite σ] (A : (σ → R) →ᵃ[R] (τ → R)) :
    ∃ p : τ → MvPolynomial σ R, ∀ x, A x = fun i => eval x (p i) := by
  obtain ⟨p, hp⟩ := A.linear.exists_mvPolynomial_eval_eq
  refine ⟨fun i => p i + C (A 0 i), fun x => funext fun i => ?_⟩
  have hx : A x = A.linear x + A 0 := by
    simpa [vadd_eq_add] using A.map_vadd (0 : σ → R) x
  simp [hx, hp]

variable [LinearOrder R]

/-- An affine map between finite-dimensional coordinate spaces is semialgebraic on every
semialgebraic domain. -/
theorem AffineMap.isSemialgebraicOn [Finite σ] [Finite τ] (A : (σ → R) →ᵃ[R] (τ → R))
    {s : Set (σ → R)} (hs : TauCeti.IsSemialgebraic s) : TauCeti.IsSemialgebraicOn A s := by
  obtain ⟨p, hp⟩ := A.exists_mvPolynomial_eval_eq
  exact (TauCeti.isSemialgebraicOn_eval p hs).congr fun x _ => (hp x).symm

/-- An affine map between finite-dimensional coordinate spaces is semialgebraic. -/
theorem AffineMap.isSemialgebraicMap [Finite σ] [Finite τ] (A : (σ → R) →ᵃ[R] (τ → R)) :
    TauCeti.IsSemialgebraicMap A :=
  TauCeti.isSemialgebraicOn_univ.1 (A.isSemialgebraicOn TauCeti.isSemialgebraic_univ)

/-- The inverse image of a semialgebraic set under an affine map out of a finite-dimensional
coordinate space is semialgebraic, without assuming projection closure. -/
theorem TauCeti.IsSemialgebraic.preimage_affineMap [Finite σ] {s : Set (τ → R)}
    (hs : TauCeti.IsSemialgebraic s) (A : (σ → R) →ᵃ[R] (τ → R)) :
    TauCeti.IsSemialgebraic (A ⁻¹' s) := by
  obtain ⟨p, hp⟩ := A.exists_mvPolynomial_eval_eq
  have hfun : (A : (σ → R) → τ → R) = fun x i => eval x (p i) := funext hp
  rw [hfun]
  exact hs.preimage_eval p

/-- Strict scalar affine positivity conditions on `σ → R` (`Finite σ`) cut out semialgebraic open
half-spaces. -/
theorem AffineMap.isSemialgebraic_pos [Finite σ] (f : (σ → R) →ᵃ[R] R) :
    TauCeti.IsSemialgebraic {x : σ → R | 0 < f x} := by
  simpa using (TauCeti.isSemialgebraic_eval_pos (X () : MvPolynomial Unit R)).preimage_affineMap
    ((LinearEquiv.funUnique Unit R R).symm.toAffineEquiv.toAffineMap.comp f)

/-! ### Standard simplex coordinate sets -/

namespace TauCeti

/-- The closed standard simplex of weight vectors in `σ → R` (`Finite σ`) is semialgebraic. -/
theorem isSemialgebraic_range_stdSimplex_weights [Finite σ] :
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

/-- The open standard simplex `{x ∈ range weights | ∀ i, 0 < x i}` in `σ → R` (`Finite σ`) is
semialgebraic. -/
theorem isSemialgebraic_openStdSimplex [Finite σ] :
    IsSemialgebraic {x ∈ range fun s : StdSimplex R σ => ⇑s.weights | ∀ i, 0 < x i} := by
  have h : {x ∈ range fun s : StdSimplex R σ => ⇑s.weights | ∀ i, 0 < x i} =
      (range fun s : StdSimplex R σ => ⇑s.weights) ∩ ⋂ i : σ, {x | 0 < eval x (X i)} := by
    ext x
    simp
  rw [h]
  exact isSemialgebraic_range_stdSimplex_weights.inter
    (.iInter fun i => isSemialgebraic_eval_pos (X i))

/-- Each open facet `{y ∈ range weights | y i = 0 ∧ ∀ j ≠ i, 0 < y j}` of the standard simplex in
`σ → R` (`Finite σ`) is semialgebraic. -/
theorem isSemialgebraic_openStdSimplexFacet [Finite σ] (i : σ) :
    IsSemialgebraic
      {y ∈ range fun s : StdSimplex R σ => ⇑s.weights | y i = 0 ∧ ∀ j ≠ i, 0 < y j} := by
  have h : {y ∈ range fun s : StdSimplex R σ => ⇑s.weights | y i = 0 ∧ ∀ j ≠ i, 0 < y j} =
      (range fun s : StdSimplex R σ => ⇑s.weights) ∩
        ({y | eval y (X i) = 0} ∩ ⋂ j : {j : σ // j ≠ i}, {y | 0 < eval y (X j.1)}) := by
    ext y
    simp
  rw [h]
  exact isSemialgebraic_range_stdSimplex_weights.inter
    ((isSemialgebraic_eval_eq_zero (X i)).inter
      (.iInter fun j => isSemialgebraic_eval_pos (X j.1)))

end TauCeti

end CommRing

/-! ### Linear and affine subspaces over an ordered field -/

section OrderedField

variable {σ K : Type*} [Field K] [LinearOrder K] [Finite σ]

/-- Every linear subspace `W` of `σ → K` (`Finite σ`) is semialgebraic, being the kernel of a
linear projection onto a complement. -/
theorem Submodule.isSemialgebraic (W : Submodule K (σ → K)) :
    TauCeti.IsSemialgebraic (W : Set (σ → K)) := by
  obtain ⟨Q, hWQ⟩ := W.exists_isCompl
  let π : (σ → K) →ₗ[K] (σ → K) := Q.subtype ∘ₗ Submodule.projectionOnto Q W hWQ.symm
  have hker : (W : Set (σ → K)) = π ⁻¹' {0} := by
    ext x
    simp [π, ← LinearMap.mem_ker]
  rw [hker]
  exact (TauCeti.isSemialgebraic_singleton (0 : σ → K)).preimage_affineMap π.toAffineMap

/-- Every affine subspace `A` of `σ → K` (`Finite σ`, possibly empty) is semialgebraic. -/
theorem AffineSubspace.isSemialgebraic (A : AffineSubspace K (σ → K)) :
    TauCeti.IsSemialgebraic (A : Set (σ → K)) := by
  rcases (A : Set (σ → K)).eq_empty_or_nonempty with h | ⟨x₀, hx₀⟩
  · simp [h]
  · have htran : (A : Set (σ → K)) =
        (AffineEquiv.vaddConst K (-x₀)).toAffineMap ⁻¹' (A.direction : Set (σ → K)) := by
      ext x
      simp only [SetLike.mem_coe, mem_preimage, AffineEquiv.coe_toAffineMap,
        AffineEquiv.vaddConst_apply, vadd_eq_add]
      constructor
      · intro hx
        simpa [vsub_eq_sub, sub_eq_add_neg] using AffineSubspace.vsub_mem_direction hx hx₀
      · intro hv
        have hmem := AffineSubspace.vadd_mem_of_mem_direction hv hx₀
        simpa [vadd_eq_add, add_assoc] using hmem
    rw [htran]
    exact A.direction.isSemialgebraic.preimage_affineMap _

end OrderedField

/-! ### Standard simplex boundary and open simplices over `ℝ` -/

section Real

variable {σ : Type*} [Finite σ]

/-- The relative boundary `stdSimplexBoundary σ` of the standard simplex in `σ → ℝ` (`Finite σ`) is
semialgebraic. -/
theorem TauCeti.isSemialgebraic_stdSimplexBoundary :
    TauCeti.IsSemialgebraic (TauCeti.stdSimplexBoundary σ) := by
  have h : TauCeti.stdSimplexBoundary σ =
      (range fun s : StdSimplex ℝ σ => ⇑s.weights) ∩ ⋃ i : σ, {x | eval x (X i) = 0} := by
    ext x
    simp
  rw [h]
  exact TauCeti.isSemialgebraic_range_stdSimplex_weights.inter
    (.iUnion fun i => TauCeti.isSemialgebraic_eval_eq_zero (X i))

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
