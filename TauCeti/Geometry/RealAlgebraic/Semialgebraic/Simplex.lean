/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Convex.Intrinsic
public import Mathlib.Analysis.Convex.SimplicialComplex.Basic
public import TauCeti.Analysis.Convex.Polyhedron.Basic
public import TauCeti.Analysis.Convex.StdSimplex
public import TauCeti.Geometry.RealAlgebraic.Semialgebraic.Dimension.Basic
public import TauCeti.Geometry.RealAlgebraic.Semialgebraic.Function
import Mathlib.Analysis.Convex.Caratheodory
import Mathlib.Analysis.Convex.Topology
import Mathlib.LinearAlgebra.AffineSpace.Basis
import Mathlib.LinearAlgebra.AffineSpace.FiniteDimensional
import TauCeti.Analysis.Analytic.Submanifold.Affine
import TauCeti.Analysis.Convex.Intrinsic
import TauCeti.Analysis.Convex.OpenSimplex
import TauCeti.Analysis.Normed.Affine.AddTorsor.Bases
import TauCeti.Geometry.RealAlgebraic.Semialgebraic.Dimension.Manifold
import TauCeti.Topology.LocallyClosed

/-!
# Semialgebraicity of affine maps, polyhedra, and simplices

Every linear or affine map from a finite-dimensional coordinate space `σ → R` into `τ → R` has
degree-at-most-one polynomial coordinates, and so is semialgebraic and pulls semialgebraic sets
back to semialgebraic sets without assuming projection closure (`HasSemialgebraicProjections R`).
Consequently, whether a subset of an abstract affine space `P` is semialgebraic after an affine
identification `P ≃ᵃ[R] (σ → R)` does not depend on the chosen identification
(`AffineEquiv.isSemialgebraic_image_iff_of_affineEquiv`).

Over any ordered field `K`, every linear subspace and every affine subspace of `σ → K` (`Finite σ`)
is cut out by finitely many linear equations and is therefore semialgebraic; over a strictly ordered
field `K`, every closed simplex, the convex hull of every finite set (by Carathéodory's theorem),
and the carrier of every finite geometric simplicial complex are semialgebraic, again without
projection closure.

Over `ℝ`, convex polyhedra (`TauCeti.IsConvexPolyhedron`), open simplices
(`intrinsicInterior ℝ (convexHull ℝ (range p))`), relative boundaries of simplices, and the
standard simplex together with its open part, open facets, and relative boundary are all
semialgebraic, and the semialgebraic dimension (`TauCeti.semialgebraicDim`) of an open or closed
simplex on `m` vertices (`m ≥ 1`) in `Fin n → ℝ` is `m - 1`, while the dimension of the carrier of
a finite simplicial complex is the supremum of the dimensions of its simplices.

## Main results

* `LinearMap.isSemialgebraicOn`, `AffineMap.isSemialgebraicOn`,
  `TauCeti.IsSemialgebraic.preimage_affineMap`: linear and affine maps are semialgebraic and pull
  semialgebraic sets back to semialgebraic sets.
* `AffineEquiv.isSemialgebraic_image_iff_of_affineEquiv`: coordinate-choice independence of
  semialgebraicity on an affine space.
* `Submodule.isSemialgebraic`, `AffineSubspace.isSemialgebraic`: linear and affine subspaces of
  `σ → K` are semialgebraic.
* `AffineIndependent.isSemialgebraic_convexHull`, `Set.Finite.isSemialgebraic_convexHull`,
  `Geometry.SimplicialComplex.isSemialgebraic_space`,
  `TauCeti.IsConvexPolyhedron.isSemialgebraic`: closed simplices, convex hulls of finite sets,
  carriers of finite simplicial complexes, and convex polyhedra are semialgebraic.
* `AffineIndependent.isSemialgebraic_intrinsicInterior_convexHull`,
  `AffineIndependent.isSemialgebraic_intrinsicFrontier_convexHull`: open simplices and relative
  frontiers of simplices in `σ → ℝ` are semialgebraic.
* `AffineIndependent.semialgebraicDim_intrinsicInterior_convexHull`,
  `AffineIndependent.semialgebraicDim_convexHull`,
  `Geometry.SimplicialComplex.semialgebraicDim_space`: semialgebraic dimension of simplices and
  finite simplicial complexes in `Fin n → ℝ`.

## References

* J. Bochnak, M. Coste, M.-F. Roy, *Real Algebraic Geometry*, Ergebnisse der Mathematik und ihrer
  Grenzgebiete 36, Springer, 1998, §§2.1, 2.8, 9.2.
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
  have hx : x = ∑ j : σ, x j • Pi.single j 1 := by
    ext k
    simp [Finset.sum_apply, Pi.single_apply]
  conv_lhs => rw [hx]
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

/-- View a scalar affine functional on `σ → R` as an affine map into `Unit → R`. -/
private def AffineMap.toUnitFun (f : (σ → R) →ᵃ[R] R) : (σ → R) →ᵃ[R] (Unit → R) where
  toFun x _ := f x
  linear :=
    { toFun := fun v _ => f.linear v
      map_add' := fun u v => by ext; simp
      map_smul' := fun c v => by ext; simp }
  map_vadd' p v := by ext; simpa [vadd_eq_add] using f.map_vadd p v

variable [LinearOrder R]

/-- A linear map between finite-dimensional coordinate spaces is semialgebraic on every
semialgebraic domain. -/
theorem LinearMap.isSemialgebraicOn [Finite σ] [Finite τ] (L : (σ → R) →ₗ[R] (τ → R))
    {s : Set (σ → R)} (hs : TauCeti.IsSemialgebraic s) : TauCeti.IsSemialgebraicOn L s := by
  obtain ⟨p, hp⟩ := L.exists_mvPolynomial_eval_eq
  exact (TauCeti.isSemialgebraicOn_eval p hs).congr fun x _ => (hp x).symm

/-- A linear map between finite-dimensional coordinate spaces is semialgebraic. -/
theorem LinearMap.isSemialgebraicMap [Finite σ] [Finite τ] (L : (σ → R) →ₗ[R] (τ → R)) :
    TauCeti.IsSemialgebraicMap L :=
  TauCeti.isSemialgebraicOn_univ.1 (L.isSemialgebraicOn TauCeti.isSemialgebraic_univ)

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

/-- Semialgebraicity is invariant under preimage by an affine equivalence between
finite-dimensional coordinate spaces. -/
@[simp]
theorem AffineEquiv.isSemialgebraic_preimage_iff [Finite σ] [Finite τ]
    (e : (σ → R) ≃ᵃ[R] (τ → R)) {s : Set (τ → R)} :
    TauCeti.IsSemialgebraic (e ⁻¹' s) ↔ TauCeti.IsSemialgebraic s := by
  refine ⟨fun hs => ?_, fun hs => hs.preimage_affineMap e.toAffineMap⟩
  have hpre : (e.symm.toAffineMap : (τ → R) → σ → R) ⁻¹' (e ⁻¹' s) = s := by
    ext y
    simp only [mem_preimage, AffineEquiv.coe_toAffineMap, AffineEquiv.apply_symm_apply]
  rw [← hpre]
  exact hs.preimage_affineMap e.symm.toAffineMap

/-- Semialgebraicity is invariant under image by an affine equivalence between
finite-dimensional coordinate spaces. -/
@[simp]
theorem AffineEquiv.isSemialgebraic_image_iff [Finite σ] [Finite τ]
    (e : (σ → R) ≃ᵃ[R] (τ → R)) {s : Set (σ → R)} :
    TauCeti.IsSemialgebraic (e '' s) ↔ TauCeti.IsSemialgebraic s := by
  have himg : e '' s = e.symm ⁻¹' s := by
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      simpa using hx
    · intro hy
      exact ⟨e.symm y, hy, e.apply_symm_apply y⟩
  rw [himg]
  exact e.symm.isSemialgebraic_preimage_iff

/-- **Coordinate-choice independence.** For any subset `s` of an affine space `P`, whether the
coordinate image of `s` is semialgebraic does not depend on the chosen affine identification of `P`
with a finite-dimensional coordinate space. -/
theorem AffineEquiv.isSemialgebraic_image_iff_of_affineEquiv [Finite σ] [Finite τ]
    {V P : Type*} [AddCommGroup V] [Module R V] [AddTorsor V P]
    (e₁ : P ≃ᵃ[R] (σ → R)) (e₂ : P ≃ᵃ[R] (τ → R)) {s : Set P} :
    TauCeti.IsSemialgebraic (e₁ '' s) ↔ TauCeti.IsSemialgebraic (e₂ '' s) := by
  have himg : e₁ '' s = (e₁.symm.trans e₂) ⁻¹' (e₂ '' s) := by
    ext y
    simp only [mem_image, mem_preimage, AffineEquiv.trans_apply, e₂.injective.eq_iff]
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact ⟨e₁.symm (e₁ x), by simpa using hx, by simp⟩
    · rintro ⟨x, hx, hxy⟩
      exact ⟨x, hx, by simp [hxy]⟩
  rw [himg, (e₁.symm.trans e₂).isSemialgebraic_preimage_iff]

/-- Scalar affine inequalities on `σ → R` (`Finite σ`) cut out semialgebraic half-spaces. -/
theorem AffineMap.isSemialgebraic_nonpos [Finite σ] (f : (σ → R) →ᵃ[R] R) :
    TauCeti.IsSemialgebraic {x : σ → R | f x ≤ 0} := by
  simpa [AffineMap.toUnitFun] using
    (TauCeti.isSemialgebraic_eval_nonpos
      (X () : MvPolynomial Unit R)).preimage_affineMap f.toUnitFun

/-- Scalar affine nonnegativity conditions on `σ → R` (`Finite σ`) cut out semialgebraic
half-spaces. -/
theorem AffineMap.isSemialgebraic_nonneg [Finite σ] (f : (σ → R) →ᵃ[R] R) :
    TauCeti.IsSemialgebraic {x : σ → R | 0 ≤ f x} := by
  simpa [AffineMap.toUnitFun] using
    (TauCeti.isSemialgebraic_eval_nonneg
      (X () : MvPolynomial Unit R)).preimage_affineMap f.toUnitFun

/-- Strict scalar affine positivity conditions on `σ → R` (`Finite σ`) cut out semialgebraic open
half-spaces. -/
theorem AffineMap.isSemialgebraic_pos [Finite σ] (f : (σ → R) →ᵃ[R] R) :
    TauCeti.IsSemialgebraic {x : σ → R | 0 < f x} := by
  simpa [AffineMap.toUnitFun] using
    (TauCeti.isSemialgebraic_eval_pos
      (X () : MvPolynomial Unit R)).preimage_affineMap f.toUnitFun

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
  let π : (σ → K) →ₗ[K] (σ → K) :=
    Q.subtype.comp
      ((LinearMap.snd K W Q).comp (Submodule.prodEquivOfIsCompl W Q hWQ).symm.toLinearMap)
  have hker : (W : Set (σ → K)) = π ⁻¹' {0} := by
    ext x
    simp only [SetLike.mem_coe, mem_preimage, mem_singleton_iff]
    constructor
    · intro hxW
      have hpair : (Submodule.prodEquivOfIsCompl W Q hWQ).symm x = (⟨x, hxW⟩, 0) :=
        (Submodule.prodEquivOfIsCompl W Q hWQ).symm_apply_eq.2 (by simp)
      change (((Submodule.prodEquivOfIsCompl W Q hWQ).symm x).2 : σ → K) = 0
      rw [hpair]
      rfl
    · intro hx0
      have hQ : ((Submodule.prodEquivOfIsCompl W Q hWQ).symm x).2 = 0 :=
        Subtype.ext (by simpa [π] using hx0)
      have hrepr : x = (((Submodule.prodEquivOfIsCompl W Q hWQ).symm x).1 : σ → K) +
          (((Submodule.prodEquivOfIsCompl W Q hWQ).symm x).2 : σ → K) := by
        simpa using ((Submodule.prodEquivOfIsCompl W Q hWQ).apply_symm_apply x).symm
      rw [hrepr, hQ, ZeroMemClass.coe_zero, add_zero]
      exact ((Submodule.prodEquivOfIsCompl W Q hWQ).symm x).1.2
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

/-! ### Closed simplices and convex hulls over a strictly ordered field -/

section StrictOrderedField

variable {σ K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K] [Finite σ]

/-- The convex hull of an affine basis of `σ → K` (`Finite σ`) is semialgebraic. -/
theorem AffineBasis.isSemialgebraic_convexHull {ι : Type*} (b : AffineBasis ι K (σ → K)) :
    TauCeti.IsSemialgebraic (convexHull K (range b)) := by
  cases nonempty_fintype σ
  have : Finite ι := b.finite
  rw [b.convexHull_eq_nonneg_coord, ofPred_forall]
  exact .iInter fun i => (b.coord i).isSemialgebraic_nonneg

/-- **Closed simplices are semialgebraic.** Over any strictly ordered field `K`, the convex hull of
a finite affinely independent family in `σ → K` (`Finite σ`) is semialgebraic, without assuming
projection closure. -/
theorem AffineIndependent.isSemialgebraic_convexHull {ι : Type*} [Finite ι] {p : ι → σ → K}
    (hp : AffineIndependent K p) : TauCeti.IsSemialgebraic (convexHull K (range p)) := by
  classical
  cases nonempty_fintype ι
  rcases isEmpty_or_nonempty ι with hι | _
  · simp [range_eq_empty]
  · obtain ⟨t, hst, hti, hts⟩ :=
      exists_subset_affineIndependent_affineSpan_eq_top (hp.range (k := K))
    let b : AffineBasis t K (σ → K) := ⟨fun q => q, hti, by simpa using hts⟩
    let c : ι → (σ → K) →ᵃ[K] K := fun i => b.coord ⟨p i, hst (mem_range_self i)⟩
    have hcp (i j : ι) : c i (p j) = if i = j then 1 else 0 := by
      rw [show p j = b ⟨p j, hst (mem_range_self j)⟩ from rfl, b.coord_apply]
      simp [hp.injective.eq_iff]
    have hc (w : ι → K) (hw : ∑ j, w j = 1) (i : ι) :
        c i (Finset.univ.affineCombination K p w) = w i := by
      rw [Finset.map_affineCombination _ _ _ hw,
        Finset.affineCombination_eq_linear_combination _ _ _ hw]
      simp [hcp]
    have heq : convexHull K (range p) =
        (affineSpan K (range p) : Set (σ → K)) ∩ ⋂ i : ι, {x | 0 ≤ c i x} := by
      ext x
      simp only [mem_inter_iff, SetLike.mem_coe, mem_iInter, mem_ofPred_eq]
      constructor
      · intro hx
        refine ⟨convexHull_subset_affineSpan _ hx, fun i => ?_⟩
        rw [convexHull_range_eq_exists_affineCombination] at hx
        obtain ⟨s, w, hw₀, hw₁, rfl⟩ := hx
        have hw1' : ∑ j, (s : Set ι).indicator w j = 1 := by
          simpa [Finset.sum_indicator_subset _ s.subset_univ] using hw₁
        rw [Finset.affineCombination_indicator_subset _ _ s.subset_univ, hc _ hw1']
        by_cases hi : i ∈ s
        · simpa [hi] using hw₀ i hi
        · simp [hi]
      · rintro ⟨hxA, hnn⟩
        obtain ⟨w, hw₁, rfl⟩ := eq_affineCombination_of_mem_affineSpan_of_fintype hxA
        exact affineCombination_mem_convexHull (fun i _ => by simpa [hc w hw₁ i] using hnn i) hw₁
    rw [heq]
    exact (affineSpan K (range p)).isSemialgebraic.inter
      (.iInter fun i => (c i).isSemialgebraic_nonneg)

/-- **Convex hulls of finite sets are semialgebraic.** By Carathéodory's theorem, the convex hull
of a finite subset of `σ → K` (`Finite σ`) is a finite union of closed simplices and is therefore
semialgebraic without assuming projection closure. -/
theorem Set.Finite.isSemialgebraic_convexHull {s : Set (σ → K)} (hs : s.Finite) :
    TauCeti.IsSemialgebraic (convexHull K s) := by
  classical
  have hfin : {t : Finset (σ → K) | (t : Set (σ → K)) ⊆ s}.Finite := by
    refine (hs.toFinset.powerset : Set (Finset (σ → K))).toFinite.subset fun t ht => ?_
    simp only [Finset.mem_coe, Finset.mem_powerset]
    exact fun x hx => hs.mem_toFinset.2 (ht hx)
  rw [convexHull_eq_union]
  refine .biUnion hfin fun t _ => ?_
  by_cases h : AffineIndependent K ((↑) : t → σ → K)
  · have hu : (⋃ (_ : AffineIndependent K ((↑) : t → σ → K)),
        convexHull K (t : Set (σ → K))) = convexHull K (range ((↑) : t → σ → K)) := by
      ext x
      simp only [mem_iUnion, exists_prop, h, true_and, Subtype.range_coe_subtype,
        Finset.setOfPred_mem]
    rw [hu]
    exact h.isSemialgebraic_convexHull
  · have hu : (⋃ (_ : AffineIndependent K ((↑) : t → σ → K)),
        convexHull K (t : Set (σ → K))) = ∅ := by
      ext x
      simp only [mem_iUnion, exists_prop, h, false_and, mem_empty_iff_false]
    rw [hu]
    exact TauCeti.isSemialgebraic_empty

/-- The underlying space `L.space` of a finite geometric simplicial complex in `σ → K` (`Finite σ`)
is semialgebraic. -/
theorem Geometry.SimplicialComplex.isSemialgebraic_space
    {L : Geometry.SimplicialComplex K (σ → K)} (hL : L.faces.Finite) :
    TauCeti.IsSemialgebraic L.space :=
  .biUnion hL fun s _ => s.finite_toSet.isSemialgebraic_convexHull

end StrictOrderedField

/-! ### Convex polyhedra, open simplices, and semialgebraic dimension over `ℝ` -/

section Real

variable {σ : Type*} [Finite σ] {n : ℕ}

/-- Every convex polyhedron in `σ → ℝ` (`Finite σ`) is semialgebraic. -/
theorem TauCeti.IsConvexPolyhedron.isSemialgebraic {s : Set (σ → ℝ)}
    (hs : TauCeti.IsConvexPolyhedron s) : TauCeti.IsSemialgebraic s := by
  obtain ⟨m, g, rfl⟩ := TauCeti.isConvexPolyhedron_iff.1 hs
  rw [ofPred_forall]
  exact .iInter fun i => (g i).toAffineMap.isSemialgebraic_nonpos

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

/-- The relative boundary `intrinsicFrontier ℝ (convexHull ℝ (range p))` of a finite simplex in
`σ → ℝ` (`Finite σ`) is semialgebraic. -/
theorem AffineIndependent.isSemialgebraic_intrinsicFrontier_convexHull {ι : Type*} [Finite ι]
    {p : ι → σ → ℝ} (hp : AffineIndependent ℝ p) :
    TauCeti.IsSemialgebraic (intrinsicFrontier ℝ (convexHull ℝ (range p))) := by
  cases nonempty_fintype σ
  rw [← ((finite_range p).isCompact_convexHull (𝕜 := ℝ)).isClosed.sdiff_intrinsicInterior]
  exact hp.isSemialgebraic_convexHull.sdiff hp.isSemialgebraic_intrinsicInterior_convexHull

/-- Every open face of a geometric simplicial complex in `σ → ℝ` (`Finite σ`) is semialgebraic. -/
theorem Geometry.SimplicialComplex.isSemialgebraic_intrinsicInterior_convexHull
    {K : Geometry.SimplicialComplex ℝ (σ → ℝ)} {s : Finset (σ → ℝ)} (hs : s ∈ K.faces) :
    TauCeti.IsSemialgebraic (intrinsicInterior ℝ (convexHull ℝ (s : Set (σ → ℝ)))) := by
  have hrange : (s : Set (σ → ℝ)) = range ((↑) : s → σ → ℝ) := by simp
  rw [hrange]
  exact (K.indep hs).isSemialgebraic_intrinsicInterior_convexHull

/-- The semialgebraic dimension of a nonempty open simplex on `Fintype.card ι` vertices in
`Fin n → ℝ` is `Fintype.card ι - 1`. -/
theorem AffineIndependent.semialgebraicDim_intrinsicInterior_convexHull {ι : Type*} [Fintype ι]
    [Nonempty ι] {p : ι → Fin n → ℝ} (hp : AffineIndependent ℝ p) :
    TauCeti.semialgebraicDim (intrinsicInterior ℝ (convexHull ℝ (range p))) =
      (Fintype.card ι - 1 : ℕ) :=
  hp.isAnalyticSubmanifold_intrinsicInterior_convexHull.semialgebraicDim_eq

/-- The semialgebraic dimension of a nonempty closed simplex on `Fintype.card ι` vertices in
`Fin n → ℝ` is `Fintype.card ι - 1`. -/
theorem AffineIndependent.semialgebraicDim_convexHull {ι : Type*} [Fintype ι] [Nonempty ι]
    {p : ι → Fin n → ℝ} (hp : AffineIndependent ℝ p) :
    TauCeti.semialgebraicDim (convexHull ℝ (range p)) = (Fintype.card ι - 1 : ℕ) := by
  refine le_antisymm ?_
    (hp.semialgebraicDim_intrinsicInterior_convexHull ▸
      TauCeti.semialgebraicDim_mono intrinsicInterior_subset)
  have hdim : Module.finrank ℝ (affineSpan ℝ (range p)).direction = Fintype.card ι - 1 := by
    rw [direction_affineSpan]
    exact hp.finrank_vectorSpan (Nat.sub_add_cancel (Nat.succ_le_iff.2 Fintype.card_pos)).symm
  obtain ⟨i₀⟩ := ‹Nonempty ι›
  have hne : (affineSpan ℝ (range p) : Set (Fin n → ℝ)).Nonempty :=
    ⟨p i₀, subset_affineSpan ℝ _ (mem_range_self i₀)⟩
  have hspan : TauCeti.semialgebraicDim (affineSpan ℝ (range p) : Set (Fin n → ℝ)) =
      (Fintype.card ι - 1 : ℕ) := by
    rw [← hdim]
    exact ((affineSpan ℝ (range p)).isAnalyticSubmanifold hne).semialgebraicDim_eq
  exact hspan ▸ TauCeti.semialgebraicDim_mono (convexHull_subset_affineSpan _)

/-- Every open face `s` of a geometric simplicial complex in `Fin n → ℝ` has semialgebraic
dimension `s.card - 1`. -/
theorem Geometry.SimplicialComplex.semialgebraicDim_intrinsicInterior_convexHull
    {K : Geometry.SimplicialComplex ℝ (Fin n → ℝ)} {s : Finset (Fin n → ℝ)} (hs : s ∈ K.faces) :
    TauCeti.semialgebraicDim (intrinsicInterior ℝ (convexHull ℝ (s : Set (Fin n → ℝ)))) =
      (s.card - 1 : ℕ) :=
  (K.isAnalyticSubmanifold_intrinsicInterior_convexHull hs).semialgebraicDim_eq

/-- Every closed face `s` of a geometric simplicial complex in `Fin n → ℝ` has semialgebraic
dimension `s.card - 1`. -/
theorem Geometry.SimplicialComplex.semialgebraicDim_convexHull
    {K : Geometry.SimplicialComplex ℝ (Fin n → ℝ)} {s : Finset (Fin n → ℝ)} (hs : s ∈ K.faces) :
    TauCeti.semialgebraicDim (convexHull ℝ (s : Set (Fin n → ℝ))) = (s.card - 1 : ℕ) := by
  have : Nonempty s := (K.nonempty_of_mem_faces hs).coe_sort
  have hrange : (s : Set (Fin n → ℝ)) = range ((↑) : s → Fin n → ℝ) := by simp
  rw [hrange, ← Fintype.card_coe]
  exact (K.indep hs).semialgebraicDim_convexHull

/-- The semialgebraic dimension of the underlying space of a finite geometric simplicial complex in
`Fin n → ℝ` is the supremum of `s.card - 1` over its faces `s`. -/
theorem Geometry.SimplicialComplex.semialgebraicDim_space
    {K : Geometry.SimplicialComplex ℝ (Fin n → ℝ)} (hK : K.faces.Finite) :
    TauCeti.semialgebraicDim K.space = ⨆ s ∈ K.faces, ((s.card - 1 : ℕ) : WithBot ℕ∞) := by
  have := hK.to_subtype
  have hspace : K.space = ⋃ s : K.faces, convexHull ℝ (s.1 : Set (Fin n → ℝ)) := by
    rw [Geometry.SimplicialComplex.space, biUnion_eq_iUnion]
  have hdim (s : K.faces) : TauCeti.semialgebraicDim (convexHull ℝ (s.1 : Set (Fin n → ℝ))) =
      (s.1.card - 1 : ℕ) := K.semialgebraicDim_convexHull s.2
  rw [hspace, TauCeti.semialgebraicDim_iUnion_of_isLocallyClosed
    (fun s => (s.1.finite_toSet.isCompact_convexHull (𝕜 := ℝ)).isClosed.isLocallyClosed)]
  simp only [hdim, iSup_subtype']

end Real
