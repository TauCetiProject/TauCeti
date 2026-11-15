/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Convex.StdSimplex.BoundaryExtension
public import TauCeti.Geometry.RealAlgebraic.Nash.Submanifold
public import TauCeti.Geometry.RealAlgebraic.Semialgebraic.Simplex
import TauCeti.Algebra.Order.Field.Basic
import TauCeti.Analysis.Analytic.Submanifold.Affine
import TauCeti.Analysis.Convex.OpenSimplex

/-!
# Semialgebraicity and Nashness of simplex extensions and barycentric coordinates

When a cylindrical algebraic decomposition of `ℝⁿ` is lifted to a semialgebraic triangulation
whose open simplices are Nash submanifolds (Łojasiewicz 1964; Bochnak–Coste–Roy 1998, §9.2),
induction over the dimension of a base simplex extends boundary section heights into the simplex by
the rational barycentric formulas `TauCeti.stdSimplexExtension` and
`TauCeti.stdSimplexGapExtension` of `TauCeti.Analysis.Convex.StdSimplex.BoundaryExtension`. Two
regularity properties are needed alongside continuity and strict ordering:

1. **Semialgebraicity on the closed simplex:** if the boundary data `g` are semialgebraic on
   `TauCeti.stdSimplexBoundary ι`, then `stdSimplexExtension α g` is semialgebraic on the whole
   closed standard simplex (`TauCeti.isSemialgebraicOn_stdSimplexExtension`); likewise, if `a` and
   `b` are semialgebraic on the closed standard simplex and `c` is semialgebraic on its boundary,
   then `stdSimplexGapExtension a b c α` is semialgebraic on the closed standard simplex without
   any non-collapse hypothesis (`TauCeti.isSemialgebraicOn_stdSimplexGapExtension`).
2. **Nashness on the open simplex:** for every `m : ℕ`, if `g` is a Nash function in dimension
   `m - 2` on each open facet `{y ∈ range weights | y i = 0 ∧ ∀ j ≠ i, 0 < y j}` of the standard
   simplex in `Fin m → ℝ` (with no regularity required on faces of codimension at least two), then
   `stdSimplexExtension α g` is a Nash function in dimension `m - 1` on the open standard simplex
   `{x ∈ range weights | ∀ i, 0 < x i}` (`TauCeti.nashOnSubmanifold_stdSimplexExtension`).
   Consequently, if `a` and `b` are Nash on the open standard simplex and `a`, `b`, `c` are Nash on
   each open facet with `a ≠ b` on open facets — allowing the gap `a ≤ b` to collapse on faces of
   codimension at least two as well as inside the open simplex — then
   `stdSimplexGapExtension a b c α` is Nash in dimension `m - 1` on the open standard simplex
   (`TauCeti.nashOnSubmanifold_stdSimplexGapExtension`).

To transport these extensions between the standard simplex and an arbitrary geometric simplex
`convexHull ℝ (range p)` in `Fin n → ℝ`, we also show that linear and affine maps are Nash on every
semialgebraic analytic submanifold (`LinearMap.nashOnSubmanifold`, `AffineMap.nashOnSubmanifold`)
and upgrade the affine barycentric coordinate map of `TauCeti.Analysis.Convex.OpenSimplex` to a
semialgebraic and Nash equivalence between closed and open simplices
(`AffineIndependent.nashOnSubmanifold_sum_smul`,
`AffineIndependent.exists_nashOnSubmanifold_barycentricCoord`).

## Main results

* `LinearMap.nashOnSubmanifold`, `AffineMap.nashOnSubmanifold`: linear and affine maps are Nash on
  every semialgebraic analytic submanifold.
* `AffineIndependent.nashOnSubmanifold_sum_smul`,
  `AffineIndependent.exists_nashOnSubmanifold_barycentricCoord`: affine barycentric coordinates
  invert the vertex combination map on closed and open simplices as semialgebraic and Nash maps.
* `TauCeti.isSemialgebraicMap_stdSimplexFacetProjection`,
  `TauCeti.nashOnSubmanifold_stdSimplexFacetProjection`: central projection onto a facet of the
  standard simplex is globally semialgebraic, and Nash on the open standard simplex (`m ≥ 2`).
* `TauCeti.isSemialgebraicOn_stdSimplexExtension`,
  `TauCeti.nashOnSubmanifold_stdSimplexExtension`: semialgebraicity on the closed simplex and
  Nashness on the open simplex for `TauCeti.stdSimplexExtension`.
* `TauCeti.isSemialgebraicOn_stdSimplexGapExtension`,
  `TauCeti.nashOnSubmanifold_stdSimplexGapExtension`: semialgebraicity on the closed simplex and
  Nashness on the open simplex for `TauCeti.stdSimplexGapExtension`.

## References

* J. Bochnak, M. Coste, M.-F. Roy, *Real Algebraic Geometry*, Ergebnisse der Mathematik und ihrer
  Grenzgebiete 36, Springer, 1998, §9.2 (semialgebraic triangulation and Nash open simplices).
* S. Łojasiewicz, *Triangulation of semi-analytic sets*, Annali della Scuola Normale Superiore di
  Pisa (3) 18 (1964), 449–474.
-/

public section

open MvPolynomial Set Finset Convexity

/-! ### Linear and affine Nash maps and barycentric coordinates -/

section Barycentric

variable {n m d : ℕ} {τ : Type*} [Fintype τ] {S : Set (Fin n → ℝ)}

/-- Every linear map `L : (Fin n → ℝ) →ₗ[ℝ] (τ → ℝ)` is a Nash map on every `d`-dimensional
semialgebraic analytic submanifold `S ⊆ Fin n → ℝ`. -/
theorem LinearMap.nashOnSubmanifold (L : (Fin n → ℝ) →ₗ[ℝ] (τ → ℝ))
    (hS : TauCeti.IsAnalyticSubmanifold d S) (hS' : TauCeti.IsSemialgebraic S) :
    TauCeti.NashOnSubmanifold d L S := by
  obtain ⟨p, hp⟩ := L.exists_mvPolynomial_eval_eq
  exact (TauCeti.nashOnSubmanifold_eval p hS hS').congr fun x _ => (hp x).symm

/-- Every affine map `A : (Fin n → ℝ) →ᵃ[ℝ] (τ → ℝ)` is a Nash map on every `d`-dimensional
semialgebraic analytic submanifold `S ⊆ Fin n → ℝ`. -/
theorem AffineMap.nashOnSubmanifold (A : (Fin n → ℝ) →ᵃ[ℝ] (τ → ℝ))
    (hS : TauCeti.IsAnalyticSubmanifold d S) (hS' : TauCeti.IsSemialgebraic S) :
    TauCeti.NashOnSubmanifold d A S := by
  obtain ⟨p, hp⟩ := A.exists_mvPolynomial_eval_eq
  exact (TauCeti.nashOnSubmanifold_eval p hS hS').congr fun x _ => (hp x).symm

/-- For `m ≥ 1` and affinely independent vertices `p : Fin m → Fin n → ℝ`, the barycentric
combination map `w ↦ ∑ i, w i • p i` is a Nash map in dimension `m - 1` on the open standard
simplex and maps it onto `intrinsicInterior ℝ (convexHull ℝ (range p))`. -/
theorem AffineIndependent.nashOnSubmanifold_sum_smul [NeZero m] {p : Fin m → Fin n → ℝ}
    (hp : AffineIndependent ℝ p) :
    TauCeti.NashOnSubmanifold (m - 1) (fun w : Fin m → ℝ => ∑ i, w i • p i)
      {w ∈ range fun s : StdSimplex ℝ (Fin m) => ⇑s.weights | ∀ i, 0 < w i} ∧
    (fun w : Fin m → ℝ => ∑ i, w i • p i) ''
        {w ∈ range fun s : StdSimplex ℝ (Fin m) => ⇑s.weights | ∀ i, 0 < w i} =
      intrinsicInterior ℝ (convexHull ℝ (range p)) := by
  let L : (Fin m → ℝ) →ₗ[ℝ] (Fin n → ℝ) :=
    ∑ i : Fin m, (LinearMap.proj i).smulRight (p i)
  have hL : (L : (Fin m → ℝ) → Fin n → ℝ) = fun w => ∑ i, w i • p i := by
    ext w j
    simp [L, LinearMap.sum_apply, Finset.sum_apply]
  refine ⟨hL ▸ L.nashOnSubmanifold TauCeti.isAnalyticSubmanifold_openStdSimplex
    TauCeti.isSemialgebraic_openStdSimplex, ?_⟩
  ext x
  rw [hp.mem_intrinsicInterior_convexHull_iff]
  constructor
  · rintro ⟨w, ⟨hw, hw₀⟩, rfl⟩
    obtain ⟨-, hw₁⟩ := StdSimplex.mem_range_toFun_comp_weights_iff.1 hw
    exact ⟨w, hw₀, hw₁, Finset.affineCombination_eq_linear_combination _ _ _ hw₁⟩
  · rintro ⟨w, hw₀, hw₁, rfl⟩
    exact ⟨w, ⟨StdSimplex.mem_range_toFun_comp_weights_iff.2 ⟨fun i => (hw₀ i).le, hw₁⟩, hw₀⟩,
      (Finset.affineCombination_eq_linear_combination _ _ _ hw₁).symm⟩

/-- **Semialgebraic and Nash barycentric coordinates of a geometric simplex.** For `m ≥ 1` and
affinely independent vertices `p : Fin m → Fin n → ℝ`, there exists an affine map
`B : (Fin n → ℝ) →ᵃ[ℝ] (Fin m → ℝ)` which is globally semialgebraic, is a Nash map in dimension
`m - 1` on `intrinsicInterior ℝ (convexHull ℝ (range p))`, inverts `w ↦ ∑ i, w i • p i` on
`{w | ∑ i, w i = 1}`, and maps the closed and open geometric simplices into the closed and open
standard simplices as a right inverse to `w ↦ ∑ i, w i • p i`. -/
theorem AffineIndependent.exists_nashOnSubmanifold_barycentricCoord [NeZero m]
    {p : Fin m → Fin n → ℝ} (hp : AffineIndependent ℝ p) :
    ∃ B : (Fin n → ℝ) →ᵃ[ℝ] (Fin m → ℝ),
      TauCeti.IsSemialgebraicMap B ∧
      TauCeti.NashOnSubmanifold (m - 1) B (intrinsicInterior ℝ (convexHull ℝ (range p))) ∧
      (∀ w : Fin m → ℝ, ∑ i, w i = 1 → B (∑ i, w i • p i) = w) ∧
      (∀ x ∈ convexHull ℝ (range p),
        B x ∈ (range fun s : StdSimplex ℝ (Fin m) => ⇑s.weights) ∧ ∑ i, B x i • p i = x) ∧
      (∀ x ∈ intrinsicInterior ℝ (convexHull ℝ (range p)),
        B x ∈ {w ∈ range fun s : StdSimplex ℝ (Fin m) => ⇑s.weights | ∀ i, 0 < w i}) := by
  obtain ⟨B, hleft, hclosed, hopen⟩ := hp.exists_affineMap_barycentricCoord
  have hM : TauCeti.IsAnalyticSubmanifold (m - 1) (intrinsicInterior ℝ (convexHull ℝ (range p))) :=
    by simpa using hp.isAnalyticSubmanifold_intrinsicInterior_convexHull
  exact ⟨B, B.isSemialgebraicMap, B.nashOnSubmanifold hM
    hp.isSemialgebraic_intrinsicInterior_convexHull, hleft, hclosed, hopen⟩

end Barycentric

namespace TauCeti

/-! ### Semialgebraicity and Nashness of facet projections -/

section FacetProjection

/-- Central projection `stdSimplexFacetProjection i` onto the facet opposite `i` is globally a
semialgebraic map on `ι → ℝ` (`Finite ι`), including along the hyperplane `x i = 1` where Lean's
division by zero sends it to `0`. -/
theorem isSemialgebraicMap_stdSimplexFacetProjection {ι : Type*} [Finite ι] [DecidableEq ι]
    (i : ι) : IsSemialgebraicMap (stdSimplexFacetProjection i) := by
  have hnum : IsSemialgebraicMap (fun x : ι → ℝ => x - x i • Pi.single i (1 : ℝ)) :=
    ((isSemialgebraicMap_eval fun j : ι => X j).sub
      (isSemialgebraicMap_eval fun j : ι => C ((Pi.single i (1 : ℝ) : ι → ℝ) j) * X i)).congr
      fun x => by ext j; simp [mul_comm]
  have hden : IsSemialgebraicMap (fun x : ι → ℝ => fun _ : ι => 1 - x i) :=
    (isSemialgebraicMap_eval fun _ : ι => (1 - X i : MvPolynomial ι ℝ)).congr
      fun x => by ext; simp
  refine (hden.inv.mul hnum).congr fun x => funext fun j => ?_
  rcases eq_or_ne j i with rfl | hj
  · simp
  · simp [hj, div_eq_inv_mul]

/-- Away from the hyperplane `x i = 1`, the facet projection `stdSimplexFacetProjection i` is a
Nash map on any `d`-dimensional semialgebraic analytic submanifold `S ⊆ Fin m → ℝ`. -/
theorem nashOnSubmanifold_stdSimplexFacetProjection_of_ne_one {m d : ℕ} {S : Set (Fin m → ℝ)}
    (i : Fin m) (hS : IsAnalyticSubmanifold d S) (hS' : IsSemialgebraic S)
    (hne : ∀ x ∈ S, x i ≠ 1) :
    NashOnSubmanifold d (stdSimplexFacetProjection i) S := by
  have hnum : NashOnSubmanifold d (fun x : Fin m → ℝ => x - x i • Pi.single i (1 : ℝ)) S := by
    refine ((nashOnSubmanifold_id hS hS').sub
      (nashOnSubmanifold_eval
        (fun j : Fin m => C ((Pi.single i (1 : ℝ) : Fin m → ℝ) j) * X i) hS hS')).congr
      fun x _ => ?_
    ext j
    simp [mul_comm]
  have hden : NashOnSubmanifold d (fun x : Fin m → ℝ => fun _ : Fin m => 1 - x i) S :=
    (nashOnSubmanifold_eval (fun _ : Fin m => (1 - X i : MvPolynomial (Fin m) ℝ)) hS hS').congr
      fun x _ => by ext; simp
  refine (hnum.div hden fun x hx _ => sub_ne_zero.2 (hne x hx).symm).congr fun x _ => ?_
  ext j
  rcases eq_or_ne j i with rfl | hj
  · simp
  · simp [hj]

/-- For `m ≥ 2`, the facet projection `stdSimplexFacetProjection i` is a Nash map in dimension
`m - 1` on the open standard simplex in `Fin m → ℝ`. -/
theorem nashOnSubmanifold_stdSimplexFacetProjection {m : ℕ} [Nontrivial (Fin m)] (i : Fin m) :
    NashOnSubmanifold (m - 1) (stdSimplexFacetProjection i)
      {x ∈ range fun s : StdSimplex ℝ (Fin m) => ⇑s.weights | ∀ j, 0 < x j} := by
  have : NeZero m := ⟨by rintro rfl; exact not_subsingleton (Fin 0) inferInstance⟩
  obtain ⟨k, hk⟩ := exists_ne i
  exact nashOnSubmanifold_stdSimplexFacetProjection_of_ne_one i
    isAnalyticSubmanifold_openStdSimplex isSemialgebraic_openStdSimplex
    fun x hx => (StdSimplex.apply_lt_one_of_mem_range_weights hx.1 hk (hx.2 k)).ne

end FacetProjection

/-! ### Semialgebraicity and Nashness of `stdSimplexExtension` -/

section Extension

private theorem isSemialgebraicOn_stdSimplexExtension_of_subsingleton {ι : Type*} [Fintype ι]
    [DecidableEq ι] [Subsingleton ι] {g : (ι → ℝ) → ℝ} (α : ℝ) :
    IsSemialgebraicOn (fun x (_ : Unit) => stdSimplexExtension α g x)
      (range fun s : StdSimplex ℝ ι => ⇑s.weights) := by
  set Δ : Set (ι → ℝ) := range fun s : StdSimplex ℝ ι => ⇑s.weights
  rcases isEmpty_or_nonempty ι with _ | ⟨⟨i₀⟩⟩
  · have hempty : Δ = ∅ := by
      ext x
      simp only [Δ, StdSimplex.mem_range_toFun_comp_weights_iff, mem_empty_iff_false, iff_false]
      rintro ⟨_, hsum⟩
      simp at hsum
    exact hempty ▸ isSemialgebraicOn_empty _
  · have hsing : Δ = {fun _ => 1} := by
      ext x
      rw [mem_singleton_iff]
      change x ∈ (range fun s : StdSimplex ℝ ι => ⇑s.weights) ↔ _
      rw [StdSimplex.mem_range_toFun_comp_weights_iff]
      constructor
      · rintro ⟨_, hsum⟩
        rw [Finset.sum_eq_single i₀ (fun _ _ hj => (hj (Subsingleton.elim _ _)).elim)
          (by simp)] at hsum
        exact funext fun j => Subsingleton.elim j i₀ ▸ hsum
      · rintro rfl
        refine ⟨fun _ => zero_le_one, ?_⟩
        rw [Finset.sum_eq_single i₀ (fun _ _ hj => (hj (Subsingleton.elim _ _)).elim) (by simp)]
    rw [hsing]
    exact (isSemialgebraicOn_const (fun _ : Unit => stdSimplexExtension α g (fun _ => 1))
      (isSemialgebraic_singleton _)).congr fun x hx => by rw [mem_singleton_iff.1 hx]

/-- **Semialgebraicity of the rational simplex extension.** If `g` is semialgebraic on the
relative boundary `stdSimplexBoundary ι` of the standard simplex (`Fintype ι`), then
`stdSimplexExtension α g` is semialgebraic on the whole closed standard simplex. -/
theorem isSemialgebraicOn_stdSimplexExtension {ι : Type*} [Fintype ι] [DecidableEq ι]
    {g : (ι → ℝ) → ℝ} (α : ℝ)
    (hg : IsSemialgebraicOn (fun x (_ : Unit) => g x) (stdSimplexBoundary ι)) :
    IsSemialgebraicOn (fun x (_ : Unit) => stdSimplexExtension α g x)
      (range fun s : StdSimplex ℝ ι => ⇑s.weights) := by
  rcases subsingleton_or_nontrivial ι with _ | _
  · exact isSemialgebraicOn_stdSimplexExtension_of_subsingleton α
  · set Δ : Set (ι → ℝ) := range fun s : StdSimplex ℝ ι => ⇑s.weights
    set P : Set (ι → ℝ) := {x | ∀ i, 0 < x i}
    have hbdry : Δ \ P = stdSimplexBoundary ι := by
      ext x
      simp only [Set.mem_sdiff, P, mem_ofPred_eq, mem_stdSimplexBoundary, Δ]
      refine ⟨fun ⟨hx, hnot⟩ =>
        mem_stdSimplexBoundary.1 ((mem_stdSimplexBoundary_or_forall_pos hx).resolve_right hnot),
        fun ⟨hx, i, hi⟩ => ⟨hx, fun h => (h i).ne' hi⟩⟩
    have hS : IsSemialgebraic (Δ ∩ P) := isSemialgebraic_openStdSimplex
    have hinv (i : ι) : IsSemialgebraicOn (fun x (_ : Unit) => (x i)⁻¹) (Δ ∩ P) :=
      (isSemialgebraicOn_eval (fun _ : Unit => (X i : MvPolynomial ι ℝ)) hS).inv.congr
        fun x _ => by ext; simp
    have hgp (i : ι) :
        IsSemialgebraicOn (fun x (_ : Unit) => g (stdSimplexFacetProjection i x)) (Δ ∩ P) :=
      hg.comp ((isSemialgebraicMap_stdSimplexFacetProjection i).isSemialgebraicOn hS)
        fun x hx => stdSimplexFacetProjection_mem_stdSimplexBoundary hx.1 hx.2 i
    have hnum : IsSemialgebraicOn
        (fun x (_ : Unit) => α + ∑ i : ι, (x i)⁻¹ * g (stdSimplexFacetProjection i x)) (Δ ∩ P) :=
      ((isSemialgebraicOn_const (fun _ : Unit => α) hS).add
        (Finset.univ.isSemialgebraicOn_sum hS fun i _ => (hinv i).mul (hgp i))).congr
        fun x _ => by ext; simp [Finset.sum_apply]
    have hden : IsSemialgebraicOn (fun x (_ : Unit) => 1 + ∑ i : ι, (x i)⁻¹) (Δ ∩ P) :=
      ((isSemialgebraicOn_const (fun _ : Unit => (1 : ℝ)) hS).add
        (Finset.univ.isSemialgebraicOn_sum hS fun i _ => hinv i)).congr
        fun x _ => by ext; simp [Finset.sum_apply]
    refine IsSemialgebraicOn.glue (f := fun x (_ : Unit) =>
        (α + ∑ i, (x i)⁻¹ * g (stdSimplexFacetProjection i x)) / (1 + ∑ i, (x i)⁻¹))
      (g := fun x (_ : Unit) => g x) ?_ (hbdry.symm ▸ hg) ?_ ?_
    · exact (hnum.div hden).congr fun x _ => by ext; simp
    · intro x hx; ext; exact stdSimplexExtension_of_forall_pos hx.2
    · intro x hx; ext; exact stdSimplexExtension_of_not_forall_pos hx.2

private theorem nashOnSubmanifold_stdSimplexExtension_of_subsingleton {m : ℕ}
    [hsub : Subsingleton (Fin m)] {g : (Fin m → ℝ) → ℝ} (α : ℝ) :
    NashOnSubmanifold (m - 1) (fun x (_ : Unit) => stdSimplexExtension α g x)
      {x ∈ range fun s : StdSimplex ℝ (Fin m) => ⇑s.weights | ∀ i, 0 < x i} := by
  set U : Set (Fin m → ℝ) :=
    {x ∈ range fun s : StdSimplex ℝ (Fin m) => ⇑s.weights | ∀ i, 0 < x i}
  rcases eq_zero_or_neZero m with rfl | _
  · have hempty : U = ∅ := by
      ext x
      simp only [U, StdSimplex.mem_range_toFun_comp_weights_iff, mem_empty_iff_false, iff_false]
      rintro ⟨⟨_, hsum⟩, _⟩
      simp at hsum
    rw [hempty]
    exact ⟨analyticOnSubmanifold_iff.2 (by simp), isSemialgebraicOn_empty _⟩
  · have i₀ : Fin m := 0
    have hm1 : m - 1 = 0 := by
      have hle : m ≤ 1 := by simpa using Fintype.card_le_one_iff_subsingleton.2 hsub
      omega
    have hsing : U = {fun _ => 1} := by
      ext x
      rw [mem_singleton_iff]
      change (x ∈ (range fun s : StdSimplex ℝ (Fin m) => ⇑s.weights) ∧ ∀ i, 0 < x i) ↔ _
      rw [StdSimplex.mem_range_toFun_comp_weights_iff]
      constructor
      · rintro ⟨⟨_, hsum⟩, _⟩
        rw [Finset.sum_eq_single i₀ (fun j _ hj => (hj (Subsingleton.elim j i₀)).elim)
          (by simp)] at hsum
        exact funext fun j => Subsingleton.elim j i₀ ▸ hsum
      · rintro rfl
        refine ⟨⟨fun _ => zero_le_one, ?_⟩, fun _ => zero_lt_one⟩
        rw [Finset.sum_eq_single i₀ (fun j _ hj => (hj (Subsingleton.elim j i₀)).elim) (by simp)]
    rw [hm1, hsing]
    exact (nashOnSubmanifold_const (fun _ : Unit => stdSimplexExtension α g (fun _ => 1))
      (isAnalyticSubmanifold_singleton _) (isSemialgebraic_singleton _)).congr
      fun x hx => by rw [mem_singleton_iff.1 hx]

/-- **Nashness of the rational simplex extension on the open simplex.** For any `m : ℕ`, if the
boundary data `g` restrict to a Nash map in dimension `m - 2` on each open facet
`{y ∈ range weights | y i = 0 ∧ ∀ j ≠ i, 0 < y j}` of the standard simplex in `Fin m → ℝ`
(requiring no regularity on faces of codimension at least two), then `stdSimplexExtension α g` is
a Nash map in dimension `m - 1` on the open standard simplex
`{x ∈ range weights | ∀ i, 0 < x i}`. -/
theorem nashOnSubmanifold_stdSimplexExtension {m : ℕ} {g : (Fin m → ℝ) → ℝ} (α : ℝ)
    (hg : ∀ i : Fin m, NashOnSubmanifold (m - 2) (fun x (_ : Unit) => g x)
      {y ∈ range fun s : StdSimplex ℝ (Fin m) => ⇑s.weights | y i = 0 ∧ ∀ j ≠ i, 0 < y j}) :
    NashOnSubmanifold (m - 1) (fun x (_ : Unit) => stdSimplexExtension α g x)
      {x ∈ range fun s : StdSimplex ℝ (Fin m) => ⇑s.weights | ∀ i, 0 < x i} := by
  rcases subsingleton_or_nontrivial (Fin m) with _ | _
  · exact nashOnSubmanifold_stdSimplexExtension_of_subsingleton α
  · set U : Set (Fin m → ℝ) :=
      {x ∈ range fun s : StdSimplex ℝ (Fin m) => ⇑s.weights | ∀ i, 0 < x i}
    have : NeZero m := ⟨by rintro rfl; exact not_subsingleton (Fin 0) inferInstance⟩
    have hM : IsAnalyticSubmanifold (m - 1) U := isAnalyticSubmanifold_openStdSimplex
    have hS : IsSemialgebraic U := isSemialgebraic_openStdSimplex
    have hinv (i : Fin m) : NashOnSubmanifold (m - 1) (fun x (_ : Unit) => (x i)⁻¹) U := by
      refine ((nashOnSubmanifold_eval (fun _ : Unit => (X i : MvPolynomial (Fin m) ℝ)) hM hS).inv
        fun x hx _ => by simpa using (hx.2 i).ne').congr fun x _ => ?_
      ext
      simp
    have hgp (i : Fin m) :
        NashOnSubmanifold (m - 1) (fun x (_ : Unit) => g (stdSimplexFacetProjection i x)) U :=
      (hg i).comp (nashOnSubmanifold_stdSimplexFacetProjection i)
        fun x hx => stdSimplexFacetProjection_mem_openStdSimplexFacet hx.1 hx.2 i
    have hnum : NashOnSubmanifold (m - 1)
        (fun x (_ : Unit) => α + ∑ i : Fin m, (x i)⁻¹ * g (stdSimplexFacetProjection i x)) U :=
      ((nashOnSubmanifold_const (fun _ : Unit => α) hM hS).add
        (Finset.univ.nashOnSubmanifold_sum hM hS fun i _ => (hinv i).mul (hgp i))).congr
        fun x _ => by ext; simp [Finset.sum_apply]
    have hden : NashOnSubmanifold (m - 1) (fun x (_ : Unit) => 1 + ∑ i : Fin m, (x i)⁻¹) U :=
      ((nashOnSubmanifold_const (fun _ : Unit => (1 : ℝ)) hM hS).add
        (Finset.univ.nashOnSubmanifold_sum hM hS fun i _ => hinv i)).congr
        fun x _ => by ext; simp [Finset.sum_apply]
    refine (hnum.div hden fun x hx _ =>
      (one_add_sum_inv_pos fun i _ => (hx.2 i).le).ne').congr fun x hx => ?_
    ext
    exact (stdSimplexExtension_of_forall_pos hx.2).symm

end Extension

/-! ### Semialgebraicity and Nashness of `stdSimplexGapExtension` -/

section GapExtension

/-- **Semialgebraicity of gap-height extensions.** If `a` and `b` are semialgebraic on the closed
standard simplex (`Fintype ι`) and `c` is semialgebraic on `stdSimplexBoundary ι`, then
`stdSimplexGapExtension a b c α` is semialgebraic on the closed standard simplex. No non-collapse
hypothesis on `a` and `b` is needed. -/
theorem isSemialgebraicOn_stdSimplexGapExtension {ι : Type*} [Fintype ι] [DecidableEq ι]
    {a b c : (ι → ℝ) → ℝ} (α : ℝ)
    (ha : IsSemialgebraicOn (fun x (_ : Unit) => a x) (range fun s : StdSimplex ℝ ι => ⇑s.weights))
    (hb : IsSemialgebraicOn (fun x (_ : Unit) => b x) (range fun s : StdSimplex ℝ ι => ⇑s.weights))
    (hc : IsSemialgebraicOn (fun x (_ : Unit) => c x) (stdSimplexBoundary ι)) :
    IsSemialgebraicOn (fun x (_ : Unit) => stdSimplexGapExtension a b c α x)
      (range fun s : StdSimplex ℝ ι => ⇑s.weights) := by
  have haB := ha.mono isSemialgebraic_stdSimplexBoundary stdSimplexBoundary_subset
  have hbB := hb.mono isSemialgebraic_stdSimplexBoundary stdSimplexBoundary_subset
  have hr : IsSemialgebraicOn (fun y (_ : Unit) => (c y - a y) / (b y - a y))
      (stdSimplexBoundary ι) :=
    ((hc.sub haB).div (hbB.sub haB)).congr fun y _ => by ext; simp
  exact (ha.add ((hb.sub ha).mul (isSemialgebraicOn_stdSimplexExtension α hr))).congr
    fun x _ => by ext; simp [stdSimplexGapExtension_def]

/-- **Nashness of gap-height extensions on the open simplex.** Let `a` and `b` be Nash functions in
dimension `m - 1` on the open standard simplex in `Fin m → ℝ`, and on each open facet
`{y ∈ range weights | y i = 0 ∧ ∀ j ≠ i, 0 < y j}` let `a`, `b`, and `c` be Nash functions in
dimension `m - 2` with `a y ≠ b y`. Then `stdSimplexGapExtension a b c α` is a Nash function in
dimension `m - 1` on the open standard simplex; the gap `a ≤ b` may collapse on faces of
codimension at least two as well as inside the open simplex. -/
theorem nashOnSubmanifold_stdSimplexGapExtension {m : ℕ} {a b c : (Fin m → ℝ) → ℝ} (α : ℝ)
    (ha : NashOnSubmanifold (m - 1) (fun x (_ : Unit) => a x)
      {x ∈ range fun s : StdSimplex ℝ (Fin m) => ⇑s.weights | ∀ i, 0 < x i})
    (hb : NashOnSubmanifold (m - 1) (fun x (_ : Unit) => b x)
      {x ∈ range fun s : StdSimplex ℝ (Fin m) => ⇑s.weights | ∀ i, 0 < x i})
    (haf : ∀ i : Fin m, NashOnSubmanifold (m - 2) (fun y (_ : Unit) => a y)
      {y ∈ range fun s : StdSimplex ℝ (Fin m) => ⇑s.weights | y i = 0 ∧ ∀ j ≠ i, 0 < y j})
    (hbf : ∀ i : Fin m, NashOnSubmanifold (m - 2) (fun y (_ : Unit) => b y)
      {y ∈ range fun s : StdSimplex ℝ (Fin m) => ⇑s.weights | y i = 0 ∧ ∀ j ≠ i, 0 < y j})
    (hcf : ∀ i : Fin m, NashOnSubmanifold (m - 2) (fun y (_ : Unit) => c y)
      {y ∈ range fun s : StdSimplex ℝ (Fin m) => ⇑s.weights | y i = 0 ∧ ∀ j ≠ i, 0 < y j})
    (hne : ∀ (i : Fin m),
      ∀ y ∈ {y ∈ range fun s : StdSimplex ℝ (Fin m) => ⇑s.weights | y i = 0 ∧ ∀ j ≠ i, 0 < y j},
        a y ≠ b y) :
    NashOnSubmanifold (m - 1) (fun x (_ : Unit) => stdSimplexGapExtension a b c α x)
      {x ∈ range fun s : StdSimplex ℝ (Fin m) => ⇑s.weights | ∀ i, 0 < x i} := by
  have hr (i : Fin m) : NashOnSubmanifold (m - 2) (fun y (_ : Unit) => (c y - a y) / (b y - a y))
      {y ∈ range fun s : StdSimplex ℝ (Fin m) => ⇑s.weights | y i = 0 ∧ ∀ j ≠ i, 0 < y j} :=
    (((hcf i).sub (haf i)).div ((hbf i).sub (haf i))
      fun y hy _ => sub_ne_zero.2 (hne i y hy).symm).congr fun y _ => by ext; simp
  exact (ha.add ((hb.sub ha).mul (nashOnSubmanifold_stdSimplexExtension α hr))).congr
    fun x _ => by ext; simp [stdSimplexGapExtension_def]

end GapExtension

end TauCeti
