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
   `TauCeti.stdSimplexBoundary ℝ ι`, then `stdSimplexExtension α g` is semialgebraic on the whole
   closed standard simplex (`TauCeti.isSemialgebraicOn_stdSimplexExtension`); likewise, if `a` and
   `b` are semialgebraic on the closed standard simplex and `c` is semialgebraic on its boundary,
   then `stdSimplexGapExtension a b c α` is semialgebraic on the closed standard simplex without
   any non-collapse hypothesis (`TauCeti.isSemialgebraicOn_stdSimplexGapExtension`).
2. **Nashness on the open simplex:** for every `m : ℕ`, if `g` is a Nash function in dimension
   `m - 2` on each open facet `TauCeti.openStdSimplexFacet ℝ i` of the standard simplex in
   `Fin m → ℝ` (with no regularity required on faces of codimension at least two), then
   `stdSimplexExtension α g` is a Nash function in dimension `m - 1` on the open standard simplex
   `TauCeti.openStdSimplex ℝ (Fin m)` (`TauCeti.nashOnSubmanifold_stdSimplexExtension`).
   Consequently, if `a` and `b` are Nash on `TauCeti.openStdSimplex ℝ (Fin m)` and `a`, `b`, `c`
   are Nash on each open facet `TauCeti.openStdSimplexFacet ℝ i` with `a ≠ b` on open facets —
   allowing the gap `a ≤ b` to collapse on faces of codimension at least two as well as inside the
   open simplex — then `stdSimplexGapExtension a b c α` is Nash in dimension `m - 1` on
   `TauCeti.openStdSimplex ℝ (Fin m)` (`TauCeti.nashOnSubmanifold_stdSimplexGapExtension`).

To transport Nash regularity between `TauCeti.openStdSimplex ℝ (Fin m)` and an arbitrary open
geometric simplex `intrinsicInterior ℝ (convexHull ℝ (range p))` in `Fin n → ℝ`, we also
characterize Nash maps on an open geometric simplex via pullback along `w ↦ ∑ i, w i • p i` to the
open standard simplex (`AffineIndependent.nashOnSubmanifold_intrinsicInterior_convexHull_iff`).

## Main results

* `AffineIndependent.nashOnSubmanifold_intrinsicInterior_convexHull_iff`: a map on an open
  geometric simplex is Nash if and only if its barycentric pullback to the open standard simplex is
  Nash.
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

/-! ### Barycentric characterization of Nash maps on open simplices -/

section Barycentric

variable {n m : ℕ} {τ : Type*} [Fintype τ]

/-- **Barycentric characterization of Nash maps on an open simplex.** For `m ≥ 1` and affinely
independent vertices `p : Fin m → Fin n → ℝ`, a map `g : (Fin n → ℝ) → τ → ℝ` is Nash in dimension
`m - 1` on `intrinsicInterior ℝ (convexHull ℝ (range p))` if and only if its barycentric pullback
`w ↦ g (∑ i, w i • p i)` is Nash in dimension `m - 1` on `TauCeti.openStdSimplex ℝ (Fin m)`. -/
theorem AffineIndependent.nashOnSubmanifold_intrinsicInterior_convexHull_iff [NeZero m]
    {p : Fin m → Fin n → ℝ} (hp : AffineIndependent ℝ p) {g : (Fin n → ℝ) → τ → ℝ} :
    TauCeti.NashOnSubmanifold (m - 1) g (intrinsicInterior ℝ (convexHull ℝ (range p))) ↔
      TauCeti.NashOnSubmanifold (m - 1) (fun w : Fin m → ℝ => g (∑ i, w i • p i))
        (TauCeti.openStdSimplex ℝ (Fin m)) := by
  constructor
  · intro hg
    exact (hg.comp
      ((Fintype.linearCombination ℝ p).toAffineMap.nashOnSubmanifold
        TauCeti.isAnalyticSubmanifold_openStdSimplex
        TauCeti.isSemialgebraic_openStdSimplex)
      fun w hw => hp.intrinsicInterior_convexHull_eq_image_sum_smul ▸ mem_image_of_mem _ hw).congr
      fun _ _ => congrArg g (Fintype.linearCombination_apply ℝ p _)
  · intro hgw
    obtain ⟨B, -, hclosed, hopen⟩ := hp.exists_affineMap_barycentricCoord
    have hM : TauCeti.IsAnalyticSubmanifold (m - 1)
        (intrinsicInterior ℝ (convexHull ℝ (range p))) := by
      simpa using hp.isAnalyticSubmanifold_intrinsicInterior_convexHull
    exact (hgw.comp (B.nashOnSubmanifold hM hp.isSemialgebraic_intrinsicInterior_convexHull)
      hopen).congr fun x hx => congrArg g (hclosed x (intrinsicInterior_subset hx)).2

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
  refine (hnum.div hden).congr fun x => funext fun j => ?_
  rcases eq_or_ne j i with rfl | hj
  · simp
  · simp [hj]

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
`m - 1` on `openStdSimplex ℝ (Fin m)`. -/
theorem nashOnSubmanifold_stdSimplexFacetProjection {m : ℕ} [Nontrivial (Fin m)] (i : Fin m) :
    NashOnSubmanifold (m - 1) (stdSimplexFacetProjection i) (openStdSimplex ℝ (Fin m)) := by
  have : NeZero m := i.neZero
  obtain ⟨k, hk⟩ := exists_ne i
  exact nashOnSubmanifold_stdSimplexFacetProjection_of_ne_one i
    isAnalyticSubmanifold_openStdSimplex isSemialgebraic_openStdSimplex
    fun x hx =>
      let hx' := mem_openStdSimplex_iff.1 hx
      (StdSimplex.apply_lt_one_of_mem_range_weights hx'.1 hk (hx'.2 k)).ne

end FacetProjection

/-! ### Semialgebraicity and Nashness of `stdSimplexExtension` -/

section Extension

private theorem isSemialgebraicOn_stdSimplexExtension_of_subsingleton {ι : Type*} [Fintype ι]
    [DecidableEq ι] [Subsingleton ι] {g : (ι → ℝ) → ℝ} (α : ℝ) :
    IsSemialgebraicOn (fun x (_ : Unit) => stdSimplexExtension α g x)
      (range fun s : StdSimplex ℝ ι => ⇑s.weights) := by
  rcases isEmpty_or_nonempty ι with _ | ⟨⟨i₀⟩⟩
  · simp
  · have : Unique ι := uniqueOfSubsingleton i₀
    rw [StdSimplex.range_toFun_comp_weights_of_unique]
    exact (isSemialgebraicOn_const (fun _ : Unit => stdSimplexExtension α g (fun _ => 1))
      (isSemialgebraic_singleton _)).congr fun x hx => by rw [mem_singleton_iff.1 hx]

/-- **Semialgebraicity of the rational simplex extension.** If `g` is semialgebraic on the
relative boundary `stdSimplexBoundary ℝ ι` of the standard simplex (`Fintype ι`), then
`stdSimplexExtension α g` is semialgebraic on the whole closed standard simplex. -/
theorem isSemialgebraicOn_stdSimplexExtension {ι : Type*} [Fintype ι] [DecidableEq ι]
    {g : (ι → ℝ) → ℝ} (α : ℝ)
    (hg : IsSemialgebraicOn (fun x (_ : Unit) => g x) (stdSimplexBoundary ℝ ι)) :
    IsSemialgebraicOn (fun x (_ : Unit) => stdSimplexExtension α g x)
      (range fun s : StdSimplex ℝ ι => ⇑s.weights) := by
  rcases subsingleton_or_nontrivial ι with _ | _
  · exact isSemialgebraicOn_stdSimplexExtension_of_subsingleton α
  · set Δ : Set (ι → ℝ) := range fun s : StdSimplex ℝ ι => ⇑s.weights
    set P : Set (ι → ℝ) := {x | ∀ i, 0 < x i}
    have hbdry : Δ \ P = stdSimplexBoundary ℝ ι := by
      ext x
      simp only [Set.mem_sdiff, P, mem_ofPred_eq, mem_stdSimplexBoundary, Δ]
      refine ⟨fun ⟨hx, hnot⟩ =>
        mem_stdSimplexBoundary.1 ((mem_stdSimplexBoundary_or_forall_pos hx).resolve_right hnot),
        fun ⟨hx, i, hi⟩ => ⟨hx, fun h => (h i).ne' hi⟩⟩
    have hopen : Δ ∩ P = openStdSimplex ℝ ι := by
      ext x
      simp [Δ, P]
    have hS : IsSemialgebraic (Δ ∩ P) := hopen ▸ isSemialgebraic_openStdSimplex
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
    [Subsingleton (Fin m)] {g : (Fin m → ℝ) → ℝ} (α : ℝ) :
    NashOnSubmanifold (m - 1) (fun x (_ : Unit) => stdSimplexExtension α g x)
      (openStdSimplex ℝ (Fin m)) := by
  rcases eq_zero_or_neZero m with rfl | _
  · rw [openStdSimplex_of_isEmpty]
    exact ⟨analyticOnSubmanifold_iff.2 (by simp), isSemialgebraicOn_empty _⟩
  · have : Unique (Fin m) := uniqueOfSubsingleton 0
    have hm1 : m - 1 = 0 := by
      have hm : m = 1 := (Fintype.card_fin m).symm.trans Fintype.card_unique
      omega
    rw [hm1, openStdSimplex_of_unique]
    exact (nashOnSubmanifold_const (fun _ : Unit => stdSimplexExtension α g (fun _ => 1))
      (isAnalyticSubmanifold_singleton _) (isSemialgebraic_singleton _)).congr
      fun x hx => by rw [mem_singleton_iff.1 hx]

/-- **Nashness of the rational simplex extension on the open simplex.** For any `m : ℕ`, if the
boundary data `g` restrict to a Nash map in dimension `m - 2` on each open facet
`openStdSimplexFacet ℝ i` of the standard simplex in `Fin m → ℝ` (requiring no regularity on faces
of codimension at least two), then `stdSimplexExtension α g` is a Nash map in dimension `m - 1` on
`openStdSimplex ℝ (Fin m)`. -/
theorem nashOnSubmanifold_stdSimplexExtension {m : ℕ} {g : (Fin m → ℝ) → ℝ} (α : ℝ)
    (hg : ∀ i : Fin m, NashOnSubmanifold (m - 2) (fun x (_ : Unit) => g x)
      (openStdSimplexFacet ℝ i)) :
    NashOnSubmanifold (m - 1) (fun x (_ : Unit) => stdSimplexExtension α g x)
      (openStdSimplex ℝ (Fin m)) := by
  rcases subsingleton_or_nontrivial (Fin m) with _ | _
  · exact nashOnSubmanifold_stdSimplexExtension_of_subsingleton α
  · set U : Set (Fin m → ℝ) := openStdSimplex ℝ (Fin m)
    have : NeZero m := Nonempty.elim inferInstance Fin.neZero
    have hM : IsAnalyticSubmanifold (m - 1) U := isAnalyticSubmanifold_openStdSimplex
    have hS : IsSemialgebraic U := isSemialgebraic_openStdSimplex
    have hinv (i : Fin m) : NashOnSubmanifold (m - 1) (fun x (_ : Unit) => (x i)⁻¹) U := by
      refine ((nashOnSubmanifold_eval (fun _ : Unit => (X i : MvPolynomial (Fin m) ℝ)) hM hS).inv
        fun x hx _ => by simpa using ((mem_openStdSimplex_iff.1 hx).2 i).ne').congr fun x _ => ?_
      ext
      simp
    have hgp (i : Fin m) :
        NashOnSubmanifold (m - 1) (fun x (_ : Unit) => g (stdSimplexFacetProjection i x)) U :=
      (hg i).comp (nashOnSubmanifold_stdSimplexFacetProjection i)
        fun x hx =>
          let hx' := mem_openStdSimplex_iff.1 hx
          stdSimplexFacetProjection_mem_openStdSimplexFacet hx'.1 fun j _ => hx'.2 j
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
      (one_add_sum_inv_pos fun i _ => ((mem_openStdSimplex_iff.1 hx).2 i).le).ne').congr
      fun x hx => ?_
    ext
    exact (stdSimplexExtension_of_forall_pos (mem_openStdSimplex_iff.1 hx).2).symm

end Extension

/-! ### Semialgebraicity and Nashness of `stdSimplexGapExtension` -/

section GapExtension

/-- **Semialgebraicity of gap-height extensions.** If `a` and `b` are semialgebraic on the closed
standard simplex (`Fintype ι`) and `c` is semialgebraic on `stdSimplexBoundary ℝ ι`, then
`stdSimplexGapExtension a b c α` is semialgebraic on the closed standard simplex. No non-collapse
hypothesis on `a` and `b` is needed. -/
theorem isSemialgebraicOn_stdSimplexGapExtension {ι : Type*} [Fintype ι] [DecidableEq ι]
    {a b c : (ι → ℝ) → ℝ} (α : ℝ)
    (ha : IsSemialgebraicOn (fun x (_ : Unit) => a x) (range fun s : StdSimplex ℝ ι => ⇑s.weights))
    (hb : IsSemialgebraicOn (fun x (_ : Unit) => b x) (range fun s : StdSimplex ℝ ι => ⇑s.weights))
    (hc : IsSemialgebraicOn (fun x (_ : Unit) => c x) (stdSimplexBoundary ℝ ι)) :
    IsSemialgebraicOn (fun x (_ : Unit) => stdSimplexGapExtension a b c α x)
      (range fun s : StdSimplex ℝ ι => ⇑s.weights) := by
  have haB := ha.mono isSemialgebraic_stdSimplexBoundary stdSimplexBoundary_subset
  have hbB := hb.mono isSemialgebraic_stdSimplexBoundary stdSimplexBoundary_subset
  have hr : IsSemialgebraicOn (fun y (_ : Unit) => (c y - a y) / (b y - a y))
      (stdSimplexBoundary ℝ ι) :=
    ((hc.sub haB).div (hbB.sub haB)).congr fun y _ => by ext; simp
  exact (ha.add ((hb.sub ha).mul (isSemialgebraicOn_stdSimplexExtension α hr))).congr
    fun x _ => by ext; simp [stdSimplexGapExtension_def]

/-- **Nashness of gap-height extensions on the open simplex.** Let `a` and `b` be Nash functions in
dimension `m - 1` on `openStdSimplex ℝ (Fin m)`, and on each open facet `openStdSimplexFacet ℝ i`
let `a`, `b`, and `c` be Nash functions in dimension `m - 2` with `a y ≠ b y`. Then
`stdSimplexGapExtension a b c α` is a Nash function in dimension `m - 1` on
`openStdSimplex ℝ (Fin m)`; the gap `a ≤ b` may collapse on faces of codimension at least two as
well as inside the open simplex. -/
theorem nashOnSubmanifold_stdSimplexGapExtension {m : ℕ} {a b c : (Fin m → ℝ) → ℝ} (α : ℝ)
    (ha : NashOnSubmanifold (m - 1) (fun x (_ : Unit) => a x) (openStdSimplex ℝ (Fin m)))
    (hb : NashOnSubmanifold (m - 1) (fun x (_ : Unit) => b x) (openStdSimplex ℝ (Fin m)))
    (haf : ∀ i : Fin m, NashOnSubmanifold (m - 2) (fun y (_ : Unit) => a y)
      (openStdSimplexFacet ℝ i))
    (hbf : ∀ i : Fin m, NashOnSubmanifold (m - 2) (fun y (_ : Unit) => b y)
      (openStdSimplexFacet ℝ i))
    (hcf : ∀ i : Fin m, NashOnSubmanifold (m - 2) (fun y (_ : Unit) => c y)
      (openStdSimplexFacet ℝ i))
    (hne : ∀ (i : Fin m), ∀ y ∈ openStdSimplexFacet ℝ i, a y ≠ b y) :
    NashOnSubmanifold (m - 1) (fun x (_ : Unit) => stdSimplexGapExtension a b c α x)
      (openStdSimplex ℝ (Fin m)) := by
  have hr (i : Fin m) : NashOnSubmanifold (m - 2) (fun y (_ : Unit) => (c y - a y) / (b y - a y))
      (openStdSimplexFacet ℝ i) :=
    (((hcf i).sub (haf i)).div ((hbf i).sub (haf i))
      fun y hy _ => sub_ne_zero.2 (hne i y hy).symm).congr fun y _ => by ext; simp
  exact (ha.add ((hb.sub ha).mul (nashOnSubmanifold_stdSimplexExtension α hr))).congr
    fun x _ => by ext; simp [stdSimplexGapExtension_def]

end GapExtension

end TauCeti
