/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.SimplicialComplex.Realization.SimplicialApproximation
public import TauCeti.AlgebraicTopology.SimplicialComplex.Subdivision.Homeomorph
import Mathlib.Analysis.SpecificLimits.Basic
import TauCeti.Algebra.Order.BigOperators.Sum.CommonLowerBound
import TauCeti.AlgebraicTopology.SimplicialComplex.Realization.Finite
import TauCeti.Order.Chain

/-!
# Iterated barycentric subdivisions and the simplicial approximation theorem

The `n`-th iterated barycentric subdivision `sd^n K` of an abstract simplicial complex `K`
(`AbstractSimplicialComplex.iteratedBarycentricSubdivision`) is obtained by subdividing `n` times;
its vertices after one more step are the faces of `sd^n K`. Composing the canonical subdivision
homeomorphisms `|sd L| ≃ₜ |L|` gives the canonical homeomorphism `b_n : |sd^n K| ≃ₜ |K|`
(`AbstractSimplicialComplex.iteratedBarycentricSubdivisionRealizationHomeomorph`), which sends each
new vertex to the barycenter of the face it stands for and is affine on every simplex of `sd^n K`.
It maps the closed simplex of every face of `sd^n K` into the closed simplex of a face of `K`
(`exists_support_iteratedBarycentricSubdivisionRealizationHomeomorph_subset`).

**The simplices become small.** Measure points of `|K|` by the `ℓ¹` distance of their barycentric
coordinates, and suppose every face of `K` has at most `D` vertices. Two points of one closed
simplex of `sd L`, a chain `τ₁ ⊂ ⋯ ⊂ τₖ` of faces of `L`, have images
`∑ᵢ xᵢ b(τᵢ)` and `∑ᵢ yᵢ b(τᵢ)`, where `b(τ)` is the barycenter of `τ`. Every `b(τᵢ)` gives weight
at least `1 / D` to a vertex `v₀` of the smallest face `τ₁`. Since `∑ᵢ (xᵢ - yᵢ) = 0`, this common
weight cancels from the difference, and what remains of each `b(τᵢ)` has total weight
`1 - 1 / D`; so one subdivision step contracts `ℓ¹` distances within a closed simplex by the
factor `1 - 1 / D`. This is the contraction argument for stochastic matrices with a common column
bound (Doeblin's condition, `TauCeti.sum_abs_sum_mul_le`). Subdivision does not increase the
number of vertices of a face
(`TauCeti.PreAbstractSimplicialComplex.card_le_of_mem_barycentricSubdivision`), so after `n` steps
the factor is `(1 - 1 / D) ^ n`. The open star of a vertex `w` of `sd^n K` consists of points
whose closed simplex contains `w`, so its image under `b_n` lies within `ℓ¹` distance
`2 (1 - 1 / D) ^ n` of the image of `w`.

For a complex with finitely many faces the realization `|K|` is compact
(`AbstractSimplicialComplex.compactSpace_realization_of_finite_faces`), and its barycentric
coordinates on the finite set of vertices of `K` embed it in a finite-dimensional coordinate space,
so every open cover of `|K|` has a Lebesgue number. Hence for all large `n` the image under `b_n`
of every open vertex star of `sd^n K` lies in a member of the cover
(`AbstractSimplicialComplex.eventually_forall_exists_image_openStarRealization_subset`).

**Simplicial approximation.** Applied to the cover of `|K|` by the preimages of the open vertex
stars of `|L|` under a continuous map `φ : |K| → |L|`, this is the star condition of
`PreAbstractSimplicialComplex.SimplicialMap.exists_isSimplicialApproximation_iff` for `φ ∘ b_n`.
So for all large `n` the map `φ ∘ b_n : |sd^n K| → |L|` has a simplicial approximation
`sd^n K → L` (`AbstractSimplicialComplex.eventually_exists_isSimplicialApproximation`), Hatcher's
Theorem 2C.1. Its realization is homotopic to `φ ∘ b_n`
(`PreAbstractSimplicialComplex.SimplicialMap.IsSimplicialApproximation.homotopic`).

## Main definitions

* `AbstractSimplicialComplex.iteratedBarycentricSubdivision`: the vertex type and the complex of
  the `n`-th iterated barycentric subdivision.
* `AbstractSimplicialComplex.iteratedBarycentricSubdivisionRealizationHomeomorph`: the canonical
  homeomorphism `|sd^n K| ≃ₜ |K|`.

## Main results

* `AbstractSimplicialComplex.card_le_of_mem_iteratedBarycentricSubdivision`: iterated
  subdivision does not increase the number of vertices of a face, and
  `AbstractSimplicialComplex.finite_iteratedBarycentricSubdivision_fst` and
  `AbstractSimplicialComplex.finite_faces_iteratedBarycentricSubdivision`: it keeps finitely many
  vertices or faces finite.
* `exists_support_iteratedBarycentricSubdivisionRealizationHomeomorph_subset`: `b_n` maps every
  closed simplex of `sd^n K` into a closed simplex of `K`.
* `AbstractSimplicialComplex.eventually_forall_exists_image_openStarRealization_subset`: for a
  complex with finitely many faces, the open vertex stars of `sd^n K` refine any open cover of
  `|K|` for all large `n`.
* `AbstractSimplicialComplex.eventually_exists_isSimplicialApproximation`: **the simplicial
  approximation theorem.** For a complex `K` with finitely many faces and a continuous map
  `φ : |K| → |L|`, the map `φ ∘ b_n` has a simplicial approximation `sd^n K → L` for all large `n`.

## References

* A. Hatcher, *Algebraic Topology*, Cambridge University Press 2002, Section 2.C, Theorem 2C.1
  and its proof, pp. 177–178.
* J. R. Munkres, *Elements of Algebraic Topology*, Addison–Wesley 1984, §15 and §16 (the
  subdivision lemma and the finite simplicial approximation theorem).
-/

public section

noncomputable section

open Filter Set Topology TauCeti.SetLike

namespace AbstractSimplicialComplex

universe u

attribute [local instance] Classical.decEq

variable {ι : Type u}

/-- The **iterated barycentric subdivision** `sd^n K`, as its vertex type together with the
complex on it: `sd^0 K = K`, and `sd^(n + 1) K` is the barycentric subdivision of `sd^n K`, whose
vertices are the faces of `sd^n K`. -/
@[expose] def iteratedBarycentricSubdivision (K : AbstractSimplicialComplex ι) :
    ℕ → Σ κ : Type u, AbstractSimplicialComplex κ
  | 0 => ⟨ι, K⟩
  | n + 1 =>
    ⟨TauCeti.SetLike.Face (K.iteratedBarycentricSubdivision n).2.toPreAbstractSimplicialComplex,
      TauCeti.PreAbstractSimplicialComplex.barycentricSubdivision
        (K.iteratedBarycentricSubdivision n).2.toPreAbstractSimplicialComplex⟩

variable (K : AbstractSimplicialComplex ι)

@[simp]
theorem iteratedBarycentricSubdivision_zero : K.iteratedBarycentricSubdivision 0 = ⟨ι, K⟩ :=
  (rfl)

theorem iteratedBarycentricSubdivision_succ (n : ℕ) :
    K.iteratedBarycentricSubdivision (n + 1) =
      ⟨TauCeti.SetLike.Face (K.iteratedBarycentricSubdivision n).2.toPreAbstractSimplicialComplex,
        TauCeti.PreAbstractSimplicialComplex.barycentricSubdivision
          (K.iteratedBarycentricSubdivision n).2.toPreAbstractSimplicialComplex⟩ :=
  (rfl)

/-- The canonical homeomorphism `|sd^n K| ≃ₜ |K|`, the composite of the subdivision
homeomorphisms `barycentricSubdivisionRealizationHomeomorph` of the successive subdivisions. It
sends a vertex of `sd^(n + 1) K`, a face of `sd^n K`, to the image of the barycenter of that
face. -/
def iteratedBarycentricSubdivisionRealizationHomeomorph (K : AbstractSimplicialComplex ι) :
    (n : ℕ) → Realization (K.iteratedBarycentricSubdivision n).2 ≃ₜ Realization K
  | 0 => Homeomorph.refl _
  | n + 1 => (barycentricSubdivisionRealizationHomeomorph
      (K.iteratedBarycentricSubdivision n).2).trans
        (K.iteratedBarycentricSubdivisionRealizationHomeomorph n)

@[simp]
theorem iteratedBarycentricSubdivisionRealizationHomeomorph_zero_apply (x : Realization K) :
    K.iteratedBarycentricSubdivisionRealizationHomeomorph 0 x = x :=
  (rfl)

@[simp]
theorem iteratedBarycentricSubdivisionRealizationHomeomorph_succ_apply (n : ℕ)
    (x : Realization (K.iteratedBarycentricSubdivision (n + 1)).2) :
    K.iteratedBarycentricSubdivisionRealizationHomeomorph (n + 1) x =
      K.iteratedBarycentricSubdivisionRealizationHomeomorph n
        (barycentricSubdivisionRealizationMap (K.iteratedBarycentricSubdivision n).2 x) :=
  congrArg (K.iteratedBarycentricSubdivisionRealizationHomeomorph n)
    (barycentricSubdivisionRealizationHomeomorph_apply _ x)

/-- The iterated barycentric subdivisions of a finite complex are finite. -/
instance finite_iteratedBarycentricSubdivision_fst [Finite ι] (n : ℕ) :
    Finite (K.iteratedBarycentricSubdivision n).1 := by
  induction n with
  | zero => exact ‹Finite ι›
  | succ n ih =>
    have := Fintype.ofFinite (K.iteratedBarycentricSubdivision n).1
    exact Subtype.finite

/-- The iterated barycentric subdivisions of a complex with finitely many faces have finitely many
faces. -/
theorem finite_faces_iteratedBarycentricSubdivision (hfin : K.faces.Finite) (n : ℕ) :
    (K.iteratedBarycentricSubdivision n).2.faces.Finite := by
  induction n with
  | zero => exact hfin
  | succ n ih =>
    have : Finite (K.iteratedBarycentricSubdivision (n + 1)).1 := ih.to_subtype
    have := Fintype.ofFinite (K.iteratedBarycentricSubdivision (n + 1)).1
    exact Set.toFinite _

variable {K}

/-- Iterated barycentric subdivision does not increase the number of vertices of a face: if every
face of `K` has at most `D` vertices, so does every face of `sd^n K`. -/
theorem card_le_of_mem_iteratedBarycentricSubdivision {D : ℕ} (hD : ∀ σ ∈ K, σ.card ≤ D)
    (n : ℕ) {σ : Finset (K.iteratedBarycentricSubdivision n).1}
    (hσ : σ ∈ (K.iteratedBarycentricSubdivision n).2) : σ.card ≤ D := by
  induction n with
  | zero => exact hD σ hσ
  | succ n ih =>
    exact TauCeti.PreAbstractSimplicialComplex.card_le_of_mem_barycentricSubdivision
      (fun τ hτ => ih hτ) hσ

/-! ### Contraction of the `ℓ¹` distance -/

/-- The `ℓ¹` distance between two finitely supported coordinate vectors. -/
private def l1Dist {κ : Type*} (x y : κ →₀ ℝ) : ℝ :=
  (x - y).sum fun _ a => |a|

private theorem l1Dist_eq_sum_of_subset {κ : Type*} {x y : κ →₀ ℝ} {s : Finset κ}
    (hx : x.support ⊆ s) (hy : y.support ⊆ s) : l1Dist x y = ∑ v ∈ s, |x v - y v| := by
  have hs : (x - y).support ⊆ s := Finsupp.support_sub.trans (Finset.union_subset hx hy)
  rw [l1Dist, Finsupp.sum_of_support_subset _ hs _ fun _ _ => abs_zero]
  simp only [Finsupp.sub_apply]

/-- Barycentric coordinates supported on a finite set `s` are bounded in sup norm on `s` by their
`ℓ¹` distance. -/
private theorem norm_restrict_sub_le_l1Dist {κ : Type*} {s : Finset κ} {x y : κ →₀ ℝ}
    (hx : x.support ⊆ s) (hy : y.support ⊆ s) :
    ‖(fun v : s => x v) - fun v : s => y v‖ ≤ l1Dist x y := by
  rw [l1Dist_eq_sum_of_subset hx hy]
  refine (pi_norm_le_iff_of_nonneg (Finset.sum_nonneg fun _ _ => abs_nonneg _)).2 fun v => ?_
  rw [Pi.sub_apply, Real.norm_eq_abs]
  exact Finset.single_le_sum (f := fun v => |x v - y v|) (fun _ _ => abs_nonneg _) v.property

/-- The barycentric coordinates of a point sum to one over every set containing its support. -/
private theorem sum_eq_one_of_support_subset {κ : Type*} {L : AbstractSimplicialComplex κ}
    (z : Realization L) {s : Finset κ} (hz : z.val.support ⊆ s) : ∑ v ∈ s, z.val v = 1 := by
  rw [← Realization.sum_eq_one L z, Finsupp.sum_of_support_subset _ hz _ fun _ _ => rfl]

/-- Two points of a realization are at `ℓ¹` distance at most `2`. -/
private theorem l1Dist_le_two {κ : Type*} {L : AbstractSimplicialComplex κ}
    (x y : Realization L) : l1Dist x.val y.val ≤ 2 := by
  have hsum (z : Realization L) (hz : z.val.support ⊆ x.val.support ∪ y.val.support) :
      ∑ v ∈ x.val.support ∪ y.val.support, z.val v = 1 :=
    sum_eq_one_of_support_subset z hz
  rw [l1Dist_eq_sum_of_subset Finset.subset_union_left Finset.subset_union_right]
  calc ∑ v ∈ x.val.support ∪ y.val.support, |x.val v - y.val v|
      ≤ ∑ v ∈ x.val.support ∪ y.val.support, (x.val v + y.val v) :=
        Finset.sum_le_sum fun v _ => (abs_sub _ _).trans (by
          rw [abs_of_nonneg (Realization.nonneg L x v), abs_of_nonneg (Realization.nonneg L y v)])
    _ = 2 := by
        rw [Finset.sum_add_distrib, hsum x Finset.subset_union_left,
          hsum y Finset.subset_union_right]
        norm_num

/-- The coordinates of the image in `|L|` of a point of the closed simplex of `sd L` spanned by
`ρ`: the weighted sum of the coordinates of the barycenters of the faces in `ρ`. -/
private theorem barycentricSubdivisionRealizationMap_apply_eq_sum {κ : Type*}
    {L : AbstractSimplicialComplex κ}
    {ρ : Finset (TauCeti.SetLike.Face L.toPreAbstractSimplicialComplex)}
    {z : Realization (TauCeti.PreAbstractSimplicialComplex.barycentricSubdivision
      L.toPreAbstractSimplicialComplex)} (hz : z.val.support ⊆ ρ) (v : κ) :
    (barycentricSubdivisionRealizationMap L z).val v =
      ∑ τ ∈ ρ, z.val τ * if v ∈ τ.val then (τ.val.card : ℝ)⁻¹ else 0 := by
  rw [barycentricSubdivisionRealizationMap_val, barycentricSubdivisionLinearMap_apply]
  exact Finset.sum_subset hz fun τ _ hτ => by simp [Finsupp.notMem_support_iff.mp hτ]

/-- The coordinates of the barycenter of a face `τ` sum to one over every set containing `τ`. -/
private theorem sum_ite_mem_inv_card {κ : Type*} {L : AbstractSimplicialComplex κ}
    {τ : TauCeti.SetLike.Face L.toPreAbstractSimplicialComplex} {σ : Finset κ}
    (hτσ : τ.val ⊆ σ) : ∑ v ∈ σ, (if v ∈ τ.val then (τ.val.card : ℝ)⁻¹ else 0) = 1 := by
  have hcard : (τ.val.card : ℝ) ≠ 0 := by
    exact_mod_cast (Finset.card_pos.mpr (L.isRelLowerSet_faces.prop_of_mem τ.property)).ne'
  rw [Finset.sum_ite_mem, Finset.inter_eq_right.mpr hτσ, Finset.sum_const, nsmul_eq_mul,
    mul_inv_cancel₀ hcard]

/-- The image in `|L|` of the closed simplex of `sd L` spanned by `ρ` lies in the closed simplex
of every set `σ` containing all faces in `ρ`. -/
private theorem support_barycentricSubdivisionRealizationMap_subset {κ : Type*}
    {L : AbstractSimplicialComplex κ}
    {ρ : Finset (TauCeti.SetLike.Face L.toPreAbstractSimplicialComplex)} {σ : Finset κ}
    (hρσ : ∀ τ ∈ ρ, τ.val ⊆ σ)
    {z : Realization (TauCeti.PreAbstractSimplicialComplex.barycentricSubdivision
      L.toPreAbstractSimplicialComplex)} (hz : z.val.support ⊆ ρ) :
    (barycentricSubdivisionRealizationMap L z).val.support ⊆ σ := by
  intro v hv
  by_contra hvσ
  refine Finsupp.mem_support_iff.mp hv
    ((barycentricSubdivisionRealizationMap_apply_eq_sum hz v).trans
      (Finset.sum_eq_zero fun τ hτ => ?_))
  have hvτ : v ∉ τ.val := fun h => hvσ (hρσ τ hτ h)
  simp [hvτ]

/-- **The carrier of `b_n`.** The image under `b_n : |sd^n K| ≃ₜ |K|` of the closed simplex of a
face `ρ` of `sd^n K` lies in the closed simplex of some face `σ` of `K`. -/
theorem exists_support_iteratedBarycentricSubdivisionRealizationHomeomorph_subset (n : ℕ)
    {ρ : Finset (K.iteratedBarycentricSubdivision n).1}
    (hρ : ρ ∈ (K.iteratedBarycentricSubdivision n).2) :
    ∃ σ ∈ K, ∀ x : Realization (K.iteratedBarycentricSubdivision n).2, x.val.support ⊆ ρ →
      (K.iteratedBarycentricSubdivisionRealizationHomeomorph n x).val.support ⊆ σ := by
  induction n with
  | zero => exact ⟨ρ, hρ, fun _ hx => hx⟩
  | succ n ih =>
    obtain ⟨hne, hchain⟩ :=
      TauCeti.PreAbstractSimplicialComplex.mem_barycentricSubdivision_iff.mp hρ
    obtain ⟨τ, -, hτ⟩ := hchain.exists_isGreatest ρ.finite_toSet (Finset.coe_nonempty.mpr hne)
    obtain ⟨σ, hσ, hσx⟩ := ih τ.property
    refine ⟨σ, hσ, fun x hx => ?_⟩
    rw [iteratedBarycentricSubdivisionRealizationHomeomorph_succ_apply]
    exact hσx _ (support_barycentricSubdivisionRealizationMap_subset
      (fun τ' hτ' => face_le_iff.mp (hτ hτ')) hx)

/-- **One subdivision step contracts `ℓ¹` distances within a closed simplex.** Let every face of
`L` have at most `D` vertices, and let `x` and `y` be two points of the closed simplex of `sd L`
spanned by a chain `ρ` of faces of `L`. Their images in `|L|` lie in the closed simplex of the
largest face of `ρ`, and their `ℓ¹` distance is at most `1 - 1 / D` times that of `x` and `y`. -/
private theorem exists_support_subset_and_l1Dist_le {κ : Type*} {L : AbstractSimplicialComplex κ}
    {D : ℕ} (hD : ∀ σ ∈ L, σ.card ≤ D)
    {ρ : Finset (TauCeti.SetLike.Face L.toPreAbstractSimplicialComplex)}
    (hρ : ρ ∈ TauCeti.PreAbstractSimplicialComplex.barycentricSubdivision
      L.toPreAbstractSimplicialComplex)
    {x y : Realization (TauCeti.PreAbstractSimplicialComplex.barycentricSubdivision
      L.toPreAbstractSimplicialComplex)} (hx : x.val.support ⊆ ρ) (hy : y.val.support ⊆ ρ) :
    ∃ σ ∈ L, (barycentricSubdivisionRealizationMap L x).val.support ⊆ σ ∧
      (barycentricSubdivisionRealizationMap L y).val.support ⊆ σ ∧
      l1Dist (barycentricSubdivisionRealizationMap L x).val
          (barycentricSubdivisionRealizationMap L y).val ≤
        (1 - (D : ℝ)⁻¹) * l1Dist x.val y.val := by
  obtain ⟨hne, hchain⟩ :=
    TauCeti.PreAbstractSimplicialComplex.mem_barycentricSubdivision_iff.mp hρ
  obtain ⟨σ, -, hσ⟩ := hchain.exists_isGreatest ρ.finite_toSet (Finset.coe_nonempty.mpr hne)
  obtain ⟨τ₀, hτ₀, hτ₀le⟩ := hchain.exists_isLeast ρ.finite_toSet (Finset.coe_nonempty.mpr hne)
  obtain ⟨v₀, hv₀⟩ := L.isRelLowerSet_faces.prop_of_mem τ₀.property
  have hτσ {τ} (hτ : τ ∈ ρ) : τ.val ⊆ σ.val := face_le_iff.mp (hσ hτ)
  have hv₀τ {τ} (hτ : τ ∈ ρ) : v₀ ∈ τ.val := face_le_iff.mp (hτ₀le hτ) hv₀
  have hsupp {z : Realization (TauCeti.PreAbstractSimplicialComplex.barycentricSubdivision
      L.toPreAbstractSimplicialComplex)} (hz : z.val.support ⊆ ρ) :
      (barycentricSubdivisionRealizationMap L z).val.support ⊆ σ.val :=
    support_barycentricSubdivisionRealizationMap_subset (fun _ hτ => hτσ hτ) hz
  refine ⟨σ.val, σ.property, hsupp hx, hsupp hy, ?_⟩
  -- The image of a point of the simplex `ρ` is the combination of the barycenters of `ρ`.
  set β : TauCeti.SetLike.Face L.toPreAbstractSimplicialComplex → κ → ℝ :=
    fun τ v => if v ∈ τ.val then (τ.val.card : ℝ)⁻¹ else 0 with hβ
  have hcoord {z : Realization (TauCeti.PreAbstractSimplicialComplex.barycentricSubdivision
      L.toPreAbstractSimplicialComplex)} (hz : z.val.support ⊆ ρ) (v : κ) :
      (barycentricSubdivisionRealizationMap L z).val v = ∑ τ ∈ ρ, z.val τ * β τ v :=
    barycentricSubdivisionRealizationMap_apply_eq_sum hz v
  -- Every barycenter of `ρ` gives weight at least `1 / D` to `v₀`.
  set δ : κ → ℝ := fun v => if v = v₀ then (D : ℝ)⁻¹ else 0 with hδ
  have hβδ {τ} (hτ : τ ∈ ρ) (v : κ) : 0 ≤ β τ v - δ v := by
    by_cases hv : v = v₀
    · subst hv
      simp only [hβ, hδ, hv₀τ hτ, ite_true, sub_nonneg]
      exact inv_anti₀ (Nat.cast_pos.mpr (Finset.card_pos.mpr
        (L.isRelLowerSet_faces.prop_of_mem τ.property))) (Nat.cast_le.mpr (hD _ τ.property))
    · simp only [hβ, hδ, hv, ite_false, sub_zero]
      split_ifs <;> positivity
  have hδsum : ∑ v ∈ σ.val, δ v = (D : ℝ)⁻¹ := by simp [hδ, hτσ hτ₀ (hv₀τ hτ₀)]
  -- The differences of the coordinates of `x` and `y` sum to zero.
  have hdiff : ∑ τ ∈ ρ, (x.val τ - y.val τ) = 0 := by
    rw [Finset.sum_sub_distrib, sum_eq_one_of_support_subset x hx,
      sum_eq_one_of_support_subset y hy, sub_self]
  have hpt (v : κ) : (barycentricSubdivisionRealizationMap L x).val v -
      (barycentricSubdivisionRealizationMap L y).val v =
        ∑ τ ∈ ρ, (x.val τ - y.val τ) * β τ v := by
    rw [hcoord hx, hcoord hy, ← Finset.sum_sub_distrib]
    simp only [sub_mul]
  rw [l1Dist_eq_sum_of_subset (hsupp hx) (hsupp hy), l1Dist_eq_sum_of_subset hx hy]
  simp only [hpt]
  exact TauCeti.sum_abs_sum_mul_le hdiff (fun τ hτ => hβδ hτ)
    (fun τ hτ => sum_ite_mem_inv_card (hτσ hτ)) hδsum

/-- **`n` subdivision steps contract `ℓ¹` distances within a closed simplex by `(1 - 1 / D) ^ n`**,
when every face of `K` has at most `D` vertices. -/
private theorem l1Dist_iteratedBarycentricSubdivisionRealizationHomeomorph_le
    {D : ℕ} (hD : ∀ σ ∈ K, σ.card ≤ D) (n : ℕ) {ρ : Finset (K.iteratedBarycentricSubdivision n).1}
    (hρ : ρ ∈ (K.iteratedBarycentricSubdivision n).2)
    {x y : Realization (K.iteratedBarycentricSubdivision n).2} (hx : x.val.support ⊆ ρ)
    (hy : y.val.support ⊆ ρ) :
    l1Dist (K.iteratedBarycentricSubdivisionRealizationHomeomorph n x).val
        (K.iteratedBarycentricSubdivisionRealizationHomeomorph n y).val ≤
      (1 - (D : ℝ)⁻¹) ^ n * l1Dist x.val y.val := by
  induction n with
  | zero => rw [pow_zero, one_mul]; exact le_rfl
  | succ n ih =>
    simp only [iteratedBarycentricSubdivisionRealizationHomeomorph_succ_apply]
    obtain ⟨σ, hσ, hxσ, hyσ, hle⟩ := exists_support_subset_and_l1Dist_le
      (fun τ hτ => card_le_of_mem_iteratedBarycentricSubdivision hD n hτ) hρ hx hy
    refine (ih hσ hxσ hyσ).trans ?_
    have hc : 0 ≤ 1 - (D : ℝ)⁻¹ := sub_nonneg.mpr (Nat.cast_inv_le_one D)
    rw [pow_succ, mul_assoc]
    exact mul_le_mul_of_nonneg_left hle (pow_nonneg hc n)

/-- The image under `b_n` of the open star of a vertex `w` of `sd^n K` lies within `ℓ¹` distance
`2 (1 - 1 / D) ^ n` of the image of `w`. -/
private theorem l1Dist_iteratedBarycentricSubdivisionRealizationHomeomorph_vertex_le {D : ℕ}
    (hD : ∀ σ ∈ K, σ.card ≤ D) (n : ℕ) {w : (K.iteratedBarycentricSubdivision n).1}
    {x : Realization (K.iteratedBarycentricSubdivision n).2}
    (hx : x ∈ (K.iteratedBarycentricSubdivision n).2.openStarRealization w) :
    l1Dist (K.iteratedBarycentricSubdivisionRealizationHomeomorph n x).val
        (K.iteratedBarycentricSubdivisionRealizationHomeomorph n
          (vertex (K.iteratedBarycentricSubdivision n).2 w)).val ≤
      2 * (1 - (D : ℝ)⁻¹) ^ n := by
  have hw : (vertex (K.iteratedBarycentricSubdivision n).2 w).val.support ⊆ x.val.support := by
    rw [support_vertex, Finset.singleton_subset_iff]
    exact Finsupp.mem_support_iff.mpr ((mem_openStarRealization _).mp hx).ne'
  have hle := l1Dist_iteratedBarycentricSubdivisionRealizationHomeomorph_le hD n
    (support_mem _ x) subset_rfl hw
  have hc : 0 ≤ 1 - (D : ℝ)⁻¹ := sub_nonneg.mpr (Nat.cast_inv_le_one D)
  calc _ ≤ (1 - (D : ℝ)⁻¹) ^ n *
        l1Dist x.val (vertex (K.iteratedBarycentricSubdivision n).2 w).val := hle
    _ ≤ (1 - (D : ℝ)⁻¹) ^ n * 2 := mul_le_mul_of_nonneg_left (l1Dist_le_two _ _) (pow_nonneg hc n)
    _ = 2 * (1 - (D : ℝ)⁻¹) ^ n := mul_comm _ _

/-! ### The simplicial approximation theorem -/

/-- **The open vertex stars of `sd^n K` refine every open cover of `|K|`** for all large `n`, when
`K` has finitely many faces: the image under `b_n : |sd^n K| ≃ₜ |K|` of the open star of every
vertex of `sd^n K` lies in a member of the cover. -/
theorem eventually_forall_exists_image_openStarRealization_subset (hfin : K.faces.Finite)
    {α : Sort*} {U : α → Set (Realization K)} (hU : ∀ i, IsOpen (U i)) (hcov : ⋃ i, U i = univ) :
    ∀ᶠ n in atTop, ∀ w, ∃ i, K.iteratedBarycentricSubdivisionRealizationHomeomorph n ''
      (K.iteratedBarycentricSubdivision n).2.openStarRealization w ⊆ U i := by
  -- `|K|` is a compact subspace of the coordinate space on the finite vertex set `V` of `K`.
  set V := PreAbstractSimplicialComplex.faceUnion hfin
  have hV (x : Realization K) : x.val.support ⊆ V :=
    PreAbstractSimplicialComplex.subset_faceUnion hfin (support_mem K x)
  let g : Realization K → (V → ℝ) := fun x v => x.val v
  have : CompactSpace (Realization K) := K.compactSpace_realization_of_finite_faces hfin
  have hemb : IsClosedEmbedding g := by
    refine Continuous.isClosedEmbedding
      (continuous_pi fun v => (continuous_apply v.val).comp (continuous_realization_coe K)) ?_
    intro x y hxy
    refine Subtype.ext (Finsupp.ext fun v => ?_)
    by_cases hv : v ∈ V
    · exact congrFun hxy ⟨v, hv⟩
    · rw [Finsupp.notMem_support_iff.mp fun h => hv (hV x h),
        Finsupp.notMem_support_iff.mp fun h => hv (hV y h)]
  choose W hWopen hWU using fun i => hemb.isInducing.isOpen_iff.mp (hU i)
  have hcpt : IsCompact (range g) := isCompact_range hemb.continuous
  have hsub : range g ⊆ ⋃ i, W i := by
    rintro _ ⟨x, rfl⟩
    obtain ⟨i, hi⟩ := mem_iUnion.mp (hcov.symm ▸ mem_univ x : x ∈ ⋃ i, U i)
    exact mem_iUnion.mpr ⟨i, by rw [← hWU i] at hi; exact hi⟩
  obtain ⟨ε, hε, hball⟩ := lebesgue_number_lemma_of_metric hcpt hWopen hsub
  -- Every face of `K` has at most `D = card V + 1` vertices, and `(1 - 1 / D) ^ n → 0`.
  set D := V.card + 1
  have hD : ∀ σ ∈ K, σ.card ≤ D := fun σ hσ =>
    (Finset.card_le_card (PreAbstractSimplicialComplex.subset_faceUnion hfin hσ)).trans
      (Nat.le_succ _)
  have hc : 1 - (D : ℝ)⁻¹ < 1 := sub_lt_self 1 (by positivity)
  have hc₀ : 0 ≤ 1 - (D : ℝ)⁻¹ := sub_nonneg.mpr (Nat.cast_inv_le_one D)
  have hlim : Tendsto (fun n => 2 * (1 - (D : ℝ)⁻¹) ^ n) atTop (𝓝 0) := by
    simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one hc₀ hc).const_mul 2
  filter_upwards [hlim.eventually (gt_mem_nhds hε)] with n hn w
  obtain ⟨i, hi⟩ := hball _ ⟨K.iteratedBarycentricSubdivisionRealizationHomeomorph n
    (vertex (K.iteratedBarycentricSubdivision n).2 w), rfl⟩
  refine ⟨i, ?_⟩
  rintro _ ⟨x, hx, rfl⟩
  rw [← hWU i]
  refine hi (Metric.mem_ball.mpr ?_)
  rw [dist_eq_norm]
  exact ((norm_restrict_sub_le_l1Dist (hV _) (hV _)).trans
    (l1Dist_iteratedBarycentricSubdivisionRealizationHomeomorph_vertex_le hD n hx)).trans_lt hn

/-- **The simplicial approximation theorem.** Let `K` be a simplicial complex with finitely many
faces and `φ : |K| → |L|` a continuous map. For all large `n`, the map `φ ∘ b_n : |sd^n K| → |L|`,
with `b_n : |sd^n K| ≃ₜ |K|` the canonical homeomorphism, has a simplicial approximation
`sd^n K → L`. -/
theorem eventually_exists_isSimplicialApproximation (hfin : K.faces.Finite) {κ : Type*}
    [DecidableEq κ] {L : AbstractSimplicialComplex κ} {φ : Realization K → Realization L}
    (hφ : Continuous φ) :
    ∀ᶠ n in atTop, ∃ f : PreAbstractSimplicialComplex.SimplicialMap
        (K.iteratedBarycentricSubdivision n).2.toPreAbstractSimplicialComplex
        L.toPreAbstractSimplicialComplex,
      f.IsSimplicialApproximation
        (φ ∘ K.iteratedBarycentricSubdivisionRealizationHomeomorph n) := by
  have hcov : ⋃ w, φ ⁻¹' L.openStarRealization w = univ := by
    rw [← preimage_iUnion, iUnion_openStarRealization, preimage_univ]
  filter_upwards [eventually_forall_exists_image_openStarRealization_subset hfin
    (fun w => (L.isOpen_openStarRealization w).preimage hφ) hcov] with n hn
  refine (PreAbstractSimplicialComplex.SimplicialMap.exists_isSimplicialApproximation_iff _).2
    fun v => ?_
  obtain ⟨w, hw⟩ := hn v
  exact ⟨w, fun x hx => hw (mem_image_of_mem _ hx)⟩

end AbstractSimplicialComplex
