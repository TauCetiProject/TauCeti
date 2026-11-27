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
import TauCeti.Topology.MetricSpace.Lebesgue

/-!
# Iterated barycentric subdivisions and the simplicial approximation theorem

The `n`-th iterated barycentric subdivision `sd^n K` of an abstract simplicial complex `K`
(`AbstractSimplicialComplex.iteratedBarycentricSubdivision`) is obtained by subdividing `n` times;
its vertices after one more step are the faces of `sd^n K`. Composing the canonical subdivision
homeomorphisms `|sd L| ≃ₜ |L|` gives the canonical homeomorphism `b_n : |sd^n K| ≃ₜ |K|`
(`AbstractSimplicialComplex.iteratedBarycentricSubdivisionRealizationHomeomorph`), which sends each
new vertex to the barycenter of the face it stands for and is affine on every simplex of `sd^n K`
(`AbstractSimplicialComplex.iteratedBarycentricSubdivisionRealizationHomeomorph_val_eq_sum`).
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
* `AbstractSimplicialComplex.iteratedBarycentricSubdivisionRealizationHomeomorph_val_eq_sum`:
  `b_n` is affine on every closed simplex of `sd^n K`.
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

/-- `b_(n + 1)` sends the vertex of `sd^(n + 1) K` given by a face `τ` of `sd^n K` to the image
under `b_n` of the barycenter of `τ`. -/
theorem iteratedBarycentricSubdivisionRealizationHomeomorph_succ_vertex (n : ℕ)
    (τ : TauCeti.SetLike.Face (K.iteratedBarycentricSubdivision n).2.toPreAbstractSimplicialComplex)
    {x : Realization (K.iteratedBarycentricSubdivision n).2}
    (hx : x.val = faceBarycenter (K.iteratedBarycentricSubdivision n).2 τ) :
    K.iteratedBarycentricSubdivisionRealizationHomeomorph (n + 1)
        (vertex (K.iteratedBarycentricSubdivision (n + 1)).2 τ) =
      K.iteratedBarycentricSubdivisionRealizationHomeomorph n x := by
  rw [iteratedBarycentricSubdivisionRealizationHomeomorph_succ_apply]
  exact congrArg _ (Subtype.ext ((barycentricSubdivisionRealizationMap_vertex _ τ).trans hx.symm))

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

/-- **`b_n` is affine on every closed simplex of `sd^n K`.** If the support of `x` lies in `ρ`,
then the barycentric coordinates of `b_n x` are the combination, with the coordinates of `x`, of
those of the images of the vertices in `ρ`. -/
theorem iteratedBarycentricSubdivisionRealizationHomeomorph_val_eq_sum (n : ℕ)
    {ρ : Finset (K.iteratedBarycentricSubdivision n).1}
    {x : Realization (K.iteratedBarycentricSubdivision n).2} (hx : x.val.support ⊆ ρ) :
    (K.iteratedBarycentricSubdivisionRealizationHomeomorph n x).val =
      ∑ w ∈ ρ, x.val w • (K.iteratedBarycentricSubdivisionRealizationHomeomorph n
        (vertex (K.iteratedBarycentricSubdivision n).2 w)).val := by
  induction n with
  | zero =>
    have h {y : Realization K} {s : Finset ι} (hy : y.val.support ⊆ s) :
        y.val = ∑ w ∈ s, y.val w • (vertex K w).val := by
      simp only [vertex_val, Finsupp.smul_single_one]
      conv_lhs => rw [← Finsupp.sum_single y.val]
      exact Finsupp.sum_of_support_subset _ hy _ fun _ _ => Finsupp.single_zero _
    exact h hx
  | succ n ih =>
    set β := barycentricSubdivisionRealizationMap (K.iteratedBarycentricSubdivision n).2
    set b := K.iteratedBarycentricSubdivisionRealizationHomeomorph n
    obtain ⟨hne, hchain⟩ :=
      TauCeti.PreAbstractSimplicialComplex.mem_barycentricSubdivision_iff.mp (support_mem _ x)
    obtain ⟨σ, -, hσ⟩ :=
      hchain.exists_isGreatest x.val.support.finite_toSet (Finset.coe_nonempty.mpr hne)
    have hβ {y : Realization (K.iteratedBarycentricSubdivision (n + 1)).2}
        (hy : y.val.support ⊆ x.val.support) : (β y).val.support ⊆ σ.val :=
      support_barycentricSubdivisionRealizationMap_subset _
        (fun _ hτ => face_le_iff.mp (hσ hτ)) hy
    have hvert {τ} (hτ : τ ∈ x.val.support) :
        (K.iteratedBarycentricSubdivisionRealizationHomeomorph (n + 1)
          (vertex (K.iteratedBarycentricSubdivision (n + 1)).2 τ)).val =
          ∑ u ∈ σ.val, faceBarycenter (K.iteratedBarycentricSubdivision n).2 τ u •
            (b (vertex (K.iteratedBarycentricSubdivision n).2 u)).val := by
      have hτv : (β (vertex (K.iteratedBarycentricSubdivision (n + 1)).2 τ)).val =
          faceBarycenter (K.iteratedBarycentricSubdivision n).2 τ :=
        barycentricSubdivisionRealizationMap_vertex _ τ
      rw [iteratedBarycentricSubdivisionRealizationHomeomorph_succ_apply,
        ih (hβ (by rw [support_vertex, Finset.singleton_subset_iff]; exact hτ)), hτv]
    rw [← Finset.sum_subset hx fun w _ hw => by
        rw [Finsupp.notMem_support_iff.mp hw, zero_smul],
      Finset.sum_congr rfl fun τ hτ => by rw [hvert hτ],
      iteratedBarycentricSubdivisionRealizationHomeomorph_succ_apply, ih (hβ subset_rfl)]
    have hβx (u) : (β x).val u =
        ∑ τ ∈ x.val.support, x.val τ * faceBarycenter (K.iteratedBarycentricSubdivision n).2 τ u :=
      barycentricSubdivisionRealizationMap_apply_eq_sum _ subset_rfl u
    simp only [hβx, Finset.sum_smul, Finset.smul_sum, mul_smul]
    exact Finset.sum_comm

/-! ### Contraction of the `ℓ¹` distance -/

/-- Two points of a realization are at `ℓ¹` distance at most `2`, measured on any finite set
containing both supports. -/
private theorem sum_abs_sub_le_two {κ : Type*} {L : AbstractSimplicialComplex κ}
    {x y : Realization L} {s : Finset κ} (hx : x.val.support ⊆ s) (hy : y.val.support ⊆ s) :
    ∑ v ∈ s, |x.val v - y.val v| ≤ 2 := by
  calc ∑ v ∈ s, |x.val v - y.val v|
      ≤ ∑ v ∈ s, (x.val v + y.val v) :=
        Finset.sum_le_sum fun v _ => (abs_sub _ _).trans (by
          rw [abs_of_nonneg (Realization.nonneg L x v), abs_of_nonneg (Realization.nonneg L y v)])
    _ = 2 := by
        rw [Finset.sum_add_distrib, Realization.sum_eq_one_of_support_subset L x hx,
          Realization.sum_eq_one_of_support_subset L y hy]
        norm_num

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
    exact hσx _ (support_barycentricSubdivisionRealizationMap_subset _
      (fun τ' hτ' => face_le_iff.mp (hτ hτ')) hx)

/-- **One subdivision step contracts `ℓ¹` distances within a closed simplex.** Let every face of
`L` have at most `D` vertices, and let `x` and `y` be two points of the closed simplex of `sd L`
spanned by a chain `ρ` of faces of `L`. Their images in `|L|` lie in the closed simplex of the
largest face `σ` of `ρ`, and their `ℓ¹` distance on `σ` is at most `1 - 1 / D` times the `ℓ¹`
distance of `x` and `y` on `ρ`. -/
private theorem exists_support_subset_and_sum_abs_sub_le {κ : Type*}
    {L : AbstractSimplicialComplex κ} {D : ℕ} (hD : ∀ σ ∈ L, σ.card ≤ D)
    {ρ : Finset (TauCeti.SetLike.Face L.toPreAbstractSimplicialComplex)}
    (hρ : ρ ∈ TauCeti.PreAbstractSimplicialComplex.barycentricSubdivision
      L.toPreAbstractSimplicialComplex)
    {x y : Realization (TauCeti.PreAbstractSimplicialComplex.barycentricSubdivision
      L.toPreAbstractSimplicialComplex)} (hx : x.val.support ⊆ ρ) (hy : y.val.support ⊆ ρ) :
    ∃ σ ∈ L, (barycentricSubdivisionRealizationMap L x).val.support ⊆ σ ∧
      (barycentricSubdivisionRealizationMap L y).val.support ⊆ σ ∧
      ∑ v ∈ σ, |(barycentricSubdivisionRealizationMap L x).val v -
          (barycentricSubdivisionRealizationMap L y).val v| ≤
        (1 - (D : ℝ)⁻¹) * ∑ τ ∈ ρ, |x.val τ - y.val τ| := by
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
    support_barycentricSubdivisionRealizationMap_subset L (fun _ hτ => hτσ hτ) hz
  refine ⟨σ.val, σ.property, hsupp hx, hsupp hy, ?_⟩
  -- Every barycenter of `ρ` gives weight at least `1 / D` to `v₀`.
  set δ : κ → ℝ := fun v => if v = v₀ then (D : ℝ)⁻¹ else 0 with hδ
  have hδle {τ} (hτ : τ ∈ ρ) (v : κ) : δ v ≤ faceBarycenter L τ v := by
    rw [faceBarycenter_apply]
    by_cases hv : v = v₀
    · subst hv
      simp only [hδ, hv₀τ hτ, ite_true]
      exact inv_anti₀ (Nat.cast_pos.mpr (Finset.card_pos.mpr
        (L.isRelLowerSet_faces.prop_of_mem τ.property))) (Nat.cast_le.mpr (hD _ τ.property))
    · simp only [hδ, hv, ite_false]
      split_ifs <;> positivity
  have hδsum : ∑ v ∈ σ.val, δ v = (D : ℝ)⁻¹ := by simp [hδ, hτσ hτ₀ (hv₀τ hτ₀)]
  -- The differences of the coordinates of `x` and `y` sum to zero.
  have hdiff : ∑ τ ∈ ρ, (x.val τ - y.val τ) = 0 := by
    rw [Finset.sum_sub_distrib, Realization.sum_eq_one_of_support_subset _ x hx,
      Realization.sum_eq_one_of_support_subset _ y hy, sub_self]
  -- The image of a point of the simplex `ρ` is the combination of the barycenters of `ρ`.
  have hpt (v : κ) : (barycentricSubdivisionRealizationMap L x).val v -
      (barycentricSubdivisionRealizationMap L y).val v =
        ∑ τ ∈ ρ, (x.val τ - y.val τ) * faceBarycenter L τ v := by
    rw [barycentricSubdivisionRealizationMap_apply_eq_sum L hx,
      barycentricSubdivisionRealizationMap_apply_eq_sum L hy, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun _ _ => (sub_mul _ _ _).symm
  simp only [hpt]
  exact TauCeti.sum_abs_sum_mul_le hdiff (fun τ hτ v _ => hδle hτ v)
    (fun τ hτ => sum_faceBarycenter_eq_one_of_subset L τ (hτσ hτ)) hδsum

/-- **`n` subdivision steps contract `ℓ¹` distances within a closed simplex by `(1 - 1 / D) ^ n`**,
when every face of `K` has at most `D` vertices: the images under `b_n` of two points of the closed
simplex of a face `ρ` of `sd^n K` lie in the closed simplex of a face `σ` of `K`, and their `ℓ¹`
distance on `σ` is at most `(1 - 1 / D) ^ n` times that of the two points on `ρ`. -/
private theorem exists_support_subset_and_sum_abs_sub_iteratedBarycentricSubdivision_le
    {D : ℕ} (hD : ∀ σ ∈ K, σ.card ≤ D) (n : ℕ) {ρ : Finset (K.iteratedBarycentricSubdivision n).1}
    (hρ : ρ ∈ (K.iteratedBarycentricSubdivision n).2)
    {x y : Realization (K.iteratedBarycentricSubdivision n).2} (hx : x.val.support ⊆ ρ)
    (hy : y.val.support ⊆ ρ) :
    ∃ σ ∈ K, (K.iteratedBarycentricSubdivisionRealizationHomeomorph n x).val.support ⊆ σ ∧
      (K.iteratedBarycentricSubdivisionRealizationHomeomorph n y).val.support ⊆ σ ∧
      ∑ v ∈ σ, |(K.iteratedBarycentricSubdivisionRealizationHomeomorph n x).val v -
          (K.iteratedBarycentricSubdivisionRealizationHomeomorph n y).val v| ≤
        (1 - (D : ℝ)⁻¹) ^ n * ∑ τ ∈ ρ, |x.val τ - y.val τ| := by
  induction n with
  | zero => exact ⟨ρ, hρ, hx, hy, by rw [pow_zero, one_mul]; exact le_rfl⟩
  | succ n ih =>
    simp only [iteratedBarycentricSubdivisionRealizationHomeomorph_succ_apply]
    obtain ⟨σ, hσ, hxσ, hyσ, hle⟩ := exists_support_subset_and_sum_abs_sub_le
      (fun τ hτ => card_le_of_mem_iteratedBarycentricSubdivision hD n hτ) hρ hx hy
    obtain ⟨σ', hσ', hxσ', hyσ', hle'⟩ := ih hσ hxσ hyσ
    refine ⟨σ', hσ', hxσ', hyσ', hle'.trans ?_⟩
    have hc : 0 ≤ 1 - (D : ℝ)⁻¹ := sub_nonneg.mpr (Nat.cast_inv_le_one D)
    rw [pow_succ, mul_assoc]
    exact mul_le_mul_of_nonneg_left hle (pow_nonneg hc n)

/-- The image under `b_n` of a point `x` of the open star of a vertex `w` of `sd^n K` and the image
of `w` lie in the closed simplex of a face `σ` of `K`, at `ℓ¹` distance at most `2 (1 - 1 / D) ^ n`
on `σ`. -/
private theorem exists_support_subset_and_sum_abs_sub_iteratedBarycentricSubdivision_vertex_le
    {D : ℕ} (hD : ∀ σ ∈ K, σ.card ≤ D) (n : ℕ) {w : (K.iteratedBarycentricSubdivision n).1}
    {x : Realization (K.iteratedBarycentricSubdivision n).2}
    (hx : x ∈ (K.iteratedBarycentricSubdivision n).2.openStarRealization w) :
    ∃ σ ∈ K, (K.iteratedBarycentricSubdivisionRealizationHomeomorph n x).val.support ⊆ σ ∧
      (K.iteratedBarycentricSubdivisionRealizationHomeomorph n
        (vertex (K.iteratedBarycentricSubdivision n).2 w)).val.support ⊆ σ ∧
      ∑ v ∈ σ, |(K.iteratedBarycentricSubdivisionRealizationHomeomorph n x).val v -
          (K.iteratedBarycentricSubdivisionRealizationHomeomorph n
            (vertex (K.iteratedBarycentricSubdivision n).2 w)).val v| ≤
        2 * (1 - (D : ℝ)⁻¹) ^ n := by
  have hw : (vertex (K.iteratedBarycentricSubdivision n).2 w).val.support ⊆ x.val.support := by
    rw [support_vertex, Finset.singleton_subset_iff]
    exact Finsupp.mem_support_iff.mpr ((mem_openStarRealization _).mp hx).ne'
  obtain ⟨σ, hσ, hxσ, hwσ, hle⟩ :=
    exists_support_subset_and_sum_abs_sub_iteratedBarycentricSubdivision_le hD n
      (support_mem _ x) subset_rfl hw
  refine ⟨σ, hσ, hxσ, hwσ, hle.trans ?_⟩
  have hc : 0 ≤ 1 - (D : ℝ)⁻¹ := sub_nonneg.mpr (Nat.cast_inv_le_one D)
  rw [mul_comm 2]
  exact mul_le_mul_of_nonneg_left (sum_abs_sub_le_two subset_rfl hw) (pow_nonneg hc n)

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
  have hgc : Continuous g :=
    continuous_pi fun v => (continuous_apply v.val).comp (continuous_realization_coe K)
  have hginj : Function.Injective g := by
    intro x y hxy
    refine Subtype.ext (Finsupp.ext fun v => ?_)
    by_cases hv : v ∈ V
    · exact congrFun hxy ⟨v, hv⟩
    · rw [Finsupp.notMem_support_iff.mp fun h => hv (hV x h),
        Finsupp.notMem_support_iff.mp fun h => hv (hV y h)]
  obtain ⟨ε, hε, hball⟩ := TauCeti.exists_pos_forall_exists_forall_dist_lt_mem hgc hginj hU hcov.ge
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
  obtain ⟨i, hi⟩ := hball (K.iteratedBarycentricSubdivisionRealizationHomeomorph n
    (vertex (K.iteratedBarycentricSubdivision n).2 w))
  refine ⟨i, ?_⟩
  rintro _ ⟨x, hx, rfl⟩
  refine hi _ ?_
  -- The sup norm on `V` is bounded by the `ℓ¹` distance on a face containing both supports.
  obtain ⟨σ, -, hxσ, hwσ, hle⟩ :=
    exists_support_subset_and_sum_abs_sub_iteratedBarycentricSubdivision_vertex_le hD n hx
  rw [dist_eq_norm]
  refine ((pi_norm_le_iff_of_nonneg (Finset.sum_nonneg fun _ _ => abs_nonneg _)).2
    fun v => ?_).trans_lt (hle.trans_lt hn)
  rw [Pi.sub_apply, Real.norm_eq_abs]
  by_cases hv : v.val ∈ σ
  · exact Finset.single_le_sum (f := fun u =>
      |(K.iteratedBarycentricSubdivisionRealizationHomeomorph n x).val u -
        (K.iteratedBarycentricSubdivisionRealizationHomeomorph n
          (vertex (K.iteratedBarycentricSubdivision n).2 w)).val u|)
      (fun _ _ => abs_nonneg _) hv
  · simp only [g, Finsupp.notMem_support_iff.mp fun h => hv (hxσ h),
      Finsupp.notMem_support_iff.mp fun h => hv (hwσ h), sub_self, abs_zero]
    exact Finset.sum_nonneg fun _ _ => abs_nonneg _

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
