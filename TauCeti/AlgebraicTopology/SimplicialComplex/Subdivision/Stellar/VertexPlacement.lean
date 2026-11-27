/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.SimplicialComplex.Subdivision.Stellar.Homeomorph
public import TauCeti.AlgebraicTopology.SimplicialComplex.CombinatorialManifold.Link
public import TauCeti.AlgebraicTopology.SimplicialComplex.CombinatorialManifold.Relabel
import Mathlib.Topology.Order.Lattice

/-!
# Placing vertices at arbitrary points via stellar subdivision

A point `x` in the realization `Realization K` of a simplicial complex `K` can be turned into a
vertex of a subdivided complex without changing the homeomorphism type of the realization, the
combinatorial manifold dimension, or finiteness of the vertex set.

If `x` is already a vertex of `K`, no change is required. Otherwise `x` lies in the open simplex
spanned by its support `σ = x.val.support` of cardinality `1 < σ.card`. Starring `σ` at a fresh
vertex `none : Option ι` gives an abstract simplicial complex `K'` on `Option ι` with a canonical
homeomorphism `Realization K' ≃ₜ Realization K` mapping `none` to the barycenter of `σ` and
fixing all original vertices. Composing with a radial self-homeomorphism of `Realization K` that
moves the barycenter of `σ` to `x` and fixes the boundary of the closed star of `σ` places `x` at
a vertex of `K'`. Iterating over any finite set `S : Set (Realization K)` yields a subdivision in
which every point of `S` is a vertex image.

## Main definitions

* `AbstractSimplicialComplex.simplexMoveHomeomorph`: radial self-homeomorphism of `Realization K`
  moving an open-simplex point `b` to another point `x` of the same open simplex while fixing every
  point whose support does not contain that simplex (in particular every vertex when `1 < σ.card`).

## Main results

* `AbstractSimplicialComplex.exists_stellarSubdivision_vertex_image`: single-point vertex
  placement preserving finiteness of the vertex type and combinatorial manifold dimension.
* `AbstractSimplicialComplex.exists_subdivision_finset_vertex_image` and
  `AbstractSimplicialComplex.exists_subdivision_vertex_image`: finite-set vertex placement.

## References

* C. P. Rourke, B. J. Sanderson, *Introduction to Piecewise-Linear Topology*, Springer (1972),
  Chapter 2 (starrings and subdivisions).
-/

public section

noncomputable section

open Set Finset

namespace AbstractSimplicialComplex

section SimplexMove

variable {ι : Type*} (K : AbstractSimplicialComplex ι)

/-- The radial scale factor `min_{i ∈ σ} y i / b i` controlling movement from `b` toward `x`
inside the open star of `σ`. -/
private def simplexMoveFactor {σ : Finset ι} (hσ : σ.Nonempty) (b y : Realization K) : ℝ :=
  σ.inf' hσ fun i => y.val i / b.val i

private theorem simplexMoveFactor_nonneg {σ : Finset ι} (hσ : σ.Nonempty)
    (b y : Realization K) :
    0 ≤ simplexMoveFactor K hσ b y := by
  refine (Finset.le_inf'_iff hσ _).mpr fun i _ => ?_
  exact div_nonneg (Realization.nonneg K y i) (Realization.nonneg K b i)

private theorem simplexMoveFactor_eq_zero_of_not_subset {σ : Finset ι} (hσ : σ.Nonempty)
    (b : Realization K) {y : Realization K} (hy : ¬ σ ⊆ y.val.support) :
    simplexMoveFactor K hσ b y = 0 := by
  obtain ⟨i, hiσ, hiy⟩ := Finset.not_subset.mp hy
  have hy0 : y.val i = 0 := Finsupp.notMem_support_iff.mp hiy
  refine le_antisymm ?_ (simplexMoveFactor_nonneg K hσ b y)
  calc
    simplexMoveFactor K hσ b y ≤ y.val i / b.val i := Finset.inf'_le _ hiσ
    _ = 0 := by simp [hy0]

private theorem simplexMoveFactor_mul_le {σ : Finset ι} (hσ : σ.Nonempty)
    (b : Realization K) (hb : b.val.support = σ) (y : Realization K)
    {i : ι} (hi : i ∈ σ) :
    simplexMoveFactor K hσ b y * b.val i ≤ y.val i := by
  have hbpos : 0 < b.val i :=
    Realization.pos_of_mem_support K b (hb.symm ▸ hi)
  exact (le_div_iff₀ hbpos).mp (Finset.inf'_le _ hi)

private theorem simplexMoveFun_mem {σ : Finset ι} (hσ : σ.Nonempty)
    (b x : Realization K) (hb : b.val.support = σ) (hx : x.val.support = σ)
    (y : Realization K) :
    y.val + simplexMoveFactor K hσ b y • (x.val - b.val) ∈
      (standardGeometricComplex K).space := by
  let α := simplexMoveFactor K hσ b y
  have hα : 0 ≤ α := simplexMoveFactor_nonneg K hσ b y
  have hcoord : ∀ i, 0 ≤ (y.val + α • (x.val - b.val)) i := by
    intro i
    simp only [Finsupp.coe_add, Finsupp.coe_smul, Finsupp.coe_sub, Pi.add_apply,
      Pi.smul_apply, Pi.sub_apply, smul_eq_mul]
    by_cases hi : i ∈ σ
    · have hle := simplexMoveFactor_mul_le K hσ b hb y hi
      have hxi : 0 ≤ x.val i := Realization.nonneg K x i
      nlinarith
    · have hbi : b.val i = 0 := Finsupp.notMem_support_iff.mp (hb ▸ hi)
      have hxi : x.val i = 0 := Finsupp.notMem_support_iff.mp (hx ▸ hi)
      simp [hbi, hxi, Realization.nonneg K y i]
  have hsum : (y.val + α • (x.val - b.val)).sum (fun _ r => r) = 1 := by
    let S := Finsupp.linearCombination ℝ (fun _ : ι => (1 : ℝ))
    have hS (z : ι →₀ ℝ) : S z = z.sum (fun _ r => r) := by
      simp [S, Finsupp.linearCombination_apply]
    rw [← hS, map_add, map_smul, map_sub, hS, hS, hS,
      Realization.sum_eq_one K y, Realization.sum_eq_one K x, Realization.sum_eq_one K b]
    simp
  have hsup : (y.val + α • (x.val - b.val)).support ∈ K := by
    by_cases hsub : σ ⊆ y.val.support
    · have hle : (y.val + α • (x.val - b.val)).support ⊆ y.val.support := by
        intro i hi
        rw [Finsupp.mem_support_iff] at hi ⊢
        by_cases hiσ : i ∈ σ
        · exact Finsupp.mem_support_iff.mp (hsub hiσ)
        · have hbi : b.val i = 0 := Finsupp.notMem_support_iff.mp (hb ▸ hiσ)
          have hxi : x.val i = 0 := Finsupp.notMem_support_iff.mp (hx ▸ hiσ)
          simpa [hbi, hxi] using hi
      exact K.isRelLowerSet_faces.mem_of_le (support_mem K y) hle
        (Finsupp.support_nonempty_iff.mpr fun h0 => by simp [h0] at hsum)
    · have hα0 : α = 0 := simplexMoveFactor_eq_zero_of_not_subset K hσ b hsub
      simpa [α, hα0] using support_mem K y
  exact TauCeti.mem_standardGeometricComplex_space_iff.mpr ⟨hcoord, hsum, hsup⟩

private def simplexMoveFun {σ : Finset ι} (hσ : σ.Nonempty)
    (b x : Realization K) (hb : b.val.support = σ) (hx : x.val.support = σ)
    (y : Realization K) : Realization K :=
  ⟨y.val + simplexMoveFactor K hσ b y • (x.val - b.val),
    simplexMoveFun_mem K hσ b x hb hx y⟩

private theorem simplexMoveFun_val {σ : Finset ι} (hσ : σ.Nonempty)
    (b x : Realization K) (hb : b.val.support = σ) (hx : x.val.support = σ)
    (y : Realization K) :
    (simplexMoveFun K hσ b x hb hx y).val =
      y.val + simplexMoveFactor K hσ b y • (x.val - b.val) :=
  rfl

private theorem simplexMoveFun_of_not_subset {σ : Finset ι} (hσ : σ.Nonempty)
    (b x : Realization K) (hb : b.val.support = σ) (hx : x.val.support = σ)
    {y : Realization K} (hy : ¬ σ ⊆ y.val.support) :
    simplexMoveFun K hσ b x hb hx y = y := by
  apply Subtype.ext
  rw [simplexMoveFun_val, simplexMoveFactor_eq_zero_of_not_subset K hσ b hy, zero_smul,
    add_zero]

private theorem simplexMoveFactor_comp {σ : Finset ι} (hσ : σ.Nonempty)
    (b x : Realization K) (hb : b.val.support = σ) (hx : x.val.support = σ)
    (y : Realization K) :
    simplexMoveFactor K hσ x (simplexMoveFun K hσ b x hb hx y) =
      simplexMoveFactor K hσ b y := by
  let α := simplexMoveFactor K hσ b y
  let z := simplexMoveFun K hσ b x hb hx y
  by_cases hsub : σ ⊆ y.val.support
  · obtain ⟨j, hjσ, hjmin⟩ := Finset.exists_mem_eq_inf' hσ fun i => y.val i / b.val i
    have hxj : 0 < x.val j := Realization.pos_of_mem_support K x (hx ▸ hjσ)
    have hbj : 0 < b.val j := Realization.pos_of_mem_support K b (hb ▸ hjσ)
    have hyj : y.val j = α * b.val j := by
      change y.val j = (σ.inf' hσ fun i => y.val i / b.val i) * b.val j
      rw [hjmin, div_mul_cancel₀ _ hbj.ne']
    have hzxj : z.val j / x.val j = α := by
      have hzv : z.val j = y.val j + α * (x.val j - b.val j) := by
        simp [z, simplexMoveFun_val, α]
      rw [hzv, hyj]
      field_simp [hxj.ne']
      ring
    refine le_antisymm ?_ ((Finset.le_inf'_iff hσ _).mpr fun i hi => ?_)
    · exact (Finset.inf'_le (fun i => z.val i / x.val i) hjσ).trans hzxj.le
    · have hxi : 0 < x.val i := Realization.pos_of_mem_support K x (hx ▸ hi)
      have hle := simplexMoveFactor_mul_le K hσ b hb y hi
      have hzi : α * x.val i ≤ z.val i := by
        have hzv : z.val i = y.val i + α * (x.val i - b.val i) := by
          simp [z, simplexMoveFun_val, α]
        linarith
      exact (le_div_iff₀ hxi).mpr hzi
  · have hz : z = y := simplexMoveFun_of_not_subset K hσ b x hb hx hsub
    change simplexMoveFactor K hσ x z = simplexMoveFactor K hσ b y
    rw [hz, simplexMoveFactor_eq_zero_of_not_subset K hσ x hsub,
      simplexMoveFactor_eq_zero_of_not_subset K hσ b hsub]

private theorem simplexMoveFun_left_inv {σ : Finset ι} (hσ : σ.Nonempty)
    (b x : Realization K) (hb : b.val.support = σ) (hx : x.val.support = σ)
    (y : Realization K) :
    simplexMoveFun K hσ x b hx hb (simplexMoveFun K hσ b x hb hx y) = y := by
  apply Subtype.ext
  rw [simplexMoveFun_val, simplexMoveFun_val, simplexMoveFactor_comp K hσ b x hb hx y]
  ext i
  simp only [Finsupp.coe_add, Finsupp.coe_smul, Finsupp.coe_sub, Pi.add_apply,
    Pi.smul_apply, Pi.sub_apply, smul_eq_mul]
  ring

private theorem continuous_simplexMoveFun {σ : Finset ι} (hσ : σ.Nonempty)
    (b x : Realization K) (hb : b.val.support = σ) (hx : x.val.support = σ) :
    Continuous (simplexMoveFun K hσ b x hb hx) := by
  refine continuous_iff_faceInclusion.mpr fun τ => ?_
  have hsub (y : StandardSimplex τ.val) :
      (simplexMoveFun K hσ b x hb hx (faceInclusion K τ y)).val.support ⊆ τ.val := by
    let fy := faceInclusion K τ y
    by_cases hσf : σ ⊆ fy.val.support
    · intro i hi
      rw [simplexMoveFun_val, Finsupp.mem_support_iff] at hi
      by_cases hiσ : i ∈ σ
      · exact StandardSimplex.support_subset y
          (by simpa [fy, faceInclusion_val] using hσf hiσ)
      · have hbi : b.val i = 0 := Finsupp.notMem_support_iff.mp (hb ▸ hiσ)
        have hxi : x.val i = 0 := Finsupp.notMem_support_iff.mp (hx ▸ hiσ)
        have hyi : fy.val i ≠ 0 := by simpa [fy, hbi, hxi] using hi
        exact StandardSimplex.support_subset y
          (by simpa [fy, faceInclusion_val, Finsupp.mem_support_iff] using hyi)
    · rw [simplexMoveFun_of_not_subset K hσ b x hb hx hσf]
      simpa [fy, faceInclusion_val] using StandardSimplex.support_subset y
  let g : StandardSimplex τ.val → StandardSimplex τ.val := fun y =>
    ⟨(simplexMoveFun K hσ b x hb hx (faceInclusion K τ y)).val,
      Realization.mem_convexHull_of_support_subset K _ (hsub y)⟩
  have hfg : simplexMoveFun K hσ b x hb hx ∘ faceInclusion K τ = faceInclusion K τ ∘ g := by
    funext y
    exact Subtype.ext (faceInclusion_val K τ (g y)).symm
  rw [hfg]
  refine (continuous_faceInclusion K τ).comp ?_
  refine continuous_induced_rng.mpr (continuous_pi fun i => ?_)
  have hcoord : ∀ j : ι, Continuous (fun y : StandardSimplex τ.val => (y.val j : ℝ)) :=
    fun j => (continuous_apply j).comp continuous_induced_dom
  have hfac : Continuous (fun y : StandardSimplex τ.val =>
      simplexMoveFactor K hσ b (faceInclusion K τ y)) := by
    have hinf : Continuous fun y : StandardSimplex τ.val =>
        σ.inf' hσ fun j => (y.val j : ℝ) / b.val j :=
      Continuous.finset_inf'_apply hσ fun j _ => (hcoord j).div_const (b.val j)
    simpa [simplexMoveFactor, faceInclusion_val] using hinf
  dsimp only [Function.comp_apply]
  have hgval : (fun y : StandardSimplex τ.val => ((g y).val : ι → ℝ) i) = fun y =>
      y.val i + simplexMoveFactor K hσ b (faceInclusion K τ y) * (x.val i - b.val i) := by
    funext y
    simp [g, simplexMoveFun_val, faceInclusion_val]
  rw [hgval]
  exact (hcoord i).add (hfac.mul continuous_const)

/-- Radial self-homeomorphism of `Realization K` moving `b` to `x` inside the open simplex `σ`,
fixing every point whose support does not contain `σ` (in particular every vertex when
`1 < σ.card`). Works for arbitrary complexes without any finiteness hypothesis. -/
def simplexMoveHomeomorph {σ : Finset ι} (hσ : σ.Nonempty)
    (b x : Realization K) (hb : b.val.support = σ) (hx : x.val.support = σ) :
    Realization K ≃ₜ Realization K where
  toFun := simplexMoveFun K hσ b x hb hx
  invFun := simplexMoveFun K hσ x b hx hb
  left_inv := simplexMoveFun_left_inv K hσ b x hb hx
  right_inv := simplexMoveFun_left_inv K hσ x b hx hb
  continuous_toFun := continuous_simplexMoveFun K hσ b x hb hx
  continuous_invFun := continuous_simplexMoveFun K hσ x b hx hb

@[simp]
theorem simplexMoveHomeomorph_symm {σ : Finset ι} (hσ : σ.Nonempty)
    (b x : Realization K) (hb : b.val.support = σ) (hx : x.val.support = σ) :
    (simplexMoveHomeomorph K hσ b x hb hx).symm =
      simplexMoveHomeomorph K hσ x b hx hb := by
  ext y
  rfl

@[simp]
theorem simplexMoveHomeomorph_apply_left {σ : Finset ι} (hσ : σ.Nonempty)
    (b x : Realization K) (hb : b.val.support = σ) (hx : x.val.support = σ) :
    simplexMoveHomeomorph K hσ b x hb hx b = x := by
  apply Subtype.ext
  change b.val + simplexMoveFactor K hσ b b • (x.val - b.val) = x.val
  have hfac : simplexMoveFactor K hσ b b = 1 := by
    refine le_antisymm ?_ ((Finset.le_inf'_iff hσ _).mpr fun i hi => ?_)
    · have ⟨i, hi⟩ := hσ
      have hbi : b.val i ≠ 0 := Finsupp.mem_support_iff.mp (hb ▸ hi)
      calc
        simplexMoveFactor K hσ b b ≤ b.val i / b.val i := Finset.inf'_le _ hi
        _ = 1 := div_self hbi
    · have hbi : b.val i ≠ 0 := Finsupp.mem_support_iff.mp (hb ▸ hi)
      rw [div_self hbi]
  rw [hfac, one_smul]
  abel

theorem simplexMoveHomeomorph_apply_of_not_subset {σ : Finset ι} (hσ : σ.Nonempty)
    (b x : Realization K) (hb : b.val.support = σ) (hx : x.val.support = σ)
    {y : Realization K} (hy : ¬ σ ⊆ y.val.support) :
    simplexMoveHomeomorph K hσ b x hb hx y = y :=
  simplexMoveFun_of_not_subset K hσ b x hb hx hy

theorem simplexMoveHomeomorph_vertex {σ : Finset ι} (hσ : σ.Nonempty)
    (b x : Realization K) (hb : b.val.support = σ) (hx : x.val.support = σ)
    (hcard : 1 < σ.card) (w : ι) :
    simplexMoveHomeomorph K hσ b x hb hx (K.vertex w) = K.vertex w := by
  refine simplexMoveHomeomorph_apply_of_not_subset K hσ b x hb hx fun hsub => ?_
  rw [support_vertex] at hsub
  have hle := (Finset.card_le_card hsub).trans (Finset.card_singleton w).le
  omega

end SimplexMove

section StellarVertexPlacement

/-- Any point `x` in the realization of a simplicial complex `K` becomes the image of a vertex
under a homeomorphism from a single stellar subdivision (or the identity if `x` is already a
vertex), preserving vertex finiteness and combinatorial manifold dimension. -/
theorem exists_stellarSubdivision_vertex_image {ι : Type u} [DecidableEq ι]
    (K : AbstractSimplicialComplex ι) (x : Realization K) :
    ∃ (ι' : Type u) (_ : DecidableEq ι') (K' : AbstractSimplicialComplex ι')
      (e : Realization K' ≃ₜ Realization K),
      (Finite ι → Finite ι') ∧
      (∀ n, PreAbstractSimplicialComplex.IsCombinatorialManifold
        K.toPreAbstractSimplicialComplex n →
        PreAbstractSimplicialComplex.IsCombinatorialManifold
          K'.toPreAbstractSimplicialComplex n) ∧
      (∃ u : ι', e (K'.vertex u) = x) ∧
      (∀ w : ι, ∃ w' : ι', e (K'.vertex w') = K.vertex w) := by
  classical
  have hσK : x.val.support ∈ K := support_mem K x
  have hne : x.val.support.Nonempty := K.isRelLowerSet_faces.prop_of_mem hσK
  by_cases hcard : x.val.support.card = 1
  · obtain ⟨v, hv⟩ := Finset.card_eq_one.mp hcard
    exact ⟨ι, inferInstance, K, Homeomorph.refl _, id, fun _ h => h,
      ⟨v, (Realization.eq_vertex_of_support_eq K x hv).symm⟩, fun w => ⟨w, rfl⟩⟩
  · have hgt : 1 < x.val.support.card :=
      lt_of_le_of_ne (Finset.card_pos.mpr hne) (Ne.symm hcard)
    let σ := x.val.support
    have hgtσ : 1 < σ.card := hgt
    let Kopt : PreAbstractSimplicialComplex (Option ι) :=
      K.toPreAbstractSimplicialComplex.map Function.Embedding.some
    let σopt : Finset (Option ι) := σ.map Function.Embedding.some
    have hσopt : σopt ∈ Kopt :=
      PreAbstractSimplicialComplex.mem_map_iff.mpr
        ⟨σ, hσK, by simp [σopt, Finset.map_eq_image]⟩
    have hnone : ({none} : Finset (Option ι)) ∉ Kopt := by
      intro hmem
      obtain ⟨τ, -, hτ⟩ := PreAbstractSimplicialComplex.mem_map_iff.mp hmem
      have : (none : Option ι) ∈ τ.image some := hτ.symm ▸ Finset.mem_singleton_self none
      obtain ⟨w, -, hw⟩ := Finset.mem_image.mp this
      exact Option.some_ne_none w hw
    let P := PreAbstractSimplicialComplex.stellarSubdivision Kopt σopt none
    let K' : AbstractSimplicialComplex (Option ι) :=
      { P with
        singleton_mem := fun u => by
          rcases u with _ | w
          · exact PreAbstractSimplicialComplex.singleton_mem_stellarSubdivision_iff.mpr hσopt
          · refine (PreAbstractSimplicialComplex.mem_stellarSubdivision_iff_of_notMem
              (by simp)).mpr ⟨?_, ?_⟩
            · exact PreAbstractSimplicialComplex.mem_map_iff.mpr
                ⟨{w}, K.singleton_mem w, by simp⟩
            · intro hsub
              have hle : σ.card ≤ 1 := by
                have h1 := Finset.card_le_card hsub
                simpa [σopt] using h1
              exact absurd hle (by omega) }
    have hP : P = K'.toPreAbstractSimplicialComplex := rfl
    have hfin : Finite ι → Finite (Option ι) := fun _ => inferInstance
    have hman : ∀ n, PreAbstractSimplicialComplex.IsCombinatorialManifold
        K.toPreAbstractSimplicialComplex n →
        PreAbstractSimplicialComplex.IsCombinatorialManifold
          K'.toPreAbstractSimplicialComplex n := by
      intro n hK
      have hKopt : PreAbstractSimplicialComplex.IsCombinatorialManifold Kopt n :=
        (PreAbstractSimplicialComplex.isCombinatorialManifold_map_iff
          (Option.some_injective (α := ι))).mpr hK
      exact hKopt.stellarSubdivision hnone
    let top := (⊤ : AbstractSimplicialComplex (Option ι))
    have hmapP : P.map (Function.Embedding.refl (Option ι)) = P := by
      rw [Function.Embedding.coe_refl]
      exact PreAbstractSimplicialComplex.map_id
    let r1 : Realization K' ≃ₜ {z : Realization top // z.val.support ∈ P} :=
      P.realizationRelabelingHomeomorph (Function.Embedding.refl _) hmapP hP
        (PreAbstractSimplicialComplex.le_top P)
    obtain ⟨est, hest⟩ := PreAbstractSimplicialComplex.exists_homeomorph_stellarSubdivision
      (A := top) hσopt hnone (PreAbstractSimplicialComplex.le_top Kopt)
      (PreAbstractSimplicialComplex.le_top P)
    let r2 : Realization K ≃ₜ {z : Realization top // z.val.support ∈ Kopt} :=
      K.toPreAbstractSimplicialComplex.realizationRelabelingHomeomorph
        Function.Embedding.some rfl rfl (PreAbstractSimplicialComplex.le_top Kopt)
    let b : Realization K :=
      ⟨faceBarycenter K ⟨σ, hσK⟩,
        mem_realization_iff.2 ⟨σ, hσK, faceBarycenter_mem K ⟨σ, hσK⟩⟩⟩
    have hb : b.val.support = σ := support_faceBarycenter K ⟨σ, hσK⟩
    let move := K.simplexMoveHomeomorph hne b x hb rfl
    let e : Realization K' ≃ₜ Realization K := r1.trans (est.trans (r2.symm.trans move))
    refine ⟨Option ι, inferInstance, K', e, hfin, hman,
      ⟨none, ?_⟩, fun w => ⟨some w, ?_⟩⟩
    · have hstnone : (est (r1 (K'.vertex none))).val.val = (r2 b).val.val := by
        rw [hest]
        have hr1 : (r1 (K'.vertex none)).val.val = Finsupp.single none 1 := by
          dsimp only [r1]
          rw [PreAbstractSimplicialComplex.realizationRelabelingHomeomorph_val]
          simp
        rw [hr1, Finset.stellarSubdivisionLinearMap_single]
        dsimp only [r2]
        rw [PreAbstractSimplicialComplex.realizationRelabelingHomeomorph_val]
        ext u
        rcases u with _ | w
        · have hnotin : (none : Option ι) ∉
              Set.range (Function.Embedding.some : ι ↪ Option ι) := by
            rintro ⟨w, hw⟩
            exact Option.some_ne_none w hw
          rw [Finsupp.mapDomain_of_notMem_range _ _ hnotin]
          simp [σopt]
        · have hbval : b.val w = if w ∈ σ then (σ.card : ℝ)⁻¹ else 0 := by
            convert faceBarycenter_apply K ⟨σ, hσK⟩ w
          have hmap : (Finsupp.mapDomain Function.Embedding.some b.val)
              (Function.Embedding.some w) = b.val w :=
            Finsupp.mapDomain_apply_of_injective Function.Embedding.some.injective b.val w
          change _ = (Finsupp.mapDomain Function.Embedding.some b.val)
            (Function.Embedding.some w)
          rw [hmap, hbval]
          by_cases hw : w ∈ σ
          · simp [σopt, hw, Finset.card_map, Finsupp.single_apply]
          · simp [σopt, hw, Finsupp.single_apply]
      have hr2b : r2.symm (est (r1 (K'.vertex none))) = b :=
        r2.symm_apply_eq.mpr (Subtype.ext (Subtype.ext hstnone))
      simp [e, hr2b, move]
    · have hstw : (est (r1 (K'.vertex (some w)))).val.val = (r2 (K.vertex w)).val.val := by
        rw [hest]
        have hr1 : (r1 (K'.vertex (some w))).val.val = Finsupp.single (some w) 1 := by
          dsimp only [r1]
          rw [PreAbstractSimplicialComplex.realizationRelabelingHomeomorph_val]
          simp
        rw [hr1, Finset.stellarSubdivisionLinearMap_single_of_ne (by simp)]
        dsimp only [r2]
        rw [PreAbstractSimplicialComplex.realizationRelabelingHomeomorph_val]
        simp
      have hr2w : r2.symm (est (r1 (K'.vertex (some w)))) = K.vertex w :=
        r2.symm_apply_eq.mpr (Subtype.ext (Subtype.ext hstw))
      simp only [e, Homeomorph.trans_apply, hr2w]
      exact simplexMoveHomeomorph_vertex K hne b x hb rfl hgtσ w

/-- Given any finite set of points `S : Finset (Realization K)`, there is a subdivided complex
`K'` on the same universe as `ι` with a homeomorphism `e : Realization K' ≃ₜ Realization K`
preserving vertex finiteness and combinatorial manifold dimension such that every point of `S`
is the `e`-image of a vertex of `K'`. -/
theorem exists_subdivision_finset_vertex_image {ι : Type u} [DecidableEq ι]
    (K : AbstractSimplicialComplex ι) (S : Finset (Realization K)) :
    ∃ (ι' : Type u) (_ : DecidableEq ι') (K' : AbstractSimplicialComplex ι')
      (e : Realization K' ≃ₜ Realization K),
      (Finite ι → Finite ι') ∧
      (∀ n, PreAbstractSimplicialComplex.IsCombinatorialManifold
        K.toPreAbstractSimplicialComplex n →
        PreAbstractSimplicialComplex.IsCombinatorialManifold
          K'.toPreAbstractSimplicialComplex n) ∧
      (∀ s ∈ S, ∃ u : ι', e (K'.vertex u) = s) := by
  classical
  induction S using Finset.induction_on with
  | empty =>
    exact ⟨ι, inferInstance, K, Homeomorph.refl _, id, fun _ h => h, fun _ h => by simp at h⟩
  | @insert x S₀ _ ih =>
    obtain ⟨ι₀, _, K₀, e₀, hfin₀, hman₀, hvert₀⟩ := ih
    obtain ⟨ι₁, _, K₁, e₁, hfin₁, hman₁, ⟨u, hu⟩, hkeep⟩ :=
      exists_stellarSubdivision_vertex_image K₀ (e₀.symm x)
    refine ⟨ι₁, inferInstance, K₁, e₁.trans e₀, hfin₁ ∘ hfin₀,
      fun n h => hman₁ n (hman₀ n h), fun s hs => ?_⟩
    rcases Finset.mem_insert.mp hs with rfl | hs₀
    · exact ⟨u, by simp [hu]⟩
    · obtain ⟨w, hw⟩ := hvert₀ s hs₀
      obtain ⟨w', hw'⟩ := hkeep w
      exact ⟨w', by simp [hw', hw]⟩

/-- Given any finite subset `S : Set (Realization K)`, there is a subdivided complex `K'`, a
homeomorphism `e : Realization K' ≃ₜ Realization K`, and a vertex subset `V : Set ι'` whose
vertex image under `e` equals `S`, preserving vertex finiteness and combinatorial manifold
dimension. -/
theorem exists_subdivision_vertex_image {ι : Type u} [DecidableEq ι]
    (K : AbstractSimplicialComplex ι) {S : Set (Realization K)} (hS : S.Finite) :
    ∃ (ι' : Type u) (_ : DecidableEq ι') (K' : AbstractSimplicialComplex ι')
      (e : Realization K' ≃ₜ Realization K) (V : Set ι'),
      (Finite ι → Finite ι') ∧
      (∀ n, PreAbstractSimplicialComplex.IsCombinatorialManifold
        K.toPreAbstractSimplicialComplex n →
        PreAbstractSimplicialComplex.IsCombinatorialManifold
          K'.toPreAbstractSimplicialComplex n) ∧
      e '' (K'.vertex '' V) = S := by
  obtain ⟨ι', _, K', e, hfin, hman, hvert⟩ :=
    exists_subdivision_finset_vertex_image K hS.toFinset
  refine ⟨ι', inferInstance, K', e, {u : ι' | e (K'.vertex u) ∈ S}, hfin, hman, ?_⟩
  ext s
  constructor
  · rintro ⟨_, ⟨u, hu, rfl⟩, rfl⟩
    exact hu
  · intro hs
    obtain ⟨u, hu⟩ := hvert s (hS.mem_toFinset.mpr hs)
    exact ⟨K'.vertex u, ⟨u, by simpa [hu] using hs, rfl⟩, hu⟩

end StellarVertexPlacement

end AbstractSimplicialComplex
