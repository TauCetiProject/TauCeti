/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.SimplicialComplex.Realization.Coordinates
import Mathlib.Topology.Order.Lattice

/-!
# Moving a point inside an open simplex by radial scaling

Given two points `b` and `x` in the weak realization `Realization K` with the same carrier
`σ = b.val.support = x.val.support`, the map
`y ↦ y + (min_{i ∈ σ} y i / b i) • (x - b)`
is a self-homeomorphism of `Realization K` that sends `b` to `x` and fixes every point whose
support does not contain `σ` (in particular, every vertex when `1 < σ.card`).

No finiteness or local-finiteness hypothesis on `K` is needed: continuity is checked on each
closed simplex `StandardSimplex τ.val` using `continuous_iff_faceInclusion`.

## Main definitions

* `AbstractSimplicialComplex.simplexMoveHomeomorph`: radial self-homeomorphism of `Realization K`
  moving `b` to `x` inside the open simplex `σ` while fixing every point whose support does not
  contain `σ`.

## References

* C. P. Rourke, B. J. Sanderson, *Introduction to Piecewise-Linear Topology*, Springer (1972),
  Chapter 2 (elementary radial homeomorphisms on stars of simplices).
-/

public section

noncomputable section

open Set Finset

namespace AbstractSimplicialComplex

variable {ι : Type*} (K : AbstractSimplicialComplex ι)

/-- The radial scale factor `min_{i ∈ σ} y i / b i` controlling movement from `b` toward `x`
inside the open star of `σ`. -/
private def simplexMoveFactor {σ : Finset ι} (b : Realization K) (hb : b.val.support = σ)
    (y : Realization K) : ℝ :=
  σ.inf' (hb ▸ K.isRelLowerSet_faces.prop_of_mem (support_mem K b)) fun i => y.val i / b.val i

private theorem simplexMoveFactor_def {σ : Finset ι} (b : Realization K)
    (hb : b.val.support = σ) (y : Realization K) :
    simplexMoveFactor K b hb y =
      σ.inf' (hb ▸ K.isRelLowerSet_faces.prop_of_mem (support_mem K b))
        fun i => y.val i / b.val i :=
  rfl

private theorem simplexMoveFactor_nonneg {σ : Finset ι} (b : Realization K)
    (hb : b.val.support = σ) (y : Realization K) :
    0 ≤ simplexMoveFactor K b hb y := by
  refine (Finset.le_inf'_iff _ _).mpr fun i _ => ?_
  exact div_nonneg (Realization.nonneg K y i) (Realization.nonneg K b i)

private theorem simplexMoveFactor_eq_zero_of_not_subset {σ : Finset ι} (b : Realization K)
    (hb : b.val.support = σ) {y : Realization K} (hy : ¬ σ ⊆ y.val.support) :
    simplexMoveFactor K b hb y = 0 := by
  obtain ⟨i, hiσ, hiy⟩ := Finset.not_subset.mp hy
  have hy0 : y.val i = 0 := Finsupp.notMem_support_iff.mp hiy
  refine le_antisymm ?_ (simplexMoveFactor_nonneg K b hb y)
  calc
    simplexMoveFactor K b hb y ≤ y.val i / b.val i := Finset.inf'_le _ hiσ
    _ = 0 := by simp [hy0]

private theorem simplexMoveFactor_mul_le {σ : Finset ι} (b : Realization K)
    (hb : b.val.support = σ) (y : Realization K) {i : ι} (hi : i ∈ σ) :
    simplexMoveFactor K b hb y * b.val i ≤ y.val i := by
  have hbpos : 0 < b.val i :=
    Realization.pos_of_mem_support K b (hb.symm ▸ hi)
  exact (le_div_iff₀ hbpos).mp (Finset.inf'_le _ hi)

private theorem simplexMoveFun_mem {σ : Finset ι}
    (b x : Realization K) (hb : b.val.support = σ) (hx : x.val.support = σ)
    (y : Realization K) :
    y.val + simplexMoveFactor K b hb y • (x.val - b.val) ∈
      (standardGeometricComplex K).space := by
  let α := simplexMoveFactor K b hb y
  have hα : 0 ≤ α := simplexMoveFactor_nonneg K b hb y
  have hcoord : ∀ i, 0 ≤ (y.val + α • (x.val - b.val)) i := by
    intro i
    simp only [Finsupp.coe_add, Finsupp.coe_smul, Finsupp.coe_sub, Pi.add_apply,
      Pi.smul_apply, Pi.sub_apply, smul_eq_mul]
    by_cases hi : i ∈ σ
    · have hle := simplexMoveFactor_mul_le K b hb y hi
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
    · have hα0 : α = 0 := simplexMoveFactor_eq_zero_of_not_subset K b hb hsub
      simpa [α, hα0] using support_mem K y
  exact TauCeti.mem_standardGeometricComplex_space_iff.mpr ⟨hcoord, hsum, hsup⟩

private def simplexMoveFun {σ : Finset ι}
    (b x : Realization K) (hb : b.val.support = σ) (hx : x.val.support = σ)
    (y : Realization K) : Realization K :=
  ⟨y.val + simplexMoveFactor K b hb y • (x.val - b.val),
    simplexMoveFun_mem K b x hb hx y⟩

private theorem simplexMoveFun_val {σ : Finset ι}
    (b x : Realization K) (hb : b.val.support = σ) (hx : x.val.support = σ)
    (y : Realization K) :
    (simplexMoveFun K b x hb hx y).val =
      y.val + simplexMoveFactor K b hb y • (x.val - b.val) :=
  rfl

private theorem simplexMoveFun_of_not_subset {σ : Finset ι}
    (b x : Realization K) (hb : b.val.support = σ) (hx : x.val.support = σ)
    {y : Realization K} (hy : ¬ σ ⊆ y.val.support) :
    simplexMoveFun K b x hb hx y = y := by
  apply Subtype.ext
  rw [simplexMoveFun_val, simplexMoveFactor_eq_zero_of_not_subset K b hb hy, zero_smul,
    add_zero]

private theorem simplexMoveFactor_comp {σ : Finset ι}
    (b x : Realization K) (hb : b.val.support = σ) (hx : x.val.support = σ)
    (y : Realization K) :
    simplexMoveFactor K x hx (simplexMoveFun K b x hb hx y) =
      simplexMoveFactor K b hb y := by
  by_cases hsub : σ ⊆ y.val.support
  · have hσ : σ.Nonempty := hb ▸ K.isRelLowerSet_faces.prop_of_mem (support_mem K b)
    obtain ⟨j, hjσ, hjmin⟩ := Finset.exists_mem_eq_inf' hσ fun i => y.val i / b.val i
    have hxj : 0 < x.val j := Realization.pos_of_mem_support K x (hx ▸ hjσ)
    have hbj : 0 < b.val j := Realization.pos_of_mem_support K b (hb ▸ hjσ)
    have hyj : y.val j = simplexMoveFactor K b hb y * b.val j := by
      rw [simplexMoveFactor_def, hjmin, div_mul_cancel₀ _ hbj.ne']
    have hzxj : (simplexMoveFun K b x hb hx y).val j / x.val j =
        simplexMoveFactor K b hb y := by
      rw [simplexMoveFun_val, Finsupp.coe_add, Finsupp.coe_smul, Finsupp.coe_sub,
        Pi.add_apply, Pi.smul_apply, Pi.sub_apply, smul_eq_mul, hyj]
      field_simp [hxj.ne']
      ring
    refine le_antisymm ?_ ((Finset.le_inf'_iff _ _).mpr fun i hi => ?_)
    · exact (Finset.inf'_le (fun i => (simplexMoveFun K b x hb hx y).val i / x.val i) hjσ).trans
        hzxj.le
    · have hxi : 0 < x.val i := Realization.pos_of_mem_support K x (hx ▸ hi)
      have hle := simplexMoveFactor_mul_le K b hb y hi
      have hzi : simplexMoveFactor K b hb y * x.val i ≤ (simplexMoveFun K b x hb hx y).val i := by
        rw [simplexMoveFun_val, Finsupp.coe_add, Finsupp.coe_smul, Finsupp.coe_sub,
          Pi.add_apply, Pi.smul_apply, Pi.sub_apply, smul_eq_mul]
        linarith
      exact (le_div_iff₀ hxi).mpr hzi
  · rw [simplexMoveFun_of_not_subset K b x hb hx hsub,
      simplexMoveFactor_eq_zero_of_not_subset K x hx hsub,
      simplexMoveFactor_eq_zero_of_not_subset K b hb hsub]

private theorem simplexMoveFun_left_inv {σ : Finset ι}
    (b x : Realization K) (hb : b.val.support = σ) (hx : x.val.support = σ)
    (y : Realization K) :
    simplexMoveFun K x b hx hb (simplexMoveFun K b x hb hx y) = y := by
  apply Subtype.ext
  rw [simplexMoveFun_val, simplexMoveFun_val, simplexMoveFactor_comp K b x hb hx y]
  ext i
  simp only [Finsupp.coe_add, Finsupp.coe_smul, Finsupp.coe_sub, Pi.add_apply,
    Pi.smul_apply, Pi.sub_apply, smul_eq_mul]
  ring

private theorem continuous_simplexMoveFun {σ : Finset ι}
    (b x : Realization K) (hb : b.val.support = σ) (hx : x.val.support = σ) :
    Continuous (simplexMoveFun K b x hb hx) := by
  refine continuous_iff_faceInclusion.mpr fun τ => ?_
  have hsub (y : StandardSimplex τ.val) :
      (simplexMoveFun K b x hb hx (faceInclusion K τ y)).val.support ⊆ τ.val := by
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
    · rw [simplexMoveFun_of_not_subset K b x hb hx hσf]
      simpa [fy, faceInclusion_val] using StandardSimplex.support_subset y
  let g : StandardSimplex τ.val → StandardSimplex τ.val := fun y =>
    ⟨(simplexMoveFun K b x hb hx (faceInclusion K τ y)).val,
      Realization.mem_convexHull_of_support_subset K _ (hsub y)⟩
  have hfg : simplexMoveFun K b x hb hx ∘ faceInclusion K τ = faceInclusion K τ ∘ g := by
    funext y
    exact Subtype.ext (faceInclusion_val K τ (g y)).symm
  rw [hfg]
  refine (continuous_faceInclusion K τ).comp ?_
  refine continuous_induced_rng.mpr (continuous_pi fun i => ?_)
  have hcoord : ∀ j : ι, Continuous (fun y : StandardSimplex τ.val => (y.val j : ℝ)) :=
    fun j => (continuous_apply j).comp continuous_induced_dom
  have hσ : σ.Nonempty := hb ▸ K.isRelLowerSet_faces.prop_of_mem (support_mem K b)
  have hfac : Continuous (fun y : StandardSimplex τ.val =>
      simplexMoveFactor K b hb (faceInclusion K τ y)) := by
    have hinf : Continuous fun y : StandardSimplex τ.val =>
        σ.inf' hσ fun j => (y.val j : ℝ) / b.val j :=
      Continuous.finset_inf'_apply hσ fun j _ => (hcoord j).div_const (b.val j)
    simpa [simplexMoveFactor_def, faceInclusion_val] using hinf
  dsimp only [Function.comp_apply]
  have hgval : (fun y : StandardSimplex τ.val => ((g y).val : ι → ℝ) i) = fun y =>
      y.val i + simplexMoveFactor K b hb (faceInclusion K τ y) * (x.val i - b.val i) := by
    funext y
    simp [g, simplexMoveFun_val, faceInclusion_val]
  rw [hgval]
  exact (hcoord i).add (hfac.mul continuous_const)

/-- Radial self-homeomorphism of `Realization K` moving `b` to `x` inside the open simplex `σ`,
fixing every point whose support does not contain `σ` (in particular every vertex when
`1 < σ.card`). Works for arbitrary complexes without any finiteness hypothesis. -/
def simplexMoveHomeomorph {σ : Finset ι}
    (b x : Realization K) (hb : b.val.support = σ) (hx : x.val.support = σ) :
    Realization K ≃ₜ Realization K where
  toFun := simplexMoveFun K b x hb hx
  invFun := simplexMoveFun K x b hx hb
  left_inv := simplexMoveFun_left_inv K b x hb hx
  right_inv := simplexMoveFun_left_inv K x b hx hb
  continuous_toFun := continuous_simplexMoveFun K b x hb hx
  continuous_invFun := continuous_simplexMoveFun K x b hx hb

private theorem simplexMoveHomeomorph_apply {σ : Finset ι}
    (b x : Realization K) (hb : b.val.support = σ) (hx : x.val.support = σ)
    (y : Realization K) :
    simplexMoveHomeomorph K b x hb hx y = simplexMoveFun K b x hb hx y :=
  (rfl)

/-- Inverting `simplexMoveHomeomorph` swaps the two open-simplex endpoints `b` and `x`. -/
@[simp]
theorem simplexMoveHomeomorph_symm {σ : Finset ι}
    (b x : Realization K) (hb : b.val.support = σ) (hx : x.val.support = σ) :
    (simplexMoveHomeomorph K b x hb hx).symm =
      simplexMoveHomeomorph K x b hx hb := by
  ext y
  rfl

/-- `simplexMoveHomeomorph` sends `b` to `x`. -/
@[simp]
theorem simplexMoveHomeomorph_apply_left {σ : Finset ι}
    (b x : Realization K) (hb : b.val.support = σ) (hx : x.val.support = σ) :
    simplexMoveHomeomorph K b x hb hx b = x := by
  apply Subtype.ext
  rw [simplexMoveHomeomorph_apply, simplexMoveFun_val]
  have hσ : σ.Nonempty := hb ▸ K.isRelLowerSet_faces.prop_of_mem (support_mem K b)
  have hfac : simplexMoveFactor K b hb b = 1 := by
    refine le_antisymm ?_ ((Finset.le_inf'_iff hσ _).mpr fun i hi => ?_)
    · obtain ⟨i, hi⟩ := hσ
      have hbi : b.val i ≠ 0 := Finsupp.mem_support_iff.mp (hb ▸ hi)
      calc
        simplexMoveFactor K b hb b ≤ b.val i / b.val i := Finset.inf'_le _ hi
        _ = 1 := div_self hbi
    · have hbi : b.val i ≠ 0 := Finsupp.mem_support_iff.mp (hb ▸ hi)
      rw [div_self hbi]
  rw [hfac, one_smul]
  abel

/-- `simplexMoveHomeomorph` fixes every point whose support does not contain `σ`. -/
theorem simplexMoveHomeomorph_apply_of_not_subset {σ : Finset ι}
    (b x : Realization K) (hb : b.val.support = σ) (hx : x.val.support = σ)
    {y : Realization K} (hy : ¬ σ ⊆ y.val.support) :
    simplexMoveHomeomorph K b x hb hx y = y :=
  simplexMoveFun_of_not_subset K b x hb hx hy

/-- When `1 < σ.card`, `simplexMoveHomeomorph` fixes every vertex of `K`. -/
theorem simplexMoveHomeomorph_vertex {σ : Finset ι}
    (b x : Realization K) (hb : b.val.support = σ) (hx : x.val.support = σ)
    (hcard : 1 < σ.card) (w : ι) :
    simplexMoveHomeomorph K b x hb hx (K.vertex w) = K.vertex w := by
  refine simplexMoveHomeomorph_apply_of_not_subset K b x hb hx fun hsub => ?_
  rw [support_vertex] at hsub
  have hle := (Finset.card_le_card hsub).trans (Finset.card_singleton w).le
  omega

end AbstractSimplicialComplex
