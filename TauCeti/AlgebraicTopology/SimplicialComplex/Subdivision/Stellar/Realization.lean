/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.SimplicialComplex.Realization.Coordinates
public import TauCeti.AlgebraicTopology.SimplicialComplex.Subdivision.Stellar.Basic

/-!
# The barycentric identification for stellar subdivision

Place the new vertex of a stellar subdivision at the barycenter of the starred face, fixing
all other vertices, and extend linearly in barycentric coordinates. This map identifies the
subdivided polyhedron bijectively with the original polyhedron. The complexes may be infinite
and may have unused vertices. This is the point-set identification; no topology on the
precomplex polyhedra or piecewise-linear compatibility is asserted here.

The module supplies the linear map, its coordinate and vertex formulas, mass preservation,
and its image, injectivity, and surjectivity properties on the corresponding polyhedra.
Together these give a point-set identification for the geometric realization of a stellar move.

## References

* C. P. Rourke, B. J. Sanderson, *Introduction to Piecewise-Linear Topology*, Springer
  (1972), Chapter 2 (starrings and subdivisions).

The coordinate construction follows the barycentric map in
`TauCeti.AlgebraicTopology.SimplicialComplex.Subdivision.Realization`, using the same
Mathlib `Geometry.SimplicialComplex.onFinsupp` realization.
-/

public section

noncomputable section

open Set

namespace Finset

variable {ι : Type*} [DecidableEq ι] {σ : Finset ι} {v : ι}

/-- Replace the coordinate vector of `v` by the normalized coordinate sum over `σ`, fixing
all other vertices. This sum is the barycenter when `σ` is nonempty, and zero when `σ` is empty.
On the stellar subdivision at `σ` with fresh vertex `v`, this is the barycentric realization
map to the original polyhedron. -/
def stellarSubdivisionLinearMap (σ : Finset ι) (v : ι) : (ι →₀ ℝ) →ₗ[ℝ] (ι →₀ ℝ) :=
  LinearMap.id + (Finsupp.lapply v).smulRight
    ((∑ i ∈ σ, Finsupp.single i ((σ.card : ℝ)⁻¹)) - Finsupp.single v 1)

/-- The coordinate formula for the stellar realization map. -/
@[simp]
theorem stellarSubdivisionLinearMap_apply (σ : Finset ι) (v : ι) (x : ι →₀ ℝ) (i : ι) :
    stellarSubdivisionLinearMap σ v x i =
      x i + x v * ((if i ∈ σ then (σ.card : ℝ)⁻¹ else 0) - if i = v then 1 else 0) := by
  simp [stellarSubdivisionLinearMap, Finsupp.single_apply, eq_comm]

omit [DecidableEq ι] in
/-- Every old vertex is fixed by the realization map. -/
@[simp]
theorem stellarSubdivisionLinearMap_single_of_ne {w : ι} (hw : w ≠ v) (r : ℝ) :
    stellarSubdivisionLinearMap σ v (Finsupp.single w r) = Finsupp.single w r := by
  simp [stellarSubdivisionLinearMap, hw]

omit [DecidableEq ι] in
/-- The coordinate vector of `v` is sent to the normalized coordinate sum over `σ`,
which is the barycenter when `σ` is nonempty, and zero when `σ` is empty. -/
@[simp]
theorem stellarSubdivisionLinearMap_single :
    stellarSubdivisionLinearMap σ v (Finsupp.single v 1) =
      ∑ i ∈ σ, Finsupp.single i ((σ.card : ℝ)⁻¹) := by
  simp [stellarSubdivisionLinearMap]

omit [DecidableEq ι] in
/-- The stellar realization map preserves total barycentric mass when the starred face
is nonempty. -/
@[simp]
theorem sum_stellarSubdivisionLinearMap (hσ : σ.Nonempty) (x : ι →₀ ℝ) :
    (stellarSubdivisionLinearMap σ v x).sum (fun _ r => r) = x.sum (fun _ r => r) := by
  let S := Finsupp.linearCombination ℝ (fun _ : ι => (1 : ℝ))
  have hS (y : ι →₀ ℝ) : S y = y.sum (fun _ r => r) := by
    simp [S, Finsupp.linearCombination_apply]
  rw [← hS, ← hS]
  have hc : (σ.card : ℝ) ≠ 0 := by exact_mod_cast hσ.card_pos.ne'
  simp [stellarSubdivisionLinearMap, map_add, map_smul, map_sub, map_sum, S, hc]

end Finset

namespace PreAbstractSimplicialComplex

open Finset

variable {ι : Type*} [DecidableEq ι] {K : PreAbstractSimplicialComplex ι}
  {σ : Finset ι} {v : ι}

private theorem exists_zero_coordinate {x : ι →₀ ℝ} (hvσ : v ∉ σ)
    (hx : x.support ∈ stellarSubdivision K σ v) :
    ∃ i ∈ σ, x i = 0 := by
  obtain ⟨i, hi, hix⟩ := exists_notMem_of_mem_stellarSubdivision hvσ hx
  exact ⟨i, hi, Finsupp.notMem_support_iff.mp hix⟩

/-- The barycentric map sends the stellar polyhedron into the original polyhedron. -/
theorem mapsTo_stellarSubdivisionLinearMap (hvσ : v ∉ σ) :
    MapsTo (stellarSubdivisionLinearMap σ v)
      (Geometry.SimplicialComplex.onFinsupp (𝕜 := ℝ) (stellarSubdivision K σ v)).space
      (Geometry.SimplicialComplex.onFinsupp (𝕜 := ℝ) K).space := by
  intro x hx
  obtain ⟨hxpos, hxsum, hxface⟩ := Geometry.SimplicialComplex.mem_space_onFinsupp_iff.mp hx
  by_cases hσempty : σ = ∅
  · subst σ
    rw [mem_stellarSubdivision_iff] at hxface
    simp at hxface
  have hσne : σ.Nonempty := Finset.nonempty_iff_ne_empty.mpr hσempty
  rw [Geometry.SimplicialComplex.mem_space_onFinsupp_iff]
  refine ⟨?_, (sum_stellarSubdivisionLinearMap hσne x).trans hxsum, ?_⟩
  · intro i
    rw [stellarSubdivisionLinearMap_apply]
    by_cases hiv : i = v
    · subst i
      simp [hvσ]
    · simp only [hiv, ite_false, sub_zero]
      exact add_nonneg (hxpos i) (mul_nonneg (hxpos v) (by split_ifs <;> positivity))
  · by_cases hvx : v ∈ x.support
    · have hold : x.support.erase v ∪ σ ∈ K :=
        (mem_stellarSubdivision_iff.mp hxface).resolve_left (by simp [hvx]) |>.2.2
      apply K.isRelLowerSet_faces.mem_of_le hold
      · intro i hi
        by_contra hnot
        have his : i ∉ σ := fun h => hnot (Finset.mem_union_right _ h)
        have hiv : i ≠ v := by
          intro h
          subst i
          have hz : stellarSubdivisionLinearMap σ v x v = 0 := by
            simp [stellarSubdivisionLinearMap_apply, hvσ]
          exact Finsupp.mem_support_iff.mp hi hz
        have hix : x i = 0 := Finsupp.notMem_support_iff.mp fun h =>
          hnot (Finset.mem_union_left _ (Finset.mem_erase.mpr ⟨hiv, h⟩))
        exact Finsupp.mem_support_iff.mp hi (by
          simp [stellarSubdivisionLinearMap_apply, his, hiv, hix])
      · apply Finsupp.support_nonempty_iff.mpr
        intro hz
        have hm := (sum_stellarSubdivisionLinearMap (v := v) hσne x).trans hxsum
        simp [hz] at hm
    · have hxv : x v = 0 := Finsupp.notMem_support_iff.mp hvx
      have heq : stellarSubdivisionLinearMap σ v x = x := by
        ext i
        simp [stellarSubdivisionLinearMap_apply, hxv]
      rw [heq]
      exact ((mem_stellarSubdivision_iff_of_notMem hvx).mp hxface).1

/-- The barycentric map is injective on the stellar polyhedron when the new vertex
lies outside the starred face. -/
theorem injOn_stellarSubdivisionLinearMap (hvσ : v ∉ σ) :
    InjOn (stellarSubdivisionLinearMap σ v)
      (Geometry.SimplicialComplex.onFinsupp (𝕜 := ℝ) (stellarSubdivision K σ v)).space := by
  intro x hx y hy heq
  obtain ⟨hxpos, -, hxface⟩ := Geometry.SimplicialComplex.mem_space_onFinsupp_iff.mp hx
  obtain ⟨hypos, -, hyface⟩ := Geometry.SimplicialComplex.mem_space_onFinsupp_iff.mp hy
  obtain ⟨i, hi, hxi⟩ := exists_zero_coordinate hvσ hxface
  obtain ⟨j, hj, hyj⟩ := exists_zero_coordinate hvσ hyface
  have hiv : i ≠ v := fun h => hvσ (h ▸ hi)
  have hjv : j ≠ v := fun h => hvσ (h ▸ hj)
  have hei := DFunLike.congr_fun heq i
  have hej := DFunLike.congr_fun heq j
  simp only [stellarSubdivisionLinearMap_apply, hi, hj, ite_true, hiv, hjv, ite_false,
    sub_zero, hxi, hyj, zero_add] at hei hej
  have hσne : σ.Nonempty := ⟨i, hi⟩
  have hc : 0 < (σ.card : ℝ)⁻¹ := inv_pos.mpr (by exact_mod_cast hσne.card_pos)
  have hxyv : x v = y v := by nlinarith [hxpos j, hypos i]
  ext k
  have hek := DFunLike.congr_fun heq k
  simp only [stellarSubdivisionLinearMap_apply, hxyv] at hek
  exact add_right_cancel hek

omit [DecidableEq ι] in
private theorem stellarSubdivisionLinearMap_lift (hσ : σ.Nonempty) (hvσ : v ∉ σ)
    {x : ι →₀ ℝ} (hxv : x v = 0) (m : ℝ) :
    stellarSubdivisionLinearMap σ v
      (x + m • ((σ.card : ℝ) • Finsupp.single v 1 - ∑ i ∈ σ, Finsupp.single i 1)) = x := by
  classical
  have hcoord (i : ι) :
      (x + m • ((σ.card : ℝ) • Finsupp.single v 1 - ∑ j ∈ σ, Finsupp.single j 1) :
        ι →₀ ℝ) i =
        x i + m * ((if i = v then (σ.card : ℝ) else 0) - if i ∈ σ then 1 else 0) := by
    simp [Finsupp.single_apply, eq_comm]
  ext i
  have hc : (σ.card : ℝ) ≠ 0 := by exact_mod_cast hσ.card_pos.ne'
  rw [stellarSubdivisionLinearMap_apply, hcoord i, hcoord v]
  simp only [hxv, ite_true, hvσ, ite_false, sub_zero, zero_add]
  by_cases hiv : i = v <;> by_cases his : i ∈ σ <;> simp [hiv, his, hvσ, hxv, hc]

/-- Every point of the original polyhedron has a preimage in the stellar polyhedron
when the starred face belongs to the original complex and the new vertex is unused. -/
theorem surjOn_stellarSubdivisionLinearMap (hσ : σ ∈ K) (hv : ({v} : Finset ι) ∉ K) :
    SurjOn (stellarSubdivisionLinearMap σ v)
      (Geometry.SimplicialComplex.onFinsupp (𝕜 := ℝ) (stellarSubdivision K σ v)).space
      (Geometry.SimplicialComplex.onFinsupp (𝕜 := ℝ) K).space := by
  intro x hx
  obtain ⟨hxpos, hxsum, hxface⟩ := Geometry.SimplicialComplex.mem_space_onFinsupp_iff.mp hx
  have hvσ := notMem_of_singleton_notMem hv hσ
  have hvx := notMem_of_singleton_notMem hv hxface
  have hxv : x v = 0 := Finsupp.notMem_support_iff.mp hvx
  have hfix : stellarSubdivisionLinearMap σ v x = x := by
    ext i
    simp [stellarSubdivisionLinearMap_apply, hxv]
  by_cases hsub : σ ⊆ x.support
  · have hσne := (K.isRelLowerSet_faces hσ).1
    obtain ⟨a, ha, hmin⟩ := (σ : Set ι).exists_min_image (fun i => x i)
      σ.finite_toSet hσne
    have haσ : a ∈ σ := ha
    have hav : a ≠ v := fun h => hvσ (h ▸ ha)
    let c : ι →₀ ℝ := ∑ i ∈ σ, Finsupp.single i 1
    let y : ι →₀ ℝ := x + x a • ((σ.card : ℝ) • Finsupp.single v 1 - c)
    have hycoord (i : ι) : y i = x i + x a *
        ((if i = v then (σ.card : ℝ) else 0) - if i ∈ σ then 1 else 0) := by
      simp [y, c, Finsupp.single_apply, eq_comm]
    -- Remove equal mass on σ and transfer it to v, preserving nonnegativity.
    have hypos : ∀ i, 0 ≤ y i := by
      intro i
      rw [hycoord]
      by_cases hiv : i = v
      · subst i
        simp only [hxv, ite_true, hvσ, ite_false, sub_zero, zero_add]
        exact mul_nonneg (hxpos a) (Nat.cast_nonneg _)
      · by_cases his : i ∈ σ
        · simp only [hiv, ite_false, his, ite_true, zero_sub, mul_neg_one]
          linarith [hmin i his]
        · simpa [hiv, his] using hxpos i
    have hya : y a = 0 := by simp [hycoord, haσ, hav]
    have hyne : y.support.Nonempty := by
      have hsum : y.sum (fun _ r => r) = 1 := by
        let S := Finsupp.linearCombination ℝ (fun _ : ι => (1 : ℝ))
        have hS (z : ι →₀ ℝ) : S z = z.sum (fun _ r => r) := by
          simp [S, Finsupp.linearCombination_apply]
        rw [← hS]
        have hSx : S x = 1 := (hS x).trans hxsum
        simp [y, c, map_add, map_smul, map_sub, map_sum, hSx, S]
      apply Finsupp.support_nonempty_iff.mpr
      intro hz
      simp [hz] at hsum
    -- The least coordinate vanishes, and every other old coordinate stays in the old face.
    have hysub : y.support.erase v ⊆ x.support := by
      intro i hi
      obtain ⟨hiv, hiy⟩ := Finset.mem_erase.mp hi
      by_contra hix
      have his : i ∉ σ := fun h => hix (hsub h)
      have hxzero := Finsupp.notMem_support_iff.mp hix
      exact Finsupp.mem_support_iff.mp hiy (by simp [hycoord, hiv, his, hxzero])
    have hylower : ¬ σ ⊆ y.support := fun h =>
      Finsupp.mem_support_iff.mp (h ha) hya
    have hyunion : y.support.erase v ∪ σ ∈ K :=
      K.isRelLowerSet_faces.mem_of_le hxface (Finset.union_subset hysub hsub)
        (hσne.mono Finset.subset_union_right)
    have hyface : y.support ∈ stellarSubdivision K σ v := by
      rw [mem_stellarSubdivision_iff]
      by_cases hvy : v ∈ y.support
      · exact Or.inr ⟨hvy, fun h => hylower (h.trans (Finset.erase_subset _ _)), hyunion⟩
      · refine Or.inl ⟨hvy, ?_, hylower⟩
        exact K.isRelLowerSet_faces.mem_of_le hxface
          (by simpa [Finset.erase_eq_of_notMem hvy] using hysub) hyne
    have hyimage : stellarSubdivisionLinearMap σ v y = x :=
      stellarSubdivisionLinearMap_lift hσne hvσ hxv (x a)
    -- The linear map undoes the transfer; mass preservation supplies the final normalization.
    refine ⟨y, Geometry.SimplicialComplex.mem_space_onFinsupp_iff.mpr
      ⟨hypos, ?_, hyface⟩, hyimage⟩
    rw [← sum_stellarSubdivisionLinearMap hσne y, hyimage]
    exact hxsum
  · refine ⟨x, Geometry.SimplicialComplex.mem_space_onFinsupp_iff.mpr
      ⟨hxpos, hxsum, (mem_stellarSubdivision_iff_of_notMem hvx).mpr ⟨hxface, hsub⟩⟩, hfix⟩

/-- Placing the new vertex at the barycenter identifies the polyhedron of a stellar
subdivision bijectively with the original polyhedron. No finiteness assumption is needed. -/
theorem bijOn_stellarSubdivisionLinearMap (hσ : σ ∈ K) (hv : ({v} : Finset ι) ∉ K) :
    BijOn (stellarSubdivisionLinearMap σ v)
      (Geometry.SimplicialComplex.onFinsupp (𝕜 := ℝ) (stellarSubdivision K σ v)).space
      (Geometry.SimplicialComplex.onFinsupp (𝕜 := ℝ) K).space :=
  ⟨mapsTo_stellarSubdivisionLinearMap (notMem_of_singleton_notMem hv hσ),
    injOn_stellarSubdivisionLinearMap (notMem_of_singleton_notMem hv hσ),
    surjOn_stellarSubdivisionLinearMap hσ hv⟩

end PreAbstractSimplicialComplex
