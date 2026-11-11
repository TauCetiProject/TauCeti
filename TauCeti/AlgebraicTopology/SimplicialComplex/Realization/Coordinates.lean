/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.SimplicialComplex.Realization.Basic
public import Mathlib.Analysis.Normed.Group.Constructions
public import Mathlib.Analysis.Normed.Group.Real
import all TauCeti.AlgebraicTopology.SimplicialComplex.Realization.Basic

/-!
# Coordinates of polyhedra with unused vertices

The standard polyhedron of a precomplex consists of nonnegative barycentric coordinates
summing to one whose support is a face. Unlike an abstract complex on a fixed vertex type,
a precomplex can leave vertices unused. This characterization therefore applies to geometric
moves which add or remove vertices, including stellar subdivision and elementary collapse.

The construction reuses Mathlib's `Geometry.SimplicialComplex.onFinsupp` and the standard
simplex coordinate API in `Realization.Basic`.

On a finite vertex type, the coordinate vectors of a closed simplex form a convex set described by
`AbstractSimplicialComplex.mem_range_standardSimplex_coe_iff`. Two nearby points of two closed
simplices have a common nearby point of both simplices
(`AbstractSimplicialComplex.exists_mem_inter_range_standardSimplex_coe`), the step that passes
metric estimates on single closed simplices between simplices.
-/

public section

open Set

attribute [local instance] Classical.decEq

namespace Finsupp

variable {ι : Type*}

/-- The finite-coordinate linear equivalence carries the standard coordinate simplex to the
finitely supported coordinate simplex. -/
theorem mem_convexHull_single_equivFunOnFinite [Finite ι]
    {τ : Finset ι} {x : ι → ℝ}
    (hx : x ∈ convexHull ℝ ((Pi.single · (1 : ℝ)) '' (τ : Set ι))) :
    equivFunOnFinite.symm x ∈
      convexHull ℝ ((Finsupp.single · (1 : ℝ)) '' (τ : Set ι)) := by
  classical
  have him := (linearEquivFunOnFinite ℝ ℝ ι).symm.toLinearMap.image_convexHull
      ((Pi.single · (1 : ℝ)) '' (τ : Set ι))
  have hxf' : (linearEquivFunOnFinite ℝ ℝ ι).symm x ∈
      (linearEquivFunOnFinite ℝ ℝ ι).symm '' convexHull ℝ
      ((Pi.single · (1 : ℝ)) '' (τ : Set ι)) := ⟨x, hx, rfl⟩
  have hxf₀ := him ▸ hxf'
  have himage : (linearEquivFunOnFinite ℝ ℝ ι).symm ''
      ((Pi.single · (1 : ℝ)) '' (τ : Set ι)) =
      (Finsupp.single · (1 : ℝ)) '' (τ : Set ι) := by
    ext z
    constructor
    · rintro ⟨y, ⟨i, hi, rfl⟩, rfl⟩
      have hi_single : (linearEquivFunOnFinite ℝ ℝ ι).symm (Pi.single i 1) =
          Finsupp.single i 1 :=
        linearEquivFunOnFinite_symm_single ℝ ℝ ι i 1
      exact ⟨i, hi, hi_single.symm⟩
    · rintro ⟨i, hi, rfl⟩
      have hi_single : (linearEquivFunOnFinite ℝ ℝ ι).symm (Pi.single i 1) =
          Finsupp.single i 1 :=
        linearEquivFunOnFinite_symm_single ℝ ℝ ι i 1
      exact ⟨Pi.single (i : ι) 1, ⟨i, hi, rfl⟩, hi_single⟩
  have hxf₁ : (linearEquivFunOnFinite ℝ ℝ ι).symm x ∈ convexHull ℝ
      ((Finsupp.single · (1 : ℝ)) '' (τ : Set ι)) := by
    convert hxf₀ using 1
    exact congrArg (convexHull ℝ) himage.symm
  exact hxf₁

end Finsupp

namespace Geometry.SimplicialComplex

variable {ι : Type*} [DecidableEq ι]

/-- A point of the standard polyhedron has nonnegative coordinates summing to one and
support a face, including for precomplexes with unused vertices. -/
@[simp]
theorem mem_space_onFinsupp_iff {K : PreAbstractSimplicialComplex ι} {x : ι →₀ ℝ} :
    x ∈ (onFinsupp (𝕜 := ℝ) K).space ↔
      (∀ i, 0 ≤ x i) ∧ x.sum (fun _ r => r) = 1 ∧ x.support ∈ K := by
  classical
  have hfaces : ∀ τ, τ ∈ (onFinsupp (𝕜 := ℝ) K).faces ↔
      ∃ σ ∈ K, σ.image (fun i => Finsupp.single i (1 : ℝ)) = τ := by
    intro τ
    simp only [onFinsupp, ofAffineIndependent, PreAbstractSimplicialComplex.map, mem_image]
    aesop
  rw [mem_space_iff]
  constructor
  · rintro ⟨τ, hτ, hx⟩
    obtain ⟨σ, hσ, rfl⟩ := (hfaces τ).mp hτ
    rw [Finset.coe_image, AbstractSimplicialComplex.mem_standardSimplex_iff] at hx
    refine ⟨hx.1, hx.2.1, K.isRelLowerSet_faces.mem_of_le hσ hx.2.2 ?_⟩
    apply Finsupp.support_nonempty_iff.mpr
    intro hzero
    simp [hzero] at hx
  · rintro ⟨hnonneg, hsum, hsupp⟩
    refine ⟨x.support.image (fun i => Finsupp.single i (1 : ℝ)),
      (hfaces _).mpr ⟨x.support, hsupp, rfl⟩, ?_⟩
    rw [Finset.coe_image, AbstractSimplicialComplex.mem_standardSimplex_iff]
    exact ⟨hnonneg, hsum, Finset.Subset.rfl⟩

end Geometry.SimplicialComplex

open AbstractSimplicialComplex

namespace TauCeti

variable {ι : Type*}

/-- A point belongs to the standard realization exactly when its barycentric coordinates are
nonnegative, sum to one, and have support in the abstract simplicial complex. -/
@[simp]
theorem mem_standardGeometricComplex_space_iff {K : AbstractSimplicialComplex ι} {x : ι →₀ ℝ} :
    x ∈ (standardGeometricComplex K).space ↔
      (∀ i, 0 ≤ x i) ∧ x.sum (fun _ r => r) = 1 ∧ x.support ∈ K :=
  Geometry.SimplicialComplex.mem_space_onFinsupp_iff (K := K.toPreAbstractSimplicialComplex)

end TauCeti

namespace AbstractSimplicialComplex

variable {ι : Type*} [Fintype ι]

/-- On a finite vertex type, a coordinate vector is the coordinate vector of a point of the
realization exactly when it is nonnegative, sums to one, and its support is a face. -/
theorem mem_range_realization_coe_iff {K : AbstractSimplicialComplex ι} {z : ι → ℝ} :
    z ∈ range (fun x : Realization K => (x.1 : ι → ℝ)) ↔
      (∀ i, 0 ≤ z i) ∧ ∑ i, z i = 1 ∧ (Finsupp.equivFunOnFinite.symm z).support ∈ K := by
  constructor
  · rintro ⟨x, rfl⟩
    obtain ⟨hnn, hsum, hsupp⟩ := TauCeti.mem_standardGeometricComplex_space_iff.mp x.2
    refine ⟨hnn, ?_, by simpa using hsupp⟩
    rwa [Finsupp.sum_fintype _ _ (fun _ => rfl)] at hsum
  · rintro ⟨hnn, hsum, hsupp⟩
    refine ⟨⟨Finsupp.equivFunOnFinite.symm z, TauCeti.mem_standardGeometricComplex_space_iff.mpr
      ⟨hnn, ?_, hsupp⟩⟩, by simp⟩
    rwa [Finsupp.sum_fintype _ _ (fun _ => rfl)]

/-- On a finite vertex type, a coordinate vector is the coordinate vector of a point of the closed
simplex on `σ` exactly when it is nonnegative, vanishes off `σ`, and sums to one. -/
theorem mem_range_standardSimplex_coe_iff {σ : Finset ι} {z : ι → ℝ} :
    z ∈ range (fun x : StandardSimplex σ => (x.1 : ι → ℝ)) ↔
      (∀ i, 0 ≤ z i) ∧ (∀ i ∉ σ, z i = 0) ∧ ∑ i, z i = 1 := by
  constructor
  · rintro ⟨x, rfl⟩
    refine ⟨StandardSimplex.nonneg x, fun i hi => Finsupp.notMem_support_iff.mp fun h =>
      hi (StandardSimplex.support_subset x h), ?_⟩
    have hsum := StandardSimplex.sum_eq_one x
    rwa [Finsupp.sum_fintype _ _ (fun _ => rfl)] at hsum
  · rintro ⟨hnn, hzero, hsum⟩
    refine ⟨⟨Finsupp.equivFunOnFinite.symm z, ?_⟩, by simp⟩
    rw [Finset.coe_image, mem_standardSimplex_iff]
    refine ⟨hnn, by rwa [Finsupp.sum_fintype _ _ (fun _ => rfl)], fun i hi => ?_⟩
    by_contra h
    exact Finsupp.mem_support_iff.mp hi (hzero i h)

omit [Fintype ι] in
/-- The coordinate vectors of the closed simplex on `σ` form a convex set. -/
theorem convex_range_standardSimplex_coe (σ : Finset ι) :
    Convex ℝ (range fun x : StandardSimplex σ => (x.1 : ι → ℝ)) := by
  simpa [image_eq_range] using (convex_convexHull ℝ _).linear_image (Finsupp.lcoeFun (R := ℝ))

/-- A coordinate of `y` at a vertex outside `σ ∩ τ` is at most the distance from `x` to `y`. -/
private theorem coord_le_norm_sub {σ τ : Finset ι} {x y : ι → ℝ}
    (hx : x ∈ range fun x : StandardSimplex σ => (x.1 : ι → ℝ))
    (hy : y ∈ range fun x : StandardSimplex τ => (x.1 : ι → ℝ)) {i : ι} (hi : i ∈ σ → i ∉ τ) :
    y i ≤ ‖x - y‖ := by
  rw [mem_range_standardSimplex_coe_iff] at hx hy
  by_cases hτ : i ∈ τ
  · have hσ : i ∉ σ := fun hσ => hi hσ hτ
    have h := norm_le_pi_norm (x - y) i
    rw [Pi.sub_apply, hx.2.1 i hσ, zero_sub, norm_neg, Real.norm_of_nonneg (hy.1 i)] at h
    exact h
  · rw [hy.2.1 i hτ]
    exact norm_nonneg _

/-- The mass of `y` off `σ ∩ τ` is at most the number of vertices times the distance of `x`
and `y`, for `x` in the closed simplex on `σ` and `y` in that on `τ`. -/
private theorem sum_ite_mem_inter_le [DecidableEq ι] {σ τ : Finset ι} {x y : ι → ℝ}
    (hx : x ∈ range fun x : StandardSimplex σ => (x.1 : ι → ℝ))
    (hy : y ∈ range fun x : StandardSimplex τ => (x.1 : ι → ℝ)) :
    (∑ i, if i ∈ σ ∩ τ then 0 else y i) ≤ Fintype.card ι * ‖x - y‖ := by
  have hpt : ∀ i ∈ (Finset.univ : Finset ι), (if i ∈ σ ∩ τ then 0 else y i) ≤ ‖x - y‖ := by
    intro i _
    split_ifs with hi
    · exact norm_nonneg _
    · exact coord_le_norm_sub hx hy fun h h' => hi (Finset.mem_inter.2 ⟨h, h'⟩)
  simpa using Finset.sum_le_sum hpt

/-- A nonnegative vector of total mass `1` that vanishes off `σ ∩ τ` lies in both closed
simplices. -/
private theorem mem_inter_of_forall_notMem_eq_zero [DecidableEq ι] {σ τ : Finset ι}
    {w : ι → ℝ}
    (hw : ∀ i ∉ σ ∩ τ, w i = 0) (h0 : ∀ i, 0 ≤ w i) (h1 : ∑ i, w i = 1) :
    w ∈ (range fun x : StandardSimplex σ => (x.1 : ι → ℝ)) ∩
      range fun x : StandardSimplex τ => (x.1 : ι → ℝ) :=
  ⟨mem_range_standardSimplex_coe_iff.2
      ⟨h0, fun i hi => hw i fun hi' => hi (Finset.mem_inter.1 hi').1, h1⟩,
    mem_range_standardSimplex_coe_iff.2
      ⟨h0, fun i hi => hw i fun hi' => hi (Finset.mem_inter.1 hi').2, h1⟩⟩

/-- Two points of the closed simplices on `σ` and on `τ` at distance less than `1 / N`, where `N`
is the number of vertices, force the two simplices to meet: otherwise one of the two coordinates
vanishes at every vertex. -/
private theorem nonempty_inter {σ τ : Finset ι} [DecidableEq ι] {x y : ι → ℝ}
    (hx : x ∈ range fun x : StandardSimplex σ => (x.1 : ι → ℝ))
    (hy : y ∈ range fun x : StandardSimplex τ => (x.1 : ι → ℝ))
    (hxy : (Fintype.card ι : ℝ) * ‖x - y‖ < 1) : (σ ∩ τ).Nonempty := by
  by_contra hρ
  rw [Finset.not_nonempty_iff_eq_empty] at hρ
  have hle (i : ι) : x i + y i ≤ ‖x - y‖ := by
    by_cases hσ : i ∈ σ
    · have hτ : i ∉ τ := fun hτ => by
        have hi : i ∈ σ ∩ τ := Finset.mem_inter.2 ⟨hσ, hτ⟩
        rw [hρ] at hi
        exact Finset.notMem_empty i hi
      have h := coord_le_norm_sub hy hx (σ := τ) (τ := σ) (i := i) fun hi _ => hτ hi
      rw [(mem_range_standardSimplex_coe_iff.1 hy).2.1 i hτ, norm_sub_rev]
      simpa using h
    · rw [(mem_range_standardSimplex_coe_iff.1 hx).2.1 i hσ, zero_add]
      exact coord_le_norm_sub hx hy fun hi => absurd hi hσ
  have hsum := Finset.sum_le_sum fun i (_ : i ∈ Finset.univ) => hle i
  rw [Finset.sum_add_distrib, (mem_range_standardSimplex_coe_iff.1 hx).2.2,
    (mem_range_standardSimplex_coe_iff.1 hy).2.2, Finset.sum_const, Finset.card_univ,
    nsmul_eq_mul] at hsum
  linarith

/-- On a finite vertex type with `N` vertices, two points `x` and `y` of the closed simplices on
`σ` and on `τ` at distance less than `1 / N` have a common nearby point `z` of the two closed
simplices, with `‖y - z‖ ≤ N * ‖x - y‖`: move the coordinates of `y` off `σ ∩ τ` to the barycenter
`β` of `σ ∩ τ`. The barycenter `β` is also a common point, with coordinates at least `1 / N` on
`σ ∩ τ`. -/
theorem exists_mem_inter_range_standardSimplex_coe {σ τ : Finset ι} {x y : ι → ℝ}
    (hx : x ∈ range fun x : StandardSimplex σ => (x.1 : ι → ℝ))
    (hy : y ∈ range fun x : StandardSimplex τ => (x.1 : ι → ℝ))
    (hxy : (Fintype.card ι : ℝ) * ‖x - y‖ < 1) :
    ∃ z ∈ (range fun x : StandardSimplex σ => (x.1 : ι → ℝ)) ∩
        range fun x : StandardSimplex τ => (x.1 : ι → ℝ),
      ∃ β ∈ (range fun x : StandardSimplex σ => (x.1 : ι → ℝ)) ∩
          range fun x : StandardSimplex τ => (x.1 : ι → ℝ),
        ‖y - z‖ ≤ Fintype.card ι * ‖x - y‖ ∧
        ∀ i ∈ σ, i ∈ τ → (Fintype.card ι : ℝ)⁻¹ ≤ β i := by
  classical
  set N : ℝ := (Fintype.card ι : ℝ)
  set ρ := σ ∩ τ
  have hρ : ρ.Nonempty := nonempty_inter hx hy hxy
  have hy' := mem_range_standardSimplex_coe_iff.1 hy
  have hN : 1 ≤ N := by
    obtain ⟨i, -⟩ := hρ
    exact Nat.one_le_cast.2 (Fintype.card_pos_iff.2 ⟨i⟩)
  have hcard : (0 : ℝ) < ρ.card := by exact_mod_cast hρ.card_pos
  set c : ℝ := (ρ.card : ℝ)⁻¹
  have hc : 0 < c := inv_pos.2 hcard
  have hc1 : c ≤ 1 := inv_le_one_of_one_le₀ (by exact_mod_cast hρ.card_pos)
  -- The mass `m` of `y` off `σ ∩ τ`, which is at most `N` times the distance of `x` and `y`.
  set m : ℝ := ∑ i, if i ∈ ρ then 0 else y i
  have hm0 : 0 ≤ m := Finset.sum_nonneg fun i _ => by split_ifs <;> simp [hy'.1 i]
  have hmN : m ≤ N * ‖x - y‖ := sum_ite_mem_inter_le hx hy
  have hsplit : (∑ i, if i ∈ ρ then y i else 0) + m = 1 := by
    rw [← Finset.sum_add_distrib, ← hy'.2.2]
    exact Finset.sum_congr rfl fun i _ => by split_ifs <;> simp
  have hβsum : (∑ i, if i ∈ ρ then c else 0) = 1 := by
    rw [Finset.sum_ite_mem, Finset.univ_inter, Finset.sum_const, nsmul_eq_mul]
    exact mul_inv_cancel₀ hcard.ne'
  have hzero {w : ι → ℝ} (hw : ∀ i ∉ ρ, w i = 0) (h0 : ∀ i, 0 ≤ w i) (h1 : ∑ i, w i = 1) :
      w ∈ (range fun x : StandardSimplex σ => (x.1 : ι → ℝ)) ∩
        range fun x : StandardSimplex τ => (x.1 : ι → ℝ) :=
    mem_inter_of_forall_notMem_eq_zero hw h0 h1
  refine ⟨fun i => if i ∈ ρ then y i + m * c else 0, hzero (fun i hi => by simp [hi])
    (fun i => ?_) ?_, fun i => if i ∈ ρ then c else 0, hzero (fun i hi => by simp [hi])
    (fun i => ?_) hβsum, ?_, fun i hσ hτ => ?_⟩
  · split_ifs
    · exact add_nonneg (hy'.1 i) (mul_nonneg hm0 hc.le)
    · exact le_rfl
  · have h (i : ι) : (if i ∈ ρ then y i + m * c else 0) =
        (if i ∈ ρ then y i else 0) + m * (if i ∈ ρ then c else 0) := by
      split_ifs <;> simp
    simp_rw [h, Finset.sum_add_distrib, ← Finset.mul_sum, hβsum, mul_one, hsplit]
  · split_ifs
    · exact hc.le
    · exact le_rfl
  · refine (pi_norm_le_iff_of_nonneg (by positivity)).2 fun i => ?_
    simp only [Pi.sub_apply, Real.norm_eq_abs]
    split_ifs with hi
    · rw [sub_add_cancel_left, abs_neg, abs_of_nonneg (mul_nonneg hm0 hc.le)]
      nlinarith
    · rw [sub_zero, abs_of_nonneg (hy'.1 i)]
      nlinarith [coord_le_norm_sub hx hy fun h h' => hi (Finset.mem_inter.2 ⟨h, h'⟩)]
  · simp only [ρ, Finset.mem_inter, hσ, hτ, and_self, ite_true]
    exact inv_anti₀ hcard (Nat.cast_le.2 (Finset.card_le_univ ρ))

end AbstractSimplicialComplex
