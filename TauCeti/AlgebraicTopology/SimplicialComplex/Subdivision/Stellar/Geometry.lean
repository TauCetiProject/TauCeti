/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.SimplicialComplex.Subdivision.Stellar.Realization

/-!
# Geometric simplices of a stellar subdivision

Placing a new vertex at the barycenter of the starred face gives nondegenerate geometric
simplices, meeting along their common faces. On each subdivided simplex the barycentric
identification has a linear inverse: choose a vertex of the starred face omitted by that
simplex, and recover the transferred mass from its coordinate.

These simplex inverse formulas and affine independence checks allow the barycentric
identification to be treated as a simplicial PL map, rather than merely a bijection of
polyhedra. The complexes and ambient vertex types need not be finite.

## References

* C. P. Rourke, B. J. Sanderson, *Introduction to Piecewise-Linear Topology*, Chapter 2
  (geometric starrings).
-/

public section

noncomputable section

open Set

namespace Finset

variable {ι : Type*} [DecidableEq ι] {σ τ : Finset ι} {v a : ι}

/-- The linear inverse formula for a stellar simplex omitting the vertex `a` of the starred
face: transfer the `a`-coordinate back from that face to the new vertex `v`. -/
def stellarSubdivisionInverseLinearMap (σ : Finset ι) (v a : ι) :
    (ι →₀ ℝ) →ₗ[ℝ] (ι →₀ ℝ) :=
  LinearMap.id + (Finsupp.lapply a).smulRight
    ((σ.card : ℝ) • Finsupp.single v 1 - ∑ i ∈ σ, Finsupp.single i 1)

/-- The inverse on a stellar simplex subtracts equal mass on the starred face and adds its
sum at the new vertex. -/
@[simp]
theorem stellarSubdivisionInverseLinearMap_apply (σ : Finset ι) (v a : ι)
    (x : ι →₀ ℝ) (i : ι) :
    stellarSubdivisionInverseLinearMap σ v a x i =
      x i + x a * ((if i = v then (σ.card : ℝ) else 0) - if i ∈ σ then 1 else 0) := by
  simp [stellarSubdivisionInverseLinearMap, Finsupp.single_apply, eq_comm]

omit [DecidableEq ι] in
/-- If the coordinate at a vertex of the starred face vanishes, its linear inverse formula
recovers the original vector after the stellar barycentric map. -/
@[simp]
theorem stellarSubdivisionInverseLinearMap_left_inv (ha : a ∈ σ) (hv : v ∉ σ)
    {x : ι →₀ ℝ} (hxa : x a = 0) :
    stellarSubdivisionInverseLinearMap σ v a (stellarSubdivisionLinearMap σ v x) = x := by
  classical
  have hav : a ≠ v := fun h => hv (h ▸ ha)
  have hc : (σ.card : ℝ) ≠ 0 := by exact_mod_cast (card_pos.mpr ⟨a, ha⟩).ne'
  ext i
  simp only [stellarSubdivisionInverseLinearMap_apply, stellarSubdivisionLinearMap_apply,
    ha, hav, ite_true, ite_false, sub_zero, hxa, zero_add]
  by_cases hiv : i = v
  · subst i
    simp [hv, hc]
  · by_cases hi : i ∈ σ <;> simp [hiv, hi]

omit [DecidableEq ι] in
/-- The inverse formula works on the entire simplex whenever the simplex omits the chosen
vertex of the starred face. -/
theorem stellarSubdivisionInverseLinearMap_left_inv_on_simplex
    (ha : a ∈ σ) (hv : v ∉ σ) (haτ : a ∉ τ) :
    EqOn ((stellarSubdivisionInverseLinearMap σ v a) ∘ stellarSubdivisionLinearMap σ v)
      id (convexHull ℝ ((fun i : ι => Finsupp.single i (1 : ℝ)) '' (τ : Set ι))) := by
  classical
  intro x hx
  have hxτ := AbstractSimplicialComplex.mem_standardSimplex_iff.mp hx
  exact stellarSubdivisionInverseLinearMap_left_inv ha hv
    (Finsupp.notMem_support_iff.mp fun h => haτ (hxτ.2.2 h))

omit [DecidableEq ι] in
/-- The barycentric images of the vertices of a simplex omitting a vertex of the starred
face are affinely independent. -/
theorem affineIndependent_stellarSubdivisionLinearMap (ha : a ∈ σ) (hv : v ∉ σ)
    (haτ : a ∉ τ) :
    AffineIndependent ℝ (fun i : τ =>
      stellarSubdivisionLinearMap σ v (Finsupp.single (i : ι) 1)) := by
  classical
  apply AffineIndependent.of_comp (stellarSubdivisionInverseLinearMap σ v a).toAffineMap
  have hsingle : (fun i : τ => stellarSubdivisionInverseLinearMap σ v a
      (stellarSubdivisionLinearMap σ v (Finsupp.single (i : ι) 1))) =
      (fun i : τ => Finsupp.single (i : ι) (1 : ℝ)) := by
    funext i
    apply stellarSubdivisionInverseLinearMap_left_inv ha hv
    simp [ne_of_mem_of_not_mem i.2 haτ]
  simp only [Function.comp_def, LinearMap.coe_toAffineMap, hsingle]
  exact ((Finsupp.linearIndependent_single_one ℝ ι).comp Subtype.val
    Subtype.val_injective).affineIndependent

end Finset

namespace PreAbstractSimplicialComplex

open Finset

variable {ι : Type*} [DecidableEq ι] {K : PreAbstractSimplicialComplex ι}
  {σ τ ρ : Finset ι} {v : ι}

/-- Every simplex of the stellar subdivision admits a linear inverse to its barycentric
identification on the whole simplex. -/
theorem exists_linearMap_leftInverse_stellarSubdivision (hvσ : v ∉ σ)
    (hτ : τ ∈ stellarSubdivision K σ v) :
    ∃ L : (ι →₀ ℝ) →ₗ[ℝ] (ι →₀ ℝ),
      EqOn (L ∘ stellarSubdivisionLinearMap σ v) id
        (convexHull ℝ ((fun i : ι => Finsupp.single i (1 : ℝ)) '' (τ : Set ι))) := by
  obtain ⟨a, ha, haτ⟩ := exists_notMem_of_mem_stellarSubdivision hvσ hτ
  exact ⟨stellarSubdivisionInverseLinearMap σ v a,
    stellarSubdivisionInverseLinearMap_left_inv_on_simplex ha hvσ haτ⟩

/-- Placing the fresh vertex at the barycenter gives affinely independent vertices on every
face of the stellar subdivision. -/
theorem affineIndependent_stellarSubdivision (hvσ : v ∉ σ)
    (hτ : τ ∈ stellarSubdivision K σ v) :
    AffineIndependent ℝ (fun i : τ =>
      stellarSubdivisionLinearMap σ v (Finsupp.single (i : ι) 1)) := by
  obtain ⟨a, ha, haτ⟩ := exists_notMem_of_mem_stellarSubdivision hvσ hτ
  exact Finset.affineIndependent_stellarSubdivisionLinearMap ha hvσ haτ

/-- Two geometric stellar simplices meet exactly in the simplex spanned by their common
vertices. Thus the barycentric placement is a geometric triangulation, not merely a
collection of nondegenerate simplices with the correct union. -/
theorem convexHull_stellarSubdivision_inter (hvσ : v ∉ σ)
    (hτ : τ ∈ stellarSubdivision K σ v) (hρ : ρ ∈ stellarSubdivision K σ v) :
    convexHull ℝ ((fun i : ι => stellarSubdivisionLinearMap σ v (Finsupp.single i 1)) ''
        (τ : Set ι)) ∩
      convexHull ℝ ((fun i : ι => stellarSubdivisionLinearMap σ v (Finsupp.single i 1)) ''
        (ρ : Set ι)) =
    convexHull ℝ ((fun i : ι => stellarSubdivisionLinearMap σ v (Finsupp.single i 1)) ''
      ((τ : Set ι) ∩ (ρ : Set ι))) := by
  let S := stellarSubdivisionLinearMap σ v
  let B : ι → (ι →₀ ℝ) := fun i => Finsupp.single i 1
  let C := Geometry.SimplicialComplex.onFinsupp (𝕜 := ℝ) (stellarSubdivision K σ v)
  have hτf : τ.image B ∈ C.faces := ⟨τ, hτ, rfl⟩
  have hρf : ρ.image B ∈ C.faces := ⟨ρ, hρ, rfl⟩
  have hτsub : convexHull ℝ (B '' (τ : Set ι)) ⊆ C.space := by
    simpa only [Finset.coe_image] using C.convexHull_subset_space hτf
  have hρsub : convexHull ℝ (B '' (ρ : Set ι)) ⊆ C.space := by
    simpa only [Finset.coe_image] using C.convexHull_subset_space hρf
  have himage (t : Set ι) : S '' convexHull ℝ (B '' t) =
      convexHull ℝ ((fun i => S (B i)) '' t) := by
    simpa only [Set.image_image, Function.comp_def] using
      S.image_convexHull (B '' t)
  have hB : Function.Injective B := (Finsupp.linearIndependent_single_one ℝ ι).injective
  have hinter : convexHull ℝ (B '' (τ : Set ι)) ∩ convexHull ℝ (B '' (ρ : Set ι)) =
      convexHull ℝ (B '' ((τ : Set ι) ∩ (ρ : Set ι))) := by
    have h := C.convexHull_inter_convexHull hτf hρf
    simpa only [Finset.coe_image,
      ← Set.image_inter hB] using h
  rw [← himage, ← himage,
    ← (injOn_stellarSubdivisionLinearMap hvσ).image_inter hτsub hρsub, hinter, himage]

/-- The geometric stellar subdivision, placing `v` at the barycenter of `σ` and retaining the
standard positions of the other vertices. Its face collection is the image of the abstract
stellar subdivision under that placement. -/
def geometricStellarSubdivision (K : PreAbstractSimplicialComplex ι)
    (σ : Finset ι) (v : ι) (hvσ : v ∉ σ) : Geometry.SimplicialComplex ℝ (ι →₀ ℝ) where
  toPreAbstractSimplicialComplex := (stellarSubdivision K σ v).map
    (fun i => stellarSubdivisionLinearMap σ v (Finsupp.single i 1))
  indep := by
    rintro s ⟨τ, hτ, rfl⟩
    have heq : (↑(τ.image (fun i => stellarSubdivisionLinearMap σ v
        (Finsupp.single i 1))) : Set (ι →₀ ℝ)) =
        Set.range (fun i : τ => stellarSubdivisionLinearMap σ v (Finsupp.single (i : ι) 1)) := by
      ext x
      simp only [Finset.mem_coe, Finset.mem_image, Set.mem_range, Subtype.exists, exists_prop]
    have hr := (affineIndependent_stellarSubdivision hvσ hτ).range
    rw [← heq] at hr
    exact hr
  inter_subset_convexHull := by
    rintro s t ⟨τ, hτ, rfl⟩ ⟨ρ, hρ, rfl⟩
    simp only [Finset.coe_image]
    rw [convexHull_stellarSubdivision_inter hvσ hτ hρ]
    exact convexHull_mono (Set.image_inter_subset _ _ _)

/-- The geometric stellar faces are exactly the barycentric images of the abstract stellar
faces. -/
@[simp]
theorem mem_geometricStellarSubdivision_iff (hvσ : v ∉ σ) {s : Finset (ι →₀ ℝ)} :
    s ∈ (geometricStellarSubdivision K σ v hvσ).faces ↔
      ∃ τ ∈ stellarSubdivision K σ v,
        τ.image (fun i => stellarSubdivisionLinearMap σ v (Finsupp.single i 1)) = s :=
  Iff.rfl

/-- A genuine geometric starring leaves the underlying polyhedron unchanged. -/
@[simp]
theorem space_geometricStellarSubdivision (hσ : σ ∈ K) (hv : ({v} : Finset ι) ∉ K) :
    (geometricStellarSubdivision K σ v (notMem_of_singleton_notMem hv hσ)).space =
      (Geometry.SimplicialComplex.onFinsupp (𝕜 := ℝ) K).space := by
  let S := stellarSubdivisionLinearMap σ v
  let B : ι → (ι →₀ ℝ) := fun i => Finsupp.single i 1
  have hmap (t : Finset ι) : S '' convexHull ℝ (B '' (t : Set ι)) =
      convexHull ℝ ((fun i => S (B i)) '' (t : Set ι)) := by
    simpa only [Set.image_image, Function.comp_def] using
      S.image_convexHull (B '' (t : Set ι))
  have himage : (geometricStellarSubdivision K σ v
      (notMem_of_singleton_notMem hv hσ)).space =
      S '' (Geometry.SimplicialComplex.onFinsupp (𝕜 := ℝ)
        (stellarSubdivision K σ v)).space := by
    ext x
    simp only [Geometry.SimplicialComplex.mem_space_iff,
      mem_geometricStellarSubdivision_iff, Set.mem_image]
    constructor
    · rintro ⟨s, ⟨τ, hτ, rfl⟩, hx⟩
      have hx' : x ∈ S '' convexHull ℝ (B '' (τ : Set ι)) := by
        rw [hmap]
        simpa only [Finset.coe_image] using hx
      obtain ⟨y, hy, rfl⟩ := hx'
      exact ⟨y, ⟨τ.image B, ⟨τ, hτ, rfl⟩, by simpa only [Finset.coe_image] using hy⟩, rfl⟩
    · rintro ⟨y, ⟨s, ⟨τ, hτ, rfl⟩, hy⟩, rfl⟩
      refine ⟨τ.image (fun i => S (B i)), ⟨τ, hτ, rfl⟩, ?_⟩
      have hy' : S y ∈ S '' convexHull ℝ (B '' (τ : Set ι)) :=
        ⟨y, by simpa only [Finset.coe_image] using hy, rfl⟩
      rw [Finset.coe_image, ← hmap]
      exact hy'
  rw [himage]
  exact (bijOn_stellarSubdivisionLinearMap hσ hv).image_eq

end PreAbstractSimplicialComplex
