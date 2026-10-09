/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.SimplicialComplex.Subdivision.Stellar.Geometry
public import TauCeti.Topology.PL.Inverse
import Mathlib.Analysis.Normed.Module.FiniteDimension

/-!
# Piecewise-linear transport across a stellar subdivision

The barycentric identification of a finite stellar subdivision is a piecewise-linear map on the
coordinate polyhedra. Its inverse is piecewise affine on the subdivided simplices, using the
finite-simplex inverse criterion. These are the local transition maps needed to transport PL
charts across stellar equivalences.

Reference: Rourke--Sanderson, *Introduction to Piecewise-Linear Topology*, Chapter 2.
-/

public section

noncomputable section

open Set

namespace PreAbstractSimplicialComplex

open Finset

variable {ι : Type*} [DecidableEq ι]
  {K : PreAbstractSimplicialComplex ι} {σ : Finset ι} {v : ι}

/-- The coordinate-space linear map induced by a stellar subdivision's barycentric map. -/
def stellarSubdivisionCoordinateMap (σ : Finset ι) (v : ι) :
    (ι → ℝ) →L[ℝ] (ι → ℝ) :=
  ContinuousLinearMap.id ℝ (ι → ℝ) +
    (ContinuousLinearMap.proj v).smulRight
      (fun i : ι => (if i ∈ σ then (σ.card : ℝ)⁻¹ else 0) - if i = v then 1 else 0)

private theorem stellarSubdivisionCoordinateMap_on_equiv [Finite ι] (x : ι →₀ ℝ) :
    stellarSubdivisionCoordinateMap σ v (Finsupp.equivFunOnFinite x) =
      Finsupp.equivFunOnFinite (Finset.stellarSubdivisionLinearMap σ v x) := by
  ext i
  simp [stellarSubdivisionCoordinateMap, Finset.stellarSubdivisionLinearMap_apply, eq_comm]

private theorem coord_single [Finite ι] (i : ι) :
    Finsupp.equivFunOnFinite (Finsupp.single i (1 : ℝ)) = Pi.single i 1 := by
  exact Finsupp.equivFunOnFinite_single i 1

private theorem coord_mem_source [Finite ι]
    {τ : (K.stellarSubdivision σ v).faces}
    {x : ι → ℝ} (hx : x ∈ convexHull ℝ ((Pi.single · (1 : ℝ)) '' (τ : Set ι))) :
    Finsupp.equivFunOnFinite.symm x ∈
      (Geometry.SimplicialComplex.onFinsupp (𝕜 := ℝ) (K.stellarSubdivision σ v)).space := by
  let e : (ι →₀ ℝ) ≃ₗ[ℝ] (ι → ℝ) :=
    Finsupp.linearEquivFunOnFinite ℝ ℝ ι
  have him := e.symm.toLinearMap.image_convexHull
      ((Pi.single · (1 : ℝ)) '' (τ : Set ι))
  have hxf' : e.symm x ∈ e.symm '' convexHull ℝ
      ((Pi.single · (1 : ℝ)) '' (τ : Set ι)) := ⟨x, hx, rfl⟩
  have hxf₀ := him ▸ hxf'
  have himage : e.symm '' ((Pi.single · (1 : ℝ)) '' (τ : Set ι)) =
      (Finsupp.single · (1 : ℝ)) '' (τ : Set ι) := by
    ext z
    constructor
    · rintro ⟨y, ⟨i, hi, rfl⟩, rfl⟩
      exact ⟨i, hi, by ext j; simp [e]⟩
    · rintro ⟨i, hi, rfl⟩
      exact ⟨Pi.single (i : ι) 1, ⟨i, hi, rfl⟩, by ext j; simp [e]⟩
  have hxf₁ : e.symm x ∈ convexHull ℝ
      ((Finsupp.single · (1 : ℝ)) '' (τ : Set ι)) := by
    convert hxf₀ using 1
    exact congrArg (convexHull ℝ) himage.symm
  rw [AbstractSimplicialComplex.mem_standardSimplex_iff] at hxf₁
  have hxf₀ := hxf₁
  have he : e.symm x = Finsupp.equivFunOnFinite.symm x := by
    ext i
    rfl
  rw [Geometry.SimplicialComplex.mem_space_onFinsupp_iff]
  refine ⟨?_, ?_, ?_⟩
  · simpa [he] using hxf₀.1
  · simpa [he] using hxf₀.2.1
  · have hface : (e.symm x).support ∈ K.stellarSubdivision σ v := by
      apply (K.stellarSubdivision σ v).isRelLowerSet_faces.mem_of_le τ.2 hxf₀.2.2
      apply Finsupp.support_nonempty_iff.mpr
      intro hzero
      have hsum := hxf₀.2.1
      simp [hzero] at hsum
    simpa [he] using hface

/-- The inverse barycentric map is piecewise linear on the original coordinate polyhedron.

The returned function is a left inverse of the stellar map on the subdivided coordinate
simplices; its values away from the image are immaterial. -/
theorem exists_isPLOn_stellarSubdivisionInverse (hfin : K.faces.Finite)
    (hσ : σ ∈ K) (hv : ({v} : Finset ι) ∉ K) [Finite ι] :
    ∃ g : (ι → ℝ) → (ι → ℝ),
      TauCeti.IsPLOn g
          (stellarSubdivisionCoordinateMap σ v ''
            (⋃ τ : (K.stellarSubdivision σ v).faces,
              convexHull ℝ ((Pi.single · (1 : ℝ)) '' (τ : Set ι)))) ∧
        ∀ x ∈ (⋃ τ : (K.stellarSubdivision σ v).faces,
            convexHull ℝ ((Pi.single · (1 : ℝ)) '' (τ : Set ι))),
          g (stellarSubdivisionCoordinateMap σ v x) = x := by
  classical
  let _ := Fintype.ofFinite ι
  let S := stellarSubdivisionCoordinateMap σ v
  let U : Set (ι → ℝ) := ⋃ τ : (K.stellarSubdivision σ v).faces,
    convexHull ℝ ((Pi.single · (1 : ℝ)) '' (τ : Set ι))
  have hfinS : (K.stellarSubdivision σ v).faces.Finite := finite_faces_stellarSubdivision hfin
  let _ := hfinS.fintype
  have hSinj : Set.InjOn S U := by
    intro x hx y hy hxy
    obtain ⟨τ, hxτ⟩ := mem_iUnion.mp hx
    obtain ⟨ρ, hyρ⟩ := mem_iUnion.mp hy
    have hxf := coord_mem_source (K := K) (σ := σ) (v := v) hxτ
    have hyf := coord_mem_source (K := K) (σ := σ) (v := v) hyρ
    have hxy_map : Finset.stellarSubdivisionLinearMap σ v
          (Finsupp.equivFunOnFinite.symm x) =
        Finset.stellarSubdivisionLinearMap σ v
          (Finsupp.equivFunOnFinite.symm y) := by
      calc
        Finset.stellarSubdivisionLinearMap σ v
            (Finsupp.equivFunOnFinite.symm x) =
            Finsupp.equivFunOnFinite.symm
              (stellarSubdivisionCoordinateMap σ v
                (Finsupp.equivFunOnFinite (Finsupp.equivFunOnFinite.symm x))) := by
          rw [stellarSubdivisionCoordinateMap_on_equiv]
          simp
        _ = Finsupp.equivFunOnFinite.symm
              (stellarSubdivisionCoordinateMap σ v
                (Finsupp.equivFunOnFinite (Finsupp.equivFunOnFinite.symm y))) := by
          simpa only [Equiv.apply_symm_apply] using
            congrArg Finsupp.equivFunOnFinite.symm hxy
        _ = Finset.stellarSubdivisionLinearMap σ v
            (Finsupp.equivFunOnFinite.symm y) := by
          rw [stellarSubdivisionCoordinateMap_on_equiv]
          simp
    have hxy_f := (injOn_stellarSubdivisionLinearMap (K := K) (σ := σ) (v := v)
      (notMem_of_singleton_notMem hv hσ)) hxf hyf hxy_map
    exact congrArg Finsupp.equivFunOnFinite hxy_f
  let g : (ι → ℝ) → (ι → ℝ) := fun y =>
    if hy : y ∈ S '' U then Classical.choose ((Set.mem_image S U _).mp hy) else 0
  have hgf : ∀ x ∈ U, g (S x) = x := by
    intro x hx
    have hy : S x ∈ S '' U := ⟨x, hx, rfl⟩
    dsimp [g]
    rw [dite_eq_left hy]
    apply hSinj (Classical.choose_spec ((Set.mem_image S U _).mp hy)).1 hx
    exact (Classical.choose_spec ((Set.mem_image S U _).mp hy)).2
  let s : (K.stellarSubdivision σ v).faces → Set (ι → ℝ) := fun τ =>
    (Pi.single · (1 : ℝ)) '' (τ : Set ι)
  let A : (K.stellarSubdivision σ v).faces →
      ((ι → ℝ) →ᴬ[ℝ] (ι → ℝ)) := fun _ => S.toContinuousAffineMap
  have heq : ∀ τ, EqOn S (A τ) (convexHull ℝ (s τ)) := by
    intro τ x hx
    rfl
  have hind : ∀ τ, AffineIndependent ℝ ((↑) : ((A τ) '' s τ) → (ι → ℝ)) := by
    intro τ
    let e : (ι →₀ ℝ) ≃ₗ[ℝ] (ι → ℝ) := Finsupp.linearEquivFunOnFinite ℝ ℝ ι
    have h := affineIndependent_stellarSubdivision (K := K) (σ := σ) (v := v)
      (notMem_of_singleton_notMem hv hσ) (τ := (τ : Finset ι)) τ.2
    have hm : AffineIndependent ℝ (fun i : (τ : Finset ι) => A τ (Pi.single (i : ι) 1)) := by
      have hm' := h.map' e.toAffineMap e.injective
      have heqfun : (fun i : (τ : Finset ι) => A τ (Pi.single (i : ι) 1)) =
          (fun i : (τ : Finset ι) => e (Finset.stellarSubdivisionLinearMap σ v
            (Finsupp.single (i : ι) 1))) := by
        funext i
        dsimp [A, S]
        rw [← coord_single, stellarSubdivisionCoordinateMap_on_equiv]
        rfl
      rw [heqfun]
      exact hm'
    have hset : (A τ) '' s τ = Set.range (fun i : (τ : Finset ι) => A τ (Pi.single (i : ι) 1)) := by
      ext y
      constructor
      · rintro ⟨z, ⟨i, hi, rfl⟩, rfl⟩
        exact ⟨⟨i, hi⟩, rfl⟩
      · rintro ⟨i, rfl⟩
        exact ⟨Pi.single (i : ι) 1, ⟨i, i.2, rfl⟩, rfl⟩
    rw [hset]
    exact hm.range
  have hgf' : ∀ x ∈ ⋃ τ, convexHull ℝ (s τ), g (S x) = x := by
    simpa [U, s] using hgf
  have hg := TauCeti.isPiecewiseAffineOn_inverse_of_finite_simplex_cover
    s A heq hind hgf'
  refine ⟨g, hg.isPLOn, hgf⟩

end PreAbstractSimplicialComplex
