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
  classical
  ext i
  simp [stellarSubdivisionCoordinateMap, Finset.stellarSubdivisionLinearMap_apply, eq_comm]

private theorem coord_single [Finite ι] (i : ι) :
    Finsupp.equivFunOnFinite (Finsupp.single i (1 : ℝ)) = Pi.single i 1 := by
  exact Finsupp.equivFunOnFinite_single i 1

private theorem coord_nonneg_of_mem_convexHull
    {τ : Finset ι} {x : ι → ℝ}
    (hx : x ∈ convexHull ℝ ((Pi.single · (1 : ℝ)) '' (τ : Set ι))) (i : ι) :
    0 ≤ x i := by
  classical
  apply (convexHull_min ?_ ((convex_Ici (0 : ℝ)).is_linear_preimage
    (ContinuousLinearMap.proj i : (ι → ℝ) →L[ℝ] ℝ).isLinear)) hx
  rintro z ⟨j, hj, rfl⟩
  simp only [ContinuousLinearMap.coe_proj, LinearMap.coe_proj, Set.mem_preimage,
    Function.eval, Set.mem_Ici]
  by_cases hji : i = j
  · subst i
    simp
  · simp [hji]

private theorem coord_eq_zero_of_mem_convexHull
    {τ : Finset ι} {x : ι → ℝ}
    (hx : x ∈ convexHull ℝ ((Pi.single · (1 : ℝ)) '' (τ : Set ι)))
    {i : ι} (hi : i ∉ τ) : x i = 0 := by
  classical
  have hle : x i ≤ 0 := by
    have hsubset : (Pi.single · (1 : ℝ)) '' (τ : Set ι) ⊆
        (ContinuousLinearMap.proj (R := ℝ) i : (ι → ℝ) → ℝ) ⁻¹' Set.Iic (0 : ℝ) := by
      rintro z ⟨j, hj, rfl⟩
      have hij : i ≠ j := fun h => hi (h ▸ hj)
      change ((Pi.single j (1 : ℝ) : ι → ℝ) i) ≤ 0
      simp [hij]
    have h := convexHull_min hsubset ((convex_Iic (0 : ℝ)).is_linear_preimage
      (ContinuousLinearMap.proj i : (ι → ℝ) →L[ℝ] ℝ).isLinear) hx
    simpa using h
  exact le_antisymm hle (coord_nonneg_of_mem_convexHull hx i)

/-- The affine inverse formula for a stellar simplex in function coordinates. -/
def stellarSubdivisionCoordinateInverseMap (σ : Finset ι) (v a : ι) :
    (ι → ℝ) →L[ℝ] (ι → ℝ) :=
  ContinuousLinearMap.id ℝ (ι → ℝ) +
    (ContinuousLinearMap.proj a).smulRight
      (fun i : ι => (if i = v then (σ.card : ℝ) else 0) - if i ∈ σ then 1 else 0)

private theorem stellarSubdivisionCoordinateInverseMap_left_inv
    (ha : a ∈ σ) (hv : v ∉ σ)
    {τ : Finset ι} {x : ι → ℝ} (hx : x ∈ convexHull ℝ
      ((Pi.single · (1 : ℝ)) '' (τ : Set ι))) (haτ : a ∉ τ) :
    stellarSubdivisionCoordinateInverseMap σ v a
        (stellarSubdivisionCoordinateMap σ v x) = x := by
  classical
  have hxa : x a = 0 := coord_eq_zero_of_mem_convexHull hx haτ
  have hav : a ≠ v := fun h => hv (h ▸ ha)
  have hc : (σ.card : ℝ) ≠ 0 := by exact_mod_cast (card_pos.mpr ⟨a, ha⟩).ne'
  ext i
  have hS (z : ι → ℝ) (i : ι) :
      stellarSubdivisionCoordinateMap σ v z i =
        z i + z v * ((if i ∈ σ then (σ.card : ℝ)⁻¹ else 0) -
          if i = v then 1 else 0) := by
    simp [stellarSubdivisionCoordinateMap]
  have hI (z : ι → ℝ) (i : ι) :
      stellarSubdivisionCoordinateInverseMap σ v a z i =
        z i + z a * ((if i = v then (σ.card : ℝ) else 0) -
          if i ∈ σ then 1 else 0) := by
    simp [stellarSubdivisionCoordinateInverseMap]
  rw [hI (stellarSubdivisionCoordinateMap σ v x) i, hS x i, hS x a]
  by_cases hiv : i = v
  · subst i
    simp [hv, ha, hxa, hc, hav]
  · by_cases hi : i ∈ σ
    · simp [hiv, hi, ha, hxa, hav]
    · simp [hiv, hi, ha, hxa, hav]

/-- The inverse barycentric map is piecewise linear on finite active coordinates.

`V` is an explicit finite set of active vertices. It must contain the starred face, the new
vertex, and every face of the stellar subdivision. This keeps the PL target finite-dimensional
even when the original complex has an infinite ambient vertex type.
-/
theorem exists_isPLOn_stellarSubdivisionInverse
    (V : Finset ι) (hVσ : σ ⊆ V) (hVv : v ∈ V)
    (hV : ∀ τ ∈ K.stellarSubdivision σ v, τ ⊆ V)
    (hfin : K.faces.Finite) (hσ : σ ∈ K)
    (hv : ({v} : Finset ι) ∉ K) :
    let κ := {i : ι // i ∈ V}
    ∃ g : (κ → ℝ) → (κ → ℝ),
      TauCeti.IsPLOn g
          (stellarSubdivisionCoordinateMap
              (σ.preimage (fun i : κ => (i : ι)) Subtype.val_injective.injOn)
              ⟨v, hVv⟩ ''
            (⋃ τ : (K.stellarSubdivision σ v).faces,
              convexHull ℝ ((Pi.single · (1 : ℝ)) ''
                (τ.1.preimage (fun i : κ => (i : ι)) Subtype.val_injective.injOn : Set κ)))) ∧
        ∀ x ∈ (⋃ τ : (K.stellarSubdivision σ v).faces,
            convexHull ℝ ((Pi.single · (1 : ℝ)) ''
              (τ.1.preimage (fun i : κ => (i : ι)) Subtype.val_injective.injOn : Set κ))),
          g (stellarSubdivisionCoordinateMap
              (σ.preimage (fun i : κ => (i : ι)) Subtype.val_injective.injOn)
              ⟨v, hVv⟩ x) = x := by
  classical
  dsimp
  let κ := {i : ι // i ∈ V}
  let _ : Fintype κ := Fintype.ofFinset V (fun _ => Iff.rfl)
  let e : κ ↪ ι := ⟨Subtype.val, Subtype.val_injective⟩
  let σ' : Finset κ := σ.preimage e e.injective.injOn
  let v' : κ := ⟨v, hVv⟩
  let L := K.stellarSubdivision σ v
  let face' (τ : L.faces) : Finset κ := τ.1.preimage e e.injective.injOn
  let s (τ : L.faces) : Set (κ → ℝ) :=
    (Pi.single · (1 : ℝ)) '' (face' τ : Set κ)
  let U : Set (κ → ℝ) := ⋃ τ : L.faces, convexHull ℝ (s τ)
  let S := stellarSubdivisionCoordinateMap σ' v'
  have hfinL : L.faces.Finite := finite_faces_stellarSubdivision hfin
  let _ := hfinL.fintype
  have hσne : σ.Nonempty := (K.isRelLowerSet_faces hσ).1
  have hσ'ne : σ'.Nonempty := by
    obtain ⟨a, ha⟩ := hσne
    exact ⟨⟨a, hVσ ha⟩, Finset.mem_preimage.mpr ha⟩
  have hv'σ' : v' ∉ σ' := by
    intro h
    have : v ∈ σ := Finset.mem_preimage.mp h
    exact (notMem_of_singleton_notMem hv hσ) this
  have omitted (τ : L.faces) : ∃ a : κ, a ∈ σ' ∧ a ∉ face' τ := by
    have hτV : τ.1 ⊆ V := hV τ.1 τ.2
    obtain ⟨a, ha, haτ⟩ := exists_notMem_of_mem_stellarSubdivision
      (notMem_of_singleton_notMem hv hσ) τ.2
    refine ⟨⟨a, hVσ ha⟩, Finset.mem_preimage.mpr ha, ?_⟩
    intro ha'
    apply haτ
    have haV : a ∈ V := by
      by_cases hmem : a ∈ τ.1
      · exact hτV hmem
      · exact hVσ ha
    have : (⟨a, haV⟩ : κ) ∈ face' τ := ha'
    exact Finset.mem_preimage.mp this
  have hS (z : κ → ℝ) (i : κ) :
      S z i = z i + z v' * ((if i ∈ σ' then (σ'.card : ℝ)⁻¹ else 0) -
        if i = v' then 1 else 0) := by
    simp [S, stellarSubdivisionCoordinateMap]
  have hSinj : Set.InjOn S U := by
    intro x hx y hy hxy
    obtain ⟨τ, hxτ⟩ := mem_iUnion.mp hx
    obtain ⟨ρ, hyρ⟩ := mem_iUnion.mp hy
    obtain ⟨a, ha, haτ⟩ := omitted τ
    obtain ⟨b, hb, hbρ⟩ := omitted ρ
    have hxa : x a = 0 := coord_eq_zero_of_mem_convexHull hxτ haτ
    have hyb : y b = 0 := coord_eq_zero_of_mem_convexHull hyρ hbρ
    have hya := coord_nonneg_of_mem_convexHull hyρ a
    have hxb := coord_nonneg_of_mem_convexHull hxτ b
    have hav : a ≠ v' := fun h => hv'σ' (h ▸ ha)
    have hbv : b ≠ v' := fun h => hv'σ' (h ▸ hb)
    have hcpos : 0 < (σ'.card : ℝ)⁻¹ := by
      exact inv_pos.mpr (by exact_mod_cast hσ'ne.card_pos)
    have hea := congrArg (fun z => z a) hxy
    have heb := congrArg (fun z => z b) hxy
    rw [hS x a, hS y a] at hea
    rw [hS x b, hS y b] at heb
    simp only [ha, hb, hxa, hyb, hav, hbv, ite_true, ite_false, sub_zero, zero_add]
      at hea heb
    have hvxy : x v' = y v' := by nlinarith
    ext i
    have hei := congrArg (fun z => z i) hxy
    rw [hS x i, hS y i, hvxy] at hei
    exact add_right_cancel hei
  let g : (κ → ℝ) → (κ → ℝ) := fun y =>
    if hy : y ∈ S '' U then Classical.choose ((Set.mem_image S U _).mp hy) else 0
  have hgf : ∀ x ∈ U, g (S x) = x := by
    intro x hx
    have hy : S x ∈ S '' U := ⟨x, hx, rfl⟩
    dsimp [g]
    rw [dite_eq_left hy]
    apply hSinj (Classical.choose_spec ((Set.mem_image S U _).mp hy)).1 hx
    exact (Classical.choose_spec ((Set.mem_image S U _).mp hy)).2
  let a (τ : L.faces) : κ := Classical.choose (omitted τ)
  have ha (τ : L.faces) : a τ ∈ σ' := (Classical.choose_spec (omitted τ)).1
  have haτ (τ : L.faces) : a τ ∉ face' τ := (Classical.choose_spec (omitted τ)).2
  let F : L.faces → ((κ → ℝ) →ᴬ[ℝ] (κ → ℝ)) := fun _ => S.toContinuousAffineMap
  let B : L.faces → ((κ → ℝ) →ᴬ[ℝ] (κ → ℝ)) := fun τ =>
    (stellarSubdivisionCoordinateInverseMap σ' v' (a τ)).toContinuousAffineMap
  have hleft (τ : L.faces) {x : κ → ℝ} (hx : x ∈ convexHull ℝ (s τ)) :
      B τ (S x) = x := by
    exact stellarSubdivisionCoordinateInverseMap_left_inv (ha τ) hv'σ' hx (haτ τ)
  have himage (τ : L.faces) : S '' convexHull ℝ (s τ) =
      convexHull ℝ (F τ '' s τ) := by
    simpa only [F, ContinuousLinearMap.coe_toContinuousAffineMap,
      ContinuousAffineMap.coe_toAffineMap] using
      (S.toContinuousAffineMap.image_convexHull (s τ))
  have hind (τ : L.faces) :
      AffineIndependent ℝ ((↑) : ((F τ) '' s τ) → (κ → ℝ)) := by
    let eF : (κ →₀ ℝ) ≃ₗ[ℝ] (κ → ℝ) := Finsupp.linearEquivFunOnFinite ℝ ℝ κ
    have h := Finset.affineIndependent_stellarSubdivisionLinearMap
      (ha τ) hv'σ' (haτ τ)
    have hm : AffineIndependent ℝ (fun i : face' τ => F τ (Pi.single (i : κ) 1)) := by
      have hm' := h.map' eF.toAffineMap eF.injective
      have heqfun : (fun i : face' τ => F τ (Pi.single (i : κ) 1)) =
          (fun i : face' τ => eF (Finset.stellarSubdivisionLinearMap σ' v'
            (Finsupp.single (i : κ) 1))) := by
        funext i
        dsimp [F, S]
        rw [← coord_single, stellarSubdivisionCoordinateMap_on_equiv]
        rfl
      rw [heqfun]
      exact hm'
    have hset : (F τ) '' s τ =
        Set.range (fun i : face' τ => F τ (Pi.single (i : κ) 1)) := by
      ext y
      constructor
      · rintro ⟨z, ⟨i, hi, rfl⟩, rfl⟩
        exact ⟨⟨i, hi⟩, rfl⟩
      · rintro ⟨i, rfl⟩
        exact ⟨Pi.single (i : κ) 1, ⟨i, i.2, rfl⟩, rfl⟩
    rw [hset]
    exact hm.range
  have hPA : TauCeti.IsPiecewiseAffineOn g (S '' U) := by
    refine TauCeti.isPiecewiseAffineOn_of_finite
      (C := fun τ : L.faces => convexHull ℝ (F τ '' s τ))
      (A := B) (fun τ => (hind τ).isConvexPolyhedron_convexHull) ?_ ?_
    · rintro y ⟨x, hx, rfl⟩
      obtain ⟨τ, hxτ⟩ := mem_iUnion.mp hx
      exact mem_iUnion.mpr ⟨τ, (himage τ).symm ▸ ⟨x, hxτ, rfl⟩⟩
    · intro τ y hy
      have hyC := hy.2
      rw [← himage τ] at hyC
      obtain ⟨x, hx, rfl⟩ := hyC
      exact (hgf x (mem_iUnion.mpr ⟨τ, hx⟩)).trans (hleft τ hx).symm
  refine ⟨g, hPA.isPLOn, ?_⟩
  simpa [S, U, s, face', L, e, σ', v'] using hgf

end PreAbstractSimplicialComplex
