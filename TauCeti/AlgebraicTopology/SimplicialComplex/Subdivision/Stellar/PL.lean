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

/-- A local classical equality decision procedure for finite-coordinate bookkeeping. -/
noncomputable local instance stellarSubdivisionDecidableEq (α : Type*) : DecidableEq α :=
  Classical.decEq α
attribute [local instance 1000] stellarSubdivisionDecidableEq

open Set

namespace Finset

variable {ι : Type*}

/-- The coordinate-space linear map induced by a stellar subdivision's barycentric map. -/
def stellarSubdivisionCoordinateMap (σ : Finset ι) (v : ι) :
    (ι → ℝ) →L[ℝ] (ι → ℝ) :=
  by
    classical
    exact ContinuousLinearMap.id ℝ (ι → ℝ) +
      (ContinuousLinearMap.proj v).smulRight
        (fun i : ι => (if i ∈ σ then (σ.card : ℝ)⁻¹ else 0) - if i = v then 1 else 0)

/-- Coordinate formula for the barycentric map of a stellar subdivision. -/
@[simp]
theorem stellarSubdivisionCoordinateMap_apply (x : ι → ℝ) (i : ι) :
    stellarSubdivisionCoordinateMap σ v x i =
      x i + x v * ((if i ∈ σ then (σ.card : ℝ)⁻¹ else 0) - if i = v then 1 else 0) := by
  classical
  simp [stellarSubdivisionCoordinateMap]

/-- The coordinate-space map agrees with the finitely supported stellar linear map. -/
@[simp]
theorem stellarSubdivisionCoordinateMap_on_equiv [Finite ι] (x : ι →₀ ℝ) :
    stellarSubdivisionCoordinateMap σ v (Finsupp.equivFunOnFinite x) =
      Finsupp.equivFunOnFinite (Finset.stellarSubdivisionLinearMap σ v x) := by
  classical
  ext i
  simp [stellarSubdivisionCoordinateMap, Finset.stellarSubdivisionLinearMap_apply, eq_comm]

end Finset

namespace PreAbstractSimplicialComplex

open Finset

variable {ι : Type*}
  {K : PreAbstractSimplicialComplex ι} {σ : Finset ι} {v : ι}

private theorem coord_mem_source [Finite ι]
    {τ : (K.stellarSubdivision σ v).faces}
    {x : ι → ℝ} (hx : x ∈ convexHull ℝ ((Pi.single · (1 : ℝ)) '' (τ : Set ι))) :
    Finsupp.equivFunOnFinite.symm x ∈
      (Geometry.SimplicialComplex.onFinsupp (𝕜 := ℝ) (K.stellarSubdivision σ v)).space := by
  classical
  have hxf₁ := Finsupp.mem_convexHull_single_equivFunOnFinite hx
  rw [AbstractSimplicialComplex.mem_standardSimplex_iff] at hxf₁
  have hxf₀ := hxf₁
  rw [Geometry.SimplicialComplex.mem_space_onFinsupp_iff]
  refine ⟨?_, ?_, ?_⟩
  · simpa using hxf₀.1
  · simpa using hxf₀.2.1
  · have hface : (Finsupp.equivFunOnFinite.symm x).support ∈ K.stellarSubdivision σ v := by
      apply (K.stellarSubdivision σ v).isRelLowerSet_faces.mem_of_le τ.2 hxf₀.2.2
      apply Finsupp.support_nonempty_iff.mpr
      intro hzero
      have hsum := hxf₀.2.1
      simp [hzero] at hsum
    simpa using hface

private theorem stellarSubdivision_face_relabel
    {ι κ : Type*} [DecidableEq ι] [DecidableEq κ]
    {K : PreAbstractSimplicialComplex ι} {σ : Finset ι} {v : ι}
    {Kκ : PreAbstractSimplicialComplex κ} {σ' : Finset κ} {v' : κ}
    (e : κ ↪ ι)
    (face' : (K.stellarSubdivision σ v).faces → Finset κ)
    (hKκ : ∀ q : Finset κ, q ∈ Kκ ↔ q.image e ∈ K)
    (hσ_spec : ∀ i : κ, i ∈ σ' ↔ e i ∈ σ)
    (hface_spec : ∀ (τ : (K.stellarSubdivision σ v).faces) (i : κ),
      i ∈ face' τ ↔ e i ∈ τ.1)
    (hσ_range : ∀ i ∈ σ, ∃ j : κ, e j = i)
    (hface_range : ∀ (τ : (K.stellarSubdivision σ v).faces) (i : ι),
      i ∈ τ.1 → ∃ j : κ, e j = i)
    (hev : e v' = v) :
    σ'.image e = σ ∧ ({v'} : Finset κ).image e = {v} ∧
      ∀ τ : (K.stellarSubdivision σ v).faces,
        face' τ ∈ Kκ.stellarSubdivision σ' v' ∧
          (face' τ).image e = τ.1 ∧
            ((face' τ).erase v').image e = τ.1.erase v := by
  have hσimage : σ'.image e = σ := by
    apply Finset.ext
    intro i
    constructor
    · intro hi
      rw [Finset.mem_image] at hi
      obtain ⟨j, hj, rfl⟩ := hi
      exact (hσ_spec j).mp hj
    · intro hi
      obtain ⟨j, hj⟩ := hσ_range i hi
      have hjσ : e j ∈ σ := by simpa [hj] using hi
      exact Finset.mem_image.mpr ⟨j, (hσ_spec j).mpr hjσ, hj⟩
  have hvimage : ({v'} : Finset κ).image e = {v} := by
    ext i
    simp [hev]
  refine ⟨hσimage, hvimage, ?_⟩
  intro τ
  have hτVimage : (face' τ).image e = τ.1 := by
    apply Finset.ext
    intro i
    constructor
    · intro hi
      rw [Finset.mem_image] at hi
      obtain ⟨j, hj, rfl⟩ := hi
      exact (hface_spec τ j).mp hj
    · intro hi
      obtain ⟨j, hj⟩ := hface_range τ i hi
      have hjτ : e j ∈ τ.1 := by simpa [hj] using hi
      exact Finset.mem_image.mpr ⟨j, (hface_spec τ j).mpr hjτ, hj⟩
  have herase : ((face' τ).erase v').image e = τ.1.erase v := by
    rw [Finset.image_erase e.injective, hτVimage]
    simp [hev]
  have hτL : τ.1 ∈ K.stellarSubdivision σ v := τ.2
  rw [mem_stellarSubdivision_iff] at hτL
  rw [mem_stellarSubdivision_iff]
  refine ⟨?_, hτVimage, herase⟩
  rcases hτL with ⟨hvτ, hτK, hτσ⟩ | ⟨hvτ, hτσ, hτK⟩
  · left
    refine ⟨?_, ?_, ?_⟩
    · intro hvτ'
      apply hvτ
      rw [← hτVimage]
      exact Finset.mem_image.mpr ⟨v', hvτ', hev⟩
    · apply (hKκ _).2
      rw [hτVimage]
      exact hτK
    · intro hsub
      apply hτσ
      rw [← hτVimage, ← hσimage]
      exact Finset.image_subset_image hsub
  · right
    refine ⟨?_, ?_, ?_⟩
    · exact (hface_spec τ v').2 (by simpa [hev] using hvτ)
    · intro hsub
      apply hτσ
      rw [← herase, ← hσimage]
      exact Finset.image_subset_image hsub
    · apply (hKκ _).2
      rw [Finset.image_union, herase, hσimage]
      exact hτK

/-- The inverse barycentric map is piecewise linear on finite active coordinates.

`V` is an explicit finite set of active vertices. It must contain the starred face, the new
vertex, and every face of the stellar subdivision. This keeps the PL target finite-dimensional
even when the original complex has an infinite ambient vertex type.
-/
theorem exists_isPLOn_stellarSubdivisionLeftInverse
    (V : Finset ι) (hVσ : σ ⊆ V)
    (hV : ∀ τ ∈ K.stellarSubdivision σ v, τ ⊆ V)
    (hVv : v ∈ V)
    (hvσ : v ∉ σ) :
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
  let _ : DecidableEq κ := stellarSubdivisionDecidableEq κ
  let e : κ ↪ ι := ⟨Subtype.val, Subtype.val_injective⟩
  let σ' : Finset κ := σ.preimage e e.injective.injOn
  let v' : κ := ⟨v, hVv⟩
  let L := K.stellarSubdivision σ v
  let face' (τ : L.faces) : Finset κ := τ.1.preimage e e.injective.injOn
  let Kκ : PreAbstractSimplicialComplex κ :=
    { faces := {q | q.image e ∈ K}
      isRelLowerSet_faces := by
        rintro q hq
        refine ⟨Finset.Nonempty.of_image ((K.isRelLowerSet_faces hq).1), ?_⟩
        intro r hr hrne
        apply (K.isRelLowerSet_faces hq).2
        · exact Finset.image_subset_image hr
        · exact Finset.image_nonempty.mpr hrne }
  let s (τ : L.faces) : Set (κ → ℝ) :=
    (Pi.single · (1 : ℝ)) '' (face' τ : Set κ)
  let U : Set (κ → ℝ) := ⋃ τ : L.faces, convexHull ℝ (s τ)
  let S := stellarSubdivisionCoordinateMap σ' v'
  have hfinL : L.faces.Finite := by
    apply Set.Finite.subset V.powerset.finite_toSet
    intro τ hτ
    exact Finset.mem_powerset.mpr (hV τ hτ)
  let _ := hfinL.fintype
  have hv'σ' : v' ∉ σ' := by
    intro h
    have : v ∈ σ := Finset.mem_preimage.mp h
    exact hvσ this
  -- Relabel finite-coordinate faces, then use injectivity and the finite-simplex criterion.
  have hfaceκ_data : σ'.image e = σ ∧ ({v'} : Finset κ).image e = {v} ∧
      ∀ τ : L.faces, face' τ ∈ Kκ.stellarSubdivision σ' v' ∧
        (face' τ).image e = τ.1 ∧ ((face' τ).erase v').image e = τ.1.erase v := by
    apply stellarSubdivision_face_relabel e face' (by intro q; rfl)
    · intro i
      simp [σ', e]
    · intro τ i
      simp [face', e]
    · intro i hi
      exact ⟨⟨i, hVσ hi⟩, rfl⟩
    · intro τ i hi
      exact ⟨⟨i, hV τ.1 τ.2 hi⟩, rfl⟩
    · rfl
  have hfaceκ (τ : L.faces) : face' τ ∈ Kκ.stellarSubdivision σ' v' :=
    (hfaceκ_data.2.2 τ).1
  have hSinj : Set.InjOn S U := by
    intro x hx y hy hxy
    obtain ⟨τ, hxτ⟩ := mem_iUnion.mp hx
    obtain ⟨ρ, hyρ⟩ := mem_iUnion.mp hy
    have hfaceκ_mem (τ : L.faces) : face' τ ∈ (Kκ.stellarSubdivision σ' v').faces := by
      exact hfaceκ τ
    have hxf := coord_mem_source (K := Kκ) (σ := σ') (v := v')
      (τ := ⟨face' τ, hfaceκ_mem τ⟩) hxτ
    have hyf := coord_mem_source (K := Kκ) (σ := σ') (v := v')
      (τ := ⟨face' ρ, hfaceκ_mem ρ⟩) hyρ
    have hxy_map : Finset.stellarSubdivisionLinearMap σ' v'
          (Finsupp.equivFunOnFinite.symm x) =
        Finset.stellarSubdivisionLinearMap σ' v'
          (Finsupp.equivFunOnFinite.symm y) := by
      calc
        Finset.stellarSubdivisionLinearMap σ' v'
            (Finsupp.equivFunOnFinite.symm x) =
            Finsupp.equivFunOnFinite.symm
              (S (Finsupp.equivFunOnFinite (Finsupp.equivFunOnFinite.symm x))) := by
          rw [Finset.stellarSubdivisionCoordinateMap_on_equiv]
          simp
        _ = Finsupp.equivFunOnFinite.symm
              (S (Finsupp.equivFunOnFinite (Finsupp.equivFunOnFinite.symm y))) := by
          simpa only [Equiv.apply_symm_apply] using
            congrArg Finsupp.equivFunOnFinite.symm hxy
        _ = Finset.stellarSubdivisionLinearMap σ' v'
            (Finsupp.equivFunOnFinite.symm y) := by
          rw [Finset.stellarSubdivisionCoordinateMap_on_equiv]
          simp
    have hxy_f := (injOn_stellarSubdivisionLinearMap (K := Kκ) (σ := σ') (v := v')
      hv'σ') hxf hyf hxy_map
    exact congrArg Finsupp.equivFunOnFinite hxy_f
  let g : (κ → ℝ) → (κ → ℝ) := fun y =>
    if hy : y ∈ S '' U then Classical.choose ((Set.mem_image S U _).mp hy) else 0
  have hgf : ∀ x ∈ U, g (S x) = x := by
    intro x hx
    have hy : S x ∈ S '' U := ⟨x, hx, rfl⟩
    dsimp [g]
    rw [dite_eq_left hy]
    apply hSinj (Classical.choose_spec ((Set.mem_image S U _).mp hy)).1 hx
    exact (Classical.choose_spec ((Set.mem_image S U _).mp hy)).2
  let F : L.faces → ((κ → ℝ) →ᴬ[ℝ] (κ → ℝ)) := fun _ => S.toContinuousAffineMap
  have hind (τ : L.faces) :
      AffineIndependent ℝ ((↑) : ((F τ) '' s τ) → (κ → ℝ)) := by
    let eF : (κ →₀ ℝ) ≃ₗ[ℝ] (κ → ℝ) := Finsupp.linearEquivFunOnFinite ℝ ℝ κ
    have h := affineIndependent_stellarSubdivision (K := Kκ) (σ := σ') (v := v')
      hv'σ' (hfaceκ τ)
    have hm : AffineIndependent ℝ (fun i : face' τ => F τ (Pi.single (i : κ) 1)) := by
      have hm' := h.map' eF.toAffineMap eF.injective
      have heqfun : (fun i : face' τ => F τ (Pi.single (i : κ) 1)) =
          (fun i : face' τ => eF (Finset.stellarSubdivisionLinearMap σ' v'
            (Finsupp.single (i : κ) 1))) := by
        funext i
        dsimp [F, S]
        rw [← Finsupp.equivFunOnFinite_single, stellarSubdivisionCoordinateMap_on_equiv]
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
    simpa only [U] using
      (TauCeti.isPiecewiseAffineOn_inverse_of_finite_simplex_cover
        (f := S) (g := g) s F (fun _ _ _ => rfl) hind hgf)
  have hσ'eq : σ.preimage (fun i : κ => (i : ι)) Subtype.val_injective.injOn = σ' := by
    ext i
    simp [σ', e]
  have hface'eq (τ : L.faces) :
      τ.1.preimage (fun i : κ => (i : ι)) Subtype.val_injective.injOn = face' τ := by
    ext i
    simp [face', e]
  let decEqκCanonical : DecidableEq κ :=
    @Subtype.instDecidableEq ι (fun i : ι => i ∈ V) (stellarSubdivisionDecidableEq ι)
  have hsingle (x : κ) :
      @Pi.single κ (fun _ : κ => ℝ) (fun _ => Real.instZero) decEqκCanonical x 1 =
        @Pi.single κ (fun _ : κ => ℝ) (fun _ => Real.instZero)
          (stellarSubdivisionDecidableEq κ) x 1 := by
    ext j
    by_cases h : x = j <;> simp [h]
  have hUCanonical :
      (⋃ τ : L.faces, convexHull ℝ
        ((@Pi.single κ (fun _ : κ => ℝ) (fun _ => Real.instZero) decEqκCanonical · 1) ''
          (τ.1.preimage (fun i : κ => (i : ι)) Subtype.val_injective.injOn : Set κ))) = U := by
    apply iUnion_congr
    intro τ
    rw [hface'eq τ]
    congr 1
    ext z
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact ⟨x, hx, (hsingle x).symm⟩
    · rintro ⟨x, hx, rfl⟩
      exact ⟨x, hx, hsingle x⟩
  have hSeq :
      stellarSubdivisionCoordinateMap
          (σ.preimage (fun i : κ => (i : ι)) Subtype.val_injective.injOn)
          ⟨v, hVv⟩ = S := by
    rw [hσ'eq]
  refine ⟨g, ?_, ?_⟩
  · convert hPA.isPLOn using 1
    rw [hSeq]
    exact congrArg (fun t : Set (κ → ℝ) => S '' t) hUCanonical
  · convert hgf using 1
    rw [hSeq, hUCanonical]

end PreAbstractSimplicialComplex
