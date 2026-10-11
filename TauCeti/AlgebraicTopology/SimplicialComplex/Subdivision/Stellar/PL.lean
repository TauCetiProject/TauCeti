/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.SimplicialComplex.Subdivision.Stellar.Geometry
public import TauCeti.AlgebraicTopology.SimplicialComplex.Subdivision.Stellar.Homeomorph
public import TauCeti.Topology.PL.FiniteInf
public import TauCeti.Topology.PL.Inverse
import Mathlib.Analysis.Normed.Module.FiniteDimension

/-!
# Piecewise-linear transport across a stellar subdivision

The barycentric identification of a finite stellar subdivision is a piecewise-linear map on the
coordinate polyhedra. Its inverse is piecewise affine on the subdivided simplices, using the
finite-simplex inverse criterion. These are the local transition maps needed to transport PL
charts across stellar equivalences.

The inverse also has an explicit extension to arbitrary coordinate spaces: it removes the least
coordinate on the starred face from each of its vertices and transfers the total removed mass
to the new vertex. This extension is piecewise affine on minimum-coordinate cells and agrees
with the inverse of the stellar homeomorphism of finite weak polyhedra.

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

/-- The coordinate extension agrees with the finitely supported stellar map. -/
@[simp]
theorem stellarSubdivisionCoordinateMap_coe (σ : Finset ι) (v : ι) (x : ι →₀ ℝ) :
    stellarSubdivisionCoordinateMap σ v x =
      (stellarSubdivisionLinearMap σ v x : ι → ℝ) := by
  classical
  ext i
  simp

/-- The coordinate-space map agrees with the finitely supported stellar linear map. -/
@[simp]
theorem stellarSubdivisionCoordinateMap_on_equiv [Finite ι] (x : ι →₀ ℝ) :
    stellarSubdivisionCoordinateMap σ v (Finsupp.equivFunOnFinite x) =
      Finsupp.equivFunOnFinite (Finset.stellarSubdivisionLinearMap σ v x) := by
  classical
  ext i
  simp [stellarSubdivisionCoordinateMap, Finset.stellarSubdivisionLinearMap_apply, eq_comm]

section

variable [DecidableEq ι]

open TauCeti

/-- Extend the inverse stellar identification to coordinate space by transferring the least
coordinate on `σ` to `v`. On an original polyhedron with unused vertex `v`, this is the inverse
of the barycentric stellar map. -/
def stellarSubdivisionInverseExtension (σ : Finset ι) (hσ : σ.Nonempty) (v : ι)
    (x : ι → ℝ) : ι → ℝ :=
  x + σ.inf' hσ x •
    (((σ.card : ℝ) • Finsupp.single v 1 - ∑ i ∈ σ, Finsupp.single i 1 : ι →₀ ℝ) : ι → ℝ)

/-- The inverse stellar extension's coordinate formula. -/
@[simp]
theorem stellarSubdivisionInverseExtension_apply (σ : Finset ι) (hσ : σ.Nonempty) (v : ι)
    (x : ι → ℝ) (i : ι) :
    stellarSubdivisionInverseExtension σ hσ v x i =
      x i + σ.inf' hσ x *
        ((if i = v then (σ.card : ℝ) else 0) - if i ∈ σ then 1 else 0) := by
  simp [stellarSubdivisionInverseExtension, Finsupp.single_apply, eq_comm]

omit [DecidableEq ι] in
/-- The inverse stellar extension is piecewise affine on the entire coordinate space.
Its cells are the regions on which one of the starred-face coordinates is least. -/
theorem isPiecewiseAffineOn_stellarSubdivisionInverseExtension (σ : Finset ι) (hσ : σ.Nonempty)
    (v : ι) : IsPiecewiseAffineOn (stellarSubdivisionInverseExtension σ hσ v) Set.univ := by
  let f (i : ι) : (ι → ℝ) →ᴬ[ℝ] ℝ :=
    (ContinuousLinearMap.proj i).toContinuousAffineMap
  let d : ι → ℝ :=
    ((σ.card : ℝ) • Finsupp.single v 1 - ∑ i ∈ σ, Finsupp.single i 1 : ι →₀ ℝ)
  let A (i : σ) : (ι → ℝ) →ᴬ[ℝ] (ι → ℝ) :=
    (ContinuousLinearMap.id ℝ (ι → ℝ) +
      (ContinuousLinearMap.proj (i : ι)).smulRight d).toContinuousAffineMap
  refine isPiecewiseAffineOn_of_finite (C := σ.infCell f) (A := A)
    (σ.isConvexPolyhedron_infCell f) (σ.subset_iUnion_infCell hσ f) ?_
  intro i x hx
  have hmin : σ.inf' hσ x = x i :=
    σ.infAffine_eq_of_mem_infCell hσ f i hx.2
  simp [stellarSubdivisionInverseExtension, A, d, hmin]

omit [DecidableEq ι] in
/-- The barycentric coordinate extension cancels the inverse extension on coordinates
vanishing at the new vertex. No positivity, support, or normalization is needed. -/
@[simp]
theorem stellarSubdivisionCoordinateMap_stellarSubdivisionInverseExtension
    {σ : Finset ι} (hσ : σ.Nonempty) {v : ι} (hvσ : v ∉ σ)
    {x : ι → ℝ} (hxv : x v = 0) :
    stellarSubdivisionCoordinateMap σ v (stellarSubdivisionInverseExtension σ hσ v x) =
      x := by
  classical
  have hc : (σ.card : ℝ) ≠ 0 := by exact_mod_cast hσ.card_pos.ne'
  ext i
  simp only [stellarSubdivisionCoordinateMap_apply, stellarSubdivisionInverseExtension_apply]
  by_cases hiv : i = v
  · subst i
    simp [hvσ, hxv]
  · by_cases his : i ∈ σ <;> simp [hiv, his, hvσ, hxv, hc]

/-- On nonnegative coordinates supported on a stellar face, the inverse extension cancels
the barycentric map. No normalization or finiteness of the complex or vertex type is needed. -/
theorem stellarSubdivisionInverseExtension_stellarSubdivisionLinearMap
    {K : PreAbstractSimplicialComplex ι} {σ : Finset ι} (hσ : σ.Nonempty)
    {v : ι} (hvσ : v ∉ σ) {x : ι →₀ ℝ}
    (hxpos : ∀ i, 0 ≤ x i)
    (hxface : x.support ∈ PreAbstractSimplicialComplex.stellarSubdivision K σ v) :
    stellarSubdivisionInverseExtension σ hσ v (stellarSubdivisionLinearMap σ v x) =
      (x : ι → ℝ) := by
  have hnot : ¬ σ ⊆ x.support := fun h =>
    PreAbstractSimplicialComplex.self_notMem_stellarSubdivision hvσ
      ((PreAbstractSimplicialComplex.stellarSubdivision K σ v).isRelLowerSet_faces.mem_of_le
        hxface h hσ)
  obtain ⟨a, ha, hxa⟩ := Finset.not_subset.mp hnot
  have hc : (σ.card : ℝ) ≠ 0 := by exact_mod_cast hσ.card_pos.ne'
  have hcoord (i : ι) (hi : i ∈ σ) :
      stellarSubdivisionLinearMap σ v x i = x i + x v * (σ.card : ℝ)⁻¹ := by
    have hiv : i ≠ v := fun h => hvσ (h ▸ hi)
    simp [stellarSubdivisionLinearMap_apply, hi, hiv]
  have hmin : σ.inf' hσ (stellarSubdivisionLinearMap σ v x) =
      x v * (σ.card : ℝ)⁻¹ := by
    apply le_antisymm
    · exact (σ.inf'_le _ ha).trans_eq (by
        simp [hcoord a ha, Finsupp.notMem_support_iff.mp hxa])
    · apply σ.le_inf' hσ
      intro i hi
      rw [hcoord i hi]
      linarith [hxpos i]
  ext i
  rw [stellarSubdivisionInverseExtension_apply, hmin, stellarSubdivisionLinearMap_apply]
  by_cases hiv : i = v
  · subst i
    simp [hvσ, hc]
  · by_cases his : i ∈ σ <;> simp [hiv, his]

end

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

section

open AbstractSimplicialComplex

variable [DecidableEq ι] {A : AbstractSimplicialComplex ι}

/-- The finite stellar homeomorphism has the barycentric continuous linear coordinate map
as its forward extension and the piecewise-affine minimum-transfer map as its inverse extension.
Thus stellar moves identify finite weak polyhedra by PL maps in both directions. -/
theorem exists_homeomorph_stellarSubdivision_with_inverse
    (hσ : σ ∈ K) (hv : ({v} : Finset ι) ∉ K) (hfin : K.faces.Finite)
    (hK : K ≤ A.toPreAbstractSimplicialComplex)
    (hS : stellarSubdivision K σ v ≤ A.toPreAbstractSimplicialComplex) :
    ∃ e : {x : Realization A // x.1.support ∈ stellarSubdivision K σ v} ≃ₜ
        {x : Realization A // x.1.support ∈ K},
      (∀ x, ((e x).1.1 : ι → ℝ) = Finset.stellarSubdivisionCoordinateMap σ v x.1.1) ∧
      ∀ y, ((e.symm y).1.1 : ι → ℝ) =
        Finset.stellarSubdivisionInverseExtension σ (K.isRelLowerSet_faces hσ).1 v y.1.1 := by
  obtain ⟨e, he⟩ := exists_homeomorph_stellarSubdivision hσ hv hfin hK hS
  refine ⟨e, fun x => ?_, fun y => ?_⟩
  · simp [he x]
  · obtain ⟨x, rfl⟩ := e.surjective y
    rw [e.symm_apply_apply, he x]
    exact (Finset.stellarSubdivisionInverseExtension_stellarSubdivisionLinearMap
      (K.isRelLowerSet_faces hσ).1 (notMem_of_singleton_notMem hv hσ)
      (Realization.nonneg A x.1) x.2).symm

end

end PreAbstractSimplicialComplex

public section

open Set TauCeti AbstractSimplicialComplex

namespace PreAbstractSimplicialComplex

variable {ι : Type*} [DecidableEq ι]
  {K L : PreAbstractSimplicialComplex ι}

/-! ### PL formulas along a stellar equivalence -/

/-- A homeomorphism package whose two ambient coordinate formulas are piecewise linear. -/
def IsPLHomeomorphPackage (A B : PreAbstractSimplicialComplex ι) : Prop :=
  ∃ e : {x : Realization (⊤ : AbstractSimplicialComplex ι) // x.1.support ∈ A} ≃ₜ
      {x : Realization (⊤ : AbstractSimplicialComplex ι) // x.1.support ∈ B},
    ∃ f g : (ι → ℝ) → (ι → ℝ),
      IsPLOn f (range fun x : {x : Realization (⊤ : AbstractSimplicialComplex ι) //
        x.1.support ∈ A} => (x.1.1 : ι → ℝ)) ∧
      IsPLOn g (range fun x : {x : Realization (⊤ : AbstractSimplicialComplex ι) //
        x.1.support ∈ B} => (x.1.1 : ι → ℝ)) ∧
      (∀ x, f (x.1.1 : ι → ℝ) = (e x).1.1) ∧
      (∀ y, g (y.1.1 : ι → ℝ) = (e.symm y).1.1)

/-- The PL package for one stellar move, using the inverse and forward coordinate extensions. -/
theorem IsStellarMove.exists_homeomorph_isPLOn
    {A B : PreAbstractSimplicialComplex ι} (h : IsStellarMove A B)
    (hfin : A.faces.Finite) : IsPLHomeomorphPackage A B := by
  obtain ⟨σ, v, hσ, hv, rfl⟩ := isStellarMove_iff.mp h
  obtain ⟨e, he, heinv⟩ := exists_homeomorph_stellarSubdivision_with_inverse
    hσ hv hfin (le_top _) (le_top _)
  let f : (ι → ℝ) → (ι → ℝ) :=
    Finset.stellarSubdivisionInverseExtension σ (A.isRelLowerSet_faces hσ).1 v
  let g : (ι → ℝ) → (ι → ℝ) := Finset.stellarSubdivisionCoordinateMap σ v
  have hf : IsPLOn f (range fun x : {x : Realization (⊤ : AbstractSimplicialComplex ι) //
      x.1.support ∈ A} => (x.1.1 : ι → ℝ)) := by
    exact (Finset.isPiecewiseAffineOn_stellarSubdivisionInverseExtension σ
      (A.isRelLowerSet_faces hσ).1 v).isPLOn.mono (subset_univ _)
  have hg : IsPLOn g (range fun x : {x : Realization (⊤ : AbstractSimplicialComplex ι) //
      x.1.support ∈ stellarSubdivision A σ v} => (x.1.1 : ι → ℝ)) := by
    exact isPLOn_continuousAffineMap
      (Finset.stellarSubdivisionCoordinateMap σ v).toContinuousAffineMap _
  exact ⟨e.symm, f, g, hf, hg, (fun x => by simpa only [f] using (heinv x).symm),
    (fun y => by simpa only [g, Homeomorph.symm_symm] using (he y).symm)⟩

omit [DecidableEq ι] in
/-- Symmetry swaps the forward and inverse maps in a PL homeomorphism package. -/
theorem IsPLHomeomorphPackage.symm {A B : PreAbstractSimplicialComplex ι}
    (h : IsPLHomeomorphPackage A B) : IsPLHomeomorphPackage B A := by
  rcases h with ⟨e, f, g, hf, hg, he, heinv⟩
  exact ⟨e.symm, g, f, hg, hf, heinv, he⟩

omit [DecidableEq ι] in
/-- Composition of PL homeomorph packages composes their ambient coordinate formulas. -/
theorem IsPLHomeomorphPackage.trans {A B C : PreAbstractSimplicialComplex ι}
    (hAB : IsPLHomeomorphPackage A B) (hBC : IsPLHomeomorphPackage B C) :
    IsPLHomeomorphPackage A C := by
  rcases hAB with ⟨e₁, f₁, g₁, hf₁, hg₁, he₁, he₁inv⟩
  rcases hBC with ⟨e₂, f₂, g₂, hf₂, hg₂, he₂, he₂inv⟩
  have hmap₁ : (range fun x : {x : Realization (⊤ : AbstractSimplicialComplex ι) //
      x.1.support ∈ A} => (x.1.1 : ι → ℝ)) ⊆ f₁ ⁻¹'
      (range fun x : {x : Realization (⊤ : AbstractSimplicialComplex ι) //
        x.1.support ∈ B} => (x.1.1 : ι → ℝ)) := by
    rintro _ ⟨x, rfl⟩
    exact ⟨e₁ x, (he₁ x).symm⟩
  have hmap₂ : (range fun y : {x : Realization (⊤ : AbstractSimplicialComplex ι) //
      x.1.support ∈ C} => (y.1.1 : ι → ℝ)) ⊆ g₂ ⁻¹'
      (range fun x : {x : Realization (⊤ : AbstractSimplicialComplex ι) //
        x.1.support ∈ B} => (x.1.1 : ι → ℝ)) := by
    rintro _ ⟨y, rfl⟩
    exact ⟨e₂.symm y, (he₂inv y).symm⟩
  refine ⟨e₁.trans e₂, f₂ ∘ f₁, g₁ ∘ g₂,
    hf₂.comp hf₁ hmap₁, hg₁.comp hg₂ hmap₂, ?_, ?_⟩
  · intro x
    simp only [Function.comp_apply, he₁ x, he₂ (e₁ x), Homeomorph.trans_apply]
  · intro y
    simp only [Function.comp_apply, he₂inv y, he₁inv (e₂.symm y), Homeomorph.symm_trans_apply]

/-- Finite stellar equivalences admit a PL homeomorphism package, by induction on their moves. -/
theorem StellarEquivalent.exists_isPLHomeomorphPackage
    (h : StellarEquivalent K L) (hfin : K.faces.Finite) : IsPLHomeomorphPackage K L := by
  have hQ : (K.faces.Finite ↔ L.faces.Finite) ∧
      ∀ hfin : K.faces.Finite, IsPLHomeomorphPackage K L := by
    refine StellarEquivalent.induction_on h
      (P := fun A B => (A.faces.Finite ↔ B.faces.Finite) ∧
        (∀ hfin : A.faces.Finite, IsPLHomeomorphPackage A B)) ?_ ?_ ?_ ?_
    · intro A B hmove
      exact ⟨hmove.finite_faces_iff, fun hfin => hmove.exists_homeomorph_isPLOn hfin⟩
    · intro A
      exact ⟨Iff.rfl, fun _ => ⟨Homeomorph.refl _, id, id, isPLOn_id _, isPLOn_id _,
        (fun _ => rfl), (fun _ => rfl)⟩⟩
    · intro A B ih
      exact ⟨ih.1.symm, fun hfin => (ih.2 (ih.1.mpr hfin)).symm⟩
    · intro A B C ihAB ihBC
      exact ⟨ihAB.1.trans ihBC.1, fun hfin =>
        (ihAB.2 hfin).trans (ihBC.2 (ihAB.1.mp hfin))⟩
  exact hQ.2 hfin

/-- A finite stellar equivalence identifies its weak polyhedra by maps that are piecewise linear
in their ambient barycentric coordinates. The two `IsPLOn` statements are the coordinate formulas
needed to transport local PL charts across a sequence of stellar moves. -/
theorem StellarEquivalent.exists_homeomorph_isPLOn
    (h : StellarEquivalent K L) (hfin : K.faces.Finite) :
    ∃ e : {x : Realization (⊤ : AbstractSimplicialComplex ι) // x.1.support ∈ K} ≃ₜ
        {x : Realization (⊤ : AbstractSimplicialComplex ι) // x.1.support ∈ L},
      ∃ f g : (ι → ℝ) → (ι → ℝ),
        IsPLOn f (range fun x : {x : Realization (⊤ : AbstractSimplicialComplex ι) //
          x.1.support ∈ K} => (x.1.1 : ι → ℝ)) ∧
        IsPLOn g (range fun x : {x : Realization (⊤ : AbstractSimplicialComplex ι) //
          x.1.support ∈ L} => (x.1.1 : ι → ℝ)) ∧
        (∀ x, f (x.1.1 : ι → ℝ) = (e x).1.1) ∧
        (∀ y, g (y.1.1 : ι → ℝ) = (e.symm y).1.1) := by
  exact h.exists_isPLHomeomorphPackage hfin

/-- Stellar equivalent finite precomplexes have homeomorphic weak polyhedra. -/
theorem StellarEquivalent.nonempty_homeomorph (h : StellarEquivalent K L)
    (hfin : K.faces.Finite) :
    Nonempty ({x : Realization (⊤ : AbstractSimplicialComplex ι) // x.1.support ∈ K} ≃ₜ
      {x : Realization (⊤ : AbstractSimplicialComplex ι) // x.1.support ∈ L}) := by
  obtain ⟨e, -⟩ := h.exists_homeomorph_isPLOn hfin
  exact ⟨e⟩

private noncomputable def topRelabelingHomeomorph {κ : Type*} [DecidableEq κ]
    (P : PreAbstractSimplicialComplex ι) (f : ι ↪ κ) :
    {x : Realization (⊤ : AbstractSimplicialComplex ι) // x.1.support ∈ P} ≃ₜ
      {y : Realization (⊤ : AbstractSimplicialComplex κ) // y.1.support ∈ P.map f} :=
  P.relabelingHomeomorph f
    (fun _ hτ => TauCeti.AbstractSimplicialComplex.mem_top_iff.mpr
      (P.isRelLowerSet_faces.prop_of_mem hτ))
    (fun _ hτ => TauCeti.AbstractSimplicialComplex.mem_top_iff.mpr
      (P.map f |>.isRelLowerSet_faces.prop_of_mem hτ))

/-- Intrinsic stellar equivalence gives homeomorphic weak polyhedra even when the two complexes
use different vertex labels. The two relabelings in the definition are removed by the canonical
homeomorphisms of `Realization.Relabel`. -/
theorem StellarEquivalentUpToRelabeling.nonempty_homeomorph
    (h : StellarEquivalentUpToRelabeling K L) (hfin : K.faces.Finite) :
    Nonempty ({x : Realization (⊤ : AbstractSimplicialComplex ι) // x.1.support ∈ K} ≃ₜ
      {x : Realization (⊤ : AbstractSimplicialComplex ι) // x.1.support ∈ L}) := by
  have aux : ∀ A B : PreAbstractSimplicialComplex ι,
      StellarEquivalentUpToRelabeling A B →
        (A.faces.Finite ↔ B.faces.Finite) ∧
          (A.faces.Finite →
            Nonempty ({x : Realization (⊤ : AbstractSimplicialComplex ι) // x.1.support ∈ A} ≃ₜ
              {x : Realization (⊤ : AbstractSimplicialComplex ι) // x.1.support ∈ B})) := by
    intro A B hAB
    apply StellarEquivalentUpToRelabeling.induction_on hAB
    · intro P Q f g he
      have hPmap : (P.map f).faces.Finite ↔ P.faces.Finite :=
        finite_faces_map_iff_of_injective f f.injective
      have hQmap : (Q.map g).faces.Finite ↔ Q.faces.Finite :=
        finite_faces_map_iff_of_injective g g.injective
      refine ⟨hPmap.symm.trans (he.finite_faces_iff.trans hQmap), ?_⟩
      intro hPfin
      have hPmapfin : (P.map f).faces.Finite := hPmap.mpr hPfin
      obtain ⟨e⟩ := he.nonempty_homeomorph hPmapfin
      exact ⟨(topRelabelingHomeomorph P f).trans
        (e.trans (topRelabelingHomeomorph Q g).symm)⟩
    · intro P
      exact ⟨Iff.rfl, fun _ => ⟨Homeomorph.refl _⟩⟩
    · intro P Q ih
      refine ⟨ih.1.symm, ?_⟩
      intro hQfin
      obtain ⟨e⟩ := ih.2 (ih.1.mpr hQfin)
      exact ⟨e.symm⟩
    · intro P Q R ihPQ ihQR
      refine ⟨ihPQ.1.trans ihQR.1, ?_⟩
      intro hPfin
      obtain ⟨e⟩ := ihPQ.2 hPfin
      obtain ⟨e'⟩ := ihQR.2 (ihPQ.1.mp hPfin)
      exact ⟨e.trans e'⟩
  exact (aux K L h).2 hfin

end PreAbstractSimplicialComplex
