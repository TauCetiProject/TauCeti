/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.FundamentalGroup.VanKampen.Basic

import TauCeti.AlgebraicTopology.FundamentalGroupoid.Glue
import TauCeti.CategoryTheory.Groupoid.SingleObj
import TauCeti.CategoryTheory.Groupoid.ConnectedFunctor

/-!
# Based van Kampen for neighborhood covers

Homomorphisms out of the fundamental groups of a family whose interiors cover the space
glue uniquely when they agree on each pairwise intersection, provided the triple intersections
are path connected and every member contains the basepoint. Repeated triple indices imply path
connectedness of the double intersections and individual members. The overlaps may differ from
pair to pair.
This gives the universal property needed to compute a fundamental group by successively
adjoining cover members, without requiring a single common overlap. Finiteness of the family is
unnecessary.

Pairwise compatibility defines transitions between local functors, and paths in triple
intersections establish their cocycle law. Choosing a cover member at each point makes these
functors agree on overlaps, so the fundamental-groupoid gluing theorem applies. No cover member
is required to be open.

## References

* A. Hatcher, *Algebraic Topology*, Cambridge University Press, 2002, Theorem 1.20.
* R. Brown, *Topology and Groupoids*, 3rd ed., Section 6.7.
-/

public section

open CategoryTheory Set Topology
open scoped FundamentalGroupoid

universe u v w

namespace TauCeti

variable {K : Type w} [Monoid K]

/-- **The based van Kampen theorem for a neighborhood cover, in universal-property form.**
Pairwise compatible homomorphisms out of the fundamental groups of the cover members extend
uniquely to the ambient fundamental group. Repeated indices in the triple-intersection
hypothesis imply path connectedness of the double intersections and individual members. No
common pairwise intersection is required, and the target can be any monoid. -/
theorem existsUnique_vanKampenDesc {X : Type v} [TopologicalSpace X]
    {ι : Type u} (U : ι → Set X) (x : X)
    (hCover : ∀ y, ∃ i, U i ∈ 𝓝 y)
    (hx : ∀ i, x ∈ U i)
    (hTriple : ∀ i j k, IsPathConnected (U i ∩ U j ∩ U k))
    (f : ∀ i, FundamentalGroup (U i) ⟨x, hx i⟩ →* K)
    (hcompat : ∀ i j,
      (f i).comp (FundamentalGroup.map (ContinuousMap.inclusion inter_subset_left)
          ⟨x, hx i, hx j⟩) =
        (f j).comp (FundamentalGroup.map (ContinuousMap.inclusion inter_subset_right)
          ⟨x, hx i, hx j⟩)) :
    ∃! d : FundamentalGroup X x →* K, ∀ i,
      d.comp (FundamentalGroup.map (ContinuousMap.subtypeVal (U i)) ⟨x, hx i⟩) = f i := by
  classical
  -- A neighborhood cover need not restrict to a subfamily, so glue using the whole family.
  have hDouble (i j : ι) : IsPathConnected (U i ∩ U j) := by
    simpa only [Set.inter_assoc, Set.inter_self] using hTriple i j j
  have hUp (i : ι) : IsPathConnected (U i) := by simpa using hDouble i i
  -- Normalize the base paths so the induced functors retain the given maps on based loops.
  -- Images of groups lie in units, allowing transitions while the public target is a monoid.
  let b (i : ι) := (FundamentalGroupoid.mk (⟨x, hx i⟩ : U i))
  let τ (i : ι) (y : FundamentalGroupoid (U i)) : b i ⟶ y :=
    if hy : y = b i then eqToHom hy.symm else
      letI := isPathConnected_iff_pathConnectedSpace.mp (hUp i)
      (FundamentalGroupoid.nonempty_hom _ _).some
  have hτ (i : ι) : τ i (b i) = 𝟙 _ := by simp [τ]
  let F (i : ι) : FundamentalGroupoid (U i) ⥤ SingleObj Kˣ :=
    Groupoid.functorOfEndHom (b i) (τ i) (f i).toHomUnits
  have hFbase (i : ι) (g : FundamentalGroup (U i) ⟨x, hx i⟩) :
      (F i).map g = (f i).toHomUnits g := by
    rw [Groupoid.functorOfEndHom_map]
    -- Pin the chosen basepoint carrier before applying its normalized transport equation.
    change (f i).toHomUnits (τ i (b i) ≫ g ≫ inv (τ i (b i))) = _
    erw [hτ, IsIso.inv_id, Category.id_comp, Category.comp_id]
  let L (i j : ι) : C(↥(U i ∩ U j), U i) := ContinuousMap.inclusion inter_subset_left
  let R (i j : ι) : C(↥(U i ∩ U j), U j) := ContinuousMap.inclusion inter_subset_right
  have hloop (i j : ι) (g : FundamentalGroup ↥(U i ∩ U j) ⟨x, hx i, hx j⟩) :
      (F i).map ((FundamentalGroupoid.map (L i j)).map g) =
        (F j).map ((FundamentalGroupoid.map (R i j)).map g) := by
    erw [hFbase, hFbase]
    apply Units.ext
    exact DFunLike.congr_fun (hcompat i j) g
  -- Pairwise compatible based maps extend to natural isomorphisms on the double overlaps.
  let T (i j : ι) : FundamentalGroupoid.map (L i j) ⋙ F i ≅
      FundamentalGroupoid.map (R i j) ⋙ F j :=
    Groupoid.natIsoOfEnd
      (x₀ := FundamentalGroupoid.mk (⟨x, hx i, hx j⟩ : ↥(U i ∩ U j)))
      (fun y ↦ by
        let := isPathConnected_iff_pathConnectedSpace.mp (hDouble i j)
        exact FundamentalGroupoid.nonempty_hom _ _) (Iso.refl _)
      (fun g ↦ by
        simpa only [Functor.comp_map, Iso.refl_hom, Category.comp_id, Category.id_comp] using
          hloop i j g)
  let t (i j : ι) (y : ↥(U i ∩ U j)) :
      SingleObj.star Kˣ ⟶ SingleObj.star Kˣ := (T i j).hom.app (FundamentalGroupoid.mk y)
  have htbase (i j : ι) : t i j ⟨x, hx i, hx j⟩ = 𝟙 _ := by
    have h := congrArg Iso.hom (Groupoid.natIsoOfEnd_app_self
      (F := FundamentalGroupoid.map (L i j) ⋙ F i)
      (G := FundamentalGroupoid.map (R i j) ⋙ F j)
      (x₀ := FundamentalGroupoid.mk (⟨x, hx i, hx j⟩ : ↥(U i ∩ U j)))
      (fun y ↦ by
        let := isPathConnected_iff_pathConnectedSpace.mp (hDouble i j)
        exact FundamentalGroupoid.nonempty_hom _ _) (Iso.refl _)
      (fun g ↦ by
        simpa only [Functor.comp_map, Iso.refl_hom, Category.comp_id, Category.id_comp] using
          hloop i j g))
    exact h
  have ht (i j : ι) (y : ↥(U i ∩ U j))
      (q : FundamentalGroupoid.mk (⟨x, hx i, hx j⟩ : ↥(U i ∩ U j)) ⟶
        FundamentalGroupoid.mk y) :
      (F i).map ((FundamentalGroupoid.map (L i j)).map q) ≫ t i j y =
        (F j).map ((FundamentalGroupoid.map (R i j)).map q) := by
    have h := (T i j).hom.naturality q
    -- Pin the overlap basepoint, whose transition component is the identity.
    change _ ≫ t i j y = t i j ⟨x, hx i, hx j⟩ ≫ _ at h
    erw [htbase, Category.id_comp] at h
    exact h
  have htnat (i j : ι) (y z : ↥(U i ∩ U j))
      (g : FundamentalGroupoid.mk y ⟶ FundamentalGroupoid.mk z) :
      (F i).map ((FundamentalGroupoid.map (L i j)).map g) ≫ t i j z =
        t i j y ≫ (F j).map ((FundamentalGroupoid.map (R i j)).map g) :=
    (T i j).hom.naturality g
  -- One path in the triple overlap computes all three transitions, proving the cocycle law.
  have htcocycle (i j k : ι) (y : X) (hi : y ∈ U i) (hj : y ∈ U j) (hk : y ∈ U k) :
      t i j ⟨y, hi, hj⟩ ≫ t j k ⟨y, hj, hk⟩ = t i k ⟨y, hi, hk⟩ := by
    let := isPathConnected_iff_pathConnectedSpace.mp (hTriple i j k)
    let q : FundamentalGroupoid.mk (⟨x, ⟨hx i, hx j⟩, hx k⟩ : ↥(U i ∩ U j ∩ U k)) ⟶
        FundamentalGroupoid.mk (⟨y, ⟨hi, hj⟩, hk⟩ : ↥(U i ∩ U j ∩ U k)) :=
      (FundamentalGroupoid.nonempty_hom _ _).some
    let qi := (FundamentalGroupoid.map
      (ContinuousMap.inclusion (s := U i ∩ U j ∩ U k) (t := U i ∩ U j)
        inter_subset_left)).map q
    let qj := (FundamentalGroupoid.map
      (ContinuousMap.inclusion (s := U i ∩ U j ∩ U k) (t := U j ∩ U k)
        (fun _ h ↦ ⟨h.1.2, h.2⟩))).map q
    let qk := (FundamentalGroupoid.map
      (ContinuousMap.inclusion (s := U i ∩ U j ∩ U k) (t := U i ∩ U k)
        (fun _ h ↦ ⟨h.1.1, h.2⟩))).map q
    have hai := ht i j ⟨y, hi, hj⟩ qi
    have haj := ht j k ⟨y, hj, hk⟩ qj
    have hak := ht i k ⟨y, hi, hk⟩ qk
    -- The composites of inclusions keep the underlying paths and their endpoints.
    have hqi : (FundamentalGroupoid.map (L i j)).map qi =
        (FundamentalGroupoid.map (L i k)).map qk := by
      dsimp only [qi, qk]
      rw [← FundamentalGroupoid.map_comp_map, ← FundamentalGroupoid.map_comp_map]
      rfl
    have hqj : (FundamentalGroupoid.map (R i j)).map qi =
        (FundamentalGroupoid.map (L j k)).map qj := by
      dsimp only [qi, qj]
      rw [← FundamentalGroupoid.map_comp_map, ← FundamentalGroupoid.map_comp_map]
      rfl
    have hqk : (FundamentalGroupoid.map (R j k)).map qj =
        (FundamentalGroupoid.map (R i k)).map qk := by
      dsimp only [qj, qk]
      rw [← FundamentalGroupoid.map_comp_map, ← FundamentalGroupoid.map_comp_map]
      rfl
    apply (cancel_epi ((F i).map ((FundamentalGroupoid.map (L i j)).map qi))).mp
    erw [← Category.assoc, hai, hqj, haj, hqk, hqi, hak]
    rfl
  have htself (i : ι) (y : U i) : t i i ⟨y, y.2, y.2⟩ = 𝟙 _ := by
    apply (cancel_epi (t i i ⟨y, y.2, y.2⟩)).mp
    exact (htcocycle i i i y y.2 y.2 y.2).trans (Category.comp_id _).symm
  -- Choose a reference member at each point and conjugate the local functors into that gauge.
  let c (y : X) : ι := (hCover y).choose
  have hc (y : X) : y ∈ U (c y) := mem_of_mem_nhds (hCover y).choose_spec
  let G (i : ι) : FundamentalGroupoid (U i) ⥤ SingleObj Kˣ :=
    { obj := fun _ ↦ SingleObj.star Kˣ
      map := fun {y z} g ↦
        t (c y.as.1) i ⟨y.as.1, hc _, y.as.2⟩ ≫ (F i).map g ≫
          t i (c z.as.1) ⟨z.as.1, z.as.2, hc _⟩
      map_id := fun y ↦ by
        erw [CategoryTheory.Functor.map_id, Category.id_comp,
          htcocycle (c y.as.1) i (c y.as.1) y.as.1 (hc _) y.as.2 (hc _)]
        exact htself (c y.as.1) ⟨y.as.1, hc _⟩
      map_comp := fun {y z w} g h ↦ by
        rw [Functor.map_comp]
        simp only [Category.assoc]
        rw [← Category.assoc (t i (c z.as.1) _) (t (c z.as.1) i _) _,
          htcocycle i (c z.as.1) i z.as.1 z.as.2 (hc _) z.as.2, htself, Category.id_comp] }
  have hGcompat (i j : ι) :
      FundamentalGroupoid.map (L i j) ⋙ G i = FundamentalGroupoid.map (R i j) ⋙ G j := by
    refine CategoryTheory.Functor.ext (fun _ ↦ rfl) fun y z g ↦ ?_
    simp only [Functor.comp_map, G, eqToHom_refl, Category.id_comp, Category.comp_id]
    -- The inclusion functors preserve points; pin the common single-object morphism carrier.
    let gi : Kˣ :=
      (F i).map ((FundamentalGroupoid.map (L i j)).map g)
    let gj : Kˣ :=
      (F j).map ((FundamentalGroupoid.map (R i j)).map g)
    change t (c y.as.1) i ⟨y.as.1, hc _, y.as.2.1⟩ ≫ gi ≫
        t i (c z.as.1) ⟨z.as.1, z.as.2.1, hc _⟩ =
      t (c y.as.1) j ⟨y.as.1, hc _, y.as.2.2⟩ ≫ gj ≫
        t j (c z.as.1) ⟨z.as.1, z.as.2.2, hc _⟩
    -- Work in the unit group: SingleObj composition is reversed multiplication.
    let tr (i j : ι) (y : ↥(U i ∩ U j)) : Kˣ := t i j y
    have hy : tr i j y.as * tr (c y.as.1) i ⟨y.as.1, hc _, y.as.2.1⟩ =
        tr (c y.as.1) j ⟨y.as.1, hc _, y.as.2.2⟩ := by
      simpa only [SingleObj.comp_as_mul] using
        htcocycle (c y.as.1) i j y.as.1 (hc _) y.as.2.1 y.as.2.2
    have hz : tr j (c z.as.1) ⟨z.as.1, z.as.2.2, hc _⟩ * tr i j z.as =
        tr i (c z.as.1) ⟨z.as.1, z.as.2.1, hc _⟩ := by
      simpa only [SingleObj.comp_as_mul] using
        htcocycle i j (c z.as.1) z.as.1 z.as.2.1 z.as.2.2 (hc _)
    have hn : tr i j z.as * gi = gj * tr i j y.as := by
      simpa only [SingleObj.comp_as_mul] using htnat i j y.as z.as g
    simp only [SingleObj.comp_as_mul]
    change tr i (c z.as.1) ⟨z.as.1, z.as.2.1, hc _⟩ * gi *
        tr (c y.as.1) i ⟨y.as.1, hc _, y.as.2.1⟩ =
      tr j (c z.as.1) ⟨z.as.1, z.as.2.2, hc _⟩ * gj *
        tr (c y.as.1) j ⟨y.as.1, hc _, y.as.2.2⟩
    calc
      _ = (tr j (c z.as.1) ⟨z.as.1, z.as.2.2, hc _⟩ * tr i j z.as) * gi *
          tr (c y.as.1) i ⟨y.as.1, hc _, y.as.2.1⟩ :=
        congrArg (fun v ↦ v * gi * tr (c y.as.1) i ⟨y.as.1, hc _, y.as.2.1⟩) hz.symm
      _ = tr j (c z.as.1) ⟨z.as.1, z.as.2.2, hc _⟩ * (gj * tr i j y.as) *
          tr (c y.as.1) i ⟨y.as.1, hc _, y.as.2.1⟩ := by
        rw [mul_assoc (tr j (c z.as.1) ⟨z.as.1, z.as.2.2, hc _⟩) (tr i j z.as) gi, hn]
      _ = _ := by
        rw [mul_assoc, mul_assoc, hy, ← mul_assoc]
  -- Glue the now compatible functors, restrict to based loops, and forget the units.
  let d' : FundamentalGroup X x →* Kˣ :=
    (SingleObj.mapHom _ _).symm (Groupoid.singleObjFunctor (FundamentalGroupoid.mk x) ⋙
      FundamentalGroupoid.glue hCover G hGcompat)
  let d : FundamentalGroup X x →* K := (Units.coeHom K).comp d'
  have hd (i : ι) : d.comp (FundamentalGroup.map (ContinuousMap.subtypeVal (U i))
      ⟨x, hx i⟩) = f i := by
    ext g
    have h := CategoryTheory.Functor.congr_hom
      (FundamentalGroupoid.map_subtypeVal_comp_glue hCover G hGcompat i) g
    simp only [Functor.comp_map, eqToHom_refl, Category.id_comp, Category.comp_id] at h
    have hbase : (G i).map g = (f i).toHomUnits g := by
      -- Both transition endpoints are the basepoint, where each transition is the identity.
      change t (c x) i _ ≫ (F i).map g ≫ t i (c x) _ = _
      erw [htbase, htbase, Category.id_comp, Category.comp_id, hFbase]
    exact congrArg Units.val (h.trans hbase)
  exact ⟨d, hd, fun d' hd' ↦ vanKampenWide_hom_ext hCover hx hDouble
    (fun i ↦ (hd' i).trans (hd i).symm)⟩

end TauCeti
