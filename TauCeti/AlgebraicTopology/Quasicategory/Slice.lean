/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicTopology.SimplicialSet.CategoryWithFibrations
public import TauCeti.AlgebraicTopology.Quasicategory.RightFibration
public import TauCeti.AlgebraicTopology.SimplicialSet.Coslice
public import TauCeti.AlgebraicTopology.SimplicialSet.Join.StdSimplex

/-!
# Slices of quasicategories

For a quasicategory `C` and a diagram `p : K ⟶ C`, the slice `C_{/p}` is again a quasicategory,
and its projection `C_{/p} ⟶ C` has the right lifting property with respect to the horn
inclusions `Λ[m, i] ⟶ Δ[m]` with `0 < i`, including the final horns `Λ[m, m]`; that is, it is a
right fibration in the sense of *Higher Topos Theory*, §2.1.2. The slice is the quasicategory of
cones over `p`, and a limit of `p` is a final object of it.

A lifting problem of `Λ[m, i] ⟶ Δ[m]` against `C_{/p} ⟶ C` is an extension problem for maps into
`C` along `(Λ[m, i] ⋆ K) ∪ Δ[m] ⟶ Δ[m] ⋆ K`. Through the universal property of the coslice, such
extension problems along `(Λ[m, i] ⋆ Y) ∪ (Δ[m] ⋆ X) ⟶ Δ[m] ⋆ Y`, for a monomorphism `X ⟶ Y`,
are lifting problems of `X ⟶ Y` against the restriction of cocones
`C_{σ/} ⟶ C_{(Λ[m, i] ⟶ Δ[m] ⟶ C)/}` for a simplex `σ : Δ[m] ⟶ C`. This restriction is a trivial
fibration: by Mathlib's description of the trivial fibrations as the maps lifting against
boundary inclusions (`SSet.rlp_monomorphisms`), it suffices to treat `∂Δ[n] ⟶ Δ[n]`, where the
pushout-join `(Λ[m, i] ⋆ Δ[n]) ∪ (Δ[m] ⋆ ∂Δ[n])` is the inner horn `Λ[m + n + 1, i]`.

More generally, for a monomorphism `j : L ⟶ K` and `0 < i`, a lifting problem of
`Λ[m, i] ⟶ Δ[m]` against the restriction of cones `C_{/p} ⟶ C_{/j ≫ p}` is a lifting problem of
`j` against the restriction of cocones `C_{σ/} ⟶ C_{(Λ[m, i] ⟶ Δ[m] ⟶ C)/}` along
`Λ[m, i] ⟶ Δ[m]`, a trivial fibration, so the restriction of cones is a right fibration. As a
right fibration over a quasicategory, it lifts with prescribed source every edge whose image in
`C` is an equivalence.

## Main results

* `SSet.coslice.hasLiftingProperty_map_horn_ι`: for a quasicategory `C`, a simplex
  `σ : Δ[m] ⟶ C` and `0 < i`, restriction of cocones `C_{σ/} ⟶ C_{(Λ[m, i] ⟶ Δ[m] ⟶ C)/}` has
  the right lifting property with respect to every monomorphism.
* `SSet.slice.hasLiftingProperty_horn_ι_π`: for a quasicategory `C` and `0 < i`, the projection
  `C_{/p} ⟶ C` has the right lifting property with respect to `Λ[m, i] ⟶ Δ[m]`.
* `SSet.slice.rightFibration_π`, `SSet.slice.quasicategory`: the projection of the slice of a
  quasicategory is a right fibration, and the slice is a quasicategory.
* `SSet.slice.hasLiftingProperty_horn_ι_map`, `SSet.slice.rightFibration_map`: for a
  monomorphism `j : L ⟶ K`, the restriction of cones `C_{/p} ⟶ C_{/j ≫ p}` is a right fibration.
* `SSet.slice.hasLift_of_isEquivalence`: this restriction lifts, with prescribed source, every
  edge whose image in `C` is an equivalence.
* `SSet.slice.hasLiftingProperty_map_horn_ι`: for a simplex `τ : Δ[m] ⟶ C` and `j < m`, the
  restriction of cones `C_{/τ} ⟶ C_{/(Λ[m, j] ⟶ Δ[m] ⟶ C)}` is a trivial fibration, by the inner
  horns `(∂Δ[n] ⋆ Δ[m]) ∪ (Δ[n] ⋆ Λ[m, j])`; in particular
  (`SSet.slice.hasLiftingProperty_map_δ_one`) so is the restriction `C_{/g} ⟶ C_{/g(0)}` of cones
  over an edge `g` to cones over its source.

## Implementation notes

The reduction of `SSet.coslice.hasLiftingProperty_map_horn_ι` to boundary inclusions and an
inner anodyne pushout-join follows the shape of the proof of Mathlib's
`SSet.innerFibration_pullbackObjObjπ` by Jack McKoen and Joël Riou, with coslices playing the
role of the internal hom.

## References

* J. Lurie, *Higher Topos Theory*, Lemma 2.1.2.3, Proposition 2.1.2.1, Corollary 2.1.2.2 and
  Proposition 2.1.2.5.
* A. Joyal, *Quasi-categories and Kan complexes*, J. Pure Appl. Algebra 175 (2002).
-/

public section

open CategoryTheory Limits MorphismProperty Simplicial

universe u

namespace SSet

variable {K C : SSet.{u}} {m : ℕ} {i : Fin (m + 1)}

namespace coslice

/-- For a quasicategory `C`, a simplex `σ : Δ[m] ⟶ C` and `0 < i`, **the restriction of cocones
`C_{σ/} ⟶ C_{(Λ[m, i] ⟶ Δ[m] ⟶ C)/}` is a trivial fibration**: it has the right lifting property
with respect to every monomorphism `j : X ⟶ Y`. Through the universal property of the coslice,
this says that maps `(Λ[m, i] ⋆ Y) ∪ (Δ[m] ⋆ X) ⟶ C` extending `σ` extend to `Δ[m] ⋆ Y`. -/
theorem hasLiftingProperty_map_horn_ι [Quasicategory C] (hi : 0 < i) (σ : Δ[m] ⟶ C)
    {X Y : SSet.{u}} (j : X ⟶ Y) [Mono j] :
    HasLiftingProperty j
      (map Λ[m, i].ι (𝟙 C) (by simp) : coslice σ ⟶ coslice (Λ[m, i].ι ≫ σ)) := by
  suffices (monomorphisms SSet.{u}).rlp
      (map Λ[m, i].ι (𝟙 C) (by simp) : coslice σ ⟶ coslice (Λ[m, i].ι ≫ σ)) from
    this j (monomorphisms.infer_property j)
  rw [rlp_monomorphisms]
  rintro _ _ _ ⟨n⟩
  refine ⟨fun {a b} sq ↦ ?_⟩
  -- The square amounts to maps `Δ[m] ⋆ ∂Δ[n] ⟶ C` and `Λ[m, i] ⋆ Δ[n] ⟶ C` agreeing on
  -- `Λ[m, i] ⋆ ∂Δ[n]`. Glue them on the pushout-join and extend along the inner horn inclusion.
  have hw : join.map (𝟙 _) ∂Δ[n].ι ≫ (homEquiv b).val = join.map Λ[m, i].ι (𝟙 _) ≫ (homEquiv a).val
      :=
    by simpa using (congrArg (fun F ↦ (homEquiv F).val) sq.w).symm
  have hpush := Subcomplex.unionJoin.isPushout Λ[m, i] ∂Δ[n]
  have := join.innerAnodyneExtensions_unionJoin_horn_boundary n hi (terminal.from C)
    (mem_innerFibrations _)
  have sq' : CommSq (hpush.desc (homEquiv b).val (homEquiv a).val hw)
      (Λ[m, i].unionJoin ∂Δ[n]).ι (terminal.from C) (terminal.from _) :=
    ⟨Subsingleton.elim _ _⟩
  have h₁ : join.map Λ[m, i].ι (𝟙 _) ≫ sq'.lift = (homEquiv b).val := by
    rw [← Subcomplex.unionJoin.ι₁_ι, Category.assoc, sq'.fac_left, IsPushout.inl_desc]
  have h₂ : join.map (𝟙 _) ∂Δ[n].ι ≫ sq'.lift = (homEquiv a).val := by
    rw [← Subcomplex.unionJoin.ι₂_ι, Category.assoc, sq'.fac_left, IsPushout.inr_desc]
  refine ⟨⟨⟨homEquiv.symm ⟨sq'.lift, ?_⟩, ?_, ?_⟩⟩⟩
  · calc join.inl _ _ ≫ sq'.lift = join.inl _ _ ≫ join.map (𝟙 _) ∂Δ[n].ι ≫ sq'.lift := by
          rw [join.inl_map_assoc, Category.id_comp]
      _ = σ := by rw [h₂, (homEquiv a).property]
  · exact hom_ext (by rw [homEquiv_comp_coe, Equiv.apply_symm_apply, h₂])
  · exact hom_ext (by rw [homEquiv_comp_map_coe, Equiv.apply_symm_apply, Category.comp_id, h₁])

end coslice

namespace slice

/-- For a quasicategory `C` and `0 < i`, **the projection `C_{/p} ⟶ C` of a slice has the right
lifting property with respect to the horn inclusion `Λ[m, i] ⟶ Δ[m]`**. This includes the final
horns `Λ[m, m]`, so the projection is a right fibration. -/
theorem hasLiftingProperty_horn_ι_π [Quasicategory C] (p : K ⟶ C) (hi : 0 < i) :
    HasLiftingProperty Λ[m, i].ι (π p) := by
  refine ⟨fun {a b} sq ↦ ?_⟩
  -- A lift is a map `Δ[m] ⋆ K ⟶ C` extending `b` on `Δ[m]` and `a` on `Λ[m, i] ⋆ K`: lift the
  -- inclusion of the empty subcomplex of `K` against the restriction of cocones under `b`.
  have ha : join.inl _ K ≫ (homEquiv a).val = Λ[m, i].ι ≫ b := by rw [← comp_π, sq.w]
  have sq' : CommSq (Subcomplex.isInitialBot.to (coslice b)) (⊥ : K.Subcomplex).ι
      (coslice.map Λ[m, i].ι (𝟙 C) (by simp))
      (coslice.homEquiv.symm ⟨(homEquiv a).val, ha⟩) :=
    ⟨Subcomplex.isInitialBot.hom_ext _ _⟩
  have := coslice.hasLiftingProperty_map_horn_ι hi b (⊥ : K.Subcomplex).ι
  have h : join.map Λ[m, i].ι (𝟙 K) ≫ (coslice.homEquiv sq'.lift).val = (homEquiv a).val := by
    have h := congrArg (fun F ↦ (coslice.homEquiv F).val) sq'.fac_right
    rwa [coslice.homEquiv_comp_map_coe, Equiv.apply_symm_apply, Category.comp_id] at h
  refine ⟨⟨⟨homEquiv.symm ⟨(coslice.homEquiv sq'.lift).val, ?_⟩, ?_, ?_⟩⟩⟩
  · calc join.inr _ _ ≫ (coslice.homEquiv sq'.lift).val =
          join.inr _ _ ≫ join.map Λ[m, i].ι (𝟙 K) ≫ (coslice.homEquiv sq'.lift).val := by
          rw [join.inr_map_assoc, Category.id_comp]
      _ = p := by rw [h, (homEquiv a).property]
  · exact hom_ext (by rw [homEquiv_comp_coe, Equiv.apply_symm_apply, h])
  · rw [comp_π, Equiv.apply_symm_apply]
    exact (coslice.homEquiv sq'.lift).property

/-- The projection of the slice of a quasicategory is a right fibration, hence an inner
fibration. -/
instance rightFibration_π [Quasicategory C] (p : K ⟶ C) : RightFibration (π p) :=
  (rightFibration_iff_hasLiftingProperty _).2 fun _ _ h0 ↦ hasLiftingProperty_horn_ι_π p h0

/-- **The slice of a quasicategory is a quasicategory** (Joyal). -/
instance quasicategory [Quasicategory C] (p : K ⟶ C) : Quasicategory (slice p) :=
  quasicategory_of_innerFibration (π p)

variable {L : SSet.{u}}

/-- For a quasicategory `C`, a diagram `p : K ⟶ C`, a monomorphism `j : L ⟶ K` and `0 < i`,
**the restriction of cones `C_{/p} ⟶ C_{/j ≫ p}` has the right lifting property with respect to
the horn inclusion `Λ[m, i] ⟶ Δ[m]`**. Through the universal property of the slice, this says
that maps `(Λ[m, i] ⋆ K) ∪ (Δ[m] ⋆ L) ⟶ C` extend to `Δ[m] ⋆ K`. -/
theorem hasLiftingProperty_horn_ι_map [Quasicategory C] (p : K ⟶ C) (j : L ⟶ K) [Mono j]
    (hi : 0 < i) :
    HasLiftingProperty Λ[m, i].ι (map j (𝟙 C) (by simp) : slice p ⟶ slice (j ≫ p)) := by
  refine ⟨fun {a b} sq ↦ ?_⟩
  -- A lift is a map `Δ[m] ⋆ K ⟶ C` extending `b` on `Δ[m] ⋆ L` and `a` on `Λ[m, i] ⋆ K`: lift `j`
  -- against the restriction of cocones under the simplex `Δ[m] ⟶ C` underlying `b`.
  have ha : join.inl _ K ≫ (homEquiv a).val = Λ[m, i].ι ≫ join.inl _ L ≫ (homEquiv b).val := by
    rw [← comp_π, ← comp_π, ← Category.comp_id (π p), ← map_π (q := j ≫ p) j (𝟙 C) (by simp),
      reassoc_of% sq.w]
  have sq' : CommSq (coslice.homEquiv.symm ⟨(homEquiv b).val, rfl⟩) j
      (coslice.map Λ[m, i].ι (𝟙 C) (by simp)) (coslice.homEquiv.symm ⟨(homEquiv a).val, ha⟩) :=
    ⟨coslice.hom_ext (by
      have := congrArg (fun F ↦ (homEquiv F).val) sq.w
      rw [homEquiv_comp_map_coe, homEquiv_comp_coe, Category.comp_id] at this
      rw [coslice.homEquiv_comp_map_coe, coslice.homEquiv_comp_coe, Equiv.apply_symm_apply,
        Equiv.apply_symm_apply, Category.comp_id, this])⟩
  have := coslice.hasLiftingProperty_map_horn_ι hi (join.inl _ L ≫ (homEquiv b).val) j
  have h₁ : join.map Λ[m, i].ι (𝟙 K) ≫ (coslice.homEquiv sq'.lift).val = (homEquiv a).val := by
    have h := congrArg (fun F ↦ (coslice.homEquiv F).val) sq'.fac_right
    rwa [coslice.homEquiv_comp_map_coe, Equiv.apply_symm_apply, Category.comp_id] at h
  have h₂ : join.map (𝟙 _) j ≫ (coslice.homEquiv sq'.lift).val = (homEquiv b).val := by
    have h := congrArg (fun F ↦ (coslice.homEquiv F).val) sq'.fac_left
    rwa [coslice.homEquiv_comp_coe, Equiv.apply_symm_apply] at h
  refine ⟨⟨⟨homEquiv.symm ⟨(coslice.homEquiv sq'.lift).val, ?_⟩, ?_, ?_⟩⟩⟩
  · calc join.inr _ _ ≫ (coslice.homEquiv sq'.lift).val =
          join.inr _ _ ≫ join.map Λ[m, i].ι (𝟙 K) ≫ (coslice.homEquiv sq'.lift).val := by
          rw [join.inr_map_assoc, Category.id_comp]
      _ = p := by rw [h₁, (homEquiv a).property]
  · exact hom_ext (by rw [homEquiv_comp_coe, Equiv.apply_symm_apply, h₁])
  · exact hom_ext (by rw [homEquiv_comp_map_coe, Equiv.apply_symm_apply, Category.comp_id, h₂])

/-- For a quasicategory `C` and a monomorphism `j : L ⟶ K`, the restriction of cones
`C_{/p} ⟶ C_{/j ≫ p}` is a right fibration. -/
instance rightFibration_map [Quasicategory C] (p : K ⟶ C) (j : L ⟶ K) [Mono j] :
    RightFibration (map j (𝟙 C) (by simp) : slice p ⟶ slice (j ≫ p)) :=
  (rightFibration_iff_hasLiftingProperty _).2 fun _ _ h0 ↦ hasLiftingProperty_horn_ι_map p j h0

open Edge in
/-- For a quasicategory `C`, a diagram `p : K ⟶ C` and a monomorphism `j : L ⟶ K`, **the
restriction of cones `C_{/p} ⟶ C_{/j ≫ p}` lifts, with prescribed source, every edge whose image
in `C` is an equivalence**: a commutative square from `Λ[1, 0] ⟶ Δ[1]` to it has a lift when the
edge of `C` underlying its bottom edge is an equivalence. Through the universal property of the
slice, maps `(Λ[1, 0] ⋆ K) ∪ (Δ[1] ⋆ L) ⟶ C` extend to `Δ[1] ⋆ K` when their edge `Δ[1] ⟶ C` is an
equivalence. -/
theorem hasLift_of_isEquivalence [Quasicategory C] (p : K ⟶ C) (j : L ⟶ K) [Mono j]
    {t : (Λ[1, 0] : SSet) ⟶ slice p} {b : Δ[1] ⟶ slice (j ≫ p)}
    (sq : CommSq t Λ[1, 0].ι (map j (𝟙 C) (by simp)) b)
    (hb : (Edge.mk' (yonedaEquiv (b ≫ π (j ≫ p)))).IsEquivalence) : sq.HasLift :=
  RightFibration.hasLift_of_isEquivalence _ sq
    ((isEquivalence_map_iff_of_rightFibration (π (j ≫ p)) _).1
      ((isEquivalence_iff_of_edge_eq (by rw [map_edge, mk'_edge, mk'_edge, yonedaEquiv_comp])).2
        hb))

variable {j : Fin (m + 1)}

/-- For a quasicategory `C`, a simplex `τ : Δ[m] ⟶ C` and `j < m`, **the restriction of cones
`C_{/τ} ⟶ C_{/(Λ[m, j] ⟶ Δ[m] ⟶ C)}` is a trivial fibration**: it has the right lifting property
with respect to every monomorphism `i : X ⟶ Y`. Through the universal property of the slice, this
says that maps `(X ⋆ Δ[m]) ∪ (Y ⋆ Λ[m, j]) ⟶ C` extending `τ` extend to `Y ⋆ Δ[m]`. -/
theorem hasLiftingProperty_map_horn_ι [Quasicategory C] (hj : j < Fin.last m) (τ : Δ[m] ⟶ C)
    {X Y : SSet.{u}} (i : X ⟶ Y) [Mono i] :
    HasLiftingProperty i
      (map Λ[m, j].ι (𝟙 C) (by simp) : slice τ ⟶ slice (Λ[m, j].ι ≫ τ)) := by
  suffices (monomorphisms SSet.{u}).rlp
      (map Λ[m, j].ι (𝟙 C) (by simp) : slice τ ⟶ slice (Λ[m, j].ι ≫ τ)) from
    this i (monomorphisms.infer_property i)
  rw [rlp_monomorphisms]
  rintro _ _ _ ⟨n⟩
  refine ⟨fun {a b} sq ↦ ?_⟩
  -- The square amounts to maps `∂Δ[n] ⋆ Δ[m] ⟶ C` and `Δ[n] ⋆ Λ[m, j] ⟶ C` agreeing on
  -- `∂Δ[n] ⋆ Λ[m, j]`. Glue them on the pushout-join and extend along the inner horn inclusion.
  have hw : join.map (𝟙 _) Λ[m, j].ι ≫ (homEquiv a).val =
      join.map ∂Δ[n].ι (𝟙 _) ≫ (homEquiv b).val :=
    by simpa using congrArg (fun F ↦ (homEquiv F).val) sq.w
  have hpush := Subcomplex.unionJoin.isPushout ∂Δ[n] Λ[m, j]
  have := join.innerAnodyneExtensions_unionJoin_boundary_horn n hj (terminal.from C)
    (mem_innerFibrations _)
  have sq' : CommSq (hpush.desc (homEquiv a).val (homEquiv b).val hw)
      (Subcomplex.unionJoin ∂Δ[n] Λ[m, j]).ι (terminal.from C) (terminal.from _) :=
    ⟨Subsingleton.elim _ _⟩
  have h₁ : join.map ∂Δ[n].ι (𝟙 _) ≫ sq'.lift = (homEquiv a).val := by
    rw [← Subcomplex.unionJoin.ι₁_ι, Category.assoc, sq'.fac_left, IsPushout.inl_desc]
  have h₂ : join.map (𝟙 _) Λ[m, j].ι ≫ sq'.lift = (homEquiv b).val := by
    rw [← Subcomplex.unionJoin.ι₂_ι, Category.assoc, sq'.fac_left, IsPushout.inr_desc]
  refine ⟨⟨⟨homEquiv.symm ⟨sq'.lift, ?_⟩, ?_, ?_⟩⟩⟩
  · calc join.inr _ _ ≫ sq'.lift = join.inr _ _ ≫ join.map ∂Δ[n].ι (𝟙 _) ≫ sq'.lift := by
          rw [join.inr_map_assoc, Category.id_comp]
      _ = τ := by rw [h₁, (homEquiv a).property]
  · exact hom_ext (by rw [homEquiv_comp_coe, Equiv.apply_symm_apply, h₁])
  · exact hom_ext (by rw [homEquiv_comp_map_coe, Equiv.apply_symm_apply, Category.comp_id, h₂])

/-- For a quasicategory `C` and an edge `g : Δ[1] ⟶ C` with source `p : Δ[0] ⟶ C`, **the
restriction of cones `C_{/g} ⟶ C_{/p}` to the source of `g` is a trivial fibration**: it has the
right lifting property with respect to every monomorphism. This is the case `m = 1`, `j = 0` of
`SSet.slice.hasLiftingProperty_map_horn_ι`, since the horn `Λ[1, 0]` is the vertex `0` of
`Δ[1]`. -/
theorem hasLiftingProperty_map_δ_one [Quasicategory C] (g : Δ[1] ⟶ C) {p : Δ[0] ⟶ C}
    (h : stdSimplex.δ 1 ≫ g ≫ 𝟙 C = p) {X Y : SSet.{u}} (i : X ⟶ Y) [Mono i] :
    HasLiftingProperty i (map (stdSimplex.δ 1) (𝟙 C) h) := by
  -- The inclusion `e` of `Δ[0]` as the face of `Λ[1, 0]` opposite to the vertex `1` is an
  -- isomorphism, through which restricting to the source factors as restricting to `Λ[1, 0]`.
  let e : Δ[0] ⟶ (Λ[1, 0] : SSet.{u}) := horn.ι 0 1 (by decide)
  have he : e ≫ Λ[1, 0].ι = stdSimplex.δ 1 := horn.ι_ι _ _ _
  have : IsIso e := ⟨stdSimplex.isTerminalObj₀.from _, stdSimplex.isTerminalObj₀.hom_ext _ _,
    horn.hom_ext' fun j hj ↦ by
      obtain rfl : j = 1 := Fin.eq_one_of_ne_zero j hj
      rw [← Category.assoc, stdSimplex.isTerminalObj₀.hom_ext (horn.ι 0 1 hj ≫ _) (𝟙 _),
        Category.id_comp, Category.comp_id]⟩
  have hmap : map (stdSimplex.δ 1) (𝟙 C) h = map (q := Λ[1, 0].ι ≫ g) Λ[1, 0].ι (𝟙 C) (by simp) ≫
      map e (𝟙 C) (by rw [← h, ← he]; simp) := by
    -- After `map_comp`, the two sides differ only in the restriction maps, equal by `he`.
    rw [map_comp]
    congr 1
  have := hasLiftingProperty_map_horn_ι (Fin.zero_lt_one) g i
  rw [hmap]
  infer_instance

end slice

end SSet
