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

## Implementation notes

The reduction of `SSet.coslice.hasLiftingProperty_map_horn_ι` to boundary inclusions and an
inner anodyne pushout-join follows the shape of the proof of Mathlib's
`SSet.innerFibration_pullbackObjObjπ` by Jack McKoen and Joël Riou, with coslices playing the
role of the internal hom.

## References

* J. Lurie, *Higher Topos Theory*, Lemma 2.1.2.3, Proposition 2.1.2.1 and Corollary 2.1.2.2.
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
  have hw : join.map (𝟙 _) ∂Δ[n].ι ≫ (homEquiv b).1 = join.map Λ[m, i].ι (𝟙 _) ≫ (homEquiv a).1 :=
    by simpa using (congrArg (fun F ↦ (homEquiv F).1) sq.w).symm
  have hpush := Subcomplex.unionJoin.isPushout Λ[m, i] ∂Δ[n]
  have := join.innerAnodyneExtensions_unionJoin_horn_boundary n hi (terminal.from C)
    (mem_innerFibrations _)
  have sq' : CommSq (hpush.desc (homEquiv b).1 (homEquiv a).1 hw)
      (Λ[m, i].unionJoin ∂Δ[n]).ι (terminal.from C) (terminal.from _) :=
    ⟨Subsingleton.elim _ _⟩
  have h₁ : join.map Λ[m, i].ι (𝟙 _) ≫ sq'.lift = (homEquiv b).1 := by
    rw [← Subcomplex.unionJoin.ι₁_ι, Category.assoc, sq'.fac_left, IsPushout.inl_desc]
  have h₂ : join.map (𝟙 _) ∂Δ[n].ι ≫ sq'.lift = (homEquiv a).1 := by
    rw [← Subcomplex.unionJoin.ι₂_ι, Category.assoc, sq'.fac_left, IsPushout.inr_desc]
  refine ⟨⟨⟨homEquiv.symm ⟨sq'.lift, ?_⟩, ?_, ?_⟩⟩⟩
  · calc join.inl _ _ ≫ sq'.lift = join.inl _ _ ≫ join.map (𝟙 _) ∂Δ[n].ι ≫ sq'.lift := by
          rw [join.inl_map_assoc, Category.id_comp]
      _ = σ := by rw [h₂, (homEquiv a).2]
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
  have ha : join.inl _ K ≫ (homEquiv a).1 = Λ[m, i].ι ≫ b := by rw [← comp_π, sq.w]
  have sq' : CommSq (Subcomplex.isInitialBot.to (coslice b)) (⊥ : K.Subcomplex).ι
      (coslice.map Λ[m, i].ι (𝟙 C) (by simp))
      (coslice.homEquiv.symm ⟨(homEquiv a).1, ha⟩) :=
    ⟨Subcomplex.isInitialBot.hom_ext _ _⟩
  have := coslice.hasLiftingProperty_map_horn_ι hi b (⊥ : K.Subcomplex).ι
  have h : join.map Λ[m, i].ι (𝟙 K) ≫ (coslice.homEquiv sq'.lift).1 = (homEquiv a).1 := by
    have h := congrArg (fun F ↦ (coslice.homEquiv F).1) sq'.fac_right
    rwa [coslice.homEquiv_comp_map_coe, Equiv.apply_symm_apply, Category.comp_id] at h
  refine ⟨⟨⟨homEquiv.symm ⟨(coslice.homEquiv sq'.lift).1, ?_⟩, ?_, ?_⟩⟩⟩
  · calc join.inr _ _ ≫ (coslice.homEquiv sq'.lift).1 =
          join.inr _ _ ≫ join.map Λ[m, i].ι (𝟙 K) ≫ (coslice.homEquiv sq'.lift).1 := by
          rw [join.inr_map_assoc, Category.id_comp]
      _ = p := by rw [h, (homEquiv a).2]
  · exact hom_ext (by rw [homEquiv_comp_coe, Equiv.apply_symm_apply, h])
  · rw [comp_π, Equiv.apply_symm_apply]
    exact (coslice.homEquiv sq'.lift).2

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
  have ha : join.inl _ K ≫ (homEquiv a).1 = Λ[m, i].ι ≫ join.inl _ L ≫ (homEquiv b).1 := by
    rw [← comp_π, ← comp_π, ← Category.comp_id (π p), ← map_π (q := j ≫ p) j (𝟙 C) (by simp),
      reassoc_of% sq.w]
  have sq' : CommSq (coslice.homEquiv.symm ⟨(homEquiv b).1, rfl⟩) j
      (coslice.map Λ[m, i].ι (𝟙 C) (by simp)) (coslice.homEquiv.symm ⟨(homEquiv a).1, ha⟩) :=
    ⟨coslice.hom_ext (by
      have := congrArg (fun F ↦ (homEquiv F).1) sq.w
      rw [homEquiv_comp_map_coe, homEquiv_comp_coe, Category.comp_id] at this
      rw [coslice.homEquiv_comp_map_coe, coslice.homEquiv_comp_coe, Equiv.apply_symm_apply,
        Equiv.apply_symm_apply, Category.comp_id, this])⟩
  have := coslice.hasLiftingProperty_map_horn_ι hi (join.inl _ L ≫ (homEquiv b).1) j
  have h₁ : join.map Λ[m, i].ι (𝟙 K) ≫ (coslice.homEquiv sq'.lift).1 = (homEquiv a).1 := by
    have h := congrArg (fun F ↦ (coslice.homEquiv F).1) sq'.fac_right
    rwa [coslice.homEquiv_comp_map_coe, Equiv.apply_symm_apply, Category.comp_id] at h
  have h₂ : join.map (𝟙 _) j ≫ (coslice.homEquiv sq'.lift).1 = (homEquiv b).1 := by
    have h := congrArg (fun F ↦ (coslice.homEquiv F).1) sq'.fac_left
    rwa [coslice.homEquiv_comp_coe, Equiv.apply_symm_apply] at h
  refine ⟨⟨⟨homEquiv.symm ⟨(coslice.homEquiv sq'.lift).1, ?_⟩, ?_, ?_⟩⟩⟩
  · calc join.inr _ _ ≫ (coslice.homEquiv sq'.lift).1 =
          join.inr _ _ ≫ join.map Λ[m, i].ι (𝟙 K) ≫ (coslice.homEquiv sq'.lift).1 := by
          rw [join.inr_map_assoc, Category.id_comp]
      _ = p := by rw [h₁, (homEquiv a).2]
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

end slice

end SSet
