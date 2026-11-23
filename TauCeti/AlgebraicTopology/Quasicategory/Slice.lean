/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Quasicategory.RightFibration
public import TauCeti.AlgebraicTopology.SimplicialSet.AnodyneExtensions.LeftRight.Slice

/-!
# Slices and coslices of quasicategories

For a quasicategory `C`, a diagram `p : K ⟶ C` and a monomorphism `j : L ⟶ K`, the restriction
of cones `C_{/p} ⟶ C_{/j ≫ p}` is a right fibration; taking `L` empty, so is the projection
`C_{/p} ⟶ C`, and the slice `C_{/p}` is a quasicategory (Joyal). The same holds dually for
coslices, with left fibrations. These are the special cases, for `S` a point, of the relative
results `SSet.slice.rightFibration_restrictionMap` and `SSet.coslice.leftFibration_restrictionMap`
of `TauCeti.AlgebraicTopology.SimplicialSet.AnodyneExtensions.LeftRight.Slice`: for an inner
fibration `p : X ⟶ S`, the relative slice and coslice maps along a monomorphism are right and left
fibrations (HTT Proposition 2.1.2.1). Those are proved through the pushout-join lifting criteria
`SSet.slice.forall_hasLiftingProperty_restrictionMap_iff_of_isPushout` and
`SSet.coslice.forall_hasLiftingProperty_restrictionMap_iff_of_isPushout`.

## Main results

* `SSet.slice.rightFibration_map`, `SSet.slice.rightFibration_π`, `SSet.slice.quasicategory`: for a
  quasicategory `C` and a monomorphism `j : L ⟶ K`, the restriction of cones `C_{/p} ⟶ C_{/j ≫ p}`
  and the projection `C_{/p} ⟶ C` are right fibrations, and `C_{/p}` is a quasicategory;
  `SSet.coslice.leftFibration_map`, `SSet.coslice.leftFibration_π`, `SSet.coslice.quasicategory`
  are the duals for coslices.
* `SSet.slice.hasLift_of_isEquivalence`: the restriction of cones along a monomorphism lifts, with
  prescribed source, every edge whose image in `C` is an equivalence.
* `SSet.slice.hasLiftingProperty_map_horn_ι`: for a simplex `τ : Δ[m] ⟶ C` and `j < m`, the
  restriction of cones `C_{/τ} ⟶ C_{/(Λ[m, j] ⟶ Δ[m] ⟶ C)}` is a trivial fibration, by the inner
  horns `(∂Δ[n] ⋆ Δ[m]) ∪ (Δ[n] ⋆ Λ[m, j])`; in particular
  (`SSet.slice.hasLiftingProperty_map_δ_one`) so is the restriction `C_{/g} ⟶ C_{/g(0)}` of cones
  over an edge `g` to cones over its source.

## References

* J. Lurie, *Higher Topos Theory*, Lemma 2.1.2.3, Proposition 2.1.2.1, Corollary 2.1.2.2 and
  Proposition 2.1.2.5.
* A. Joyal, *Quasi-categories and Kan complexes*, J. Pure Appl. Algebra 175 (2002).
-/

public section

open CategoryTheory Limits MorphismProperty Simplicial

universe u

namespace SSet

variable {K L : SSet.{u}}

/-! ### Slices and coslices of quasicategories -/

variable {C : SSet.{u}}

namespace slice

/-- For a quasicategory `C`, a diagram `p : K ⟶ C` and a monomorphism `j : L ⟶ K`, the
restriction of cones `C_{/p} ⟶ C_{/j ≫ p}` is a right fibration. It is the relative slice map of
`C ⟶ Δ[0]`, followed by an isomorphism. -/
instance rightFibration_map [Quasicategory C] (p : K ⟶ C) (j : L ⟶ K) [Mono j] :
    RightFibration (map j (𝟙 C) (by simp) : slice p ⟶ slice (j ≫ p)) := by
  have : IsIso (map j (𝟙 _) (by simp) :
      slice (p ≫ terminal.from C) ⟶ slice (j ≫ p ≫ terminal.from C)) :=
    isIso_of_isTerminal (isTerminal _ terminalIsTerminal) (isTerminal _ terminalIsTerminal) _
  rw [← restrictionMap_fst j (terminal.from C) p]
  infer_instance

/-- The projection of the slice of a quasicategory is a right fibration. It is the restriction of
cones to the empty diagram, followed by an isomorphism. -/
instance rightFibration_π [Quasicategory C] (p : K ⟶ C) : RightFibration (π p) := by
  have := isIso_π ((⊥ : K.Subcomplex).ι ≫ p) Subcomplex.not_nonempty_bot
  rw [← Category.comp_id (π p),
    ← map_π (q := (⊥ : K.Subcomplex).ι ≫ p) (⊥ : K.Subcomplex).ι (𝟙 C) (by simp)]
  infer_instance

/-- **The slice of a quasicategory is a quasicategory** (Joyal). -/
instance quasicategory [Quasicategory C] (p : K ⟶ C) : Quasicategory (slice p) :=
  quasicategory_of_innerFibration (π p)

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

variable {m : ℕ} {j : Fin (m + 1)}

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

namespace coslice

/-- For a quasicategory `C`, a diagram `p : K ⟶ C` and a monomorphism `j : L ⟶ K`, the
restriction of cocones `C_{p/} ⟶ C_{j ≫ p/}` is a left fibration. It is the relative coslice map
of `C ⟶ Δ[0]`, followed by an isomorphism. -/
instance leftFibration_map [Quasicategory C] (p : K ⟶ C) (j : L ⟶ K) [Mono j] :
    LeftFibration (map j (𝟙 C) (by simp) : coslice p ⟶ coslice (j ≫ p)) := by
  have : IsIso (map j (𝟙 _) (by simp) :
      coslice (p ≫ terminal.from C) ⟶ coslice (j ≫ p ≫ terminal.from C)) :=
    isIso_of_isTerminal (isTerminal _ terminalIsTerminal) (isTerminal _ terminalIsTerminal) _
  rw [← restrictionMap_fst j (terminal.from C) p]
  infer_instance

/-- The projection of the coslice of a quasicategory is a left fibration. It is the restriction of
cocones to the empty diagram, followed by an isomorphism. -/
instance leftFibration_π [Quasicategory C] (p : K ⟶ C) : LeftFibration (π p) := by
  have := isIso_π ((⊥ : K.Subcomplex).ι ≫ p) Subcomplex.not_nonempty_bot
  rw [← Category.comp_id (π p),
    ← map_π (q := (⊥ : K.Subcomplex).ι ≫ p) (⊥ : K.Subcomplex).ι (𝟙 C) (by simp)]
  infer_instance

/-- **The coslice of a quasicategory is a quasicategory** (Joyal). -/
instance quasicategory [Quasicategory C] (p : K ⟶ C) : Quasicategory (coslice p) :=
  quasicategory_of_innerFibration (π p)

end coslice

end SSet
