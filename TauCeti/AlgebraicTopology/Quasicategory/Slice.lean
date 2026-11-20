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

## References

* J. Lurie, *Higher Topos Theory*, Lemma 2.1.2.3, Proposition 2.1.2.1 and Corollary 2.1.2.2.
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
