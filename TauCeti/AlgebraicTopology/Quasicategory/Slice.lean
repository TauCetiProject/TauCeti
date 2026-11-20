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
# Relative slices of inner fibrations

Let `p : X ⟶ S` be an inner fibration, `i : L ⟶ K` a monomorphism and `σ : K ⟶ X` a diagram. The
relative slice map `SSet.slice.restrictionMap i p σ`,
`X_{/σ} ⟶ X_{/i ≫ σ} ×_{S_{/i ≫ σ ≫ p}} S_{/σ ≫ p}`,
which restricts a cone over `σ` along `i` and pushes it forward along `p`, is a right fibration
(HTT Proposition 2.1.2.1). Dually, the relative coslice map `SSet.coslice.restrictionMap i p σ` is
a left fibration. Taking `S` a point, the restriction of cones `C_{/p} ⟶ C_{/j ≫ p}` along a
monomorphism `j` is a right fibration for a quasicategory `C`; taking moreover `L` empty, so is the
projection `C_{/p} ⟶ C`, and the slice `C_{/p}` is a quasicategory (Joyal). The same holds dually
for coslices.

The proof is by the join horn filtration. Through the universal properties of slices and coslices,
a lifting problem of a map `j : A ⟶ B` against the relative slice map for `i`, and a lifting
problem of `i` against the relative coslice map for `j`, are both extension problems along the
pushout-join of `j` and `i` for maps `B ⋆ K ⟶ X` over `S`
(`SSet.slice.forall_hasLiftingProperty_restrictionMap_iff_of_isPushout` and its coslice
counterpart, in `TauCeti.AlgebraicTopology.SimplicialSet.Coslice`). For a horn `Λ[m, k] ⟶ Δ[m]` with
`0 < k`, the relative coslice map for it is a trivial fibration: by Mathlib's description of the
trivial fibrations as the maps lifting against boundary inclusions (`SSet.rlp_monomorphisms`), it
suffices to lift `∂Δ[n] ⟶ Δ[n]`, and the pushout-join `(Λ[m, k] ⋆ Δ[n]) ∪ (Δ[m] ⋆ ∂Δ[n])` is the
inner horn `Λ[m + n + 1, k]`, which lifts against the inner fibration `p`. Dually, for `k < m` the
relative slice map for `Λ[m, k] ⟶ Δ[m]` is a trivial fibration, by the inner horns
`(∂Δ[n] ⋆ Δ[m]) ∪ (Δ[n] ⋆ Λ[m, k])`.

## Main results

* `SSet.coslice.hasLiftingProperty_restrictionMap_horn_ι`,
  `SSet.slice.hasLiftingProperty_restrictionMap_horn_ι`: for an inner fibration `p`, the relative
  coslice map for `Λ[m, k] ⟶ Δ[m]` with `0 < k`, and the relative slice map for it with `k < m`,
  are trivial fibrations.
* `SSet.slice.rightFibration_restrictionMap`: **the relative slice map of an inner fibration along
  a monomorphism is a right fibration** (HTT Proposition 2.1.2.1);
  `SSet.coslice.leftFibration_restrictionMap`: dually, the relative coslice map is a left
  fibration.
* `SSet.slice.rightFibration_map`, `SSet.slice.rightFibration_π`, `SSet.slice.quasicategory`: for a
  quasicategory `C` and a monomorphism `j : L ⟶ K`, the restriction of cones `C_{/p} ⟶ C_{/j ≫ p}`
  and the projection `C_{/p} ⟶ C` are right fibrations, and `C_{/p}` is a quasicategory;
  `SSet.coslice.leftFibration_map`, `SSet.coslice.leftFibration_π`, `SSet.coslice.quasicategory`
  are the duals for coslices.
* `SSet.slice.hasLift_of_isEquivalence`: the restriction of cones along a monomorphism lifts, with
  prescribed source, every edge whose image in `C` is an equivalence.

## Implementation notes

The reduction to boundary inclusions and inner anodyne pushout-joins follows the shape of the
proof of Mathlib's `SSet.innerFibration_pullbackObjObjπ` by Jack McKoen and Joël Riou, with slices
and coslices playing the role of the internal hom.

## References

* J. Lurie, *Higher Topos Theory*, Lemma 2.1.2.3, Proposition 2.1.2.1 and Corollary 2.1.2.2.
* A. Joyal, *Quasi-categories and Kan complexes*, J. Pure Appl. Algebra 175 (2002).
-/

public section

open CategoryTheory Limits MorphismProperty Simplicial

universe u

namespace SSet

variable {A B K L X S : SSet.{u}} {m : ℕ} {k : Fin (m + 1)}

/-! ### Relative slices and coslices of inner fibrations -/

namespace coslice

/-- For an inner fibration `p : X ⟶ S`, a simplex `τ : Δ[m] ⟶ X` and `0 < k`, **the relative
coslice map `X_{τ/} ⟶ X_{(Λ[m, k] ⟶ Δ[m] ⟶ X)/} ×_{S_{(Λ[m, k] ⟶ Δ[m] ⟶ S)/}} S_{τ ≫ p/}` is a
trivial fibration**: it has the right lifting property with respect to every monomorphism
`j : A ⟶ B`. Through the universal property of the coslice, this says that a map
`(Λ[m, k] ⋆ B) ∪ (Δ[m] ⋆ A) ⟶ X` extending `τ` extends to `Δ[m] ⋆ B` over every map
`Δ[m] ⋆ B ⟶ S` whose restriction to `(Λ[m, k] ⋆ B) ∪ (Δ[m] ⋆ A)` is its composite with `p`. -/
theorem hasLiftingProperty_restrictionMap_horn_ι (p : X ⟶ S) [InnerFibration p] (hk : 0 < k)
    (τ : Δ[m] ⟶ X) (j : A ⟶ B) [Mono j] :
    HasLiftingProperty j (restrictionMap Λ[m, k].ι p τ) := by
  suffices (monomorphisms SSet.{u}).rlp (restrictionMap Λ[m, k].ι p τ) from
    this j (monomorphisms.infer_property j)
  rw [rlp_monomorphisms]
  rintro _ _ _ ⟨n⟩
  have := join.innerAnodyneExtensions_unionJoin_horn_boundary n hk p (mem_innerFibrations p)
  exact (forall_hasLiftingProperty_restrictionMap_iff_of_isPushout Λ[m, k].ι ∂Δ[n].ι p
    (Subcomplex.unionJoin.isPushout _ _) (Subcomplex.unionJoin.ι₁_ι _ _)
    (Subcomplex.unionJoin.ι₂_ι _ _)).2 inferInstance τ

end coslice

namespace slice

/-- For an inner fibration `p : X ⟶ S`, a simplex `σ : Δ[m] ⟶ X` and `k < m`, **the relative
slice map `X_{/σ} ⟶ X_{/(Λ[m, k] ⟶ Δ[m] ⟶ X)} ×_{S_{/(Λ[m, k] ⟶ Δ[m] ⟶ S)}} S_{/σ ≫ p}` is a
trivial fibration**: it has the right lifting property with respect to every monomorphism
`j : A ⟶ B`. Through the universal property of the slice, this says that a map
`(A ⋆ Δ[m]) ∪ (B ⋆ Λ[m, k]) ⟶ X` extending `σ` extends to `B ⋆ Δ[m]` over every map
`B ⋆ Δ[m] ⟶ S` whose restriction to `(A ⋆ Δ[m]) ∪ (B ⋆ Λ[m, k])` is its composite with `p`. -/
theorem hasLiftingProperty_restrictionMap_horn_ι (p : X ⟶ S) [InnerFibration p]
    (hk : k < Fin.last m) (σ : Δ[m] ⟶ X) (j : A ⟶ B) [Mono j] :
    HasLiftingProperty j (restrictionMap Λ[m, k].ι p σ) := by
  suffices (monomorphisms SSet.{u}).rlp (restrictionMap Λ[m, k].ι p σ) from
    this j (monomorphisms.infer_property j)
  rw [rlp_monomorphisms]
  rintro _ _ _ ⟨n⟩
  have := join.innerAnodyneExtensions_unionJoin_boundary_horn n hk p (mem_innerFibrations p)
  exact (forall_hasLiftingProperty_restrictionMap_iff_of_isPushout ∂Δ[n].ι Λ[m, k].ι p
    (Subcomplex.unionJoin.isPushout _ _) (Subcomplex.unionJoin.ι₁_ι _ _)
    (Subcomplex.unionJoin.ι₂_ι _ _)).2 inferInstance σ

/-- **The relative slice map of an inner fibration is a right fibration** (HTT
Proposition 2.1.2.1): for an inner fibration `p : X ⟶ S`, a monomorphism `i : L ⟶ K` and a
diagram `σ : K ⟶ X`, the map `X_{/σ} ⟶ X_{/i ≫ σ} ×_{S_{/i ≫ σ ≫ p}} S_{/σ ≫ p}` is a right
fibration. -/
instance rightFibration_restrictionMap (p : X ⟶ S) [InnerFibration p] (i : L ⟶ K) [Mono i]
    (σ : K ⟶ X) : RightFibration (restrictionMap i p σ) :=
  (rightFibration_iff_hasLiftingProperty _).2 fun _ _ hk ↦
    (forall_hasLiftingProperty_restrictionMap_iff _ i p).2
      (fun τ ↦ coslice.hasLiftingProperty_restrictionMap_horn_ι p hk τ i) σ

end slice

namespace coslice

/-- **The relative coslice map of an inner fibration is a left fibration**, dually to HTT
Proposition 2.1.2.1: for an inner fibration `p : X ⟶ S`, a monomorphism `i : L ⟶ K` and a
diagram `τ : K ⟶ X`, the map `X_{τ/} ⟶ X_{i ≫ τ/} ×_{S_{i ≫ τ ≫ p/}} S_{τ ≫ p/}` is a left
fibration. -/
instance leftFibration_restrictionMap (p : X ⟶ S) [InnerFibration p] (i : L ⟶ K) [Mono i]
    (τ : K ⟶ X) : LeftFibration (restrictionMap i p τ) :=
  (leftFibration_iff_hasLiftingProperty _).2 fun _ _ hk ↦
    (slice.forall_hasLiftingProperty_restrictionMap_iff i _ p).1
      (fun σ ↦ slice.hasLiftingProperty_restrictionMap_horn_ι p hk σ i) τ

end coslice

/-! ### Slices and coslices of quasicategories -/

variable {C : SSet.{u}}

/-- The empty subcomplex has no vertex. -/
private lemma not_nonempty_bot : ¬ ((⊥ : K.Subcomplex) : SSet.{u}).Nonempty :=
  fun ⟨⟨_, hx⟩⟩ ↦ by simp only [Subfunctor.bot_obj, Set.mem_empty_iff_false] at hx

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
  have := isIso_π ((⊥ : K.Subcomplex).ι ≫ p) not_nonempty_bot
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
  have := isIso_π ((⊥ : K.Subcomplex).ι ≫ p) not_nonempty_bot
  rw [← Category.comp_id (π p),
    ← map_π (q := (⊥ : K.Subcomplex).ι ≫ p) (⊥ : K.Subcomplex).ι (𝟙 C) (by simp)]
  infer_instance

/-- **The coslice of a quasicategory is a quasicategory** (Joyal). -/
instance quasicategory [Quasicategory C] (p : K ⟶ C) : Quasicategory (coslice p) :=
  quasicategory_of_innerFibration (π p)

end coslice

end SSet
