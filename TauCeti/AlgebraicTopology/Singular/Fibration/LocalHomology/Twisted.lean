/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.LocalCoefficient.Contractible
public import TauCeti.AlgebraicTopology.Singular.Fibration.LocalHomology
public import TauCeti.AlgebraicTopology.Singular.Twisted.ConstantNaturality
public import TauCeti.AlgebraicTopology.Singular.Twisted.LivesOver
public import TauCeti.AlgebraicTopology.Singular.Twisted.Excision

/-!
# Local homology of a Serre fibration along a fibre, with local coefficients

Let `p : E → B` be a Serre fibration over a `T₁` space `B`, and `b` a point of `B` in the source
of an open partial homeomorphism `e : B → V` to a real normed space of finite dimension `r`, such
as a chart of a topological manifold modelled on `V`. Let `L` be a local coefficient system on the
base. This file computes the local homology `Hₖ(E, E ∖ F; p*L)` of `E` along the fibre
`F = p⁻¹(b)`, with coefficients in the pulled-back system `p*L`:

* it is the local homology with constant coefficients in the fibre `L_b` of `L` over `b`,
  `Hₖ(E, E ∖ F; p*L) ≅ Hₖ(E, E ∖ F; L_b)`
  (`TauCeti.TopCat.twistedHomologyComplFiberConstantIso`);
* hence `Hₙ₊ᵣ(E, E ∖ F; p*L) ≅ Hₙ(F; L_b)` (`TauCeti.TopCat.twistedHomologyComplFiberIso`), and
  `Hₘ(E, E ∖ F; p*L) = 0` for `m < r` (`TauCeti.TopCat.isZero_twistedHomology_complFiber`).

Composing with the map of pairs `(E, ∅) → (E, E ∖ F)` gives a map
`Hₙ₊ᵣ(E; p*L) → Hₙ(F; L_b)`; this file does not define the composite. For `L` the orientation
local system `or_B` of a manifold base, it is the twisted form of the shriek map of the inclusion
of the point `b`. This form is needed when `B` is not orientable, since `B` then has a fundamental
class only in `H_r(B; or_B)`.

## The computation

Choose a ball of positive radius `ε` about `e b` inside the target of `e`, and let `U` be its
preimage in the source of `e` (`OpenPartialHomeomorph.chartBall`). Excision with local coefficients
(`TopPair.isIso_twistedHomologyMap_excisionMap_of_isClosed_subset`) identifies `Hₖ(E, E ∖ F; p*L)`
with the local homology of the open set `p⁻¹(U)` along `F`, with coefficients in the restriction of
`p*L`. That restriction is the pullback of `L` along the restriction of `p` to `p⁻¹(U)`, a map into
`U`, and straight lines to `e b` in the chart contract every map into `U` onto the constant map at
`b` (`OpenPartialHomeomorph.chartBallHomotopy`). So the restricted system is constant, with fibre
`L_b` (`TauCeti.TopCat.chartBallPullbackIsoConstant`, an instance of
`TauCeti.LocalCoefficientSystem.pullbackIsoConstantOfHomotopy`): at a point `z` the
identification is transport by `L` along the path from `p z` to `b` traced by that homotopy.
Twisted homology with constant coefficients is ordinary homology
(`TopPair.twistedHomologyConstantIso`), and excision for ordinary homology returns to
`Hₖ(E, E ∖ F; L_b)`. The untwisted local homology along the fibre is
then `TauCeti.TopCat.singularHomologyComplFiberIso`.

## Main definitions

* `TauCeti.TopCat.chartBallPullbackIsoConstant`: over the part of `E` above a chart ball about
  `b`, the pullback of `L` is the constant system with fibre `L_b`.
* `TauCeti.TopCat.twistedHomologyComplFiberConstantIso`:
  `Hₖ(E, E ∖ p⁻¹(b); p*L) ≅ Hₖ(E, E ∖ p⁻¹(b); L_b)`.
* `TauCeti.TopCat.twistedHomologyComplFiberIso`: `Hₙ₊ᵣ(E, E ∖ p⁻¹(b); p*L) ≅ Hₙ(p⁻¹(b); L_b)`.

## Main results

* `TauCeti.TopCat.isZero_twistedHomology_complFiber`: `Hₘ(E, E ∖ p⁻¹(b); p*L) = 0` for `m < r`.
* `TauCeti.TopCat.twistedHomologyMap_excisionMap_comp_twistedHomologyComplFiberConstantIso_hom`:
  the defining square of the comparison after excision.
* `TauCeti.TopCat.twistedHomologyπ_comp_twistedHomologyComplFiberIso_hom_ne_zero_iff`: a class of
  `Hₙ₊ᵣ(E; p*L)` is detected by the twisted shriek map exactly when its localization along the
  fibre is nonzero, independently of the chart.
* `TauCeti.TopCat.twistedHomologyComplFiberIso_hom_constant`: for a constant system the
  isomorphism is the untwisted `TauCeti.TopCat.singularHomologyComplFiberIso`.
* `LocalCoefficientSystem.livesOverFundamentalClass_iff_twistedHomologyComplFiberIso_hom_ne_zero`:
  a class of `Hₙ₊ᵣ(E; p*L)` lives over the fundamental class at `b`
  (`TauCeti.LocalCoefficientSystem.LivesOverFundamentalClass`) exactly when its image under the
  twisted shriek map is nonzero.
* `TauCeti.LocalCoefficientSystem.LivesOverFundamentalClass.finrank_le`: such a class has degree at
  least the dimension of the base.

## References

* A. Hatcher, *Algebraic Topology*, Cambridge University Press, 2002, Section 3.H (homology with
  local coefficients, and the orientation local system of a manifold).
* J.-F. Barraud, M. Damian, V. Humilière, A. Oancea, *Floer homology with DG coefficients.
  Applications to cotangent bundles*, arXiv:2404.07953, §2.4, Proposition 2.6 and Lemma 2.9.
-/

public section

noncomputable section

open CategoryTheory Metric Module Set TauCeti.LocalCoefficientSystem

universe u

namespace TauCeti.TopCat

variable {V : Type u} [NormedAddCommGroup V] [NormedSpace ℝ V] {E B : _root_.TopCat.{u}}
  {p : E ⟶ B} {R : Type*} [Ring R] (L : LocalCoefficientSystem.{_, u, u} R B)
  (e : OpenPartialHomeomorph B V) {b : B} (hb : b ∈ e.source) {ε : ℝ}
  (hε : ball (e b) ε ⊆ e.target)

omit [NormedSpace ℝ V] in
/-- The part of `E` over the chart ball `OpenPartialHomeomorph.chartBall e b ε` is sent by `p` into
that chart ball. -/
lemma comp_excisionMap_fst_mem_chartBall
    (z : (TopPair.interPair (X := E) (p ⁻¹' e.chartBall b ε) (p ⁻¹' {b})ᶜ).fst) :
    p.hom.comp (TopPair.Hom.fst
      (TopPair.excisionMap (X := E) (p ⁻¹' e.chartBall b ε) (p ⁻¹' {b})ᶜ)).hom z ∈
        e.chartBall b ε := by
  -- The codomain of the excision inclusion is only definitionally `E`, so the composite is
  -- evaluated by `change` before rewriting with the evaluation lemma of the inclusion.
  change p (TopPair.Hom.fst
    (TopPair.excisionMap (X := E) (p ⁻¹' e.chartBall b ε) (p ⁻¹' {b})ᶜ) z) ∈ _
  rw [TopPair.excisionMap_fst_apply]
  exact z.property

/-- **The pullback of a local coefficient system over a chart ball is constant.** Over the part
`p⁻¹(U)` of `E` above the chart ball `U = OpenPartialHomeomorph.chartBall e b ε`, the restriction
of the pulled-back system `p*L` is the constant system with fibre `L_b`. At a point `z` the
comparison is transport by `L` along the path from `p z` to `b` traced by the straight-line
contraction `OpenPartialHomeomorph.chartBallHomotopy` of the chart ball. -/
def chartBallPullbackIsoConstant :
    (pullback (TopPair.Hom.fst
        (TopPair.excisionMap (X := E) (p ⁻¹' e.chartBall b ε) (p ⁻¹' {b})ᶜ)).hom).obj
        ((pullback p.hom).obj L) ≅
      (constantFunctor (R := R)
        (TopPair.interPair (X := E) (p ⁻¹' e.chartBall b ε) (p ⁻¹' {b})ᶜ).fst).obj
        (L.obj (FundamentalGroupoid.mk b)) :=
  ((pullbackCompIso _ p.hom).app L).symm ≪≫
    pullbackIsoConstantOfHomotopy (e.chartBallHomotopy hb hε
      (g := p.hom.comp (TopPair.Hom.fst
        (TopPair.excisionMap (X := E) (p ⁻¹' e.chartBall b ε) (p ⁻¹' {b})ᶜ)).hom)
      (comp_excisionMap_fst_mem_chartBall e)) L

/-- At a point `z` over the chart ball, `TauCeti.TopCat.chartBallPullbackIsoConstant` is transport
by `L` along the path from `p z` to `b` traced by the straight-line contraction of the chart
ball. -/
@[simp]
lemma chartBallPullbackIsoConstant_hom_app
    (z : FundamentalGroupoid
      (TopPair.interPair (X := E) (p ⁻¹' e.chartBall b ε) (p ⁻¹' {b})ᶜ).fst) :
    (chartBallPullbackIsoConstant L e hb hε).hom.app z =
      L.map ⟦(e.chartBallHomotopy hb hε
        (g := p.hom.comp (TopPair.Hom.fst
          (TopPair.excisionMap (X := E) (p ⁻¹' e.chartBall b ε) (p ⁻¹' {b})ᶜ)).hom)
        (comp_excisionMap_fst_mem_chartBall e)).evalAt z.as⟧ := by
  -- The component of `pullbackCompIso` is an identity between objects which are only
  -- definitionally equal, so the composite is split by `rfl` rather than by rewriting
  -- `Iso.trans_hom`, and the unit law is applied by `exact`.
  calc _ = ((pullbackCompIso _ p.hom).inv.app L).app z ≫
        (pullbackIsoConstantOfHomotopy (e.chartBallHomotopy hb hε
          (comp_excisionMap_fst_mem_chartBall e)) L).hom.app z := rfl
    _ = _ := by
      refine (congrArg (· ≫ _) (pullbackCompIso_inv_app_app _ _ L z)).trans ?_
      exact (Category.id_comp _).trans (pullbackIsoConstantOfHomotopy_hom_app _ L z)

variable [T1Space B]

omit [NormedSpace ℝ V] in
include hb in
/-- Excision with local coefficients onto the part of `E` over `e.chartBall b ε` is an
isomorphism on homology, for every local coefficient system `K` on `E`: the twisted analogue of
`TauCeti.TopCat.isIso_singularHomologyMap_excisionMap_preimage` for the chart ball. -/
lemma isIso_twistedHomologyMap_excisionMap_chartBall (hε₀ : 0 < ε)
    (K : LocalCoefficientSystem.{_, u, u} R E) (m : ℕ) :
    IsIso (TopPair.twistedHomologyMap
      (TopPair.excisionMap (X := E) (p ⁻¹' e.chartBall b ε) (p ⁻¹' {b})ᶜ) K m) :=
  TopPair.isIso_twistedHomologyMap_excisionMap_of_isClosed_subset K
    ((e.isOpen_chartBall b ε).preimage p.hom.continuous)
    (isClosed_singleton.preimage p.hom.continuous)
    (preimage_mono (singleton_subset_iff.2 (e.mem_chartBall_self hb hε₀))) m

/-- **Local homology along a fibre with pulled-back coefficients is local homology with constant
coefficients.** Let `p : E ⟶ B` be a continuous map to a `T₁` space, `L` a local coefficient
system on `B`, and `b` a point in the source of an open partial homeomorphism `e : B → V` to a
real normed space. Then `Hₘ(E, E ∖ p⁻¹(b); p*L) ≅ Hₘ(E, E ∖ p⁻¹(b); L_b)`, where `L_b` is the
fibre of `L` over `b`.

The isomorphism is constructed from a ball about `e b` inside the target of `e`: it is excision
onto the part of `E` over `OpenPartialHomeomorph.chartBall e b ε`, followed by the identification
`TauCeti.TopCat.chartBallPullbackIsoConstant` of the coefficients there with the constant system
at `L_b`, the comparison of twisted homology with constant coefficients with ordinary homology, and
excision back to `E`
(`TauCeti.TopCat.twistedHomologyMap_excisionMap_comp_twistedHomologyComplFiberConstantIso_hom`).
No fibration hypothesis is needed. -/
def twistedHomologyComplFiberConstantIso (hε₀ : 0 < ε) (m : ℕ) :
    -- The universe of the coefficient modules is given explicitly: elaborating the twisted side
    -- first leaves it as `max u ?w`, for which instance search on `ModuleCat` does not terminate.
    (TopPair.ofSubset (p ⁻¹' {b})ᶜ).twistedHomology.{_, _, u} ((pullback p.hom).obj L) m ≅
      (TopPair.ofSubset (p ⁻¹' {b})ᶜ).singularHomology (L.obj (FundamentalGroupoid.mk b)) m :=
  haveI := isIso_twistedHomologyMap_excisionMap_chartBall (p := p) e hb hε₀
    ((pullback p.hom).obj L) m
  haveI := isIso_singularHomologyMap_excisionMap_preimage (p := p)
    (L.obj (FundamentalGroupoid.mk b)) (e.isOpen_chartBall b ε) isClosed_singleton
    (singleton_subset_iff.2 (e.mem_chartBall_self hb hε₀)) m
  (asIso (TopPair.twistedHomologyMap
      (TopPair.excisionMap (X := E) (p ⁻¹' e.chartBall b ε) (p ⁻¹' {b})ᶜ)
      ((pullback p.hom).obj L) m)).symm ≪≫
    asIso (TopPair.twistedHomologyCoefficientMap
      (TopPair.interPair (X := E) (p ⁻¹' e.chartBall b ε) (p ⁻¹' {b})ᶜ)
      (chartBallPullbackIsoConstant L e hb hε).hom m) ≪≫
    (TopPair.interPair (X := E) (p ⁻¹' e.chartBall b ε) (p ⁻¹' {b})ᶜ).twistedHomologyConstantIso
      _ m ≪≫
    asIso (TopPair.singularHomologyMap
      (TopPair.excisionMap (X := E) (p ⁻¹' e.chartBall b ε) (p ⁻¹' {b})ᶜ) _ m)

/-- The defining square of `TauCeti.TopCat.twistedHomologyComplFiberConstantIso`: after excision
onto the part of `E` over `OpenPartialHomeomorph.chartBall e b ε`, it is the change of
coefficients along `TauCeti.TopCat.chartBallPullbackIsoConstant`, followed by the comparison of
twisted homology with constant coefficients with ordinary homology and by excision for ordinary
homology. -/
@[reassoc]
lemma twistedHomologyMap_excisionMap_comp_twistedHomologyComplFiberConstantIso_hom
    (hε₀ : 0 < ε) (m : ℕ) :
    TopPair.twistedHomologyMap
        (TopPair.excisionMap (X := E) (p ⁻¹' e.chartBall b ε) (p ⁻¹' {b})ᶜ)
        ((pullback p.hom).obj L) m ≫
        (twistedHomologyComplFiberConstantIso L e hb hε hε₀ m).hom =
      TopPair.twistedHomologyCoefficientMap
          (TopPair.interPair (X := E) (p ⁻¹' e.chartBall b ε) (p ⁻¹' {b})ᶜ)
          (chartBallPullbackIsoConstant L e hb hε).hom m ≫
        ((TopPair.interPair (X := E) (p ⁻¹' e.chartBall b ε)
          (p ⁻¹' {b})ᶜ).twistedHomologyConstantIso _ m).hom ≫
        TopPair.singularHomologyMap
          (TopPair.excisionMap (X := E) (p ⁻¹' e.chartBall b ε) (p ⁻¹' {b})ᶜ)
          (L.obj (FundamentalGroupoid.mk b)) m := by
  simp [twistedHomologyComplFiberConstantIso]

/-- For a constant system `M` on `B`, the comparison
`TauCeti.TopCat.twistedHomologyComplFiberConstantIso` is the change of coefficients along
`p*M ≅ M` followed by the comparison of twisted homology with constant coefficients with ordinary
homology. -/
lemma twistedHomologyComplFiberConstantIso_hom_constant (M : ModuleCat.{u} R) (hε₀ : 0 < ε)
    (m : ℕ) :
    (twistedHomologyComplFiberConstantIso ((constantFunctor B).obj M) e hb hε hε₀ m).hom =
      (TopPair.ofSubset (p ⁻¹' {b})ᶜ).twistedHomologyCoefficientMap
          (pullbackConstantIso p.hom M).hom m ≫
        ((TopPair.ofSubset (p ⁻¹' {b})ᶜ).twistedHomologyConstantIso M m).hom := by
  have := isIso_twistedHomologyMap_excisionMap_chartBall (p := p) e hb hε₀
    ((pullback p.hom).obj ((constantFunctor B).obj M)) m
  refine (cancel_epi (TopPair.twistedHomologyMap
      (TopPair.excisionMap (X := E) (p ⁻¹' e.chartBall b ε) (p ⁻¹' {b})ᶜ)
      ((pullback p.hom).obj ((constantFunctor B).obj M)) m)).1 ?_
  -- The ambient space of `(E, E ∖ p⁻¹(b))` is `E` only up to unfolding `TopPair.ofSubset`, so the
  -- naturality squares along the excision inclusion are applied with `erw`.
  rw [twistedHomologyMap_excisionMap_comp_twistedHomologyComplFiberConstantIso_hom]
  erw [TopPair.twistedHomologyMap_naturality_assoc]
  erw [TopPair.twistedHomologyConstantIso_hom_pair_naturality M
    (TopPair.excisionMap (X := E) (p ⁻¹' e.chartBall b ε) (p ⁻¹' {b})ᶜ) m]
  erw [← TopPair.twistedHomologyCoefficientMap_comp_assoc]
  congr 2
  -- Both coefficient maps are the identity of `M` at every point: transport in a constant system
  -- is trivial, and pulling back a constant system is the identity.
  refine NatTrans.ext (funext fun z ↦ ?_)
  rw [chartBallPullbackIsoConstant_hom_app]
  erw [NatTrans.comp_app, pullback_map_app, pullbackConstantIso_hom_app,
    pullbackConstantIso_hom_app]
  exact (constantFunctor_obj_map B M _).trans (Category.comp_id _).symm

variable [FiniteDimensional ℝ V]

/-- **The homology of a Serre fibration with pulled-back coefficients, modulo the complement of a
fibre, is the shifted homology of the fibre.** Let `p : E ⟶ B` be a Serre fibration over a `T₁`
space, `L` a local coefficient system on `B`, and `b` a point in the source of an open partial
homeomorphism `e : B → V` to a real normed space of finite dimension `r`, such as the chart
`chartAt V b` of a topological manifold modelled on `V`. Then
`Hₘ(E, E ∖ p⁻¹(b); p*L) ≅ Hₙ(p⁻¹(b); L_b)` for `m = n + r`, where `L_b` is the fibre of `L` over
`b`.

It is `TauCeti.TopCat.twistedHomologyComplFiberConstantIso` followed by
`TauCeti.TopCat.singularHomologyComplFiberIso` with coefficients in `L_b`, both built from the same
ball about `e b`. -/
def twistedHomologyComplFiberIso (hε₀ : 0 < ε) (hp : serreFibrations p) (n m : ℕ)
    (h : n + finrank ℝ V = m) :
    -- The universe of the coefficient modules is explicit, as for
    -- `TauCeti.TopCat.twistedHomologyComplFiberConstantIso`.
    (TopPair.ofSubset (p ⁻¹' {b})ᶜ).twistedHomology.{_, _, u} ((pullback p.hom).obj L) m ≅
      ((AlgebraicTopology.singularHomologyFunctor (ModuleCat.{u} R) n).obj
        (L.obj (FundamentalGroupoid.mk b))).obj (_root_.TopCat.of (p ⁻¹' {b})) :=
  twistedHomologyComplFiberConstantIso L e hb hε hε₀ m ≪≫
    singularHomologyComplFiberIso _ e hb hε hε₀ hp n m h

/-- `TauCeti.TopCat.twistedHomologyComplFiberIso` is the comparison with constant coefficients
`TauCeti.TopCat.twistedHomologyComplFiberConstantIso`, followed by the untwisted
`TauCeti.TopCat.singularHomologyComplFiberIso`. -/
lemma twistedHomologyComplFiberIso_hom (hε₀ : 0 < ε) (hp : serreFibrations p) (n m : ℕ)
    (h : n + finrank ℝ V = m) :
    (twistedHomologyComplFiberIso L e hb hε hε₀ hp n m h).hom =
      (twistedHomologyComplFiberConstantIso L e hb hε hε₀ m).hom ≫
        (singularHomologyComplFiberIso _ e hb hε hε₀ hp n m h).hom :=
  (rfl)

include hb in
/-- **The homology of a Serre fibration with pulled-back coefficients, modulo the complement of a
fibre, vanishes below the dimension.** Let `p : E ⟶ B` be a Serre fibration over a `T₁` space, `L`
a local coefficient system on `B`, and `b` a point in the source of an open partial homeomorphism
`e : B → V` to a finite-dimensional real normed space. Then `Hₘ(E, E ∖ p⁻¹(b); p*L) = 0` for every
`m < dim V`. -/
theorem isZero_twistedHomology_complFiber (hp : serreFibrations p) {m : ℕ}
    (hm : m < finrank ℝ V) :
    Limits.IsZero
      ((TopPair.ofSubset (p ⁻¹' {b})ᶜ).twistedHomology.{_, _, u} ((pullback p.hom).obj L) m) := by
  obtain ⟨ε, hε₀, hε⟩ := Metric.isOpen_iff.1 e.open_target (e b) (e.map_source hb)
  exact (isZero_singularHomology_complFiber _ e hb hp hm).of_iso
    (twistedHomologyComplFiberConstantIso L e hb hε hε₀ m)

/-- A class `α ∈ Hₘ(E; p*L)` is detected by the shriek map
`Hₘ(E; p*L) → Hₘ(E, E ∖ p⁻¹(b); p*L) ≅ Hₙ(p⁻¹(b); L_b)` of the inclusion of `b`, for
`m = n + dim V`, exactly when its localization along the fibre is nonzero. In particular whether
it is detected does not depend on the chart. -/
theorem twistedHomologyπ_comp_twistedHomologyComplFiberIso_hom_ne_zero_iff (hε₀ : 0 < ε)
    (hp : serreFibrations p) (n m : ℕ) (h : n + finrank ℝ V = m)
    (α : ((pullback p.hom).obj L).twistedHomology m) :
    ((TopPair.ofSubset (p ⁻¹' {b})ᶜ).twistedHomologyπ _ m ≫
        (twistedHomologyComplFiberIso L e hb hε hε₀ hp n m h).hom).hom α ≠ 0 ↔
      ((TopPair.ofSubset (p ⁻¹' {b})ᶜ).twistedHomologyπ _ m).hom α ≠ 0 :=
  not_congr (twistedHomologyComplFiberIso L e hb hε hε₀ hp n m h).toLinearEquiv.map_eq_zero_iff

/-- For a constant system `M` on `B`, the isomorphism
`TauCeti.TopCat.twistedHomologyComplFiberIso` is the comparison of twisted homology with constant
coefficients and ordinary homology, followed by the untwisted
`TauCeti.TopCat.singularHomologyComplFiberIso`. -/
lemma twistedHomologyComplFiberIso_hom_constant (M : ModuleCat.{u} R) (hε₀ : 0 < ε)
    (hp : serreFibrations p) (n m : ℕ) (h : n + finrank ℝ V = m) :
    (twistedHomologyComplFiberIso ((constantFunctor B).obj M) e hb hε hε₀ hp n m h).hom =
      (TopPair.ofSubset (p ⁻¹' {b})ᶜ).twistedHomologyCoefficientMap
          (pullbackConstantIso p.hom M).hom m ≫
        ((TopPair.ofSubset (p ⁻¹' {b})ᶜ).twistedHomologyConstantIso M m).hom ≫
          (singularHomologyComplFiberIso M e hb hε hε₀ hp n m h).hom :=
  -- The coefficient fibre `((constantFunctor B).obj M).obj b` is `M` only by definition, so the
  -- two factors are composed in term mode rather than by rewriting.
  (congrArg (· ≫ _) (twistedHomologyComplFiberConstantIso_hom_constant e hb hε M hε₀ m)).trans
    (Category.assoc _ _ _)

end TauCeti.TopCat

/-! ### Classes living over the fundamental class -/

namespace TauCeti.LocalCoefficientSystem

variable {V : Type u} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  {E B : _root_.TopCat.{u}} [T1Space B] {p : E ⟶ B} {R : Type*} [Ring R]
  {L : LocalCoefficientSystem.{_, u, u} R B} (e : OpenPartialHomeomorph B V) {b : B}
  (hb : b ∈ e.source)

/-- **Living over the fundamental class through the twisted shriek map.** For a Serre fibration
`p : E ⟶ B` over a `T₁` space with a chart `e` of dimension `r` at `b`, and a local system `L` on
`B`, a class `α ∈ Hₙ₊ᵣ(E; p*L)` lives over the fundamental class at `b` exactly when its image under
the twisted shriek map `Hₙ₊ᵣ(E; p*L) → Hₙ₊ᵣ(E, E ∖ p⁻¹(b); p*L) ≅ Hₙ(p⁻¹(b); L_b)` of the inclusion
of `b` is nonzero, for any ball about `e b` inside the target of `e`. -/
theorem livesOverFundamentalClass_iff_twistedHomologyComplFiberIso_hom_ne_zero {ε : ℝ}
    (hε : ball (e b) ε ⊆ e.target) (hε₀ : 0 < ε) (hp : TopCat.serreFibrations p) {n m : ℕ}
    (h : n + finrank ℝ V = m) (α : ((pullback p.hom).obj L).twistedHomology m) :
    ((pullback p.hom).obj L).LivesOverFundamentalClass p b α ↔
      (TopCat.twistedHomologyComplFiberIso L e hb hε hε₀ hp n m h).hom.hom
        ((((pullback p.hom).obj L).fiberLocalization p b m).hom α) ≠ 0 :=
  (livesOverFundamentalClass_iff _ _ _ α).trans
    (TopCat.twistedHomologyπ_comp_twistedHomologyComplFiberIso_hom_ne_zero_iff L e hb hε hε₀ hp n
      m h α).symm

include hb in
/-- **A class living over the fundamental class has degree at least the dimension of the base.**
For a Serre fibration `p : E ⟶ B` over a `T₁` space with a chart of dimension `r` at `b`, and a
local system `L` on `B`, the local homology `Hₖ(E, E ∖ p⁻¹(b); p*L)` vanishes for `k < r`, so no
class of `Hₖ(E; p*L)` of degree below `r` lives over the fundamental class at `b`. -/
theorem LivesOverFundamentalClass.finrank_le
    (hp : TopCat.serreFibrations p) {d : ℕ} {α : ((pullback p.hom).obj L).twistedHomology d}
    (h : ((pullback p.hom).obj L).LivesOverFundamentalClass p b α) : finrank ℝ V ≤ d := by
  by_contra hd
  have := ModuleCat.isZero_iff_subsingleton.1
    (TopCat.isZero_twistedHomology_complFiber L e hb hp (not_le.1 hd))
  exact (livesOverFundamentalClass_iff _ _ _ _).1 h (Subsingleton.elim _ _)

end TauCeti.LocalCoefficientSystem
