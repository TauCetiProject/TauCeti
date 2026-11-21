/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.LocalCoefficient.Contractible
public import TauCeti.AlgebraicTopology.Singular.Fibration.LocalHomology
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
  exact z.2

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
`TauCeti.TopCat.isIso_singularHomologyMap_excisionMap_chartBall`. -/
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
  haveI := isIso_singularHomologyMap_excisionMap_chartBall (p := p)
    (L.obj (FundamentalGroupoid.mk b)) e hb hε₀ m
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

end TauCeti.TopCat
