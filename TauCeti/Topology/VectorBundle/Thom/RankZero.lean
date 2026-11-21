/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Cohomology.DegreeZero
public import TauCeti.Topology.VectorBundle.Thom.Isomorphism
import TauCeti.Algebra.Module.Equiv.SpanSingleton
import TauCeti.Topology.FiberBundle.Trivialization

/-!
# The Thom isomorphism in rank zero

Let `E → B` be a real vector bundle of rank `0`, or more generally a fibre bundle with a chosen
point `0` in each fibre whose model fibre `F` is a real normed space of dimension `0`. Every fibre
`E_b` is then a point (`TauCeti.subsingleton_fiber_of_subsingleton`), so the bundle has no nonzero
vectors (`TauCeti.zeroSectionCompl_eq_empty_of_subsingleton`) and its Thom pair is `(E, ∅)`.
The projection `π : E → B` is a continuous open bijection, hence a homeomorphism
(`TauCeti.isIso_thomPairProj_of_subsingleton`).

A Thom class `u ∈ H⁰(E, ∅; K)` restricts on each fibre pair `(E_b, ∅)` to a generator of
`H⁰(E_b; K) ≅ K`, that is, to a unit. So its image in `H⁰(E; K)` has a unit value at every point,
hence is invertible for the cup product (`TauCeti.exists_singularCup_eq_one`), and the cup product
with it is bijective. The Thom map `a ↦ π^*a ⌣ u` is this cup product composed with the pull-back
along the homeomorphism `π` and the identification `Hᵖ(E, ∅) ≅ Hᵖ(E)`, so it is bijective in
every degree and for every module of coefficients
(`TauCeti.IsThomClass.bijective_thomMap_of_finrank_eq_zero`).

Such a class exists for every commutative ring of coefficients, with no orientation
(`TauCeti.exists_isThomClass_of_finrank_eq_zero`): the class of the constant cocycle `1`.

This is the rank-zero case of the Thom isomorphism `Hᵖ(B; M) ≅ Hᵖ⁺ʳ(E, E₀; M)`. It is the case of
the negative normal bundle of a Morse–Bott critical submanifold of index `0`, a family of local
minima, whose negative disc bundle is its zero section.

## Main results

* `TauCeti.IsThomClass.bijective_thomMap_of_finrank_eq_zero`: the Thom isomorphism in cohomology
  for a bundle of rank zero, with coefficients in any module.
* `TauCeti.exists_isThomClass_of_finrank_eq_zero`: a bundle of rank zero has a Thom class with
  coefficients in any commutative ring.

## References

* J. W. Milnor, J. D. Stasheff, *Characteristic Classes*, Annals of Mathematics Studies 76,
  Princeton (1974), §10, Theorem 10.4.
-/

public section

noncomputable section

open Bundle CategoryTheory MonoidalCategory Module

universe w

namespace TauCeti

section Subsingleton

variable {B : Type w} [TopologicalSpace B] (F : Type*) [TopologicalSpace F] [Subsingleton F]
  (E : B → Type w) [TopologicalSpace (TotalSpace F E)] [∀ b, Zero (E b)]
  [∀ b, TopologicalSpace (E b)] [FiberBundle F E]

/-- A bundle whose model fibre is a point has no nonzero vectors. -/
theorem zeroSectionCompl_eq_empty_of_subsingleton : zeroSectionCompl F E = ∅ :=
  Set.eq_empty_of_forall_notMem fun v hv ↦
    have := subsingleton_fiber_of_subsingleton F E v.proj
    (mem_zeroSectionCompl.1 hv) (Subsingleton.elim _ _)

/-- For a bundle whose model fibre is a point, the Thom pair `(E, E₀)` has empty subspace. -/
theorem isEmpty_thomPair_snd_of_subsingleton : IsEmpty (thomPair F E).snd :=
  Set.isEmpty_coe_sort.2 (zeroSectionCompl_eq_empty_of_subsingleton F E)

/-- The projection of a bundle whose model fibre is a point is a homeomorphism onto its base: it
is a continuous open bijection. -/
theorem isIso_thomPairProj_of_subsingleton : IsIso (thomPairProj F E) := by
  have h : ⇑(thomPairProj F E) = π F E := funext (thomPairProj_apply F E)
  exact TopCat.isIso_of_bijective_of_isOpenMap _
    (h ▸ bijective_proj_of_subsingleton F E) (h ▸ FiberBundle.isOpenMap_proj F E)

end Subsingleton

variable {B : Type w} [TopologicalSpace B] {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {E : B → Type w} [TopologicalSpace (TotalSpace F E)] [∀ b, Zero (E b)]
  [∀ b, TopologicalSpace (E b)] [FiberBundle F E]

variable {K : Type w} [CommRing K]

-- The two helpers below take their classes with coefficients the monoidal unit
-- `𝟙_ (ModuleCat K)`, the coefficients of `singularCohomologyZeroEval` and of the cup product, so
-- that their proofs rewrite with plain `rw`. Mathlib defines this unit to be `ModuleCat.of K K`,
-- the coefficients of `IsThomClass`, so a class with either coefficients is accepted for the other
-- by definitional unfolding. The theorems below rely on this only where a class or a hypothesis
-- passes between the two forms, never inside a rewrite.

omit [NormedSpace ℝ F] in
/-- In rank zero, the restriction of a class `u ∈ H⁰(E, ∅; K)` to a fibre pair `(E_b, ∅)` generates
exactly when the restriction to `E_b` of its image in `H⁰(E; K)` generates, since
`H⁰(E_b, ∅; K) ≅ H⁰(E_b; K)`. -/
private theorem span_singularCohomologyMap_fiber_eq_top_iff [Subsingleton F]
    (u : (thomPair F E).singularCohomology (𝟙_ (ModuleCat.{w} K)) K (𝟙_ (ModuleCat.{w} K)) 0)
    (b : B) :
    Submodule.span K {(TopCat.singularCohomologyMap (TopPair.Hom.fst (fiberThomPairMap F E b)) 0
        ((thomPair F E).singularCohomologyπ _ K _ 0 u))} = ⊤ ↔
      Submodule.span K {TopPair.singularCohomologyMap (fiberThomPairMap F E b) 0 u} = ⊤ := by
  set Q := TopPair.ofSubset (X := TopCat.of (E b)) ({0}ᶜ : Set (E b))
  have : IsEmpty Q.snd := isEmpty_compl_zero_fiber_of_subsingleton F E b
  rw [← ConcreteCategory.comp_apply, TopPair.singularCohomologyπ_naturality,
    ConcreteCategory.comp_apply]
  exact (asIso (Q.singularCohomologyπ _ K _ 0)).toLinearEquiv.span_singleton_apply_eq_top_iff

omit [NormedSpace ℝ F] in
/-- In rank zero, a class `u ∈ H⁰(E, ∅; K)` restricting to a generator of `H⁰(E_b, ∅; K) ≅ K` on
every fibre, as a Thom class does, has a unit value at every point of `E`. -/
private theorem isUnit_singularCohomologyZeroEval_of_subsingleton [Subsingleton F]
    {u : (thomPair F E).singularCohomology (𝟙_ (ModuleCat.{w} K)) K (𝟙_ (ModuleCat.{w} K)) 0}
    (hgen : ∀ b, Submodule.span K
      {TopPair.singularCohomologyMap (fiberThomPairMap F E b) 0 u} = ⊤) (v : TotalSpace F E) :
    IsUnit (singularCohomologyZeroEval v ((thomPair F E).singularCohomologyπ _ K _ 0 u)) := by
  obtain ⟨b, x⟩ := v
  set Q := TopPair.ofSubset (X := TopCat.of (E b)) ({0}ᶜ : Set (E b))
  obtain ⟨y, hy⟩ : ∃ y : Q.fst, TopPair.Hom.fst (fiberThomPairMap F E b) y = ⟨b, x⟩ :=
    ⟨x, fiberThomPairMap_fst_apply F E b x⟩
  -- The restriction to `E_b` of the image of `u` generates, so `c` times it is `1` for some `c`;
  -- evaluating at `y`, its value there is a unit.
  obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.1
    ((span_singularCohomologyMap_fiber_eq_top_iff u b).2 (hgen b) ▸ Submodule.mem_top :
      Q.fst.singularCohomologyZeroOne (k := K) ∈ _)
  have := congrArg (singularCohomologyZeroEval y) hc
  rw [map_smul, singularCohomologyZeroEval_singularCohomologyZeroOne,
    singularCohomologyZeroEval_naturality, hy, smul_eq_mul] at this
  exact IsUnit.of_mul_eq_one c (mul_comm c _ ▸ this)

/-- **The Thom isomorphism in rank zero.** For a bundle of rank zero and a Thom class `u`, the Thom
map `a ↦ π^*a ⌣ u` is a bijection `Hᵖ(B; M) ≅ Hᵖ(E, E₀; M)` in every degree, for every `K`-module
`M` of coefficients. -/
theorem IsThomClass.bijective_thomMap_of_finrank_eq_zero (hF : finrank ℝ F = 0)
    {u : (thomPair F E).singularCohomology (ModuleCat.of K K) K (ModuleCat.of K K) (finrank ℝ F)}
    (hu : IsThomClass F E u) (M : ModuleCat.{w} K) {p m : ℕ} (h : p + finrank ℝ F = m) :
    Function.Bijective (thomMap F E M (finrank ℝ F) p m h u) := by
  obtain ⟨_, hgen⟩ := isThomClass_iff.1 hu
  have : Subsingleton F := finrank_zero_iff.1 hF
  have := isEmpty_thomPair_snd_of_subsingleton F E
  have := isIso_thomPairProj_of_subsingleton F E
  clear hu
  -- The degree is `finrank ℝ F`, which is `0` only propositionally.
  generalize hr : finrank ℝ F = r at u hgen h
  obtain rfl : r = 0 := hr ▸ hF
  -- The pair `(E, ∅)` has empty subspace, `π` is a homeomorphism and the values of the image of `u`
  -- in `H⁰(E; K)` are units.
  rw [thomMap_def]
  exact TopPair.bijective_pullbackCup_of_isEmpty _ _ u
    (isUnit_singularCohomologyZeroEval_of_subsingleton (u := u) hgen) M h

variable (F E) in
/-- **A bundle of rank zero has a Thom class** with coefficients in any commutative ring `K`, with
no orientation: the class of `H⁰(E, ∅; K) ≅ H⁰(E; K)` of the constant cocycle `1`. -/
theorem exists_isThomClass_of_finrank_eq_zero [FiniteDimensional ℝ F] (hF : finrank ℝ F = 0)
    (K : Type w) [CommRing K] :
    ∃ u : (thomPair F E).singularCohomology (ModuleCat.of K K) K (ModuleCat.of K K)
      (finrank ℝ F), IsThomClass F E u := by
  have : Subsingleton F := finrank_zero_iff.1 hF
  have := isEmpty_thomPair_snd_of_subsingleton F E
  -- The degree is `finrank ℝ F`, which is `0` only propositionally.
  suffices ∀ r, r = 0 → ∃ u : (thomPair F E).singularCohomology (ModuleCat.of K K) K
      (ModuleCat.of K K) r, ∀ b, Submodule.span K
        {TopPair.singularCohomologyMap (fiberThomPairMap F E b) r u} = ⊤ by
    obtain ⟨u, hu⟩ := this _ hF
    exact ⟨u, isThomClass_iff.2 ⟨inferInstance, hu⟩⟩
  rintro r rfl
  refine ⟨inv ((thomPair F E).singularCohomologyπ (𝟙_ (ModuleCat.{w} K)) K
      (𝟙_ (ModuleCat.{w} K)) 0) (thomPair F E).fst.singularCohomologyZeroOne,
    fun b ↦ (span_singularCohomologyMap_fiber_eq_top_iff _ b).1 ?_⟩
  -- On the fibre, the class restricts to the unit `1 ∈ H⁰(E_b; K)`, which generates since `E_b` is
  -- a point.
  rw [IsIso.inv_hom_id_apply, singularCohomologyMap_singularCohomologyZeroOne]
  have := subsingleton_fiber_of_subsingleton F E b
  have : PathConnectedSpace (TopCat.of (E b)) :=
    ⟨⟨(0 : E b)⟩, fun x y ↦ Subsingleton.elim x y ▸ Joined.refl x⟩
  refine eq_top_iff.2 fun y _ ↦ ?_
  rw [eq_singularCohomologyZeroEval_smul_singularCohomologyZeroOne (X := TopCat.of (E b))
    (0 : E b) y]
  exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _)

end TauCeti
