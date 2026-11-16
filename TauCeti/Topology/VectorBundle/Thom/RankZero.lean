/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Cohomology.DegreeZero
public import TauCeti.Topology.VectorBundle.Thom.Homology
import TauCeti.Algebra.Module.Equiv.SpanSingleton

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
Over a field the homology Thom map `x ↦ π_*(x ⌢ u)` is then bijective as well
(`TauCeti.IsThomClass.bijective_homologyThomMap_of_finrank_eq_zero`).

Such a class exists for every commutative ring of coefficients, with no orientation
(`TauCeti.exists_isThomClass_of_finrank_eq_zero`): the class of the constant cocycle `1`.

This is the rank-zero case of the Thom isomorphism `Hᵖ(B; M) ≅ Hᵖ⁺ʳ(E, E₀; M)`. It is the case of
the negative normal bundle of a Morse–Bott critical submanifold of index `0`, a family of local
minima, whose negative disc bundle is its zero section.

## Main results

* `TauCeti.IsThomClass.bijective_thomMap_of_finrank_eq_zero`: the Thom isomorphism in cohomology
  for a bundle of rank zero, with coefficients in any module.
* `TauCeti.IsThomClass.bijective_homologyThomMap_of_finrank_eq_zero`: the Thom isomorphism in
  homology for a bundle of rank zero, with coefficients in a field.
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

include F in
/-- The fibres of a fibre bundle whose model fibre is a point have a single point. -/
theorem subsingleton_fiber_of_subsingleton (b : B) : Subsingleton (E b) :=
  (Function.LeftInverse.injective (g := (trivializationAt F E b).symm b) fun y ↦
    (trivializationAt F E b).symm_apply_apply_mk (mem_baseSet_trivializationAt F E b) y
      ).subsingleton

/-- A bundle whose model fibre is a point has no nonzero vectors. -/
theorem zeroSectionCompl_eq_empty_of_subsingleton : zeroSectionCompl F E = ∅ :=
  Set.eq_empty_of_forall_notMem fun v hv ↦
    have := subsingleton_fiber_of_subsingleton F E v.proj
    (mem_zeroSectionCompl.1 hv) (Subsingleton.elim _ _)

/-- For a bundle whose model fibre is a point, the Thom pair `(E, E₀)` has empty subspace. -/
theorem isEmpty_thomPair_snd_of_subsingleton : IsEmpty (thomPair F E).snd :=
  Set.isEmpty_coe_sort.2 (zeroSectionCompl_eq_empty_of_subsingleton F E)

include F in
/-- For a bundle whose model fibre is a point, each fibre pair `(E_b, E_b ∖ {0})` has empty
subspace. -/
theorem isEmpty_compl_zero_fiber_of_subsingleton (b : B) : IsEmpty ({0}ᶜ : Set (E b)) :=
  have := subsingleton_fiber_of_subsingleton F E b
  Set.isEmpty_coe_sort.2 (Set.eq_empty_of_forall_notMem fun _ hx ↦ hx (Subsingleton.elim _ _))

/-- The projection of a bundle whose model fibre is a point is a bijection onto its base. -/
theorem bijective_proj_of_subsingleton : Function.Bijective (π F E) := by
  refine ⟨fun v w h ↦ ?_, fun b ↦ ⟨⟨b, 0⟩, rfl⟩⟩
  obtain ⟨b, x⟩ := v
  obtain ⟨b', y⟩ := w
  obtain rfl : b = b' := h
  have := subsingleton_fiber_of_subsingleton F E b
  rw [Subsingleton.elim x y]

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

omit [NormedSpace ℝ F] in
/-- In rank zero, a class `u ∈ H⁰(E, ∅; K)` restricting to a generator of `H⁰(E_b; K) ≅ K` on every
fibre, as a Thom class does, has a unit value at every point of `E`. -/
private theorem isUnit_singularCohomologyZeroEval_of_subsingleton [Subsingleton F]
    {u : (thomPair F E).singularCohomology (ModuleCat.of K K) K (ModuleCat.of K K) 0}
    (hgen : ∀ b, Submodule.span K
      {TopPair.singularCohomologyMap (fiberThomPairMap F E b) 0 u} = ⊤) (v : TotalSpace F E) :
    IsUnit (singularCohomologyZeroEval (k := K) v
      ((thomPair F E).singularCohomologyπ (ModuleCat.of K K) K (ModuleCat.of K K) 0 u)) := by
  obtain ⟨b, x⟩ := v
  have := subsingleton_fiber_of_subsingleton F E b
  set Q := TopPair.ofSubset (X := TopCat.of (E b)) ({0}ᶜ : Set (E b))
  have : IsEmpty Q.snd := isEmpty_compl_zero_fiber_of_subsingleton F E b
  -- The image `y ∈ H⁰(E_b; K)` of the fibre restriction of `u` generates, since
  -- `H⁰(E_b, ∅) ≅ H⁰(E_b)`.
  set y := Q.singularCohomologyπ (ModuleCat.of K K) K (ModuleCat.of K K) 0
    (TopPair.singularCohomologyMap (fiberThomPairMap F E b) 0 u)
  have hspan : Submodule.span K {y} = ⊤ :=
    (asIso (Q.singularCohomologyπ (ModuleCat.of K K) K (ModuleCat.of K K) 0)).toLinearEquiv
      |>.span_singleton_apply_eq_top_iff.2 (hgen b)
  -- So `c • y = 1` for some `c`; evaluating at the point `0` of `E_b`, its value is a unit.
  obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.1
    (hspan ▸ Submodule.mem_top : (TopCat.of (E b)).singularCohomologyZeroOne (k := K) ∈ _)
  have hy : y = TopCat.singularCohomologyMap (TopPair.Hom.fst (fiberThomPairMap F E b)) 0
      ((thomPair F E).singularCohomologyπ (ModuleCat.of K K) K (ModuleCat.of K K) 0 u) :=
    (ConcreteCategory.congr_hom (TopPair.singularCohomologyπ_naturality
      (fiberThomPairMap F E b) 0) u).symm
  have := congrArg (singularCohomologyZeroEval (k := K) (0 : E b)) hc
  -- `singularCohomologyZeroEval` is stated for the coefficients `𝟙_ (ModuleCat K)`, which are
  -- `ModuleCat.of K K` only up to definitional unfolding, so `rw` does not see these two lemmas.
  erw [LinearMap.map_smul] at this
  rw [singularCohomologyZeroEval_singularCohomologyZeroOne, hy] at this
  erw [singularCohomologyZeroEval_naturality, fiberThomPairMap_fst_apply] at this
  rw [smul_eq_mul, ← Subsingleton.elim x 0] at this
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
  obtain rfl : p = m := by omega
  -- After `Hᵖ(E, ∅) ≅ Hᵖ(E)`, the Thom map is the pull-back along the homeomorphism `π` followed
  -- by the cup product with the image `ū` of `u`. Its values are units, so `ū` has an inverse `v`
  -- for the cup product, and the cup products with `ū` and `v` are inverse to each other.
  set X := TopCat.of (TotalSpace F E)
  obtain ⟨v, h₁, h₂⟩ := exists_singularCup_eq_one (X := X)
    ((thomPair F E).singularCohomologyπ (ModuleCat.of K K) K (ModuleCat.of K K) 0 u)
    (isUnit_singularCohomologyZeroEval_of_subsingleton hgen)
  have key (x y : X.singularCohomology (𝟙_ (ModuleCat.{w} K)) K (𝟙_ (ModuleCat.{w} K)) 0)
      (hxy : X.singularCup K (λ_ _).inv (λ_ _).hom 0 0 0 rfl x y = X.singularCohomologyZeroOne) :
      Function.LeftInverse
        (fun a ↦ X.singularCup K (λ_ (𝟙_ (ModuleCat.{w} K))).inv (ρ_ M).hom p 0 p rfl a y)
        (fun a ↦ X.singularCup K (λ_ (𝟙_ (ModuleCat.{w} K))).inv (ρ_ M).hom p 0 p rfl a x) := by
    intro a
    refine (X.singularCup_assoc K (u₁₂ := (λ_ (𝟙_ (ModuleCat.{w} K))).inv)
      (u := (λ_ (𝟙_ (ModuleCat.{w} K))).inv) (u₂₃ := (λ_ (𝟙_ (ModuleCat.{w} K))).inv)
      (u' := (λ_ (𝟙_ (ModuleCat.{w} K))).inv) (μ₁₂ := (ρ_ M).hom) (μ := (ρ_ M).hom)
      (μ₂₃ := (λ_ (𝟙_ (ModuleCat.{w} K))).hom) (μ' := (ρ_ M).hom) (by monoidal) (by monoidal)
      rfl rfl rfl rfl a x y).trans ?_
    rw [hxy, TopCat.singularCohomologyZeroOne_def]
    exact X.singularCup_constSingularCocycle_right K (η := 𝟙 _) (by simp [unitors_inv_equal])
      (by simp) rfl a
  have hcup : Function.Bijective fun a : X.singularCohomology (𝟙_ (ModuleCat.{w} K)) K M p ↦
      X.singularCup K (λ_ (𝟙_ (ModuleCat.{w} K))).inv (ρ_ M).hom p 0 p rfl a
        ((thomPair F E).singularCohomologyπ (ModuleCat.of K K) K (ModuleCat.of K K) 0 u) :=
    ⟨(key _ v h₁).injective, (key v _ h₂).rightInverse.surjective⟩
  have hπ := ConcreteCategory.bijective_of_isIso
    ((thomPair F E).singularCohomologyπ (ModuleCat.of K K) K M p)
  have hpull := ConcreteCategory.bijective_of_isIso
    ((singularCohomologyFunctor (ModuleCat.of K K) K M p).map (thomPairProj F E).op)
  refine (Function.Bijective.of_comp_iff' hπ _).1 (cast (congrArg Function.Bijective ?_)
    (hcup.comp hpull))
  funext a
  simp only [Function.comp_apply]
  rw [thomMap_apply, TopPair.singularCohomologyπ_singularCup]
  -- The two sides differ only in the proof of `p + 0 = p` and in writing the coefficients `K` as
  -- `𝟙_ (ModuleCat K)` or as `ModuleCat.of K K`.
  rfl

/-- **The homology Thom isomorphism in rank zero.** For a bundle of rank zero and a Thom class `u`
with coefficients in a field `K`, the homology Thom map `x ↦ π_*(x ⌢ u)` is a bijection
`Hₘ(E, E₀; K) ≅ Hₘ(B; K)` in every degree. -/
theorem IsThomClass.bijective_homologyThomMap_of_finrank_eq_zero {K : Type w} [Field K]
    (hF : finrank ℝ F = 0)
    {u : (thomPair F E).singularCohomology (ModuleCat.of K K) K (ModuleCat.of K K) (finrank ℝ F)}
    (hu : IsThomClass F E u) {p m : ℕ} (h : finrank ℝ F + p = m) :
    Function.Bijective (homologyThomMap F E (ModuleCat.of K K) (finrank ℝ F) p m h u).hom :=
  (bijective_homologyThomMap_iff F E h u).2
    (hu.bijective_thomMap_of_finrank_eq_zero hF (ModuleCat.of K K) _)

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
  refine ⟨inv ((thomPair F E).singularCohomologyπ (ModuleCat.of K K) K (ModuleCat.of K K) 0)
    (TopCat.of (TotalSpace F E)).singularCohomologyZeroOne, fun b ↦ ?_⟩
  have := subsingleton_fiber_of_subsingleton F E b
  set Q := TopPair.ofSubset (X := TopCat.of (E b)) ({0}ᶜ : Set (E b))
  have : IsEmpty Q.snd := isEmpty_compl_zero_fiber_of_subsingleton F E b
  rw [← (asIso (Q.singularCohomologyπ (ModuleCat.of K K) K (ModuleCat.of K K) 0)).toLinearEquiv
    |>.span_singleton_apply_eq_top_iff]
  -- On the fibre, the class restricts to the unit `1 ∈ H⁰(E_b; K)`, which generates since `E_b` is
  -- a point.
  have h1 : Q.singularCohomologyπ (ModuleCat.of K K) K (ModuleCat.of K K) 0
      (TopPair.singularCohomologyMap (fiberThomPairMap F E b) 0
        (inv ((thomPair F E).singularCohomologyπ (ModuleCat.of K K) K (ModuleCat.of K K) 0)
          (TopCat.of (TotalSpace F E)).singularCohomologyZeroOne)) =
        (TopCat.of (E b)).singularCohomologyZeroOne (k := K) := by
    rw [← ConcreteCategory.comp_apply, ← TopPair.singularCohomologyπ_naturality,
      ConcreteCategory.comp_apply]
    -- `singularCohomologyZeroOne` lives in the cohomology with coefficients `𝟙_ (ModuleCat K)`,
    -- which is `ModuleCat.of K K` only up to definitional unfolding.
    erw [IsIso.inv_hom_id_apply]
    exact singularCohomologyMap_singularCohomologyZeroOne _
  have : PathConnectedSpace (TopCat.of (E b)) :=
    ⟨⟨(0 : E b)⟩, fun x y ↦ Subsingleton.elim x y ▸ Joined.refl x⟩
  refine eq_top_iff.2 fun y _ ↦ ?_
  rw [Iso.toLinearEquiv_apply, asIso_hom, h1,
    eq_singularCohomologyZeroEval_smul_singularCohomologyZeroOne (X := TopCat.of (E b))
      (0 : E b) y]
  exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _)

end TauCeti
