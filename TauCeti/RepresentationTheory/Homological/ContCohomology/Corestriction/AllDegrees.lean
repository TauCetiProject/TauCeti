/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Homological.ContCohomology.Shapiro.AllDegrees
public import TauCeti.RepresentationTheory.Homological.ContCohomology.Corestriction.Trace.DegreeOne
public import TauCeti.RepresentationTheory.Homological.ContCohomology.Corestriction.Trace.DegreeTwo

/-!
# Corestriction in every degree

For an open subgroup `U` of finite index in a profinite group `G` and a discrete `G`-module `M`,
**corestriction** `cor : Hⁿ(U, M) ⟶ Hⁿ(G, M)` is defined on Mathlib's canonical continuous
cohomology in every degree `n`, with no cochain formula, as the composite

```text
Hⁿ(U, M) ≅ Hⁿ(G, Coind_U^G M) ⟶ Hⁿ(G, M)
```

of the inverse of Shapiro's isomorphism `TauCeti.ContinuousCohomology.shapiroIso` and the
coefficient map of the trace `Coind_U^G M → M`, `f ↦ ∑_{gU ∈ G ⧸ U} g • f g⁻¹`
(`TauCeti.DiscreteCoind.trace`). This is the coinduced-module construction of the transfer in
Brown, *Cohomology of Groups*, III §9; it is the classical cohomological corestriction of
Neukirch–Schmidt–Wingberg I §5, not the covariant functoriality of group *homology* that Mathlib's
`groupCohomology` files call by the same name.

The identity `cor ∘ res = [G : U]` (NSW (1.5.7)) rests on the unit `M → Coind_U^G M`,
`m ↦ (g ↦ g • m)`, of coinduction (`TauCeti.DiscreteCoind.unit`), through two facts: restriction
followed by the inverse of Shapiro's isomorphism is the coefficient map of the unit
(`TauCeti.ContinuousCohomology.res_comp_shapiroIso_inv`), and the trace of the unit is
multiplication by the index (`TauCeti.DiscreteCoind.trace_unit`). Corestriction is natural in the
coefficient module, and in degrees `0`, `1` and `2` it agrees, under the comparison isomorphisms
with the explicit inhomogeneous model, with the transversal formulas
`TauCeti.ContCohomology.explicitCor0`, `TauCeti.ContCohomology.explicitCor1` and
`TauCeti.ContCohomology.explicitCor2`.

## Main definitions

* `TauCeti.ContinuousCohomology.corestriction`: **corestriction** `Hⁿ(U, M) ⟶ Hⁿ(G, M)` in every
  degree, for an open finite-index subgroup `U` of a profinite group `G`.

## Main results

* `TauCeti.ContinuousCohomology.shapiroMap_comp_corestriction`: the Shapiro map followed by
  corestriction is the coefficient map of the trace.
* `TauCeti.ContinuousCohomology.res_comp_corestriction`,
  `TauCeti.ContinuousCohomology.corestriction_res`: **`cor ∘ res = [G : U] • id`** in every degree.
* `TauCeti.ContinuousCohomology.corestriction_naturality`: corestriction is natural in the
  coefficient module.
* `TauCeti.ContinuousCohomology.explicitH0Iso_corestriction`,
  `TauCeti.ContinuousCohomology.explicitH1AddEquivContinuousCohomology_corestriction`,
  `TauCeti.ContinuousCohomology.explicitH2AddEquivContinuousCohomology_corestriction`: agreement
  with the explicit corestrictions in degrees `0`, `1` and `2`.

## References

* K. S. Brown, *Cohomology of Groups*, Chapter III, §9, the coinduced-module construction of the
  transfer, and (9.5).
* J. Neukirch, A. Schmidt, K. Wingberg, *Cohomology of Number Fields*, 2nd ed., (1.5.7) and
  (1.6.4).
-/

public section

open CategoryTheory

namespace TauCeti.ContinuousCohomology

open TauCeti.ContCohomology

universe u

variable {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  (U : Subgroup G) (M : Type u) [AddCommGroup M] [TopologicalSpace M] [DiscreteTopology M]
  [DistribMulAction G M] [ContinuousSMul G M]

/-! ### Corestriction -/

variable [CompactSpace G] [TotallyDisconnectedSpace G] (hU : IsOpen (U : Set G)) [U.FiniteIndex]

/-- **Corestriction in every degree**, `cor : Hⁿ(U, M) ⟶ Hⁿ(G, M)`, for an open finite-index
subgroup `U` of a profinite group `G` and a discrete `G`-module `M`: the inverse of Shapiro's
isomorphism `Hⁿ(G, Coind_U^G M) ≅ Hⁿ(U, M)` followed by the coefficient map of the trace
`Coind_U^G M → M`, `f ↦ ∑_{gU} g • f g⁻¹`. This is the classical cohomological corestriction
(transfer), normalized by `cor ∘ res = [G : U]` (`res_comp_corestriction`), and it is characterized
by `shapiroMap_comp_corestriction`. -/
noncomputable def corestriction (n : ℕ) :
    continuousCohomology n (ofDiscreteModule ℤ U M) ⟶
      continuousCohomology n (ofDiscreteModule ℤ G M) :=
  (shapiroIso U (U.isClosed_of_isOpen hU) M n).inv ≫
    coeffMap (ofDiscreteModuleMap (DiscreteCoind.trace G U M).toAddMonoidHom.toIntLinearMap
      fun g f => _root_.map_smul (DiscreteCoind.trace G U M) g f) n

-- Not `@[simp]`: `corestriction` is the intended normal form, and this lemma unfolds it.
/-- The defining equation of corestriction: the inverse of Shapiro's isomorphism followed by the
coefficient map of the trace `Coind_U^G M → M`. -/
theorem corestriction_def (n : ℕ) :
    corestriction U M hU n =
      (shapiroIso U (U.isClosed_of_isOpen hU) M n).inv ≫
        coeffMap (ofDiscreteModuleMap (DiscreteCoind.trace G U M).toAddMonoidHom.toIntLinearMap
          fun g f => _root_.map_smul (DiscreteCoind.trace G U M) g f) n := (rfl)

/-- **The Shapiro map followed by corestriction is the coefficient map of the trace.** This is the
characteristic property of corestriction: it is the unique map `Hⁿ(U, M) ⟶ Hⁿ(G, M)` whose
composite with the Shapiro isomorphism is the coefficient map of `Coind_U^G M → M`. -/
@[reassoc (attr := simp)]
theorem shapiroMap_comp_corestriction (n : ℕ) :
    shapiroMap U M n ≫ corestriction U M hU n =
      coeffMap (ofDiscreteModuleMap (DiscreteCoind.trace G U M).toAddMonoidHom.toIntLinearMap
        fun g f => _root_.map_smul (DiscreteCoind.trace G U M) g f) n := by
  rw [corestriction_def, ← Category.assoc, shapiroMap_shapiroIso_inv, Category.id_comp]

omit [CompactSpace G] [TotallyDisconnectedSpace G] in
/-- The unit followed by the trace is multiplication by the index on `M`, as an endomorphism of
the canonical object of `M`. -/
private theorem unit_comp_trace :
    ofDiscreteModuleMap (DiscreteCoind.unit G U M).toAddMonoidHom.toIntLinearMap
        (fun g m => _root_.map_smul (DiscreteCoind.unit G U M) g m) ≫
      ofDiscreteModuleMap (DiscreteCoind.trace G U M).toAddMonoidHom.toIntLinearMap
        (fun g f => _root_.map_smul (DiscreteCoind.trace G U M) g f) =
      U.index • 𝟙 (ofDiscreteModule ℤ G M) := by
  refine TopRep.hom_ext (DFunLike.ext _ _ fun (m : M) => ?_)
  set ι := ofDiscreteModuleMap (DiscreteCoind.unit G U M).toAddMonoidHom.toIntLinearMap
    fun g m => _root_.map_smul (DiscreteCoind.unit G U M) g m
  set τ := ofDiscreteModuleMap (DiscreteCoind.trace G U M).toAddMonoidHom.toIntLinearMap
    fun g f => _root_.map_smul (DiscreteCoind.trace G U M) g f
  have h₁ : (ι ≫ τ).hom m = τ.hom (ι.hom m) := TopRep.comp_apply ι τ m
  have h₂ : ι.hom m = DiscreteCoind.unit G U M m := ofDiscreteModuleMap_hom_apply _ _ m
  have h₃ : τ.hom (DiscreteCoind.unit G U M m) =
      DiscreteCoind.trace G U M (DiscreteCoind.unit G U M m) :=
    ofDiscreteModuleMap_hom_apply _ _ _
  -- The right side is `[G : U] • m` by definition: the underlying map of `n • f` is `n • f.hom`,
  -- and `(n • F) m = n • F m` for an intertwining map `F`, both additive structures on morphisms
  -- being defined pointwise.
  exact ((h₁.trans (congrArg (fun x => τ.hom x) h₂)).trans h₃).trans (DiscreteCoind.trace_unit m)

/-- **`cor ∘ res = [G : U]` in every degree** (NSW (1.5.7)): restriction to an open finite-index
subgroup `U` followed by corestriction is multiplication by the index `[G : U]` on `Hⁿ(G, M)`. -/
theorem res_comp_corestriction (n : ℕ) :
    res U (ofDiscreteModule ℤ G M) n ≫ corestriction U M hU n =
      U.index • 𝟙 (continuousCohomology n (ofDiscreteModule ℤ G M)) := by
  -- Continuous cohomology is additive in the coefficients, so the coefficient map of `[G : U] • id`
  -- is `[G : U]` times the identity.
  have hfun : coeffMap (U.index • 𝟙 (ofDiscreteModule ℤ G M)) n =
      U.index • 𝟙 (continuousCohomology n (ofDiscreteModule ℤ G M)) := by
    have h := (continuousCohomologyFunctor ℤ G n).map_nsmul (f := 𝟙 (ofDiscreteModule ℤ G M))
      (n := U.index)
    rwa [continuousCohomologyFunctor_map, continuousCohomologyFunctor_map, coeffMap_id] at h
  rw [corestriction_def]
  -- The composites are reassociated by hand, since the middle object of `res ≫ inv` is
  -- `continuousCohomology n (TopRep.res U.subtype (ofDiscreteModule ℤ G M))` on one side and
  -- `continuousCohomology n (ofDiscreteModule ℤ U M)` on the other, which stops `Category.assoc`
  -- from matching as a rewrite rule.
  exact ((Category.assoc _ _ _).symm.trans
    (congrArg (· ≫ coeffMap _ n) (res_comp_shapiroIso_inv U (U.isClosed_of_isOpen hU) M n))).trans
    ((coeffMap_comp _ _ n).symm.trans ((congrArg (coeffMap · n) (unit_comp_trace U M)).trans hfun))

/-- **`cor (res x) = [G : U] • x`** for every class `x ∈ Hⁿ(G, M)` (NSW (1.5.7)). -/
@[simp]
theorem corestriction_res (n : ℕ) (x : continuousCohomology n (ofDiscreteModule ℤ G M)) :
    corestriction U M hU n (res U (ofDiscreteModule ℤ G M) n x) = U.index • x := by
  have h := ConcreteCategory.congr_hom (res_comp_corestriction U M hU n) x
  -- `(res ≫ cor) x` is `cor (res x)` by definition of composition in `TopModuleCat`, and
  -- `([G : U] • 𝟙) x` is `[G : U] • x` by definition of the additive structure on its morphisms
  -- (`TopModuleCat.hom_nsmul`).
  exact h.trans rfl

/-! ### Naturality in the coefficients -/

section Naturality

variable {N : Type u} [AddCommGroup N] [TopologicalSpace N] [DiscreteTopology N]
  [DistribMulAction G N] [ContinuousSMul G N] (f : M →+[G] N)

omit [ContinuousSMul G M] [CompactSpace G] [TotallyDisconnectedSpace G] [ContinuousSMul G N] in
/-- The trace is natural in the coefficients, as morphisms of the canonical objects: the trace of
`M` followed by `f` is the coinduction of `f` followed by the trace of `N`
(`TauCeti.DiscreteCoind.trace_map`). -/
private theorem trace_comp_ofDiscreteModuleMap :
    ofDiscreteModuleMap (DiscreteCoind.trace G U M).toAddMonoidHom.toIntLinearMap
        (fun g φ => _root_.map_smul (DiscreteCoind.trace G U M) g φ) ≫
      ofDiscreteModuleMap f.toAddMonoidHom.toIntLinearMap (fun g m => _root_.map_smul f g m) =
    ofDiscreteModuleMap
        (DiscreteCoind.map f.toAddMonoidHom.toIntLinearMap
          fun (u : U) (m : M) => _root_.map_smul f (u : G) m).toAddMonoidHom.toIntLinearMap
        (fun g φ => DiscreteCoind.map_smul f.toAddMonoidHom.toIntLinearMap
          (fun (u : U) (m : M) => _root_.map_smul f (u : G) m) g φ) ≫
      ofDiscreteModuleMap (DiscreteCoind.trace G U N).toAddMonoidHom.toIntLinearMap
        fun g φ => _root_.map_smul (DiscreteCoind.trace G U N) g φ := by
  refine TopRep.hom_ext (DFunLike.ext _ _ fun (φ : DiscreteCoind G U M) => ?_)
  set τM := ofDiscreteModuleMap (DiscreteCoind.trace G U M).toAddMonoidHom.toIntLinearMap
    fun g φ => _root_.map_smul (DiscreteCoind.trace G U M) g φ
  set τN := ofDiscreteModuleMap (DiscreteCoind.trace G U N).toAddMonoidHom.toIntLinearMap
    fun g φ => _root_.map_smul (DiscreteCoind.trace G U N) g φ
  set fG := ofDiscreteModuleMap f.toAddMonoidHom.toIntLinearMap fun g m => _root_.map_smul f g m
  set cf := ofDiscreteModuleMap
    (DiscreteCoind.map f.toAddMonoidHom.toIntLinearMap
      (fun (u : U) (m : M) => _root_.map_smul f (u : G) m)).toAddMonoidHom.toIntLinearMap
    fun g φ => DiscreteCoind.map_smul f.toAddMonoidHom.toIntLinearMap
      (fun (u : U) (m : M) => _root_.map_smul f (u : G) m) g φ
  -- Both sides send `φ` to `f (tr φ)`: the left one directly, the right one through
  -- `tr (Coind f φ) = f (tr φ)`. Not `simp`: `TopRep.comp_apply` is stated through the
  -- concrete-category coercion, not through `.hom`, so it is applied by hand.
  have hl : (τM ≫ fG).hom φ = f (DiscreteCoind.trace G U M φ) :=
    (TopRep.comp_apply τM fG φ).trans
      ((congrArg (fun x => fG.hom x) (ofDiscreteModuleMap_hom_apply _ _ φ)).trans
        (ofDiscreteModuleMap_hom_apply _ _ (DiscreteCoind.trace G U M φ)))
  have hr : (cf ≫ τN).hom φ = f (DiscreteCoind.trace G U M φ) :=
    (TopRep.comp_apply cf τN φ).trans
      ((congrArg (fun x => τN.hom x) (ofDiscreteModuleMap_hom_apply _ _ φ)).trans
        ((ofDiscreteModuleMap_hom_apply _ _ (DiscreteCoind.map f.toAddMonoidHom.toIntLinearMap
          (fun (u : U) (m : M) => _root_.map_smul f (u : G) m) φ)).trans
          (DiscreteCoind.trace_map f.toAddMonoidHom.toIntLinearMap
            (fun g m => _root_.map_smul f g m) φ)))
  exact hl.trans hr.symm

/-- **Corestriction is natural in the coefficient module**: for a `G`-equivariant homomorphism
`f : M → N` of discrete `G`-modules, corestriction followed by the coefficient map of `f` over `G`
is the coefficient map of `f` over `U` followed by corestriction. -/
@[reassoc]
theorem corestriction_naturality (n : ℕ) :
    corestriction U M hU n ≫
        coeffMap (ofDiscreteModuleMap f.toAddMonoidHom.toIntLinearMap
          fun g m => _root_.map_smul f g m) n =
      coeffMap (ofDiscreteModuleMap (G := U) f.toAddMonoidHom.toIntLinearMap
          fun u m => _root_.map_smul f (u : G) m) n ≫ corestriction U N hU n := by
  -- Cancel the Shapiro isomorphism of `M` on the left; by naturality of the Shapiro map, both sides
  -- become the coefficient map of a composite through the trace, and the two composites agree by
  -- naturality of the trace.
  have := isIso_shapiroMap U (U.isClosed_of_isOpen hU) M n
  rw [← cancel_epi (shapiroMap U M n), ← shapiroMap_naturality_assoc U M (B := N)
    f.toAddMonoidHom (fun u m => _root_.map_smul f (u : G) m)]
  simp only [shapiroMap_comp_corestriction_assoc, shapiroMap_comp_corestriction, ← coeffMap_comp,
    trace_comp_ofDiscreteModuleMap]

end Naturality

/-! ### Agreement with the explicit corestrictions -/

/-- **In degree zero, corestriction is the explicit norm** `m ↦ ∑_{gU} g • m` of
`TauCeti.ContCohomology.explicitCor0`, under the comparisons of `H⁰` with the canonical carrier. -/
theorem explicitH0Iso_corestriction (x : H0 U M) :
    corestriction U M hU 0 ((explicitH0IsoContinuousCohomology U M).hom x) =
      (explicitH0IsoContinuousCohomology G M).hom (explicitCor0 G M U x) := by
  -- The class `x` is the Shapiro image of `y`, so inverse Shapiro sends it to `y`, and the trace
  -- of `y` is the explicit norm of `x`.
  set y := (explicitShapiro0 G U M).symm x with hy
  have hx : (explicitH0IsoContinuousCohomology U M).hom x =
      shapiroMap U M 0 ((explicitH0IsoContinuousCohomology G (DiscreteCoind G U M)).hom y) := by
    rw [explicitH0Iso_shapiroMap, hy, AddEquiv.apply_symm_apply]
  rw [hx, ← ConcreteCategory.comp_apply, shapiroMap_comp_corestriction,
    explicitH0Iso_coeffMap, explicitCor0_eq_explicitCoeff0_trace]
  rfl

/-- **In degree one, corestriction is the explicit transversal formula** of
`TauCeti.ContCohomology.explicitCor1`, under the comparisons of `H¹` with the canonical carrier. -/
theorem explicitH1AddEquivContinuousCohomology_corestriction (x : H1 U M) :
    corestriction U M hU 1 (explicitH1AddEquivContinuousCohomology U M x) =
      explicitH1AddEquivContinuousCohomology G M (explicitCor1 G M U hU x) := by
  have : CompactSpace U := isCompact_iff_compactSpace.mp (U.isClosed_of_isOpen hU).isCompact
  set y := (explicitShapiro1 G U M (U.isClosed_of_isOpen hU)).symm x with hy
  have hx : explicitH1AddEquivContinuousCohomology U M x =
      shapiroMap U M 1 (explicitH1AddEquivContinuousCohomology G (DiscreteCoind G U M) y) := by
    rw [explicitH1AddEquivContinuousCohomology_shapiroMap, hy, ← explicitShapiro1_apply _ _ _
      (U.isClosed_of_isOpen hU), AddEquiv.apply_symm_apply]
  -- The class `x` is the Shapiro image of `y`, so inverse Shapiro sends it to `y`, and the
  -- coefficient map of the trace on `y` is the explicit coefficient map of the trace on `y`.
  rw [hx, ← ConcreteCategory.comp_apply, shapiroMap_comp_corestriction,
    explicitH1AddEquivContinuousCohomology_coeffMap, explicitCor1_eq_explicitCoeff1_trace hU,
    AddMonoidHom.comp_apply, AddEquiv.coe_toAddMonoidHom, ← hy]

/-- **In degree two, corestriction is the explicit transversal formula** of
`TauCeti.ContCohomology.explicitCor2`, under the comparisons of `H²` with the canonical carrier.
The degree-two comparison for `U` needs `U` to be locally compact, which holds because `U` is
closed in the compact group `G`. -/
theorem explicitH2AddEquivContinuousCohomology_corestriction (x : H2 U M) :
    haveI : LocallyCompactSpace U := (U.isClosed_of_isOpen hU).locallyCompactSpace
    corestriction U M hU 2 (explicitH2AddEquivContinuousCohomology U M x) =
      explicitH2AddEquivContinuousCohomology G M (explicitCor2 G M U hU x) := by
  have : LocallyCompactSpace U := (U.isClosed_of_isOpen hU).locallyCompactSpace
  set y := (explicitShapiro2 G U M (U.isClosed_of_isOpen hU)).symm x with hy
  have hx : explicitH2AddEquivContinuousCohomology U M x =
      shapiroMap U M 2 (explicitH2AddEquivContinuousCohomology G (DiscreteCoind G U M) y) := by
    rw [explicitH2AddEquivContinuousCohomology_shapiroMap, hy, ← explicitShapiro2_apply _ _ _
      (U.isClosed_of_isOpen hU), AddEquiv.apply_symm_apply]
  -- As in degree one: the class `x` is the Shapiro image of `y`, so corestriction of `x` is the
  -- coefficient map of the trace on `y`, which is the explicit coefficient map of the trace.
  rw [hx, ← ConcreteCategory.comp_apply, shapiroMap_comp_corestriction,
    explicitH2AddEquivContinuousCohomology_coeffMap, explicitCor2_eq_explicitCoeff2_trace hU,
    AddMonoidHom.comp_apply, AddEquiv.coe_toAddMonoidHom, ← hy]

end TauCeti.ContinuousCohomology
