/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Homological.ContCohomology.Corestriction.TrivialF2

/-!
# Corestriction is invariant under conjugation

Let `U` be an open subgroup of finite index in a profinite group `G`, let `g : G`, and let
`V = gUg⁻¹`. Conjugation `κ : V → U`, `v ↦ g⁻¹ v g`, together with the action of `g` on a discrete
`G`-module `M`, is a compatible pair, and so induces a map `(g)_* : Hⁿ(U, M) ⟶ Hⁿ(V, M)`. This file
proves that corestriction does not see it, in every degree:

```text
cor_V ∘ (g)_* = cor_U : Hⁿ(U, M) ⟶ Hⁿ(G, M).
```

Corestriction from a subgroup therefore depends on that subgroup only through its conjugacy class,
once the subgroups in the class are identified by conjugation; for instance, corestriction along a
finite field extension `L/K` does not depend on the embedding of `L` into the separable closure of
`K` (`TauCeti.galoisCor_embedding_independent`).

The proof runs through Shapiro's lemma, by which corestriction is the coefficient map of the trace
`Coind_U^G M → M` read through the Shapiro isomorphism. Conjugation by `g` gives a `G`-equivariant
map of coinduced modules `TauCeti.DiscreteCoind.conj : Coind_U^G M → Coind_V^G M`,
`f ↦ (x ↦ g • f (g⁻¹ x))`, which commutes with the traces (`TauCeti.DiscreteCoind.trace_conj`).
On the Shapiro side, the two ways of passing from `Hⁿ(G, Coind_U^G M)` to `Hⁿ(V, M)` differ by the
compatible pair of the inner automorphism `x ↦ g⁻¹ x g` of `G` and the action of `g`, which acts
trivially on cohomology (`TauCeti.ContinuousCohomology.map_eq_id_of_inner`).

For a normal subgroup `V`, conjugation `v ↦ g⁻¹ v g` of `V` and the action of `g` form a
compatible pair, which induces the endomorphism `(g)_*` of `Hⁿ(V, M)`
(`TauCeti.ContinuousCohomology.conjNormalMap`), the conjugation through which NSW (3.3.11)
describes the kernel of corestriction. Under Shapiro's map it is the coefficient map
of the conjugation `f ↦ (x ↦ g • f (g⁻¹ x))` of `Coind_V^G M`.

## Main definitions

* `TauCeti.ContinuousCohomology.conjNormalMap`: the conjugation `(g)_*` on `Hⁿ(V, M)` for a normal
  subgroup `V`, in every degree.

## Main results

* `TauCeti.ContinuousCohomology.shapiroMap_comp_map_of_conj`: the Shapiro maps intertwine the
  conjugation `(g)_*` with the coefficient map of the conjugation of coinduced modules.
* `TauCeti.ContinuousCohomology.map_comp_corestriction_of_conj`: corestriction from `gUg⁻¹`
  after conjugation `(g)_*` is corestriction from `U`, in every degree.
* `TauCeti.trivialF2Map_comp_trivialF2CorMap_of_conj`: the same statement with trivial `𝔽₂`
  coefficients, where `(g)_*` is pullback along `κ`.
* `TauCeti.ContCohomology.explicitCor2_explicitMap2_of_conj`: the same statement in degree two
  for the explicit inhomogeneous model, with the transversal corestriction `explicitCor2`.
* `TauCeti.ContinuousCohomology.shapiroMap_comp_conjNormalMap`: for a normal subgroup, Shapiro's
  map intertwines `(g)_*` with the conjugation of `Coind_V^G M`.
* `TauCeti.ContinuousCohomology.conjNormalMap_one`,
  `TauCeti.ContinuousCohomology.conjNormalMap_comp`: `g ↦ (g)_*` is an action of `G` on
  `Hⁿ(V, M)`, `(1)_* = 𝟙` and `(g)_* ≫ (h)_* = (h * g)_*`.
* `TauCeti.ContinuousCohomology.conjNormalMap_naturality`: `(g)_*` is natural in the
  coefficients.

## References

* J. Neukirch, A. Schmidt, K. Wingberg, *Cohomology of Number Fields*, 2nd ed., Chapter I, §5,
  for the conjugation maps `g_*` and their compatibility with corestriction.
* K. S. Brown, *Cohomology of Groups*, Chapter III, §§8–9, for conjugation on cohomology and the
  coinduced-module construction of the transfer.
-/

public section

open CategoryTheory

namespace TauCeti

universe u

/-! ### Corestriction and conjugation -/

namespace ContinuousCohomology

open TauCeti.ContCohomology

variable {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [CompactSpace G] [TotallyDisconnectedSpace G]
  (U V : Subgroup G) (M : Type u) [AddCommGroup M] [TopologicalSpace M] [DiscreteTopology M]
  [DistribMulAction G M] [ContinuousSMul G M]
  (g : G) (κ : V →ₜ* U) (hκ : ∀ v : V, (κ v : G) = g⁻¹ * v * g)
  (f : TopRep.res (κ : V →* U) (ofDiscreteModule ℤ U M) ⟶ ofDiscreteModule ℤ V M)
  (hf : ∀ m : M, f.hom m = g • m)

omit [TotallyDisconnectedSpace G] [ContinuousSMul G M] in
include hκ hf in
/-- **The Shapiro map intertwines conjugation**: Shapiro's map for `U` followed by the conjugation
`(g)_*` is the coefficient map of the conjugation `Coind_U^G M → Coind_V^G M` followed by Shapiro's
map for `V`. Both are compatible-pair maps from `Hⁿ(G, Coind_U^G M)` to `Hⁿ(V, M)`; they differ by
the pair of the inner automorphism `x ↦ g⁻¹ x g` of `G` and the action of `g`, which induces the
identity. Compactness ensures that the right-translation action on the discrete coinduced module is
continuous. -/
theorem shapiroMap_comp_map_of_conj (hVU : V ≤ U.map (MulAut.conj g).toMonoidHom) (n : ℕ) :
    shapiroMap U M n ≫ _root_.ContinuousCohomology.map κ f n =
      coeffMap (ofDiscreteModuleMap
          (DiscreteCoind.conj U V M g hVU).toAddMonoidHom.toIntLinearMap
          fun h F => _root_.map_smul (DiscreteCoind.conj U V M g hVU) h F) n ≫
        shapiroMap V M n := by
  let X := ofDiscreteModule ℤ G (DiscreteCoind G U M)
  -- The inner compatible pair `(x ↦ g⁻¹ x g, F ↦ g • F)` on `Hⁿ(G, Coind_U^G M)`.
  let c : G →ₜ* G := ContinuousMonoidHom.toContinuousMonoidHom (ContinuousAut.conj g⁻¹)
  have hc (x : G) : c x = g⁻¹ * x * g := by simp [c]
  have hcM (x : G) : (c : G →* G) x = g⁻¹ * x * g := hc x
  let B : TopRep.res (c : G →* G) X ⟶ X := ofDiscreteModulePair (c : G →* G)
    (DistribSMul.toAddMonoidHom (DiscreteCoind G U M) g).toIntLinearMap
    fun x F => by
      simp only [AddMonoidHom.coe_toIntLinearMap, DistribSMul.toAddMonoidHom_apply,
        hcM, smul_smul]
      congr 1
      group
  have hB : _root_.ContinuousCohomology.map c B n = 𝟙 _ :=
    map_eq_id_of_inner g c hc B
      (fun (Φ : DiscreteCoind G U M) => (ofDiscreteModulePair_hom_apply (c : G →* G) _ _ Φ).trans
        (ofDiscreteModule_ρ_apply_apply g Φ).symm)
      (ofDiscreteModule_isSmoothDiscrete ℤ G (DiscreteCoind G U M)) n
  -- Both sides are the compatible pair of `v ↦ g⁻¹ v g` and `Φ ↦ g • Φ 1`; on the left this needs
  -- the inner pair, which induces the identity.
  let F : DiscreteCoind G U M →ₗ[ℤ] M :=
    ((DistribSMul.toAddMonoidHom M g).comp (DiscreteCoind.eval G U M)).toIntLinearMap
  have hF (v : V) (Φ : DiscreteCoind G U M) :
      F ((ContinuousMonoidHom.subgroupSubtype U).comp κ v • Φ) = v • F Φ := by
    simp only [F, AddMonoidHom.coe_toIntLinearMap, AddMonoidHom.coe_comp, Function.comp_apply,
      DiscreteCoind.eval_apply, DistribSMul.toAddMonoidHom_apply, DiscreteCoind.coe_smul, one_mul,
      ContinuousMonoidHom.comp_toFun, ContinuousMonoidHom.subgroupSubtype_apply,
      DiscreteCoind.apply_coe, Subgroup.smul_def]
    rw [hκ, smul_smul, smul_smul]
    congr 1
    group
  have hFΦ (Φ : DiscreteCoind G U M) : F Φ = g • Φ 1 := by simp [F]
  let Ψ := ofDiscreteModuleMap (DiscreteCoind.conj U V M g hVU).toAddMonoidHom.toIntLinearMap
    fun h Φ => _root_.map_smul (DiscreteCoind.conj U V M g hVU) h Φ
  let evV := ofDiscreteModulePair (ContinuousMonoidHom.subgroupSubtype V : V →* G)
    (DiscreteCoind.eval G V M).toIntLinearMap fun v Φ => eval_subgroupSubtype_smul G V M v Φ
  -- A coefficient map followed by a compatible-pair map is a single compatible-pair map.
  have hΨ : coeffMap Ψ n ≫ _root_.ContinuousCohomology.map _ evV n =
      _root_.ContinuousCohomology.map (ContinuousMonoidHom.subgroupSubtype V)
        ((TopRep.resFunctor _).map Ψ ≫ evV) n := by
    rw [← map_comp_coeffMap _ _ evV Ψ (𝟙 _) (Category.comp_id _).symm, coeffMap_id,
      Category.comp_id]
  -- Write both sides as single compatible-pair maps, inserting the inner pair on the left.
  symm
  rw [shapiroMap_def, shapiroMap_def, ← _root_.ContinuousCohomology.map_comp (X := X), hΨ,
    ← Category.id_comp (_root_.ContinuousCohomology.map _ _ n), ← hB,
    ← _root_.ContinuousCohomology.map_comp (X := X) c]
  refine map_congr (ContinuousMonoidHom.ext fun v => by simp [hc, hκ]) ?_ n
  -- Both coefficient maps send `Φ` to `g • Φ 1`.
  refine HEq.trans (ofDiscreteModulePair_heq_of_hom_apply
    (MonoidHom.ext fun v => by simp [hc, hκ]) F (fun v Φ => hF v Φ) _ ?_).symm
    (heq_of_eq (ofDiscreteModulePair_eq_of_hom_apply _ F (fun v Φ => hF v Φ) _ ?_))
  · intro Φ
    let BV := (TopRep.resFunctor (ContinuousMonoidHom.subgroupSubtype V : V →* G)).map B
    let ΨV := (TopRep.resFunctor (ContinuousMonoidHom.subgroupSubtype V : V →* G)).map Ψ
    have h₁ : BV.hom Φ = g • Φ := ofDiscreteModulePair_hom_apply (c : G →* G) _ _ Φ
    have h₂ : ΨV.hom (g • Φ) = DiscreteCoind.conj U V M g hVU (g • Φ) :=
      ofDiscreteModuleMap_hom_apply (G := G)
        (DiscreteCoind.conj U V M g hVU).toAddMonoidHom.toIntLinearMap
        (fun h Φ => _root_.map_smul (DiscreteCoind.conj U V M g hVU) h Φ) (g • Φ)
    have h₃ : evV.hom (DiscreteCoind.conj U V M g hVU (g • Φ)) =
        DiscreteCoind.conj U V M g hVU (g • Φ) 1 :=
      (ofDiscreteModulePair_hom_apply (ContinuousMonoidHom.subgroupSubtype V : V →* G)
        (DiscreteCoind.eval G V M).toIntLinearMap
        (fun v Φ => eval_subgroupSubtype_smul G V M v Φ) _).trans
        (DiscreteCoind.eval_apply (A := M) _)
    refine (TopRep.comp_apply BV (ΨV ≫ evV) Φ).trans ((TopRep.comp_apply ΨV evV _).trans ?_)
    refine (congrArg evV.hom ((congrArg ΨV.hom h₁).trans h₂)).trans (h₃.trans ?_)
    rw [hFΦ, DiscreteCoind.conj_apply, DiscreteCoind.coe_smul, mul_one, inv_mul_cancel]
  · intro Φ
    refine (TopRep.comp_apply ((TopRep.resFunctor (κ : V →* U)).map (ofDiscreteModulePair
      (ContinuousMonoidHom.subgroupSubtype U : U →* G) (DiscreteCoind.eval G U M).toIntLinearMap
      fun u Φ => eval_subgroupSubtype_smul G U M u Φ)) f Φ).trans ((hf _).trans ?_)
    exact (congrArg (fun m : M => g • m) ((ofDiscreteModulePair_hom_apply _ _ _ Φ).trans
      (DiscreteCoind.eval_apply Φ))).trans (hFΦ Φ).symm

include hκ hf in
/-- **Corestriction is invariant under conjugation**, in every degree: for `g : G`, an open
subgroup `U` of finite index and `V = gUg⁻¹`, corestriction from `V` after the conjugation
`(g)_* : Hⁿ(U, M) ⟶ Hⁿ(V, M)` is corestriction from `U`. Here `(g)_*` is the map of the compatible
pair of `κ : V → U`, `v ↦ g⁻¹ v g`, and the action of `g` on `M`; both are taken as hypotheses on
their values, so that the statement applies to any presentation of the pair. -/
@[reassoc]
theorem map_comp_corestriction_of_conj (hVU : V = U.map (MulAut.conj g).toMonoidHom)
    (hU : IsOpen (U : Set G)) [U.FiniteIndex]
    (hV : IsOpen (V : Set G)) [V.FiniteIndex] (n : ℕ) :
    _root_.ContinuousCohomology.map κ f n ≫ corestriction V M hV n = corestriction U M hU n := by
  have := isIso_shapiroMap U (U.isClosed_of_isOpen hU) M n
  rw [← cancel_epi (shapiroMap U M n), shapiroMap_comp_corestriction,
    reassoc_of% (shapiroMap_comp_map_of_conj U V M g κ hκ f hf hVU.le n),
    shapiroMap_comp_corestriction, ← coeffMap_comp]
  -- It remains that the conjugation map of coinduced modules commutes with the traces.
  congr 1
  set Ψ := ofDiscreteModuleMap (DiscreteCoind.conj U V M g hVU.le).toAddMonoidHom.toIntLinearMap
    fun h Φ => _root_.map_smul (DiscreteCoind.conj U V M g hVU.le) h Φ
  set τV := ofDiscreteModuleMap (DiscreteCoind.trace G V M).toAddMonoidHom.toIntLinearMap
    fun h Φ => _root_.map_smul (DiscreteCoind.trace G V M) h Φ
  set τU := ofDiscreteModuleMap (DiscreteCoind.trace G U M).toAddMonoidHom.toIntLinearMap
    fun h Φ => _root_.map_smul (DiscreteCoind.trace G U M) h Φ
  refine TopRep.hom_ext (DFunLike.ext _ _ fun (Φ : DiscreteCoind G U M) => ?_)
  have h₁ : (Ψ ≫ τV).hom Φ = τV.hom (Ψ.hom Φ) := TopRep.comp_apply Ψ τV Φ
  have h₂ : Ψ.hom Φ = DiscreteCoind.conj U V M g hVU.le Φ := ofDiscreteModuleMap_hom_apply _ _ Φ
  have h₃ : τV.hom (DiscreteCoind.conj U V M g hVU.le Φ) =
      DiscreteCoind.trace G V M (DiscreteCoind.conj U V M g hVU.le Φ) :=
    ofDiscreteModuleMap_hom_apply _ _ _
  have h₄ : τU.hom Φ = DiscreteCoind.trace G U M Φ := ofDiscreteModuleMap_hom_apply _ _ Φ
  exact ((h₁.trans (congrArg τV.hom h₂)).trans h₃).trans
    ((DiscreteCoind.trace_conj g hVU Φ).trans h₄.symm)

end ContinuousCohomology

/-! ### Conjugation on the cohomology of a normal subgroup -/

namespace ContinuousCohomology

open TauCeti.ContCohomology

-- `v ↦ g⁻¹ v g` is `ContinuousAut.conjNormal g⁻¹`, read as a continuous endomorphism of `V`
-- by `ContinuousMonoidHom.toContinuousMonoidHom`, as for `ContinuousAut.conj` above.

variable {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  (V : Subgroup G) [V.Normal]
  (M : Type u) [AddCommGroup M] [TopologicalSpace M] [DiscreteTopology M]
  [DistribMulAction G M]

/-- The compatible pair of conjugation `v ↦ g⁻¹ v g` of the normal subgroup `V`
(`TauCeti.ContinuousAut.conjNormal g⁻¹`) and the action of `g` on `M`, which induces
`conjNormalMap`. -/
noncomputable def conjNormalPair (g : G) :
    TopRep.res (ContinuousMonoidHom.toContinuousMonoidHom
        (ContinuousAut.conjNormal g⁻¹ : ContinuousAut V) : V →* V) (ofDiscreteModule ℤ V M) ⟶
      ofDiscreteModule ℤ V M :=
  ofDiscreteModulePair _ (DistribSMul.toAddMonoidHom M g).toIntLinearMap fun v m => by
    have hv : ((ContinuousMonoidHom.toContinuousMonoidHom
        (ContinuousAut.conjNormal g⁻¹ : ContinuousAut V) : V →* V) v : G) = g⁻¹ * v * g := by
      simp
    simp only [AddMonoidHom.coe_toIntLinearMap, DistribSMul.toAddMonoidHom_apply,
      Subgroup.smul_def, smul_smul, hv]
    congr 1
    group

/-- The compatible pair `conjNormalPair V M g` acts on `M` as `g`. -/
@[simp]
theorem conjNormalPair_hom_apply (g : G) (m : M) : (conjNormalPair V M g).hom m = g • m :=
  ofDiscreteModulePair_hom_apply _ _ _ m

/-- **Conjugation on the cohomology of a normal subgroup**, `(g)_* : Hⁿ(V, M) ⟶ Hⁿ(V, M)` in every
degree: the map of the compatible pair of `v ↦ g⁻¹ v g` and the action of `g` on `M`. -/
noncomputable def conjNormalMap (g : G) (n : ℕ) :
    continuousCohomology n (ofDiscreteModule ℤ V M) ⟶
      continuousCohomology n (ofDiscreteModule ℤ V M) :=
  _root_.ContinuousCohomology.map
    (ContinuousMonoidHom.toContinuousMonoidHom (ContinuousAut.conjNormal g⁻¹))
    (conjNormalPair V M g) n

-- Not `@[simp]`: `conjNormalMap` is the intended normal form, and this lemma unfolds it.
/-- The defining equation of `conjNormalMap`: the map of the compatible pair `conjNormalPair`. -/
theorem conjNormalMap_def (g : G) (n : ℕ) :
    conjNormalMap V M g n =
      _root_.ContinuousCohomology.map
        (ContinuousMonoidHom.toContinuousMonoidHom (ContinuousAut.conjNormal g⁻¹))
        (conjNormalPair V M g) n :=
  (rfl)

/-- Conjugation by `1` is the identity of `Hⁿ(V, M)`. -/
@[simp]
theorem conjNormalMap_one (n : ℕ) : conjNormalMap V M 1 n = 𝟙 _ := by
  rw [conjNormalMap_def, ← _root_.ContinuousCohomology.map_id (ofDiscreteModule ℤ V M) n]
  have hφ : ContinuousMonoidHom.toContinuousMonoidHom
      (ContinuousAut.conjNormal (1 : G)⁻¹ : ContinuousAut V) = ContinuousMonoidHom.id V :=
    ContinuousMonoidHom.ext fun v => Subtype.ext (by simp)
  refine map_congr hφ ?_ n
  -- Both coefficient maps are the identity of `M`.
  refine ofDiscreteModulePair_heq_of_hom_apply (congrArg (fun φ : V →ₜ* V => (φ : V →* V)) hφ)
    _ _ (𝟙 (ofDiscreteModule ℤ V M)) fun m => ?_
  exact (one_smul G m).symm

/-- **Conjugation is multiplicative**: conjugation by `g` followed by conjugation by `h` is
conjugation by `h * g`. -/
@[reassoc]
theorem conjNormalMap_comp (g h : G) (n : ℕ) :
    conjNormalMap V M g n ≫ conjNormalMap V M h n = conjNormalMap V M (h * g) n := by
  rw [conjNormalMap_def, conjNormalMap_def, conjNormalMap_def,
    ← _root_.ContinuousCohomology.map_comp]
  have hφ : (ContinuousMonoidHom.toContinuousMonoidHom
        (ContinuousAut.conjNormal g⁻¹ : ContinuousAut V)).comp
        (ContinuousMonoidHom.toContinuousMonoidHom
          (ContinuousAut.conjNormal h⁻¹ : ContinuousAut V)) =
      ContinuousMonoidHom.toContinuousMonoidHom
        (ContinuousAut.conjNormal (h * g)⁻¹ : ContinuousAut V) :=
    ContinuousMonoidHom.ext fun v => Subtype.ext (by simp [mul_assoc])
  refine map_congr hφ ?_ n
  -- Both coefficient maps are the action of `h * g` on `M`.
  refine HEq.symm (ofDiscreteModulePair_heq_of_hom_apply
    (congrArg (fun φ : V →ₜ* V => (φ : V →* V)) hφ.symm) _ _ _ fun m => ?_)
  -- The composite of `TopRep` morphisms evaluates as the composite of the underlying maps.
  change (conjNormalPair V M h).hom ((conjNormalPair V M g).hom m) = (h * g) • m
  rw [conjNormalPair_hom_apply, conjNormalPair_hom_apply, smul_smul]

/-- **Shapiro's map intertwines conjugation**: for a normal subgroup `V`, Shapiro's map followed by
`(g)_*` is the coefficient map of the conjugation of `Coind_V^G M` by `g`, followed by Shapiro's
map. -/
theorem shapiroMap_comp_conjNormalMap [CompactSpace G] (g : G) (n : ℕ) :
    shapiroMap V M n ≫ conjNormalMap V M g n =
      coeffMap (ofDiscreteModuleMap
          (DiscreteCoind.conj V V M g (show V.map (MulAut.conj g).toMonoidHom = V from
            Subgroup.Normal.map_conj_eq V g).ge).toAddMonoidHom.toIntLinearMap
          fun h F => _root_.map_smul (DiscreteCoind.conj V V M g
            (show V.map (MulAut.conj g).toMonoidHom = V from
              Subgroup.Normal.map_conj_eq V g).ge) h F) n ≫
        shapiroMap V M n :=
  shapiroMap_comp_map_of_conj V V M g _ (fun v => by simp)
    (conjNormalPair V M g) (conjNormalPair_hom_apply V M g)
    (show V.map (MulAut.conj g).toMonoidHom = V from Subgroup.Normal.map_conj_eq V g).ge n

/-- **Conjugation is natural in the coefficients**: for a `G`-equivariant map `f : M → N`, the
coefficient map of `f` on `Hⁿ(V, -)` commutes with `(g)_*`. -/
theorem conjNormalMap_naturality (N : Type u) [AddCommGroup N] [TopologicalSpace N]
    [DiscreteTopology N] [DistribMulAction G N] (f : M →+[G] N) (g : G) (n : ℕ) :
    conjNormalMap V M g n ≫
        coeffMap (ofDiscreteModuleMap (G := V) f.toAddMonoidHom.toIntLinearMap
          fun v m => _root_.map_smul f (v : G) m) n =
      coeffMap (ofDiscreteModuleMap (G := V) f.toAddMonoidHom.toIntLinearMap
          fun v m => _root_.map_smul f (v : G) m) n ≫
        conjNormalMap V N g n := by
  refine map_comp_coeffMap _ _ _ _ _ ?_ n
  refine TopRep.hom_ext (DFunLike.ext _ _ fun (m : M) => ?_)
  -- Both composites of `TopRep` morphisms evaluate as the composites of their underlying maps
  -- (`TopRep.comp_apply`, by `rfl`), and the coefficient map of `f` evaluates as `f`.
  change (conjNormalPair V N g).hom (f m) =
    (ofDiscreteModuleMap (G := V) f.toAddMonoidHom.toIntLinearMap
      fun v m => _root_.map_smul f (v : G) m).hom ((conjNormalPair V M g).hom m)
  rw [conjNormalPair_hom_apply, conjNormalPair_hom_apply]
  exact (_root_.map_smul f g m).symm

end ContinuousCohomology

/-! ### Trivial `𝔽₂` coefficients -/

section TrivialF2

variable {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [CompactSpace G] [TotallyDisconnectedSpace G] {U V : Subgroup G}

attribute [local instance] TopRep.distribMulAction TopRep.smulCommClass continuousSMul_trivialF2

/-- **Corestriction with trivial `𝔽₂` coefficients is invariant under conjugation**, in every
degree: for `g : G`, an open subgroup `U` of finite index and `V = gUg⁻¹`, pullback along any
continuous `κ : V → U` with `κ v = g⁻¹ v g` followed by corestriction from `V` is corestriction
from `U`. -/
@[reassoc]
theorem trivialF2Map_comp_trivialF2CorMap_of_conj (hU : IsOpen (U : Set G)) [U.FiniteIndex]
    (hV : IsOpen (V : Set G)) [V.FiniteIndex] (g : G)
    (hVU : V = U.map (MulAut.conj g).toMonoidHom) (κ : V →ₜ* U)
    (hκ : ∀ v : V, (κ v : G) = g⁻¹ * v * g) (n : ℕ) :
    trivialF2Map κ n ≫ trivialF2CorMap G V hV n = trivialF2CorMap G U hU n := by
  -- Read in the discrete model `(trivialF2 G).V`, pullback along `κ` is the compatible pair of
  -- `κ` and the identity, which is also the action of `g` since `G` acts trivially.
  have hid (v : V) (m : (trivialF2 G).V) :
      AddMonoidHom.id _ ((κ : V →* U) v • m) = v • AddMonoidHom.id _ m := by
    simp only [AddMonoidHom.id_apply, Subgroup.smul_def, TopRep.distribMulAction_smul,
      trivialF2_ρ_apply_apply]
  have h := eqToHom_comp_trivialF2Map κ (ofDiscreteModule_subgroup_trivialF2 G U)
    (ofDiscreteModule_subgroup_trivialF2 G V) (AddMonoidHom.id _) hid
    (fun m => (trivialF2Equiv_eqToHom_ofDiscreteModule_subgroup_trivialF2 G V m).trans
      (trivialF2Equiv_eqToHom_ofDiscreteModule_subgroup_trivialF2 G U m).symm) n
  rw [trivialF2CorMap_def, trivialF2CorMap_def, ← cancel_epi (eqToHom (congrArg
    (continuousCohomology n) (ofDiscreteModule_subgroup_trivialF2 G U))), reassoc_of% h]
  simp only [eqToHom_trans_assoc, eqToHom_refl, Category.id_comp]
  exact ContinuousCohomology.map_comp_corestriction_of_conj_assoc U V (trivialF2 G).V g κ hκ _
    (fun m => (ofDiscreteModulePair_hom_apply _ _ _ m).trans
      ((TopRep.distribMulAction_smul _ g m).trans (trivialF2_ρ_apply_apply G g m)).symm) hVU hU hV
    n _

end TrivialF2

/-! ### Degree two in the explicit model -/

namespace ContCohomology

variable {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [CompactSpace G] [TotallyDisconnectedSpace G]
  (U V : Subgroup G) (M : Type u) [AddCommGroup M] [TopologicalSpace M] [DiscreteTopology M]
  [DistribMulAction G M] [ContinuousSMul G M]

/-- **Degree-two corestriction is invariant under conjugation**, in the explicit inhomogeneous
model: for `g : G`, an open subgroup `U` of finite index and `V = gUg⁻¹`, the explicit
corestriction from `V` after the conjugation `(g)_* : H²(U, M) → H²(V, M)` is the explicit
corestriction from `U`. As in `TauCeti.ContinuousCohomology.map_comp_corestriction_of_conj`,
`(g)_*` is the map of the compatible pair of `κ : V → U`, `v ↦ g⁻¹ v g`, and the action `f` of
`g` on `M`, both given through their values. -/
theorem explicitCor2_explicitMap2_of_conj (g : G) (κ : V →ₜ* U)
    (hκ : ∀ v : V, (κ v : G) = g⁻¹ * v * g) (f : M →+ M) (hf : ∀ m : M, f m = g • m)
    (hVU : V = U.map (MulAut.conj g).toMonoidHom) (hU : IsOpen (U : Set G)) [U.FiniteIndex]
    (hV : IsOpen (V : Set G)) [V.FiniteIndex] (x : H2 U M) :
    explicitCor2 G M V hV (explicitMap2 U M V M κ f continuous_of_discreteTopology
      (fun v m => by
        simp only [hf, Subgroup.smul_def, hκ, smul_smul, mul_assoc, mul_inv_cancel_left]) x) =
      explicitCor2 G M U hU x := by
  have : LocallyCompactSpace U := (U.isClosed_of_isOpen hU).locallyCompactSpace
  have : LocallyCompactSpace V := (V.isClosed_of_isOpen hV).locallyCompactSpace
  -- Transport to the canonical carrier, where the statement is
  -- `ContinuousCohomology.map_comp_corestriction_of_conj` in degree two.
  refine (explicitH2AddEquivContinuousCohomology G M).injective ?_
  rw [← ContinuousCohomology.explicitH2AddEquivContinuousCohomology_corestriction,
    ← ContinuousCohomology.explicitH2AddEquivContinuousCohomology_corestriction,
    ← explicitH2AddEquivContinuousCohomology_map U M V M κ f _ x, ← ConcreteCategory.comp_apply]
  exact ConcreteCategory.congr_hom (ContinuousCohomology.map_comp_corestriction_of_conj U V M g κ hκ
    _ (fun m => (ofDiscreteModulePair_hom_apply _ _ _ m).trans (hf m)) hVU hU hV 2) _

end ContCohomology

end TauCeti
