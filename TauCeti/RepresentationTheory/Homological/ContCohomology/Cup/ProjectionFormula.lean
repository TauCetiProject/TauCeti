/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Homological.ContCohomology.Coinduced.Pairing
public import TauCeti.RepresentationTheory.Homological.ContCohomology.Corestriction.AllDegrees
public import TauCeti.RepresentationTheory.Homological.ContCohomology.Cup.Functoriality

/-!
# The projection formula for continuous cohomology

For an open finite-index subgroup `U` of a profinite group `G`, an equivariant biadditive pairing
`μ : M →+ N →+ P`, and classes `a ∈ Hᵐ(G, M)`, `b ∈ Hⁿ(U, N)`, this file proves the
projection formula in every bidegree:

```text
cor (res a ⌣ b) = a ⌣ cor b.
```

The proof uses the definition of all-degree corestriction through Shapiro's lemma. The pairing
`TauCeti.coindTopPairing` sends `(m, f)` to the coinduced function
`g ↦ μ (g • m) (f g)`. Evaluation at `1` identifies its cup product under the Shapiro map with
`res a ⌣ b`, while `TauCeti.DiscreteCoind.trace_pairing` identifies its coefficient trace with
`m ↦ μ m (tr f)`. Naturality of the all-degree cup product then gives the result.

## Main definitions

* `TauCeti.coindTopPairing`: the coefficient pairing
  `M × Coind_U^G N → Coind_U^G P` on canonical discrete coefficient objects.

## Main results

* `TauCeti.TopPairing.shapiroMap_cup`: the Shapiro map carries the coinduced cup product to the
  cup product of restriction with the Shapiro image.
* `TauCeti.TopPairing.cup_projection`: **the projection formula in every bidegree**.

## References

* K. S. Brown, *Cohomology of Groups*, GTM 87, Springer (1982), Chapter V, §3, (3.8).
* J. Neukirch, A. Schmidt, K. Wingberg, *Cohomology of Number Fields*, 2nd ed., Springer (2008),
  Chapter I, §5, (1.5.3)(iv).
-/

public section

namespace TauCeti

open CategoryTheory ContCohomology _root_.ContinuousCohomology

universe u

variable {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  (U : Subgroup G)
  {M N P : Type u}
  [AddCommGroup M] [TopologicalSpace M] [DiscreteTopology M] [DistribMulAction G M]
  [ContinuousSMul G M]
  [AddCommGroup N] [TopologicalSpace N] [DiscreteTopology N] [DistribMulAction G N]
  [ContinuousSMul G N]
  [AddCommGroup P] [TopologicalSpace P] [DiscreteTopology P] [DistribMulAction G P]
  [ContinuousSMul G P]
  (μ : M →+ N →+ P)
  (hμ : ∀ (g : G) (m : M) (n : N), μ (g • m) (g • n) = g • μ m n)

/-- The coefficient pairing `M × Coind_U^G N → Coind_U^G P` associated to an equivariant
biadditive pairing `μ : M × N → P`, given by `(m, f) ↦ (g ↦ μ (g • m) (f g))`. -/
noncomputable def coindTopPairing :
    TopPairing (ofDiscreteModule ℤ G M)
      (ofDiscreteModule ℤ G (DiscreteCoind G U N))
      (ofDiscreteModule ℤ G (DiscreteCoind G U P)) :=
  ofDiscreteModulePairing (DiscreteCoind.pairing (hμ := hμ) U μ)
    (DiscreteCoind.pairing_smul U μ hμ)

omit [ContinuousSMul G N] [ContinuousSMul G P] in
@[simp]
theorem coindTopPairing_bil_apply (m : M) (f : DiscreteCoind G U N) :
    (coindTopPairing U μ hμ).bil m f = DiscreteCoind.pairing (hμ := hμ) U μ m f := by
  rw [coindTopPairing, ofDiscreteModulePairing_bil_apply]

namespace TopPairing

variable [CompactSpace G] [TotallyDisconnectedSpace G]

omit [ContinuousSMul G N] [ContinuousSMul G P] [CompactSpace G]
  [TotallyDisconnectedSpace G] in
/-- **The Shapiro map carries the coinduced cup product to the subgroup cup product**: evaluation
at `1` sends `(m, f) ↦ (g ↦ μ (g • m) (f g))` to `μ(m, f(1))`. -/
theorem shapiroMap_cup (m n : ℕ)
    (a : continuousCohomology m (ofDiscreteModule ℤ G M))
    (b : continuousCohomology n (ofDiscreteModule ℤ G (DiscreteCoind G U N))) :
    ContinuousCohomology.shapiroMap U P (m + n) ((coindTopPairing U μ hμ).cup m n a b) =
      (ofDiscreteModulePairing (G := U) μ (fun u x y => hμ (u : G) x y)).cup m n
        (ContinuousCohomology.res U (ofDiscreteModule ℤ G M) m a)
        (ContinuousCohomology.shapiroMap U N n b) := by
  let fM := ofDiscreteModulePair (ContinuousMonoidHom.subgroupSubtype U : U →* G)
    (LinearMap.id (R := ℤ) (M := M)) (fun _ _ => rfl)
  let fN := ofDiscreteModulePair (ContinuousMonoidHom.subgroupSubtype U : U →* G)
    (DiscreteCoind.eval G U N).toIntLinearMap (eval_subgroupSubtype_smul G U N)
  let fP := ofDiscreteModulePair (ContinuousMonoidHom.subgroupSubtype U : U →* G)
    (DiscreteCoind.eval G U P).toIntLinearMap (eval_subgroupSubtype_smul G U P)
  have hpair (x : M) (f : DiscreteCoind G U N) :
      fP.hom ((coindTopPairing U μ hμ).bil x f) =
        (ofDiscreteModulePairing (G := U) μ
          (fun u x y => hμ (u : G) x y)).bil (fM x) (fN.hom f) := by
    have hx : fM x = x := by
      exact (ofDiscreteModulePair_hom_apply _ _ _ _).trans (LinearMap.id_apply x)
    have hf : fN.hom f = DiscreteCoind.eval G U N f :=
      by simpa only [fN, AddMonoidHom.coe_toIntLinearMap] using
        (ofDiscreteModulePair_hom_apply
          (ContinuousMonoidHom.subgroupSubtype U : U →* G)
          (DiscreteCoind.eval G U N).toIntLinearMap (eval_subgroupSubtype_smul G U N) f)
    have hleft := ofDiscreteModulePair_hom_apply
      (ContinuousMonoidHom.subgroupSubtype U : U →* G)
      (DiscreteCoind.eval G U P).toIntLinearMap (eval_subgroupSubtype_smul G U P)
      ((coindTopPairing U μ hμ).bil x f)
    have hmiddle : DiscreteCoind.eval G U P ((coindTopPairing U μ hμ).bil x f) =
        μ x (DiscreteCoind.eval G U N f) := by
      rw [coindTopPairing_bil_apply]
      exact DiscreteCoind.eval_pairing (hμ := hμ) U μ x f
    have hright : μ x (DiscreteCoind.eval G U N f) =
        (ofDiscreteModulePairing (G := U) μ
          (fun u x y => hμ (u : G) x y)).bil (fM x) (fN.hom f) := by
      rw [hx, hf, ofDiscreteModulePairing_bil_apply]
    simpa only [fP, AddMonoidHom.coe_toIntLinearMap] using hleft.trans (hmiddle.trans hright)
  have h := (coindTopPairing U μ hμ).cup_map
      (ofDiscreteModulePairing (G := U) μ (fun u x y => hμ (u : G) x y))
      (ContinuousMonoidHom.subgroupSubtype U) fM fN fP hpair m n a b
  have hfM : fM = 𝟙 (TopRep.res (U.subtype : U →* G) (ofDiscreteModule ℤ G M)) := by
    refine TopRep.hom_ext (DFunLike.ext fM.hom
      ((𝟙 (TopRep.res (U.subtype : U →* G) (ofDiscreteModule ℤ G M)) :
        TopRep.res (U.subtype : U →* G) (ofDiscreteModule ℤ G M) ⟶
          TopRep.res (U.subtype : U →* G) (ofDiscreteModule ℤ G M)).hom) fun (x : M) => ?_)
    exact ((ofDiscreteModulePair_hom_apply _ _ _ _).trans (LinearMap.id_apply x)).trans rfl
  simp only [ContinuousCohomology.shapiroMap_def, ContinuousCohomology.res_def]
  rw [hfM] at h
  exact h

/-- **The projection formula in every bidegree** (NSW (1.5.3)(iv), Brown V (3.8)):
corestricting the cup of a restricted ambient class with a subgroup class is the cup of the
ambient class with the corestriction of the subgroup class. -/
theorem cup_projection (hU : IsOpen (U : Set G)) [U.FiniteIndex] (m n : ℕ)
    (a : continuousCohomology m (ofDiscreteModule ℤ G M))
    (b : continuousCohomology n (ofDiscreteModule ℤ U N)) :
    ContinuousCohomology.corestriction U P hU (m + n)
        ((ofDiscreteModulePairing (G := U) μ
          (fun u x y => hμ (u : G) x y)).cup m n
          (ContinuousCohomology.res U (ofDiscreteModule ℤ G M) m a) b) =
      (ofDiscreteModulePairing μ hμ).cup m n a
        (ContinuousCohomology.corestriction U N hU n b) := by
  let b' := (ContinuousCohomology.shapiroIso U (U.isClosed_of_isOpen hU) N n).inv b
  have hb : ContinuousCohomology.shapiroMap U N n b' = b := by
    have hb' := ConcreteCategory.congr_hom
      (ContinuousCohomology.shapiroIso_inv_shapiroMap U
        (U.isClosed_of_isOpen hU) N n) b
    exact hb'.trans rfl
  have hcor : ContinuousCohomology.corestriction U N hU n b =
      ContinuousCohomology.coeffMap
        (ofDiscreteModuleMap (DiscreteCoind.trace G U N).toAddMonoidHom.toIntLinearMap
          (fun g f => _root_.map_smul (DiscreteCoind.trace G U N) g f)) n b' := by
    rw [ContinuousCohomology.corestriction_def, ConcreteCategory.comp_apply]
  rw [hcor, ← hb, ← shapiroMap_cup (hμ := hμ) U μ m n a b', ← ConcreteCategory.comp_apply,
    ContinuousCohomology.shapiroMap_comp_corestriction]
  have hcompat (x : M) (f : DiscreteCoind G U N) :
      (ofDiscreteModuleMap (DiscreteCoind.trace G U P).toAddMonoidHom.toIntLinearMap
        (fun g f => _root_.map_smul (DiscreteCoind.trace G U P) g f)).hom
          ((coindTopPairing U μ hμ).bil x f) =
        (ofDiscreteModulePairing μ hμ).bil
          ((𝟙 (ofDiscreteModule ℤ G M)) x)
          ((ofDiscreteModuleMap (DiscreteCoind.trace G U N).toAddMonoidHom.toIntLinearMap
            (fun g f => _root_.map_smul (DiscreteCoind.trace G U N) g f)).hom f) := by
    have hx : ((𝟙 (ofDiscreteModule ℤ G M)) x) = x := by rfl
    have hf :
        (ofDiscreteModuleMap (DiscreteCoind.trace G U N).toAddMonoidHom.toIntLinearMap
          (fun g f => _root_.map_smul (DiscreteCoind.trace G U N) g f)).hom f =
            DiscreteCoind.trace G U N f :=
      ofDiscreteModuleMap_hom_apply _ _ _
    have hleft := ofDiscreteModuleMap_hom_apply
      (DiscreteCoind.trace G U P).toAddMonoidHom.toIntLinearMap
      (fun g f => _root_.map_smul (DiscreteCoind.trace G U P) g f)
      ((coindTopPairing U μ hμ).bil x f)
    have hmiddle : DiscreteCoind.trace G U P ((coindTopPairing U μ hμ).bil x f) =
        μ x (DiscreteCoind.trace G U N f) := by
      rw [coindTopPairing_bil_apply]
      exact DiscreteCoind.trace_pairing (hμ := hμ) U μ x f
    have hright : μ x (DiscreteCoind.trace G U N f) =
        (ofDiscreteModulePairing μ hμ).bil
          ((𝟙 (ofDiscreteModule ℤ G M)) x)
          ((ofDiscreteModuleMap (DiscreteCoind.trace G U N).toAddMonoidHom.toIntLinearMap
            (fun g f => _root_.map_smul (DiscreteCoind.trace G U N) g f)).hom f) := by
      rw [hx, hf, ofDiscreteModulePairing_bil_apply]
    simpa only [AddMonoidHom.coe_toIntLinearMap] using hleft.trans (hmiddle.trans hright)
  rw [(coindTopPairing U μ hμ).cup_coeffMap (ofDiscreteModulePairing μ hμ)
    (𝟙 _)
    (ofDiscreteModuleMap (DiscreteCoind.trace G U N).toAddMonoidHom.toIntLinearMap
      fun g f => _root_.map_smul (DiscreteCoind.trace G U N) g f)
    (ofDiscreteModuleMap (DiscreteCoind.trace G U P).toAddMonoidHom.toIntLinearMap
      fun g f => _root_.map_smul (DiscreteCoind.trace G U P) g f)
    hcompat m n a b',
    ContinuousCohomology.coeffMap_id]
  rfl

end TopPairing

end TauCeti
