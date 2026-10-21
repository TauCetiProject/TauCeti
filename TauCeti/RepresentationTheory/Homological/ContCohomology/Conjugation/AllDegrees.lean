/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Homological.ContCohomology.Corestriction.Conjugation
import TauCeti.Algebra.Group.Subgroup.Map

/-!
# Conjugation between conjugate subgroups in every degree

Let `G` be a topological group, `M` a discrete `G`-module, `g : G`, and let `U` and `V` be
subgroups of `G` with `V = gUg⁻¹`. Conjugation `κ : V → U`, `v ↦ g⁻¹ v g`, together with the
action of `g` on `M`, is a compatible pair, and so induces the **conjugation map**

```text
(g)_* : Hⁿ(U, M) ⟶ Hⁿ(V, M)
```

on Mathlib's canonical continuous cohomology, in every degree (Neukirch–Schmidt–Wingberg,
Chapter I, §5). The target subgroup is a separate argument together with the equation
`V = gUg⁻¹`, so that `(g)_*` relates two named subgroups: for a normal subgroup `V` it is an
endomorphism of `Hⁿ(V, M)`, and it is then `TauCeti.ContinuousCohomology.conjNormalMap`.

This file names the map and proves the laws that characterise it: it is an action
(`(1)_* = 𝟙`, `(g)_* ≫ (h)_* = (h * g)_*`), hence an isomorphism; it is natural in the
coefficients; and it commutes with restriction to smaller subgroups. Three further laws rest on the
triviality of inner automorphisms on cohomology (`TauCeti.ContinuousCohomology.map_eq_id_of_inner`):
conjugation by an element of `U` is the identity of `Hⁿ(U, M)`, restriction from `G` followed by
`(g)_*` is restriction from `G`, and, for open subgroups of a profinite group, corestriction from
`V` after `(g)_*` is corestriction from `U`.

## Main definitions

* `TauCeti.ContinuousCohomology.conjHom`: for `V = gUg⁻¹`, the continuous homomorphism
  `V →ₜ* U`, `v ↦ g⁻¹ v g`.
* `TauCeti.ContinuousCohomology.conjMap`: the conjugation `(g)_* : Hⁿ(U, M) ⟶ Hⁿ(V, M)`.

## Main results

* `TauCeti.ContinuousCohomology.conjMap_one`, `TauCeti.ContinuousCohomology.conjMap_comp`:
  conjugation is an action; hence each `(g)_*` is an isomorphism
  (`TauCeti.ContinuousCohomology.isIso_conjMap`).
* `TauCeti.ContinuousCohomology.conjMap_eq_conjNormalMap`: on a normal subgroup, `(g)_*` is
  `conjNormalMap`.
* `TauCeti.ContinuousCohomology.conjMap_naturality`: `(g)_*` is natural in the coefficients.
* `TauCeti.ContinuousCohomology.conjMap_comp_resLE`: `(g)_*` commutes with restriction to
  subgroups `U' ≤ U` and `gU'g⁻¹ ≤ gUg⁻¹`.
* `TauCeti.ContinuousCohomology.res_comp_conjMap`: `(g)_* ∘ res_U = res_V` on `Hⁿ(G, M)`.
* `TauCeti.ContinuousCohomology.conjMap_eq_id_of_mem`: conjugation by an element of `U` is the
  identity of `Hⁿ(U, M)`.
* `TauCeti.ContinuousCohomology.conjMap_comp_corestriction`: `cor_V ∘ (g)_* = cor_U`.

## References

* J. Neukirch, A. Schmidt, K. Wingberg, *Cohomology of Number Fields*, 2nd ed., Chapter I, §5,
  for the conjugation maps `g_*` and their properties.
* K. S. Brown, *Cohomology of Groups*, GTM 87, Chapter III, §8.
-/

public section

open CategoryTheory

namespace TauCeti.ContinuousCohomology

open TauCeti.ContCohomology

universe u

variable {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

/-! ### The conjugation homomorphism -/

section ConjHom

variable (U V : Subgroup G) (g : G)

/-- For `V = gUg⁻¹`, conjugation `V →ₜ* U`, `v ↦ g⁻¹ v g`: the group half of the compatible
pair inducing `conjMap`. -/
def conjHom (hVU : V = U.map (MulAut.conj g).toMonoidHom) : V →ₜ* U where
  toFun v := ⟨(MulAut.conj g).symm v, Subgroup.mem_map_equiv.mp (hVU ▸ v.2)⟩
  map_one' := Subtype.ext (map_one _)
  map_mul' x y := Subtype.ext (map_mul _ _ _)
  continuous_toFun := by
    refine Continuous.subtype_mk ?_ _
    simp only [MulAut.conj_symm_apply]
    fun_prop

/-- `conjHom` is conjugation `v ↦ g⁻¹ v g`. -/
@[simp]
theorem coe_conjHom_apply (hVU : V = U.map (MulAut.conj g).toMonoidHom) (v : V) :
    (conjHom U V g hVU v : G) = g⁻¹ * v * g :=
  MulAut.conj_symm_apply g v

/-- The conjugation compatible-pair identity on coefficients: the action of `g` intertwines the
actions of `V` and of `U` through `conjHom`, `g • (g⁻¹ v g) • m = v • g • m`. -/
theorem conjHom_smul {M : Type*} [AddMonoid M] [DistribMulAction G M]
    (hVU : V = U.map (MulAut.conj g).toMonoidHom) (v : V) (m : M) :
    (DistribSMul.toAddMonoidHom M g) (conjHom U V g hVU v • m) =
      v • (DistribSMul.toAddMonoidHom M g) m := by
  simp only [DistribSMul.toAddMonoidHom_apply, Subgroup.smul_def, coe_conjHom_apply, smul_smul]
  congr 1
  group

end ConjHom

/-! ### The conjugation map -/

variable (U V W : Subgroup G) (M : Type u) [AddCommGroup M] [TopologicalSpace M]
  [DiscreteTopology M] [DistribMulAction G M]

/-- The compatible pair of `conjHom` and the action of `g` on `M`, which induces `conjMap`. -/
noncomputable def conjPair (g : G) (hVU : V = U.map (MulAut.conj g).toMonoidHom) :
    TopRep.res (conjHom U V g hVU : V →* U) (ofDiscreteModule ℤ U M) ⟶
      ofDiscreteModule ℤ V M :=
  ofDiscreteModulePair _ (DistribSMul.toAddMonoidHom M g).toIntLinearMap
    (conjHom_smul U V g hVU)

-- Not `@[simp]`: `conjPair` is the intended normal form, and this lemma unfolds it.
/-- The defining equation of `conjPair`: the compatible pair on the action of `g`. -/
theorem conjPair_def (g : G) (hVU : V = U.map (MulAut.conj g).toMonoidHom) :
    conjPair U V M g hVU =
      ofDiscreteModulePair _ (DistribSMul.toAddMonoidHom M g).toIntLinearMap
        (conjHom_smul U V g hVU) :=
  (rfl)

/-- The compatible pair `conjPair U V M g hVU` acts on `M` as `g`. -/
@[simp]
theorem conjPair_hom_apply (g : G) (hVU : V = U.map (MulAut.conj g).toMonoidHom) (m : M) :
    (conjPair U V M g hVU).hom m = g • m :=
  ofDiscreteModulePair_hom_apply _ _ _ m

/-- **Conjugation between conjugate subgroups**, `(g)_* : Hⁿ(U, M) ⟶ Hⁿ(V, M)` for
`V = gUg⁻¹`, in every degree: the map of the compatible pair of `v ↦ g⁻¹ v g` and the action of
`g` on `M`. -/
noncomputable def conjMap (g : G) (hVU : V = U.map (MulAut.conj g).toMonoidHom) (n : ℕ) :
    continuousCohomology n (ofDiscreteModule ℤ U M) ⟶
      continuousCohomology n (ofDiscreteModule ℤ V M) :=
  _root_.ContinuousCohomology.map (conjHom U V g hVU) (conjPair U V M g hVU) n

-- Not `@[simp]`: `conjMap` is the intended normal form, and this lemma unfolds it.
/-- The defining equation of `conjMap`: the map of the compatible pair `conjPair`. -/
theorem conjMap_def (g : G) (hVU : V = U.map (MulAut.conj g).toMonoidHom) (n : ℕ) :
    conjMap U V M g hVU n =
      _root_.ContinuousCohomology.map (conjHom U V g hVU) (conjPair U V M g hVU) n :=
  (rfl)

-- The subgroup equation is proved in the statement, not a hypothesis: `simpNF` adds hypotheses to
-- the simp set, and `U = U.map _` then loops while discharging `U.Normal` for the simp lemma
-- `conjMap_eq_conjNormalMap`.
/-- Conjugation by `1` is the identity of `Hⁿ(U, M)`. -/
@[simp]
theorem conjMap_one (n : ℕ) :
    conjMap U U M 1 (by rw [map_one]; exact (Subgroup.map_id U).symm) n = 𝟙 _ := by
  have hU : U = U.map (MulAut.conj (1 : G)).toMonoidHom := by
    rw [map_one]; exact (Subgroup.map_id U).symm
  rw [conjMap_def, ← _root_.ContinuousCohomology.map_id (ofDiscreteModule ℤ U M) n]
  have hφ : conjHom U U 1 hU = ContinuousMonoidHom.id U :=
    ContinuousMonoidHom.ext fun u => Subtype.ext (by simp)
  -- Both coefficient maps are the identity of `M`.
  exact map_congr_of_hom_apply hφ _ _
    (fun (m : M) => (conjPair_hom_apply U U M 1 hU m).trans (one_smul G m)) n

/-- **Conjugation is multiplicative**: for `V = gUg⁻¹` and `W = hVh⁻¹`, conjugation by `g`
followed by conjugation by `h` is conjugation by `h * g`. -/
@[reassoc]
theorem conjMap_comp (g h : G) (hVU : V = U.map (MulAut.conj g).toMonoidHom)
    (hWV : W = V.map (MulAut.conj h).toMonoidHom)
    (hWU : W = U.map (MulAut.conj (h * g)).toMonoidHom) (n : ℕ) :
    conjMap U V M g hVU n ≫ conjMap V W M h hWV n = conjMap U W M (h * g) hWU n := by
  rw [conjMap_def, conjMap_def, conjMap_def, ← _root_.ContinuousCohomology.map_comp]
  have hφ : (conjHom U V g hVU).comp (conjHom V W h hWV) = conjHom U W (h * g) hWU :=
    ContinuousMonoidHom.ext fun w => Subtype.ext (by simp [mul_assoc])
  refine map_congr_of_hom_apply hφ _ _ (fun (m : M) => ?_) n
  -- Both coefficient maps are the action of `h * g` on `M`. `map_comp` types the composite
  -- `(resFunctor _).map _ ≫ _` at `TopRep.res (φ.comp ψ) _`, so this goal is not type-correct at
  -- instance transparency and `TopRep.comp_apply` cannot rewrite it; `change` evaluates it.
  change (conjPair V W M h hWV).hom ((conjPair U V M g hVU).hom m) = (conjPair U W M _ hWU).hom m
  rw [conjPair_hom_apply, conjPair_hom_apply, conjPair_hom_apply, smul_smul]

/-- Conjugation by `g` is an isomorphism `Hⁿ(U, M) ≅ Hⁿ(gUg⁻¹, M)`, with inverse conjugation by
`g⁻¹`. -/
instance isIso_conjMap (g : G) (hVU : V = U.map (MulAut.conj g).toMonoidHom) (n : ℕ) :
    IsIso (conjMap U V M g hVU n) := by
  -- Conjugation by an element equal to `1` is the identity.
  have hid (W : Subgroup G) (k : G) (hk : k = 1) (hW : W = W.map (MulAut.conj k).toMonoidHom) :
      conjMap W W M k hW n = 𝟙 _ := by
    subst hk
    exact conjMap_one W M n
  have hUV : U = V.map (MulAut.conj g⁻¹).toMonoidHom := by
    rw [hVU, Subgroup.map_conj_map_conj, inv_mul_cancel, map_one]
    exact (Subgroup.map_id U).symm
  have hVV : V = V.map (MulAut.conj (g * g⁻¹)).toMonoidHom := by
    rw [← Subgroup.map_conj_map_conj, ← hUV, hVU]
  have hUU : U = U.map (MulAut.conj (g⁻¹ * g)).toMonoidHom := by
    rw [← Subgroup.map_conj_map_conj, ← hVU, hUV]
  exact ⟨conjMap V U M g⁻¹ hUV n,
    (conjMap_comp U V U M g g⁻¹ hVU hUV hUU n).trans (hid U _ (inv_mul_cancel g) hUU),
    (conjMap_comp V U V M g⁻¹ g hUV hVU hVV n).trans (hid V _ (mul_inv_cancel g) hVV)⟩

/-- **Conjugation on a normal subgroup** is `conjNormalMap`: for a normal subgroup `V`,
conjugation from `V` to `gVg⁻¹ = V` is the endomorphism `(g)_*` of `Hⁿ(V, M)`. -/
@[simp]
theorem conjMap_eq_conjNormalMap [V.Normal] (g : G)
    (hV : V = V.map (MulAut.conj g).toMonoidHom) (n : ℕ) :
    conjMap V V M g hV n = conjNormalMap V M g n := by
  rw [conjMap_def, conjNormalMap_def]
  have hφ : conjHom V V g hV =
      ContinuousMonoidHom.toContinuousMonoidHom (ContinuousAut.conjNormal g⁻¹ : ContinuousAut V) :=
    ContinuousMonoidHom.ext fun v => Subtype.ext (by simp)
  -- Both coefficient maps are the action of `g` on `M`.
  exact map_congr_of_hom_apply hφ _ _
    (fun (m : M) =>
      (conjPair_hom_apply V V M g hV m).trans (conjNormalPair_hom_apply V M g m).symm) n

/-- **Conjugation is natural in the coefficients**: for a `G`-equivariant map `f : M → N`, the
coefficient maps of `f` commute with `(g)_*`. -/
@[reassoc]
theorem conjMap_naturality (N : Type u) [AddCommGroup N] [TopologicalSpace N]
    [DiscreteTopology N] [DistribMulAction G N] (f : M →+[G] N) (g : G)
    (hVU : V = U.map (MulAut.conj g).toMonoidHom) (n : ℕ) :
    conjMap U V M g hVU n ≫
        coeffMap (ofDiscreteModuleMap (G := V) f.toAddMonoidHom.toIntLinearMap
          fun v m => _root_.map_smul f (v : G) m) n =
      coeffMap (ofDiscreteModuleMap (G := U) f.toAddMonoidHom.toIntLinearMap
          fun u m => _root_.map_smul f (u : G) m) n ≫
        conjMap U V N g hVU n := by
  refine map_comp_coeffMap _ _ _ _ _ ?_ n
  refine TopRep.hom_ext (DFunLike.ext _ _ fun (m : M) => ?_)
  -- Both composites of `TopRep` morphisms evaluate as the composites of their underlying maps,
  -- by `change` as in `conjMap_comp`, and the coefficient map of `f` evaluates as `f`.
  change (conjPair U V N g hVU).hom (f m) =
    (ofDiscreteModuleMap (G := V) f.toAddMonoidHom.toIntLinearMap
      fun v m => _root_.map_smul f (v : G) m).hom ((conjPair U V M g hVU).hom m)
  rw [conjPair_hom_apply, conjPair_hom_apply]
  exact (_root_.map_smul f g m).symm

/-- **Conjugation commutes with restriction**: for `V = gUg⁻¹`, subgroups `U' ≤ U` and
`V' ≤ V` with `V' = gU'g⁻¹`, conjugation followed by restriction from `V` to `V'` is restriction
from `U` to `U'` followed by conjugation. -/
@[reassoc]
theorem conjMap_comp_resLE {U' V' : Subgroup G} (hU'U : U' ≤ U) (hV'V : V' ≤ V) (g : G)
    (hVU : V = U.map (MulAut.conj g).toMonoidHom)
    (hV'U' : V' = U'.map (MulAut.conj g).toMonoidHom) (n : ℕ) :
    conjMap U V M g hVU n ≫ resLE hV'V (ofDiscreteModule ℤ G M) n =
      resLE hU'U (ofDiscreteModule ℤ G M) n ≫ conjMap U' V' M g hV'U' n := by
  have hφ : (conjHom U V g hVU).comp (ContinuousMonoidHom.subgroupInclusion hV'V) =
      (ContinuousMonoidHom.subgroupInclusion hU'U).comp (conjHom U' V' g hV'U') :=
    ContinuousMonoidHom.ext fun v => Subtype.ext (by simp)
  rw [conjMap_def, conjMap_def, resLE_def, resLE_def]
  -- Write both sides as single compatible-pair maps.
  refine (_root_.ContinuousCohomology.map_comp (X := ofDiscreteModule ℤ U M) _
      (ContinuousMonoidHom.subgroupInclusion hV'V) (conjPair U V M g hVU) (𝟙 _) n).symm.trans
    ((map_congr_of_hom_apply hφ _ _ (fun (m : M) => ?_) n).trans
      (_root_.ContinuousCohomology.map_comp (X := ofDiscreteModule ℤ U M)
        (ContinuousMonoidHom.subgroupInclusion hU'U) _ (𝟙 _) (conjPair U' V' M g hV'U') n))
  -- Both coefficient maps are the action of `g` on `M`; the composites of `TopRep` morphisms
  -- evaluate as the composites of the underlying maps, by `change` as in `conjMap_comp`.
  change (conjPair U V M g hVU).hom m = (conjPair U' V' M g hV'U').hom m
  rw [conjPair_hom_apply, conjPair_hom_apply]

/-- **Conjugation by an element of the subgroup is trivial**: for `g ∈ U`, conjugation
`(g)_* : Hⁿ(U, M) ⟶ Hⁿ(gUg⁻¹, M) = Hⁿ(U, M)` is the identity. This is the triviality of inner
automorphisms on continuous cohomology, `map_eq_id_of_inner`, for the group `U`. -/
theorem conjMap_eq_id_of_mem [ContinuousSMul U M] [LocallyCompactSpace U] {g : G} (hg : g ∈ U)
    (hU : U = U.map (MulAut.conj g).toMonoidHom) (n : ℕ) :
    conjMap U U M g hU n = 𝟙 _ :=
  map_eq_id_of_inner (⟨g, hg⟩ : U) (conjHom U U g hU) (fun u => Subtype.ext (by simp))
    (conjPair U U M g hU) (conjPair_hom_apply U U M g hU)
    (ofDiscreteModule_isSmoothDiscrete ℤ U M) n

section ContinuousAction

variable [ContinuousSMul G M]

/-- **Restriction from `G` followed by conjugation is restriction**: for `V = gUg⁻¹`, restricting a
class of `Hⁿ(G, M)` to `U` and conjugating by `g` gives its restriction to `V`, because conjugation
by `g` acts trivially on `Hⁿ(G, M)`. -/
-- `@[simp]` only on this form: `simp` already proves the reassociated form from it.
@[simp, reassoc]
theorem res_comp_conjMap [LocallyCompactSpace G] (g : G)
    (hVU : V = U.map (MulAut.conj g).toMonoidHom) (n : ℕ) :
    res U (ofDiscreteModule ℤ G M) n ≫ conjMap U V M g hVU n =
      res V (ofDiscreteModule ℤ G M) n := by
  -- Insert the inner compatible pair `(x ↦ g⁻¹ x g, m ↦ g • m)` of `G`, which induces the
  -- identity.
  let c : G →ₜ* G := ContinuousMonoidHom.toContinuousMonoidHom (ContinuousAut.conj g⁻¹)
  have hc (x : G) : c x = g⁻¹ * x * g := by simp [c]
  let B : TopRep.res (c : G →* G) (ofDiscreteModule ℤ G M) ⟶ ofDiscreteModule ℤ G M :=
    ofDiscreteModulePair (c : G →* G) (DistribSMul.toAddMonoidHom M g).toIntLinearMap
      fun x m => by
        have hx : (c : G →* G) x = g⁻¹ * x * g := hc x
        simp only [AddMonoidHom.coe_toIntLinearMap, DistribSMul.toAddMonoidHom_apply, hx,
          smul_smul]
        congr 1
        group
  have hBm (m : M) : B.hom m = g • m := ofDiscreteModulePair_hom_apply _ _ _ m
  have hB : _root_.ContinuousCohomology.map c B n = 𝟙 _ :=
    map_eq_id_of_inner g c hc B hBm (ofDiscreteModule_isSmoothDiscrete ℤ G M) n
  have hφ : (ContinuousMonoidHom.subgroupSubtype U).comp (conjHom U V g hVU) =
      c.comp (ContinuousMonoidHom.subgroupSubtype V) :=
    ContinuousMonoidHom.ext fun v => by simp [hc]
  rw [← Category.id_comp (res V (ofDiscreteModule ℤ G M) n), ← hB, res_def, res_def, conjMap_def]
  -- Write both sides as single compatible-pair maps.
  refine (_root_.ContinuousCohomology.map_comp (X := ofDiscreteModule ℤ G M)
      (ContinuousMonoidHom.subgroupSubtype U) _ (𝟙 _) (conjPair U V M g hVU) n).symm.trans
    ((map_congr_of_hom_apply hφ _ _ (fun (m : M) => ?_) n).trans
      (_root_.ContinuousCohomology.map_comp (X := ofDiscreteModule ℤ G M) c
        (ContinuousMonoidHom.subgroupSubtype V) B (𝟙 _) n))
  -- Both coefficient maps are the action of `g` on `M`; the composites of `TopRep` morphisms
  -- evaluate as the composites of the underlying maps, by `change` as in `conjMap_comp`.
  change (conjPair U V M g hVU).hom m = B.hom m
  exact (conjPair_hom_apply U V M g hVU m).trans (hBm m).symm

/-- **Corestriction is invariant under conjugation**: for open subgroups `U` and `V = gUg⁻¹` of
finite index in a profinite group, corestriction from `V` after `(g)_*` is corestriction from `U`,
in every degree. -/
@[reassoc (attr := simp)]
theorem conjMap_comp_corestriction [CompactSpace G] [TotallyDisconnectedSpace G]
    (hU : IsOpen (U : Set G)) [U.FiniteIndex] (hV : IsOpen (V : Set G)) [V.FiniteIndex] (g : G)
    (hVU : V = U.map (MulAut.conj g).toMonoidHom) (n : ℕ) :
    conjMap U V M g hVU n ≫ corestriction V M hV n = corestriction U M hU n :=
  map_comp_corestriction_of_conj U V M g (conjHom U V g hVU) (coe_conjHom_apply U V g hVU)
    (conjPair U V M g hVU) (conjPair_hom_apply U V M g hVU) hVU hU hV n

end ContinuousAction

end TauCeti.ContinuousCohomology
