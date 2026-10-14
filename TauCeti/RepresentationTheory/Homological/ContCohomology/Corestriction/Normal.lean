/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Homological.ContCohomology.Corestriction.Conjugation

/-!
# Restriction of corestriction from a normal subgroup

Let `U` be an open normal subgroup of finite index in a profinite group `G`, and `M` a discrete
`G`-module. Restriction back to `U` of the corestriction from `U` is the norm of the conjugation
action of `G ⧸ U` on the cohomology of `U`, in every degree `n`:

```text
res^G_U ∘ cor^G_U = ∑_{gU ∈ G ⧸ U} (g)_* : Hⁿ(U, M) ⟶ Hⁿ(U, M),
```

for any choice of representatives `g` of the cosets, where `(g)_*` is the conjugation
`TauCeti.ContinuousCohomology.conjNormalMap`. This is the case `V = U` of the Mackey double-coset
formula, in which every double coset is a single coset and every Mackey subgroup is `U` itself.
In degree one on the explicit model it is
`TauCeti.ContCohomology.explicitRes1_explicitCor1_of_normal`.

## Main results

* `TauCeti.ContinuousCohomology.corestriction_comp_res_eq_sum_conjNormalMap`: for an open normal
  subgroup `U`, `res ∘ cor` is the sum of the conjugations `(g)_*` over a transversal of `G ⧸ U`.
* `TauCeti.trivialF2CorMap_comp_trivialF2ResMap_eq_sum`: the same statement with trivial `𝔽₂`
  coefficients, where `(g)_*` is pullback along the conjugation `u ↦ g⁻¹ u g` of `U`.

## References

* K. S. Brown, *Cohomology of Groups*, Chapter III, (9.5)(ii).
* J. Neukirch, A. Schmidt, K. Wingberg, *Cohomology of Number Fields*, 2nd ed., (1.5.6).
-/

public section

open CategoryTheory

namespace TauCeti.ContinuousCohomology

open TauCeti.ContCohomology

universe u

attribute [local instance] Subgroup.fintypeQuotientOfFiniteIndex

variable {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [CompactSpace G] [TotallyDisconnectedSpace G]
  (U : Subgroup G) [U.Normal] (M : Type u) [AddCommGroup M] [TopologicalSpace M]
  [DiscreteTopology M] [DistribMulAction G M] [ContinuousSMul G M]
  (hU : IsOpen (U : Set G)) [U.FiniteIndex]

omit [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G] [TotallyDisconnectedSpace G]
  [U.FiniteIndex] in
/-- A normal subgroup `U` lies in its conjugate `gUg⁻¹`, stated with `MulEquiv.toMonoidHom` as
`DiscreteCoind.conj` takes it; Mathlib's `Subgroup.Normal.map_conj_eq` uses the `MonoidHomClass`
coercion instead, which is the same map up to definitional unfolding. -/
private theorem le_map_conj_toMonoidHom (g : G) : U ≤ U.map (MulAut.conj g).toMonoidHom :=
  (Subgroup.Normal.map_conj_eq U g).ge

/-- The conjugation `f ↦ (x ↦ g • f (g⁻¹ x))` of `Coind_U^G M`, for normal `U`, as an endomorphism
of its coefficient object. Shapiro's map carries its coefficient map to `(g)_*`
(`shapiroMap_comp_conjNormalMap`). -/
private noncomputable abbrev conjCoind (g : G) :
    ofDiscreteModule ℤ G (DiscreteCoind G U M) ⟶ ofDiscreteModule ℤ G (DiscreteCoind G U M) :=
  ofDiscreteModuleMap
    (DiscreteCoind.conj U U M g (le_map_conj_toMonoidHom U g)).toAddMonoidHom.toIntLinearMap
    fun h F => _root_.map_smul (DiscreteCoind.conj U U M g (le_map_conj_toMonoidHom U g)) h F

omit [CompactSpace G] [TotallyDisconnectedSpace G] in
/-- **The trace followed by the unit is the norm of conjugation** on `Coind_U^G M`, for normal `U`
and any transversal `t` of `G ⧸ U`. -/
private theorem trace_comp_unit_eq_sum_conjCoind (t : G ⧸ U → G)
    (ht : ∀ x : G ⧸ U, (t x : G ⧸ U) = x) :
    ofDiscreteModuleMap (DiscreteCoind.trace G U M).toAddMonoidHom.toIntLinearMap
        (fun g f => _root_.map_smul (DiscreteCoind.trace G U M) g f) ≫
      ofDiscreteModuleMap (DiscreteCoind.unit G U M).toAddMonoidHom.toIntLinearMap
        (fun g m => _root_.map_smul (DiscreteCoind.unit G U M) g m) =
      ∑ x, conjCoind U M (t x) := by
  refine TopRep.hom_ext (DFunLike.ext _ _ fun (Φ : DiscreteCoind G U M) =>
    DiscreteCoind.ext fun y => ?_)
  -- Evaluation at `Φ` and then at `y` is additive in the morphism.
  let ev : (ofDiscreteModule ℤ G (DiscreteCoind G U M) ⟶
      ofDiscreteModule ℤ G (DiscreteCoind G U M)) →+ M :=
    AddMonoidHom.mk' (fun f => DFunLike.coe (F := DiscreteCoind G U M) (f.hom Φ) y)
      fun _ _ => rfl
  have hl : DFunLike.coe (F := DiscreteCoind G U M)
      ((ofDiscreteModuleMap (DiscreteCoind.trace G U M).toAddMonoidHom.toIntLinearMap
          (fun g f => _root_.map_smul (DiscreteCoind.trace G U M) g f) ≫
        ofDiscreteModuleMap (DiscreteCoind.unit G U M).toAddMonoidHom.toIntLinearMap
          (fun g m => _root_.map_smul (DiscreteCoind.unit G U M) g m)).hom Φ) y =
      y • DiscreteCoind.trace G U M Φ :=
    DiscreteCoind.unit_apply _ y
  refine hl.trans (Eq.trans ?_ (map_sum ev _ _).symm)
  rw [DiscreteCoind.trace_eq_sum_transversal (fun x => y⁻¹ * t (y • x))
      (fun x => by rw [← smul_eq_mul, ← MulAction.Quotient.smul_mk, ht, inv_smul_smul]),
    Finset.smul_sum]
  refine (Finset.sum_congr rfl fun x _ => ?_).trans
    (Equiv.sum_comp (MulAction.toPerm y : Equiv.Perm (G ⧸ U)) fun x => ev (conjCoind U M (t x)))
  rw [smul_smul, mul_inv_rev, inv_inv, mul_inv_cancel_left]
  exact (DiscreteCoind.conj_apply _ _ Φ y).symm

/-- **Restriction of corestriction from a normal subgroup** (Brown III (9.5)(ii)). For an open
normal subgroup `U` of finite index in a profinite group `G`, a discrete `G`-module `M` and any
transversal `t` of `G ⧸ U`, restriction to `U` of the corestriction from `U` is the sum of the
conjugations `(t x)_*` on `Hⁿ(U, M)`, in every degree:

```text
res^G_U ∘ cor^G_U = ∑_{x ∈ G ⧸ U} (t x)_*.
```
-/
theorem corestriction_comp_res_eq_sum_conjNormalMap (t : G ⧸ U → G)
    (ht : ∀ x : G ⧸ U, (t x : G ⧸ U) = x) (n : ℕ) :
    corestriction U M hU n ≫ res U (ofDiscreteModule ℤ G M) n =
      ∑ x, conjNormalMap U M (t x) n := by
  have := isIso_shapiroMap U (U.isClosed_of_isOpen hU) M n
  -- After the Shapiro isomorphism of `U`, both sides are coefficient maps followed by the Shapiro
  -- map of `U`, and the two coefficient maps agree by `trace_comp_unit_eq_sum_conjCoind`.
  -- The two sides are compared in term mode: their codomains `Hⁿ(U, res_U M)` and `Hⁿ(U, M)`
  -- agree only up to `res_ofDiscreteModule`, which stops `rw` from abstracting them.
  have hleft : shapiroMap U M n ≫ corestriction U M hU n ≫ res U (ofDiscreteModule ℤ G M) n =
      coeffMap (ofDiscreteModuleMap (DiscreteCoind.trace G U M).toAddMonoidHom.toIntLinearMap
          (fun g f => _root_.map_smul (DiscreteCoind.trace G U M) g f) ≫
        ofDiscreteModuleMap (DiscreteCoind.unit G U M).toAddMonoidHom.toIntLinearMap
          (fun g m => _root_.map_smul (DiscreteCoind.unit G U M) g m)) n ≫ shapiroMap U M n :=
    (shapiroMap_comp_corestriction_assoc U M hU n _).trans <| by
      rw [coeffMap_comp, Category.assoc]
      exact congrArg _ (coeffMap_unit_comp_shapiroMap U M n).symm
  have hright : shapiroMap U M n ≫ ∑ x, conjNormalMap U M (t x) n =
      coeffMap (∑ x, conjCoind U M (t x)) n ≫ shapiroMap U M n := by
    have hsum := (continuousCohomologyFunctor ℤ G n).map_sum
      (fun x => conjCoind U M (t x)) Finset.univ
    simp only [continuousCohomologyFunctor_map] at hsum
    rw [Preadditive.comp_sum, hsum]
    exact (Finset.sum_congr rfl fun x _ =>
      shapiroMap_comp_conjNormalMap U M (t x) n).trans (Preadditive.sum_comp _ _ _).symm
  exact (cancel_epi (shapiroMap U M n)).1 (hleft.trans ((congrArg (coeffMap · n ≫ _)
    (trace_comp_unit_eq_sum_conjCoind U M t ht)).trans hright.symm))

end TauCeti.ContinuousCohomology

/-! ### Trivial `𝔽₂` coefficients -/

namespace TauCeti

open TauCeti.ContinuousCohomology

universe u

attribute [local instance] Subgroup.fintypeQuotientOfFiniteIndex TopRep.distribMulAction
  continuousSMul_trivialF2

variable {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [CompactSpace G] [TotallyDisconnectedSpace G]
  (U : Subgroup G) [U.Normal] (hU : IsOpen (U : Set G)) [U.FiniteIndex]

omit [CompactSpace G] [TotallyDisconnectedSpace G] [U.FiniteIndex] in
/-- With trivial coefficients, the conjugation `(g)_*` of `Hⁿ(U, 𝔽₂)`, read through the
identification of `ofDiscreteModule ℤ U (trivialF2 G).V` with `trivialF2 U`, is pullback along
`u ↦ g⁻¹ u g`. -/
private theorem eqToHom_conjNormalMap_eqToHom (g : G) (n : ℕ) :
    eqToHom (congrArg (continuousCohomology n) (ofDiscreteModule_subgroup_trivialF2 G U).symm) ≫
        conjNormalMap U (trivialF2 G).V g n ≫
          eqToHom (congrArg (continuousCohomology n) (ofDiscreteModule_subgroup_trivialF2 G U)) =
      trivialF2Map (ContinuousMonoidHom.toContinuousMonoidHom
        (ContinuousAut.conjNormal g⁻¹ : ContinuousAut U)) n := by
  have hM := ofDiscreteModule_subgroup_trivialF2 G U
  rw [conjNormalMap_eq_map_of_smul_eq_self _ _
      (fun g m => (TopRep.distribMulAction_smul _ g m).trans (trivialF2_ρ_apply_apply G g m)),
    ← cancel_epi (eqToHom (congrArg (continuousCohomology n) hM)), eqToHom_trans_assoc,
    eqToHom_refl, Category.id_comp]
  exact (eqToHom_comp_trivialF2Map _ hM hM (AddMonoidHom.id _) _ (fun _ => rfl) n).symm

/-- **Restriction of corestriction from a normal subgroup, with trivial `𝔽₂` coefficients**: for an
open normal subgroup `U` of finite index and any transversal `t` of `G ⧸ U`, restriction of the
corestriction from `U` is the sum over `x ∈ G ⧸ U` of the pullbacks along the conjugations
`u ↦ (t x)⁻¹ u (t x)` of `U`, in every degree. -/
theorem trivialF2CorMap_comp_trivialF2ResMap_eq_sum (t : G ⧸ U → G)
    (ht : ∀ x : G ⧸ U, (t x : G ⧸ U) = x) (n : ℕ) :
    trivialF2CorMap G U hU n ≫ trivialF2ResMap G U n =
      ∑ x, trivialF2Map (ContinuousMonoidHom.toContinuousMonoidHom
        (ContinuousAut.conjNormal (t x)⁻¹ : ContinuousAut U)) n := by
  let M := (trivialF2 G).V
  have hM := ofDiscreteModule_subgroup_trivialF2 G U
  -- Restriction with trivial coefficients is restriction of `ofDiscreteModule ℤ G M`, read through
  -- the identifications of the coefficient objects; generalize the target object so that its
  -- identification with the model can be substituted away.
  have hres : ∀ (X : TopRep ℤ G) (hX : ofDiscreteModule ℤ G M = X)
      (hX' : TopRep.res (U.subtype : U →* G) X = trivialF2 U),
      eqToHom (congrArg (continuousCohomology n) hX) ≫ res U X n ≫
          eqToHom (congrArg (continuousCohomology n) hX') =
        res U (ofDiscreteModule ℤ G M) n ≫ eqToHom (congrArg (continuousCohomology n) hM) := by
    rintro X rfl hX'
    rw [eqToHom_refl, Category.id_comp]
  rw [trivialF2CorMap_def, trivialF2ResMap_def, Category.assoc, Category.assoc,
    hres _ (ofDiscreteModule_trivialF2 G) (res_trivialF2 G U)]
  simp only [← eqToHom_conjNormalMap_eqToHom, ← Preadditive.comp_sum, ← Preadditive.sum_comp]
  -- Compared in term mode: the codomains `Hⁿ(U, res_U M)` and `Hⁿ(U, M)` of `res ∘ cor` and of
  -- the sum of the conjugations agree only up to `res_ofDiscreteModule`.
  exact congrArg (eqToHom _ ≫ ·) ((Category.assoc _ _ _).symm.trans (congrArg (· ≫ eqToHom _)
    (corestriction_comp_res_eq_sum_conjNormalMap U M hU t ht n)))

end TauCeti
