/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicGeometry.Birational.Composition
public import Mathlib.AlgebraicGeometry.Noetherian
public import TauCeti.AlgebraicGeometry.Morphisms.Modification.GraphClosure
public import TauCeti.AlgebraicGeometry.Scheme.KrullDimension

/-!
# The correspondence of a composite of rational maps

Let `f : X ⤏ Y` be a dominant rational map and `g : Y ⤏ Z` a rational map, all over a base `S`,
with `X` reduced and `Y`, `Z` separated. Let `U` be the intersection of the domains of definition
of `f` and of `g ∘ f`, a dense open of `X`, and let `f_U` and `(g ∘ f)_U` be the restrictions to
`U` of the representatives of `f` and `g ∘ f` on their domains. The *correspondence of the
composite* `W_{f,g}` is the scheme-theoretic image of `(ι_U, f_U, (g ∘ f)_U) : U → X ×_S Y ×_S Z`,
with `X ×_S Y ×_S Z` written as `X ×_S (Y ×_S Z)`. It is Tau Ceti's graph closure
`TauCeti.AlgebraicGeometry.graphClosure` of `(f_U, (g ∘ f)_U) : U → Y ×_S Z`, so the graph
closure API applies to it.

For `X` Noetherian and integral, `W_{f,g}` is integral (no integrality of `Y ×_S Z` is used), and
replacing `U` by a smaller dense open does not change it. Over a field `K`, for `X`, `Y`, `Z`
locally of finite type, `W_{f,g}` has the dimension of `X`: the first projection is an isomorphism
over `U`, so `U` is a nonempty open of the irreducible `W_{f,g}`.

## Main definitions

* `AlgebraicGeometry.Scheme.RationalMap.compositeDomain`: the open `U`.
* `AlgebraicGeometry.Scheme.RationalMap.compositeLift`: the morphism `(f_U, (g ∘ f)_U)`.
* `AlgebraicGeometry.Scheme.RationalMap.compositeCorrespondence`: the correspondence `W_{f,g}`,
  with its closed immersion `compositeCorrespondenceι` into `X ×_S (Y ×_S Z)`, its projections
  `compositeCorrespondenceFst`, `compositeCorrespondenceSndY`, `compositeCorrespondenceSndZ`, and
  the factorization `toCompositeCorrespondence` of `U` through it.

## Main results

* `AlgebraicGeometry.Scheme.RationalMap.isIntegral_compositeCorrespondence`: `W_{f,g}` is
  integral.
* `AlgebraicGeometry.Scheme.RationalMap.ker_homOfLE_comp_opensGraph_compositeLift`: the image of
  the restriction to a smaller dense open is `W_{f,g}`.
* `AlgebraicGeometry.Scheme.RationalMap.topologicalKrullDim_compositeCorrespondence`: over a
  field, `W_{f,g}` has the dimension of `X`.
-/

public section

open CategoryTheory Limits TopologicalSpace TauCeti.AlgebraicGeometry

noncomputable section

namespace AlgebraicGeometry.Scheme.RationalMap

universe u

variable {S X Y Z : Scheme.{u}} (sX : X ⟶ S) (sY : Y ⟶ S) (sZ : Z ⟶ S)
  [IsReduced X] [PreirreducibleSpace X] [Nonempty Y] [Y.IsSeparated] [Z.IsSeparated]
  (f : X ⤏ Y) [f.IsDominant] (g : Y ⤏ Z)

/-- The open `U` on which the correspondence of the composite is cut out: the intersection of the
domains of definition of `f` and of `g ∘ f`. -/
def compositeDomain : X.Opens :=
  f.domain ⊓ (f.comp g).domain

omit [IsReduced X] [Y.IsSeparated] [Z.IsSeparated] in
/-- The open `U` is dense in `X`. -/
theorem dense_compositeDomain : Dense (compositeDomain f g : Set X) :=
  f.dense_domain.inter_of_isOpen_left (f.comp g).dense_domain f.domain.isOpen

/-- The restriction `f_U` of the representative of `f` on its domain to `U`. -/
def compositeFst : (compositeDomain f g).toScheme ⟶ Y :=
  X.homOfLE (show compositeDomain f g ≤ f.toPartialMap.domain from inf_le_left) ≫
    f.toPartialMap.hom

/-- The restriction `(g ∘ f)_U` of the representative of `g ∘ f` on its domain to `U`. -/
def compositeSnd : (compositeDomain f g).toScheme ⟶ Z :=
  X.homOfLE (show compositeDomain f g ≤ (f.comp g).toPartialMap.domain from inf_le_right) ≫
    (f.comp g).toPartialMap.hom

section Over

variable [S.IsSeparated] [f.IsOver sX sY] [(f.comp g).IsOver sX sZ]

omit [Z.IsSeparated] in
/-- `f_U` is a morphism over `S`. -/
theorem compositeFst_comp : compositeFst f g ≫ sY = (compositeDomain f g).ι ≫ sX := by
  rw [compositeFst, Category.assoc, f.toPartialMap.over sX sY, Scheme.homOfLE_ι_assoc]

omit [Y.IsSeparated] in
/-- `(g ∘ f)_U` is a morphism over `S`. -/
theorem compositeSnd_comp : compositeSnd f g ≫ sZ = (compositeDomain f g).ι ≫ sX := by
  rw [compositeSnd, Category.assoc, (f.comp g).toPartialMap.over sX sZ,
    Scheme.homOfLE_ι_assoc]

/-- The morphism `(f_U, (g ∘ f)_U) : U → Y ×_S Z`. -/
def compositeLift : (compositeDomain f g).toScheme ⟶ pullback sY sZ :=
  pullback.lift (compositeFst f g) (compositeSnd f g)
    ((compositeFst_comp sX sY f g).trans (compositeSnd_comp sX sZ f g).symm)

@[reassoc (attr := simp)]
theorem compositeLift_fst : compositeLift sX sY sZ f g ≫ pullback.fst sY sZ = compositeFst f g :=
  pullback.lift_fst _ _ _

@[reassoc (attr := simp)]
theorem compositeLift_snd : compositeLift sX sY sZ f g ≫ pullback.snd sY sZ = compositeSnd f g :=
  pullback.lift_snd _ _ _

/-- `(f_U, (g ∘ f)_U)` is a morphism over `S`. -/
theorem compositeLift_comp :
    compositeLift sX sY sZ f g ≫ pullback.fst sY sZ ≫ sY = (compositeDomain f g).ι ≫ sX := by
  rw [compositeLift_fst_assoc, compositeFst_comp sX]

/-- The *correspondence of the composite* `W_{f,g}`: the scheme-theoretic image of
`(ι_U, f_U, (g ∘ f)_U) : U → X ×_S (Y ×_S Z)`, the graph closure of `compositeLift`. -/
abbrev compositeCorrespondence : Scheme.{u} :=
  graphClosure sX (pullback.fst sY sZ ≫ sY) (compositeDomain f g) (compositeLift sX sY sZ f g)
    (compositeLift_comp sX sY sZ f g)

/-- The closed immersion of `W_{f,g}` into `X ×_S (Y ×_S Z)`. -/
abbrev compositeCorrespondenceι :
    compositeCorrespondence sX sY sZ f g ⟶ pullback sX (pullback.fst sY sZ ≫ sY) :=
  (opensGraph sX (pullback.fst sY sZ ≫ sY) (compositeDomain f g) (compositeLift sX sY sZ f g)
    (compositeLift_comp sX sY sZ f g)).imageι

/-- The projection `q_X : W_{f,g} → X`. -/
abbrev compositeCorrespondenceFst : compositeCorrespondence sX sY sZ f g ⟶ X :=
  graphClosureFst sX (pullback.fst sY sZ ≫ sY) (compositeDomain f g)
    (compositeLift sX sY sZ f g) (compositeLift_comp sX sY sZ f g)

/-- The projection `q_Y : W_{f,g} → Y`. -/
abbrev compositeCorrespondenceSndY : compositeCorrespondence sX sY sZ f g ⟶ Y :=
  graphClosureSnd sX (pullback.fst sY sZ ≫ sY) (compositeDomain f g)
    (compositeLift sX sY sZ f g) (compositeLift_comp sX sY sZ f g) ≫ pullback.fst sY sZ

/-- The projection `q_Z : W_{f,g} → Z`. -/
abbrev compositeCorrespondenceSndZ : compositeCorrespondence sX sY sZ f g ⟶ Z :=
  graphClosureSnd sX (pullback.fst sY sZ ≫ sY) (compositeDomain f g)
    (compositeLift sX sY sZ f g) (compositeLift_comp sX sY sZ f g) ≫ pullback.snd sY sZ

/-- The factorization `U → W_{f,g}` of `(ι_U, f_U, (g ∘ f)_U)`. -/
abbrev toCompositeCorrespondence :
    (compositeDomain f g).toScheme ⟶ compositeCorrespondence sX sY sZ f g :=
  toGraphClosure sX (pullback.fst sY sZ ≫ sY) (compositeDomain f g)
    (compositeLift sX sY sZ f g) (compositeLift_comp sX sY sZ f g)

/-- `q_Y` restricts to `f_U` on `U`. -/
@[reassoc]
theorem toCompositeCorrespondence_sndY :
    toCompositeCorrespondence sX sY sZ f g ≫ compositeCorrespondenceSndY sX sY sZ f g =
      compositeFst f g := by
  simp

/-- `q_Z` restricts to `(g ∘ f)_U` on `U`. -/
@[reassoc]
theorem toCompositeCorrespondence_sndZ :
    toCompositeCorrespondence sX sY sZ f g ≫ compositeCorrespondenceSndZ sX sY sZ f g =
      compositeSnd f g := by
  simp

section Noetherian

variable [NoetherianSpace X]

instance quasiCompact_compositeDomain_ι : QuasiCompact (compositeDomain f g).ι :=
  have : NoetherianSpace (compositeDomain f g) :=
    NoetherianSpace.set (compositeDomain f g : Set X)
  quasiCompact_of_noetherianSpace_source _

/-- The open `U` is nonempty when `X` is: it is dense. -/
instance nonempty_compositeDomain [Nonempty X] : Nonempty (compositeDomain f g) :=
  (dense_compositeDomain f g).nonempty.to_subtype

/-- The correspondence of the composite is integral when `X` is a Noetherian integral scheme:
it is the scheme-theoretic image of the quasi-compact morphism `(ι_U, f_U, (g ∘ f)_U)` from the
integral scheme `U`. No integrality of `Y ×_S Z` is used. -/
theorem isIntegral_compositeCorrespondence [IsIntegral X] :
    IsIntegral (compositeCorrespondence sX sY sZ f g) :=
  inferInstance

omit [NoetherianSpace X] in
/-- **Independence of the open.** For a dense open `V ⊆ U`, the scheme-theoretic image of the
restriction of `(ι_U, f_U, (g ∘ f)_U)` to `V` is `W_{f,g}`: the two morphisms have the same
kernel. -/
theorem ker_homOfLE_comp_opensGraph_compositeLift {V : X.Opens} (hV : Dense (V : Set X))
    (hVU : V ≤ compositeDomain f g) :
    (X.homOfLE hVU ≫ opensGraph sX (pullback.fst sY sZ ≫ sY) (compositeDomain f g)
        (compositeLift sX sY sZ f g) (compositeLift_comp sX sY sZ f g)).ker =
      (opensGraph sX (pullback.fst sY sZ ≫ sY) (compositeDomain f g)
        (compositeLift sX sY sZ f g) (compositeLift_comp sX sY sZ f g)).ker := by
  have : IsDominant (X.homOfLE hVU) := by
    refine ⟨?_⟩
    rw [DenseRange, ← Scheme.Hom.coe_opensRange, Scheme.opensRange_homOfLE]
    exact hV.preimage (compositeDomain f g).ι.isOpenEmbedding.isOpenMap
  have := IsSchemeTheoreticallyDominant.of_isDominant (X.homOfLE hVU)
  exact Scheme.Hom.ker_comp_of_isSchemeTheoreticallyDominant _ _

end Noetherian

end Over

section Field

variable {K : Type u} [Field K] (sX : X ⟶ Spec (.of K)) (sY : Y ⟶ Spec (.of K))
  (sZ : Z ⟶ Spec (.of K)) [f.IsOver sX sY] [(f.comp g).IsOver sX sZ]
  [NoetherianSpace X] [IsIntegral X]
  [LocallyOfFiniteType sX] [LocallyOfFiniteType sY] [LocallyOfFiniteType sZ]

/-- **The dimension of the correspondence.** Over a field, for `X`, `Y`, `Z` locally of finite
type, `W_{f,g}` has the dimension of `X`. The first projection is an isomorphism over `U`, so `U`
is a nonempty open of the irreducible `W_{f,g}`. -/
theorem topologicalKrullDim_compositeCorrespondence :
    topologicalKrullDim (compositeCorrespondence sX sY sZ f g) = topologicalKrullDim X := by
  have H := range_toGraphClosure_subset_preimage (hg := compositeLift_comp sX sY sZ f g)
    (le_refl (compositeDomain f g))
  let l := IsOpenImmersion.lift
    (compositeCorrespondenceFst sX sY sZ f g ⁻¹ᵁ compositeDomain f g).ι
    (toCompositeCorrespondence sX sY sZ f g) (by rwa [Scheme.Opens.range_ι])
  have hl : l ≫ (compositeCorrespondenceFst sX sY sZ f g ∣_ compositeDomain f g) = 𝟙 _ := by
    rw [lift_graphClosureFst_restrict le_rfl, Scheme.homOfLE_rfl]
  have : IsIso (l ≫ (compositeCorrespondenceFst sX sY sZ f g ∣_ compositeDomain f g)) :=
    hl ▸ inferInstance
  have : IsIso l := IsIso.of_isIso_comp_right l
    (compositeCorrespondenceFst sX sY sZ f g ∣_ compositeDomain f g)
  have hU : Topology.IsOpenEmbedding (toCompositeCorrespondence sX sY sZ f g) := by
    rw [← IsOpenImmersion.lift_fac
      (compositeCorrespondenceFst sX sY sZ f g ⁻¹ᵁ compositeDomain f g).ι
      (toCompositeCorrespondence sX sY sZ f g) (by rwa [Scheme.Opens.range_ι])]
    exact (l ≫ (compositeCorrespondenceFst sX sY sZ f g ⁻¹ᵁ compositeDomain f g).ι).isOpenEmbedding
  rw [(topologicalKrullDim_eq_of_isOpenEmbedding_of_locallyOfFiniteType
      (compositeCorrespondenceFst sX sY sZ f g ≫ sX) hU).symm,
    topologicalKrullDim_eq_of_isOpenEmbedding_of_locallyOfFiniteType sX
      (compositeDomain f g).ι.isOpenEmbedding]

end Field

end AlgebraicGeometry.Scheme.RationalMap
