/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicGeometry.Birational.Composition
public import Mathlib.AlgebraicGeometry.Noetherian
public import TauCeti.AlgebraicGeometry.Birational.RationalMap.ValuationRing
public import TauCeti.AlgebraicGeometry.Morphisms.Modification.GraphClosure

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

For `X` locally Noetherian and integral, `W_{f,g}` is integral: instance search finds this
through the graph closure, from `AlgebraicGeometry.Scheme.Hom.isIntegral_image`. For `X` reduced,
restricting `(ι_U, f_U, (g ∘ f)_U)` to a dense open `V ⊆ U` gives the graph of the restriction of
`compositeLift` to `V` (`TauCeti.AlgebraicGeometry.homOfLE_comp_opensGraph`), which has the same
kernel, hence the same scheme-theoretic image `W_{f,g}`
(`TauCeti.AlgebraicGeometry.ker_opensGraph_homOfLE_comp`).
Over a field `K`, for `X` integral and `X`, `Y`, `Z` locally of finite type, `W_{f,g}` has the
dimension of `X`.

## Main definitions

* `AlgebraicGeometry.Scheme.RationalMap.compositeDomain`: the open `U`.
* `AlgebraicGeometry.Scheme.RationalMap.compositeToY`,
  `AlgebraicGeometry.Scheme.RationalMap.compositeToZ`: the morphisms `f_U` and `(g ∘ f)_U`.
* `AlgebraicGeometry.Scheme.RationalMap.compositeLift`: the morphism `(f_U, (g ∘ f)_U)`.
* `AlgebraicGeometry.Scheme.RationalMap.compositeCorrespondence`: the correspondence `W_{f,g}`,
  with its closed immersion `compositeCorrespondenceι` into `X ×_S (Y ×_S Z)`, its projections
  `compositeCorrespondenceFst`, `compositeCorrespondenceSndY`, `compositeCorrespondenceSndZ`, and
  the factorization `toCompositeCorrespondence` of `U` through it.

## Main results

* `AlgebraicGeometry.Scheme.RationalMap.topologicalKrullDim_compositeCorrespondence`: over a
  field, for `X` integral and `X`, `Y`, `Z` locally of finite type, `W_{f,g}` has the dimension
  of `X`.

## References

* N.-B. Dang, *Degrees of iterates of rational maps on normal projective varieties*, Proc. London
  Math. Soc. 121 (2020), [arXiv:1701.07760](https://arxiv.org/abs/1701.07760), §5 and
  diagram (5.1).
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
/-- The open `U` is the intersection of the domains of definition of `f` and of `g ∘ f`. -/
theorem compositeDomain_def : compositeDomain f g = f.domain ⊓ (f.comp g).domain := (rfl)

omit [IsReduced X] [Y.IsSeparated] [Z.IsSeparated] in
/-- The open `U` lies in the domain of definition of `f`. -/
theorem compositeDomain_le_domain : compositeDomain f g ≤ f.domain :=
  inf_le_left

omit [IsReduced X] [Y.IsSeparated] [Z.IsSeparated] in
/-- The open `U` lies in the domain of definition of `g ∘ f`. -/
theorem compositeDomain_le_domain_comp : compositeDomain f g ≤ (f.comp g).domain :=
  inf_le_right

omit [IsReduced X] [Y.IsSeparated] [Z.IsSeparated] in
/-- The open `U` is dense in `X`. -/
theorem dense_compositeDomain : Dense (compositeDomain f g : Set X) :=
  f.dense_domain.inter_of_isOpen_left (f.comp g).dense_domain f.domain.isOpen

omit [IsReduced X] [Y.IsSeparated] [Z.IsSeparated] in
/-- The open `U` is nonempty when `X` is: it is dense. -/
instance nonempty_compositeDomain [Nonempty X] : Nonempty (compositeDomain f g) :=
  (dense_compositeDomain f g).nonempty.to_subtype

/-- The restriction `f_U` of the representative of `f` on its domain to `U`. -/
def compositeToY : (compositeDomain f g).toScheme ⟶ Y :=
  (f.toPartialMap.restrict (compositeDomain f g) (dense_compositeDomain f g)
    ((compositeDomain_le_domain f g).trans_eq f.toPartialMap_domain.symm)).hom

/-- The restriction `(g ∘ f)_U` of the representative of `g ∘ f` on its domain to `U`. -/
def compositeToZ : (compositeDomain f g).toScheme ⟶ Z :=
  ((f.comp g).toPartialMap.restrict (compositeDomain f g) (dense_compositeDomain f g)
    ((compositeDomain_le_domain_comp f g).trans_eq (f.comp g).toPartialMap_domain.symm)).hom

omit [Z.IsSeparated] in
/-- `f_U` is the representative of `f` on its domain, precomposed with the inclusion of `U`. -/
theorem compositeToY_eq :
    compositeToY f g = X.homOfLE ((compositeDomain_le_domain f g).trans_eq
      f.toPartialMap_domain.symm) ≫ f.toPartialMap.hom :=
  PartialMap.restrict_hom _ _ _ _

omit [Y.IsSeparated] in
/-- `(g ∘ f)_U` is the representative of `g ∘ f` on its domain, precomposed with the inclusion of
`U`. -/
theorem compositeToZ_eq :
    compositeToZ f g = X.homOfLE ((compositeDomain_le_domain_comp f g).trans_eq
      (f.comp g).toPartialMap_domain.symm) ≫ (f.comp g).toPartialMap.hom :=
  PartialMap.restrict_hom _ _ _ _

section Over

variable [S.IsSeparated] [f.IsOver sX sY] [(f.comp g).IsOver sX sZ]

omit [Z.IsSeparated] in
/-- `f_U` is a morphism over `S`. -/
theorem compositeToY_comp : compositeToY f g ≫ sY = (compositeDomain f g).ι ≫ sX := by
  rw [compositeToY_eq, Category.assoc, f.toPartialMap.over sX sY,
    Scheme.homOfLE_ι_assoc]

omit [Y.IsSeparated] in
/-- `(g ∘ f)_U` is a morphism over `S`. -/
theorem compositeToZ_comp : compositeToZ f g ≫ sZ = (compositeDomain f g).ι ≫ sX := by
  rw [compositeToZ_eq, Category.assoc, (f.comp g).toPartialMap.over sX sZ,
    Scheme.homOfLE_ι_assoc]

/-- The morphism `(f_U, (g ∘ f)_U) : U → Y ×_S Z`. -/
def compositeLift : (compositeDomain f g).toScheme ⟶ pullback sY sZ :=
  pullback.lift (compositeToY f g) (compositeToZ f g)
    ((compositeToY_comp sX sY f g).trans (compositeToZ_comp sX sZ f g).symm)

@[reassoc (attr := simp)]
theorem compositeLift_fst : compositeLift sX sY sZ f g ≫ pullback.fst sY sZ = compositeToY f g :=
  pullback.lift_fst _ _ _

@[reassoc (attr := simp)]
theorem compositeLift_snd : compositeLift sX sY sZ f g ≫ pullback.snd sY sZ = compositeToZ f g :=
  pullback.lift_snd _ _ _

/-- `(f_U, (g ∘ f)_U)` is a morphism over `S`. -/
theorem compositeLift_comp :
    compositeLift sX sY sZ f g ≫ pullback.fst sY sZ ≫ sY = (compositeDomain f g).ι ≫ sX := by
  rw [compositeLift_fst_assoc, compositeToY_comp sX]

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
      compositeToY f g := by
  simp

/-- `q_Z` restricts to `(g ∘ f)_U` on `U`. -/
@[reassoc]
theorem toCompositeCorrespondence_sndZ :
    toCompositeCorrespondence sX sY sZ f g ≫ compositeCorrespondenceSndZ sX sY sZ f g =
      compositeToZ f g := by
  simp

end Over

section Field

variable {K : Type u} [Field K] (sX : X ⟶ Spec (.of K)) (sY : Y ⟶ Spec (.of K))
  (sZ : Z ⟶ Spec (.of K)) [f.IsOver sX sY] [(f.comp g).IsOver sX sZ]
  [IsIntegral X]
  [LocallyOfFiniteType sX] [LocallyOfFiniteType sY] [LocallyOfFiniteType sZ]

/-- **The dimension of the correspondence.** Over a field `K`, for `X` integral and `X`, `Y`, `Z`
locally of finite type over `K`, `W_{f,g}` has the same topological Krull dimension as `X`. -/
theorem topologicalKrullDim_compositeCorrespondence :
    topologicalKrullDim (compositeCorrespondence sX sY sZ f g) = topologicalKrullDim X := by
  have := LocallyOfFiniteType.isLocallyNoetherian sX
  exact topologicalKrullDim_graphClosure (compositeLift_comp sX sY sZ f g)

end Field

end AlgebraicGeometry.Scheme.RationalMap
