/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicGeometry.Birational.Composition
public import Mathlib.AlgebraicGeometry.Noetherian
public import TauCeti.AlgebraicGeometry.Birational.Composition
public import TauCeti.AlgebraicGeometry.Birational.Graph.Basic
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

The projections of `X ×_S (Y ×_S Z)` to the absolute products `X × Y`, `X × Z` and `Y × Z` carry
`W_{f,g}` into the graphs `Γ_f`, `Γ_{g ∘ f}` and `Γ_g` of
`AlgebraicGeometry.Scheme.RationalMap.graph` (through their closed immersions), giving `(q_X, q_Y)`,
`(q_X, q_Z)` and `(q_Y, q_Z)`. For the first two this is
`AlgebraicGeometry.Scheme.RationalMap.ker_graphLift_le`, since `f_U` and `(g ∘ f)_U` are
restrictions of the representatives of `f` and `g ∘ f` on their domains. For `(q_Y, q_Z)` it is
`AlgebraicGeometry.Scheme.RationalMap.ker_graphLift_le_of_homOfLE_comp_eq` on `U` intersected with
the domain of the composite of the representatives of `f` and `g`, where `(f_U, (g ∘ f)_U)` is
`γ_g` after the restriction of the representative of `f`. The three morphisms are
proper when their composites with the first projection of the target graph (`q_X`, `q_X`, `q_Y`)
are, since the projections are separated: for the first two when `Y` and `Z` are proper over `S`,
and for the third when `X` and `Z` are.

## Main definitions

* `AlgebraicGeometry.Scheme.RationalMap.compositeDomain`: the open `U`.
* `AlgebraicGeometry.Scheme.RationalMap.compositeToY`,
  `AlgebraicGeometry.Scheme.RationalMap.compositeToZ`: the morphisms `f_U` and `(g ∘ f)_U`.
* `AlgebraicGeometry.Scheme.RationalMap.compositeLift`: the morphism `(f_U, (g ∘ f)_U)`.
* `AlgebraicGeometry.Scheme.RationalMap.compositeCorrespondence`: the correspondence `W_{f,g}`,
  with its closed immersion `compositeCorrespondenceι` into `X ×_S (Y ×_S Z)`, its projections
  `compositeCorrespondenceFst`, `compositeCorrespondenceSndY`, `compositeCorrespondenceSndZ`, and
  the factorization `toCompositeCorrespondence` of `U` through it.
* `AlgebraicGeometry.Scheme.tripleToXY`, `AlgebraicGeometry.Scheme.tripleToXZ`,
  `AlgebraicGeometry.Scheme.tripleToYZ`: the projections of `X ×_S (Y ×_S Z)` to the
  absolute products `X × Y`, `X × Z` and `Y × Z`.
* `AlgebraicGeometry.Scheme.RationalMap.compositeCorrespondenceToGraphXY`,
  `AlgebraicGeometry.Scheme.RationalMap.compositeCorrespondenceToGraphXZ`,
  `AlgebraicGeometry.Scheme.RationalMap.compositeCorrespondenceToGraphYZ`: the morphisms
  `(q_X, q_Y) : W_{f,g} → Γ_f`, `(q_X, q_Z) : W_{f,g} → Γ_{g ∘ f}` and
  `(q_Y, q_Z) : W_{f,g} → Γ_g`.

## Main results

* `AlgebraicGeometry.Scheme.RationalMap.topologicalKrullDim_compositeCorrespondence`: over a
  field, for `X` integral and `X`, `Y`, `Z` locally of finite type, `W_{f,g}` has the dimension
  of `X`.
* `AlgebraicGeometry.Scheme.RationalMap.isProper_compositeCorrespondenceToGraphXY`,
  `AlgebraicGeometry.Scheme.RationalMap.isProper_compositeCorrespondenceToGraphXZ`,
  `AlgebraicGeometry.Scheme.RationalMap.isProper_compositeCorrespondenceToGraphYZ`: the three
  morphisms to the graphs are proper, the first two for `Y`, `Z` proper over `S` and the third for
  `X`, `Z` proper over `S`.

## References

* N.-B. Dang, *Degrees of iterates of rational maps on normal projective varieties*, Proc. London
  Math. Soc. 121 (2020), [arXiv:1701.07760](https://arxiv.org/abs/1701.07760), §5 and
  diagram (5.1).
-/

public section

open CategoryTheory Limits TopologicalSpace TauCeti.AlgebraicGeometry

noncomputable section

namespace AlgebraicGeometry.Scheme

universe u

section Triple

variable {S X Y Z : Scheme.{u}} (sX : X ⟶ S) (sY : Y ⟶ S) (sZ : Z ⟶ S)

/-- The projection `X ×_S (Y ×_S Z) → X × Y`. -/
def tripleToXY : pullback sX (pullback.fst sY sZ ≫ sY) ⟶
    pullback (terminal.from X) (terminal.from Y) :=
  pullback.lift (pullback.fst _ _) (pullback.snd _ _ ≫ pullback.fst sY sZ)
    (terminal.hom_ext _ _)

/-- The projection `X ×_S (Y ×_S Z) → X × Z`. -/
def tripleToXZ : pullback sX (pullback.fst sY sZ ≫ sY) ⟶
    pullback (terminal.from X) (terminal.from Z) :=
  pullback.lift (pullback.fst _ _) (pullback.snd _ _ ≫ pullback.snd sY sZ)
    (terminal.hom_ext _ _)

/-- The projection `X ×_S (Y ×_S Z) → Y × Z`. -/
def tripleToYZ : pullback sX (pullback.fst sY sZ ≫ sY) ⟶
    pullback (terminal.from Y) (terminal.from Z) :=
  pullback.lift (pullback.snd _ _ ≫ pullback.fst sY sZ) (pullback.snd _ _ ≫ pullback.snd sY sZ)
    (terminal.hom_ext _ _)

@[reassoc (attr := simp)]
theorem tripleToXY_fst : tripleToXY sX sY sZ ≫ pullback.fst _ _ = pullback.fst _ _ :=
  pullback.lift_fst _ _ _

@[reassoc (attr := simp)]
theorem tripleToXY_snd :
    tripleToXY sX sY sZ ≫ pullback.snd _ _ = pullback.snd _ _ ≫ pullback.fst sY sZ :=
  pullback.lift_snd _ _ _

@[reassoc (attr := simp)]
theorem tripleToXZ_fst : tripleToXZ sX sY sZ ≫ pullback.fst _ _ = pullback.fst _ _ :=
  pullback.lift_fst _ _ _

@[reassoc (attr := simp)]
theorem tripleToXZ_snd :
    tripleToXZ sX sY sZ ≫ pullback.snd _ _ = pullback.snd _ _ ≫ pullback.snd sY sZ :=
  pullback.lift_snd _ _ _

@[reassoc (attr := simp)]
theorem tripleToYZ_fst :
    tripleToYZ sX sY sZ ≫ pullback.fst _ _ = pullback.snd _ _ ≫ pullback.fst sY sZ :=
  pullback.lift_fst _ _ _

@[reassoc (attr := simp)]
theorem tripleToYZ_snd :
    tripleToYZ sX sY sZ ≫ pullback.snd _ _ = pullback.snd _ _ ≫ pullback.snd sY sZ :=
  pullback.lift_snd _ _ _

end Triple

namespace RationalMap

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

/-- The ideal of `Γ_f` lies in the pushforward along `X ×_S (Y ×_S Z) → X × Y` of the ideal of
`W_{f,g}`, so this projection carries `W_{f,g}` into `Γ_f`. -/
theorem ker_graphLift_le_map_tripleToXY :
    (graphLift f).ker ≤ (opensGraph sX (pullback.fst sY sZ ≫ sY) (compositeDomain f g)
      (compositeLift sX sY sZ f g) (compositeLift_comp sX sY sZ f g)).ker.map
      (tripleToXY sX sY sZ) := by
  rw [Scheme.IdealSheafData.map_ker]
  exact ker_graphLift_le f (dense_compositeDomain f g)
    ((compositeDomain_le_domain f g).trans_eq f.toPartialMap_domain.symm) _ _
    (by simp) (by simp [compositeToY_eq])

/-- The ideal of `Γ_{g ∘ f}` lies in the pushforward along `X ×_S (Y ×_S Z) → X × Z` of the ideal
of `W_{f,g}`, so this projection carries `W_{f,g}` into `Γ_{g ∘ f}`. -/
theorem ker_graphLift_le_map_tripleToXZ :
    (graphLift (f.comp g)).ker ≤ (opensGraph sX (pullback.fst sY sZ ≫ sY) (compositeDomain f g)
      (compositeLift sX sY sZ f g) (compositeLift_comp sX sY sZ f g)).ker.map
      (tripleToXZ sX sY sZ) := by
  rw [Scheme.IdealSheafData.map_ker]
  exact ker_graphLift_le (f.comp g) (dense_compositeDomain f g)
    ((compositeDomain_le_domain_comp f g).trans_eq (f.comp g).toPartialMap_domain.symm) _ _
    (by simp) (by simp [compositeToZ_eq])

/-- The ideal of `Γ_g` lies in the pushforward along `X ×_S (Y ×_S Z) → Y × Z` of the ideal of
`W_{f,g}`, so this projection carries `W_{f,g}` into `Γ_g`. The comparison is made on `U`
intersected with the domain of the composite of the representatives of `f` and `g`. -/
theorem ker_graphLift_le_map_tripleToYZ :
    (graphLift g).ker ≤ (opensGraph sX (pullback.fst sY sZ ≫ sY) (compositeDomain f g)
      (compositeLift sX sY sZ f g) (compositeLift_comp sX sY sZ f g)).ker.map
      (tripleToYZ sX sY sZ) := by
  rw [Scheme.IdealSheafData.map_ker]
  have hP := (f.representative.comp g.representative).hom_eq_homOfLE_comp_toPartialMap
    (toRationalMap_representative_comp_representative f g)
    ((f.representative.comp g.representative).le_domain_toRationalMap.trans_eq
      (by rw [toRationalMap_representative_comp_representative, toPartialMap_domain]))
  -- the composite of the representatives is the restriction of `f`'s followed by `g`'s
  rw [PartialMap.comp_hom] at hP
  refine ker_graphLift_le_of_homOfLE_comp_eq g
    ((dense_compositeDomain f g).inter_of_isOpen_left
      (f.representative.comp g.representative).dense_domain (compositeDomain f g).isOpen)
    inf_le_left _
    (X.homOfLE (inf_le_right : compositeDomain f g ⊓
        f.representative.domain.ι ''ᵁ f.representative.hom ⁻¹ᵁ g.representative.domain ≤ _) ≫
      (f.representative.domain.ι.isoImage _).inv ≫
      f.representative.hom ∣_ g.representative.domain) ?_ ?_
  · simp [compositeToY_eq, representative_hom_eq f]
  · simp only [Category.assoc, tripleToYZ_snd, opensGraph_snd_assoc, compositeLift_snd,
      compositeToZ_eq, hP, Scheme.homOfLE_homOfLE_assoc]
    -- the middle open of the right side is the domain of the composite of the representatives,
    -- which is only definitionally the image form appearing in `hP`, so `simp` cannot merge it
    exact (X.homOfLE_homOfLE_assoc _ _ _).symm

/-- The morphism `(q_X, q_Y) : W_{f,g} → Γ_f`. -/
def compositeCorrespondenceToGraphXY : compositeCorrespondence sX sY sZ f g ⟶ graph f :=
  IdealSheafData.subschemeMap _ _ _ (ker_graphLift_le_map_tripleToXY sX sY sZ f g)

/-- The morphism `(q_X, q_Z) : W_{f,g} → Γ_{g ∘ f}`. -/
def compositeCorrespondenceToGraphXZ :
    compositeCorrespondence sX sY sZ f g ⟶ graph (f.comp g) :=
  IdealSheafData.subschemeMap _ _ _ (ker_graphLift_le_map_tripleToXZ sX sY sZ f g)

/-- The morphism `(q_Y, q_Z) : W_{f,g} → Γ_g`. -/
def compositeCorrespondenceToGraphYZ : compositeCorrespondence sX sY sZ f g ⟶ graph g :=
  IdealSheafData.subschemeMap _ _ _ (ker_graphLift_le_map_tripleToYZ sX sY sZ f g)

/-- `(q_X, q_Y)` followed by the closed immersion `Γ_f → X × Y` is the projection of `W_{f,g}`. -/
@[reassoc (attr := simp)]
theorem compositeCorrespondenceToGraphXY_graphι :
    compositeCorrespondenceToGraphXY sX sY sZ f g ≫ graphι f =
      compositeCorrespondenceι sX sY sZ f g ≫ tripleToXY sX sY sZ :=
  IdealSheafData.subschemeMap_subschemeι _ _ _ _

/-- `(q_X, q_Z)` followed by the closed immersion `Γ_{g ∘ f} → X × Z` is the projection of
`W_{f,g}`. -/
@[reassoc (attr := simp)]
theorem compositeCorrespondenceToGraphXZ_graphι :
    compositeCorrespondenceToGraphXZ sX sY sZ f g ≫ graphι (f.comp g) =
      compositeCorrespondenceι sX sY sZ f g ≫ tripleToXZ sX sY sZ :=
  IdealSheafData.subschemeMap_subschemeι _ _ _ _

/-- `(q_Y, q_Z)` followed by the closed immersion `Γ_g → Y × Z` is the projection of `W_{f,g}`. -/
@[reassoc (attr := simp)]
theorem compositeCorrespondenceToGraphYZ_graphι :
    compositeCorrespondenceToGraphYZ sX sY sZ f g ≫ graphι g =
      compositeCorrespondenceι sX sY sZ f g ≫ tripleToYZ sX sY sZ :=
  IdealSheafData.subschemeMap_subschemeι _ _ _ _

/-- On `U`, `(q_X, q_Y)` followed by `Γ_f → X × Y` is `(ι_U, f_U)`. -/
@[reassoc]
theorem toCompositeCorrespondence_compositeCorrespondenceToGraphXY_graphι :
    toCompositeCorrespondence sX sY sZ f g ≫ compositeCorrespondenceToGraphXY sX sY sZ f g ≫
      graphι f =
      pullback.lift (compositeDomain f g).ι (compositeToY f g) (terminal.hom_ext _ _) := by
  ext <;> simp

/-- On `U`, `(q_X, q_Z)` followed by `Γ_{g ∘ f} → X × Z` is `(ι_U, (g ∘ f)_U)`. -/
@[reassoc]
theorem toCompositeCorrespondence_compositeCorrespondenceToGraphXZ_graphι :
    toCompositeCorrespondence sX sY sZ f g ≫ compositeCorrespondenceToGraphXZ sX sY sZ f g ≫
      graphι (f.comp g) =
      pullback.lift (compositeDomain f g).ι (compositeToZ f g) (terminal.hom_ext _ _) := by
  ext <;> simp

/-- On `U`, `(q_Y, q_Z)` followed by `Γ_g → Y × Z` is `(f_U, (g ∘ f)_U)`. -/
@[reassoc]
theorem toCompositeCorrespondence_compositeCorrespondenceToGraphYZ_graphι :
    toCompositeCorrespondence sX sY sZ f g ≫ compositeCorrespondenceToGraphYZ sX sY sZ f g ≫
      graphι g = pullback.lift (compositeToY f g) (compositeToZ f g) (terminal.hom_ext _ _) := by
  ext <;> simp

@[reassoc (attr := simp)]
theorem compositeCorrespondenceToGraphXY_graphFst :
    compositeCorrespondenceToGraphXY sX sY sZ f g ≫ graphFst f =
      compositeCorrespondenceFst sX sY sZ f g := by
  simp [graphClosureFst_def]

@[reassoc (attr := simp)]
theorem compositeCorrespondenceToGraphXY_graphSnd :
    compositeCorrespondenceToGraphXY sX sY sZ f g ≫ graphSnd f =
      compositeCorrespondenceSndY sX sY sZ f g := by
  simp [graphClosureSnd_def, compositeCorrespondenceSndY]

@[reassoc (attr := simp)]
theorem compositeCorrespondenceToGraphXZ_graphFst :
    compositeCorrespondenceToGraphXZ sX sY sZ f g ≫ graphFst (f.comp g) =
      compositeCorrespondenceFst sX sY sZ f g := by
  simp [graphClosureFst_def]

@[reassoc (attr := simp)]
theorem compositeCorrespondenceToGraphXZ_graphSnd :
    compositeCorrespondenceToGraphXZ sX sY sZ f g ≫ graphSnd (f.comp g) =
      compositeCorrespondenceSndZ sX sY sZ f g := by
  simp [graphClosureSnd_def, compositeCorrespondenceSndZ]

@[reassoc (attr := simp)]
theorem compositeCorrespondenceToGraphYZ_graphFst :
    compositeCorrespondenceToGraphYZ sX sY sZ f g ≫ graphFst g =
      compositeCorrespondenceSndY sX sY sZ f g := by
  simp [graphClosureFst_def, graphClosureSnd_def, compositeCorrespondenceSndY]

@[reassoc (attr := simp)]
theorem compositeCorrespondenceToGraphYZ_graphSnd :
    compositeCorrespondenceToGraphYZ sX sY sZ f g ≫ graphSnd g =
      compositeCorrespondenceSndZ sX sY sZ f g := by
  simp [graphClosureSnd_def, compositeCorrespondenceSndZ]

/-- For `Y` and `Z` proper over `S`, `(q_X, q_Y) : W_{f,g} → Γ_f` is proper. -/
instance isProper_compositeCorrespondenceToGraphXY [IsProper sY] [IsProper sZ] :
    IsProper (compositeCorrespondenceToGraphXY sX sY sZ f g) := by
  have : IsProper (compositeCorrespondenceToGraphXY sX sY sZ f g ≫ graphFst f) := by
    rw [compositeCorrespondenceToGraphXY_graphFst]
    infer_instance
  exact IsProper.of_comp _ (graphFst f)

/-- For `Y` and `Z` proper over `S`, `(q_X, q_Z) : W_{f,g} → Γ_{g ∘ f}` is proper. -/
instance isProper_compositeCorrespondenceToGraphXZ [IsProper sY] [IsProper sZ] :
    IsProper (compositeCorrespondenceToGraphXZ sX sY sZ f g) := by
  have : IsProper (compositeCorrespondenceToGraphXZ sX sY sZ f g ≫ graphFst (f.comp g)) := by
    rw [compositeCorrespondenceToGraphXZ_graphFst]
    infer_instance
  exact IsProper.of_comp _ (graphFst (f.comp g))

/-- For `X` and `Z` proper over `S`, `(q_Y, q_Z) : W_{f,g} → Γ_g` is proper. -/
instance isProper_compositeCorrespondenceToGraphYZ [IsProper sX] [IsProper sZ] :
    IsProper (compositeCorrespondenceToGraphYZ sX sY sZ f g) := by
  have : IsProper (compositeCorrespondenceToGraphYZ sX sY sZ f g ≫ graphFst g) := by
    rw [compositeCorrespondenceToGraphYZ_graphFst]
    infer_instance
  exact IsProper.of_comp _ (graphFst g)

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

end RationalMap

end AlgebraicGeometry.Scheme
