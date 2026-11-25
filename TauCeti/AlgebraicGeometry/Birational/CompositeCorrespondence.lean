/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicGeometry.Birational.Composition
public import Mathlib.AlgebraicGeometry.Noetherian
public import TauCeti.AlgebraicGeometry.Birational.Graph
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

The projections of `X ×_S (Y ×_S Z)` to the absolute products `X × Y`, `X × Z` and `Y × Z` carry
`W_{f,g}` into the graphs `Γ_f`, `Γ_{g ∘ f}` and `Γ_g` of
`AlgebraicGeometry.Scheme.RationalMap.graph` (through their closed immersions), giving `(q_X, q_Y)`,
`(q_X, q_Z)` and `(q_Y, q_Z)`. For the first two this holds because, for `X` reduced, kernels can be
compared on a dense open (`AlgebraicGeometry.Scheme.Hom.ker_le_ker_of_homOfLE_comp_eq`), and the
representative of a rational map is the restriction of its partial map on the domain of definition.
For `(q_Y, q_Z)` the dense open is `U` intersected with the domain of the composite of the
representatives of `f` and `g`, where `(g ∘ f)_U` factors through `f_U` and the representative of
`g`. When `X`, `Y` and `Z` are proper over `S`, the three morphisms are proper, since their
composites with the first projection of the target graph (`q_X`, `q_X`, `q_Y`) are proper and the
projections are separated.

## Main definitions

* `AlgebraicGeometry.Scheme.RationalMap.compositeDomain`: the open `U`.
* `AlgebraicGeometry.Scheme.RationalMap.compositeToY`,
  `AlgebraicGeometry.Scheme.RationalMap.compositeToZ`: the morphisms `f_U` and `(g ∘ f)_U`.
* `AlgebraicGeometry.Scheme.RationalMap.compositeLift`: the morphism `(f_U, (g ∘ f)_U)`.
* `AlgebraicGeometry.Scheme.RationalMap.compositeCorrespondence`: the correspondence `W_{f,g}`,
  with its closed immersion `compositeCorrespondenceι` into `X ×_S (Y ×_S Z)`, its projections
  `compositeCorrespondenceFst`, `compositeCorrespondenceSndY`, `compositeCorrespondenceSndZ`, and
  the factorization `toCompositeCorrespondence` of `U` through it.
* `AlgebraicGeometry.Scheme.RationalMap.compositeCorrespondenceToGraph`,
  `AlgebraicGeometry.Scheme.RationalMap.compositeCorrespondenceToGraphComp`,
  `AlgebraicGeometry.Scheme.RationalMap.compositeCorrespondenceToGraphRight`: the morphisms
  `(q_X, q_Y) : W_{f,g} → Γ_f`, `(q_X, q_Z) : W_{f,g} → Γ_{g ∘ f}` and
  `(q_Y, q_Z) : W_{f,g} → Γ_g`.

## Main results

* `AlgebraicGeometry.Scheme.RationalMap.topologicalKrullDim_compositeCorrespondence`: over a
  field, for `X` integral and `X`, `Y`, `Z` locally of finite type, `W_{f,g}` has the dimension
  of `X`.
* `AlgebraicGeometry.Scheme.RationalMap.isProper_compositeCorrespondenceToGraph`,
  `AlgebraicGeometry.Scheme.RationalMap.isProper_compositeCorrespondenceToGraphComp`,
  `AlgebraicGeometry.Scheme.RationalMap.isProper_compositeCorrespondenceToGraphRight`: for `X`,
  `Y`, `Z` proper over `S`, the three morphisms to the graphs are proper.

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

/-- For `X` reduced, if two morphisms out of opens of `X` agree, up to a morphism `m`, on a dense
open `V`, the kernel of the second bounds the kernel of the first. -/
theorem Hom.ker_le_ker_of_homOfLE_comp_eq {X T A : Scheme.{u}}
    [IsReduced X] {U V : X.Opens} (hV : Dense (V : Set X)) (hVU : V ≤ U)
    (a : U.toScheme ⟶ T) (m : V.toScheme ⟶ A) (b : A ⟶ T) (h : X.homOfLE hVU ≫ a = m ≫ b) :
    b.ker ≤ a.ker := by
  rw [← Scheme.Hom.ker_homOfLE_comp hV hVU a, h]
  exact Scheme.Hom.le_ker_comp m b

/-- A partial map from a reduced scheme to a separated scheme is the restriction of the
representative on the domain of definition of its rational map. -/
theorem PartialMap.hom_eq_homOfLE_comp_toPartialMap
    {X Y : Scheme.{u}} [IsReduced X] [Y.IsSeparated] (P : X.PartialMap Y) {f : X ⤏ Y}
    (hP : P.toRationalMap = f) (h : P.domain ≤ f.toPartialMap.domain) :
    P.hom = X.homOfLE h ≫ f.toPartialMap.hom := by
  subst hP
  exact P.toPartialMap_toRationalMap_restrict.symm.trans (PartialMap.restrict_hom _ _ _ _)

namespace RationalMap

/-- The representative of a rational map from a reduced scheme to a separated scheme lies in the
domain of definition, where it is the restriction of `toPartialMap`. -/
theorem representative_hom_eq {X Y : Scheme.{u}} [IsReduced X] [Y.IsSeparated] (f : X ⤏ Y) :
    f.representative.hom = X.homOfLE (f.representative.le_domain_toRationalMap.trans_eq
      (by rw [f.toRationalMap_representative, toPartialMap_domain])) ≫ f.toPartialMap.hom :=
  f.representative.hom_eq_homOfLE_comp_toPartialMap f.toRationalMap_representative _

/-- For `X` reduced, a morphism `c` out of a dense open `U ⊆ X` whose composite with
`p : Q → X × T` is the graph of the restriction of `h : X ⤏ T` to `U` has kernel containing that
of `γ_h`: the image of `c ≫ p` lies in the graph `Γ_h`. -/
theorem ker_graphLift_le {X T Q : Scheme.{u}} [IsReduced X] [T.IsSeparated] (h : X ⤏ T)
    {U : X.Opens} (hU : Dense (U : Set X)) (hUh : U ≤ h.toPartialMap.domain)
    (c : U.toScheme ⟶ Q) (p : Q ⟶ pullback (terminal.from X) (terminal.from T))
    (hc : c ≫ p ≫ pullback.fst _ _ = U.ι)
    (hc' : c ≫ p ≫ pullback.snd _ _ = X.homOfLE hUh ≫ h.toPartialMap.hom) :
    (graphLift h).ker ≤ (c ≫ p).ker := by
  refine Hom.ker_le_ker_of_homOfLE_comp_eq
    (hU.inter_of_isOpen_left h.representative.dense_domain U.isOpen) inf_le_left _
    (X.homOfLE inf_le_right) _ ?_
  apply pullback.hom_ext
  · simp [hc]
  · simp [hc', representative_hom_eq h]


variable {S X Y Z : Scheme.{u}} (sX : X ⟶ S) (sY : Y ⟶ S) (sZ : Z ⟶ S)
  [IsReduced X] [PreirreducibleSpace X] [Nonempty Y] [Y.IsSeparated] [Z.IsSeparated]
  (f : X ⤏ Y) [f.IsDominant] (g : Y ⤏ Z)

omit [IsReduced X] [Y.IsSeparated] [Z.IsSeparated] in
/-- The composite of the representatives of `f` and `g` represents `g ∘ f`. -/
theorem toRationalMap_representative_comp_representative :
    (f.representative.comp g.representative).toRationalMap = f.comp g := by
  rw [← RationalMap.comp_def, g.toRationalMap_representative]

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

theorem ker_graphLift_le_map_tripleToXY :
    (graphLift f).ker ≤ (opensGraph sX (pullback.fst sY sZ ≫ sY) (compositeDomain f g)
      (compositeLift sX sY sZ f g) (compositeLift_comp sX sY sZ f g)).ker.map
      (tripleToXY sX sY sZ) := by
  rw [Scheme.IdealSheafData.map_ker]
  exact ker_graphLift_le f (dense_compositeDomain f g)
    ((compositeDomain_le_domain f g).trans_eq f.toPartialMap_domain.symm) _ _
    (by simp [tripleToXY]) (by simp [tripleToXY, compositeToY_eq])

theorem ker_graphLift_le_map_tripleToXZ :
    (graphLift (f.comp g)).ker ≤ (opensGraph sX (pullback.fst sY sZ ≫ sY) (compositeDomain f g)
      (compositeLift sX sY sZ f g) (compositeLift_comp sX sY sZ f g)).ker.map
      (tripleToXZ sX sY sZ) := by
  rw [Scheme.IdealSheafData.map_ker]
  exact ker_graphLift_le (f.comp g) (dense_compositeDomain f g)
    ((compositeDomain_le_domain_comp f g).trans_eq (f.comp g).toPartialMap_domain.symm) _ _
    (by simp [tripleToXZ]) (by simp [tripleToXZ, compositeToZ_eq])

theorem ker_graphLift_le_map_tripleToYZ :
    (graphLift g).ker ≤ (opensGraph sX (pullback.fst sY sZ ≫ sY) (compositeDomain f g)
      (compositeLift sX sY sZ f g) (compositeLift_comp sX sY sZ f g)).ker.map
      (tripleToYZ sX sY sZ) := by
  rw [Scheme.IdealSheafData.map_ker]
  set P := f.representative.comp g.representative
  refine Hom.ker_le_ker_of_homOfLE_comp_eq
    ((dense_compositeDomain f g).inter_of_isOpen_left P.dense_domain
      (compositeDomain f g).isOpen) inf_le_left _
    (X.homOfLE (inf_le_right : compositeDomain f g ⊓
        f.representative.domain.ι ''ᵁ f.representative.hom ⁻¹ᵁ g.representative.domain ≤ _) ≫
      (f.representative.domain.ι.isoImage _).inv ≫
      f.representative.hom ∣_ g.representative.domain) _ ?_
  have hP := P.hom_eq_homOfLE_comp_toPartialMap
    (toRationalMap_representative_comp_representative f g)
    (P.le_domain_toRationalMap.trans_eq
      (by rw [toRationalMap_representative_comp_representative, toPartialMap_domain]))
  apply pullback.hom_ext
  · simp only [Category.assoc, tripleToYZ, pullback.lift_fst, opensGraph_snd_assoc,
      compositeLift_fst, compositeToY_eq, graphLift, opensGraph_fst, morphismRestrict_ι,
      representative_hom_eq f, Scheme.homOfLE_homOfLE_assoc]
    simp only [← Category.assoc]
    exact congrArg (· ≫ f.toPartialMap.hom) (by rw [← cancel_mono (Opens.ι _)]; simp)
  · simp only [Category.assoc, tripleToYZ, pullback.lift_snd, opensGraph_snd_assoc,
      compositeLift_snd, compositeToZ_eq, graphLift, opensGraph_snd]
    -- `P.hom` is the composite of the restriction of `f`'s representative with `g`'s.
    change _ = X.homOfLE _ ≫ P.hom
    rw [hP, Scheme.homOfLE_homOfLE_assoc]
    exact (X.homOfLE_homOfLE_assoc (V := P.domain) _ _ _).symm

/-- The morphism `(q_X, q_Y) : W_{f,g} → Γ_f`. -/
def compositeCorrespondenceToGraph : compositeCorrespondence sX sY sZ f g ⟶ graph f :=
  IdealSheafData.subschemeMap _ _ _ (ker_graphLift_le_map_tripleToXY sX sY sZ f g)

/-- The morphism `(q_X, q_Z) : W_{f,g} → Γ_{g ∘ f}`. -/
def compositeCorrespondenceToGraphComp :
    compositeCorrespondence sX sY sZ f g ⟶ graph (f.comp g) :=
  IdealSheafData.subschemeMap _ _ _ (ker_graphLift_le_map_tripleToXZ sX sY sZ f g)

/-- The morphism `(q_Y, q_Z) : W_{f,g} → Γ_g`. -/
def compositeCorrespondenceToGraphRight : compositeCorrespondence sX sY sZ f g ⟶ graph g :=
  IdealSheafData.subschemeMap _ _ _ (ker_graphLift_le_map_tripleToYZ sX sY sZ f g)

@[reassoc (attr := simp)]
theorem compositeCorrespondenceToGraph_graphFst :
    compositeCorrespondenceToGraph sX sY sZ f g ≫ graphFst f =
      compositeCorrespondenceFst sX sY sZ f g := by
  simp [compositeCorrespondenceToGraph, graphClosureFst_def, tripleToXY]

@[reassoc (attr := simp)]
theorem compositeCorrespondenceToGraph_graphSnd :
    compositeCorrespondenceToGraph sX sY sZ f g ≫ graphSnd f =
      compositeCorrespondenceSndY sX sY sZ f g := by
  simp [compositeCorrespondenceToGraph, graphClosureSnd_def, tripleToXY,
    compositeCorrespondenceSndY]

@[reassoc (attr := simp)]
theorem compositeCorrespondenceToGraphComp_graphFst :
    compositeCorrespondenceToGraphComp sX sY sZ f g ≫ graphFst (f.comp g) =
      compositeCorrespondenceFst sX sY sZ f g := by
  simp [compositeCorrespondenceToGraphComp, graphClosureFst_def, tripleToXZ]

@[reassoc (attr := simp)]
theorem compositeCorrespondenceToGraphComp_graphSnd :
    compositeCorrespondenceToGraphComp sX sY sZ f g ≫ graphSnd (f.comp g) =
      compositeCorrespondenceSndZ sX sY sZ f g := by
  simp [compositeCorrespondenceToGraphComp, graphClosureSnd_def, tripleToXZ,
    compositeCorrespondenceSndZ]

@[reassoc (attr := simp)]
theorem compositeCorrespondenceToGraphRight_graphFst :
    compositeCorrespondenceToGraphRight sX sY sZ f g ≫ graphFst g =
      compositeCorrespondenceSndY sX sY sZ f g := by
  simp [compositeCorrespondenceToGraphRight, graphClosureFst_def, graphClosureSnd_def, tripleToYZ,
    compositeCorrespondenceSndY]

@[reassoc (attr := simp)]
theorem compositeCorrespondenceToGraphRight_graphSnd :
    compositeCorrespondenceToGraphRight sX sY sZ f g ≫ graphSnd g =
      compositeCorrespondenceSndZ sX sY sZ f g := by
  simp [compositeCorrespondenceToGraphRight, graphClosureSnd_def, tripleToYZ,
    compositeCorrespondenceSndZ]

variable [IsProper sX] [IsProper sY] [IsProper sZ]

/-- For `X`, `Y`, `Z` proper over `S`, `(q_X, q_Y) : W_{f,g} → Γ_f` is proper. -/
instance isProper_compositeCorrespondenceToGraph :
    IsProper (compositeCorrespondenceToGraph sX sY sZ f g) := by
  have : IsProper (compositeCorrespondenceToGraph sX sY sZ f g ≫ graphFst f) := by
    rw [compositeCorrespondenceToGraph_graphFst]
    infer_instance
  exact IsProper.of_comp _ (graphFst f)

/-- For `X`, `Y`, `Z` proper over `S`, `(q_X, q_Z) : W_{f,g} → Γ_{g ∘ f}` is proper. -/
instance isProper_compositeCorrespondenceToGraphComp :
    IsProper (compositeCorrespondenceToGraphComp sX sY sZ f g) := by
  have : IsProper (compositeCorrespondenceToGraphComp sX sY sZ f g ≫ graphFst (f.comp g)) := by
    rw [compositeCorrespondenceToGraphComp_graphFst]
    infer_instance
  exact IsProper.of_comp _ (graphFst (f.comp g))

/-- For `X`, `Y`, `Z` proper over `S`, `(q_Y, q_Z) : W_{f,g} → Γ_g` is proper. -/
instance isProper_compositeCorrespondenceToGraphRight :
    IsProper (compositeCorrespondenceToGraphRight sX sY sZ f g) := by
  have : IsProper (compositeCorrespondenceToGraphRight sX sY sZ f g ≫ graphFst g) := by
    rw [compositeCorrespondenceToGraphRight_graphFst]
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
