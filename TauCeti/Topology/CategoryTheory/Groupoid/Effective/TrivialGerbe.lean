/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.Algebra.ProperAction.Basic
public import TauCeti.Topology.CategoryTheory.Groupoid.Constructions
public import TauCeti.Topology.CategoryTheory.Groupoid.Effective.Principal
public import TauCeti.Topology.CategoryTheory.Groupoid.Examples

/-!
# The trivial gerbe `K × N ⇒ N` and its effective reduction

When a group `K` acts trivially on a topological space `N` (`∀ k x, k • x = x`), the native action
groupoid `ActionCategory K N` (`K ⋉ N`) is the trivial `K`-gerbe `K × N ⇒ N`: its object space is
homeomorphic to `N` (`ActionGroupoid.objectHomeomorph K N`), its total arrow space is homeomorphic
to `K × N` (`ActionGroupoid.arrowHomeomorph K N`), and every arrow has equal source and target.

For compact `K` and Hausdorff `N` with discrete `K` (in particular for a finite discrete group `K`),
`ActionCategory K N` is a Hausdorff proper étale topological groupoid whose coarse space is `N`,
whose isotropy at every object is canonically isomorphic to `K`, and whose arrows all induce the
identity germ on `N`:
* `ineffectiveArrows (ActionCategory K N) = Set.univ`,
* `ineffectiveKernel (ActionGroupoid.isLocalHomeomorph_source K N) a = ⊤`, of order `Nat.card K`
  everywhere.

Consequently its effective quotient `EffectiveQuotient (ActionCategory K N)` collapses all isotropy
labels and is equivalent to the unit groupoid `Discrete N`, with both its object space and its
total arrow space homeomorphic to `N`. Whenever `K` is nontrivial, no nonempty category admits
fully faithful functors to both `ActionCategory K N` and its effective quotient (or `Discrete N`):
in particular, no Morita roof of essential equivalences and no categorical equivalence can connect
`ActionCategory K N` to its effective reduction over a nonempty `N`.

## Main declarations

* `TauCeti.TrivialGerbe.continuousSMul_of_smul_eq`,
  `TauCeti.TrivialGerbe.isProperMap_source_target`: continuity of the trivial action and properness
  of `(source, target)` for compact `K` and Hausdorff `N`.
* `TauCeti.TrivialGerbe.coarseHomeomorph`: the coarse space of `ActionCategory K N` is homeomorphic
  to `N`.
* `TauCeti.TrivialGerbe.autMulEquiv`, `TauCeti.TrivialGerbe.ineffectiveArrows_eq_univ`,
  `TauCeti.TrivialGerbe.ineffectiveKernel_eq_top`, `TauCeti.TrivialGerbe.card_ineffectiveKernel`:
  the isotropy is `K` everywhere and is entirely ineffective.
* `TauCeti.TrivialGerbe.effectiveQuotientToDiscrete`,
  `TauCeti.TrivialGerbe.effectiveQuotientObjectHomeomorph`,
  `TauCeti.TrivialGerbe.effectiveQuotientArrowHomeomorph`: categorical equivalence and
  homeomorphisms between `EffectiveQuotient (ActionCategory K N)` and the unit groupoid on `N`.
* `TauCeti.TrivialGerbe.not_exists_fullyFaithful_span_effectiveQuotient`,
  `TauCeti.TrivialGerbe.isEmpty_equivalence_effectiveQuotient`: when `K` is nontrivial, no roof of
  fully faithful functors from a nonempty category (hence no Morita equivalence over a nonempty `N`)
  connects `ActionCategory K N` to its effective quotient.

## References

* I. Moerdijk, *Orbifolds as groupoids: an introduction*, Section 2.
* A. Adem, J. Leida and Y. Ruan, *Orbifolds and Stringy Topology*, Chapter 1.
-/

public section

open CategoryTheory MulAction Set Topology TauCeti.MulAction

namespace TauCeti.TrivialGerbe

section Algebraic

variable {K N : Type*} [Group K] [MulAction K N] (hact : ∀ (k : K) (x : N), k • x = x)

include hact

/-- In the trivial gerbe `ActionCategory K N`, every arrow has equal source and target. -/
theorem left_eq_right (a : Quiver.Total (ActionCategory K N)) :
    a.left = a.right :=
  (ActionCategory.objEquiv K N).symm.injective (a.hom.map_val.symm.trans (hact _ _)).symm

/-- Every element of `K` fixes every point of `N` under a trivial action. -/
theorem stabilizer_eq_top (x : N) : stabilizer K x = ⊤ := by
  rw [Subgroup.eq_top_iff']
  exact fun k ↦ hact k x

/-- At every object of `ActionCategory K N` for a trivial action, the isotropy group is canonically
isomorphic to `K`. -/
def autMulEquiv (a : ActionCategory K N) : Aut a ≃* K where
  toFun e := e.asIso.hom.hom
  invFun k := Aut.of
    { hom := Functor.Elements.homMk k (hact k a.back)
      inv := Functor.Elements.homMk k⁻¹ (hact k⁻¹ a.back)
      hom_inv_id := Functor.Elements.hom_ext (inv_mul_cancel k)
      inv_hom_id := Functor.Elements.hom_ext (mul_inv_cancel k) }
  left_inv _ := Aut.ext (Iso.ext (Functor.Elements.hom_ext rfl))
  right_inv _ := rfl
  map_mul' _ _ := rfl

/-- `autMulEquiv` reads off the group label of an automorphism in `ActionCategory K N`. -/
@[simp]
theorem autMulEquiv_apply (a : ActionCategory K N) (e : Aut a) :
    autMulEquiv hact a e = e.asIso.hom.hom := (rfl)

/-- Forgetting the group label sends the trivial gerbe `ActionCategory K N` to the unit groupoid
`Discrete N`. -/
def toDiscreteFunctor : ActionCategory K N ⥤ Discrete N where
  obj a := Discrete.mk a.back
  map f := Discrete.eqToHom (f.map_val.symm.trans (hact _ _)).symm

/-- `toDiscreteFunctor` sends an object of `ActionCategory K N` to its underlying point in
`Discrete N`. -/
@[simp]
theorem toDiscreteFunctor_obj (a : ActionCategory K N) :
    (toDiscreteFunctor hact).obj a = Discrete.mk a.back := (rfl)

/-- When `K` is nontrivial, no nonempty category `H` admits fully faithful functors to both
`ActionCategory K N` and `Discrete N`: any object of `H` would simultaneously have nontrivial
automorphism group `K` and trivial automorphism group. -/
theorem not_exists_fullyFaithful_span_discrete [Nontrivial K] {H : Type*} [Category H]
    [Nonempty H] :
    ¬ ∃ (F₁ : H ⥤ ActionCategory K N) (F₂ : H ⥤ Discrete N),
      F₁.Full ∧ F₁.Faithful ∧ F₂.Full ∧ F₂.Faithful := by
  rintro ⟨F₁, F₂, hF₁full, hF₁faith, hF₂full, hF₂faith⟩
  obtain ⟨h⟩ := ‹Nonempty H›
  let e₁ : Aut h ≃* K :=
    ((Functor.FullyFaithful.ofFullyFaithful F₁).autMulEquivOfFullyFaithful h).trans
      (autMulEquiv hact (F₁.obj h))
  let e₂ : Aut h ≃* Aut (F₂.obj h) :=
    (Functor.FullyFaithful.ofFullyFaithful F₂).autMulEquivOfFullyFaithful h
  have : Nontrivial (Aut h) := e₁.toEquiv.nontrivial
  have : Subsingleton (Aut (F₂.obj h)) :=
    ⟨fun a b ↦ Aut.ext (Iso.ext (Subsingleton.elim _ _))⟩
  have : Subsingleton (Aut h) := e₂.toEquiv.subsingleton
  exact false_of_nontrivial_of_subsingleton (Aut h)

/-- When `K` is nontrivial and `N` is nonempty, `ActionCategory K N` is not categorically
equivalent to `Discrete N`. -/
theorem isEmpty_equivalence_discrete [Nontrivial K] [Nonempty N] :
    IsEmpty (ActionCategory K N ≌ Discrete N) :=
  have : Nonempty (ActionCategory K N) :=
    ⟨ActionCategory.objEquiv K N (Classical.arbitrary N)⟩
  ⟨fun E ↦ not_exists_fullyFaithful_span_discrete hact (H := ActionCategory K N)
    ⟨𝟭 _, E.functor, inferInstance, inferInstance, inferInstance, inferInstance⟩⟩

end Algebraic

/-- A trivial action of any topological monoid on a topological space is jointly continuous. -/
theorem continuousSMul_of_smul_eq {M N : Type*} [Monoid M] [MulAction M N]
    [TopologicalSpace M] [TopologicalSpace N] (h : ∀ (m : M) (x : N), m • x = x) :
    ContinuousSMul M N :=
  ⟨by simpa only [show (fun p : M × N ↦ p.1 • p.2) = Prod.snd from funext fun p ↦ h p.1 p.2]
    using continuous_snd⟩

section Topological

variable {K N : Type*} [Group K] [MulAction K N] [TopologicalSpace K] [TopologicalSpace N]
  (hact : ∀ (k : K) (x : N), k • x = x)

include hact

/-- When `K` is compact (for example finite and discrete) and `N` is Hausdorff, the source-target
map of the trivial gerbe `ActionCategory K N` is proper. -/
theorem isProperMap_source_target [CompactSpace K] [T2Space N] :
    IsProperMap fun f : Quiver.Total (ActionCategory K N) ↦ (f.left, f.right) := by
  have : ContinuousSMul K N := continuousSMul_of_smul_eq hact
  have := properSMul_of_compactSpace K N
  exact (ActionGroupoid.isProperMap_source_target_iff K N).mpr this

omit [TopologicalSpace K] in
/-- For a trivial action, the germ kernel at every point of `N` is all of `K`. -/
theorem germKernel_eq_top (x : N) : germKernel K x = ⊤ := by
  rw [Subgroup.eq_top_iff']
  intro k
  rw [mem_germKernel]
  exact Filter.Eventually.of_forall (hact k)

omit [TopologicalSpace K] in
/-- The coarse space of the trivial gerbe `ActionCategory K N` is homeomorphic to `N`. -/
noncomputable def coarseHomeomorph :
    _root_.Quotient (isIsomorphicSetoid (ActionCategory K N)) ≃ₜ N where
  toFun := _root_.Quotient.lift (ActionGroupoid.objectHomeomorph K N)
    (by
      rintro a b ⟨e⟩
      simp only [ActionGroupoid.objectHomeomorph_apply]
      exact (e.hom.map_val.symm.trans (hact _ _)).symm)
  invFun x := _root_.Quotient.mk (isIsomorphicSetoid _)
    ((ActionGroupoid.objectHomeomorph K N).symm x)
  left_inv := _root_.Quotient.ind fun a ↦
    congrArg (_root_.Quotient.mk _) ((ActionGroupoid.objectHomeomorph K N).symm_apply_apply a)
  right_inv := (ActionGroupoid.objectHomeomorph K N).apply_symm_apply
  continuous_toFun :=
    isQuotientMap_quotient_mk'.continuous_iff.mpr
      (ActionGroupoid.objectHomeomorph K N).continuous
  continuous_invFun :=
    continuous_quotient_mk'.comp (ActionGroupoid.objectHomeomorph K N).symm.continuous

omit [TopologicalSpace K] in
/-- `coarseHomeomorph` sends the isomorphism class of `a` to its underlying point `a.back`. -/
@[simp]
theorem coarseHomeomorph_mk (a : ActionCategory K N) :
    coarseHomeomorph hact (_root_.Quotient.mk (isIsomorphicSetoid _) a) = a.back :=
  ActionGroupoid.objectHomeomorph_apply K N a

omit [TopologicalSpace K] in
/-- The inverse of `coarseHomeomorph` sends `x : N` to the class of `objEquiv K N x`. -/
@[simp]
theorem coarseHomeomorph_symm_apply (x : N) :
    (coarseHomeomorph hact).symm x =
      _root_.Quotient.mk (isIsomorphicSetoid _) (ActionCategory.objEquiv K N x) := by
  simp [coarseHomeomorph]

/-- Every arrow of the trivial gerbe `ActionCategory K N` is ineffective. -/
theorem ineffectiveArrows_eq_univ :
    ineffectiveArrows (ActionCategory K N) = Set.univ :=
  eq_univ_of_forall fun _ ↦ mem_ineffectiveArrows_iff.mpr
    (Filter.Eventually.of_forall (left_eq_right hact))

/-- Any two parallel arrows of the trivial gerbe `ActionCategory K N` induce the same germ. -/
theorem germRel_apply {a b : ActionCategory K N} (f f' : a ⟶ b) :
    germRel (ActionCategory K N) f f' := by
  simp [germRel_iff, ineffectiveArrows_eq_univ hact]

/-- For discrete `K`, the ineffective kernel of the trivial gerbe `ActionCategory K N` at every
object is the entire isotropy group `Aut a`. -/
theorem ineffectiveKernel_eq_top [DiscreteTopology K] (a : ActionCategory K N) :
    letI : ContinuousSMul K N := continuousSMul_of_smul_eq hact
    ineffectiveKernel (ActionGroupoid.isLocalHomeomorph_source K N) a = ⊤ := by
  let : ContinuousSMul K N := continuousSMul_of_smul_eq hact
  rw [Subgroup.eq_top_iff']
  intro g
  simp [mem_ineffectiveKernel, ineffectiveArrows_eq_univ hact]

/-- For discrete `K`, the order of the ineffective kernel at every object of `ActionCategory K N`
is `Nat.card K`. -/
theorem card_ineffectiveKernel [DiscreteTopology K] (a : ActionCategory K N) :
    letI : ContinuousSMul K N := continuousSMul_of_smul_eq hact
    Nat.card (ineffectiveKernel (ActionGroupoid.isLocalHomeomorph_source K N) a) =
      Nat.card K := by
  let : ContinuousSMul K N := continuousSMul_of_smul_eq hact
  rw [ineffectiveKernel_eq_top hact a]
  exact (Nat.card_congr Subgroup.topEquiv.toEquiv).trans
    (Nat.card_congr (autMulEquiv hact a).toEquiv)

/-- Projection from the effective quotient of the trivial gerbe `ActionCategory K N` to the unit
groupoid `Discrete N`. -/
def effectiveQuotientToDiscrete : EffectiveQuotient (ActionCategory K N) ⥤ Discrete N :=
  CategoryTheory.Quotient.lift (germRel (ActionCategory K N))
    (toDiscreteFunctor hact)
    fun _ _ _ _ _ ↦ Subsingleton.elim _ _

/-- `effectiveQuotientToDiscrete` sends the effective image of `a` to `Discrete.mk a.back`. -/
@[simp]
theorem effectiveQuotientToDiscrete_obj_toEffectiveQuotient_obj (a : ActionCategory K N) :
    (effectiveQuotientToDiscrete hact).obj ((toEffectiveQuotient _).obj a) =
      Discrete.mk a.back := (rfl)

/-- `effectiveQuotientToDiscrete` is full. -/
theorem full_effectiveQuotientToDiscrete : (effectiveQuotientToDiscrete hact).Full :=
  Functor.full_of_comp_essSurj _ (toEffectiveQuotient (ActionCategory K N))
    fun x y φ ↦
      let f : x ⟶ y := Functor.Elements.homMk 1
        ((hact 1 x.back).trans (Discrete.eq_of_hom φ))
      ⟨(toEffectiveQuotient _).map f, Subsingleton.elim _ _⟩

/-- `effectiveQuotientToDiscrete` is faithful: parallel arrows induce equal identity germs. -/
theorem faithful_effectiveQuotientToDiscrete : (effectiveQuotientToDiscrete hact).Faithful :=
  Functor.faithful_of_comp_essSurj _ (toEffectiveQuotient (ActionCategory K N))
    fun _ _ φ ψ _ ↦ by
      obtain ⟨f, rfl⟩ := (toEffectiveQuotient _).map_surjective φ
      obtain ⟨g, rfl⟩ := (toEffectiveQuotient _).map_surjective ψ
      exact CategoryTheory.Quotient.sound _ (germRel_apply hact f g)

/-- `effectiveQuotientToDiscrete` is essentially surjective. -/
theorem essSurj_effectiveQuotientToDiscrete : (effectiveQuotientToDiscrete hact).EssSurj where
  mem_essImage x :=
    ⟨(toEffectiveQuotient _).obj (ActionCategory.objEquiv K N x.as), ⟨Iso.refl x⟩⟩

/-- The effective quotient of the trivial gerbe `ActionCategory K N` is categorically equivalent to
the unit groupoid `Discrete N`. -/
theorem isEquivalence_effectiveQuotientToDiscrete :
    (effectiveQuotientToDiscrete hact).IsEquivalence :=
  have := full_effectiveQuotientToDiscrete hact
  have := faithful_effectiveQuotientToDiscrete hact
  have := essSurj_effectiveQuotientToDiscrete hact
  { }

omit hact in
variable (K N) in
/-- Objects of `EffectiveQuotient (ActionCategory K N)` are homeomorphic to `N`. -/
noncomputable def effectiveQuotientObjectHomeomorph :
    EffectiveQuotient (ActionCategory K N) ≃ₜ N :=
  (EffectiveQuotient.objHomeomorph (ActionCategory K N)).symm.trans
    (ActionGroupoid.objectHomeomorph K N)

omit hact in
/-- `effectiveQuotientObjectHomeomorph` reads off the point underlying a lifted object. -/
@[simp]
theorem effectiveQuotientObjectHomeomorph_toEffectiveQuotient_obj (a : ActionCategory K N) :
    effectiveQuotientObjectHomeomorph K N ((toEffectiveQuotient (ActionCategory K N)).obj a) =
      a.back := by
  simp [effectiveQuotientObjectHomeomorph]

/-- Total arrows of `EffectiveQuotient (ActionCategory K N)` are homeomorphic to `N`, matching the
total arrow space of the unit groupoid `Discrete N`. -/
noncomputable def effectiveQuotientArrowHomeomorph :
    Quiver.Total (EffectiveQuotient (ActionCategory K N)) ≃ₜ N where
  toFun a := effectiveQuotientObjectHomeomorph K N a.left
  invFun x := (toEffectiveQuotient (ActionCategory K N)).toPrefunctor.mapTotal
    ((ActionGroupoid.arrowHomeomorph K N).symm (1, x))
  left_inv a := by
    obtain ⟨⟨x, y, f⟩, rfl⟩ := EffectiveQuotient.mapTotal_surjective a
    have hxy : x = y := left_eq_right hact ⟨x, y, f⟩
    subst hxy
    have hex : (ActionGroupoid.arrowHomeomorph K N).symm (1, x.back) = ⟨x, x, 𝟙 x⟩ := by
      apply (ActionGroupoid.arrowHomeomorph K N).injective
      simp only [Homeomorph.apply_symm_apply, ActionGroupoid.arrowHomeomorph_apply]
      exact Prod.ext rfl rfl
    have hm : (toEffectiveQuotient (ActionCategory K N)).map (𝟙 x) =
        (toEffectiveQuotient (ActionCategory K N)).map f :=
      CategoryTheory.Quotient.sound _ (germRel_apply hact _ _)
    simp only [Prefunctor.mapTotal_left, Functor.toPrefunctor_obj,
      effectiveQuotientObjectHomeomorph_toEffectiveQuotient_obj, hex]
    simp [Prefunctor.mapTotal, hm]
  right_inv x := by
    simp only [Prefunctor.mapTotal_left, Functor.toPrefunctor_obj,
      effectiveQuotientObjectHomeomorph_toEffectiveQuotient_obj,
      ActionGroupoid.arrowHomeomorph_symm_apply, ActionCategory.totalEquiv_symm_apply_left]
    exact (ActionCategory.objEquiv K N).left_inv x
  continuous_toFun :=
    EffectiveQuotient.isQuotientMap_mapTotal.continuous_iff.mpr
      (((ActionGroupoid.objectHomeomorph K N).continuous.comp
        (ActionGroupoid.continuous_source K N)).congr fun b ↦ by
          simp [Prefunctor.mapTotal])
  continuous_invFun :=
    EffectiveQuotient.isQuotientMap_mapTotal.continuous.comp
      ((ActionGroupoid.arrowHomeomorph K N).symm.continuous.comp
        (continuous_const.prodMk continuous_id))

/-- `effectiveQuotientArrowHomeomorph` sends the image of `a` to the point underlying `a.left`. -/
@[simp]
theorem effectiveQuotientArrowHomeomorph_mapTotal (a : Quiver.Total (ActionCategory K N)) :
    effectiveQuotientArrowHomeomorph hact
      ((toEffectiveQuotient (ActionCategory K N)).toPrefunctor.mapTotal a) = a.left.back := by
  simp [effectiveQuotientArrowHomeomorph, Prefunctor.mapTotal]

/-- When `K` is nontrivial, no nonempty category `H` admits fully faithful functors to both
`ActionCategory K N` and `EffectiveQuotient (ActionCategory K N)`; in particular, no Morita roof of
essential equivalences can connect them over a nonempty `N`. -/
theorem not_exists_fullyFaithful_span_effectiveQuotient [Nontrivial K]
    {H : Type*} [Category H] [Nonempty H] :
    ¬ ∃ (F₁ : H ⥤ ActionCategory K N)
        (F₂ : H ⥤ EffectiveQuotient (ActionCategory K N)),
      F₁.Full ∧ F₁.Faithful ∧ F₂.Full ∧ F₂.Faithful := by
  rintro ⟨F₁, F₂, hF₁full, hF₁faith, hF₂full, hF₂faith⟩
  have := full_effectiveQuotientToDiscrete hact
  have := faithful_effectiveQuotientToDiscrete hact
  exact not_exists_fullyFaithful_span_discrete hact (H := H)
    ⟨F₁, F₂ ⋙ effectiveQuotientToDiscrete hact, hF₁full, hF₁faith, inferInstance, inferInstance⟩

/-- When `K` is nontrivial and `N` is nonempty, the trivial gerbe `ActionCategory K N` is not
categorically equivalent to its effective quotient. -/
theorem isEmpty_equivalence_effectiveQuotient [Nontrivial K] [Nonempty N] :
    IsEmpty (ActionCategory K N ≌ EffectiveQuotient (ActionCategory K N)) :=
  have : Nonempty (ActionCategory K N) :=
    ⟨ActionCategory.objEquiv K N (Classical.arbitrary N)⟩
  ⟨fun E ↦ not_exists_fullyFaithful_span_effectiveQuotient hact (H := ActionCategory K N)
    ⟨𝟭 _, E.functor, inferInstance, inferInstance, inferInstance, inferInstance⟩⟩

end Topological

end TauCeti.TrivialGerbe
