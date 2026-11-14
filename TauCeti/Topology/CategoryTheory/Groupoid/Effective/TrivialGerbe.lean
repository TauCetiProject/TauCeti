/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Groupoid.Discrete
public import TauCeti.Topology.CategoryTheory.Groupoid.Constructions
public import TauCeti.Topology.CategoryTheory.Groupoid.Effective.Topology
public import TauCeti.Topology.CategoryTheory.Groupoid.Examples
public import TauCeti.Topology.Homeomorph.Quotient

/-!
# The trivial gerbe and its effective reduction

For a group `K` and a topological space `N`, the product groupoid `SingleObj K × Discrete N` is the
*trivial `K`-gerbe* `K × N ⇒ N`: its object space is homeomorphic to `N`, its total-arrow space is
homeomorphic to `K × N`, and both source and target project `K × N` to `N`. Every arrow is an
automorphism of its source, and the isotropy group at each point is isomorphic to `K`. Using the
product `SingleObj K × Discrete N` avoids introducing a redundant carrier or a global trivial
`MulAction K N` instance on `N`.

When `K` carries the discrete topology, `SingleObj K × Discrete N` is an étale topological
groupoid, and when `K` is compact and `N` is Hausdorff its source-target map is proper (in
particular for finite discrete `K`). Because source and target agree identically on all arrows,
every arrow is ineffective: `ineffectiveArrows (SingleObj K × Discrete N) = Set.univ`, and every
ineffective kernel is the whole isotropy group, of order `Nat.card K`.

Passing to the effective quotient collapses the `K`-isotropy while keeping `N` as the coarse space:
`TauCeti.TrivialGerbe.effectiveQuotientEquivalence` identifies
`EffectiveQuotient (SingleObj K × Discrete N)` with the unit groupoid `Discrete N` by an
equivalence of categories that is simultaneously a homeomorphism on objects and on total arrows.
When `K` is nontrivial and `N` is nonempty, however, there is no faithful functor from
`SingleObj K × Discrete N` to `Discrete N`, hence no equivalence of categories with `Discrete N` or
with `EffectiveQuotient (SingleObj K × Discrete N)`
(`TauCeti.TrivialGerbe.isEmpty_equivalence_effectiveQuotient`). Since any weak equivalence (and
therefore any zig-zag of weak equivalences, i.e. Morita equivalence) of topological or Lie
groupoids induces an equivalence of the underlying categories, effective reduction induces a
homeomorphism on coarse spaces without being a categorical or Morita equivalence.

## Main declarations

* `TauCeti.TrivialGerbe.objectHomeomorph` and `TauCeti.TrivialGerbe.arrowHomeomorph`: explicit
  coordinate homeomorphisms `(SingleObj K × Discrete N) ≃ₜ N` and
  `Quiver.Total (SingleObj K × Discrete N) ≃ₜ K × N`.
* `TauCeti.TrivialGerbe.isLocalHomeomorph_source`, `TauCeti.TrivialGerbe.isLocalHomeomorph_target`,
  `TauCeti.TrivialGerbe.isProperMap_source_target`: étale and proper-presentation hypotheses for
  `SingleObj K × Discrete N`.
* `TauCeti.TrivialGerbe.autMulEquiv`: the isotropy isomorphism `K ≃* Aut x` at each object `x`.
* `TauCeti.TrivialGerbe.ineffectiveArrows_eq_univ` and
  `TauCeti.TrivialGerbe.ineffectiveKernel_eq_top`: every arrow of the trivial gerbe is
  ineffective.
* `TauCeti.TrivialGerbe.isomorphismClassesHomeomorph`: the coarse space of
  `SingleObj K × Discrete N` is homeomorphic to `N`.
* `TauCeti.TrivialGerbe.effectiveQuotientEquivalence`,
  `TauCeti.TrivialGerbe.effectiveQuotientObjectHomeomorph`, and
  `TauCeti.TrivialGerbe.effectiveQuotientArrowHomeomorph`: the effective quotient of
  `SingleObj K × Discrete N` is `Discrete N`, categorically and topologically on objects and
  arrows.
* `TauCeti.TrivialGerbe.not_faithful_toEffectiveQuotient`,
  `TauCeti.TrivialGerbe.isEmpty_faithful_functor_discrete`, and
  `TauCeti.TrivialGerbe.isEmpty_equivalence_effectiveQuotient`: for nontrivial `K` and nonempty `N`,
  the trivial gerbe is not categorically equivalent (`≌`) to its effective quotient.

## References

* I. Moerdijk, *Orbifolds as groupoids: an introduction*, Section 2.
* A. Adem, J. Leida and Y. Ruan, *Orbifolds and Stringy Topology*, Cambridge Tracts in
  Mathematics 171, Cambridge University Press, 2007, Chapter 1, Section 1.2.
-/

public section

open CategoryTheory Set Topology

namespace TauCeti.TrivialGerbe

section Monoid

variable (K N : Type*) [Monoid K]

/-- Every arrow of `SingleObj K × Discrete N` has equal source and target. -/
@[simp]
theorem right_eq_left (a : Quiver.Total (SingleObj K × Discrete N)) : a.right = a.left :=
  Prod.ext (Subsingleton.elim _ _) (Discrete.ext (Discrete.eq_of_hom a.hom.2).symm)

/-- On `SingleObj K × Discrete N`, the target map equals the source map. -/
theorem target_eq_source :
    (Quiver.Total.right : Quiver.Total (SingleObj K × Discrete N) → SingleObj K × Discrete N) =
      Quiver.Total.left :=
  funext (right_eq_left K N)

variable [TopologicalSpace K] [TopologicalSpace N]

omit [Monoid K] [TopologicalSpace K] in
/-- The object space of the trivial gerbe `SingleObj K × Discrete N` is homeomorphic to `N`. -/
def objectHomeomorph : SingleObj K × Discrete N ≃ₜ N :=
  (Homeomorph.uniqueProd (SingleObj K) (Discrete N)).trans (UnitGroupoid.objectHomeomorph N)

omit [Monoid K] [TopologicalSpace K] in
@[simp]
theorem objectHomeomorph_apply (x : SingleObj K × Discrete N) :
    objectHomeomorph K N x = x.2.as := by
  simp [objectHomeomorph]

omit [Monoid K] [TopologicalSpace K] in
@[simp]
theorem objectHomeomorph_symm_apply (y : N) :
    (objectHomeomorph K N).symm y = (SingleObj.star K, ⟨y⟩) := by
  simp [objectHomeomorph]
  rfl

/-- The total-arrow space of `SingleObj K × Discrete N` is homeomorphic to `K × N`. -/
def arrowHomeomorph : Quiver.Total (SingleObj K × Discrete N) ≃ₜ K × N :=
  (totalProdHomeomorph (SingleObj K) (Discrete N)).trans
    ((OneObjectGroupoid.arrowHomeomorph K).prodCongr (UnitGroupoid.arrowHomeomorph N))

@[simp]
theorem arrowHomeomorph_apply (a : Quiver.Total (SingleObj K × Discrete N)) :
    arrowHomeomorph K N a = (a.hom.1, a.left.2.as) := by
  simp [arrowHomeomorph]

@[simp]
theorem arrowHomeomorph_symm_apply (p : K × N) :
    (arrowHomeomorph K N).symm p =
      ⟨(SingleObj.star K, ⟨p.2⟩), (SingleObj.star K, ⟨p.2⟩), (p.1, 𝟙 _)⟩ :=
  (arrowHomeomorph K N).injective <| by simp

/-- Every arrow of `SingleObj K × Discrete N` is ineffective. -/
@[simp]
theorem ineffectiveArrows_eq_univ :
    ineffectiveArrows (SingleObj K × Discrete N) = Set.univ :=
  eq_univ_of_forall fun _ ↦ mem_ineffectiveArrows_iff.mpr
    (Filter.Eventually.of_forall fun b ↦ (right_eq_left K N b).symm)

/-- For discrete `K`, the source map of `SingleObj K × Discrete N` is a local homeomorphism. -/
theorem isLocalHomeomorph_source [DiscreteTopology K] :
    IsLocalHomeomorph
      (Quiver.Total.left : Quiver.Total (SingleObj K × Discrete N) → SingleObj K × Discrete N) :=
  isLocalHomeomorph_source_prod (OneObjectGroupoid.isLocalHomeomorph_source K)
    (UnitGroupoid.isLocalHomeomorph_source N)

/-- For discrete `K`, the target map of `SingleObj K × Discrete N` is a local homeomorphism. -/
theorem isLocalHomeomorph_target [DiscreteTopology K] :
    IsLocalHomeomorph
      (Quiver.Total.right : Quiver.Total (SingleObj K × Discrete N) → SingleObj K × Discrete N) :=
  isLocalHomeomorph_target_prod (OneObjectGroupoid.isLocalHomeomorph_target K)
    (UnitGroupoid.isLocalHomeomorph_target N)

/-- For compact `K` (for instance finite discrete `K`) and Hausdorff `N`, the source-target map of
`SingleObj K × Discrete N` is proper. -/
theorem isProperMap_source_target [CompactSpace K] [T2Space N] :
    IsProperMap fun a : Quiver.Total (SingleObj K × Discrete N) ↦ (a.left, a.right) :=
  isProperMap_source_target_prod (OneObjectGroupoid.isProperMap_source_target K)
    (UnitGroupoid.isProperMap_source_target N)

end Monoid

section Groupoid

variable (K N : Type*) [Group K]

/-- At every object of `SingleObj K × Discrete N`, the isotropy group is `K`. Both `SingleObj` and
`Aut` reverse categorical composition, so the group multiplication matches `K` directly. -/
def autMulEquiv (x : SingleObj K × Discrete N) : K ≃* Aut x where
  toFun k := Aut.of
    { hom := (k, 𝟙 x.2)
      inv := (k⁻¹, 𝟙 x.2)
      hom_inv_id := Prod.ext (inv_mul_cancel k) (Category.id_comp _)
      inv_hom_id := Prod.ext (mul_inv_cancel k) (Category.id_comp _) }
  invFun e := e.asIso.hom.1
  left_inv _ := rfl
  right_inv _ := Aut.ext (Iso.ext (Prod.ext rfl (Subsingleton.elim _ _)))
  map_mul' _ _ := Aut.ext (Iso.ext (Prod.ext rfl (Category.id_comp _).symm))

@[simp]
theorem autMulEquiv_apply_asIso_hom (x : SingleObj K × Discrete N) (k : K) :
    (autMulEquiv K N x k).asIso.hom = (k, 𝟙 x.2) :=
  (rfl)

@[simp]
theorem autMulEquiv_apply_asIso_inv (x : SingleObj K × Discrete N) (k : K) :
    (autMulEquiv K N x k).asIso.inv = (k⁻¹, 𝟙 x.2) :=
  (rfl)

@[simp]
theorem autMulEquiv_symm_apply (x : SingleObj K × Discrete N) (e : Aut x) :
    (autMulEquiv K N x).symm e = e.asIso.hom.1 :=
  (rfl)

theorem nontrivial_aut (x : SingleObj K × Discrete N) [Nontrivial K] : Nontrivial (Aut x) :=
  (autMulEquiv K N x).symm.toEquiv.nontrivial

variable [TopologicalSpace K] [TopologicalSpace N]

omit [TopologicalSpace K] in
/-- The coarse space of the trivial gerbe `SingleObj K × Discrete N` is homeomorphic to `N`. -/
def isomorphismClassesHomeomorph :
    _root_.Quotient (isIsomorphicSetoid (SingleObj K × Discrete N)) ≃ₜ N :=
  (Homeomorph.Quotient.congrRight (r := isIsomorphicSetoid (SingleObj K × Discrete N))
    (r' := ⊥) fun _ _ ↦
      ⟨fun ⟨e⟩ ↦ (right_eq_left K N ⟨_, _, e.hom⟩).symm, fun h ↦ h ▸ ⟨Iso.refl _⟩⟩).trans
    (Homeomorph.quotientBot.trans (objectHomeomorph K N))

omit [TopologicalSpace K] in
@[simp]
theorem isomorphismClassesHomeomorph_mk (x : SingleObj K × Discrete N) :
    isomorphismClassesHomeomorph K N (_root_.Quotient.mk _ x) = x.2.as := by
  simp only [isomorphismClassesHomeomorph, Homeomorph.trans_apply,
    Homeomorph.Quotient.congrRight_mk]
  exact objectHomeomorph_apply K N x

omit [TopologicalSpace K] in
@[simp]
theorem isomorphismClassesHomeomorph_symm_apply (y : N) :
    (isomorphismClassesHomeomorph K N).symm y = _root_.Quotient.mk _ (SingleObj.star K, ⟨y⟩) :=
  (isomorphismClassesHomeomorph K N).injective (by simp)

/-- Projection from the effective quotient of `SingleObj K × Discrete N` to the unit groupoid
`Discrete N`, induced by the second projection. -/
def effectiveQuotientToDiscrete :
    EffectiveQuotient (SingleObj K × Discrete N) ⥤ Discrete N :=
  CategoryTheory.Quotient.lift (germRel (SingleObj K × Discrete N))
    (CategoryTheory.Prod.snd (SingleObj K) (Discrete N)) fun _ _ _ _ _ ↦ Subsingleton.elim _ _

@[simp]
theorem toEffectiveQuotient_comp_effectiveQuotientToDiscrete :
    toEffectiveQuotient (SingleObj K × Discrete N) ⋙ effectiveQuotientToDiscrete K N =
      CategoryTheory.Prod.snd (SingleObj K) (Discrete N) :=
  CategoryTheory.Quotient.lift_spec _ _ _

@[simp]
theorem effectiveQuotientToDiscrete_obj_toEffectiveQuotient_obj (x : SingleObj K × Discrete N) :
    (effectiveQuotientToDiscrete K N).obj ((toEffectiveQuotient _).obj x) = x.2 :=
  (rfl)

@[simp]
theorem effectiveQuotientToDiscrete_mapTotal_mapTotal
    (a : Quiver.Total (SingleObj K × Discrete N)) :
    (effectiveQuotientToDiscrete K N).toPrefunctor.mapTotal
        ((toEffectiveQuotient _).toPrefunctor.mapTotal a) =
      ⟨a.left.2, a.right.2, a.hom.2⟩ :=
  (rfl)

/-- Inclusion of `Discrete N` into `EffectiveQuotient (SingleObj K × Discrete N)` along the
trivial arrow `1 : K`. -/
def discreteToEffectiveQuotient :
    Discrete N ⥤ EffectiveQuotient (SingleObj K × Discrete N) :=
  CategoryTheory.Prod.sectR (SingleObj.star K) (Discrete N) ⋙
    toEffectiveQuotient (SingleObj K × Discrete N)

theorem discreteToEffectiveQuotient_obj (z : Discrete N) :
    (discreteToEffectiveQuotient K N).obj z =
      (toEffectiveQuotient (SingleObj K × Discrete N)).obj (SingleObj.star K, z) :=
  (rfl)

@[simp]
theorem discreteToEffectiveQuotient_mapTotal (b : Quiver.Total (Discrete N)) :
    (discreteToEffectiveQuotient K N).toPrefunctor.mapTotal b =
      (toEffectiveQuotient (SingleObj K × Discrete N)).toPrefunctor.mapTotal
        ⟨(SingleObj.star K, b.left), (SingleObj.star K, b.right),
          (𝟙 (SingleObj.star K), b.hom)⟩ :=
  (rfl)

@[simp]
theorem discreteToEffectiveQuotient_obj_effectiveQuotientToDiscrete_obj
    (y : EffectiveQuotient (SingleObj K × Discrete N)) :
    (discreteToEffectiveQuotient K N).obj ((effectiveQuotientToDiscrete K N).obj y) = y := by
  obtain ⟨x, rfl⟩ := (EffectiveQuotient.objHomeomorph (SingleObj K × Discrete N)).surjective y
  exact congrArg (toEffectiveQuotient (SingleObj K × Discrete N)).obj
    (Prod.ext (Subsingleton.elim _ _) rfl)

@[simp]
theorem effectiveQuotientToDiscrete_obj_discreteToEffectiveQuotient_obj (z : Discrete N) :
    (effectiveQuotientToDiscrete K N).obj ((discreteToEffectiveQuotient K N).obj z) = z :=
  (rfl)

/-- The object map of `effectiveQuotientToDiscrete` is a homeomorphism onto `Discrete N`. -/
def effectiveQuotientObjectHomeomorph :
    EffectiveQuotient (SingleObj K × Discrete N) ≃ₜ Discrete N :=
  (EffectiveQuotient.objHomeomorph (SingleObj K × Discrete N)).symm.trans
    (Homeomorph.uniqueProd (SingleObj K) (Discrete N))

@[simp]
theorem coe_effectiveQuotientObjectHomeomorph :
    ⇑(effectiveQuotientObjectHomeomorph K N) = (effectiveQuotientToDiscrete K N).obj := by
  funext y
  obtain ⟨x, rfl⟩ := (EffectiveQuotient.objHomeomorph (SingleObj K × Discrete N)).surjective y
  simp [effectiveQuotientObjectHomeomorph]

@[simp]
theorem coe_effectiveQuotientObjectHomeomorph_symm :
    ⇑(effectiveQuotientObjectHomeomorph K N).symm = (discreteToEffectiveQuotient K N).obj := by
  funext z
  simp [effectiveQuotientObjectHomeomorph, discreteToEffectiveQuotient_obj]
  rfl

/-- In `EffectiveQuotient (SingleObj K × Discrete N)`, all parallel arrows are identified. -/
instance instSubsingletonHomEffectiveQuotient
    (y₁ y₂ : EffectiveQuotient (SingleObj K × Discrete N)) :
    Subsingleton (y₁ ⟶ y₂) :=
  ⟨fun f g ↦ by
    obtain ⟨f₀, rfl⟩ := (toEffectiveQuotient _).map_surjective f
    obtain ⟨g₀, rfl⟩ := (toEffectiveQuotient _).map_surjective g
    exact CategoryTheory.Quotient.sound _ (by simp [germRel_iff, ineffectiveArrows_eq_univ])⟩

/-- **Effective quotient of the trivial gerbe.** The effective quotient of
`SingleObj K × Discrete N` is categorically equivalent to the unit groupoid `Discrete N`. -/
def effectiveQuotientEquivalence :
    EffectiveQuotient (SingleObj K × Discrete N) ≌ Discrete N where
  functor := effectiveQuotientToDiscrete K N
  inverse := discreteToEffectiveQuotient K N
  unitIso := NatIso.ofComponents
    (fun y ↦ eqToIso (discreteToEffectiveQuotient_obj_effectiveQuotientToDiscrete_obj K N y).symm)
    fun _ ↦ Subsingleton.elim _ _
  counitIso := NatIso.ofComponents (fun _ ↦ Iso.refl _) fun _ ↦ Subsingleton.elim _ _
  functor_unitIso_comp _ := Subsingleton.elim _ _

@[simp]
theorem effectiveQuotientEquivalence_functor :
    (effectiveQuotientEquivalence K N).functor = effectiveQuotientToDiscrete K N :=
  (rfl)

@[simp]
theorem effectiveQuotientEquivalence_inverse :
    (effectiveQuotientEquivalence K N).inverse = discreteToEffectiveQuotient K N :=
  (rfl)

/-- The arrow map of `effectiveQuotientToDiscrete` is a homeomorphism between the total arrows of
`EffectiveQuotient (SingleObj K × Discrete N)` and `Quiver.Total (Discrete N)`. -/
def effectiveQuotientArrowHomeomorph :
    Quiver.Total (EffectiveQuotient (SingleObj K × Discrete N)) ≃ₜ Quiver.Total (Discrete N) where
  toFun := (effectiveQuotientToDiscrete K N).toPrefunctor.mapTotal
  invFun := (discreteToEffectiveQuotient K N).toPrefunctor.mapTotal
  left_inv a := by
    obtain ⟨⟨⟨u₁, x₁⟩, ⟨u₂, x₂⟩, f⟩, rfl⟩ :=
      EffectiveQuotient.mapTotal_surjective (C := SingleObj K × Discrete N) a
    obtain rfl : u₁ = SingleObj.star K := Subsingleton.elim _ _
    obtain rfl : u₂ = SingleObj.star K := Subsingleton.elim _ _
    rw [effectiveQuotientToDiscrete_mapTotal_mapTotal, discreteToEffectiveQuotient_mapTotal]
    simp only [Prefunctor.mapTotal_mk]
    congr 1
    exact Subsingleton.elim _ _
  right_inv b := by
    rw [discreteToEffectiveQuotient_mapTotal, effectiveQuotientToDiscrete_mapTotal_mapTotal]
  continuous_toFun := by
    rw [EffectiveQuotient.isQuotientMap_mapTotal.continuous_iff]
    refine (UnitGroupoid.arrowHomeomorph N).isInducing.continuous_iff.mpr ?_
    convert continuous_snd.comp (arrowHomeomorph K N).continuous using 1
    funext a
    simp
  continuous_invFun := by
    let ι : Quiver.Total (Discrete N) → Quiver.Total (SingleObj K × Discrete N) :=
      fun b ↦ ⟨(SingleObj.star K, b.left), (SingleObj.star K, b.right),
        (𝟙 (SingleObj.star K), b.hom)⟩
    have hι : Continuous ι := by
      refine (arrowHomeomorph K N).isInducing.continuous_iff.mpr ?_
      convert (continuous_const (y := 𝟙 (SingleObj.star K))).prodMk
        (UnitGroupoid.arrowHomeomorph N).continuous using 1
      funext b
      simp [ι]
    convert EffectiveQuotient.isQuotientMap_mapTotal.continuous.comp hι using 1
    funext b
    simp [ι]

@[simp]
theorem coe_effectiveQuotientArrowHomeomorph :
    ⇑(effectiveQuotientArrowHomeomorph K N) =
      (effectiveQuotientToDiscrete K N).toPrefunctor.mapTotal :=
  (rfl)

@[simp]
theorem coe_effectiveQuotientArrowHomeomorph_symm :
    ⇑(effectiveQuotientArrowHomeomorph K N).symm =
      (discreteToEffectiveQuotient K N).toPrefunctor.mapTotal :=
  (rfl)

omit [TopologicalSpace K] [TopologicalSpace N] in
/-- At every object of `SingleObj K × Discrete N`, the automorphism group has order `Nat.card K`. -/
@[simp]
theorem card_aut (x : SingleObj K × Discrete N) :
    Nat.card (Aut x) = Nat.card K :=
  Nat.card_congr (autMulEquiv K N x).toEquiv.symm

section Etale

variable [DiscreteTopology K]

/-- Every ineffective kernel of the trivial gerbe `SingleObj K × Discrete N` is the whole isotropy
group. -/
@[simp]
theorem ineffectiveKernel_eq_top (x : SingleObj K × Discrete N) :
    ineffectiveKernel (isLocalHomeomorph_source K N) x = ⊤ :=
  eq_top_iff.mpr fun _ _ ↦ by simp [ineffectiveArrows_eq_univ]

/-- At every object of `SingleObj K × Discrete N`, the ineffective kernel has order `Nat.card K`. -/
theorem card_ineffectiveKernel (x : SingleObj K × Discrete N) :
    Nat.card (ineffectiveKernel (isLocalHomeomorph_source K N) x) = Nat.card K := by
  simp

/-- On the coarse space of `SingleObj K × Discrete N`, the ineffective-kernel order is the constant
`Nat.card K`. -/
@[simp]
theorem coarseCardIneffectiveKernel_eq_card
    (q : _root_.Quotient (isIsomorphicSetoid (SingleObj K × Discrete N))) :
    coarseCardIneffectiveKernel (isLocalHomeomorph_source K N) q = Nat.card K :=
  _root_.Quotient.inductionOn q fun x ↦
    (coarseCardIneffectiveKernel_mk _ x).trans (card_ineffectiveKernel K N x)

end Etale

section Nontrivial

omit [TopologicalSpace K] [TopologicalSpace N] in
/-- When `K` is nontrivial and `N` is nonempty, no functor from `SingleObj K × Discrete N` to
`Discrete N` is faithful. -/
theorem isEmpty_faithful_functor_discrete [Nontrivial K] [Nonempty N] :
    IsEmpty {F : SingleObj K × Discrete N ⥤ Discrete N // F.Faithful} :=
  ⟨fun ⟨F, hF⟩ ↦ by
    obtain ⟨y⟩ := ‹Nonempty N›
    obtain ⟨k₁, k₂, hk⟩ := exists_pair_ne K
    let x : SingleObj K × Discrete N := (SingleObj.star K, Discrete.mk y)
    have hmap : F.map ((k₁, 𝟙 (Discrete.mk y)) : x ⟶ x) =
        F.map ((k₂, 𝟙 (Discrete.mk y)) : x ⟶ x) :=
      Subsingleton.elim _ _
    exact hk (congrArg Prod.fst (hF.map_injective hmap))⟩

omit [TopologicalSpace K] [TopologicalSpace N] in
/-- When `K` is nontrivial and `N` is nonempty, `SingleObj K × Discrete N` is not categorically
equivalent to `Discrete N`. -/
theorem isEmpty_equivalence_discrete [Nontrivial K] [Nonempty N] :
    IsEmpty (SingleObj K × Discrete N ≌ Discrete N) :=
  ⟨fun e ↦ (isEmpty_faithful_functor_discrete K N).false ⟨e.functor, inferInstance⟩⟩

/-- When `K` is nontrivial and `N` is nonempty, the projection to the effective quotient of
`SingleObj K × Discrete N` is not faithful. -/
theorem not_faithful_toEffectiveQuotient [Nontrivial K] [Nonempty N] :
    ¬ (toEffectiveQuotient (SingleObj K × Discrete N)).Faithful := fun hF ↦
  (isEmpty_faithful_functor_discrete K N).false
    ⟨toEffectiveQuotient (SingleObj K × Discrete N) ⋙
      (effectiveQuotientEquivalence K N).functor,
      haveI := hF; Functor.Faithful.comp _ _⟩

/-- **Effective reduction is not an equivalence of categories.** When `K` is nontrivial and `N` is
nonempty, `SingleObj K × Discrete N` is not categorically equivalent (`≌`) to its effective
quotient, even though their coarse spaces are homeomorphic. -/
theorem isEmpty_equivalence_effectiveQuotient [Nontrivial K] [Nonempty N] :
    IsEmpty (SingleObj K × Discrete N ≌ EffectiveQuotient (SingleObj K × Discrete N)) :=
  ⟨fun e ↦ (isEmpty_equivalence_discrete K N).false
    (e.trans (effectiveQuotientEquivalence K N))⟩

end Nontrivial

end Groupoid

end TauCeti.TrivialGerbe
