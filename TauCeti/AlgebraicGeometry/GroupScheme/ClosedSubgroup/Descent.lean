/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.Descent.GroupScheme
public import TauCeti.AlgebraicGeometry.GroupScheme.ClosedSubgroup.BaseChange
import TauCeti.CategoryTheory.Monoidal.Mon

/-!
# Effective fpqc descent of closed subgroup schemes

Let `G₀` be an arbitrary group scheme over a base scheme `S`, and let `p : S' ⟶ S` be a morphism
of schemes. A closed subgroup scheme `P` of `G₀` pulls back to a closed subgroup scheme
`baseChange p P` of the base-changed group scheme `(Over.pullback p).mapGrp.obj G₀` over `S'`,
whose two pullbacks to `S' ×_S S'` agree under the canonical overlap isomorphism `overlapIso p G₀`
(`mapIso_overlapIso_baseChange`).

This file proves that:

* whenever every base change of `p` is an effective epimorphism, `baseChange p` reflects inclusions
  (`baseChange_le_baseChange_iff`) and is therefore injective (`baseChange_injective`);
* when `p` is surjective, flat and quasi-compact, every closed subgroup scheme `H'` of
  `(Over.pullback p).mapGrp.obj G₀` satisfying the overlap condition
  `mapIso (overlapIso p G₀) (baseChange (pullback.fst p p) H') = baseChange (pullback.snd p p) H'`
  descends uniquely to a closed subgroup scheme `descend p H' hH'` of `G₀`, giving an order
  isomorphism `descentOrderIso p G₀`;
* morphism properties satisfying fpqc descent (finiteness, flatness, local finite presentation) and
  finite-flat rank (`Scheme.Hom.finrank`) of the structure morphism to the base transfer between a
  closed subgroup scheme of `G₀` and its base change (or descent), and a finite locally free closed
  subgroup scheme of a commutative group scheme `G₀` bundles into a `FiniteFlatCommGroupScheme S`
  (`toFiniteFlatCommGroupScheme`).

## Main definitions and results

* `TauCeti.ClosedSubgroupScheme.baseChange_le_baseChange_iff` and
  `TauCeti.ClosedSubgroupScheme.baseChange_injective`: order-reflection and injectivity of
  `baseChange p` along morphisms with universally effective epimorphic pullbacks.
* `TauCeti.ClosedSubgroupScheme.exists_baseChange_eq`,
  `TauCeti.ClosedSubgroupScheme.descend`, and `TauCeti.ClosedSubgroupScheme.descentOrderIso`:
  effective fpqc descent of closed subgroup schemes of an arbitrary group scheme `G₀`.
* `TauCeti.ClosedSubgroupScheme.isFinite_baseChange_iff`,
  `TauCeti.ClosedSubgroupScheme.flat_baseChange_iff`,
  `TauCeti.ClosedSubgroupScheme.locallyOfFinitePresentation_baseChange_iff`,
  `TauCeti.ClosedSubgroupScheme.finrank_baseChange`, and
  `TauCeti.ClosedSubgroupScheme.finrank_descend`: fpqc descent of finite local freeness and rank
  for closed subgroup schemes.
* `TauCeti.ClosedSubgroupScheme.toFiniteFlatCommGroupScheme`: a finite locally free closed subgroup
  scheme of a commutative group scheme `G₀` over `S` as a `FiniteFlatCommGroupScheme S`.

## References

* A. Grothendieck, *Revêtements étales et groupe fondamental* (SGA 1), Exposé VIII, §1 and §2.
* N. M. Katz and B. Mazur, *Arithmetic Moduli of Elliptic Curves*, §1.12 and §4.7.
* [The Stacks Project, Tag 0245](https://stacks.math.columbia.edu/tag/0245).
-/

public section

open CategoryTheory Limits AlgebraicGeometry
open scoped CategoryTheory.Obj

attribute [local instance] Over.cartesianMonoidalCategory Over.braidedCategory

namespace TauCeti.ClosedSubgroupScheme

universe u

section BaseChangeProperties

variable {S S' : Scheme.{u}} (s : S' ⟶ S) {G₀ : Grp (Over S)} (P : ClosedSubgroupScheme G₀)

/-- If a closed subgroup scheme `P` of `G₀` is finite over `S`, then `baseChange s P` is finite
over `S'`. -/
instance isFinite_baseChange [IsFinite (P.1 : Grp (Over S)).X.hom] :
    IsFinite ((baseChange s P).1 : Grp (Over S')).X.hom :=
  MorphismProperty.of_isPullback (isPullback_baseChange_hom s P).flip ‹_›

/-- If a closed subgroup scheme `P` of `G₀` is flat over `S`, then `baseChange s P` is flat over
`S'`. -/
instance flat_baseChange [Flat (P.1 : Grp (Over S)).X.hom] :
    Flat ((baseChange s P).1 : Grp (Over S')).X.hom :=
  MorphismProperty.of_isPullback (isPullback_baseChange_hom s P).flip ‹_›

/-- If a closed subgroup scheme `P` of `G₀` is locally of finite presentation over `S`, then
`baseChange s P` is locally of finite presentation over `S'`. -/
instance locallyOfFinitePresentation_baseChange
    [LocallyOfFinitePresentation (P.1 : Grp (Over S)).X.hom] :
    LocallyOfFinitePresentation ((baseChange s P).1 : Grp (Over S')).X.hom :=
  MorphismProperty.of_isPullback (isPullback_baseChange_hom s P).flip ‹_›

/-- **Base-change invariance of rank for closed subgroup schemes.** If `P` is finite and flat over
`S`, the rank of `baseChange s P` over `S'` is the rank of `P` pulled back along `s`. -/
theorem finrank_baseChange [IsFinite (P.1 : Grp (Over S)).X.hom]
    [Flat (P.1 : Grp (Over S)).X.hom] :
    ((baseChange s P).1 : Grp (Over S')).X.hom.finrank =
      (P.1 : Grp (Over S)).X.hom.finrank ∘ s := by
  funext y
  exact Scheme.Hom.finrank_of_isPullback _ _ _ _ (isPullback_baseChange_hom s P).flip y

end BaseChangeProperties

section EffectiveEpi

variable {S S' : Scheme.{u}} (p : S' ⟶ S)
  [∀ {Z : Scheme.{u}} (g : Z ⟶ S), EffectiveEpi (pullback.fst g p)]
  {G₀ : Grp (Over S)}

/-- **Order-reflection of `baseChange` along universally effective epimorphic morphisms.** Let
`p : S' ⟶ S` be a morphism all of whose base changes are effective epimorphisms, and let `P` and
`Q` be closed subgroup schemes of `G₀`. Then `baseChange p P ≤ baseChange p Q` if and only if
`P ≤ Q`. -/
@[simp]
theorem baseChange_le_baseChange_iff {P Q : ClosedSubgroupScheme G₀} :
    baseChange p P ≤ baseChange p Q ↔ P ≤ Q := by
  refine ⟨fun h ↦ ?_, fun h ↦ baseChange_mono p h⟩
  let f₁ := (Over.pullback p).mapGrp.map P.1.arrow
  let f₂ := (Over.pullback p).mapGrp.map Q.1.arrow
  have hmk : Subobject.mk f₁ ≤ Subobject.mk f₂ := by
    have hle := Subtype.coe_le_coe.2 h
    rwa [baseChange_def, baseChange_def, coe_mk, coe_mk] at hle
  let u := Subobject.ofMkLEMk f₁ f₂ hmk
  have hu : u ≫ f₂ = f₁ := Subobject.ofMkLEMk_comp hmk
  let uOver : (Over.pullback p).obj (P.1 : Grp (Over S)).X ⟶
      (Over.pullback p).obj (Q.1 : Grp (Over S)).X := u.hom.hom
  have hcongr : uOver ≫ (Over.pullback p).map Q.1.arrow.hom.hom =
      (Over.pullback p).map P.1.arrow.hom.hom :=
    congrArg (fun φ ↦ φ.hom.hom) hu
  have hu_over : uOver ≫ (DescentDatum.baseChangeHom p Q.1.arrow.hom.hom).hom =
      (DescentDatum.baseChangeHom p P.1.arrow.hom.hom).hom := by
    rw [DescentDatum.baseChangeHom_hom, DescentDatum.baseChangeHom_hom]
    exact hcongr
  have : IsClosedImmersion (DescentDatum.baseChangeHom p Q.1.arrow.hom.hom).hom.left := by
    rw [DescentDatum.baseChangeHom_hom]
    exact MorphismProperty.of_isPullback
      (Over.isPullback_pullback_map_left p Q.1.arrow.hom.hom).flip inferInstance
  let uDD := DescentDatum.Hom.mkOfCompMono uOver
    (DescentDatum.baseChangeHom p Q.1.arrow.hom.hom)
    (DescentDatum.baseChangeHom p P.1.arrow.hom.hom) hu_over
  let u₀ := (DescentDatum.baseChangeGrpHomEquiv p
    (P.1 : Grp (Over S)) (Q.1 : Grp (Over S))).symm
    ⟨uDD, by
      rw [DescentDatum.Hom.mkOfCompMono_hom]
      exact (inferInstance : IsMonHom u.hom.hom)⟩
  have hu₀ : u₀ ≫ Q.1.arrow = P.1.arrow := by
    apply Grp.hom_ext
    apply (Over.pullback p).map_injective
    rw [Grp.comp', Mon.comp_hom', Functor.map_comp]
    have hdesc : (Over.pullback p).map u₀.hom.hom = uOver := by
      rw [← DescentDatum.baseChangeHom_hom]
      dsimp only [u₀]
      rw [DescentDatum.baseChangeGrpHomEquiv_symm_apply_hom_hom,
        DescentDatum.baseChangeHom_descend, DescentDatum.Hom.mkOfCompMono_hom]
    rw [hdesc]
    exact hcongr
  exact Subtype.coe_le_coe.1 (Subobject.le_of_comm u₀ hu₀)

/-- **Injectivity of `baseChange` on closed subgroup schemes.** Along a morphism `p : S' ⟶ S` all
of whose base changes are effective epimorphisms, a closed subgroup scheme of `G₀` is uniquely
determined by its base change along `p`. -/
theorem baseChange_injective : Function.Injective (baseChange (G := G₀) p) :=
  fun _ _ h ↦ le_antisymm ((baseChange_le_baseChange_iff p).1 h.le)
    ((baseChange_le_baseChange_iff p).1 h.ge)

end EffectiveEpi

section FpqcDescent

variable {S S' : Scheme.{u}} (p : S' ⟶ S) [Surjective p] [Flat p] [QuasiCompact p]
  {G₀ : Grp (Over S)}

/-- Given a closed subgroup scheme `H'` of `(Over.pullback p).mapGrp.obj G₀` satisfying the overlap
condition on `S' ×_S S'`, the canonical descent datum on `(Over.pullback p).obj G₀.X` restricts to
`(H'.1 : Grp (Over S')).X`. -/
private theorem exists_restricted_descentDatum
    {p : S' ⟶ S} {G₀ : Grp (Over S)}
    (H' : ClosedSubgroupScheme ((Over.pullback p).mapGrp.obj G₀))
    (hH' : mapIso (overlapIso p G₀) (baseChange (pullback.fst p p) H') =
      baseChange (pullback.snd p p) H') :
    ∃ (D : DescentDatum p (H'.1 : Grp (Over S')).X)
      (φ : DescentDatum.Hom D (DescentDatum.baseChange p G₀.X)),
      D.IsMon ∧ φ.hom = H'.1.arrow.hom.hom := by
  let K : Grp (Over S') := (H'.1 : Grp (Over S'))
  let i : K ⟶ (Over.pullback p).mapGrp.obj G₀ := H'.1.arrow
  let iOver : K.X ⟶ (Over.pullback p).obj G₀.X := i.hom.hom
  have : IsClosedImmersion iOver.left := isClosedImmersion_arrow H'
  let f₁ := (Over.pullback (pullback.fst p p)).mapGrp.map i ≫ (overlapIso p G₀).hom
  let f₂ := (Over.pullback (pullback.snd p p)).mapGrp.map i
  have hmk : Subobject.mk f₁ ≤ Subobject.mk f₂ := by
    have heq := Subtype.ext_iff.1 hH'
    rw [baseChange_def, baseChange_def, coe_mapIso, coe_mk, coe_mk, Subobject.map_mk] at heq
    exact heq.le
  let u := Subobject.ofMkLEMk f₁ f₂ hmk
  have hu : u ≫ f₂ = f₁ := Subobject.ofMkLEMk_comp hmk
  let pair : pullback p (K.X.hom ≫ p) ⟶ pullback p p :=
    pullback.lift (pullback.snd p (K.X.hom ≫ p) ≫ K.X.hom) (pullback.fst p (K.X.hom ≫ p))
      (by rw [Category.assoc, ← pullback.condition])
  let θ : pullback p (K.X.hom ≫ p) ⟶ pullback K.X.hom (pullback.fst p p) :=
    pullback.lift (pullback.snd p (K.X.hom ≫ p)) pair (by simp [pair])
  let act : pullback p (K.X.hom ≫ p) ⟶ K.X.left :=
    θ ≫ u.hom.hom.left ≫ pullback.fst K.X.hom (pullback.snd p p)
  have hact : act ≫ iOver.left =
      pullback.map p (K.X.hom ≫ p) p (((Over.pullback p).obj G₀.X).hom ≫ p) (𝟙 S') iOver.left
        (𝟙 S) (by simp) (by rw [← Over.w_assoc iOver, Category.comp_id]) ≫
        (DescentDatum.baseChange p G₀.X).act := by
    have hu_left : u.hom.hom.left ≫ ((Over.pullback (pullback.snd p p)).map iOver).left =
        ((Over.pullback (pullback.fst p p)).map iOver).left ≫
          (overlapIso p G₀).hom.hom.hom.left :=
      congrArg (fun φ ↦ φ.hom.hom.left) hu
    have hf₂_fst : ((Over.pullback (pullback.snd p p)).map iOver).left ≫
        pullback.fst ((Over.pullback p).obj G₀.X).hom (pullback.snd p p) =
        pullback.fst K.X.hom (pullback.snd p p) ≫ iOver.left := by
      simp
    have hθ : act ≫ iOver.left =
        θ ≫ ((Over.pullback (pullback.fst p p)).map iOver).left ≫
          pullback.lift
            (pullback.fst ((Over.pullback p).obj G₀.X).hom (pullback.fst p p) ≫
              pullback.fst G₀.X.hom p)
            (pullback.snd ((Over.pullback p).obj G₀.X).hom (pullback.fst p p) ≫
              pullback.snd p p)
            (by
              rw [Category.assoc, pullback.condition, ← Over.pullback_obj_hom p G₀.X,
                pullback.condition_assoc, pullback.condition, Category.assoc]) := by
      refine (Category.assoc θ _ _).trans ?_
      refine congrArg (θ ≫ ·) ?_
      refine (Category.assoc u.hom.hom.left _ _).trans ?_
      refine (congrArg (u.hom.hom.left ≫ ·) hf₂_fst.symm).trans ?_
      refine (Category.assoc _ _ _).symm.trans ?_
      refine (congrArg (· ≫ pullback.fst ((Over.pullback p).obj G₀.X).hom (pullback.snd p p))
        hu_left).trans ?_
      exact (Category.assoc _ _ _).trans
        (congrArg (((Over.pullback (pullback.fst p p)).map iOver).left ≫ ·)
          (overlapIso_hom_left_fst p G₀))
    rw [hθ]
    refine pullback.hom_ext ?_ ?_ <;> simp [θ, pair]
  have : IsMonHom (DescentDatum.ofMonoHom
      (DescentDatum.baseChange p G₀.X) iOver act hact).hom := by
    rw [DescentDatum.ofMonoHom_hom]
    exact (inferInstance : IsMonHom i.hom.hom)
  have : Mono (DescentDatum.ofMonoHom
      (DescentDatum.baseChange p G₀.X) iOver act hact).hom.left := by
    rw [DescentDatum.ofMonoHom_hom]
    infer_instance
  exact ⟨DescentDatum.ofMono (DescentDatum.baseChange p G₀.X) iOver act hact,
    DescentDatum.ofMonoHom (DescentDatum.baseChange p G₀.X) iOver act hact,
    (DescentDatum.ofMonoHom (DescentDatum.baseChange p G₀.X) iOver act hact).isMon_of_mono,
    DescentDatum.ofMonoHom_hom (DescentDatum.baseChange p G₀.X) iOver act hact⟩

/-- **Existence of fpqc descent for closed subgroup schemes.** Let `p : S' ⟶ S` be surjective, flat
and quasi-compact, and let `G₀` be an arbitrary group scheme over `S`. Every closed subgroup scheme
`H'` of `(Over.pullback p).mapGrp.obj G₀` whose two pullbacks to `S' ×_S S'` agree under
`overlapIso p G₀` is the base change along `p` of a closed subgroup scheme of `G₀`. -/
theorem exists_baseChange_eq
    (H' : ClosedSubgroupScheme ((Over.pullback p).mapGrp.obj G₀))
    (hH' : mapIso (overlapIso p G₀) (baseChange (pullback.fst p p) H') =
      baseChange (pullback.snd p p) H') :
    ∃ P : ClosedSubgroupScheme G₀, baseChange p P = H' := by
  obtain ⟨D, φ, _, hφ⟩ := exists_restricted_descentDatum H' hH'
  have : IsMonHom φ.hom := by
    have hm : IsMonHom H'.1.arrow.hom.hom := inferInstance
    exact hφ.symm ▸ hm
  have : IsClosedImmersion φ.hom.left := by
    have hc : IsClosedImmersion H'.1.arrow.hom.hom.left := isClosedImmersion_arrow H'
    rwa [hφ]
  obtain ⟨K₀, i₀, g, _, _, hcomp, _⟩ :=
    φ.exists_grp_baseChange_hom_isIso_of_isClosedImmersion
  refine ⟨mk i₀, ?_⟩
  rw [baseChange_mk]
  refine Subtype.ext ?_
  rw [coe_mk]
  let eg : (Over.pullback p).obj K₀.X ≅ (H'.1 : Grp (Over S')).X := asIso g.hom
  let e : (Over.pullback p).mapGrp.obj K₀ ≅ (H'.1 : Grp (Over S')) :=
    Grp.mkIso (G := (Over.pullback p).mapGrp.obj K₀) (H := (H'.1 : Grp (Over S')))
      eg (IsMonHom.one_hom g.hom) (IsMonHom.mul_hom g.hom)
  have he : e.hom ≫ H'.1.arrow = (Over.pullback p).mapGrp.map i₀ := by
    apply Grp.hom_ext
    have hmap := congrArg DescentDatum.Hom.hom hcomp
    simp only [DescentDatum.Hom.comp_hom, hφ, DescentDatum.baseChangeHom_hom] at hmap
    exact hmap
  exact (Subobject.mk_eq_mk_of_comm ((Over.pullback p).mapGrp.map i₀) H'.1.arrow e he).trans
    (Subobject.mk_arrow H'.1)

/-- **Effective fpqc descent of a closed subgroup scheme.** Given `p : S' ⟶ S` surjective, flat and
quasi-compact and a closed subgroup scheme `H'` of `(Over.pullback p).mapGrp.obj G₀` satisfying the
overlap condition on `S' ×_S S'`, `descend p H' hH'` is the unique closed subgroup scheme of `G₀`
whose base change along `p` is `H'`. -/
noncomputable def descend
    (H' : ClosedSubgroupScheme ((Over.pullback p).mapGrp.obj G₀))
    (hH' : mapIso (overlapIso p G₀) (baseChange (pullback.fst p p) H') =
      baseChange (pullback.snd p p) H') :
    ClosedSubgroupScheme G₀ :=
  (exists_baseChange_eq p H' hH').choose

/-- Base-changing `descend p H' hH'` along `p` recovers `H'`. -/
@[simp]
theorem baseChange_descend
    (H' : ClosedSubgroupScheme ((Over.pullback p).mapGrp.obj G₀))
    (hH' : mapIso (overlapIso p G₀) (baseChange (pullback.fst p p) H') =
      baseChange (pullback.snd p p) H') :
    baseChange p (descend p H' hH') = H' :=
  (exists_baseChange_eq p H' hH').choose_spec

/-- Descending the base change of a closed subgroup scheme `P` of `G₀` recovers `P`. -/
@[simp]
theorem descend_baseChange (P : ClosedSubgroupScheme G₀) :
    descend p (baseChange p P) (mapIso_overlapIso_baseChange p P) = P :=
  baseChange_injective p (baseChange_descend p _ _)

/-- Uniqueness characterization of `descend p H' hH'`. -/
theorem eq_descend_iff {P : ClosedSubgroupScheme G₀}
    {H' : ClosedSubgroupScheme ((Over.pullback p).mapGrp.obj G₀)}
    {hH' : mapIso (overlapIso p G₀) (baseChange (pullback.fst p p) H') =
      baseChange (pullback.snd p p) H'} :
    P = descend p H' hH' ↔ baseChange p P = H' :=
  ⟨fun h ↦ h ▸ baseChange_descend p H' hH',
    fun h ↦ baseChange_injective p (h.trans (baseChange_descend p H' hH').symm)⟩

variable (G₀) in
/-- **Effective fpqc descent equivalence for closed subgroup schemes.** Base change along a
surjective, flat and quasi-compact morphism `p : S' ⟶ S` is an order isomorphism from closed
subgroup schemes of `G₀` to closed subgroup schemes of `(Over.pullback p).mapGrp.obj G₀` whose two
pullbacks to `S' ×_S S'` correspond under `overlapIso p G₀`. -/
noncomputable def descentOrderIso :
    ClosedSubgroupScheme G₀ ≃o
      {H' : ClosedSubgroupScheme ((Over.pullback p).mapGrp.obj G₀) //
        mapIso (overlapIso p G₀) (baseChange (pullback.fst p p) H') =
          baseChange (pullback.snd p p) H'} where
  toFun P := ⟨baseChange p P, mapIso_overlapIso_baseChange p P⟩
  invFun H' := descend p H'.1 H'.2
  left_inv P := descend_baseChange p P
  right_inv H' := Subtype.ext (baseChange_descend p H'.1 H'.2)
  map_rel_iff' := baseChange_le_baseChange_iff p

@[simp]
theorem descentOrderIso_apply_coe (P : ClosedSubgroupScheme G₀) :
    (descentOrderIso p G₀ P : ClosedSubgroupScheme ((Over.pullback p).mapGrp.obj G₀)) =
      baseChange p P :=
  (rfl)

@[simp]
theorem descentOrderIso_symm_apply
    (H' : {H' : ClosedSubgroupScheme ((Over.pullback p).mapGrp.obj G₀) //
      mapIso (overlapIso p G₀) (baseChange (pullback.fst p p) H') =
        baseChange (pullback.snd p p) H'}) :
    (descentOrderIso p G₀).symm H' = descend p H'.1 H'.2 :=
  (rfl)

/-- **Fpqc descent of morphism properties on closed subgroup schemes.** For any morphism property
`M` stable under base change and satisfying fpqc descent, the structure morphism to the base of
`baseChange p P` satisfies `M` if and only if that of `P` does. -/
theorem hom_mem_baseChange_iff {M : MorphismProperty Scheme.{u}}
    [M.IsStableUnderBaseChange] [M.DescendsAlong (@Surjective ⊓ @Flat ⊓ @QuasiCompact)]
    (P : ClosedSubgroupScheme G₀) :
    M ((baseChange p P).1 : Grp (Over S')).X.hom ↔ M (P.1 : Grp (Over S)).X.hom :=
  ⟨fun h ↦ MorphismProperty.of_isPullback_of_descendsAlong
      (Q := @Surjective ⊓ @Flat ⊓ @QuasiCompact)
      (isPullback_baseChange_hom p P) ⟨⟨inferInstance, inferInstance⟩, inferInstance⟩ h,
    fun h ↦ MorphismProperty.of_isPullback (isPullback_baseChange_hom p P).flip h⟩

/-- Finiteness over the base descends along fpqc covers for closed subgroup schemes. -/
@[simp]
theorem isFinite_baseChange_iff (P : ClosedSubgroupScheme G₀) :
    IsFinite ((baseChange p P).1 : Grp (Over S')).X.hom ↔
      IsFinite (P.1 : Grp (Over S)).X.hom :=
  hom_mem_baseChange_iff p P

/-- Flatness over the base descends along fpqc covers for closed subgroup schemes. -/
@[simp]
theorem flat_baseChange_iff (P : ClosedSubgroupScheme G₀) :
    Flat ((baseChange p P).1 : Grp (Over S')).X.hom ↔
      Flat (P.1 : Grp (Over S)).X.hom :=
  hom_mem_baseChange_iff p P

/-- Local finite presentation over the base descends along fpqc covers for closed subgroup
schemes. -/
@[simp]
theorem locallyOfFinitePresentation_baseChange_iff (P : ClosedSubgroupScheme G₀) :
    LocallyOfFinitePresentation ((baseChange p P).1 : Grp (Over S')).X.hom ↔
      LocallyOfFinitePresentation (P.1 : Grp (Over S)).X.hom :=
  hom_mem_baseChange_iff p P

/-- If `H'` is finite over `S'`, its descended closed subgroup scheme `descend p H' hH'` is finite
over `S`. -/
theorem isFinite_descend
    (H' : ClosedSubgroupScheme ((Over.pullback p).mapGrp.obj G₀))
    (hH' : mapIso (overlapIso p G₀) (baseChange (pullback.fst p p) H') =
      baseChange (pullback.snd p p) H')
    [IsFinite (H'.1 : Grp (Over S')).X.hom] :
    IsFinite ((descend p H' hH').1 : Grp (Over S)).X.hom := by
  rw [← isFinite_baseChange_iff p, baseChange_descend]
  infer_instance

/-- If `H'` is flat over `S'`, its descended closed subgroup scheme `descend p H' hH'` is flat over
`S`. -/
theorem flat_descend
    (H' : ClosedSubgroupScheme ((Over.pullback p).mapGrp.obj G₀))
    (hH' : mapIso (overlapIso p G₀) (baseChange (pullback.fst p p) H') =
      baseChange (pullback.snd p p) H')
    [Flat (H'.1 : Grp (Over S')).X.hom] :
    Flat ((descend p H' hH').1 : Grp (Over S)).X.hom := by
  rw [← flat_baseChange_iff p, baseChange_descend]
  infer_instance

/-- If `H'` is locally of finite presentation over `S'`, its descended closed subgroup scheme
`descend p H' hH'` is locally of finite presentation over `S`. -/
theorem locallyOfFinitePresentation_descend
    (H' : ClosedSubgroupScheme ((Over.pullback p).mapGrp.obj G₀))
    (hH' : mapIso (overlapIso p G₀) (baseChange (pullback.fst p p) H') =
      baseChange (pullback.snd p p) H')
    [LocallyOfFinitePresentation (H'.1 : Grp (Over S')).X.hom] :
    LocallyOfFinitePresentation ((descend p H' hH').1 : Grp (Over S)).X.hom := by
  rw [← locallyOfFinitePresentation_baseChange_iff p, baseChange_descend]
  infer_instance

/-- **Rank of a descended finite flat closed subgroup scheme.** If `H'` is finite and flat over
`S'`, then the rank of `H'` over `S'` is the rank of `descend p H' hH'` pulled back along `p`. -/
theorem finrank_descend
    (H' : ClosedSubgroupScheme ((Over.pullback p).mapGrp.obj G₀))
    (hH' : mapIso (overlapIso p G₀) (baseChange (pullback.fst p p) H') =
      baseChange (pullback.snd p p) H')
    [IsFinite (H'.1 : Grp (Over S')).X.hom] [Flat (H'.1 : Grp (Over S')).X.hom] :
    (H'.1 : Grp (Over S')).X.hom.finrank =
      ((descend p H' hH').1 : Grp (Over S)).X.hom.finrank ∘ p := by
  have : IsFinite ((descend p H' hH').1 : Grp (Over S)).X.hom := isFinite_descend p H' hH'
  have : Flat ((descend p H' hH').1 : Grp (Over S)).X.hom := flat_descend p H' hH'
  have h := finrank_baseChange p (descend p H' hH')
  have hbc : ((baseChange p (descend p H' hH')).1 : Grp (Over S')).X.hom.finrank =
      (H'.1 : Grp (Over S')).X.hom.finrank := by
    rw [baseChange_descend]
  exact hbc.symm.trans h

end FpqcDescent

section FiniteFlat

variable {S : Scheme.{u}} {G₀ : Grp (Over S)} [IsCommMonObj G₀.X]

/-- Every closed subgroup scheme of a commutative group scheme is commutative. -/
instance isCommMonObj_underlying (P : ClosedSubgroupScheme G₀) :
    IsCommMonObj (P.1 : Grp (Over S)).X := by
  have := Over.mono_of_mono_left P.1.arrow.hom.hom
  exact isCommMonObj_of_mono P.1.arrow.hom.hom

/-- A closed subgroup scheme `P` of a commutative group scheme `G₀` over `S` whose structure
morphism to `S` is finite, flat, and locally of finite presentation bundles into a
`FiniteFlatCommGroupScheme S`. -/
noncomputable def toFiniteFlatCommGroupScheme (P : ClosedSubgroupScheme G₀)
    [IsFinite (P.1 : Grp (Over S)).X.hom] [Flat (P.1 : Grp (Over S)).X.hom]
    [LocallyOfFinitePresentation (P.1 : Grp (Over S)).X.hom] :
    TauCeti.AlgebraicGeometry.FiniteFlatCommGroupScheme S where
  carrier := (P.1 : Grp (Over S)).X.left
  structureMap := (P.1 : Grp (Over S)).X.hom
  grp := (P.1 : Grp (Over S)).grp
  comm := isCommMonObj_underlying P
  finite := inferInstance
  flat := inferInstance
  locallyOfFinitePresentation := inferInstance

/-- The underlying scheme of `P.toFiniteFlatCommGroupScheme` is `(P.1 : Grp (Over S)).X.left`. -/
@[simp]
theorem toFiniteFlatCommGroupScheme_carrier (P : ClosedSubgroupScheme G₀)
    [IsFinite (P.1 : Grp (Over S)).X.hom] [Flat (P.1 : Grp (Over S)).X.hom]
    [LocallyOfFinitePresentation (P.1 : Grp (Over S)).X.hom] :
    P.toFiniteFlatCommGroupScheme.carrier = (P.1 : Grp (Over S)).X.left :=
  (rfl)

/-- The `S`-scheme underlying `P.toFiniteFlatCommGroupScheme` is
`Over.mk (P.1 : Grp (Over S)).X.hom`. -/
@[simp]
theorem toFiniteFlatCommGroupScheme_toOver (P : ClosedSubgroupScheme G₀)
    [IsFinite (P.1 : Grp (Over S)).X.hom] [Flat (P.1 : Grp (Over S)).X.hom]
    [LocallyOfFinitePresentation (P.1 : Grp (Over S)).X.hom] :
    P.toFiniteFlatCommGroupScheme.toOver = Over.mk (P.1 : Grp (Over S)).X.hom :=
  (rfl)

/-- The rank function of `P.toFiniteFlatCommGroupScheme` is that of `(P.1 : Grp (Over S)).X.hom`. -/
@[simp]
theorem finrank_toFiniteFlatCommGroupScheme_structureMap (P : ClosedSubgroupScheme G₀)
    [IsFinite (P.1 : Grp (Over S)).X.hom] [Flat (P.1 : Grp (Over S)).X.hom]
    [LocallyOfFinitePresentation (P.1 : Grp (Over S)).X.hom] :
    P.toFiniteFlatCommGroupScheme.structureMap.finrank =
      (P.1 : Grp (Over S)).X.hom.finrank :=
  (rfl)

end FiniteFlat

end TauCeti.ClosedSubgroupScheme
