/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.Descent.OverBaseChange
public import TauCeti.AlgebraicGeometry.GroupScheme.ClosedSubgroup.BaseChange
public import TauCeti.CategoryTheory.EffectiveEpi.GrpObj
public import TauCeti.CategoryTheory.Monoidal.Grp.Pullback

/-!
# Effective fpqc descent of closed subgroup schemes

Let `G` be an arbitrary group scheme over a base scheme `S`, and let `p : S' ⟶ S` be surjective,
flat and quasi-compact.

First, for explicit descent data (`TauCeti.DescentDatum`), a closed subgroup immersion into
`G ×_S S'` respecting a descent datum descends to a closed subgroup of `G`, with a comparison
preserving both the descent datum and the group law
(`TauCeti.DescentDatum.Hom.exists_grp_baseChange_hom_isIso_of_isClosedImmersion`). Compatibility of
the local group operations with descent follows automatically from the subgroup inclusion via
`TauCeti.exists_grpObj_isMonHom_pullback_iff`. When the subgroup is finite locally free over `S'`,
the descended subgroup is finite locally free over `S` with pulled-back rank
(`TauCeti.DescentDatum.Hom.exists_finiteLocallyFree_grp_baseChange_hom_isIso_of_isClosedImmersion`).

Second, at the subobject level (`TauCeti.ClosedSubgroupScheme`), a closed subgroup scheme `P` of
`G₀` pulls back to a closed subgroup scheme `baseChange p P` of `(Over.pullback p).mapGrp.obj G₀`
over `S'`, whose two pullbacks to `S' ×_S S'` agree under `Grp.pullbackOverlapIso p G₀`
(`mapIso_pullbackOverlapIso_baseChange`). This file proves that:

* whenever every base change of `p` is an effective epimorphism, `baseChange p` reflects inclusions
  (`baseChange_le_baseChange_iff`) and is therefore injective (`baseChange_injective`);
* when `p` is surjective, flat and quasi-compact, every closed subgroup scheme `H'` of
  `(Over.pullback p).mapGrp.obj G₀` satisfying the overlap condition
  `mapIso (Grp.pullbackOverlapIso p G₀) (baseChange (pullback.fst p p) H') =`
  `baseChange (pullback.snd p p) H'`
  descends uniquely to a closed subgroup scheme `descend p H' hH'` of `G₀`, giving an order
  isomorphism `descentOrderIso p G₀`;
* morphism properties satisfying fpqc descent (finiteness, flatness, local finite presentation) and
  finite-flat rank (`Scheme.Hom.finrank`) of the structure morphism to the base transfer between a
  closed subgroup scheme of `G₀` and its base change or descent (`finrank_descend`).

## Main definitions and results

* `TauCeti.DescentDatum.Hom.exists_grp_baseChange_hom_isIso_of_isClosedImmersion` and
  `TauCeti.DescentDatum.Hom.exists_finiteLocallyFree_grp_baseChange_hom_isIso_of_isClosedImmersion`:
  effective fpqc descent of closed subgroup immersions with descent data, preserving finite local
  freeness and rank.
* `TauCeti.ClosedSubgroupScheme.baseChange_le_baseChange_iff` and
  `TauCeti.ClosedSubgroupScheme.baseChange_injective`: order-reflection and injectivity of
  `baseChange p` along morphisms with universally effective epimorphic pullbacks.
* `TauCeti.ClosedSubgroupScheme.exists_baseChange_eq`,
  `TauCeti.ClosedSubgroupScheme.descend`, and `TauCeti.ClosedSubgroupScheme.descentOrderIso`:
  effective fpqc descent of closed subgroup schemes of an arbitrary group scheme `G₀`.
* `TauCeti.ClosedSubgroupScheme.isFinite_baseChange_iff`,
  `TauCeti.ClosedSubgroupScheme.flat_baseChange_iff`,
  `TauCeti.ClosedSubgroupScheme.locallyOfFinitePresentation_baseChange_iff`, and
  `TauCeti.ClosedSubgroupScheme.finrank_descend`: fpqc descent of finite local freeness and rank
  for closed subgroup schemes.

## References

* A. Grothendieck, *Revêtements étales et groupe fondamental* (SGA 1), Exposé VIII, §1 and §2.
* N. M. Katz and B. Mazur, *Arithmetic Moduli of Elliptic Curves*, §1.3, §1.12, and §4.7.
* [The Stacks Project, Tag 0245](https://stacks.math.columbia.edu/tag/0245).
-/

public section

open CategoryTheory Limits AlgebraicGeometry
open scoped MonObj Obj

namespace TauCeti.DescentDatum

universe u

variable {S S' : Scheme.{u}} {p : S' ⟶ S} [Surjective p] [Flat p] [QuasiCompact p]
  {G : Grp (Over S)} {H : Over S'} [GrpObj H] {D : DescentDatum p H}

/-- **Effective fpqc descent of a stable closed subgroup.** A closed subgroup of the base change
of `G`, whose inclusion respects a descent datum, descends to a closed subgroup of `G`.
The comparison is simultaneously an isomorphism of descent data and a group homomorphism. -/
theorem Hom.exists_grp_baseChange_hom_isIso_of_isClosedImmersion
    (i : Hom D (baseChange p G.X)) [IsClosedImmersion i.hom.left] [IsMonHom i.hom] :
    ∃ (K : Grp (Over S)) (j : K ⟶ G) (e : Hom (baseChange p K.X) D),
      IsClosedImmersion j.hom.hom.left ∧ IsIso e.hom ∧ IsMonHom e.hom ∧
        i.comp e = baseChangeHom p j.hom.hom := by
  obtain ⟨W, e, he, hfac, hW⟩ := i.exists_baseChange_hom_isIso_of_isClosedImmersion
  let K₀ : Over S := Over.mk (W.hom ≫ G.X.hom)
  let j₀ : K₀ ⟶ G.X := Over.homMk W.hom
  have hj₀ : IsClosedImmersion j₀.left := by
    simpa only [j₀, Over.homMk_left] using hW
  have : Mono j₀ := Over.mono_of_mono_left j₀
  have heq : e.hom ≫ i.hom = (Over.pullback p).map j₀ := by
    simpa only [Hom.comp_hom, baseChangeHom_hom] using congr(Hom.hom $hfac)
  -- Transport the local subgroup structure to the chosen pullback of the descended carrier.
  let hlocal : GrpObj ((Over.pullback p).obj K₀) := GrpObj.ofIso (asIso e.hom).symm
  have hcomp : IsMonHom e.hom := by
    have := isMonHom_ofIso (asIso e.hom).symm
    rw [← asIso_hom e.hom, ← Iso.symm_inv]
    infer_instance
  have hjlocal : IsMonHom ((Over.pullback p).map j₀) := by
    rw [← heq]
    infer_instance
  obtain ⟨hK, hj⟩ := (exists_grpObj_isMonHom_pullback_iff p j₀).1 ⟨hlocal, hjlocal⟩
  let := hK
  let := hj
  -- The two group structures on the pullback have the same monic inclusion into `G`.
  have hstructures : Functor.grpObjObj (F := Over.pullback p) (G := K₀) = hlocal :=
    grpObj_eq_of_mono ((Over.pullback p).map j₀) _ _ inferInstance hjlocal
  have hehom : @IsMonHom _ _ _ ((Over.pullback p).obj K₀) H
      (Functor.grpObjObj (F := Over.pullback p) (G := K₀)).toMonObj inferInstance e.hom := by
    rw [hstructures]
    exact hcomp
  refine ⟨Grp.mk K₀, Grp.homMk j₀, e, ?_, he, hehom, ?_⟩
  · simpa only [Grp.homMk_hom_hom] using hj₀
  · simpa only [Grp.homMk_hom_hom, j₀] using hfac

/-- **Effective fpqc descent of finite locally free subgroup schemes, with rank.** A stable
closed subgroup which is finite, flat and locally of finite presentation over the cover descends
with these three properties. Its finite-flat rank is pulled back from the descended subgroup. -/
theorem Hom.exists_finiteLocallyFree_grp_baseChange_hom_isIso_of_isClosedImmersion
    [IsFinite H.hom] [Flat H.hom] [LocallyOfFinitePresentation H.hom]
    (i : Hom D (baseChange p G.X)) [IsClosedImmersion i.hom.left] [IsMonHom i.hom] :
    ∃ (K : Grp (Over S)) (j : K ⟶ G) (e : Hom (baseChange p K.X) D),
      IsClosedImmersion j.hom.hom.left ∧ IsIso e.hom ∧ IsMonHom e.hom ∧
        i.comp e = baseChangeHom p j.hom.hom ∧
        IsFinite K.X.hom ∧ Flat K.X.hom ∧ LocallyOfFinitePresentation K.X.hom ∧
        H.hom.finrank = K.X.hom.finrank ∘ p := by
  obtain ⟨K, j, e, hj, he, hehom, hfac⟩ := i.exists_grp_baseChange_hom_isIso_of_isClosedImmersion
  have : IsFinite K.X.hom := e.mem_of_descendsAlong (P := @IsFinite) inferInstance
  have : Flat K.X.hom := e.mem_of_descendsAlong (P := @Flat) inferInstance
  have : LocallyOfFinitePresentation K.X.hom :=
    e.mem_of_descendsAlong (P := @LocallyOfFinitePresentation) inferInstance
  refine ⟨K, j, e, hj, he, hehom, hfac, inferInstance, inferInstance, inferInstance, ?_⟩
  funext s
  have hw := e.hom.w
  simp only [Over.pullback_obj_hom] at hw
  rw [← Scheme.Hom.finrank_comp_left_of_isIso e.hom.left H.hom, hw]
  exact Scheme.Hom.finrank_pullback_snd _ _ s

end TauCeti.DescentDatum

namespace TauCeti.ClosedSubgroupScheme

attribute [local instance] Over.cartesianMonoidalCategory Over.braidedCategory

universe u

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
  let f₁ := (Over.pullback p).mapGrp.map P.val.arrow
  let f₂ := (Over.pullback p).mapGrp.map Q.val.arrow
  have hmk : Subobject.mk f₁ ≤ Subobject.mk f₂ := by
    have hle := Subtype.coe_le_coe.2 h
    rwa [baseChange_def, baseChange_def, coe_mk, coe_mk] at hle
  let u := Subobject.ofMkLEMk f₁ f₂ hmk
  have hu : u ≫ f₂ = f₁ := Subobject.ofMkLEMk_comp hmk
  let uOver : (Over.pullback p).obj (P.val : Grp (Over S)).X ⟶
      (Over.pullback p).obj (Q.val : Grp (Over S)).X := u.hom.hom
  have hcongr : uOver ≫ (Over.pullback p).map Q.val.arrow.hom.hom =
      (Over.pullback p).map P.val.arrow.hom.hom :=
    congrArg (fun φ ↦ φ.hom.hom) hu
  have hu_over : uOver ≫ (DescentDatum.baseChangeHom p Q.val.arrow.hom.hom).hom =
      (DescentDatum.baseChangeHom p P.val.arrow.hom.hom).hom := by
    rw [DescentDatum.baseChangeHom_hom, DescentDatum.baseChangeHom_hom]
    exact hcongr
  have : IsClosedImmersion (DescentDatum.baseChangeHom p Q.val.arrow.hom.hom).hom.left := by
    rw [DescentDatum.baseChangeHom_hom]
    exact MorphismProperty.of_isPullback
      (Over.isPullback_pullback_map_left p Q.val.arrow.hom.hom).flip inferInstance
  let uDD := DescentDatum.Hom.mkOfCompMono uOver
    (DescentDatum.baseChangeHom p Q.val.arrow.hom.hom)
    (DescentDatum.baseChangeHom p P.val.arrow.hom.hom) hu_over
  let u₀ := (DescentDatum.baseChangeGrpHomEquiv p
    (P.val : Grp (Over S)) (Q.val : Grp (Over S))).symm
    ⟨uDD, by
      rw [DescentDatum.Hom.mkOfCompMono_hom]
      exact (inferInstance : IsMonHom u.hom.hom)⟩
  have hu₀ : u₀ ≫ Q.val.arrow = P.val.arrow := by
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

/-- Given a morphism `iOver : K ⟶ G₀ ×_S S'` over `S'` and a morphism `u` between the two pullbacks
of `K` to `S' ×_S S'` intertwining `iOver` with `Grp.pullbackOverlapIso p G₀`, evaluating `u` on
`(k, (π k, s₂))` and projecting to `K` yields an action `S' ×_S K ⟶ K` that intertwines `iOver` with
the canonical descent action on `G₀ ×_S S'`. -/
private theorem overlap_act_comp_left {p : S' ⟶ S} {G₀ : Grp (Over S)} {K : Over S'}
    (iOver : K ⟶ (Over.pullback p).obj G₀.X)
    (u : (Over.pullback (pullback.fst p p)).obj K ⟶
      (Over.pullback (pullback.snd p p)).obj K)
    (hu : u.left ≫ ((Over.pullback (pullback.snd p p)).map iOver).left =
      ((Over.pullback (pullback.fst p p)).map iOver).left ≫
        (Grp.pullbackOverlapIso p G₀).hom.hom.hom.left) :
    (pullback.lift (pullback.snd p (K.hom ≫ p))
        (pullback.lift (pullback.snd p (K.hom ≫ p) ≫ K.hom) (pullback.fst p (K.hom ≫ p))
          (by rw [Category.assoc, ← pullback.condition]))
        (by simp) ≫
      u.left ≫ pullback.fst K.hom (pullback.snd p p)) ≫ iOver.left =
      pullback.map p (K.hom ≫ p) p (((Over.pullback p).obj G₀.X).hom ≫ p) (𝟙 S') iOver.left
        (𝟙 S) (by simp) (by rw [← Over.w_assoc iOver, Category.comp_id]) ≫
        (DescentDatum.baseChange p G₀.X).act := by
  let θ : pullback p (K.hom ≫ p) ⟶ pullback K.hom (pullback.fst p p) :=
    pullback.lift (pullback.snd p (K.hom ≫ p))
      (pullback.lift (pullback.snd p (K.hom ≫ p) ≫ K.hom) (pullback.fst p (K.hom ≫ p))
        (by rw [Category.assoc, ← pullback.condition]))
      (by simp)
  have hf₂_fst : pullback.fst K.hom (pullback.snd p p) ≫ iOver.left =
      ((Over.pullback (pullback.snd p p)).map iOver).left ≫
        pullback.fst ((Over.pullback p).obj G₀.X).hom (pullback.snd p p) := by simp
  have hθ :
      (θ ≫ u.left ≫ pullback.fst K.hom (pullback.snd p p)) ≫ iOver.left = _ := calc
    (θ ≫ u.left ≫ pullback.fst K.hom (pullback.snd p p)) ≫ iOver.left
      = θ ≫ (u.left ≫ ((Over.pullback (pullback.snd p p)).map iOver).left) ≫
          pullback.fst ((Over.pullback p).obj G₀.X).hom (pullback.snd p p) := by
        simp only [Category.assoc, hf₂_fst]
    _ = θ ≫ ((Over.pullback (pullback.fst p p)).map iOver).left ≫
          ((Grp.pullbackOverlapIso p G₀).hom.hom.hom.left ≫
            pullback.fst ((Over.pullback p).obj G₀.X).hom (pullback.snd p p)) :=
        congrArg (θ ≫ ·) ((congrArg (· ≫ _) hu).trans (Category.assoc _ _ _))
    _ = _ := congrArg (θ ≫ ((Over.pullback (pullback.fst p p)).map iOver).left ≫ ·)
        (Grp.pullbackOverlapIso_hom_left_fst p G₀)
  rw [hθ]
  refine pullback.hom_ext ?_ ?_ <;> simp [θ]

/-- Given a closed subgroup scheme `H'` of `(Over.pullback p).mapGrp.obj G₀` satisfying the overlap
condition on `S' ×_S S'`, the canonical descent datum on `(Over.pullback p).obj G₀.X` restricts
along the monomorphism `H'.val.arrow` to `(H'.val : Grp (Over S')).X`. -/
private theorem exists_restricted_descentDatum {p : S' ⟶ S} {G₀ : Grp (Over S)}
    (H' : ClosedSubgroupScheme ((Over.pullback p).mapGrp.obj G₀))
    (hH' : mapIso (Grp.pullbackOverlapIso p G₀) (baseChange (pullback.fst p p) H') =
      baseChange (pullback.snd p p) H') :
    ∃ (D : DescentDatum p (H'.val : Grp (Over S')).X)
      (φ : DescentDatum.Hom D (DescentDatum.baseChange p G₀.X)),
      φ.hom = H'.val.arrow.hom.hom := by
  let i := H'.val.arrow
  let iOver : (H'.val : Grp (Over S')).X ⟶ (Over.pullback p).obj G₀.X := i.hom.hom
  have : IsClosedImmersion iOver.left := isClosedImmersion_arrow H'
  -- The overlap equality `hH'` gives a comparison morphism `u` between the two pullbacks of `H'`
  -- to `S' ×_S S'` intertwining `i` with `Grp.pullbackOverlapIso p G₀`.
  let f₁ := (Over.pullback (pullback.fst p p)).mapGrp.map i ≫ (Grp.pullbackOverlapIso p G₀).hom
  let f₂ := (Over.pullback (pullback.snd p p)).mapGrp.map i
  have hmk : Subobject.mk f₁ ≤ Subobject.mk f₂ := by
    have heq := Subtype.ext_iff.1 hH'
    rw [baseChange_def, baseChange_def, coe_mapIso, coe_mk, coe_mk, Subobject.map_mk] at heq
    exact heq.le
  let u := Subobject.ofMkLEMk f₁ f₂ hmk
  have hact := overlap_act_comp_left iOver u.hom.hom
    (congrArg (fun ψ ↦ ψ.hom.hom.left) (Subobject.ofMkLEMk_comp hmk))
  exact ⟨DescentDatum.ofMono (DescentDatum.baseChange p G₀.X) iOver _ hact,
    DescentDatum.ofMonoHom (DescentDatum.baseChange p G₀.X) iOver _ hact,
    DescentDatum.ofMonoHom_hom (DescentDatum.baseChange p G₀.X) iOver _ hact⟩

/-- **Existence of fpqc descent for closed subgroup schemes.** Let `p : S' ⟶ S` be surjective, flat
and quasi-compact, and let `G₀` be an arbitrary group scheme over `S`. Every closed subgroup scheme
`H'` of `(Over.pullback p).mapGrp.obj G₀` whose two pullbacks to `S' ×_S S'` agree under
`Grp.pullbackOverlapIso p G₀` is the base change along `p` of a closed subgroup scheme of `G₀`. -/
theorem exists_baseChange_eq
    (H' : ClosedSubgroupScheme ((Over.pullback p).mapGrp.obj G₀))
    (hH' : mapIso (Grp.pullbackOverlapIso p G₀) (baseChange (pullback.fst p p) H') =
      baseChange (pullback.snd p p) H') :
    ∃ P : ClosedSubgroupScheme G₀, baseChange p P = H' := by
  obtain ⟨D, φ, hφ⟩ := exists_restricted_descentDatum H' hH'
  have : IsMonHom φ.hom := hφ.symm ▸ (inferInstance : IsMonHom H'.val.arrow.hom.hom)
  have : IsClosedImmersion φ.hom.left := by
    rw [hφ]
    exact isClosedImmersion_arrow H'
  obtain ⟨K₀, i₀, g, _, _, _, hcomp⟩ :=
    φ.exists_grp_baseChange_hom_isIso_of_isClosedImmersion
  refine ⟨mk i₀, ?_⟩
  rw [baseChange_mk]
  refine Subtype.ext ?_
  rw [coe_mk]
  let eg : (Over.pullback p).obj K₀.X ≅ (H'.val : Grp (Over S')).X := asIso g.hom
  let e : (Over.pullback p).mapGrp.obj K₀ ≅ (H'.val : Grp (Over S')) :=
    Grp.mkIso (G := (Over.pullback p).mapGrp.obj K₀) (H := (H'.val : Grp (Over S')))
      eg (IsMonHom.one_hom g.hom) (IsMonHom.mul_hom g.hom)
  have he : e.hom ≫ H'.val.arrow = (Over.pullback p).mapGrp.map i₀ := by
    apply Grp.hom_ext
    have hmap := congrArg DescentDatum.Hom.hom hcomp
    simp only [DescentDatum.Hom.comp_hom, hφ, DescentDatum.baseChangeHom_hom] at hmap
    exact hmap
  exact (Subobject.mk_eq_mk_of_comm ((Over.pullback p).mapGrp.map i₀) H'.val.arrow e he).trans
    (Subobject.mk_arrow H'.val)

/-- **Effective fpqc descent of a closed subgroup scheme.** Given `p : S' ⟶ S` surjective, flat and
quasi-compact and a closed subgroup scheme `H'` of `(Over.pullback p).mapGrp.obj G₀` satisfying the
overlap condition on `S' ×_S S'`, `descend p H' hH'` is the unique closed subgroup scheme of `G₀`
whose base change along `p` is `H'`. -/
noncomputable def descend
    (H' : ClosedSubgroupScheme ((Over.pullback p).mapGrp.obj G₀))
    (hH' : mapIso (Grp.pullbackOverlapIso p G₀) (baseChange (pullback.fst p p) H') =
      baseChange (pullback.snd p p) H') :
    ClosedSubgroupScheme G₀ :=
  (exists_baseChange_eq p H' hH').choose

/-- Base-changing `descend p H' hH'` along `p` recovers `H'`. -/
@[simp]
theorem baseChange_descend
    (H' : ClosedSubgroupScheme ((Over.pullback p).mapGrp.obj G₀))
    (hH' : mapIso (Grp.pullbackOverlapIso p G₀) (baseChange (pullback.fst p p) H') =
      baseChange (pullback.snd p p) H') :
    baseChange p (descend p H' hH') = H' :=
  (exists_baseChange_eq p H' hH').choose_spec

/-- Descending the base change of a closed subgroup scheme `P` of `G₀` recovers `P`. -/
@[simp]
theorem descend_baseChange (P : ClosedSubgroupScheme G₀) :
    descend p (baseChange p P) (mapIso_pullbackOverlapIso_baseChange p P) = P :=
  baseChange_injective p (baseChange_descend p _ _)

/-- Uniqueness characterization of `descend p H' hH'`. -/
theorem eq_descend_iff {P : ClosedSubgroupScheme G₀}
    {H' : ClosedSubgroupScheme ((Over.pullback p).mapGrp.obj G₀)}
    {hH' : mapIso (Grp.pullbackOverlapIso p G₀) (baseChange (pullback.fst p p) H') =
      baseChange (pullback.snd p p) H'} :
    P = descend p H' hH' ↔ baseChange p P = H' :=
  ⟨fun h ↦ h ▸ baseChange_descend p H' hH',
    fun h ↦ baseChange_injective p (h.trans (baseChange_descend p H' hH').symm)⟩

variable (G₀) in
/-- **Effective fpqc descent equivalence for closed subgroup schemes.** Base change along a
surjective, flat and quasi-compact morphism `p : S' ⟶ S` is an order isomorphism from closed
subgroup schemes of `G₀` to closed subgroup schemes of `(Over.pullback p).mapGrp.obj G₀` whose two
pullbacks to `S' ×_S S'` correspond under `Grp.pullbackOverlapIso p G₀`. -/
noncomputable def descentOrderIso :
    ClosedSubgroupScheme G₀ ≃o
      {H' : ClosedSubgroupScheme ((Over.pullback p).mapGrp.obj G₀) //
        mapIso (Grp.pullbackOverlapIso p G₀) (baseChange (pullback.fst p p) H') =
          baseChange (pullback.snd p p) H'} where
  toFun P := ⟨baseChange p P, mapIso_pullbackOverlapIso_baseChange p P⟩
  invFun H' := descend p H'.val H'.property
  left_inv P := descend_baseChange p P
  right_inv H' := Subtype.ext (baseChange_descend p H'.val H'.property)
  map_rel_iff' := baseChange_le_baseChange_iff p

/-- `descentOrderIso` acts on closed subgroup schemes by `baseChange p`. -/
@[simp]
theorem descentOrderIso_apply_coe (P : ClosedSubgroupScheme G₀) :
    (descentOrderIso p G₀ P : ClosedSubgroupScheme ((Over.pullback p).mapGrp.obj G₀)) =
      baseChange p P :=
  (rfl)

/-- The inverse of `descentOrderIso` descends a compatible closed subgroup scheme over `S'`. -/
@[simp]
theorem descentOrderIso_symm_apply
    (H' : {H' : ClosedSubgroupScheme ((Over.pullback p).mapGrp.obj G₀) //
      mapIso (Grp.pullbackOverlapIso p G₀) (baseChange (pullback.fst p p) H') =
        baseChange (pullback.snd p p) H'}) :
    (descentOrderIso p G₀).symm H' = descend p H'.val H'.property :=
  (rfl)

/-- **Fpqc descent of morphism properties on closed subgroup schemes.** For any morphism property
`M` stable under base change and satisfying fpqc descent, the structure morphism to the base of
`baseChange p P` satisfies `M` if and only if that of `P` does. -/
theorem hom_mem_baseChange_iff {M : MorphismProperty Scheme.{u}}
    [M.IsStableUnderBaseChange] [M.DescendsAlong (@Surjective ⊓ @Flat ⊓ @QuasiCompact)]
    (P : ClosedSubgroupScheme G₀) :
    M ((baseChange p P).val : Grp (Over S')).X.hom ↔ M (P.val : Grp (Over S)).X.hom :=
  ⟨fun h ↦ MorphismProperty.of_isPullback_of_descendsAlong
      (Q := @Surjective ⊓ @Flat ⊓ @QuasiCompact)
      (isPullback_baseChange_hom p P) ⟨⟨inferInstance, inferInstance⟩, inferInstance⟩ h,
    fun h ↦ MorphismProperty.of_isPullback (isPullback_baseChange_hom p P).flip h⟩

/-- Finiteness over the base descends along fpqc covers for closed subgroup schemes. -/
@[simp]
theorem isFinite_baseChange_iff (P : ClosedSubgroupScheme G₀) :
    IsFinite ((baseChange p P).val : Grp (Over S')).X.hom ↔
      IsFinite (P.val : Grp (Over S)).X.hom :=
  hom_mem_baseChange_iff p P

/-- Flatness over the base descends along fpqc covers for closed subgroup schemes. -/
@[simp]
theorem flat_baseChange_iff (P : ClosedSubgroupScheme G₀) :
    Flat ((baseChange p P).val : Grp (Over S')).X.hom ↔
      Flat (P.val : Grp (Over S)).X.hom :=
  hom_mem_baseChange_iff p P

/-- Local finite presentation over the base descends along fpqc covers for closed subgroup
schemes. -/
@[simp]
theorem locallyOfFinitePresentation_baseChange_iff (P : ClosedSubgroupScheme G₀) :
    LocallyOfFinitePresentation ((baseChange p P).val : Grp (Over S')).X.hom ↔
      LocallyOfFinitePresentation (P.val : Grp (Over S)).X.hom :=
  hom_mem_baseChange_iff p P

/-- If `H'` is finite over `S'`, its descended closed subgroup scheme `descend p H' hH'` is finite
over `S`. -/
theorem isFinite_descend
    (H' : ClosedSubgroupScheme ((Over.pullback p).mapGrp.obj G₀))
    (hH' : mapIso (Grp.pullbackOverlapIso p G₀) (baseChange (pullback.fst p p) H') =
      baseChange (pullback.snd p p) H')
    [IsFinite (H'.val : Grp (Over S')).X.hom] :
    IsFinite ((descend p H' hH').val : Grp (Over S)).X.hom := by
  rw [← isFinite_baseChange_iff p, baseChange_descend]
  infer_instance

/-- If `H'` is flat over `S'`, its descended closed subgroup scheme `descend p H' hH'` is flat over
`S`. -/
theorem flat_descend
    (H' : ClosedSubgroupScheme ((Over.pullback p).mapGrp.obj G₀))
    (hH' : mapIso (Grp.pullbackOverlapIso p G₀) (baseChange (pullback.fst p p) H') =
      baseChange (pullback.snd p p) H')
    [Flat (H'.val : Grp (Over S')).X.hom] :
    Flat ((descend p H' hH').val : Grp (Over S)).X.hom := by
  rw [← flat_baseChange_iff p, baseChange_descend]
  infer_instance

/-- If `H'` is locally of finite presentation over `S'`, its descended closed subgroup scheme
`descend p H' hH'` is locally of finite presentation over `S`. -/
theorem locallyOfFinitePresentation_descend
    (H' : ClosedSubgroupScheme ((Over.pullback p).mapGrp.obj G₀))
    (hH' : mapIso (Grp.pullbackOverlapIso p G₀) (baseChange (pullback.fst p p) H') =
      baseChange (pullback.snd p p) H')
    [LocallyOfFinitePresentation (H'.val : Grp (Over S')).X.hom] :
    LocallyOfFinitePresentation ((descend p H' hH').val : Grp (Over S)).X.hom := by
  rw [← locallyOfFinitePresentation_baseChange_iff p, baseChange_descend]
  infer_instance

/-- **Rank of a descended finite flat closed subgroup scheme.** If `H'` is finite and flat over
`S'`, then the rank of `H'` over `S'` is the rank of `descend p H' hH'` pulled back along `p`. -/
theorem finrank_descend
    (H' : ClosedSubgroupScheme ((Over.pullback p).mapGrp.obj G₀))
    (hH' : mapIso (Grp.pullbackOverlapIso p G₀) (baseChange (pullback.fst p p) H') =
      baseChange (pullback.snd p p) H')
    [IsFinite (H'.val : Grp (Over S')).X.hom] [Flat (H'.val : Grp (Over S')).X.hom] :
    (H'.val : Grp (Over S')).X.hom.finrank =
      ((descend p H' hH').val : Grp (Over S)).X.hom.finrank ∘ p := by
  have : IsFinite ((descend p H' hH').val : Grp (Over S)).X.hom := isFinite_descend p H' hH'
  have : Flat ((descend p H' hH').val : Grp (Over S)).X.hom := flat_descend p H' hH'
  have h := finrank_baseChange p (descend p H' hH')
  have hbc : ((baseChange p (descend p H' hH')).val : Grp (Over S')).X.hom.finrank =
      (H'.val : Grp (Over S')).X.hom.finrank := by
    rw [baseChange_descend]
  exact hbc.symm.trans h

end FpqcDescent

end TauCeti.ClosedSubgroupScheme
