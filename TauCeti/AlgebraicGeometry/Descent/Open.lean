/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.Descent.AffineMorphism

/-!
# Descent of stable open subschemes

Let `p : S' ⟶ S` be a morphism of schemes and `D` a descent datum relative to `p` on a scheme
`X ⟶ S'`, with action `D.act : S' ×_S X ⟶ X`, `(s, x) ↦ s · x`. An open subscheme `U` of `X` is
*stable* under `D` (`DescentDatum.IsStable`) when `s · x ∈ U ↔ x ∈ U`, that is, when the preimages
of `U` under the action and under the second projection `S' ×_S X ⟶ X` agree. The action then
restricts to a descent datum `D.restrict U hU` on `U`, and the inclusion of `U` is a morphism of
descent data `D.restrictHom U hU`; morphisms of descent data with image in `U` factor through it
(`DescentDatum.Hom.codRestrict`). Since `x = π x · (s · x)`, an open is stable as soon as the
action maps the points over `U` into `U` (`DescentDatum.isStable_of_forall_mem`); in particular the
image of a morphism of descent data which is an open immersion is stable
(`DescentDatum.Hom.isStable_opensRange`).

For the canonical descent datum on a base change `X₀ ×_S S'`, the preimage of every open of `X₀` is
stable. Conversely, if `p` is surjective, flat and quasi-compact, every stable open of
`X₀ ×_S S'` is the preimage of a unique open of `X₀` (`DescentDatum.isStable_baseChange_iff`,
`DescentDatum.existsUnique_preimage_eq_of_isStable`): the projection `X₀ ×_S S' ⟶ X₀` is then a
topological quotient map, and stability says that the open is a union of its fibres.

Consequently, effectivity passes to stable opens: if `D` is isomorphic to the canonical descent
datum on `X₀ ×_S S'`, then for every stable open `U` of `X` there is an open `U₀` of `X₀` such
that `D.restrict U hU` is isomorphic to the canonical descent datum on `U₀ ×_S S'`, compatibly with
the inclusions (`DescentDatum.exists_baseChange_hom_isIso_restrict`). In particular a descent
datum on a stable open subscheme of a scheme affine over `S'`, relative to an affine, flat and
surjective `p`, is effective (`DescentDatum.exists_baseChange_hom_isIso_restrict_of_isAffineHom`).
More generally, a descent datum admitting an open immersion, as a morphism of descent data, into
the canonical descent datum on a base change `X₀ ×_S S'` is effective, with model an open of `X₀`
(`DescentDatum.Hom.exists_baseChange_hom_isIso_of_isOpenImmersion`). This is how descent data are
descended on schemes which are only open in a scheme whose descent is known, such as a
quasi-projective scheme embedded as an open of the projective spectrum of its section ring.

## Main declarations

* `TauCeti.DescentDatum.IsStable D U`: the open `U` is stable under `D`; for instance the preimage
  in `X` of an open of `S` is stable (`TauCeti.DescentDatum.isStable_comp_preimage`).
* `TauCeti.DescentDatum.restrict D U hU`: the descent datum induced on a stable open `U`, with the
  inclusion `TauCeti.DescentDatum.restrictHom D U hU` and the factorization
  `TauCeti.DescentDatum.Hom.codRestrict`.
* `TauCeti.DescentDatum.isStable_baseChange_iff`: for `p` surjective, flat and quasi-compact, the
  stable opens of `X₀ ×_S S'` are exactly the preimages of opens of `X₀`.
* `TauCeti.DescentDatum.exists_baseChange_hom_isIso_restrict`: for such `p`, the restriction of an
  effective descent datum to a stable open is effective.
* `TauCeti.DescentDatum.Hom.exists_baseChange_hom_isIso_of_isOpenImmersion`: for such `p`, a
  descent datum which is open in the canonical descent datum on a base change `X₀ ×_S S'` is the
  base change of an open of `X₀`.
* `TauCeti.DescentDatum.Hom.exists_baseChange_hom_isIso_restrict_of_pullbackAlong`: effectivity
  of the base change of a descent datum to an open of the base gives effectivity of its restriction
  to the preimage of that open.

## References

* A. Grothendieck, *Revêtements étales et groupe fondamental* (SGA 1), Exposé VIII, §1 and §7.
* The Stacks Project, Chapter *Descent*, Section *Descent data for schemes over schemes*.
-/

public section

open CategoryTheory Limits AlgebraicGeometry TopologicalSpace

namespace TauCeti.DescentDatum

universe u

variable {S S' : Scheme.{u}} {p : S' ⟶ S} {X : Over S'} (D : DescentDatum p X)

/-- An open `U` of the carrier of a descent datum `D` is *stable* under `D` when `s · x ∈ U` exactly
when `x ∈ U`: its preimages under the action and under the second projection `S' ×_S X ⟶ X`
agree. -/
def IsStable (U : X.left.Opens) : Prop :=
  D.act ⁻¹ᵁ U = pullback.snd p (X.hom ≫ p) ⁻¹ᵁ U

variable {D} in
/-- An open `U` is stable exactly when, for every point `(s, x)` of `S' ×_S X`, `s · x ∈ U`
exactly when `x ∈ U`. -/
theorem isStable_iff {U : X.left.Opens} :
    D.IsStable U ↔ ∀ z, D.act z ∈ U ↔ pullback.snd p (X.hom ≫ p) z ∈ U :=
  SetLike.ext_iff

variable {D} in
/-- An open `U` is stable as soon as the action maps points over `U` into `U`: if `x ∈ U` always
gives `s · x ∈ U`, then conversely `s · x ∈ U` gives `x = π x · (s · x) ∈ U`. -/
theorem isStable_of_forall_mem {U : X.left.Opens}
    (h : ∀ z, pullback.snd p (X.hom ≫ p) z ∈ U → D.act z ∈ U) : D.IsStable U := by
  refine isStable_iff.mpr fun z ↦ ⟨fun hz ↦ ?_, h z⟩
  have := h (pullback.lift (pullback.snd p (X.hom ≫ p) ≫ X.hom) D.act
    (by rw [Category.assoc, D.act_comp_hom_comp]) z) (by rwa [← Scheme.Hom.comp_apply,
      pullback.lift_snd])
  rwa [← Scheme.Hom.comp_apply, lift_act_comp_act] at this

@[simp]
theorem isStable_top : D.IsStable ⊤ := by
  simp [IsStable]

variable {D} in
theorem IsStable.inf {U V : X.left.Opens} (hU : D.IsStable U) (hV : D.IsStable V) :
    D.IsStable (U ⊓ V) := by
  unfold IsStable at *
  rw [Scheme.Hom.preimage_inf, Scheme.Hom.preimage_inf, hU, hV]

variable {D} in
theorem IsStable.iSup {ι : Sort*} {U : ι → X.left.Opens} (hU : ∀ i, D.IsStable (U i)) :
    D.IsStable (⨆ i, U i) := by
  unfold IsStable at *
  simp only [Scheme.Hom.preimage_iSup, hU]

variable {D} in
/-- Stability is preserved by preimages under morphisms of descent data. -/
theorem IsStable.preimage {Y : Over S'} {E : DescentDatum p Y} (f : Hom D E) {U : Y.left.Opens}
    (hU : E.IsStable U) : D.IsStable (f.hom.left ⁻¹ᵁ U) := by
  unfold IsStable at hU ⊢
  rw [← Scheme.Hom.comp_preimage, ← f.map_act, Scheme.Hom.comp_preimage, hU]
  simp only [← Scheme.Hom.comp_preimage, pullback.lift_snd]

variable {D} in
/-- The image of a morphism of descent data which is an open immersion is stable. -/
theorem Hom.isStable_opensRange {Y : Over S'} {E : DescentDatum p Y} (f : Hom D E)
    [IsOpenImmersion f.hom.left] : E.IsStable f.hom.left.opensRange := by
  -- The action space `S' ×_S X` is the part of `S' ×_S Y` lying over the image of `f`.
  have hpb : IsPullback (pullback.map p (X.hom ≫ p) p (Y.hom ≫ p) (𝟙 S') f.hom.left (𝟙 S)
      (by simp) (by simp)) (pullback.snd p (X.hom ≫ p)) (pullback.snd p (Y.hom ≫ p))
      f.hom.left := by
    refine IsPullback.of_right ?_ (by simp) (IsPullback.of_hasPullback p (Y.hom ≫ p))
    simpa using IsPullback.of_hasPullback p (X.hom ≫ p)
  refine isStable_of_forall_mem fun z hz ↦ ?_
  obtain ⟨x, hx⟩ := Scheme.Hom.mem_opensRange.mp hz
  have hz' : z ∈ (pullback.snd p (Y.hom ≫ p)).base ⁻¹' (f.hom.left.base '' Set.univ) :=
    ⟨x, trivial, hx⟩
  rw [← Scheme.image_preimage_eq_of_isPullback hpb.flip] at hz'
  obtain ⟨w, -, rfl⟩ := hz'
  rw [← Scheme.Hom.comp_apply, f.map_act, Scheme.Hom.comp_apply]
  exact Scheme.Hom.mem_opensRange.mpr ⟨_, rfl⟩

/-- The preimage in `X` of an open of `S` is stable: the action `(s, x) ↦ s · x` does not change
the image of a point in `S`. -/
theorem isStable_comp_preimage (U : S.Opens) : D.IsStable ((X.hom ≫ p) ⁻¹ᵁ U) := by
  refine isStable_iff.mpr fun z ↦ ?_
  rw [Scheme.Hom.mem_preimage, Scheme.Hom.mem_preimage, ← Scheme.Hom.comp_apply,
    ← Scheme.Hom.comp_apply, act_comp_hom_comp]

section Restrict

variable (U : X.left.Opens)

/-- The inclusion `S' ×_S U ⟶ S' ×_S X` of action spaces induced by an open `U` of `X`. -/
noncomputable abbrev restrictActionMap :
    pullback p ((Over.mk (U.ι ≫ X.hom)).hom ≫ p) ⟶ pullback p (X.hom ≫ p) :=
  pullback.map _ _ _ _ (𝟙 S') U.ι (𝟙 S) (by simp) (by simp)

variable {U}

private theorem range_restrictActionMap_comp_act_subset (hU : D.IsStable U) :
    Set.range (restrictActionMap U ≫ D.act) ⊆ Set.range U.ι := by
  rintro _ ⟨z, rfl⟩
  rw [Scheme.Opens.range_ι, SetLike.mem_coe, Scheme.Hom.comp_apply, isStable_iff.mp hU,
    ← Scheme.Hom.comp_apply, pullback.lift_snd, Scheme.Hom.comp_apply]
  exact Subtype.prop _

/-- The descent datum induced by `D` on a stable open `U`: the action of `D` restricted to
`S' ×_S U`, which lands in `U` by stability. -/
noncomputable def restrict (U : X.left.Opens) (hU : D.IsStable U) :
    DescentDatum p (Over.mk (U.ι ≫ X.hom)) where
  act := IsOpenImmersion.lift U.ι _ (D.range_restrictActionMap_comp_act_subset hU)
  act_hom := by
    simp [IsOpenImmersion.lift_fac_assoc]
  lift_act := by
    have h : pullback.lift (f := p) (Over.mk (U.ι ≫ X.hom)).hom (𝟙 _) (by simp) ≫
        restrictActionMap U = U.ι ≫ pullback.lift (f := p) X.hom (𝟙 X.left) (by simp) :=
      pullback.hom_ext (by simp) (by simp)
    rw [← cancel_mono U.ι, Category.assoc, IsOpenImmersion.lift_fac, reassoc_of% h]
    simp
  act_assoc := by
    rw [← cancel_mono U.ι]
    simp only [Category.assoc, IsOpenImmersion.lift_fac]
    have := pullback.map p (pullback.fst p ((Over.mk (U.ι ≫ X.hom)).hom ≫ p) ≫ p) p
      (pullback.fst p (X.hom ≫ p) ≫ p) (𝟙 S') (restrictActionMap U) (𝟙 S) (by simp)
      (by simp) ≫= D.act_assoc
    convert this using 1 <;>
    · simp only [← Category.assoc]
      congr 1
      apply pullback.hom_ext <;> simp [IsOpenImmersion.lift_fac]

/-- The restricted action is the action of `D` on points of `U`. -/
@[reassoc (attr := simp)]
theorem restrict_act_ι (hU : D.IsStable U) :
    (D.restrict U hU).act ≫ U.ι = restrictActionMap U ≫ D.act :=
  IsOpenImmersion.lift_fac _ _ _

/-- The inclusion of a stable open `U` as a morphism of descent data `D.restrict U hU ⟶ D`. -/
noncomputable def restrictHom (U : X.left.Opens) (hU : D.IsStable U) : Hom (D.restrict U hU) D where
  hom := Over.homMk U.ι
  map_act := (D.restrict_act_ι hU).symm

@[simp]
theorem restrictHom_hom_left (hU : D.IsStable U) : (D.restrictHom U hU).hom.left = U.ι :=
  (rfl)

variable {D} in
/-- A morphism of descent data into `D` whose image lies in a stable open `U` factors through the
restriction of `D` to `U`. -/
noncomputable def Hom.codRestrict {Y : Over S'} {E : DescentDatum p Y} (f : Hom E D)
    (hU : D.IsStable U) (hf : Set.range f.hom.left ⊆ U) : Hom E (D.restrict U hU) where
  hom := Over.homMk (IsOpenImmersion.lift U.ι f.hom.left (by rwa [Scheme.Opens.range_ι]))
    (by simp [IsOpenImmersion.lift_fac_assoc])
  map_act := by
    rw [← cancel_mono U.ι]
    simp only [Category.assoc, restrict_act_ι, Over.homMk_left, IsOpenImmersion.lift_fac]
    rw [← f.map_act, ← Category.assoc]
    congr 1
    apply pullback.hom_ext <;> simp [IsOpenImmersion.lift_fac]

variable {D} in
@[reassoc (attr := simp)]
theorem Hom.codRestrict_hom_left_ι {Y : Over S'} {E : DescentDatum p Y} (f : Hom E D)
    (hU : D.IsStable U) (hf : Set.range f.hom.left ⊆ U) :
    (f.codRestrict hU hf).hom.left ≫ U.ι = f.hom.left :=
  IsOpenImmersion.lift_fac _ _ _

variable {D} in
@[simp]
theorem Hom.restrictHom_comp_codRestrict {Y : Over S'} {E : DescentDatum p Y} (f : Hom E D)
    (hU : D.IsStable U) (hf : Set.range f.hom.left ⊆ U) :
    (D.restrictHom U hU).comp (f.codRestrict hU hf) = f :=
  Hom.ext (Over.OverMorphism.ext (by simp))

variable {D} in
/-- `Hom.codRestrict` is the unique factorization through the restriction of `D` to `U`. -/
theorem Hom.eq_codRestrict_iff {Y : Over S'} {E : DescentDatum p Y} (f : Hom E D)
    (hU : D.IsStable U) (hf : Set.range f.hom.left ⊆ U) (g : Hom E (D.restrict U hU)) :
    g = f.codRestrict hU hf ↔ (D.restrictHom U hU).comp g = f := by
  refine ⟨fun h ↦ h ▸ f.restrictHom_comp_codRestrict hU hf, fun h ↦ ?_⟩
  refine Hom.ext (Over.OverMorphism.ext ?_)
  rw [← cancel_mono U.ι, Hom.codRestrict_hom_left_ι, ← h]
  simp

variable {D} in
/-- A morphism of descent data into `D` which is an open immersion with image a stable open `U` is
an isomorphism onto the restriction of `D` to `U`. -/
theorem Hom.isIso_codRestrict_hom {Y : Over S'} {E : DescentDatum p Y} (f : Hom E D)
    [IsOpenImmersion f.hom.left] (hU : D.IsStable U) (hf : Set.range f.hom.left = U) :
    IsIso (f.codRestrict hU hf.subset).hom := by
  suffices IsIso ((Over.forget S').map (f.codRestrict hU hf.subset).hom) from
    isIso_of_reflects_iso _ (Over.forget S')
  have hrange : Set.range f.hom.left = Set.range U.ι := hf.trans (Scheme.Opens.range_ι U).symm
  -- The corestriction is the isomorphism between two open immersions with the same range.
  have : (f.codRestrict hU hf.subset).hom.left =
      (IsOpenImmersion.isoOfRangeEq _ _ hrange).hom := by
    rw [← cancel_mono U.ι, Hom.codRestrict_hom_left_ι, IsOpenImmersion.isoOfRangeEq_hom_fac]
  rw [Over.forget_map, this]
  infer_instance

end Restrict

section BaseChange

variable (p) in
/-- For the canonical descent datum on a base change `X₀ ×_S S'`, the preimage of every open of `X₀`
is stable. -/
theorem isStable_baseChange_preimage (X₀ : Over S) (U₀ : X₀.left.Opens) :
    (baseChange p X₀).IsStable (pullback.fst X₀.hom p ⁻¹ᵁ U₀) := by
  rw [IsStable, ← Scheme.Hom.comp_preimage, baseChange_act_fst, Scheme.Hom.comp_preimage]

/-- Stability under the canonical descent datum on `X₀ ×_S S'` says that the open is a union of
fibres of the projection `X₀ ×_S S' ⟶ X₀`. -/
theorem IsStable.mem_of_fst_eq {X₀ : Over S} {V : (pullback X₀.hom p).Opens}
    (hV : (baseChange p X₀).IsStable V) {v w : ((pullback X₀.hom p : Scheme.{u}) : Type u)}
    (h : pullback.fst X₀.hom p v = pullback.fst X₀.hom p w) (hv : v ∈ V) : w ∈ V := by
  obtain ⟨z, hz₁, hz₂⟩ := Scheme.Pullback.exists_preimage_pullback v w h
  -- The point `z` of `(X₀ ×_S S') ×_{X₀} (X₀ ×_S S')` over `(v, w)` gives the point
  -- `(π w, v)` of the action space, which the canonical action sends to `w`.
  let φ : pullback (pullback.fst X₀.hom p) (pullback.fst X₀.hom p) ⟶
      pullback p (((Over.pullback p).obj X₀).hom ≫ p) :=
    pullback.lift (pullback.snd _ _ ≫ pullback.snd X₀.hom p) (pullback.fst _ _) <| by
      simp only [Over.pullback_obj_hom, Category.assoc, ← pullback.condition,
        pullback.condition_assoc]
  have hφ₁ : φ ≫ (baseChange p X₀).act = pullback.snd _ _ := by
    refine pullback.hom_ext ?_ ?_
    · simp [φ, pullback.condition]
    · simp [φ]
  have hφ₂ : φ ≫ pullback.snd _ _ = pullback.fst _ _ := pullback.lift_snd _ _ _
  have hz : φ z ∈ pullback.snd p (((Over.pullback p).obj X₀).hom ≫ p) ⁻¹ᵁ V := by
    rw [Scheme.Hom.mem_preimage, ← Scheme.Hom.comp_apply, hφ₂, hz₁]
    exact hv
  rw [← hV, Scheme.Hom.mem_preimage, ← Scheme.Hom.comp_apply, hφ₁, hz₂] at hz
  exact hz

variable [Surjective p] [Flat p] [QuasiCompact p]

/-- **Descent of opens.** For `p` surjective, flat and quasi-compact, every open of `X₀ ×_S S'`
which is stable under the canonical descent datum is the preimage of a unique open of `X₀`. -/
theorem existsUnique_preimage_eq_of_isStable {X₀ : Over S} {V : (pullback X₀.hom p).Opens}
    (hV : (baseChange p X₀).IsStable V) :
    ∃! U₀ : X₀.left.Opens, pullback.fst X₀.hom p ⁻¹ᵁ U₀ = V := by
  let g := pullback.fst X₀.hom p
  have hsat : g ⁻¹' (g '' V) = V := by
    refine subset_antisymm ?_ (Set.subset_preimage_image _ _)
    rintro w ⟨v, hv, h⟩
    exact IsStable.mem_of_fst_eq hV h hv
  refine ⟨⟨g '' V, ?_⟩, Opens.ext hsat, fun U₀ hU₀ ↦ ?_⟩
  · rw [← (Flat.isQuotientMap_of_surjective g).isOpen_preimage, hsat]
    exact V.isOpen
  · exact Opens.ext (Set.preimage_injective.mpr g.surjective
      ((congrArg SetLike.coe hU₀).trans hsat.symm))

variable (p) in
/-- For `p` surjective, flat and quasi-compact, the opens of `X₀ ×_S S'` which are stable under the
canonical descent datum are exactly the preimages of opens of `X₀`. -/
theorem isStable_baseChange_iff {X₀ : Over S} {V : (pullback X₀.hom p).Opens} :
    (baseChange p X₀).IsStable V ↔ ∃ U₀ : X₀.left.Opens, pullback.fst X₀.hom p ⁻¹ᵁ U₀ = V :=
  ⟨fun hV ↦ (existsUnique_preimage_eq_of_isStable hV).exists,
    fun ⟨U₀, hU₀⟩ ↦ hU₀ ▸ isStable_baseChange_preimage p X₀ U₀⟩

end BaseChange

section Effective

variable [Surjective p] [Flat p] [QuasiCompact p]

variable {D} in
/-- **Effectivity passes to stable opens.** Let `p` be surjective, flat and quasi-compact, and let
`f` be an isomorphism from the canonical descent datum on `X₀ ×_S S'` to `D`. For every stable open
`U` of `X` there is an open `U₀` of `X₀` such that the restriction of `D` to `U` is isomorphic to
the canonical descent datum on `U₀ ×_S S'`, compatibly with `f` and the two inclusions. -/
theorem exists_baseChange_hom_isIso_restrict {X₀ : Over S} (f : Hom (baseChange p X₀) D)
    [IsIso f.hom] {U : X.left.Opens} (hU : D.IsStable U) :
    ∃ (U₀ : X₀.left.Opens) (g : Hom (baseChange p (Over.mk (U₀.ι ≫ X₀.hom))) (D.restrict U hU)),
      IsIso g.hom ∧
        (D.restrictHom U hU).comp g = f.comp (baseChangeHom p (Over.homMk U₀.ι)) := by
  obtain ⟨U₀, hU₀⟩ := (isStable_baseChange_iff p).mp (hU.preimage f)
  let m := baseChangeHom p (Over.homMk U₀.ι : Over.mk (U₀.ι ≫ X₀.hom) ⟶ X₀)
  -- `U₀ ×_S S'` is the preimage of `U₀` in `X₀ ×_S S'`.
  have hm : IsPullback (pullback.fst (U₀.ι ≫ X₀.hom) p) m.hom.left U₀.ι (pullback.fst X₀.hom p) :=
    (isPullback_baseChangeHom p (Over.homMk U₀.ι : Over.mk (U₀.ι ≫ X₀.hom) ⟶ X₀)).flip
  -- The image of `U₀ ×_S S'` in `X₀ ×_S S'` is the preimage of `U₀`, which `f` maps onto `U`.
  have hrange : Set.range m.hom.left = SetLike.coe (pullback.fst X₀.hom p ⁻¹ᵁ U₀) := by
    have := Scheme.image_preimage_eq_of_isPullback hm Set.univ
    rwa [Set.preimage_univ, Set.image_univ, Set.image_univ, Scheme.Opens.range_ι] at this
  -- `f` maps the image `pullback.fst X₀.hom p ⁻¹ᵁ U₀` of `U₀ ×_S S'` onto `U`.
  have hrange' : Set.range (f.comp m).hom.left = Set.range U.ι := by
    simp [Set.range_comp, hrange, hU₀, Set.image_preimage_eq _ f.hom.left.surjective]
  have : IsOpenImmersion m.hom.left := MorphismProperty.of_isPullback hm inferInstance
  have : IsOpenImmersion (f.comp m).hom.left := by
    rw [Hom.comp_hom, Over.comp_left]
    infer_instance
  exact ⟨U₀, _, (f.comp m).isIso_codRestrict_hom hU (hrange'.trans (Scheme.Opens.range_ι U)),
    Hom.restrictHom_comp_codRestrict _ _ _⟩

variable {D} in
/-- **Descent of schemes open in a descended scheme.** Let `p` be surjective, flat and
quasi-compact, and let `f : X ⟶ X₀ ×_S S'` be an open immersion which is a morphism of descent data
from `D` to the canonical descent datum on a base change. Then `D` is effective: it is isomorphic
to the canonical descent datum on `U₀ ×_S S'` for an open `U₀` of `X₀`, under an isomorphism which
identifies `f` with the base change of the inclusion of `U₀`. -/
theorem Hom.exists_baseChange_hom_isIso_of_isOpenImmersion {X₀ : Over S}
    (f : Hom D (baseChange p X₀)) [IsOpenImmersion f.hom.left] :
    ∃ (U₀ : X₀.left.Opens) (g : Hom (baseChange p (Over.mk (U₀.ι ≫ X₀.hom))) D),
      IsIso g.hom ∧ f.comp g = baseChangeHom p (Over.homMk U₀.ι) := by
  have hV := f.isStable_opensRange
  have : IsIso (Hom.id (baseChange p X₀)).hom := by
    rw [Hom.id_hom]
    infer_instance
  obtain ⟨U₀, g, hg, hgf⟩ := exists_baseChange_hom_isIso_restrict (Hom.id _) hV
  -- `f` identifies `D` with the restriction of the canonical descent datum to the image of `f`.
  have hf : Set.range f.hom.left = f.hom.left.opensRange := (Scheme.Hom.coe_opensRange _).symm
  have := f.isIso_codRestrict_hom hV hf
  set e := f.codRestrict hV hf.subset
  have he : ((baseChange p X₀).restrictHom _ hV).comp e = f :=
    Hom.restrictHom_comp_codRestrict _ _ _
  refine ⟨U₀, e.inv.comp g, by rw [Hom.comp_hom]; infer_instance, ?_⟩
  calc f.comp (e.inv.comp g)
      = (((baseChange p X₀).restrictHom _ hV).comp e).comp (e.inv.comp g) := by rw [he]
    _ = _ := by
      rw [Hom.comp_assoc, ← Hom.comp_assoc e e.inv g, Hom.comp_inv_self, Hom.id_comp, hgf,
        Hom.id_comp]

end Effective

variable {D} in
/-- A descent datum relative to an affine, flat and surjective `p`, on a stable open `U` of a scheme
`X` affine over `S'`, is effective: it is isomorphic to the canonical descent datum on
`U₀ ×_S S'` for an open `U₀` of the descended scheme `D.descended`. -/
theorem exists_baseChange_hom_isIso_restrict_of_isAffineHom [IsAffineHom p] [Flat p]
    [Surjective p] [IsAffineHom X.hom] {U : X.left.Opens} (hU : D.IsStable U) :
    ∃ (U₀ : D.descended.left.Opens)
      (g : Hom (baseChange p (Over.mk (U₀.ι ≫ D.descended.hom))) (D.restrict U hU)),
      IsIso g.hom := by
  obtain ⟨U₀, g, hg, -⟩ := exists_baseChange_hom_isIso_restrict D.toBaseChangeDescended.inv hU
  exact ⟨U₀, g, hg⟩

section PullbackAlong

variable {D} {U : S.Opens} {Y₀ : Over U.toScheme}
  (f : Hom (baseChange (pullback.fst U.ι p) Y₀) (D.pullbackAlong U.ι)) [IsIso f.hom]

/-- An isomorphism from a canonical descent datum to the base change of `D` to an open `U` of `S`
gives an open immersion `Y₀ ×_S S' ⟶ X`. -/
instance Hom.isOpenImmersion_ofPullbackAlong_hom_left :
    IsOpenImmersion f.ofPullbackAlong.hom.left := by
  have : IsIso f.hom.left := (Over.forget _).map_isIso f.hom
  rw [Hom.ofPullbackAlong_hom_left]
  infer_instance

/-- The open immersion `Y₀ ×_S S' ⟶ X` given by an isomorphism onto the base change of `D` to an
open `U` of `S` has image the preimage of `U` in `X`. -/
theorem Hom.opensRange_ofPullbackAlong_hom_left :
    f.ofPullbackAlong.hom.left.opensRange = (X.hom ≫ p) ⁻¹ᵁ U := by
  have : IsIso f.hom.left := (Over.forget _).map_isIso f.hom
  simp only [Hom.ofPullbackAlong_hom_left]
  rw [Scheme.Hom.opensRange_comp_of_isIso, Scheme.Hom.opensRange_comp_of_isIso,
    Scheme.Hom.opensRange_pullbackFst, Scheme.Hom.opensRange_pullbackSnd,
    Scheme.Opens.opensRange_ι, Scheme.Hom.comp_preimage]

/-- **Effectivity after base change to an open gives effectivity of the restriction.** If the base
change `D.pullbackAlong U.ι` of `D` to an open `U` of `S` is isomorphic to the canonical descent
datum on `Y₀ ×_U (U ×_S S')`, then the restriction of `D` to the preimage of `U` in `X` is
isomorphic to the canonical descent datum on `Y₀ ×_S S'`, with `Y₀` viewed over `S`, compatibly
with `Hom.ofPullbackAlong`. -/
theorem Hom.exists_baseChange_hom_isIso_restrict_of_pullbackAlong :
    ∃ g : Hom (baseChange p ((Over.map U.ι).obj Y₀)) (D.restrict _ (D.isStable_comp_preimage U)),
      IsIso g.hom ∧ (D.restrictHom _ _).comp g = f.ofPullbackAlong := by
  have hrange : Set.range f.ofPullbackAlong.hom.left = (X.hom ≫ p) ⁻¹ᵁ U := by
    rw [← Scheme.Hom.coe_opensRange, f.opensRange_ofPullbackAlong_hom_left]
  exact ⟨_, f.ofPullbackAlong.isIso_codRestrict_hom _ hrange,
    Hom.restrictHom_comp_codRestrict _ _ _⟩

end PullbackAlong

end TauCeti.DescentDatum
