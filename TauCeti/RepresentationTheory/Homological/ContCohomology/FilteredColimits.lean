/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Category.ModuleCat.Topology.FilteredColimits
public import TauCeti.RepresentationTheory.Homological.ContCohomology.CompactDiscrete
public import TauCeti.RepresentationTheory.Homological.ContCohomology.Functoriality
public import TauCeti.RepresentationTheory.Homological.ContCohomology.SmoothDiscrete.FilteredColimits

/-!
# Continuous cohomology of a compact group commutes with filtered colimits of coefficients

Let `G` be a compact group and let `X : J ⥤ SmoothDiscreteTopRep k G` be a filtered diagram of
smooth discrete representations. If a cocone `c` on `X` is a colimit on underlying sets, then in
every degree `n` the induced cocone of continuous cohomology groups is a colimit:

```text
Hⁿ(G, colim_j X_j) = colim_j Hⁿ(G, X_j).
```

The argument is on Mathlib's homogeneous cochains, the invariant elements of the iterated function
spaces `C(G, C(G, …, X))`, and it is uniform in the degree.

* **Descent of resolution elements.** An element of `C(G, C(G, …, colim_j X_j))` comes from some
  stage `X_j`, and an element of `C(G, C(G, …, X_j))` that vanishes in the colimit already
  vanishes at some deeper stage. Both are proved by induction on the depth: a continuous map from
  the compact group `G` into a discrete space has finite image, and finitely many elements can be
  treated at once in a filtered category.
* **Descent of cochains.** A lift of an invariant element need not be invariant, but its orbit is
  finite, because the stabilizers in a smooth discrete representation are open and `G` is compact;
  at a deeper stage the finitely many differences `g • y - y` vanish, and the lift becomes
  invariant there.
* **Cohomology.** Hence every class of `Hⁿ(G, colim_j X_j)` comes from some stage
  (`TauCeti.ContinuousCohomology.exists_coeffMap_eq_of_isColimit`), and a class at some stage
  that vanishes in the colimit vanishes at a deeper stage
  (`TauCeti.ContinuousCohomology.exists_coeffMap_eq_zero_of_isColimit`).

Every continuous cohomology group of a compact group with discrete coefficients is discrete, so the
colimit statement in `TopModuleCat k` reduces to these two elementwise statements
(`TauCeti.TopModuleCat.isColimitOfJointlySurjective`).

Compactness of `G` is used for the finiteness of images and orbits, and smoothness of the
coefficients for the openness of stabilizers. The cocone is only assumed to be a colimit on
underlying sets, the form in which filtered colimits of discrete modules are computed. Every
colimit cocone of a filtered diagram in `SmoothDiscreteTopRep k G` has this form
(`TauCeti.SmoothDiscreteTopRep.forget_preservesFilteredColimits`), so `Hⁿ(G, -)` preserves
filtered colimits of smooth discrete representations.

## Main statements

* `TauCeti.ContinuousCohomology.exists_coeffMap_eq_of_isColimit`: every class of the colimit comes
  from some stage.
* `TauCeti.ContinuousCohomology.exists_coeffMap_eq_zero_of_isColimit`: a class at some stage that
  vanishes in the colimit vanishes at a deeper stage.
* `TauCeti.ContinuousCohomology.isColimitMapCoconeOfIsColimitForget`: the image of the cocone under
  `Hⁿ(G, -)` is a colimit in `TopModuleCat k`.
* `TauCeti.ContinuousCohomology.continuousCohomology_preservesFilteredColimits`: `Hⁿ(G, -)`
  preserves filtered colimits of smooth discrete representations.

## References

* J. Neukirch, A. Schmidt, K. Wingberg, *Cohomology of Number Fields*, 2nd ed., (1.5.1).
* J.-P. Serre, *Galois Cohomology*, Ch. I, §2.2, Proposition 8.
-/

public section

open CategoryTheory CategoryTheory.Limits

namespace TauCeti.ContinuousCohomology

open _root_.ContinuousCohomology

universe w' w v u

variable {k : Type v} [Ring k] [TopologicalSpace k]
  {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

/-! ### Descent through a filtered colimit of coefficients -/

section Descent

variable {J : Type w'} [Category.{w} J] {X : J ⥤ SmoothDiscreteTopRep.{v, u, u} k G}
  {c : Cocone X}

/-- The transition maps of the diagram followed by the legs of the cocone are the legs, on the
coinduced resolutions. -/
private theorem resolutionMap_ι_app_map_apply {i j : J} (f : i ⟶ j) (m : ℕ)
    (y : (TopRep.resolutionX (X.obj i).obj m).V) :
    (resolutionMap (ContinuousMonoidHom.id G) (c.ι.app j).hom m).hom
        ((resolutionMap (ContinuousMonoidHom.id G) (X.map f).hom m).hom y) =
      (resolutionMap (ContinuousMonoidHom.id G) (c.ι.app i).hom m).hom y :=
  resolutionMap_id_apply_of_comp_eq _ _ (congrArg (·.hom) (c.w f)) m y

/-- The transition maps of the diagram compose, on the coinduced resolutions. -/
private theorem resolutionMap_map_comp_apply {i j l : J} (f : i ⟶ j) (g : j ⟶ l) (m : ℕ)
    (y : (TopRep.resolutionX (X.obj i).obj m).V) :
    (resolutionMap (ContinuousMonoidHom.id G) (X.map g).hom m).hom
        ((resolutionMap (ContinuousMonoidHom.id G) (X.map f).hom m).hom y) =
      (resolutionMap (ContinuousMonoidHom.id G) (X.map (f ≫ g)).hom m).hom y :=
  resolutionMap_id_apply_of_comp_eq _ _ (congrArg (·.hom) (X.map_comp f g).symm) m y

variable [CompactSpace G] [IsFiltered J]
  (hc : IsColimit ((smoothDiscreteι k G ⋙ forget (TopRep k G)).mapCocone c))
include hc

/-- **Descent of resolution elements.** Every element of the coinduced resolution
`C(G, C(G, …, colim_j X_j))` comes from some stage of the diagram. -/
private theorem exists_resolutionMap_eq :
    ∀ (m : ℕ) (x : (TopRep.resolutionX c.pt.obj m).V),
      ∃ (j : J) (y : (TopRep.resolutionX (X.obj j).obj m).V),
        (resolutionMap (ContinuousMonoidHom.id G) (c.ι.app j).hom m).hom y = x
  | 0, x => Types.jointly_surjective_of_isColimit hc x
  | m + 1, x => by
    have := c.pt.property.discreteTopology
    let x' : C(G, (TopRep.resolutionX c.pt.obj m).V) := x
    -- the continuous map `x'` from the compact group `G` into a discrete space has finite image,
    -- each point of which comes from some stage
    have : Finite (Set.range x') := (isCompact_range x'.continuous).finite_of_discrete.to_subtype
    have := Fintype.ofFinite (Set.range x')
    choose j y hy using fun v : Set.range x' ↦ exists_resolutionMap_eq m v.1
    -- a common stage for the finitely many values
    classical
    obtain ⟨l, hl⟩ := IsFiltered.sup_objs_exists (Finset.univ.image j)
    have a (v : Set.range x') : j v ⟶ l := (hl (Finset.mem_image_of_mem j (Finset.mem_univ v))).some
    -- the lift sends `g` to the transported lift of the value `x' g`
    let lift : Set.range x' → (TopRep.resolutionX (X.obj l).obj m).V := fun v ↦
      (resolutionMap (ContinuousMonoidHom.id G) (X.map (a v)).hom m).hom (y v)
    refine ⟨l, ⟨lift ∘ Set.rangeFactorization x',
      continuous_of_discreteTopology.comp (x'.continuous.subtype_mk _)⟩,
      ContinuousMap.ext fun g ↦ ?_⟩
    exact (resolutionMap_ι_app_map_apply (a _) m _).trans (hy ⟨x' g, g, rfl⟩)

/-- **Vanishing descends through the colimit.** An element of the coinduced resolution
`C(G, C(G, …, X_j))` whose image in `C(G, C(G, …, colim_j X_j))` vanishes already vanishes at some
deeper stage of the diagram. -/
private theorem exists_resolutionMap_eq_zero :
    ∀ (m : ℕ) {j : J} (y : (TopRep.resolutionX (X.obj j).obj m).V),
      (resolutionMap (ContinuousMonoidHom.id G) (c.ι.app j).hom m).hom y = 0 →
        ∃ (l : J) (f : j ⟶ l), (resolutionMap (ContinuousMonoidHom.id G) (X.map f).hom m).hom y = 0
  | 0, j, y, hy => by
    have h : (c.ι.app j).hom.hom y = (c.ι.app j).hom.hom 0 :=
      hy.trans (map_zero (c.ι.app j).hom.hom).symm
    obtain ⟨l, f, hf⟩ := (Types.FilteredColimit.isColimit_eq_iff' hc (x := y)
      (y := (0 : (X.obj j).obj.V))).1 h
    exact ⟨l, f, hf.trans (map_zero (X.map f).hom.hom)⟩
  | m + 1, j, y, hy => by
    have := (X.obj j).property.discreteTopology
    let y' : C(G, (TopRep.resolutionX (X.obj j).obj m).V) := y
    -- the finitely many values of `y'` each vanish at some deeper stage
    have : Finite (Set.range y') := (isCompact_range y'.continuous).finite_of_discrete.to_subtype
    choose l f hf using fun v : Set.range y' ↦ exists_resolutionMap_eq_zero m v.1 (by
      obtain ⟨g, hg⟩ := v.2
      -- the value at `g` of the image of `y'` is the image of `y' g`, by `resolutionMap_succ_apply`
      have h : (resolutionMap (ContinuousMonoidHom.id G) (c.ι.app j).hom m).hom (y' g) = 0 :=
        DFunLike.congr_fun hy g
      exact hg ▸ h)
    -- and so they vanish at one common deeper stage
    obtain ⟨l', f', a, ha⟩ := IsFiltered.wideSpan f
    refine ⟨l', f', ContinuousMap.ext fun g ↦ ?_⟩
    have h := congrArg (resolutionMap (ContinuousMonoidHom.id G) (X.map (a ⟨y' g, g, rfl⟩)).hom
      m).hom (hf ⟨y' g, g, rfl⟩)
    rw [resolutionMap_map_comp_apply, ha, map_zero] at h
    -- `h` is the value at `g` of the image of `y`, by `resolutionMap_succ_apply`
    exact h

/-- **Descent of homogeneous cochains.** Every homogeneous cochain with values in the colimit is
the image of a homogeneous cochain at some stage of the diagram. -/
private theorem exists_cochainsMap_f_eq (n : ℕ)
    (x : (TopRep.homogeneousCochains c.pt.obj).X n) :
    ∃ (j : J) (y : (TopRep.homogeneousCochains (X.obj j).obj).X n),
      (cochainsMap (ContinuousMonoidHom.id G) (c.ι.app j).hom).f n y = x := by
  obtain ⟨j, y, hy⟩ := exists_resolutionMap_eq hc (n + 1) x.1
  let Y := TopRep.resolutionX (X.obj j).obj (n + 1)
  let := TopRep.distribMulAction Y
  -- the lift `y` has a finite orbit, since `G` is compact and the stabilizers are open
  have hsmooth := (X.obj j).property.resolutionX (n + 1)
  have := hsmooth.discreteTopology
  have := hsmooth.continuousSMul
  -- `g • y` is `Y.ρ g y` for the derived action, by `TopRep.distribMulAction_smul`
  have hcont : Continuous fun g : G ↦ Y.ρ g y :=
    (continuous_id.smul continuous_const : Continuous fun g : G ↦ g • (y : Y.V))
  have : Finite (Set.range fun g : G ↦ Y.ρ g y) :=
    (isCompact_range hcont).finite_of_discrete.to_subtype
  -- each difference `g • y - y` vanishes in the colimit, since `x` is invariant
  choose l f hf using fun v : Set.range fun g : G ↦ Y.ρ g y ↦
    exists_resolutionMap_eq_zero hc (n + 1) (v.1 - y) (by
      obtain ⟨g, hg⟩ := v.2
      rw [← hg, map_sub, sub_eq_zero]
      exact (TopRep.hom_comm_apply _ g y).trans
        ((congrArg _ hy).trans ((x.2 g).trans hy.symm)))
  -- so at a common deeper stage the image of `y` is invariant
  obtain ⟨l', f', a, ha⟩ := IsFiltered.wideSpan f
  refine ⟨l', ⟨(resolutionMap (ContinuousMonoidHom.id G) (X.map f').hom (n + 1)).hom y,
    fun g ↦ ?_⟩, Subtype.ext ?_⟩
  · have h := congrArg (resolutionMap (ContinuousMonoidHom.id G)
      (X.map (a ⟨Y.ρ g y, g, rfl⟩)).hom (n + 1)).hom (hf ⟨Y.ρ g y, g, rfl⟩)
    rw [resolutionMap_map_comp_apply, ha, map_sub, map_zero, sub_eq_zero] at h
    exact (TopRep.hom_comm_apply _ g y).symm.trans h
  · exact (resolutionMap_ι_app_map_apply f' (n + 1) y).trans hy

/-- A homogeneous cochain at some stage whose image in the colimit vanishes already vanishes at
some deeper stage of the diagram. -/
private theorem exists_cochainsMap_f_eq_zero (n : ℕ) {j : J}
    (y : (TopRep.homogeneousCochains (X.obj j).obj).X n)
    (hy : (cochainsMap (ContinuousMonoidHom.id G) (c.ι.app j).hom).f n y = 0) :
    ∃ (l : J) (f : j ⟶ l), (cochainsMap (ContinuousMonoidHom.id G) (X.map f).hom).f n y = 0 := by
  obtain ⟨l, f, hf⟩ := exists_resolutionMap_eq_zero hc (n + 1) y.1 (congrArg Subtype.val hy)
  exact ⟨l, f, Subtype.ext hf⟩

end Descent

/-! ### Cohomology -/

section Cohomology

variable {J : Type w'} [Category.{w} J]
  {X : J ⥤ SmoothDiscreteTopRep.{v, u, u} k G} {c : Cocone X}

/-- The transition maps of the diagram followed by the legs of the cocone are the legs, on
continuous cohomology classes. -/
private theorem coeffMap_ι_app_map_apply {i j : J} (f : i ⟶ j) (n : ℕ)
    (y : continuousCohomology n (X.obj i).obj) :
    (coeffMap (c.ι.app j).hom n).hom ((coeffMap (X.map f).hom n).hom y) =
      (coeffMap (c.ι.app i).hom n).hom y := by
  rw [← ConcreteCategory.comp_apply, ← coeffMap_comp,
    ← ObjectProperty.FullSubcategory.comp_hom, c.w]

/-- The transition maps of the diagram compose, on continuous cohomology classes. -/
private theorem coeffMap_map_comp_apply {i j l : J} (f : i ⟶ j) (g : j ⟶ l) (n : ℕ)
    (y : continuousCohomology n (X.obj i).obj) :
    (coeffMap (X.map g).hom n).hom ((coeffMap (X.map f).hom n).hom y) =
      (coeffMap (X.map (f ≫ g)).hom n).hom y := by
  rw [← ConcreteCategory.comp_apply, ← coeffMap_comp,
    ← ObjectProperty.FullSubcategory.comp_hom, ← X.map_comp]

variable [CompactSpace G] [IsFiltered J]
  (hc : IsColimit ((smoothDiscreteι k G ⋙ forget (TopRep k G)).mapCocone c))
include hc

/-- **Every class comes from some stage.** For a compact group `G` and a filtered diagram of smooth
discrete representations whose cocone `c` is a colimit on underlying sets, every class of
`Hⁿ(G, c.pt)` is the image of a class of `Hⁿ(G, X_j)` for some stage `j`. A representing cocycle
is itself the image of a cocycle at some stage, with no coboundary subtracted. -/
theorem exists_coeffMap_eq_of_isColimit {n : ℕ} (x : continuousCohomology n c.pt.obj) :
    ∃ (j : J) (y : continuousCohomology n (X.obj j).obj),
      (coeffMap (c.ι.app j).hom n).hom y = x := by
  set K := TopRep.homogeneousCochains c.pt.obj
  obtain ⟨z, rfl⟩ := K.homologyπ_surjective n x
  -- lift a representing cocycle to some stage
  obtain ⟨j, y, hy⟩ := exists_cochainsMap_f_eq hc n (K.iCycles n z)
  set ιj := cochainsMap (ContinuousMonoidHom.id G) (c.ι.app j).hom
  -- its differential vanishes in the colimit, hence at a deeper stage
  have hd : ιj.f (n + 1) (((X.obj j).obj.homogeneousCochains.d n (n + 1)).hom y) = 0 := by
    have h := ConcreteCategory.congr_hom (ιj.comm n (n + 1)) y
    simp only [ConcreteCategory.comp_apply] at h
    exact h.symm.trans ((congrArg _ hy).trans (K.d_iCycles_apply (n + 1) z))
  obtain ⟨l, f, hf⟩ := exists_cochainsMap_f_eq_zero hc (n + 1) _ hd
  set tf := cochainsMap (ContinuousMonoidHom.id G) (X.map f).hom
  have hdl : ((X.obj l).obj.homogeneousCochains.d n (n + 1)).hom (tf.f n y) = 0 := by
    have h := ConcreteCategory.congr_hom (tf.comm n (n + 1)) y
    simp only [ConcreteCategory.comp_apply] at h
    exact h.trans hf
  -- so the transported lift is a cocycle at that stage, whose class maps to the given one
  refine ⟨l, (X.obj l).obj.homogeneousCochains.homologyπ n
    ((X.obj l).obj.homogeneousCochains.cyclesMkOfEq _ (n + 1) (CochainComplex.next ℕ n) hdl), ?_⟩
  rw [coeffMap_def]
  refine (map_π_apply _ _ n _).trans (congrArg (K.homologyπ n).hom (K.iCycles_injective n ?_))
  refine (iCycles_cocyclesMap_apply _ _ n _).trans ?_
  rw [HomologicalComplex.iCycles_cyclesMkOfEq]
  exact (cochainsMap_id_apply_of_comp_eq _ _ (congrArg (·.hom) (c.w f)) n y).trans hy

/-- **Vanishing descends.** For a compact group `G` and a filtered diagram of smooth discrete
representations whose cocone `c` is a colimit on underlying sets, a class of `Hⁿ(G, X_j)` whose
image in `Hⁿ(G, c.pt)` vanishes already vanishes in `Hⁿ(G, X_l)` for some stage `l` under `j`. -/
theorem exists_coeffMap_eq_zero_of_isColimit {n : ℕ} {j : J}
    (y : continuousCohomology n (X.obj j).obj) (hy : (coeffMap (c.ι.app j).hom n).hom y = 0) :
    ∃ (l : J) (f : j ⟶ l), (coeffMap (X.map f).hom n).hom y = 0 := by
  set K := TopRep.homogeneousCochains c.pt.obj
  obtain ⟨z, rfl⟩ := (X.obj j).obj.homogeneousCochains.homologyπ_surjective n y
  obtain ⟨m, hm⟩ : ∃ m, (ComplexShape.up ℕ).prev n = m := ⟨_, rfl⟩
  -- the image of the cocycle is the coboundary of some cochain `w` in the colimit
  rw [coeffMap_def] at hy
  obtain ⟨w, hw⟩ := (K.homologyπ_eq_zero_iff n hm).1 ((map_π_apply _ _ n z).symm.trans hy)
  -- which comes from some stage `j'`
  obtain ⟨j', w', hw'⟩ := exists_cochainsMap_f_eq hc m w
  -- at a common stage `i`, the difference of the cocycle and the coboundary of `w'` vanishes in
  -- the colimit, hence at a deeper stage `l`
  set i := IsFiltered.max j j'
  set a := IsFiltered.leftToMax j j'
  set b := IsFiltered.rightToMax j j'
  set ta := cochainsMap (ContinuousMonoidHom.id G) (X.map a).hom
  set tb := cochainsMap (ContinuousMonoidHom.id G) (X.map b).hom
  set ιi := cochainsMap (ContinuousMonoidHom.id G) (c.ι.app i).hom
  have hd :
      ιi.f n (((X.obj i).obj.homogeneousCochains.d m n).hom (tb.f m w')) = (K.d m n).hom w := by
    have h := ConcreteCategory.congr_hom (ιi.comm m n) (tb.f m w')
    simp only [ConcreteCategory.comp_apply] at h
    exact h.symm.trans (congrArg _
      ((cochainsMap_id_apply_of_comp_eq _ _ (congrArg (·.hom) (c.w b)) m w').trans hw'))
  have hz : ιi.f n (ta.f n ((X.obj j).obj.homogeneousCochains.iCycles n z)) = (K.d m n).hom w :=
    (cochainsMap_id_apply_of_comp_eq _ _ (congrArg (·.hom) (c.w a)) n _).trans
      ((iCycles_cocyclesMap_apply _ _ n z).symm.trans
        ((congrArg (K.iCycles n) hw.symm).trans (K.iCycles_toCycles_apply m w)))
  obtain ⟨l, f, hf⟩ := exists_cochainsMap_f_eq_zero hc n
    (ta.f n ((X.obj j).obj.homogeneousCochains.iCycles n z) -
      ((X.obj i).obj.homogeneousCochains.d m n).hom (tb.f m w'))
    (by rw [map_sub, hz, hd, sub_self])
  set tf := cochainsMap (ContinuousMonoidHom.id G) (X.map f).hom
  rw [map_sub, sub_eq_zero] at hf
  -- there the transported cocycle is the coboundary of the transported `w'`
  refine ⟨l, a ≫ f, ?_⟩
  rw [coeffMap_def]
  refine (map_π_apply _ _ n z).trans
    (((X.obj l).obj.homogeneousCochains.homologyπ_eq_zero_iff n hm).2
      ⟨tf.f m (tb.f m w'), HomologicalComplex.iCycles_injective _ n ?_⟩)
  refine (HomologicalComplex.iCycles_toCycles_apply _ m _).trans
    (Eq.trans ?_ (iCycles_cocyclesMap_apply _ _ n z).symm)
  have h := ConcreteCategory.congr_hom (tf.comm m n) (tb.f m w')
  simp only [ConcreteCategory.comp_apply] at h
  exact h.trans (hf.symm.trans
    (cochainsMap_id_apply_of_comp_eq _ _ (congrArg (·.hom) (X.map_comp a f).symm) n _))

/-- Two classes at two stages with the same image in `Hⁿ(G, c.pt)` agree at a common deeper
stage. -/
private theorem exists_coeffMap_eq_coeffMap_of_isColimit {n : ℕ} {i j : J}
    (yi : continuousCohomology n (X.obj i).obj) (yj : continuousCohomology n (X.obj j).obj)
    (h : (coeffMap (c.ι.app i).hom n).hom yi = (coeffMap (c.ι.app j).hom n).hom yj) :
    ∃ (l : J) (f : i ⟶ l) (g : j ⟶ l),
      (coeffMap (X.map f).hom n).hom yi = (coeffMap (X.map g).hom n).hom yj := by
  set a := IsFiltered.leftToMax i j
  set b := IsFiltered.rightToMax i j
  -- the difference of the two classes at the common stage vanishes in the colimit
  obtain ⟨l, f, hf⟩ := exists_coeffMap_eq_zero_of_isColimit hc
    ((coeffMap (X.map a).hom n).hom yi - (coeffMap (X.map b).hom n).hom yj) (by
      rw [map_sub, coeffMap_ι_app_map_apply (c := c) a,
        coeffMap_ι_app_map_apply (c := c) b, h, sub_self])
  refine ⟨l, a ≫ f, b ≫ f, ?_⟩
  rw [map_sub, sub_eq_zero, coeffMap_map_comp_apply (X := X) a f,
    coeffMap_map_comp_apply (X := X) b f] at hf
  exact hf

variable (n : ℕ) [UnivLE.{w', u}] [UnivLE.{w, u}]

/-- **Continuous cohomology of a compact group commutes with filtered colimits of smooth discrete
coefficients.** For a compact group `G` and a filtered diagram of smooth discrete representations
whose cocone `c` is a colimit on underlying sets, the image of `c` under `Hⁿ(G, -)` is a colimit in
`TopModuleCat k`: `Hⁿ(G, colim_j X_j) = colim_j Hⁿ(G, X_j)`. -/
noncomputable def isColimitMapCoconeOfIsColimitForget :
    IsColimit ((smoothDiscreteι k G ⋙ continuousCohomologyFunctor k G n).mapCocone c) := by
  have := c.pt.property.discreteTopology
  have : DiscreteTopology
      ((smoothDiscreteι k G ⋙ continuousCohomologyFunctor k G n).mapCocone c).pt :=
    inferInstanceAs (DiscreteTopology (continuousCohomology n c.pt.obj))
  exact TopModuleCat.isColimitOfJointlySurjective
    ((smoothDiscreteι k G ⋙ continuousCohomologyFunctor k G n).mapCocone c)
    (fun x ↦ exists_coeffMap_eq_of_isColimit hc x)
    fun i j yi yj h ↦ exists_coeffMap_eq_coeffMap_of_isColimit hc yi yj h

end Cohomology

/-- **Continuous cohomology of a compact group preserves filtered colimits of smooth discrete
coefficients.** For a compact group `G`, the functor `Hⁿ(G, -)` from smooth discrete
representations to topological modules preserves filtered colimits, in every degree `n`. -/
theorem continuousCohomology_preservesFilteredColimits [CompactSpace G] [UnivLE.{w', u}]
    [UnivLE.{w, u}] (n : ℕ) :
    PreservesFilteredColimitsOfSize.{w', w}
      (smoothDiscreteι.{v, u, u} k G ⋙ continuousCohomologyFunctor k G n) where
  preserves_filtered_colimits J _ _ := by
    have : PreservesFilteredColimitsOfSize.{w', w}
        (smoothDiscreteι.{v, u, u} k G ⋙ forget (TopRep.{u} k G)) :=
      preservesFilteredColimitsOfSize_of_univLE.{u, u, w', w} _
    exact ⟨fun {X} ↦ ⟨fun {c} hc ↦
      ⟨isColimitMapCoconeOfIsColimitForget (isColimitOfPreserves _ hc) n⟩⟩⟩

end TauCeti.ContinuousCohomology
