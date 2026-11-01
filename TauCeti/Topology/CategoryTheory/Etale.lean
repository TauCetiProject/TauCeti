/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Action
public import Mathlib.Combinatorics.Quiver.Subquiver
public import Mathlib.Topology.DiscreteSubset
public import Mathlib.Topology.IsLocalHomeomorph
public import Mathlib.Topology.Maps.Proper.Basic
public import Mathlib.Topology.OpenPartialHomeomorph.Basic
public import TauCeti.CategoryTheory.Groupoid.ActionCategory.Basic

/-!
# Finite local arrow charts for proper étale presentations

Give the objects and the total arrows of a quiver their own topologies. If the source is a
local homeomorphism and the source-target map is proper, there are finitely many arrows between
any two objects. In particular, the isotropy of a groupoid with these properties is finite.

If target is also a local homeomorphism and the arrow space is Hausdorff, the arrows at an
object admit pairwise disjoint open bisection neighborhoods. After shrinking the object
neighborhood, these bisections contain every arrow with both endpoints in that neighborhood.
This is the finite retained-arrow neighborhood needed to reconstruct local finite actions:
different isotropy arrows remain separate, even if their induced object maps coincide.

For a groupoid whose units and composition are also continuous, these bisections assemble into
a local action of the isotropy group (`TauCeti.exists_isotropy_action_of_proper_source_target`).
Following each bisection from a nearby source gives a local homeomorphism for each isotropy arrow
`g`. Continuity of composition makes these maps compose like `Aut x` near `x`, and an invariant
shrinking gives an open neighbourhood `U` with a continuous action of `Aut x`. The resulting
functor from the action groupoid `Aut x ⋉ U` is fully faithful and the inclusion on objects, so
it identifies `Aut x ⋉ U` with the full subgroupoid on `U`. The arrows of each label form an open
set, parametrized homeomorphically by their sources. The isotropy group acts with its
multiplication `g * h = h ≫ g`, and each isotropy arrow is its own label even when it acts
trivially near `x`.

No new groupoid carrier or topology on individual hom types is introduced. The results apply
to native categorical groupoids through `Quiver.Total`, and only use the displayed topological
hypotheses. Inversion is never needed, and the neighbourhood statements need no composition.

## References

* I. Moerdijk, *Orbifolds as groupoids: an introduction*, Section 2.
* A. Adem, J. Leida and Y. Ruan, *Orbifolds and stringy topology*, Chapter 1.
-/

public section

open Set Topology

namespace TauCeti

section Quiver

variable {C : Type*} [Quiver C] [TopologicalSpace C] [TopologicalSpace (Quiver.Total C)]

/-- A proper source-target map and a locally homeomorphic source imply that each set of
arrows with prescribed endpoints is finite. No separation hypothesis is needed. -/
theorem finite_total_arrows_of_proper_source_target
    (hp : IsProperMap (fun a : Quiver.Total C ↦ (a.left, a.right)))
    (hs : IsLocalHomeomorph (Quiver.Total.left : Quiver.Total C → C)) (x y : C) :
    Set.Finite {a : Quiver.Total C | a.left = x ∧ a.right = y} := by
  have hc : IsCompact {a : Quiver.Total C | a.left = x ∧ a.right = y} := by
    simpa only [Set.preimage, Set.mem_singleton_iff, Prod.mk.injEq] using
      hp.isCompact_preimage (isCompact_singleton (x := (x, y)))
  apply hc.finite
  apply hs.isLocalHomeomorphOn.isDiscrete_of_image
  exact Set.subsingleton_singleton.isDiscrete.mono fun _ ⟨a, ha, h⟩ ↦ h ▸ ha.1

/-- Every hom type is finite in a quiver with proper source-target map and locally
homeomorphic source. Applied with equal endpoints, this gives finiteness of isotropy. -/
theorem finite_hom_of_proper_source_target
    (hp : IsProperMap (fun a : Quiver.Total C ↦ (a.left, a.right)))
    (hs : IsLocalHomeomorph (Quiver.Total.left : Quiver.Total C → C)) (x y : C) :
    Finite (x ⟶ y) := by
  have := (finite_total_arrows_of_proper_source_target hp hs x y).to_subtype
  exact Finite.of_injective (fun f : x ⟶ y ↦
    (⟨⟨x, y, f⟩, rfl, rfl⟩ : {a : Quiver.Total C // a.left = x ∧ a.right = y}))
    (by intro f g h; simpa using congrArg Subtype.val h)

/-- Near an object of a Hausdorff proper étale presentation, all arrows lie in finitely many
pairwise disjoint open bisections, one through each isotropy arrow. The bisections retain
actual arrows, not just the germs of the corresponding object maps. -/
theorem exists_disjoint_bisections_of_proper_source_target [T2Space (Quiver.Total C)]
    (hp : IsProperMap (fun a : Quiver.Total C ↦ (a.left, a.right)))
    (hs : IsLocalHomeomorph (Quiver.Total.left : Quiver.Total C → C))
    (ht : IsLocalHomeomorph (Quiver.Total.right : Quiver.Total C → C)) (x : C) :
    ∃ (U : Set C) (W : (x ⟶ x) → Set (Quiver.Total C)),
      IsOpen U ∧ x ∈ U ∧
      (∀ f, IsOpen (W f) ∧ (⟨x, x, f⟩ : Quiver.Total C) ∈ W f ∧
        IsOpenEmbedding ((W f).domRestrict Quiver.Total.left) ∧
        IsOpenEmbedding ((W f).domRestrict Quiver.Total.right)) ∧
      Pairwise (fun f g ↦ Disjoint (W f) (W g)) ∧
      ∀ a : Quiver.Total C, a.left ∈ U → a.right ∈ U → ∃! f, a ∈ W f := by
  classical
  let A := {a : Quiver.Total C | a.left = x ∧ a.right = x}
  have hA : A.Finite := finite_total_arrows_of_proper_source_target hp hs x x
  obtain ⟨O, hO, hdisj⟩ := hA.t2_separation
  have hb (a : Quiver.Total C) : ∃ W : Set (Quiver.Total C),
      IsOpen W ∧ a ∈ W ∧ W ⊆ O a ∧
      IsOpenEmbedding (W.domRestrict Quiver.Total.left) ∧
      IsOpenEmbedding (W.domRestrict Quiver.Total.right) := by
    obtain ⟨S, hS, hsS⟩ := isLocalHomeomorph_iff_isOpenEmbedding_restrict.mp hs a
    obtain ⟨T, hT, htT⟩ := isLocalHomeomorph_iff_isOpenEmbedding_restrict.mp ht a
    obtain ⟨W, hWsub, hW, haW⟩ := mem_nhds_iff.mp
      (Filter.inter_mem (Filter.inter_mem hS hT) ((hO a).2.mem_nhds (hO a).1))
    refine ⟨W, hW, haW, fun b hb ↦ (hWsub hb).2, ?_, ?_⟩
    · exact hsS.comp (.inclusion (fun b hb ↦ (hWsub hb).1.1)
        (hW.preimage continuous_subtype_val))
    · exact htT.comp (.inclusion (fun b hb ↦ (hWsub hb).1.2)
        (hW.preimage continuous_subtype_val))
  choose B hBopen hBmem hBsub hBs hBt using hb
  let W (f : x ⟶ x) := B ⟨x, x, f⟩
  have hcover : ∀ a : Quiver.Total C, a.left = x → a.right = x → a ∈ ⋃ f, W f := by
    rintro ⟨a, b, f⟩ ha hb
    dsimp only at ha hb
    subst a b
    exact mem_iUnion.mpr ⟨f, hBmem _⟩
  have hpair : Pairwise (fun f g ↦ Disjoint (W f) (W g)) := by
    intro f g hfg
    apply (hdisj (by exact ⟨rfl, rfl⟩) (by exact ⟨rfl, rfl⟩) ?_).mono (hBsub _) (hBsub _)
    intro h
    exact hfg (by simpa using h)
  -- Closedness excludes every arrow outside these bisections near the whole isotropy fiber.
  have hnear := hp.isClosedMap.eventually_nhds_fiber (p := fun a ↦ a ∈ ⋃ f, W f) (x, x)
    (by
      intro a ha
      exact (isOpen_iUnion fun f ↦ hBopen ⟨x, x, f⟩).mem_nhds
        (hcover a (Prod.mk.inj ha).1 (Prod.mk.inj ha).2))
  obtain ⟨U, V, hU, hxU, hV, hxV, hUV⟩ := mem_nhds_prod_iff'.mp hnear
  refine ⟨U ∩ V, W, hU.inter hV, ⟨hxU, hxV⟩,
    fun f ↦ ⟨hBopen _, hBmem _, hBs _, hBt _⟩, hpair, ?_⟩
  intro a ha hb
  obtain ⟨f, hf⟩ := mem_iUnion.mp (hUV ⟨ha.1, hb.2⟩ a rfl)
  exact ⟨f, hf, fun g hg ↦ by
    by_contra hgf
    exact Set.disjoint_left.mp (hpair hgf) hg hf⟩

/-- A local continuous section of the source through an arrow of an open set on which the
source is an open embedding. -/
private theorem exists_section_of_isOpenEmbedding {W : Set (Quiver.Total C)}
    (hW : IsOpenEmbedding (W.domRestrict Quiver.Total.left)) {a : Quiver.Total C} (ha : a ∈ W) :
    ∃ (σ : C → Quiver.Total C) (T : Set C), ContinuousOn σ T ∧ IsOpen T ∧ a.left ∈ T ∧
      (∀ y ∈ T, σ y ∈ W ∧ (σ y).left = y) ∧ σ a.left = a := by
  have : Nonempty W := ⟨⟨a, ha⟩⟩
  let e := hW.toOpenPartialHomeomorph (W.domRestrict Quiver.Total.left)
  refine ⟨fun y ↦ (e.symm y : Quiver.Total C), e.target,
    continuous_subtype_val.comp_continuousOn e.continuousOn_symm, e.open_target, ?_,
    fun y hy ↦ ⟨(e.symm y).2, ?_⟩, ?_⟩
  · rw [hW.toOpenPartialHomeomorph_target]
    exact ⟨⟨a, ha⟩, rfl⟩
  · rw [hW.toOpenPartialHomeomorph_target] at hy
    exact hW.toOpenPartialHomeomorph_right_inv _ hy
  · exact congrArg Subtype.val (hW.toOpenPartialHomeomorph_left_inv (x := ⟨a, ha⟩))

/-- The restriction of a local section of the source to an open set is an open embedding,
when the section lands in an open set of arrows on which arrows are determined by their
source. -/
private theorem isOpenEmbedding_restrict_section {W : Set (Quiver.Total C)} (hW : IsOpen W)
    (hl : Continuous (Quiver.Total.left : Quiver.Total C → C))
    (hinj : ∀ b ∈ W, ∀ b' ∈ W, b.left = b'.left → b = b') {σ : C → Quiver.Total C}
    {U : Set C} (hU : IsOpen U) (hσc : ContinuousOn σ U)
    (hσ : ∀ y ∈ U, σ y ∈ W ∧ (σ y).left = y) : IsOpenEmbedding fun y : U ↦ σ y := by
  refine .of_continuous_injective_isOpenMap
    (hσc.comp_continuous continuous_subtype_val Subtype.prop)
    (fun y y' h ↦ Subtype.ext ((hσ y y.2).2.symm.trans
      ((congrArg Quiver.Total.left h).trans (hσ y' y'.2).2))) ?_
  rintro _ ⟨O, hO, rfl⟩
  -- The image of `U ∩ O` is the set of arrows of `W` with source in `U ∩ O`.
  have himage : (fun y : U ↦ σ y) '' (Subtype.val ⁻¹' O) =
      W ∩ Quiver.Total.left ⁻¹' (U ∩ O) := by
    ext b
    constructor
    · rintro ⟨y, hy, rfl⟩
      refine ⟨(hσ y y.2).1, ?_⟩
      rw [Set.mem_preimage, (hσ y y.2).2]
      exact ⟨y.2, hy⟩
    · rintro ⟨hbW, hbU, hbO⟩
      exact ⟨⟨b.left, hbU⟩, hbO, hinj _ (hσ _ hbU).1 _ hbW (hσ _ hbU).2⟩
  rw [himage]
  exact hW.inter ((hU.inter hO).preimage hl)

end Quiver

open CategoryTheory

section Category

variable {C : Type*} [Category C]

/-- The composite of a composable pair of total arrows. -/
private def compTotal (p : {p : Quiver.Total C × Quiver.Total C // p.1.right = p.2.left}) :
    Quiver.Total C :=
  ⟨p.1.1.left, p.1.2.right, p.1.1.hom ≫ eqToHom p.2 ≫ p.1.2.hom⟩

private theorem compTotal_congr
    {p q : {p : Quiver.Total C × Quiver.Total C // p.1.right = p.2.left}} (h : p.1 = q.1) :
    compTotal p = compTotal q :=
  congrArg compTotal (Subtype.ext h)

/-- A total arrow with identified endpoints, read as a morphism between those endpoints. -/
private def homOfTotal (a : Quiver.Total C) {y z : C} (hy : a.left = y) (hz : a.right = z) :
    y ⟶ z :=
  eqToHom hy.symm ≫ a.hom ≫ eqToHom hz

private theorem mk_homOfTotal (a : Quiver.Total C) {y z : C} (hy : a.left = y)
    (hz : a.right = z) : (⟨y, z, homOfTotal a hy hz⟩ : Quiver.Total C) = a := by
  subst hy hz
  simp [homOfTotal]

private theorem homOfTotal_eq_of_mk_eq {a : Quiver.Total C} {y z : C} (hy : a.left = y)
    (hz : a.right = z) {φ : y ⟶ z} (h : (⟨y, z, φ⟩ : Quiver.Total C) = a) :
    homOfTotal a hy hz = φ := by
  subst h
  simp [homOfTotal]

private theorem mk_homOfTotal_comp {a b : Quiver.Total C} {y z w : C} (hy : a.left = y)
    (hz : a.right = z) (hz' : b.left = z) (hw : b.right = w) :
    (⟨y, w, homOfTotal a hy hz ≫ homOfTotal b hz' hw⟩ : Quiver.Total C) =
      compTotal ⟨(a, b), hz.trans hz'.symm⟩ := by
  obtain ⟨a₁, a₂, f⟩ := a
  obtain ⟨b₁, b₂, g⟩ := b
  dsimp only at hy hz hz' hw
  subst hy hz hz' hw
  simp [homOfTotal, compTotal]

end Category

section Groupoid

variable {C : Type*} [Groupoid C] [TopologicalSpace C] [TopologicalSpace (Quiver.Total C)]

/-- If two local sections of the source compose at `x` to an arrow in an open set `O`, then
they compose into `O` at every source near `x`. -/
private theorem eventually_compTotal_mem
    (hc : Continuous (compTotal (C := C)))
    (ht : Continuous (Quiver.Total.right : Quiver.Total C → C))
    {σ τ : C → Quiver.Total C} {S T : Set C} (hσ : ContinuousOn σ S) (hτ : ContinuousOn τ T)
    (hS : IsOpen S) (hT : IsOpen T) (hτl : ∀ z ∈ T, (τ z).left = z) {x : C} (hxS : x ∈ S)
    (hxT : (σ x).right ∈ T) {O : Set (Quiver.Total C)} (hO : IsOpen O)
    (hOx : ∀ h, compTotal ⟨(σ x, τ (σ x).right), h⟩ ∈ O) :
    ∀ᶠ y in 𝓝 x, ∀ h : (σ y).right = (τ (σ y).right).left,
      compTotal ⟨(σ y, τ (σ y).right), h⟩ ∈ O := by
  have hσr : ContinuousOn (fun y ↦ (σ y).right) S := ht.comp_continuousOn hσ
  set D := S ∩ (fun y ↦ (σ y).right) ⁻¹' T
  have hD : IsOpen D := hσr.isOpen_inter_preimage hS hT
  -- On `D` both sections are defined, and their composite is continuous.
  let Φ : D → Quiver.Total C := fun y ↦
    compTotal ⟨(σ y, τ (σ y).right), (hτl _ y.2.2).symm⟩
  have hΦ : Continuous Φ := hc.comp <| Continuous.subtype_mk
    ((hσ.comp_continuous continuous_subtype_val fun y ↦ y.2.1).prodMk
      (hτ.comp_continuous (hσr.comp_continuous continuous_subtype_val fun y ↦ y.2.1)
        fun y ↦ y.2.2)) _
  rw [← hD.isOpenMap_subtype_val.map_nhds_eq continuous_subtype_val.continuousAt
    (x := ⟨x, hxS, hxT⟩)]
  exact Filter.eventually_map.2
    ((hΦ.continuousAt.eventually_mem (hO.mem_nhds (hOx _))).mono fun y hy _ ↦ hy)

/-- **Local isotropy actions of proper étale groupoids.** Near an object `x` of a Hausdorff
proper étale groupoid with continuous units and composition, the groupoid is the action
groupoid of its isotropy group: there is an open neighbourhood `U` of `x` with a continuous
action of `Aut x`, and a fully faithful functor `Aut x ⋉ U ⥤ C` which is the inclusion on
objects. Hence it identifies the action groupoid with the full subgroupoid on `U`. For each label
`g`, the arrows labelled `g` form an open set of arrows, parametrized homeomorphically by their
sources, and the arrow labelled `g` at `x` is the isotropy arrow `g` itself. Every isotropy arrow
is retained as its own label, even when it acts trivially on `U`. -/
theorem exists_isotropy_action_of_proper_source_target [T2Space (Quiver.Total C)]
    (hp : IsProperMap (fun a : Quiver.Total C ↦ (a.left, a.right)))
    (hs : IsLocalHomeomorph (Quiver.Total.left : Quiver.Total C → C))
    (ht : IsLocalHomeomorph (Quiver.Total.right : Quiver.Total C → C))
    (hu : Continuous fun y : C ↦ (⟨y, y, 𝟙 y⟩ : Quiver.Total C))
    (hc : Continuous fun p : {p : Quiver.Total C × Quiver.Total C // p.1.right = p.2.left} ↦
      (⟨p.1.1.left, p.1.2.right, p.1.1.hom ≫ eqToHom p.2 ≫ p.1.2.hom⟩ : Quiver.Total C))
    (x : C) :
    ∃ (U : Set C) (_ : MulAction (Aut x) U) (F : ActionCategory (Aut x) U ⥤ C),
      IsOpen U ∧ x ∈ U ∧ (∀ g : Aut x, Continuous fun y : U ↦ g • y) ∧
      (∀ a, F.obj a = (a.back : C)) ∧ F.Full ∧ F.Faithful ∧
      (∀ g : Aut x, IsOpenEmbedding fun y : U ↦
        (⟨_, _, F.map ((ActionCategory.totalEquiv (Aut x) U).symm (g, y)).hom⟩ :
          Quiver.Total C)) ∧
      ∀ (hx : x ∈ U) (g : Aut x),
        (⟨_, _, F.map ((ActionCategory.totalEquiv (Aut x) U).symm (g, ⟨x, hx⟩)).hom⟩ :
          Quiver.Total C) = ⟨x, x, g.asIso.hom⟩ := by
  -- Outline: take the disjoint bisections `W g` through the isotropy arrows and their source
  -- sections `σ g`. Near `x`, continuity of units and composition forces `σ 1` to be the unit
  -- section and `σ (g * h)` to be the composite of `σ h` and `σ g`. An invariant shrinking `U`
  -- of that neighbourhood carries the action `g • y = (σ g y).right`, and `σ` gives the functor.
  obtain ⟨U₀, W, hU₀, hxU₀, hW, hdisj, hcover⟩ :=
    exists_disjoint_bisections_of_proper_source_target hp hs ht x
  have := finite_hom_of_proper_source_target hp hs x x
  have : Finite (Aut x) := .of_equiv _ (Aut.isoEquiv.trans (Groupoid.isoEquivHom x x)).symm
  have huniq (f : x ⟶ x) {b b' : Quiver.Total C} (hb : b ∈ W f) (hb' : b' ∈ W f)
      (h : b.left = b'.left) : b = b' :=
    congrArg Subtype.val (@(hW f).2.2.1.injective ⟨b, hb⟩ ⟨b', hb'⟩ h)
  -- The section `σ g` of the source through the bisection of each isotropy arrow `g`.
  choose σ T hσc hT hxT hσ hσx using fun g : Aut x ↦
    exists_section_of_isOpenEmbedding (hW g.asIso.hom).2.2.1 (hW g.asIso.hom).2.1
  have hact (g : Aut x) : ContinuousOn (fun y ↦ (σ g y).right) (T g) :=
    ht.continuous.comp_continuousOn (hσc g)
  have hσxr (g : Aut x) : (σ g x).right = x := by rw [hσx g]
  -- Near `x`, the sections compose like the isotropy group and the unit section is `σ 1`.
  have hE : ∀ᶠ y in 𝓝 x, y ∈ U₀ ∧ (∀ g, y ∈ T g) ∧ (∀ g h, (σ h y).right ∈ T g) ∧
      (⟨y, y, 𝟙 y⟩ : Quiver.Total C) ∈ W (1 : Aut x).asIso.hom ∧
      ∀ g h (hgh : (σ h y).right = (σ g (σ h y).right).left),
        compTotal ⟨(σ h y, σ g (σ h y).right), hgh⟩ ∈ W (g * h).asIso.hom := by
    refine (hU₀.eventually_mem hxU₀).and
      ((Filter.eventually_all.2 fun g ↦ (hT g).eventually_mem (hxT g)).and
      ((Filter.eventually_all.2 fun g ↦ Filter.eventually_all.2 fun h ↦ ?_).and
      ((hu.continuousAt.eventually_mem ((hW _).1.mem_nhds (hW _).2.1)).and
      (Filter.eventually_all.2 fun g ↦ Filter.eventually_all.2 fun h ↦ ?_))))
    · exact ((hact h).continuousAt ((hT h).mem_nhds (hxT h))).eventually_mem
        ((hT g).mem_nhds (by rw [hσxr]; exact hxT g))
    · refine eventually_compTotal_mem hc ht.continuous (hσc h) (hσc g) (hT h) (hT g)
        (fun z hz ↦ (hσ g z hz).2) (hxT h) (by rw [hσxr]; exact hxT g) (hW _).1 fun hgh ↦ ?_
      -- At `x` the two sections pass through `h` and `g`, which compose to `g * h`.
      have : compTotal ⟨(σ h x, σ g (σ h x).right), hgh⟩ = ⟨x, x, (g * h).asIso.hom⟩ := by
        refine (compTotal_congr (q := ⟨(⟨x, x, h.asIso.hom⟩, ⟨x, x, g.asIso.hom⟩), rfl⟩)
          (Prod.ext (hσx h) ?_)).trans ?_
        · simp only [hσxr]
          exact hσx g
        · simp [compTotal]
      rw [this]
      exact (hW _).2.1
  obtain ⟨V, hVE, hV, hxV⟩ := mem_nhds_iff.mp hE
  have hone (y : C) (hy : y ∈ V) : σ 1 y = ⟨y, y, 𝟙 y⟩ :=
    huniq _ (hσ 1 y ((hVE hy).2.1 1)).1 (hVE hy).2.2.2.1 (hσ 1 y ((hVE hy).2.1 1)).2
  have hmul (y : C) (hy : y ∈ V) (g h : Aut x) : σ (g * h) y =
      compTotal ⟨(σ h y, σ g (σ h y).right), ((hσ g _ ((hVE hy).2.2.1 g h)).2).symm⟩ :=
    huniq _ (hσ _ y ((hVE hy).2.1 _)).1 ((hVE hy).2.2.2.2 g h _)
      ((hσ _ y ((hVE hy).2.1 _)).2.trans (hσ h y ((hVE hy).2.1 h)).2.symm)
  -- Shrink `V` to the neighbourhood `U` which the local action preserves.
  set U : Set C := V ∩ ⋂ g, T g ∩ (fun y ↦ (σ g y).right) ⁻¹' V
  have hUo : IsOpen U :=
    hV.inter (isOpen_iInter_of_finite fun g ↦ (hact g).isOpen_inter_preimage (hT g) hV)
  have hxU : x ∈ U := ⟨hxV, Set.mem_iInter.2 fun g ↦ ⟨hxT g, by
    simp only [Set.mem_preimage, hσxr]; exact hxV⟩⟩
  have hUT (y : C) (hy : y ∈ U) (g : Aut x) : y ∈ T g := (Set.mem_iInter.1 hy.2 g).1
  have hUσ (y : C) (hy : y ∈ U) (h : Aut x) : (σ h y).right ∈ U := by
    refine ⟨(Set.mem_iInter.1 hy.2 h).2, Set.mem_iInter.2 fun g ↦ ⟨(hVE hy.1).2.2.1 g h, ?_⟩⟩
    have := (Set.mem_iInter.1 hy.2 (g * h)).2
    rwa [Set.mem_preimage, hmul y hy.1] at this
  let inst : MulAction (Aut x) U :=
    { smul g y := ⟨(σ g y).right, hUσ y y.2 g⟩
      one_smul y := Subtype.ext ((congrArg Quiver.Total.right (hone y y.2.1)).trans rfl)
      mul_smul g h y :=
        Subtype.ext ((congrArg Quiver.Total.right (hmul y y.2.1 g h)).trans rfl) }
  let F : ActionCategory (Aut x) U ⥤ C :=
    { obj a := a.back
      map {a b} f := homOfTotal (σ f.hom a.back) (hσ _ _ (hUT _ a.back.2 _)).2
        (congrArg Subtype.val f.map_val)
      map_id a := homOfTotal_eq_of_mk_eq _ _ (by
        rw [ActionCategory.id_hom]
        exact (hone _ a.back.2.1).symm)
      map_comp {a b c} f g := homOfTotal_eq_of_mk_eq _ _ ((mk_homOfTotal_comp _ _ _ _).trans (by
        rw [ActionCategory.comp_hom, hmul _ a.back.2.1]
        exact compTotal_congr (Prod.ext rfl
          (congrArg (σ g.hom) (congrArg Subtype.val f.map_val).symm)))) }
  have hF {a b : ActionCategory (Aut x) U} (f : a ⟶ b) :
      (⟨_, _, F.map f⟩ : Quiver.Total C) = σ f.hom a.back :=
    mk_homOfTotal _ (hσ _ _ (hUT _ a.back.2 _)).2 (congrArg Subtype.val f.map_val)
  refine ⟨U, inst, F, hUo, hxU, fun g ↦ ((hact g).comp_continuous continuous_subtype_val
    fun y ↦ hUT _ y.2 g).subtype_mk _, fun _ ↦ rfl, ?_, ?_, fun g ↦ ?_,
    fun hx g ↦ (hF _).trans ?_⟩
  · -- Every arrow between objects of `U` lies in the bisection of a unique isotropy arrow.
    refine ⟨fun {a b} φ ↦ ?_⟩
    obtain ⟨f, hf, -⟩ := hcover ⟨_, _, φ⟩ (a.back.2.1 |> hVE |>.1) (b.back.2.1 |> hVE |>.1)
    let g : Aut x := .of ((Groupoid.isoEquivHom x x).symm f)
    have hg : σ g a.back = ⟨_, _, φ⟩ :=
      huniq f (hσ g _ (hUT _ a.back.2 g)).1 hf (hσ g _ (hUT _ a.back.2 g)).2
    let m : a ⟶ b :=
      Functor.Elements.homMk g (Subtype.ext ((congrArg Quiver.Total.right hg).trans rfl))
    exact ⟨m, eq_of_heq (Quiver.Total.mk.inj ((hF m).trans hg)).2.2⟩
  · refine ⟨fun {a b} f f' h ↦ Functor.Elements.hom_ext ?_⟩
    have hσf : σ f.hom a.back = σ f'.hom a.back :=
      (hF f).symm.trans ((congrArg (fun φ ↦ (⟨_, _, φ⟩ : Quiver.Total C)) h).trans (hF f'))
    by_contra hne
    have hne' : f.hom.asIso.hom ≠ f'.hom.asIso.hom := fun h ↦ hne (Aut.ext (Iso.ext h))
    exact Set.disjoint_left.mp (hdisj hne') (hσ _ _ (hUT _ a.back.2 _)).1
      (hσf ▸ (hσ _ _ (hUT _ a.back.2 _)).1)
  · have hfun : (fun y : U ↦ (⟨_, _, F.map ((ActionCategory.totalEquiv (Aut x) U).symm
        (g, y)).hom⟩ : Quiver.Total C)) = fun y : U ↦ σ g y := by
      funext y
      rw [hF, ActionCategory.totalEquiv_symm_apply_hom_hom,
        ActionCategory.totalEquiv_symm_apply_left]
      -- The underlying point of the object `objEquiv y` is `y` by definition.
      rfl
    rw [hfun]
    exact isOpenEmbedding_restrict_section (hW _).1 hs.continuous
      (fun b hb b' hb' ↦ huniq _ hb hb') hUo ((hσc g).mono fun y hy ↦ hUT y hy g)
      fun y hy ↦ hσ g y (hUT y hy g)
  · simp only [ActionCategory.totalEquiv_symm_apply_hom_hom,
      ActionCategory.totalEquiv_symm_apply_left]
    exact hσx g

end Groupoid

end TauCeti
