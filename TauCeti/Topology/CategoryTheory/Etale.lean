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
public import TauCeti.CategoryTheory.Groupoid.ActionCategory.Basic
public import TauCeti.Topology.CategoryTheory.QuiverTotal
public import TauCeti.Topology.IsLocalHomeomorph
public import TauCeti.Topology.OpenPartialHomeomorph.Constructions

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

For a category with continuous units, the identity arrows are open when the source is a local
homeomorphism, as the image of a continuous section of the source (`TauCeti.isOpen_range_unit`),
and closed when the source is continuous and the arrow space Hausdorff, as a retract of the arrow
space (`TauCeti.isClosed_range_unit`). So they are clopen in an étale category with Hausdorff
arrow space (`TauCeti.isClopen_range_unit`).

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
  exact hs.isLocallyInjective.finite_preimage_singleton_inter (s := Quiver.Total.right ⁻¹' {y}) hc

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

end Quiver

open CategoryTheory

section Category

variable {C : Type*} [Category C] [TopologicalSpace C] [TopologicalSpace (Quiver.Total C)]
  (hu : Continuous fun x : C ↦ (⟨x, x, 𝟙 x⟩ : Quiver.Total C))
include hu

/-- In a topological category with continuous units and locally homeomorphic source, the identity
arrows form an open set: they are the image of a continuous section of the source. -/
theorem isOpen_range_unit (hs : IsLocalHomeomorph (Quiver.Total.left : Quiver.Total C → C)) :
    IsOpen (Set.range fun x : C ↦ (⟨x, x, 𝟙 x⟩ : Quiver.Total C)) :=
  (hs.isOpenEmbedding_of_comp (f := fun x : C ↦ (⟨x, x, 𝟙 x⟩ : Quiver.Total C))
    IsOpenEmbedding.id hu).isOpen_range

/-- In a topological category with continuous units, continuous source and Hausdorff arrow
space, the identity arrows form a closed set: they are a retract of the arrow space. -/
theorem isClosed_range_unit [T2Space (Quiver.Total C)]
    (hl : Continuous (Quiver.Total.left : Quiver.Total C → C)) :
    IsClosed (Set.range fun x : C ↦ (⟨x, x, 𝟙 x⟩ : Quiver.Total C)) :=
  Function.LeftInverse.isClosed_range (f := Quiver.Total.left) (fun _ ↦ rfl) hl hu

variable [T2Space (Quiver.Total C)]
  (hs : IsLocalHomeomorph (Quiver.Total.left : Quiver.Total C → C))
include hs

/-- In a topological category with continuous units, locally homeomorphic source and Hausdorff
arrow space, the identity arrows form a clopen set. -/
theorem isClopen_range_unit : IsClopen (Set.range fun x : C ↦ (⟨x, x, 𝟙 x⟩ : Quiver.Total C)) :=
  ⟨isClosed_range_unit hu hs.continuous, isOpen_range_unit hu hs⟩

end Category

section Groupoid

variable {C : Type*} [Groupoid C]

/-- Fullness of the local isotropy action: if the bisection `W f` of each isotropy arrow `f` is
injective under the source, and `σ g y` is the arrow of `W g` with source `y`, then every arrow
from `y` lying in some bisection is `σ g y` for some `g`. -/
private theorem exists_section_eq {x y : C} {W : (x ⟶ x) → Set (Quiver.Total C)}
    (hinj : ∀ f, InjOn Quiver.Total.left (W f)) {σ : Aut x → C → Quiver.Total C}
    (hσW : ∀ g : Aut x, σ g y ∈ W g.asIso.hom) (hσl : ∀ g : Aut x, (σ g y).left = y)
    {a : Quiver.Total C} (ha : ∃ f, a ∈ W f) (hay : a.left = y) : ∃ g, σ g y = a := by
  obtain ⟨f, hf⟩ := ha
  let g : Aut x := .of ((Groupoid.isoEquivHom x x).symm f)
  exact ⟨g, hinj f (hσW g) hf ((hσl g).trans hay.symm)⟩

/-- Faithfulness of the local isotropy action: sections through pairwise disjoint bisections
take different values at every point where both are defined. -/
private theorem eq_of_section_eq {x y : C} {W : (x ⟶ x) → Set (Quiver.Total C)}
    (hdisj : Pairwise fun f g ↦ Disjoint (W f) (W g)) {σ : Aut x → C → Quiver.Total C}
    {g g' : Aut x} (hg : σ g y ∈ W g.asIso.hom) (hg' : σ g' y ∈ W g'.asIso.hom)
    (h : σ g y = σ g' y) : g = g' := by
  by_contra hne
  exact Set.disjoint_left.mp (hdisj fun h ↦ hne (Aut.ext (Iso.ext h))) hg (h ▸ hg')

variable [TopologicalSpace C] [TopologicalSpace (Quiver.Total C)]

/-- Near `x`, sections `σ g` of the source through the bisections of the isotropy arrows compose
like the isotropy group: `σ 1` is the unit section and `σ (g * h)` is the composite of `σ h`
followed by `σ g`. -/
private theorem exists_nhds_section_one_mul {x : C} [Finite (Aut x)]
    {W : (x ⟶ x) → Set (Quiver.Total C)}
    (hu : Continuous fun y : C ↦ (⟨y, y, 𝟙 y⟩ : Quiver.Total C))
    (hc : Continuous fun p : {p : Quiver.Total C × Quiver.Total C // p.1.right = p.2.left} ↦
      p.1.1.comp p.1.2 p.2)
    (ht : Continuous (Quiver.Total.right : Quiver.Total C → C)) (hWo : ∀ f, IsOpen (W f))
    (hWx : ∀ f, (⟨x, x, f⟩ : Quiver.Total C) ∈ W f) (hinj : ∀ f, InjOn Quiver.Total.left (W f))
    {σ : Aut x → C → Quiver.Total C} {T : Aut x → Set C} (hT : ∀ g, IsOpen (T g))
    (hxT : ∀ g, x ∈ T g) (hσc : ∀ g, ContinuousOn (σ g) (T g))
    (hσW : ∀ g, ∀ y ∈ T g, σ g y ∈ W g.asIso.hom) (hσl : ∀ g, ∀ y ∈ T g, (σ g y).left = y)
    (hσx : ∀ g, σ g x = ⟨x, x, g.asIso.hom⟩) :
    ∀ᶠ y in 𝓝 x, (∀ g, y ∈ T g) ∧ (∀ g h, (σ h y).right ∈ T g) ∧ σ 1 y = ⟨y, y, 𝟙 y⟩ ∧
      ∀ g h, ∃ hgh, σ (g * h) y = (σ h y).comp (σ g (σ h y).right) hgh := by
  have hσxr (g : Aut x) : (σ g x).right = x := by rw [hσx g]
  have hact (h : Aut x) : ContinuousOn (fun y ↦ (σ h y).right) (T h) :=
    ht.comp_continuousOn (hσc h)
  have hT' : ∀ᶠ y in 𝓝 x, ∀ g, y ∈ T g := Filter.eventually_all.2 fun g ↦
    (hT g).eventually_mem (hxT g)
  have hTT : ∀ᶠ y in 𝓝 x, ∀ g h, (σ h y).right ∈ T g :=
    Filter.eventually_all.2 fun g ↦ Filter.eventually_all.2 fun h ↦
      ((hact h).continuousAt ((hT h).mem_nhds (hxT h))).eventually_mem
        ((hT g).mem_nhds (by rw [hσxr]; exact hxT g))
  have hunit : ∀ᶠ y in 𝓝 x, (⟨y, y, 𝟙 y⟩ : Quiver.Total C) ∈ W (1 : Aut x).asIso.hom :=
    hu.continuousAt.eventually_mem ((hWo _).mem_nhds (hWx _))
  have hcomp : ∀ᶠ y in 𝓝 x, ∀ g h (hgh : (σ h y).right = (σ g (σ h y).right).left),
      (σ h y).comp (σ g (σ h y).right) hgh ∈ W (g * h).asIso.hom := by
    refine Filter.eventually_all.2 fun g ↦ Filter.eventually_all.2 fun h ↦ ?_
    refine eventually_comp_mem hc ht (hσc h) (hσc g) (hT h) (hT g) (hσl g) (hxT h)
      (by rw [hσxr]; exact hxT g) (hWo _) fun hgh ↦ ?_
    -- At `x` the two sections pass through `h` and `g`, which compose to `g * h`.
    have hgx : σ g (σ h x).right = ⟨x, x, g.asIso.hom⟩ := by rw [hσxr]; exact hσx g
    rw [Quiver.Total.comp_congr (hσx h) hgx hgh rfl, Quiver.Total.mk_comp_mk]
    exact hWx _
  filter_upwards [hT', hTT, hunit, hcomp] with y hyT hyTT hyunit hycomp
  exact ⟨hyT, hyTT, hinj _ (hσW 1 y (hyT 1)) hyunit (hσl 1 y (hyT 1)), fun g h ↦
    ⟨(hσl g _ (hyTT g h)).symm, hinj _ (hσW _ y (hyT _)) (hycomp g h _)
      ((hσl _ y (hyT _)).trans ((Quiver.Total.comp_left _ _ _).trans (hσl h y (hyT h))).symm)⟩⟩

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
      p.1.1.comp p.1.2 p.2)
    (x : C) :
    ∃ (U : Set C) (hxU : x ∈ U) (_ : MulAction (Aut x) U) (F : ActionCategory (Aut x) U ⥤ C),
      IsOpen U ∧ (∀ g : Aut x, Continuous fun y : U ↦ g • y) ∧
      (∀ a, F.obj a = (a.back : C)) ∧ F.Full ∧ F.Faithful ∧
      (∀ g : Aut x, IsOpenEmbedding fun y : U ↦
        (⟨_, _, F.map ((ActionCategory.totalEquiv (Aut x) U).symm (g, y)).hom⟩ :
          Quiver.Total C)) ∧
      ∀ g : Aut x,
        (⟨_, _, F.map ((ActionCategory.totalEquiv (Aut x) U).symm (g, ⟨x, hxU⟩)).hom⟩ :
          Quiver.Total C) = ⟨x, x, g.asIso.hom⟩ := by
  -- Outline: take the disjoint bisections `W g` through the isotropy arrows and the inverses
  -- `σ g` of the source on them. Near `x` these compose like `Aut x`. An invariant shrinking `U`
  -- of that neighbourhood carries the action `g • y = (σ g y).right`, and `σ` gives the functor.
  obtain ⟨U₀, W, hU₀, hxU₀, hW, hdisj, hcover⟩ :=
    exists_disjoint_bisections_of_proper_source_target hp hs ht x
  choose hWo hWx hWl _ using hW
  have := finite_hom_of_proper_source_target hp hs x x
  have : Finite (Aut x) := .of_equiv _ (Aut.isoEquiv.trans (Groupoid.isoEquivHom x x)).symm
  have hinj (f : x ⟶ x) : InjOn Quiver.Total.left (W f) := fun b hb b' hb' h ↦
    congrArg Subtype.val (@(hWl f).injective ⟨b, hb⟩ ⟨b', hb'⟩ h)
  -- The source restricted to the bisection of each isotropy arrow `g` is a chart `e g`.
  choose e hes hel using fun g : Aut x ↦
    OpenPartialHomeomorph.exists_source_eq_of_isOpenEmbedding (hWo _) (hWl _) ⟨_, hWx g.asIso.hom⟩
  let σ (g : Aut x) : C → Quiver.Total C := (e g).symm
  let T (g : Aut x) : Set C := (e g).target
  have hσW (g : Aut x) (y : C) (hy : y ∈ T g) : σ g y ∈ W g.asIso.hom :=
    hes g ▸ (e g).map_target hy
  have hσl (g : Aut x) (y : C) (hy : y ∈ T g) : (σ g y).left = y :=
    (hel g ⟨_, hσW g y hy⟩).symm.trans ((e g).right_inv hy)
  have hex (g : Aut x) : e g ⟨x, x, g.asIso.hom⟩ = x := hel g ⟨_, hWx _⟩
  have hxT (g : Aut x) : x ∈ T g := hex g ▸ (e g).map_source (hes g ▸ hWx _)
  have hσx (g : Aut x) : σ g x = ⟨x, x, g.asIso.hom⟩ := by
    have := (e g).left_inv (hes g ▸ hWx _)
    rwa [hex g] at this
  have hact (g : Aut x) : ContinuousOn (fun y ↦ (σ g y).right) (T g) :=
    ht.continuous.comp_continuousOn (e g).continuousOn_symm
  obtain ⟨V, hVE, hV, hxV⟩ := mem_nhds_iff.mp ((hU₀.eventually_mem hxU₀).and
    (exists_nhds_section_one_mul (σ := σ) (T := T) hu hc ht.continuous hWo hWx hinj
      (fun g ↦ (e g).open_target) hxT (fun g ↦ (e g).continuousOn_symm) hσW hσl hσx))
  simp only [Set.subset_ofPred, forall₂_and] at hVE
  obtain ⟨hVU₀, hVT, hVTT, hone, hmul⟩ := hVE
  choose _ hmul using hmul
  -- Shrink `V` to the neighbourhood `U` which the local action preserves.
  set U : Set C := V ∩ ⋂ g, T g ∩ (fun y ↦ (σ g y).right) ⁻¹' V
  have hUo : IsOpen U :=
    hV.inter (isOpen_iInter_of_finite fun g ↦ (hact g).isOpen_inter_preimage (e g).open_target hV)
  have hxU : x ∈ U := ⟨hxV, Set.mem_iInter.2 fun g ↦ ⟨hxT g, by
    simp only [Set.mem_preimage, hσx]; exact hxV⟩⟩
  have hUT (y : C) (hy : y ∈ U) (g : Aut x) : y ∈ T g := (Set.mem_iInter.1 hy.2 g).1
  have hUσ (y : C) (hy : y ∈ U) (h : Aut x) : (σ h y).right ∈ U := by
    refine ⟨(Set.mem_iInter.1 hy.2 h).2, Set.mem_iInter.2 fun g ↦ ⟨hVTT y hy.1 g h, ?_⟩⟩
    have := (Set.mem_iInter.1 hy.2 (g * h)).2
    rwa [Set.mem_preimage, hmul y hy.1, Quiver.Total.comp_right] at this
  let inst : MulAction (Aut x) U :=
    { smul g y := ⟨(σ g y).right, hUσ y y.2 g⟩
      one_smul y := Subtype.ext ((congrArg Quiver.Total.right (hone y y.2.1)).trans rfl)
      mul_smul g h y :=
        Subtype.ext ((congrArg Quiver.Total.right (hmul y y.2.1 g h)).trans
          (Quiver.Total.comp_right _ _ _)) }
  let F : ActionCategory (Aut x) U ⥤ C :=
    { obj a := a.back
      map {a b} f := Quiver.homOfEq (σ f.hom a.back).hom (hσl _ _ (hUT _ a.back.2 _))
        (congrArg Subtype.val f.map_val)
      map_id a := eq_of_heq (Quiver.Total.mk.inj ((Quiver.Total.mk_homOfEq _ _ _).trans (by
        rw [ActionCategory.id_hom]
        exact hone _ a.back.2.1))).2.2
      map_comp {a b c} f g := eq_of_heq (Quiver.Total.mk.inj
        ((Quiver.Total.mk_homOfEq _ _ _).trans <| Eq.trans (by
          rw [ActionCategory.comp_hom, hmul _ a.back.2.1]
          exact Quiver.Total.comp_congr rfl
            (congrArg (σ g.hom) (congrArg Subtype.val f.map_val)) _ _)
          (Quiver.Total.mk_homOfEq_comp_homOfEq _ _ _ _ _ _).symm)).2.2 }
  have hF {a b : ActionCategory (Aut x) U} (f : a ⟶ b) :
      (⟨_, _, F.map f⟩ : Quiver.Total C) = σ f.hom a.back :=
    Quiver.Total.mk_homOfEq _ _ _
  -- `back` is the inverse of `objEquiv`, which the arrow coordinates `totalEquiv` use.
  have hback (y : U) : (ActionCategory.objEquiv (Aut x) U y).back = y :=
    (ActionCategory.objEquiv (Aut x) U).left_inv y
  refine ⟨U, hxU, inst, F, hUo, fun g ↦ ((hact g).comp_continuous continuous_subtype_val
    fun y ↦ hUT _ y.2 g).subtype_mk _, fun _ ↦ rfl, ?_, ?_, fun g ↦ ?_,
    fun g ↦ (hF _).trans ?_⟩
  · -- Every arrow between objects of `U` lies in a bisection, so it is the arrow of some label.
    refine ⟨fun {a b} φ ↦ ?_⟩
    obtain ⟨g, hg⟩ := exists_section_eq hinj (fun g ↦ hσW g _ (hUT _ a.back.2 g))
      (fun g ↦ hσl g _ (hUT _ a.back.2 g))
      (hcover ⟨_, _, φ⟩ (hVU₀ _ a.back.2.1) (hVU₀ _ b.back.2.1)).exists rfl
    let m : a ⟶ b :=
      Functor.Elements.homMk g (Subtype.ext ((congrArg Quiver.Total.right hg).trans rfl))
    exact ⟨m, eq_of_heq (Quiver.Total.mk.inj ((hF m).trans hg)).2.2⟩
  · refine ⟨fun {a b} f f' h ↦ Functor.Elements.hom_ext ?_⟩
    exact eq_of_section_eq hdisj (hσW _ _ (hUT _ a.back.2 _)) (hσW _ _ (hUT _ a.back.2 _))
      ((hF f).symm.trans ((congrArg (fun φ ↦ (⟨_, _, φ⟩ : Quiver.Total C)) h).trans (hF f')))
  · have hfun : (fun y : U ↦ (⟨_, _, F.map ((ActionCategory.totalEquiv (Aut x) U).symm
        (g, y)).hom⟩ : Quiver.Total C)) = fun y : U ↦ σ g y := by
      funext y
      rw [hF, ActionCategory.totalEquiv_symm_apply_hom_hom,
        ActionCategory.totalEquiv_symm_apply_left, hback]
    rw [hfun]
    exact (e g).symm.isOpenEmbedding_restrict.comp
      (.inclusion (fun y hy ↦ hUT y hy g) (hUo.preimage continuous_subtype_val))
  · rw [ActionCategory.totalEquiv_symm_apply_hom_hom, ActionCategory.totalEquiv_symm_apply_left,
      hback]
    exact hσx g

end Groupoid

end TauCeti
