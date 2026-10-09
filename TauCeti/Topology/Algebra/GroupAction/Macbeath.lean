/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.GroupTheory.PresentedGroup
public import Mathlib.Topology.Algebra.ConstMulAction
public import Mathlib.AlgebraicTopology.FundamentalGroupoid.SimplyConnected
import TauCeti.Topology.Homotopy.Covering

/-!
# Macbeath's presentation of a group acting on a simply connected space

Let a group `G` act by homeomorphisms on a space `X`, and let `U ⊆ X` be an open set whose
translates cover `X`. The elements `g` for which `g • U` meets `U` are the *Macbeath generators*
of `U`. For two such generators `s` and `t`, the product `s * t` is again one whenever the
three sets `U`, `s • U` and `(s * t) • U` have a common point, and the *Macbeath relations* are
the words `s t (s t)⁻¹` for all such triples.

Macbeath's theorem says that these generators and relations present `G` as soon as `X` is
simply connected and `U` is path-connected:

* if `X` is connected, the Macbeath generators generate `G`: the translates of `U` by the
  generated subgroup and by its complement are disjoint open sets covering `X`;
* if `X` is simply connected and `U` is path-connected, every relation among the generators is
  a consequence of the Macbeath relations.

For the second statement, let `Γ` be the presented group. Glue copies `{a} × U`, for `a : Γ`,
by identifying `(a * s, v)` with `(a, s • v)` whenever both points of `U` are defined. The
resulting space maps to `X` by `(a, v) ↦ a • v`. Over a translate `g • U`, it is the disjoint
union of the copies indexed by the preimages of `g` in `Γ`, so the map is a covering map. The
glued space is path-connected because `U` is path-connected and consecutive copies along a
generator overlap. A covering map from a path-connected space onto a simply connected space is
injective, and hence so is `Γ → G`.

The intended application is to a Fuchsian group acting on the upper half-plane, with `U` a
neighbourhood of a fundamental polygon: it turns the tiling by the polygon into a presentation of
the group.

## Main definitions

* `TauCeti.macbeathGenerators G U`: the elements `g : G` with `U ∩ g • U` nonempty.
* `TauCeti.macbeathRels G U`: the Macbeath relations, words in the free group on the generators.
* `TauCeti.macbeathHom G U`: the evaluation homomorphism from the presented group to `G`.
* `TauCeti.macbeathEquiv`: **Macbeath's theorem**, the presentation of `G`, as an isomorphism.

## Main results

* `TauCeti.macbeathHom_surjective`: the Macbeath generators of an open set whose translates
  cover a connected space generate the group.
* `TauCeti.macbeathHom_injective`: if moreover the space is simply connected and the set is
  path-connected, the Macbeath relations are a complete set of relations.
* `TauCeti.ker_lift_eq_normalClosure_macbeathRels`: the same statement as an equality of
  subgroups of the free group: the kernel of evaluation is the normal closure of the Macbeath
  relations.

## References

* A. M. Macbeath, *Groups of homeomorphisms of a simply connected space*, Ann. of Math. (2) 79
  (1964), 473–488.
-/

public section

namespace TauCeti

open Set Function Topology
open scoped Pointwise

variable (G : Type*) {X : Type*} [Group G] [MulAction G X]

/-- The **Macbeath generators** of a set `U`: the elements `g` whose translate `g • U` meets
`U`. -/
def macbeathGenerators (U : Set X) : Set G :=
  {g | (U ∩ g • U).Nonempty}

/-- The **Macbeath relations** of a set `U`: the words `s t u⁻¹` in its Macbeath generators for
which `u = s * t` and the three sets `U`, `s • U` and `u • U` have a common point. -/
def macbeathRels (U : Set X) : Set (FreeGroup (macbeathGenerators G U)) :=
  {r | ∃ s t u : macbeathGenerators G U, (u : G) = s * t ∧
    (U ∩ (s : G) • U ∩ (u : G) • U).Nonempty ∧
    r = FreeGroup.of s * FreeGroup.of t * (FreeGroup.of u)⁻¹}

/-- The evaluation of the group presented by the Macbeath generators and relations of `U`,
sending each generator to itself. -/
def macbeathHom (U : Set X) : PresentedGroup (macbeathRels G U) →* G :=
  PresentedGroup.toGroup (f := Subtype.val) <| by
    rintro _ ⟨s, t, u, hu, -, rfl⟩
    simp [hu]

variable {G}

@[simp]
theorem mem_macbeathGenerators {U : Set X} {g : G} :
    g ∈ macbeathGenerators G U ↔ (U ∩ g • U).Nonempty :=
  Iff.rfl

@[simp]
theorem mem_macbeathRels {U : Set X} {r : FreeGroup (macbeathGenerators G U)} :
    r ∈ macbeathRels G U ↔ ∃ s t u : macbeathGenerators G U, (u : G) = s * t ∧
      (U ∩ (s : G) • U ∩ (u : G) • U).Nonempty ∧
      r = FreeGroup.of s * FreeGroup.of t * (FreeGroup.of u)⁻¹ :=
  Iff.rfl

@[simp]
theorem macbeathHom_of (U : Set X) (s : macbeathGenerators G U) :
    macbeathHom G U (PresentedGroup.of s) = s :=
  PresentedGroup.toGroup.of _

variable {U : Set X}

theorem one_mem_macbeathGenerators (hU : U.Nonempty) : (1 : G) ∈ macbeathGenerators G U := by
  simpa using hU

theorem inv_mem_macbeathGenerators {g : G} (hg : g ∈ macbeathGenerators G U) :
    g⁻¹ ∈ macbeathGenerators G U := by
  obtain ⟨x, hxU, hxg⟩ := hg
  obtain ⟨y, hyU, rfl⟩ := mem_smul_set.1 hxg
  exact ⟨y, hyU, mem_inv_smul_set_iff.2 hxU⟩

/-- The defining relation of the presented group: `s * t = u` for Macbeath generators with
`u = s * t` as soon as `U`, `s • U` and `u • U` have a common point. -/
theorem macbeath_of_mul_of {s t u : macbeathGenerators G U} (hu : (u : G) = s * t)
    (h : (U ∩ (s : G) • U ∩ (u : G) • U).Nonempty) :
    (PresentedGroup.of s * PresentedGroup.of t : PresentedGroup (macbeathRels G U)) =
      PresentedGroup.of u := by
  have := PresentedGroup.one_of_mem (rels := macbeathRels G U)
    (x := FreeGroup.of s * FreeGroup.of t * (FreeGroup.of u)⁻¹) ⟨s, t, u, hu, h, rfl⟩
  rwa [map_mul, map_inv, mul_inv_eq_one] at this

/-- The Macbeath generator `1` is the identity of the presented group. -/
theorem macbeath_of_eq_one {s : macbeathGenerators G U} (hs : (s : G) = 1) :
    (PresentedGroup.of s : PresentedGroup (macbeathRels G U)) = 1 := by
  have h := macbeath_of_mul_of (s := s) (t := s) (u := s) (by rw [hs, mul_one])
    (by simpa [hs] using s.2)
  simpa using h

/-- The Macbeath generator `s⁻¹` is the inverse of the generator `s` in the presented group. -/
@[simp]
theorem macbeath_of_inv (s : macbeathGenerators G U) :
    (PresentedGroup.of ⟨(s : G)⁻¹, inv_mem_macbeathGenerators s.2⟩ :
      PresentedGroup (macbeathRels G U)) = (PresentedGroup.of s)⁻¹ := by
  rw [eq_inv_iff_mul_eq_one, macbeath_of_mul_of (u := ⟨1, ?_⟩) (inv_mul_cancel _).symm ?_,
    macbeath_of_eq_one rfl]
  · exact one_mem_macbeathGenerators (s.2.mono inter_subset_left)
  · obtain ⟨x, hx⟩ := inv_mem_macbeathGenerators s.2
    exact ⟨x, hx, by simpa using hx.1⟩

/-- If a translate of `U` by an element of the image of `macbeathHom` meets the translate by
`g`, then `g` also lies in that image. -/
private theorem mem_range_macbeathHom_of_nonempty {h g : G} (hh : h ∈ (macbeathHom G U).range)
    (hg : (h • U ∩ g • U).Nonempty) : g ∈ (macbeathHom G U).range := by
  obtain ⟨x, hxh, hxg⟩ := hg
  have hs : h⁻¹ * g ∈ macbeathGenerators G U :=
    ⟨h⁻¹ • x, mem_smul_set_iff_inv_smul_mem.1 hxh, by
      rw [mul_smul]; exact smul_mem_smul_set hxg⟩
  simpa using (macbeathHom G U).range.mul_mem hh ⟨PresentedGroup.of ⟨_, hs⟩, macbeathHom_of _ _⟩

/-! ### The space glued from copies of `U` -/

variable (G U) in
/-- The gluing relation on `Σ a, U` identifying `(a, s • v)` with `(a * s, v)`. -/
private def macbeathSetoid : Setoid (Σ _ : PresentedGroup (macbeathRels G U), U) where
  r y z := ∃ s : macbeathGenerators G U,
    z.1 = y.1 * PresentedGroup.of s ∧ (y.2 : X) = (s : G) • (z.2 : X)
  iseqv :=
    { refl y := ⟨⟨1, one_mem_macbeathGenerators ⟨_, y.2.2⟩⟩,
        by rw [macbeath_of_eq_one rfl, mul_one], (one_smul _ _).symm⟩
      symm := by
        rintro y z ⟨s, h₁, h₂⟩
        refine ⟨⟨_, inv_mem_macbeathGenerators s.2⟩, ?_, by simp [h₂]⟩
        rw [macbeath_of_inv, h₁, mul_inv_cancel_right]
      trans := by
        rintro x y z ⟨s, h₁, h₂⟩ ⟨t, h₃, h₄⟩
        have hst : (U ∩ (s : G) • U ∩ ((s : G) * t) • U).Nonempty := by
          refine ⟨x.2, ⟨x.2.2, ?_⟩, ?_⟩
          · rw [h₂]; exact smul_mem_smul_set y.2.2
          · rw [h₂, h₄, mul_smul]; exact smul_mem_smul_set (smul_mem_smul_set z.2.2)
        have hmem : (s : G) * t ∈ macbeathGenerators G U := hst.mono fun w hw ↦ ⟨hw.1.1, hw.2⟩
        refine ⟨⟨_, hmem⟩, ?_, by simp [h₂, h₄, mul_smul]⟩
        rw [h₃, h₁, mul_assoc, macbeath_of_mul_of (u := ⟨_, hmem⟩) rfl hst] }

/-- The copy of `U` indexed by `a` in the glued space. -/
private def macbeathSheet (a : PresentedGroup (macbeathRels G U)) (v : U) :
    Quotient (macbeathSetoid G U) :=
  Quotient.mk _ ⟨a, v⟩

private theorem macbeathSheet_eq_iff {a b : PresentedGroup (macbeathRels G U)} {v w : U} :
    macbeathSheet a v = macbeathSheet b w ↔
      ∃ s : macbeathGenerators G U, b = a * PresentedGroup.of s ∧ (v : X) = (s : G) • (w : X) :=
  Quotient.eq

variable (G U) in
/-- The projection of the glued space to `X`, sending `(a, v)` to `a • v`. -/
private def macbeathProj : Quotient (macbeathSetoid G U) → X :=
  Quotient.lift (fun y ↦ macbeathHom G U y.1 • (y.2 : X)) <| by
    rintro y z ⟨s, h₁, h₂⟩
    simp [h₁, h₂, mul_smul]

private theorem macbeathProj_sheet (a : PresentedGroup (macbeathRels G U)) (v : U) :
    macbeathProj G U (macbeathSheet a v) = macbeathHom G U a • (v : X) :=
  rfl

variable [TopologicalSpace X]

private theorem continuous_macbeathSheet (a : PresentedGroup (macbeathRels G U)) :
    Continuous (macbeathSheet a) :=
  continuous_quotient_mk'.comp continuous_sigmaMk

/-- The glued space is path-connected: each copy of `U` is, and the copies indexed by `a` and
`a * s` overlap for every Macbeath generator `s`. -/
private theorem pathConnectedSpace_macbeath (hUc : IsPathConnected U) :
    PathConnectedSpace (Quotient (macbeathSetoid G U)) := by
  obtain ⟨u₀, hu₀⟩ := hUc.nonempty
  have : PathConnectedSpace U := isPathConnected_iff_pathConnectedSpace.1 hUc
  set y₀ := macbeathSheet (1 : PresentedGroup (macbeathRels G U)) ⟨u₀, hu₀⟩
  -- a copy of `U` with one point in the path component of `y₀` lies in it entirely
  have hsheet (a : PresentedGroup (macbeathRels G U)) (v : U)
      (hv : macbeathSheet a v ∈ pathComponent y₀) :
      range (macbeathSheet a) ⊆ pathComponent y₀ := by
    rw [← pathComponent_congr hv]
    exact (isPathConnected_range (continuous_macbeathSheet a)).subset_pathComponent
      (mem_range_self v)
  have hstep (a : PresentedGroup (macbeathRels G U)) (s : macbeathGenerators G U)
      (ha : range (macbeathSheet a) ⊆ pathComponent y₀) :
      range (macbeathSheet (a * PresentedGroup.of s)) ⊆ pathComponent y₀ := by
    obtain ⟨x, hxU, hxs⟩ := s.2
    obtain ⟨v, hv, rfl⟩ := mem_smul_set.1 hxs
    refine hsheet _ ⟨v, hv⟩ ?_
    rw [← (macbeathSheet_eq_iff (a := a) (v := ⟨_, hxU⟩)).2 ⟨s, rfl, rfl⟩]
    exact ha (mem_range_self _)
  have hall (a : PresentedGroup (macbeathRels G U)) :
      range (macbeathSheet a) ⊆ pathComponent y₀ := by
    have ha : a ∈ Subgroup.closure (range PresentedGroup.of) := by
      rw [PresentedGroup.closure_range_of]
      exact Subgroup.mem_top a
    induction ha using Subgroup.closure_induction_right with
    | one => exact hsheet 1 ⟨u₀, hu₀⟩ (mem_pathComponent_self _)
    | mul_right x _ y hy ih =>
      obtain ⟨s, rfl⟩ := hy
      exact hstep x s ih
    | mul_inv_cancel x _ y hy ih =>
      obtain ⟨s, rfl⟩ := hy
      rw [← macbeath_of_inv]
      exact hstep x _ ih
  refine pathConnectedSpace_iff_eq.2 ⟨y₀, eq_univ_of_forall fun y ↦ ?_⟩
  obtain ⟨⟨a, v⟩, rfl⟩ := Quotient.exists_rep y
  exact hall a (mem_range_self v)

variable [ContinuousConstSMul G X]

/-- **The Macbeath generators generate the group.** If the translates of an open set `U` cover a
connected space, then the elements `g` with `g • U` meeting `U` generate `G`. -/
theorem macbeathHom_surjective [ConnectedSpace X] (hUo : IsOpen U)
    (hcover : ⋃ g : G, g • U = univ) : Surjective (macbeathHom G U) := by
  obtain ⟨g₀, hg₀⟩ := mem_iUnion.1 (hcover ▸ mem_univ (Classical.arbitrary X))
  have hU : U.Nonempty := (smul_set_nonempty.1 ⟨_, hg₀⟩)
  -- the translates of `U` by the image of `macbeathHom` form a clopen set
  set A := ⋃ h ∈ (macbeathHom G U).range, h • U
  have hAo : IsOpen A := isOpen_biUnion fun h _ ↦ hUo.smul h
  have hAc : IsOpen Aᶜ := isOpen_iff_forall_mem_open.2 fun x hx ↦ by
    obtain ⟨g, hg⟩ := mem_iUnion.1 (hcover ▸ mem_univ x)
    refine ⟨g • U, fun y hy hyA ↦ hx ?_, hUo.smul g, hg⟩
    obtain ⟨h, hh, hyh⟩ := mem_iUnion₂.1 hyA
    exact mem_iUnion₂.2 ⟨g, mem_range_macbeathHom_of_nonempty hh ⟨y, hyh, hy⟩, hg⟩
  have hA : A = univ := IsClopen.eq_univ ⟨isOpen_compl_iff.1 hAc, hAo⟩
    (hU.smul_set.mono (subset_biUnion_of_mem (u := fun h : G ↦ h • U) (one_mem _)))
  intro g
  obtain ⟨x, hx⟩ := hU.smul_set (a := g)
  obtain ⟨h, hh, hxh⟩ := mem_iUnion₂.1 (hA ▸ mem_univ x)
  exact mem_range_macbeathHom_of_nonempty hh ⟨x, hxh, hx⟩

private theorem continuous_macbeathProj : Continuous (macbeathProj G U) :=
  Continuous.quotient_lift
    (f := fun y : Σ _ : PresentedGroup (macbeathRels G U), U ↦ macbeathHom G U y.1 • (y.2 : X))
    (continuous_sigma fun a ↦
      (continuous_const_smul (macbeathHom G U a)).comp continuous_subtype_val) _

private theorem isOpen_range_macbeathSheet (hUo : IsOpen U)
    (c : PresentedGroup (macbeathRels G U)) : IsOpen (range (macbeathSheet c)) := by
  rw [← (isQuotientMap_quotient_mk' (s := macbeathSetoid G U)).isOpen_preimage, isOpen_sigma_iff]
  intro b
  -- a point `(b, w)` lies in the copy indexed by `c` when `b = c * s` with `s • w ∈ U`
  have : Sigma.mk b ⁻¹' (@Quotient.mk' _ (macbeathSetoid G U) ⁻¹' range (macbeathSheet c)) =
      ⋃ s : {s : macbeathGenerators G U // b = c * PresentedGroup.of s},
        {w : U | ((s : macbeathGenerators G U) : G) • (w : X) ∈ U} := by
    ext w
    simp only [mem_preimage, mem_range, mem_iUnion, mem_ofPred_eq]
    constructor
    · rintro ⟨v, hv⟩
      obtain ⟨s, h₁, h₂⟩ := (macbeathSheet_eq_iff (b := b) (w := w)).1 hv
      exact ⟨⟨s, h₁⟩, h₂ ▸ v.2⟩
    · rintro ⟨⟨s, h₁⟩, hw⟩
      exact ⟨⟨_, hw⟩, (macbeathSheet_eq_iff (b := b) (w := w)).2 ⟨s, h₁, rfl⟩⟩
  rw [this]
  exact isOpen_iUnion fun _ ↦ hUo.preimage ((continuous_const_smul _).comp continuous_subtype_val)

/-- Over each translate `g • U`, the glued space is the disjoint union of the copies of `U`
indexed by the preimages of `g`; hence its projection to `X` is a covering map. -/
private theorem isCoveringMap_macbeathProj (hUo : IsOpen U)
    (hsurj : Surjective (macbeathHom G U)) (hcover : ⋃ g : G, g • U = univ) :
    IsCoveringMap (macbeathProj G U) := by
  let _ : TopologicalSpace (PresentedGroup (macbeathRels G U)) := ⊥
  have : DiscreteTopology (PresentedGroup (macbeathRels G U)) := ⟨rfl⟩
  intro x
  obtain ⟨g, hg⟩ := mem_iUnion.1 (hcover ▸ mem_univ x)
  obtain ⟨u₀, hu₀⟩ : U.Nonempty := smul_set_nonempty.1 ⟨x, hg⟩
  have : Nonempty (macbeathHom G U ⁻¹' {g}) :=
    let ⟨a, ha⟩ := hsurj g
    ⟨⟨a, ha⟩⟩
  have : Nonempty (X → Quotient (macbeathSetoid G U)) := ⟨fun _ ↦ macbeathSheet 1 ⟨u₀, hu₀⟩⟩
  refine IsEvenlyCovered.to_isEvenlyCovered_preimage (IsEvenlyCovered.of_trivialization
    (t := (hUo.smul g).trivializationDiscrete
      (fun c : macbeathHom G U ⁻¹' {g} ↦ range (macbeathSheet (c : PresentedGroup _)))
      (g • U) ?_ ?_ ?_ ?_ ?_) hg)
  · -- openness in `g • U` is detected on each sheet
    rintro ⟨c, hc⟩ W hW
    have hc : macbeathHom G U c = g := hc
    refine ⟨fun h ↦ (h.preimage continuous_macbeathProj).inter (isOpen_range_macbeathSheet hUo c),
      fun h ↦ ?_⟩
    have hO := h.preimage (continuous_macbeathSheet c)
    have hW' : W = g • ((↑) '' (macbeathSheet c ⁻¹'
        (macbeathProj G U ⁻¹' W ∩ range (macbeathSheet c)))) := by
      ext y
      constructor
      · intro hy
        obtain ⟨v, hv, rfl⟩ := mem_smul_set.1 (hW hy)
        refine smul_mem_smul_set ⟨⟨v, hv⟩, ⟨?_, mem_range_self _⟩, rfl⟩
        rwa [mem_preimage, macbeathProj_sheet, hc]
      · intro hy
        obtain ⟨_, ⟨v, ⟨hv, -⟩, rfl⟩, rfl⟩ := mem_smul_set.1 hy
        rwa [mem_preimage, macbeathProj_sheet, hc] at hv
    rw [hW']
    exact (hUo.isOpenMap_subtype_val _ hO).smul g
  · -- the projection is injective on each sheet
    rintro ⟨c, hc⟩ _ ⟨v, rfl⟩ _ ⟨w, rfl⟩ h
    rw [macbeathProj_sheet, macbeathProj_sheet, smul_left_cancel_iff] at h
    rw [Subtype.ext h]
  · -- each sheet maps onto `g • U`
    rintro ⟨c, hc⟩ y hy
    have hc : macbeathHom G U c = g := hc
    obtain ⟨v, hv, rfl⟩ := mem_smul_set.1 hy
    exact ⟨macbeathSheet c ⟨v, hv⟩, mem_range_self _, by rw [macbeathProj_sheet, hc]⟩
  · -- distinct sheets are disjoint
    rintro ⟨c, hc⟩ ⟨c', hc'⟩ hne
    have hc : macbeathHom G U c = g := hc
    have hc' : macbeathHom G U c' = g := hc'
    refine disjoint_left.2 ?_
    rintro _ ⟨v, rfl⟩ ⟨w, hw⟩
    obtain ⟨s, h₁, -⟩ := macbeathSheet_eq_iff.1 hw
    have hs : (s : G) = 1 := by simpa [hc, hc'] using congrArg (macbeathHom G U) h₁
    exact hne (Subtype.ext (by rw [h₁, macbeath_of_eq_one hs, mul_one]))
  · -- the sheets exhaust the preimage of `g • U`
    intro y hy
    obtain ⟨⟨b, w⟩, rfl⟩ := Quotient.exists_rep y
    have hv : g⁻¹ • macbeathHom G U b • (w : X) ∈ U := mem_smul_set_iff_inv_smul_mem.1 hy
    have ht : (macbeathHom G U b)⁻¹ * g ∈ macbeathGenerators G U :=
      ⟨w, w.2, mem_smul_set_iff_inv_smul_mem.2 (by simpa [mul_smul] using hv)⟩
    have hc : b * PresentedGroup.of ⟨_, ht⟩ ∈ macbeathHom G U ⁻¹' {g} := by simp
    refine mem_iUnion.2 ⟨⟨_, hc⟩, ⟨_, hv⟩, ((macbeathSheet_eq_iff (a := b)).2
      ⟨⟨_, ht⟩, rfl, by simp [mul_smul]⟩).symm⟩

/-- **The Macbeath relations are complete.** If the translates of a path-connected open set `U`
cover a simply connected space, then every relation among the Macbeath generators of `U` is a
consequence of the Macbeath relations. -/
theorem macbeathHom_injective [SimplyConnectedSpace X] (hUo : IsOpen U)
    (hUc : IsPathConnected U) (hcover : ⋃ g : G, g • U = univ) :
    Injective (macbeathHom G U) := by
  have := pathConnectedSpace_macbeath (G := G) hUc
  have hp := (isCoveringMap_macbeathProj hUo (macbeathHom_surjective hUo hcover) hcover).injective
  obtain ⟨u₀, hu₀⟩ := hUc.nonempty
  refine (injective_iff_map_eq_one _).2 fun a ha ↦ ?_
  obtain ⟨s, h₁, -⟩ := (macbeathSheet_eq_iff (a := a) (b := 1) (v := ⟨u₀, hu₀⟩)
    (w := ⟨u₀, hu₀⟩)).1 (hp (by simp [macbeathProj_sheet, ha]))
  have hs : (s : G) = 1 := by simpa [ha] using (congrArg (macbeathHom G U) h₁).symm
  rw [macbeath_of_eq_one hs, mul_one] at h₁
  exact h₁.symm

/-- **Macbeath's theorem.** If the translates of a path-connected open set `U` cover a simply
connected space `X`, then `G` is presented by the Macbeath generators and relations of `U`. -/
noncomputable def macbeathEquiv [SimplyConnectedSpace X] (hUo : IsOpen U)
    (hUc : IsPathConnected U) (hcover : ⋃ g : G, g • U = univ) :
    PresentedGroup (macbeathRels G U) ≃* G :=
  MulEquiv.ofBijective (macbeathHom G U)
    ⟨macbeathHom_injective hUo hUc hcover, macbeathHom_surjective hUo hcover⟩

@[simp]
theorem macbeathEquiv_apply [SimplyConnectedSpace X] (hUo : IsOpen U)
    (hUc : IsPathConnected U) (hcover : ⋃ g : G, g • U = univ)
    (a : PresentedGroup (macbeathRels G U)) :
    macbeathEquiv hUo hUc hcover a = macbeathHom G U a :=
  (rfl)

/-- **Macbeath's theorem**, as a description of the relations: if the translates of a
path-connected open set `U` cover a simply connected space, then the kernel of the evaluation of
words in the Macbeath generators of `U` is the normal closure of the Macbeath relations. -/
theorem ker_lift_eq_normalClosure_macbeathRels [SimplyConnectedSpace X] (hUo : IsOpen U)
    (hUc : IsPathConnected U) (hcover : ⋃ g : G, g • U = univ) :
    (FreeGroup.lift (Subtype.val : macbeathGenerators G U → G)).ker =
      Subgroup.normalClosure (macbeathRels G U) := by
  have h : FreeGroup.lift (Subtype.val : macbeathGenerators G U → G) =
      (macbeathHom G U).comp (PresentedGroup.mk _) :=
    FreeGroup.ext_hom _ _ fun s ↦ by
      rw [FreeGroup.lift_apply_of]
      exact (macbeathHom_of U s).symm
  ext x
  rw [h, MonoidHom.mem_ker, MonoidHom.comp_apply,
    (injective_iff_map_eq_one' _).1 (macbeathHom_injective hUo hUc hcover),
    PresentedGroup.mk_eq_one_iff]

end TauCeti
