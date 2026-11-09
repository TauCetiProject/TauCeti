/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Covering.Quotient
import TauCeti.Topology.Covering.Quotient

/-!
# The balanced product of a quotient covering map with a discrete set

Let a group `G` act on a space `E` so that `q : E → X` presents `X` as the quotient `E / G` in
the strong sense of Mathlib's `IsQuotientCoveringMap`: the fibres of `q` are the orbits, and every
point of `E` has a neighbourhood whose `G`-translates are pairwise disjoint. For a discrete
`G`-set `A`, the *balanced product* `BalancedProduct G E A` is the quotient of `E × A` by the
diagonal action of `G`. Since `q` is invariant along the first factor it descends to

`BalancedProduct.proj A : BalancedProduct G E A → X`,

and the theorem of this file is that this projection is a covering map, with fibre `A`.

Neither space is assumed connected, and no local connectedness of `X` is needed. Over the base
set `q '' U` cut out by a set `U` whose `G`-translates are pairwise disjoint, the sheets of the
projection are the images of `U ×ˢ {a}`, one for each `a : A`, and each defining property of a
sheet comes straight from the disjointness of those translates: two points of `U` with the same
class differ by a group element carrying `U` into itself, hence by the identity.

The intended reading is the cover of `X` attached to a set acted on by the deck group of a
regular cover. For `E` the universal cover of `X` and `G` its fundamental group, this is the
covering space attached to an arbitrary `π₁(X, x₀)`-set; no transitivity, and hence no
connectedness of the resulting cover, is assumed. The transitive case `A = G ⧸ H`, where the
balanced product is `E / H`, is `IsQuotientCoveringMap.isCoveringMap_of_comp`, proved
there for an abstract presentation of `E / H` rather than for a fixed model.

## Main declarations

* `TauCeti.BalancedProduct`: the quotient of `E × A` by the diagonal action of `G`.
* `TauCeti.BalancedProduct.equivSelf` and `homeomorphSelf`: the regular label action recovers
  `E`, sending `⟦e, g⟧` to `g⁻¹ • e`.
* `TauCeti.isQuotientCoveringMap_quotientMk_of_smul_disjoint`: an action with locally pairwise
  disjoint translates presents its orbit space as a quotient covering map.
* `TauCeti.BalancedProduct.isQuotientCoveringMap_mk`: the class map `E × A → E ×_G A` is one such.
* `TauCeti.BalancedProduct.isCoveringMap_proj`: **the balanced product of a quotient covering map
  with a discrete set is a covering map.**
* `TauCeti.BalancedProduct.fiberEquiv`: its fibre over `q e` is `A`, through `a ↦ ⟦(e, a)⟧`. This
  last bijection is purely algebraic: it uses no topology, only that the action on `E` is free and
  that the fibres of `q` are its orbits.

## References

The `IsQuotientCoveringMap` interface used here — the predicate itself, its `disjoint` and
`apply_eq_iff_mem_orbit` fields, `IsQuotientCoveringMap.isOpenQuotientMap`, and
`IsOpen.trivializationDiscrete` — is Junyan Xu's, in `Mathlib/Topology/Covering/Quotient.lean`
and `Mathlib/Topology/Covering/Basic.lean`. The sheet bookkeeping follows the subgroup case in
`TauCeti/Topology/Covering/Quotient.lean`.
-/

public section

namespace TauCeti

open Pointwise Topology

section OrbitQuotient

variable {E : Type*} [TopologicalSpace E] {G : Type*} [Group G] [MulAction G E]

/-- **An action whose translates are locally pairwise disjoint presents its orbit space as a
quotient covering map.** This is the free, not necessarily properly discontinuous, form of
Mathlib's `isQuotientCoveringMap_quotientMk_of_properlyDiscontinuousSMul`: no local compactness
or separation of `E` is assumed. -/
theorem isQuotientCoveringMap_quotientMk_of_smul_disjoint [ContinuousConstSMul G E]
    (hdisj : ∀ e : E, ∃ U ∈ 𝓝 e, ∀ g : G, ((g • ·) '' U ∩ U).Nonempty → g = 1) :
    IsQuotientCoveringMap (Quotient.mk (MulAction.orbitRel G E)) G where
  __ := isQuotientMap_quotient_mk'
  apply_eq_iff_mem_orbit := Quotient.eq''
  disjoint := hdisj

end OrbitQuotient

variable {E X A : Type*} {G : Type*} [Group G] [MulAction G E] [MulAction G A] {q : E → X}

/-- The **balanced product** `E ×_G A` of a `G`-space `E` and a `G`-set `A`: the quotient of
`E × A` by the diagonal action of `G`. -/
abbrev BalancedProduct (G E A : Type*) [Group G] [MulAction G E] [MulAction G A] : Type _ :=
  Quotient (MulAction.orbitRel G (E × A))

namespace BalancedProduct

/-- The class of a pair in the balanced product. -/
abbrev mk (G : Type*) [Group G] [MulAction G E] [MulAction G A] (e : E) (a : A) :
    BalancedProduct G E A :=
  Quotient.mk (MulAction.orbitRel G (E × A)) (e, a)

/-- Moving a point of `E × A` by `g` in the first coordinate is the same as moving it by `g⁻¹`
in the second. -/
@[simp]
theorem mk_smul_left (g : G) (e : E) (a : A) : mk G (g • e) a = mk G e (g⁻¹ • a) :=
  Quotient.sound ⟨g, by simp⟩

/-- Two pairs have the same class in the balanced product exactly when one is a translate of the
other under the diagonal action. -/
theorem mk_eq_mk_iff {e e' : E} {a a' : A} :
    mk G e a = mk G e' a' ↔ ∃ g : G, g • e' = e ∧ g • a' = a := by
  simp [Quotient.eq, MulAction.orbitRel_apply, MulAction.mem_orbit_iff, Prod.ext_iff]

/-- Two points of a set `U` whose `G`-translates are pairwise disjoint have the same class in the
balanced product only when they, and their labels, agree. -/
private theorem eq_and_eq_of_mk_eq {U : Set E}
    (hdisj : ∀ g : G, ((g • ·) '' U ∩ U).Nonempty → g = 1) {u u' : E} {a a' : A} (hu : u ∈ U)
    (hu' : u' ∈ U) (hEq : mk G u a = mk G u' a') : u = u' ∧ a = a' := by
  obtain ⟨g, hgu, hga⟩ := mk_eq_mk_iff.mp hEq
  rw [hdisj g ⟨u, ⟨u', hu', hgu⟩, hu⟩, one_smul] at hga hgu
  exact ⟨hgu.symm, hga.symm⟩

/-! ### The regular label action -/

/-- The balanced product with the left regular action of `G` recovers `E`.
The class of `(e, g)` is sent to `g⁻¹ • e`. -/
def equivSelf : BalancedProduct G E G ≃ E where
  toFun := Quotient.lift (fun p : E × G => p.2⁻¹ • p.1) fun _ _ ⟨g, hg⟩ => by
    simp [← hg, mul_smul]
  invFun e := mk G e 1
  left_inv z := Quotient.inductionOn z fun _ => by simp
  right_inv e := by simp

/-- On representatives, the regular-action comparison applies the inverse label to the
first coordinate. -/
@[simp]
theorem equivSelf_mk (e : E) (g : G) :
    equivSelf (mk G e g) = g⁻¹ • e :=
  (rfl)

/-- The inverse regular-action comparison attaches the identity label. -/
@[simp]
theorem equivSelf_symm_apply (e : E) :
    (equivSelf (G := G) (E := E)).symm e = mk G e 1 :=
  (rfl)

/-- The regular-action comparison is a homeomorphism when inversion and the action are
continuous. No freeness or covering hypothesis is needed. -/
def homeomorphSelf [TopologicalSpace E] [TopologicalSpace G] [ContinuousInv G]
    [ContinuousSMul G E] : BalancedProduct G E G ≃ₜ E where
  toEquiv := equivSelf
  continuous_toFun := (continuous_snd.inv.smul continuous_fst).quotient_lift _
  continuous_invFun := continuous_quotient_mk'.comp (continuous_id.prodMk continuous_const)

/-- The topological regular-action comparison has underlying equivalence `equivSelf`. -/
@[simp]
theorem homeomorphSelf_toEquiv [TopologicalSpace E] [TopologicalSpace G] [ContinuousInv G]
    [ContinuousSMul G E] :
    (homeomorphSelf (G := G) (E := E)).toEquiv = equivSelf :=
  (rfl)

/-- On representatives, the topological comparison applies the inverse label. -/
@[simp]
theorem homeomorphSelf_mk [TopologicalSpace E] [TopologicalSpace G] [ContinuousInv G]
    [ContinuousSMul G E] (e : E) (g : G) :
    homeomorphSelf (mk G e g) = g⁻¹ • e :=
  (rfl)

/-- The inverse topological comparison attaches the identity label. -/
@[simp]
theorem homeomorphSelf_symm_apply [TopologicalSpace E] [TopologicalSpace G] [ContinuousInv G]
    [ContinuousSMul G E] (e : E) :
    (homeomorphSelf (G := G) (E := E)).symm e = mk G e 1 :=
  (rfl)

section Map

variable {B C : Type*} [MulAction G B] [MulAction G C]

/-- An equivariant map of labels induces a map of balanced products, keeping the first
coordinate fixed. -/
def mapRight (f : A → B) (hf : ∀ (g : G) a, f (g • a) = g • f a) :
    BalancedProduct G E A → BalancedProduct G E B :=
  Quotient.map' (Prod.map id f) fun _ _ ⟨g, hg⟩ =>
    ⟨g, by rw [← hg]; exact Prod.ext rfl (hf g _).symm⟩

@[simp]
theorem mapRight_mk (f : A → B) (hf : ∀ (g : G) a, f (g • a) = g • f a) (e : E) (a : A) :
    mapRight f hf (mk G e a) = mk G e (f a) :=
  (rfl)

@[simp]
theorem mapRight_id : mapRight (G := G) (E := E) (id : A → A) (fun _ _ => rfl) = id :=
  funext fun z => Quotient.inductionOn z fun _ => rfl

@[simp]
theorem mapRight_comp (f : A → B) (hf : ∀ (g : G) a, f (g • a) = g • f a)
    (k : B → C) (hk : ∀ (g : G) b, k (g • b) = g • k b) :
    mapRight (G := G) (E := E) (k ∘ f) (fun g a => by simp only [Function.comp_apply, hf, hk]) =
      mapRight k hk ∘ mapRight f hf :=
  funext fun z => Quotient.inductionOn z fun _ => rfl

/-- The map induced by a continuous equivariant label map is continuous. -/
theorem continuous_mapRight [TopologicalSpace E] [TopologicalSpace A] [TopologicalSpace B]
    (f : A → B) (hf : ∀ (g : G) a, f (g • a) = g • f a) (hfc : Continuous f) :
    Continuous (mapRight (G := G) (E := E) f hf) :=
  (continuous_id.prodMap hfc).quotient_map' _

/-- An open equivariant label map induces an open map of balanced products. -/
theorem isOpenMap_mapRight [TopologicalSpace E] [TopologicalSpace A] [TopologicalSpace B]
    [ContinuousConstSMul G E] [ContinuousConstSMul G B]
    (f : A → B) (hf : ∀ (g : G) a, f (g • a) = g • f a) (hfo : IsOpenMap f) :
    IsOpenMap (mapRight (G := G) (E := E) f hf) := by
  apply IsOpenMap.of_comp continuous_quotient_mk'
    (@Quotient.mk'_surjective _ (MulAction.orbitRel G (E × A)))
  exact isOpenMap_quotient_mk'_mul.comp (IsOpenMap.id.prodMap hfo)

end Map

variable (hq : ∀ (g : G) (e : E), q (g • e) = q e)

variable (A) in
/-- A `G`-invariant map `q : E → X` descends to the balanced product. -/
def proj : BalancedProduct G E A → X :=
  Quotient.lift (fun p => q p.1) fun _ _ ⟨g, hg⟩ => hg ▸ hq g _

variable (A) in
@[simp]
theorem proj_mk (e : E) (a : A) : proj A hq (mk G e a) = q e :=
  (rfl)

/-- A map of labels commutes with the balanced-product projections. -/
@[simp]
theorem proj_mapRight {B : Type*} [MulAction G B] (f : A → B)
    (hf : ∀ (g : G) a, f (g • a) = g • f a) (z : BalancedProduct G E A) :
    proj B hq (mapRight f hf z) = proj A hq z :=
  Quotient.inductionOn z fun _ => rfl

section Covering

variable [TopologicalSpace E] [TopologicalSpace X] [TopologicalSpace A]

variable (A) in
/-- The descended projection is continuous when `q` is. -/
theorem continuous_proj (hqc : Continuous q) : Continuous (proj A hq) :=
  (hqc.comp continuous_fst).quotient_lift _

variable (A) in
/-- The class map onto the balanced product is a quotient covering map for the diagonal action,
as soon as the action on `E` is one and the action on `A` is continuous: a neighbourhood `U` of
`e` with pairwise disjoint translates gives the neighbourhood `U ×ˢ univ` of `(e, a)`, whose
translates are again pairwise disjoint. -/
theorem isQuotientCoveringMap_mk [ContinuousConstSMul G A]
    (hqc : IsQuotientCoveringMap q G) :
    IsQuotientCoveringMap
      (Quotient.mk (MulAction.orbitRel G (E × A)) : E × A → BalancedProduct G E A) G := by
  have : ContinuousConstSMul G E := hqc.toContinuousConstSMul
  refine isQuotientCoveringMap_quotientMk_of_smul_disjoint fun p => ?_
  obtain ⟨U, hU, hdisj⟩ := hqc.disjoint p.1
  refine ⟨U ×ˢ Set.univ, prod_mem_nhds hU Filter.univ_mem, fun g hg => hdisj g ?_⟩
  obtain ⟨z, ⟨w, hw, hwz⟩, hz⟩ := hg
  exact ⟨z.1, ⟨w.1, hw.1, congrArg Prod.fst hwz⟩, hz.1⟩

variable [DiscreteTopology A]

omit [DiscreteTopology A] in
/-- Openness inside the base set `q '' U` is detected on any single sheet `U ×ˢ {a}`. -/
private theorem isOpen_of_isOpen_preimage_inter_sheet (hqc : IsQuotientCoveringMap q G)
    {U : Set E} (hUo : IsOpen U) (a : A) {W : Set X} (hWV : W ⊆ q '' U)
    (hW : IsOpen (proj A hq ⁻¹' W ∩ Quotient.mk (MulAction.orbitRel G (E × A)) '' (U ×ˢ {a}))) :
    IsOpen W := by
  have hcsG : ContinuousConstSMul G E := hqc.toContinuousConstSMul
  -- The slice at `a` of the preimage of that open set, cut down to `U`, is `q ⁻¹' W ∩ U`.
  have hslice : IsOpen (q ⁻¹' W ∩ U) := by
    have hopen : IsOpen (Quotient.mk (MulAction.orbitRel G (E × A)) ⁻¹'
        (proj A hq ⁻¹' W ∩ Quotient.mk (MulAction.orbitRel G (E × A)) '' (U ×ˢ {a}))) :=
      hW.preimage continuous_quotient_mk'
    have hcont : Continuous fun u : E => (u, a) := continuous_id.prodMk continuous_const
    have heq : q ⁻¹' W ∩ U = ((fun u : E => (u, a)) ⁻¹'
        (Quotient.mk (MulAction.orbitRel G (E × A)) ⁻¹'
          (proj A hq ⁻¹' W ∩ Quotient.mk (MulAction.orbitRel G (E × A)) '' (U ×ˢ {a})))) ∩ U := by
      ext u
      constructor
      · rintro ⟨hqu, hu⟩
        exact ⟨⟨hqu, (u, a), ⟨hu, rfl⟩, rfl⟩, hu⟩
      · rintro ⟨⟨hw, -⟩, hu⟩
        exact ⟨hw, hu⟩
    rw [heq]
    exact (hopen.preimage hcont).inter hUo
  exact hqc.isOpen_of_isOpen_preimage_inter hWV hslice

variable (A) in
/-- The evenly covered neighbourhood of `q e` cut out by a set `U` around `e` whose `G`-translates
are pairwise disjoint. Its sheets are the classes of `U ×ˢ {a}`, indexed by `a : A`. -/
private theorem isEvenlyCovered_of_smul_disjoint [Nonempty A] (hqc : IsQuotientCoveringMap q G)
    {U : Set E} (hUo : IsOpen U) (hdisj : ∀ g : G, ((g • ·) '' U ∩ U).Nonempty → g = 1) {e : E}
    (heU : e ∈ U) :
    IsEvenlyCovered (proj A hq) (q e) (proj A hq ⁻¹' {q e}) := by
  let _ : ContinuousConstSMul G A := ⟨fun _ => continuous_of_discreteTopology⟩
  have ht := isQuotientCoveringMap_mk A hqc
  have hrc : Continuous (proj A hq) := continuous_proj A hq hqc.continuous
  have hVo : IsOpen (q '' U) := hqc.isOpenQuotientMap.isOpenMap _ hUo
  set S : A → Set (BalancedProduct G E A) :=
    fun a => Quotient.mk (MulAction.orbitRel G (E × A)) '' (U ×ˢ {a})
  have hSo : ∀ a, IsOpen (S a) := fun a =>
    ht.isOpenQuotientMap.isOpenMap _ (hUo.prod (isOpen_discrete _))
  have hmemS : ∀ (a : A) (z : BalancedProduct G E A), z ∈ S a ↔ ∃ u ∈ U, mk G u a = z :=
    fun a z => by simp only [S, Set.prod_singleton, Set.image_image, Set.mem_image, mk]
  have : Nonempty (X → BalancedProduct G E A) := ⟨fun _ => mk G e (Classical.arbitrary A)⟩
  refine IsEvenlyCovered.to_isEvenlyCovered_preimage
    (IsEvenlyCovered.of_trivialization (f := proj A hq)
      (t := hVo.trivializationDiscrete S (q '' U) ?_ ?_ ?_ ?_ ?_) ⟨e, heU, rfl⟩)
  · -- Openness inside the base set is detected on any single sheet.
    intro a W hWV
    exact ⟨fun hW => (hW.preimage hrc).inter (hSo a),
      isOpen_of_isOpen_preimage_inter_sheet hq hqc hUo a hWV⟩
  · -- The projection is injective on each sheet.
    intro a z hz z' hz' hzz'
    obtain ⟨u, hu, rfl⟩ := (hmemS a z).mp hz
    obtain ⟨u', hu', rfl⟩ := (hmemS a z').mp hz'
    rw [proj_mk, proj_mk] at hzz'
    obtain ⟨m, hm⟩ := MulAction.mem_orbit_iff.mp (hqc.apply_eq_iff_mem_orbit.mp hzz')
    rw [← hm, hdisj m ⟨u, ⟨u', hu', hm⟩, hu⟩, one_smul]
  · -- Each sheet surjects onto the base set.
    rintro a v ⟨u, hu, rfl⟩
    exact ⟨mk G u a, (hmemS a _).mpr ⟨u, hu, rfl⟩, proj_mk A hq u a⟩
  · -- Distinct sheets are disjoint.
    intro a a' hne
    refine Set.disjoint_left.mpr fun z hz hz' => hne ?_
    obtain ⟨u, hu, rfl⟩ := (hmemS a z).mp hz
    obtain ⟨u', hu', hEq⟩ := (hmemS a' _).mp hz'
    exact (eq_and_eq_of_mk_eq hdisj hu' hu hEq).2.symm
  · -- The sheets exhaust the preimage of the base set.
    intro z hz
    obtain ⟨⟨w, b⟩, rfl⟩ := ht.surjective z
    rw [Set.mem_preimage] at hz
    obtain ⟨u, hu, hqu⟩ := hz
    obtain ⟨m, hm⟩ := hqc.apply_eq_iff_mem_orbit.mp hqu.symm
    have hmu : m • u = w := hm
    refine Set.mem_iUnion.mpr ⟨m⁻¹ • b, (hmemS _ _).mpr ⟨u, hu, ?_⟩⟩
    rw [← mk_smul_left m u b, hmu]

variable (A) in
/-- **The balanced product of a quotient covering map with a discrete set is a covering map.**

If `q : E → X` presents `X` as the quotient of `E` by a group `G` in the sense of
`IsQuotientCoveringMap`, and `A` is a discrete `G`-set, then the descended projection of the
balanced product `E ×_G A` to `X` is a covering map. -/
theorem isCoveringMap_proj (hqc : IsQuotientCoveringMap q G) : IsCoveringMap (proj A hq) := by
  let _ : ContinuousConstSMul G A := ⟨fun _ => continuous_of_discreteTopology⟩
  cases isEmpty_or_nonempty A with
  | inl _ =>
    exact IsCoveringMap.of_isEmpty _
  | inr _ =>
    intro x
    obtain ⟨e, rfl⟩ := hqc.surjective x
    obtain ⟨U, hU, hdisj⟩ := hqc.disjoint e
    exact isEvenlyCovered_of_smul_disjoint A hq hqc isOpen_interior
      (fun g hg => hdisj g (hg.mono (by grw [interior_subset])))
      (mem_interior_iff_mem_nhds.mpr hU)

end Covering

section Fiber

variable (A) in
/-- **The fibre of the balanced product over `x` is `A`.** The bijection sends `a` to the class
of `(e, a)`; it depends on the chosen point `e` of the fibre of `q`.

Only two consequences of `q` being a quotient covering map are used, and neither involves a
topology: the action on `E` is free, and points of `E` with the same image lie in one orbit. -/
noncomputable def fiberEquiv [IsCancelSMul G E]
    (hfiber : ∀ {e₁ e₂ : E}, q e₁ = q e₂ → e₁ ∈ MulAction.orbit G e₂) {x : X} (e : q ⁻¹' {x}) :
    A ≃ proj A hq ⁻¹' {x} := by
  refine Equiv.ofBijective (fun a => ⟨mk G (e : E) a, ?_⟩) ⟨?_, ?_⟩
  · rw [Set.mem_preimage, Set.mem_singleton_iff, proj_mk]
    exact e.2
  · intro a a' hEq
    obtain ⟨g, hg, rfl⟩ := mk_eq_mk_iff.mp (congrArg Subtype.val hEq)
    rw [IsCancelSMul.eq_one_of_smul hg, one_smul]
  · rintro ⟨z, hz⟩
    obtain ⟨⟨w, b⟩, rfl⟩ := Quotient.mk''_surjective z
    rw [Set.mem_preimage, Set.mem_singleton_iff, proj_mk] at hz
    obtain ⟨g, hge⟩ := MulAction.mem_orbit_iff.mp (hfiber (hz.trans e.2.symm))
    exact ⟨g⁻¹ • b, Subtype.ext <| by dsimp only; rw [← mk_smul_left, hge]⟩

variable (A) in
/-- The fibre bijection of the balanced product sends `a` to the class of `(e, a)`. -/
@[simp]
theorem fiberEquiv_apply_coe [IsCancelSMul G E]
    (hfiber : ∀ {e₁ e₂ : E}, q e₁ = q e₂ → e₁ ∈ MulAction.orbit G e₂) {x : X} (e : q ⁻¹' {x})
    (a : A) :
    (fiberEquiv A hq hfiber e a : BalancedProduct G E A) = mk G (e : E) a :=
  (rfl)

end Fiber

end BalancedProduct

end TauCeti
