/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.Homotopy.Extension.Cube
public import TauCeti.Topology.Homotopy.Extension.NDRPair
public import TauCeti.Topology.Homotopy.Proper

/-!
# The proper homotopy extension property

A subset `A` of a topological space `X` has the *proper homotopy extension property*
(`TauCeti.HasProperHomotopyExtensionProperty`) when every proper homotopy `H : I × A → Y` whose
initial map extends to a proper map `f : X → Y` extends to a proper homotopy `G : I × X → Y`, with
properness required on the full cylinders `I × A` and `I × X`.

For closed `A`, this is equivalent to a *proper* retraction of `I × X` onto `{0} × X ∪ I × A`
(`TauCeti.hasProperHomotopyExtensionProperty_iff_exists_retraction`), making the property
universe-free (`TauCeti.HasProperHomotopyExtensionProperty.exists_extension_of_isClosed`) and
equivalent to NDR data with proper deformation `I × X → X` (`TauCeti.exists_proper_ndrPair_iff`).
Passing through proper NDR pairs yields the proper Strøm product theorem
(`TauCeti.HasProperHomotopyExtensionProperty.prod_univ_union_univ_prod`) and its cylinder-boundary
instance `{0, 1} × X ∪ I × A ⊆ I × X`
(`TauCeti.HasProperHomotopyExtensionProperty.zero_one_prod_univ_union_univ_prod`).

## Main declarations

* `TauCeti.HasProperHomotopyExtensionProperty`,
  `TauCeti.hasProperHomotopyExtensionProperty_iff_exists_retraction`,
  `TauCeti.HasProperHomotopyExtensionProperty.exists_extension_of_isClosed`: proper homotopy
  extension and its proper cylinder-retraction characterization.
* `TauCeti.HasHomotopyExtensionProperty.hasProperHomotopyExtensionProperty_of_compactSpace`: closed
  cofibrations in compact Hausdorff spaces have the proper homotopy extension property.
* `TauCeti.NDRPair.isProperMap_cylinderDeformation`,
  `TauCeti.NDRPair.hasProperHomotopyExtensionProperty`, `TauCeti.exists_proper_ndrPair_iff`:
  **proper Strøm characterization** via NDR pairs with proper deformation.
* `TauCeti.NDRPair.isProperMap_prod_deformation`,
  `TauCeti.HasProperHomotopyExtensionProperty.prod_univ_union_univ_prod`,
  `TauCeti.HasProperHomotopyExtensionProperty.zero_one_prod_univ_union_univ_prod`: **proper Strøm
  product theorem** and cylinder-boundary corollary.

## References

* F. T. Farrell, L. R. Taylor, J. B. Wagoner, *The Whitehead theorem in the proper category*,
  Compositio Math. 27 (1973), 1–23, Section 1.
* A. Strøm, *Note on cofibrations II*, Math. Scand. 22 (1968), 130–142.
* A. Hatcher, [*Algebraic Topology*](https://pi.math.cornell.edu/~hatcher/AT/AT.pdf), Chapter 0.
-/

public section

namespace TauCeti

open Filter Set Topology unitInterval

universe u u' v

section Basic

variable {X : Type u} [TopologicalSpace X] {A : Set X}

/-- A subset `A` of `X` has the *proper homotopy extension property* when every proper homotopy
`H : I × A → Y` whose initial slice extends to a proper map `f : X → Y` extends to a proper
homotopy `G : I × X → Y`.

Targets `Y` are quantified in the universe of `X`; for closed `A`,
`TauCeti.HasProperHomotopyExtensionProperty.exists_extension_of_isClosed` extends proper homotopies
with values in any universe. -/
def HasProperHomotopyExtensionProperty (A : Set X) : Prop :=
  ∀ {Y : Type u} [TopologicalSpace Y] (f : C(X, Y)), IsProperMap f →
    ∀ (H : C(I × A, Y)), IsProperMap H → (∀ a : A, H (0, a) = f a) →
      ∃ G : C(I × X, Y), IsProperMap G ∧
        (∀ x : X, G (0, x) = f x) ∧ ∀ (t : I) (a : A), G (t, a) = H (t, a)

/-- Unfolding of `TauCeti.HasProperHomotopyExtensionProperty`. -/
theorem hasProperHomotopyExtensionProperty_iff :
    HasProperHomotopyExtensionProperty A ↔
      ∀ {Y : Type u} [TopologicalSpace Y] (f : C(X, Y)), IsProperMap f →
        ∀ (H : C(I × A, Y)), IsProperMap H → (∀ a : A, H (0, a) = f a) →
          ∃ G : C(I × X, Y), IsProperMap G ∧
            (∀ x : X, G (0, x) = f x) ∧ ∀ (t : I) (a : A), G (t, a) = H (t, a) :=
  Iff.rfl

/-- Applying the proper homotopy extension property to a proper initial map `f` and a proper
partial homotopy `H`. -/
theorem HasProperHomotopyExtensionProperty.exists_extension
    (h : HasProperHomotopyExtensionProperty A) {Y : Type u} [TopologicalSpace Y]
    (f : C(X, Y)) (hf : IsProperMap f) (H : C(I × A, Y)) (hH : IsProperMap H)
    (hH₀ : ∀ a : A, H (0, a) = f a) :
    ∃ G : C(I × X, Y), IsProperMap G ∧
      (∀ x : X, G (0, x) = f x) ∧ ∀ (t : I) (a : A), G (t, a) = H (t, a) :=
  h f hf H hH hH₀

/-- The empty subset has the proper homotopy extension property. -/
theorem hasProperHomotopyExtensionProperty_empty :
    HasProperHomotopyExtensionProperty (∅ : Set X) :=
  fun f hf _ _ _ ↦ ⟨f.comp ContinuousMap.snd, hf.comp (isProperMap_snd_of_compactSpace (X := I)),
    fun _ ↦ rfl, fun _ a ↦ a.2.elim⟩

/-- The whole space has the proper homotopy extension property. -/
theorem hasProperHomotopyExtensionProperty_univ :
    HasProperHomotopyExtensionProperty (univ : Set X) := by
  intro Y _ _ _ H hH hH₀
  let e : I × X ≃ₜ I × (univ : Set X) := (Homeomorph.refl I).prodCongr (Homeomorph.Set.univ X).symm
  exact ⟨H.comp (e : C(I × X, I × (univ : Set X))), hH.comp e.isProperMap, fun x ↦ hH₀ ⟨x, trivial⟩,
    fun t _ ↦ congrArg (fun b : (univ : Set X) ↦ H (t, b)) (Subtype.ext rfl)⟩

/-- The side piece `{q ∈ cylinderExtensionDomain A | q.2 ∈ A}` is homeomorphic to `I × A`. -/
private def cylinderSideHomeomorph (A : Set X) :
    {q : cylinderExtensionDomain A | q.1.2 ∈ A} ≃ₜ I × A where
  toFun z := (z.1.1.1, ⟨z.1.1.2, z.2⟩)
  invFun p := ⟨⟨(p.1, p.2.1), mem_cylinderExtensionDomain_of_mem p.2.2⟩, p.2.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- The bottom piece `{q ∈ cylinderExtensionDomain A | q.1 = 0}` is homeomorphic to `X`. -/
private def cylinderBottomHomeomorph (A : Set X) :
    {q : cylinderExtensionDomain A | q.1.1 = 0} ≃ₜ X where
  toFun z := z.1.1.2
  invFun x := ⟨⟨(0, x), zero_mem_cylinderExtensionDomain x⟩, rfl⟩
  left_inv z := Subtype.ext (Subtype.ext (Prod.ext z.2.symm rfl))
  right_inv _ := rfl

/-- A proper retraction of `I × X` onto `{0} × X ∪ I × A` solves every proper homotopy extension
problem for a closed subset `A ⊆ X`, with values in a space in any universe. -/
theorem exists_proper_homotopy_extension_of_retraction {Y : Type v} [TopologicalSpace Y]
    (hA : IsClosed A) {r : C(I × X, I × X)} (hr_proper : IsProperMap r)
    (hr : ∀ p, r p ∈ cylinderExtensionDomain A)
    (hr' : ∀ p ∈ cylinderExtensionDomain A, r p = p)
    (f : C(X, Y)) (hf : IsProperMap f) (H : C(I × A, Y)) (hH : IsProperMap H)
    (hH₀ : ∀ a : A, H (0, a) = f a) :
    ∃ G : C(I × X, Y), IsProperMap G ∧
      (∀ x : X, G (0, x) = f x) ∧ ∀ (t : I) (a : A), G (t, a) = H (t, a) := by
  classical
  let g₀ : cylinderExtensionDomain A → Y := fun q ↦
    if h : q.1.2 ∈ A then H (q.1.1, ⟨q.1.2, h⟩) else f q.1.2
  let s₁ : Set (cylinderExtensionDomain A) := {q | q.1.2 ∈ A}
  let s₂ : Set (cylinderExtensionDomain A) := {q | q.1.1 = 0}
  have hs₁ : IsClosed s₁ := hA.preimage (continuous_snd.comp continuous_subtype_val)
  have hs₂ : IsClosed s₂ :=
    (isClosed_singleton (x := (0 : I))).preimage (continuous_fst.comp continuous_subtype_val)
  have hcov : s₁ ∪ s₂ = univ := by
    ext q
    simpa only [s₁, s₂, mem_union, mem_ofPred_eq, mem_univ, iff_true, or_comm] using
      mem_cylinderExtensionDomain_iff.1 q.2
  have hg₀ : IsProperMap g₀ := by
    refine IsProperMap.of_union_isClosed hs₁ hs₂ hcov ?_ ?_
    · convert hH.comp (cylinderSideHomeomorph A).isProperMap using 1
      ext z
      exact dite_eq_left z.2
    · convert hf.comp (cylinderBottomHomeomorph A).isProperMap using 1
      ext z
      have hz0 : z.1.1.1 = 0 := z.2
      by_cases h : z.1.1.2 ∈ A <;> simp [g₀, cylinderBottomHomeomorph, h, hz0, hH₀]
  let r₀ : C(I × X, cylinderExtensionDomain A) := ⟨fun p ↦ ⟨r p, hr p⟩, r.continuous.subtype_mk hr⟩
  have hr₀ : IsProperMap r₀ :=
    isProperMap_of_comp_of_inj r₀.continuous continuous_subtype_val hr_proper Subtype.val_injective
  let g₀_cont : C(cylinderExtensionDomain A, Y) := ⟨g₀, hg₀.continuous⟩
  refine ⟨g₀_cont.comp r₀, hg₀.comp hr₀, fun x ↦ ?_, fun t a ↦ ?_⟩
  · have hfix : r₀ (0, x) = ⟨(0, x), zero_mem_cylinderExtensionDomain x⟩ :=
      Subtype.ext (hr' _ (zero_mem_cylinderExtensionDomain x))
    by_cases hx : x ∈ A <;> simp [g₀_cont, ContinuousMap.comp_apply, hfix, g₀, hx, hH₀]
  · have hfix : r₀ (t, a) = ⟨(t, a), mem_cylinderExtensionDomain_of_mem a.2⟩ :=
      Subtype.ext (hr' _ (mem_cylinderExtensionDomain_of_mem a.2))
    simp [g₀_cont, ContinuousMap.comp_apply, hfix, g₀, a.2]

/-- A closed subset onto whose cylinder extension domain `I × X` properly retracts has the proper
homotopy extension property. -/
theorem hasProperHomotopyExtensionProperty_of_retraction (hA : IsClosed A) {r : C(I × X, I × X)}
    (hr_proper : IsProperMap r) (hr : ∀ p, r p ∈ cylinderExtensionDomain A)
    (hr' : ∀ p ∈ cylinderExtensionDomain A, r p = p) :
    HasProperHomotopyExtensionProperty A := fun f hf H hH hH₀ ↦
  exists_proper_homotopy_extension_of_retraction hA hr_proper hr hr' f hf H hH hH₀

/-- If a closed subset `A` has the proper homotopy extension property, then `I × X` admits a proper
retraction onto `{0} × X ∪ I × A`. -/
theorem HasProperHomotopyExtensionProperty.exists_retraction (hA : IsClosed A)
    (h : HasProperHomotopyExtensionProperty A) :
    ∃ r : C(I × X, I × X), IsProperMap r ∧ (∀ p, r p ∈ cylinderExtensionDomain A) ∧
      ∀ p ∈ cylinderExtensionDomain A, r p = p := by
  have hs₁ : IsClosed {q : cylinderExtensionDomain A | q.1.2 ∈ A} :=
    hA.preimage (continuous_snd.comp continuous_subtype_val)
  have hs₂ : IsClosed {q : cylinderExtensionDomain A | q.1.1 = 0} :=
    (isClosed_singleton (x := (0 : I))).preimage (continuous_fst.comp continuous_subtype_val)
  obtain ⟨G, hG, hG₀, hG₁⟩ := h.exists_extension
    ((ContinuousMap.subtypeVal _).comp (cylinderBottomHomeomorph A).symm)
    (hs₂.isProperMap_subtypeVal.comp (cylinderBottomHomeomorph A).symm.isProperMap)
    ((ContinuousMap.subtypeVal _).comp (cylinderSideHomeomorph A).symm)
    (hs₁.isProperMap_subtypeVal.comp (cylinderSideHomeomorph A).symm.isProperMap)
    fun _ ↦ Subtype.ext rfl
  refine ⟨(ContinuousMap.subtypeVal _).comp G,
    (isClosed_cylinderExtensionDomain hA).isProperMap_subtypeVal.comp hG, fun p ↦ (G p).2, ?_⟩
  rintro ⟨t, x⟩ hp
  rcases mem_cylinderExtensionDomain_iff.1 hp with rfl | hx
  · exact congrArg Subtype.val (hG₀ x)
  · exact congrArg Subtype.val (hG₁ t ⟨x, hx⟩)

/-- **A closed subset has the proper homotopy extension property if and only if `{0} × X ∪ I × A`
is a proper retract of `I × X`.** -/
theorem hasProperHomotopyExtensionProperty_iff_exists_retraction (hA : IsClosed A) :
    HasProperHomotopyExtensionProperty A ↔
      ∃ r : C(I × X, I × X), IsProperMap r ∧ (∀ p, r p ∈ cylinderExtensionDomain A) ∧
        ∀ p ∈ cylinderExtensionDomain A, r p = p :=
  ⟨fun h ↦ h.exists_retraction hA, fun ⟨_, hr_proper, hr, hr'⟩ ↦
    hasProperHomotopyExtensionProperty_of_retraction hA hr_proper hr hr'⟩

/-- For a closed subset, the proper homotopy extension property implies the ordinary homotopy
extension property. -/
theorem HasProperHomotopyExtensionProperty.hasHomotopyExtensionProperty (hA : IsClosed A)
    (h : HasProperHomotopyExtensionProperty A) : HasHomotopyExtensionProperty A := by
  obtain ⟨_, -, hr, hr'⟩ := h.exists_retraction hA
  exact hasHomotopyExtensionProperty_of_retraction hA hr hr'

/-- For a closed subset, the proper homotopy extension property extends proper homotopies with
values in a space in an arbitrary universe. -/
theorem HasProperHomotopyExtensionProperty.exists_extension_of_isClosed (hA : IsClosed A)
    (h : HasProperHomotopyExtensionProperty A) {Y : Type v} [TopologicalSpace Y]
    (f : C(X, Y)) (hf : IsProperMap f) (H : C(I × A, Y)) (hH : IsProperMap H)
    (hH₀ : ∀ a : A, H (0, a) = f a) :
    ∃ G : C(I × X, Y), IsProperMap G ∧
      (∀ x : X, G (0, x) = f x) ∧ ∀ (t : I) (a : A), G (t, a) = H (t, a) := by
  obtain ⟨_, hr_proper, hr, hr'⟩ := h.exists_retraction hA
  exact exists_proper_homotopy_extension_of_retraction hA hr_proper hr hr' f hf H hH hH₀

/-- On a compact Hausdorff space, every closed subset with the homotopy extension property has the
proper homotopy extension property. -/
theorem HasHomotopyExtensionProperty.hasProperHomotopyExtensionProperty_of_compactSpace
    [CompactSpace X] [T2Space X] (h : HasHomotopyExtensionProperty A) (hA : IsClosed A) :
    HasProperHomotopyExtensionProperty A := by
  obtain ⟨r, hr, hr'⟩ := h.exists_retraction
  exact hasProperHomotopyExtensionProperty_of_retraction hA r.continuous.isProperMap hr hr'

/-- Every clopen subset has the proper homotopy extension property. -/
theorem _root_.IsClopen.hasProperHomotopyExtensionProperty (hA : IsClopen A) :
    HasProperHomotopyExtensionProperty A := by
  classical
  have hfr : frontier {p : I × X | p.2 ∈ A} = ∅ :=
    (hA.preimage (f := (Prod.snd : I × X → X)) continuous_snd).frontier_eq
  let r : C(I × X, I × X) :=
    ⟨fun p ↦ if p.2 ∈ A then p else ((0 : I), p.2),
      Continuous.if (by simp [hfr]) continuous_id (by fun_prop)⟩
  have hs : IsClosed {p : I × X | p.2 ∈ A} := hA.isClosed.preimage continuous_snd
  have ht : IsClosed {p : I × X | p.2 ∉ A} := hA.compl.isClosed.preimage continuous_snd
  have hr_proper : IsProperMap r := by
    refine IsProperMap.of_union_isClosed hs ht (Set.eq_univ_of_forall fun p ↦ em (p.2 ∈ A)) ?_ ?_
    · convert hs.isProperMap_subtypeVal using 1
      funext p
      exact ite_eq_left p.2
    · convert (isProperMap_prodMk_left (0 : I)).comp
        ((isProperMap_snd_of_compactSpace (X := I)).comp ht.isProperMap_subtypeVal) using 1
      funext p
      exact ite_eq_right p.2
  rw [hasProperHomotopyExtensionProperty_iff_exists_retraction hA.isClosed]
  refine ⟨r, hr_proper, fun p ↦ ?_, fun ⟨u, x⟩ hp ↦ ?_⟩
  · by_cases hp : p.2 ∈ A <;> simp [r, hp, mem_cylinderExtensionDomain_iff]
  · rcases mem_cylinderExtensionDomain_iff.1 hp with rfl | hx
    · by_cases hx : x ∈ A <;> simp [r, hx]
    · simp [r, hx]

/-- The proper homotopy extension property transports along a homeomorphism in the same universe,
with no closedness assumption on `A`. -/
theorem HasProperHomotopyExtensionProperty.image {X' : Type u} [TopologicalSpace X']
    (h : HasProperHomotopyExtensionProperty A) (e : X ≃ₜ X') :
    HasProperHomotopyExtensionProperty (e '' A) := by
  intro Y _ f hf H hH hH₀
  let eA : A ≃ₜ (e '' A : Set X') := e.image A
  let eIA : I × A ≃ₜ I × (e '' A : Set X') := (Homeomorph.refl I).prodCongr eA
  let eIX : I × X' ≃ₜ I × X := (Homeomorph.refl I).prodCongr e.symm
  obtain ⟨G, hG, hG₀, hG₁⟩ := h.exists_extension (f.comp (e : C(X, X'))) (hf.comp e.isProperMap)
    (H.comp (eIA : C(I × A, I × (e '' A : Set X')))) (hH.comp eIA.isProperMap) fun a ↦ hH₀ (eA a)
  refine ⟨G.comp (eIX : C(I × X', I × X)), hG.comp eIX.isProperMap, fun x' ↦ ?_, fun t b ↦ ?_⟩
  · simpa [eIX] using hG₀ (e.symm x')
  · obtain ⟨a, ha, hae⟩ := b.2
    have hsymm : e.symm (b : X') = a := by rw [← hae, e.symm_apply_apply]
    change G (t, e.symm b) = H (t, b)
    rw [hsymm, hG₁ t ⟨a, ha⟩]
    exact congrArg (fun c ↦ H (t, c)) (Subtype.ext hae)

/-- For a closed subset, the proper homotopy extension property transports along a homeomorphism
across universes. -/
theorem HasProperHomotopyExtensionProperty.image_of_isClosed {X' : Type u'} [TopologicalSpace X']
    (h : HasProperHomotopyExtensionProperty A) (e : X ≃ₜ X') (hA : IsClosed A) :
    HasProperHomotopyExtensionProperty (e '' A) := by
  obtain ⟨r, hr_proper, hr, hr'⟩ := h.exists_retraction hA
  let eIX : I × X ≃ₜ I × X' := (Homeomorph.refl I).prodCongr e
  let r' : C(I × X', I × X') :=
    ((eIX : C(I × X, I × X')).comp r).comp (eIX.symm : C(I × X', I × X))
  rw [hasProperHomotopyExtensionProperty_iff_exists_retraction (e.isClosedMap A hA)]
  refine ⟨r', eIX.isProperMap.comp (hr_proper.comp eIX.symm.isProperMap), fun q ↦ ?_,
    fun q hq ↦ ?_⟩
  · change ((r (q.1, e.symm q.2)).1, e (r (q.1, e.symm q.2)).2) ∈ cylinderExtensionDomain (e '' A)
    exact (mem_cylinderExtensionDomain_iff.1 (hr (q.1, e.symm q.2))).elim
      (fun h0 ↦ mem_cylinderExtensionDomain_iff.2 (.inl h0))
      (fun hm ↦ mem_cylinderExtensionDomain_iff.2 (.inr (mem_image_of_mem e hm)))
  · have hq' : (q.1, e.symm q.2) ∈ cylinderExtensionDomain A :=
      (mem_cylinderExtensionDomain_iff.1 hq).elim
        (fun h0 ↦ mem_cylinderExtensionDomain_iff.2 (.inl h0))
        fun ⟨a, ha, hae⟩ ↦ mem_cylinderExtensionDomain_iff.2
          (.inr (by rw [← hae, e.symm_apply_apply]; exact ha))
    change ((r (q.1, e.symm q.2)).1, e (r (q.1, e.symm q.2)).2) = q
    rw [hr' _ hq']
    exact Prod.ext rfl (e.apply_symm_apply q.2)

/-- **Proper cofibrations compose along closed embeddings.** If `j : X → X'` is a closed embedding
whose range has the proper homotopy extension property in `X'`, and `A` has the proper homotopy
extension property in `X`, then `j '' A` has the proper homotopy extension property in `X'`. -/
theorem HasProperHomotopyExtensionProperty.image_of_isClosedEmbedding
    {X' : Type u} [TopologicalSpace X'] (h : HasProperHomotopyExtensionProperty A)
    {j : X → X'} (hj : IsClosedEmbedding j)
    (hj' : HasProperHomotopyExtensionProperty (range j)) :
    HasProperHomotopyExtensionProperty (j '' A) := by
  intro Y _ f hf H hH hH₀
  let eIA : I × A ≃ₜ I × (j '' A : Set X') :=
    (Homeomorph.refl I).prodCongr (hj.isEmbedding.homeomorphImage A)
  let eIR : I × (range j : Set X') ≃ₜ I × X :=
    (Homeomorph.refl I).prodCongr hj.isEmbedding.toHomeomorph.symm
  have heir (t : I) (x : X) :
      (eIR : C(I × (range j : Set X'), I × X)) (t, ⟨j x, mem_range_self x⟩) = (t, x) :=
    Prod.ext rfl (hj.isEmbedding.toHomeomorph_symm_apply x)
  obtain ⟨G, hG, hG₀, hG₁⟩ := h.exists_extension (f.comp ⟨j, hj.continuous⟩)
    (hf.comp hj.isProperMap) (H.comp (eIA : C(I × A, I × (j '' A : Set X'))))
    (hH.comp eIA.isProperMap) fun a ↦ hH₀ ⟨j a, mem_image_of_mem j a.2⟩
  obtain ⟨G', hG', hG'₀, hG'₁⟩ := hj'.exists_extension f hf
    (G.comp (eIR : C(I × (range j : Set X'), I × X))) (hG.comp eIR.isProperMap) fun ⟨_, x, rfl⟩ ↦ by
      rw [ContinuousMap.comp_apply, heir, hG₀]; rfl
  refine ⟨G', hG', hG'₀, fun t ⟨_, a, ha, rfl⟩ ↦ ?_⟩
  rw [hG'₁ t ⟨j a, mem_range_self a⟩, ContinuousMap.comp_apply, heir, hG₁ t ⟨a, ha⟩]
  rfl

end Basic

section CompactExamples

/-- The unit sphere of a proper real normed space has the proper homotopy extension property inside
the closed unit ball. -/
theorem hasProperHomotopyExtensionProperty_sphere_closedBall {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [ProperSpace E] :
    HasProperHomotopyExtensionProperty
      (Subtype.val ⁻¹' Metric.sphere (0 : E) 1 : Set (Metric.closedBall (0 : E) 1)) :=
  hasHomotopyExtensionProperty_sphere_closedBall.hasProperHomotopyExtensionProperty_of_compactSpace
    (Metric.isClosed_sphere.preimage continuous_subtype_val)

/-- For a finite index type `N`, the boundary of the cube `I^N` is closed. -/
theorem Cube.isClosed_boundary {N : Type*} [Finite N] : IsClosed (Cube.boundary N) := by
  have heq : Cube.boundary N = ⋃ i : N, {y : N → I | y i = 0 ∨ y i = 1} := by
    ext y; simp [Cube.boundary]
  rw [heq]
  exact isClosed_iUnion_of_finite fun i ↦
    (isClosed_eq (continuous_apply i) continuous_const).union
      (isClosed_eq (continuous_apply i) continuous_const)

/-- For a finite index type `N`, the boundary of the cube `I^N` has the proper homotopy extension
property in `I^N`. -/
theorem hasProperHomotopyExtensionProperty_cubeBoundary {N : Type*} [Finite N] :
    HasProperHomotopyExtensionProperty (Cube.boundary N) :=
  hasHomotopyExtensionProperty_cubeBoundary.hasProperHomotopyExtensionProperty_of_compactSpace
    Cube.isClosed_boundary

/-- The endpoints `{0, 1}` of the unit interval have the proper homotopy extension property in
`I`. -/
theorem hasProperHomotopyExtensionProperty_zero_one :
    HasProperHomotopyExtensionProperty ({0, 1} : Set I) :=
  hasHomotopyExtensionProperty_zero_one.hasProperHomotopyExtensionProperty_of_compactSpace
    (Set.toFinite _).isClosed

end CompactExamples

section NDRPair

variable {X : Type u} [TopologicalSpace X] {A : Set X}

/-- Ultrafilter convergence step for a proper deformation `h : T × Y → Y` fixing `S` pointwise and
evaluated at a time `φ z` continuous away from `S`. -/
private theorem ultrafilter_tendsto_apply_prodMk_of_fixed {T Y Z : Type*} [TopologicalSpace T]
    [T2Space T] [TopologicalSpace Y] [TopologicalSpace Z] {h : C(T × Y, Y)} (hh : IsProperMap h)
    {S : Set Y} (hS : ∀ t, ∀ y ∈ S, h (t, y) = y) {q : Z → Y} {φ : Z → T}
    (hφ : ∀ z, q z ∉ S → ContinuousAt φ z) {𝒰 : Ultrafilter Z} {y₀ : Y}
    (hlim : Tendsto (fun z ↦ h (φ z, q z)) 𝒰 (𝓝 y₀)) :
    ∃ y₁ : Y, Tendsto q 𝒰 (𝓝 y₁) ∧
      ∀ z₀ : Z, (𝒰 : Filter Z) ≤ 𝓝 z₀ → q z₀ = y₁ → h (φ z₀, q z₀) = y₀ := by
  obtain ⟨⟨t₁, y₁⟩, hty, hle⟩ := hh.ultrafilter_le_nhds_of_tendsto (f := h)
    (𝒰 := 𝒰.map fun z ↦ (φ z, q z)) (by rwa [Ultrafilter.coe_map, tendsto_map'_iff])
  refine ⟨y₁, tendsto_map'_iff.1 ((continuous_snd.tendsto (t₁, y₁)).mono_left hle),
    fun z₀ hz₀ hqz ↦ ?_⟩
  by_cases hy₁ : y₁ ∈ S
  · rw [hqz, hS _ _ hy₁, ← hty, hS _ _ hy₁]
  · have ht_lim : Tendsto φ 𝒰 (𝓝 t₁) :=
      tendsto_map'_iff.1 ((continuous_fst.tendsto (t₁, y₁)).mono_left hle)
    rw [hqz, tendsto_nhds_unique (((hφ z₀ (hqz.symm ▸ hy₁)).tendsto).mono_left hz₀) ht_lim, hty]

namespace NDRPair

/-- If the ambient deformation `I × X → X` of an NDR pair `(X, A)` is proper, then the induced
strong deformation `I × (I × X) → I × X` of the cylinder onto `{0} × X ∪ I × A` is proper. No
separation axiom is needed on `X`. -/
theorem isProperMap_cylinderDeformation {N : NDRPair A} (hN : IsProperMap N.deformation) :
    IsProperMap N.cylinderDeformation := by
  refine (?_ : IsProperMap fun w : I × (I × X) ↦ (N.cylinderDeformation w).2).prodMk_of_t2_left
    N.cylinderDeformation.continuous.fst
  rw [isProperMap_iff_ultrafilter]
  refine ⟨N.cylinderDeformation.continuous.snd, fun 𝒰 x₀ hx₀ ↦ ?_⟩
  obtain ⟨x₁, hx₁, hval⟩ := ultrafilter_tendsto_apply_prodMk_of_fixed hN
    (fun t _ hx ↦ N.deformation_of_mem t hx)
    (fun w hw ↦ continuous_fst.continuousAt.mul
      (N.control.continuousAt_projIcc_div_of_notMem N.control_eq_zero_iff
        (continuous_fst.comp continuous_snd) (continuous_snd.comp continuous_snd) hw))
    (hx₀.congr fun ⟨s, t, x⟩ ↦ N.cylinderDeformation_snd s t x)
  obtain ⟨s₁, -, hs₁⟩ := isCompact_univ.ultrafilter_le_nhds' (𝒰.map Prod.fst) univ_mem
  obtain ⟨t₁, -, ht₁⟩ := isCompact_univ.ultrafilter_le_nhds' (𝒰.map fun w ↦ w.2.1) univ_mem
  have hle : (𝒰 : Filter (I × (I × X))) ≤ 𝓝 (s₁, t₁, x₁) := by
    rw [nhds_prod_eq, nhds_prod_eq, le_prod]
    exact ⟨hs₁, le_prod.2 ⟨tendsto_map'_iff.1 ht₁, tendsto_map'_iff.1 hx₁⟩⟩
  exact ⟨(s₁, t₁, x₁), (cylinderDeformation_snd N s₁ t₁ x₁).trans (hval _ hle rfl), hle⟩

/-- If the deformation of an NDR pair `(X, A)` is proper, then the retraction of `I × X` onto
`{0} × X ∪ I × A` is proper as a map into `I × X`. -/
theorem isProperMap_cylinderRetraction {N : NDRPair A} (hN : IsProperMap N.deformation) :
    IsProperMap ((ContinuousMap.subtypeVal _).comp N.cylinderRetraction) := by
  convert (isProperMap_cylinderDeformation hN).comp (isProperMap_prodMk_left (1 : I)) using 1
  funext z
  exact coe_cylinderRetraction_apply N z

/-- An NDR pair whose ambient deformation is proper has the proper homotopy extension property. -/
theorem hasProperHomotopyExtensionProperty {N : NDRPair A} (hN : IsProperMap N.deformation) :
    HasProperHomotopyExtensionProperty A :=
  hasProperHomotopyExtensionProperty_of_retraction N.isClosed (isProperMap_cylinderRetraction hN)
    (fun z ↦ (N.cylinderRetraction z).2)
    fun z hz ↦ congrArg Subtype.val (N.cylinderRetraction_apply_coe ⟨z, hz⟩)

/-- The NDR pair built by `NDRPair.ofRetraction` from a proper cylinder retraction has a proper
ambient deformation. -/
theorem isProperMap_ofRetraction_deformation {r : C(I × X, I × X)}
    (hr_proper : IsProperMap r) (hr : ∀ p, r p ∈ cylinderExtensionDomain A)
    (hr' : ∀ p ∈ cylinderExtensionDomain A, r p = p) (hA : IsClosed A) :
    IsProperMap (NDRPair.ofRetraction hr hr' hA).deformation := by
  convert (isProperMap_snd_of_compactSpace (X := I)).comp hr_proper using 1
  funext p
  exact ofRetraction_deformation hr hr' hA p

/-- **Proper product of NDR pairs.** If the deformations of two NDR pairs `(X, A)` and `(Y, B)`
are proper, then the deformation of their product NDR pair `(X × Y, A × Y ∪ X × B)` is proper. -/
theorem isProperMap_prod_deformation {Y : Type v} [TopologicalSpace Y] {B : Set Y}
    {N : NDRPair A} {M : NDRPair B} (hN : IsProperMap N.deformation)
    (hM : IsProperMap M.deformation) : IsProperMap (N.prod M).deformation := by
  rw [isProperMap_iff_ultrafilter]
  refine ⟨(N.prod M).deformation.continuous, fun 𝒰 ⟨x₀, y₀⟩ hxy₀ ↦ ?_⟩
  rw [nhds_prod_eq, tendsto_prod_iff'] at hxy₀
  obtain ⟨x₁, hx₁, hxval⟩ := ultrafilter_tendsto_apply_prodMk_of_fixed hN
    (fun t _ hx ↦ N.deformation_of_mem t hx)
    (fun w hw ↦ continuous_fst.continuousAt.mul
      (N.control.continuousAt_projIcc_div_of_notMem N.control_eq_zero_iff
        (M.control.continuous.comp (continuous_snd.comp continuous_snd))
        (continuous_fst.comp continuous_snd) hw))
    (hxy₀.1.congr fun ⟨t, x, y⟩ ↦ congrArg Prod.fst (N.prod_deformation_apply M t x y))
  obtain ⟨y₁, hy₁, hyval⟩ := ultrafilter_tendsto_apply_prodMk_of_fixed hM
    (fun t _ hy ↦ M.deformation_of_mem t hy)
    (fun w hw ↦ continuous_fst.continuousAt.mul
      (M.control.continuousAt_projIcc_div_of_notMem M.control_eq_zero_iff
        (N.control.continuous.comp (continuous_fst.comp continuous_snd))
        (continuous_snd.comp continuous_snd) hw))
    (hxy₀.2.congr fun ⟨t, x, y⟩ ↦ congrArg Prod.snd (N.prod_deformation_apply M t x y))
  obtain ⟨t₁, -, ht₁⟩ := isCompact_univ.ultrafilter_le_nhds' (𝒰.map Prod.fst) univ_mem
  have hle : (𝒰 : Filter (I × (X × Y))) ≤ 𝓝 (t₁, x₁, y₁) := by
    rw [nhds_prod_eq, nhds_prod_eq, le_prod]
    exact ⟨ht₁, le_prod.2 ⟨tendsto_map'_iff.1 hx₁, tendsto_map'_iff.1 hy₁⟩⟩
  refine ⟨(t₁, x₁, y₁), ?_, hle⟩
  rw [prod_deformation_apply]
  exact Prod.ext (hxval _ hle rfl) (hyval _ hle rfl)

end NDRPair

/-- **Proper Strøm characterization.** A subset `A ⊆ X` is closed and has the proper homotopy
extension property if and only if it admits NDR data whose deformation `I × X → X` is proper. -/
theorem exists_proper_ndrPair_iff :
    (∃ N : NDRPair A, IsProperMap N.deformation) ↔
      IsClosed A ∧ HasProperHomotopyExtensionProperty A :=
  ⟨fun ⟨N, hN⟩ ↦ ⟨N.isClosed, N.hasProperHomotopyExtensionProperty hN⟩,
    fun ⟨hA, h⟩ ↦
      let ⟨_, hr_proper, hr, hr'⟩ := h.exists_retraction hA
      ⟨NDRPair.ofRetraction hr hr' hA,
        NDRPair.isProperMap_ofRetraction_deformation hr_proper hr hr' hA⟩⟩

end NDRPair

section Prod

variable {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y]
  {A : Set X} {B : Set Y}

/-- **Proper Strøm product theorem.** If closed subsets `A ⊆ X` and `B ⊆ Y` have the proper
homotopy extension property, then so does `A × Y ∪ X × B ⊆ X × Y`. -/
theorem HasProperHomotopyExtensionProperty.prod_univ_union_univ_prod
    (hA : HasProperHomotopyExtensionProperty A) (hA' : IsClosed A)
    (hB : HasProperHomotopyExtensionProperty B) (hB' : IsClosed B) :
    HasProperHomotopyExtensionProperty (A ×ˢ (univ : Set Y) ∪ (univ : Set X) ×ˢ B) := by
  obtain ⟨N, hN⟩ := exists_proper_ndrPair_iff.2 ⟨hA', hA⟩
  obtain ⟨M, hM⟩ := exists_proper_ndrPair_iff.2 ⟨hB', hB⟩
  exact (N.prod M).hasProperHomotopyExtensionProperty (NDRPair.isProperMap_prod_deformation hN hM)

/-- Taking the product with an arbitrary space preserves the proper homotopy extension property of
a closed subset. -/
theorem HasProperHomotopyExtensionProperty.univ_prod
    (h : HasProperHomotopyExtensionProperty A) (hA : IsClosed A) :
    HasProperHomotopyExtensionProperty ((univ : Set Y) ×ˢ A) := by
  have : HasProperHomotopyExtensionProperty
      ((∅ : Set Y) ×ˢ (univ : Set X) ∪ (univ : Set Y) ×ˢ A) :=
    hasProperHomotopyExtensionProperty_empty.prod_univ_union_univ_prod isClosed_empty h hA
  rwa [empty_prod, empty_union] at this

/-- **Proper homotopy extension on the cylinder boundary.** If a closed subset `A ⊆ X` has the
proper homotopy extension property, then `{0, 1} × X ∪ I × A` has the proper homotopy extension
property in `I × X`. -/
theorem HasProperHomotopyExtensionProperty.zero_one_prod_univ_union_univ_prod
    (h : HasProperHomotopyExtensionProperty A) (hA : IsClosed A) :
    HasProperHomotopyExtensionProperty (({0, 1} : Set I) ×ˢ (univ : Set X) ∪ univ ×ˢ A) :=
  hasProperHomotopyExtensionProperty_zero_one.prod_univ_union_univ_prod (Set.toFinite _).isClosed
    h hA

end Prod

end TauCeti
