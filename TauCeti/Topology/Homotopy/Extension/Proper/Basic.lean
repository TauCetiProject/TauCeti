/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Maps.Proper.Basic
public import TauCeti.Topology.Homotopy.Extension.Basic
import TauCeti.Topology.Maps.Proper.Basic

/-!
# The proper homotopy extension property

A subset `A` of a topological space `X` has the *proper homotopy extension property*
(`TauCeti.HasProperHomotopyExtensionProperty`) when every proper homotopy `H : I × A → Y` whose
initial slice extends to a proper map `f : X → Y` extends to a homotopy `K : I × X → Y` that is
proper on the whole cylinder `I × X`.

For a closed subset `A ⊆ X` (equivalently, when the subspace inclusion `A → X` is proper,
`TauCeti.isProperMap_subtypeVal_iff`), the property has the same geometric characterization as in
the unproper theory, with properness added to the retraction: `A` has the proper homotopy extension
property if and only if `{0} × X ∪ I × A` (`TauCeti.cylinderExtensionDomain A`) is a *proper*
retract of `I × X` (`TauCeti.hasProperHomotopyExtensionProperty_iff_exists_proper_retraction`).
This universal retraction characterization makes the property universe-polymorphic in the target `Y`
(`TauCeti.HasProperHomotopyExtensionProperty.exists_extension_of_isClosed`), shows that closed
proper cofibrations are in particular ordinary cofibrations
(`TauCeti.HasProperHomotopyExtensionProperty.hasHomotopyExtensionProperty`), and shows that on a
compact Hausdorff ambient space `X` the proper and ordinary homotopy extension properties coincide
for closed subsets
(`TauCeti.hasProperHomotopyExtensionProperty_iff_hasHomotopyExtensionProperty`).

Closedness of `A` is genuinely needed in the retraction characterization: if `X` is compact and
`A ⊆ X` is noncompact (for instance `(0, 1] ⊆ I`), then no pair of proper maps `f : X → Y` and
`H : I × A → Y` can agree on `{0} × A` (since `H ⁻¹' (range f)` would be compact and contain the
closed copy `{0} × A` of `A`), making `HasProperHomotopyExtensionProperty A` hold vacuously even
when `{0} × X ∪ I × A` is not a retract of `I × X`.

## Main declarations

* `TauCeti.HasProperHomotopyExtensionProperty`: the proper homotopy extension property of `A ⊆ X`,
  with `TauCeti.hasProperHomotopyExtensionProperty_iff` and
  `TauCeti.HasProperHomotopyExtensionProperty.exists_extension`.
* `TauCeti.hasProperHomotopyExtensionProperty_iff_exists_proper_retraction`: **a closed subset has
  the proper homotopy extension property if and only if `{0} × X ∪ I × A` is a proper retract of
  `I × X`.**
* `TauCeti.HasProperHomotopyExtensionProperty.exists_extension_of_isClosed` and
  `TauCeti.HasProperHomotopyExtensionProperty.exists_homotopy_of_restrict`: cross-universe proper
  homotopy extension for closed subsets.
* `IsClopen.hasProperHomotopyExtensionProperty`,
  `TauCeti.hasProperHomotopyExtensionProperty_empty`,
  `TauCeti.hasProperHomotopyExtensionProperty_univ`: clopen subsets (in particular `∅` and `univ`)
  have the proper homotopy extension property.
* `TauCeti.hasProperHomotopyExtensionProperty_iff_hasHomotopyExtensionProperty`: on a compact
  Hausdorff space, proper and ordinary homotopy extension agree for closed subsets.
* `TauCeti.HasProperHomotopyExtensionProperty.image`,
  `TauCeti.HasProperHomotopyExtensionProperty.image_of_isClosed`, and
  `TauCeti.HasProperHomotopyExtensionProperty.image_of_isClosedEmbedding`: transport along
  homeomorphisms and composition of proper cofibrations along closed embeddings.

## References

* F. T. Farrell, L. R. Taylor, J. B. Wagoner, *The Whitehead theorem in the proper category*,
  Compositio Math. 27 (1973), 1–23, §1 (Theorem 1.6).
* A. Hatcher, *Algebraic Topology*, Cambridge University Press, 2002, Chapter 0 ("The Homotopy
  Extension Property").
-/

public section

namespace TauCeti

open Set Topology unitInterval

universe u u' v

variable {X : Type u} [TopologicalSpace X] {A : Set X}

/-- A subset `A` of `X` has the *proper homotopy extension property* when every proper map
`f : C(X, Y)` and proper homotopy `H : C(I × A, Y)` agreeing on `{0} × A` admit a proper
extension `K : C(I × X, Y)`.

Only targets `Y` in the universe of `X` are quantified over in the definition; for closed `A`,
`TauCeti.HasProperHomotopyExtensionProperty.exists_extension_of_isClosed` upgrades this to targets
in any universe. -/
def HasProperHomotopyExtensionProperty (A : Set X) : Prop :=
  ∀ {Y : Type u} [TopologicalSpace Y] (f : C(X, Y)), IsProperMap f →
    ∀ (H : C(I × A, Y)), IsProperMap H → (∀ a : A, H (0, a) = f a) →
      ∃ K : C(I × X, Y), IsProperMap K ∧ (∀ x, K (0, x) = f x) ∧
        ∀ (t : I) (a : A), K (t, a) = H (t, a)

/-- Unfolding of `TauCeti.HasProperHomotopyExtensionProperty`. -/
theorem hasProperHomotopyExtensionProperty_iff :
    HasProperHomotopyExtensionProperty A ↔
      ∀ {Y : Type u} [TopologicalSpace Y] (f : C(X, Y)), IsProperMap f →
        ∀ (H : C(I × A, Y)), IsProperMap H → (∀ a : A, H (0, a) = f a) →
          ∃ K : C(I × X, Y), IsProperMap K ∧ (∀ x, K (0, x) = f x) ∧
            ∀ (t : I) (a : A), K (t, a) = H (t, a) :=
  (Iff.rfl)

/-- Applying the proper homotopy extension property to proper initial data `(f, H)`. -/
theorem HasProperHomotopyExtensionProperty.exists_extension
    (h : HasProperHomotopyExtensionProperty A) {Y : Type u} [TopologicalSpace Y]
    (f : C(X, Y)) (hf : IsProperMap f) (H : C(I × A, Y)) (hH : IsProperMap H)
    (h0 : ∀ a : A, H (0, a) = f a) :
    ∃ K : C(I × X, Y), IsProperMap K ∧ (∀ x, K (0, x) = f x) ∧
      ∀ (t : I) (a : A), K (t, a) = H (t, a) :=
  h f hf H hH h0

/-- A proper retraction of `I × X` onto `{0} × X ∪ I × A` solves every proper homotopy extension
problem for `A ⊆ X`, with values in a space in any universe. Closedness of `A` follows
automatically from properness of `r`. -/
theorem exists_proper_homotopy_extension_of_retraction {Y : Type v} [TopologicalSpace Y]
    {r : C(I × X, I × X)} (hrp : IsProperMap r)
    (hr : ∀ p, r p ∈ cylinderExtensionDomain A)
    (hr' : ∀ p ∈ cylinderExtensionDomain A, r p = p)
    (f : C(X, Y)) (hf : IsProperMap f) (H : C(I × A, Y)) (hH : IsProperMap H)
    (h0 : ∀ a : A, H (0, a) = f a) :
    ∃ K : C(I × X, Y), IsProperMap K ∧ (∀ x, K (0, x) = f x) ∧
      ∀ (t : I) (a : A), K (t, a) = H (t, a) := by
  classical
  -- Closedness of `{0} × X ∪ I × A` and of `A` follows from properness of the retraction `r`.
  have hrange : range r = cylinderExtensionDomain A := by
    ext q
    exact ⟨fun ⟨p, hp⟩ ↦ hp ▸ hr p, fun hq ↦ ⟨q, hr' q hq⟩⟩
  have hdom : IsClosed (cylinderExtensionDomain A) := hrange ▸ hrp.isClosed_range
  have hA : IsClosed A := by
    have hpre : (Prod.mk (1 : I)) ⁻¹' cylinderExtensionDomain A = A := by
      ext x
      simp [mem_cylinderExtensionDomain_iff]
    exact hpre ▸ hdom.preimage (.prodMk_right 1)
  -- Glue `f` and `H` on `J = {0} × X ∪ I × A`; the bottom slice and wall form a closed cover of `J`
  -- on which the glued map restricts to proper maps.
  let g₀ : cylinderExtensionDomain A → Y := fun q ↦
    if h : q.val.2 ∈ A then H (q.val.1, ⟨q.val.2, h⟩) else f q.val.2
  let C₀ : Set (cylinderExtensionDomain A) := {q | q.val.1 = 0}
  let C₁ : Set (cylinderExtensionDomain A) := {q | q.val.2 ∈ A}
  have hC₀ : IsClosed C₀ := (isClosed_singleton (x := (0 : I))).preimage (by fun_prop)
  have hC₁ : IsClosed C₁ := hA.preimage (by fun_prop)
  have hcov : C₀ ∪ C₁ = univ := eq_univ_of_forall fun q ↦ mem_cylinderExtensionDomain_iff.1
      q.property
  have hinc : IsProperMap ((↑) : cylinderExtensionDomain A → I × X) := hdom.isProperMap_subtypeVal
  have hg₀ : IsProperMap g₀ := by
    rw [hC₀.isProperMap_iff_domRestrict_of_union_eq_univ hC₁ hcov]
    refine ⟨?_, ?_⟩
    · have h₀ : C₀.domRestrict g₀ = (f ∘ Prod.snd) ∘ C₀.domRestrict Subtype.val := by
        funext ⟨q, hq⟩
        have hq0 : q.val.1 = 0 := hq
        by_cases hx : q.val.2 ∈ A <;> simp [g₀, hq0, hx, h0]
      rw [h₀]
      exact (hf.comp isProperMap_snd_of_compactSpace).comp (hinc.restrict hC₀)
    · let φ : C₁ → I × A := fun q ↦ (q.val.val.1, ⟨q.val.val.2, q.property⟩)
      have hφ_comp : Prod.map id Subtype.val ∘ φ = C₁.domRestrict Subtype.val := by
        funext q
        simp [φ]
      have hφ : IsProperMap φ :=
        isProperMap_of_comp_of_inj (by fun_prop) (continuous_id.prodMap continuous_subtypeVal)
          (hφ_comp ▸ hinc.restrict hC₁) (Function.injective_id.prodMap Subtype.val_injective)
      have h₁ : C₁.domRestrict g₀ = H ∘ φ := by
        funext ⟨q, hq⟩
        have hx : q.val.2 ∈ A := hq
        simp [g₀, φ, hx]
      rw [h₁]
      exact hH.comp hφ
  let r₀ : I × X → cylinderExtensionDomain A := fun p ↦ ⟨r p, hr p⟩
  have hr₀ : IsProperMap r₀ :=
    isProperMap_of_comp_of_inj (r.continuous.subtype_mk hr) continuous_subtypeVal hrp
      Subtype.val_injective
  refine ⟨⟨g₀ ∘ r₀, hg₀.continuous.comp hr₀.continuous⟩, hg₀.comp hr₀, fun x ↦ ?_, fun t a ↦ ?_⟩
  · by_cases hx : x ∈ A <;>
      simp [g₀, r₀, hr' _ (zero_mem_cylinderExtensionDomain x), hx, h0]
  · simp [g₀, r₀, hr' _ (mem_cylinderExtensionDomain_of_mem a.property), a.property]

/-- A subset onto whose cylinder extension domain the cylinder properly retracts has the proper
homotopy extension property. -/
theorem hasProperHomotopyExtensionProperty_of_retraction {r : C(I × X, I × X)}
    (hrp : IsProperMap r) (hr : ∀ p, r p ∈ cylinderExtensionDomain A)
    (hr' : ∀ p ∈ cylinderExtensionDomain A, r p = p) :
    HasProperHomotopyExtensionProperty A :=
  fun f hf H hH h0 ↦ exists_proper_homotopy_extension_of_retraction hrp hr hr' f hf H hH h0

/-- Every clopen subset has the proper homotopy extension property. -/
theorem _root_.IsClopen.hasProperHomotopyExtensionProperty (hA : IsClopen A) :
    HasProperHomotopyExtensionProperty A := by
  classical
  -- Collapse `I × Aᶜ` to `{0} × Aᶜ` while fixing `I × A`; each clopen piece is proper.
  let r : I × X → I × X := fun p ↦ if p.2 ∈ A then p else ((0 : I), p.2)
  let s : Set (I × X) := {p | p.2 ∈ A}
  let t : Set (I × X) := {p | p.2 ∈ Aᶜ}
  have hs : IsClosed s := hA.isClosed.preimage continuous_snd
  have ht : IsClosed t := hA.compl.isClosed.preimage continuous_snd
  have hst : s ∪ t = univ := by ext p; simp [s, t, em]
  have hrp : IsProperMap r := by
    rw [hs.isProperMap_iff_domRestrict_of_union_eq_univ ht hst]
    refine ⟨?_, ?_⟩
    · have h₀ : s.domRestrict r = Subtype.val := by
        funext p
        have hp : p.val.2 ∈ A := p.property
        simp [r, hp]
      rw [h₀]
      exact hs.isProperMap_subtypeVal
    · have h₁ : t.domRestrict r = t.domRestrict (Prod.mk (0 : I) ∘ Prod.snd) := by
        funext p
        have hp : p.val.2 ∉ A := p.property
        simp [r, hp]
      rw [h₁]
      exact ((isProperMap_prodMk_left (0 : I)).comp isProperMap_snd_of_compactSpace).restrict ht
  apply hasProperHomotopyExtensionProperty_of_retraction (r := ⟨r, hrp.continuous⟩) hrp
  · intro p
    by_cases h : p.2 ∈ A <;> simp [r, h, mem_cylinderExtensionDomain_iff]
  · rintro ⟨u, x⟩ hp
    rcases mem_cylinderExtensionDomain_iff.1 hp with rfl | hx
    · by_cases h : x ∈ A <;> simp [r, h]
    · simp [r, hx]

/-- The empty subset has the proper homotopy extension property. -/
theorem hasProperHomotopyExtensionProperty_empty :
    HasProperHomotopyExtensionProperty (∅ : Set X) :=
  isClopen_empty.hasProperHomotopyExtensionProperty

/-- The whole space has the proper homotopy extension property. -/
theorem hasProperHomotopyExtensionProperty_univ :
    HasProperHomotopyExtensionProperty (univ : Set X) :=
  isClopen_univ.hasProperHomotopyExtensionProperty

/-- If a closed subset `A ⊆ X` has the proper homotopy extension property, then `I × X` admits a
proper retraction onto `{0} × X ∪ I × A`. -/
theorem HasProperHomotopyExtensionProperty.exists_proper_retraction
    (h : HasProperHomotopyExtensionProperty A) (hA : IsClosed A) :
    ∃ r : C(I × X, I × X), IsProperMap r ∧ (∀ p, r p ∈ cylinderExtensionDomain A) ∧
      ∀ p ∈ cylinderExtensionDomain A, r p = p := by
  -- Extend the tautological inclusions of `X` and `I × A` into `{0} × X ∪ I × A`.
  let f₀ : C(X, cylinderExtensionDomain A) :=
    ⟨fun x ↦ ⟨((0 : I), x), zero_mem_cylinderExtensionDomain x⟩, by fun_prop⟩
  let H₀ : C(I × A, cylinderExtensionDomain A) :=
    ⟨fun q ↦ ⟨(q.1, q.2.val), mem_cylinderExtensionDomain_of_mem q.2.property⟩, by fun_prop⟩
  have hf₀_comp : Subtype.val ∘ (f₀ : X → cylinderExtensionDomain A) = Prod.mk (0 : I) := by
    funext x
    simp [f₀]
  have hf₀ : IsProperMap f₀ :=
    isProperMap_of_comp_of_inj f₀.continuous continuous_subtypeVal
      (hf₀_comp ▸ isProperMap_prodMk_left (0 : I)) Subtype.val_injective
  have hH₀_comp : Subtype.val ∘ (H₀ : I × A → cylinderExtensionDomain A) =
      Prod.map id Subtype.val := by
    funext ⟨t, a⟩
    simp [H₀]
  have hH₀ : IsProperMap H₀ :=
    isProperMap_of_comp_of_inj H₀.continuous continuous_subtypeVal
      (hH₀_comp ▸ isProperMap_id.prodMap hA.isProperMap_subtypeVal) Subtype.val_injective
  obtain ⟨K, hKp, hK₀, hK₁⟩ := h.exists_extension f₀ hf₀ H₀ hH₀ fun _ ↦ rfl
  refine ⟨⟨fun p ↦ (K p : I × X), continuous_subtypeVal.comp K.continuous⟩,
    (isClosed_cylinderExtensionDomain hA).isProperMap_subtypeVal.comp hKp, fun p ↦ (K p).property,
        ?_⟩
  rintro ⟨t, x⟩ htx
  rcases mem_cylinderExtensionDomain_iff.1 htx with rfl | hx
  · exact congrArg Subtype.val (hK₀ x)
  · exact congrArg Subtype.val (hK₁ t ⟨x, hx⟩)

/-- **A closed subset has the proper homotopy extension property if and only if `{0} × X ∪ I × A`
is a proper retract of `I × X`.** -/
theorem hasProperHomotopyExtensionProperty_iff_exists_proper_retraction (hA : IsClosed A) :
    HasProperHomotopyExtensionProperty A ↔
      ∃ r : C(I × X, I × X), IsProperMap r ∧ (∀ p, r p ∈ cylinderExtensionDomain A) ∧
        ∀ p ∈ cylinderExtensionDomain A, r p = p :=
  ⟨fun h ↦ h.exists_proper_retraction hA,
    fun ⟨_, hrp, hr, hr'⟩ ↦ hasProperHomotopyExtensionProperty_of_retraction hrp hr hr'⟩

/-- For a closed subset, the proper homotopy extension property extends proper homotopies with
values in a space in any universe. -/
theorem HasProperHomotopyExtensionProperty.exists_extension_of_isClosed (hA : IsClosed A)
    (h : HasProperHomotopyExtensionProperty A) {Y : Type v} [TopologicalSpace Y]
    (f : C(X, Y)) (hf : IsProperMap f) (H : C(I × A, Y)) (hH : IsProperMap H)
    (h0 : ∀ a : A, H (0, a) = f a) :
    ∃ K : C(I × X, Y), IsProperMap K ∧ (∀ x, K (0, x) = f x) ∧
      ∀ (t : I) (a : A), K (t, a) = H (t, a) :=
  let ⟨_, hrp, hr, hr'⟩ := h.exists_proper_retraction hA
  exists_proper_homotopy_extension_of_retraction hrp hr hr' f hf H hH h0

/-- Bundled proper homotopy extension for a closed subset `A ⊆ X`: a proper homotopy starting at
`f.restrict A` extends to a proper homotopy starting at `f`, with target in any universe. -/
theorem HasProperHomotopyExtensionProperty.exists_homotopy_of_restrict (hA : IsClosed A)
    (h : HasProperHomotopyExtensionProperty A) {Y : Type v} [TopologicalSpace Y]
    (f : C(X, Y)) (hf : IsProperMap f) {g : C(A, Y)}
    (H : (f.restrict A).Homotopy g) (hH : IsProperMap H) :
    ∃ (f' : C(X, Y)) (K : f.Homotopy f'), IsProperMap K ∧
      ∀ (t : I) (a : A), K (t, a) = H (t, a) := by
  obtain ⟨K, hKp, hK₀, hK₁⟩ :=
    h.exists_extension_of_isClosed hA f hf H.toContinuousMap hH fun a ↦
      (H.apply_zero a).trans (f.restrict_apply A a)
  exact ⟨⟨fun x ↦ K (1, x), by fun_prop⟩,
    { toContinuousMap := K, map_zero_left := hK₀, map_one_left := fun _ ↦ rfl }, hKp, hK₁⟩

/-- A closed subset with the proper homotopy extension property also has the ordinary homotopy
extension property. -/
theorem HasProperHomotopyExtensionProperty.hasHomotopyExtensionProperty
    (h : HasProperHomotopyExtensionProperty A) (hA : IsClosed A) :
    HasHomotopyExtensionProperty A :=
  let ⟨_, _, hr, hr'⟩ := h.exists_proper_retraction hA
  hasHomotopyExtensionProperty_of_retraction hA hr hr'

/-- On a compact Hausdorff space, every subset with the ordinary homotopy extension property also
has the proper homotopy extension property. -/
theorem HasHomotopyExtensionProperty.hasProperHomotopyExtensionProperty
    [CompactSpace X] [T2Space X] (h : HasHomotopyExtensionProperty A) :
    HasProperHomotopyExtensionProperty A :=
  let ⟨r, hr, hr'⟩ := h.exists_retraction
  hasProperHomotopyExtensionProperty_of_retraction r.continuous.isProperMap hr hr'

/-- On a compact Hausdorff space, the proper and ordinary homotopy extension properties coincide
for closed subsets. -/
theorem hasProperHomotopyExtensionProperty_iff_hasHomotopyExtensionProperty
    [CompactSpace X] [T2Space X] (hA : IsClosed A) :
    HasProperHomotopyExtensionProperty A ↔ HasHomotopyExtensionProperty A :=
  ⟨fun h ↦ h.hasHomotopyExtensionProperty hA, fun h ↦ h.hasProperHomotopyExtensionProperty⟩

/-- **Proper cofibrations compose along closed embeddings.** If `j : X → X'` is a closed embedding
whose range has the proper homotopy extension property in `X'`, and `A` has the proper homotopy
extension property in `X`, then `j '' A` has the proper homotopy extension property in `X'`. -/
theorem HasProperHomotopyExtensionProperty.image_of_isClosedEmbedding
    {X' : Type u} [TopologicalSpace X'] (h : HasProperHomotopyExtensionProperty A) {j : X → X'}
    (hj : IsClosedEmbedding j) (hj' : HasProperHomotopyExtensionProperty (range j)) :
    HasProperHomotopyExtensionProperty (j '' A) := by
  intro Y _ f hf H hH h0
  let eA : A ≃ₜ ↥(j '' A) := hj.isEmbedding.homeomorphImage A
  have heA : ∀ a : A, (eA a : X') = j a := fun a ↦ by
    simp [eA, IsEmbedding.homeomorphImage, Homeomorph.setCongr]
  obtain ⟨K, hKp, hK₀, hK₁⟩ :=
    h (f.comp ⟨j, hj.continuous⟩) (hf.comp hj.isProperMap)
      (H.comp ((Homeomorph.refl I).prodCongr eA))
      (hH.comp ((Homeomorph.refl I).prodCongr eA).isProperMap)
      fun a ↦ by simpa [heA] using h0 (eA a)
  let ej : X ≃ₜ ↥(range j) := hj.isEmbedding.toHomeomorph
  obtain ⟨K', hK'p, hK'₀, hK'₁⟩ :=
    hj' f hf (K.comp ((Homeomorph.refl I).prodCongr ej.symm))
      (hKp.comp ((Homeomorph.refl I).prodCongr ej.symm).isProperMap)
      fun y ↦ by
        obtain ⟨_, x, rfl⟩ := y
        simpa [ej] using hK₀ x
  refine ⟨K', hK'p, hK'₀, fun t b ↦ ?_⟩
  obtain ⟨_, a, ha, rfl⟩ := b
  rw [hK'₁ t ⟨j a, mem_range_self a⟩]
  have hK_eq : (K.comp ((Homeomorph.refl I).prodCongr ej.symm : C(I × ↥(range j), I × X)))
      (t, (⟨j a, mem_range_self a⟩ : ↥(range j))) = K (t, a) := by
    simp [ej]
  rw [hK_eq, hK₁ t ⟨a, ha⟩]
  simp only [ContinuousMap.comp_apply, ContinuousMap.coe_ofClass, Homeomorph.coe_prodCongr,
    Prod.map_apply, Homeomorph.refl_apply]
  exact congrArg (fun z ↦ H (t, z)) (Subtype.ext (heA ⟨a, ha⟩))

/-- The proper homotopy extension property transports along a homeomorphism within the same
universe, with no closedness assumption on `A`. -/
theorem HasProperHomotopyExtensionProperty.image {X' : Type u} [TopologicalSpace X']
    (h : HasProperHomotopyExtensionProperty A) (e : X ≃ₜ X') :
    HasProperHomotopyExtensionProperty (e '' A) :=
  h.image_of_isClosedEmbedding e.isClosedEmbedding
    (e.range_coe.symm ▸ hasProperHomotopyExtensionProperty_univ)

/-- For a closed subset, the proper homotopy extension property transports along a homeomorphism
into a space in any universe. -/
theorem HasProperHomotopyExtensionProperty.image_of_isClosed {X' : Type u'} [TopologicalSpace X']
    (h : HasProperHomotopyExtensionProperty A) (e : X ≃ₜ X') (hA : IsClosed A) :
    HasProperHomotopyExtensionProperty (e '' A) := by
  obtain ⟨r, hrp, hr, hr'⟩ := h.exists_proper_retraction hA
  let E : I × X ≃ₜ I × X' := (Homeomorph.refl I).prodCongr e
  apply hasProperHomotopyExtensionProperty_of_retraction
    (r := ((E : C(I × X, I × X')).comp r).comp E.symm)
    (E.isProperMap.comp (hrp.comp E.symm.isProperMap))
  · intro q
    rw [mem_cylinderExtensionDomain_iff]
    rcases mem_cylinderExtensionDomain_iff.1 (hr (q.1, e.symm q.2)) with h0 | hmem
    · exact Or.inl h0
    · exact Or.inr (mem_image_of_mem e hmem)
  · rintro ⟨t, x'⟩ hq
    have hq' : (t, e.symm x') ∈ cylinderExtensionDomain A := by
      rw [mem_cylinderExtensionDomain_iff] at hq ⊢
      rcases hq with h0 | ⟨a, ha, rfl⟩
      · exact Or.inl h0
      · exact Or.inr (by simpa using ha)
    simp [E, hr' _ hq']

end TauCeti
