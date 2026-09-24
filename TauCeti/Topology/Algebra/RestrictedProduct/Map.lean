/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.Algebra.RestrictedProduct.Basic

/-!
# Componentwise maps of restricted products

A family of coordinate homomorphisms induces a homomorphism of restricted products when it
preserves the reference subgroups at all but finitely many indices. This file records that map,
its continuity and functoriality, the criterion for it to be surjective, and the stronger
everywhere-preserving specialization that maps the everywhere-integral subgroup into the
everywhere-integral subgroup.

The distinction between eventual and everywhere preservation is essential: the final theorem
gives an explicit family for which the eventual map does not preserve the integral subgroup.
The construction is the fixed-index specialization of Mathlib's
`RestrictedProduct.mapAlongMonoidHom`.

## References

* N. Bourbaki, *General Topology*.
* A. Weil, *Basic Number Theory*.
-/

public section

namespace TauCeti

open Filter
open scoped RestrictedProduct

universe u v w z

variable {ι : Type u} {G : ι → Type v}
variable [∀ i, Group (G i)]

/-- The componentwise homomorphism of restricted products induced by a family that eventually
maps each reference subgroup into the corresponding target subgroup. -/
def restrictedProductMap {H : ι → Type w} [∀ i, Group (H i)]
    (U : ∀ i, Subgroup (G i)) (U' : ∀ i, Subgroup (H i))
    (φ : ∀ i, G i →* H i)
    (hφ : ∀ᶠ i in cofinite, Set.MapsTo (φ i) (U i) (U' i)) :
    (Πʳ i, [G i, (U i : Set (G i))]) →*
      (Πʳ i, [H i, (U' i : Set (H i))]) :=
  RestrictedProduct.mapAlongMonoidHom G H id tendsto_id φ hφ

/-- Evaluation of a componentwise restricted-product homomorphism at a coordinate. -/
@[simp]
theorem restrictedProductMap_apply {H : ι → Type w} [∀ i, Group (H i)]
    (U : ∀ i, Subgroup (G i)) (U' : ∀ i, Subgroup (H i))
    (φ : ∀ i, G i →* H i)
    (hφ : ∀ᶠ i in cofinite, Set.MapsTo (φ i) (U i) (U' i))
    (x : Πʳ i, [G i, (U i : Set (G i))]) (i : ι) :
    restrictedProductMap U U' φ hφ x i = φ i (x i) := by
  exact RestrictedProduct.mapAlongMonoidHom_apply G H id tendsto_id φ hφ x i

/-- A componentwise restricted-product homomorphism is continuous when all its coordinate maps
are continuous. -/
theorem continuous_restrictedProductMap {H : ι → Type w} [∀ i, Group (H i)]
    [∀ i, TopologicalSpace (G i)] [∀ i, TopologicalSpace (H i)]
    (U : ∀ i, Subgroup (G i)) (U' : ∀ i, Subgroup (H i))
    (φ : ∀ i, G i →* H i)
    (hφ : ∀ᶠ i in cofinite, Set.MapsTo (φ i) (U i) (U' i))
    (hφcont : ∀ i, Continuous (φ i)) :
    Continuous (restrictedProductMap U U' φ hφ) :=
  RestrictedProduct.mapAlong_continuous G H id tendsto_id
    (fun i ↦ (φ i : G i → H i)) hφ hφcont

/-- The componentwise restricted-product homomorphism when every coordinate map preserves the
reference subgroup. -/
def restrictedProductMapOfForall {H : ι → Type w} [∀ i, Group (H i)]
    (U : ∀ i, Subgroup (G i)) (U' : ∀ i, Subgroup (H i))
    (φ : ∀ i, G i →* H i) (hφ : ∀ i, Set.MapsTo (φ i) (U i) (U' i)) :
    (Πʳ i, [G i, (U i : Set (G i))]) →*
      (Πʳ i, [H i, (U' i : Set (H i))]) :=
  restrictedProductMap U U' φ (.of_forall hφ)

/-- Evaluation of the everywhere-preserving componentwise homomorphism at a coordinate. -/
@[simp]
theorem restrictedProductMapOfForall_apply {H : ι → Type w} [∀ i, Group (H i)]
    (U : ∀ i, Subgroup (G i)) (U' : ∀ i, Subgroup (H i))
    (φ : ∀ i, G i →* H i) (hφ : ∀ i, Set.MapsTo (φ i) (U i) (U' i))
    (x : Πʳ i, [G i, (U i : Set (G i))]) (i : ι) :
    restrictedProductMapOfForall U U' φ hφ x i = φ i (x i) := by
  exact restrictedProductMap_apply U U' φ (.of_forall hφ) x i

/-- The componentwise restricted-product homomorphism induced by identity maps is the identity. -/
@[simp]
theorem restrictedProductMap_id (U : ∀ i, Subgroup (G i)) :
    restrictedProductMap U U (fun i ↦ MonoidHom.id (G i))
        (.of_forall fun _ _ hx ↦ hx) =
      MonoidHom.id (Πʳ i, [G i, (U i : Set (G i))]) := by
  ext x i
  rw [restrictedProductMap_apply, MonoidHom.id_apply, MonoidHom.id_apply]

/-- Componentwise restricted-product homomorphisms compose coordinatewise. -/
@[simp]
theorem restrictedProductMap_comp {H : ι → Type w} {K : ι → Type z}
    [∀ i, Group (H i)] [∀ i, Group (K i)]
    (U : ∀ i, Subgroup (G i)) (U' : ∀ i, Subgroup (H i))
    (U'' : ∀ i, Subgroup (K i))
    (φ : ∀ i, G i →* H i) (ψ : ∀ i, H i →* K i)
    (hφ : ∀ᶠ i in cofinite, Set.MapsTo (φ i) (U i) (U' i))
    (hψ : ∀ᶠ i in cofinite, Set.MapsTo (ψ i) (U' i) (U'' i)) :
    (restrictedProductMap U' U'' ψ hψ).comp (restrictedProductMap U U' φ hφ) =
      restrictedProductMap U U'' (fun i ↦ (ψ i).comp (φ i))
        (by filter_upwards [hφ, hψ] with i hφi hψi
            exact hψi.comp hφi) := by
  ext x i
  rw [MonoidHom.comp_apply, restrictedProductMap_apply, restrictedProductMap_apply,
    restrictedProductMap_apply, MonoidHom.comp_apply]

/-- A componentwise restricted-product homomorphism is surjective exactly when every coordinate
map is surjective and, at all but finitely many indices, the coordinate map carries the source
reference subgroup onto the target one. Surjectivity of each coordinate map alone is not enough:
an element of the target may lie in the target reference subgroups at infinitely many indices
where no preimage lies in the source reference subgroup. -/
@[simp]
theorem restrictedProductMap_surjective_iff {H : ι → Type w} [∀ i, Group (H i)]
    (U : ∀ i, Subgroup (G i)) (U' : ∀ i, Subgroup (H i))
    (φ : ∀ i, G i →* H i)
    (hφ : ∀ᶠ i in cofinite, Set.MapsTo (φ i) (U i) (U' i)) :
    Function.Surjective (restrictedProductMap U U' φ hφ) ↔
      (∀ i, Function.Surjective (φ i)) ∧
        ∀ᶠ i in cofinite, Set.SurjOn (φ i) (U i) (U' i) := by
  classical
  constructor
  · intro h
    refine ⟨fun i z ↦ ?_, ?_⟩
    · -- Hit the element supported at `i` with value `z`.
      obtain ⟨x, hx⟩ := h (RestrictedProduct.mulSingle U' i z)
      refine ⟨x i, ?_⟩
      rw [← restrictedProductMap_apply U U' φ hφ, hx,
        RestrictedProduct.mulSingle_eq_same]
    · -- At each index where `φ j` misses part of `U' j`, pick a missed element; elsewhere pick
      -- `1`. A preimage of the result must leave `U j` at every index of the first kind.
      have hmiss : ∀ j, ∃ z ∈ U' j, ¬ Set.SurjOn (φ j) (U j) (U' j) → z ∉ φ j '' U j := by
        intro j
        by_cases hj : Set.SurjOn (φ j) (U j) (U' j)
        · exact ⟨1, one_mem _, fun h ↦ absurd hj h⟩
        · obtain ⟨z, hz, hz'⟩ := Set.not_subset.mp hj
          exact ⟨z, hz, fun _ ↦ hz'⟩
      choose z hzU hz using hmiss
      obtain ⟨x, hx⟩ := h ⟨z, .of_forall hzU⟩
      filter_upwards [x.2] with j hxj
      by_contra hj
      refine hz j hj ⟨x j, hxj, ?_⟩
      rw [← restrictedProductMap_apply U U' φ hφ, hx, RestrictedProduct.mk_apply]
  · rintro ⟨hsurj, hsurjOn⟩ y
    -- Lift `y i` into `U i` whenever possible, and to an arbitrary preimage otherwise.
    have hlift : ∀ i, ∃ a, φ i a = y i ∧ (y i ∈ φ i '' U i → a ∈ U i) := by
      intro i
      by_cases hi : y i ∈ φ i '' U i
      · obtain ⟨a, ha, hay⟩ := hi
        exact ⟨a, hay, fun _ ↦ ha⟩
      · obtain ⟨a, hay⟩ := hsurj i (y i)
        exact ⟨a, hay, fun h ↦ absurd h hi⟩
    choose x hx hxU using hlift
    refine ⟨⟨x, ?_⟩, ?_⟩
    · filter_upwards [y.2, hsurjOn] with i hyi hi using hxU i (hi hyi)
    · ext i
      exact (restrictedProductMap_apply U U' φ hφ _ i).trans (hx i)

/-- An everywhere-preserving componentwise map sends the integral subgroup into the target
integral subgroup. -/
theorem mapsTo_integralSubgroup_of_forall {H : ι → Type w} [∀ i, Group (H i)]
    (U : ∀ i, Subgroup (G i)) (U' : ∀ i, Subgroup (H i))
    (φ : ∀ i, G i →* H i) (hφ : ∀ i, Set.MapsTo (φ i) (U i) (U' i)) :
    (integralSubgroup U).map (restrictedProductMapOfForall U U' φ hφ) ≤
      integralSubgroup U' := by
  rintro _ ⟨x, hx, rfl⟩
  apply (mem_integralSubgroup U' _).mpr
  exact fun i ↦ hφ i ((mem_integralSubgroup U x).mp hx i)

/-- Eventual preservation of reference subgroups does not imply preservation of the integral
subgroups. The witness uses identity maps on `Multiplicative ℤ`, with the source reference family
everywhere `⊤` and the target reference family equal to `⊥` at zero and `⊤` elsewhere. -/
theorem not_forall_mapsTo_integralSubgroup :
    ¬ ∀ (U U' : ℕ → Subgroup (Multiplicative ℤ))
        (φ : ∀ _ : ℕ, Multiplicative ℤ →* Multiplicative ℤ)
        (hφ : ∀ᶠ i in cofinite, Set.MapsTo (φ i) (U i) (U' i)),
        (integralSubgroup U).map (restrictedProductMap U U' φ hφ) ≤
          integralSubgroup U' := by
  intro h
  let U : ℕ → Subgroup (Multiplicative ℤ) := fun _ ↦ ⊤
  let U' : ℕ → Subgroup (Multiplicative ℤ) := fun i ↦ if i = 0 then ⊥ else ⊤
  let φ : ∀ _ : ℕ, Multiplicative ℤ →* Multiplicative ℤ := fun _ ↦ MonoidHom.id _
  have hφ : ∀ᶠ i in cofinite, Set.MapsTo (φ i) (U i) (U' i) := by
    have hne : ∀ᶠ i : ℕ in cofinite, i ≠ 0 := by simp
    filter_upwards [hne] with i hi
    simp [U, U', φ, hi]
  let x : Πʳ i, [Multiplicative ℤ, (U i : Set (Multiplicative ℤ))] :=
    ⟨fun _ ↦ Multiplicative.ofAdd 1, .of_forall fun i ↦ by simp [U]⟩
  have hx : x ∈ integralSubgroup U := by
    rw [mem_integralSubgroup]
    intro i
    simp [U]
  have himage : restrictedProductMap U U' φ hφ x ∈
      (integralSubgroup U).map (restrictedProductMap U U' φ hφ) :=
    ⟨x, hx, rfl⟩
  have htarget := h U U' φ hφ himage
  have hzero := (mem_integralSubgroup U' _).mp htarget 0
  rw [restrictedProductMap_apply] at hzero
  simp [U', φ, x] at hzero

end TauCeti
