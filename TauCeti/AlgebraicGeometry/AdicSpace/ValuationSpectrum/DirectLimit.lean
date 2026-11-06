/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Order.DirectedInverseSystem
public import TauCeti.AlgebraicGeometry.AdicSpace.ValuationSpectrum.OfDirected

/-!
# The valuation spectrum of a directed colimit of rings

Let `(Aᵢ, tᵢⱼ)` be a directed system of commutative rings over a directed preorder `ι`, and let
`φᵢ : Aᵢ → L` be compatible ring homomorphisms (`φⱼ ∘ tᵢⱼ = φᵢ`) exhibiting `L` as the colimit:
every element of `L` comes from some stage, and two elements of a stage with the same image in
`L` become equal at a later stage. This holds for Mathlib's `Ring.DirectLimit` with its
canonical maps.

Then pulling back along the `φᵢ` identifies `Spv L` with the inverse limit of the spaces
`Spv Aᵢ` along the maps `comap tᵢⱼ`, realised as the subspace of compatible families in the
product `∏ᵢ Spv Aᵢ`:

```text
Spv L ≃ₜ {w ∈ ∏ᵢ Spv Aᵢ | comap tᵢⱼ (wⱼ) = wᵢ for all i ≤ j}.
```

The comparison is a topological embedding as soon as every element of `L` comes from some stage
(`TauCeti.ValuationSpectrum.isEmbedding_pi_comap`): two elements of `L` lift to a common stage,
so a point of `Spv L` is determined by its pullbacks, and every basic open `Spv(L)(f/s)` is the
preimage of a basic open of a single stage. Its image is the set of compatible families
(`TauCeti.ValuationSpectrum.range_pi_comap`): a compatible family glues to a point of `Spv L`
by `TauCeti.ValuationSpectrum.ofDirected`, the second colimit condition making the comparison
of two lifts independent of the stage.

This is the valuation-spectrum layer of the description of the adic spectrum of a colimit of
Huber pairs as the inverse limit of the adic spectra of the stages.

## Main results

* `TauCeti.ValuationSpectrum.isEmbedding_pi_comap`: `Spv L → ∏ᵢ Spv Aᵢ` is an embedding.
* `TauCeti.ValuationSpectrum.range_pi_comap`: its image is the set of compatible families.
* `TauCeti.ValuationSpectrum.directLimitHomeomorph`: the resulting homeomorphism of `Spv L`
  onto the compatible families.

## References

* K. S. Kedlaya, R. Liu, *Relative p-adic Hodge theory: foundations*, Astérisque 371 (2015),
  §2.6, Remark 2.6.3.
* T. Wedhorn, *Adic Spaces*, arXiv:1910.05934v1, §7.2, Remark 7.11(1).
-/

public section

namespace TauCeti.ValuationSpectrum

open Topology

variable {ι : Type*} [Preorder ι] {A : ι → Type*} [∀ i, CommRing (A i)]
  {t : ∀ i j, i ≤ j → A i →+* A j} {L : Type*} [CommRing L] {φ : ∀ i, A i →+* L}

/-- Pulling back along `φⱼ` and then along `tᵢⱼ` is pulling back along `φᵢ`. -/
theorem comap_comap_of_comp_eq (hφt : ∀ i j (h : i ≤ j) a, φ j (t i j h a) = φ i a)
    {i j : ι} (h : i ≤ j) (v : Spv L) : comap (t i j h) (comap (φ j) v) = comap (φ i) v := by
  rw [comap_comap]
  exact congrArg (comap · v) (RingHom.ext (hφt i j h))

variable [IsDirectedOrder ι] (hφt : ∀ i j (h : i ≤ j) a, φ j (t i j h a) = φ i a)
  (hcover : ∀ x : L, ∃ i a, φ i a = x)

include hφt hcover in
/-- Finitely many elements of the colimit lift to a common stage. -/
theorem exists_lift (S : Finset L) : ∃ i, ∃ g : L → A i, ∀ x ∈ S, φ i (g x) = x := by
  classical
  induction S using Finset.induction_on with
  | empty =>
    obtain ⟨i, -⟩ := hcover 0
    exact ⟨i, 0, by simp⟩
  | insert a S _ ih =>
    obtain ⟨i, g, hg⟩ := ih
    obtain ⟨j, b, rfl⟩ := hcover a
    obtain ⟨k, hik, hjk⟩ := directed_of (· ≤ ·) i j
    refine ⟨k, fun x ↦ if x = φ j b then t j k hjk b else t i k hik (g x), fun x hx ↦ ?_⟩
    by_cases hxa : x = φ j b
    · simp only [hxa, ↓reduceIte, hφt]
    · simp only [hxa, ↓reduceIte, hφt]
      exact hg x ((Finset.mem_insert.mp hx).resolve_left hxa)

include hφt hcover in
/-- **The valuation spectrum of a colimit embeds into the product of the spectra of the
stages.** If every element of `L` comes from some stage of a directed system with compatible
maps `φᵢ : Aᵢ → L`, then `v ↦ (comap φᵢ v)ᵢ` is a topological embedding
`Spv L → ∏ᵢ Spv Aᵢ`. -/
theorem isEmbedding_pi_comap : IsEmbedding fun (v : Spv L) i ↦ comap (φ i) v := by
  classical
  refine ⟨⟨le_antisymm (continuous_iff_le_induced.mp
    (continuous_pi fun i ↦ continuous_comap (φ i))) ?_⟩, fun v w h ↦ ?_⟩
  · rw [instTopologicalSpace_eq_generateFrom]
    refine le_generateFrom fun U ⟨x, y, hU⟩ ↦ ?_
    obtain ⟨i, g, hg⟩ := exists_lift hφt hcover {x, y}
    obtain ⟨a, b, rfl, rfl⟩ : ∃ a b : A i, φ i a = x ∧ φ i b = y :=
      ⟨g x, g y, hg x (by simp), hg y (by simp)⟩
    refine isOpen_induced_iff.mpr ⟨(fun w : ∀ i, Spv (A i) ↦ w i) ⁻¹' basicOpen a b,
      (isOpen_basicOpen a b).preimage (continuous_apply i), ?_⟩
    rw [hU, ← comap_preimage_basicOpen]
    rfl
  · refine ext' fun x y ↦ ?_
    obtain ⟨i, g, hg⟩ := exists_lift hφt hcover {x, y}
    obtain ⟨a, b, rfl, rfl⟩ : ∃ a b : A i, φ i a = x ∧ φ i b = y :=
      ⟨g x, g y, hg x (by simp), hg y (by simp)⟩
    rw [← comap_vle, ← comap_vle, congr_fun h i]

variable [DirectedSystem A fun i j h ↦ t i j h]
  (hker : ∀ i (a b : A i), φ i a = φ i b → ∃ j, ∃ h : i ≤ j, t i j h a = t i j h b)

include hφt hker in
/-- Two pairs of elements of stages `i` and `j` with the same images in the colimit become equal
at a common later stage. -/
theorem exists_eq_eq_of_eq_eq {i j : ι} {a b : A i} {a' b' : A j}
    (ha : φ i a = φ j a') (hb : φ i b = φ j b') :
    ∃ k, ∃ (hik : i ≤ k) (hjk : j ≤ k),
      t i k hik a = t j k hjk a' ∧ t i k hik b = t j k hjk b' := by
  obtain ⟨k, hik, hjk⟩ := directed_of (· ≤ ·) i j
  have ha' : φ k (t i k hik a) = φ k (t j k hjk a') := by rw [hφt, hφt, ha]
  have hb' : φ k (t i k hik b) = φ k (t j k hjk b') := by rw [hφt, hφt, hb]
  obtain ⟨l, hkl, hal⟩ := hker k _ _ ha'
  obtain ⟨l', hkl', hbl'⟩ := hker k _ _ hb'
  obtain ⟨m, hlm, hl'm⟩ := directed_of (· ≤ ·) l l'
  refine ⟨m, hik.trans (hkl.trans hlm), hjk.trans (hkl.trans hlm), ?_, ?_⟩
  · have := congrArg (t l m hlm) hal
    simp only [DirectedSystem.map_map (f := fun i j h ↦ t i j h)] at this
    exact this
  · have := congrArg (t l' m hl'm) hbl'
    simp only [DirectedSystem.map_map (f := fun i j h ↦ t i j h)] at this
    exact this

include hφt hcover hker in
/-- **The compatible families are exactly the pullbacks of points of the colimit.** For a
directed system `(Aᵢ, tᵢⱼ)` with colimit `L`, the image of `v ↦ (comap φᵢ v)ᵢ` is the set of
families `(wᵢ)` with `comap tᵢⱼ (wⱼ) = wᵢ` for all `i ≤ j`. -/
theorem range_pi_comap :
    Set.range (fun (v : Spv L) i ↦ comap (φ i) v) =
      {w : ∀ i, Spv (A i) | ∀ i j (h : i ≤ j), comap (t i j h) (w j) = w i} := by
  refine Set.Subset.antisymm ?_ fun w hw ↦ ?_
  · rintro _ ⟨v, rfl⟩ i j h
    exact comap_comap_of_comp_eq hφt h v
  have hdir : Directed (· ≤ ·) fun i ↦ (φ i).range := fun i j ↦ by
    obtain ⟨k, hik, hjk⟩ := directed_of (· ≤ ·) i j
    exact ⟨k, fun _ ⟨a, ha⟩ ↦ ⟨t i k hik a, (hφt i k hik a).trans ha⟩,
      fun _ ⟨a, ha⟩ ↦ ⟨t j k hjk a, (hφt j k hjk a).trans ha⟩⟩
  have hcompat : ∀ i j (a b : A i) (a' b' : A j), φ i a = φ j a' → φ i b = φ j b' →
      (w i).toValuativeRel.vle a b → (w j).toValuativeRel.vle a' b' := by
    intro i j a b a' b' ha hb hab
    obtain ⟨k, hik, hjk, hak, hbk⟩ := exists_eq_eq_of_eq_eq hφt hker ha hb
    rw [← hw i k hik, comap_vle, hak, hbk] at hab
    rwa [← hw j k hjk, comap_vle]
  exact ⟨ofDirected φ hcompat hdir fun x ↦ (hcover x).imp fun i ⟨a, ha⟩ ↦ ⟨a, ha⟩,
    funext fun i ↦ comap_ofDirected φ hcompat hdir _ i⟩

/-- **The valuation spectrum of a directed colimit is the inverse limit of the valuation
spectra.** Pulling back along the maps `φᵢ : Aᵢ → L` of a colimit of a directed system of rings
is a homeomorphism of `Spv L` onto the space of compatible families of points of the `Spv Aᵢ`.
-/
noncomputable def directLimitHomeomorph :
    Spv L ≃ₜ {w : ∀ i, Spv (A i) | ∀ i j (h : i ≤ j), comap (t i j h) (w j) = w i} :=
  (isEmbedding_pi_comap hφt hcover).toHomeomorph.trans
    (Homeomorph.setCongr (range_pi_comap hφt hcover hker))

/-- The `i`-th coordinate of `directLimitHomeomorph` is the pullback along `φᵢ`. -/
@[simp]
theorem directLimitHomeomorph_apply_coe (v : Spv L) (i : ι) :
    (directLimitHomeomorph hφt hcover hker v : ∀ i, Spv (A i)) i = comap (φ i) v :=
  (rfl)

/-- The point of `Spv L` glued from a compatible family pulls back to the `i`-th member of the
family along `φᵢ`. -/
@[simp]
theorem comap_directLimitHomeomorph_symm_apply
    (w : {w : ∀ i, Spv (A i) | ∀ i j (h : i ≤ j), comap (t i j h) (w j) = w i}) (i : ι) :
    comap (φ i) ((directLimitHomeomorph hφt hcover hker).symm w) = (w : ∀ i, Spv (A i)) i := by
  rw [← directLimitHomeomorph_apply_coe hφt hcover hker, Homeomorph.apply_symm_apply]

end TauCeti.ValuationSpectrum
