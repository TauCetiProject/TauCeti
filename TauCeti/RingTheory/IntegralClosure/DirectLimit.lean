/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Polynomial.Lifts
public import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
public import TauCeti.Algebra.Colimit.CommonStage

/-!
# Integral closedness in a directed colimit of rings

Let `(Aᵢ, tᵢⱼ)` be a directed system of commutative rings with compatible maps `φᵢ : Aᵢ → L`
exhibiting `L` as its colimit, and let `Sᵢ ⊆ Aᵢ` be subrings carried into one another by the
transition maps. If every `Sᵢ` is integrally closed in `Aᵢ`, then the union `S` of the images of
the `Sᵢ` is integrally closed in `L`: an integral equation over `S` involves finitely many
coefficients, so it comes from a monic polynomial over some `Sⱼ`, and it holds at a later stage.

This is used to show that the colimit of the plus rings of a directed system of Huber pairs is
integrally closed.

## Main results

* `TauCeti.DirectLimit.isIntegrallyClosedIn`: the colimit of integrally closed subrings is
  integrally closed in the colimit.
-/

public section

open Polynomial

namespace TauCeti.DirectLimit

variable {ι : Type*} [Preorder ι] [IsDirectedOrder ι] {A : ι → Type*} [∀ i, CommRing (A i)]
  {t : ∀ i j, i ≤ j → A i →+* A j} {L : Type*} [CommRing L] {φ : ∀ i, A i →+* L}

/-- **A directed colimit of integrally closed subrings is integrally closed.** Let `L` be the
colimit of a directed system of rings `(Aᵢ, tᵢⱼ)`, let `Sᵢ ⊆ Aᵢ` be subrings integrally closed in
`Aᵢ` and preserved by the transition maps, and let `S ⊆ L` be the union of the images of the
`Sᵢ`. Then `S` is integrally closed in `L`. -/
theorem isIntegrallyClosedIn
    (hφt : ∀ i j (h : i ≤ j) a, φ j (t i j h a) = φ i a) (hcover : ∀ x : L, ∃ i a, φ i a = x)
    (hker : ∀ i (a b : A i), φ i a = φ i b → ∃ j, ∃ h : i ≤ j, t i j h a = t i j h b)
    (S : ∀ i, Subring (A i)) [∀ i, IsIntegrallyClosedIn (S i) (A i)]
    (htS : ∀ i j (h : i ≤ j), ∀ a ∈ S i, t i j h a ∈ S j) {T : Subring L}
    (hφS : ∀ i, ∀ a ∈ S i, φ i a ∈ T) (hT : ∀ x ∈ T, ∃ i, ∃ a ∈ S i, φ i a = x) :
    IsIntegrallyClosedIn T L := by
  classical
  have : Nonempty ι := ⟨(hcover 0).choose⟩
  refine Subring.isIntegrallyClosedIn_iff.mpr fun x ⟨p, hpm, hp⟩ ↦ ?_
  -- lift the coefficients of `p` into a common `Sⱼ` and `x` to a common stage `k ≥ j`
  obtain ⟨j, g, hg⟩ := exists_lift_mem hφt (fun i ↦ (S i : Set (A i))) htS
    ((p.map T.subtype).support.image (p.map T.subtype).coeff) fun y hy ↦ by
      obtain ⟨n, -, rfl⟩ := Finset.mem_image.mp hy
      simpa using hT _ (p.coeff n).property
  obtain ⟨i, b, rfl⟩ := hcover x
  obtain ⟨k, hjk, hik⟩ := directed_of (· ≤ ·) j i
  let f : S k →+* L := (φ k).comp (S k).subtype
  have hlifts : p.map T.subtype ∈ lifts f := by
    refine (lifts_iff_coeff_lifts _).mpr fun n ↦ ?_
    by_cases hn : n ∈ (p.map T.subtype).support
    · obtain ⟨hgS, hgφ⟩ := hg _ (Finset.mem_image_of_mem _ hn)
      exact ⟨⟨_, htS j k hjk _ hgS⟩, by simpa [f, hφt] using hgφ⟩
    · exact ⟨0, by simp [f, notMem_support_iff.mp hn]⟩
  obtain ⟨q, hq, -, hqm⟩ := lifts_and_natDegree_eq_and_monic hlifts (hpm.map _)
  -- the lifted equation holds in `L`, hence at a later stage `m`
  have hroot : φ k ((q.eval₂ (S k).subtype (t i k hik b))) = φ k 0 := by
    rw [hom_eval₂, hφt, map_zero, ← eval_map, hq, eval_map, ← hp, Algebra.algebraMap_ofSubring]
  obtain ⟨m, hkm, hm⟩ := hker k _ _ hroot
  let r : S k →+* S m := (t k m hkm).restrict (S k) (S m) (htS k m hkm)
  have hint : IsIntegral (S m) (t k m hkm (t i k hik b)) := by
    refine ⟨q.map r, hqm.map r, ?_⟩
    have hr : (S m).subtype.comp r = (t k m hkm).comp (S k).subtype :=
      RingHom.ext fun _ ↦ by simp [r]
    rw [Algebra.algebraMap_ofSubring, eval₂_map, hr, ← hom_eval₂, hm, map_zero]
  simpa [hφt] using hφS m _ (Subring.isIntegrallyClosedIn_iff.mp inferInstance hint)

end TauCeti.DirectLimit
