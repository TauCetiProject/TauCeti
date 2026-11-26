/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
public import TauCeti.Algebra.Colimit.CommonStage
import TauCeti.Algebra.Colimit.Ring.Basic
import TauCeti.RingTheory.IntegralClosure.IntegrallyClosed
import TauCeti.RingTheory.Polynomial.ScaleRoots

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
* `TauCeti.isIntegrallyClosed_of_directed`: a directed colimit of integrally closed domains,
  described elementwise, is integrally closed.
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

namespace TauCeti

variable {ι : Type*} [Preorder ι] [IsDirectedOrder ι] {G : ι → Type*} [∀ i, CommRing (G i)]
  {R : Type*} [CommRing R]

/-- **A directed colimit of integrally closed domains is an integrally closed domain**
(`TauCeti.isDomain_of_directed` gives the domain). Here `R` is the colimit of the `G i` along `φ`,
as in `TauCeti.isDomain_of_directed`. -/
theorem isIntegrallyClosed_of_directed (f : ∀ i j, i ≤ j → G i →+* G j)
    (φ : ∀ i, G i →+* R) (hf : ∀ i j h x, φ j (f i j h x) = φ i x)
    (hsurj : ∀ x : R, ∃ i y, φ i y = x) (hker : ∀ i y, φ i y = 0 → ∃ j h, f i j h y = 0)
    [∀ i, IsDomain (G i)] [∀ i, IsIntegrallyClosed (G i)] :
    IsIntegrallyClosed R := by
  classical
  have := isDomain_of_directed f φ hf hsurj hker
  refine (isIntegrallyClosed_iff (FractionRing R)).mpr fun {z} ⟨p, hpm, hp⟩ ↦ ?_
  obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective R z
  have hb' : algebraMap R (FractionRing R) b ≠ 0 :=
    IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hb
  -- The cleared equation `(p.scaleRoots b).eval a = 0` holds in `R`.
  have hrel : (p.scaleRoots b).eval a = 0 := by
    apply IsFractionRing.injective R (FractionRing R)
    rw [← eval₂_at_apply, map_zero]
    exact scaleRoots_eval₂_eq_zero_of_eval₂_div_eq_zero (IsFractionRing.injective R _) hp hb
  -- Lift `a`, `b` and the coefficients of `p` to a common stage `i`.
  obtain ⟨i, g, hg⟩ := DirectLimit.exists_lift (t := fun i j h ↦ f i j h) (φ := fun i ↦ φ i)
    hf hsurj (insert a (insert b p.coeffs))
  obtain ⟨a', rfl⟩ : ∃ a', φ i a' = a := ⟨g a, hg a (by simp)⟩
  obtain ⟨b', rfl⟩ : ∃ b', φ i b' = b := ⟨g b, hg b (by simp)⟩
  have hlifts : p ∈ lifts (φ i) := (lifts_iff_coeff_lifts _).mpr fun n ↦ by
    by_cases h : p.coeff n = 0
    · exact ⟨0, by simp [h]⟩
    · exact ⟨g _, hg _ (by simp [coeff_mem_coeffs h])⟩
  obtain ⟨p', rfl, -, hp'⟩ := lifts_and_degree_eq_and_monic hlifts hpm
  -- The cleared equation holds at a later stage `j`.
  obtain ⟨j, hij, hj⟩ := hker i ((p'.scaleRoots b').eval a') (by
    rw [map_eval_scaleRoots _ (hp'.natDegree_map _), hrel])
  rw [map_eval_scaleRoots _ (hp'.natDegree_map _)] at hj
  -- So `f a'` is divisible by `f b'` in the integrally closed domain `G j`.
  obtain ⟨c, hc⟩ := IsIntegrallyClosed.dvd_of_eval_scaleRoots_eq_zero (hp'.map _) hj
  refine ⟨φ j c, ?_⟩
  rw [eq_div_iff hb', ← map_mul, ← hf i j hij b', ← map_mul, mul_comm, ← hc, hf]

end TauCeti
