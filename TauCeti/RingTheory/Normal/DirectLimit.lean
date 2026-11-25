/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Colimit.Ring
public import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
import Mathlib.RingTheory.Polynomial.RationalRoot
import TauCeti.Algebra.Colimit.Ring.Basic
import TauCeti.RingTheory.IntegralClosure.DirectLimit

/-!
# Directed colimits of normal rings

A ring `R` is *normal* when its localization at every prime is an integrally closed domain
(Stacks, Definition 10.37.11 (00GV)); this is the condition
`∀ p [p.IsPrime], IsDomain (Localization.AtPrime p) ∧ IsIntegrallyClosed (Localization.AtPrime p)`,
which `TauCeti.AlgebraicGeometry.isNormalScheme_Spec_iff_forall_localization` identifies with the
normality of `Spec R`. This file shows that a directed colimit of normal rings is normal
(Stacks, Lemma 10.37.17 (037D)). No Noetherian hypothesis is made.

The colimit is described elementwise: ring maps `φ i : G i →+* R` compatible with the transition
maps `f i j`, such that every element of `R` comes from some `G i`, and an element of `G i` sent
to `0` in `R` is sent to `0` in some `G j`. For a nonempty directed system, Mathlib's
`Ring.DirectLimit` is such a colimit, and so is a ring that is the directed union of subrings. For
an empty index set the direct limit is `ℤ` (`Ring.DirectLimit.ringEquivIntOfIsEmpty`).

For a prime `P` of `R` with preimages `P_i` in `G i`, the local ring `R_P` is again such a colimit
of the local rings `(G i)_{P_i}`. A relation `a * b = 0` in a colimit of domains holds at some
stage, where one factor vanishes; and if `a / b` satisfies a monic equation over a colimit of
integrally closed domains, the cleared equation `aⁿ + c₁ aⁿ⁻¹ b + ⋯ + cₙ bⁿ = 0` holds at some
stage `j`, where `b` is nonzero, so `a = c * b` already in `G j`. These two steps are
`TauCeti.isDomain_of_directed` (in `TauCeti/Algebra/Colimit/Ring/Basic.lean`) and
`TauCeti.isIntegrallyClosed_of_directed` (in `TauCeti/RingTheory/IntegralClosure/DirectLimit.lean`).

## Main results

* `TauCeti.forall_isDomain_and_isIntegrallyClosed_of_directed`: a directed colimit of normal rings
  is normal (Stacks, Lemma 10.37.17 (037D)).
* `TauCeti.forall_isDomain_and_isIntegrallyClosed_directLimit`: the same for
  `Ring.DirectLimit`.

## References

* [Stacks Project, Definition 10.37.11](https://stacks.math.columbia.edu/tag/00GV) and
  [Lemma 10.37.17](https://stacks.math.columbia.edu/tag/037D).
-/

public section

namespace TauCeti

variable {ι : Type*} [Preorder ι] [IsDirectedOrder ι] {G : ι → Type*} [∀ i, CommRing (G i)]
  {R : Type*} [CommRing R]

/-- **A directed colimit of normal rings is normal**: if every localization of every `G i` at a
prime is an integrally closed domain, then so is every localization of `R` at a prime. Here `R` is
the colimit of the directed system `(G i, f)` along `φ`: every element of `R` comes from some
`G i`, and an element of `G i` sent to `0` in `R` is sent to `0` in some `G j`. No Noetherian
hypothesis is made. Stacks, Lemma 10.37.17 (037D). -/
@[stacks 037D]
theorem forall_isDomain_and_isIntegrallyClosed_of_directed (f : ∀ i j, i ≤ j → G i →+* G j)
    [DirectedSystem G fun i j h ↦ f i j h] (φ : ∀ i, G i →+* R)
    (hf : ∀ i j h x, φ j (f i j h x) = φ i x) (hsurj : ∀ x : R, ∃ i y, φ i y = x)
    (hker : ∀ i y, φ i y = 0 → ∃ j h, f i j h y = 0)
    (hG : ∀ i (p : Ideal (G i)) [p.IsPrime],
      IsDomain (Localization.AtPrime p) ∧ IsIntegrallyClosed (Localization.AtPrime p))
    (P : Ideal R) [P.IsPrime] :
    IsDomain (Localization.AtPrime P) ∧ IsIntegrallyClosed (Localization.AtPrime P) := by
  classical
  have hff : ∀ i j k (hij : i ≤ j) (hjk : j ≤ k) x,
      f j k hjk (f i j hij x) = f i k (hij.trans hjk) x := fun i j k hij hjk x ↦
    DirectedSystem.map_map (f := fun i j h ↦ f i j h) hij hjk x
  have hcomap : ∀ i j h, P.comap (φ i) = (P.comap (φ j)).comap (f i j h) := by
    intro i j h
    ext x
    simp [hf]
  have : ∀ i, IsDomain (Localization.AtPrime (P.comap (φ i))) := fun i ↦ (hG i _).1
  have : ∀ i, IsIntegrallyClosed (Localization.AtPrime (P.comap (φ i))) := fun i ↦ (hG i _).2
  let g i j h : Localization.AtPrime (P.comap (φ i)) →+* Localization.AtPrime (P.comap (φ j)) :=
    Localization.localRingHom _ _ (f i j h) (hcomap i j h)
  let ψ i : Localization.AtPrime (P.comap (φ i)) →+* Localization.AtPrime P :=
    Localization.localRingHom _ P (φ i) rfl
  have hψ : ∀ i j h x, ψ j (g i j h x) = ψ i x := by
    intro i j h x
    have hcomp : (φ j).comp (f i j h) = φ i := RingHom.ext (hf i j h)
    rw [← RingHom.comp_apply, ← Localization.localRingHom_comp _ _ _ _ (hcomap i j h) _ rfl]
    simp only [ψ, hcomp]
  have hsurj' : ∀ z, ∃ i y, ψ i y = z := by
    intro z
    obtain ⟨⟨x, s⟩, rfl⟩ := IsLocalization.mk'_surjective P.primeCompl z
    obtain ⟨i, g, hg⟩ := DirectLimit.exists_lift (t := fun i j h ↦ f i j h) (φ := fun i ↦ φ i)
      hf hsurj {x, (s : R)}
    obtain ⟨x', hx'⟩ : ∃ x', φ i x' = x := ⟨g x, hg x (by simp)⟩
    obtain ⟨s', hs'⟩ : ∃ s', φ i s' = s := ⟨g s, hg s (by simp)⟩
    have hs : s' ∈ (P.comap (φ i)).primeCompl := by
      simpa [Ideal.primeCompl, hs'] using s.property
    refine ⟨i, IsLocalization.mk' _ x' ⟨s', hs⟩, ?_⟩
    simp only [ψ, Localization.localRingHom_mk']
    congr 1
    exact Subtype.ext hs'
  have hker' : ∀ i y, ψ i y = 0 → ∃ j h, g i j h y = 0 := by
    intro i y hy
    obtain ⟨⟨y, t⟩, rfl⟩ := IsLocalization.mk'_surjective (P.comap (φ i)).primeCompl y
    rw [Localization.localRingHom_mk', IsLocalization.mk'_eq_zero_iff] at hy
    obtain ⟨⟨m, hm⟩, hmy⟩ := hy
    obtain ⟨i', m', rfl⟩ := hsurj m
    obtain ⟨k, hik, hi'k⟩ := exists_ge_ge i i'
    obtain ⟨j, hkj, hj⟩ := hker k (f i' k hi'k m' * f i k hik y) (by simp [hf, hmy])
    refine ⟨j, hik.trans hkj, ?_⟩
    rw [Localization.localRingHom_mk', IsLocalization.mk'_eq_zero_iff]
    refine ⟨⟨f i' j (hi'k.trans hkj) m', by simpa [Ideal.primeCompl, hf] using hm⟩, ?_⟩
    rwa [map_mul, hff, hff] at hj
  exact ⟨isDomain_of_directed g ψ hψ hsurj' hker',
    isIntegrallyClosed_of_directed g ψ hψ hsurj' hker'⟩

/-- **The direct limit of a directed system of normal rings is normal**: if every localization of
every `G i` at a prime is an integrally closed domain, then so is every localization of
`Ring.DirectLimit G f` at a prime. Stacks, Lemma 10.37.17 (037D). -/
@[stacks 037D]
theorem forall_isDomain_and_isIntegrallyClosed_directLimit
    (f : ∀ i j, i ≤ j → G i →+* G j) [DirectedSystem G fun i j h ↦ f i j h]
    (hG : ∀ i (p : Ideal (G i)) [p.IsPrime],
      IsDomain (Localization.AtPrime p) ∧ IsIntegrallyClosed (Localization.AtPrime p))
    (P : Ideal (Ring.DirectLimit G fun i j h ↦ f i j h)) [P.IsPrime] :
    IsDomain (Localization.AtPrime P) ∧ IsIntegrallyClosed (Localization.AtPrime P) := by
  cases isEmpty_or_nonempty ι
  · let e := Ring.DirectLimit.ringEquivIntOfIsEmpty f
    have : IsDomain (Ring.DirectLimit G fun i j h ↦ f i j h) := e.symm.toMulEquiv.isDomain _
    have : IsIntegrallyClosed (Ring.DirectLimit G fun i j h ↦ f i j h) := .of_equiv e
    exact ⟨IsLocalization.isDomain_localization P.primeCompl_le_nonZeroDivisors,
      isIntegrallyClosed_of_isLocalization _ _ P.primeCompl_le_nonZeroDivisors⟩
  · exact forall_isDomain_and_isIntegrallyClosed_of_directed f (Ring.DirectLimit.of G _)
      (fun _ _ _ _ ↦ Ring.DirectLimit.of_f ..) Ring.DirectLimit.exists_of
      (fun _ _ ↦ Ring.DirectLimit.of.zero_exact) hG P

end TauCeti
