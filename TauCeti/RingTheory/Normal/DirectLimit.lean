/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Colimit.Ring
public import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
public import Mathlib.RingTheory.Localization.AtPrime.Basic
import Mathlib.Algebra.Polynomial.Lifts
import Mathlib.RingTheory.Int.Basic
import Mathlib.RingTheory.Polynomial.RationalRoot
import Mathlib.RingTheory.Polynomial.ScaleRoots

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
to `0` in `R` is sent to `0` in some `G j`. Mathlib's `Ring.DirectLimit` is such a colimit, and so
is a ring that is the directed union of subrings.

For a prime `P` of `R` with preimages `P_i` in `G i`, the local ring `R_P` is again such a colimit
of the local rings `(G i)_{P_i}`. A relation `a * b = 0` in a colimit of domains holds at some
stage, where one factor vanishes; and if `a / b` satisfies a monic equation over a colimit of
integrally closed domains, the cleared equation `aⁿ + c₁ aⁿ⁻¹ b + ⋯ + cₙ bⁿ = 0` holds at some
stage `j`, where `b` is nonzero, so `a = c * b` already in `G j`.

## Main results

* `TauCeti.isDomain_of_directed`: a directed colimit of domains is a domain.
* `TauCeti.isIntegrallyClosed_of_directed`: a directed colimit of integrally closed domains is
  integrally closed.
* `TauCeti.forall_isDomain_and_isIntegrallyClosed_of_directed`: a directed colimit of normal rings
  is normal (Stacks, Lemma 10.37.17 (037D)).
* `TauCeti.forall_isDomain_and_isIntegrallyClosed_directLimit`: the same for
  `Ring.DirectLimit`.

## References

* [Stacks Project, Definition 10.37.11](https://stacks.math.columbia.edu/tag/00GV) and
  [Lemma 10.37.17](https://stacks.math.columbia.edu/tag/037D).
-/

public section

open Polynomial

namespace TauCeti

variable {ι : Type*} [Preorder ι] [IsDirectedOrder ι] {G : ι → Type*} [∀ i, CommRing (G i)]
  {R : Type*} [CommRing R]

/-- In a directed colimit, finitely many elements come from a common stage. -/
private theorem exists_forall_exists_eq (f : ∀ i j, i ≤ j → G i →+* G j)
    (φ : ∀ i, G i →+* R) (hf : ∀ i j h x, φ j (f i j h x) = φ i x)
    (hsurj : ∀ x : R, ∃ i y, φ i y = x) (s : Finset R) :
    ∃ i, ∀ x ∈ s, ∃ y, φ i y = x := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    obtain ⟨i, -⟩ := hsurj 0
    exact ⟨i, by simp⟩
  | insert a s _ ih =>
    obtain ⟨i, hi⟩ := ih
    obtain ⟨i', y, rfl⟩ := hsurj a
    obtain ⟨j, hij, hi'j⟩ := exists_ge_ge i i'
    refine ⟨j, fun x hx ↦ ?_⟩
    rcases Finset.mem_insert.mp hx with rfl | hx
    · exact ⟨f i' j hi'j y, hf ..⟩
    · obtain ⟨z, rfl⟩ := hi x hx
      exact ⟨f i j hij z, hf ..⟩

/-- **A directed colimit of domains is a domain.** Here `R` is the colimit of
the `G i` along `φ`: every element of `R` comes from some `G i`, and an element of `G i` sent to
`0` in `R` is sent to `0` in some `G j`. -/
theorem isDomain_of_directed (f : ∀ i j, i ≤ j → G i →+* G j) (φ : ∀ i, G i →+* R)
    (hf : ∀ i j h x, φ j (f i j h x) = φ i x) (hsurj : ∀ x : R, ∃ i y, φ i y = x)
    (hker : ∀ i y, φ i y = 0 → ∃ j h, f i j h y = 0) [∀ i, IsDomain (G i)] :
    IsDomain R := by
  classical
  -- `1 ≠ 0` in `R`: otherwise `1` would vanish in some domain `G j`.
  have : Nontrivial R := by
    refine ⟨0, 1, fun h ↦ ?_⟩
    obtain ⟨i, -⟩ := hsurj 0
    obtain ⟨j, hij, hj⟩ := hker i 1 (by rw [map_one, h])
    exact one_ne_zero (by rwa [map_one] at hj)
  have : NoZeroDivisors R := ⟨fun {a b} hab ↦ by
    obtain ⟨i, hi⟩ := exists_forall_exists_eq f φ hf hsurj {a, b}
    obtain ⟨x, rfl⟩ := hi a (by simp)
    obtain ⟨y, rfl⟩ := hi b (by simp)
    obtain ⟨j, hij, h⟩ := hker i (x * y) (by rw [map_mul, hab])
    rw [map_mul, mul_eq_zero] at h
    rw [← hf i j hij x, ← hf i j hij y]
    exact h.imp (fun h ↦ by rw [h, map_zero]) fun h ↦ by rw [h, map_zero]⟩
  exact NoZeroDivisors.to_isDomain R

/-- A ring map `φ` with nontrivial target sends the evaluation of `p.scaleRoots b` at `a`, for a
monic `p`, to the evaluation of `(p.map φ).scaleRoots (φ b)` at `φ a`. -/
private theorem map_eval_scaleRoots {S T : Type*} [CommRing S] [CommRing T] [Nontrivial T]
    (φ : S →+* T) {p : S[X]} (hp : p.Monic) (a b : S) :
    φ ((p.scaleRoots b).eval a) = ((p.map φ).scaleRoots (φ b)).eval (φ a) := by
  rw [← map_scaleRoots _ _ _ (by simp [hp.leadingCoeff]), eval_map, eval₂_at_apply]

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
    have := scaleRoots_eval₂_eq_zero (algebraMap R (FractionRing R)) (s := b) hp
    rwa [mul_div_cancel₀ _ hb', eval₂_at_apply, ← map_zero (algebraMap R _)] at this
  -- Lift `a`, `b` and the coefficients of `p` to a common stage `i`.
  obtain ⟨i, hi⟩ := exists_forall_exists_eq f φ hf hsurj (insert a (insert b p.coeffs))
  obtain ⟨a', rfl⟩ := hi a (by simp)
  obtain ⟨b', rfl⟩ := hi b (by simp)
  have hlifts : p ∈ lifts (φ i) := (lifts_iff_coeff_lifts _).mpr fun n ↦ by
    by_cases h : p.coeff n = 0
    · exact ⟨0, by simp [h]⟩
    · exact hi _ (by simp [coeff_mem_coeffs h])
  obtain ⟨p', rfl, -, hp'⟩ := lifts_and_degree_eq_and_monic hlifts hpm
  -- The cleared equation holds at a later stage `j`.
  obtain ⟨j, hij, hj⟩ := hker i ((p'.scaleRoots b').eval a') (by
    rw [map_eval_scaleRoots _ hp', hrel])
  rw [map_eval_scaleRoots _ hp'] at hj
  set A := f i j hij a'
  set B := f i j hij b'
  set q := p'.map (f i j hij)
  have hB : algebraMap (G j) (FractionRing (G j)) B ≠ 0 := by
    refine (map_ne_zero_iff _ (IsFractionRing.injective _ _)).mpr fun h ↦ ?_
    have : φ i b' = 0 := by rw [← hf i j hij b']; exact (congrArg (φ j) h).trans (map_zero _)
    exact nonZeroDivisors.ne_zero hb this
  -- So `A / B` is integral over `G j`, hence `A = c * B` for some `c` in `G j`.
  have hint : IsIntegral (G j) (algebraMap (G j) (FractionRing (G j)) A /
      algebraMap (G j) (FractionRing (G j)) B) := by
    refine ⟨q, hp'.map _, ?_⟩
    have := scaleRoots_eval₂_mul (p := q) (algebraMap (G j) (FractionRing (G j)))
      (algebraMap (G j) (FractionRing (G j)) A / algebraMap (G j) (FractionRing (G j)) B) B
    rw [mul_div_cancel₀ _ hB, eval₂_at_apply, hj, map_zero, eq_comm, mul_eq_zero] at this
    exact this.resolve_left (pow_ne_zero _ hB)
  obtain ⟨c, hc⟩ := IsIntegrallyClosed.isIntegral_iff.mp hint
  have hcB : c * B = A := by
    apply IsFractionRing.injective (G j) (FractionRing (G j))
    rw [map_mul, hc, div_mul_cancel₀ _ hB]
  refine ⟨φ j c, ?_⟩
  rw [eq_div_iff hb', ← map_mul, ← hf i j hij b', ← map_mul, hcB, hf]

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
    obtain ⟨⟨y, t⟩, rfl⟩ := IsLocalization.mk'_surjective (P.comap (φ i)).primeCompl x
    simp only [ψ, g, Localization.localRingHom_mk']
    congr 1 <;> simp [hf]
  have hsurj' : ∀ z, ∃ i y, ψ i y = z := by
    intro z
    obtain ⟨⟨x, s⟩, rfl⟩ := IsLocalization.mk'_surjective P.primeCompl z
    obtain ⟨i, hi⟩ := exists_forall_exists_eq f φ hf hsurj {x, (s : R)}
    obtain ⟨x', hx'⟩ := hi x (by simp)
    obtain ⟨s', hs'⟩ := hi s (by simp)
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

omit [IsDirectedOrder ι] in
/-- Over an empty index set, `Ring.DirectLimit G f` is `ℤ`. -/
private theorem isDomain_and_isIntegrallyClosed_directLimit_of_isEmpty [IsEmpty ι]
    (f : ∀ i j, i ≤ j → G i →+* G j) :
    IsDomain (Ring.DirectLimit G fun i j h ↦ f i j h) ∧
      IsIntegrallyClosed (Ring.DirectLimit G fun i j h ↦ f i j h) := by
  let g : Ring.DirectLimit G (fun i j h ↦ f i j h) →+* ℤ :=
    Ring.DirectLimit.lift G _ ℤ (fun i ↦ isEmptyElim i) fun i ↦ isEmptyElim i
  let e : ℤ ≃+* Ring.DirectLimit G fun i j h ↦ f i j h :=
    RingEquiv.ofRingHom (Int.castRingHom _) g
      (Ring.DirectLimit.hom_ext (h := fun i ↦ isEmptyElim i)) (RingHom.ext_int _ _)
  exact ⟨e.symm.toMulEquiv.isDomain _, IsIntegrallyClosed.of_equiv e⟩

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
  · obtain ⟨_, _⟩ := isDomain_and_isIntegrallyClosed_directLimit_of_isEmpty f
    exact ⟨IsLocalization.isDomain_localization P.primeCompl_le_nonZeroDivisors,
      isIntegrallyClosed_of_isLocalization _ _ P.primeCompl_le_nonZeroDivisors⟩
  · exact forall_isDomain_and_isIntegrallyClosed_of_directed f (Ring.DirectLimit.of G _)
      (fun _ _ _ _ ↦ Ring.DirectLimit.of_f ..) Ring.DirectLimit.exists_of
      (fun _ _ ↦ Ring.DirectLimit.of.zero_exact) hG P

end TauCeti
