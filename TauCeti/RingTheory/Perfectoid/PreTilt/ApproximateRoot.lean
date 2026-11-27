/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.IntegralClosure.AbsolutelyIntegrallyClosed
public import TauCeti.RingTheory.Perfectoid.Untilt

/-!
# Approximate roots in the tilt

Let `A` be a `p`-adically complete ring in which `p` is not a unit, with tilt
`A♭ = PreTilt A p = lim_{x ↦ x ^ p} A ⧸ p`, and suppose that every monic polynomial of positive
degree over `A ⧸ p` has a root, as when `A` is the valuation ring `O_C` of an algebraically closed
nonarchimedean field. Then every monic polynomial `Q` of positive degree over `A♭` has roots up
to arbitrarily high powers of `p` after untilting: for every `m` there is `x ∈ A♭` with
`p ^ m ∣ Q(x)♯`.

The zeroth coordinate `A♭ → A ⧸ p` is a surjective ring homomorphism, so a root of the reduction
of `Q` in `A ⧸ p` lifts to `y ∈ A♭` with `p ∣ Q(y)♯`. Applying this to the Frobenius twist
`Q' = φ^(-n)(Q)` and raising the resulting approximate root to the power `p ^ n` gives
`p ^ (p ^ n) ∣ Q(y ^ p ^ n)♯`, since the untilt is multiplicative.

For `A = O_C` this is the first half of the proof that the tilt `O♭` is absolutely integrally
closed (`PreTilt.instIsAbsolutelyIntegrallyClosed`): when the discriminant of `Q` is nonzero,
Hensel's lemma turns a sufficiently good approximate root into a root.

## Main results

* `PreTilt.exists_pow_dvd_untilt_eval`: monic polynomials of positive degree over `A♭` have roots
  modulo every power of `p` after untilting.

## References

* O. Brinon, B. Conrad, *CMI Summer School notes on `p`-adic Hodge theory*, §4.3.
-/

public section

open Ideal Polynomial TauCeti

namespace PreTilt

variable {A : Type*} [CommRing A] {p : ℕ} [hp : Fact p.Prime] [Fact ¬IsUnit (p : A)]
  [IsAdicComplete (span {(p : A)}) A]

/-- **Approximate roots in the tilt.** If every monic polynomial of positive degree over `A ⧸ p`
has a root, then for every monic polynomial `Q` of positive degree over `A♭ = PreTilt A p` and
every `m` there is `x ∈ A♭` such that `p ^ m` divides the untilt `Q(x)♯`. -/
theorem exists_pow_dvd_untilt_eval [IsAbsolutelyIntegrallyClosed (ModP A p)]
    {Q : (PreTilt A p)[X]} (hQ : Q.Monic) (hdeg : 0 < Q.natDegree) (m : ℕ) :
    ∃ x, (p : A) ^ m ∣ (Q.eval x).untilt := by
  -- Write `Q = Q'.map F` for the Frobenius power `F = (· ^ p ^ m)`.
  set F := iterateFrobeniusEquiv (PreTilt A p) p m
  set Q' := Q.map (F.symm : PreTilt A p →+* PreTilt A p)
  have hQ' : Q'.Monic := hQ.map _
  have hQQ' : Q'.map (F : PreTilt A p →+* PreTilt A p) = Q := by
    rw [Polynomial.map_map]
    simp
  -- A root of the reduction of `Q'` modulo `p` lifts along the surjective zeroth coordinate.
  have hfrob : Function.Surjective (frobenius (ModP A p) p) := fun x ↦
    (IsAbsolutelyIntegrallyClosed.exists_pow_nat_eq x hp.out.pos).imp fun y hy ↦ by
      rw [frobenius_def, hy]
  obtain ⟨z, hz⟩ := IsAbsolutelyIntegrallyClosed.exists_root (Q'.map (coeff 0)) (hQ'.map _)
    (by rwa [hQ'.natDegree_map, natDegree_map_eq_of_injective F.symm.injective])
  obtain ⟨y, rfl⟩ : ∃ y : PreTilt A p, coeff 0 y = z := Perfection.coeff_surjective hfrob 0 z
  have hpy : (p : A) ∣ (Q'.eval y).untilt := by
    rw [← mem_span_singleton, ← Ideal.Quotient.eq_zero_iff_mem, mk_untilt_eq_coeff_zero,
      ← eval_map_apply]
    exact hz
  -- Then `Q(F y) = F (Q'(y)) = Q'(y) ^ p ^ m`, whose untilt is divisible by `p ^ p ^ m`.
  have hev : Q.eval (F y) = F (Q'.eval y) := by
    rw [← hQQ']
    exact eval_map_apply (p := Q') (f := (F : PreTilt A p →+* PreTilt A p)) y
  refine ⟨F y, ?_⟩
  rw [hev, iterateFrobeniusEquiv_apply, iterateFrobenius_def, map_pow]
  exact (pow_dvd_pow _ (Nat.lt_pow_self hp.out.one_lt).le).trans (pow_dvd_pow_of_dvd hpy _)

end PreTilt
