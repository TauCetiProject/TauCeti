/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.GaloisRepresentation.Genericity.DecomposedGeneric
public import TauCeti.NumberTheory.NumberField.Cyclotomic.Frobenius
import TauCeti.NumberTheory.NumberField.Frobenius
import TauCeti.RingTheory.Ideal.Norm.AbsNorm

/-!
# The trace obstruction at a decomposed generic prime

For a pair of characteristic roots, the product of the two forbidden differences
`α - qβ` and `β - qα` is symmetric. Expressing it in terms of trace and determinant
tests genericity in the coefficient field, including when the roots coincide.

For a residual representation with cyclotomic or inverse cyclotomic determinant,
this gives a restriction on the primes witnessing decomposed genericity. If
`tr(g)² = (1 + det(g))²` for every image element outside the determinant kernel,
every witness is congruent to one modulo the residual characteristic. This is the
trace condition in the auxiliary-prime argument of Caraiani and Newton,
*On the modularity of elliptic curves over imaginary quadratic fields*, proof of
Theorem 5.2, and Darmon, Diamond and Taylor, *Fermat's Last Theorem*, Lemma 4.11.
-/

public section

open NumberField Ideal Matrix

/-- Suppose the determinant is the cyclotomic character or its inverse, and the trace
identity holds away from its kernel. Every decomposed generic witness `q` is congruent to
one modulo `ℓ`. The finite Galois field of definition contains the chosen primitive root
so that both characters can be compared on the same group. -/
theorem MonoidHom.IsDecomposedGenericPrime.modEq_one_of_trace_sq_eq
    {F L k : Type*} [Field F] [NumberField F] [Field L] [NumberField L]
    [Algebra F L] [IsGalois F L] {ℓ : ℕ} [Fact ℓ.Prime] [Field k] [Algebra (ZMod ℓ) k]
    {r : Gal(L/F) →* GL (Fin 2) k} {q : ℕ} (hq : r.IsDecomposedGenericPrime q)
    {ζ : L} (hζ : IsPrimitiveRoot ζ ℓ)
    (hdet : (∀ σ, (r σ).val.det = algebraMap (ZMod ℓ) k (hζ.autToPow F σ : ZMod ℓ)) ∨
      (∀ σ, (r σ).val.det = algebraMap (ZMod ℓ) k (hζ.autToPow F σ⁻¹ : ZMod ℓ)))
    (htr : ∀ σ, (r σ).val.det ≠ 1 → (r σ).val.trace ^ 2 = (1 + (r σ).val.det) ^ 2) :
    q ≡ 1 [MOD ℓ] := by
  have : Fact q.Prime := ⟨hq.prime⟩
  obtain ⟨Q, hQ⟩ : ((span {(q : ℤ)}).primesOver (𝓞 L)).Nonempty :=
    Set.nonempty_coe_sort.mp inferInstance
  have := hQ.1
  have := hQ.2
  have hq0 : span {(q : ℤ)} ≠ ⊥ := by simpa using hq.prime.ne_zero
  have hQ0 := ne_bot_of_liesOver_of_ne_bot hq0 Q
  obtain ⟨σ, hσ⟩ := exists_isArithFrobAt F Q hQ0
  let P : IsDedekindDomain.HeightOneSpectrum (𝓞 F) :=
    ⟨Q.under (𝓞 F), inferInstance, Ideal.IsIntegral.under_ne_bot _ hQ0⟩
  have : Q.LiesOver P.asIdeal := Ideal.over_under Q
  have hnorm := hq.absNorm_eq (Q.under (𝓞 F))
  have hne : q ≠ ℓ := by
    rintro rfl
    exact hq.natCast_ne_zero (by rw [← map_natCast (algebraMap (ZMod q) k), ZMod.natCast_self,
      map_zero])
  have hℓ : (ℓ : 𝓞 F) ∉ P.asIdeal := natCast_notMem_of_coprime_absNorm P.isPrime.ne_top
    (hnorm ▸ (Nat.coprime_primes Fact.out hq.prime).mpr hne.symm)
  have hχ : (hζ.autToPow F σ : ZMod ℓ) = q := (hσ.autToPow_eq_absNorm hζ P hℓ Q).trans
    (congrArg (Nat.cast : ℕ → ZMod ℓ) hnorm)
  have hg := hq.isGenericAt Q hσ
  obtain ⟨τ, hτ, hd⟩ : ∃ τ, r.IsGenericAt (Q.inertia Gal(L/F)) τ q ∧ (r τ).val.det = q := by
    rcases hdet with h | h
    · exact ⟨σ, hg, by rw [h, hχ, map_natCast]⟩
    · exact ⟨σ⁻¹, isGenericAt_inv_iff.mpr hg, by rw [h, inv_inv, hχ, map_natCast]⟩
  have hgen := ((r τ).val.isGenericAt_iff_of_card_eq_two (by simp) q).mp
    (MonoidHom.isGenericAt_iff.mp hτ).2
  have hq1 : (q : k) = 1 := by
    by_contra hne
    rw [htr τ (hd.trans_ne hne), hd, mul_comm] at hgen
    exact hgen rfl
  apply (ZMod.natCast_eq_natCast_iff ..).mp
  apply (algebraMap (ZMod ℓ) k).injective
  simpa using hq1
