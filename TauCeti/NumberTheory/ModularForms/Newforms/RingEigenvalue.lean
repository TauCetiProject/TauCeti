/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.ModularForms.HeckeSlash.Nebentypus.Scalar
public import TauCeti.NumberTheory.ModularForms.Newforms.Newform

/-!
# The eigenvalue system of a good Hecke eigenform

The eigenvalues of a good Hecke eigenform `f` (`EigenformAwayFromLevel`) inherit the
multiplication table of the `Γ₀(N)` Hecke ring: they are multiplicative on coprime indices, and
along the powers of a good prime `p` they satisfy the Diamond–Shurman recurrence
`λ_{p^{r+2}} = λ_p λ_{p^{r+1}} − χ(p) p^{k−1} λ_{p^r}`, because the scalar coset `T(p, p)` acts on
the character space by `χ(p) p^{k−2}`. Nothing here touches Fourier coefficients: the three
identities `eigenvalue_one`, `eigenvalue_mul` and `eigenvalue_prime_pow_add_two` are images of
relations in the ring under `heckeRingHomCuspCharSpace`, evaluated on the (nonzero) form; the
remaining statements are consequences (a congruence in the index, the prime-square instance, and
the cancellation argument below).

These identities are what the strong-multiplicity-one argument consumes: they let the eigenvalues
at composite good indices be read off the eigenvalues at good primes and the character.

## Main results

* `HeckeRing.GL2.EigenformAwayFromLevel.eigenvalue_one`: `λ₁ = 1`.
* `HeckeRing.GL2.EigenformAwayFromLevel.eigenvalue_mul`: `λ_{mn} = λ_m λ_n` for coprime good
  indices.
* `HeckeRing.GL2.EigenformAwayFromLevel.eigenvalue_prime_pow_add_two`: the recurrence along the
  powers of a good prime, and its first instance
  `HeckeRing.GL2.EigenformAwayFromLevel.eigenvalue_prime_sq`.

The statements build the coprimality proofs guarding `eigenvalue` from their hypotheses
(`Nat.coprime_mul_iff_left`, `Nat.Coprime.pow_left`, cast along the coercion lemmas of `ℕ+`); by
proof irrelevance they rewrite whichever proof a consumer holds, and `eigenvalue_congr` moves
between spellings of an index.

## Provenance

The multiplicativity and the prime-square identity appear as
`Eigenform.coeff_eq_coeff_one_mul_eigenvalue` and `eigenvalue_at_prime_sq_of_coeff_one_ne_zero`
in the AINTLIB `LeanModularForms` project
(`LeanModularForms/StrongMultiplicityOne/ConstantMultiple.lean`, Chris Birkbeck, commit
`2baa76f742bdb4fb8ee323fabba41203bd390e08`, Apache-2.0,
<https://github.com/CBirkbeck/AINTLIB/tree/main/projects/LeanModularForms>), derived there from
the Fourier coefficients of a normalised eigenform. Here both are read off the Hecke ring
instead, so no normalisation and no coefficient formula is needed.

## References

* [F. Diamond and J. Shurman, *A first course in modular forms*][diamondshurman2005], §5.8.
* [T. Miyake, *Modular forms*][miyake1989], §4.6.
-/

public section


namespace HeckeRing.GL2.EigenformAwayFromLevel

variable {N : ℕ} [NeZero N] {k : ℤ} (f : EigenformAwayFromLevel N k)

/-- The form, as a nonzero vector of its character space. -/
private theorem mk_ne_zero :
    (⟨f.toCuspForm, f.mem_charSpace⟩ : cuspFormCharSpace k f.χ) ≠ 0 :=
  fun h ↦ f.ne_zero (congrArg Subtype.val h)

/-- Two scalars acting alike on the form are equal. -/
private theorem eq_of_smul_eq {a b : ℂ}
    (h : a • (⟨f.toCuspForm, f.mem_charSpace⟩ : cuspFormCharSpace k f.χ) =
      b • (⟨f.toCuspForm, f.mem_charSpace⟩ : cuspFormCharSpace k f.χ)) : a = b :=
  smul_left_injective ℂ f.mk_ne_zero h

/-- The eigenvalue depends only on the index, not on the coprimality proof or on how the index
is spelled. -/
theorem eigenvalue_congr {m n : ℕ+} (hmn : m = n) {hm : Nat.Coprime m N} {hn : Nat.Coprime n N} :
    f.eigenvalue m hm = f.eigenvalue n hn := by
  subst hmn
  rfl

/-- The eigenvalue at `1` is `1`: the ring element at index `1` is the identity. -/
@[simp]
theorem eigenvalue_one : f.eigenvalue 1 (Nat.coprime_one_left N) = 1 := by
  refine f.eq_of_smul_eq ?_
  rw [← f.isEigen 1 (Nat.coprime_one_left N), PNat.one_coe, heckeTCompositeGamma0_one, map_one,
    Module.End.one_apply, one_smul]

/-- **Multiplicativity on coprime good indices**: `λ_{mn} = λ_m λ_n`, the image of the coprime
multiplication rule `heckeTCompositeGamma0_mul_of_coprime` of the Hecke ring. -/
theorem eigenvalue_mul {m n : ℕ+} (hmn : Nat.Coprime m n) (hm : Nat.Coprime m N)
    (hn : Nat.Coprime n N) :
    f.eigenvalue (m * n) (PNat.mul_coe m n ▸ Nat.coprime_mul_iff_left.mpr ⟨hm, hn⟩) =
      f.eigenvalue m hm * f.eigenvalue n hn := by
  refine f.eq_of_smul_eq ?_
  rw [← f.isEigen (m * n) (PNat.mul_coe m n ▸ Nat.coprime_mul_iff_left.mpr ⟨hm, hn⟩),
    PNat.mul_coe, heckeTCompositeGamma0_mul_of_coprime N hmn, map_mul, Module.End.mul_apply,
    f.isEigen n hn, map_smul, f.isEigen m hm, smul_smul, mul_comm]

/-- The recurrence block `heckeTGeneratorRecGamma0 N p v` acts by `λ_{p^v}` at a good prime. -/
private theorem heckeRingHomCuspCharSpace_heckeTGeneratorRecGamma0 {p : ℕ+}
    (hp : (p : ℕ).Prime) {v : ℕ} (hv : Nat.Coprime ((p ^ v : ℕ+) : ℕ) N) :
    heckeRingHomCuspCharSpace k f.χ (heckeTGeneratorRecGamma0 N p v)
        ⟨f.toCuspForm, f.mem_charSpace⟩ =
      f.eigenvalue (p ^ v) hv • (⟨f.toCuspForm, f.mem_charSpace⟩ : cuspFormCharSpace k f.χ) := by
  have h := f.isEigen (p ^ v) hv
  rwa [PNat.pow_coe, heckeTCompositeGamma0_prime_pow N hp] at h

/-- **The recurrence along the powers of a good prime**:
`λ_{p^{r+2}} = λ_p λ_{p^{r+1}} − χ(p) p^{k−1} λ_{p^r}`. This is the image of the defining
recurrence `heckeTGeneratorRecGamma0_succ_succ` of the ring, with the scalar coset acting by
`χ(p) p^{k−2}` (`heckeRingHomCuspCharSpace_heckeTScalarGamma0`). -/
theorem eigenvalue_prime_pow_add_two {p : ℕ+} (hp : (p : ℕ).Prime) (hpN : Nat.Coprime p N)
    (r : ℕ) :
    f.eigenvalue (p ^ (r + 2)) (PNat.pow_coe p (r + 2) ▸ hpN.pow_left (r + 2)) =
      f.eigenvalue p hpN *
          f.eigenvalue (p ^ (r + 1)) (PNat.pow_coe p (r + 1) ▸ hpN.pow_left (r + 1)) -
        (f.χ (ZMod.unitOfCoprime p hpN) : ℂ) * (p : ℂ) ^ (k - 1) *
          f.eigenvalue (p ^ r) (PNat.pow_coe p r ▸ hpN.pow_left r) := by
  have hc (v : ℕ) : Nat.Coprime ((p ^ v : ℕ+) : ℕ) N := PNat.pow_coe p v ▸ hpN.pow_left v
  -- the ring recurrence, transported along the ring homomorphism
  have hrec : heckeRingHomCuspCharSpace k f.χ (heckeTGeneratorRecGamma0 N p (r + 2)) =
      heckeRingHomCuspCharSpace k f.χ (heckeTGeneratorGamma0 N p) *
          heckeRingHomCuspCharSpace k f.χ (heckeTGeneratorRecGamma0 N p (r + 1)) -
        (p : ℤ) • heckeRingHomCuspCharSpace k f.χ (heckeTScalarGamma0 N p) *
          heckeRingHomCuspCharSpace k f.χ (heckeTGeneratorRecGamma0 N p r) := by
    rw [heckeTGeneratorRecGamma0_succ_succ, map_sub, map_mul, map_mul, map_zsmul]
  -- the generator and the scalar coset evaluated on the form
  have eₚ : heckeRingHomCuspCharSpace k f.χ (heckeTGeneratorGamma0 N p)
      ⟨f.toCuspForm, f.mem_charSpace⟩ =
      f.eigenvalue p hpN • (⟨f.toCuspForm, f.mem_charSpace⟩ : cuspFormCharSpace k f.χ) := by
    have := f.heckeRingHomCuspCharSpace_heckeTGeneratorRecGamma0 hp (hc 1)
    rwa [heckeTGeneratorRecGamma0_one, f.eigenvalue_congr (pow_one p) (hn := hpN)] at this
  have eₛ : heckeRingHomCuspCharSpace k f.χ (heckeTScalarGamma0 N p)
      ⟨f.toCuspForm, f.mem_charSpace⟩ =
      ((f.χ (ZMod.unitOfCoprime p hpN) : ℂ) * (p : ℂ) ^ (k - 2)) •
        (⟨f.toCuspForm, f.mem_charSpace⟩ : cuspFormCharSpace k f.χ) := by
    rw [heckeRingHomCuspCharSpace_heckeTScalarGamma0 k f.χ p hp.pos hpN, LinearMap.smul_apply,
      Module.End.one_apply]
  -- evaluate the recurrence on the form and read off the scalars
  have h := congrArg (fun T : Module.End ℂ (cuspFormCharSpace k f.χ) ↦
    T ⟨f.toCuspForm, f.mem_charSpace⟩) hrec
  simp only [LinearMap.sub_apply, Module.End.mul_apply, LinearMap.smul_apply,
    f.heckeRingHomCuspCharSpace_heckeTGeneratorRecGamma0 hp (hc r),
    f.heckeRingHomCuspCharSpace_heckeTGeneratorRecGamma0 hp (hc (r + 1)),
    f.heckeRingHomCuspCharSpace_heckeTGeneratorRecGamma0 hp (hc (r + 2)), map_smul, eₚ, eₛ,
    smul_smul, ← Int.cast_smul_eq_zsmul ℂ, ← sub_smul] at h
  have hp0 : (p : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hp.ne_zero
  have hk : k - 1 = k - 2 + 1 := by ring
  have hpow : (p : ℂ) ^ (k - 1) = (p : ℂ) ^ (k - 2) * p := by rw [hk, zpow_add_one₀ hp0]
  rw [f.eq_of_smul_eq h, hpow]
  push_cast
  ring

/-- **The prime-square identity**: `λ_{p²} = λ_p² − χ(p) p^{k−1}` at a good prime. -/
theorem eigenvalue_prime_sq {p : ℕ+} (hp : (p : ℕ).Prime) (hpN : Nat.Coprime p N) :
    f.eigenvalue (p ^ 2) (PNat.pow_coe p 2 ▸ hpN.pow_left 2) =
      f.eigenvalue p hpN ^ 2 - (f.χ (ZMod.unitOfCoprime p hpN) : ℂ) * (p : ℂ) ^ (k - 1) := by
  have hc (v : ℕ) : Nat.Coprime ((p ^ v : ℕ+) : ℕ) N := PNat.pow_coe p v ▸ hpN.pow_left v
  have e₀ : f.eigenvalue (p ^ 0) (hc 0) = 1 :=
    (f.eigenvalue_congr (pow_zero p)).trans f.eigenvalue_one
  have e₁ : f.eigenvalue (p ^ (0 + 1)) (hc (0 + 1)) = f.eigenvalue p hpN :=
    f.eigenvalue_congr (by rw [zero_add, pow_one])
  rw [f.eigenvalue_prime_pow_add_two hp hpN 0, e₀, e₁, mul_one, sq]

end HeckeRing.GL2.EigenformAwayFromLevel
