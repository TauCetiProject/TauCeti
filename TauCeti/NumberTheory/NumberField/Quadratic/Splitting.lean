/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.FieldTheory.KummerPolynomial
public import Mathlib.NumberTheory.LegendreSymbol.Basic
public import Mathlib.NumberTheory.NumberField.Ideal.KummerDedekind
public import Mathlib.RingTheory.Discriminant
public import TauCeti.NumberTheory.NumberField.Quadratic.Basic
public import TauCeti.NumberTheory.NumberField.SplitsCompletely
import Mathlib.RingTheory.Adjoin.PowerBasis
import TauCeti.NumberTheory.NumberField.Ideal.KummerDedekind
import TauCeti.NumberTheory.NumberField.Quadratic.RingOfIntegers

/-!
# The prime-splitting law for a quadratic field

For a quadratic number field `K = ℚ(√d)` — given as `K` generated over `ℚ` by an algebraic
integer `θ` whose minimal polynomial over `ℤ` is `X² - d` — and an odd prime `p` not dividing
`d`, the prime `p` splits completely in `K` (there are `[K:ℚ] = 2` primes of `𝓞 K` above it) if
and only if `d` is a quadratic residue mod `p`, i.e. `legendreSym p d = 1`.

The proof routes through Mathlib's number-field Kummer–Dedekind theorem
(`primesOverSpanEquivMonicFactorsMod`): the primes above `p` biject with the monic irreducible
factors of `X² - d` mod `p`, of which there are two exactly when `d` is a square mod `p`. The
required conductor hypothesis `p ∤ exponent θ` follows because the conductor exponent divides the
power-basis discriminant `4d`, which is coprime to the odd prime `p ∤ d`.

This is the base case `n = 1` of the multiquadratic prime-splitting law.

The splitting law is then read off at the level of ideals: a completely split rational prime is
the absolute norm of a prime of `𝓞 K`
(`Ideal.absNorm_eq_of_ncard_primesOver_eq_finrank`). That is the shape in which the
splitting law enters genus theory, where an ideal of norm `p` is what carries the prescribed
values of the genus characters.

The prime `2` is handled separately, through the count of primes above `2` for a generator with
minimal polynomial `X² - X + c` and odd conductor exponent
(`NumberField.ncard_primesOver_two_of_minpoly_eq_X_sq_sub_X_add`, in
`TauCeti.NumberTheory.NumberField.Ideal.KummerDedekind`): for `c = (1 - d)/4` with
`d ≡ 1 (mod 4)`, the presentation of `ℚ(√d)` by `(1 + √d)/2`, this says that `2` splits exactly
when `d ≡ 1 (mod 8)` and is inert exactly when `d ≡ 5 (mod 8)`. For `K = ℚ(√d)` with `d`
squarefree and `d ≡ 1 (mod 4)`, the half-integer generator `(1 + θ)/2` (`halfGen`) has minimal
polynomial `X² - X + (1 - d)/4` (`minpoly_halfGen`) and generates `𝓞 K` over `ℤ`
(`adjoin_halfGen_eq_top_of_mod_four_eq_one`), so its conductor exponent is `1`, and `(1 - d)/4` is
even exactly when `d ≡ 1 (mod 8)`; the generator `θ` with `θ² = d` is useless here, since `2`
divides its conductor exponent.

## Main results

* `NumberField.ncard_primesOver_quadratic_iff`: the quadratic splitting law at an odd prime.
* `NumberField.exists_isPrime_and_absNorm_eq_of_legendreSym_eq_one`: an odd prime `p` with
  `legendreSym p d = 1` is the absolute norm of a prime ideal of `𝓞 K`.
* `NumberField.ncard_primesOver_two_eq_finrank_iff_of_minpoly_eq_X_sq_sub_X_add` and
  `NumberField.ncard_primesOver_two_eq_one_iff_of_minpoly_eq_X_sq_sub_X_add`: for a generator
  with minimal polynomial `X² - X + (1 - d)/4`, `d ≡ 1 (mod 4)`, and odd conductor exponent, `2`
  splits iff `d ≡ 1 (mod 8)` and is inert iff `d ≡ 5 (mod 8)`.
* `NumberField.ncard_primesOver_two_of_mod_four_eq_one`: the number of primes above `2` is
  `if d % 8 = 1 then 2 else 1` for `ℚ(√d)` with `d` squarefree, `d ≡ 1 (mod 4)`, presented by
  `√d`, with the corollaries `NumberField.ncard_primesOver_two_eq_finrank_iff_of_mod_four_eq_one`
  (`2` splits iff `d ≡ 1 (mod 8)`) and
  `NumberField.ncard_primesOver_two_eq_one_iff_of_mod_four_eq_one` (`2` is inert iff
  `d ≡ 5 (mod 8)`).

## References

* J. Neukirch, *Algebraic Number Theory*, Chapter I, §8, Proposition (8.3).
-/

public section

open Polynomial NumberField Ideal Module RingOfIntegers UniqueFactorizationMonoid

namespace NumberField

variable {K : Type*} [Field K] [NumberField K]


/-- The power-basis discriminant `4d` lies in the conductor: for `θ` generating `K` over `ℚ`
with minimal polynomial `X² - d` over `ℤ`, the image of `4 * d` in `𝓞 K` belongs to
`conductor ℤ θ`. This is the crux of the conductor bound, since it forces the conductor
exponent of `θ` to divide `4d`. -/
private theorem algebraMap_four_mul_mem_conductor {θ : 𝓞 K} {d : ℤ}
    (hmin : minpoly ℤ θ = X ^ 2 - C d) (hgen : Algebra.adjoin ℚ {(θ : K)} = ⊤) :
    (algebraMap ℤ (𝓞 K)) (4 * d) ∈ conductor ℤ θ := by
  rw [mem_conductor_iff]
  intro b
  have hintθℤ : IsIntegral ℤ (θ : K) := θ.isIntegral_coe
  have hintθℚ : IsIntegral ℚ (θ : K) := hintθℤ.tower_top
  let pb : PowerBasis ℚ K := PowerBasis.ofAdjoinEqTop' hintθℚ hgen
  have hgenθ : pb.gen = (θ : K) := PowerBasis.ofAdjoinEqTop'_gen hintθℚ hgen
  have hmin' : minpoly ℚ pb.gen = X ^ 2 - C ((d : ℤ) : ℚ) := by
    rw [hgenθ]; exact minpoly_rat_quadratic hmin
  have hdim : pb.dim = 2 := by
    rw [← pb.natDegree_minpoly, hmin', natDegree_X_pow_sub_C]
  have hdiscr : Algebra.discr ℚ pb.basis = ((4 * d : ℤ) : ℚ) := by
    -- `pb.basis` is `{1, θ}` reindexed along `pb.dim = 2`, so its discriminant is `discr_one_gen`.
    have hb2 : ⇑pb.basis ∘ ⇑(finCongr hdim).symm = ![(1 : K), (θ : K)] := by
      funext j; fin_cases j <;> simp [hgenθ]
    rw [← Algebra.discr_reindex ℚ pb.basis (finCongr hdim), hb2, discr_one_gen hmin hgen]
  have hgenint : IsIntegral ℤ pb.gen := hgenθ ▸ hintθℤ
  have key := Algebra.discr_mul_isIntegral_mem_adjoin (R := ℤ) (K := ℚ) (L := K) (B := pb)
    hgenint (z := (b : K)) (b.isIntegral_coe)
  rw [hdiscr, hgenθ] at key
  -- `key : ((4d:ℤ):ℚ) • (b:K) ∈ adjoin ℤ {(θ:K)}`; bridge back into `𝓞 K`.
  let f : (𝓞 K) →ₐ[ℤ] K := IsScalarTower.toAlgHom ℤ (𝓞 K) K
  have hfθ : f θ = (θ : K) := by rw [IsScalarTower.coe_toAlgHom']
  have hAmap : (Algebra.adjoin ℤ {θ}).map f = Algebra.adjoin ℤ {(θ : K)} := by
    rw [← Algebra.adjoin_image, Set.image_singleton, hfθ]
  have himg : ((4 * d : ℤ) : ℚ) • (b : K) = f (algebraMap ℤ (𝓞 K) (4 * d) * b) := by
    have key1 : f (algebraMap ℤ (𝓞 K) (4 * d) * b) = algebraMap ℤ K (4 * d) * (b : K) := by
      rw [map_mul, IsScalarTower.coe_toAlgHom', ← IsScalarTower.algebraMap_apply ℤ (𝓞 K) K]
    rw [key1, Algebra.smul_def]
    simp
  rw [himg, ← hAmap] at key
  obtain ⟨y, hyA, hyeq⟩ := key
  rwa [(FaithfulSMul.algebraMap_injective (𝓞 K) K) hyeq] at hyA

/-- **Conductor bound.** If `θ` generates `K` and has minimal polynomial `X² - d`, then an odd
prime not dividing `d` does not divide the conductor exponent of `θ`. -/
private theorem not_dvd_exponent_of_minpoly_quadratic {θ : 𝓞 K} {d : ℤ}
    (hmin : minpoly ℤ θ = X ^ 2 - C d)
    (hgen : Algebra.adjoin ℚ {(θ : K)} = ⊤) {p : ℕ} [Fact p.Prime] (hodd : p ≠ 2)
    (hcop : ¬ (p : ℤ) ∣ d) : ¬ p ∣ exponent θ := by
  -- Key bound: `4d ∈ conductor ℤ θ`, hence the conductor exponent divides `4d`.
  have hmem := algebraMap_four_mul_mem_conductor hmin hgen
  have hdvd : exponent θ ∣ (4 * d).natAbs := by
    have hmem' : (4 * d : ℤ) ∈ under ℤ (conductor ℤ θ) := Ideal.mem_comap.mpr hmem
    rw [← Int.ideal_span_absNorm_eq_self (under ℤ (conductor ℤ θ)),
      Ideal.mem_span_singleton] at hmem'
    have h : absNorm (under ℤ (conductor ℤ θ)) ∣ (4 * d).natAbs := by
      simpa using Int.natAbs_dvd_natAbs.mpr hmem'
    exact h
  -- `p` odd and `p ∤ d` ⟹ `p ∤ 4d` ⟹ `p ∤ exponent`.
  intro hp
  have hp4d : (p : ℤ) ∣ 4 * d := by
    have h := Int.natCast_dvd_natCast.mpr (hp.trans hdvd)
    rwa [Int.dvd_natAbs] at h
  rcases (Nat.prime_iff_prime_int.mp (Fact.out : p.Prime)).dvd_mul.mp hp4d with h4 | hd
  · have hp4 : p ∣ 4 := by exact_mod_cast h4
    have hp2 : p ∣ 2 := (Fact.out : p.Prime).dvd_of_dvd_pow (by simpa using hp4 : p ∣ 2 ^ 2)
    exact hodd ((Nat.prime_dvd_prime_iff_eq Fact.out Nat.prime_two).mp hp2)
  · exact hcop hd

omit [NumberField K] in
/-- **Factor count mod p.** `X² - d` has two monic irreducible factors mod `p` (for `p` odd,
`p ∤ d`) iff `d` is a square mod `p`. -/
private theorem card_monicFactorsMod_quadratic_iff {θ : 𝓞 K} {d : ℤ}
    (hmin : minpoly ℤ θ = X ^ 2 - C d) {p : ℕ} [Fact p.Prime] (hodd : p ≠ 2)
    (hcop : ¬ (p : ℤ) ∣ d) : (monicFactorsMod θ p).card = 2 ↔ legendreSym p d = 1 := by
  classical
  have hc0 : (d : ZMod p) ≠ 0 := by rw [Ne, ZMod.intCast_zmod_eq_zero_iff_dvd]; exact hcop
  have h2 : (2 : ZMod p) ≠ 0 := by
    have hnd : ¬ (p ∣ 2) := fun h => hodd ((Nat.prime_dvd_prime_iff_eq Fact.out Nat.prime_two).mp h)
    intro h0
    exact hnd ((CharP.cast_eq_zero_iff (ZMod p) p 2).mp (by exact_mod_cast h0))
  have hmap : (minpoly ℤ θ).map (Int.castRingHom (ZMod p)) = X ^ 2 - C (d : ZMod p) := by
    rw [hmin]; simp [Polynomial.map_sub, Polynomial.map_pow]
  rw [legendreSym.eq_one_iff p hc0]
  simp only [monicFactorsMod, hmap]
  constructor
  · intro hcard
    by_contra hns
    have hirr : Irreducible (X ^ 2 - C (d : ZMod p)) :=
      (X_pow_sub_C_irreducible_iff_of_prime Nat.prime_two).mpr
        (fun b hb => hns ⟨b, by rw [← hb]; ring⟩)
    rw [normalizedFactors_irreducible hirr] at hcard
    simp at hcard
  · rintro ⟨a, ha⟩
    have ha0 : a ≠ 0 := fun h => hc0 (by rw [ha, h]; ring)
    have hane : a ≠ -a := by
      intro h
      have h2a : (2 : ZMod p) * a = 0 := by linear_combination h
      exact ha0 ((mul_eq_zero.mp h2a).resolve_left h2)
    have hfac : X ^ 2 - C (d : ZMod p) = (X - C a) * (X - C (-a)) := by
      rw [ha]; simp only [map_mul, map_neg]; ring
    rw [hfac, normalizedFactors_mul (X_sub_C_ne_zero a) (X_sub_C_ne_zero (-a)),
      normalizedFactors_irreducible (irreducible_X_sub_C a),
      normalizedFactors_irreducible (irreducible_X_sub_C (-a)),
      (monic_X_sub_C a).normalize_eq_self, (monic_X_sub_C (-a)).normalize_eq_self,
      Multiset.toFinset_add, Multiset.toFinset_singleton, Multiset.toFinset_singleton,
      Finset.card_union_of_disjoint (Finset.disjoint_singleton.mpr (by
        rw [Ne, sub_right_inj, C_inj]; exact hane))]
    simp

/-- **The quadratic splitting law.** For `K = ℚ(√d)` (`θ` a square root of the integer `d`
generating `K`) and an odd prime `p ∤ d`, `p` splits completely in `K` iff `d` is a quadratic
residue mod `p`. This is the `n = 1` case of the multiquadratic prime-splitting law. -/
theorem ncard_primesOver_quadratic_iff {θ : 𝓞 K} {d : ℤ}
    (hmin : minpoly ℤ θ = X ^ 2 - C d) (hgen : Algebra.adjoin ℚ {(θ : K)} = ⊤)
    {p : ℕ} [Fact p.Prime] (hodd : p ≠ 2) (hcop : ¬ (p : ℤ) ∣ d) :
    (primesOver (span {(p : ℤ)}) (𝓞 K)).ncard = finrank ℚ K ↔ legendreSym p d = 1 := by
  have hp := not_dvd_exponent_of_minpoly_quadratic hmin hgen hodd hcop
  rw [ncard_primesOver_eq_card_monicFactorsMod θ hp, finrank_rat_eq_two hmin hgen]
  exact card_monicFactorsMod_quadratic_iff hmin hodd hcop

/-- **A split prime is an ideal norm.** For `K = ℚ(√d)` and an odd prime `p` for which `d` is a
quadratic residue mod `p` — that is, one which splits in `K` by
`ncard_primesOver_quadratic_iff` — there is a prime ideal of `𝓞 K` of absolute norm `p`. This is the
form in which the splitting law feeds genus theory: the genus characters are computed on ideals
through their absolute norms. -/
theorem exists_isPrime_and_absNorm_eq_of_legendreSym_eq_one {θ : 𝓞 K} {d : ℤ}
    (hmin : minpoly ℤ θ = X ^ 2 - C d) (hgen : Algebra.adjoin ℚ {(θ : K)} = ⊤)
    {p : ℕ} [Fact p.Prime] (hodd : p ≠ 2) (hleg : legendreSym p d = 1) :
    ∃ 𝔭 : Ideal (𝓞 K), 𝔭.IsPrime ∧ 𝔭.LiesOver (span {(p : ℤ)}) ∧ Ideal.absNorm 𝔭 = p := by
  -- A nonzero value of the Legendre symbol already records that `p ∤ d`.
  have hcop : ¬ (p : ℤ) ∣ d := by
    intro hdvd
    rw [(legendreSym.eq_zero_iff p d).mpr ((ZMod.intCast_zmod_eq_zero_iff_dvd d p).mpr hdvd)]
      at hleg
    exact zero_ne_one hleg
  have hsplit : ((span {(p : ℤ)} : Ideal ℤ).primesOver (𝓞 K)).ncard = finrank ℚ K :=
    (ncard_primesOver_quadratic_iff hmin hgen hodd hcop).mpr hleg
  obtain ⟨⟨𝔮, h𝔮, hlo⟩⟩ :=
    (inferInstance : Nonempty ((span {(p : ℤ)} : Ideal ℤ).primesOver (𝓞 K)))
  -- `h𝔮` and `hlo` are the prime and lies-over hypotheses of the norm computation; pass them
  -- explicitly rather than installing them as anonymous local instances.
  exact ⟨𝔮, h𝔮, hlo,
    @Ideal.absNorm_eq_of_ncard_primesOver_eq_finrank K _ _ p _ 𝔮 h𝔮 hlo hsplit⟩

/-! ### The prime `2` for `d ≡ 1 (mod 4)` -/

/-- The field generated over `ℚ` by a root of a monic quadratic `X² - X + c` has degree `2`. -/
private theorem finrank_rat_eq_two_of_minpoly_eq_X_sq_sub_X_add {ω : 𝓞 K} {c : ℤ}
    (hmin : minpoly ℤ ω = X ^ 2 - X + C c) (hgen : Algebra.adjoin ℚ {(ω : K)} = ⊤) :
    finrank ℚ K = 2 := by
  rw [(PowerBasis.ofAdjoinEqTop (IsIntegral.of_finite ℚ (ω : K)) hgen).finrank,
    PowerBasis.ofAdjoinEqTop_dim, minpoly.isIntegrallyClosed_eq_field_fractions' ℚ ω.isIntegral_coe,
    RingOfIntegers.minpoly_coe, (minpoly.monic ω.isIntegral).natDegree_map, hmin]
  have hq : (X ^ 2 - X + C c : ℤ[X]) = X ^ 2 + (C (-1) * X + C c) := by
    rw [map_neg, C_1]; ring
  have hlt : (C (-1) * X + C c : ℤ[X]).natDegree < (X ^ 2 : ℤ[X]).natDegree := by
    rw [natDegree_X_pow]
    exact lt_of_le_of_lt natDegree_linear_le (by norm_num)
  rw [hq, natDegree_add_eq_left_of_natDegree_lt hlt, natDegree_X_pow]

/-- **The splitting law at `2`, in the half-integer presentation.** Let `K` be generated over `ℚ`
by an algebraic integer `ω` with minimal polynomial `X² - X + (1 - d)/4` over `ℤ`, where
`d ≡ 1 (mod 4)` — the presentation of `ℚ(√d)` by `ω = (1 + √d)/2` — and suppose `2` does not
divide the conductor exponent of `ω`. Then `2` splits completely in `K` if and only if
`d ≡ 1 (mod 8)`. -/
theorem ncard_primesOver_two_eq_finrank_iff_of_minpoly_eq_X_sq_sub_X_add {ω : 𝓞 K} {d : ℤ}
    (hmin : minpoly ℤ ω = X ^ 2 - X + C ((1 - d) / 4)) (hgen : Algebra.adjoin ℚ {(ω : K)} = ⊤)
    (hd4 : d % 4 = 1) (hexp : ¬ 2 ∣ exponent ω) :
    (primesOver (span {(2 : ℤ)}) (𝓞 K)).ncard = finrank ℚ K ↔ d % 8 = 1 := by
  rw [ncard_primesOver_two_of_minpoly_eq_X_sq_sub_X_add hmin hexp,
    finrank_rat_eq_two_of_minpoly_eq_X_sq_sub_X_add hmin hgen]
  -- `(1 - d)/4` is even exactly when `d ≡ 1 (mod 8)`, given `d ≡ 1 (mod 4)`.
  by_cases hc : 2 ∣ (1 - d) / 4
  · rw [ite_eq_left hc]
    exact ⟨fun _ => by omega, fun _ => rfl⟩
  · rw [ite_eq_right hc]
    exact ⟨fun h => by omega, fun h => by omega⟩

/-- **The inert case at `2`, in the half-integer presentation.** Let `K` be generated over `ℚ` by
an algebraic integer `ω` with minimal polynomial `X² - X + (1 - d)/4` over `ℤ`, where
`d ≡ 1 (mod 4)`, and suppose `2` does not divide the conductor exponent of `ω`. Then `2` is inert
in `K` (there is a single prime above it) if and only if `d ≡ 5 (mod 8)`. -/
theorem ncard_primesOver_two_eq_one_iff_of_minpoly_eq_X_sq_sub_X_add {ω : 𝓞 K} {d : ℤ}
    (hmin : minpoly ℤ ω = X ^ 2 - X + C ((1 - d) / 4)) (hd4 : d % 4 = 1)
    (hexp : ¬ 2 ∣ exponent ω) :
    (primesOver (span {(2 : ℤ)}) (𝓞 K)).ncard = 1 ↔ d % 8 = 5 := by
  rw [ncard_primesOver_two_of_minpoly_eq_X_sq_sub_X_add hmin hexp]
  by_cases hc : 2 ∣ (1 - d) / 4
  · rw [ite_eq_left hc]
    exact ⟨fun h => by omega, fun h => by omega⟩
  · rw [ite_eq_right hc]
    exact ⟨fun _ => by omega, fun _ => rfl⟩

/-- **The number of primes above `2` for `d ≡ 1 (mod 4)`.** For `K = ℚ(√d)` with `d` squarefree
and `d ≡ 1 (mod 4)`, there are two primes of `𝓞 K` above `2` when `d ≡ 1 (mod 8)` and one when
`d ≡ 5 (mod 8)`: the half-integer generator `(1 + √d)/2` has minimal polynomial
`X² - X + (1 - d)/4` and conductor exponent `1`, and `(1 - d)/4` is even exactly when
`d ≡ 1 (mod 8)`. -/
theorem ncard_primesOver_two_of_mod_four_eq_one {θ : 𝓞 K} {d : ℤ}
    (hmin : minpoly ℤ θ = X ^ 2 - C d) (hgen : Algebra.adjoin ℚ {(θ : K)} = ⊤)
    (hsf : Squarefree d) (hd4 : d % 4 = 1) :
    (primesOver (span {(2 : ℤ)}) (𝓞 K)).ncard = if d % 8 = 1 then 2 else 1 := by
  have hexp : exponent (halfGen hmin hd4) = 1 :=
    exponent_eq_one_iff.mpr (adjoin_halfGen_eq_top_of_mod_four_eq_one hmin hgen hsf hd4)
  rw [ncard_primesOver_two_of_minpoly_eq_X_sq_sub_X_add (minpoly_halfGen hmin hd4)
    (by rw [hexp]; norm_num)]
  -- `(1 - d)/4` is even exactly when `d ≡ 1 (mod 8)`, given `d ≡ 1 (mod 4)`.
  by_cases hd8 : d % 8 = 1
  · have hc : 2 ∣ (1 - d) / 4 := by omega
    rw [ite_eq_left hd8, ite_eq_left hc]
  · have hc : ¬ 2 ∣ (1 - d) / 4 := by omega
    rw [ite_eq_right hd8, ite_eq_right hc]

/-- **The splitting law at `2` for `d ≡ 1 (mod 4)`.** For `K = ℚ(√d)` with `d` squarefree and
`d ≡ 1 (mod 4)`, the prime `2` splits completely in `K` if and only if `d ≡ 1 (mod 8)`. -/
theorem ncard_primesOver_two_eq_finrank_iff_of_mod_four_eq_one {θ : 𝓞 K} {d : ℤ}
    (hmin : minpoly ℤ θ = X ^ 2 - C d) (hgen : Algebra.adjoin ℚ {(θ : K)} = ⊤)
    (hsf : Squarefree d) (hd4 : d % 4 = 1) :
    (primesOver (span {(2 : ℤ)}) (𝓞 K)).ncard = finrank ℚ K ↔ d % 8 = 1 := by
  rw [ncard_primesOver_two_of_mod_four_eq_one hmin hgen hsf hd4, finrank_rat_eq_two hmin hgen]
  split_ifs with h <;> simp [h]

/-- **The inert case at `2` for `d ≡ 1 (mod 4)`.** For `K = ℚ(√d)` with `d` squarefree and
`d ≡ 1 (mod 4)`, the prime `2` is inert in `K` (there is a single prime above it) if and only if
`d ≡ 5 (mod 8)`. -/
theorem ncard_primesOver_two_eq_one_iff_of_mod_four_eq_one {θ : 𝓞 K} {d : ℤ}
    (hmin : minpoly ℤ θ = X ^ 2 - C d) (hgen : Algebra.adjoin ℚ {(θ : K)} = ⊤)
    (hsf : Squarefree d) (hd4 : d % 4 = 1) :
    (primesOver (span {(2 : ℤ)}) (𝓞 K)).ncard = 1 ↔ d % 8 = 5 := by
  rw [ncard_primesOver_two_of_mod_four_eq_one hmin hgen hsf hd4]
  split_ifs with h
  · simp only [OfNat.ofNat_ne_one, false_iff]; omega
  · simp only [true_iff]; omega

end NumberField
