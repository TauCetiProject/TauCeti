/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.FieldTheory.Galois.Basic
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.FieldTheory.IsRealClosed.Basic
import Mathlib.Algebra.Algebra.ZMod
import Mathlib.FieldTheory.KummerExtension
import Mathlib.RingTheory.Polynomial.Cyclotomic.Roots
import TauCeti.FieldTheory.Finite.FrobeniusFixed
import TauCeti.FieldTheory.Galois.FixedField
import TauCeti.FieldTheory.Galois.Hilbert90
import TauCeti.FieldTheory.RealClosure.QuadraticExtension
import TauCeti.FieldTheory.Separable.PerfectField

/-!
# The Artin–Schreier theorem

If an algebraically closed field `C` has finite degree greater than one over a subfield `F`, then
`[C : F] = 2` and `F` is real closed (`TauCeti.RealClosure.finrank_eq_two_of_isAlgClosed` and
`TauCeti.RealClosure.isRealClosed_of_isAlgClosed_of_one_lt_finrank`). Consequently a nontrivial
automorphism of finite order of an algebraically closed field has order two and a real closed fixed
field (`TauCeti.RealClosure.orderOf_eq_two_of_isOfFinOrder` and
`TauCeti.RealClosure.isRealClosed_fixedField_zpowers`). This is what controls the torsion of
absolute Galois groups: a field whose absolute Galois group has a nontrivial element of finite order
is contained in a real closed field, hence is formally real.

The extension `C / F` is Galois (`IsGalois.of_isAlgClosed_top`). The first step shows
that `C` has no prime degree `ℓ ≠ 2` over any subfield:

* if `ℓ` is the characteristic `p` of `F`, a generator `g` of `Gal(C/F)` gives, by the additive
  Hilbert 90, an element `y` with `g y = y + 1`, so `y ^ p - y` lies in `F`. Tracing a root of
  `X ^ p - X - a θ`, with `θ` of trace one, shows that every `a` in `F` is `c ^ p - c` for some
  `c` in `F`. Then `z = y - c` is fixed by Frobenius, so lies in the prime field and is fixed by
  `g`, contradicting `g z = z + 1`;
* if `ℓ` is odd and invertible in `F`, then `F` contains the `ℓ`-th roots of unity, whose degree
  over `F` is at most `ℓ - 1` and divides `ℓ`. By Kummer theory `C = F(α)` with `α ^ ℓ = a` in `F`
  and `a` not an `ℓ`-th power in `F`; then `X ^ ℓ ^ 2 - a` is irreducible over `F`, so its roots in
  `C` have degree `ℓ ^ 2 > [C : F]`.

Now let `i` be a square root of `-1` in `C`. If `C ≠ F(i)`, a subgroup of prime order of
`Gal(C/F(i))` has a fixed field `E ⊇ F(i)` with `[C : E]` prime, hence two. Then `-1` is a square
in `E` and `C` is an algebraically closed quadratic extension of `E`, which is impossible
(`TauCeti.RealClosure.not_isSquare_neg_one_of_isAlgClosed_of_isQuadraticExtension`). Hence
`[C : F] ≤ [F(i) : F] ≤ 2`, and an algebraically closed quadratic extension makes `F` real closed
(`TauCeti.RealClosure.isRealClosed_of_isAlgClosed_of_isQuadraticExtension`).

## Main results

* `TauCeti.RealClosure.finrank_eq_two_of_isAlgClosed` and
  `TauCeti.RealClosure.isRealClosed_of_isAlgClosed_of_one_lt_finrank`: the Artin–Schreier theorem.
* `TauCeti.RealClosure.orderOf_eq_two_of_isOfFinOrder` and
  `TauCeti.RealClosure.isRealClosed_fixedField_zpowers`: automorphisms of finite order of an
  algebraically closed field.

## References

* E. Artin and O. Schreier, *Eine Kennzeichnung der reell abgeschlossenen Körper*, Abh. Math.
  Sem. Univ. Hamburg 5 (1927), 225–231.
* S. Lang, *Algebra*, third edition, Chapter VI, Corollary 9.3; the two cases of prime degree follow
  its proof, through Theorems 6.4 and 9.1.
-/

public section

namespace TauCeti.RealClosure

open Module Polynomial IntermediateField

variable {F C : Type*} [Field F] [Field C] [Algebra F C] [IsAlgClosed C]

/-- If an algebraically closed field `C` is finite of characteristic `p` over `F`, then every
element of `F` has the form `c ^ p - c` for some `c` in `F`. -/
private theorem exists_pow_sub_self_eq [FiniteDimensional F C] (p : ℕ) [Fact p.Prime] [CharP C p]
    (a : F) : ∃ c : F, c ^ p - c = a := by
  have := IsGalois.of_isAlgClosed_top F C
  obtain ⟨θ, hθ⟩ := Algebra.trace_surjective F C 1
  have hdeg : (X ^ p - X - Polynomial.C (a • θ) : C[X]).degree ≠ 0 := by
    have hX : (X ^ p - X : C[X]).degree = p := degree_X_pow_sub_X (Fact.out : p.Prime).one_lt
    rw [degree_sub_C (by rw [hX]; exact_mod_cast (Fact.out : p.Prime).pos), hX]
    exact_mod_cast (Fact.out : p.Prime).ne_zero
  obtain ⟨x, hx⟩ := IsAlgClosed.exists_root _ hdeg
  have hx' : x ^ p - x = a • θ := by simpa [sub_eq_zero] using hx
  -- The trace commutes with `p`-th powers: both are sums over the Galois group.
  have htr (z : C) : algebraMap F C (Algebra.trace F C (z ^ p)) =
      algebraMap F C (Algebra.trace F C z) ^ p := by
    simp_rw [trace_eq_sum_automorphisms, sum_pow_char, map_pow]
  refine ⟨Algebra.trace F C x, (algebraMap F C).injective ?_⟩
  rw [map_sub, map_pow, ← htr, ← map_sub, ← map_sub, hx', LinearMap.map_smul, hθ, smul_eq_mul,
    mul_one]

/-- An algebraically closed field `C` does not have degree `p` over a subfield `F` of
characteristic `p`. -/
private theorem finrank_ne_of_charP (p : ℕ) [hp : Fact p.Prime] [CharP F p] : finrank F C ≠ p := by
  intro h
  have : FiniteDimensional F C := Module.finite_of_finrank_pos (h ▸ hp.out.pos)
  have := IsGalois.of_isAlgClosed_top F C
  have : CharP C p := charP_of_injective_algebraMap (algebraMap F C).injective p
  have : IsCyclic Gal(C/F) := isCyclic_of_prime_card (by rw [IsGalois.card_aut_eq_finrank, h])
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := Gal(C/F))
  -- Additive Hilbert 90 gives `y` with `g y = y + 1`, since `1` has trace `p = 0`.
  obtain ⟨y, hy⟩ := (exists_apply_sub_eq_iff_trace_eq_zero hg (x := 1)).2 (by
    rw [← map_one (algebraMap F C), Algebra.trace_algebraMap, h, nsmul_eq_mul,
      CharP.cast_eq_zero, zero_mul])
  have hgy : g y = y + 1 := by rw [← hy, add_sub_cancel]
  -- So `y ^ p - y` is fixed by `g`, hence lies in `F`, and so it is `c ^ p - c` with `c` in `F`.
  have hmem : y ^ p - y ∈ (⊥ : IntermediateField F C) := by
    rw [← IsGalois.fixedField_top, ← eq_top_iff.2 fun σ _ ↦ hg σ, mem_fixedField_zpowers_iff,
      map_sub, map_pow, hgy, add_pow_char, one_pow, add_sub_add_right_eq_sub]
  obtain ⟨a, ha⟩ := mem_bot.1 hmem
  obtain ⟨c, hc⟩ := exists_pow_sub_self_eq (C := C) p a
  -- Then `z = y - c` is fixed by Frobenius, so it lies in the prime field and is fixed by `g`.
  set z := y - algebraMap F C c
  have hz : z ^ Fintype.card (ZMod p) = z := by
    rw [ZMod.card, ← sub_eq_zero, sub_pow_char, sub_sub_sub_comm, ← map_pow, ← map_sub, hc, ha,
      sub_self]
  let := ZMod.algebra C p
  obtain ⟨k, hk⟩ := (FiniteField.pow_card_eq_self_iff_mem_range_algebraMap z).1 hz
  have hgz : g z = z := by
    rw [← hk]
    exact DFunLike.congr_fun (RingHom.ext_zmod ((g : C →+* C).comp (algebraMap (ZMod p) C))
      (algebraMap (ZMod p) C)) k
  -- But `g z = z + 1`.
  rw [map_sub, AlgEquiv.commutes, hgy, add_sub_right_comm, add_eq_left] at hgz
  exact one_ne_zero hgz

/-- If an algebraically closed field `C` has prime degree `ℓ` over a subfield `F` in which `ℓ` is
invertible, then `F` contains a primitive `ℓ`-th root of unity. -/
private theorem exists_isPrimitiveRoot {ℓ : ℕ} (hℓ : ℓ.Prime) (h : finrank F C = ℓ)
    (hℓF : (ℓ : F) ≠ 0) : ∃ ζ : F, IsPrimitiveRoot ζ ℓ := by
  have : FiniteDimensional F C := Module.finite_of_finrank_pos (h ▸ hℓ.pos)
  have : NeZero (ℓ : C) := ⟨by simpa using (algebraMap F C).injective.ne hℓF⟩
  obtain ⟨ζ, hζ⟩ := IsAlgClosed.exists_root (cyclotomic ℓ C) (degree_cyclotomic_pos ℓ C hℓ.pos).ne'
  -- The degree of `ζ` over `F` divides `ℓ = [C : F]` and is at most `φ(ℓ) = ℓ - 1`.
  have hdvd : (minpoly F ζ).natDegree ∣ ℓ := h ▸ minpoly.degree_dvd (IsIntegral.of_finite F ζ)
  have hle : (minpoly F ζ).natDegree ≤ ℓ - 1 := by
    have hroot : aeval ζ (cyclotomic ℓ F) = 0 := by
      rwa [aeval_def, eval₂_eq_eval_map, map_cyclotomic]
    have := natDegree_le_of_dvd (minpoly.dvd F ζ hroot) (cyclotomic_ne_zero ℓ F)
    rwa [natDegree_cyclotomic, Nat.totient_prime hℓ] at this
  have h1 : (minpoly F ζ).natDegree = 1 :=
    ((Nat.dvd_prime hℓ).1 hdvd).resolve_right (by have := hℓ.one_lt; omega)
  obtain ⟨ζ₀, rfl⟩ := minpoly.natDegree_eq_one_iff.1 h1
  exact ⟨ζ₀, ((isRoot_cyclotomic_iff).1 hζ).of_map_of_injective (algebraMap F C).injective⟩

/-- An algebraically closed field `C` does not have odd prime degree `ℓ` over a subfield `F` in
which `ℓ` is invertible. -/
private theorem finrank_ne_of_prime_of_ne_two {ℓ : ℕ} (hℓ : ℓ.Prime) (h2 : ℓ ≠ 2)
    (hℓF : (ℓ : F) ≠ 0) : finrank F C ≠ ℓ := by
  intro h
  have : Fact ℓ.Prime := ⟨hℓ⟩
  have : FiniteDimensional F C := Module.finite_of_finrank_pos (h ▸ hℓ.pos)
  have := IsGalois.of_isAlgClosed_top F C
  have : IsCyclic Gal(C/F) := isCyclic_of_prime_card (by rw [IsGalois.card_aut_eq_finrank, h])
  obtain ⟨ζ, hζ⟩ := exists_isPrimitiveRoot hℓ h hℓF
  -- By Kummer theory `C = F(α)` with `α ^ ℓ = a` in `F` and `X ^ ℓ - a` irreducible.
  obtain ⟨α, ⟨a, ha⟩, hα⟩ := exists_root_adjoin_eq_top_of_isCyclic F C
    ⟨ζ, (mem_primitiveRoots (finrank_pos)).2 (h ▸ hζ)⟩
  have hirr := irreducible_X_pow_sub_C_of_root_adjoin_eq_top ha.symm hα
  rw [h] at hirr
  -- So `a` is not an `ℓ`-th power in `F`, and `X ^ ℓ ^ 2 - a` is irreducible over `F` as well.
  have hirr2 := irreducible_X_pow_sub_C_of_prime_pow_of_ne_two hℓ h2 2
    (pow_ne_of_irreducible_X_pow_sub_C hirr dvd_rfl hℓ.ne_one)
  -- A root `β` of it in `C` then has degree `ℓ ^ 2` over `F`, which exceeds `[C : F] = ℓ`.
  obtain ⟨β, hβ⟩ := IsAlgClosed.exists_pow_nat_eq (algebraMap F C a) (pow_pos hℓ.pos 2)
  have hmin : X ^ ℓ ^ 2 - Polynomial.C a = minpoly F β :=
    minpoly.eq_of_irreducible_of_monic hirr2 (by simp [hβ])
      (monic_X_pow_sub_C _ (pow_pos hℓ.pos 2).ne')
  have hle := minpoly.natDegree_le (A := F) β
  rw [← hmin, natDegree_X_pow_sub_C, h] at hle
  nlinarith [hℓ.two_le]

/-- If an algebraically closed field `C` has prime degree `ℓ` over a subfield `F`, then `ℓ = 2`. -/
private theorem eq_two_of_finrank_eq_prime {ℓ : ℕ} (hℓ : ℓ.Prime) (h : finrank F C = ℓ) :
    ℓ = 2 := by
  by_contra h2
  by_cases hℓF : (ℓ : F) = 0
  · have : Fact ℓ.Prime := ⟨hℓ⟩
    have : CharP F ℓ := (CharP.charP_iff_prime_eq_zero hℓ).2 hℓF
    exact finrank_ne_of_charP ℓ h
  · exact finrank_ne_of_prime_of_ne_two hℓ h2 hℓF h

/-- If `-1` is a square in `F`, then an algebraically closed field `C` of finite degree over `F` is
`F` itself. -/
private theorem finrank_eq_one_of_isSquare_neg_one [FiniteDimensional F C]
    (hF : IsSquare (-1 : F)) : finrank F C = 1 := by
  by_contra hne
  have := IsGalois.of_isAlgClosed_top F C
  obtain ⟨ℓ, hℓ, hdvd⟩ := Nat.exists_prime_and_dvd hne
  have : Fact ℓ.Prime := ⟨hℓ⟩
  obtain ⟨g, hg⟩ := exists_prime_orderOf_dvd_card' (G := Gal(C/F)) ℓ
    (by rwa [IsGalois.card_aut_eq_finrank])
  -- The fixed field `E` of an automorphism of order `ℓ` has `[C : E] = ℓ`, hence `[C : E] = 2`.
  set E := fixedField (Subgroup.zpowers g)
  have hE : finrank E C = ℓ := by rw [finrank_fixedField_eq_card, Nat.card_zpowers, hg]
  have : Algebra.IsQuadraticExtension E C := ⟨hE.trans (eq_two_of_finrank_eq_prime hℓ hE)⟩
  -- But `-1` is a square in `E`, which has the algebraically closed quadratic extension `C`.
  obtain ⟨r, hr⟩ := hF
  exact not_isSquare_neg_one_of_isAlgClosed_of_isQuadraticExtension (R := E) (K := C)
    ⟨algebraMap F E r, by rw [← map_mul, ← hr, map_neg, map_one]⟩

/-- **The Artin–Schreier theorem.** If an algebraically closed field `C` has finite degree greater
than one over a subfield `F`, then this degree is two. -/
theorem finrank_eq_two_of_isAlgClosed (h : 1 < finrank F C) : finrank F C = 2 := by
  have : FiniteDimensional F C := Module.finite_of_finrank_pos (by omega)
  obtain ⟨i, hi⟩ := IsAlgClosed.exists_pow_nat_eq (-1 : C) two_pos
  -- Over `F(i)`, in which `-1` is a square, `C` has degree one.
  have h1 : finrank F⟮i⟯ C = 1 := finrank_eq_one_of_isSquare_neg_one
    ⟨⟨i, mem_adjoin_simple_self F i⟩, Subtype.ext (by simp [← hi, sq])⟩
  -- And `F(i)` has degree at most two over `F`, since `i` is a root of `X ^ 2 + 1`.
  have hle : finrank F F⟮i⟯ ≤ 2 := by
    rw [adjoin.finrank (IsIntegral.of_finite F i)]
    have := natDegree_le_of_dvd (minpoly.dvd F i (p := X ^ 2 + Polynomial.C 1) (by simp [hi]))
      (X_pow_add_C_ne_zero two_pos 1)
    rwa [natDegree_X_pow_add_C] at this
  rw [← finrank_mul_finrank F F⟮i⟯ C, h1, mul_one] at h ⊢
  omega

/-- **The Artin–Schreier theorem.** A field over which an algebraically closed field has finite
degree greater than one is real closed. -/
theorem isRealClosed_of_isAlgClosed_of_one_lt_finrank (h : 1 < finrank F C) : IsRealClosed F :=
  have : Algebra.IsQuadraticExtension F C := ⟨finrank_eq_two_of_isAlgClosed h⟩
  isRealClosed_of_isAlgClosed_of_isQuadraticExtension (K := C)

omit [IsAlgClosed C] in
/-- Below the fixed field of a nontrivial automorphism `σ` of finite order, `C` has degree
`orderOf σ > 1`. -/
private theorem one_lt_finrank_fixedField_zpowers {k : Type*} [Field k] [Algebra k C]
    {σ : C ≃ₐ[k] C} (hσ : IsOfFinOrder σ) (h1 : σ ≠ 1) :
    1 < finrank (fixedField (Subgroup.zpowers σ)) C := by
  have : Finite (Subgroup.zpowers σ) := finite_zpowers.2 hσ
  have hne : orderOf σ ≠ 1 := mt orderOf_eq_one_iff.1 h1
  have := hσ.orderOf_pos
  rw [finrank_fixedField_zpowers_eq_orderOf]
  omega

/-- A nontrivial automorphism of finite order of an algebraically closed field has order two. -/
theorem orderOf_eq_two_of_isOfFinOrder {k : Type*} [Field k] [Algebra k C] {σ : C ≃ₐ[k] C}
    (hσ : IsOfFinOrder σ) (h1 : σ ≠ 1) : orderOf σ = 2 := by
  have : Finite (Subgroup.zpowers σ) := finite_zpowers.2 hσ
  rw [← finrank_fixedField_zpowers_eq_orderOf]
  exact finrank_eq_two_of_isAlgClosed (one_lt_finrank_fixedField_zpowers hσ h1)

/-- The fixed field of a nontrivial automorphism of finite order of an algebraically closed field is
real closed. -/
theorem isRealClosed_fixedField_zpowers {k : Type*} [Field k] [Algebra k C] {σ : C ≃ₐ[k] C}
    (hσ : IsOfFinOrder σ) (h1 : σ ≠ 1) : IsRealClosed (fixedField (Subgroup.zpowers σ)) :=
  isRealClosed_of_isAlgClosed_of_one_lt_finrank (one_lt_finrank_fixedField_zpowers hσ h1)

end TauCeti.RealClosure
