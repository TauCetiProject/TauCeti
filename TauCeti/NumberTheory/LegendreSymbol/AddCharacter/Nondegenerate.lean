/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Group.AddChar.Basic
public import TauCeti.NumberTheory.LegendreSymbol.AddCharacter
public import TauCeti.RingTheory.Idempotents.Connected.Spectrum
import TauCeti.FieldTheory.Trace

/-!
# Nondegenerate additive characters

An additive character `ψ : ZMod p → Λ` of the prime field with values in a commutative ring `Λ`
is *nondegenerate* when `ψ 1 - 1` is a unit of `Λ`. These are the coefficient characters of the
`ℓ`-adic Fourier transform: the finite Fourier transform of `Λ`-valued functions on a vector space
over a finite field of characteristic `p`, and the Artin–Schreier sheaves built from `ψ`, need
exactly this condition to make the orthogonality relations and Fourier inversion hold over an
arbitrary coefficient ring, not just a domain.

Nontriviality is the wrong condition outside local rings: the character of `ZMod 3` with values in
`ZMod 7 × ZMod 7` and `ψ 1 = (2, 1)` is nontrivial, but `ψ 1 - 1 = (1, 0)` is not a unit and the
character sum is `(0, 3) ≠ 0`. Over a local ring in which `p` is invertible, the two conditions
agree.

## Main definitions and results

* `AddChar.IsNondegenerate`: `ψ 1 - 1` is a unit.
* `AddChar.IsNondegenerate.isUnit_sub_one`: then `ψ a - 1` is a unit for every `a ≠ 0`;
  `AddChar.IsNondegenerate.apply_ne_one`: over a nontrivial ring, `ψ a ≠ 1` for every `a ≠ 0`.
* `AddChar.IsNondegenerate.isUnit_natCast`, `AddChar.IsNondegenerate.isRoot_cyclotomic`: `p` is a
  unit of `Λ`, and `ψ 1` is a root of the `p`-th cyclotomic polynomial.
* `AddChar.IsNondegenerate.isPrimitive`: over a nontrivial ring, a nondegenerate character is
  primitive in Mathlib's sense.
* `AddChar.IsNondegenerate.inv`, `AddChar.IsNondegenerate.mulShift`, `AddChar.IsNondegenerate.map`:
  nondegeneracy passes to the inverse character, to nonzero multiplicative shifts and along ring
  homomorphisms.
* `AddChar.isNondegenerate_iff_forall_isMaximal_ne_one`: `ψ` is nondegenerate if and only if its
  reduction modulo every maximal ideal is nontrivial;
  `AddChar.isNondegenerate_iff_ne_one_and_isUnit_natCast`: over a local ring, if and only if `ψ`
  is nontrivial and `p` is a unit.
* `AddChar.IsNondegenerate.coprime_ringChar`: the characteristic of `Λ`, when positive, is prime
  to `p`.
* `AddChar.IsNondegenerate.sum_mulShift`: orthogonality on `ZMod p`, `∑ x, ψ (x * y)` is `p` at
  `y = 0` and `0` elsewhere.
* `AddChar.IsNondegenerate.sum_trace_mul`: orthogonality over a finite field `k` of characteristic
  `p`, `∑ x, ψ (Tr (x * y))` is `#k` at `y = 0` and `0` elsewhere.
* `AddChar.IsNondegenerate.mulShift_bijective`: if `Spec Λ` is connected, every additive
  character of `ZMod p` with values in `Λ` is `a ↦ ψ (c * a)` for a unique `c`.
* `AddChar.IsNondegenerate.mulShift_compAddMonoidHom_trace_bijective`: if `Spec Λ` is connected,
  every additive character of `k` with values in `Λ` is `x ↦ ψ (Tr (c * x))` for a unique `c`.

When `Λ` is a domain, Mathlib's `AddChar.sum_mulShift` and Tau Ceti's
`Submodule.sum_addChar_dotProduct` give the orthogonality relation for primitive characters. The
statements here instead allow any commutative coefficient ring, at the price of nondegeneracy.

## References

* N. Katz, G. Laumon, *Transformation de Fourier et majoration de sommes exponentielles*,
  Publ. Math. IHÉS 62 (1985), §2.1 (nontrivial characters into local rings).
* G. Laumon, *Transformation de Fourier, constantes d'équations fonctionnelles et conjecture de
  Weil*, Publ. Math. IHÉS 65 (1987), (0.2) (additive characters of a finite field are
  `x ↦ ψ (Tr (c * x))`).
-/

public section

open Finset

namespace AddChar

variable {p : ℕ} [Fact p.Prime] {Λ Λ' : Type*} [CommRing Λ] [CommRing Λ']
  {ψ : AddChar (ZMod p) Λ}

/-- An additive character `ψ` of `ZMod p` with values in a commutative ring is *nondegenerate*
when `ψ 1 - 1` is a unit. Then `ψ a - 1` is a unit for every `a ≠ 0`
(`AddChar.IsNondegenerate.isUnit_sub_one`) and `p` is a unit
(`AddChar.IsNondegenerate.isUnit_natCast`).
Over a local ring in which `p` is a unit this is nontriviality of `ψ`. -/
def IsNondegenerate (ψ : AddChar (ZMod p) Λ) : Prop :=
  IsUnit (ψ 1 - 1)

theorem isNondegenerate_iff : ψ.IsNondegenerate ↔ IsUnit (ψ 1 - 1) :=
  Iff.rfl

/-- A nondegenerate character satisfies `IsUnit (ψ a - 1)` at every nonzero `a`. -/
theorem IsNondegenerate.isUnit_sub_one (hψ : ψ.IsNondegenerate) {a : ZMod p} (ha : a ≠ 0) :
    IsUnit (ψ a - 1) := by
  have h : ψ 1 = ψ a ^ (a⁻¹).val := by
    rw [← map_nsmul_eq_pow, nsmul_eq_mul, ZMod.natCast_zmod_val, inv_mul_cancel₀ ha]
  refine isUnit_of_dvd_unit ?_ hψ
  simpa only [h, one_pow] using sub_dvd_pow_sub_pow (ψ a) 1 (a⁻¹).val

/-- A character is nondegenerate if and only if `ψ a - 1` is a unit at every nonzero `a`. -/
theorem isNondegenerate_iff_forall_isUnit_sub_one :
    ψ.IsNondegenerate ↔ ∀ a : ZMod p, a ≠ 0 → IsUnit (ψ a - 1) :=
  ⟨fun hψ _ ↦ hψ.isUnit_sub_one, fun h ↦ h 1 one_ne_zero⟩

/-- A nondegenerate character into a nontrivial ring takes the value `1` only at `0`. -/
theorem IsNondegenerate.apply_ne_one [Nontrivial Λ] (hψ : ψ.IsNondegenerate) {a : ZMod p}
    (ha : a ≠ 0) : ψ a ≠ 1 := fun h ↦ by
  simpa [h] using hψ.isUnit_sub_one ha

/-- A nondegenerate character into a nontrivial ring is injective. -/
theorem IsNondegenerate.injective [Nontrivial Λ] (hψ : ψ.IsNondegenerate) :
    Function.Injective ψ := by
  intro a b hab
  by_contra h
  refine hψ.apply_ne_one (sub_ne_zero.2 h) <| (ψ.val_isUnit b).mul_left_injective ?_
  dsimp only
  rw [← map_add_eq_mul, sub_add_cancel, hab, one_mul]

/-- For every character `ψ` of `ZMod p`, the geometric sum of `ψ 1` is killed by `ψ 1 - 1`. -/
private theorem geom_sum_mul_sub_one_eq_zero (ψ : AddChar (ZMod p) Λ) :
    (∑ i ∈ range p, ψ 1 ^ i) * (ψ 1 - 1) = 0 := by
  rw [geom_sum_mul, AddChar.pow_char_eq_one, sub_self]

/-- The powers `ψ 1 ^ i`, `i < p`, of a nondegenerate character sum to zero. -/
theorem IsNondegenerate.geom_sum_eq_zero (hψ : ψ.IsNondegenerate) :
    ∑ i ∈ range p, ψ 1 ^ i = 0 :=
  hψ.mul_left_eq_zero.1 (geom_sum_mul_sub_one_eq_zero ψ)

/-- The value at `1` of a nondegenerate character is a root of the `p`-th cyclotomic polynomial. -/
theorem IsNondegenerate.isRoot_cyclotomic (hψ : ψ.IsNondegenerate) :
    (Polynomial.cyclotomic p Λ).IsRoot (ψ 1) := by
  simpa [Polynomial.cyclotomic_prime, Polynomial.eval_geom_sum] using hψ.geom_sum_eq_zero

/-- If `ψ` is nondegenerate, then `p` is a unit of `Λ`. -/
theorem IsNondegenerate.isUnit_natCast (hψ : ψ.IsNondegenerate) : IsUnit (p : Λ) := by
  -- Modulo a maximal ideal containing `p`, `ψ 1` would be a `p`-th root of unity in
  -- characteristic `p`, hence equal to `1`.
  by_contra h
  obtain ⟨m, hm, hpm⟩ := exists_max_ideal_of_mem_nonunits h
  let := Ideal.Quotient.field m
  have hp : ((p : ℕ) : Λ ⧸ m) = 0 := by
    rw [← map_natCast (Ideal.Quotient.mk m), Ideal.Quotient.eq_zero_iff_mem]
    exact hpm
  have : CharP (Λ ⧸ m) p := (CharP.charP_iff_prime_eq_zero Fact.out).2 hp
  have hu : IsUnit (Ideal.Quotient.mk m (ψ 1) - 1) := by
    simpa using IsUnit.map (Ideal.Quotient.mk m) hψ
  have hz : (Ideal.Quotient.mk m (ψ 1) - 1) ^ p = 0 := by
    rw [sub_pow_char, one_pow, ← map_pow, AddChar.pow_char_eq_one, map_one, sub_self]
  exact hu.ne_zero (pow_eq_zero_iff (Fact.out : p.Prime).ne_zero |>.1 hz)

/-- If `Λ` has positive characteristic, for instance if `Λ` is finite, and carries a nondegenerate
character, then its characteristic is prime to `p`. -/
theorem IsNondegenerate.coprime_ringChar (hψ : ψ.IsNondegenerate) (h0 : ringChar Λ ≠ 0) :
    (ringChar Λ).Coprime p := by
  rw [Nat.coprime_comm, Nat.Prime.coprime_iff_not_dvd Fact.out]
  rintro ⟨m, hm⟩
  have hm0 : m ≠ 0 := by rintro rfl; exact h0 (by simpa using hm)
  have hdvd : ringChar Λ ∣ m := ringChar.dvd <| by
    rw [← hψ.isUnit_natCast.mul_right_eq_zero, ← Nat.cast_mul, ← hm, ringChar.Nat.cast_ringChar]
  have := Nat.le_of_dvd (Nat.pos_of_ne_zero hm0) hdvd
  rw [hm] at this
  nlinarith [(Fact.out : p.Prime).two_le, Nat.pos_of_ne_zero hm0]

/-- The inverse of a nondegenerate character is nondegenerate. -/
theorem IsNondegenerate.inv (hψ : ψ.IsNondegenerate) : ψ⁻¹.IsNondegenerate := by
  simpa [IsNondegenerate] using hψ.isUnit_sub_one (neg_ne_zero.2 one_ne_zero)

/-- The multiplicative shift `a ↦ ψ (c * a)` of a nondegenerate character by `c ≠ 0` is
nondegenerate. -/
theorem IsNondegenerate.mulShift (hψ : ψ.IsNondegenerate) {c : ZMod p} (hc : c ≠ 0) :
    (ψ.mulShift c).IsNondegenerate := by
  simpa [IsNondegenerate] using hψ.isUnit_sub_one hc

/-- The composite of a nondegenerate character with a ring homomorphism is nondegenerate. In
particular nondegeneracy survives reduction modulo every ideal. -/
theorem IsNondegenerate.map (hψ : ψ.IsNondegenerate) (f : Λ →+* Λ') :
    (f.toMonoidHom.compAddChar ψ).IsNondegenerate := by
  simpa [IsNondegenerate] using IsUnit.map f hψ

/-- A nondegenerate character into a nontrivial ring is primitive. -/
theorem IsNondegenerate.isPrimitive [Nontrivial Λ] (hψ : ψ.IsNondegenerate) : ψ.IsPrimitive :=
  fun _ ha h ↦ hψ.apply_ne_one ha (by simpa using DFunLike.congr_fun h 1)

/-- **Orthogonality** on `ZMod p` for a nondegenerate character: `∑ x, ψ (x * y)` is `p` at
`y = 0` and vanishes elsewhere. This is the `ZMod p` analogue of Mathlib's `AddChar.sum_mulShift`,
with its `IsDomain` and `IsPrimitive` hypotheses replaced by nondegeneracy. -/
theorem IsNondegenerate.sum_mulShift (hψ : ψ.IsNondegenerate) (y : ZMod p) :
    ∑ x, ψ (x * y) = if y = 0 then (p : Λ) else 0 := by
  split_ifs with hy
  · simp [hy, ZMod.card]
  simp_rw [mul_comm _ y, ← mulShift_apply]
  exact sum_eq_zero_of_sub_one_mem_nonZeroDivisors (b := 1)
    (by simpa using (hψ.isUnit_sub_one hy).mem_nonZeroDivisors)

/-- A character is nondegenerate if and only if its reduction modulo every maximal ideal is
nontrivial. -/
theorem isNondegenerate_iff_forall_isMaximal_ne_one :
    ψ.IsNondegenerate ↔
      ∀ m : Ideal Λ, m.IsMaximal → (Ideal.Quotient.mk m).toMonoidHom.compAddChar ψ ≠ 1 := by
  refine ⟨fun hψ m hm h ↦ ?_, fun h ↦ by_contra fun hψ ↦ ?_⟩
  · have h1 : Ideal.Quotient.mk m (ψ 1) = 1 := by simpa using DFunLike.congr_fun h 1
    let := Ideal.Quotient.field m
    simpa [h1] using IsUnit.map (Ideal.Quotient.mk m) hψ
  · obtain ⟨m, hm, hmem⟩ := exists_max_ideal_of_mem_nonunits hψ
    have h1 : Ideal.Quotient.mk m (ψ 1) = 1 := by
      simpa [sub_eq_zero] using Ideal.Quotient.eq_zero_iff_mem.2 hmem
    exact (zmod_char_ne_one_iff p _).1 (h m hm) (by simpa using h1)

/-- Over a local ring, a character is nondegenerate if and only if it is nontrivial and `p` is a
unit, that is, the residue characteristic is not `p`. In residue characteristic `p` no character
is nondegenerate. -/
theorem isNondegenerate_iff_ne_one_and_isUnit_natCast [IsLocalRing Λ] :
    ψ.IsNondegenerate ↔ ψ ≠ 1 ∧ IsUnit (p : Λ) := by
  refine ⟨fun hψ ↦ ⟨fun h ↦ ?_, hψ.isUnit_natCast⟩, fun ⟨hne, hp⟩ ↦ ?_⟩
  · simp [IsNondegenerate, h] at hψ
  rw [zmod_char_ne_one_iff] at hne
  by_contra hu
  have hmem : ψ 1 - 1 ∈ IsLocalRing.maximalIdeal Λ := (IsLocalRing.mem_maximalIdeal _).2 hu
  have hsum : IsUnit (∑ i ∈ range p, ψ 1 ^ i) := by
    by_contra hs
    have h1 : ∑ i ∈ range p, ψ 1 ^ i - p ∈ IsLocalRing.maximalIdeal Λ := by
      have : ∑ i ∈ range p, ψ 1 ^ i - p = ∑ i ∈ range p, (ψ 1 ^ i - 1) := by
        simp [sum_sub_distrib]
      rw [this]
      refine Ideal.sum_mem _ fun i _ ↦ Ideal.mem_of_dvd _ ?_ hmem
      simpa using sub_dvd_pow_sub_pow (ψ 1) 1 i
    have hpm : (p : Λ) ∈ IsLocalRing.maximalIdeal Λ := by simpa using Ideal.sub_mem _ hs h1
    exact (IsLocalRing.mem_maximalIdeal _).1 hpm hp
  exact hne (sub_eq_zero.1 <| hsum.mul_right_eq_zero.1 (geom_sum_mul_sub_one_eq_zero ψ))

section FiniteField

variable (k : Type*) [Field k] [Algebra (ZMod p) k]

attribute [local instance] TauCeti.nontrivial_of_connectedSpace_primeSpectrum

/-- **Orthogonality** for a nondegenerate character over a finite field `k` of characteristic `p`:
`∑ x, ψ (Tr (x * y))` is `#k` at `y = 0` and vanishes elsewhere. -/
theorem IsNondegenerate.sum_trace_mul [Fintype k] [DecidableEq k] (hψ : ψ.IsNondegenerate) (y : k) :
    ∑ x : k, ψ (Algebra.trace (ZMod p) k (x * y)) =
      if y = 0 then (Fintype.card k : Λ) else 0 := by
  split_ifs with hy
  · simp [hy]
  obtain ⟨x₀, hx₀⟩ := TauCeti.Algebra.exists_trace_mul_ne_zero (F := ZMod p) hy
  rw [mul_comm] at hx₀
  have h := sum_eq_zero_of_sub_one_mem_nonZeroDivisors
    (φ := ψ.compAddMonoidHom ((Algebra.trace (ZMod p) k).toAddMonoidHom.comp
      (AddMonoidHom.mulRight y))) (b := x₀)
    (by simpa using (hψ.isUnit_sub_one hx₀).mem_nonZeroDivisors)
  simpa using h

/-- The character `ψ ∘ Tr` of a finite field `k` of characteristic `p` is primitive when `ψ` is
nondegenerate and `Λ` is nontrivial. -/
theorem IsNondegenerate.isPrimitive_compAddMonoidHom_trace [Finite k] [Nontrivial Λ]
    (hψ : ψ.IsNondegenerate) :
    (ψ.compAddMonoidHom (Algebra.trace (ZMod p) k).toAddMonoidHom).IsPrimitive := by
  intro c hc h
  obtain ⟨x, hx⟩ := TauCeti.Algebra.exists_trace_mul_ne_zero (F := ZMod p) hc
  exact hψ.apply_ne_one hx (by simpa using DFunLike.congr_fun h x)

/-- Every additive character of `ZMod p` with values in a ring with connected spectrum takes the
value `ψ c` at `1` for some `c`. -/
private theorem IsNondegenerate.exists_apply_eq [ConnectedSpace (PrimeSpectrum Λ)]
    (hψ : ψ.IsNondegenerate) (χ : AddChar (ZMod p) Λ) : ∃ c, ψ c = χ 1 := by
  -- Split `1` into the orthogonal idempotents `e i = p⁻¹ ∑ⱼ ψ (-(i * j)) χ j`, on which `χ 1`
  -- acts by `ψ i`; connectedness makes one of them equal to `1`.
  obtain ⟨v, hv⟩ := hψ.isUnit_natCast.exists_left_inv
  obtain ⟨e, he⟩ : ∃ e : ZMod p → Λ, ∀ i, e i = v * ∑ j, ψ (-(i * j)) * χ j := ⟨_, fun _ ↦ rfl⟩
  -- `χ a` acts on `e i` by `ψ (i * a)`.
  have hshift (a i : ZMod p) : χ a * e i = ψ (i * a) * e i := by
    have hs : ∑ j, χ a * (ψ (-(i * j)) * χ j) = ∑ j, ψ (i * a) * (ψ (-(i * j)) * χ j) :=
      Fintype.sum_equiv (Equiv.addLeft a) _ _ fun j ↦ by
        -- Split `-(i * j)` as `i * a + -(i * (a + j))`; the rest is multiplicativity.
        have hij : -(i * j) = i * a + -(i * (a + j)) := by ring
        simp only [Equiv.coe_addLeft, hij, map_add_eq_mul]
        ring
    rw [he, mul_left_comm, mul_sum, hs, ← mul_sum]
    ring
  -- The `e i` sum to `1`, by orthogonality on `ZMod p`.
  have horth (j : ZMod p) : ∑ i, ψ (-(i * j)) = if j = 0 then (p : Λ) else 0 := by
    simpa [mul_neg] using hψ.sum_mulShift (-j)
  have hsum : ∑ i, e i = 1 := by
    simp only [he, ← mul_sum]
    rw [sum_comm]
    simp [← sum_mul, horth, hv]
  -- Each `e i` is idempotent.
  have hidem (i : ZMod p) : IsIdempotentElem (e i) := by
    have h (j : ZMod p) : ψ (-(i * j)) * χ j * e i = e i := by
      rw [mul_assoc, hshift, ← mul_assoc, ← map_add_eq_mul, neg_add_cancel, map_zero_eq_one,
        one_mul]
    calc e i * e i = v * ∑ j, ψ (-(i * j)) * χ j * e i := by
          nth_rw 1 [he i]
          rw [mul_assoc, sum_mul]
      _ = e i := by simp [h, ZMod.card, ← mul_assoc, hv]
  obtain ⟨i, hi⟩ : ∃ i, e i ≠ 0 := by
    by_contra! h
    simp [h] at hsum
  have hi1 : e i = 1 := (hidem i).eq_zero_or_eq_one_of_preconnectedSpace.resolve_left hi
  exact ⟨i, by simpa [hi1] using (hshift 1 i).symm⟩

/-- **Classification of additive characters of `ZMod p`.** If `Spec Λ` is connected, every
additive character of `ZMod p` with values in `Λ` is `a ↦ ψ (c * a)` for a unique `c`. -/
theorem IsNondegenerate.mulShift_bijective [ConnectedSpace (PrimeSpectrum Λ)]
    (hψ : ψ.IsNondegenerate) : Function.Bijective ψ.mulShift := by
  refine ⟨to_mulShift_inj_of_isPrimitive hψ.isPrimitive, fun χ ↦ ?_⟩
  obtain ⟨c, hc⟩ := hψ.exists_apply_eq χ
  refine ⟨c, ext _ _ fun a ↦ ?_⟩
  obtain ⟨n, rfl⟩ := ZMod.natCast_zmod_surjective a
  have hχ : χ n = χ 1 ^ n := by simpa using map_nsmul_eq_pow χ n 1
  rw [mulShift_apply, mul_comm]
  simpa [nsmul_eq_mul, hc, hχ] using map_nsmul_eq_pow ψ n c

/-- **Classification of additive characters of a finite field.** If `Spec Λ` is connected, every
additive character of a finite field `k` of characteristic `p` with values in `Λ` is
`x ↦ ψ (Tr (c * x))` for a unique `c ∈ k`. -/
theorem IsNondegenerate.mulShift_compAddMonoidHom_trace_bijective [Finite k]
    [ConnectedSpace (PrimeSpectrum Λ)] (hψ : ψ.IsNondegenerate) :
    Function.Bijective (ψ.compAddMonoidHom (Algebra.trace (ZMod p) k).toAddMonoidHom).mulShift := by
  refine ⟨to_mulShift_inj_of_isPrimitive (hψ.isPrimitive_compAddMonoidHom_trace k), fun χ ↦ ?_⟩
  -- Write `χ = ψ ∘ f` for an additive `f : k → ZMod p`, and represent `f` by the trace form.
  have hf (x : k) : ∃ c, ψ c = χ x := by
    simpa using hψ.exists_apply_eq
      (χ.compAddMonoidHom ((AddMonoidHom.mulRight x).comp (algebraMap (ZMod p) k).toAddMonoidHom))
  choose f hf using hf
  let F : k →+ ZMod p :=
    { toFun := f
      map_zero' := hψ.injective (by simp [hf])
      map_add' := fun x y ↦ hψ.injective (by simp [hf, map_add_eq_mul]) }
  refine ⟨((Algebra.traceForm (ZMod p) k).toDual (traceForm_nondegenerate (ZMod p) k)).symm
    (F.toZModLinearMap p), ?_⟩
  ext y
  have := LinearMap.BilinForm.apply_toDual_symm_apply (hB := traceForm_nondegenerate (ZMod p) k)
    (F.toZModLinearMap p) y
  simp only [F, Algebra.traceForm_apply, AddMonoidHom.coe_toZModLinearMap, AddMonoidHom.coe_mk,
    ZeroHom.coe_mk] at this
  simpa [F, mulShift_apply, this] using hf y

end FiniteField

/-! ### Examples -/

/-- On `ZMod 3` with values in `ZMod 7`, the character with `ψ 1 = 2` is nondegenerate. -/
example : (zmodChar 3 (by decide : (2 : ZMod 7) ^ 3 = 1)).IsNondegenerate := by
  rw [isNondegenerate_iff, zmodChar_apply, ZMod.val_one]
  exact (by decide : (2 : ZMod 7) ^ 1 - 1 = 1) ▸ isUnit_one

/-- On `ZMod 3` with values in `ZMod 7 × ZMod 7`, the character with `ψ 1 = (2, 1)` is nontrivial
but degenerate: nontriviality is the wrong condition outside local rings. -/
example : zmodChar 3 (by decide : ((2, 1) : ZMod 7 × ZMod 7) ^ 3 = 1) ≠ 1 ∧
    ¬(zmodChar 3 (by decide : ((2, 1) : ZMod 7 × ZMod 7) ^ 3 = 1)).IsNondegenerate := by
  rw [zmod_char_ne_one_iff, isNondegenerate_iff, zmodChar_apply, ZMod.val_one, pow_one,
    Prod.isUnit_iff]
  refine ⟨by decide, fun h ↦ ?_⟩
  have h0 : IsUnit (0 : ZMod 7) := by simpa using h.2
  exact absurd (isUnit_zero_iff.1 h0) (by decide)

end AddChar
