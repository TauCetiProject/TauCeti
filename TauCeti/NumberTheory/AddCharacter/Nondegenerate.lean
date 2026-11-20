/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.FieldTheory.Finite.Trace
public import Mathlib.NumberTheory.AddCharacter.Trace
public import Mathlib.RingTheory.Polynomial.Cyclotomic.Basic
public import TauCeti.Algebra.Group.AddChar
public import TauCeti.RingTheory.Idempotents.Connected.Spectrum

/-!
# Nondegenerate additive characters of `ZMod p`

An additive character `ψ : ZMod p → Λ` of the prime field with values in a commutative ring `Λ` is
*nondegenerate* when `ψ 1 - 1` is a unit of `Λ`. This is the condition under which the finite
Fourier transform of `Λ`-valued functions on a finite vector space is invertible, and the
coefficient condition for the Artin–Schreier sheaves in the `ℓ`-adic Fourier transform of
Deligne, Katz and Laumon. Over a domain, or more generally over a local ring whose residue
characteristic is not `p`, it says that `ψ` is nontrivial. Over a ring such as `ZMod 7 × ZMod 7`
nontriviality is too weak, and nondegeneracy is what makes the orthogonality relations hold.

## Main definitions

* `AddChar.IsNondegenerate`: `ψ 1 - 1` is a unit.

## Main results

* `AddChar.IsNondegenerate.isUnit_sub_one`: `ψ a - 1` is a unit for every `a ≠ 0`.
* `AddChar.IsNondegenerate.isUnit_natCast`: `p` is a unit of `Λ`.
* `AddChar.IsNondegenerate.isRoot_cyclotomic`: `ψ 1` is a root of the `p`-th cyclotomic
  polynomial.
* `AddChar.IsNondegenerate.isPrimitive`: over a nontrivial ring, a nondegenerate character is
  primitive.
* `AddChar.IsNondegenerate.sum_comp_eq_ite`: for an additive map `f` from a finite group to
  `ZMod p`, `∑ x, ψ (f x)` is the order of the group if `f = 0` and `0` otherwise.
* `AddChar.IsNondegenerate.sum_trace_mul_eq_ite`: the orthogonality relation
  `∑ x : k, ψ (Tr (x * y)) = if y = 0 then #k else 0` over a finite field `k` of
  characteristic `p`.
* `AddChar.isNondegenerate_iff_forall_isMaximal`: `ψ` is nondegenerate if and only if its
  reduction modulo every maximal ideal is nontrivial.
* `AddChar.isNondegenerate_iff_of_isLocalRing`: over a local ring, `ψ` is nondegenerate if and
  only if `p` is a unit and `ψ` is nontrivial.
* `AddChar.IsNondegenerate.exists_eq_apply`: if `Spec Λ` is connected, every `p`-th root of
  unity of `Λ` is a value of `ψ`.
* `AddChar.IsNondegenerate.existsUnique_trace_mul`: if `Spec Λ` is connected, every additive
  character of a finite field `k` of characteristic `p` is `x ↦ ψ (Tr (c * x))` for a unique
  `c ∈ k`.

## References

* [N. Katz, G. Laumon, *Transformation de Fourier et majoration de sommes exponentielles*,
  Publ. Math. IHÉS 62 (1985)], §2.
* [G. Laumon, *Transformation de Fourier, constantes d'équations fonctionnelles et conjecture de
  Weil*, Publ. Math. IHÉS 65 (1987)], (0.2).
-/

public section

open Finset

namespace AddChar

variable {p : ℕ} [Fact p.Prime] {Λ : Type*} [CommRing Λ] {ψ : AddChar (ZMod p) Λ}

/-- An additive character `ψ` of `ZMod p` with values in a commutative ring is *nondegenerate*
when `ψ 1 - 1` is a unit. Then `ψ a - 1` is a unit for every `a ≠ 0`
(`AddChar.IsNondegenerate.isUnit_sub_one`), and `p` is a unit
(`AddChar.IsNondegenerate.isUnit_natCast`). -/
def IsNondegenerate (ψ : AddChar (ZMod p) Λ) : Prop :=
  IsUnit (ψ 1 - 1)

theorem isNondegenerate_iff : ψ.IsNondegenerate ↔ IsUnit (ψ 1 - 1) :=
  Iff.rfl

/-- The character of `ZMod p` sending `1` to a `p`-th root of unity `ζ` is nondegenerate exactly
when `ζ - 1` is a unit. -/
@[simp]
theorem isNondegenerate_zmodChar_iff {ζ : Λ} (hζ : ζ ^ p = 1) :
    (zmodChar p hζ).IsNondegenerate ↔ IsUnit (ζ - 1) := by
  rw [isNondegenerate_iff, zmodChar_apply, ZMod.val_one, pow_one]

/-- For a nondegenerate character, `ψ a - 1` is a unit for every nonzero `a`. -/
theorem IsNondegenerate.isUnit_sub_one (hψ : ψ.IsNondegenerate) {a : ZMod p} (ha : a ≠ 0) :
    IsUnit (ψ a - 1) := by
  -- `ψ 1` is a power of `ψ a`, so `ψ a - 1` divides the unit `ψ 1 - 1`
  have h : ψ 1 = ψ a ^ (a⁻¹).val := by
    rw [← map_nsmul_eq_pow, nsmul_eq_mul, ZMod.natCast_zmod_val, inv_mul_cancel₀ ha]
  refine isUnit_of_dvd_unit ?_ hψ
  simpa [h] using sub_dvd_pow_sub_pow (ψ a) 1 (a⁻¹).val

/-- A character of `ZMod p` is nondegenerate if and only if `ψ a - 1` is a unit for every
nonzero `a`. -/
theorem isNondegenerate_iff_forall_isUnit :
    ψ.IsNondegenerate ↔ ∀ a : ZMod p, a ≠ 0 → IsUnit (ψ a - 1) :=
  ⟨fun hψ _ ha ↦ hψ.isUnit_sub_one ha, fun h ↦ h 1 one_ne_zero⟩

/-- Over a nontrivial ring, a nondegenerate character takes the value `1` only at `0`. -/
@[simp]
theorem IsNondegenerate.apply_eq_one_iff [Nontrivial Λ] (hψ : ψ.IsNondegenerate) {a : ZMod p} :
    ψ a = 1 ↔ a = 0 := by
  refine ⟨fun h ↦ ?_, fun h ↦ by rw [h, map_zero_eq_one]⟩
  by_contra ha
  simpa [h] using hψ.isUnit_sub_one ha

/-- Over a nontrivial ring, a nondegenerate character is injective. -/
theorem IsNondegenerate.injective [Nontrivial Λ] (hψ : ψ.IsNondegenerate) :
    Function.Injective ψ := by
  intro a b h
  rw [← sub_eq_zero, ← hψ.apply_eq_one_iff]
  apply (ψ.val_isUnit b).mul_left_injective
  dsimp only
  rw [← map_add_eq_mul, sub_add_cancel, h, one_mul]

/-- Over a nontrivial ring, a nondegenerate character is nontrivial. -/
theorem IsNondegenerate.ne_one [Nontrivial Λ] (hψ : ψ.IsNondegenerate) : ψ ≠ 1 :=
  ne_one_iff.2 ⟨1, by simpa using hψ.apply_eq_one_iff.not.2 one_ne_zero⟩

/-- Over a nontrivial ring, a nondegenerate character is primitive: every shift `x ↦ ψ (a * x)`
by `a ≠ 0` is nontrivial. -/
theorem IsNondegenerate.isPrimitive [Nontrivial Λ] (hψ : ψ.IsNondegenerate) : ψ.IsPrimitive :=
  fun a ha h ↦ ha <| hψ.apply_eq_one_iff.1 <| by simpa using DFunLike.congr_fun h 1

/-- Over a nontrivial ring, the value at `1` of a nondegenerate character is a primitive `p`-th
root of unity. -/
theorem IsNondegenerate.isPrimitiveRoot [Nontrivial Λ] (hψ : ψ.IsNondegenerate) :
    IsPrimitiveRoot (ψ 1) p where
  pow_eq_one := ψ.pow_char_eq_one p 1
  dvd_of_pow_eq_one l hl := by
    rwa [← map_nsmul_eq_pow, nsmul_one, hψ.apply_eq_one_iff, ZMod.natCast_eq_zero_iff] at hl

/-- Composing a nondegenerate character with the trace of a `ZMod p`-algebra `A` gives Mathlib's
`AddChar.traceChar` at the primitive root `ψ 1`. -/
theorem IsNondegenerate.compAddMonoidHom_trace_eq_traceChar [Nontrivial Λ] (hψ : ψ.IsNondegenerate)
    (A : Type*) [CommRing A] [Algebra (ZMod p) A] :
    ψ.compAddMonoidHom (Algebra.trace (ZMod p) A).toAddMonoidHom =
      traceChar A hψ.isPrimitiveRoot := by
  ext x
  rw [coe_compAddMonoidHom, Function.comp_apply, traceChar_apply, ← map_nsmul_eq_pow, nsmul_one,
    ZMod.natCast_zmod_val, LinearMap.toAddMonoidHom_coe]

/-- The prime `p` is a unit in a ring carrying a nondegenerate character of `ZMod p`. -/
theorem IsNondegenerate.isUnit_natCast (hψ : ψ.IsNondegenerate) : IsUnit (p : Λ) := by
  -- expanding `ψ 1 ^ p = ((ψ 1 - 1) + 1) ^ p` shows that the unit `(ψ 1 - 1) ^ p` is a multiple
  -- of `p`
  obtain ⟨r, hr⟩ := exists_add_pow_prime_eq (Fact.out : p.Prime) (ψ 1 - 1) 1
  rw [sub_add_cancel, ψ.pow_char_eq_one p, one_pow, mul_one] at hr
  have h : (ψ 1 - 1) ^ p = p * (-((ψ 1 - 1) * r)) := by linear_combination -hr
  exact isUnit_of_mul_isUnit_left (h ▸ hψ.pow p)

/-- The characteristic of a ring with a nondegenerate character of `ZMod p` is prime to `p`, as
soon as it is nonzero, for instance for a finite ring. -/
theorem IsNondegenerate.coprime_ringChar (hψ : ψ.IsNondegenerate) (h : ringChar Λ ≠ 0) :
    (ringChar Λ).Coprime p := by
  refine Nat.Coprime.symm <| (Nat.Prime.coprime_iff_not_dvd Fact.out).2 fun ⟨m, hm⟩ ↦ ?_
  have hm0 : (m : Λ) = 0 :=
    hψ.isUnit_natCast.mul_right_eq_zero.1 <| by
      rw [← Nat.cast_mul, ← hm, ringChar.Nat.cast_ringChar]
  have hpos : 0 < m := Nat.pos_of_ne_zero <| by rintro rfl; simp [hm] at h
  have := Nat.le_of_dvd hpos <| (ringChar.spec Λ m).1 hm0
  nlinarith [(Fact.out : p.Prime).two_le]

/-- The values of a nondegenerate character sum to zero. -/
theorem IsNondegenerate.sum_eq_zero (hψ : ψ.IsNondegenerate) : ∑ a, ψ a = 0 :=
  sum_eq_zero_of_isLeftRegular_sub_one hψ.isRegular.left

/-- The value at `1` of a nondegenerate character is a root of the `p`-th cyclotomic polynomial
`1 + X + ⋯ + X ^ (p - 1)`. -/
theorem IsNondegenerate.isRoot_cyclotomic (hψ : ψ.IsNondegenerate) :
    (Polynomial.cyclotomic p Λ).IsRoot (ψ 1) := by
  rw [Polynomial.IsRoot, Polynomial.cyclotomic_prime, Polynomial.eval_geom_sum]
  refine hψ.mul_left_eq_zero.1 ?_
  rw [geom_sum_mul, ψ.pow_char_eq_one p, sub_self]

/-- **Orthogonality.** For an additive map `f` from a finite group to `ZMod p`, the sum of a
nondegenerate character over the values of `f` is the order of the group if `f = 0` and `0`
otherwise. -/
theorem IsNondegenerate.sum_comp_eq_ite (hψ : ψ.IsNondegenerate) {G : Type*} [AddGroup G]
    [Fintype G] (f : G →+ ZMod p) [Decidable (f = 0)] :
    ∑ x, ψ (f x) = if f = 0 then (Fintype.card G : Λ) else 0 := by
  split_ifs with hf
  · simp [hf]
  obtain ⟨b, hb⟩ := DFunLike.ne_iff.1 hf
  exact sum_eq_zero_of_isLeftRegular_sub_one (ψ := ψ.compAddMonoidHom f) (b := b)
    (hψ.isUnit_sub_one hb).isRegular.left

/-- **Orthogonality on `ZMod p`.** The sum of `x ↦ ψ (x * b)` for a nondegenerate `ψ` is `p`
if `b = 0` and `0` otherwise. Over a domain and for primitive `ψ` this is
`AddChar.sum_mulShift`. -/
theorem IsNondegenerate.sum_mulShift (hψ : ψ.IsNondegenerate) (b : ZMod p) :
    ∑ x : ZMod p, ψ (x * b) = if b = 0 then (p : Λ) else 0 := by
  classical
  have := hψ.sum_comp_eq_ite (AddMonoidHom.mulRight b)
  simp only [AddMonoidHom.coe_mulRight, ZMod.card] at this
  rw [this]
  congr 1
  exact propext ⟨fun h ↦ by simpa using DFunLike.congr_fun h 1, fun h ↦ by ext; simp [h]⟩

/-- **Orthogonality over a finite field.** For a finite field `k` of characteristic `p` and a
nondegenerate character `ψ`, `∑ x : k, ψ (Tr (x * y))` is the cardinality of `k` if `y = 0`
and `0` otherwise. -/
theorem IsNondegenerate.sum_trace_mul_eq_ite (hψ : ψ.IsNondegenerate) {k : Type*} [Field k]
    [Fintype k] [Algebra (ZMod p) k] [DecidableEq k] (y : k) :
    ∑ x : k, ψ (Algebra.trace (ZMod p) k (x * y)) =
      if y = 0 then (Fintype.card k : Λ) else 0 := by
  classical
  have := hψ.sum_comp_eq_ite
    ((Algebra.trace (ZMod p) k).toAddMonoidHom.comp (AddMonoidHom.mulRight y))
  simp only [AddMonoidHom.comp_apply, AddMonoidHom.coe_mulRight, LinearMap.toAddMonoidHom_coe]
    at this
  rw [this]
  congr 1
  refine propext ⟨fun h ↦ ?_, fun h ↦ by ext x; simp [h]⟩
  by_contra hy
  obtain ⟨z, hz⟩ := DFunLike.ne_iff.1 (Algebra.trace_ne_zero (ZMod p) k)
  refine hz ?_
  simpa [inv_mul_cancel_right₀ hy] using DFunLike.congr_fun h (z * y⁻¹)

/-- A nondegenerate character remains nondegenerate after composing with a ring homomorphism,
for instance a reduction modulo an ideal. -/
theorem IsNondegenerate.map {Λ' : Type*} [CommRing Λ'] (hψ : ψ.IsNondegenerate) (f : Λ →+* Λ') :
    (f.toMonoidHom.compAddChar ψ).IsNondegenerate := by
  simpa [isNondegenerate_iff, MonoidHom.compAddChar_apply] using IsUnit.map f hψ

/-- The inverse of a nondegenerate character is nondegenerate. -/
theorem IsNondegenerate.inv (hψ : ψ.IsNondegenerate) : ψ⁻¹.IsNondegenerate := by
  rw [isNondegenerate_iff, inv_apply]
  exact hψ.isUnit_sub_one (neg_ne_zero.2 one_ne_zero)

/-- The shift `x ↦ ψ (c * x)` of a nondegenerate character by `c ≠ 0` is nondegenerate. -/
theorem IsNondegenerate.mulShift (hψ : ψ.IsNondegenerate) {c : ZMod p} (hc : c ≠ 0) :
    (ψ.mulShift c).IsNondegenerate := by
  rw [isNondegenerate_iff, mulShift_apply, mul_one]
  exact hψ.isUnit_sub_one hc

/-- A character of `ZMod p` is nondegenerate if and only if its reduction modulo every maximal
ideal is nontrivial. -/
theorem isNondegenerate_iff_forall_isMaximal :
    ψ.IsNondegenerate ↔
      ∀ m : Ideal Λ, m.IsMaximal → (Ideal.Quotient.mk m).toMonoidHom.compAddChar ψ ≠ 1 := by
  simp_rw [zmod_char_ne_one_iff, MonoidHom.compAddChar_apply, Function.comp_apply,
    RingHom.toMonoidHom_eq_coe, MonoidHom.coe_ofClass, ne_eq, ← map_one (Ideal.Quotient.mk _),
    Ideal.Quotient.eq]
  refine ⟨fun hψ m hm hmem ↦ hm.ne_top (m.eq_top_of_isUnit_mem hmem hψ), fun h ↦ ?_⟩
  by_contra hψ
  obtain ⟨m, hm, hmem⟩ := exists_max_ideal_of_mem_nonunits hψ
  exact h m hm hmem

/-- Over a local ring, a character of `ZMod p` is nondegenerate if and only if `p` is a unit and
the character is nontrivial. Thus for a local ring of residue characteristic different from `p`
nondegenerate means nontrivial, and for residue characteristic `p` no character is
nondegenerate. -/
theorem isNondegenerate_iff_of_isLocalRing [IsLocalRing Λ] :
    ψ.IsNondegenerate ↔ IsUnit (p : Λ) ∧ ψ ≠ 1 := by
  refine ⟨fun hψ ↦ ⟨hψ.isUnit_natCast, hψ.ne_one⟩, fun ⟨hp, hψ⟩ ↦ ?_⟩
  rw [zmod_char_ne_one_iff, ne_eq, ← sub_eq_zero] at hψ
  by_contra hunit
  have hmem : ψ 1 - 1 ∈ IsLocalRing.maximalIdeal Λ := hunit
  -- `∑ i < p, ψ 1 ^ i` is congruent to `p` modulo the maximal ideal, hence a unit.
  have hsum : IsUnit (∑ i ∈ range p, ψ 1 ^ i) := by
    by_contra hns
    have hdiff : ∑ i ∈ range p, ψ 1 ^ i - p ∈ IsLocalRing.maximalIdeal Λ := by
      have h : ∑ i ∈ range p, ψ 1 ^ i - p = ∑ i ∈ range p, (ψ 1 ^ i - 1) := by
        simp [sum_sub_distrib]
      rw [h]
      exact Ideal.sum_mem _ fun i _ ↦
        Ideal.mem_of_dvd _ (by simpa using sub_dvd_pow_sub_pow (ψ 1) 1 i) hmem
    exact (IsLocalRing.mem_maximalIdeal _).1
      (by simpa using sub_mem ((IsLocalRing.mem_maximalIdeal _).2 hns) hdiff) hp
  refine hψ (hsum.mul_right_eq_zero.1 ?_)
  rw [mul_comm, mul_geom_sum, ψ.pow_char_eq_one p, sub_self]

section Connected

/-- **Roots of unity over a connected base.** If `Spec Λ` is preconnected, every `p`-th root of
unity of `Λ` is a value of a nondegenerate character `ψ`. Over `ZMod 7 × ZMod 7` with
`ψ 1 = (2, 2)` the root of unity `(2, 4)` is not a value of `ψ`, so connectedness cannot be
dropped. -/
theorem IsNondegenerate.exists_apply_eq [PreconnectedSpace (PrimeSpectrum Λ)]
    (hψ : ψ.IsNondegenerate) {η : Λ} (hη : η ^ p = 1) : ∃ a, ψ a = η := by
  by_contra hne
  push Not at hne
  -- the elements `e j = p⁻¹ ∑ i, η ^ i ψ (- j * i)` are idempotents summing to `1`, and
  -- `e j = 1` would force `η = ψ j`; so every `e j` vanishes and `Λ` is the zero ring
  set φ := zmodChar p hη
  set u : Λ := ↑hψ.isUnit_natCast.unit⁻¹
  have hup : u * p = 1 := hψ.isUnit_natCast.val_inv_mul
  -- the character `χ j = φ * (ψ.mulShift j)⁻¹` and its normalized sum `e j`
  set χ : ZMod p → AddChar (ZMod p) Λ := fun j ↦ φ * (ψ.mulShift j)⁻¹
  set e : ZMod p → Λ := fun j ↦ u * ∑ i, χ j i
  have hfix (j i : ZMod p) : χ j i * e j = e j := by
    simp only [e, mul_left_comm (χ j i), (χ j).apply_mul_sum]
  have hidem (j : ZMod p) : IsIdempotentElem (e j) := by
    have h : u * ∑ i, χ j i * e j = e j * e j := by
      rw [← sum_mul, ← mul_assoc]
    rw [IsIdempotentElem, ← h]
    simp only [hfix, sum_const, card_univ, ZMod.card, nsmul_eq_mul, ← mul_assoc, hup, one_mul]
  have hsum : ∑ j, e j = 1 := by
    simp only [e, χ, ← mul_sum, mul_apply, inv_apply, mulShift_apply]
    rw [sum_comm]
    simp only [← mul_sum, hψ.sum_mulShift, neg_eq_zero, mul_ite, mul_zero, sum_ite_eq',
      mem_univ, ite_true, map_zero_eq_one, one_mul, hup]
  have hzero (j : ZMod p) : e j = 0 := by
    refine (hidem j).eq_zero_or_eq_one_of_preconnectedSpace.resolve_right fun h1 ↦ hne j ?_
    have h := hfix j 1
    rw [h1, mul_one] at h
    simp only [χ, φ, mul_apply, inv_apply, mulShift_apply, zmodChar_apply, ZMod.val_one,
      pow_one, mul_neg, mul_one] at h
    rw [← mul_one (ψ j), ← h, ← mul_assoc, mul_comm (ψ j), mul_assoc, ← map_add_eq_mul,
      add_neg_cancel, map_zero_eq_one, mul_one]
  have : Subsingleton Λ := subsingleton_of_zero_eq_one <| by
    simpa only [hzero, sum_const_zero] using hsum
  exact hne 0 (Subsingleton.elim _ _)

/-- **Additive characters of a finite field over a connected base.** If `Spec Λ` is connected
and `ψ` is nondegenerate, every additive character of a finite field `k` of characteristic `p`
with values in `Λ` is `x ↦ ψ (Tr (c * x))` for a unique `c ∈ k`. -/
theorem IsNondegenerate.existsUnique_trace_mul [ConnectedSpace (PrimeSpectrum Λ)]
    (hψ : ψ.IsNondegenerate) {k : Type*} [Field k] [Finite k] [Algebra (ZMod p) k]
    (φ : AddChar k Λ) : ∃! c : k, ∀ x, φ x = ψ (Algebra.trace (ZMod p) k (c * x)) := by
  have : Nontrivial Λ := PrimeSpectrum.nonempty_iff_nontrivial.1 inferInstance
  have : CharP k p := (Algebra.charP_iff (ZMod p) k p).mp (ZMod.charP p)
  -- `φ` takes values in the `p`-th roots of unity, hence factors through `ψ`
  choose L hL using fun x ↦ hψ.exists_apply_eq (φ.pow_char_eq_one p x)
  let L' : k →+ ZMod p :=
    { toFun := L
      map_zero' := hψ.injective <| by rw [hL, map_zero_eq_one, map_zero_eq_one]
      map_add' x y := hψ.injective <| by rw [hL, map_add_eq_mul, map_add_eq_mul, hL, hL] }
  have hB := traceForm_nondegenerate (ZMod p) k
  refine ⟨((Algebra.traceForm (ZMod p) k).toDual hB).symm (L'.toZModLinearMap p), fun x ↦ ?_,
    fun c hc ↦ ?_⟩
  · rw [← Algebra.traceForm_apply, LinearMap.BilinForm.apply_toDual_symm_apply,
      AddMonoidHom.coe_toZModLinearMap]
    exact (hL x).symm
  · refine ((Algebra.traceForm (ZMod p) k).toDual hB).injective (LinearMap.ext fun x ↦ ?_)
    rw [LinearEquiv.apply_symm_apply, LinearMap.BilinForm.toDual_def, Algebra.traceForm_apply,
      AddMonoidHom.coe_toZModLinearMap]
    exact hψ.injective ((hc x).symm.trans (hL x).symm)

end Connected

/-! ### Examples -/

/-- `2` has order `3` in `ZMod 7` and `2 - 1` is a unit, so the character of `ZMod 3` sending `1`
to `2` is nondegenerate. -/
example : (zmodChar 3 (by decide : (2 : ZMod 7) ^ 3 = 1)).IsNondegenerate := by
  rw [isNondegenerate_zmodChar_iff]
  decide

/-- A nontrivial character into a non-reduced local ring of residue characteristic different
from `p` is nondegenerate: `18 ^ 3 = 1` and `18 - 1 = 17` is a unit in `ZMod 49`. -/
example : (zmodChar 3 (by decide : (18 : ZMod 49) ^ 3 = 1)).IsNondegenerate := by
  rw [isNondegenerate_zmodChar_iff]
  decide

/-- Nontriviality is not enough in residue characteristic `p`: the character of `ZMod 3` sending
`1` to `4` in `ZMod 9` is nontrivial, but `4 - 1 = 3` is not a unit. -/
example : ¬(zmodChar 3 (by decide : (4 : ZMod 9) ^ 3 = 1)).IsNondegenerate := by
  rw [isNondegenerate_zmodChar_iff]
  decide

/-- Over the disconnected `ZMod 7 × ZMod 7`, the `3`-rd root of unity `(2, 4)` is not a value of
the nondegenerate character sending `1` to `(2, 2)`. -/
example : (zmodChar 3 (by decide : ((2, 2) : ZMod 7 × ZMod 7) ^ 3 = 1)).IsNondegenerate ∧
    ∀ a, zmodChar 3 (by decide : ((2, 2) : ZMod 7 × ZMod 7) ^ 3 = 1) a ≠ (2, 4) := by
  refine ⟨by rw [isNondegenerate_zmodChar_iff]; decide, fun a ↦ ?_⟩
  rw [zmodChar_apply]
  fin_cases a <;> decide

/-- Nontriviality is not enough over a ring that is not local: the character of `ZMod 3` sending
`1` to `(2, 1)` in `ZMod 7 × ZMod 7` is nontrivial, but `(2, 1) - 1 = (1, 0)` is not a unit. -/
example : ¬(zmodChar 3 (by decide : ((2, 1) : ZMod 7 × ZMod 7) ^ 3 = 1)).IsNondegenerate := by
  rw [isNondegenerate_zmodChar_iff]
  decide

end AddChar
