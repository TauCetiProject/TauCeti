/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Complex.Basic
public import Mathlib.FieldTheory.SplittingField.IsSplittingField
public import TauCeti.NumberTheory.NumberField.CMField.Basic

/-!
# Radical extensions of CM fields and discriminant descent

Let `K` be a CM field and `u ∈ K` with `u * conj u = 1`, so that `u` has absolute value one under
every complex embedding. Every root `β` of `Xⁿ - u` then also has absolute value one, so complex
conjugation sends `β` to `β⁻¹`, again a root. Consequently the splitting field `L` of `Xⁿ - u` over
`K` is stable under complex conjugation in every complex embedding, and the conjugation is the same
automorphism of `L` for all of them: it is `complexConj K` on `K` and inversion on the roots. Hence
`L` is CM (`IsCMField.of_isSplittingField_X_pow_sub_C`).

The typical radicand is `u = a / conj a` for a unit `a` of `K`. In any CM field `L`, a unit `x`
is a totally real unit times an `n`-th power exactly when `x / conj x` is an `n`-th power
(`IsCMField.exists_mem_maximalRealSubfield_div_eq_pow_iff`): an `n`-th root `β` of `x / conj x`
satisfies `β * conj β = 1`, so `β = b / conj b` by Hilbert's Theorem 90, and then `x / bⁿ` is
fixed by complex conjugation. Applied to the splitting field of `Xⁿ - a / conj a`, this is the
descent of a Weierstrass discriminant (with `n = 6`) to a totally real one after a solvable CM
extension
(`IsCMField.exists_mem_maximalRealSubfield_algebraMap_div_eq_pow`). That the extension is
solvable is `TauCeti.isSolvable_of_isSplittingField_X_pow_sub_C`; it is Galois since it is a
splitting field in characteristic zero.

## Main results

* `NumberField.IsCMField.mul_complexConj_eq_one_of_pow_eq`: `n`-th roots of elements with
  `x * conj x = 1` satisfy the same identity.
* `NumberField.IsCMField.exists_mem_maximalRealSubfield_div_eq_pow_iff`: a unit `x` of a CM field
  is a totally real unit times an `n`-th power if and only if `x / conj x` is an `n`-th power.
* `NumberField.IsCMField.of_isSplittingField_X_pow_sub_C`: the splitting field of `Xⁿ - u` over a
  CM field, with `u * conj u = 1`, is CM.
* `NumberField.IsCMField.exists_mem_maximalRealSubfield_algebraMap_div_eq_pow`: over the
  splitting field of `Xⁿ - a / conj a`, `a` is a totally real unit times an `n`-th power.

## References

* P. B. Allen, C. Khare and J. A. Thorne, *Modularity of `GL₂(𝔽_p)`-representations over CM
  fields*, arXiv:1910.12986v2, Corollary 9.4.
-/

public section

open Polynomial NumberField ComplexEmbedding

namespace NumberField.IsCMField

/-- If `w = zⁿ` with `n ≠ 0` and `w * conj w = 1`, then `conj z = z⁻¹`. -/
private theorem star_eq_inv_of_pow_eq {z w : ℂ} {n : ℕ} (hn : n ≠ 0) (hz : z ^ n = w)
    (hw : w * star w = 1) : star z = z⁻¹ := by
  have hw' : ‖w‖ = 1 := by
    have h := congrArg norm hw
    rw [norm_mul, norm_star, norm_one] at h
    nlinarith [norm_nonneg w]
  have hz' : ‖z‖ = 1 :=
    (pow_eq_one_iff_of_nonneg (norm_nonneg z) hn).mp (by rw [← norm_pow, hz, hw'])
  exact (Complex.inv_eq_conj hz').symm

section CMField

variable {L : Type*} [Field L] [CharZero L] [IsCMField L] [Algebra.IsIntegral ℚ L]

local notation3 "L⁺" => maximalRealSubfield L

/-- An `n`-th root `β`, `n ≠ 0`, of an element `x` with `x * conj x = 1` again satisfies
`β * conj β = 1`. -/
theorem mul_complexConj_eq_one_of_pow_eq {β x : L} {n : ℕ} (hn : n ≠ 0) (hβ : β ^ n = x)
    (hx : x * complexConj L x = 1) : β * complexConj L β = 1 := by
  let φ : L →+* ℂ := Classical.choice (inferInstance : Nonempty _)
  have h := star_eq_inv_of_pow_eq hn (z := φ β) (w := φ x) (by rw [← map_pow, hβ])
    (by rw [← starRingEnd_apply, ← complexEmbedding_complexConj, ← map_mul, hx, map_one])
  have hβ0 : β ≠ 0 := by
    rintro rfl
    simp [← hβ, zero_pow hn] at hx
  apply φ.injective
  rw [map_mul, complexEmbedding_complexConj, starRingEnd_apply, h, map_one,
    mul_inv_cancel₀ ((map_ne_zero φ).2 hβ0)]

/-- **Real-times-power decomposition in a CM field.** A unit `x` of a CM field is a totally real
unit times an `n`-th power if and only if `x / conj x` is an `n`-th power. -/
theorem exists_mem_maximalRealSubfield_div_eq_pow_iff {x : Lˣ} {n : ℕ} :
    (∃ z : Lˣ, (z : L) ∈ L⁺ ∧ ∃ b : Lˣ, (x : L) / z = b ^ n) ↔
      ∃ β : L, β ^ n = x / complexConj L x := by
  have hcx : complexConj L (x : L) ≠ 0 := by simp
  constructor
  · rintro ⟨z, hz, b, hb⟩
    have hcz : complexConj L (z : L) = z := (complexConj_eq_self_iff L _).2 hz
    have hcb : complexConj L (b : L) ≠ 0 := by simp
    have hx : (x : L) = z * b ^ n := by rw [← hb]; field_simp
    refine ⟨b / complexConj L b, ?_⟩
    rw [hx, map_mul, map_pow, hcz, div_pow]
    field_simp
  rintro ⟨β, hβ⟩
  rcases eq_or_ne n 0 with rfl | hn
  · refine ⟨x, (complexConj_eq_self_iff L _).1 ?_, 1, by simp⟩
    rw [pow_zero, eq_comm, div_eq_one_iff_eq hcx] at hβ
    exact hβ.symm
  have hβ1 : β * complexConj L β = 1 := mul_complexConj_eq_one_of_pow_eq hn hβ (by
    rw [map_div₀, complexConj_apply_apply]
    field_simp)
  obtain ⟨y, hy⟩ := (exists_complexConj_div_eq_iff L (x := Units.mk0 β
    (left_ne_zero_of_mul_eq_one hβ1))).2 hβ1
  rw [Units.val_mk0, div_eq_iff y.ne_zero] at hy
  refine ⟨x * y ^ n, (complexConj_eq_self_iff L _).1 ?_, y⁻¹, ?_⟩
  · rw [Units.val_mul, Units.val_pow_eq_pow_val, map_mul, map_pow, hy, mul_pow, hβ]
    field_simp
  · simp only [Units.val_mul, Units.val_pow_eq_pow_val, Units.val_inv_eq_inv_val, inv_pow]
    field_simp

end CMField

section SplittingField

/-- A subfield of a splitting field containing the base field and the roots is everything. -/
private theorem forall_mem_of_isSplittingField {K L : Type*} [Field K] [Field L] [Algebra K L]
    (f : K[X]) [IsSplittingField K L f]
    (S : Subfield L) (hK : ∀ k, algebraMap K L k ∈ S) (hroots : ∀ β ∈ f.rootSet L, β ∈ S)
    (x : L) : x ∈ S := by
  let T : Subalgebra K L := { S.toSubsemiring with algebraMap_mem' := hK }
  have hT : Algebra.adjoin K (f.rootSet L) ≤ T := Algebra.adjoin_le hroots
  rw [IsSplittingField.adjoin_rootSet] at hT
  exact hT (Algebra.mem_top (x := x))

/-- A root of `Xⁿ - u` is an `n`-th root of `u`, and its existence forces `n ≠ 0`. -/
private theorem ne_zero_and_pow_eq_of_mem_rootSet {K L : Type*} [Field K] [Field L] [Algebra K L]
    {n : ℕ} {u : K} {β : L} (hβ : β ∈ (X ^ n - C u).rootSet L) :
    n ≠ 0 ∧ β ^ n = algebraMap K L u := by
  rw [mem_rootSet, map_sub, aeval_X_pow, aeval_C, sub_eq_zero] at hβ
  obtain ⟨hne, hpow⟩ := hβ
  refine ⟨fun hn ↦ hne ?_, hpow⟩
  subst hn
  rw [pow_zero, eq_comm, ← map_one (algebraMap K L), (algebraMap K L).injective.eq_iff] at hpow
  rw [hpow, pow_zero, C_1, sub_self]

variable {K L : Type*} [Field K] [CharZero K] [Algebra.IsIntegral ℚ K] [IsCMField K] [Field L]
  [Algebra K L] {n : ℕ} {u : K}

/-- The complex conjugate of an element of `K`, under an embedding of `L`. -/
private theorem star_algebraMap (φ : L →+* ℂ) (k : K) :
    star (φ (algebraMap K L k)) = φ (algebraMap K L (complexConj K k)) :=
  (complexEmbedding_complexConj K (φ.comp (algebraMap K L)) k).symm

/-- Under every complex embedding of `L`, a root of `Xⁿ - u` with `u * conj u = 1` is conjugated
to its inverse. -/
private theorem star_eq_inv_of_mem_rootSet (hu : u * complexConj K u = 1) (φ : L →+* ℂ) {β : L}
    (hβ : β ∈ (X ^ n - C u).rootSet L) : star (φ β) = φ β⁻¹ := by
  obtain ⟨hn, hβ⟩ := ne_zero_and_pow_eq_of_mem_rootSet hβ
  rw [map_inv₀]
  refine star_eq_inv_of_pow_eq hn (w := φ (algebraMap K L u)) (by rw [← map_pow, hβ]) ?_
  rw [star_algebraMap, ← map_mul, ← map_mul, hu, map_one, map_one]

/-- **Radical extensions by unit-modulus radicands stay CM.** If `K` is CM and `u * conj u = 1`, the
splitting field of `Xⁿ - u` over `K` is CM; its complex conjugation inverts every root. -/
theorem of_isSplittingField_X_pow_sub_C [CharZero L] (hu : u * complexConj K u = 1)
    [IsSplittingField K L (X ^ n - C u)] : IsCMField L := by
  have : FiniteDimensional K L := IsSplittingField.finiteDimensional L (X ^ n - C u)
  have : Algebra.IsIntegral ℚ L := Algebra.IsIntegral.trans K
  have : IsTotallyComplex L := isTotallyComplex_of_algebra K L
  let φ₀ : L →+* ℂ := Classical.choice (inferInstance : Nonempty _)
  let ψ : L →+* ℂ := (starRingEnd ℂ).comp φ₀
  -- The conjugate embedding `ψ` takes values in the image of `φ₀`.
  have hrange : ψ.fieldRange ≤ φ₀.fieldRange := by
    rintro _ ⟨x, rfl⟩
    refine forall_mem_of_isSplittingField (X ^ n - C u) (φ₀.fieldRange.comap ψ)
      (fun k ↦ ⟨_, (star_algebraMap φ₀ k).symm⟩)
      (fun β hβ ↦ ⟨_, (star_eq_inv_of_mem_rootSet hu φ₀ hβ).symm⟩) x
  -- Hence `ψ = φ₀ ∘ σ` for a field endomorphism `σ` of `L`, which is an automorphism.
  let σ₀ : L →+* L := (φ₀.rangeRestrictFieldEquiv.symm : φ₀.fieldRange →+* L).comp
    ((Subfield.inclusion hrange).comp ψ.rangeRestrictField)
  -- `Subfield.inclusion` does not change the underlying complex number, by definition.
  have hσ₀ (x : L) : φ₀ (σ₀ x) = star (φ₀ x) :=
    (φ₀.rangeRestrictFieldEquiv_apply_symm_apply _).trans (ψ.coe_rangeRestrictField x)
  let σ : Gal(L/ℚ) := AlgEquiv.ofBijective σ₀.toRatAlgHom
    (Algebra.IsAlgebraic.algHom_bijective _)
  have hσK (k : K) : σ (algebraMap K L k) = algebraMap K L (complexConj K k) :=
    φ₀.injective ((hσ₀ _).trans (star_algebraMap φ₀ k))
  have hσβ {β : L} (hβ : β ∈ (X ^ n - C u).rootSet L) : σ β = β⁻¹ :=
    φ₀.injective ((hσ₀ _).trans (star_eq_inv_of_mem_rootSet hu φ₀ hβ))
  -- `σ` is the conjugation of every complex embedding.
  refine of_isTotallyComplex_of_forall_isConj L (σ := σ) fun φ ↦ RingHom.ext fun x ↦ ?_
  refine forall_mem_of_isSplittingField (X ^ n - C u) (RingHom.eqLocusField _ _) (fun k ↦ ?_)
    (fun β hβ ↦ ?_) x
  · exact (star_algebraMap φ k).trans (congrArg φ (hσK k).symm)
  · exact (star_eq_inv_of_mem_rootSet hu φ hβ).trans (congrArg φ (hσβ hβ).symm)

/-- **Discriminant descent for CM fields.** Let `K` be CM, `a ∈ Kˣ` and `n ≠ 0`, and let `L` be
the splitting field of `Xⁿ - a / conj a` over `K`. Then `a = z bⁿ` in `L` for a totally real
unit `z` and a unit `b` of `L`. -/
theorem exists_mem_maximalRealSubfield_algebraMap_div_eq_pow (a : Kˣ) (hn : n ≠ 0)
    [IsSplittingField K L (X ^ n - C ((a : K) / complexConj K a))] :
    ∃ z : Lˣ, (z : L) ∈ maximalRealSubfield L ∧ ∃ b : Lˣ, algebraMap K L a / z = b ^ n := by
  have : CharZero L := charZero_of_injective_algebraMap (algebraMap K L).injective
  have : FiniteDimensional K L :=
    IsSplittingField.finiteDimensional L (X ^ n - C ((a : K) / complexConj K a))
  have : Algebra.IsIntegral ℚ L := Algebra.IsIntegral.trans K
  have : IsCMField L := of_isSplittingField_X_pow_sub_C (n := n)
    (u := (a : K) / complexConj K a) (by
      rw [map_div₀, complexConj_apply_apply]
      field_simp)
  obtain ⟨β, hβ⟩ :=
    (IsSplittingField.splits L (X ^ n - C ((a : K) / complexConj K a))).exists_eval_eq_zero (by
      rw [Polynomial.map_sub, Polynomial.map_pow, map_X, map_C,
        degree_X_pow_sub_C (Nat.pos_of_ne_zero hn)]
      exact_mod_cast hn)
  rw [eval_map_algebraMap, map_sub, aeval_X_pow, aeval_C, sub_eq_zero, map_div₀,
    ← complexConj_algebraMap K L] at hβ
  exact (exists_mem_maximalRealSubfield_div_eq_pow_iff (x := Units.map (algebraMap K L) a)).2
    ⟨β, hβ⟩

end SplittingField

end NumberField.IsCMField
