/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Polynomial.XPow.SubC
public import TauCeti.Analysis.Complex.Basic
public import TauCeti.FieldTheory.SplittingField.Basic
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
(`IsCMField.exists_mem_maximalRealSubfield_div_eq_pow_iff`, in
`TauCeti/NumberTheory/NumberField/CMField/Basic.lean`). Applied to the splitting field of
`Xⁿ - a / conj a`, this is the descent of a Weierstrass discriminant (with `n = 6`) to a totally
real one after a solvable CM extension
(`IsCMField.exists_mem_maximalRealSubfield_algebraMap_div_eq_pow`). That the extension is
solvable is `TauCeti.isSolvable_of_isSplittingField_X_pow_sub_C`; it is Galois since it is a
splitting field in characteristic zero.

## Main results

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

section SplittingField

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
  have hn := ne_zero_of_mem_rootSet_X_pow_sub_C hβ
  rw [mem_rootSet_X_pow_sub_C hn] at hβ
  rw [map_inv₀]
  refine Complex.conj_eq_inv_of_pow_eq hn (w := φ (algebraMap K L u)) (by rw [← map_pow, hβ]) ?_
  rw [starRingEnd_apply, star_algebraMap, ← map_mul, ← map_mul, hu, map_one, map_one]

/-- **Radical extensions by unit-modulus radicands stay CM.** If `K` is CM and `u * conj u = 1`, the
splitting field of `Xⁿ - u` over `K` is CM. -/
theorem of_isSplittingField_X_pow_sub_C [CharZero L] (hu : u * complexConj K u = 1)
    [IsSplittingField K L (X ^ n - C u)] : IsCMField L := by
  have : FiniteDimensional K L := IsSplittingField.finiteDimensional L (X ^ n - C u)
  have : Algebra.IsIntegral ℚ L := Algebra.IsIntegral.trans K
  have : IsTotallyComplex L := isTotallyComplex_of_algebra K L
  let φ₀ : L →+* ℂ := Classical.choice (inferInstance : Nonempty _)
  let ψ : L →+* ℂ := (starRingEnd ℂ).comp φ₀
  -- The conjugate embedding `ψ` takes values in the image of `φ₀`.
  have hrange : ψ.fieldRange ≤ φ₀.fieldRange := by
    intro y hy
    obtain ⟨x, rfl⟩ := RingHom.mem_fieldRange.1 hy
    refine Subfield.mem_comap.1 (eq_top_iff.1 (IsSplittingField.subfield_eq_top (X ^ n - C u)
      (S := φ₀.fieldRange.comap ψ) (fun k ↦ ?_) (fun β hβ ↦ ?_)) (Subfield.mem_top x))
    all_goals simp only [SetLike.mem_coe, Subfield.mem_comap, RingHom.mem_fieldRange, ψ,
      RingHom.comp_apply, starRingEnd_apply]
    exacts [⟨_, (star_algebraMap φ₀ k).symm⟩, ⟨_, (star_eq_inv_of_mem_rootSet hu φ₀ hβ).symm⟩]
  -- Hence `ψ = φ₀ ∘ σ` for a field endomorphism `σ` of `L`, which is an automorphism.
  let σ₀ : L →+* L := (φ₀.rangeRestrictFieldEquiv.symm : φ₀.fieldRange →+* L).comp
    ((Subfield.inclusion hrange).comp ψ.rangeRestrictField)
  have hσ₀ (x : L) : φ₀ (σ₀ x) = star (φ₀ x) := by
    -- `Subfield.inclusion` does not change the underlying complex number, by definition.
    have h : φ₀ (σ₀ x) = ψ x :=
      (φ₀.rangeRestrictFieldEquiv_apply_symm_apply _).trans (ψ.coe_rangeRestrictField x)
    rw [h, RingHom.comp_apply, starRingEnd_apply]
  let σ : Gal(L/ℚ) := AlgEquiv.ofBijective σ₀.toRatAlgHom
    (Algebra.IsAlgebraic.algHom_bijective _)
  have hσK (k : K) : σ (algebraMap K L k) = algebraMap K L (complexConj K k) :=
    φ₀.injective ((hσ₀ _).trans (star_algebraMap φ₀ k))
  have hσβ {β : L} (hβ : β ∈ (X ^ n - C u).rootSet L) : σ β = β⁻¹ :=
    φ₀.injective ((hσ₀ _).trans (star_eq_inv_of_mem_rootSet hu φ₀ hβ))
  -- `σ` is the conjugation of every complex embedding.
  refine TauCeti.NumberField.IsCMField.of_forall_isConj L (σ := σ) fun φ ↦ ?_
  unfold ComplexEmbedding.IsConj
  refine IsSplittingField.ringHom_ext (X ^ n - C u) (fun k ↦ ?_) (fun β hβ ↦ ?_)
  all_goals simp only [conjugate_coe_eq, starRingEnd_apply, RingHom.comp_apply]
  exacts [(star_algebraMap φ k).trans (congrArg φ (hσK k).symm),
    (star_eq_inv_of_mem_rootSet hu φ hβ).trans (congrArg φ (hσβ hβ).symm)]

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
    (u := (a : K) / complexConj K a) (div_complexConj_mul_complexConj_div_complexConj_eq_one a)
  obtain ⟨β, hβ⟩ := Splits.exists_eval_eq_zero
    (IsSplittingField.splits L (X ^ n - C ((a : K) / complexConj K a)))
    (by simpa [degree_X_pow_sub_C (Nat.pos_of_ne_zero hn)] using hn)
  replace hβ : β ∈ (X ^ n - C ((a : K) / complexConj K a)).rootSet L :=
    (monic_X_pow_sub_C _ hn).mem_rootSet.2 (by rwa [eval_map_algebraMap] at hβ)
  rw [mem_rootSet_X_pow_sub_C hn, map_div₀, ← complexConj_algebraMap K L] at hβ
  have key := (exists_mem_maximalRealSubfield_div_eq_pow_iff (x := Units.map (algebraMap K L) a)).2
    ⟨β, by rwa [Units.coe_map, MonoidHom.coe_ofClass]⟩
  simpa only [Units.coe_map, MonoidHom.coe_ofClass] using key

end SplittingField

end NumberField.IsCMField
