/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.Cyclotomic.Basic
public import Mathlib.NumberTheory.NumberField.Cyclotomic.Basic
import TauCeti.NumberTheory.Cyclotomic.Aut

/-!
# Exact cyclotomic integers and the ring of integers

For a primitive `e`-th root of unity `ζ` in a cyclotomic extension `K` of `ℚ`, the exact,
computable ring `TauCeti.Cyclotomic e` is isomorphic to the ring of integers `𝓞 K` on the same
generator: `IsPrimitiveRoot.cyclotomicEquivRingOfIntegers` sends `TauCeti.Cyclotomic.zeta e` to
`ζ`. The native coordinates `TauCeti.Cyclotomic.coeff` are the coordinates in Mathlib's integral
power basis `IsPrimitiveRoot.integralPowerBasis`, so a computation with exact cyclotomic integers
is a computation in `𝓞 K`, and a statement about them can be read in Mathlib's algebraic number
theory.

Mathlib's integral power basis rests on the computation of the ring of integers of a cyclotomic
field, `IsCyclotomicExtension.Rat.isIntegralClosure_adjoin_singleton`.

The comparison respects the distinguished complex embedding: an embedding of `K` into `ℂ` sending
`ζ` to `TauCeti.Cyclotomic.complexRoot e` restricts along the isomorphism to
`TauCeti.Cyclotomic.complexEmbedding`, and such an embedding exists for every primitive root `ζ`.

## Main results

* `IsPrimitiveRoot.cyclotomicEquivRingOfIntegers`: the isomorphism `Cyclotomic e ≃+* 𝓞 K`.
* `IsPrimitiveRoot.repr_cyclotomicEquivRingOfIntegers`: its coordinates are the native ones.
* `TauCeti.Cyclotomic.exists_ringOfIntegers_equiv_integralPowerBasis`: the assembled comparison for
  `CyclotomicField e ℚ` and its distinguished primitive root.
-/

public section

open NumberField Polynomial TauCeti

namespace IsPrimitiveRoot

variable {e : ℕ} [NeZero e] {K : Type*} [Field K] {ζ : K}

/-- Evaluation of exact cyclotomic integers at the primitive root in the ring of integers. -/
private noncomputable def evalToInteger (hζ : IsPrimitiveRoot ζ e) : Cyclotomic e →+* 𝓞 K :=
  Cyclotomic.evalRingHom (Int.castRingHom (𝓞 K)) hζ.toInteger
    (hζ.toInteger_isPrimitiveRoot.eval₂_cyclotomic _)

/-- The evaluation expands an exact element in the powers of the primitive root, with the native
coordinates as coefficients. -/
private theorem evalToInteger_eq_sum (hζ : IsPrimitiveRoot ζ e) (x : Cyclotomic e) :
    hζ.evalToInteger x = ∑ j : Fin e.totient, x.coeff j • hζ.toInteger ^ (j : ℕ) := by
  simp [evalToInteger, Cyclotomic.evalRingHom_eq_evalCoeffs, Cyclotomic.evalCoeffs_eq_sum]

variable [CharZero K] [IsCyclotomicExtension {e} ℚ K]

/-- The evaluation reads the native coordinates as coordinates in the integral power basis,
indexed as in the exact ring. -/
private theorem repr_evalToInteger (hζ : IsPrimitiveRoot ζ e) (x : Cyclotomic e)
    (j : Fin e.totient) :
    (hζ.integralPowerBasis.basis.reindex (finCongr hζ.integralPowerBasis_dim)).repr
      (hζ.evalToInteger x) j = x.coeff j := by
  let b := hζ.integralPowerBasis.basis.reindex (finCongr hζ.integralPowerBasis_dim)
  have h : hζ.evalToInteger x = ∑ k : Fin e.totient, x.coeff k • b k := by
    simp [evalToInteger_eq_sum, b]
  rw [h, b.repr_sum_self]

private theorem evalToInteger_bijective (hζ : IsPrimitiveRoot ζ e) :
    Function.Bijective hζ.evalToInteger := by
  refine ⟨fun x y h ↦ Cyclotomic.ext fun j ↦ ?_, fun y ↦ ?_⟩
  · rw [← hζ.repr_evalToInteger x j, h, hζ.repr_evalToInteger y j]
  · let b := hζ.integralPowerBasis.basis.reindex (finCongr hζ.integralPowerBasis_dim)
    refine ⟨∑ j, b.repr y j • Cyclotomic.zeta e ^ (j : ℕ), ?_⟩
    conv_rhs => rw [← b.sum_repr y]
    simp [evalToInteger, b]

/-- The exact cyclotomic ring is isomorphic to the ring of integers of a cyclotomic extension of
`ℚ`, on the same generator: `TauCeti.Cyclotomic.zeta e` goes to the primitive root `ζ`. -/
noncomputable def cyclotomicEquivRingOfIntegers (hζ : IsPrimitiveRoot ζ e) : Cyclotomic e ≃+* 𝓞 K :=
  RingEquiv.ofBijective hζ.evalToInteger hζ.evalToInteger_bijective

/-- The isomorphism sends the exact generator to the primitive root. -/
@[simp]
theorem cyclotomicEquivRingOfIntegers_zeta (hζ : IsPrimitiveRoot ζ e) :
    hζ.cyclotomicEquivRingOfIntegers (Cyclotomic.zeta e) = hζ.toInteger :=
  Cyclotomic.evalRingHom_zeta _ _ _

/-- The inverse isomorphism sends the primitive root to the exact generator. -/
@[simp]
theorem cyclotomicEquivRingOfIntegers_symm_toInteger (hζ : IsPrimitiveRoot ζ e) :
    hζ.cyclotomicEquivRingOfIntegers.symm hζ.toInteger = Cyclotomic.zeta e := by
  rw [RingEquiv.symm_apply_eq, cyclotomicEquivRingOfIntegers_zeta]

/-- The coordinates in the integral power basis are the native ascending coordinates of the exact
cyclotomic ring. -/
@[simp]
theorem repr_cyclotomicEquivRingOfIntegers (hζ : IsPrimitiveRoot ζ e) (x : Cyclotomic e)
    (j : Fin hζ.integralPowerBasis.dim) :
    hζ.integralPowerBasis.basis.repr (hζ.cyclotomicEquivRingOfIntegers x) j = x.coeff j := by
  simpa [cyclotomicEquivRingOfIntegers] using hζ.repr_evalToInteger x (finCongr (by simp) j)

/-- The native coordinates of the exact representative of an element of the ring of integers are
its coordinates in the integral power basis. -/
@[simp]
theorem coeff_cyclotomicEquivRingOfIntegers_symm (hζ : IsPrimitiveRoot ζ e) (y : 𝓞 K)
    (j : Fin hζ.integralPowerBasis.dim) :
    (hζ.cyclotomicEquivRingOfIntegers.symm y).coeff j = hζ.integralPowerBasis.basis.repr y j := by
  rw [← repr_cyclotomicEquivRingOfIntegers, RingEquiv.apply_symm_apply]

/-- An embedding of a cyclotomic extension into `ℂ` sending the primitive root `ζ` to the pinned
root `TauCeti.Cyclotomic.complexRoot e` restricts to the pinned embedding of the exact ring. -/
theorem map_cyclotomicEquivRingOfIntegers_eq_complexEmbedding (hζ : IsPrimitiveRoot ζ e)
    {ι : K →+* ℂ} (hι : ι ζ = Cyclotomic.complexRoot e) (x : Cyclotomic e) :
    ι (algebraMap (𝓞 K) K (hζ.cyclotomicEquivRingOfIntegers x)) = Cyclotomic.complexEmbedding x :=
  have hmk : algebraMap (𝓞 K) K hζ.toInteger = ζ := RingOfIntegers.map_mk _ _
  DFunLike.congr_fun (Cyclotomic.ringHom_ext
    (g₁ := (ι.comp (algebraMap (𝓞 K) K)).comp hζ.cyclotomicEquivRingOfIntegers.toRingHom)
    (g₂ := Cyclotomic.complexEmbedding)
    (by simpa [hmk] using hι)) x

end IsPrimitiveRoot

namespace TauCeti.Cyclotomic

/-- **The ring-of-integers comparison on the same generator.** For `K = CyclotomicField e ℚ` with
its distinguished primitive root `ζ`, there are a ring isomorphism `E` from the exact ring
`TauCeti.Cyclotomic e` onto `𝓞 K` and a field embedding `ι : K →+* ℂ` with
`ι ζ = complexRoot e`, such that `E (zeta e) = ζ`, such that `ι ∘ algebraMap ∘ E` is
`complexEmbedding`, and such that the coordinates of `E x` in the integral power basis of `ζ` are
the native coordinates `x.coeff k`. -/
theorem exists_ringOfIntegers_equiv_integralPowerBasis (e : ℕ) [NeZero e] :
    haveI : IsCyclotomicExtension {e} ℚ (CyclotomicField e ℚ) :=
      CyclotomicField.isCyclotomicExtension e ℚ
    let hζ := IsCyclotomicExtension.zeta_spec e ℚ (CyclotomicField e ℚ)
    ∃ (E : Cyclotomic e ≃+* 𝓞 (CyclotomicField e ℚ)) (ι : CyclotomicField e ℚ →+* ℂ),
      ι (IsCyclotomicExtension.zeta e ℚ (CyclotomicField e ℚ)) = complexRoot e ∧
      algebraMap (𝓞 (CyclotomicField e ℚ)) (CyclotomicField e ℚ) (E (zeta e)) =
        IsCyclotomicExtension.zeta e ℚ (CyclotomicField e ℚ) ∧
      (∀ x : Cyclotomic e,
        ι (algebraMap (𝓞 (CyclotomicField e ℚ)) (CyclotomicField e ℚ) (E x)) =
          complexEmbedding x) ∧
      ∀ (x : Cyclotomic e) (k : Fin e.totient),
        hζ.integralPowerBasis.basis.repr (E x) ((finCongr hζ.integralPowerBasis_dim).symm k) =
          x.coeff k := by
  have : IsCyclotomicExtension {e} ℚ (CyclotomicField e ℚ) :=
    CyclotomicField.isCyclotomicExtension e ℚ
  intro hζ
  obtain ⟨ι, hι, -⟩ := hζ.existsUnique_algHom_apply_eq
    (cyclotomic.irreducible_rat (NeZero.pos e)) (isPrimitiveRoot_complexRoot (e := e))
  exact ⟨hζ.cyclotomicEquivRingOfIntegers, ι, hι,
    by rw [hζ.cyclotomicEquivRingOfIntegers_zeta]; exact RingOfIntegers.map_mk _ _,
    hζ.map_cyclotomicEquivRingOfIntegers_eq_complexEmbedding hι,
    fun x k ↦ by rw [hζ.repr_cyclotomicEquivRingOfIntegers]; simp⟩

/-! The comparison computes coordinates in the ring of integers: `ζ₃² = -1 - ζ₃`, so both
coordinates of `ζ₃²` in the integral power basis of `ℚ(ζ₃)` are `-1`. -/

example {K : Type*} [Field K] [CharZero K] [IsCyclotomicExtension {3} ℚ K] {ζ : K}
    (hζ : IsPrimitiveRoot ζ 3) (j : Fin hζ.integralPowerBasis.dim) :
    hζ.integralPowerBasis.basis.repr (hζ.toInteger ^ 2) j = -1 := by
  have hj : (j : ℕ) < 2 := by simpa [Nat.totient_prime Nat.prime_three] using j.2
  rw [← hζ.cyclotomicEquivRingOfIntegers_zeta, ← map_pow, hζ.repr_cyclotomicEquivRingOfIntegers]
  interval_cases (j : ℕ) <;> decide

end TauCeti.Cyclotomic
