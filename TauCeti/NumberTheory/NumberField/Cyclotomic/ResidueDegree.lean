/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.Cyclotomic.Gal
public import TauCeti.NumberTheory.NumberField.Cyclotomic.Frobenius
public import TauCeti.NumberTheory.NumberField.Frobenius.DecompositionGroup

/-!
# The residue degree in a cyclotomic extension

The classical cyclotomic splitting law: at a prime `𝔭` not dividing `m`, the residue degree of a
prime of `F` above `𝔭` is the multiplicative order of `𝔑𝔭` modulo `m`. Over `ℚ` this is the
familiar statement that `f(p)` is the order of `p` in `(ZMod m)ˣ` — so `p` splits completely
exactly when `p ≡ 1 (mod m)`, and is inert exactly when `p` generates `(ZMod m)ˣ`.

The law is stated twice: once with the residue degree as the order of the cyclotomic character
at a Frobenius element, and once with it as the order of a unit of `ZMod m` reducing to `𝔑𝔭`.
The second form is the computational one — it turns a question about prime splitting into a
multiplicative order in `(ZMod m)ˣ` — and takes that unit from the caller, together with the
proof that it reduces to `𝔑𝔭`, so that a caller may pass whichever presentation it holds. Over
`ℚ` that is typically `ZMod.unitOfCoprime p`.

## Main results

* `IsPrimitiveRoot.inertiaDeg_eq_orderOf_autToPow`: the residue degree is the order of the
  cyclotomic character at a Frobenius element at `Q`.
* `IsPrimitiveRoot.inertiaDeg_eq_orderOf_of_val_eq_absNorm`: equivalently, the order of `𝔑𝔭`
  in `(ZMod m)ˣ`.

## References

* J. Neukirch, *Algebraic Number Theory*, Chapter I, §10.
-/

public section

open IsDedekindDomain NumberField

open scoped NumberField

namespace IsPrimitiveRoot

variable {K F : Type*} [Field K] [NumberField K] [Field F] [NumberField F]
  [Algebra K F] [IsGalois K F]

/-- **The residue degree of `Q` is the order of the cyclotomic character at a Frobenius element
at `Q`**, for `Q` unramified over `𝓞 K`. -/
theorem inertiaDeg_eq_orderOf_autToPow {m : ℕ} [NeZero m] {ζ : F} (hζ : IsPrimitiveRoot ζ m)
    [IsCyclotomicExtension {m} K F]
    (Q : Ideal (𝓞 F)) [Q.IsPrime] (hQ : Q ≠ ⊥) [Algebra.IsUnramifiedAt (𝓞 K) Q]
    {σ : F ≃ₐ[K] F} (hσ : IsArithFrobAt (𝓞 K) σ Q) :
    Q.inertiaDeg (𝓞 K) = orderOf (hζ.autToPow K σ) := by
  -- The character is injective, hence order-preserving.
  rw [orderOf_injective _ (hζ.autToPow_injective K),
    Ideal.orderOf_eq_inertiaDeg_of_isArithFrobAt Q hQ hσ]

/-- **The cyclotomic splitting law.** At a prime `𝔭` not dividing `m`, the residue degree of `Q`
above `𝔭` is the multiplicative order in `(ZMod m)ˣ` of any unit `u` reducing to `𝔑𝔭`. -/
theorem inertiaDeg_eq_orderOf_of_val_eq_absNorm {m : ℕ} [NeZero m] {ζ : F}
    (hζ : IsPrimitiveRoot ζ m) [IsCyclotomicExtension {m} K F]
    (𝔭 : HeightOneSpectrum (𝓞 K)) (hm : (m : 𝓞 K) ∉ 𝔭.asIdeal)
    (Q : Ideal (𝓞 F)) [Q.IsPrime] [Q.LiesOver 𝔭.asIdeal] (hQ : Q ≠ ⊥)
    [Algebra.IsUnramifiedAt (𝓞 K) Q]
    {σ : F ≃ₐ[K] F} (hσ : IsArithFrobAt (𝓞 K) σ Q)
    (u : (ZMod m)ˣ) (hu : (u : ZMod m) = Ideal.absNorm 𝔭.asIdeal) :
    Q.inertiaDeg (𝓞 K) = orderOf u := by
  -- A unit of `ZMod m` is determined by its value, so `u` is the character at `σ`.
  have hueq : u = hζ.autToPow K σ :=
    Units.ext (by rw [hu, hσ.autToPow_eq_absNorm hζ 𝔭 hm Q])
  rw [hueq, hζ.inertiaDeg_eq_orderOf_autToPow Q hQ hσ]

end IsPrimitiveRoot

end
