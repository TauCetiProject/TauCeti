/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.NumberField.AdeleRing
public import TauCeti.NumberTheory.NumberField.AddChar
public import TauCeti.RingTheory.DedekindDomain.FiniteAdeleRing.AddChar
import TauCeti.NumberTheory.NumberField.InfinitePlace.Trace

/-!
# The standard additive character of the adeles of a number field

Let `K` be a number field with adele ring `𝔸[K] = K∞ × 𝔸ᶠ[K]` and write `e(t) = exp (2πi t)`. The
**standard additive character** of `𝔸[K]` is

`ψ(x) = e(-∑_w mult w · Re (x_w)) · ψ_f(x_f)`,

where `w` runs over the infinite places, `Re (x_w)` is the real part of the image of `x_w ∈ K_w`
in `ℂ` under the extension of `w.embedding`, `mult w` is `1` at a real and `2` at a complex place,
and `ψ_f` is the finite part:

* `ψ_f` (`TauCeti.GlobalNumberFields.finiteAdeleStdAddChar`) is the continuous additive character
  of the finite adeles that is trivial on the integral finite adeles `Ô` and equals `e(Tr_{K/ℚ} a)`
  at `a ∈ K`. It is the extension of the trace character `TauCeti.numberFieldTraceChar` of `K`,
  which is trivial on `𝓞 K`, along `K / 𝓞 K ≃ 𝔸ᶠ[K] / Ô`
  (`IsDedekindDomain.FiniteAdeleRing.extendAddChar`), and it is the only character with these
  properties, since `𝔸ᶠ[K] = K + Ô`.
* The infinite part `ψ_∞ = e(-Tr_∞)` (`TauCeti.GlobalNumberFields.infiniteAdeleStdAddChar`) is
  built from the archimedean trace `Tr_∞ x = ∑_w mult w · Re (x_w)`
  (`TauCeti.GlobalNumberFields.infiniteAdeleTrace`). A complex place contributes
  `2 Re z = z + conj z`, so `Tr_∞` does not depend on which of the two conjugate embeddings
  represents the place.

On the diagonal copy of `K` the archimedean trace is the trace `Tr_{K/ℚ}`
(`TauCeti.NumberField.InfinitePlace.sum_mult_mul_re_embedding_eq_trace`), so the two parts cancel
and `ψ` is trivial on `K` (`TauCeti.GlobalNumberFields.adeleStdAddChar_algebraMap`): it is a
character of the compact group `𝔸[K] / K`. For a totally complex field every place is complex and
`ψ(x) = e(-∑_w 2 Re (x_w)) · ψ_f(x_f)`. These are the signs of Tate's thesis; the character
`x ↦ ψ(-x)`, equal to `e(-Tr_{K/ℚ} a)` at `a ∈ K` in the finite adeles, is the standard character
of the opposite normalisation.

## Main definitions

* `TauCeti.GlobalNumberFields.finiteAdeleStdAddChar K`: the finite part `ψ_f`.
* `TauCeti.GlobalNumberFields.infiniteAdeleTrace K`: the archimedean trace `K∞ → ℝ`.
* `TauCeti.GlobalNumberFields.infiniteAdeleStdAddChar K`: the infinite part `e(-Tr_∞)`.
* `TauCeti.GlobalNumberFields.adeleStdAddChar K`: the standard additive character of `𝔸[K]`.

## Main results

* `TauCeti.GlobalNumberFields.finiteAdeleStdAddChar_algebraMap`,
  `TauCeti.GlobalNumberFields.finiteAdeleStdAddChar_eq_one_of_mem_integralAdeles`,
  `TauCeti.GlobalNumberFields.eq_finiteAdeleStdAddChar`: `ψ_f` is `e(Tr a)` on `K`, trivial on
  `Ô`, and the only such character.
* `TauCeti.GlobalNumberFields.infiniteAdeleTrace_algebraMap`: `Tr_∞` restricts to `Tr_{K/ℚ}`.
* `TauCeti.GlobalNumberFields.adeleStdAddChar_algebraMap`: `ψ` is trivial on `K`.
* `TauCeti.GlobalNumberFields.continuous_adeleStdAddChar`: `ψ` is continuous.

## References

* J. Tate, *Fourier analysis in number fields and Hecke's zeta-functions*, thesis (1950), in
  J. W. S. Cassels and A. Fröhlich, eds., *Algebraic Number Theory*, Chapter XV, §§2.2, 3.1, 4.1.

The finite part, its triviality on `Ô` and its values on `K`, and the triviality of `ψ` on `K`
follow grh-lean (https://github.com/lsernau/grh-lean, Apache 2.0, Copyright 2026 Anthropic PBC),
`src/Lib/Adelic/Adeles/AdditiveCharacter.lean` (`New.ψf`, `New.stdAddChar`) and
`src/Lib/Adelic/Adeles/StrongApproximation.lean` (`New.stdAddChar_toAdele`), stated there for a
totally complex field with adeles `ℂ^Φ × 𝔸ᶠ[K]`; here `K` is any number field, with Mathlib's
adele ring.
-/

public section

open IsDedekindDomain NumberField NumberField.InfinitePlace NumberField.InfinitePlace.Completion
open scoped NumberField.AdeleRing

namespace TauCeti.GlobalNumberFields

variable (K : Type*) [Field K] [NumberField K]

/-! ### The finite part -/

/-- The finite part `ψ_f` of the standard additive character: the additive character of the finite
adeles that is trivial on the integral finite adeles and equals `e(Tr_{K/ℚ} a)` at `a ∈ K`. -/
noncomputable def finiteAdeleStdAddChar : AddChar (FiniteAdeleRing (𝓞 K) K) Circle :=
  FiniteAdeleRing.extendAddChar (numberFieldTraceChar K) (numberFieldTraceChar_algebraMap_eq_one K)

/-- `ψ_f` is the extension of the trace character of `K`, trivial on `𝓞 K`, to the finite adeles
that is trivial on the integral finite adeles. -/
theorem finiteAdeleStdAddChar_def :
    finiteAdeleStdAddChar K = FiniteAdeleRing.extendAddChar (numberFieldTraceChar K)
      (numberFieldTraceChar_algebraMap_eq_one K) := (rfl)

variable {K}

/-- `ψ_f` at the diagonal image of `a ∈ K` is `e(Tr_{K/ℚ} a)`. -/
@[simp]
theorem finiteAdeleStdAddChar_algebraMap (a : K) :
    finiteAdeleStdAddChar K (algebraMap K (FiniteAdeleRing (𝓞 K) K) a) = numberFieldTraceChar K a :=
  FiniteAdeleRing.extendAddChar_algebraMap a

/-- `ψ_f` at a finite adele `x` is `e(Tr_{K/ℚ} a)` for every `a ∈ K` with `a - x` integral. -/
theorem finiteAdeleStdAddChar_apply_of_sub_mem_integralAdeles {x : FiniteAdeleRing (𝓞 K) K}
    {a : K} (h : algebraMap K (FiniteAdeleRing (𝓞 K) K) a - x ∈
      FiniteAdeleRing.integralAdeles (𝓞 K) K) :
    finiteAdeleStdAddChar K x = numberFieldTraceChar K a :=
  FiniteAdeleRing.extendAddChar_apply_of_sub_mem_integralAdeles h

/-- `ψ_f` is trivial on the integral finite adeles. -/
theorem finiteAdeleStdAddChar_eq_one_of_mem_integralAdeles {x : FiniteAdeleRing (𝓞 K) K}
    (hx : x ∈ FiniteAdeleRing.integralAdeles (𝓞 K) K) : finiteAdeleStdAddChar K x = 1 :=
  FiniteAdeleRing.extendAddChar_eq_one_of_mem_integralAdeles hx

/-- **Uniqueness of `ψ_f`.** An additive character of the finite adeles that equals
`e(Tr_{K/ℚ} a)` at every `a ∈ K` and is trivial on the integral finite adeles is `ψ_f`. -/
theorem eq_finiteAdeleStdAddChar {ψ : AddChar (FiniteAdeleRing (𝓞 K) K) Circle}
    (halg : ∀ a : K, ψ (algebraMap K (FiniteAdeleRing (𝓞 K) K) a) = numberFieldTraceChar K a)
    (hint : ∀ x ∈ FiniteAdeleRing.integralAdeles (𝓞 K) K, ψ x = 1) :
    ψ = finiteAdeleStdAddChar K :=
  FiniteAdeleRing.eq_extendAddChar halg hint

/-- `ψ_f` is continuous. -/
theorem continuous_finiteAdeleStdAddChar : Continuous (finiteAdeleStdAddChar K) :=
  FiniteAdeleRing.continuous_extendAddChar

/-! ### The infinite part -/

variable (K) in
/-- The archimedean trace `Tr_∞ x = ∑_w mult w · Re (x_w)` on the infinite adeles, where `Re (x_w)`
is the real part of the image of `x_w` under the extension `w.Completion → ℂ` of `w.embedding`.
At a complex place it is `2 Re (x_w)`, which does not depend on the embedding chosen for `w`. -/
noncomputable def infiniteAdeleTrace : InfiniteAdeleRing K →+ ℝ where
  toFun x := ∑ w : InfinitePlace K, (mult w : ℝ) * (extensionEmbedding w (x w)).re
  map_zero' := Finset.sum_eq_zero fun w _ ↦ by
    rw [Pi.zero_apply, map_zero, Complex.zero_re, mul_zero]
  map_add' x y := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun w _ ↦ ?_
    rw [Pi.add_apply, map_add, Complex.add_re, mul_add]

/-- The archimedean trace is the sum over the infinite places of `mult w · Re (x_w)`. -/
theorem infiniteAdeleTrace_apply (x : InfiniteAdeleRing K) :
    infiniteAdeleTrace K x =
      ∑ w : InfinitePlace K, (mult w : ℝ) * (extensionEmbedding w (x w)).re :=
  (rfl)

/-- On the diagonal copy of `K`, the archimedean trace is the trace `Tr_{K/ℚ}`. -/
@[simp]
theorem infiniteAdeleTrace_algebraMap (a : K) :
    infiniteAdeleTrace K (algebraMap K (InfiniteAdeleRing K) a) = Algebra.trace ℚ K a := by
  rw [← TauCeti.NumberField.InfinitePlace.sum_mult_mul_re_embedding_eq_trace,
    infiniteAdeleTrace_apply]
  simp

/-- The archimedean trace is continuous. -/
theorem continuous_infiniteAdeleTrace : Continuous (infiniteAdeleTrace K) := by
  rw [show ⇑(infiniteAdeleTrace K) = _ from funext infiniteAdeleTrace_apply]
  exact continuous_finsetSum _ fun w _ ↦ continuous_const.mul <| Complex.continuous_re.comp <|
    (isometry_extensionEmbedding w).continuous.comp (continuous_apply w)

variable (K) in
/-- The infinite part `x ↦ e(-Tr_∞ x)` of the standard additive character. -/
noncomputable def infiniteAdeleStdAddChar : AddChar (InfiniteAdeleRing K) Circle :=
  Real.fourierChar.compAddMonoidHom (-infiniteAdeleTrace K)

/-- The infinite part at `x` is `e(-Tr_∞ x)`. -/
theorem infiniteAdeleStdAddChar_apply (x : InfiniteAdeleRing K) :
    infiniteAdeleStdAddChar K x = Real.fourierChar (-infiniteAdeleTrace K x) :=
  (rfl)

/-- The infinite part at the diagonal image of `a ∈ K` is `e(-Tr_{K/ℚ} a)`, the inverse of the
trace character at `a`. -/
@[simp]
theorem infiniteAdeleStdAddChar_algebraMap (a : K) :
    infiniteAdeleStdAddChar K (algebraMap K (InfiniteAdeleRing K) a) =
      (numberFieldTraceChar K a)⁻¹ := by
  rw [infiniteAdeleStdAddChar_apply, infiniteAdeleTrace_algebraMap, numberFieldTraceChar_apply,
    AddChar.map_neg_eq_inv]

/-- The infinite part is continuous. -/
theorem continuous_infiniteAdeleStdAddChar : Continuous (infiniteAdeleStdAddChar K) :=
  Real.continuous_fourierChar.comp continuous_infiniteAdeleTrace.neg

/-! ### The standard additive character -/

variable (K) in
/-- The standard additive character `ψ(x) = e(-Tr_∞ x_∞) · ψ_f(x_f)` of the adeles of `K`. -/
noncomputable def adeleStdAddChar : AddChar 𝔸[K] Circle where
  toFun x := infiniteAdeleStdAddChar K x.1 * finiteAdeleStdAddChar K x.2
  map_zero_eq_one' := by
    rw [Prod.fst_zero, Prod.snd_zero, AddChar.map_zero_eq_one, AddChar.map_zero_eq_one, mul_one]
  map_add_eq_mul' x y := by
    rw [Prod.fst_add, Prod.snd_add, AddChar.map_add_eq_mul, AddChar.map_add_eq_mul,
      mul_mul_mul_comm]

/-- The standard additive character is the product of its infinite and finite parts. -/
theorem adeleStdAddChar_apply (x : 𝔸[K]) :
    adeleStdAddChar K x = infiniteAdeleStdAddChar K x.1 * finiteAdeleStdAddChar K x.2 :=
  (rfl)

/-- **The standard additive character is trivial on `K`.** -/
@[simp]
theorem adeleStdAddChar_algebraMap (a : K) : adeleStdAddChar K (algebraMap K 𝔸[K] a) = 1 := by
  rw [adeleStdAddChar_apply, AdeleRing.algebraMap_fst_def, AdeleRing.algebraMap_snd_def,
    infiniteAdeleStdAddChar_algebraMap, finiteAdeleStdAddChar_algebraMap, inv_mul_cancel]

/-- The standard additive character is continuous. -/
theorem continuous_adeleStdAddChar : Continuous (adeleStdAddChar K) :=
  (continuous_infiniteAdeleStdAddChar.comp continuous_fst).mul
    (continuous_finiteAdeleStdAddChar.comp continuous_snd)

end TauCeti.GlobalNumberFields
