/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.NumberField.AdeleRing
public import Mathlib.NumberTheory.NumberField.InfinitePlace.TotallyRealComplex
public import TauCeti.NumberTheory.NumberField.AddChar
public import TauCeti.RingTheory.DedekindDomain.FiniteAdeleRing.AddChar
public import TauCeti.RingTheory.DedekindDomain.FiniteAdeleRing.FractionalIdeal

import TauCeti.Algebra.Group.AddChar.Prod
import TauCeti.NumberTheory.NumberField.Global.Adeles.Basic
import TauCeti.NumberTheory.NumberField.InfinitePlace.Trace

/-!
# The standard additive character of the adeles of a number field

Let `K` be a number field, with adele ring `𝔸 = K∞ × 𝔸ᶠ`, integral finite adeles `Ô`, and let
`e(t) = exp (2πi t)`. This file constructs the standard additive character `ψ` of `𝔸`, trivial on
the diagonal copy of `K`, as the product of a finite and an infinite part.

* The finite part `ψ_f = finiteAdeleAddChar K` is the character of `𝔸ᶠ` that is trivial on `Ô` and
  equals `e(Tr_{K/ℚ} a)` at `a ∈ K`. It exists and is unique because `𝔸ᶠ = K + Ô` and
  `K ∩ Ô = 𝓞 K`, while `Tr_{K/ℚ}` takes integer values on `𝓞 K`; it is the extension
  `IsDedekindDomain.FiniteAdeleRing.extendAddChar` of the trace character
  `TauCeti.numberFieldTraceChar K`. It is locally constant, and the `z ∈ 𝔸ᶠ` with `ψ_f (z u) = 1`
  for every `u ∈ Ô` form the inverse different times `Ô`.
* The infinite part `ψ_∞ = infiniteAdeleAddChar K` is `x ↦ e(-∑_w Tr_{K_w/ℝ} x_w)`, where the
  local trace `Tr_{K_w/ℝ}` is the identity at a real place and `z ↦ z + conj z = 2 Re z` at a
  complex place, read in `ℂ` through the embedding of the completion `K_w`.
* The standard character is `ψ (x) = ψ_∞ (x_∞) · ψ_f (x_f)` (`adeleAddChar K`). At `a ∈ K` the two
  parts are `e(-Tr_{K/ℚ} a)` and `e(Tr_{K/ℚ} a)`, because `Tr_{K/ℚ} a = ∑_w Tr_{K_w/ℝ} a`
  (`TauCeti.NumberField.InfinitePlace.sum_mult_mul_re_embedding_eq_trace`); so `ψ` is trivial
  on `K`.

When `K` is totally complex, `ψ (x) = e(-∑_w 2 Re x_w) · ψ_f (x_f)`
(`adeleAddChar_apply_of_isTotallyComplex`). The real part does not depend on which of the two
complex embeddings above `w` identifies `K_w` with `ℂ`.

## Main definitions

* `TauCeti.GlobalNumberFields.finiteAdeleAddChar`: the standard character `ψ_f` of the finite
  adeles.
* `TauCeti.GlobalNumberFields.infiniteAdeleTrace`: the trace `∑_w Tr_{K_w/ℝ}` of the infinite
  adeles.
* `TauCeti.GlobalNumberFields.infiniteAdeleAddChar`: the character `e(-∑_w Tr_{K_w/ℝ} x_w)` of the
  infinite adeles.
* `TauCeti.GlobalNumberFields.adeleAddChar`: the standard character `ψ` of the adeles.

## Main results

* `TauCeti.GlobalNumberFields.finiteAdeleAddChar_algebraMap`,
  `TauCeti.GlobalNumberFields.finiteAdeleAddChar_apply_of_mem_integralAdeles`: `ψ_f` is
  `e(Tr_{K/ℚ} ·)` on `K` and trivial on `Ô`.
* `TauCeti.GlobalNumberFields.eq_finiteAdeleAddChar_iff`: these two properties characterize `ψ_f`.
* `TauCeti.GlobalNumberFields.continuous_finiteAdeleAddChar`: `ψ_f` is continuous.
* `TauCeti.GlobalNumberFields.forall_finiteAdeleAddChar_mul_eq_one_iff`: the annihilator of `Ô`
  under `(z, u) ↦ ψ_f (z u)` is the finite adelic ideal of the inverse different.
* `TauCeti.GlobalNumberFields.infiniteAdeleTrace_algebraMap`: on `K` the trace of the infinite
  adeles is `Tr_{K/ℚ}`.
* `TauCeti.GlobalNumberFields.adeleAddChar_algebraMap`: `ψ` is trivial on `K`.
* `TauCeti.GlobalNumberFields.continuous_adeleAddChar`: `ψ` is continuous.
* `TauCeti.GlobalNumberFields.adeleAddChar_apply_of_isTotallyComplex`: the formula for `ψ` over a
  totally complex field.

## References

* J. Tate, *Fourier analysis in number fields and Hecke's zeta-functions*, in
  J. W. S. Cassels and A. Fröhlich, eds., *Algebraic Number Theory* (1967).
-/

public section

noncomputable section

open IsDedekindDomain IsDedekindDomain.FiniteAdeleRing NumberField NumberField.InfinitePlace
open scoped NumberField.AdeleRing nonZeroDivisors

namespace TauCeti.GlobalNumberFields

variable (K : Type*) [Field K] [NumberField K]

/-! ### The finite part -/

/-- **The standard additive character `ψ_f` of the finite adeles** of a number field `K`: the
character of `𝔸ᶠ[K]` that is trivial on the integral finite adeles and equals
`exp (2πi Tr_{K/ℚ} a)` at `a ∈ K` (`eq_finiteAdeleAddChar_iff`). Its value at `a` is
`exp (2πi Tr_{K/ℚ} x)` for any `x ∈ K` such that `a - x` is integral at every finite place. -/
def finiteAdeleAddChar : AddChar (FiniteAdeleRing (𝓞 K) K) Circle :=
  extendAddChar (numberFieldTraceChar K) (numberFieldTraceChar_algebraMap K)

variable {K}

/-- The value of `ψ_f` at a finite adele `a` is `exp (2πi Tr_{K/ℚ} x)` for every `x ∈ K` such that
`a - x` is an integral finite adele. -/
theorem finiteAdeleAddChar_apply_of_sub_mem {a : FiniteAdeleRing (𝓞 K) K} {x : K}
    (hx : a - algebraMap K (FiniteAdeleRing (𝓞 K) K) x ∈ integralAdeles (𝓞 K) K) :
    finiteAdeleAddChar K a = numberFieldTraceChar K x :=
  extendAddChar_apply_of_sub_mem _ _ hx

/-- On the diagonal copy of `K`, `ψ_f` is `x ↦ exp (2πi Tr_{K/ℚ} x)`. -/
@[simp]
theorem finiteAdeleAddChar_algebraMap (x : K) :
    finiteAdeleAddChar K (algebraMap K (FiniteAdeleRing (𝓞 K) K) x) = numberFieldTraceChar K x :=
  extendAddChar_algebraMap _ _ x

/-- `ψ_f` is trivial on the integral finite adeles. -/
theorem finiteAdeleAddChar_apply_of_mem_integralAdeles {a : FiniteAdeleRing (𝓞 K) K}
    (ha : a ∈ integralAdeles (𝓞 K) K) : finiteAdeleAddChar K a = 1 :=
  extendAddChar_apply_of_mem_integralAdeles _ _ ha

/-- **Characterization of `ψ_f`**: it is the unique additive character of the finite adeles that
is trivial on the integral finite adeles and equals `exp (2πi Tr_{K/ℚ} x)` at every `x ∈ K`. -/
theorem eq_finiteAdeleAddChar_iff {ψ : AddChar (FiniteAdeleRing (𝓞 K) K) Circle} :
    ψ = finiteAdeleAddChar K ↔ (∀ a ∈ integralAdeles (𝓞 K) K, ψ a = 1) ∧
      ∀ x : K, ψ (algebraMap K (FiniteAdeleRing (𝓞 K) K) x) = numberFieldTraceChar K x :=
  eq_extendAddChar_iff _ _

/-- `ψ_f` is locally constant: it is constant on the cosets of the open subgroup of integral finite
adeles. -/
theorem isLocallyConstant_finiteAdeleAddChar : IsLocallyConstant (finiteAdeleAddChar K) :=
  isLocallyConstant_extendAddChar _ _

/-- `ψ_f` is continuous. -/
@[continuity, fun_prop]
theorem continuous_finiteAdeleAddChar : Continuous (finiteAdeleAddChar K) :=
  isLocallyConstant_finiteAdeleAddChar.continuous

/-- **The annihilator of the integral finite adeles under `ψ_f`.** A finite adele `z` satisfies
`ψ_f (z u) = 1` for every integral finite adele `u` exactly when `z` lies in the finite adelic
ideal `𝔇⁻¹ Ô` of the inverse different `𝔇⁻¹ = FractionalIdeal.dual ℤ ℚ 1`. -/
theorem forall_finiteAdeleAddChar_mul_eq_one_iff (z : FiniteAdeleRing (𝓞 K) K) :
    (∀ u ∈ integralAdeles (𝓞 K) K, finiteAdeleAddChar K (z * u) = 1) ↔
      z ∈ finiteAdelicIdeal (Units.mk0 (FractionalIdeal.dual ℤ ℚ 1)
        (FractionalIdeal.dual_ne_zero ℤ ℚ one_ne_zero)) := by
  set D := Units.mk0 (FractionalIdeal.dual ℤ ℚ (1 : FractionalIdeal (𝓞 K)⁰ K))
    (FractionalIdeal.dual_ne_zero ℤ ℚ one_ne_zero)
  -- the condition on the rational part of `z` says that it lies in the inverse different
  have hdual (x : K) : (∀ r : 𝓞 K, numberFieldTraceChar K (x * algebraMap (𝓞 K) K r) = 1) ↔
      x ∈ (D : FractionalIdeal (𝓞 K)⁰ K) := by
    rw [Units.val_mk0, FractionalIdeal.mem_dual_iff_forall_numberFieldTraceChar_eq_one _
      one_ne_zero]
    simp only [FractionalIdeal.mem_one_iff, forall_exists_index, forall_apply_eq_imp_iff]
  rw [finiteAdeleAddChar, forall_extendAddChar_mul_eq_one_iff]
  simp only [hdual]
  constructor
  · -- `z = x + (z - x)` with `x ∈ 𝔇⁻¹` and `z - x ∈ Ô = Ô · 1 ⊆ 𝔇⁻¹ Ô`
    rintro ⟨x, hx, hzx⟩
    have hone : algebraMap K (FiniteAdeleRing (𝓞 K) K) 1 ∈ finiteAdelicIdeal D :=
      (algebraMap_mem_finiteAdelicIdeal_iff D 1).mpr
        (FractionalIdeal.one_le_dual_one ℤ ℚ (FractionalIdeal.one_mem_one _))
    have hint := mul_mem_finiteAdelicIdeal (mem_finiteAdelicIdeal_one.mpr hzx) hone
    rw [one_mul, map_one, mul_one] at hint
    simpa using add_mem hint ((algebraMap_mem_finiteAdelicIdeal_iff D x).mpr hx)
  · -- `𝔇⁻¹ Ô` is the closure of `𝔇⁻¹`, and `z + Ô` is an open neighbourhood of `z`
    intro hz
    have hcl : z ∈ closure (algebraMap K (FiniteAdeleRing (𝓞 K) K) ''
        (D : FractionalIdeal (𝓞 K)⁰ K)) := by
      rwa [closure_image_algebraMap_fractionalIdeal]
    have hU : IsOpen {y : FiniteAdeleRing (𝓞 K) K | z - y ∈ integralAdeles (𝓞 K) K} :=
      (isOpen_integralAdeles (𝓞 K) K).preimage (by fun_prop)
    obtain ⟨_, hy, x, hx, rfl⟩ := mem_closure_iff.mp hcl _ hU (by simp)
    exact ⟨x, hx, hy⟩

/-! ### The infinite part -/

variable (K)

/-- **The trace of the infinite adeles**, `x ↦ ∑_w Tr_{K_w/ℝ} x_w`: the local trace is the
identity at a real place and `z ↦ z + conj z = 2 Re z` at a complex place, read in `ℂ` through the
embedding of the completion `K_w`. On `K` it is the trace `Tr_{K/ℚ}`
(`infiniteAdeleTrace_algebraMap`). -/
def infiniteAdeleTrace : InfiniteAdeleRing K →+ ℝ where
  toFun x := ∑ w, (w.mult : ℝ) * (Completion.extensionEmbedding w (x w)).re
  map_zero' := by simp
  map_add' x y := by simp [mul_add, Finset.sum_add_distrib]

variable {K}

/-- The trace of an infinite adele is `∑_w mult w * Re x_w`, with `x_w` read in `ℂ` through the
embedding of the completion. -/
theorem infiniteAdeleTrace_apply (x : InfiniteAdeleRing K) :
    infiniteAdeleTrace K x = ∑ w, (w.mult : ℝ) * (Completion.extensionEmbedding w (x w)).re :=
  (rfl)

/-- On the diagonal copy of `K`, the trace of the infinite adeles is the trace `Tr_{K/ℚ}`. -/
@[simp]
theorem infiniteAdeleTrace_algebraMap (x : K) :
    infiniteAdeleTrace K (algebraMap K (InfiniteAdeleRing K) x) = Algebra.trace ℚ K x := by
  rw [infiniteAdeleTrace_apply, ← NumberField.InfinitePlace.sum_mult_mul_re_embedding_eq_trace]
  simp

/-- The trace of the infinite adeles is continuous. -/
@[continuity, fun_prop]
theorem continuous_infiniteAdeleTrace : Continuous (infiniteAdeleTrace K) :=
  (continuous_finsetSum _ fun w _ ↦ continuous_const.mul <| Complex.continuous_re.comp <|
    (Completion.isometry_extensionEmbedding w).continuous.comp (continuous_apply w)).congr
    fun x ↦ (infiniteAdeleTrace_apply x).symm

variable (K)

/-- **The standard additive character of the infinite adeles**, `x ↦ exp (-2πi ∑_w Tr_{K_w/ℝ} x_w)`,
where `Tr_{K_w/ℝ}` is the identity at a real place and `2 Re` at a complex place. On `K` it is
`x ↦ exp (-2πi Tr_{K/ℚ} x)` (`infiniteAdeleAddChar_algebraMap`). -/
def infiniteAdeleAddChar : AddChar (InfiniteAdeleRing K) Circle :=
  Real.fourierChar.compAddMonoidHom (-infiniteAdeleTrace K)

variable {K}

/-- The standard character of the infinite adeles is `exp (-2πi ·)` of their trace. -/
theorem infiniteAdeleAddChar_apply (x : InfiniteAdeleRing K) :
    infiniteAdeleAddChar K x = Real.fourierChar (-infiniteAdeleTrace K x) :=
  (rfl)

/-- On the diagonal copy of `K`, the standard character of the infinite adeles is
`x ↦ exp (-2πi Tr_{K/ℚ} x)`, the inverse of the trace character. -/
@[simp]
theorem infiniteAdeleAddChar_algebraMap (x : K) :
    infiniteAdeleAddChar K (algebraMap K (InfiniteAdeleRing K) x) =
      (numberFieldTraceChar K x)⁻¹ := by
  rw [infiniteAdeleAddChar_apply, infiniteAdeleTrace_algebraMap, numberFieldTraceChar_apply,
    AddChar.map_neg_eq_inv]

/-- The standard character of the infinite adeles is continuous. -/
@[continuity, fun_prop]
theorem continuous_infiniteAdeleAddChar : Continuous (infiniteAdeleAddChar K) :=
  Real.continuous_fourierChar.comp continuous_infiniteAdeleTrace.neg

/-! ### The standard character of the adeles -/

variable (K)

/-- **The standard additive character `ψ` of the adeles** of a number field `K`:
`ψ (x) = ψ_∞ (x_∞) · ψ_f (x_f)`, with `ψ_∞ (x_∞) = exp (-2πi ∑_w Tr_{K_w/ℝ} x_w)` and `ψ_f` the
standard character of the finite adeles. It is trivial on the diagonal copy of `K`
(`adeleAddChar_algebraMap`). -/
def adeleAddChar : AddChar 𝔸[K] Circle :=
  AddChar.coprodEquiv (infiniteAdeleAddChar K, finiteAdeleAddChar K)

variable {K}

/-- The standard character of the adeles is the product of its infinite and finite parts. -/
theorem adeleAddChar_apply (x : 𝔸[K]) :
    adeleAddChar K x = infiniteAdeleAddChar K x.1 * finiteAdeleAddChar K x.2 :=
  AddChar.coprodEquiv_apply _ x

/-- **The standard character of the adeles is trivial on `K`**: at `x ∈ K` its infinite and finite
parts are `exp (-2πi Tr_{K/ℚ} x)` and `exp (2πi Tr_{K/ℚ} x)`. -/
@[simp]
theorem adeleAddChar_algebraMap (x : K) : adeleAddChar K (algebraMap K 𝔸[K] x) = 1 := by
  rw [adeleAddChar_apply, AdeleRing.algebraMap_fst_def, AdeleRing.algebraMap_snd_def,
    infiniteAdeleAddChar_algebraMap, finiteAdeleAddChar_algebraMap, inv_mul_cancel]

/-- The standard character of the adeles is continuous. -/
@[continuity, fun_prop]
theorem continuous_adeleAddChar : Continuous (adeleAddChar K) :=
  ((continuous_infiniteAdeleAddChar.comp continuous_fst).mul
    (continuous_finiteAdeleAddChar.comp continuous_snd)).congr fun x ↦ (adeleAddChar_apply x).symm

/-- **The standard character of the adeles of a totally complex field**:
`ψ (x) = exp (-2πi ∑_w 2 Re x_w) · ψ_f (x_f)`, with `x_w` read in `ℂ` through the embedding of the
completion at the infinite place `w`. -/
theorem adeleAddChar_apply_of_isTotallyComplex [IsTotallyComplex K] (x : 𝔸[K]) :
    adeleAddChar K x = Real.fourierChar
      (-∑ w, 2 * (Completion.extensionEmbedding w (x.1 w)).re) * finiteAdeleAddChar K x.2 := by
  simp [adeleAddChar_apply, infiniteAdeleAddChar_apply, infiniteAdeleTrace_apply,
    IsTotallyComplex.mult_eq]

end TauCeti.GlobalNumberFields
