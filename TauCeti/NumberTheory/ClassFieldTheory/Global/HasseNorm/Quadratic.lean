/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex, The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.NumberField.Completion.InfinitePlace
public import Mathlib.RingTheory.DedekindDomain.AdicValuation.Completion
import Mathlib.Algebra.Field.Shrink
import Mathlib.Algebra.QuadraticAlgebra.Basic
import Mathlib.Algebra.Ring.Shrink
import Mathlib.RingTheory.Finiteness.Small
import Mathlib.Tactic.NormNum.IsSquare
import TauCeti.Analysis.Normed.Field.WithAbs
import TauCeti.NumberTheory.ClassFieldTheory.Global.HasseNorm.Basic
import TauCeti.NumberTheory.NumberField.InfinitePlace.Transport
import TauCeti.NumberTheory.NumberField.RingOfIntegers.Transport
import TauCeti.RingTheory.DedekindDomain.AdicValuation.Transport
import TauCeti.RingTheory.Norm.Quadratic

/-!
# Quadratic norm equations over number fields

For a nonsquare `d` in a number field `K`, the equation `a = x² - d y²`, with `a ≠ 0`, has a
solution in `K` exactly when it has a solution in every finite and infinite completion of `K`.
This is the cyclic Hasse norm theorem for `K(√d)/K`, expressed in coordinates, and holds in any
universe: over `Type` it is read off directly from `isGlobalNorm_iff_isLocalNormEverywhere`, and
`Shrink.ringEquiv K` transports both the global equation and the finite and archimedean local
equations (`IsDedekindDomain.HeightOneSpectrum.adicCompletionCongr` and
`AbsoluteValue.Completion.congr`) to arbitrary universes.

The local algebras are the scalar extensions `K_v ⊗[K] K(√d)`. In particular a split place
still uses the two-dimensional split algebra, rather than a field incorrectly assumed to have
degree two. The norm calculation in these algebras is
`TauCeti.Algebra.mem_range_normUnits_baseChange_iff_exists_sq_sub_mul_sq`.

`exists_sq_sub_five_mul_sq_iff_forall_completion` gives the explicit equation `a = x² - 5y²`
over `ℚ` and its completions.
Infinite places remain in the statement, including complex places for a general number field.

## References

* J. Neukirch, *Algebraic Number Theory*, Chapter VI, §4 (the cyclic Hasse norm theorem).
* J. S. Milne, *Class Field Theory*, v4.03, Chapter VII, §2.
-/

public noncomputable section

open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum NumberField

namespace TauCeti.ClassFieldTheory

/-- The quadratic Hasse norm criterion in `Type`, read directly from the idelic cyclic Hasse norm
theorem. -/
private theorem exists_sq_sub_mul_sq_iff_forall_completion_zero {K₀ : Type} [Field K₀]
    [NumberField K₀] {d : K₀} (hd : ¬ IsSquare d) (a : K₀ˣ) :
    (∃ x y : K₀, (a : K₀) = x ^ 2 - d * y ^ 2) ↔
      (∀ v : HeightOneSpectrum (𝓞 K₀), ∃ x y : v.adicCompletion K₀,
        algebraMap K₀ (v.adicCompletion K₀) (a : K₀) =
          x ^ 2 - algebraMap K₀ (v.adicCompletion K₀) d * y ^ 2) ∧
      ∀ w : InfinitePlace K₀, ∃ x y : w.Completion,
        algebraMap K₀ w.Completion (a : K₀) =
          x ^ 2 - algebraMap K₀ w.Completion d * y ^ 2 := by
  have : Fact (¬ IsSquare d) := ⟨hd⟩
  have : NumberField (QuadraticAlgebra K₀ d 0) := NumberField.of_module_finite K₀ _
  have : Algebra.IsQuadraticExtension K₀ (QuadraticAlgebra K₀ d 0) :=
    ⟨QuadraticAlgebra.finrank_eq_two d 0⟩
  have hθ : (QuadraticAlgebra.omega : QuadraticAlgebra K₀ d 0) ∉
      Set.range (algebraMap K₀ (QuadraticAlgebra K₀ d 0)) := by
    rintro ⟨x, hx⟩
    have := congrArg QuadraticAlgebra.im hx
    simp at this
  have hθ2 : (QuadraticAlgebra.omega : QuadraticAlgebra K₀ d 0) ^ 2 =
      algebraMap K₀ (QuadraticAlgebra K₀ d 0) d := by
    simp [QuadraticAlgebra.omega_pow_two_eq_add, Algebra.algebraMap_eq_smul_one]
  rw [← mem_normGroup_iff_exists_sq_sub_mul_sq _ hθ hθ2,
    isGlobalNorm_iff_isLocalNormEverywhere K₀ _, GlobalNumberFields.isLocalNormEverywhere_def]
  simp only [GlobalNumberFields.isFiniteLocalNorm_def,
    GlobalNumberFields.isInfiniteLocalNorm_def,
    Algebra.mem_range_normUnits_baseChange_iff_exists_sq_sub_mul_sq _ hθ hθ2,
    Units.coe_map, RingHom.toMonoidHom_eq_coe, MonoidHom.coe_ofClass]

variable {K : Type*} [Field K] [NumberField K]

/-- For a nonsquare `d` in a number field, solvability of the nonzero quadratic norm equation
`a = x² - d y²` is detected by all finite and infinite completions. -/
theorem exists_sq_sub_mul_sq_iff_forall_completion {d : K}
    (hd : ¬ IsSquare d) (a : Kˣ) :
    (∃ x y : K, (a : K) = x ^ 2 - d * y ^ 2) ↔
      (∀ v : HeightOneSpectrum (𝓞 K), ∃ x y : v.adicCompletion K,
        algebraMap K (v.adicCompletion K) (a : K) =
          x ^ 2 - algebraMap K (v.adicCompletion K) d * y ^ 2) ∧
      ∀ w : InfinitePlace K, ∃ x y : w.Completion,
        algebraMap K w.Completion (a : K) =
          x ^ 2 - algebraMap K w.Completion d * y ^ 2 := by
  have : Small.{0} K := Module.Finite.small.{0} ℚ K
  let e : Shrink.{0} K ≃+* K := Shrink.ringEquiv K
  have : NumberField (Shrink.{0} K) := .of_ringEquiv K (Shrink.{0} K) e.symm
  let d₀ : Shrink.{0} K := e.symm d
  have hd₀ : d = e d₀ := (e.apply_symm_apply d).symm
  have hnsq₀ : ¬ IsSquare d₀ := fun h ↦ hd (hd₀ ▸ h.map (e : Shrink.{0} K →* K))
  let a₀ : (Shrink.{0} K)ˣ := Units.map (e.symm : K →* Shrink.{0} K) a
  have ha₀ : (a : K) = e (a₀ : Shrink.{0} K) := (e.apply_symm_apply a).symm
  rw [ha₀, hd₀, e.exists_sq_sub_mul_sq_iff (a₀ : Shrink.{0} K) d₀,
    exists_sq_sub_mul_sq_iff_forall_completion_zero hnsq₀ a₀]
  refine and_congr ?_ ?_
  · refine (HeightOneSpectrum.equivOfRingEquiv
      (RingOfIntegers.mapRingEquiv e)).forall_congr fun v₀ ↦ ?_
    let v := HeightOneSpectrum.equivOfRingEquiv (RingOfIntegers.mapRingEquiv e) v₀
    have hv (x : Shrink.{0} K) : v.valuation K (e x) = v₀.valuation (Shrink.{0} K) x := by
      simpa only [RingOfIntegers.ringEquivOfRingEquiv_mapRingEquiv] using
        valuation_ringEquivOfRingEquiv (K := Shrink.{0} K) (K' := K)
          (RingOfIntegers.mapRingEquiv e)
          (asIdeal_equivOfRingEquiv (RingOfIntegers.mapRingEquiv e) v₀) x
    exact ((adicCompletionCongr v₀ v e hv).exists_sq_sub_mul_sq_algebraMap_iff
      (adicCompletionCongr_algebraMap hv) (a₀ : Shrink.{0} K) d₀).symm
  · refine (InfinitePlace.equivOfRingEquiv e).forall_congr fun w₀ ↦ ?_
    have hw := InfinitePlace.apply_eq_of_eq_equivOfRingEquiv e (v := w₀) rfl
    exact ((AbsoluteValue.Completion.congr e hw).exists_sq_sub_mul_sq_algebraMap_iff
      (AbsoluteValue.Completion.congr_algebraMap hw) (a₀ : Shrink.{0} K) d₀).symm

/-- **The Hasse norm test for `ℚ(√5)`.** A nonzero rational is a value of `x² - 5y²` over `ℚ`
exactly when it is a value over every finite and infinite completion of `ℚ`. -/
theorem exists_sq_sub_five_mul_sq_iff_forall_completion (a : ℚˣ) :
    (∃ x y : ℚ, (a : ℚ) = x ^ 2 - 5 * y ^ 2) ↔
      (∀ v : HeightOneSpectrum (𝓞 ℚ), ∃ x y : v.adicCompletion ℚ,
        algebraMap ℚ (v.adicCompletion ℚ) (a : ℚ) = x ^ 2 - 5 * y ^ 2) ∧
      ∀ w : InfinitePlace ℚ, ∃ x y : w.Completion,
        algebraMap ℚ w.Completion (a : ℚ) = x ^ 2 - 5 * y ^ 2 := by
  simpa using exists_sq_sub_mul_sq_iff_forall_completion
    (K := ℚ) (d := 5) (by norm_num) a

end TauCeti.ClassFieldTheory
