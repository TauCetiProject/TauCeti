/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.DedekindDomain.AdicValuation.Completion
public import TauCeti.NumberTheory.NumberField.TotallyPositive
import Mathlib.Algebra.QuadraticAlgebra.Basic
import TauCeti.NumberTheory.ClassFieldTheory.Global.HasseNorm.Quadratic
import TauCeti.NumberTheory.NumberField.InfinitePlace.Completion.Basic
import TauCeti.RingTheory.DedekindDomain.AdicCompletionExtension
import TauCeti.RingTheory.DedekindDomain.PrimesAbove

/-!
# The Hasse principle for sums of two squares

Let `K` be a number field. A totally positive `x ∈ K` is a sum of two squares in `K` exactly when it
is a sum of two squares in every completion `K_v` at a finite place
(`TauCeti.ClassFieldTheory.exists_sq_add_sq_iff_forall_adicCompletion`). If `-1` is a square in `K`
every element is a sum of two squares; otherwise this is the quadratic Hasse norm theorem for
`K(√-1) / K` (`TauCeti.ClassFieldTheory.exists_sq_sub_mul_sq_iff_forall_completion`), whose
conditions at the infinite places hold by total positivity.

The second result applies this over a finite extension `M / F` of number fields in which
`q p - B²` has a square root `m`, for `p, q, B ∈ F` with `p` totally positive. Suppose that at each
finite place `v` of `F`, `p` is a sum of two squares in `F_v`, or `q ≠ 0` is. Then `p` is a sum of
two squares in `M` (`TauCeti.ClassFieldTheory.exists_algebraMap_eq_sq_add_sq_of_sq_eq`). At a place
of `M` above a place of the second kind, `p = q⁻¹ (B² + m²)` is a quotient of sums of two squares.
Taking `M = F` when `q p - B²` is a square in `F`, and `M = F(√(q p - B²))` otherwise, gives
`p = a² + c² + (q p - B²) (b² + d²)` with `a b + c d = 0` for some `a, b, c, d ∈ F`
(`TauCeti.ClassFieldTheory.exists_sq_add_sq_add_mul_eq`).

That identity is the arithmetic input to Landherr's theorem for hermitian forms over a CM field
with maximal real subfield `F` and `i² = -1`: it writes `p` as the value
`conj α * α + μ * conj β * β` of the hermitian form `⟨1, μ⟩`, `μ = q p - B²`, at `α = a + c i` and
`β = i (b + d i)`, for which `conj β * α` lies in `F`.

## Main results

* `TauCeti.ClassFieldTheory.exists_sq_add_sq_iff_forall_adicCompletion`: the Hasse principle for
  sums of two squares.
* `TauCeti.ClassFieldTheory.exists_algebraMap_eq_sq_add_sq_of_sq_eq`: `p` is a sum of two squares
  in every extension containing a square root of `q p - B²`.
* `TauCeti.ClassFieldTheory.exists_sq_add_sq_add_mul_eq`: the same in coordinates over `F`.

## References

* W. Landherr, *Äquivalenz Hermitescher Formen über einem beliebigen algebraischen Zahlkörper*,
  Abh. Math. Sem. Univ. Hamburg 11 (1936), 245–248.
* J. Neukirch, *Algebraic Number Theory*, Chapter VI, §4 (the Hasse norm theorem).

## Provenance

The statements and the proof strategy follow `New.exists_norm_eq_of_forall_mem_closure` and
`New.exists_sq_add_sq_quadraticAlgebra` in grh-lean (https://github.com/lsernau/grh-lean, Apache
2.0, Copyright 2026 Anthropic, PBC), file `src/Lib/Adelic/Landherr.lean`. There the local
conditions are closures of the sums of two squares, the argument passes through finite adeles of
the CM field, and the extension `M` is a quadratic algebra; here the local conditions are stated in
the completions of `F` directly, and `M` is any finite extension.
-/

public section

open IsDedekindDomain NumberField NumberField.InfinitePlace

namespace TauCeti.ClassFieldTheory

section HassePrinciple

variable {K : Type*} [Field K] [NumberField K]

/-- **The Hasse principle for sums of two squares.** A totally positive element `x` of a number
field `K` is a sum of two squares in `K` exactly when it is a sum of two squares in the completion
`K_v` at every finite place `v`. -/
theorem exists_sq_add_sq_iff_forall_adicCompletion {x : K} (hx : IsTotallyPositive x) :
    (∃ a b : K, x = a ^ 2 + b ^ 2) ↔
      ∀ v : HeightOneSpectrum (𝓞 K), ∃ a b : v.adicCompletion K,
        algebraMap K (v.adicCompletion K) x = a ^ 2 + b ^ 2 := by
  refine ⟨fun ⟨a, b, h⟩ v ↦ ⟨algebraMap K _ a, algebraMap K _ b, by simp [h]⟩, fun h ↦ ?_⟩
  -- If `-1 = r²`, then `x = ((x + 1) / 2)² + (r (x - 1) / 2)²`.
  by_cases hsq : IsSquare (-1 : K)
  · obtain ⟨r, hr⟩ := hsq
    exact ⟨(x + 1) / 2, r * (x - 1) / 2, by linear_combination (x - 1) ^ 2 / 4 * hr⟩
  by_cases hx0 : x = 0
  · exact ⟨0, 0, by simp [hx0]⟩
  -- Otherwise apply the Hasse norm theorem for `K(√-1) / K`.
  have key := (exists_sq_sub_mul_sq_iff_forall_completion hsq (Units.mk0 x hx0)).2
  simp only [Units.val_mk0, map_neg, map_one, neg_mul, one_mul, sub_neg_eq_add] at key
  refine key ⟨h, fun w ↦ ?_⟩
  rcases w.isReal_or_isComplex with hw | hw
  · -- At a real place `x` is positive, hence a square.
    set e := Completion.ringEquivRealOfIsReal hw
    have hpos : 0 < e (algebraMap K w.Completion x) := by
      rw [Completion.ringEquivRealOfIsReal_apply, Completion.extensionEmbeddingOfIsReal_algebraMap]
      exact isTotallyPositive_iff.mp hx w hw
    refine ⟨e.symm (Real.sqrt (e (algebraMap K w.Completion x))), 0, e.injective ?_⟩
    simp [Real.sq_sqrt hpos.le]
  · -- At a complex place every element is a square.
    set e := Completion.ringEquivComplexOfIsComplex hw
    obtain ⟨z, hz⟩ := IsAlgClosed.exists_pow_nat_eq (e (algebraMap K w.Completion x)) two_pos
    exact ⟨e.symm z, 0, e.injective (by simp [hz])⟩

end HassePrinciple

section Extension

open scoped AdicCompletionExtension

variable {F : Type*} [Field F] [NumberField F]

/-- Let `p, q, B` be elements of a number field `F` with `p` totally positive, and `M` a finite
extension of `F` containing a square root `m` of `q p - B²`. If at every finite place `v` of `F`
either `p`, or `q ≠ 0`, is a sum of two squares in the completion `F_v`, then `p` is a sum of two
squares in `M`. -/
theorem exists_algebraMap_eq_sq_add_sq_of_sq_eq {M : Type*} [Field M] [NumberField M]
    [Algebra F M] {p q B : F} {m : M} (hm : m ^ 2 = algebraMap F M (q * p - B ^ 2))
    (hp : IsTotallyPositive p)
    (hloc : ∀ v : HeightOneSpectrum (𝓞 F),
      (∃ x y : v.adicCompletion F, algebraMap F (v.adicCompletion F) p = x ^ 2 + y ^ 2) ∨
        q ≠ 0 ∧ ∃ x y : v.adicCompletion F, algebraMap F (v.adicCompletion F) q = x ^ 2 + y ^ 2) :
    ∃ x y : M, algebraMap F M p = x ^ 2 + y ^ 2 := by
  refine (exists_sq_add_sq_iff_forall_adicCompletion (hp.map (algebraMap F M))).2 fun w ↦ ?_
  -- Compare the completion `M_w` with the completion `F_v` of `F` at the place `v` below `w`.
  set v := w.under (𝓞 F)
  set φ := HeightOneSpectrum.adicCompletionExtension F M v w
  set ι := algebraMap M (w.adicCompletion M)
  have hφ (t : F) : φ (algebraMap F (v.adicCompletion F) t) = ι (algebraMap F M t) := by
    simp only [φ, ι, HeightOneSpectrum.algebraMap_adicCompletion, Function.comp_apply,
      Algebra.algebraMap_self, RingHom.id_apply]
    exact HeightOneSpectrum.adicCompletionExtension_coe F M v w t
  rcases hloc v with ⟨x, y, h⟩ | ⟨hq, x, y, h⟩
  · exact ⟨φ x, φ y, by rw [← hφ, h, map_add, map_pow, map_pow]⟩
  · -- `q` and `q p = B² + m²` are sums of two squares in `M_w`, hence so is `q² p`.
    have hqx : ι (algebraMap F M q) = φ x ^ 2 + φ y ^ 2 := by
      rw [← hφ, h, map_add, map_pow, map_pow]
    have hqp : ι (algebraMap F M q) * ι (algebraMap F M p) =
        ι (algebraMap F M B) ^ 2 + ι m ^ 2 := by
      have : algebraMap F M q * algebraMap F M p = algebraMap F M B ^ 2 + m ^ 2 := by
        rw [hm, map_sub, map_mul, map_pow]
        ring
      simpa only [map_mul, map_add, map_pow] using congrArg ι this
    have hq0 : ι (algebraMap F M q) ≠ 0 := by simpa using hq
    refine ⟨(φ x * ι (algebraMap F M B) + φ y * ι m) / ι (algebraMap F M q),
      (φ x * ι m - φ y * ι (algebraMap F M B)) / ι (algebraMap F M q), ?_⟩
    field_simp
    linear_combination ι (algebraMap F M q) * hqp + (ι (algebraMap F M B) ^ 2 + ι m ^ 2) * hqx

/-- Let `p, q, B` be elements of a number field `F` with `p` totally positive. If at every finite
place `v` of `F` either `p`, or `q ≠ 0`, is a sum of two squares in the completion `F_v`, then
`p = a² + c² + (q p - B²) (b² + d²)` with `a b + c d = 0` for some `a, b, c, d ∈ F`. -/
theorem exists_sq_add_sq_add_mul_eq {p q B : F} (hp : IsTotallyPositive p)
    (hloc : ∀ v : HeightOneSpectrum (𝓞 F),
      (∃ x y : v.adicCompletion F, algebraMap F (v.adicCompletion F) p = x ^ 2 + y ^ 2) ∨
        q ≠ 0 ∧ ∃ x y : v.adicCompletion F, algebraMap F (v.adicCompletion F) q = x ^ 2 + y ^ 2) :
    ∃ a b c d : F, a ^ 2 + c ^ 2 + (q * p - B ^ 2) * (b ^ 2 + d ^ 2) = p ∧ a * b + c * d = 0 := by
  by_cases hμ : IsSquare (q * p - B ^ 2)
  · -- If `q p - B² = r²`, then `p` is a sum of two squares in `F` itself.
    obtain ⟨r, hr⟩ := hμ
    obtain ⟨x, y, hxy⟩ := exists_algebraMap_eq_sq_add_sq_of_sq_eq (M := F) (m := r)
      (by rw [Algebra.algebraMap_self_apply, hr, sq]) hp hloc
    exact ⟨x, 0, y, 0, by simpa using hxy.symm, by ring⟩
  · -- Otherwise write `p = (a + b ω)² + (c + d ω)²` in `F(ω)`, `ω² = q p - B²`.
    have : Fact (¬ IsSquare (q * p - B ^ 2)) := ⟨hμ⟩
    have : NumberField (QuadraticAlgebra F (q * p - B ^ 2) 0) := NumberField.of_module_finite F _
    obtain ⟨x, y, hxy⟩ := exists_algebraMap_eq_sq_add_sq_of_sq_eq (B := B)
      (m := (QuadraticAlgebra.omega : QuadraticAlgebra F (q * p - B ^ 2) 0))
      ((pow_two _).trans (QuadraticAlgebra.omega_mul_omega_eq_algebraMap.trans
        (by rw [map_zero, zero_mul, add_zero]))) hp hloc
    refine ⟨x.re, x.im, y.re, y.im, ?_, ?_⟩
    · have hre := congrArg QuadraticAlgebra.re hxy
      simp only [QuadraticAlgebra.algebraMap_eq, QuadraticAlgebra.re_C, sq, QuadraticAlgebra.re_add,
        QuadraticAlgebra.re_mul] at hre
      linear_combination -hre
    · have him := congrArg QuadraticAlgebra.im hxy
      simp only [QuadraticAlgebra.algebraMap_eq, QuadraticAlgebra.im_C, sq, QuadraticAlgebra.im_add,
        QuadraticAlgebra.im_mul] at him
      linear_combination -him / 2

end Extension

end TauCeti.ClassFieldTheory
