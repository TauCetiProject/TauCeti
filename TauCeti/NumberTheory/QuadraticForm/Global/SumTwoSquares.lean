/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.QuadraticAlgebra.Basic
public import Mathlib.RingTheory.DedekindDomain.AdicValuation.Completion
public import TauCeti.NumberTheory.NumberField.TotallyPositive
import TauCeti.NumberTheory.QuadraticForm.Global.HilbertSymbol
import TauCeti.NumberTheory.QuadraticForm.Global.NormForm
import TauCeti.RingTheory.DedekindDomain.AdicCompletionExtension
import TauCeti.RingTheory.DedekindDomain.PrimesAbove

/-!
# Sums of two squares over number fields

An element `x` of a number field `K` is a sum of two squares in `K` exactly when it is a sum of two
squares in every completion `K_v` at a finite place and is nonnegative at every real place
(`TauCeti.exists_sq_add_sq_iff_forall_places`). This is the local-to-global principle for the
norm plane `⟨1, 1⟩`.

At a finite place not above `2`, every element of `K_v` of valuation `1` is a sum of two squares in
`K_v` (`TauCeti.exists_sq_add_sq_of_valued_eq_one`). At a place above `2` this can fail (`3` is not
a sum of two squares in `ℚ₂`), but it holds when `-1` is a square in `K_v`. This gives a criterion
over an extension `M` of a number field `F`. Suppose that `p ∈ F` is totally positive, that `-1`
is a square in `F_v` at every place `v` of `F` above `2`, and that at every finite place of `F`
either `p` or `q` has valuation `1`. If `q p` is a sum of two squares in `M`, then so is `p`
(`NumberField.IsTotallyPositive.exists_sq_add_sq_algebraMap`). Locally at a place `w` of `M` above
`v`, either `p` itself is a sum of two squares in `F_v`, or `q⁻¹` is and `p = q⁻¹ · (q p)`.

Taking for `M` the quadratic algebra `F[X] / (X² - (q p - B²))`, in which `q p = B² + X²`, gives
`NumberField.IsTotallyPositive.exists_sq_add_sq_quadraticAlgebra`: `p` is a sum of two squares in
`F[X] / (X² - (q p - B²))` for every `B ∈ F`. This algebra is a number field when `q p - B²` is not
a square in `F`; otherwise `q p` is already a sum of two squares in `F`. For the maximal real
subfield `F` of a CM field `E` containing a primitive fourth and a primitive seventh root of unity,
the condition at `2` holds
(`NumberField.IsCMField.isSquare_neg_one_adicCompletion_of_isPrimitiveRoot`), and a sum of two
squares in an extension of `F` is a norm from the corresponding extension of `E`.
This is the global input of the Hasse principle for the representation of `1` by a hermitian form
over `E`, which is proved one column at a time.

## Main results

* `TauCeti.exists_sq_add_sq_iff_forall_places`: the local-to-global principle for sums of two
  squares in a number field.
* `TauCeti.exists_sq_add_sq_of_valued_eq_one`: at a place not above `2`, the elements of
  valuation `1` of the completion are sums of two squares.
* `NumberField.IsTotallyPositive.exists_sq_add_sq_algebraMap`: a totally positive `p ∈ F` is a sum
  of two squares in an extension `M` in which `q p` is one, under the conditions above.
* `NumberField.IsTotallyPositive.exists_sq_add_sq_quadraticAlgebra`: the same in the quadratic
  algebra `F[X] / (X² - (q p - B²))`.

## References

* O. T. O'Meara, *Introduction to Quadratic Forms*, Springer (1963), 65:23 and 66:1 (the
  Hasse–Minkowski theorem for representations).
* W. Landherr, *Äquivalenz Hermitescher Formen über einem beliebigen algebraischen Zahlkörper*,
  Abh. Math. Sem. Hamburg 11 (1936), 245–248.
* `grh-lean`, https://github.com/lsernau/grh-lean, file `src/Lib/Adelic/Landherr.lean`
  (declarations `New.exists_norm_eq_of_forall_mem_closure` and
  `New.exists_sq_add_sq_quadraticAlgebra`); Apache 2.0, Copyright 2026 Anthropic, PBC. The
  reduction of the quadratic algebra to an extension field containing a square root of
  `q p - B²`, and the local splitting `p = q⁻¹ · (B² + m²)`, follow those declarations; the local
  argument here goes through the Hilbert symbol at places not above `2` instead of norms from the
  adeles.
-/

public section

open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum NumberField

namespace TauCeti

variable {K : Type*} [Field K] [NumberField K]

/-- **The local-to-global principle for sums of two squares.** An element `x` of a number field
`K` is a sum of two squares in `K` exactly when it is a sum of two squares in the completion `K_v`
at every finite place `v` and is nonnegative at every real place. -/
theorem exists_sq_add_sq_iff_forall_places (x : K) :
    (∃ a b : K, a ^ 2 + b ^ 2 = x) ↔
      (∀ v : HeightOneSpectrum (𝓞 K), ∃ a b : v.adicCompletion K,
        a ^ 2 + b ^ 2 = algebraMap K (v.adicCompletion K) x) ∧
      ∀ (w : InfinitePlace K) (hw : w.IsReal), 0 ≤ InfinitePlace.embedding_of_isReal hw x := by
  constructor
  · rintro ⟨a, b, rfl⟩
    refine ⟨fun v ↦ ⟨algebraMap K _ a, algebraMap K _ b, by simp⟩, fun w hw ↦ ?_⟩
    simpa using add_nonneg (sq_nonneg (InfinitePlace.embedding_of_isReal hw a))
      (sq_nonneg (InfinitePlace.embedding_of_isReal hw b))
  · rintro ⟨hfin, hreal⟩
    -- `x` is represented by `⟨1, -(-1)⟩ = ⟨1, 1⟩` at every place, hence over `K`.
    have hloc : QuadraticForm.LocallyRepresentsScalar
        (QuadraticMap.weightedSumSquares K ![1, -(-1 : K)]) x := by
      refine (QuadraticForm.locallyRepresentsScalar_iff _ _).2 ⟨fun v ↦ ?_, fun w ↦ ?_⟩
      · obtain ⟨a, b, hab⟩ := hfin v
        refine (QuadraticForm.represents_atFinitePlace_weightedSumSquares_one_neg_iff v _ x).2
          ⟨a, b, ?_⟩
        rw [← hab, map_neg, map_one]
        ring
      · refine (QuadraticForm.represents_atRealPlace_weightedSumSquares_one_neg_iff w _ x).2
          ⟨√(InfinitePlace.embedding_of_isReal w.property x), 0, ?_⟩
        rw [Real.sq_sqrt (hreal w.val w.property)]
        ring
    obtain ⟨a, b, hab⟩ := (represents_binary_one_neg_iff (-1 : K) x).1
      ((QuadraticForm.represents_weightedSumSquares_one_neg_iff_locallyRepresentsScalar x).2 hloc)
    exact ⟨a, b, by rw [hab]; ring⟩

/-- **Local units are sums of two squares away from `2`.** At a finite place `v` of a number field
`K` not above `2`, every element of valuation `1` of the completion `K_v` is a sum of two squares
in `K_v`. -/
theorem exists_sq_add_sq_of_valued_eq_one {v : HeightOneSpectrum (𝓞 K)}
    (h2 : v.valuation K 2 = 1) {u : v.adicCompletion K} (hu : Valued.v u = 1) :
    ∃ a b : v.adicCompletion K, a ^ 2 + b ^ 2 = u := by
  have hu0 : u ≠ 0 := by
    rintro rfl
    simp at hu
  -- The Hilbert symbol `(-1, u)` of two local units is `1`, so `u = a² - (-1) b²`.
  have hsymb := hilbertSymbol_eq_one_of_valued_eq_one h2 (u := -1) (u' := Units.mk0 u hu0)
    (by simp) hu
  obtain ⟨a, b, hab⟩ := (hilbertSymbol_eq_one_iff _ _).1 hsymb
  exact ⟨a, b, by rw [Units.val_mk0] at hab; rw [hab]; simp⟩

end TauCeti

namespace NumberField.IsTotallyPositive

open scoped AdicCompletionExtension

variable {F : Type*} [Field F] [NumberField F]

/-- **Totally positive elements as sums of two squares in an extension.** Let `F` be a number field
in which `-1` is a square in the completion at every finite place above `2`, let `p ∈ F` be totally
positive and let `q ∈ F` be such that at every finite place `v` of `F` one of `p` and `q` has
valuation `1`. If `q p` is a sum of two squares in a number field `M` containing `F`, so is `p`. -/
theorem exists_sq_add_sq_algebraMap {M : Type*} [Field M] [NumberField M] [Algebra F M] {p : F}
    (hp : IsTotallyPositive p)
    (h2 : ∀ v : HeightOneSpectrum (𝓞 F), v.valuation F 2 ≠ 1 → IsSquare (-1 : v.adicCompletion F))
    {q : F} (hpq : ∀ v : HeightOneSpectrum (𝓞 F), v.valuation F p = 1 ∨ v.valuation F q = 1)
    (hqp : ∃ c d : M, c ^ 2 + d ^ 2 = algebraMap F M (q * p)) :
    ∃ a b : M, a ^ 2 + b ^ 2 = algebraMap F M p := by
  obtain ⟨c, d, hcd⟩ := hqp
  refine (TauCeti.exists_sq_add_sq_iff_forall_places _).2
    ⟨fun w ↦ ?_, fun w hw ↦ (isTotallyPositive_iff.1 (hp.map (algebraMap F M)) w hw).le⟩
  -- Work at the place `v` of `F` below `w`, through the extension `φ : F_v → M_w`.
  set v := under (𝓞 F) w
  set φ := adicCompletionExtension F M v w
  have hφ (t : F) : φ (algebraMap F (v.adicCompletion F) t) =
      algebraMap M (w.adicCompletion M) (algebraMap F M t) :=
    adicCompletionExtension_coe F M v w t
  -- Every element of `F` of valuation `1` at `v` is a sum of two squares in `F_v`.
  have hloc (t : F) (ht : v.valuation F t = 1) :
      ∃ a b : v.adicCompletion F, a ^ 2 + b ^ 2 = algebraMap F (v.adicCompletion F) t := by
    by_cases hv2 : v.valuation F 2 = 1
    · exact TauCeti.exists_sq_add_sq_of_valued_eq_one hv2
        (by rwa [← valuedAdicCompletion_eq_valuation'] at ht)
    · -- With `i² = -1`, `t = ((t + 1) / 2)² + (i (t - 1) / 2)²`.
      obtain ⟨i, hi⟩ := h2 v hv2
      refine ⟨(algebraMap F _ t + 1) / 2, i * (algebraMap F _ t - 1) / 2, ?_⟩
      linear_combination (-(algebraMap F (v.adicCompletion F) t - 1) ^ 2 / 4) * hi
  rcases hpq v with hpv | hqv
  · obtain ⟨a, b, hab⟩ := hloc p hpv
    exact ⟨φ a, φ b, by rw [← map_pow, ← map_pow, ← map_add, hab, hφ]⟩
  · -- Here `p = q⁻¹ · (c² + d²)` with `q⁻¹` a sum of two squares in `F_v`.
    have hq0 : q ≠ 0 := by
      rintro rfl
      simp at hqv
    obtain ⟨a, b, hab⟩ := hloc q⁻¹ (by rw [map_inv₀, hqv, inv_one])
    have hp_eq : algebraMap F M p = algebraMap F M q⁻¹ * (c ^ 2 + d ^ 2) := by
      rw [hcd, ← map_mul, inv_mul_cancel_left₀ hq0]
    refine ⟨φ a * algebraMap M _ c - φ b * algebraMap M _ d,
      φ a * algebraMap M _ d + φ b * algebraMap M _ c, ?_⟩
    rw [hp_eq, map_mul, ← hφ, ← hab]
    simp only [map_add, map_pow]
    ring

/-- **Totally positive elements as sums of two squares in a quadratic algebra.** Let `F` be a
number field in which `-1` is a square in the completion at every finite place above `2`, let
`p ∈ F` be totally positive and let `q ∈ F` be such that at every finite place of `F` one of `p`
and `q` has valuation `1`. Then for every `B ∈ F`, `p` is a sum of two squares in the quadratic
algebra `F[X] / (X² - (q p - B²))`. -/
theorem exists_sq_add_sq_quadraticAlgebra {p : F} (hp : IsTotallyPositive p)
    (h2 : ∀ v : HeightOneSpectrum (𝓞 F), v.valuation F 2 ≠ 1 → IsSquare (-1 : v.adicCompletion F))
    {q : F} (hpq : ∀ v : HeightOneSpectrum (𝓞 F), v.valuation F p = 1 ∨ v.valuation F q = 1)
    (B : F) :
    ∃ x y : QuadraticAlgebra F (q * p - B ^ 2) 0,
      x ^ 2 + y ^ 2 = algebraMap F (QuadraticAlgebra F (q * p - B ^ 2) 0) p := by
  by_cases hμ : IsSquare (q * p - B ^ 2)
  · -- If `q p - B² = r²`, then `q p = B² + r²` in `F` itself.
    obtain ⟨r, hr⟩ := hμ
    obtain ⟨a, b, hab⟩ := hp.exists_sq_add_sq_algebraMap (M := F) h2 hpq
      ⟨B, r, by rw [Algebra.algebraMap_self, RingHom.id_apply]; linear_combination -hr⟩
    refine ⟨algebraMap F _ a, algebraMap F _ b, ?_⟩
    rw [Algebra.algebraMap_self, RingHom.id_apply] at hab
    rw [← map_pow, ← map_pow, ← map_add, hab]
  · -- Otherwise the algebra is a number field, in which `q p = B² + X²`.
    have : Fact (¬IsSquare (q * p - B ^ 2)) := ⟨hμ⟩
    have : NumberField (QuadraticAlgebra F (q * p - B ^ 2) 0) := .of_module_finite F _
    refine hp.exists_sq_add_sq_algebraMap h2 hpq ⟨algebraMap F _ B, QuadraticAlgebra.omega, ?_⟩
    rw [sq QuadraticAlgebra.omega, QuadraticAlgebra.omega_mul_omega_eq_algebraMap, map_zero,
      zero_mul, add_zero, ← map_pow, ← map_add]
    congr 1
    ring

end NumberField.IsTotallyPositive
