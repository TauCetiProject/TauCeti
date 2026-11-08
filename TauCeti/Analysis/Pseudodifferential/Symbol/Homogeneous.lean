/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Pseudodifferential.HomogeneousSymbol
public import TauCeti.Analysis.Pseudodifferential.Symbol.Basic
import TauCeti.Analysis.SpecialFunctions.Pow.Bounds

/-!
# The symbol of a cut-off homogeneous term

The terms `a_{m-j}` of a classical symbol `a ∼ ∑ⱼ χ(ξ) a_{m-j}(x, ξ)` are homogeneous symbols,
singular at `ξ = 0`; multiplying by a frequency cutoff `χ` turns each of them into a symbol of
its degree. For a homogeneous symbol `a` of degree `m` on `ℝⁿ`,
`TauCeti.HomogeneousSymbol.cutoffSymbol χ a` is the symbol `χ(ξ) a(x, ξ)` of order `m`, linear
in `a`. Its symbol estimates are those of the cut-off term
(`TauCeti.HomogeneousSymbol.exists_norm_iteratedFDeriv_smul_coefficient_le`), read on the
coordinate directions through `TauCeti.mixedDeriv_eq_iteratedFDeriv_append`.

The main results are:

* `TauCeti.HomogeneousSymbol.isSmoothing_cutoffSymbol_sub_cutoffSymbol`: changing the cutoff
  changes the cut-off term by a smoothing symbol;
* `TauCeti.HomogeneousSymbol.eq_zero_of_coefficient_eq_cutoffSymbol`: the cut-off term has no
  order below `m` unless `a = 0`, since homogeneity transports any extra decay at large
  frequencies to every frequency.

## References

* L. Hörmander, *The Analysis of Linear Partial Differential Operators III*, Section 18.1.
* M. E. Taylor, *Pseudodifferential Operators: Four Lectures at MSRI*, September 2008,
  Lecture I, (1.17).
-/

public section

noncomputable section

open Filter Topology

namespace TauCeti

variable {n : ℕ} {V W : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V] [NormedAddCommGroup W]
  [NormedSpace ℂ W] {m : ℝ}

namespace HomogeneousSymbol

/-- The cut-off term `χ(ξ) a(x, ξ)` of a homogeneous symbol of degree `m` satisfies the symbol
estimates of order `m`. -/
private theorem exists_bound_mixedDeriv_smul_coefficient
    (a : HomogeneousSymbol (CoordinateSpace n) (CoordinateSpace n) V W m)
    (χ : FrequencyCutoff (CoordinateSpace n)) {K : Set (CoordinateSpace n)} (hK : IsCompact K)
    (α β : List (Fin n)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x ∈ K, ∀ ξ,
      ‖mixedDeriv α β (fun p => χ p.2 • a.coefficient p) x ξ‖ ≤
        C * (1 + ‖ξ‖ ^ 2) ^ ((m - β.length) / 2) := by
  obtain ⟨C, hC, h⟩ := a.exists_norm_iteratedFDeriv_smul_coefficient_le χ hK α.length β.length
  refine ⟨C, hC, fun x hx ξ => ?_⟩
  rw [mixedDeriv_eq_iteratedFDeriv_append α β
    ((a.contDiff_smul_coefficient χ).of_le (mod_cast le_top))]
  simpa [PiLp.norm_single] using
    h x hx ξ (fun i => EuclideanSpace.single (α.get i) 1) fun i => EuclideanSpace.single (β.get i) 1

variable (χ χ' : FrequencyCutoff (CoordinateSpace n))

/-- The cut-off term `χ(ξ) a(x, ξ)` of a homogeneous symbol `a` of degree `m`, as a symbol of order
`m`. The cutoff removes the singularity of `a` at `ξ = 0` and leaves `a` unchanged at frequencies
of norm at least `2`. -/
def cutoffSymbol :
    HomogeneousSymbol (CoordinateSpace n) (CoordinateSpace n) V W m →ₗ[ℂ] Symbol n V W m where
  toFun a :=
    { coefficient p := χ p.2 • a.coefficient p
      contDiff_coefficient := a.contDiff_smul_coefficient χ
      exists_bound _ hK α β := exists_bound_mixedDeriv_smul_coefficient a χ hK α β }
  map_add' a b := Symbol.ext <| funext fun p => by simp [smul_add]
  map_smul' c a := Symbol.ext <| funext fun p => by simp [smul_comm (χ p.2) c]

@[simp]
theorem coefficient_cutoffSymbol
    (a : HomogeneousSymbol (CoordinateSpace n) (CoordinateSpace n) V W m)
    (p : CoordinateSpace n × CoordinateSpace n) :
    (cutoffSymbol χ a).coefficient p = χ p.2 • a.coefficient p :=
  (rfl)

/-- At frequencies of norm at least `2` the cut-off term is the homogeneous symbol itself. -/
theorem coefficient_cutoffSymbol_of_two_le_norm
    (a : HomogeneousSymbol (CoordinateSpace n) (CoordinateSpace n) V W m) {x ξ : CoordinateSpace n}
    (hξ : 2 ≤ ‖ξ‖) : (cutoffSymbol χ a).coefficient (x, ξ) = a.coefficient (x, ξ) := by
  simp [χ.apply_eq_one_of_two_le_norm hξ]

/-- **Independence of the cutoff.** Changing the frequency cutoff changes the cut-off term by a
smoothing symbol: the two cut-off terms agree at all frequencies of norm at least `2`. -/
theorem isSmoothing_cutoffSymbol_sub_cutoffSymbol
    (a : HomogeneousSymbol (CoordinateSpace n) (CoordinateSpace n) V W m) :
    (cutoffSymbol χ a - cutoffSymbol χ' a).IsSmoothing := by
  set d := cutoffSymbol χ a - cutoffSymbol χ' a
  have hR : ∀ x ξ, 2 ≤ ‖ξ‖ → d.coefficient (x, ξ) = 0 := fun x ξ hξ => by
    simp [d, χ.apply_eq_one_of_two_le_norm hξ, χ'.apply_eq_one_of_two_le_norm hξ]
  rw [← Symbol.ext (Symbol.coefficient_ofBoundedFrequencySupport (m := m) _
    d.contDiff_coefficient 2 hR)]
  exact Symbol.isSmoothing_ofBoundedFrequencySupport _ _ 2 hR

/-- A homogeneous symbol of degree `m` whose cut-off term is a symbol of some order `m' < m`
vanishes. -/
theorem eq_zero_of_coefficient_eq_cutoffSymbol {m' : ℝ} (hm : m' < m)
    {a : HomogeneousSymbol (CoordinateSpace n) (CoordinateSpace n) V W m} (b : Symbol n V W m')
    (hb : b.coefficient = (cutoffSymbol χ a).coefficient) : a = 0 := by
  refine ext_of_ne_zero fun x ξ hξ => ?_
  rw [coefficient_zero, Pi.zero_apply, ← norm_le_zero_iff]
  have hξ0 : 0 < ‖ξ‖ := norm_pos_iff.2 hξ
  obtain ⟨C, hC, hbC⟩ := b.exists_bound {x} isCompact_singleton [] []
  set D := C * 2 ^ (|m'| / 2) * ‖ξ‖ ^ m'
  -- For `t ≥ 2 / ‖ξ‖`, homogeneity at `t • ξ` and the bound of order `m'` there give
  -- `t ^ m ‖a (x, ξ)‖ ≤ D t ^ m'`.
  have key : ∀ᶠ t in atTop, ‖a.coefficient (x, ξ)‖ ≤ D * t ^ (m' - m) := by
    filter_upwards [eventually_ge_atTop (2 / ‖ξ‖), eventually_gt_atTop 0] with t ht ht0
    have htξ : 2 ≤ ‖t • ξ‖ := by
      rwa [norm_smul, Real.norm_of_nonneg ht0.le, ← div_le_iff₀ hξ0]
    have h := hbC x rfl (t • ξ)
    have hw := one_add_norm_sq_rpow_le_norm_rpow (by linarith : 1 ≤ ‖t • ξ‖) m'
    rw [mixedDeriv_nil_nil, hb, coefficient_cutoffSymbol_of_two_le_norm χ a htξ,
      a.norm_homogeneous x ξ ht0] at h
    simp only [List.length_nil, Nat.cast_zero, sub_zero, norm_smul, Real.norm_of_nonneg ht0.le,
      Real.mul_rpow ht0.le hξ0.le] at h hw
    refine le_of_mul_le_mul_left ?_ (Real.rpow_pos_of_pos ht0 m)
    calc t ^ m * ‖a.coefficient (x, ξ)‖
        ≤ C * (2 ^ (|m'| / 2) * (t ^ m' * ‖ξ‖ ^ m')) := h.trans (mul_le_mul_of_nonneg_left hw hC)
      _ = t ^ m * (D * t ^ (m' - m)) := by
          rw [Real.rpow_sub ht0]
          field_simp
          ring
  have hlim : Tendsto (fun t : ℝ => D * t ^ (m' - m)) atTop (𝓝 0) := by
    simpa [neg_sub] using (tendsto_rpow_neg_atTop (by linarith : 0 < m - m')).const_mul D
  exact ge_of_tendsto hlim key

end HomogeneousSymbol

end TauCeti
