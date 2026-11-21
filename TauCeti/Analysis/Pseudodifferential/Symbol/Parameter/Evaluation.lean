/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Pseudodifferential.Symbol.Parameter.Basic
public import TauCeti.Analysis.Pseudodifferential.Symbol.Topology
import TauCeti.Analysis.Calculus.IteratedFDeriv.Prod

/-!
# Parameter-dependent symbols at a fixed spectral parameter

A strongly parameter-dependent symbol `a((x, ξ), z)` of order `m` (`TauCeti.ParameterSymbol`)
is, at each fixed spectral parameter `z`, an ordinary symbol `x, ξ ↦ a((x, ξ), z)` of order `m`
(`TauCeti.ParameterSymbol.toSymbol`). This is how the parameter-dependent calculus is quantized:
`Op(a(z))` is the quantization of this ordinary symbol.

The point of the parameter-dependent class is the dependence of these symbols on `z`. On each
compact set of positions, every spatial and frequency derivative of `a` is bounded by
`C (1 + ‖ξ‖ + ‖z‖ ^ (1 / 2)) ^ (m - |β|)`, with `C` depending on the compact set, uniformly in
`z ∈ Λ` (`TauCeti.ParameterSymbol.exists_norm_mixedDeriv_coefficient_le`), and the weight is at
least both `⟨ξ⟩ = (1 + ‖ξ‖²) ^ (1 / 2)` and `1 + ‖z‖ ^ (1 / 2)`. So for `m ≤ m' ≤ 0` a symbol of
order `m` trades `m' - m` frequency orders for decay in the spectral parameter: as a symbol of
order `m'`, `a(z)` has seminorms

`p_{K,α,β}(a(z)) ≤ C (1 + ‖z‖ ^ (1 / 2)) ^ (m - m')`

uniformly on `Λ` (`TauCeti.ParameterSymbol.exists_seminorm_inclusion_toSymbol_le`). For instance
the seminorms of order `0` of a remainder of order `-N` in a resolvent parametrix decay like
`‖z‖ ^ (-N / 2)`. The corresponding bound of the operators on Sobolev spaces, for symbols vanishing
outside a fixed compact set of positions, is
`TauCeti.ParameterSymbol.exists_norm_quantizeSobolev_inclusion_toSymbol_le`. At fixed `z` the
frequency estimates of order `m` hold with a constant that depends on `z`, since then the weight is
at most a multiple of `⟨ξ⟩`.

## Main declarations

* `TauCeti.ParameterSymbol.exists_norm_mixedDeriv_coefficient_le`: the estimates of the mixed
  derivatives `∂ₓ^α ∂_ξ^β a((x, ξ), z)` at a fixed spectral parameter on a compact set of
  positions, uniformly on `Λ`.
* `TauCeti.ParameterSymbol.toSymbol`: the ordinary symbol of order `m` at a spectral parameter;
  it is linear in the symbol and commutes with the order inclusions and the composition.
* `TauCeti.ParameterSymbol.exists_seminorm_inclusion_toSymbol_le`: the decay of its seminorms of
  order `m' ∈ [m, 0]` in the spectral parameter.

## References

* M. A. Shubin, *Pseudodifferential Operators and Spectral Theory*, Chapter II, §9.
-/

public section

noncomputable section

open Set
open scoped ContDiff

namespace TauCeti

variable {n : ℕ}

namespace ParameterSymbol

variable {Λ : TopologicalSpace.Opens ℂ} {V W U : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]
  [NormedAddCommGroup W] [NormedSpace ℂ W] [NormedAddCommGroup U] [NormedSpace ℂ U] {m m' : ℝ}

/-! ### Slices at a fixed spectral parameter -/

/-- At a spectral parameter outside `Λ` the coefficient vanishes in the position and the
frequency. -/
theorem coefficient_slice_of_notMem (a : ParameterSymbol n Λ V W m) {z : ℂ} (hz : z ∉ Λ) :
    (fun q : CoordinateSpace n × CoordinateSpace n => a.coefficient (q, z)) = 0 :=
  funext fun q => a.coefficient_of_notMem (q, z) hz

/-- At a fixed spectral parameter the coefficient is smooth in the position and the frequency. -/
theorem contDiff_coefficient_slice (a : ParameterSymbol n Λ V W m) (z : ℂ) :
    ContDiff ℝ ∞ fun q : CoordinateSpace n × CoordinateSpace n => a.coefficient (q, z) := by
  by_cases hz : z ∈ Λ
  · exact contDiff_iff_contDiffAt.2 fun q =>
      (a.contDiffAt_coefficient (p := (q, z)) hz).comp q (contDiff_prodMk_left z).contDiffAt
  · rw [a.coefficient_slice_of_notMem hz]
    exact contDiff_const

/-- In terms of the dilated derivatives defining the class, a mixed derivative `∂ₓ^α ∂_ξ^β` of
the coefficient takes `|β|` frequency directions, each the image under the dilation by the weight
`t` of a vector of norm `t⁻¹`. -/
private theorem norm_mixedDeriv_coefficient_le_aux (a : ParameterSymbol n Λ V W m)
    (α β : List (Fin n)) {x ξ : CoordinateSpace n} {z : ℂ} (hz : z ∈ Λ) :
    ‖mixedDeriv α β (fun q => a.coefficient (q, z)) x ξ‖ ≤
      ‖parameterIteratedFDeriv (α.length + β.length) a.coefficient ((x, ξ), z)‖ *
        (parameterWeight ξ z)⁻¹ ^ β.length := by
  set t := parameterWeight ξ z
  have ht : 0 < t := parameterWeight_pos ξ z
  -- The directions of the mixed derivative, and their preimages under the dilation.
  set d : Fin (α.length + β.length) → CoordinateSpace n × CoordinateSpace n :=
    Fin.append (fun i => (EuclideanSpace.single (α.get i) 1, 0))
      fun i => (0, EuclideanSpace.single (β.get i) 1)
  have hd : ∀ i, parameterDilation n t (((d i).1, t⁻¹ • (d i).2), 0) = ((d i), 0) := fun i => by
    simp [smul_smul, mul_inv_cancel₀ ht.ne']
  rw [mixedDeriv_eq_iteratedFDeriv_append α β
      ((a.contDiff_coefficient_slice z).of_le (by exact_mod_cast le_top)),
    (a.contDiffAt_coefficient (p := ((x, ξ), z)) hz).iteratedFDeriv_prod_left _
      (by exact_mod_cast le_top), ContinuousMultilinearMap.compContinuousLinearMap_apply]
  have heq : (iteratedFDeriv ℝ (α.length + β.length) a.coefficient ((x, ξ), z))
      (fun i => ContinuousLinearMap.inl ℝ _ ℂ (d i)) =
      parameterIteratedFDeriv (α.length + β.length) a.coefficient ((x, ξ), z)
        (fun i => (((d i).1, t⁻¹ • (d i).2), 0)) := by
    rw [parameterIteratedFDeriv_apply]
    simp only [hd, ContinuousLinearMap.inl_apply, t]
  rw [heq]
  refine (ContinuousMultilinearMap.le_opNorm _ _).trans_eq ?_
  congr 1
  -- A spatial direction has norm `1`, a rescaled frequency direction norm `t⁻¹`.
  simp [d, Fin.prod_univ_add, Prod.norm_def, norm_smul, abs_of_pos ht, ht.le]

/-- **Estimates at a fixed spectral parameter.** On a compact set of positions, the mixed
derivatives of a parameter-dependent symbol of order `m` in the position and the frequency satisfy
`‖∂ₓ^α ∂_ξ^β a((x, ξ), z)‖ ≤ C (1 + ‖ξ‖ + ‖z‖ ^ (1 / 2)) ^ (m - |β|)`, uniformly in the spectral
parameter `z ∈ Λ`. -/
theorem exists_norm_mixedDeriv_coefficient_le (a : ParameterSymbol n Λ V W m)
    {K : Set (CoordinateSpace n)} (hK : IsCompact K) (α β : List (Fin n)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x ∈ K, ∀ ξ, ∀ z ∈ Λ,
      ‖mixedDeriv α β (fun q => a.coefficient (q, z)) x ξ‖ ≤
        C * parameterWeight ξ z ^ (m - β.length) := by
  obtain ⟨C, hC, h⟩ := a.exists_bound K hK (α.length + β.length)
  refine ⟨C, hC, fun x hx ξ z hz => (a.norm_mixedDeriv_coefficient_le_aux α β hz).trans ?_⟩
  have ht := parameterWeight_pos ξ z
  calc _ ≤ C * parameterWeight ξ z ^ m * (parameterWeight ξ z)⁻¹ ^ β.length :=
        mul_le_mul_of_nonneg_right (h x hx ξ z hz) (by positivity)
    _ = C * parameterWeight ξ z ^ (m - β.length) := by
        rw [Real.rpow_sub ht, Real.rpow_natCast, inv_pow, div_eq_mul_inv, mul_assoc]

/-- **The symbol at a spectral parameter.** At a fixed spectral parameter `z`, a
parameter-dependent symbol of order `m` is the ordinary symbol `(x, ξ) ↦ a((x, ξ), z)` of order
`m`, its quantization being the operator `Op(a(z))` of the family. The constants of its estimates
depend on `z`; for `z ∉ Λ` it is `0`. -/
def toSymbol (a : ParameterSymbol n Λ V W m) (z : ℂ) : Symbol n V W m where
  coefficient q := a.coefficient (q, z)
  contDiff_coefficient := a.contDiff_coefficient_slice z
  exists_bound K hK α β := by
    by_cases hz : z ∈ Λ
    · obtain ⟨C, hC, h⟩ := a.exists_norm_mixedDeriv_coefficient_le hK α β
      refine ⟨C * (3 * (1 + ‖z‖)) ^ (|m - β.length| / 2), by positivity, fun x hx ξ => ?_⟩
      rw [mul_assoc]
      exact (h x hx ξ z hz).trans
        (mul_le_mul_of_nonneg_left (parameterWeight_rpow_le_mul_one_add_norm_sq_rpow ξ z _) hC)
    · refine ⟨0, le_rfl, fun x _ ξ => ?_⟩
      rw [a.coefficient_slice_of_notMem hz, mixedDeriv_zero, norm_zero, zero_mul]

@[simp]
theorem coefficient_toSymbol (a : ParameterSymbol n Λ V W m) (z : ℂ)
    (q : CoordinateSpace n × CoordinateSpace n) :
    (a.toSymbol z).coefficient q = a.coefficient (q, z) :=
  (rfl)

/-- Outside `Λ` the symbol at a spectral parameter is `0`. -/
theorem toSymbol_of_notMem (a : ParameterSymbol n Λ V W m) {z : ℂ} (hz : z ∉ Λ) :
    a.toSymbol z = 0 :=
  Symbol.ext (a.coefficient_slice_of_notMem hz)

@[simp]
theorem toSymbol_zero (z : ℂ) : (0 : ParameterSymbol n Λ V W m).toSymbol z = 0 :=
  (rfl)

@[simp]
theorem toSymbol_add (a b : ParameterSymbol n Λ V W m) (z : ℂ) :
    (a + b).toSymbol z = a.toSymbol z + b.toSymbol z :=
  (rfl)

@[simp]
theorem toSymbol_smul (c : ℂ) (a : ParameterSymbol n Λ V W m) (z : ℂ) :
    (c • a).toSymbol z = c • a.toSymbol z :=
  (rfl)

@[simp]
theorem toSymbol_neg (a : ParameterSymbol n Λ V W m) (z : ℂ) : (-a).toSymbol z = -a.toSymbol z :=
  Symbol.ext <| funext fun q => by simp

@[simp]
theorem toSymbol_sub (a b : ParameterSymbol n Λ V W m) (z : ℂ) :
    (a - b).toSymbol z = a.toSymbol z - b.toSymbol z :=
  Symbol.ext <| funext fun q => by simp

@[simp]
theorem toSymbol_nsmul (k : ℕ) (a : ParameterSymbol n Λ V W m) (z : ℂ) :
    (k • a).toSymbol z = k • a.toSymbol z :=
  Symbol.ext <| funext fun q => by simp

@[simp]
theorem toSymbol_zsmul (k : ℤ) (a : ParameterSymbol n Λ V W m) (z : ℂ) :
    (k • a).toSymbol z = k • a.toSymbol z :=
  Symbol.ext <| funext fun q => by simp

@[simp]
theorem toSymbol_sum {ι : Type*} (s : Finset ι) (a : ι → ParameterSymbol n Λ V W m) (z : ℂ) :
    (∑ i ∈ s, a i).toSymbol z = ∑ i ∈ s, (a i).toSymbol z :=
  map_sum (AddMonoidHom.mk' (toSymbol · z) (toSymbol_add · · z)) a s

/-- Evaluation at a spectral parameter commutes with the inclusion of orders. -/
@[simp]
theorem toSymbol_inclusion (h : m ≤ m') (a : ParameterSymbol n Λ V W m) (z : ℂ) :
    (inclusion h a).toSymbol z = Symbol.inclusion h (a.toSymbol z) :=
  Symbol.ext <| funext fun q => by simp

/-- Evaluation at a spectral parameter commutes with the pointwise composition. -/
@[simp]
theorem toSymbol_comp (b : ParameterSymbol n Λ W U m') (a : ParameterSymbol n Λ V W m) (z : ℂ) :
    (b.comp a).toSymbol z = (b.toSymbol z).comp (a.toSymbol z) :=
  Symbol.ext <| funext fun q => by simp

/-- If a parameter-dependent symbol vanishes, at a spectral parameter `z`, at the positions outside
a compact set `K` for every frequency, then its symbol at `z` has compact spatial support. -/
theorem hasCompactSpatialSupport_toSymbol (a : ParameterSymbol n Λ V W m) (z : ℂ)
    {K : Set (CoordinateSpace n)} (hK : IsCompact K)
    (ha : ∀ x ∉ K, ∀ ξ, a.coefficient ((x, ξ), z) = 0) :
    (a.toSymbol z).HasCompactSpatialSupport :=
  Symbol.hasCompactSpatialSupport_iff.2 ⟨K, hK, ha⟩

/-- **Decay in the spectral parameter.** For orders `m ≤ m' ≤ 0`, a parameter-dependent symbol of
order `m`, viewed at each spectral parameter as an ordinary symbol of order `m'`, has seminorms
`p_{K,α,β}(a(z)) ≤ C (1 + ‖z‖ ^ (1 / 2)) ^ (m - m')`, uniformly in `z ∈ Λ`. -/
theorem exists_seminorm_inclusion_toSymbol_le (a : ParameterSymbol n Λ V W m) (h : m ≤ m')
    (h' : m' ≤ 0) (K : TopologicalSpace.Compacts (CoordinateSpace n)) (α β : List (Fin n)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ z ∈ Λ,
      Symbol.seminorm K α β (Symbol.inclusion h (a.toSymbol z)) ≤
        C * (1 + Real.sqrt ‖z‖) ^ (m - m') := by
  obtain ⟨C, hC, hb⟩ := a.exists_norm_mixedDeriv_coefficient_le K.isCompact α β
  refine ⟨C, hC, fun z hz => Symbol.seminorm_le_bound K α β _ (by positivity) fun x hx ξ => ?_⟩
  have ht := parameterWeight_pos ξ z
  have hβ : m' - β.length ≤ 0 := by linarith [(Nat.cast_nonneg β.length : (0 : ℝ) ≤ _)]
  rw [Symbol.coefficient_inclusion]
  calc _ ≤ C * parameterWeight ξ z ^ (m - β.length) := hb x hx ξ z hz
    _ = C * (parameterWeight ξ z ^ (m' - β.length) * parameterWeight ξ z ^ (m - m')) := by
        rw [← Real.rpow_add ht]
        ring_nf
    _ ≤ C * ((1 + ‖ξ‖ ^ 2) ^ ((m' - β.length) / 2) * (1 + Real.sqrt ‖z‖) ^ (m - m')) := by
        exact mul_le_mul_of_nonneg_left
          (mul_le_mul (parameterWeight_rpow_le_one_add_norm_sq_rpow ξ z hβ)
            (parameterWeight_rpow_le_one_add_sqrt_rpow ξ z (by linarith)) (by positivity)
            (by positivity)) hC
    _ = _ := by ring

end ParameterSymbol

end TauCeti
