/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.SeibergWitten.NormalModel.Basic
public import TauCeti.Analysis.PDE.Vortex.Kernel.Coercivity
public import TauCeti.Analysis.PDE.Vortex.Kernel.Tangent
import TauCeti.Analysis.PDE.Vortex.Gauge.ComplexStructure
import TauCeti.Analysis.PDE.Vortex.SpectralGap
import TauCeti.MeasureTheory.Function.LocallyIntegrable

/-!
# The frozen normal model at a base frequency

Near a pseudoholomorphic curve, Taubes's rescaled large-parameter Seiberg–Witten solutions are
modelled on `ℂ_base × ℂ_normal` by a plane vortex `x` in the normal factor, and the linearized
equations at such a frozen model act on a normal family `Ξ` and a paired family `Η` of plane fields
over the base through the two rows (`TauCeti.Analysis.PDE.SeibergWitten.NormalModel.Basic`)

`N = L_x Ξ (w, ·) + normalBaseCoupling (D_w Η)`,  `P = L_x* Η (w, ·) + pairedBaseCoupling (D_w Ξ)`.

The coefficients do not depend on the base point `w`, so the model is diagonalized by the
frequencies `ξ ∈ ℂ` along the base. This file studies the operator at a single base frequency: the
principal family of the frozen model, which Taubes's analysis evaluates at `ξ = η / h` for the
rescaled frequency `η` and the length scale `h`.

**The family at frequency `ξ`.** Write `b_N(ξ) v = Re ξ • v - Im ξ • J' v` and
`b_P(ξ) u = Re ξ • u + Im ξ • J u` for the base couplings of the rank-one derivative
`w ↦ ⟪ξ, w⟫ v` (`normalBaseCoupling_smulRight_innerSL`, `pairedBaseCoupling_smulRight_innerSL`),
where `J`, `J'` are the complex structures on variations and on the target of `L_x`. In the
complex structure `J`, `b_P(ξ)` is multiplication by `ξ`. Both couplings multiply norms by `|ξ|`
(`norm_normalBaseCoupling_smulRight_innerSL`), and their transposes are the couplings at
`conj ξ` (`inner_normalBaseCoupling_smulRight_innerSL_left`). The family at frequency `ξ` sends
a pair of plane fields `(u, v)` to

`N_ξ(u, v) = L_x u - b_N(ξ) v`,  `P_ξ(u, v) = L_x* v + b_P(ξ) u`

(`frequencyNormalRow`, `frequencyPairedRow`). These are the rows of the normal model on the plane
wave with this frequency: for `Ξ (w, z) = cos ⟪ξ, w⟫ u z` and `Η (w, z) = -sin ⟪ξ, w⟫ v z`,
`N = cos ⟪ξ, w⟫ N_ξ(u, v)` and `P = -sin ⟪ξ, w⟫ P_ξ(u, v)`
(`gaugeFixedOperator_add_normalBaseCoupling_planeWave`,
`gaugeFixedAdjoint_add_pairedBaseCoupling_planeWave`). The complex Fourier symbol of the model
is `(u, v) ↦ (L_x u + i b_N(ξ) v, L_x* v + i b_P(ξ) u)`; replacing `v` by `i v` and the paired row
by its quotient by `i` makes it real, and this real form is the family above.

**The adjoint.** Its formal adjoint is the family at the conjugate frequency, with the two slots
exchanged: `∫ ⟪N_ξ(u, v), n⟫ + ∫ ⟪P_ξ(u, v), p⟫ = ∫ ⟪u, P_(conj ξ)(p, n)⟫ + ∫ ⟪v, N_(conj ξ)(p, n)⟫`
(`integral_inner_frequencyNormalRow_add_integral_inner_frequencyPairedRow`).

**The energy identity.** For compactly supported `C¹` fields there are no cross terms:

`∫ (|N_ξ|² + |P_ξ|²) = ∫ |L_x u|² + ∫ |L_x* v|² + |ξ|² (∫ |u|² + ∫ |v|²)`

(`integral_norm_sq_add_norm_sq_frequencyNormalModel`), the frequency form of
`TauCeti.SeibergWitten.integral_norm_sq_add_norm_sq_familyNormalModel`. The couplings cancel
against each other by integration by parts and the complex linearity `L_x J = J' L_x`.

**The slow and fast blocks.** At a vortex of degree `m`, `L_x` has a kernel `K` of real dimension
`2m`, preserved by `J`, and `L_x*` is injective. The family respects the splitting of the
normal slot into `K` and its orthogonal complement:

* on the slow block it is exactly multiplication by `ξ`. A kernel field `κ` goes to
  `(0, b_P(ξ) κ)` (`frequencyNormalRow_zero_right`, `frequencyPairedRow_zero_right`), and
  `b_P(ξ) κ` lies in `K` (`frequencyPairedRow_zero_right_mem_gaugeFixedKernel`). In the
  divisor coordinates `K ≃ ℂ^m` (`TauCeti.Vortex.gaugeFixedKernelEquivCoeff`) the slow block is
  `c ↦ ξ • c` (`frequencyPairedRow_gaugeFixedKernelEquivCoeff_symm`), the symbol of the
  `∂bar`-operator of
  `TauCeti.SeibergWitten.pairedBaseCoupling_fderiv_gaugeFixedKernelEquivCoeff_symm`.
  It has no correction of higher order in `ξ`: the frozen Schur complement is the principal
  symbol itself;
* the fast block does not feed the slow one: the `K`-component of the paired row only sees the
  `K`-component of `u`, `∫ ⟪κ, P_ξ(u, v)⟫ = Re ξ ∫ ⟪κ, u⟫ - Im ξ ∫ ⟪J κ, u⟫`
  (`integral_inner_frequencyPairedRow`), so `P_ξ(u, v)` is orthogonal
  to `K` whenever `u` is (`integral_inner_frequencyPairedRow_eq_zero_of_forall`).

**The bands.** The energy identity gives Clifford coercivity at every frequency, with no
hypothesis on `x`: `|ξ|² (∫ |u|² + ∫ |v|²) ≤ ∫ (|N_ξ|² + |P_ξ|²)`
(`mul_add_le_integral_norm_sq_add_norm_sq_frequencyNormalModel`). This is the
high band `|ξ| ≥ C₀ / h` and, with the lower bound `c₁ / h` on `|ξ|`, the annulus. In the low band
it degenerates only on the slow block. With a spectral gap `c ∫ |η|² ≤ ∫ |L_x* η|²` the fast
components are controlled uniformly in `ξ`:

`c (‖û - Π û‖² + ∫ |v|²) + |ξ|² (∫ |u|² + ∫ |v|²) ≤ ∫ (|N_ξ|² + |P_ξ|²)`,

with `û` the `L²` class of `u` and `Π` the orthogonal projection onto the weak kernel of `L_x`
(`mul_add_add_le_integral_norm_sq_add_norm_sq_frequencyNormalModel`), and one
constant `c > 0` serves for all smooth framed vortices of degree `m` and all frequencies
(`exists_pos_forall_mul_add_add_le_integral_norm_sq_add_norm_sq_frequencyNormalModel`).

The vortex is frozen here: along a curve it moves with a divisor `σ (w)`, and the projections
onto the moving kernels contribute commutator terms, which are not treated in this file.

## Main definitions

* `TauCeti.SeibergWitten.frequencyNormalRow`, `TauCeti.SeibergWitten.frequencyPairedRow`: the two
  rows of the frozen normal model at base frequency `ξ`.

## Main results

* `integral_norm_sq_add_norm_sq_frequencyNormalModel`: the energy identity.
* `integral_inner_frequencyNormalRow_add_integral_inner_frequencyPairedRow`: the formal adjoint
  is the family at the conjugate frequency.
* `frequencyPairedRow_gaugeFixedKernelEquivCoeff_symm`: the slow block is multiplication by `ξ`
  in divisor coordinates.
* `integral_inner_frequencyPairedRow`: the fast block does not feed the slow one.
* `exists_pos_forall_mul_add_add_le_integral_norm_sq_add_norm_sq_frequencyNormalModel`: the band
  estimate, uniform over the vortices of degree `m` and over the frequencies.

## References

* C. H. Taubes, *Gr ⇒ SW: From pseudo-holomorphic curves to Seiberg–Witten solutions*,
  J. Differential Geom. 51 (1999), 203–334.
-/

public section

noncomputable section

namespace TauCeti.SeibergWitten

open Filter MeasureTheory Complex
open scoped Topology ContDiff RealInnerProductSpace InnerProductSpace ComplexConjugate

/-! ### The base couplings at a frequency -/

section Coupling

/-- The base coupling of the normal rows on the rank-one derivative `w ↦ ⟪ξ, w⟫ v` is
`Re ξ • v - Im ξ • J' v`. -/
theorem normalBaseCoupling_smulRight_innerSL (ξ : ℂ) (v : EuclideanSpace ℝ (Fin 4)) :
    normalBaseCoupling ((innerSL ℝ ξ).smulRight v) =
      ξ.re • v - ξ.im • Vortex.targetComplexStructure v := by
  rw [normalBaseCoupling_apply]
  simp [Complex.inner]

/-- The base coupling of the paired rows on the rank-one derivative `w ↦ ⟪ξ, w⟫ u` is
`Re ξ • u + Im ξ • J u`, multiplication by `ξ` in the complex structure `J`. -/
theorem pairedBaseCoupling_smulRight_innerSL (ξ : ℂ) (u : EuclideanSpace ℝ (Fin 4)) :
    pairedBaseCoupling ((innerSL ℝ ξ).smulRight u) =
      ξ.re • u + ξ.im • Vortex.variationComplexStructure u := by
  rw [pairedBaseCoupling_apply]
  simp [Complex.inner]

/-- The base coupling of the normal rows multiplies norms by `|ξ|` on the rank-one derivative
`w ↦ ⟪ξ, w⟫ v`. -/
theorem norm_normalBaseCoupling_smulRight_innerSL (ξ : ℂ) (v : EuclideanSpace ℝ (Fin 4)) :
    ‖normalBaseCoupling ((innerSL ℝ ξ).smulRight v)‖ = ‖ξ‖ * ‖v‖ := by
  -- `v` and `J' v` are orthogonal and have the same length.
  have h0 : ⟪v, Vortex.targetComplexStructure v⟫ = 0 :=
    Vortex.inner_targetComplexStructure_self v
  have h : ‖normalBaseCoupling ((innerSL ℝ ξ).smulRight v)‖ ^ 2 = (‖ξ‖ * ‖v‖) ^ 2 := by
    rw [normalBaseCoupling_smulRight_innerSL, norm_sub_sq_real, inner_smul_left, inner_smul_right,
      h0, norm_smul, norm_smul, LinearIsometryEquiv.norm_map]
    simp only [mul_pow, Complex.sq_norm, Complex.normSq_apply, Real.norm_eq_abs, sq_abs]
    ring
  exact (pow_left_inj₀ (norm_nonneg _) (by positivity) two_ne_zero).1 h

/-- The base coupling of the paired rows multiplies norms by `|ξ|` on the rank-one derivative
`w ↦ ⟪ξ, w⟫ u`. -/
theorem norm_pairedBaseCoupling_smulRight_innerSL (ξ : ℂ) (u : EuclideanSpace ℝ (Fin 4)) :
    ‖pairedBaseCoupling ((innerSL ℝ ξ).smulRight u)‖ = ‖ξ‖ * ‖u‖ := by
  -- `u` and `J u` are orthogonal and have the same length.
  have h0 : ⟪u, Vortex.variationComplexStructure u⟫ = 0 :=
    Vortex.inner_variationComplexStructure_self u
  have h : ‖pairedBaseCoupling ((innerSL ℝ ξ).smulRight u)‖ ^ 2 = (‖ξ‖ * ‖u‖) ^ 2 := by
    rw [pairedBaseCoupling_smulRight_innerSL, norm_add_sq_real, inner_smul_left, inner_smul_right,
      h0, norm_smul, norm_smul, LinearIsometryEquiv.norm_map]
    simp only [mul_pow, Complex.sq_norm, Complex.normSq_apply, Real.norm_eq_abs, sq_abs]
    ring
  exact (pow_left_inj₀ (norm_nonneg _) (by positivity) two_ne_zero).1 h

/-- The transpose of the base coupling of the normal rows at frequency `ξ` is the same coupling at
`conj ξ`. -/
theorem inner_normalBaseCoupling_smulRight_innerSL_left (ξ : ℂ) (v n : EuclideanSpace ℝ (Fin 4)) :
    ⟪normalBaseCoupling ((innerSL ℝ ξ).smulRight v), n⟫ =
      ⟪v, normalBaseCoupling ((innerSL ℝ (conj ξ)).smulRight n)⟫ := by
  rw [normalBaseCoupling_smulRight_innerSL, normalBaseCoupling_smulRight_innerSL, inner_sub_left,
    inner_smul_left, inner_smul_left, Vortex.inner_targetComplexStructure_left, inner_sub_right,
    inner_smul_right, inner_smul_right]
  simp only [conj_re, conj_im, RCLike.conj_to_real]
  ring

/-- The transpose of the base coupling of the paired rows at frequency `ξ` is the same coupling at
`conj ξ`. -/
theorem inner_pairedBaseCoupling_smulRight_innerSL_left (ξ : ℂ) (u p : EuclideanSpace ℝ (Fin 4)) :
    ⟪pairedBaseCoupling ((innerSL ℝ ξ).smulRight u), p⟫ =
      ⟪u, pairedBaseCoupling ((innerSL ℝ (conj ξ)).smulRight p)⟫ := by
  rw [pairedBaseCoupling_smulRight_innerSL, pairedBaseCoupling_smulRight_innerSL, inner_add_left,
    inner_smul_left, inner_smul_left, Vortex.inner_variationComplexStructure_left,
    inner_add_right, inner_smul_right, inner_smul_right]
  simp only [conj_re, conj_im, RCLike.conj_to_real]
  ring

end Coupling

/-! ### The family at a frequency -/

section Rows

variable (x : ℂ → EuclideanSpace ℝ (Fin 4)) (ξ : ℂ) (u v : ℂ → EuclideanSpace ℝ (Fin 4))

/-- The **normal row of the frozen normal model at base frequency `ξ`**:
`N_ξ(u, v) = L_x u - b_N(ξ) v`, where `b_N(ξ) v` is the base coupling of the normal rows on the
rank-one derivative `w ↦ ⟪ξ, w⟫ v`. -/
def frequencyNormalRow (z : ℂ) : EuclideanSpace ℝ (Fin 4) :=
  Vortex.gaugeFixedOperator x u z - normalBaseCoupling ((innerSL ℝ ξ).smulRight (v z))

/-- The **paired row of the frozen normal model at base frequency `ξ`**:
`P_ξ(u, v) = L_x* v + b_P(ξ) u`, where `b_P(ξ) u` is the base coupling of the paired rows on the
rank-one derivative `w ↦ ⟪ξ, w⟫ u`. -/
def frequencyPairedRow (z : ℂ) : EuclideanSpace ℝ (Fin 4) :=
  Vortex.gaugeFixedAdjoint x v z + pairedBaseCoupling ((innerSL ℝ ξ).smulRight (u z))

/-- The normal row at frequency `ξ` is `L_x u - (Re ξ • v - Im ξ • J' v)`. -/
theorem frequencyNormalRow_apply (z : ℂ) :
    frequencyNormalRow x ξ u v z = Vortex.gaugeFixedOperator x u z -
      (ξ.re • v z - ξ.im • Vortex.targetComplexStructure (v z)) := by
  rw [frequencyNormalRow, normalBaseCoupling_smulRight_innerSL]

/-- The paired row at frequency `ξ` is `L_x* v + (Re ξ • u + Im ξ • J u)`. -/
theorem frequencyPairedRow_apply (z : ℂ) :
    frequencyPairedRow x ξ u v z = Vortex.gaugeFixedAdjoint x v z +
      (ξ.re • u z + ξ.im • Vortex.variationComplexStructure (u z)) := by
  rw [frequencyPairedRow, pairedBaseCoupling_smulRight_innerSL]

/-- At frequency zero the family is `(u, v) ↦ (L_x u, L_x* v)`. -/
@[simp]
theorem frequencyNormalRow_zero_frequency :
    frequencyNormalRow x 0 u v = Vortex.gaugeFixedOperator x u := by
  funext z
  simp [frequencyNormalRow_apply]

/-- At frequency zero the family is `(u, v) ↦ (L_x u, L_x* v)`. -/
@[simp]
theorem frequencyPairedRow_zero_frequency :
    frequencyPairedRow x 0 u v = Vortex.gaugeFixedAdjoint x v := by
  funext z
  simp [frequencyPairedRow_apply]

/-- **The normal row of the model on a plane wave.** On the families
`Ξ (w, z) = cos ⟪ξ, w⟫ u z` and `Η (w, z) = -sin ⟪ξ, w⟫ v z`, the normal row
`L_x Ξ (w, ·) + normalBaseCoupling (D_w Η)` of the normal model is `cos ⟪ξ, w⟫ N_ξ(u, v)`. -/
theorem gaugeFixedOperator_add_normalBaseCoupling_planeWave (w z : ℂ) :
    Vortex.gaugeFixedOperator x (Real.cos ⟪ξ, w⟫ • u) z +
        normalBaseCoupling (fderiv ℝ (fun w' ↦ -Real.sin ⟪ξ, w'⟫ • v z) w) =
      Real.cos ⟪ξ, w⟫ • frequencyNormalRow x ξ u v z := by
  -- The base derivative of the paired family is `-cos ⟪ξ, w⟫ ⟪ξ, ·⟫ v z`.
  have hd : fderiv ℝ (fun w' ↦ -Real.sin ⟪ξ, w'⟫ • v z) w =
      -Real.cos ⟪ξ, w⟫ • (innerSL ℝ ξ).smulRight (v z) := by
    refine ((((Real.hasDerivAt_sin _).neg.comp_hasFDerivAt w
      (innerSL ℝ ξ).hasFDerivAt).smul_const (v z)).fderiv).trans ?_
    ext a
    simp [smul_smul, mul_comm]
  rw [Vortex.gaugeFixedOperator_smul, hd, map_smul, frequencyNormalRow, smul_sub, neg_smul,
    ← sub_eq_add_neg]

/-- **The paired row of the model on a plane wave.** On the families
`Ξ (w, z) = cos ⟪ξ, w⟫ u z` and `Η (w, z) = -sin ⟪ξ, w⟫ v z`, the paired row
`L_x* Η (w, ·) + pairedBaseCoupling (D_w Ξ)` of the normal model is `-sin ⟪ξ, w⟫ P_ξ(u, v)`. -/
theorem gaugeFixedAdjoint_add_pairedBaseCoupling_planeWave (w z : ℂ) :
    Vortex.gaugeFixedAdjoint x (-Real.sin ⟪ξ, w⟫ • v) z +
        pairedBaseCoupling (fderiv ℝ (fun w' ↦ Real.cos ⟪ξ, w'⟫ • u z) w) =
      -Real.sin ⟪ξ, w⟫ • frequencyPairedRow x ξ u v z := by
  -- The base derivative of the normal family is `-sin ⟪ξ, w⟫ ⟪ξ, ·⟫ u z`.
  have hd : fderiv ℝ (fun w' ↦ Real.cos ⟪ξ, w'⟫ • u z) w =
      -Real.sin ⟪ξ, w⟫ • (innerSL ℝ ξ).smulRight (u z) := by
    refine ((((Real.hasDerivAt_cos _).comp_hasFDerivAt w
      (innerSL ℝ ξ).hasFDerivAt).smul_const (u z)).fderiv).trans ?_
    ext a
    simp [smul_smul, mul_comm]
  rw [Vortex.gaugeFixedAdjoint_smul, hd, map_smul, frequencyPairedRow, smul_add]

end Rows

/-! ### Continuity and support of the rows -/

section Support

variable {x u v : ℂ → EuclideanSpace ℝ (Fin 4)} {ξ : ℂ}

/-- The normal row of a continuous field on a `C¹` field and a continuous field is continuous. -/
theorem continuous_frequencyNormalRow (hx : Continuous x) (hu : ContDiff ℝ 1 u)
    (hv : Continuous v) : Continuous (frequencyNormalRow x ξ u v) := by
  have hL := Vortex.continuous_gaugeFixedOperator hx hu
  have hJ := Vortex.targetComplexStructure.continuous
  refine Continuous.congr ?_ fun z ↦ (frequencyNormalRow_apply x ξ u v z).symm
  fun_prop

/-- The paired row of a continuous field on a continuous field and a `C¹` field is continuous. -/
theorem continuous_frequencyPairedRow (hx : Continuous x) (hu : Continuous u)
    (hv : ContDiff ℝ 1 v) : Continuous (frequencyPairedRow x ξ u v) := by
  have hL := Vortex.continuous_gaugeFixedAdjoint hx hv
  have hJ := Vortex.variationComplexStructure.continuous
  refine Continuous.congr ?_ fun z ↦ (frequencyPairedRow_apply x ξ u v z).symm
  fun_prop

/-- The normal row of compactly supported fields is compactly supported. -/
theorem hasCompactSupport_frequencyNormalRow (huc : HasCompactSupport u)
    (hvc : HasCompactSupport v) : HasCompactSupport (frequencyNormalRow x ξ u v) := by
  refine ((Vortex.hasCompactSupport_gaugeFixedOperator (x := x) huc).sub
    (f' := fun z ↦ ξ.re • v z - ξ.im • Vortex.targetComplexStructure (v z))
    (hvc.mono fun z hz h0 ↦ hz (by simp [h0]))).mono fun z hz h0 ↦ hz ?_
  rw [frequencyNormalRow_apply]
  simpa using h0

/-- The paired row of compactly supported fields is compactly supported. -/
theorem hasCompactSupport_frequencyPairedRow (huc : HasCompactSupport u)
    (hvc : HasCompactSupport v) : HasCompactSupport (frequencyPairedRow x ξ u v) := by
  refine ((Vortex.hasCompactSupport_gaugeFixedAdjoint (x := x) hvc).add
    (f' := fun z ↦ ξ.re • u z + ξ.im • Vortex.variationComplexStructure (u z))
    (huc.mono fun z hz h0 ↦ hz (by simp [h0]))).mono fun z hz h0 ↦ hz ?_
  rw [frequencyPairedRow_apply]
  simpa using h0

end Support

/-! ### The adjoint and the energy identity -/

section Energy

variable {ν : Measure ℂ} [ν.IsAddHaarMeasure] {x : ℂ → EuclideanSpace ℝ (Fin 4)}
  {u v : ℂ → EuclideanSpace ℝ (Fin 4)}

/-- Pointwise, the pairings of the family at `ξ` and of the family at `conj ξ` differ only by
the first-order terms: the couplings are exchanged by their transposes. -/
private theorem inner_frequencyNormalRow_add_inner_frequencyPairedRow
    {n p : ℂ → EuclideanSpace ℝ (Fin 4)} (ξ z : ℂ) :
    ⟪frequencyNormalRow x ξ u v z, n z⟫ + ⟪frequencyPairedRow x ξ u v z, p z⟫ =
      ⟪u z, frequencyPairedRow x (conj ξ) p n z⟫ + ⟪v z, frequencyNormalRow x (conj ξ) p n z⟫ +
        ((⟪Vortex.gaugeFixedOperator x u z, n z⟫ - ⟪u z, Vortex.gaugeFixedAdjoint x n z⟫) +
          (⟪Vortex.gaugeFixedAdjoint x v z, p z⟫ - ⟪v z, Vortex.gaugeFixedOperator x p z⟫)) := by
  rw [frequencyNormalRow, frequencyPairedRow, frequencyPairedRow, frequencyNormalRow,
    inner_sub_left, inner_add_left, inner_add_right, inner_sub_right,
    inner_normalBaseCoupling_smulRight_innerSL_left,
    inner_pairedBaseCoupling_smulRight_innerSL_left]
  ring

/-- **The formal adjoint of the family at frequency `ξ`** is the family at frequency `conj ξ`
with the two slots exchanged: for a continuous field `x` and `C¹` fields `u`, `v`, `n`, `p`,
where `u` and `v` or `n` and `p` are compactly supported,

`∫ ⟪N_ξ(u, v), n⟫ + ∫ ⟪P_ξ(u, v), p⟫ = ∫ ⟪u, P_(conj ξ)(p, n)⟫ + ∫ ⟪v, N_(conj ξ)(p, n)⟫`. -/
theorem integral_inner_frequencyNormalRow_add_integral_inner_frequencyPairedRow (hx : Continuous x)
    {n p : ℂ → EuclideanSpace ℝ (Fin 4)} (hu : ContDiff ℝ 1 u) (hv : ContDiff ℝ 1 v)
    (hn : ContDiff ℝ 1 n) (hp : ContDiff ℝ 1 p)
    (hc : (HasCompactSupport u ∧ HasCompactSupport v) ∨ (HasCompactSupport n ∧ HasCompactSupport p))
    (ξ : ℂ) :
    ∫ z, ⟪frequencyNormalRow x ξ u v z, n z⟫ ∂ν + ∫ z, ⟪frequencyPairedRow x ξ u v z, p z⟫ ∂ν =
      ∫ z, ⟪u z, frequencyPairedRow x (conj ξ) p n z⟫ ∂ν +
        ∫ z, ⟪v z, frequencyNormalRow x (conj ξ) p n z⟫ ∂ν := by
  -- A pairing of continuous fields, one of which is compactly supported, is integrable.
  have hI {f g : ℂ → EuclideanSpace ℝ (Fin 4)} (hf : Continuous f) (hg : Continuous g)
      (h : HasCompactSupport f ∨ HasCompactSupport g) : Integrable (fun z ↦ ⟪f z, g z⟫) ν :=
    h.elim (hf.integrable_inner_of_hasCompactSupport_left hg)
      (hf.integrable_inner_of_hasCompactSupport_right hg)
  -- In each of the eight pairings, one factor is compactly supported.
  obtain ⟨c₁, c₂, c₃, c₄, c₅, c₆, c₇, c₈⟩ :
      (HasCompactSupport (frequencyNormalRow x ξ u v) ∨ HasCompactSupport n) ∧
      (HasCompactSupport (frequencyPairedRow x ξ u v) ∨ HasCompactSupport p) ∧
      (HasCompactSupport u ∨ HasCompactSupport (frequencyPairedRow x (conj ξ) p n)) ∧
      (HasCompactSupport v ∨ HasCompactSupport (frequencyNormalRow x (conj ξ) p n)) ∧
      (HasCompactSupport (Vortex.gaugeFixedOperator x u) ∨ HasCompactSupport n) ∧
      (HasCompactSupport u ∨ HasCompactSupport (Vortex.gaugeFixedAdjoint x n)) ∧
      (HasCompactSupport (Vortex.gaugeFixedAdjoint x v) ∨ HasCompactSupport p) ∧
      (HasCompactSupport v ∨ HasCompactSupport (Vortex.gaugeFixedOperator x p)) := by
    rcases hc with ⟨huc, hvc⟩ | ⟨hnc, hpc⟩
    · exact ⟨.inl (hasCompactSupport_frequencyNormalRow huc hvc),
        .inl (hasCompactSupport_frequencyPairedRow huc hvc), .inl huc, .inl hvc,
        .inl (Vortex.hasCompactSupport_gaugeFixedOperator huc), .inl huc,
        .inl (Vortex.hasCompactSupport_gaugeFixedAdjoint hvc), .inl hvc⟩
    · exact ⟨.inr hnc, .inr hpc, .inr (hasCompactSupport_frequencyPairedRow hpc hnc),
        .inr (hasCompactSupport_frequencyNormalRow hpc hnc), .inr hnc,
        .inr (Vortex.hasCompactSupport_gaugeFixedAdjoint hnc), .inr hpc,
        .inr (Vortex.hasCompactSupport_gaugeFixedOperator hpc)⟩
  have i₁ := hI (continuous_frequencyNormalRow (ξ := ξ) hx hu hv.continuous) hn.continuous c₁
  have i₂ := hI (continuous_frequencyPairedRow (ξ := ξ) hx hu.continuous hv) hp.continuous c₂
  have i₃ := hI hu.continuous (continuous_frequencyPairedRow (ξ := conj ξ) hx hp.continuous hn) c₃
  have i₄ := hI hv.continuous (continuous_frequencyNormalRow (ξ := conj ξ) hx hp hn.continuous) c₄
  have j₁ := hI (Vortex.continuous_gaugeFixedOperator hx hu) hn.continuous c₅
  have j₂ := hI hu.continuous (Vortex.continuous_gaugeFixedAdjoint hx hn) c₆
  have j₃ := hI (Vortex.continuous_gaugeFixedAdjoint hx hv) hp.continuous c₇
  have j₄ := hI hv.continuous (Vortex.continuous_gaugeFixedOperator hx hp) c₈
  -- The first-order parts are exchanged by integration by parts.
  have e₁ : ∫ z, ⟪Vortex.gaugeFixedOperator x u z, n z⟫ ∂ν =
      ∫ z, ⟪u z, Vortex.gaugeFixedAdjoint x n z⟫ ∂ν :=
    Vortex.integral_inner_gaugeFixedOperator hu hn (hc.imp (·.1) (·.1))
  have e₂ : ∫ z, ⟪Vortex.gaugeFixedAdjoint x v z, p z⟫ ∂ν =
      ∫ z, ⟪v z, Vortex.gaugeFixedOperator x p z⟫ ∂ν := by
    rw [integral_congr_ae (.of_forall fun z ↦ real_inner_comm (p z) _),
      ← Vortex.integral_inner_gaugeFixedOperator hp hv (hc.symm.imp (·.2) (·.2))]
    exact integral_congr_ae (.of_forall fun z ↦ real_inner_comm _ _)
  rw [← integral_add i₁ i₂, ← integral_add i₃ i₄, integral_congr_ae (.of_forall fun z ↦
      inner_frequencyNormalRow_add_inner_frequencyPairedRow (n := n) (p := p) ξ z),
    integral_add (i₃.fun_add i₄) ((j₁.sub' j₂).fun_add (j₃.sub' j₄)),
    integral_add (j₁.sub' j₂) (j₃.sub' j₄), integral_sub j₁ j₂, integral_sub j₃ j₄, e₁, e₂]
  ring

/-- The pointwise expansion of `|N_ξ|² + |P_ξ|²`: the squares of the four blocks plus the cross
terms, which pair `L_x` and `L_x*` with the couplings. -/
private theorem norm_sq_add_norm_sq_frequencyNormalModel (ξ z : ℂ) :
    ‖frequencyNormalRow x ξ u v z‖ ^ 2 + ‖frequencyPairedRow x ξ u v z‖ ^ 2 =
      ‖Vortex.gaugeFixedOperator x u z‖ ^ 2 + ‖Vortex.gaugeFixedAdjoint x v z‖ ^ 2 +
        ‖ξ‖ ^ 2 * (‖u z‖ ^ 2 + ‖v z‖ ^ 2) +
        2 * (ξ.re * (⟪u z, Vortex.gaugeFixedAdjoint x v z⟫ -
              ⟪Vortex.gaugeFixedOperator x u z, v z⟫) +
          ξ.im * (⟪Vortex.variationComplexStructure (u z), Vortex.gaugeFixedAdjoint x v z⟫ -
              ⟪Vortex.gaugeFixedOperator x (fun w ↦ Vortex.variationComplexStructure (u w)) z,
                v z⟫)) := by
  have hA : ⟪Vortex.gaugeFixedOperator x u z, Vortex.targetComplexStructure (v z)⟫ =
      -⟪Vortex.gaugeFixedOperator x (fun w ↦ Vortex.variationComplexStructure (u w)) z, v z⟫ := by
    rw [Vortex.gaugeFixedOperator_variationComplexStructure,
      Vortex.inner_targetComplexStructure_left, neg_neg]
  -- Expand the squares, then the coupling pairings, and normalize the order of the pairings.
  rw [frequencyNormalRow, frequencyPairedRow, norm_sub_sq_real, norm_add_sq_real,
    norm_normalBaseCoupling_smulRight_innerSL, norm_pairedBaseCoupling_smulRight_innerSL,
    normalBaseCoupling_smulRight_innerSL, pairedBaseCoupling_smulRight_innerSL]
  simp only [inner_sub_right, inner_add_right, inner_smul_right, hA,
    real_inner_comm (Vortex.gaugeFixedAdjoint x v z)]
  ring

/-- **The energy identity of the frozen normal model at frequency `ξ`.** For a continuous field
`x` and compactly supported `C¹` fields `u`, `v`,

`∫ (|N_ξ|² + |P_ξ|²) = ∫ |L_x u|² + ∫ |L_x* v|² + |ξ|² (∫ |u|² + ∫ |v|²)`:

the couplings contribute exactly `|ξ|²` times the energy of the fields, with no cross terms. -/
theorem integral_norm_sq_add_norm_sq_frequencyNormalModel (hx : Continuous x)
    (hu : ContDiff ℝ 1 u) (hv : ContDiff ℝ 1 v) (huc : HasCompactSupport u)
    (hvc : HasCompactSupport v) (ξ : ℂ) :
    ∫ z, (‖frequencyNormalRow x ξ u v z‖ ^ 2 + ‖frequencyPairedRow x ξ u v z‖ ^ 2) ∂ν =
      ∫ z, ‖Vortex.gaugeFixedOperator x u z‖ ^ 2 ∂ν +
        ∫ z, ‖Vortex.gaugeFixedAdjoint x v z‖ ^ 2 ∂ν +
        ‖ξ‖ ^ 2 * (∫ z, ‖u z‖ ^ 2 ∂ν + ∫ z, ‖v z‖ ^ 2 ∂ν) := by
  have hJu : ContDiff ℝ 1 fun w ↦ Vortex.variationComplexStructure (u w) :=
    Vortex.variationComplexStructure.contDiff.comp hu
  have hJuc : HasCompactSupport fun w ↦ Vortex.variationComplexStructure (u w) :=
    huc.comp_left (map_zero _)
  have hLu := Vortex.continuous_gaugeFixedOperator hx hu
  have hLJu := Vortex.continuous_gaugeFixedOperator hx hJu
  have hLv := Vortex.continuous_gaugeFixedAdjoint hx hv
  have a₁ := hLu.integrable_norm_sq_of_hasCompactSupport (μ := ν)
    (Vortex.hasCompactSupport_gaugeFixedOperator huc)
  have a₂ := hLv.integrable_norm_sq_of_hasCompactSupport (μ := ν)
    (Vortex.hasCompactSupport_gaugeFixedAdjoint hvc)
  have a₃ := hu.continuous.integrable_norm_sq_of_hasCompactSupport (μ := ν) huc
  have a₄ := hv.continuous.integrable_norm_sq_of_hasCompactSupport (μ := ν) hvc
  -- The pairings in the cross terms are continuous and supported in the supports of `u`, `v`.
  have c₁ : Integrable (fun z ↦ ⟪u z, Vortex.gaugeFixedAdjoint x v z⟫) ν :=
    hu.continuous.integrable_inner_of_hasCompactSupport_left hLv huc
  have c₂ : Integrable (fun z ↦ ⟪Vortex.gaugeFixedOperator x u z, v z⟫) ν :=
    hLu.integrable_inner_of_hasCompactSupport_right hv.continuous hvc
  have c₃ : Integrable (fun z ↦
      ⟪Vortex.variationComplexStructure (u z), Vortex.gaugeFixedAdjoint x v z⟫) ν :=
    hJu.continuous.integrable_inner_of_hasCompactSupport_left hLv hJuc
  have c₄ : Integrable (fun z ↦
      ⟪Vortex.gaugeFixedOperator x (fun w ↦ Vortex.variationComplexStructure (u w)) z, v z⟫) ν :=
    hLJu.integrable_inner_of_hasCompactSupport_right hv.continuous hvc
  -- The two cross terms integrate to zero by integration by parts.
  have e₁ : ∫ z, (⟪u z, Vortex.gaugeFixedAdjoint x v z⟫ -
      ⟪Vortex.gaugeFixedOperator x u z, v z⟫) ∂ν = 0 := by
    rw [integral_sub c₁ c₂, Vortex.integral_inner_gaugeFixedOperator hu hv (.inl huc), sub_self]
  have e₂ : ∫ z, (⟪Vortex.variationComplexStructure (u z), Vortex.gaugeFixedAdjoint x v z⟫ -
      ⟪Vortex.gaugeFixedOperator x (fun w ↦ Vortex.variationComplexStructure (u w)) z, v z⟫)
        ∂ν = 0 := by
    rw [integral_sub c₃ c₄, Vortex.integral_inner_gaugeFixedOperator hJu hv (.inl hJuc), sub_self]
  have i₁ := (a₁.fun_add a₂).fun_add ((a₃.fun_add a₄).const_mul (‖ξ‖ ^ 2))
  have i₂ := ((c₁.sub' c₂).const_mul ξ.re).fun_add ((c₃.sub' c₄).const_mul ξ.im)
  rw [integral_congr_ae (.of_forall fun z ↦
      norm_sq_add_norm_sq_frequencyNormalModel (x := x) (u := u) (v := v) ξ z),
    integral_add i₁ (i₂.const_mul 2), integral_const_mul,
    integral_add ((c₁.sub' c₂).const_mul ξ.re) ((c₃.sub' c₄).const_mul ξ.im), integral_const_mul,
    integral_const_mul, e₁, e₂, integral_add (a₁.fun_add a₂) ((a₃.fun_add a₄).const_mul _),
    integral_add a₁ a₂, integral_const_mul, integral_add a₃ a₄]
  ring

/-- **Clifford coercivity at every frequency.** For a continuous field `x` and compactly supported
`C¹` fields `u`, `v`, `|ξ|² (∫ |u|² + ∫ |v|²) ≤ ∫ (|N_ξ|² + |P_ξ|²)`. No equation and no spectral
gap is assumed. -/
theorem mul_add_le_integral_norm_sq_add_norm_sq_frequencyNormalModel
    (hx : Continuous x) (hu : ContDiff ℝ 1 u) (hv : ContDiff ℝ 1 v) (huc : HasCompactSupport u)
    (hvc : HasCompactSupport v) (ξ : ℂ) :
    ‖ξ‖ ^ 2 * (∫ z, ‖u z‖ ^ 2 ∂ν + ∫ z, ‖v z‖ ^ 2 ∂ν) ≤
      ∫ z, (‖frequencyNormalRow x ξ u v z‖ ^ 2 + ‖frequencyPairedRow x ξ u v z‖ ^ 2) ∂ν := by
  rw [integral_norm_sq_add_norm_sq_frequencyNormalModel hx hu hv huc hvc]
  have h₁ : 0 ≤ ∫ z, ‖Vortex.gaugeFixedOperator x u z‖ ^ 2 ∂ν :=
    integral_nonneg fun z ↦ by positivity
  have h₂ : 0 ≤ ∫ z, ‖Vortex.gaugeFixedAdjoint x v z‖ ^ 2 ∂ν :=
    integral_nonneg fun z ↦ by positivity
  linarith

end Energy

/-! ### The slow and the fast blocks -/

section Blocks

variable {x κ : ℂ → EuclideanSpace ℝ (Fin 4)}

/-- With zero in the paired slot, the normal row is `L_x u` alone. In particular it vanishes on
the kernel of `L_x`. -/
@[simp]
theorem frequencyNormalRow_zero_right (ξ : ℂ) (u : ℂ → EuclideanSpace ℝ (Fin 4)) :
    frequencyNormalRow x ξ u 0 = Vortex.gaugeFixedOperator x u := by
  funext z
  simp [frequencyNormalRow_apply]

/-- With zero in the paired slot, the paired row is the coupling `Re ξ • u + Im ξ • J u` alone. -/
@[simp]
theorem frequencyPairedRow_zero_right (ξ : ℂ) (u : ℂ → EuclideanSpace ℝ (Fin 4)) :
    frequencyPairedRow x ξ u 0 =
      fun z ↦ ξ.re • u z + ξ.im • Vortex.variationComplexStructure (u z) := by
  funext z
  simp [frequencyPairedRow_apply]

/-- **The slow block maps the kernel of `L_x` to itself.** If `κ` lies in the kernel of `L_x`,
so does the paired row `Re ξ • κ + Im ξ • J κ` of the family on `(κ, 0)`. -/
theorem frequencyPairedRow_zero_right_mem_gaugeFixedKernel (hκ : κ ∈ Vortex.gaugeFixedKernel x)
    (ξ : ℂ) : frequencyPairedRow x ξ κ 0 ∈ Vortex.gaugeFixedKernel x := by
  rw [frequencyPairedRow_zero_right]
  exact (Vortex.gaugeFixedKernel x).add_mem ((Vortex.gaugeFixedKernel x).smul_mem _ hκ)
    ((Vortex.gaugeFixedKernel x).smul_mem _
      (Vortex.variationComplexStructure_comp_mem_gaugeFixedKernel hκ))

variable {ν : Measure ℂ} [ν.IsAddHaarMeasure]

/-- **The fast block does not feed the slow block.** For a continuous field `x`, a `C¹` field `κ`
with `L_x κ = 0`, a continuous compactly supported field `u` and a compactly supported `C¹` field
`v`, the pairing of the paired row with `κ` only involves `u`:

`∫ ⟪κ, P_ξ(u, v)⟫ = Re ξ ∫ ⟪κ, u⟫ - Im ξ ∫ ⟪J κ, u⟫`.

The paired slot drops out, since `∫ ⟪κ, L_x* v⟫ = ∫ ⟪L_x κ, v⟫ = 0`. -/
theorem integral_inner_frequencyPairedRow (hx : Continuous x) (hκ₁ : ContDiff ℝ 1 κ)
    (hLκ : ∀ z, Vortex.gaugeFixedOperator x κ z = 0) {u v : ℂ → EuclideanSpace ℝ (Fin 4)}
    (hu : Continuous u) (hv : ContDiff ℝ 1 v) (huc : HasCompactSupport u)
    (hvc : HasCompactSupport v) (ξ : ℂ) :
    ∫ z, ⟪κ z, frequencyPairedRow x ξ u v z⟫ ∂ν =
      ξ.re * ∫ z, ⟪κ z, u z⟫ ∂ν -
        ξ.im * ∫ z, ⟪Vortex.variationComplexStructure (κ z), u z⟫ ∂ν := by
  have hJκ : Continuous fun z ↦ Vortex.variationComplexStructure (κ z) :=
    Vortex.variationComplexStructure.continuous.comp hκ₁.continuous
  -- `⟪κ, L_x* v⟫` is integrable and `∫ ⟪κ, L_x* v⟫ = ∫ ⟪L_x κ, v⟫ = 0`.
  have i₁ := Vortex.integrable_inner_gaugeFixedAdjoint (μ := ν) hx hκ₁.continuous hv hvc
  have h₀ := Vortex.integral_inner_gaugeFixedAdjoint_eq_zero (μ := ν) hκ₁ hv (.inr hvc) hLκ
  -- The other pairings are continuous and supported in the support of `u`.
  have i₂ : Integrable (fun z ↦ ⟪κ z, u z⟫) ν :=
    hκ₁.continuous.integrable_inner_of_hasCompactSupport_right hu huc
  have i₃ : Integrable (fun z ↦ ⟪Vortex.variationComplexStructure (κ z), u z⟫) ν :=
    hJκ.integrable_inner_of_hasCompactSupport_right hu huc
  have hpt (z : ℂ) : ⟪κ z, frequencyPairedRow x ξ u v z⟫ =
      ⟪κ z, Vortex.gaugeFixedAdjoint x v z⟫ +
        (ξ.re * ⟪κ z, u z⟫ - ξ.im * ⟪Vortex.variationComplexStructure (κ z), u z⟫) := by
    rw [frequencyPairedRow_apply, inner_add_right, inner_add_right, inner_smul_right,
      inner_smul_right, Vortex.inner_variationComplexStructure_left]
    ring
  simp_rw [hpt]
  rw [integral_add i₁ ((i₂.const_mul _).sub' (i₃.const_mul _)), h₀, zero_add,
    integral_sub (i₂.const_mul _) (i₃.const_mul _), integral_const_mul, integral_const_mul]

/-- **The fast block preserves the orthogonal complement of the kernel.** If a continuous
compactly supported field `u` is `L²`-orthogonal to the kernel of `L_x`, then so is the paired row
`P_ξ(u, v)`, for every compactly supported `C¹` field `v`. -/
theorem integral_inner_frequencyPairedRow_eq_zero_of_forall (hx : Continuous x)
    {u v : ℂ → EuclideanSpace ℝ (Fin 4)} (hu : Continuous u) (hv : ContDiff ℝ 1 v)
    (huc : HasCompactSupport u) (hvc : HasCompactSupport v)
    (horth : ∀ κ ∈ Vortex.gaugeFixedKernel x, ∫ z, ⟪κ z, u z⟫ ∂ν = 0) (ξ : ℂ)
    (hκ : κ ∈ Vortex.gaugeFixedKernel x) :
    ∫ z, ⟪κ z, frequencyPairedRow x ξ u v z⟫ ∂ν = 0 := by
  obtain ⟨hκ₂, -, hLκ⟩ := Vortex.mem_gaugeFixedKernel.1 hκ
  rw [integral_inner_frequencyPairedRow hx (hκ₂.of_le (by norm_num)) hLκ hu hv huc hvc, horth κ hκ,
    horth _ (Vortex.variationComplexStructure_comp_mem_gaugeFixedKernel hκ)]
  ring

end Blocks

/-! ### The slow block in divisor coordinates -/

section DivisorCoordinates

variable {x : ℂ → EuclideanSpace ℝ (Fin 4)} {m : ℕ} {D : Sym ℂ m}
  (hx : ContDiff ℝ ∞ x) (hhol : ∀ w, Vortex.equation x w 1 = 0 ∧ Vortex.equation x w 2 = 0)
  (hlim : Tendsto (fun w ↦ 4 * (x w 2 ^ 2 + x w 3 ^ 2)) (cocompact ℂ) (𝓝 1))
  (hD : IsZeroMultiplicity (Vortex.sectionValue x) fun z ↦ (D : Multiset ℂ).count z)

include hx hhol hlim hD in
/-- **The slow block is multiplication by `ξ`.** At a smooth field `x` with `∂bar_a α = 0`,
`|α|² → 1` at infinity and zero divisor `D ∈ Sym^m ℂ`, let `E : ker L_x ≃ ℂ^m` be the divisor
coordinates of the kernel of `L_x` (`TauCeti.Vortex.gaugeFixedKernelEquivCoeff`). On the kernel
field with coordinates `c` in the normal slot and zero in the paired slot, the paired row of the
family at frequency `ξ` is the kernel field with coordinates `ξ • c`. The normal row is `L_x` of
the kernel field (`frequencyNormalRow_zero_right`), which vanishes. -/
theorem frequencyPairedRow_gaugeFixedKernelEquivCoeff_symm (ξ : ℂ) (c : Fin m → ℂ) :
    frequencyPairedRow x ξ ((Vortex.gaugeFixedKernelEquivCoeff hx hhol hlim hD).symm c) 0 =
      ((Vortex.gaugeFixedKernelEquivCoeff hx hhol hlim hD).symm (ξ • c) :
        ℂ → EuclideanSpace ℝ (Fin 4)) := by
  have hξ : ξ • c = ξ.re • c + ξ.im • (I • c) := by
    ext j
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Complex.real_smul]
    nth_rw 1 [← re_add_im ξ]
    ring
  rw [frequencyPairedRow_zero_right, hξ, map_add, map_smul, map_smul,
    Vortex.gaugeFixedKernelEquivCoeff_symm_I_smul]
  funext z
  simp

end DivisorCoordinates

/-! ### The band estimates -/

section Bands

variable {x u v : ℂ → EuclideanSpace ℝ (Fin 4)}

/-- **Coercivity of the family at frequency `ξ` modulo the slow block.** Suppose that `L_x*` is
bounded below, `c ∫ |η|² ≤ ∫ |L_x* η|²` for every compactly supported `C²` field `η`, with
`c > 0`. Let `u` be a compactly supported `C¹` field with `L²` class `û`, `v` a compactly
supported `C²` field, and `Π` the orthogonal projection onto the weak kernel of `L_x`. Then

`c (‖û - Π û‖² + ∫ |v|²) + |ξ|² (∫ |u|² + ∫ |v|²) ≤ ∫ (|N_ξ|² + |P_ξ|²)`.

The fast components `û - Π û` and `v` are controlled uniformly in `ξ`, and the slow component
`Π û` at the rate `|ξ|`. -/
theorem mul_add_add_le_integral_norm_sq_add_norm_sq_frequencyNormalModel
    (hx : Continuous x) {c : ℝ} (hc : 0 < c)
    (hgap : ∀ η : ℂ → EuclideanSpace ℝ (Fin 4), ContDiff ℝ 2 η → HasCompactSupport η →
      c * ∫ z, ‖η z‖ ^ 2 ≤ ∫ z, ‖Vortex.gaugeFixedAdjoint x η z‖ ^ 2)
    (hu : ContDiff ℝ 1 u) (hv : ContDiff ℝ 2 v) (huc : HasCompactSupport u)
    (hvc : HasCompactSupport v) {û : Lp (EuclideanSpace ℝ (Fin 4)) 2 (volume : Measure ℂ)}
    (hû : û =ᵐ[volume] u) (ξ : ℂ) :
    c * (‖û - (Vortex.weakGaugeFixedKernel x).starProjection û‖ ^ 2 + ∫ z, ‖v z‖ ^ 2) +
        ‖ξ‖ ^ 2 * ((∫ z, ‖u z‖ ^ 2) + ∫ z, ‖v z‖ ^ 2) ≤
      ∫ z, (‖frequencyNormalRow x ξ u v z‖ ^ 2 + ‖frequencyPairedRow x ξ u v z‖ ^ 2) := by
  rw [integral_norm_sq_add_norm_sq_frequencyNormalModel hx hu
    (hv.of_le (by norm_num)) huc hvc]
  have hA := Vortex.mul_norm_sub_starProjection_sq_le_integral_norm_sq_gaugeFixedOperator hx hc
    hgap hu huc hû
  have hB := hgap v hv hvc
  linarith [mul_add c (‖û - (Vortex.weakGaugeFixedKernel x).starProjection û‖ ^ 2)
    (∫ z, ‖v z‖ ^ 2)]

/-- **The band estimate, uniformly over the vortices of degree `m`.** There is `c > 0`, depending
only on `m`, such that at every smooth plane vortex `x` with the degree-`m` end framing and zero
divisor `D`, at every frequency `ξ`, for every compactly supported `C¹` field `u` with `L²` class
`û` and every compactly supported `C²` field `v`, with `Π` the orthogonal projection onto the weak
kernel of `L_x`,

`c (‖û - Π û‖² + ∫ |v|²) + |ξ|² (∫ |u|² + ∫ |v|²) ≤ ∫ (|N_ξ|² + |P_ξ|²)`.

The constant is uniform over the whole moduli space `Sym^m ℂ` of the frozen vortex and over all
frequencies, so in every band `|ξ| ≤ c₁ / h`, `c₁ / h ≤ |ξ| ≤ C₀ / h` and `|ξ| ≥ C₀ / h`. -/
theorem exists_pos_forall_mul_add_add_le_integral_norm_sq_add_norm_sq_frequencyNormalModel (m : ℕ) :
    ∃ c > 0, ∀ (x : ℂ → EuclideanSpace ℝ (Fin 4)) (D : Multiset ℂ), ContDiff ℝ ∞ x →
      (∀ z, Vortex.equation x z = 0) →
      Tendsto (fun z ↦ Vortex.sectionValue x z * ((z / (‖z‖ : ℂ)) ^ m)⁻¹) (cocompact ℂ)
        (𝓝 1) →
      IsZeroMultiplicity (Vortex.sectionValue x) (fun z ↦ D.count z) →
      ∀ (ξ : ℂ) (u v : ℂ → EuclideanSpace ℝ (Fin 4)), ContDiff ℝ 1 u → ContDiff ℝ 2 v →
      HasCompactSupport u → HasCompactSupport v →
      ∀ û : Lp (EuclideanSpace ℝ (Fin 4)) 2 (volume : Measure ℂ), û =ᵐ[volume] u →
        c * (‖û - (Vortex.weakGaugeFixedKernel x).starProjection û‖ ^ 2 + ∫ z, ‖v z‖ ^ 2) +
            ‖ξ‖ ^ 2 * ((∫ z, ‖u z‖ ^ 2) + ∫ z, ‖v z‖ ^ 2) ≤
          ∫ z, (‖frequencyNormalRow x ξ u v z‖ ^ 2 + ‖frequencyPairedRow x ξ u v z‖ ^ 2) := by
  obtain ⟨c, hc, hgap⟩ :=
    Vortex.exists_pos_forall_mul_integral_norm_sq_le_integral_norm_sq_gaugeFixedAdjoint
      (μ := volume) m
  exact ⟨c, hc, fun x D hx hsol hlim hD ξ u v hu hv huc hvc û hû ↦
    mul_add_add_le_integral_norm_sq_add_norm_sq_frequencyNormalModel
      hx.continuous hc (hgap x D hx hsol hlim hD) hu hv huc hvc hû ξ⟩

end Bands

end TauCeti.SeibergWitten
