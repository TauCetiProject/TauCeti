/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.InnerProductSpace.HodgeStar.Kahler.Hermitian
public import TauCeti.Analysis.PDE.SeibergWitten.CutoffCurrent
public import TauCeti.Analysis.PDE.SeibergWitten.SelfDualSplitting
public import TauCeti.Geometry.Symplectic.Complex.Module.Basic

/-!
# Examples: the normalizations of the large-parameter Seiberg–Witten equations

Taubes's analysis of the Seiberg–Witten equations perturbed by a large multiple `r` of the
symplectic form `ω` of a symplectic four-manifold fixes three normalizations: the Kähler form has
norm `√2`, the Hermitian part of a two-form is read off its anti-self-dual part with the factor
`1 / √2`, and the twisted differential is `d^c_J f = -(1/2) df ∘ J`. This file checks each of them
on an explicit example, and shows how the competing convention would fail.

**The quadratic map on the canonical line.** For a spinor `ψ` of the line `P_α W⁺` of a
self-dual form `ω`, `q(ψ) = (|ψ|² / 4) ω`
(`TauCeti.SeibergWitten.coe_quadraticTwoForm_of_cliffordProjection_apply_eq_self`), so
`|q(ψ)|² = |ω|² |ψ|⁴ / 16` (`norm_quadraticTwoForm_sq_of_cliffordProjection_apply_eq_self`).
A nonzero spinor on that line forces `|ω|² = 2`
(`TauCeti.SeibergWitten.norm_sq_eq_two_of_cliffordProjection_apply_eq_self`), so for a form
normalized by `|ω| = 1` the line is zero and the value `1 / 16` that `q(u₀) = ω / 4` would then
suggest never occurs. For every unit spinor `u₀`, in particular a unit spinor of the canonical
line, `|q(u₀)|² = 1 / 8 = |u₀|⁴ / 8` (`norm_quadraticTwoForm_sq_eq_one_div_eight`, from
`TauCeti.SeibergWitten.norm_quadraticTwoForm_sq`); on the line this is `|ω|² / 16` with
`|ω|² = 2`.

**The Hermitian part.** In a positively oriented unitary frame `e₀, e₁, e₂, e₃` of an oriented
Euclidean four-space, `J e₀ = e₁` and `J e₂ = e₃`, the Kähler form is `ω = e₀₁ + e₂₃`, writing
`eᵢⱼ = eᵢ ∧ eⱼ`. The Hermitian part `B(v, w) = (F(v, J w) + F(w, J v)) / 2` of a two-form `F`
(`TauCeti.AlmostComplexStructure.hermitianForm`) has least eigenvalue `c - |F⁻| / √2`, with
`c = ⟨ω, F⟩ / 2` (`TauCeti.AlmostComplexStructure.isLeast_hermitianForm_apply_self`).

* The anti-self-dual form `F = e₀₁ - e₂₃` (`hodgeStar_ιMulti_zero_one_sub_ιMulti_two_three`) has
  norm `√2` (`norm_ιMulti_zero_one_sub_ιMulti_two_three`) and Hermitian part
  `B = diag(1, 1, -1, -1)` in the frame
  (`toMatrix_hermitianForm_ιMulti_zero_one_sub_ιMulti_two_three`). Its least eigenvalue is
  `-1 = -|F| / √2` (`isLeast_hermitianForm_ιMulti_zero_one_sub_ιMulti_two_three`); the formula
  with `|F⁻|` in place of `|F⁻| / √2` would give `-√2`, which is not the least eigenvalue
  (`not_isLeast_hermitianForm_ιMulti_zero_one_sub_ιMulti_two_three_neg_sqrt_two`).
* The anti-`J`-invariant self-dual forms `e₀₂ - e₁₃` and `e₀₃ + e₁₂` have Hermitian part zero
  (`hermitianForm_ιMulti_zero_two_sub_ιMulti_one_three`,
  `hermitianForm_ιMulti_zero_three_add_ιMulti_one_two`).
* For `F = ω`, `c = 1` and `B` is the metric (`inner_kahlerForm_self_div_two`,
  `TauCeti.AlmostComplexStructure.hermitianForm_kahlerForm`).

**The twisted differential.** On `ℂ` with its complex structure `J v = i v`, the trivial
connection and the section `α = z`, the phase form `τ = Im(conj z dz) / |z|²`
(`TauCeti.SeibergWitten.covariantPhaseForm`) takes the value `1` on the rotation field `i z`, as
the angular form `dθ` does (`covariantPhaseForm_zero_id_apply_I_mul`). Since `∂bar_a α = 0`
(`covariantDBar_zero_id`), it is `d^c_J log |z|²`
(`covariantPhaseForm_zero_id_eq_twistedDifferential_log`), the correction form `E` of the
modulus-potential decomposition vanishes (`cutoffDBarForm_zero_id`), and
`χ(|z|²) τ = d^c_J H(|z|²)` for the modulus potential `H` of any continuous cutoff `χ` vanishing
near `0`
(`cutoffPhaseForm_zero_id_eq_twistedDifferential_modulusPotential`). The convention
`d^c_J f = (1/2) df ∘ J` would give `-dθ`, which differs from `τ`
(`neg_twistedDifferential_log_ne_covariantPhaseForm_zero_id`).

## References

* C. H. Taubes, *SW ⇒ Gr: from the Seiberg–Witten equations to pseudo-holomorphic curves*,
  J. Amer. Math. Soc. 9 (1996), 845–918.
-/

public section

noncomputable section

open Module exteriorPower
open scoped RealInnerProductSpace Topology

namespace TauCeti.Examples.LargeParameter

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [Fact (finrank ℝ V = 4)]

/-- The dimension `Fact` makes the oriented four-space finite-dimensional. -/
local instance finiteDimensional_of_finrank_four : FiniteDimensional ℝ V :=
  .of_fact_finrank_eq_succ 3

/-! ### The quadratic map on the canonical line -/

section Quadratic

open CliffordAlgebra SeibergWitten

variable {Q : QuadraticForm ℝ V} (o : Orientation ℝ V (Fin 4))
  {W : Type*} [NormedAddCommGroup W] [InnerProductSpace ℂ W] [FiniteDimensional ℂ W]
  {ρ : CliffordAlgebra Q →ₐ[ℝ] Module.End ℂ W} {ω : ⋀[ℝ]^2 V}
  (hQ : ∀ v, Q v = -‖v‖ ^ 2) (hkl : 2 + 2 = finrank ℝ V) (hω : o.hodgeStar hkl ω = ω)
  (h₂ : finrank ℂ (positiveHalfSpinors o ρ) = 2)
  (hρ : ∀ v, LinearMap.adjoint (ρ (ι Q v)) = -ρ (ι Q v))
include hQ hω h₂ hρ

/-- **The quadratic map on the canonical line.** For a spinor `ψ` of the line `P_α W⁺` of a
self-dual form `ω`, `|q(ψ)|² = |ω|² |ψ|⁴ / 16`, since `q(ψ) = (|ψ|² / 4) ω`. -/
theorem norm_quadraticTwoForm_sq_of_cliffordProjection_apply_eq_self
    {ψ : positiveHalfSpinors o ρ} (hψ : cliffordProjection o ρ ω ψ = ψ) :
    ‖quadraticTwoForm o ρ hkl ψ‖ ^ 2 = ‖ω‖ ^ 2 * ‖ψ‖ ^ 4 / 16 := by
  rw [← Submodule.norm_coe,
    coe_quadraticTwoForm_of_cliffordProjection_apply_eq_self o hQ hkl hω h₂ hρ hψ, norm_smul,
    Real.norm_of_nonneg (by positivity)]
  ring

omit hω in
/-- **Taubes's normalization `|q(u₀)|² = 1 / 8`.** For every unit spinor `u₀`, in particular a
unit spinor of the canonical line `P_α W⁺`, `|q(u₀)|² = 1 / 8 = |u₀|⁴ / 8`. -/
theorem norm_quadraticTwoForm_sq_eq_one_div_eight {u₀ : positiveHalfSpinors o ρ}
    (hu : ‖u₀‖ = 1) : ‖quadraticTwoForm o ρ hkl u₀‖ ^ 2 = 1 / 8 := by
  rw [norm_quadraticTwoForm_sq o hQ hkl hρ h₂, hu]
  norm_num

end Quadratic

/-! ### The Hermitian part of a two-form in a unitary frame -/

section Hermitian

open AlmostComplexStructure

variable {e : OrthonormalBasis (Fin 4) ℝ V} {J : AlmostComplexStructure V}
  (h₀ : J (e 0) = e 1) (h₂ : J (e 2) = e 3)

/-- The dimension `Fact` in the form `2 + 2 = dim V` taken by the Hodge star. -/
private theorem two_add_two_eq_finrank : 2 + 2 = finrank ℝ V :=
  (Fact.out : finrank ℝ V = 4).symm

/-- **`e₀₁ - e₂₃` is anti-self-dual**: `⋆(e₀₁ - e₂₃) = -(e₀₁ - e₂₃)` for a positively oriented
orthonormal frame. -/
theorem hodgeStar_ιMulti_zero_one_sub_ιMulti_two_three {o : Orientation ℝ V (Fin 4)}
    (hkl : 2 + 2 = finrank ℝ V) (he : e.toBasis.orientation = o) :
    o.hodgeStar hkl (ιMulti ℝ 2 ![e 0, e 1] - ιMulti ℝ 2 ![e 2, e 3]) =
      -(ιMulti ℝ 2 ![e 0, e 1] - ιMulti ℝ 2 ![e 2, e 3]) := by
  rw [map_sub, o.hodgeStar_ιMulti_zero_one hkl he, o.hodgeStar_ιMulti_two_three hkl he, neg_sub]

/-- **`e₀₁ - e₂₃` has norm `√2`.** -/
theorem norm_ιMulti_zero_one_sub_ιMulti_two_three :
    ‖ιMulti ℝ 2 ![e 0, e 1] - ιMulti ℝ 2 ![e 2, e 3]‖ = √2 := by
  have h : ‖ιMulti ℝ 2 ![e 0, e 1] - ιMulti ℝ 2 ![e 2, e 3]‖ ^ 2 = 2 := by
    rw [← real_inner_self_eq_norm_sq]
    simp only [inner_sub_left, inner_sub_right, inner_ιMulti_two, e.inner_eq_ite]
    norm_num
  rw [← h, Real.sqrt_sq (norm_nonneg _)]

include h₀ h₂ in
/-- **The Hermitian part of `e₀₁ - e₂₃` in coordinates**:
`B(v, w) = v₀ w₀ + v₁ w₁ - v₂ w₂ - v₃ w₃`, with `vᵢ = ⟪eᵢ, v⟫`. -/
theorem hermitianForm_ιMulti_zero_one_sub_ιMulti_two_three_apply (v w : V) :
    J.hermitianForm (ιMulti ℝ 2 ![e 0, e 1] - ιMulti ℝ 2 ![e 2, e 3]) v w =
      e.repr v 0 * e.repr w 0 + e.repr v 1 * e.repr w 1 - e.repr v 2 * e.repr w 2 -
        e.repr v 3 * e.repr w 3 := by
  simp only [hermitianForm_apply, inner_sub_left, inner_ιMulti_two, ← e.repr_apply_apply,
    repr_apply h₀ h₂, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons]
  ring

include h₀ h₂ in
/-- **The Hermitian part of `e₀₁ - e₂₃` is `diag(1, 1, -1, -1)`** in the frame `e`. -/
theorem toMatrix_hermitianForm_ιMulti_zero_one_sub_ιMulti_two_three :
    LinearMap.BilinForm.toMatrix e.toBasis
        (J.hermitianForm (ιMulti ℝ 2 ![e 0, e 1] - ιMulti ℝ 2 ![e 2, e 3])) =
      Matrix.diagonal ![1, 1, -1, -1] := by
  ext i j
  rw [LinearMap.BilinForm.toMatrix_apply, OrthonormalBasis.coe_toBasis,
    hermitianForm_ιMulti_zero_one_sub_ιMulti_two_three_apply h₀ h₂]
  fin_cases i <;> fin_cases j <;> simp [OrthonormalBasis.repr_self, Matrix.diagonal]

include h₀ h₂ in
/-- **The least eigenvalue of the Hermitian part of `e₀₁ - e₂₃` is `-1 = -|F| / √2`**: on the unit
sphere the least value of `B(v, v)` is `c - |F⁻| / √2` with `c = 0` and `F⁻ = F` of norm `√2`. -/
theorem isLeast_hermitianForm_ιMulti_zero_one_sub_ιMulti_two_three :
    IsLeast ((fun v ↦ J.hermitianForm (ιMulti ℝ 2 ![e 0, e 1] - ιMulti ℝ 2 ![e 2, e 3]) v v) ''
      Metric.sphere 0 1) (-1) := by
  set F := ιMulti ℝ 2 ![e 0, e 1] - ιMulti ℝ 2 ![e 2, e 3]
  have hF := hodgeStar_ιMulti_zero_one_sub_ιMulti_two_three (e := e) two_add_two_eq_finrank rfl
  -- The anti-self-dual part of `F` is `F` itself.
  have hF' : (2⁻¹ : ℝ) • (F - (e.toBasis.orientation).hodgeStar two_add_two_eq_finrank F) = F := by
    rw [hF]
    module
  convert isLeast_hermitianForm_apply_self h₀ h₂ two_add_two_eq_finrank rfl F using 1
  rw [inner_kahlerForm_eq_zero_of_hodgeStar_eq_neg h₀ h₂ two_add_two_eq_finrank rfl hF, hF',
    norm_ιMulti_zero_one_sub_ιMulti_two_three]
  field_simp
  ring

include h₀ h₂ in
/-- **The anti-self-dual part enters with the factor `1 / √2`.** The formula `c - |F⁻|` for the
least eigenvalue of the Hermitian part would give `-√2` for `F = e₀₁ - e₂₃`, which is not its
least eigenvalue. -/
theorem not_isLeast_hermitianForm_ιMulti_zero_one_sub_ιMulti_two_three_neg_sqrt_two :
    ¬IsLeast ((fun v ↦ J.hermitianForm (ιMulti ℝ 2 ![e 0, e 1] - ιMulti ℝ 2 ![e 2, e 3]) v v) ''
      Metric.sphere 0 1) (-√2) := by
  intro h
  have h1 := h.unique (isLeast_hermitianForm_ιMulti_zero_one_sub_ιMulti_two_three h₀ h₂)
  linarith [Real.one_lt_sqrt_two]

include h₀ h₂ in
/-- **The anti-`J`-invariant self-dual form `e₀₂ - e₁₃` has Hermitian part zero.** -/
theorem hermitianForm_ιMulti_zero_two_sub_ιMulti_one_three :
    J.hermitianForm (ιMulti ℝ 2 ![e 0, e 2] - ιMulti ℝ 2 ![e 1, e 3]) = 0 := by
  refine hermitianForm_eq_zero_of_hodgeStar_eq_self_of_inner_eq_zero h₀ h₂
    two_add_two_eq_finrank rfl ?_ ?_
  · rw [map_sub, Orientation.hodgeStar_ιMulti_zero_two _ rfl,
      Orientation.hodgeStar_ιMulti_one_three _ rfl]
    abel
  · simp [kahlerForm_eq_ιMulti_add_ιMulti h₀ h₂, inner_add_left, inner_sub_right,
      inner_ιMulti_two, e.inner_eq_ite]

include h₀ h₂ in
/-- **The anti-`J`-invariant self-dual form `e₀₃ + e₁₂` has Hermitian part zero.** -/
theorem hermitianForm_ιMulti_zero_three_add_ιMulti_one_two :
    J.hermitianForm (ιMulti ℝ 2 ![e 0, e 3] + ιMulti ℝ 2 ![e 1, e 2]) = 0 := by
  refine hermitianForm_eq_zero_of_hodgeStar_eq_self_of_inner_eq_zero h₀ h₂
    two_add_two_eq_finrank rfl ?_ ?_
  · rw [map_add, Orientation.hodgeStar_ιMulti_zero_three _ rfl,
      Orientation.hodgeStar_ιMulti_one_two _ rfl, add_comm]
  · simp [kahlerForm_eq_ιMulti_add_ιMulti h₀ h₂, inner_add_left, inner_add_right,
      inner_ιMulti_two, e.inner_eq_ite]

include h₀ h₂ in
/-- **For `F = ω` the coefficient `c = ⟪ω, F⟫ / 2` is `1`**, so the least and greatest eigenvalues
of its Hermitian part, the metric (`TauCeti.AlmostComplexStructure.hermitianForm_kahlerForm`),
are both `1`. -/
theorem inner_kahlerForm_self_div_two : ⟪J.kahlerForm, J.kahlerForm⟫ / 2 = 1 := by
  rw [real_inner_self_eq_norm_sq,
    norm_kahlerForm_sq_eq_two (inner_apply_apply_of_orthonormalBasis h₀ h₂)]
  norm_num

end Hermitian

/-! ### The twisted differential of `log |z|²` -/

section Twisted

open AlmostComplexStructure Complex SeibergWitten

/-- **The phase form of `α = z` on the rotation field**: with the trivial connection,
`τ = Im(conj z dz) / |z|²` takes the value `1` on the rotation field `i z`, for `z ≠ 0`, as the
angular form `dθ` does. -/
theorem covariantPhaseForm_zero_id_apply_I_mul {z : ℂ} (hz : z ≠ 0) :
    covariantPhaseForm 0 id z (fun _ ↦ I * z) = 1 := by
  rw [covariantPhaseForm_apply_eq_div hz, id_eq, div_eq_one_iff_eq (normSq_pos.2 hz).ne']
  simp [covariantDeriv_apply, normSq_apply]

/-- **`α = z` is holomorphic**: for the trivial connection, `∂bar_a α = 0`. -/
theorem covariantDBar_zero_id (z : ℂ) : covariantDBar (ofComplexModule ℂ) 0 id z = 0 := by
  ext v
  simp [covariantDeriv_apply, ofComplexModule_apply, ← mul_assoc]

/-- **The phase form of `z` is `d^c_J log |z|²`** away from `0`, with
`d^c_J f = -(1/2) df ∘ J`. -/
theorem covariantPhaseForm_zero_id_eq_twistedDifferential_log {z : ℂ} (hz : z ≠ 0) :
    covariantPhaseForm 0 id z = twistedDifferential (ofComplexModule ℂ)
      (fun y ↦ Real.log (‖y‖ ^ 2)) z :=
  covariantPhaseForm_eq_twistedDifferential_log (ofComplexModule ℂ) differentiableAt_id hz
    (covariantDBar_zero_id z)

/-- **The correction form `E` vanishes for `α = z`**, since `∂bar_a α = 0`. -/
theorem cutoffDBarForm_zero_id (χ : ℝ → ℝ) (z : ℂ) :
    cutoffDBarForm (ofComplexModule ℂ) χ 0 id z = 0 := by
  ext v
  simp [covariantDBar_zero_id]

/-- **The modulus-potential decomposition for `α = z`**: for a continuous cutoff `χ` vanishing
near `0` and its modulus potential `H`, `χ(|z|²) τ = d^c_J H(|z|²)`, the correction form `E`
being zero. -/
theorem cutoffPhaseForm_zero_id_eq_twistedDifferential_modulusPotential {χ : ℝ → ℝ}
    (hχ : Continuous χ) (hχ₀ : χ =ᶠ[𝓝 0] 0) (z : ℂ) :
    cutoffPhaseForm χ 0 id z =
      twistedDifferential (ofComplexModule ℂ) (fun y ↦ modulusPotential χ (normSq y)) z := by
  rw [cutoffPhaseForm_eq_twistedDifferential_add (ofComplexModule ℂ)
    (hasDerivAt_modulusPotential hχ hχ₀ _) hχ₀.self_of_nhds differentiableAt_id,
    cutoffDBarForm_zero_id, add_zero]
  simp only [id_eq]

/-- **The convention `d^c_J f = (1/2) df ∘ J` would give `-dθ`.** For `z ≠ 0`, the opposite of
`d^c_J log |z|²` is not the phase form `τ` of `α = z`. -/
theorem neg_twistedDifferential_log_ne_covariantPhaseForm_zero_id {z : ℂ} (hz : z ≠ 0) :
    -twistedDifferential (ofComplexModule ℂ)
      (fun y ↦ Real.log (‖y‖ ^ 2)) z ≠ covariantPhaseForm 0 id z := by
  rw [← covariantPhaseForm_zero_id_eq_twistedDifferential_log hz]
  intro h
  have h1 := congrArg (fun f ↦ f (fun _ ↦ I * z)) h
  simp only [ContinuousAlternatingMap.neg_apply, covariantPhaseForm_zero_id_apply_I_mul hz] at h1
  norm_num at h1

end Twisted

end TauCeti.Examples.LargeParameter
