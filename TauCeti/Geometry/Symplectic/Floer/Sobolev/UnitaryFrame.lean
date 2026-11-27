/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Floer.Sobolev.Stationary
import TauCeti.Analysis.Calculus.ContinuousLinearMapInverse
import TauCeti.Analysis.Sobolev.Cylinder.Frame
import TauCeti.Analysis.Sobolev.Circle.LinearODE.DeterminantLine
import TauCeti.Geometry.Symplectic.AlmostComplex.Frame
import TauCeti.Geometry.Symplectic.Complex.InnerProductSpace
import TauCeti.Geometry.Symplectic.Floer.AsymptoticOperator.Trivialization

/-!
# The linearized Floer operator at a nondegenerate orbit in a unitary frame

Let `(V, ω)` be a finite-dimensional symplectic vector space, `x` a one-periodic orbit of a
one-periodic Hamiltonian `H` with `x(0)` a nondegenerate fixed point of the time-one map, and
`J_t(y)` a family of almost complex structures. At the stationary cylinder `u(s, t) = x(t)` the
linearized Floer operator is the translation-invariant operator

`D_u = ∂s + J_t(x(t)) (∂t - S_t)`,  `S_t = dX_{H_t}(x(t))`,

and its realization `D_u : W^{1,2}(ℝ × S¹, V) → L²(ℝ × S¹, V)`
(`TauCeti.SymplecticForm.floerSobolevOperator 2`) is injective as soon as the structures
`J_t(x(t))` are `ω`-compatible
(`TauCeti.SymplecticForm.ker_floerSobolevOperator_eq_bot_of_isNondegenerateFixedPt`). This file
proves that it is onto, hence an isomorphism of Banach spaces: the invertible block of a stationary
cylinder over a nondegenerate orbit, for a general loop `J_t(x(t))` rather than only the constant
structure `i` of a unitary trivialization.

The loop of structures is straightened by a **unitary frame**: a `C²` one-periodic family of
invertible maps `Φ_t : F → V` from a finite-dimensional complex inner product space, carrying
`Im ⟪·, ·⟫` to `ω` and `i` to `J_t(x(t))`. Such a frame makes every `J_t(x(t))` compatible with
`ω` (`TauCeti.SymplecticForm.compatible_of_isInvertible_of_forall_eq_im_inner`).

* **The loop in the frame.** Read in the frame, `S` becomes the `C¹` loop
  `S'_t = Φ_t⁻¹ (S_t Φ_t - Φ_t')` (`TauCeti.trivializedCoeff`), infinitesimally symplectic for
  `Im ⟪·, ·⟫` (`TauCeti.SymplecticForm.im_inner_apply_add_eq_zero_of_trivializedCoeff`), and
  `det (1 - Ψ'(1)) ≠ 0` for the return map `Ψ'(1)` of `ζ' = S'_t ζ` because the orbit is
  nondegenerate (`isInvertible_loopOperator_iff_isNondegenerateFixedPt_of_trivializedCoeff`, in the
  namespace `TauCeti.SymplecticForm`).
* **Conjugation.** `D_u` is the stationary cylinder operator `∂s + J_t(x(t)) (∂t - S_t)`
  (`TauCeti.SymplecticForm.floerJetCoeff_eq_stationaryJetCoeff`), so its range is closed
  (`TauCeti.Floer.isClosed_range_stationarySobolevOperator`). For a test section `ζ` of `F`, `Φ ζ`
  is a test section of `V`, and `D_u (Φ ζ) = Φ (D_F ζ)` for the stationary cylinder operator
  `D_F = ∂s + i (∂t - S')` (`TauCeti.Floer.stationaryCylinderOperator_frame_apply`).
* **Surjectivity.** `D_F` maps `W^{1,2}(F)` onto `L²(F)`
  (`TauCeti.Floer.bijective_stationarySobolevOperator_ofComplexModule`), and multiplication by `Φ`
  maps `L²(F)` onto `L²(V)` (`TauCeti.CylinderSobolev.surjective_operatorMultiplication_comp_snd`).
  Since the jets of test sections are dense in `W^{1,2}(F)` and the range of `D_u` is closed, the
  image of `D_F` under multiplication by `Φ`, which is all of `L²(V)`, lies in the range of `D_u`.

When the inner product of `V` is the metric `ω(·, J₀ ·)` of a structure `J₀` with a frame
`Φ : F ≃ V`, the unitary frames `Ψ_t` of a `C²` loop of compatible structures
(`TauCeti.SymplecticForm.unitaryFrame`) give the frame `Ψ_t Φ`, so the operator is invertible
for every such loop.

## Main results

In the namespace `TauCeti.SymplecticForm`:

* `range_floerSobolevOperator_eq_top_of_isNondegenerateFixedPt_of_frame`: `D_u` is onto.
* `isInvertible_floerSobolevOperator_of_isNondegenerateFixedPt_of_frame`: `D_u` is an isomorphism
  `W^{1,2} ≃ L²`.
* `isInvertible_floerSobolevOperator_of_isNondegenerateFixedPt_of_compatible`: the same for a `C²`
  one-periodic loop of compatible structures along `x`, through its unitary frames.
* `range_floerSobolevOperator_eq_top_of_isNondegenerateFixedPt`,
  `isInvertible_floerSobolevOperator_of_isNondegenerateFixedPt`: the case of the identity frame, a
  unitary trivialization with `ω = Im ⟪·, ·⟫` and `J = i`.
* `isInvertible_stationarySobolevOperator_of_compatible`: in a unitary trivialization, the
  stationary cylinder operator `∂s + J_t (∂t - S_t)` over a nondegenerate orbit is invertible for
  every `C²` loop of compatible structures, which need not be the structures of a Floer datum
  along the orbit. On a punctured surface it serves both as the model of an end and as an
  invertible operator with a prescribed constant principal part.

## References

* D. Salamon, *Lectures on Floer homology*, in *Symplectic geometry and topology*, IAS/Park City
  Math. Ser. 7 (1999), Lecture 2, on the invertibility of `∂s + J_t (∂t - S_t)` at a nondegenerate
  orbit, read in a unitary trivialization along the orbit.
* D. McDuff and D. Salamon, *J-holomorphic curves and symplectic topology*, 2nd ed., Section 3.1,
  on unitary trivializations of real Cauchy–Riemann operators.
-/

public section

noncomputable section

open Filter Set Function MeasureTheory Topology ContinuousLinearMap
open scoped NNReal ENNReal Manifold

namespace TauCeti.SymplecticForm

open CylinderSobolev
open StripSobolev (stripMeasure jetLp jetLp_mem_jetClosure)

section Frame

/-! ### Invertibility at a nondegenerate orbit in a unitary frame -/

variable {V F : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [FiniteDimensional ℂ F]
  (ω : SymplecticForm V) {H : ℝ → V → ℝ} {K : ℝ≥0}
  (hX : LipschitzWith K (ω.timeDependentHamiltonianSuspension H))
  (hH : ContDiff ℝ 3 (Function.uncurry H)) (hHp : Periodic H 1) {x : ℝ → V}
  (hx : ∀ t, HasDerivAt x (ω.hamiltonianVectorField (H t) (x t)) t) (hxp : Periodic x 1)
  {J : ℝ → V → AlmostComplexStructure V}
  {Φ : ℝ → F →L[ℝ] V} (hΦ : ContDiff ℝ 2 Φ) (hΦp : Periodic Φ 1)
  (hΦi : ∀ t, (Φ t).IsInvertible) (hΦω : ∀ t v w, ω (Φ t v) (Φ t w) = (inner ℂ v w).im)
  (hΦJ : ∀ t v, J t (x t) (Φ t v) = Φ t (Complex.I • v))

include hΦ hΦi hΦJ in
/-- A unitary frame `Φ` of the structures `J_t(x(t))` makes them continuous in `t`, since
`J_t(x(t)) = Φ_t i Φ_t⁻¹`. -/
theorem continuous_toContinuousLinearMap_of_frame :
    Continuous fun t ↦ (J t (x t)).toLinearMap.toContinuousLinearMap := by
  refine (hΦ.continuous.clm_comp ((continuous_const (y := (AlmostComplexStructure.ofComplexModule
    F).toLinearMap.toContinuousLinearMap)).clm_comp (hΦ.clm_inverse hΦi).continuous)).congr
    fun t ↦ ContinuousLinearMap.ext fun v ↦ ?_
  conv_rhs => rw [← (hΦi t).self_apply_inverse v]
  simp [hΦJ, AlmostComplexStructure.ofComplexModule_apply]

include hH hHp hx hxp hΦ hΦp hΦi hΦω in
/-- The linearized Hamiltonian vector field `S_t = dX_{H_t}(x(t))` along a nondegenerate orbit,
read in a unitary frame `Φ`, is a `C¹` loop `S'_t = Φ_t⁻¹ (S_t Φ_t - Φ_t')` on the circle that is
infinitesimally symplectic for `Im ⟪·, ·⟫` and with `det (1 - Ψ(1)) ≠ 0` for the return map
`Ψ(1)` of `ζ' = S'_t ζ`. -/
private theorem exists_loop_eq_trivializedCoeff
    (hnd : IsNondegenerateFixedPt 𝓘(ℝ, V) (ω.timeDependentHamiltonianFlow H hX 0 1) (x 0)) :
    ∃ S : C(AddCircle (1 : ℝ), F →L[ℝ] F), (fun t : ℝ ↦ S t) =
        trivializedCoeff Φ (fun t ↦ fderiv ℝ (ω.hamiltonianVectorField (H t)) (x t)) ∧
      ContDiff ℝ 1 (fun t : ℝ ↦ S t) ∧
      (∀ θ v w, (inner ℂ (S θ v) w).im + (inner ℂ v (S θ w)).im = 0) ∧
      LinearMap.det ((1 - dysonSeriesLeft (fun t : ℝ ↦ S t) 1 : F →L[ℝ] F) : F →ₗ[ℝ] F) ≠ 0 := by
  have : CompleteSpace F := FiniteDimensional.completeSpace ℂ F
  have hH₂ : ContDiff ℝ 2 (Function.uncurry H) := hH.of_le (by norm_num)
  have hΦd : Differentiable ℝ Φ := hΦ.differentiable (by norm_num)
  obtain ⟨S, hS, hS₁⟩ := ω.exists_loop_eq_fderiv_hamiltonianVectorField hH hHp
    (ω.contDiff_one_of_hasDerivAt_hamiltonianVectorField (hH.of_le (by norm_num)) hx) hxp
  have hSv : (fun t : ℝ ↦ S t) = fun t ↦ fderiv ℝ (ω.hamiltonianVectorField (H t)) (x t) :=
    funext hS
  have hSvp : Periodic (fun t ↦ fderiv ℝ (ω.hamiltonianVectorField (H t)) (x t)) 1 := fun t ↦ by
    rw [← hSv]
    simp only [AddCircle.coe_add_period]
  have hper := periodic_trivializedCoeff hΦp hSvp
  have hS'₁ := contDiff_trivializedCoeff (n := 1) hΦ hΦi (hSv ▸ hS₁)
  let S' : C(AddCircle (1 : ℝ), F →L[ℝ] F) :=
    ⟨hper.lift, continuous_coinduced_dom.2 hS'₁.continuous⟩
  have hS' (t : ℝ) : S' t = trivializedCoeff Φ _ t := hper.lift_coe t
  have hdet := (CircleSobolev.isInvertible_loopOperator_iff_det_ne_zero 1 S').1
    ((ω.isInvertible_loopOperator_iff_isNondegenerateFixedPt_of_trivializedCoeff hX hH₂ hHp hx hxp
      hΦd hΦp hΦi hS').2 hnd)
  exact ⟨S', funext hS', funext hS' ▸ hS'₁, ω.im_inner_apply_add_eq_zero_of_trivializedCoeff
    (fun t ↦ (hH₂.comp (contDiff_prodMk_right t)).contDiffAt) hΦd hΦi hΦω hS', by simpa using hdet⟩

include hH hHp hx hxp hΦ hΦp hΦi hΦω hΦJ in
/-- **The linearized Floer operator at a nondegenerate orbit is onto.** Let `x` be a one-periodic
orbit of a one-periodic, jointly `C³` time-dependent Hamiltonian `H` whose suspended vector field is
globally Lipschitz, with `x(0)` a nondegenerate fixed point of the time-one map, and let `J_t(y)` be
a family of almost complex structures. Suppose that along `x` the structures `J_t(x(t))` have
a unitary frame: a `C²` one-periodic family of invertible maps `Φ_t : F → V` from a
finite-dimensional complex inner product space, carrying `Im ⟪·, ·⟫` to `ω` and `i` to
`J_t(x(t))`. Then at the stationary cylinder `u(s, t) = x(t)` the realization
`D_u : W^{1,2}(ℝ × S¹, V) → L²(ℝ × S¹, V)` of the linearized Floer operator is onto. -/
theorem range_floerSobolevOperator_eq_top_of_isNondegenerateFixedPt_of_frame
    (hnd : IsNondegenerateFixedPt 𝓘(ℝ, V) (ω.timeDependentHamiltonianFlow H hX 0 1) (x 0)) :
    (ω.floerSobolevOperator 2 (fun w y ↦ (J w.2 y).toLinearMap.toContinuousLinearMap)
      (fun _ _ ↦ 0) (fun w ↦ H w.2) (fun w ↦ x w.2)).range = ⊤ := by
  have hH₂ : ContDiff ℝ 2 (Function.uncurry H) := hH.of_le (by norm_num)
  have hΦd : Differentiable ℝ Φ := hΦ.differentiable (by norm_num)
  have hxc : Continuous x := continuous_iff_continuousAt.2 fun t ↦ (hx t).continuousAt
  have hJc := continuous_toContinuousLinearMap_of_frame hΦ hΦi hΦJ
  have hSc := ω.continuous_fderiv_hamiltonianVectorField_comp hH₂ hxc
  -- `D_u` is the stationary cylinder operator `∂s + J_t(x(t)) (∂t - S_t)`, with closed range.
  rw [floerSobolevOperator_def, floerJetCoeff_eq_stationaryJetCoeff ω J H hx,
    ← Floer.stationarySobolevOperator_def, LinearMap.range_eq_top]
  set D := Floer.stationarySobolevOperator (fun t ↦ J t (x t))
    fun t ↦ fderiv ℝ (ω.hamiltonianVectorField (H t)) (x t)
  have hclosed : IsClosed (Set.range D) := Floer.isClosed_range_stationarySobolevOperator
    (fun t ↦ ω.compatible_of_isInvertible_of_forall_eq_im_inner (hΦi t) (hΦω t) (hΦJ t)) hJc
    (fun t ↦ ω.apply_fderiv_hamiltonianVectorField_add
      (hH₂.comp (contDiff_prodMk_right t)).contDiffAt) hSc
    (ω.det_one_sub_dysonSeriesLeft_ne_zero_of_isNondegenerateFixedPt hX hH₂ hx hnd)
  -- The loop `S'` in the frame, and the stationary cylinder operator `D_F = ∂s + i (∂t - S')`.
  obtain ⟨S', hS'f, hS'₁, hS'ω, hdet⟩ :=
    exists_loop_eq_trivializedCoeff ω hX hH hHp hx hxp hΦ hΦp hΦi hΦω hnd
  set DF := Floer.stationarySobolevOperator (fun _ ↦ AlmostComplexStructure.ofComplexModule F)
    fun t : ℝ ↦ S' t
  -- Multiplication by the frame, which maps `L²(F)` onto `L²(V)`.
  set mult := Lp.operatorMultiplication 2 ((memLp_top_comp_snd hΦd.continuous).toLp _)
  have hmult (f : Lp F 2 stripMeasure) : mult f =ᵐ[stripMeasure] fun z ↦ Φ z.2 (f z) := by
    filter_upwards [Lp.operatorMultiplication_ae ((memLp_top_comp_snd hΦd.continuous).toLp _) f,
      (memLp_top_comp_snd hΦd.continuous).coeFn_toLp] with z h₁ h₂
    rw [h₁, h₂]
  -- `D_u (Φ ζ) = Φ (D_F ζ)` for every test section `ζ` of `F`.
  have hgen (ζ : testSection F) :
      mult (DF ⟨jetLp 2 (testSection F) ζ, jetLp_mem_jetClosure ζ⟩) ∈ Set.range D := by
    have hζ := (mem_testSection_iff.1 ζ.property).1
    have hξ := frame_mem_testSection (Φ := fun w : ℝ × ℝ ↦ Φ w.2)
      (hΦ.comp contDiff_snd) (fun _ t ↦ hΦp t) ζ.property
    refine ⟨⟨jetLp 2 (testSection V) ⟨_, hξ⟩, jetLp_mem_jetClosure _⟩, Lp.ext ?_⟩
    filter_upwards [Floer.stationarySobolevOperator_jetLp_ae_eq hJc hSc ⟨_, hξ⟩, hmult _,
      Floer.stationarySobolevOperator_jetLp_ae_eq continuous_const hS'₁.continuous ζ]
      with z h₁ h₂ h₃
    rw [h₁, h₂, h₃, Floer.stationaryCylinderOperator_frame_apply
        (J₀ := fun _ ↦ AlmostComplexStructure.ofComplexModule F) (hΦd z.2) (hΦi z.2)
        (fun v ↦ by simp [hΦJ, AlmostComplexStructure.ofComplexModule_apply])
        ((hζ.differentiable (by norm_num)) z), hS'f]
  -- The frame carries the range of `D_F`, which is all of `L²(F)`, into the closed range of
  -- `D_u`, since the jets of test sections are dense in `W^{1,2}`.
  intro g
  obtain ⟨f, rfl⟩ := surjective_operatorMultiplication_comp_snd hΦd.continuous hΦi g
  obtain ⟨ξ, rfl⟩ := (Floer.bijective_stationarySobolevOperator_ofComplexModule hS'₁ hS'ω hdet).2 f
  refine StripSobolev.jetClosure_induction (hclosed.preimage (mult.continuous.comp DF.continuous))
    (fun ζ ↦ ?_) ξ
  rw [StripSobolev.toJetClosure_apply]
  exact hgen ζ

include hH hHp hx hxp hΦ hΦp hΦi hΦω hΦJ in
/-- **The linearized Floer operator at a nondegenerate orbit is invertible.** Under the hypotheses
of `TauCeti.SymplecticForm.range_floerSobolevOperator_eq_top_of_isNondegenerateFixedPt_of_frame`,
the realization `D_u : W^{1,2}(ℝ × S¹, V) → L²(ℝ × S¹, V)` of the linearized Floer operator at the
stationary cylinder `u(s, t) = x(t)` is an isomorphism of Banach spaces. -/
theorem isInvertible_floerSobolevOperator_of_isNondegenerateFixedPt_of_frame
    (hnd : IsNondegenerateFixedPt 𝓘(ℝ, V) (ω.timeDependentHamiltonianFlow H hX 0 1) (x 0)) :
    (ω.floerSobolevOperator 2 (fun w y ↦ (J w.2 y).toLinearMap.toContinuousLinearMap)
      (fun _ _ ↦ 0) (fun w ↦ H w.2) (fun w ↦ x w.2)).IsInvertible :=
  ⟨.ofBijective _ (ker_floerSobolevOperator_eq_bot_of_isNondegenerateFixedPt ω hX
      (hH.of_le (by norm_num)) hx (continuous_toContinuousLinearMap_of_frame hΦ hΦi hΦJ)
      (fun t ↦ ω.compatible_of_isInvertible_of_forall_eq_im_inner (hΦi t) (hΦω t) (hΦJ t)) hnd)
    (range_floerSobolevOperator_eq_top_of_isNondegenerateFixedPt_of_frame ω hX hH hHp hx hxp hΦ
      hΦp hΦi hΦω hΦJ hnd),
    ContinuousLinearEquiv.coe_ofBijective ..⟩

end Frame

section Unitary

/-! ### Invertibility at a nondegenerate orbit in a unitary trivialization -/

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] [FiniteDimensional ℂ F]
  (ω : SymplecticForm F) {H : ℝ → F → ℝ} {K : ℝ≥0}
  (hX : LipschitzWith K (ω.timeDependentHamiltonianSuspension H))
  (hH : ContDiff ℝ 3 (Function.uncurry H)) (hHp : Periodic H 1) {x : ℝ → F}
  (hx : ∀ t, HasDerivAt x (ω.hamiltonianVectorField (H t) (x t)) t) (hxp : Periodic x 1)

include hH hHp hx hxp in
/-- **The linearized Floer operator at a nondegenerate orbit is onto in a unitary trivialization.**
Let `F` be a finite-dimensional complex inner product space whose symplectic form `ω` is
`Im ⟪·, ·⟫`, and let `x` be a one-periodic orbit of a one-periodic, jointly `C³` time-dependent
Hamiltonian `H` whose suspended vector field is globally Lipschitz, with `x(0)` a nondegenerate
fixed point of the time-one map. At the stationary cylinder `u(s, t) = x(t)`, with the complex
structure `i`, the realization `D_u : W^{1,2}(ℝ × S¹, F) → L²(ℝ × S¹, F)` of the linearized Floer
operator is onto. This is the case of the identity frame of
`TauCeti.SymplecticForm.range_floerSobolevOperator_eq_top_of_isNondegenerateFixedPt_of_frame`. -/
theorem range_floerSobolevOperator_eq_top_of_isNondegenerateFixedPt
    (hω : ∀ v w, ω v w = (inner ℂ v w).im)
    (hnd : IsNondegenerateFixedPt 𝓘(ℝ, F) (ω.timeDependentHamiltonianFlow H hX 0 1) (x 0)) :
    (ω.floerSobolevOperator 2
      (fun _ _ ↦ (AlmostComplexStructure.ofComplexModule F).toLinearMap.toContinuousLinearMap)
        (fun _ _ ↦ 0) (fun w ↦ H w.2) (fun w ↦ x w.2)).range = ⊤ :=
  range_floerSobolevOperator_eq_top_of_isNondegenerateFixedPt_of_frame ω hX hH hHp hx hxp
    (J := fun _ _ ↦ AlmostComplexStructure.ofComplexModule F)
    (Φ := fun _ ↦ ContinuousLinearMap.id ℝ F) contDiff_const (fun _ ↦ rfl)
    (fun _ ↦ ⟨.refl ℝ F, rfl⟩) (fun _ ↦ hω)
    (fun _ v ↦ AlmostComplexStructure.ofComplexModule_apply v) hnd

include hH hHp hx hxp in
/-- **The linearized Floer operator at a nondegenerate orbit is invertible in a unitary
trivialization.** Under the hypotheses of
`TauCeti.SymplecticForm.range_floerSobolevOperator_eq_top_of_isNondegenerateFixedPt`, the
realization `D_u : W^{1,2}(ℝ × S¹, F) → L²(ℝ × S¹, F)` of the linearized Floer operator at the
stationary cylinder `u(s, t) = x(t)` is an isomorphism of Banach spaces. This is the case of the
identity frame of
`TauCeti.SymplecticForm.isInvertible_floerSobolevOperator_of_isNondegenerateFixedPt_of_frame`. -/
theorem isInvertible_floerSobolevOperator_of_isNondegenerateFixedPt
    (hω : ∀ v w, ω v w = (inner ℂ v w).im)
    (hnd : IsNondegenerateFixedPt 𝓘(ℝ, F) (ω.timeDependentHamiltonianFlow H hX 0 1) (x 0)) :
    (ω.floerSobolevOperator 2
      (fun _ _ ↦ (AlmostComplexStructure.ofComplexModule F).toLinearMap.toContinuousLinearMap)
        (fun _ _ ↦ 0) (fun w ↦ H w.2) (fun w ↦ x w.2)).IsInvertible :=
  isInvertible_floerSobolevOperator_of_isNondegenerateFixedPt_of_frame ω hX hH hHp hx hxp
    (J := fun _ _ ↦ AlmostComplexStructure.ofComplexModule F)
    (Φ := fun _ ↦ ContinuousLinearMap.id ℝ F) contDiff_const (fun _ ↦ rfl)
    (fun _ ↦ ⟨.refl ℝ F, rfl⟩) (fun _ ↦ hω)
    (fun _ v ↦ AlmostComplexStructure.ofComplexModule_apply v) hnd

end Unitary

section CompatibleLoop

/-! ### Invertibility at a nondegenerate orbit for a loop of compatible structures -/

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [FiniteDimensional ℂ F]
  (ω : SymplecticForm E) {H : ℝ → E → ℝ} {K : ℝ≥0}
  (hX : LipschitzWith K (ω.timeDependentHamiltonianSuspension H))
  (hH : ContDiff ℝ 3 (Function.uncurry H)) (hHp : Periodic H 1) {x : ℝ → E}
  (hx : ∀ t, HasDerivAt x (ω.hamiltonianVectorField (H t) (x t)) t) (hxp : Periodic x 1)
  {J : ℝ → E → AlmostComplexStructure E}

include hH hHp hx hxp in
/-- **The linearized Floer operator at a nondegenerate orbit is invertible for a loop of compatible
structures.** Let the inner product of `E` be the metric `ω(·, J₀ ·)` of a structure `J₀` with a
frame `Φ : F ≃ E` from a finite-dimensional complex inner product space: `Φ (i v) = J₀ (Φ v)` and
`ω (Φ v) (Φ w) = Im ⟪v, w⟫`. Let `x` be a one-periodic orbit of a one-periodic, jointly `C³`
time-dependent Hamiltonian `H` whose suspended vector field is globally Lipschitz, with `x(0)` a
nondegenerate fixed point of the time-one map, and let `J_t(y)` be a family of almost complex
structures such that along `x` the structures `J_t(x(t))` are `ω`-compatible, one-periodic and `C²`
in `t`. Then at the stationary cylinder `u(s, t) = x(t)` the realization
`D_u : W^{1,2}(ℝ × S¹, E) → L²(ℝ × S¹, E)` of the linearized Floer operator is an isomorphism of
Banach spaces. -/
theorem isInvertible_floerSobolevOperator_of_isNondegenerateFixedPt_of_compatible
    {J₀ : AlmostComplexStructure E} (hg : ∀ v w, ω v (J₀ w) = inner ℝ v w) {Φ : F ≃L[ℝ] E}
    (hΦ : ∀ v, Φ (Complex.I • v) = J₀ (Φ v)) (hΦω : ∀ v w, ω (Φ v) (Φ w) = (inner ℂ v w).im)
    (hJx : ∀ t, ω.Compatible (J t (x t)))
    (hJx₂ : ContDiff ℝ 2 fun t ↦ (J t (x t)).toLinearMap.toContinuousLinearMap)
    (hJxp : Periodic (fun t ↦ J t (x t)) 1)
    (hnd : IsNondegenerateFixedPt 𝓘(ℝ, E) (ω.timeDependentHamiltonianFlow H hX 0 1) (x 0)) :
    (ω.floerSobolevOperator 2 (fun w y ↦ (J w.2 y).toLinearMap.toContinuousLinearMap)
      (fun _ _ ↦ 0) (fun w ↦ H w.2) (fun w ↦ x w.2)).IsInvertible :=
  -- The frame of `J_t(x(t))` is `Ψ_t Φ`, for the unitary frames `Ψ_t` of the loop.
  isInvertible_floerSobolevOperator_of_isNondegenerateFixedPt_of_frame ω hX hH hHp hx hxp
    (Φ := fun t ↦ ω.unitaryFrame (J t (x t)) ∘L (Φ : F →L[ℝ] E))
    ((hJx₂.unitaryFrame hJx).clm_comp contDiff_const)
    (fun t ↦ congrArg (fun J' ↦ ω.unitaryFrame J' ∘L (Φ : F →L[ℝ] E)) (hJxp t))
    (fun t ↦ (hJx t).isInvertible_unitaryFrame.comp ⟨Φ, rfl⟩)
    (fun t v w ↦ by simp [(hJx t).apply_unitaryFrame_unitaryFrame hg, hΦω])
    (fun t v ↦ by simp [(hJx t).apply_unitaryFrame hg, hΦ]) hnd

end CompatibleLoop

section CompatibleLoopUnitary

/-! ### The stationary operator for a loop of compatible structures in a unitary trivialization -/

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] [FiniteDimensional ℂ F]

/-- In a unitary trivialization, the stationary cylinder operator `∂s + J_t (∂t - S_t)` at a
nondegenerate one-periodic orbit, `S_t = dX_{H_t}(x(t))`, is invertible on `W^{1,2}` for every
`C²` one-periodic loop `J_t` of `ω`-compatible structures. -/
theorem isInvertible_stationarySobolevOperator_of_compatible (ω : SymplecticForm F)
    (hω : ∀ v w, ω v w = (inner ℂ v w).im) {H : ℝ → F → ℝ} {K : ℝ≥0}
    (hX : LipschitzWith K (ω.timeDependentHamiltonianSuspension H))
    (hH : ContDiff ℝ 3 (uncurry H)) (hHp : Periodic H 1) {x : ℝ → F}
    (hx : ∀ t, HasDerivAt x (ω.hamiltonianVectorField (H t) (x t)) t) (hxp : Periodic x 1)
    (hnd : IsNondegenerateFixedPt 𝓘(ℝ, F) (ω.timeDependentHamiltonianFlow H hX 0 1) (x 0))
    {J₁ : ℝ → AlmostComplexStructure F} (hJ₁ : ∀ t, ω.Compatible (J₁ t))
    (hJ₁₂ : ContDiff ℝ 2 fun t ↦ (J₁ t).toLinearMap.toContinuousLinearMap)
    (hJ₁p : Periodic J₁ 1) :
    (Floer.stationarySobolevOperator J₁
      fun t ↦ fderiv ℝ (ω.hamiltonianVectorField (H t)) (x t)).IsInvertible := by
  let : InnerProductSpace ℝ F := InnerProductSpace.complexToReal
  have h := ω.isInvertible_floerSobolevOperator_of_isNondegenerateFixedPt_of_compatible hX hH hHp
    hx hxp (J := fun t _ ↦ J₁ t) (ω.apply_ofComplexModule_eq_inner hω)
    (Φ := ContinuousLinearEquiv.refl ℝ F)
    (fun v ↦ by simp [AlmostComplexStructure.ofComplexModule_apply]) (fun v w ↦ by simp [hω])
    hJ₁ hJ₁₂ hJ₁p hnd
  rwa [floerSobolevOperator_def, floerJetCoeff_eq_stationaryJetCoeff ω (fun t _ ↦ J₁ t) H hx,
    ← Floer.stationarySobolevOperator_def] at h

end CompatibleLoopUnitary

end TauCeti.SymplecticForm
