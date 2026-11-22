/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Floer.Sobolev.Realization
import TauCeti.Analysis.ODE.Regularity
import TauCeti.Geometry.Symplectic.AlmostComplex.Frame
import TauCeti.Geometry.Symplectic.Complex.InnerProductSpace
import TauCeti.Geometry.Symplectic.Floer.AsymptoticOperator.DenseRange
import TauCeti.Geometry.Symplectic.Floer.AsymptoticOperator.Trivialization

/-!
# The linearized Floer operator at a nondegenerate orbit in a unitary frame

Let `(V, ω)` be a finite-dimensional symplectic vector space, `x` a one-periodic orbit of a
one-periodic Hamiltonian `H` with `x(0)` a nondegenerate fixed point of the time-one map, and
`J_t(y)` a family of almost complex structures. At the stationary cylinder `u(s, t) = x(t)` the
linearized Floer operator is the translation-invariant operator

`D_u = ∂s + J_t(x(t)) (∂t - S_t)`,  `S_t = dX_{H_t}(x(t))`,

and its realization `D_u : W^{1,2}(ℝ × S¹, V) → L²(ℝ × S¹, V)`
(`TauCeti.SymplecticForm.floerSobolevOperator`) is injective as soon as the structures
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
  `ζ' = S'_t ζ` has no nonzero one-periodic solution because the orbit is nondegenerate
  (`isInvertible_loopOperator_iff_isNondegenerateFixedPt_of_trivializedCoeff`, in the namespace
  `TauCeti.SymplecticForm`).
* **Conjugation.** For a test section `ζ` of `F`, `Φ ζ` is a test section of `V`, and
  `D_u (Φ ζ) = Φ (D_F ζ)` for the stationary cylinder operator `D_F = ∂s + i (∂t - S')`
  (`TauCeti.Floer.stationaryCylinderOperator_frame_apply`).
* **Density.** The values `D_F ζ` on test sections are dense in the Hilbert space `L²(F)`: an
  `L²` section orthogonal to all of them vanishes
  (`TauCeti.Floer.ae_eq_zero_of_forall_integral_re_inner_stationaryCylinderOperator_eq_zero`).
  Multiplication by `Φ` maps `L²(F)` onto `L²(V)`
  (`TauCeti.CylinderSobolev.surjective_operatorMultiplication_comp_snd`), so the range of `D_u`
  contains a dense subspace of `L²(V)`. It is closed by the semi-Fredholm estimate, so it is
  everything.

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

namespace TauCeti.Floer

open CylinderSobolev
open StripSobolev (jet jet_apply stripMeasure)

/-- The stationary cylinder operator of continuous loops maps test sections into `L²`. -/
private theorem memLp_stationaryCylinderOperator {W : Type*} [NormedAddCommGroup W]
    [NormedSpace ℝ W] [FiniteDimensional ℝ W] {J : ℝ → AlmostComplexStructure W}
    {S : ℝ → W →L[ℝ] W} (hJc : Continuous fun t ↦ (J t).toLinearMap.toContinuousLinearMap)
    (hSc : Continuous S) (ζ : testSection W) :
    MemLp (stationaryCylinderOperator J S ζ) 2 stripMeasure := by
  obtain ⟨hζ, -, R, hR⟩ := mem_testSection_iff.1 ζ.property
  refine memLp_stripMeasure_of_continuous (R := R)
    (continuous_stationaryCylinderOperator hJc hSc (hζ.of_le one_le_two)) (fun z hz ↦ ?_) 2
  -- The operator vanishes where the jet of `ζ` does.
  have h := StripSobolev.jet_eq_zero_of_lt_abs hR hz
  rw [jet_apply, Prod.mk_eq_zero, Prod.mk_eq_zero] at h
  simp only [stationaryCylinderOperator_def, stdComplexLineReal_eq, stdComplexLineImag_eq, h.1,
    h.2.1, h.2.2, map_zero, sub_zero, add_zero]

/-- **Dense range in a unitary trivialization.** Let `F` be a finite-dimensional complex inner
product space and `S` a `C¹` loop of maps infinitesimally symplectic for `Im ⟪·, ·⟫`, whose
equation `ζ' = S_t ζ` has no nonzero one-periodic solution. Then the values on test sections of
the stationary cylinder operator `∂s + i (∂t - S_t)` span a dense subspace of `L²(ℝ × S¹, F)`. -/
private theorem topologicalClosure_span_stationaryCylinderOperator_eq_top {F : Type*}
    [NormedAddCommGroup F] [InnerProductSpace ℂ F] [FiniteDimensional ℂ F]
    {S : C(AddCircle (1 : ℝ), F →L[ℝ] F)} (hS₁ : ContDiff ℝ 1 fun t : ℝ ↦ S t)
    (hS : ∀ t v w, (inner ℂ (S t v) w).im + (inner ℂ v (S t w)).im = 0)
    (hnd : ∀ ζ : C(AddCircle (1 : ℝ), F),
      (∀ x : ℝ, HasDerivAt (fun y : ℝ ↦ ζ y) (S x (ζ x)) x) → ζ = 0) :
    (Submodule.span ℝ (Set.range fun ζ : testSection F ↦
      (memLp_stationaryCylinderOperator (J := fun _ ↦ AlmostComplexStructure.ofComplexModule F)
        continuous_const hS₁.continuous ζ).toLp _)).topologicalClosure = ⊤ := by
  let : InnerProductSpace ℝ F := InnerProductSpace.complexToReal
  rw [← Submodule.orthogonal_orthogonal_eq_closure]
  convert Submodule.bot_orthogonal_eq_top
  -- An `L²` section orthogonal to every value vanishes.
  refine (Submodule.eq_bot_iff _).2 fun η hη ↦ Lp.eq_zero_iff_ae_eq_zero.2 ?_
  refine ae_eq_zero_of_forall_integral_re_inner_stationaryCylinderOperator_eq_zero hS₁ hS hnd
    (Lp.memLp η) fun ξ hξ ↦ ?_
  have hDF := memLp_stationaryCylinderOperator
    (J := fun _ ↦ AlmostComplexStructure.ofComplexModule F) continuous_const hS₁.continuous
  have h₀ := Submodule.inner_right_of_mem_orthogonal
    (Submodule.subset_span (R := ℝ) (Set.mem_range_self (f := fun ζ ↦ (hDF ζ).toLp _) ⟨ξ, hξ⟩))
    hη
  rw [L2.inner_def] at h₀
  refine (integral_congr_ae ?_).trans h₀
  -- The real inner product of `F` is the real part of its complex inner product.
  filter_upwards [(hDF ⟨ξ, hξ⟩).coeFn_toLp] with z hz
  rw [hz]
  exact (real_inner_eq_re_inner ℂ _ _).symm

end TauCeti.Floer

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
  (hJ : ContDiff ℝ 1 fun p : ℝ × V ↦ (J p.1 p.2).toLinearMap.toContinuousLinearMap)
  {Φ : ℝ → F →L[ℝ] V} (hΦ : ContDiff ℝ 2 Φ) (hΦp : Periodic Φ 1)
  (hΦi : ∀ t, (Φ t).IsInvertible) (hΦω : ∀ t v w, ω (Φ t v) (Φ t w) = (inner ℂ v w).im)
  (hΦJ : ∀ t v, J t (x t) (Φ t v) = Φ t (Complex.I • v))

include hH hHp hx hxp hΦ hΦp hΦi hΦω in
/-- The linearized Hamiltonian vector field `S_t = dX_{H_t}(x(t))` along a nondegenerate orbit,
read in a unitary frame `Φ`, is a `C¹` loop `S'_t = Φ_t⁻¹ (S_t Φ_t - Φ_t')` on the circle that is
infinitesimally symplectic for `Im ⟪·, ·⟫` and whose equation `ζ' = S'_t ζ` has no nonzero
one-periodic solution. -/
private theorem exists_loop_eq_trivializedCoeff
    (hnd : IsNondegenerateFixedPt 𝓘(ℝ, V) (ω.timeDependentHamiltonianFlow H hX 0 1) (x 0)) :
    ∃ S : C(AddCircle (1 : ℝ), F →L[ℝ] F), (fun t : ℝ ↦ S t) =
        trivializedCoeff Φ (fun t ↦ fderiv ℝ (ω.hamiltonianVectorField (H t)) (x t)) ∧
      ContDiff ℝ 1 (fun t : ℝ ↦ S t) ∧
      (∀ θ v w, (inner ℂ (S θ v) w).im + (inner ℂ v (S θ w)).im = 0) ∧
      ∀ ζ : C(AddCircle (1 : ℝ), F), (∀ t : ℝ, HasDerivAt (fun y : ℝ ↦ ζ y) (S t (ζ t)) t) →
        ζ = 0 := by
  have : CompleteSpace F := FiniteDimensional.completeSpace ℂ F
  have hH₂ : ContDiff ℝ 2 (Function.uncurry H) := hH.of_le (by norm_num)
  have hΦd : Differentiable ℝ Φ := hΦ.differentiable (by norm_num)
  obtain ⟨S, hS, hS₁⟩ := ω.exists_loop_eq_fderiv_hamiltonianVectorField hH hHp hx hxp
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
  refine ⟨S', funext hS', funext hS' ▸ hS'₁, ω.im_inner_apply_add_eq_zero_of_trivializedCoeff
    (fun t ↦ (hH₂.comp (contDiff_prodMk_right t)).contDiffAt) hΦd hΦi hΦω hS',
    (CircleSobolev.isInvertible_loopOperator_iff 1 S').1
      ((ω.isInvertible_loopOperator_iff_isNondegenerateFixedPt_of_trivializedCoeff hX hH₂ hHp hx
        hxp hΦd hΦp hΦi hS').2 hnd)⟩

omit [FiniteDimensional ℂ F] in
include hH hx hJ hΦi hΦω hΦJ in
/-- At the stationary cylinder over a nondegenerate orbit with a unitary frame, the coefficients of
the linearized Floer operator are bounded and its realization on `W^{1,2}` has closed range. -/
private theorem memLp_floerJetCoeff_and_isClosed_range_of_frame
    (hnd : IsNondegenerateFixedPt 𝓘(ℝ, V) (ω.timeDependentHamiltonianFlow H hX 0 1) (x 0)) :
    MemLp (ω.floerJetCoeff (fun w y ↦ (J w.2 y).toLinearMap.toContinuousLinearMap) (fun _ _ ↦ 0)
        (fun w ↦ H w.2) (fun w ↦ x w.2)) ∞ stripMeasure ∧
      IsClosed ((ω.floerSobolevOperator (fun w y ↦ (J w.2 y).toLinearMap.toContinuousLinearMap)
        (fun _ _ ↦ 0) (fun w ↦ H w.2) (fun w ↦ x w.2)).range : Set (Lp V 2 stripMeasure)) := by
  have hH₂ : ContDiff ℝ 2 (Function.uncurry H) := hH.of_le (by norm_num)
  have hJx (t : ℝ) : ω.Compatible (J t (x t)) :=
    ω.compatible_of_isInvertible_of_forall_eq_im_inner (hΦi t) (hΦω t) (hΦJ t)
  have hu : ContDiff ℝ 1 fun w : ℝ × ℝ ↦ x w.2 :=
    (contDiff_one_of_hasDerivAt (X := fun t ↦ ω.hamiltonianVectorField (H t))
      (ω.contDiff_hamiltonianVectorField_uncurry (n := 0)
        (by simpa using hH₂.of_le one_le_two)).continuous hx).comp contDiff_snd
  -- The loops of `u` and its slice defect do not depend on `s`, so they converge uniformly.
  have hc (f : ℝ → V) (l : Filter ℝ) : TendstoUniformlyOn (fun (_ : ℝ) t ↦ f t) f l (Icc 0 1) :=
    fun _ hU ↦ Eventually.of_forall fun _ _ _ ↦ refl_mem_uniformity hU
  have h₀ (l : Filter ℝ) : TendstoUniformlyOn (fun s t ↦ sliceDefect
      (fun t ↦ ω.hamiltonianVectorField (H t)) (fun w : ℝ × ℝ ↦ x w.2) (s, t)) 0 l (Icc 0 1) := by
    simpa only [sliceDefect_comp_snd_eq_zero hx, Pi.zero_apply] using hc 0 l
  exact ⟨ω.memLp_floerJetCoeff hH₂ hJ hu (hc x _) (hc x _) (h₀ _) (h₀ _),
    ω.isClosed_range_floerSobolevOperator hX hH₂ hx hnd hx hnd hJ hJx hJx hu (fun z ↦ hJx z.2)
      (hc x _) (hc x _) (h₀ _) (h₀ _)⟩

include hH hHp hx hxp hJ hΦ hΦp hΦi hΦω hΦJ in
/-- **The linearized Floer operator at a nondegenerate orbit is onto.** Let `x` be a one-periodic
orbit of a one-periodic, jointly `C³` time-dependent Hamiltonian `H` whose suspended vector field is
globally Lipschitz, with `x(0)` a nondegenerate fixed point of the time-one map, and let `J_t(y)` be
a `C¹` family of almost complex structures. Suppose that along `x` the structures `J_t(x(t))` have
a unitary frame: a `C²` one-periodic family of invertible maps `Φ_t : F → V` from a
finite-dimensional complex inner product space, carrying `Im ⟪·, ·⟫` to `ω` and `i` to
`J_t(x(t))`. Then at the stationary cylinder `u(s, t) = x(t)` the realization
`D_u : W^{1,2}(ℝ × S¹, V) → L²(ℝ × S¹, V)` of the linearized Floer operator is onto. -/
theorem range_floerSobolevOperator_eq_top_of_isNondegenerateFixedPt_of_frame
    (hnd : IsNondegenerateFixedPt 𝓘(ℝ, V) (ω.timeDependentHamiltonianFlow H hX 0 1) (x 0)) :
    (ω.floerSobolevOperator (fun w y ↦ (J w.2 y).toLinearMap.toContinuousLinearMap)
      (fun _ _ ↦ 0) (fun w ↦ H w.2) (fun w ↦ x w.2)).range = ⊤ := by
  have hΦd : Differentiable ℝ Φ := hΦ.differentiable (by norm_num)
  obtain ⟨hM, hclosed⟩ :=
    memLp_floerJetCoeff_and_isClosed_range_of_frame ω hX hH hx hJ hΦi hΦω hΦJ hnd
  set D := ω.floerSobolevOperator (fun w y ↦ (J w.2 y).toLinearMap.toContinuousLinearMap)
    (fun _ _ ↦ 0) (fun w ↦ H w.2) (fun w ↦ x w.2)
  -- The loop `S'` of the linearized vector field in the frame, and the stationary cylinder
  -- operator `D_F = ∂s + i (∂t - S')` on `F`, whose values on test sections are dense in `L²(F)`.
  obtain ⟨S', hS'f, hS'₁, hS'ω, hS'nd⟩ :=
    exists_loop_eq_trivializedCoeff ω hX hH hHp hx hxp hΦ hΦp hΦi hΦω hnd
  have hDF := Floer.memLp_stationaryCylinderOperator
    (J := fun _ ↦ AlmostComplexStructure.ofComplexModule F) continuous_const hS'₁.continuous
  have hP := Floer.topologicalClosure_span_stationaryCylinderOperator_eq_top hS'₁ hS'ω hS'nd
  -- Multiplication by the frame, which maps `L²(F)` onto `L²(V)`.
  set mult := Lp.operatorMultiplication 2 ((memLp_top_comp_snd hΦd.continuous).toLp _)
  have hmult (f : Lp F 2 stripMeasure) : mult f =ᵐ[stripMeasure] fun z ↦ Φ z.2 (f z) := by
    filter_upwards [Lp.operatorMultiplication_ae ((memLp_top_comp_snd hΦd.continuous).toLp _) f,
      (memLp_top_comp_snd hΦd.continuous).coeFn_toLp] with z h₁ h₂
    rw [h₁, h₂]
  -- `D_u (Φ ζ) = Φ (D_F ζ)` for every test section `ζ` of `F`, so the frame carries the values
  -- of `D_F` into the range of `D_u`.
  have hgen (ζ : testSection F) : mult ((hDF ζ).toLp _) ∈ D.range := by
    obtain ⟨hζ, hζp, R, hR⟩ := mem_testSection_iff.1 ζ.property
    have hξ : (fun w : ℝ × ℝ ↦ Φ w.2 ((ζ : ℝ × ℝ → F) w)) ∈ testSection V :=
      mem_testSection_iff.2 ⟨(hΦ.comp contDiff_snd).clm_apply hζ,
        fun s t ↦ by simp only [hΦp t, hζp s t], R, fun s t hs ↦ by simp only [hR s t hs, map_zero]⟩
    refine ⟨⟨jetLp (testSection V) ⟨_, hξ⟩, jetLp_mem_jetClosure _⟩, Lp.ext ?_⟩
    filter_upwards [ω.floerSobolevOperator_jetLp_ae_eq hM ⟨_, hξ⟩, hmult ((hDF ζ).toLp _),
      (hDF ζ).coeFn_toLp] with z h₁ h₂ h₃
    refine h₁.trans ?_
    rw [h₂, h₃, floerLinearization_eq_stationaryCylinderOperator ω J H hx,
      Floer.stationaryCylinderOperator_frame_apply
        (J₀ := fun _ ↦ AlmostComplexStructure.ofComplexModule F) (hΦd z.2) (hΦi z.2)
        (fun v ↦ by simp [hΦJ, AlmostComplexStructure.ofComplexModule_apply])
        ((hζ.differentiable (by norm_num)) z), hS'f]
  -- The range of `D_u` is closed and contains the image of a dense subspace.
  have hle := Submodule.topologicalClosure_minimal _
    (Submodule.span_le.2 (Set.range_subset_iff.2 hgen) : _ ≤ D.range.comap mult.toLinearMap)
    (hclosed.preimage mult.continuous)
  rw [hP] at hle
  refine eq_top_iff.2 fun g _ ↦ ?_
  obtain ⟨f, rfl⟩ := surjective_operatorMultiplication_comp_snd hΦd.continuous hΦi g
  exact hle Submodule.mem_top

include hH hHp hx hxp hJ hΦ hΦp hΦi hΦω hΦJ in
/-- **The linearized Floer operator at a nondegenerate orbit is invertible.** Under the hypotheses
of `TauCeti.SymplecticForm.range_floerSobolevOperator_eq_top_of_isNondegenerateFixedPt_of_frame`,
the realization `D_u : W^{1,2}(ℝ × S¹, V) → L²(ℝ × S¹, V)` of the linearized Floer operator at the
stationary cylinder `u(s, t) = x(t)` is an isomorphism of Banach spaces. -/
theorem isInvertible_floerSobolevOperator_of_isNondegenerateFixedPt_of_frame
    (hnd : IsNondegenerateFixedPt 𝓘(ℝ, V) (ω.timeDependentHamiltonianFlow H hX 0 1) (x 0)) :
    (ω.floerSobolevOperator (fun w y ↦ (J w.2 y).toLinearMap.toContinuousLinearMap)
      (fun _ _ ↦ 0) (fun w ↦ H w.2) (fun w ↦ x w.2)).IsInvertible :=
  ⟨.ofBijective _ (ker_floerSobolevOperator_eq_bot_of_isNondegenerateFixedPt ω hX
      (hH.of_le (by norm_num)) hx hJ (fun t ↦ ω.compatible_of_isInvertible_of_forall_eq_im_inner
        (hΦi t) (hΦω t) (hΦJ t)) hnd)
    (range_floerSobolevOperator_eq_top_of_isNondegenerateFixedPt_of_frame ω hX hH hHp hx hxp hJ hΦ
      hΦp hΦi hΦω hΦJ hnd),
    ContinuousLinearEquiv.coe_ofBijective ..⟩

end Frame

section CompatibleLoop

/-! ### Invertibility at a nondegenerate orbit for a loop of compatible structures -/

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [FiniteDimensional ℂ F]
  (ω : SymplecticForm E) {H : ℝ → E → ℝ} {K : ℝ≥0}
  (hX : LipschitzWith K (ω.timeDependentHamiltonianSuspension H))
  (hH : ContDiff ℝ 3 (Function.uncurry H)) (hHp : Periodic H 1) {x : ℝ → E}
  (hx : ∀ t, HasDerivAt x (ω.hamiltonianVectorField (H t) (x t)) t) (hxp : Periodic x 1)
  {J : ℝ → E → AlmostComplexStructure E}
  (hJ : ContDiff ℝ 1 fun p : ℝ × E ↦ (J p.1 p.2).toLinearMap.toContinuousLinearMap)

include hH hHp hx hxp hJ in
/-- **The linearized Floer operator at a nondegenerate orbit is invertible for a loop of compatible
structures.** Let the inner product of `E` be the metric `ω(·, J₀ ·)` of a structure `J₀` with a
frame `Φ : F ≃ E` from a finite-dimensional complex inner product space: `Φ (i v) = J₀ (Φ v)` and
`ω (Φ v) (Φ w) = Im ⟪v, w⟫`. Let `x` be a one-periodic orbit of a one-periodic, jointly `C³`
time-dependent Hamiltonian `H` whose suspended vector field is globally Lipschitz, with `x(0)` a
nondegenerate fixed point of the time-one map, and let `J_t(y)` be a `C¹` family of almost complex
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
    (ω.floerSobolevOperator (fun w y ↦ (J w.2 y).toLinearMap.toContinuousLinearMap)
      (fun _ _ ↦ 0) (fun w ↦ H w.2) (fun w ↦ x w.2)).IsInvertible :=
  -- The frame of `J_t(x(t))` is `Ψ_t Φ`, for the unitary frames `Ψ_t` of the loop.
  isInvertible_floerSobolevOperator_of_isNondegenerateFixedPt_of_frame ω hX hH hHp hx hxp hJ
    (Φ := fun t ↦ ω.unitaryFrame (J t (x t)) ∘L (Φ : F →L[ℝ] E))
    ((hJx₂.unitaryFrame hJx).clm_comp contDiff_const)
    (fun t ↦ congrArg (fun J' ↦ ω.unitaryFrame J' ∘L (Φ : F →L[ℝ] E)) (hJxp t))
    (fun t ↦ (hJx t).isInvertible_unitaryFrame.comp ⟨Φ, rfl⟩)
    (fun t v w ↦ by simp [(hJx t).apply_unitaryFrame_unitaryFrame hg, hΦω])
    (fun t v ↦ by simp [(hJx t).apply_unitaryFrame hg, hΦ]) hnd

end CompatibleLoop

end TauCeti.SymplecticForm
