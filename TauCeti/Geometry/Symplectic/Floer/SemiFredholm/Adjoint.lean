/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Floer.SemiFredholm
public import TauCeti.Geometry.Symplectic.Floer.Linearization.Adjoint
import TauCeti.Geometry.Symplectic.Cayley.Tangent
import TauCeti.Geometry.Symplectic.Floer.SemiFredholm.CauchyRiemann
import TauCeti.Geometry.Symplectic.Floer.Sobolev.Density
import TauCeti.MeasureTheory.Integral.Rectangle
import TauCeti.Topology.Compactness.Normed

/-!
# The semi-Fredholm estimate of the formal adjoint of the linearized Floer operator

Let `D_u` be the linearized Floer operator along a map `u : ℝ × ℝ → V` into a finite-dimensional
symplectic vector space, and `D_u^*` its formal adjoint on covector fields
(`TauCeti.SymplecticForm.floerLinearizationAdjoint`),

`D_u^* η = -(∂s η + (∂t η) ∘ J(z, u z) + η ∘ A(z))`,  `A = ∂t J - C`

(`TauCeti.SymplecticForm.floerLinearizationAdjoint_eq_neg`). The cokernel of `D_u` is the kernel
of `D_u^*`, and the surjectivity of `D_u` behind regular moduli spaces and gluing is an
injectivity estimate for `D_u^*`, as in
`eventually_setIntegral_sobolev_le_mul_setIntegral_floerLinearizationAdjoint_preglue`. This file
proves the semi-Fredholm estimate for `D_u^*` on the cylinder:

`∫ (‖∂s η‖² + ‖∂t η‖² + ‖η‖²) ≤ C (∫ ‖D_u^* η‖² + ∫_{[-T, T] × [0, 1]} ‖η‖²)`

for `C²` covector fields `η` of period one in `t` vanishing outside a strip `(a, b) × ℝ`, with
the integrals over `[a, b] × [0, 1]`, whenever `u` is asymptotic at both ends to nondegenerate
orbits. It is the estimate of `TauCeti.Geometry.Symplectic.Floer.SemiFredholm` for `D_u^*`.

* **Reflection.** The leading term of `D_u^*` is `-∂s`. Precomposing with the reflection
  `ρ (s, t) = (-s, t)` and writing covectors through `ω`, `η (ρ w) = ω (ζ w, ·)`, turns `D_u^*`
  into the real Cauchy–Riemann operator `∂s ζ + J(ρ w, u (ρ w)) ∂t ζ - A(ρ w)ᵀ ζ` on vector fields,
  where `ᵀ` is the `ω`-transpose `TauCeti.SymplecticForm.leftAdjointL` and `ω♭` is
  `TauCeti.SymplecticForm.flatEquiv`. Its leading coefficient is again `ω`-compatible, and the
  reflection exchanges the two ends.
* **The limits.** At an end orbit `x`, with `j_t = J_t(x t)`, `S_t = dX_{H_t}(x t)` and
  `j' = d/dt j_t`, the coefficient `A` converges to `j' + j S`
  (`TauCeti.SymplecticForm.cylindricalAdjointCoeff` along `x`), so the reflected operator
  converges to the stationary cylinder operator `∂s + j (∂t - S'')` of the rotated field
  `S'' = j j' - j S j`. This field is infinitesimally symplectic, and `ξ ↦ j ξ` carries solutions
  of `ξ' = S ξ` to solutions of `ξ' = S'' ξ` (`TauCeti.dysonSeriesLeft_mul_sub_mul_mul_eq`). When
  `j` has period one, the return map of `S''` is conjugate to that of `S`
  (`TauCeti.det_one_sub_dysonSeriesLeft_mul_sub_mul_mul`), so it fixes no nonzero vector at a
  nondegenerate orbit.
* **The estimate.** The semi-Fredholm estimate of real Cauchy–Riemann operators with
  nondegenerate limits
  (`exists_forall_setIntegral_le_mul_setIntegral_cauchyRiemann_add_of_tendstoUniformlyOn`)
  then applies to the reflected operator, and the reflection and `ω` carry it back to `D_u^*`.

## Main results

In the namespace `TauCeti.SymplecticForm`:

* `exists_forall_setIntegral_le_mul_setIntegral_floerLinearizationAdjoint_add_of_cylindrical`:
  the estimate for Floer data that are cylindrical near the ends
  (`TauCeti.Floer.IsCylindricalNearEnds`), such as continuation data, with end structures of period
  one in `t`.
* `exists_forall_setIntegral_le_mul_setIntegral_floerLinearizationAdjoint_add`:
  the estimate along a Floer trajectory, for the datum `K = H_t dt`.

The Sobolev completion of `D_u^*`, the regularity of weak `L²` cokernel elements and the Fredholm
property are not treated here.

## References

* D. McDuff and D. Salamon, *J-holomorphic curves and symplectic topology*, 2nd ed., Section 3.1
  and Appendix C.1, on the formal adjoint of a real Cauchy–Riemann operator, which becomes an
  operator of the same type after the reflection `(s, t) ↦ (-s, t)`.
* D. Salamon, *Lectures on Floer homology*, in *Symplectic geometry and topology*, IAS/Park City
  Math. Ser. 7 (1999), Lecture 2, on the Fredholm property of `∂s + J ∂t + S(s, t)` with
  nondegenerate limits.
-/

public section

open Set Filter Function MeasureTheory Topology ContinuousLinearMap
open scoped NNReal Manifold

namespace TauCeti.SymplecticForm

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]

/-! ### The reflected adjoint -/

/-- The reflection `ρ (s, t) = (-s, t)` of the cylinder, as a linear map. -/
private noncomputable def reflectL : (ℝ × ℝ) →L[ℝ] ℝ × ℝ :=
  (-ContinuousLinearMap.fst ℝ ℝ ℝ).prod (ContinuousLinearMap.snd ℝ ℝ ℝ)

private theorem reflectL_apply (z : ℝ × ℝ) : reflectL z = (-z.1, z.2) := (rfl)

private theorem reflectL_stdComplexLineReal :
    reflectL stdComplexLineReal = -stdComplexLineReal := by
  simp [reflectL_apply, stdComplexLineReal]

private theorem reflectL_stdComplexLineImag :
    reflectL stdComplexLineImag = stdComplexLineImag := by
  simp [reflectL_apply, stdComplexLineImag]

/-- The derivative of the reflected vector field `ω♭⁻¹ ∘ η ∘ ρ` of a covector field `η`. -/
private theorem hasFDerivAt_flatEquiv_symm_comp_reflectL (ω : SymplecticForm V)
    {η : ℝ × ℝ → V →L[ℝ] ℝ} {z : ℝ × ℝ} (hη : DifferentiableAt ℝ η (reflectL z)) :
    HasFDerivAt (fun w ↦ ω.flatEquiv.symm (η (reflectL w)))
      ((ω.flatEquiv.symm : (V →L[ℝ] ℝ) →L[ℝ] V).comp ((fderiv ℝ η (reflectL z)).comp reflectL))
      z :=
  ω.flatEquiv.symm.hasFDerivAt.comp z (hη.hasFDerivAt.comp z reflectL.hasFDerivAt)

/-- **The reflected formal adjoint is a Cauchy–Riemann operator.** Let `J(z, u z)` preserve `ω`
at `ρ z`, for the reflection `ρ (s, t) = (-s, t)`. Write the covector field `η` through `ω` as the
reflected vector field `ζ (w) = ω♭⁻¹ (η (ρ w))`, where `ω♭ v = ω(v, ·)`. Then the formal adjoint
of the linearized Floer operator at `ρ z` is `ω♭` of

`∂s ζ + J(ρ z, u (ρ z)) ∂t ζ - A(ρ z)ᵀ ζ`

at `z`, where `A = ∂t J - C` is the zeroth-order coefficient of `floerLinearizationAdjoint_eq_neg`
and `ᵀ` is the `ω`-transpose. -/
private theorem floerLinearizationAdjoint_reflectL_eq (ω : SymplecticForm V)
    {J : ℝ × ℝ → V → AlmostComplexStructure V} {Ks Kt : ℝ × ℝ → V → ℝ} {u : ℝ × ℝ → V}
    {η : ℝ × ℝ → V →L[ℝ] ℝ} {z : ℝ × ℝ} (hη : DifferentiableAt ℝ η (reflectL z))
    (hJu : DifferentiableAt ℝ (fun w ↦ (J w (u w)).toLinearMap.toContinuousLinearMap)
      (reflectL z))
    (hc : ω.Invariant (J (reflectL z) (u (reflectL z)))) :
    ω.floerLinearizationAdjoint (fun w y ↦ (J w y).toLinearMap.toContinuousLinearMap) Ks Kt u η
        (reflectL z) =
      ω.flatEquiv (fderiv ℝ (fun w ↦ ω.flatEquiv.symm (η (reflectL w))) z stdComplexLineReal +
        J (reflectL z) (u (reflectL z))
          (fderiv ℝ (fun w ↦ ω.flatEquiv.symm (η (reflectL w))) z stdComplexLineImag) -
        ω.leftAdjointL (fderiv ℝ (fun w ↦ (J w (u w)).toLinearMap.toContinuousLinearMap)
            (reflectL z) stdComplexLineImag -
          ω.floerLinearizationCoeff (fun w y ↦ (J w y).toLinearMap.toContinuousLinearMap) Ks Kt u
            (reflectL z)) (ω.flatEquiv.symm (η (reflectL z)))) := by
  rw [floerLinearizationAdjoint_eq_neg hη hJu,
    (hasFDerivAt_flatEquiv_symm_comp_reflectL ω hη).fderiv]
  ext w
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe,
    reflectL_stdComplexLineReal, reflectL_stdComplexLineImag, map_neg, flatEquiv_apply, map_add,
    map_sub, apply_leftAdjointL_apply, apply_flatEquiv_symm_apply, neg_apply, add_apply, sub_apply,
    hc.apply_apply_eq_neg, LinearMap.coe_toContinuousLinearMap']
  ring

/-! ### The limit of the reflected adjoint at a nondegenerate orbit -/

section EndLoop

variable {ω : SymplecticForm V} {Je : ℝ → V → AlmostComplexStructure V} {He : ℝ → V → ℝ}
  {x : ℝ → V}

/-- The loop `t ↦ J_t(x(t))` of complex structures along a curve `x`, as linear maps. -/
private noncomputable def endLoop (Je : ℝ → V → AlmostComplexStructure V) (x : ℝ → V) (t : ℝ) :
    V →L[ℝ] V :=
  (Je t (x t)).toLinearMap.toContinuousLinearMap

/-- The derivative `D = d/dt J_t(x(t))` of `endLoop` along an orbit `x` of `X_{H_t}`. -/
private noncomputable def endLoopDeriv (ω : SymplecticForm V)
    (Je : ℝ → V → AlmostComplexStructure V) (He : ℝ → V → ℝ) (x : ℝ → V) (t : ℝ) : V →L[ℝ] V :=
  fderiv ℝ (fun p : ℝ × V ↦ (Je p.1 p.2).toLinearMap.toContinuousLinearMap) (t, x t)
    (1, ω.hamiltonianVectorField (He t) (x t))

/-- The rotated linearized Hamiltonian field `J D - J S J`, for `J = endLoop`,
`D = endLoopDeriv` and `S_t = dX_{H_t}(x(t))`: the limit of the reflected adjoint at the orbit is
the stationary cylinder operator of this field. -/
private noncomputable def rotatedField (ω : SymplecticForm V)
    (Je : ℝ → V → AlmostComplexStructure V) (He : ℝ → V → ℝ) (x : ℝ → V) (t : ℝ) : V →L[ℝ] V :=
  endLoop Je x t * endLoopDeriv ω Je He x t -
    endLoop Je x t * fderiv ℝ (ω.hamiltonianVectorField (He t)) (x t) * endLoop Je x t

private theorem endLoop_mul_self (t : ℝ) : endLoop Je x t * endLoop Je x t = -1 := by
  ext v
  simp [endLoop]

/-- Along an orbit where `J_t` is `ω`-compatible, the loop `j` is `ω`-skew. -/
private theorem apply_endLoop_apply (hJx : ∀ t, ω.Compatible (Je t (x t))) (t : ℝ) (a b : V) :
    ω (endLoop Je x t a) b = -ω a (endLoop Je x t b) := by
  simpa only [endLoop, LinearMap.coe_toContinuousLinearMap'] using
    (hJx t).invariant.apply_apply_eq_neg a b

/-- The linearized Hamiltonian field `S = dX_{H_t}(y)` is `ω`-skew. -/
private theorem apply_fderiv_hamiltonianVectorField_apply (hHe : ContDiff ℝ 2 (uncurry He))
    (t : ℝ) (y a b : V) :
    ω (fderiv ℝ (ω.hamiltonianVectorField (He t)) y a) b =
      -ω a (fderiv ℝ (ω.hamiltonianVectorField (He t)) y b) :=
  eq_neg_of_add_eq_zero_left (ω.apply_fderiv_hamiltonianVectorField_add
    ((hHe.comp ((contDiff_const (c := t)).prodMk contDiff_id)).contDiffAt) a b)

private theorem hasDerivAt_endLoop
    (hJe : ContDiff ℝ 1 fun p : ℝ × V ↦ (Je p.1 p.2).toLinearMap.toContinuousLinearMap)
    (hx : ∀ t, HasDerivAt x (ω.hamiltonianVectorField (He t) (x t)) t) (t : ℝ) :
    HasDerivAt (endLoop Je x) (endLoopDeriv ω Je He x t) t := by
  -- `endLoop` is the structure `(t, y) ↦ J_t(y)` along the curve `t ↦ (t, x t)`, whose velocity
  -- is `(1, X_{H_t}(x t))`, so the chain rule gives `endLoopDeriv`.
  unfold endLoop endLoopDeriv
  exact (hJe.differentiable one_ne_zero (t, x t)).hasFDerivAt.comp_hasDerivAt t
    ((hasDerivAt_id t).prodMk (hx t))

private theorem continuous_endLoopDeriv (hHe : ContDiff ℝ 2 (uncurry He))
    (hJe : ContDiff ℝ 1 fun p : ℝ × V ↦ (Je p.1 p.2).toLinearMap.toContinuousLinearMap)
    (hx : Continuous x) : Continuous (endLoopDeriv ω Je He x) :=
  ((hJe.continuous_fderiv one_ne_zero).comp (continuous_id.prodMk hx)).clm_apply
    (continuous_const.prodMk
      ((ω.contDiff_hamiltonianVectorField_uncurry (n := 1) hHe).continuous.comp
        (continuous_id.prodMk hx)))

/-- The derivative `D` of a loop `j` of `ω`-compatible structures lies in the compatible tangent
space: `D j = -j D` and `D` is `ω`-skew. -/
private theorem endLoopDeriv_endLoop_apply_and_apply_endLoopDeriv_add
    (hJe : ContDiff ℝ 1 fun p : ℝ × V ↦ (Je p.1 p.2).toLinearMap.toContinuousLinearMap)
    (hx : ∀ t, HasDerivAt x (ω.hamiltonianVectorField (He t) (x t)) t)
    (hJx : ∀ t, ω.Compatible (Je t (x t))) (t : ℝ) :
    (∀ a, endLoopDeriv ω Je He x t (endLoop Je x t a) =
        -endLoop Je x t (endLoopDeriv ω Je He x t a)) ∧
      ∀ a b, ω (endLoopDeriv ω Je He x t a) b + ω a (endLoopDeriv ω Je He x t b) = 0 := by
  have h := mem_compatibleTangentSpace.1 <| ω.mem_compatibleTangentSpace_of_hasFDerivAt
    (J := fun s ↦ Je s (x s)) (Eventually.of_forall fun s ↦ (hJx s).invariant)
    (hasDerivAt_endLoop hJe hx t).hasFDerivAt 1
  simpa [endLoop] using h

/-- `rotatedField` is infinitesimally symplectic. -/
private theorem apply_rotatedField_add
    (hJe : ContDiff ℝ 1 fun p : ℝ × V ↦ (Je p.1 p.2).toLinearMap.toContinuousLinearMap)
    (hHe : ContDiff ℝ 2 (uncurry He))
    (hx : ∀ t, HasDerivAt x (ω.hamiltonianVectorField (He t) (x t)) t)
    (hJx : ∀ t, ω.Compatible (Je t (x t))) (t : ℝ) (v w : V) :
    ω (rotatedField ω Je He x t v) w + ω v (rotatedField ω Je He x t w) = 0 := by
  simp only [rotatedField, sub_apply, mul_apply_eq_comp, map_sub, LinearMap.sub_apply]
  have hj := apply_endLoop_apply hJx t
  have hS := apply_fderiv_hamiltonianVectorField_apply (ω := ω) hHe t (x t)
  obtain ⟨e₁, hD⟩ := endLoopDeriv_endLoop_apply_and_apply_endLoopDeriv_add hJe hx hJx t
  set j := endLoop Je x t
  set D := endLoopDeriv ω Je He x t
  set S := fderiv ℝ (ω.hamiltonianVectorField (He t)) (x t)
  have e₂ : ω v (D (j w)) = -ω v (j (D w)) := by
    beta_reduce
    rw [e₁, map_neg]
  linarith [hj (D v) w, hD v (j w), hj (S (j v)) w, hS (j v) (j w), hj v (S (j w))]

/-- Along the orbit, `cylindricalAdjointCoeff (t, x t, X_{H_t}(x t))` is `D + j S`: its term in
the slice defect `∂t u - X_{H_t}(u)` vanishes there. -/
private theorem cylindricalAdjointCoeff_eq_endLoopDeriv_add (t : ℝ) :
    ω.cylindricalAdjointCoeff (fun t y ↦ (Je t y).toLinearMap.toContinuousLinearMap) He
      (t, x t, ω.hamiltonianVectorField (He t) (x t)) =
        endLoopDeriv ω Je He x t +
          endLoop Je x t * fderiv ℝ (ω.hamiltonianVectorField (He t)) (x t) := by
  rw [cylindricalAdjointCoeff_def, sub_self, map_zero, zero_sub, sub_neg_eq_add, endLoopDeriv,
    endLoop, mul_def, uncurry_def]

/-- The `ω`-transpose of the limit `A(t, x t, X_{H_t}(x t)) = D + j S` of the zeroth-order
coefficient of the formal adjoint is `j * rotatedField`. -/
private theorem leftAdjointL_cylindricalAdjointCoeff
    (hJe : ContDiff ℝ 1 fun p : ℝ × V ↦ (Je p.1 p.2).toLinearMap.toContinuousLinearMap)
    (hHe : ContDiff ℝ 2 (uncurry He))
    (hx : ∀ t, HasDerivAt x (ω.hamiltonianVectorField (He t) (x t)) t)
    (hJx : ∀ t, ω.Compatible (Je t (x t))) (t : ℝ) :
    ω.leftAdjointL (ω.cylindricalAdjointCoeff
        (fun t y ↦ (Je t y).toLinearMap.toContinuousLinearMap) He
        (t, x t, ω.hamiltonianVectorField (He t) (x t))) =
      endLoop Je x t * rotatedField ω Je He x t := by
  refine ω.continuousLinearMap_ext_of_apply_eq fun v w ↦ ?_
  rw [cylindricalAdjointCoeff_eq_endLoopDeriv_add, apply_leftAdjointL_apply]
  simp only [rotatedField, mul_apply_eq_comp, add_apply, sub_apply, map_add, map_sub,
    LinearMap.sub_apply]
  have hj := apply_endLoop_apply hJx t
  have hS := apply_fderiv_hamiltonianVectorField_apply (ω := ω) hHe t (x t)
  have hD := (endLoopDeriv_endLoop_apply_and_apply_endLoopDeriv_add hJe hx hJx t).2 v w
  have hjj (a : V) : endLoop Je x t (endLoop Je x t a) = -a := by
    simpa using congrArg (· a) (endLoop_mul_self (Je := Je) (x := x) t)
  rw [hjj, hjj, map_neg, map_neg, LinearMap.neg_apply, LinearMap.neg_apply]
  set j := endLoop Je x t
  set S := fderiv ℝ (ω.hamiltonianVectorField (He t)) (x t)
  linarith [hj v (S w), hS (j v) w]

private theorem continuous_rotatedField (hHe : ContDiff ℝ 2 (uncurry He))
    (hJe : ContDiff ℝ 1 fun p : ℝ × V ↦ (Je p.1 p.2).toLinearMap.toContinuousLinearMap)
    (hx : Continuous x) : Continuous (rotatedField ω Je He x) := by
  have hj : Continuous (endLoop Je x) := hJe.continuous.comp (continuous_id.prodMk hx)
  exact (hj.mul (continuous_endLoopDeriv hHe hJe hx)).sub
    ((hj.mul (ω.continuous_fderiv_hamiltonianVectorField_comp hHe hx)).mul hj)

/-- At a nondegenerate orbit `x`, the return map of the rotated field fixes no nonzero vector,
for a structure `J_t` of period one. -/
private theorem det_one_sub_dysonSeriesLeft_rotatedField_ne_zero {K : ℝ≥0}
    (hX : LipschitzWith K (ω.timeDependentHamiltonianSuspension He))
    (hHe : ContDiff ℝ 2 (uncurry He))
    (hx : ∀ t, HasDerivAt x (ω.hamiltonianVectorField (He t) (x t)) t)
    (hnd : IsNondegenerateFixedPt 𝓘(ℝ, V) (ω.timeDependentHamiltonianFlow He hX 0 1) (x 0))
    (hJe : ContDiff ℝ 1 fun p : ℝ × V ↦ (Je p.1 p.2).toLinearMap.toContinuousLinearMap)
    (hJe1 : Je 1 = Je 0) :
    LinearMap.det ((1 - dysonSeriesLeft (rotatedField ω Je He x) 1 : V →L[ℝ] V) :
      V →ₗ[ℝ] V) ≠ 0 := by
  have hxc : Continuous x := continuous_iff_continuousAt.2 fun t ↦ (hx t).continuousAt
  have hx1 : x 1 = x 0 := (ω.eq_timeDependentHamiltonianFlow He hX hx 0 1).trans
    (isNondegenerateFixedPt_iff.1 hnd).1
  unfold rotatedField
  rw [det_one_sub_dysonSeriesLeft_mul_sub_mul_mul (hasDerivAt_endLoop hJe hx) endLoop_mul_self
    (continuous_endLoopDeriv hHe hJe hxc) (ω.continuous_fderiv_hamiltonianVectorField_comp hHe hxc)
    (by simp [endLoop, hx1, hJe1])]
  exact ω.det_one_sub_dysonSeriesLeft_ne_zero_of_isNondegenerateFixedPt hX hHe hx hnd

/-- **The coefficients of the adjoint near an orbit.** Along a filter `l` of slices on which the
loops of `u` converge uniformly to an orbit `x` and the slice defect tends uniformly to zero,
the structures `J_t(u)` and the coefficients `cylindricalAdjointCoeff (t, u, ∂t u)` converge
uniformly for `t ∈ [0, 1]` to their values along `x`. -/
private theorem eventually_norm_sub_le_of_tendstoUniformlyOn (hHe : ContDiff ℝ 2 (uncurry He))
    (hJe : ContDiff ℝ 1 fun p : ℝ × V ↦ (Je p.1 p.2).toLinearMap.toContinuousLinearMap)
    (hx : Continuous x) {l : Filter ℝ} {u : ℝ × ℝ → V}
    (hux : TendstoUniformlyOn (fun s t ↦ u (s, t)) x l (Icc 0 1))
    (hδ : TendstoUniformlyOn
      (fun s t ↦ sliceDefect (fun t ↦ ω.hamiltonianVectorField (He t)) u (s, t)) 0 l (Icc 0 1))
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ s in l, ∀ t ∈ Icc (0 : ℝ) 1,
      ‖(Je t (u (s, t))).toLinearMap.toContinuousLinearMap - endLoop Je x t‖ ≤ ε ∧
      ‖ω.cylindricalAdjointCoeff (fun t y ↦ (Je t y).toLinearMap.toContinuousLinearMap) He
          (t, u (s, t), fderiv ℝ u (s, t) stdComplexLineImag) -
        ω.cylindricalAdjointCoeff (fun t y ↦ (Je t y).toLinearMap.toContinuousLinearMap) He
          (t, x t, ω.hamiltonianVectorField (He t) (x t))‖ ≤ ε := by
  obtain ⟨δ, hδ0, hnear⟩ := ω.exists_pos_forall_norm_cylindricalAdjointCoeff_sub_le
    (J := fun t y ↦ (Je t y).toLinearMap.toContinuousLinearMap) hJe hHe hx hε
  have hXc : Continuous fun p : ℝ × V ↦ ω.hamiltonianVectorField (He p.1) p.2 :=
    (ω.contDiff_hamiltonianVectorField_uncurry (n := 1) hHe).continuous
  obtain ⟨δ', hδ'0, hX⟩ := (isCompact_Icc (a := (0 : ℝ)) (b := 1)).exists_pos_forall_norm_sub_le
    hx.continuousOn (fun _ _ ↦ hXc.continuousAt) (half_pos hδ0)
  filter_upwards [Metric.tendstoUniformlyOn_iff.1 hux (min δ δ') (lt_min hδ0 hδ'0),
    Metric.tendstoUniformlyOn_iff.1 hδ (δ / 2) (half_pos hδ0)] with s hs₁ hs₂ t ht
  have hu₀ : ‖u (s, t) - x t‖ ≤ min δ δ' := by
    rw [← dist_eq_norm, dist_comm]
    exact (hs₁ t ht).le
  have hd : ‖sliceDefect (fun t ↦ ω.hamiltonianVectorField (He t)) u (s, t)‖ ≤ δ / 2 := by
    simpa using (hs₂ t ht).le
  have hdu : fderiv ℝ u (s, t) stdComplexLineImag - ω.hamiltonianVectorField (He t) (x t) =
      sliceDefect (fun t ↦ ω.hamiltonianVectorField (He t)) u (s, t) +
        (ω.hamiltonianVectorField (He t) (u (s, t)) -
          ω.hamiltonianVectorField (He t) (x t)) := by
    rw [sliceDefect_def]
    simp [stdComplexLineImag]
  have hq : ‖(u (s, t), fderiv ℝ u (s, t) stdComplexLineImag) -
      (x t, ω.hamiltonianVectorField (He t) (x t))‖ ≤ δ := by
    refine norm_prod_le_iff.2 ⟨hu₀.trans (min_le_left _ _), ?_⟩
    rw [Prod.snd_sub, hdu]
    refine (norm_add_le _ _).trans ?_
    linarith [hX t ht (u (s, t)) (hu₀.trans (min_le_right _ _))]
  have h₀ : ‖(x t, ω.hamiltonianVectorField (He t) (x t)) -
      (x t, ω.hamiltonianVectorField (He t) (x t))‖ ≤ δ := by
    rw [sub_self, norm_zero]
    exact hδ0.le
  exact hnear t ht (u (s, t), fderiv ℝ u (s, t) stdComplexLineImag)
    (x t, ω.hamiltonianVectorField (He t) (x t)) hq h₀

end EndLoop

/-! ### Transferring the estimate through `ω` and the reflection -/

/-- The reflection `ρ` carries `[-b, -a] × [0, 1]` onto `[a, b] × [0, 1]`, preserving
integrals. -/
private theorem setIntegral_comp_reflectL (g : ℝ × ℝ → ℝ) (a b : ℝ) :
    ∫ z in Icc (-b) (-a) ×ˢ Icc (0 : ℝ) 1, g (reflectL z) =
      ∫ z in Icc a b ×ˢ Icc (0 : ℝ) 1, g z := by
  simpa [reflectL_apply] using (setIntegral_Icc_neg_prod_eq g (-b) (-a) (Icc 0 1)).symm

/-- Pointwise, the `W^{1,2}` density of a covector field `η` at `ρ w` is at most `‖ω♭‖²` times
that of the reflected vector field `ζ = ω♭⁻¹ ∘ η ∘ ρ` at `w`. -/
private theorem sobolev_reflectL_le (ω : SymplecticForm V) {η : ℝ × ℝ → V →L[ℝ] ℝ}
    (hη : Differentiable ℝ η) (w : ℝ × ℝ) :
    ‖fderiv ℝ η (reflectL w) stdComplexLineReal‖ ^ 2 +
        ‖fderiv ℝ η (reflectL w) stdComplexLineImag‖ ^ 2 + ‖η (reflectL w)‖ ^ 2 ≤
      ‖(ω.flatEquiv : V →L[ℝ] (V →L[ℝ] ℝ))‖ ^ 2 *
        (‖fderiv ℝ (fun w ↦ ω.flatEquiv.symm (η (reflectL w))) w stdComplexLineReal‖ ^ 2 +
          ‖fderiv ℝ (fun w ↦ ω.flatEquiv.symm (η (reflectL w))) w stdComplexLineImag‖ ^ 2 +
          ‖ω.flatEquiv.symm (η (reflectL w))‖ ^ 2) := by
  set c := ‖(ω.flatEquiv : V →L[ℝ] (V →L[ℝ] ℝ))‖
  have hb (φ : V →L[ℝ] ℝ) : ‖φ‖ ^ 2 ≤ c ^ 2 * ‖ω.flatEquiv.symm φ‖ ^ 2 := by
    rw [← mul_pow]
    refine pow_le_pow_left₀ (norm_nonneg _) ?_ 2
    simpa using (ω.flatEquiv : V →L[ℝ] (V →L[ℝ] ℝ)).le_opNorm (ω.flatEquiv.symm φ)
  rw [(hasFDerivAt_flatEquiv_symm_comp_reflectL ω (hη (reflectL w))).fderiv]
  simp only [ContinuousLinearMap.comp_apply, reflectL_stdComplexLineReal,
    reflectL_stdComplexLineImag, map_neg, norm_neg, mul_add]
  gcongr <;> exact hb _

/-- `‖ω♭⁻¹ φ‖² ≤ ‖ω♭⁻¹‖² ‖φ‖²`. -/
private theorem norm_flatEquiv_symm_sq_le (ω : SymplecticForm V) (φ : V →L[ℝ] ℝ) :
    ‖ω.flatEquiv.symm φ‖ ^ 2 ≤ ‖(ω.flatEquiv.symm : (V →L[ℝ] ℝ) →L[ℝ] V)‖ ^ 2 * ‖φ‖ ^ 2 := by
  rw [← mul_pow]
  exact pow_le_pow_left₀ (norm_nonneg _) ((ω.flatEquiv.symm : _ →L[ℝ] V).le_opNorm φ) 2

/-- **Transferring the estimate.** Let `P ζ = ∂s ζ + Jr ∂t ζ + Ar ζ` satisfy the semi-Fredholm
estimate with error region `[-T, T] × [0, 1]`, and let `D` be an operator on covector fields such
that, for every `C²` field `η`, `D η` is continuous and `D η (ρ z) = ω♭ (P ζ z)` for the reflected
vector field `ζ = ω♭⁻¹ ∘ η ∘ ρ`. Then `D` satisfies the semi-Fredholm estimate with the same error
region. -/
private theorem exists_forall_setIntegral_le_of_flatEquiv_reflectL (ω : SymplecticForm V)
    {Jr : ℝ × ℝ → AlmostComplexStructure V} {Ar : ℝ × ℝ → V →L[ℝ] V}
    (hJr : Continuous fun z ↦ (Jr z).toLinearMap.toContinuousLinearMap) (hAr : Continuous Ar)
    {D : (ℝ × ℝ → V →L[ℝ] ℝ) → ℝ × ℝ → V →L[ℝ] ℝ}
    (hDc : ∀ ⦃η : ℝ × ℝ → V →L[ℝ] ℝ⦄, ContDiff ℝ 2 η → Continuous (D η))
    (hD : ∀ ⦃η : ℝ × ℝ → V →L[ℝ] ℝ⦄, ContDiff ℝ 2 η → ∀ z, D η (reflectL z) = ω.flatEquiv
      (fderiv ℝ (fun w ↦ ω.flatEquiv.symm (η (reflectL w))) z stdComplexLineReal +
        Jr z (fderiv ℝ (fun w ↦ ω.flatEquiv.symm (η (reflectL w))) z stdComplexLineImag) +
        Ar z (ω.flatEquiv.symm (η (reflectL z)))))
    {C₀ T : ℝ} (hC₀ : 0 ≤ C₀)
    (hest : ∀ ⦃ξ : ℝ × ℝ → V⦄, ContDiff ℝ 2 ξ → (∀ s t, ξ (s, t + 1) = ξ (s, t)) →
      ∀ ⦃a b : ℝ⦄, a ≤ b → (∀ s t, s ∉ Ioo a b → ξ (s, t) = 0) →
        ∫ z in Icc a b ×ˢ Icc (0 : ℝ) 1, (‖fderiv ℝ ξ z stdComplexLineReal‖ ^ 2 +
            ‖fderiv ℝ ξ z stdComplexLineImag‖ ^ 2 + ‖ξ z‖ ^ 2) ≤
          C₀ * ((∫ z in Icc a b ×ˢ Icc (0 : ℝ) 1, ‖fderiv ℝ ξ z stdComplexLineReal +
            Jr z (fderiv ℝ ξ z stdComplexLineImag) + Ar z (ξ z)‖ ^ 2) +
            ∫ z in Icc (-T) T ×ˢ Icc (0 : ℝ) 1, ‖ξ z‖ ^ 2)) :
    ∃ C, 0 ≤ C ∧ ∀ ⦃η : ℝ × ℝ → V →L[ℝ] ℝ⦄, ContDiff ℝ 2 η →
      (∀ s t, η (s, t + 1) = η (s, t)) → ∀ ⦃a b : ℝ⦄, a ≤ b →
      (∀ s t, s ∉ Ioo a b → η (s, t) = 0) →
        ∫ z in Icc a b ×ˢ Icc (0 : ℝ) 1, (‖fderiv ℝ η z stdComplexLineReal‖ ^ 2 +
            ‖fderiv ℝ η z stdComplexLineImag‖ ^ 2 + ‖η z‖ ^ 2) ≤
          C * ((∫ z in Icc a b ×ˢ Icc (0 : ℝ) 1, ‖D η z‖ ^ 2) +
            ∫ z in Icc (-T) T ×ˢ Icc (0 : ℝ) 1, ‖η z‖ ^ 2) := by
  set c₁ := ‖(ω.flatEquiv : V →L[ℝ] (V →L[ℝ] ℝ))‖
  set c₂ := ‖(ω.flatEquiv.symm : (V →L[ℝ] ℝ) →L[ℝ] V)‖
  refine ⟨c₁ ^ 2 * C₀ * c₂ ^ 2, by positivity, fun η hη hper a b hab hη₀ ↦ ?_⟩
  set ζ : ℝ × ℝ → V := fun w ↦ ω.flatEquiv.symm (η (reflectL w))
  have hζ : ContDiff ℝ 2 ζ := ω.flatEquiv.symm.contDiff.comp (hη.comp reflectL.contDiff)
  have hζ₀ (s t : ℝ) (hs : s ∉ Ioo (-b) (-a)) : ζ (s, t) = 0 := by
    have : -s ∉ Ioo a b := fun h ↦ hs ⟨by linarith [h.2], by linarith [h.1]⟩
    simp [ζ, reflectL_apply, hη₀ _ t this]
  have hb := ω.norm_flatEquiv_symm_sq_le
  have hP (w : ℝ × ℝ) : ‖fderiv ℝ ζ w stdComplexLineReal + Jr w (fderiv ℝ ζ w stdComplexLineImag) +
      Ar w (ζ w)‖ ^ 2 ≤ c₂ ^ 2 * ‖D η (reflectL w)‖ ^ 2 := by
    rw [← ContinuousLinearEquiv.symm_apply_apply ω.flatEquiv (_ + _), ← hD hη w]
    exact hb _
  have hm : MeasurableSet (Icc (-b) (-a) ×ˢ Icc (0 : ℝ) 1) :=
    measurableSet_Icc.prod measurableSet_Icc
  have hmT : MeasurableSet (Icc (-T) T ×ˢ Icc (0 : ℝ) 1) :=
    measurableSet_Icc.prod measurableSet_Icc
  have hηc := hη.continuous.comp reflectL.continuous
  have hDρ := (hDc hη).comp reflectL.continuous
  have hTr := setIntegral_comp_reflectL (fun z ↦ ‖η z‖ ^ 2) (-T) T
  rw [neg_neg] at hTr
  calc _ = ∫ w in Icc (-b) (-a) ×ˢ Icc (0 : ℝ) 1,
          (‖fderiv ℝ η (reflectL w) stdComplexLineReal‖ ^ 2 +
            ‖fderiv ℝ η (reflectL w) stdComplexLineImag‖ ^ 2 + ‖η (reflectL w)‖ ^ 2) :=
        (setIntegral_comp_reflectL _ a b).symm
    _ ≤ ∫ w in Icc (-b) (-a) ×ˢ Icc (0 : ℝ) 1, c₁ ^ 2 * (‖fderiv ℝ ζ w stdComplexLineReal‖ ^ 2 +
          ‖fderiv ℝ ζ w stdComplexLineImag‖ ^ 2 + ‖ζ w‖ ^ 2) :=
        setIntegral_mono_on
          ((Floer.continuous_sobolev (hη.of_le one_le_two)).comp
            reflectL.continuous).integrableOn_Icc_prod_Icc
          (continuous_const.mul (Floer.continuous_sobolev
            (hζ.of_le one_le_two))).integrableOn_Icc_prod_Icc hm
          fun w _ ↦ sobolev_reflectL_le ω (hη.differentiable (by norm_num)) w
    _ ≤ c₁ ^ 2 * (C₀ * ((∫ w in Icc (-b) (-a) ×ˢ Icc (0 : ℝ) 1,
          c₂ ^ 2 * ‖D η (reflectL w)‖ ^ 2) +
          ∫ w in Icc (-T) T ×ˢ Icc (0 : ℝ) 1, c₂ ^ 2 * ‖η (reflectL w)‖ ^ 2)) := by
      rw [integral_const_mul]
      refine mul_le_mul_of_nonneg_left ((hest hζ (fun s t ↦ by simp [ζ, reflectL_apply, hper])
        (neg_le_neg hab) hζ₀).trans (mul_le_mul_of_nonneg_left (add_le_add ?_ ?_) hC₀))
        (sq_nonneg _)
      · exact setIntegral_mono_on ((continuous_cauchyRiemann hJr hAr
          (hζ.of_le one_le_two)).norm.pow 2).integrableOn_Icc_prod_Icc
          (continuous_const.mul (hDρ.norm.pow 2)).integrableOn_Icc_prod_Icc hm fun w _ ↦ hP w
      · exact setIntegral_mono_on (hζ.continuous.norm.pow 2).integrableOn_Icc_prod_Icc
          (continuous_const.mul (hηc.norm.pow 2)).integrableOn_Icc_prod_Icc hmT
          fun w _ ↦ hb (η (reflectL w))
    _ = _ := by
      rw [integral_const_mul, integral_const_mul,
        setIntegral_comp_reflectL (fun z ↦ ‖D η z‖ ^ 2) a b, hTr]
      ring

/-! ### The coefficients of the reflected adjoint at the ends -/

/-- Where the data agree near `z` with the cylindrical datum `(Je_t, 0, He_t)`, the zeroth-order
coefficient `∂t J - C` of the formal adjoint at `z` is `cylindricalAdjointCoeff`. -/
private theorem fderiv_sub_floerLinearizationCoeff_eq_of_eventuallyEq (ω : SymplecticForm V)
    {J : ℝ × ℝ → V → AlmostComplexStructure V} {Ks Kt : ℝ × ℝ → V → ℝ}
    {Je : ℝ → V → AlmostComplexStructure V} {He : ℝ → V → ℝ} {u : ℝ × ℝ → V} {z : ℝ × ℝ}
    (hJe : Differentiable ℝ fun p : ℝ × V ↦ (Je p.1 p.2).toLinearMap.toContinuousLinearMap)
    (hu : DifferentiableAt ℝ u z)
    (h : ∀ᶠ w in 𝓝 z, J w = Je w.2 ∧ Ks w = 0 ∧ Kt w = He w.2) :
    fderiv ℝ (fun w ↦ (J w (u w)).toLinearMap.toContinuousLinearMap) z stdComplexLineImag -
        ω.floerLinearizationCoeff (fun w y ↦ (J w y).toLinearMap.toContinuousLinearMap) Ks Kt u
          z =
      ω.cylindricalAdjointCoeff (fun t y ↦ (Je t y).toLinearMap.toContinuousLinearMap) He
        (z.2, u z, fderiv ℝ u z stdComplexLineImag) := by
  obtain ⟨hJz, hKs, hKt⟩ := h.self_of_nhds
  have hJev : (fun w ↦ (J w (u w)).toLinearMap.toContinuousLinearMap) =ᶠ[𝓝 z]
      fun w ↦ (Je w.2 (u w)).toLinearMap.toContinuousLinearMap :=
    h.mono fun w hw ↦ by simp only [hw.1]
  have hC : ω.floerLinearizationCoeff (fun w y ↦ (J w y).toLinearMap.toContinuousLinearMap) Ks
      Kt u z = ω.floerLinearizationCoeff (fun w y ↦ (Je w.2 y).toLinearMap.toContinuousLinearMap)
        (fun _ _ ↦ 0) (fun w ↦ He w.2) u z := by
    ext v
    simp [floerLinearizationCoeff_apply, hJz, hKs, hKt, Pi.zero_def]
  rw [hJev.fderiv_eq, hC]
  exact ω.fderiv_sub_floerLinearizationCoeff_eq_cylindricalAdjointCoeff
    (J := fun t y ↦ (Je t y).toLinearMap.toContinuousLinearMap) (H := He) hJe hu

/-- **The reflected coefficients at an end.** Let the data agree, near the points `(s, t)` for `s`
eventually along `l`, with a cylindrical datum `(Je_t, 0, He_t)`, and let the loops of `u`
converge uniformly to an orbit `x` along `l` with vanishing slice defect. Along a filter `l'` sent
to `l` by `s ↦ -s`, the coefficients `J(ρ z, u (ρ z))` and `-A(ρ z)ᵀ` of the reflected adjoint
at `z = (s, t)` converge uniformly for `t ∈ [0, 1]` to `j_t = J_t(x t)` and `-j_t S''_t`, for the
rotated field `S''`. -/
private theorem tendstoUniformlyOn_reflectL (ω : SymplecticForm V)
    {J : ℝ × ℝ → V → AlmostComplexStructure V} {Ks Kt : ℝ × ℝ → V → ℝ}
    {Je : ℝ → V → AlmostComplexStructure V} {He : ℝ → V → ℝ} {x : ℝ → V} {u : ℝ × ℝ → V}
    (hJe : ContDiff ℝ 1 fun p : ℝ × V ↦ (Je p.1 p.2).toLinearMap.toContinuousLinearMap)
    (hHe : ContDiff ℝ 2 (uncurry He))
    (hx : ∀ t, HasDerivAt x (ω.hamiltonianVectorField (He t) (x t)) t)
    (hJx : ∀ t, ω.Compatible (Je t (x t))) (hu : Differentiable ℝ u) {l l' : Filter ℝ}
    (hl : Tendsto Neg.neg l' l)
    (hagree : ∀ᶠ s in l, ∀ t, ∀ᶠ w in 𝓝 (s, t), J w = Je w.2 ∧ Ks w = 0 ∧ Kt w = He w.2)
    (hux : TendstoUniformlyOn (fun s t ↦ u (s, t)) x l (Icc 0 1))
    (hδ : TendstoUniformlyOn
      (fun s t ↦ sliceDefect (fun t ↦ ω.hamiltonianVectorField (He t)) u (s, t)) 0 l (Icc 0 1)) :
    TendstoUniformlyOn
        (fun s t ↦ (J (reflectL (s, t)) (u (reflectL (s, t)))).toLinearMap.toContinuousLinearMap)
        (fun t ↦ (Je t (x t)).toLinearMap.toContinuousLinearMap) l' (Icc 0 1) ∧
      TendstoUniformlyOn (fun s t ↦ -ω.leftAdjointL
          (fderiv ℝ (fun w ↦ (J w (u w)).toLinearMap.toContinuousLinearMap) (reflectL (s, t))
              stdComplexLineImag -
            ω.floerLinearizationCoeff (fun w y ↦ (J w y).toLinearMap.toContinuousLinearMap) Ks Kt
              u (reflectL (s, t))))
        (fun t ↦ -((Je t (x t)).toLinearMap.toContinuousLinearMap ∘L rotatedField ω Je He x t))
        l' (Icc 0 1) := by
  have hxc : Continuous x := continuous_iff_continuousAt.2 fun t ↦ (hx t).continuousAt
  set c := ‖ω.leftAdjointL‖ + 1
  have hc : 0 < c := by positivity
  have hc1 : 1 ≤ c := by simp only [c]; linarith [norm_nonneg ω.leftAdjointL]
  have hev (ε : ℝ) (hε : 0 < ε) := hl.eventually
    ((eventually_norm_sub_le_of_tendstoUniformlyOn hHe hJe hxc hux hδ
      (ε := ε / (2 * c)) (by positivity)).and hagree)
  have hεc (ε : ℝ) (hε : 0 < ε) : c * (ε / (2 * c)) < ε := by
    have h : c * (ε / (2 * c)) = ε / 2 := by field_simp
    linarith
  have hεc' (ε : ℝ) (hε : 0 < ε) : ε / (2 * c) < ε :=
    lt_of_le_of_lt (le_mul_of_one_le_left (by positivity) hc1) (hεc ε hε)
  constructor <;> refine Metric.tendstoUniformlyOn_iff.2 fun ε hε ↦ (hev ε hε).mono
    fun s ⟨hs, hag⟩ t ht ↦ ?_ <;> rw [dist_comm, dist_eq_norm] <;>
    simp only [reflectL_apply] at hs hag ⊢
  · rw [(hag t).self_of_nhds.1]
    exact ((hs t ht).1).trans_lt (hεc' ε hε)
  · have hB := leftAdjointL_cylindricalAdjointCoeff hJe hHe hx hJx t
    simp only [endLoop] at hB
    rw [fderiv_sub_floerLinearizationCoeff_eq_of_eventuallyEq ω (hJe.differentiable one_ne_zero)
      (hu _) (hag t), ← mul_def, ← hB, neg_sub_neg, ← map_sub]
    refine (le_opNorm _ _).trans_lt (lt_of_le_of_lt ?_ (hεc ε hε))
    exact mul_le_mul (by simp only [c]; linarith)
      (by rw [norm_sub_rev]; exact (hs t ht).2) (norm_nonneg _) hc.le

/-! ### Data cylindrical near the ends -/

section Cylindrical

variable {J : ℝ × ℝ → V → AlmostComplexStructure V} {Ks Kt : ℝ × ℝ → V → ℝ}
  {Hm Hp : ℝ → V → ℝ} {Jm Jp : ℝ → V → AlmostComplexStructure V} {R : ℝ} {u : ℝ × ℝ → V}

private theorem contDiff_almostComplex_of_isCylindricalNearEnds
    (hcyl : Floer.IsCylindricalNearEnds J Ks Kt Jm Jp Hm Hp R u) (hu : ContDiff ℝ 1 u) :
    ContDiff ℝ 1 fun w ↦ (J w (u w)).toLinearMap.toContinuousLinearMap :=
  contDiff_iff_contDiffAt.2 fun z ↦ (hcyl.contDiffAt_almostComplex z).comp
    (f := fun w ↦ (w, u w)) z (contDiffAt_id.prodMk hu.contDiffAt)

/-- The zeroth-order coefficient `A = ∂t J - C` of the formal adjoint is continuous. -/
private theorem continuous_adjointCoeff_of_isCylindricalNearEnds (ω : SymplecticForm V)
    (hcyl : Floer.IsCylindricalNearEnds J Ks Kt Jm Jp Hm Hp R u) (hu : ContDiff ℝ 1 u) :
    Continuous fun z ↦ fderiv ℝ (fun w ↦ (J w (u w)).toLinearMap.toContinuousLinearMap)
      z stdComplexLineImag -
        ω.floerLinearizationCoeff (fun w y ↦ (J w y).toLinearMap.toContinuousLinearMap) Ks Kt u z :=
  (((contDiff_almostComplex_of_isCylindricalNearEnds hcyl hu).continuous_fderiv
    one_ne_zero).clm_apply continuous_const).sub
      (continuousOn_univ.1 (ω.continuousOn_floerLinearizationCoeff
        (fun z _ ↦ hcyl.contDiffAt_almostComplex z) (fun z _ ↦ hcyl.contDiffAt_hamiltonianS z)
        (fun z _ ↦ hcyl.contDiffAt_hamiltonianT z) fun _ _ ↦ hu.contDiffAt))

/-- Beyond `R`, the data agree near every point with the data of the positive end. -/
private theorem eventually_atTop_of_isCylindricalNearEnds
    (hcyl : Floer.IsCylindricalNearEnds J Ks Kt Jm Jp Hm Hp R u) :
    ∀ᶠ s in atTop, ∀ t, ∀ᶠ w in 𝓝 (s, t), J w = Jp w.2 ∧ Ks w = 0 ∧ Kt w = Hp w.2 := by
  filter_upwards [eventually_gt_atTop R] with s hs t
  filter_upwards [(isOpen_lt continuous_const continuous_fst).mem_nhds
    (show R < (s, t).1 from hs)] with w hw
  exact ⟨hcyl.almostComplex_eq_of_le w hw.le,
    hcyl.hamiltonianS_eq_zero w fun h ↦ h.2.not_ge hw.le, hcyl.hamiltonianT_eq_of_le w hw.le⟩

/-- Below `-R`, the data agree near every point with the data of the negative end. -/
private theorem eventually_atBot_of_isCylindricalNearEnds
    (hcyl : Floer.IsCylindricalNearEnds J Ks Kt Jm Jp Hm Hp R u) :
    ∀ᶠ s in atBot, ∀ t, ∀ᶠ w in 𝓝 (s, t), J w = Jm w.2 ∧ Ks w = 0 ∧ Kt w = Hm w.2 := by
  filter_upwards [eventually_lt_atBot (-R)] with s hs t
  filter_upwards [(isOpen_lt continuous_fst continuous_const).mem_nhds
    (show (s, t).1 < -R from hs)] with w hw
  exact ⟨hcyl.almostComplex_eq_of_le_neg w hw.le,
    hcyl.hamiltonianS_eq_zero w fun h ↦ h.1.not_ge hw.le, hcyl.hamiltonianT_eq_of_le_neg w hw.le⟩

end Cylindrical

/-! ### The semi-Fredholm estimate of the formal adjoint -/

/-- **The semi-Fredholm estimate of the formal adjoint for Floer data that are cylindrical near
the ends.** Let `J(z)`, `K_s`, `K_t` be Floer data on the cylinder that agree with the cylindrical
data `(J₋_t, 0, H₋_t)` for `s ≤ -R` and with `(J₊_t, 0, H₊_t)` for `s ≥ R`, with `J` `C¹` and
`K_s`, `K_t` `C²` at the points `(z, u z)`, where `u` is a `C¹` map along which `J` is
`ω`-compatible. Let the end Hamiltonians `H±` be jointly `C²` with globally Lipschitz suspended
vector fields, the end structures `J±_t(y)` be `C¹` families of period one in `t`, compatible
along orbits `x±` of `H±` that start at nondegenerate fixed points of the time-one maps, and let
the loops of `u` converge uniformly to `xm` at `-∞` and to `xp` at `+∞` while the slice defects
`∂t u - X_{H±_t}(u)` tend uniformly to zero there. Then there are `C ≥ 0` and `T` such that every
`C²` covector field `η` of period one in `t` that vanishes for `s ∉ (a, b)` satisfies

`∫ (‖∂s η‖² + ‖∂t η‖² + ‖η‖²) ≤ C (∫ ‖D_u^* η‖² + ∫_{[-T, T] × [0, 1]} ‖η‖²)`

over `[a, b] × [0, 1]`, for the formal adjoint `D_u^*` of the linearized Floer operator of the data
`(J, K_s, K_t)` along `u`. -/
theorem exists_forall_setIntegral_le_mul_setIntegral_floerLinearizationAdjoint_add_of_cylindrical
    (ω : SymplecticForm V) {J : ℝ × ℝ → V → AlmostComplexStructure V} {Ks Kt : ℝ × ℝ → V → ℝ}
    {Hm Hp : ℝ → V → ℝ} {Jm Jp : ℝ → V → AlmostComplexStructure V} {R : ℝ} {u : ℝ × ℝ → V}
    (hcyl : Floer.IsCylindricalNearEnds J Ks Kt Jm Jp Hm Hp R u) (hu : ContDiff ℝ 1 u)
    (hJu : ∀ z, ω.Compatible (J z (u z))) {Km : ℝ≥0}
    (hXm : LipschitzWith Km (ω.timeDependentHamiltonianSuspension Hm))
    (hHm : ContDiff ℝ 2 (uncurry Hm)) {xm : ℝ → V}
    (hxm : ∀ t, HasDerivAt xm (ω.hamiltonianVectorField (Hm t) (xm t)) t)
    (hndm : IsNondegenerateFixedPt 𝓘(ℝ, V) (ω.timeDependentHamiltonianFlow Hm hXm 0 1) (xm 0))
    (hJm : ContDiff ℝ 1 fun p : ℝ × V ↦ (Jm p.1 p.2).toLinearMap.toContinuousLinearMap)
    (hJm1 : Jm 1 = Jm 0) (hJxm : ∀ t, ω.Compatible (Jm t (xm t)))
    (huxm : TendstoUniformlyOn (fun s t ↦ u (s, t)) xm atBot (Icc 0 1))
    (hδm : TendstoUniformlyOn
      (fun s t ↦ sliceDefect (fun t ↦ ω.hamiltonianVectorField (Hm t)) u (s, t)) 0 atBot
        (Icc 0 1)) {Kp : ℝ≥0}
    (hXp : LipschitzWith Kp (ω.timeDependentHamiltonianSuspension Hp))
    (hHp : ContDiff ℝ 2 (uncurry Hp)) {xp : ℝ → V}
    (hxp : ∀ t, HasDerivAt xp (ω.hamiltonianVectorField (Hp t) (xp t)) t)
    (hndp : IsNondegenerateFixedPt 𝓘(ℝ, V) (ω.timeDependentHamiltonianFlow Hp hXp 0 1) (xp 0))
    (hJp : ContDiff ℝ 1 fun p : ℝ × V ↦ (Jp p.1 p.2).toLinearMap.toContinuousLinearMap)
    (hJp1 : Jp 1 = Jp 0) (hJxp : ∀ t, ω.Compatible (Jp t (xp t)))
    (huxp : TendstoUniformlyOn (fun s t ↦ u (s, t)) xp atTop (Icc 0 1))
    (hδp : TendstoUniformlyOn
      (fun s t ↦ sliceDefect (fun t ↦ ω.hamiltonianVectorField (Hp t)) u (s, t)) 0 atTop
        (Icc 0 1)) :
    ∃ C, 0 ≤ C ∧ ∃ T, ∀ ⦃η : ℝ × ℝ → V →L[ℝ] ℝ⦄, ContDiff ℝ 2 η →
      (∀ s t, η (s, t + 1) = η (s, t)) → ∀ ⦃a b : ℝ⦄, a ≤ b →
      (∀ s t, s ∉ Ioo a b → η (s, t) = 0) →
        ∫ z in Icc a b ×ˢ Icc (0 : ℝ) 1, (‖fderiv ℝ η z stdComplexLineReal‖ ^ 2 +
            ‖fderiv ℝ η z stdComplexLineImag‖ ^ 2 + ‖η z‖ ^ 2) ≤
          C * ((∫ z in Icc a b ×ˢ Icc (0 : ℝ) 1, ‖ω.floerLinearizationAdjoint
            (fun w y ↦ (J w y).toLinearMap.toContinuousLinearMap) Ks Kt u η z‖ ^ 2) +
            ∫ z in Icc (-T) T ×ˢ Icc (0 : ℝ) 1, ‖η z‖ ^ 2) := by
  have hJu₁ := contDiff_almostComplex_of_isCylindricalNearEnds hcyl hu
  have hAc := continuous_adjointCoeff_of_isCylindricalNearEnds ω hcyl hu
  have hagp := eventually_atTop_of_isCylindricalNearEnds hcyl
  have hagm := eventually_atBot_of_isCylindricalNearEnds hcyl
  -- The ends of the reflected operator: its positive end is the negative end of `u`.
  obtain ⟨hJlp, hAlp⟩ := tendstoUniformlyOn_reflectL ω hJm hHm hxm hJxm
    (hu.differentiable one_ne_zero) tendsto_neg_atTop_atBot hagm huxm hδm
  obtain ⟨hJlm, hAlm⟩ := tendstoUniformlyOn_reflectL ω hJp hHp hxp hJxp
    (hu.differentiable one_ne_zero) tendsto_neg_atBot_atTop hagp huxp hδp
  have hxmc : Continuous xm := continuous_iff_continuousAt.2 fun t ↦ (hxm t).continuousAt
  have hxpc : Continuous xp := continuous_iff_continuousAt.2 fun t ↦ (hxp t).continuousAt
  have hJrc : Continuous fun z ↦
      (J (reflectL z) (u (reflectL z))).toLinearMap.toContinuousLinearMap :=
    hJu₁.continuous.comp reflectL.continuous
  have hArc : Continuous fun z ↦ -ω.leftAdjointL
      (fderiv ℝ (fun w ↦ (J w (u w)).toLinearMap.toContinuousLinearMap) (reflectL z)
          stdComplexLineImag -
        ω.floerLinearizationCoeff (fun w y ↦ (J w y).toLinearMap.toContinuousLinearMap) Ks Kt u
          (reflectL z)) :=
    (ω.leftAdjointL.continuous.comp (hAc.comp reflectL.continuous)).neg
  obtain ⟨C₀, hC₀, T, hest⟩ :=
    ω.exists_forall_setIntegral_le_mul_setIntegral_cauchyRiemann_add_of_tendstoUniformlyOn
      (fun z ↦ hJu (reflectL z)) hJrc hArc hJxp (hJp.continuous.comp (continuous_id.prodMk hxpc))
      (apply_rotatedField_add hJp hHp hxp hJxp) (continuous_rotatedField hHp hJp hxpc)
      (det_one_sub_dysonSeriesLeft_rotatedField_ne_zero hXp hHp hxp hndp hJp hJp1) hJlm hAlm
      hJxm (hJm.continuous.comp (continuous_id.prodMk hxmc))
      (apply_rotatedField_add hJm hHm hxm hJxm) (continuous_rotatedField hHm hJm hxmc)
      (det_one_sub_dysonSeriesLeft_rotatedField_ne_zero hXm hHm hxm hndm hJm hJm1) hJlp hAlp
  -- Transfer the estimate back to the formal adjoint on covector fields.
  obtain ⟨C, hC, h⟩ := exists_forall_setIntegral_le_of_flatEquiv_reflectL ω hJrc hArc
    (D := ω.floerLinearizationAdjoint (fun w y ↦ (J w y).toLinearMap.toContinuousLinearMap) Ks Kt
      u)
    (fun η hη ↦ continuous_floerLinearizationAdjoint (fun z ↦ hcyl.contDiffAt_almostComplex z)
      hcyl.contDiffAt_hamiltonianS hcyl.contDiffAt_hamiltonianT hu (hη.of_le one_le_two))
    (fun η hη z ↦ by
      rw [floerLinearizationAdjoint_reflectL_eq ω (hη.differentiable (by norm_num) _)
        (hJu₁.differentiable one_ne_zero _) (hJu _).invariant, sub_eq_add_neg, ← neg_apply])
    hC₀ hest
  exact ⟨C, hC, T, h⟩

/-- **The semi-Fredholm estimate of the formal adjoint along a Floer trajectory.** Let `H` be a
jointly `C²` Hamiltonian whose suspended vector field is globally Lipschitz, and let `J_t(y)` be a
`C¹` family of almost complex structures of period one in `t`. Let `u : ℝ × ℝ → V` be a `C¹` map
along which `J_t` is `ω`-compatible, whose loops converge uniformly to orbits `xm` at `-∞` and `xp`
at `+∞` starting at nondegenerate fixed points of the time-one map, with `J_t` compatible along
them, while its slice defect `∂t u - X_{H_t}(u)` tends uniformly to zero at both ends, as for a
Floer trajectory from `xm` to `xp`. Then there are `C ≥ 0` and `T` such that every `C²` covector
field `η` of period one in `t` that vanishes for `s ∉ (a, b)` satisfies

`∫ (‖∂s η‖² + ‖∂t η‖² + ‖η‖²) ≤ C (∫ ‖D_u^* η‖² + ∫_{[-T, T] × [0, 1]} ‖η‖²)`

over `[a, b] × [0, 1]`, for the formal adjoint `D_u^*` of the linearized Floer operator of the
datum `K = H_t dt`. -/
theorem exists_forall_setIntegral_le_mul_setIntegral_floerLinearizationAdjoint_add
    (ω : SymplecticForm V) {H : ℝ → V → ℝ} {K : ℝ≥0}
    (hX : LipschitzWith K (ω.timeDependentHamiltonianSuspension H))
    (hH : ContDiff ℝ 2 (uncurry H)) {xm xp : ℝ → V}
    (hxm : ∀ t, HasDerivAt xm (ω.hamiltonianVectorField (H t) (xm t)) t)
    (hndm : IsNondegenerateFixedPt 𝓘(ℝ, V) (ω.timeDependentHamiltonianFlow H hX 0 1) (xm 0))
    (hxp : ∀ t, HasDerivAt xp (ω.hamiltonianVectorField (H t) (xp t)) t)
    (hndp : IsNondegenerateFixedPt 𝓘(ℝ, V) (ω.timeDependentHamiltonianFlow H hX 0 1) (xp 0))
    {J : ℝ → V → AlmostComplexStructure V}
    (hJ : ContDiff ℝ 1 fun p : ℝ × V ↦ (J p.1 p.2).toLinearMap.toContinuousLinearMap)
    (hJ1 : J 1 = J 0) (hJxm : ∀ t, ω.Compatible (J t (xm t)))
    (hJxp : ∀ t, ω.Compatible (J t (xp t))) {u : ℝ × ℝ → V} (hu : ContDiff ℝ 1 u)
    (hJu : ∀ z, ω.Compatible (J z.2 (u z)))
    (huxm : TendstoUniformlyOn (fun s t ↦ u (s, t)) xm atBot (Icc 0 1))
    (huxp : TendstoUniformlyOn (fun s t ↦ u (s, t)) xp atTop (Icc 0 1))
    (hδm : TendstoUniformlyOn
      (fun s t ↦ sliceDefect (fun t ↦ ω.hamiltonianVectorField (H t)) u (s, t)) 0 atBot (Icc 0 1))
    (hδp : TendstoUniformlyOn
      (fun s t ↦ sliceDefect (fun t ↦ ω.hamiltonianVectorField (H t)) u (s, t)) 0 atTop
        (Icc 0 1)) :
    ∃ C, 0 ≤ C ∧ ∃ T, ∀ ⦃η : ℝ × ℝ → V →L[ℝ] ℝ⦄, ContDiff ℝ 2 η →
      (∀ s t, η (s, t + 1) = η (s, t)) → ∀ ⦃a b : ℝ⦄, a ≤ b →
      (∀ s t, s ∉ Ioo a b → η (s, t) = 0) →
        ∫ z in Icc a b ×ˢ Icc (0 : ℝ) 1, (‖fderiv ℝ η z stdComplexLineReal‖ ^ 2 +
            ‖fderiv ℝ η z stdComplexLineImag‖ ^ 2 + ‖η z‖ ^ 2) ≤
          C * ((∫ z in Icc a b ×ˢ Icc (0 : ℝ) 1, ‖ω.floerLinearizationAdjoint
            (fun w y ↦ (J w.2 y).toLinearMap.toContinuousLinearMap) (fun _ _ ↦ 0)
            (fun w ↦ H w.2) u η z‖ ^ 2) + ∫ z in Icc (-T) T ×ˢ Icc (0 : ℝ) 1, ‖η z‖ ^ 2) :=
  ω.exists_forall_setIntegral_le_mul_setIntegral_floerLinearizationAdjoint_add_of_cylindrical
    (Floer.isCylindricalNearEnds_comp_snd hJ hH u) hu hJu hX hH hxm hndm hJ hJ1 hJxm huxm hδm hX hH
    hxp hndp hJ hJ1 hJxp huxp hδp

end TauCeti.SymplecticForm
