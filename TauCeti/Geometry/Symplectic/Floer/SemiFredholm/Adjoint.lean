/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Floer.SemiFredholm
public import TauCeti.Geometry.Symplectic.Floer.Linearization.Adjoint
public import TauCeti.Geometry.Symplectic.Floer.Sobolev.Density
import TauCeti.Analysis.Calculus.BumpFunction.Cutoff
import TauCeti.Analysis.Complex.EquivRealProd
import TauCeti.Geometry.Symplectic.Cayley.Tangent
import TauCeti.Geometry.Symplectic.Floer.SemiFredholm.CauchyRiemann
import TauCeti.Geometry.Symplectic.JHolomorphic.Energy.VaryingStructure
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
* **One end.** The estimate on one end at a time needs only the end of `u` at `+∞`: for covector
  fields supported far out on that end it holds without the error term, from the estimate of
  Cauchy–Riemann operators on one end
  (`exists_mem_forall_setIntegral_le_mul_setIntegral_cauchyRiemann_of_tendstoUniformlyOn`). There
  `u` need only be `C¹` far out, so the reflected coefficients are evaluated at the reflected
  point pushed into that region, which makes them continuous on the whole cylinder. This is the
  form of the estimate that applies to the ends of a punctured domain such as the pair of pants.

## Main results

In the namespace `TauCeti.SymplecticForm`:

* `exists_forall_setIntegral_le_mul_setIntegral_floerLinearizationAdjoint_add_of_cylindrical`:
  the estimate for Floer data that are cylindrical near the ends
  (`TauCeti.Floer.IsCylindricalNearEnds`), such as continuation data, with end structures of period
  one in `t`.
* `exists_forall_setIntegral_le_mul_setIntegral_floerLinearizationAdjoint_add`:
  the estimate along a Floer trajectory, for the datum `K = H_t dt`.
* `exists_forall_setIntegral_le_mul_setIntegral_floerLinearizationAdjoint`: the estimate on the
  end at `+∞` of a map asymptotic there to a nondegenerate orbit, for covector fields supported far
  out on that end, for the datum `K = H_t dt`.
* `exists_forall_setIntegral_sobolevDensity_le_mul_setIntegral_floerLinearizationAdjoint_add`: the
  `L²` estimate `∫_K (‖∂s η‖² + ‖∂t η‖² + ‖η‖²) ≤ C ∫_K (‖D_u^* η‖² + ‖η‖²)` for covector fields
  supported in a compact set `K` along which `J` is compatible, with no asymptotic condition. After
  the reflection, it is the `L²` estimate of
  `TauCeti.Geometry.Symplectic.JHolomorphic.Energy.VaryingStructure`. It is the estimate on the
  compact part of a punctured domain, such as the pair of pants.
* `exists_forall_setIntegral_sobolevDensity_le_mul_integral_floerLinearizationAdjoint_add_of_lt`:
  the estimate `∫_{‖z‖ ≤ a} (‖∂s η‖² + ‖∂t η‖² + ‖η‖²) ≤ C (∫ w ‖D_u^* η‖² + ∫_{‖z‖ ≤ b} ‖η‖²)`
  on a disc, for covector fields of compact support, when `J` is compatible along `u` and the
  continuous weight `w ≥ 0` is positive on the larger disc `‖z‖ ≤ b`. A cutoff between the discs
  costs an `L²` norm of `η` (`exists_integral_mul_norm_floerLinearizationAdjoint_smul_sq_le`),
  and the compact-set estimate passes to the weighted norm by
  `setIntegral_sobolevDensity_le_mul_integral_mul_norm_floerLinearizationAdjoint_add`, which the
  core of the pair of pants shares. It is the adjoint counterpart of
  `exists_forall_setIntegral_le_mul_integral_floerLinearization_add_of_lt`, and the estimate on
  the compact core of a plane with one cylindrical end, such as a PSS plane.
* `exists_forall_setIntegral_sobolevDensity_le_mul_setIntegral_floerLinearizationAdjoint_add_of_lt`:
  the unweighted local form, `∫_{‖z‖ ≤ a} (‖∂s η‖² + ‖∂t η‖² + ‖η‖²) ≤ C ∫_{‖z‖ ≤ b} (‖D_u^* η‖² +
  ‖η‖²)` for covector fields of arbitrary support, with every hypothesis only on the larger disc
  `‖z‖ ≤ b`, through a cutoff between the two discs.

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
  -- The derivatives of `ω♭⁻¹ ∘ η` at `ρ z` are those of the reflected field, with `∂s` negated.
  have hd (v : ℝ × ℝ) : fderiv ℝ (fun w ↦ ω.flatEquiv.symm (η w)) (reflectL z) (reflectL v) =
      fderiv ℝ (fun w ↦ ω.flatEquiv.symm (η (reflectL w))) z v := by
    rw [fderiv_flatEquiv_symm_apply, (hasFDerivAt_flatEquiv_symm_comp_reflectL ω hη).fderiv]
    simp only [ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe]
  have h₁ := hd stdComplexLineReal
  have h₂ := hd stdComplexLineImag
  rw [reflectL_stdComplexLineReal, map_neg] at h₁
  rw [reflectL_stdComplexLineImag] at h₂
  rw [floerLinearizationAdjoint_eq_neg_flatEquiv ω hη hJu hc, ← h₁, ← h₂, ← map_neg]
  congr 1
  simp only [AlmostComplexStructure.neg_apply]
  abel

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

/-- The reflection `ρ` preserves integrals: the integral of `g ∘ ρ` over `ρ⁻¹ s` is the integral
of `g` over `s`. -/
private theorem setIntegral_preimage_reflectL (g : ℝ × ℝ → ℝ) (s : Set (ℝ × ℝ)) :
    ∫ w in reflectL ⁻¹' s, g (reflectL w) = ∫ z in s, g z :=
  setIntegral_preimage_prodMap_neg_id g s

/-- The reflection `ρ` carries `[-b, -a] × [0, 1]` onto `[a, b] × [0, 1]`, preserving
integrals. -/
private theorem setIntegral_comp_reflectL (g : ℝ × ℝ → ℝ) (a b : ℝ) :
    ∫ z in Icc (-b) (-a) ×ˢ Icc (0 : ℝ) 1, g (reflectL z) =
      ∫ z in Icc a b ×ˢ Icc (0 : ℝ) 1, g z := by
  have h : reflectL ⁻¹' (Icc a b ×ˢ Icc (0 : ℝ) 1) = Icc (-b) (-a) ×ˢ Icc 0 1 := by
    ext z
    simp only [mem_preimage, reflectL_apply, mem_prod, mem_Icc, le_neg, neg_le]
    tauto
  rw [← h, setIntegral_preimage_reflectL]

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
  rw [(hasFDerivAt_flatEquiv_symm_comp_reflectL ω (hη (reflectL w))).fderiv]
  simp only [ContinuousLinearMap.comp_apply, reflectL_stdComplexLineReal,
    reflectL_stdComplexLineImag, map_neg, norm_neg, mul_add]
  gcongr <;> exact ω.norm_sq_le_norm_flatEquiv_sq_mul_norm_flatEquiv_symm_apply_sq _

/-- **Transferring the estimate.** Let `P ζ = ∂s ζ + Jr ∂t ζ + Ar ζ` satisfy the semi-Fredholm
estimate with error region `[-T, T] × [0, 1]` on the strips reflected into a set `I` of slices, and
let `D` be an operator on covector fields such that, for every `C²` field `η`, `D η` is continuous
over `I` and `D η (ρ z) = ω♭ (P ζ z)` wherever `ρ z` lies over `I`, for the reflected vector field
`ζ = ω♭⁻¹ ∘ η ∘ ρ`. Then `D` satisfies the semi-Fredholm estimate with the same error region on the
strips over `I`. -/
private theorem exists_forall_setIntegral_le_of_flatEquiv_reflectL (ω : SymplecticForm V)
    {Jr : ℝ × ℝ → AlmostComplexStructure V} {Ar : ℝ × ℝ → V →L[ℝ] V}
    (hJr : Continuous fun z ↦ (Jr z).toLinearMap.toContinuousLinearMap) (hAr : Continuous Ar)
    {D : (ℝ × ℝ → V →L[ℝ] ℝ) → ℝ × ℝ → V →L[ℝ] ℝ} {I : Set ℝ}
    (hDc : ∀ ⦃η : ℝ × ℝ → V →L[ℝ] ℝ⦄, ContDiff ℝ 2 η → ContinuousOn (D η) (I ×ˢ univ))
    (hD : ∀ ⦃η : ℝ × ℝ → V →L[ℝ] ℝ⦄, ContDiff ℝ 2 η → ∀ z, (reflectL z).1 ∈ I →
      D η (reflectL z) = ω.flatEquiv
        (fderiv ℝ (fun w ↦ ω.flatEquiv.symm (η (reflectL w))) z stdComplexLineReal +
          Jr z (fderiv ℝ (fun w ↦ ω.flatEquiv.symm (η (reflectL w))) z stdComplexLineImag) +
          Ar z (ω.flatEquiv.symm (η (reflectL z)))))
    {C₀ T : ℝ} (hC₀ : 0 ≤ C₀)
    (hest : ∀ ⦃ξ : ℝ × ℝ → V⦄, ContDiff ℝ 2 ξ → (∀ s t, ξ (s, t + 1) = ξ (s, t)) →
      ∀ ⦃a b : ℝ⦄, a ≤ b → (∀ s ∈ Icc a b, -s ∈ I) → (∀ s t, s ∉ Ioo a b → ξ (s, t) = 0) →
        ∫ z in Icc a b ×ˢ Icc (0 : ℝ) 1, (‖fderiv ℝ ξ z stdComplexLineReal‖ ^ 2 +
            ‖fderiv ℝ ξ z stdComplexLineImag‖ ^ 2 + ‖ξ z‖ ^ 2) ≤
          C₀ * ((∫ z in Icc a b ×ˢ Icc (0 : ℝ) 1, ‖fderiv ℝ ξ z stdComplexLineReal +
            Jr z (fderiv ℝ ξ z stdComplexLineImag) + Ar z (ξ z)‖ ^ 2) +
            ∫ z in Icc (-T) T ×ˢ Icc (0 : ℝ) 1, ‖ξ z‖ ^ 2)) :
    ∃ C, 0 ≤ C ∧ ∀ ⦃η : ℝ × ℝ → V →L[ℝ] ℝ⦄, ContDiff ℝ 2 η →
      (∀ s t, η (s, t + 1) = η (s, t)) → ∀ ⦃a b : ℝ⦄, a ≤ b → Icc a b ⊆ I →
      (∀ s t, s ∉ Ioo a b → η (s, t) = 0) →
        ∫ z in Icc a b ×ˢ Icc (0 : ℝ) 1, (‖fderiv ℝ η z stdComplexLineReal‖ ^ 2 +
            ‖fderiv ℝ η z stdComplexLineImag‖ ^ 2 + ‖η z‖ ^ 2) ≤
          C * ((∫ z in Icc a b ×ˢ Icc (0 : ℝ) 1, ‖D η z‖ ^ 2) +
            ∫ z in Icc (-T) T ×ˢ Icc (0 : ℝ) 1, ‖η z‖ ^ 2) := by
  set c₁ := ‖(ω.flatEquiv : V →L[ℝ] (V →L[ℝ] ℝ))‖
  set c₂ := ‖(ω.flatEquiv.symm : (V →L[ℝ] ℝ) →L[ℝ] V)‖
  refine ⟨c₁ ^ 2 * C₀ * c₂ ^ 2, by positivity, fun η hη hper a b hab hI hη₀ ↦ ?_⟩
  set ζ : ℝ × ℝ → V := fun w ↦ ω.flatEquiv.symm (η (reflectL w))
  have hζ : ContDiff ℝ 2 ζ := ω.flatEquiv.symm.contDiff.comp (hη.comp reflectL.contDiff)
  have hζ₀ (s t : ℝ) (hs : s ∉ Ioo (-b) (-a)) : ζ (s, t) = 0 := by
    simp [ζ, reflectL_apply, hη₀ (-s) t fun h ↦ hs ⟨by linarith [h.2], by linarith [h.1]⟩]
  set K := Icc (-b) (-a) ×ˢ Icc (0 : ℝ) 1
  -- On the reflected strip, `ρ` lands over `I`.
  have hKI {w : ℝ × ℝ} (hw : w ∈ K) : (reflectL w).1 ∈ I :=
    hI ⟨by rw [reflectL_apply]; linarith [hw.1.2], by rw [reflectL_apply]; linarith [hw.1.1]⟩
  have hP {w : ℝ × ℝ} (hw : w ∈ K) : ‖fderiv ℝ ζ w stdComplexLineReal +
      Jr w (fderiv ℝ ζ w stdComplexLineImag) + Ar w (ζ w)‖ ^ 2 ≤
      c₂ ^ 2 * ‖D η (reflectL w)‖ ^ 2 := by
    rw [← ContinuousLinearEquiv.symm_apply_apply ω.flatEquiv (_ + _), ← hD hη w (hKI hw)]
    exact ω.norm_flatEquiv_symm_apply_sq_le _
  have hm : MeasurableSet K := measurableSet_Icc.prod measurableSet_Icc
  have hDρ : ContinuousOn (fun w ↦ D η (reflectL w)) K :=
    (hDc hη).comp reflectL.continuous.continuousOn fun w hw ↦ ⟨hKI hw, mem_univ _⟩
  calc _ = ∫ w in K, (‖fderiv ℝ η (reflectL w) stdComplexLineReal‖ ^ 2 +
            ‖fderiv ℝ η (reflectL w) stdComplexLineImag‖ ^ 2 + ‖η (reflectL w)‖ ^ 2) :=
        (setIntegral_comp_reflectL _ a b).symm
    _ ≤ ∫ w in K, c₁ ^ 2 * (‖fderiv ℝ ζ w stdComplexLineReal‖ ^ 2 +
          ‖fderiv ℝ ζ w stdComplexLineImag‖ ^ 2 + ‖ζ w‖ ^ 2) :=
        setIntegral_mono_on
          (Continuous.integrableOn_Icc_prod_Icc (by
            simpa only [Function.comp_def, Floer.sobolevDensity_apply] using
              (Floer.continuous_sobolevDensity (hη.of_le one_le_two)).comp reflectL.continuous))
          (Continuous.integrableOn_Icc_prod_Icc (continuous_const.mul (by
            simpa only [funext (Floer.sobolevDensity_apply ζ)] using
              Floer.continuous_sobolevDensity (hζ.of_le one_le_two)))) hm
          fun w _ ↦ sobolev_reflectL_le ω (hη.differentiable (by norm_num)) w
    _ ≤ c₁ ^ 2 * (C₀ * ((∫ w in K, c₂ ^ 2 * ‖D η (reflectL w)‖ ^ 2) +
          ∫ w in Icc (-T) T ×ˢ Icc (0 : ℝ) 1, c₂ ^ 2 * ‖η (reflectL w)‖ ^ 2)) := by
      rw [integral_const_mul]
      refine mul_le_mul_of_nonneg_left ((hest hζ (fun s t ↦ by simp [ζ, reflectL_apply, hper])
        (neg_le_neg hab) (fun s hs ↦ hI ⟨by linarith [hs.2], by linarith [hs.1]⟩) hζ₀).trans
        (mul_le_mul_of_nonneg_left (add_le_add ?_ ?_) hC₀)) (sq_nonneg _)
      · exact setIntegral_mono_on ((continuous_cauchyRiemann hJr hAr
          (hζ.of_le one_le_two)).norm.pow 2).integrableOn_Icc_prod_Icc
          ((continuousOn_const.mul (hDρ.norm.pow 2)).integrableOn_compact
            (isCompact_Icc.prod isCompact_Icc)) hm fun w hw ↦ hP hw
      · exact setIntegral_mono (hζ.continuous.norm.pow 2).integrableOn_Icc_prod_Icc
          (continuous_const.mul ((hη.continuous.comp reflectL.continuous).norm.pow 2)
            ).integrableOn_Icc_prod_Icc fun w ↦ ω.norm_flatEquiv_symm_apply_sq_le (η (reflectL w))
    _ = _ := by
      have hTr := setIntegral_comp_reflectL (fun z ↦ ‖η z‖ ^ 2) (-T) T
      rw [neg_neg] at hTr
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
    (hJx : ∀ t, ω.Compatible (Je t (x t))) {l l' : Filter ℝ}
    (hu : ∀ᶠ s in l, ∀ t, DifferentiableAt ℝ u (s, t)) (hl : Tendsto Neg.neg l' l)
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
      (ε := ε / (2 * c)) (by positivity)).and (hagree.and hu))
  have hεc (ε : ℝ) (hε : 0 < ε) : c * (ε / (2 * c)) < ε := by
    have h : c * (ε / (2 * c)) = ε / 2 := by field_simp
    linarith
  have hεc' (ε : ℝ) (hε : 0 < ε) : ε / (2 * c) < ε :=
    lt_of_le_of_lt (le_mul_of_one_le_left (by positivity) hc1) (hεc ε hε)
  constructor <;> refine Metric.tendstoUniformlyOn_iff.2 fun ε hε ↦ (hev ε hε).mono
    fun s ⟨hs, hag, hus⟩ t ht ↦ ?_ <;> rw [dist_comm, dist_eq_norm] <;>
    simp only [reflectL_apply] at hs hag hus ⊢
  · rw [(hag t).self_of_nhds.1]
    exact ((hs t ht).1).trans_lt (hεc' ε hε)
  · have hB := leftAdjointL_cylindricalAdjointCoeff hJe hHe hx hJx t
    simp only [endLoop] at hB
    rw [fderiv_sub_floerLinearizationCoeff_eq_of_eventuallyEq ω (hJe.differentiable one_ne_zero)
      (hus t) (hag t), ← mul_def, ← hB, neg_sub_neg, ← map_sub]
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
  have hud {l : Filter ℝ} : ∀ᶠ s in l, ∀ t, DifferentiableAt ℝ u (s, t) :=
    .of_forall fun _ _ ↦ hu.differentiable one_ne_zero _
  obtain ⟨hJlp, hAlp⟩ := tendstoUniformlyOn_reflectL ω hJm hHm hxm hJxm hud
    tendsto_neg_atTop_atBot hagm huxm hδm
  obtain ⟨hJlm, hAlm⟩ := tendstoUniformlyOn_reflectL ω hJp hHp hxp hJxp hud
    tendsto_neg_atBot_atTop hagp huxp hδp
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
      u) (I := univ)
    (fun η hη ↦ (continuous_floerLinearizationAdjoint (fun z ↦ hcyl.contDiffAt_almostComplex z)
      hcyl.contDiffAt_hamiltonianS hcyl.contDiffAt_hamiltonianT hu
        (hη.of_le one_le_two)).continuousOn)
    (fun η hη z _ ↦ by
      rw [floerLinearizationAdjoint_reflectL_eq ω (hη.differentiable (by norm_num) _)
        (hJu₁.differentiable one_ne_zero _) (hJu _).invariant, sub_eq_add_neg, ← neg_apply])
    hC₀ fun ξ hξ hper a b hab _ hξ₀ ↦ hest hξ hper hab hξ₀
  exact ⟨C, hC, T, fun η hη hper a b hab hη₀ ↦ h hη hper hab (subset_univ _) hη₀⟩

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
    (Floer.isCylindricalNearEnds_comp_snd hJ hH (R := 0) u) hu hJu hX hH hxm hndm hJ hJ1 hJxm huxm
    hδm hX hH hxp hndp hJ hJ1 hJxp huxp hδp

/-- **The reflected coefficients on one end.** Let `u` be `C¹` near every point `(s, t)` with
`s ≥ s₀`, with loops converging uniformly at `+∞` to an orbit `x` of `H` and vanishing slice
defect. Then there are continuous coefficient fields `Jr`, `Ar` on the whole cylinder that agree,
where `s ≤ -s₀`, with the coefficients `J_t(u (ρ z))` and `-A(ρ z)ᵀ` of the reflected adjoint of
the datum `K = H_t dt`, and converge uniformly at `-∞` to `j_t` and `-j_t S''_t`. They are the
reflected coefficients evaluated at the reflected point pushed into the end `s ≥ s₀`. -/
private theorem exists_continuous_reflectL_coeff (ω : SymplecticForm V) {H : ℝ → V → ℝ}
    (hH : ContDiff ℝ 2 (uncurry H)) {x : ℝ → V}
    (hx : ∀ t, HasDerivAt x (ω.hamiltonianVectorField (H t) (x t)) t)
    {J : ℝ → V → AlmostComplexStructure V}
    (hJ : ContDiff ℝ 1 fun p : ℝ × V ↦ (J p.1 p.2).toLinearMap.toContinuousLinearMap)
    (hJx : ∀ t, ω.Compatible (J t (x t))) {u : ℝ × ℝ → V} {s₀ : ℝ}
    (hu : ∀ s, s₀ ≤ s → ∀ t, ContDiffAt ℝ 1 u (s, t))
    (hux : TendstoUniformlyOn (fun s t ↦ u (s, t)) x atTop (Icc 0 1))
    (hδ : TendstoUniformlyOn
      (fun s t ↦ sliceDefect (fun t ↦ ω.hamiltonianVectorField (H t)) u (s, t)) 0 atTop
        (Icc 0 1)) :
    ∃ (Jr : ℝ × ℝ → AlmostComplexStructure V) (Ar : ℝ × ℝ → V →L[ℝ] V),
      (Continuous fun z ↦ (Jr z).toLinearMap.toContinuousLinearMap) ∧ Continuous Ar ∧
      (∀ z, z.1 ≤ -s₀ → Jr z = J z.2 (u (reflectL z)) ∧ Ar z = -ω.leftAdjointL
        (fderiv ℝ (fun w ↦ (J w.2 (u w)).toLinearMap.toContinuousLinearMap) (reflectL z)
            stdComplexLineImag -
          ω.floerLinearizationCoeff (fun w y ↦ (J w.2 y).toLinearMap.toContinuousLinearMap)
            (fun _ _ ↦ 0) (fun w ↦ H w.2) u (reflectL z))) ∧
      TendstoUniformlyOn (fun s t ↦ (Jr (s, t)).toLinearMap.toContinuousLinearMap)
        (fun t ↦ (J t (x t)).toLinearMap.toContinuousLinearMap) atBot (Icc 0 1) ∧
      TendstoUniformlyOn (fun s t ↦ Ar (s, t))
        (fun t ↦ -((J t (x t)).toLinearMap.toContinuousLinearMap ∘L rotatedField ω J H x t))
        atBot (Icc 0 1) := by
  have hJu' : ContDiff ℝ 1 (uncurry fun t y ↦ (J t y).toLinearMap.toContinuousLinearMap) := by
    simpa only [uncurry_def] using hJ
  -- The reflected point, pushed into the end `s ≥ s₀` where `u` is `C¹`.
  set g : ℝ × ℝ → ℝ × ℝ := fun z ↦ (max (-z.1) s₀, z.2)
  have hg : Continuous g := (continuous_fst.neg.max continuous_const).prodMk continuous_snd
  have hgρ {z : ℝ × ℝ} (hz : z.1 ≤ -s₀) : g z = reflectL z := by
    simp only [g, reflectL_apply, max_eq_left (le_neg.2 hz)]
  have hug : Continuous fun z ↦ u (g z) :=
    (show ContinuousOn u {p | s₀ ≤ p.1} from fun p hp ↦
      (hu p.1 hp p.2).continuousAt.continuousWithinAt).comp_continuous hg
        fun _ ↦ le_max_right (α := ℝ) _ _
  have hdug : Continuous fun z ↦ fderiv ℝ u (g z) stdComplexLineImag :=
    (show ContinuousOn (fun p ↦ fderiv ℝ u p stdComplexLineImag) {p | s₀ ≤ p.1} from
      fun p hp ↦ (((hu p.1 hp p.2).continuousAt_fderiv one_ne_zero).clm_apply
        continuousAt_const).continuousWithinAt).comp_continuous hg
        fun _ ↦ le_max_right (α := ℝ) _ _
  have hρ {z : ℝ × ℝ} (hz : z.1 ≤ -s₀) : DifferentiableAt ℝ u (reflectL z) :=
    (hu (-z.1) (by linarith) z.2).differentiableAt one_ne_zero
  refine ⟨fun z ↦ J z.2 (u (g z)), fun z ↦ -ω.leftAdjointL (ω.cylindricalAdjointCoeff
    (fun t y ↦ (J t y).toLinearMap.toContinuousLinearMap) H
    (z.2, u (g z), fderiv ℝ u (g z) stdComplexLineImag)),
    hJ.continuous.comp (continuous_snd.prodMk hug), (ω.leftAdjointL.continuous.comp
      ((ω.continuous_cylindricalAdjointCoeff hJu' hH).comp
        (continuous_snd.prodMk (hug.prodMk hdug)))).neg, ?_⟩
  -- Beyond `-s₀` the fields are the reflected coefficients, which converge at `-∞`.
  have heq {z : ℝ × ℝ} (hz : z.1 ≤ -s₀) : J z.2 (u (g z)) = J z.2 (u (reflectL z)) ∧
      -ω.leftAdjointL (ω.cylindricalAdjointCoeff
        (fun t y ↦ (J t y).toLinearMap.toContinuousLinearMap) H
        (z.2, u (g z), fderiv ℝ u (g z) stdComplexLineImag)) = -ω.leftAdjointL
      (fderiv ℝ (fun w ↦ (J w.2 (u w)).toLinearMap.toContinuousLinearMap) (reflectL z)
          stdComplexLineImag -
        ω.floerLinearizationCoeff (fun w y ↦ (J w.2 y).toLinearMap.toContinuousLinearMap)
          (fun _ _ ↦ 0) (fun w ↦ H w.2) u (reflectL z)) := by
    rw [ω.fderiv_sub_floerLinearizationCoeff_eq_cylindricalAdjointCoeff
      (J := fun t y ↦ (J t y).toLinearMap.toContinuousLinearMap)
      (hJu'.differentiable one_ne_zero) (hρ hz), hgρ hz, reflectL_apply]
    exact ⟨rfl, rfl⟩
  obtain ⟨hJl, hAl⟩ := tendstoUniformlyOn_reflectL ω (J := fun w ↦ J w.2) (Ks := fun _ _ ↦ 0)
    (Kt := fun w ↦ H w.2) hJ hH hx hJx
    ((eventually_ge_atTop s₀).mono fun s hs t ↦ (hu s hs t).differentiableAt one_ne_zero)
    tendsto_neg_atBot_atTop (.of_forall fun _ _ ↦ .of_forall fun _ ↦ ⟨rfl, rfl, rfl⟩) hux hδ
  have hρs : ∀ᶠ s in (atBot : Filter ℝ), s ≤ -s₀ := eventually_le_atBot _
  refine ⟨fun z hz ↦ heq hz, hJl.congr (hρs.mono fun s hs t _ ↦ ?_),
    hAl.congr (hρs.mono fun s hs t _ ↦ (heq (z := (s, t)) hs).2.symm)⟩
  simp only [(heq (z := (s, t)) hs).1, reflectL_apply]

/-- **The end estimate of the formal adjoint.** Let `H` be a jointly `C²` Hamiltonian whose
suspended vector field is globally Lipschitz, and let `J_t(y)` be a `C¹` family of almost complex
structures of period one in `t`. Let `u : ℝ × ℝ → V` be a map that is `C¹` near every point
`(s, t)` with `s` large, along which `J_t` is `ω`-compatible there, whose loops converge uniformly
at `+∞` to an orbit `x` starting at a nondegenerate fixed point of the time-one map, with `J_t`
compatible along it, while its slice defect `∂t u - X_{H_t}(u)` tends uniformly to zero, as on the
positive end of a Floer trajectory. Then there are `C ≥ 0` and `R` such that every `C²` covector
field `η` of period one in `t` that vanishes for `s ∉ (a, b)`, with `R ≤ a`, satisfies

`∫ (‖∂s η‖² + ‖∂t η‖² + ‖η‖²) ≤ C ∫ ‖D_u^* η‖²`

over `[a, b] × [0, 1]`, for the formal adjoint `D_u^*` of the linearized Floer operator of the
datum `K = H_t dt`. Only the end of `u` at `+∞` enters. -/
theorem exists_forall_setIntegral_le_mul_setIntegral_floerLinearizationAdjoint
    (ω : SymplecticForm V) {H : ℝ → V → ℝ} {K : ℝ≥0}
    (hX : LipschitzWith K (ω.timeDependentHamiltonianSuspension H))
    (hH : ContDiff ℝ 2 (uncurry H)) {x : ℝ → V}
    (hx : ∀ t, HasDerivAt x (ω.hamiltonianVectorField (H t) (x t)) t)
    (hnd : IsNondegenerateFixedPt 𝓘(ℝ, V) (ω.timeDependentHamiltonianFlow H hX 0 1) (x 0))
    {J : ℝ → V → AlmostComplexStructure V}
    (hJ : ContDiff ℝ 1 fun p : ℝ × V ↦ (J p.1 p.2).toLinearMap.toContinuousLinearMap)
    (hJ1 : J 1 = J 0) (hJx : ∀ t, ω.Compatible (J t (x t))) {u : ℝ × ℝ → V}
    (hu : ∀ᶠ s in atTop, ∀ t, ContDiffAt ℝ 1 u (s, t))
    (hJu : ∀ᶠ s in atTop, ∀ t, ω.Compatible (J t (u (s, t))))
    (hux : TendstoUniformlyOn (fun s t ↦ u (s, t)) x atTop (Icc 0 1))
    (hδ : TendstoUniformlyOn
      (fun s t ↦ sliceDefect (fun t ↦ ω.hamiltonianVectorField (H t)) u (s, t)) 0 atTop
        (Icc 0 1)) :
    ∃ C, 0 ≤ C ∧ ∃ R, ∀ ⦃η : ℝ × ℝ → V →L[ℝ] ℝ⦄, ContDiff ℝ 2 η →
      (∀ s t, η (s, t + 1) = η (s, t)) → ∀ ⦃a b : ℝ⦄, a ≤ b → R ≤ a →
      (∀ s t, s ∉ Ioo a b → η (s, t) = 0) →
        ∫ z in Icc a b ×ˢ Icc (0 : ℝ) 1, (‖fderiv ℝ η z stdComplexLineReal‖ ^ 2 +
            ‖fderiv ℝ η z stdComplexLineImag‖ ^ 2 + ‖η z‖ ^ 2) ≤
          C * ∫ z in Icc a b ×ˢ Icc (0 : ℝ) 1, ‖ω.floerLinearizationAdjoint
            (fun w y ↦ (J w.2 y).toLinearMap.toContinuousLinearMap) (fun _ _ ↦ 0)
            (fun w ↦ H w.2) u η z‖ ^ 2 := by
  obtain ⟨s₀, hs₀⟩ := eventually_atTop.1 ((hu.and hJu).mono fun _ h (t : ℝ) ↦ And.intro (h.1 t)
    (h.2 t))
  have hxc : Continuous x := continuous_iff_continuousAt.2 fun t ↦ (hx t).continuousAt
  obtain ⟨Jr, Ar, hJrc, hArc, hρ, hJl, hAl⟩ := exists_continuous_reflectL_coeff ω hH hx hJ hJx
    (fun s hs t ↦ (hs₀ s hs t).1) hux hδ
  -- The Cauchy–Riemann estimate at `-∞` for the reflected coefficients.
  obtain ⟨C₀, hC₀, U, hU, hest⟩ :=
    ω.exists_mem_forall_setIntegral_le_mul_setIntegral_cauchyRiemann_of_tendstoUniformlyOn hJx
      (hJ.continuous.comp (continuous_id.prodMk hxc)) (apply_rotatedField_add hJ hH hx hJx)
      (continuous_rotatedField hH hJ hxc)
      (det_one_sub_dysonSeriesLeft_rotatedField_ne_zero hX hH hx hnd hJ hJ1) hJrc hArc hJl hAl
  obtain ⟨r, hr⟩ := mem_atBot_sets.1 hU
  -- Transfer it to the adjoint on the slices `s ≥ R`, with an empty error region.
  set R := max (max s₀ (-r)) 1
  have hRs₀ : s₀ ≤ R := (le_max_left _ _).trans (le_max_left _ _)
  have hRr : -r ≤ R := (le_max_right _ _).trans (le_max_left _ _)
  obtain ⟨C, hC, h⟩ := exists_forall_setIntegral_le_of_flatEquiv_reflectL ω hJrc hArc
    (D := ω.floerLinearizationAdjoint (fun w y ↦ (J w.2 y).toLinearMap.toContinuousLinearMap)
      (fun _ _ ↦ 0) (fun w ↦ H w.2) u) (I := Ici R) (T := 0)
    (fun η hη p hp ↦ (continuousAt_floerLinearizationAdjoint (ω := ω)
      (J := fun w y ↦ (J w.2 y).toLinearMap.toContinuousLinearMap) (Ks := fun _ _ ↦ 0)
      (Kt := fun w ↦ H w.2) (hJ.comp (contDiff_fst.snd.prodMk contDiff_snd)).contDiffAt
      contDiffAt_const (hH.comp (contDiff_fst.snd.prodMk contDiff_snd)).contDiffAt
      (hs₀ p.1 (hRs₀.trans hp.1) p.2).1 (hη.contDiffAt.of_le one_le_two)).continuousWithinAt)
    (fun η hη z hz ↦ by
      have hz₀ : z.1 ≤ -s₀ := by rw [reflectL_apply] at hz; linarith [mem_Ici.1 hz]
      obtain ⟨hJrz, hArz⟩ := hρ z hz₀
      have hs := hs₀ (reflectL z).1 (hRs₀.trans hz) (reflectL z).2
      rw [floerLinearizationAdjoint_reflectL_eq ω (J := fun w ↦ J w.2)
        (hη.differentiable (by norm_num) _) ((hJ.differentiable one_ne_zero _).comp _
          (differentiableAt_snd.prodMk (hs.1.differentiableAt one_ne_zero))) hs.2.invariant,
        hJrz, hArz]
      simp only [reflectL_apply, sub_eq_add_neg, neg_apply])
    hC₀ fun ξ hξ hper a b hab hI hξ₀ ↦ by
      have hbr : b ≤ r := by linarith [mem_Ici.1 (hI b ⟨hab, le_rfl⟩)]
      refine (hest hξ hper hab (fun s hs ↦ hr s (hs.2.trans hbr)) (fun t ↦ hξ₀ a t
        fun h ↦ lt_irrefl _ h.1) (fun t ↦ hξ₀ b t fun h ↦ lt_irrefl _ h.2)).trans ?_
      exact mul_le_mul_of_nonneg_left (le_add_of_nonneg_right (setIntegral_nonneg
        (measurableSet_Icc.prod measurableSet_Icc) fun _ _ ↦ sq_nonneg _)) hC₀
  refine ⟨C, hC, R, fun η hη hper a b hab hRa hη₀ ↦ ?_⟩
  -- The error region `{0} × [0, 1]` lies outside the strip, where `η` vanishes.
  have h₀ : ∫ z in Icc (-0 : ℝ) 0 ×ˢ Icc (0 : ℝ) 1, ‖η z‖ ^ 2 = 0 :=
    setIntegral_eq_zero_of_forall_eq_zero fun ⟨s, t⟩ hz ↦ by
      have hs : s = 0 := by linarith [hz.1.1, hz.1.2]
      rw [hs, hη₀ 0 t fun h ↦ by linarith [h.1, le_max_right (max s₀ (-r)) 1], norm_zero]
      norm_num
  simpa only [h₀, add_zero] using
    h hη hper hab (fun s hs ↦ mem_Ici.2 (hRa.trans hs.1)) hη₀

/-! ### The estimate on compact parts of the domain -/

private theorem reflectL_reflectL (z : ℝ × ℝ) : reflectL (reflectL z) = z := by
  simp [reflectL_apply]

/-- The reflection `ρ⁻¹ K` of a compact set is compact. -/
private theorem isCompact_preimage_reflectL {K : Set (ℝ × ℝ)} (hK : IsCompact K) :
    IsCompact (reflectL ⁻¹' K) := by
  rw [← congrFun (image_eq_preimage_of_inverse reflectL_reflectL reflectL_reflectL) K]
  exact hK.image reflectL.continuous

/-- The coefficients `J(ρ w, u (ρ w))` and `-A(ρ w)ᵀ` of the reflected formal adjoint, with
`A = ∂t J - C`, are continuous on `ρ⁻¹ K` when `J` is `C¹` and `K_s`, `K_t` are `C²` along `u`
on `K`, and `u` is `C¹` there. -/
private theorem continuousOn_reflectL_coeff (ω : SymplecticForm V)
    {J : ℝ × ℝ → V → AlmostComplexStructure V} {Ks Kt : ℝ × ℝ → V → ℝ} {u : ℝ × ℝ → V}
    {K : Set (ℝ × ℝ)}
    (hJ : ∀ z ∈ K, ContDiffAt ℝ 1
      (fun p : (ℝ × ℝ) × V ↦ (J p.1 p.2).toLinearMap.toContinuousLinearMap) (z, u z))
    (hKs : ∀ z ∈ K, ContDiffAt ℝ 2 (uncurry Ks) (z, u z))
    (hKt : ∀ z ∈ K, ContDiffAt ℝ 2 (uncurry Kt) (z, u z))
    (hu : ∀ z ∈ K, ContDiffAt ℝ 1 u z) :
    ContinuousOn
        (fun w ↦ (J (reflectL w) (u (reflectL w))).toLinearMap.toContinuousLinearMap)
        (reflectL ⁻¹' K) ∧
      ContinuousOn (fun w ↦ -ω.leftAdjointL
        (fderiv ℝ (fun w ↦ (J w (u w)).toLinearMap.toContinuousLinearMap) (reflectL w)
            stdComplexLineImag -
          ω.floerLinearizationCoeff (fun w y ↦ (J w y).toLinearMap.toContinuousLinearMap) Ks Kt
            u (reflectL w))) (reflectL ⁻¹' K) := by
  have hJu (z : ℝ × ℝ) (hz : z ∈ K) :
      ContDiffAt ℝ 1 (fun w ↦ (J w (u w)).toLinearMap.toContinuousLinearMap) z :=
    (hJ z hz).comp (f := fun w ↦ (w, u w)) z (contDiffAt_id.prodMk (hu z hz))
  have hA : ContinuousOn (fun z ↦
      fderiv ℝ (fun w ↦ (J w (u w)).toLinearMap.toContinuousLinearMap) z stdComplexLineImag -
        ω.floerLinearizationCoeff (fun w y ↦ (J w y).toLinearMap.toContinuousLinearMap) Ks Kt u z)
      K := fun z hz ↦
    ((((hJu z hz).continuousAt_fderiv one_ne_zero).clm_apply
      continuousAt_const).continuousWithinAt).sub
      (ω.continuousOn_floerLinearizationCoeff hJ hKs hKt hu z hz)
  exact ⟨fun w hw ↦ ((hJu _ hw).continuousAt.comp reflectL.continuous.continuousAt
    ).continuousWithinAt, (ω.leftAdjointL.continuous.comp_continuousOn
      (hA.comp reflectL.continuous.continuousOn fun _ hw ↦ hw)).neg⟩

/-- An integral over `ρ⁻¹ K` of a nonnegative function bounded by `c` times `F ∘ ρ` is at most `c`
times the integral of `F` over `K`, for `F` continuous on the compact set `K`. -/
private theorem setIntegral_preimage_reflectL_le {K : Set (ℝ × ℝ)} (hK : IsCompact K)
    {F : ℝ × ℝ → ℝ} (hF : ContinuousOn F K) {g : ℝ × ℝ → ℝ} (hg : ∀ w, 0 ≤ g w) {c : ℝ}
    (hgF : ∀ w ∈ reflectL ⁻¹' K, g w ≤ c * F (reflectL w)) :
    ∫ w in reflectL ⁻¹' K, g w ≤ c * ∫ z in K, F z := by
  rw [← setIntegral_preimage_reflectL F K, ← integral_const_mul]
  exact integral_mono_of_nonneg (ae_of_all _ hg) ((continuousOn_const.mul (hF.comp
    reflectL.continuous.continuousOn fun _ hw ↦ hw)).integrableOn_compact
    (isCompact_preimage_reflectL hK)) ((ae_restrict_iff' (isCompact_preimage_reflectL hK
    ).measurableSet).2 (ae_of_all _ hgF))

/-- **Reflecting the energy.** The `W^{1,2}` energy of a covector field `η` over `K` is at most
`‖ω♭‖²` times that of the reflected vector field `ζ = ω♭⁻¹ ∘ η ∘ ρ` over `ρ⁻¹ K`, split into its
derivative and `L²` parts. -/
private theorem setIntegral_sobolevDensity_le_of_flatEquiv_reflectL (ω : SymplecticForm V)
    {K : Set (ℝ × ℝ)} (hK : IsCompact K) {η : ℝ × ℝ → V →L[ℝ] ℝ} (hη : ContDiff ℝ 2 η) :
    ∫ z in K, Floer.sobolevDensity η z ≤
      ‖(ω.flatEquiv : V →L[ℝ] (V →L[ℝ] ℝ))‖ ^ 2 *
        ((∫ w in reflectL ⁻¹' K,
          (‖fderiv ℝ (fun w ↦ ω.flatEquiv.symm (η (reflectL w))) w stdComplexLineReal‖ ^ 2 +
            ‖fderiv ℝ (fun w ↦ ω.flatEquiv.symm (η (reflectL w))) w stdComplexLineImag‖ ^ 2)) +
          ∫ w in reflectL ⁻¹' K, ‖ω.flatEquiv.symm (η (reflectL w))‖ ^ 2) := by
  set ζ : ℝ × ℝ → V := fun w ↦ ω.flatEquiv.symm (η (reflectL w))
  have hζ : ContDiff ℝ 2 ζ := ω.flatEquiv.symm.contDiff.comp (hη.comp reflectL.contDiff)
  have hK' := isCompact_preimage_reflectL hK
  have hζ2 : IntegrableOn (fun w ↦ ‖ζ w‖ ^ 2) (reflectL ⁻¹' K) :=
    (hζ.continuous.norm.pow 2).continuousOn.integrableOn_compact hK'
  have hdζ : IntegrableOn (fun w ↦ ‖fderiv ℝ ζ w stdComplexLineReal‖ ^ 2 +
      ‖fderiv ℝ ζ w stdComplexLineImag‖ ^ 2) (reflectL ⁻¹' K) := by
    have := hζ.continuous_fderiv two_ne_zero
    exact Continuous.continuousOn (by fun_prop) |>.integrableOn_compact hK'
  rw [← integral_add hdζ hζ2, ← integral_const_mul, ← setIntegral_preimage_reflectL]
  exact integral_mono_of_nonneg (ae_of_all _ fun _ ↦ Floer.sobolevDensity_nonneg _ _)
    ((hdζ.add hζ2).const_mul _) (ae_of_all _ fun w ↦ by
      simpa only [Floer.sobolevDensity_apply] using
        sobolev_reflectL_le ω (hη.differentiable two_ne_zero) w)

/-- **The `L²` estimate of the formal adjoint on compactly supported covector fields.** Let
`K ⊆ ℝ × ℝ` be compact, and suppose that at every `z ∈ K` the structure `J(z, u z)` is
`ω`-compatible, `J` is `C¹` and the Hamiltonians `K_s`, `K_t` are `C²` at `(z, u z)`, and `u` is
`C¹` at `z`. Then there is a constant `C ≥ 0` such that every `C²` covector field `η` with support
in `K` satisfies

`∫_K (‖∂s η‖² + ‖∂t η‖² + ‖η‖²) ≤ C ∫_K (‖D_u^* η‖² + ‖η‖²)`

for the formal adjoint `D_u^*` of the linearized Floer operator. This is the adjoint counterpart of
`exists_forall_setIntegral_norm_fderiv_sq_le_mul_setIntegral_floerLinearization_of_tsupport_subset`:
after the reflection `ρ (s, t) = (-s, t)` and `ω`, `D_u^*` is a real Cauchy–Riemann operator with
the compatible leading coefficient `J(ρ w, u (ρ w))`, to which the `L²` estimate of
`TauCeti.Geometry.Symplectic.JHolomorphic.Energy.VaryingStructure` applies. -/
theorem exists_forall_setIntegral_sobolevDensity_le_mul_setIntegral_floerLinearizationAdjoint_add
    (ω : SymplecticForm V) {J : ℝ × ℝ → V → AlmostComplexStructure V} {Ks Kt : ℝ × ℝ → V → ℝ}
    {u : ℝ × ℝ → V} {K : Set (ℝ × ℝ)} (hK : IsCompact K)
    (hJ : ∀ z ∈ K, ContDiffAt ℝ 1
      (fun p : (ℝ × ℝ) × V ↦ (J p.1 p.2).toLinearMap.toContinuousLinearMap) (z, u z))
    (hKs : ∀ z ∈ K, ContDiffAt ℝ 2 (uncurry Ks) (z, u z))
    (hKt : ∀ z ∈ K, ContDiffAt ℝ 2 (uncurry Kt) (z, u z))
    (hu : ∀ z ∈ K, ContDiffAt ℝ 1 u z) (hc : ∀ z ∈ K, ω.Compatible (J z (u z))) :
    ∃ C, 0 ≤ C ∧ ∀ ⦃η : ℝ × ℝ → V →L[ℝ] ℝ⦄, ContDiff ℝ 2 η → tsupport η ⊆ K →
      ∫ z in K, Floer.sobolevDensity η z ≤
        C * ∫ z in K, (‖ω.floerLinearizationAdjoint
            (fun w y ↦ (J w y).toLinearMap.toContinuousLinearMap) Ks Kt u η z‖ ^ 2 +
          ‖η z‖ ^ 2) := by
  set J' : ℝ × ℝ → V → V →L[ℝ] V := fun w y ↦ (J w y).toLinearMap.toContinuousLinearMap
  set K' := reflectL ⁻¹' K
  have hK' : IsCompact K' := isCompact_preimage_reflectL hK
  obtain ⟨hJr, hT⟩ := ω.continuousOn_reflectL_coeff hJ hKs hKt hu
  have : (volume : Measure (ℝ × ℝ)).IsAddHaarMeasure := Measure.prod.instIsAddHaarMeasure _ _
  obtain ⟨C₀, hC₀, hest⟩ := exists_forall_setIntegral_norm_fderiv_sq_le_of_tsupport_subset
    (μ := volume) hK' (J := fun w ↦ J (reflectL w) (u (reflectL w))) (fun w hw ↦ hc _ hw) hJr hT
  set c₁ := ‖(ω.flatEquiv : V →L[ℝ] (V →L[ℝ] ℝ))‖
  set c₂ := ‖(ω.flatEquiv.symm : (V →L[ℝ] ℝ) →L[ℝ] V)‖
  refine ⟨c₁ ^ 2 * (C₀ + 1) * c₂ ^ 2, by positivity, fun η hη hηK ↦ ?_⟩
  set D := ω.floerLinearizationAdjoint J' Ks Kt u η
  set ζ : ℝ × ℝ → V := fun w ↦ ω.flatEquiv.symm (η (reflectL w))
  have hζ : ContDiff ℝ 2 ζ := ω.flatEquiv.symm.contDiff.comp (hη.comp reflectL.contDiff)
  have hζK : tsupport ζ ⊆ K' :=
    (tsupport_comp_subset (map_zero ω.flatEquiv.symm) (η ∘ reflectL)).trans
      ((tsupport_comp_subset_preimage η reflectL.continuous).trans (preimage_mono hηK))
  have hDc : ContinuousOn D K := fun z hz ↦ (continuousAt_floerLinearizationAdjoint
    (by simpa only [Function.uncurry_def] using hJ z hz) (hKs z hz) (hKt z hz) (hu z hz)
    (hη.of_le one_le_two).contDiffAt).continuousWithinAt
  have hF : ContinuousOn (fun z ↦ ‖D z‖ ^ 2 + ‖η z‖ ^ 2) K :=
    (hDc.norm.pow 2).add (hη.continuous.norm.pow 2).continuousOn
  -- On `K'`, the reflected adjoint is `ω♭` of the Cauchy–Riemann operator of the estimate, so its
  -- Cauchy–Riemann and `L²` terms are controlled by those of `D η` and `η`.
  have hPI : ∫ w in K', (‖fderiv ℝ ζ w stdComplexLineReal +
      J (reflectL w) (u (reflectL w)) (fderiv ℝ ζ w stdComplexLineImag) +
      (-ω.leftAdjointL (fderiv ℝ (fun w ↦ J' w (u w)) (reflectL w) stdComplexLineImag -
        ω.floerLinearizationCoeff J' Ks Kt u (reflectL w))) (ζ w)‖ ^ 2 + ‖ζ w‖ ^ 2) ≤
      c₂ ^ 2 * ∫ z in K, (‖D z‖ ^ 2 + ‖η z‖ ^ 2) := by
    refine setIntegral_preimage_reflectL_le hK hF (fun _ ↦ by positivity) fun w hw ↦ ?_
    have h := floerLinearizationAdjoint_reflectL_eq ω (Ks := Ks) (Kt := Kt)
      (hη.differentiable two_ne_zero _) ((hJ _ hw).comp (f := fun w ↦ (w, u w)) _
        (contDiffAt_id.prodMk (hu _ hw)) |>.differentiableAt one_ne_zero) (hc _ hw).invariant
    rw [neg_apply, ← sub_eq_add_neg, ← ContinuousLinearEquiv.symm_apply_apply ω.flatEquiv (_ - _),
      ← h]
    nlinarith [ω.norm_flatEquiv_symm_apply_sq_le (D (reflectL w)),
      ω.norm_flatEquiv_symm_apply_sq_le (η (reflectL w))]
  have hζI : ∫ w in K', ‖ζ w‖ ^ 2 ≤ c₂ ^ 2 * ∫ z in K, (‖D z‖ ^ 2 + ‖η z‖ ^ 2) :=
    setIntegral_preimage_reflectL_le hK hF (fun _ ↦ by positivity) fun w _ ↦ by
      nlinarith [ω.norm_flatEquiv_symm_apply_sq_le (η (reflectL w)), sq_nonneg c₂,
        sq_nonneg ‖D (reflectL w)‖]
  calc _ ≤ c₁ ^ 2 * ((∫ w in K', (‖fderiv ℝ ζ w stdComplexLineReal‖ ^ 2 +
          ‖fderiv ℝ ζ w stdComplexLineImag‖ ^ 2)) + ∫ w in K', ‖ζ w‖ ^ 2) :=
        setIntegral_sobolevDensity_le_of_flatEquiv_reflectL ω hK hη
    _ ≤ c₁ ^ 2 * (C₀ * (c₂ ^ 2 * ∫ z in K, (‖D z‖ ^ 2 + ‖η z‖ ^ 2)) +
          c₂ ^ 2 * ∫ z in K, (‖D z‖ ^ 2 + ‖η z‖ ^ 2)) := by
        gcongr
        exact (hest hζ hζK).trans (mul_le_mul_of_nonneg_left hPI hC₀)
    _ = _ := by ring

/-! ### The estimate on a disc -/

section Disc

open Floer

/-- **The estimate of the adjoint on a compact set, with a weight.** Let the data be regular along
`u` on an open set `S`, and let the weight `w ≥ 0` be continuous on `S`. If `D_u^*` satisfies the
`L²` estimate `hcore` on covector fields supported in a compact set `K`, and `1 ≤ Λ w` on `K`, then
a `C²` covector field `θ` of compact support in `K ∩ S` satisfies
`∫_K (‖∂s θ‖² + ‖∂t θ‖² + ‖θ‖²) ≤ C₀ (Λ ∫ w ‖D_u^* θ‖² + ∫_K ‖θ‖²)`. -/
theorem setIntegral_sobolevDensity_le_mul_integral_mul_norm_floerLinearizationAdjoint_add
    (ω : SymplecticForm V) {J : ℝ × ℝ → V → V →L[ℝ] V} {Ks Kt : ℝ × ℝ → V → ℝ} {u : ℝ × ℝ → V}
    {S : Set (ℝ × ℝ)}
    (hS : IsOpen S) (hJ : ∀ z ∈ S, ContDiffAt ℝ 1 (uncurry J) (z, u z))
    (hKs : ∀ z ∈ S, ContDiffAt ℝ 2 (uncurry Ks) (z, u z))
    (hKt : ∀ z ∈ S, ContDiffAt ℝ 2 (uncurry Kt) (z, u z)) (hu : ∀ z ∈ S, ContDiffAt ℝ 1 u z)
    {w : ℝ × ℝ → ℝ} (hw : ∀ z, 0 ≤ w z) (hwc : ContinuousOn w S) {K : Set (ℝ × ℝ)}
    (hK : IsCompact K) {Λ : ℝ} (hΛ₀ : 0 ≤ Λ) (hΛ : ∀ z ∈ K, 1 ≤ Λ * w z) {C₀ : ℝ}
    (hC₀ : 0 ≤ C₀)
    (hcore : ∀ ⦃θ : ℝ × ℝ → V →L[ℝ] ℝ⦄, ContDiff ℝ 2 θ → tsupport θ ⊆ K →
      ∫ z in K, sobolevDensity θ z ≤
        C₀ * ∫ z in K, (‖ω.floerLinearizationAdjoint J Ks Kt u θ z‖ ^ 2 + ‖θ z‖ ^ 2))
    {θ : ℝ × ℝ → V →L[ℝ] ℝ} (hθ : ContDiff ℝ 2 θ) (hθS : tsupport θ ⊆ S) (hθK : tsupport θ ⊆ K) :
    ∫ z in K, sobolevDensity θ z ≤
      C₀ * (Λ * (∫ z, w z * ‖ω.floerLinearizationAdjoint J Ks Kt u θ z‖ ^ 2) +
        ∫ z in K, ‖θ z‖ ^ 2) := by
  have hθc : HasCompactSupport θ := hK.of_isClosed_subset (isClosed_tsupport θ) hθK
  have hDc := ω.continuous_floerLinearizationAdjoint_of_tsupport_subset hJ hKs hKt hu
    (hθ.of_le one_le_two) hθS
  have hW := ω.integrable_mul_norm_floerLinearizationAdjoint_sq hS hJ hKs hKt hu hwc
    (hθ.of_le one_le_two) subset_rfl hθc hθS
  have hD : IntegrableOn (fun z ↦ ‖ω.floerLinearizationAdjoint J Ks Kt u θ z‖ ^ 2) K :=
    (hDc.norm.pow 2).continuousOn.integrableOn_compact hK
  have hθ₂ : IntegrableOn (fun z ↦ ‖θ z‖ ^ 2) K :=
    (hθ.continuous.norm.pow 2).continuousOn.integrableOn_compact hK
  -- On `K`, where `1 ≤ Λ w`, the unweighted norm is at most `Λ` times the weighted one.
  have h : ∫ z in K, ‖ω.floerLinearizationAdjoint J Ks Kt u θ z‖ ^ 2 ≤
      Λ * ∫ z, w z * ‖ω.floerLinearizationAdjoint J Ks Kt u θ z‖ ^ 2 := by
    rw [← integral_const_mul]
    refine (setIntegral_mono_on hD (hW.const_mul Λ).integrableOn hK.measurableSet
      fun z hz ↦ ?_).trans (setIntegral_le_integral (hW.const_mul Λ) (ae_of_all _ fun z ↦ ?_))
    · calc _ ≤ Λ * w z * ‖ω.floerLinearizationAdjoint J Ks Kt u θ z‖ ^ 2 :=
          le_mul_of_one_le_left (sq_nonneg _) (hΛ z hz)
        _ = _ := by ring
    · have := hw z
      positivity
  calc _ ≤ C₀ * ((∫ z in K, ‖ω.floerLinearizationAdjoint J Ks Kt u θ z‖ ^ 2) +
        ∫ z in K, ‖θ z‖ ^ 2) := by
        rw [← integral_add hD hθ₂]
        exact hcore hθ hθK
    _ ≤ _ := by gcongr

/-- **The estimate of the formal adjoint on a disc.** Let `a < b`, let `J(z, u z)` be
`ω`-compatible for every `z` in the disc `‖z‖ ≤ b`, with `J` `C¹` and `K_s`, `K_t` `C²` at the
points `(z, u z)`, and `u` `C¹`, and let `w ≥ 0` be a continuous weight, positive on that disc.
Then there is a constant `C ≥ 0` such that every `C²` covector field `η` of compact support
satisfies
`∫_{‖z‖ ≤ a} (‖∂s η‖² + ‖∂t η‖² + ‖η‖²) ≤ C (∫ w ‖D_u^* η‖² + ∫_{‖z‖ ≤ b} ‖η‖²)`, the discs read in
real coordinates. A cutoff between the two discs reduces this to the estimate on compactly
supported fields,
`exists_forall_setIntegral_sobolevDensity_le_mul_setIntegral_floerLinearizationAdjoint_add`. -/
theorem exists_forall_setIntegral_sobolevDensity_le_mul_integral_floerLinearizationAdjoint_add_of_lt
    (ω : SymplecticForm V) {J : ℝ × ℝ → V → AlmostComplexStructure V} {Ks Kt : ℝ × ℝ → V → ℝ}
    {u : ℝ × ℝ → V}
    (hJ : ∀ z, ContDiffAt ℝ 1
      (fun q : (ℝ × ℝ) × V ↦ (J q.1 q.2).toLinearMap.toContinuousLinearMap) (z, u z))
    (hKs : ∀ z, ContDiffAt ℝ 2 (uncurry Ks) (z, u z))
    (hKt : ∀ z, ContDiffAt ℝ 2 (uncurry Kt) (z, u z)) (hu : ContDiff ℝ 1 u)
    {w : ℝ × ℝ → ℝ} (hw : ∀ z, 0 ≤ w z) (hwc : Continuous w) {a b : ℝ}
    (hwb : ∀ z, ‖Complex.equivRealProdCLM.symm z‖ ≤ b → 0 < w z)
    (hc : ∀ z, ‖Complex.equivRealProdCLM.symm z‖ ≤ b → ω.Compatible (J z (u z))) (hab : a < b) :
    ∃ C, 0 ≤ C ∧ ∀ ⦃η : ℝ × ℝ → V →L[ℝ] ℝ⦄, ContDiff ℝ 2 η → HasCompactSupport η →
      ∫ z in {z | ‖Complex.equivRealProdCLM.symm z‖ ≤ a}, sobolevDensity η z ≤
        C * ((∫ z, w z * ‖ω.floerLinearizationAdjoint
            (fun z y ↦ (J z y).toLinearMap.toContinuousLinearMap) Ks Kt u η z‖ ^ 2) +
          ∫ z in {z | ‖Complex.equivRealProdCLM.symm z‖ ≤ b}, ‖η z‖ ^ 2) := by
  set K := {z : ℝ × ℝ | ‖Complex.equivRealProdCLM.symm z‖ ≤ b}
  have hK : IsCompact K := isCompact_setOf_norm_equivRealProdCLM_symm_le b
  set J' : ℝ × ℝ → V → V →L[ℝ] V := fun z y ↦ (J z y).toLinearMap.toContinuousLinearMap
  obtain ⟨C₀, hC₀, hcore⟩ :=
    ω.exists_forall_setIntegral_sobolevDensity_le_mul_setIntegral_floerLinearizationAdjoint_add hK
      (fun z _ ↦ hJ z) (fun z _ ↦ hKs z) (fun z _ ↦ hKt z) (fun z _ ↦ hu.contDiffAt) hc
  -- `w` is bounded below on the disc `K` by some `m > 0`, so that `1 ≤ m⁻¹ w` there.
  obtain ⟨m, hm, hmK⟩ := hK.exists_forall_le' hwc.continuousOn hwb
  have hΛK (z : ℝ × ℝ) (hz : z ∈ K) : 1 ≤ m⁻¹ * w z := (one_le_inv_mul₀ hm).2 (hmK z hz)
  -- A cutoff `β` equal to `1` near `‖z‖ ≤ a` and vanishing near `‖z‖ ≥ b`.
  obtain ⟨β, hβ, hβ01, hβ1, hβ0, hβK⟩ :=
    (isCompact_setOf_norm_equivRealProdCLM_symm_le a).exists_contDiff_cutoff_sublevel
      Complex.equivRealProdCLM.symm.continuous.norm hab
  obtain ⟨C₁, hC₁, herr⟩ := ω.exists_integral_mul_norm_floerLinearizationAdjoint_smul_sq_le
    (J := J') hJ hKs hKt hu hw hwc (hβ.of_le (by simp)) hβ01 hK fun z hz ↦ hβK z (not_le.1 hz)
  refine ⟨C₀ * (m⁻¹ * (2 + C₁) + 1), by positivity, fun η hη hηc ↦ ?_⟩
  set η₀ : ℝ × ℝ → V →L[ℝ] ℝ := fun z ↦ β z • η z
  have hη₀ : ContDiff ℝ 2 η₀ := (hβ.of_le (by simp)).smul hη
  have hη₀K : tsupport η₀ ⊆ K := fun z hz ↦ by
    rw [mem_ofPred_eq]
    exact (not_le.1 fun h ↦ notMem_tsupport_iff_eventuallyEq.2 (hβ0 z h)
      (tsupport_smul_subset_left _ _ hz)).le
  set X := ∫ z, w z * ‖ω.floerLinearizationAdjoint J' Ks Kt u η z‖ ^ 2
  set Y := ∫ z in K, ‖η z‖ ^ 2
  have hX : 0 ≤ X := integral_nonneg fun z ↦ mul_nonneg (hw z) (sq_nonneg _)
  have hY : 0 ≤ Y := setIntegral_nonneg hK.measurableSet fun _ _ ↦ sq_nonneg _
  -- The cutoff does not increase the `L²` norm on `K`.
  have hη₀Y : ∫ z in K, ‖η₀ z‖ ^ 2 ≤ Y :=
    setIntegral_mono_on ((hη₀.continuous.norm.pow 2).continuousOn.integrableOn_compact hK)
      ((hη.continuous.norm.pow 2).continuousOn.integrableOn_compact hK) hK.measurableSet
      fun z _ ↦ by
        simp only [η₀, norm_smul, Real.norm_eq_abs, abs_of_nonneg (hβ01 z).1, mul_pow]
        exact mul_le_of_le_one_left (by positivity) (pow_le_one₀ (hβ01 z).1 (hβ01 z).2)
  have h : m⁻¹ * (2 * X + C₁ * Y) + Y ≤ (m⁻¹ * (2 + C₁) + 1) * (X + Y) := by
    nlinarith [mul_nonneg (mul_nonneg (inv_pos.2 hm).le hC₁) hX, mul_nonneg (inv_pos.2 hm).le hY]
  calc _ ≤ ∫ z in K, sobolevDensity η₀ z :=
        setIntegral_sobolevDensity_le_of_eventuallyEq_one
          (isCompact_setOf_norm_equivRealProdCLM_symm_le a).measurableSet hK
          (ofPred_subset_ofPred.2 fun _ hz ↦ hz.trans hab.le) hβ1 (hη₀.of_le one_le_two)
    _ ≤ C₀ * (m⁻¹ * (∫ z, w z * ‖ω.floerLinearizationAdjoint J' Ks Kt u η₀ z‖ ^ 2) +
          ∫ z in K, ‖η₀ z‖ ^ 2) :=
        ω.setIntegral_sobolevDensity_le_mul_integral_mul_norm_floerLinearizationAdjoint_add
          (J := J') isOpen_univ (fun z _ ↦ hJ z) (fun z _ ↦ hKs z) (fun z _ ↦ hKt z)
          (fun z _ ↦ hu.contDiffAt) hw hwc.continuousOn hK (inv_pos.2 hm).le hΛK hC₀ hcore hη₀
          (subset_univ _) hη₀K
    _ ≤ C₀ * (m⁻¹ * (2 * X + C₁ * Y) + Y) := by
        gcongr
        exact herr (hη.of_le one_le_two) hηc
    _ ≤ C₀ * ((m⁻¹ * (2 + C₁) + 1) * (X + Y)) := mul_le_mul_of_nonneg_left h hC₀
    _ = _ := by ring

/-- **The formal adjoint and the `L²` norm on a cut-off covector field, pointwise.** If
`0 ≤ f ≤ 1`, `‖df‖ ≤ M` and `‖J‖ ≤ B` at `z`, then
`‖D^* (f η)‖² + ‖f η‖² ≤ (2 (M (1 + B))² + 2) (‖D^* η‖² + ‖η‖²)` at `z`. -/
private theorem norm_floerLinearizationAdjoint_fun_smul_sq_add_sq_le {ω : SymplecticForm V}
    {J : ℝ × ℝ → V → V →L[ℝ] V} {Ks Kt : ℝ × ℝ → V → ℝ} {u : ℝ × ℝ → V}
    {η : ℝ × ℝ → V →L[ℝ] ℝ} {f : ℝ × ℝ → ℝ} {z : ℝ × ℝ} (hf : DifferentiableAt ℝ f z)
    (hη : DifferentiableAt ℝ η z) (hJu : DifferentiableAt ℝ (fun w ↦ J w (u w)) z)
    (hf01 : f z ∈ Icc 0 1) {M B : ℝ} (hM : ‖fderiv ℝ f z‖ ≤ M) (hB : ‖J z (u z)‖ ≤ B) :
    ‖ω.floerLinearizationAdjoint J Ks Kt u (fun w ↦ f w • η w) z‖ ^ 2 + ‖f z • η z‖ ^ 2 ≤
      (2 * (M * (1 + B)) ^ 2 + 2) *
        (‖ω.floerLinearizationAdjoint J Ks Kt u η z‖ ^ 2 + ‖η z‖ ^ 2) := by
  have h := norm_floerLinearizationAdjoint_fun_smul_sq_le (ω := ω) (Ks := Ks) (Kt := Kt) hf hη
    hJu (abs_le.2 ⟨by linarith [hf01.1], hf01.2⟩) hM hB
  have h₀ : ‖f z • η z‖ ^ 2 ≤ ‖η z‖ ^ 2 := by
    rw [norm_smul, Real.norm_eq_abs, mul_pow, sq_abs]
    exact mul_le_of_le_one_left (sq_nonneg _) (pow_le_one₀ hf01.1 hf01.2)
  nlinarith [sq_nonneg ‖ω.floerLinearizationAdjoint J Ks Kt u η z‖,
    mul_nonneg (sq_nonneg (M * (1 + B))) (sq_nonneg ‖η z‖)]

/-- **The `L²` estimate of the formal adjoint on a disc.** Let `a < b`, and suppose that at every
`z` in the disc `‖w‖ ≤ b` the structure `J(z, u z)` is `ω`-compatible, `J` is `C¹` and the
Hamiltonians `K_s`, `K_t` are `C²` at `(z, u z)`, and `u` is `C¹` at `z`. Then there is a constant
`C ≥ 0` such that every `C²` covector field `η` satisfies

`∫_{‖w‖ ≤ a} (‖∂s η‖² + ‖∂t η‖² + ‖η‖²) ≤ C ∫_{‖w‖ ≤ b} (‖D_u^* η‖² + ‖η‖²)`

for the formal adjoint `D_u^*` of the linearized Floer operator, the discs read in real
coordinates. A cutoff between the two discs reduces this to the estimate on covector fields
supported in the larger disc,
`exists_forall_setIntegral_sobolevDensity_le_mul_setIntegral_floerLinearizationAdjoint_add`. This
is the adjoint counterpart of
`exists_forall_setIntegral_le_mul_integral_floerLinearization_add_of_lt`. -/
theorem
    exists_forall_setIntegral_sobolevDensity_le_mul_setIntegral_floerLinearizationAdjoint_add_of_lt
    (ω : SymplecticForm V) {J : ℝ × ℝ → V → AlmostComplexStructure V} {Ks Kt : ℝ × ℝ → V → ℝ}
    {u : ℝ × ℝ → V} {a b : ℝ} (hab : a < b)
    (hJ : ∀ z, ‖Complex.equivRealProdCLM.symm z‖ ≤ b → ContDiffAt ℝ 1
      (fun p : (ℝ × ℝ) × V ↦ (J p.1 p.2).toLinearMap.toContinuousLinearMap) (z, u z))
    (hKs : ∀ z, ‖Complex.equivRealProdCLM.symm z‖ ≤ b → ContDiffAt ℝ 2 (uncurry Ks) (z, u z))
    (hKt : ∀ z, ‖Complex.equivRealProdCLM.symm z‖ ≤ b → ContDiffAt ℝ 2 (uncurry Kt) (z, u z))
    (hu : ∀ z, ‖Complex.equivRealProdCLM.symm z‖ ≤ b → ContDiffAt ℝ 1 u z)
    (hc : ∀ z, ‖Complex.equivRealProdCLM.symm z‖ ≤ b → ω.Compatible (J z (u z))) :
    ∃ C, 0 ≤ C ∧ ∀ ⦃η : ℝ × ℝ → V →L[ℝ] ℝ⦄, ContDiff ℝ 2 η →
      ∫ z in {z | ‖Complex.equivRealProdCLM.symm z‖ ≤ a}, sobolevDensity η z ≤
        C * ∫ z in {z | ‖Complex.equivRealProdCLM.symm z‖ ≤ b},
          (‖ω.floerLinearizationAdjoint (fun w y ↦ (J w y).toLinearMap.toContinuousLinearMap)
            Ks Kt u η z‖ ^ 2 + ‖η z‖ ^ 2) := by
  set J' : ℝ × ℝ → V → V →L[ℝ] V := fun w y ↦ (J w y).toLinearMap.toContinuousLinearMap
  set K := {z : ℝ × ℝ | ‖Complex.equivRealProdCLM.symm z‖ ≤ b}
  have hK : IsCompact K := isCompact_setOf_norm_equivRealProdCLM_symm_le b
  obtain ⟨C₀, hC₀, hint⟩ :=
    ω.exists_forall_setIntegral_sobolevDensity_le_mul_setIntegral_floerLinearizationAdjoint_add
      hK hJ hKs hKt hu hc
  -- A cutoff `β` equal to `1` near `‖w‖ ≤ a` and vanishing near `‖w‖ ≥ b`.
  obtain ⟨β, hβ, hβ01, hβ1, hβ0, -⟩ :=
    (isCompact_setOf_norm_equivRealProdCLM_symm_le a).exists_contDiff_cutoff_sublevel
      Complex.equivRealProdCLM.symm.continuous.norm hab
  have hβ2 : ContDiff ℝ 2 β := hβ.of_le (by simp)
  -- Bounds on `K` for `J` along `u` and for the derivative of the cutoff.
  obtain ⟨B, hB⟩ := hK.exists_bound_of_continuousOn (f := fun z ↦ J' z (u z)) fun z hz ↦
    ((hJ z hz).continuousAt.comp₂ continuousAt_id (hu z hz).continuousAt).continuousWithinAt
  obtain ⟨M, hM⟩ := hK.exists_bound_of_continuousOn (hβ2.continuous_fderiv two_ne_zero).continuousOn
  refine ⟨C₀ * (2 * (max M 0 * (1 + max B 0)) ^ 2 + 2), by positivity, fun η hη ↦ ?_⟩
  set η₀ : ℝ × ℝ → V →L[ℝ] ℝ := fun w ↦ β w • η w
  have hη₀ : ContDiff ℝ 2 η₀ := hβ2.smul hη
  have hη₀K : tsupport η₀ ⊆ K := fun z hz ↦ by
    rw [mem_ofPred_eq]
    exact (not_le.1 fun h ↦ notMem_tsupport_iff_eventuallyEq.2 (hβ0 z h)
      (tsupport_smul_subset_left _ _ hz)).le
  have hI {g : ℝ × ℝ → ℝ} (hg : ContinuousOn g K) : IntegrableOn g K := hg.integrableOn_compact hK
  have hDc {θ : ℝ × ℝ → V →L[ℝ] ℝ} (hθ : ContDiff ℝ 2 θ) :
      ContinuousOn (ω.floerLinearizationAdjoint J' Ks Kt u θ) K := fun z hz ↦
    (continuousAt_floerLinearizationAdjoint (hJ z hz) (hKs z hz) (hKt z hz) (hu z hz)
      (hθ.of_le one_le_two).contDiffAt).continuousWithinAt
  -- Pointwise on `K`, the cutoff costs `2 c² ‖η‖²` in the adjoint and nothing in `L²`.
  have hpt (z : ℝ × ℝ) (hz : z ∈ K) :=
    norm_floerLinearizationAdjoint_fun_smul_sq_add_sq_le (ω := ω) (Ks := Ks) (Kt := Kt)
      (hβ2.differentiable two_ne_zero z) (hη.differentiable two_ne_zero z)
      (((hJ z hz).differentiableAt one_ne_zero).comp (f := fun x ↦ (x, u x)) z
        (differentiableAt_id.prodMk ((hu z hz).differentiableAt one_ne_zero))) (hβ01 z)
      ((hM z hz).trans (le_max_left M 0)) ((hB z hz).trans (le_max_left B 0))
  have hF : ContinuousOn
      (fun z ↦ ‖ω.floerLinearizationAdjoint J' Ks Kt u η z‖ ^ 2 + ‖η z‖ ^ 2) K :=
    ((hDc hη).norm.pow 2).add (hη.continuous.norm.pow 2).continuousOn
  calc _ ≤ ∫ z in K, sobolevDensity η₀ z :=
        setIntegral_sobolevDensity_le_of_eventuallyEq_one
          (isCompact_setOf_norm_equivRealProdCLM_symm_le a).measurableSet hK
          (ofPred_subset_ofPred.2 fun _ hz ↦ hz.trans hab.le) hβ1 (hη₀.of_le one_le_two)
    _ ≤ C₀ * ∫ z in K, (‖ω.floerLinearizationAdjoint J' Ks Kt u η₀ z‖ ^ 2 + ‖η₀ z‖ ^ 2) :=
        hint hη₀ hη₀K
    _ ≤ C₀ * ∫ z in K, (2 * (max M 0 * (1 + max B 0)) ^ 2 + 2) *
          (‖ω.floerLinearizationAdjoint J' Ks Kt u η z‖ ^ 2 + ‖η z‖ ^ 2) :=
        mul_le_mul_of_nonneg_left (setIntegral_mono_on (hI (((hDc hη₀).norm.pow 2).add
          (hη₀.continuous.norm.pow 2).continuousOn)) (hI (continuousOn_const.mul hF))
          hK.measurableSet hpt) hC₀
    _ = _ := by rw [integral_const_mul, mul_assoc]

end Disc

end TauCeti.SymplecticForm
