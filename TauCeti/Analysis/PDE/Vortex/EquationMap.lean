/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.Vortex.Gauge.Fixed
public import TauCeti.Analysis.PDE.Vortex.Multiplier
public import TauCeti.Analysis.PDE.Vortex.WindingPhase
public import TauCeti.Analysis.Sobolev.BesselPotential.Algebra
public import TauCeti.Analysis.Sobolev.BesselPotential.Operator
import TauCeti.Analysis.Sobolev.BesselPotential.SmoothMultiplier
import TauCeti.Analysis.Sobolev.BesselPotential.Embedding
import TauCeti.MeasureTheory.Function.Lp.Basic

/-!
# The plane vortex equation on the Sobolev scale

The framed degree-`m` plane vortex fields form the affine space
`A_m^(k+1) = (a_m, α_m) + H^(k+1)(ℂ; iT*ℂ ⊕ ℂ)` (`TauCeti.Vortex.framedFieldSpace`), centered at
a smooth reference pair which equals `(-i m dθ, exp (i m θ))` outside a disc. This file shows
that the vortex equation `∂bar_a α = 0`, `*iF_a = (1 - |α|²) / 8` and its deformation complex
are maps between the expected Sobolev spaces, for every integer `k ≥ 1`:

* the equation defect `TauCeti.Vortex.equation x` of a `C¹` field `x ∈ A_m^(k+1)` has its three
  real components in `H^k(ℂ)` (`equation_apply_mem_realSobolevFunctions`);
* at every `x ∈ A_m^(k+1)`, the linearized equation `d₁ = TauCeti.Vortex.linearizedEquation x`
  maps `C¹` variations in `H^(k+1)` to `H^k` (`linearizedEquation_apply_mem_realSobolevFunctions`);
* at every `x ∈ A_m^(k+1)`, the infinitesimal gauge action
  `d₀ = TauCeti.Vortex.gaugeDirection x` maps `C¹` phases in `H^(k+2)` to `H^(k+1)`
  (`gaugeDirection_mem_sobolevFields`);
* at every `x ∈ A_m^(k+1)`, the gauge-fixed operator `L_x = d₀* ⊕ d₁`
  (`TauCeti.Vortex.gaugeFixedOperator x`) and its formal adjoint `L_x*`
  (`TauCeti.Vortex.gaugeFixedAdjoint x`) map `C¹` fields in `H^(k+1)` to `H^k`
  (`gaugeFixedOperator_mem_sobolevFields`, `gaugeFixedAdjoint_mem_sobolevFields`).

The reference field is an exact vortex outside the cutoff disc (`equation_referenceField_eq_zero`).
Its equation defect is therefore smooth with compact support, and lies in every `H^s`. The exact
quadratic expansion `equation (x_m + y) = equation x_m + d₁ y + quadraticTerm y` about the reference
field (`TauCeti.Vortex.equation_add_smul`) then reduces the equation map to three kinds of terms:
first derivatives of `H^(k+1)` functions, which lie in `H^k`; products of a reference coordinate,
which is smooth with bounded derivatives, with an `H^(k+1)` function; and products of two `H^(k+1)`
functions, which lie in `H^(k+1)` because `H^(k+1)(ℂ)` is an algebra for `k ≥ 1`
(`mul_mem_realSobolevFunctions_of_mem_framedFieldSpace`).

The fields are pointwise representatives and the operators are classical differential expressions,
so these membership statements assume `C¹` regularity of the field, variation or phase.

**The equation map between Hilbert spaces.** The second part of the file realizes the equation, in
the affine chart `y ↦ x_m + y` of `A_m^(k+1)`, as a smooth map of Hilbert spaces. Its coordinates
are the complexified coordinates of the variation, elements of Mathlib's Bessel-potential space
`H^(k+1)(ℂ) = H^{k+1,2}(ℂ, ℂ)`, on which the vortex equation is a polynomial map. For `k ≥ 1`:

* `sobolevEquation f m hk : (Fin 4 → H^(k+1)(ℂ)) → (Fin 3 → H^k(ℂ))` is the sum of the reference
  defect `sobolevReferenceDefect`, the linearized equation `sobolevLinearizedEquation f m hk 0` at
  the reference field, and the quadratic term `sobolevQuadraticTerm`. It is analytic
  (`contDiff_sobolevEquation`), and its derivative at `y` is the complexified linearized equation
  `sobolevLinearizedEquation f m hk y` at `x_m + y` (`hasFDerivAt_sobolevEquation`).
  The derivatives in it are `BesselPotentialSpace.lineDerivCLM`, the coefficients of the reference
  field act by `referenceMulCLM`, and those of `x_m + y` by `fieldMulCLM`.
* A real field `y` lies in `sobolevFields s` exactly when its coordinates are, almost everywhere,
  the `L²` functions of some `u : Fin 4 → H^s(ℂ)`
  (`mem_sobolevFields_iff_exists_inclusionLp_ae_eq`). For such `u` and `C¹` fields, the Sobolev
  maps compute the pointwise ones: `sobolevEquation f m hk u` is almost everywhere
  `equation (x_m + y)` (`coeFn_inclusionLp_sobolevEquation_ae_eq`), and similarly for the linearized
  equation and the quadratic term. In particular, for a real `C¹` field `x ∈ A_m^(k+1)` whose
  difference with `x_m` has coordinates `u`, `x` is a vortex exactly when
  `sobolevEquation f m hk u = 0` (`sobolevEquation_eq_zero_iff`). Only these real zeros, at
  coordinates of real fields, are vortices: the complexified map can also vanish at non-real `u`,
  which corresponds to no field. For `k ≥ 2`, its restriction to the real subspace, whose zeros
  are exactly the vortices, is `TauCeti.Vortex.realSobolevEquation` in
  `TauCeti.Analysis.PDE.Vortex.FramedGauge.RealChart`.

No Fredholm property, slice or quotient is constructed here.

## References

* A. Jaffe and C. H. Taubes, *Vortices and Monopoles*, Progress in Physics 2, Birkhäuser, 1980,
  Chapter III.
* C. H. Taubes, *Arbitrary N-vortex solutions to the first order Ginzburg–Landau equations*,
  Comm. Math. Phys. 72 (1980), 277–292.
-/

public section

namespace TauCeti.Vortex

open Complex Filter Metric TemperedDistribution
open scoped Topology ContDiff

/-! ### The equation of the reference field -/

/-- Each component of the equation defect of the reference field lies in every Sobolev space. -/
theorem equation_referenceField_apply_mem_realSobolevFunctions (f : ContDiffBump (0 : ℝ))
    (m : ℕ) (s : ℝ) (i : Fin 3) :
    (fun z ↦ equation (referenceField f m) z i) ∈ realSobolevFunctions ℂ s 2 :=
  mem_realSobolevFunctions_of_hasCompactSupport
    (contDiff_euclidean.1 (contDiff_equation (contDiff_referenceField f m)
      ENat.coe_top_add_one.le) i)
    ((hasCompactSupport_equation_referenceField f m).comp_left
      (g := fun v : EuclideanSpace ℝ (Fin 3) ↦ v i) rfl) s

/-! ### The deformation complex and the equation map -/

/-- A first derivative of a `C¹` variation in `H^(k+1)` lies in `H^k`. -/
private theorem fderiv_apply_mem_of_mem_sobolevFields {k : ℕ}
    {y : ℂ → EuclideanSpace ℝ (Fin 4)} (hy : y ∈ sobolevFields (k + 1)) (hyc : ContDiff ℝ 1 y)
    (b : Fin 4) (v : ℂ) :
    (fun z ↦ fderiv ℝ (fun w ↦ y w b) z v) ∈ realSobolevFunctions ℂ k 2 :=
  fderiv_apply_mem_realSobolevFunctions (by norm_num) (by norm_num) k.cast_nonneg
    (contDiff_euclidean.1 hyc b) (mem_sobolevFields.1 hy b) v

/-- For `k ≥ 1`, a coordinate of a field of `A_m^(k+1)` times a coordinate of a variation in
`H^(k+1)` lies in `H^k`. -/
private theorem mul_apply_mem_of_mem_framedFieldSpace {f : ContDiffBump (0 : ℝ)} {m k : ℕ}
    (hk : 1 ≤ k) {x : ℂ → EuclideanSpace ℝ (Fin 4)} (hx : x ∈ framedFieldSpace f m (k + 1))
    {y : ℂ → EuclideanSpace ℝ (Fin 4)} (hy : y ∈ sobolevFields (k + 1)) (a b : Fin 4) :
    (fun z ↦ x z a * y z b) ∈ realSobolevFunctions ℂ k 2 := by
  have hcast : ((k + 1 : ℕ) : ℝ) = k + 1 := Nat.cast_succ k
  rw [← hcast] at hx hy
  exact realSobolevFunctions_mono (by norm_num) (by norm_num) (by rw [hcast]; linarith)
    (mul_mem_realSobolevFunctions_of_mem_framedFieldSpace (by omega) hx a
      (mem_sobolevFields.1 hy b))

/-- **The linearized equation on the Sobolev scale.** For an integer `k ≥ 1` and any field
`x ∈ A_m^(k+1)`, the linearized vortex equation `d₁ = linearizedEquation x` maps a `C¹`
variation in `H^(k+1)` to a defect with components in `H^k`. -/
theorem linearizedEquation_apply_mem_realSobolevFunctions {f : ContDiffBump (0 : ℝ)} {m k : ℕ}
    (hk : 1 ≤ k) {x : ℂ → EuclideanSpace ℝ (Fin 4)} (hx : x ∈ framedFieldSpace f m (k + 1))
    {y : ℂ → EuclideanSpace ℝ (Fin 4)} (hy : y ∈ sobolevFields (k + 1)) (hyc : ContDiff ℝ 1 y)
    (i : Fin 3) :
    (fun z ↦ linearizedEquation x y z i) ∈ realSobolevFunctions ℂ k 2 := by
  have hd := fderiv_apply_mem_of_mem_sobolevFields hy hyc
  have hp := mul_apply_mem_of_mem_framedFieldSpace hk hx hy
  fin_cases i
  · convert add_mem (add_mem (sub_mem (hd 0 I) (hd 1 1)) (hp 2 2)) (hp 3 3) using 1
    ext z
    simp
  · convert sub_mem (sub_mem (sub_mem (sub_mem (sub_mem (hd 2 1) (hd 3 I)) (hp 0 3)) (hp 3 0))
      (hp 1 2)) (hp 2 1) using 1
    ext z
    simp only [Fin.reduceFinMk, Fin.isValue, linearizedEquation_apply_one, Pi.sub_apply]
    ring
  · convert sub_mem (sub_mem (add_mem (add_mem (add_mem (hd 3 1) (hd 2 I)) (hp 0 2)) (hp 2 0))
      (hp 1 3)) (hp 3 1) using 1
    ext z
    simp only [Fin.reduceFinMk, Fin.isValue, linearizedEquation_apply_two, Pi.add_apply,
      Pi.sub_apply]
    ring

/-- The gauge-fixing row `d₀* y = ∂₁ y₀ + ∂₂ y₁ + p y₃ - q y₂` at a field `x ∈ A_m^(k+1)`,
`k ≥ 1`, maps a `C¹` variation in `H^(k+1)` to `H^k`. -/
theorem gaugeAdjoint_mem_realSobolevFunctions {f : ContDiffBump (0 : ℝ)} {m k : ℕ}
    (hk : 1 ≤ k) {x : ℂ → EuclideanSpace ℝ (Fin 4)} (hx : x ∈ framedFieldSpace f m (k + 1))
    {y : ℂ → EuclideanSpace ℝ (Fin 4)} (hy : y ∈ sobolevFields (k + 1)) (hyc : ContDiff ℝ 1 y) :
    gaugeAdjoint x y ∈ realSobolevFunctions ℂ k 2 := by
  have hd := fderiv_apply_mem_of_mem_sobolevFields hy hyc
  have hp := mul_apply_mem_of_mem_framedFieldSpace hk hx hy
  convert sub_mem (add_mem (add_mem (hd 0 1) (hd 1 I)) (hp 2 3)) (hp 3 2) using 1
  ext z
  simp

/-- **The gauge-fixed operator on the Sobolev scale.** For an integer `k ≥ 1` and any field
`x ∈ A_m^(k+1)`, the gauge-fixed operator `L_x = d₀* ⊕ d₁` maps a `C¹` variation in `H^(k+1)` to
`H^k(ℂ; ℝ ⊕ ℝ ⊕ ℂ)`. -/
theorem gaugeFixedOperator_mem_sobolevFields {f : ContDiffBump (0 : ℝ)} {m k : ℕ}
    (hk : 1 ≤ k) {x : ℂ → EuclideanSpace ℝ (Fin 4)} (hx : x ∈ framedFieldSpace f m (k + 1))
    {y : ℂ → EuclideanSpace ℝ (Fin 4)} (hy : y ∈ sobolevFields (k + 1)) (hyc : ContDiff ℝ 1 y) :
    gaugeFixedOperator x y ∈ sobolevFields k := by
  refine mem_sobolevFields.2 fun i ↦ ?_
  fin_cases i
  · simpa [-gaugeAdjoint_def] using gaugeAdjoint_mem_realSobolevFunctions hk hx hy hyc
  · simpa using linearizedEquation_apply_mem_realSobolevFunctions hk hx hy hyc 0
  · simpa using linearizedEquation_apply_mem_realSobolevFunctions hk hx hy hyc 1
  · simpa using linearizedEquation_apply_mem_realSobolevFunctions hk hx hy hyc 2

/-- **The adjoint gauge-fixed operator on the Sobolev scale.** For an integer `k ≥ 1` and any
field `x ∈ A_m^(k+1)`, the formal adjoint `L_x*` maps a `C¹` field in `H^(k+1)(ℂ; ℝ ⊕ ℝ ⊕ ℂ)` to
a variation in `H^k`. -/
theorem gaugeFixedAdjoint_mem_sobolevFields {f : ContDiffBump (0 : ℝ)} {m k : ℕ}
    (hk : 1 ≤ k) {x : ℂ → EuclideanSpace ℝ (Fin 4)} (hx : x ∈ framedFieldSpace f m (k + 1))
    {η : ℂ → EuclideanSpace ℝ (Fin 4)} (hη : η ∈ sobolevFields (k + 1)) (hηc : ContDiff ℝ 1 η) :
    gaugeFixedAdjoint x η ∈ sobolevFields k := by
  have hd := fderiv_apply_mem_of_mem_sobolevFields hη hηc
  have hp := mul_apply_mem_of_mem_framedFieldSpace hk hx hη
  refine mem_sobolevFields.2 fun i ↦ ?_
  fin_cases i
  · convert sub_mem (add_mem (sub_mem (neg_mem (hd 0 1)) (hd 1 I)) (hp 2 3)) (hp 3 2) using 1
    ext z
    simp only [Fin.zero_eta, Fin.isValue, gaugeFixedAdjoint_apply_zero, Pi.sub_apply,
      Pi.add_apply, Pi.neg_apply]
  · convert sub_mem (sub_mem (add_mem (neg_mem (hd 0 I)) (hd 1 1)) (hp 2 2)) (hp 3 3) using 1
    ext z
    simp only [Fin.mk_one, Fin.isValue, gaugeFixedAdjoint_apply_one, Pi.sub_apply, Pi.add_apply,
      Pi.neg_apply]
  · convert add_mem (sub_mem (add_mem (sub_mem (sub_mem (neg_mem (hd 2 1)) (hd 3 I)) (hp 1 2))
      (hp 0 3)) (hp 3 0)) (hp 2 1) using 1
    ext z
    simp only [Fin.reduceFinMk, Fin.isValue, gaugeFixedAdjoint_apply_two, Pi.add_apply,
      Pi.sub_apply, Pi.neg_apply]
  · convert add_mem (add_mem (sub_mem (sub_mem (add_mem (neg_mem (hd 3 1)) (hd 2 I)) (hp 0 2))
      (hp 1 3)) (hp 2 0)) (hp 3 1) using 1
    ext z
    simp only [Fin.reduceFinMk, Fin.isValue, gaugeFixedAdjoint_apply_three, Pi.add_apply,
      Pi.sub_apply, Pi.neg_apply]

/-- The quadratic remainder of the vortex equation maps `H^s` fields, `s > 1`, to `H^s`. -/
theorem quadraticTerm_apply_mem_realSobolevFunctions {s : ℝ} (hs : 1 < s)
    {y : ℂ → EuclideanSpace ℝ (Fin 4)} (hy : y ∈ sobolevFields s) (i : Fin 3) :
    (fun z ↦ quadraticTerm y z i) ∈ realSobolevFunctions ℂ s 2 := by
  have hp (a b : Fin 4) : (fun z ↦ y z a * y z b) ∈ realSobolevFunctions ℂ s 2 :=
    mul_mem_realSobolevFunctions (finrank_real_complex_lt_two_mul hs) (mem_sobolevFields.1 hy a)
      (mem_sobolevFields.1 hy b)
  fin_cases i
  · convert Submodule.smul_mem _ (1 / 2 : ℝ) (add_mem (hp 2 2) (hp 3 3)) using 1
    ext z
    simp only [Fin.zero_eta, Fin.isValue, quadraticTerm_apply_zero, Pi.smul_apply, Pi.add_apply,
      smul_eq_mul]
    ring
  · convert neg_mem (add_mem (hp 0 3) (hp 1 2)) using 1
    ext z
    simp only [Fin.mk_one, Fin.isValue, quadraticTerm_apply_one, Pi.neg_apply, Pi.add_apply]
    ring
  · convert sub_mem (hp 0 2) (hp 1 3) using 1
    ext z
    simp

/-- **The vortex equation map on the Sobolev scale.** For an integer `k ≥ 1`, the equation
defect `(*iF_a - (1 - |α|²) / 8, Re ∂bar_a α, Im ∂bar_a α)` of a `C¹` field `x ∈ A_m^(k+1)` has
its three components in `H^k`. -/
theorem equation_apply_mem_realSobolevFunctions {f : ContDiffBump (0 : ℝ)} {m k : ℕ}
    (hk : 1 ≤ k) {x : ℂ → EuclideanSpace ℝ (Fin 4)} (hx : x ∈ framedFieldSpace f m (k + 1))
    (hxc : ContDiff ℝ 1 x) (i : Fin 3) :
    (fun z ↦ equation x z i) ∈ realSobolevFunctions ℂ k 2 := by
  set y := x - referenceField f m
  have hy : y ∈ sobolevFields (k + 1) := mem_framedFieldSpace.1 hx
  have hyc : ContDiff ℝ 1 y := hxc.sub ((contDiff_referenceField f m).of_le (by simp))
  -- Expand the equation exactly about the reference field.
  have hexp (z : ℂ) : equation x z = equation (referenceField f m) z +
      linearizedEquation (referenceField f m) y z + quadraticTerm y z := by
    have h := equation_add_smul (z := z)
      (fun j ↦ (contDiff_euclidean.1 (contDiff_referenceField f m) j).differentiable
        (by simp) z)
      (fun j ↦ (contDiff_euclidean.1 hyc j).differentiable one_ne_zero z) 1
    simpa only [one_smul, one_pow, y, add_sub_cancel] using h
  have hq := realSobolevFunctions_mono (p := 2) (by norm_num) (by norm_num)
    (by linarith : (k : ℝ) ≤ k + 1)
    (quadraticTerm_apply_mem_realSobolevFunctions (by norm_cast; omega) hy i)
  convert add_mem (add_mem (equation_referenceField_apply_mem_realSobolevFunctions f m k i)
    (linearizedEquation_apply_mem_realSobolevFunctions hk
      (referenceField_mem_framedFieldSpace f m _) hy hyc i)) hq using 1
  ext z
  simp [hexp z]

/-- **The infinitesimal gauge action on the Sobolev scale.** For an integer `k ≥ 1` and any
field `x ∈ A_m^(k+1)`, the infinitesimal gauge action `d₀ = gaugeDirection x` maps a `C¹` phase
in `H^(k+2)` to a variation in `H^(k+1)`. -/
theorem gaugeDirection_mem_sobolevFields {f : ContDiffBump (0 : ℝ)} {m k : ℕ} (hk : 1 ≤ k)
    {x : ℂ → EuclideanSpace ℝ (Fin 4)} (hx : x ∈ framedFieldSpace f m (k + 1)) {g : ℂ → ℝ}
    (hg : g ∈ realSobolevFunctions ℂ (k + 2) 2) (hgc : ContDiff ℝ 1 g) :
    gaugeDirection x g ∈ sobolevFields (k + 1) := by
  have hcast : ((k + 1 : ℕ) : ℝ) = k + 1 := Nat.cast_succ k
  have hd (v : ℂ) : (fun z ↦ fderiv ℝ g z v) ∈ realSobolevFunctions ℂ (k + 1) 2 :=
    fderiv_apply_mem_realSobolevFunctions (by norm_num) (by norm_num) (by positivity) hgc
      (by convert hg using 2; ring) v
  have hx' : x ∈ framedFieldSpace f m ((k + 1 : ℕ) : ℝ) := by rwa [hcast]
  have hg' : g ∈ realSobolevFunctions ℂ ((k + 1 : ℕ) : ℝ) 2 :=
    realSobolevFunctions_mono (by norm_num) (by norm_num) (by rw [hcast]; linarith) hg
  have hp (a : Fin 4) : (fun z ↦ x z a * g z) ∈ realSobolevFunctions ℂ (k + 1) 2 :=
    hcast ▸ mul_mem_realSobolevFunctions_of_mem_framedFieldSpace (by omega) hx' a hg'
  refine mem_sobolevFields.2 fun i ↦ ?_
  fin_cases i
  · convert neg_mem (hd 1) using 1
    ext z
    simp
  · convert neg_mem (hd I) using 1
    ext z
    simp
  · convert neg_mem (hp 3) using 1
    ext z
    simp [mul_comm]
  · convert hp 2 using 1
    ext z
    simp [mul_comm]

/-! ### The equation map between Sobolev spaces -/

noncomputable section Smooth

open BesselPotentialSpace ContinuousLinearMap MeasureTheory
open scoped BesselPotentialSpace

variable {f : ContDiffBump (0 : ℝ)} {m k : ℕ}

private theorem finrank_lt_two_mul_natCast_add_one (hk : 1 ≤ k) :
    (Module.finrank ℝ ℂ : ℝ) < 2 * ((k : ℝ) + 1) :=
  finrank_real_complex_lt_two_mul (by linarith [show (1 : ℝ) ≤ k from mod_cast hk])

variable (f m k) in
/-- Multiplication by the coordinate `a` of the reference field `x_m`, as a bounded operator on
`H^k(ℂ)`. The coordinates of `x_m` are smooth with bounded derivatives, so they multiply every
integer-order Sobolev space into itself. -/
def referenceMulCLM (a : Fin 4) : H^{(k : ℝ)}(ℂ) →L[ℂ] H^{(k : ℝ)}(ℂ) :=
  mapCLM (TemperedDistribution.smulLeftCLM ℂ fun z ↦ (referenceField f m z a : ℂ)) fun u ↦
    u.memSobolev_toDistr.smulLeftCLM_of_norm_iteratedFDeriv_le (by norm_num) (by norm_num)
      (hasTemperateGrowth_ofReal_referenceField_apply f m a)
      fun n _ ↦ exists_norm_iteratedFDeriv_ofReal_referenceField_apply_le f m a n

/-- `referenceMulCLM f m k a` multiplies the underlying tempered distribution by the coordinate
`a` of the reference field. -/
@[simp]
theorem toDistr_referenceMulCLM (a : Fin 4) (u : H^{(k : ℝ)}(ℂ)) :
    (referenceMulCLM f m k a u).toDistr =
      TemperedDistribution.smulLeftCLM ℂ (fun z ↦ (referenceField f m z a : ℂ)) u.toDistr :=
  toDistr_mapCLM _ _ u

/-- The `L²` function of `x_m,a u` is the pointwise product. -/
theorem coeFn_inclusionLp_referenceMulCLM_ae_eq (a : Fin 4) (u : H^{(k : ℝ)}(ℂ)) :
    ⇑(inclusionLp (k.cast_nonneg : (0 : ℝ) ≤ k) (referenceMulCLM f m k a u)) =ᵐ[volume]
      fun z ↦ (referenceField f m z a : ℂ) * inclusionLp (k.cast_nonneg : (0 : ℝ) ≤ k) u z := by
  obtain ⟨C, hC⟩ := exists_norm_iteratedFDeriv_ofReal_referenceField_apply_le f m a 0
  simpa only [smul_eq_mul] using coeFn_inclusionLp_ae_eq_smul_of_toDistr_eq_smulLeftCLM _ _
    (hasTemperateGrowth_ofReal_referenceField_apply f m a) (C := C)
    (fun z ↦ by simpa using hC z) (toDistr_referenceMulCLM a u)

variable (f m) in
/-- Multiplication by the coordinate `a` of `x_m + y`, for complexified coordinates
`y ∈ H^(k+1)(ℂ)⁴` of a variation, as a bounded operator `H^(k+1)(ℂ) → H^k(ℂ)`. The product with
`y_a` uses that `H^(k+1)(ℂ)` is an algebra for `k ≥ 1`. -/
def fieldMulCLM (hk : 1 ≤ k) (y : Fin 4 → H^{(k : ℝ) + 1}(ℂ)) (a : Fin 4) :
    H^{(k : ℝ) + 1}(ℂ) →L[ℂ] H^{(k : ℝ)}(ℂ) :=
  (referenceMulCLM f m k a).comp (inclusion (lt_add_one _).le) +
    (inclusion (lt_add_one _).le).comp (mulCLM (finrank_lt_two_mul_natCast_add_one hk) (y a))

/-- `fieldMulCLM` is the sum of the multiplications by the reference coordinate and by `y_a`;
`hs` is any proof that `H^(k+1)(ℂ)` is an algebra. -/
theorem fieldMulCLM_apply (hk : 1 ≤ k) (hs : (Module.finrank ℝ ℂ : ℝ) < 2 * ((k : ℝ) + 1))
    (y : Fin 4 → H^{(k : ℝ) + 1}(ℂ)) (a : Fin 4) (v : H^{(k : ℝ) + 1}(ℂ)) :
    fieldMulCLM f m hk y a v = referenceMulCLM f m k a (inclusion (lt_add_one _).le v) +
      inclusion (lt_add_one _).le (mulCLM hs (y a) v) :=
  (rfl)

variable (f m) in
/-- **The linearized vortex equation between Sobolev spaces.** For `k ≥ 1` and complexified
coordinates `y ∈ H^(k+1)(ℂ)⁴`, the complexified linearized equation `d₁`
(`TauCeti.Vortex.linearizedEquation`) at `x_m + y`, as a bounded operator `H^(k+1)(ℂ)⁴ → H^k(ℂ)³`.
When `y` holds the coordinates of a real variation, it computes the linearized equation at the
field `x_m + y` of `A_m^(k+1)` (`coeFn_inclusionLp_sobolevLinearizedEquation_ae_eq`). Its rows are
those of `linearizedEquation`, with the classical derivatives replaced by `lineDerivCLM` and the
coefficients of `x_m + y` by `fieldMulCLM`. -/
def sobolevLinearizedEquation (hk : 1 ≤ k) (y : Fin 4 → H^{(k : ℝ) + 1}(ℂ)) :
    (Fin 4 → H^{(k : ℝ) + 1}(ℂ)) →L[ℂ] (Fin 3 → H^{(k : ℝ)}(ℂ)) :=
  let D (v : ℂ) (b : Fin 4) : (Fin 4 → H^{(k : ℝ) + 1}(ℂ)) →L[ℂ] H^{(k : ℝ)}(ℂ) :=
    (lineDerivCLM ENNReal.one_lt_two ENNReal.ofNat_ne_top v).comp (proj b)
  let X (a b : Fin 4) : (Fin 4 → H^{(k : ℝ) + 1}(ℂ)) →L[ℂ] H^{(k : ℝ)}(ℂ) :=
    (fieldMulCLM f m hk y a).comp (proj b)
  pi ![D I 0 - D 1 1 + X 2 2 + X 3 3,
    D 1 2 - D I 3 - X 0 3 - X 3 0 - X 1 2 - X 2 1,
    D 1 3 + D I 2 + X 0 2 + X 2 0 - X 1 3 - X 3 1]

section apply

variable (hk : 1 ≤ k) (y h : Fin 4 → H^{(k : ℝ) + 1}(ℂ))

/-- The first row of `sobolevLinearizedEquation`, the linearized curvature equation. -/
theorem sobolevLinearizedEquation_apply_zero :
    sobolevLinearizedEquation f m hk y h 0 =
      lineDerivCLM ENNReal.one_lt_two ENNReal.ofNat_ne_top I (h 0) -
        lineDerivCLM ENNReal.one_lt_two ENNReal.ofNat_ne_top 1 (h 1) +
        fieldMulCLM f m hk y 2 (h 2) + fieldMulCLM f m hk y 3 (h 3) :=
  (rfl)

/-- The second row of `sobolevLinearizedEquation`, the real part of the linearized `∂bar_a α`. -/
theorem sobolevLinearizedEquation_apply_one :
    sobolevLinearizedEquation f m hk y h 1 =
      lineDerivCLM ENNReal.one_lt_two ENNReal.ofNat_ne_top 1 (h 2) -
        lineDerivCLM ENNReal.one_lt_two ENNReal.ofNat_ne_top I (h 3) -
        fieldMulCLM f m hk y 0 (h 3) - fieldMulCLM f m hk y 3 (h 0) -
        fieldMulCLM f m hk y 1 (h 2) - fieldMulCLM f m hk y 2 (h 1) :=
  (rfl)

/-- The third row of `sobolevLinearizedEquation`, the imaginary part of the linearized
`∂bar_a α`. -/
theorem sobolevLinearizedEquation_apply_two :
    sobolevLinearizedEquation f m hk y h 2 =
      lineDerivCLM ENNReal.one_lt_two ENNReal.ofNat_ne_top 1 (h 3) +
        lineDerivCLM ENNReal.one_lt_two ENNReal.ofNat_ne_top I (h 2) +
        fieldMulCLM f m hk y 0 (h 2) + fieldMulCLM f m hk y 2 (h 0) -
        fieldMulCLM f m hk y 1 (h 3) - fieldMulCLM f m hk y 3 (h 1) :=
  (rfl)

end apply

/-- **The quadratic remainder between Sobolev spaces.** The quadratic term of the vortex equation
(`TauCeti.Vortex.quadraticTerm`) on complexified coordinates `y ∈ H^(k+1)(ℂ)⁴`, `k ≥ 1`, with
values in `H^k(ℂ)³`. -/
def sobolevQuadraticTerm (hk : 1 ≤ k) (y : Fin 4 → H^{(k : ℝ) + 1}(ℂ)) :
    Fin 3 → H^{(k : ℝ)}(ℂ) :=
  let μ := mulCLM (finrank_lt_two_mul_natCast_add_one hk)
  ![inclusion (lt_add_one _).le ((1 / 2 : ℂ) • (μ (y 2) (y 2) + μ (y 3) (y 3))),
    inclusion (lt_add_one _).le (-μ (y 0) (y 3) - μ (y 1) (y 2)),
    inclusion (lt_add_one _).le (μ (y 0) (y 2) - μ (y 1) (y 3))]

section apply

variable (hk : 1 ≤ k) (hs : (Module.finrank ℝ ℂ : ℝ) < 2 * ((k : ℝ) + 1))
  (y : Fin 4 → H^{(k : ℝ) + 1}(ℂ))

/-- The first row of `sobolevQuadraticTerm`; `hs` is any proof that `H^(k+1)(ℂ)` is an algebra. -/
theorem sobolevQuadraticTerm_apply_zero :
    sobolevQuadraticTerm hk y 0 =
      inclusion (lt_add_one _).le ((1 / 2 : ℂ) • (mulCLM hs (y 2) (y 2) + mulCLM hs (y 3) (y 3))) :=
  (rfl)

/-- The second row of `sobolevQuadraticTerm`. -/
theorem sobolevQuadraticTerm_apply_one :
    sobolevQuadraticTerm hk y 1 =
      inclusion (lt_add_one _).le (-mulCLM hs (y 0) (y 3) - mulCLM hs (y 1) (y 2)) :=
  (rfl)

/-- The third row of `sobolevQuadraticTerm`. -/
theorem sobolevQuadraticTerm_apply_two :
    sobolevQuadraticTerm hk y 2 =
      inclusion (lt_add_one _).le (mulCLM hs (y 0) (y 2) - mulCLM hs (y 1) (y 3)) :=
  (rfl)

end apply

variable (f m k) in
/-- The equation defect of the reference field `x_m`, as an element of `H^k(ℂ)³`. The reference
field is an exact vortex outside a disc, so its defect is smooth with compact support. -/
def sobolevReferenceDefect (i : Fin 3) : H^{(k : ℝ)}(ℂ) :=
  SchwartzMap.toBesselPotentialSpaceCLM (k : ℝ) 2
    ((hasCompactSupport_ofReal_equation_referenceField_apply f m i).toSchwartzMap
      (contDiff_ofReal_equation_referenceField_apply f m i))

variable (f m) in
/-- **The vortex equation between Sobolev spaces.** For `k ≥ 1`, the vortex equation
(`TauCeti.Vortex.equation`) in the affine chart `y ↦ x_m + y` of `A_m^(k+1)` centred at the
reference field, on complexified coordinates: a map `H^(k+1)(ℂ)⁴ → H^k(ℂ)³`. It is the exact
expansion `equation (x_m + y) = equation x_m + d₁ y + quadraticTerm y` about the reference field
(`TauCeti.Vortex.equation_add_smul`), so it is a polynomial of degree two. -/
def sobolevEquation (hk : 1 ≤ k) (y : Fin 4 → H^{(k : ℝ) + 1}(ℂ)) : Fin 3 → H^{(k : ℝ)}(ℂ) :=
  sobolevReferenceDefect f m k + sobolevLinearizedEquation f m hk 0 y + sobolevQuadraticTerm hk y

/-- `sobolevEquation` is the exact expansion about the reference field. -/
theorem sobolevEquation_def (hk : 1 ≤ k) (y : Fin 4 → H^{(k : ℝ) + 1}(ℂ)) :
    sobolevEquation f m hk y =
      sobolevReferenceDefect f m k + sobolevLinearizedEquation f m hk 0 y +
        sobolevQuadraticTerm hk y :=
  (rfl)

/-! #### Smoothness and the derivative -/

/-- The quadratic term has derivative `h ↦ B(y, h) + B(h, y)` at `y`, the difference of the
linearizations at `x_m + y` and at `x_m`. -/
private theorem hasFDerivAt_sobolevQuadraticTerm (hk : 1 ≤ k) (y : Fin 4 → H^{(k : ℝ) + 1}(ℂ)) :
    HasFDerivAt (sobolevQuadraticTerm hk)
      (sobolevLinearizedEquation f m hk y - sobolevLinearizedEquation f m hk 0) y := by
  set μ := mulCLM (finrank_lt_two_mul_natCast_add_one hk)
  set ι : H^{(k : ℝ) + 1}(ℂ) →L[ℂ] H^{(k : ℝ)}(ℂ) := inclusion (lt_add_one _).le
  -- The derivative of `y ↦ y_a y_b` at `y` is `h ↦ y_a h_b + h_a y_b`.
  have hP (a b : Fin 4) : HasFDerivAt (fun y : Fin 4 → H^{(k : ℝ) + 1}(ℂ) ↦ μ (y a) (y b))
      (μ.precompR _ (y a) (proj b) + μ.precompL _ (proj a) (y b)) y :=
    μ.hasFDerivAt_of_bilinear (hasFDerivAt_apply a y) (hasFDerivAt_apply b y)
  refine hasFDerivAt_pi'' fun i ↦ ?_
  fin_cases i
  · refine (ι.hasFDerivAt.comp y (((hP 2 2).add (hP 3 3)).const_smul (1 / 2 : ℂ))).congr_fderiv ?_
    ext1 h
    simp [sobolevLinearizedEquation_apply_zero, fieldMulCLM_apply hk
      (finrank_lt_two_mul_natCast_add_one hk), ι, μ, mulCLM_comm _ (h 2), mulCLM_comm _ (h 3)]
    module
  · refine (ι.hasFDerivAt.comp y ((hP 0 3).neg.sub (hP 1 2))).congr_fderiv ?_
    ext1 h
    simp [sobolevLinearizedEquation_apply_one, fieldMulCLM_apply hk
      (finrank_lt_two_mul_natCast_add_one hk), ι, μ, mulCLM_comm _ (h 0), mulCLM_comm _ (h 1)]
    abel
  · refine (ι.hasFDerivAt.comp y ((hP 0 2).sub (hP 1 3))).congr_fderiv ?_
    ext1 h
    simp [sobolevLinearizedEquation_apply_two, fieldMulCLM_apply hk
      (finrank_lt_two_mul_natCast_add_one hk), ι, μ, mulCLM_comm _ (h 0), mulCLM_comm _ (h 1)]
    abel

/-- **The derivative of the vortex equation map.** The derivative of `sobolevEquation` at `y` is
the complexified linearized equation at `x_m + y`. -/
theorem hasFDerivAt_sobolevEquation (hk : 1 ≤ k) (y : Fin 4 → H^{(k : ℝ) + 1}(ℂ)) :
    HasFDerivAt (sobolevEquation f m hk) (sobolevLinearizedEquation f m hk y) y := by
  have h := ((hasFDerivAt_const (sobolevReferenceDefect f m k) y).add
    (sobolevLinearizedEquation f m hk 0).hasFDerivAt).add
      (hasFDerivAt_sobolevQuadraticTerm (f := f) (m := m) hk y)
  exact h.congr_fderiv (by abel)

/-- The derivative of `sobolevEquation` at `y` is the linearized equation at `x_m + y`. -/
theorem fderiv_sobolevEquation (hk : 1 ≤ k) (y : Fin 4 → H^{(k : ℝ) + 1}(ℂ)) :
    fderiv ℂ (sobolevEquation f m hk) y = sobolevLinearizedEquation f m hk y :=
  (hasFDerivAt_sobolevEquation hk y).fderiv

/-- **The vortex equation map is smooth.** As a polynomial map of degree two between the Hilbert
spaces `H^(k+1)(ℂ)⁴` and `H^k(ℂ)³`, `sobolevEquation` is analytic. -/
theorem contDiff_sobolevEquation (hk : 1 ≤ k) : ContDiff ℂ ω (sobolevEquation f m hk) := by
  set μ := mulCLM (finrank_lt_two_mul_natCast_add_one hk)
  have hP (a b : Fin 4) :
      ContDiff ℂ ω fun y : Fin 4 → H^{(k : ℝ) + 1}(ℂ) ↦ μ (y a) (y b) :=
    ((μ.comp (proj (R := ℂ) (φ := fun _ : Fin 4 ↦ H^{(k : ℝ) + 1}(ℂ)) a)).contDiff).clm_apply
      (contDiff_apply ℂ (fun _ : Fin 4 ↦ H^{(k : ℝ) + 1}(ℂ)) b)
  have hQ : ContDiff ℂ ω (sobolevQuadraticTerm hk) := by
    refine contDiff_pi' fun i ↦ ?_
    fin_cases i
    · exact (inclusion _).contDiff.comp (((hP 2 2).add (hP 3 3)).const_smul _)
    · exact (inclusion _).contDiff.comp ((hP 0 3).neg.sub (hP 1 2))
    · exact (inclusion _).contDiff.comp ((hP 0 2).sub (hP 1 3))
  exact (contDiff_const.add (sobolevLinearizedEquation f m hk 0).contDiff).add hQ

/-! #### Comparison with the pointwise equation

For `s ≥ 0` an element `u` of `H^s(ℂ)` is an `L²` function (`inclusionLp`). A real field
`y : ℂ → ℝ⁴` lies in `sobolevFields s` exactly when its coordinates are, almost everywhere, the
`L²` functions of some `u : Fin 4 → H^s(ℂ)`; this `u` is unique. The theorems below compute the
Sobolev maps on such `u` through the pointwise expressions of the vortex equations. -/

/-- The equation defect of the reference field is, as an `L²` function, the pointwise defect
`equation x_m`. -/
theorem coeFn_inclusionLp_sobolevReferenceDefect_ae_eq (i : Fin 3) :
    ⇑(inclusionLp (k.cast_nonneg : (0 : ℝ) ≤ k) (sobolevReferenceDefect f m k i)) =ᵐ[volume]
      fun z ↦ (equation (referenceField f m) z i : ℂ) := by
  rw [sobolevReferenceDefect, inclusionLp_toBesselPotentialSpaceCLM]
  exact SchwartzMap.coeFn_toLp _ 2 volume

/-- If the coordinates of `y` are almost everywhere the real functions `y_a`, and `v` is almost
everywhere the real function `g`, then `fieldMulCLM f m hk y a v` is almost everywhere the
product `(x_m + y)_a g`. -/
theorem coeFn_inclusionLp_fieldMulCLM_ae_eq (hk : 1 ≤ k) {u : Fin 4 → H^{(k : ℝ) + 1}(ℂ)}
    {y : ℂ → EuclideanSpace ℝ (Fin 4)}
    (hu : ∀ a, ⇑(inclusionLp (by positivity) (u a)) =ᵐ[volume] fun z ↦ (y z a : ℂ)) (a : Fin 4)
    {v : H^{(k : ℝ) + 1}(ℂ)} {g : ℂ → ℝ}
    (hv : ⇑(inclusionLp (by positivity) v) =ᵐ[volume] fun z ↦ (g z : ℂ)) :
    ⇑(inclusionLp (k.cast_nonneg : (0 : ℝ) ≤ k) (fieldMulCLM f m hk u a v)) =ᵐ[volume]
      fun z ↦ ((referenceField f m + y) z a * g z : ℝ) := by
  have hs := finrank_lt_two_mul_natCast_add_one hk
  have h₀ : (0 : ℝ) ≤ k + 1 := by positivity
  rw [fieldMulCLM_apply hk hs, map_add, inclusionLp_inclusion]
  have hr := (coeFn_inclusionLp_referenceMulCLM_ae_eq (f := f) (m := m) a
    (inclusion (lt_add_one _).le v))
  rw [inclusionLp_inclusion] at hr
  filter_upwards [Lp.coeFn_add (inclusionLp _ (referenceMulCLM f m k a
    (inclusion (lt_add_one _).le v))) (inclusionLp h₀ (mulCLM hs (u a) v)), hr,
    coeFn_toLp_inclusion_mulCLM hs h₀ (u a) v, hu a, hv]
    with z h₁ h₂ h₃ h₄ h₅
  simp only [toLp_inclusion] at h₃
  rw [h₁, Pi.add_apply, h₂, h₃, h₄, h₅]
  simp only [PiLp.add_apply, Pi.add_apply, Complex.ofReal_mul, Complex.ofReal_add]
  ring

/-- **The Sobolev linearized equation computes the pointwise one.** If the coordinates of
`u` and `w` are almost everywhere those of the real fields `y` and `h`, with `h` of class `C¹`,
then `sobolevLinearizedEquation f m hk u w` is almost everywhere the linearized equation
`linearizedEquation (x_m + y) h`. -/
theorem coeFn_inclusionLp_sobolevLinearizedEquation_ae_eq (hk : 1 ≤ k)
    {u w : Fin 4 → H^{(k : ℝ) + 1}(ℂ)} {y h : ℂ → EuclideanSpace ℝ (Fin 4)}
    (hu : ∀ a, ⇑(inclusionLp (by positivity) (u a)) =ᵐ[volume] fun z ↦ (y z a : ℂ))
    (hw : ∀ a, ⇑(inclusionLp (by positivity) (w a)) =ᵐ[volume] fun z ↦ (h z a : ℂ))
    (hh : ContDiff ℝ 1 h) (i : Fin 3) :
    ⇑(inclusionLp (k.cast_nonneg : (0 : ℝ) ≤ k) (sobolevLinearizedEquation f m hk u w i))
      =ᵐ[volume] fun z ↦ (linearizedEquation (referenceField f m + y) h z i : ℂ) := by
  have hd (b : Fin 4) (v : ℂ) := coeFn_inclusionLp_lineDerivCLM_ae_eq ENNReal.one_lt_two
    ENNReal.ofNat_ne_top k.cast_nonneg (contDiff_euclidean.1 hh b) (hw b) v
  have hX (a b : Fin 4) := coeFn_inclusionLp_fieldMulCLM_ae_eq (f := f) (m := m) hk hu a (hw b)
  fin_cases i
  · simp only [Fin.zero_eta, Fin.isValue, sobolevLinearizedEquation_apply_zero, map_add, map_sub]
    filter_upwards [Lp.coeFn_add_ae_eq_of_ae_eq (Lp.coeFn_add_ae_eq_of_ae_eq
      (Lp.coeFn_sub_ae_eq_of_ae_eq (hd 0 I) (hd 1 1)) (hX 2 2)) (hX 3 3)] with z hz
    rw [hz]
    simp only [Pi.add_apply, Pi.sub_apply, Fin.isValue, linearizedEquation_apply_zero,
      Complex.ofReal_add, Complex.ofReal_sub]
  · simp only [Fin.mk_one, Fin.isValue, sobolevLinearizedEquation_apply_one, map_sub]
    filter_upwards [Lp.coeFn_sub_ae_eq_of_ae_eq (Lp.coeFn_sub_ae_eq_of_ae_eq
      (Lp.coeFn_sub_ae_eq_of_ae_eq (Lp.coeFn_sub_ae_eq_of_ae_eq
        (Lp.coeFn_sub_ae_eq_of_ae_eq (hd 2 1) (hd 3 I)) (hX 0 3)) (hX 3 0)) (hX 1 2)) (hX 2 1)]
      with z hz
    rw [hz]
    simp only [Pi.sub_apply, Fin.isValue, linearizedEquation_apply_one,
      Complex.ofReal_sub, Complex.ofReal_mul]
    ring
  · simp only [Fin.reduceFinMk, Fin.isValue, sobolevLinearizedEquation_apply_two, map_add,
      map_sub]
    filter_upwards [Lp.coeFn_sub_ae_eq_of_ae_eq (Lp.coeFn_sub_ae_eq_of_ae_eq
      (Lp.coeFn_add_ae_eq_of_ae_eq (Lp.coeFn_add_ae_eq_of_ae_eq
        (Lp.coeFn_add_ae_eq_of_ae_eq (hd 3 1) (hd 2 I)) (hX 0 2)) (hX 2 0)) (hX 1 3)) (hX 3 1)]
      with z hz
    rw [hz]
    simp only [Pi.add_apply, Pi.sub_apply, Fin.isValue, linearizedEquation_apply_two,
      Complex.ofReal_add, Complex.ofReal_sub, Complex.ofReal_mul]
    ring

/-- **The Sobolev quadratic term computes the pointwise one.** If the coordinates of `u` are
almost everywhere those of the real field `y`, then `sobolevQuadraticTerm hk u` is almost
everywhere `quadraticTerm y`. -/
theorem coeFn_inclusionLp_sobolevQuadraticTerm_ae_eq (hk : 1 ≤ k)
    {u : Fin 4 → H^{(k : ℝ) + 1}(ℂ)} {y : ℂ → EuclideanSpace ℝ (Fin 4)}
    (hu : ∀ a, ⇑(inclusionLp (by positivity) (u a)) =ᵐ[volume] fun z ↦ (y z a : ℂ))
    (i : Fin 3) :
    ⇑(inclusionLp (k.cast_nonneg : (0 : ℝ) ≤ k) (sobolevQuadraticTerm hk u i)) =ᵐ[volume]
      fun z ↦ (quadraticTerm y z i : ℂ) := by
  have hs := finrank_lt_two_mul_natCast_add_one hk
  have h₀ : (0 : ℝ) ≤ k + 1 := by positivity
  have hP (a b : Fin 4) : ⇑(inclusionLp h₀ (mulCLM hs (u a) (u b))) =ᵐ[volume]
      fun z ↦ (y z a : ℂ) * y z b := by
    filter_upwards [coeFn_toLp_inclusion_mulCLM hs h₀ (u a) (u b), hu a, hu b]
      with z h₁ h₂ h₃
    simp only [toLp_inclusion] at h₁
    rw [h₁, h₂, h₃]
  fin_cases i
  · simp only [Fin.zero_eta, Fin.isValue, sobolevQuadraticTerm_apply_zero hk hs,
      inclusionLp_inclusion, map_smul, map_add]
    filter_upwards [Lp.coeFn_smul_ae_eq_of_ae_eq (1 / 2 : ℂ)
      (Lp.coeFn_add_ae_eq_of_ae_eq (hP 2 2) (hP 3 3))] with z hz
    rw [hz]
    simp only [Pi.smul_apply, Pi.add_apply, smul_eq_mul, quadraticTerm_apply_zero]
    push_cast
    ring
  · simp only [Fin.mk_one, Fin.isValue, sobolevQuadraticTerm_apply_one hk hs,
      inclusionLp_inclusion, map_sub, map_neg]
    filter_upwards [Lp.coeFn_sub_ae_eq_of_ae_eq (Lp.coeFn_neg_ae_eq_of_ae_eq (hP 0 3)) (hP 1 2)]
      with z hz
    rw [hz]
    simp only [Pi.sub_apply, Pi.neg_apply, quadraticTerm_apply_one]
    push_cast
    ring
  · simp only [Fin.reduceFinMk, Fin.isValue, sobolevQuadraticTerm_apply_two hk hs,
      inclusionLp_inclusion, map_sub]
    filter_upwards [Lp.coeFn_sub_ae_eq_of_ae_eq (hP 0 2) (hP 1 3)] with z hz
    rw [hz]
    simp only [Pi.sub_apply, quadraticTerm_apply_two]
    push_cast
    ring

/-- **The Sobolev equation map computes the vortex equation.** For `k ≥ 1`, if the coordinates of
`u : Fin 4 → H^(k+1)(ℂ)` are almost everywhere those of a real `C¹` field `y`, then
`sobolevEquation f m hk u` is almost everywhere the vortex defect `equation (x_m + y)` of the
field `x_m + y ∈ A_m^(k+1)`. -/
theorem coeFn_inclusionLp_sobolevEquation_ae_eq (hk : 1 ≤ k) {u : Fin 4 → H^{(k : ℝ) + 1}(ℂ)}
    {y : ℂ → EuclideanSpace ℝ (Fin 4)}
    (hu : ∀ a, ⇑(inclusionLp (by positivity) (u a)) =ᵐ[volume] fun z ↦ (y z a : ℂ))
    (hy : ContDiff ℝ 1 y) (i : Fin 3) :
    ⇑(inclusionLp (k.cast_nonneg : (0 : ℝ) ≤ k) (sobolevEquation f m hk u i)) =ᵐ[volume]
      fun z ↦ (equation (referenceField f m + y) z i : ℂ) := by
  have h₀ : ∀ a, ⇑(inclusionLp (by positivity) ((0 : Fin 4 → H^{(k : ℝ) + 1}(ℂ)) a))
      =ᵐ[volume] fun z ↦ (((0 : ℂ → EuclideanSpace ℝ (Fin 4)) z a : ℝ) : ℂ) := fun a ↦ by
    rw [Pi.zero_apply, map_zero]
    exact (Lp.coeFn_zero _ _ _).trans (.of_forall fun _ ↦ by simp)
  rw [sobolevEquation_def, Pi.add_apply, Pi.add_apply, map_add, map_add]
  filter_upwards [Lp.coeFn_add_ae_eq_of_ae_eq (Lp.coeFn_add_ae_eq_of_ae_eq
    (coeFn_inclusionLp_sobolevReferenceDefect_ae_eq i)
    (coeFn_inclusionLp_sobolevLinearizedEquation_ae_eq hk h₀ hu hy i))
    (coeFn_inclusionLp_sobolevQuadraticTerm_ae_eq hk hu i)] with z hz
  rw [hz]
  -- Expand the equation exactly about the reference field.
  have hexp := equation_add_smul (z := z) (t := 1)
    (fun j ↦ (contDiff_euclidean.1 (contDiff_referenceField f m) j).differentiable (by simp) z)
    (fun j ↦ (contDiff_euclidean.1 hy j).differentiable one_ne_zero z)
  simp only [one_smul, one_pow] at hexp
  simp [hexp]

/-- **Vortices are the zeros of the Sobolev equation map.** Let `k ≥ 1` and let `x` be a `C¹`
field whose difference with the reference field has coordinates almost everywhere those of
`u : Fin 4 → H^(k+1)(ℂ)`, so that `x ∈ A_m^(k+1)`. Then `x` solves the vortex equation exactly
when `sobolevEquation f m hk u = 0`. -/
theorem sobolevEquation_eq_zero_iff (hk : 1 ≤ k) {u : Fin 4 → H^{(k : ℝ) + 1}(ℂ)}
    {x : ℂ → EuclideanSpace ℝ (Fin 4)}
    (hu : ∀ a, ⇑(inclusionLp (by positivity) (u a)) =ᵐ[volume]
      fun z ↦ ((x - referenceField f m) z a : ℂ))
    (hx : ContDiff ℝ 1 x) : sobolevEquation f m hk u = 0 ↔ equation x = 0 := by
  have hy : ContDiff ℝ 1 (x - referenceField f m) :=
    hx.sub ((contDiff_referenceField f m).of_le (by simp))
  have he (i : Fin 3) := coeFn_inclusionLp_sobolevEquation_ae_eq (f := f) (m := m) hk hu hy i
  simp only [add_sub_cancel] at he
  have hc (i : Fin 3) : Continuous fun z ↦ (equation x z i : ℂ) :=
    Complex.continuous_ofReal.comp
      ((contDiff_euclidean.1 (contDiff_equation (m := 0) hx (by simp)) i).continuous)
  constructor
  · intro h
    funext z
    ext i
    have h0 : (fun z ↦ (equation x z i : ℂ)) =ᵐ[volume] 0 := by
      have h₁ := (he i).symm
      rw [h, Pi.zero_apply, map_zero] at h₁
      exact h₁.trans (Lp.coeFn_zero _ _ _)
    simpa using congrFun (Measure.eq_of_ae_eq h0 (hc i) continuous_zero) z
  · intro h
    funext i
    refine ext_of_ae_eq_inclusionLp (k.cast_nonneg : (0 : ℝ) ≤ k) ?_
    rw [Pi.zero_apply, map_zero]
    exact (he i).trans ((Filter.EventuallyEq.of_eq (funext fun z ↦ by simp [h])).trans
      (Lp.coeFn_zero _ _ _).symm)

end Smooth

end TauCeti.Vortex
