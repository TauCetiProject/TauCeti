/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Floer.ExponentialDecay
public import TauCeti.Geometry.Symplectic.Floer.Plane.Orbit.Basic
import TauCeti.Algebra.Ring.Periodic

/-!
# Exponential convergence at the end of a PSS plane

Let `𝔎` be the perturbation `TauCeti.Floer.PSSPlane.perturbation` of a PSS plane `p`, built from a
period-one `C³` Hamiltonian `H` on a symplectic vector space `(V, ω)` whose suspended Hamiltonian
vector field is globally Lipschitz, and let `ε = ±1` be the sign of the end of `p` at `∞`. Let `u`
be a `C³` solution of the Floer equation `(du - X_𝔎)^{0,1} = 0` on a part `‖w‖ > r` of the end,
with image in a compact set `K` in which every one-periodic orbit of `H` is nondegenerate, and with
finite energy there. Suppose that the almost complex structure is cylindrical on that part,
`J(w) = J_t(u(w))` where `t` is the angular coordinate of `w` (`(p.endCoord w).im`), for a
one-periodic family `J_t(x)` which is `C²` on an open neighbourhood of `ℝ × K` and tamed by `ω` on
`ℝ × K`. By `TauCeti.Geometry.Symplectic.Floer.Plane.Orbit.Basic` the loops
`ℓ_s(t) = u(φ(ε s + i t))` along the end, where `φ(z) = exp (2π ε z)` is the end lift, converge to
a one-periodic orbit along some sequence `s_n → ∞`. This file shows that they converge as
`s → ∞`, and exponentially fast in `C¹`: there are a one-periodic orbit `x` of `H` and `κ > 0`,
`C` with

`‖ℓ_s(t) - x(t)‖ + ‖d(u ∘ φ)(ε s, t) - dt ⊗ X_{H_t}(x(t))‖ ≤ C exp (-κ s)`

for all large `s` and all `t`, where `dt ⊗ X_{H_t}(x(t))` is the derivative of the stationary
cylinder `(s, t) ↦ x(t)`. In the namespace `TauCeti.SymplecticForm` this is
`exists_pos_eventually_norm_sub_add_norm_fderiv_sub_le_exp_pssPlanePerturbation`.
This is the asymptotic condition under which a PSS plane with a nondegenerate end lies in the
exponentially weighted function spaces of its linearized Floer operator, and under which its end
can be pre-glued to Floer cylinders, for the PSS maps, the unit of the pair-of-pants product and
the multiplicative PSS comparison.

**The positive plane.** On the positive plane `ε = 1` the end, read through the end lift, is a
finite-energy Floer half-cylinder for the cylindrical datum `H(t) dt`
(`TauCeti.SymplecticForm.exists_halfCylinder_comp_realChart_positive`), and the cylindrical
structure is `J_t` there, since the angular coordinate of `φ(s + i t)` is `t` up to an integer
(`TauCeti.Floer.PSSPlane.apply_im_endCoord_cylindricalEndLift`). Nondegenerate orbits are isolated
(`TauCeti.SymplecticForm.exists_pos_forall_eq_of_isNondegenerateFixedPt`) and their linearized
return maps fix no nonzero vector
(`TauCeti.SymplecticForm.eq_zero_of_dysonSeriesLeft_apply_eq_self`), and a finite-energy
cylindrical half-cylinder whose orbits are isolated and nondegenerate converges exponentially in
`C¹` to the stationary cylinder over one of them
(`TauCeti.SymplecticForm.exists_pos_eventually_norm_sub_add_norm_fderiv_sub_smulRight_le_exp`).

**The negative plane.** The negative plane given by `H` is the positive plane given by the
reversed Hamiltonian `-H(-t)` (`TauCeti.Floer.PSSPlane.perturbation_negative`), whose angular
coordinate is the negative of that of the negative plane
(`TauCeti.Floer.PSSPlane.im_endCoord_negative`), so the cylindrical structure becomes `J_{-t}`.
Reversing time turns orbits of `-H(-t)` into orbits of `H`
(`TauCeti.SymplecticForm.hasDerivAt_comp_neg_of_hasDerivAt_hamiltonianVectorField_reverse`); it
preserves isolation
(`TauCeti.SymplecticForm.exists_pos_forall_eq_of_isNondegenerateFixedPt_reverse`) and
nondegeneracy of the linearized return map
(`TauCeti.SymplecticForm.eq_zero_of_dysonSeriesLeft_reverse_apply_eq_self`). The loops of the
negative plane are those of the positive plane traversed backwards
(`TauCeti.Floer.PSSPlane.cylindricalEndLift_negative_endSign_mul`), and its end lift is that of the
positive plane after the reflection `z ↦ -z`, which changes the sign of both the derivative of `u`
and that of the stationary cylinder.

## Main results

In the namespace `TauCeti.SymplecticForm`:

* `exists_pos_eventually_norm_sub_add_norm_fderiv_sub_le_exp_pssPlanePerturbation`: exponential
  `C¹` convergence of the end of a PSS plane to the stationary cylinder of an orbit;
* `exists_pos_eventually_norm_sub_le_exp_pssPlanePerturbation`: its `C⁰` part;
* `exists_periodic_hasDerivAt_tendstoUniformly_atTop_pssPlanePerturbation`: the loops along the end
  converge uniformly to that orbit as `s → ∞`.

## References

* S. Piunikhin, D. Salamon and M. Schwarz, *Symplectic Floer–Donaldson theory and quantum
  cohomology*, in *Contact and symplectic geometry*, Publ. Newton Inst. 8 (1996), 171–200, on the
  asymptotics of the perturbed planes of the PSS maps.
* D. Salamon, *Lectures on Floer homology*, in *Symplectic geometry and topology*, IAS/Park City
  Math. Ser. 7 (1999), Lecture 2, on exponential decay at nondegenerate ends.
-/

public section

open Set Real Function Filter
open TauCeti.Complex (realChart realChart_apply)
open scoped Topology NNReal Manifold

namespace TauCeti.SymplecticForm

open Floer Floer.PSSPlane

section InnerProductSpace

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  {ω : SymplecticForm V} {H : ℝ → V → ℝ} {u : ℝ × ℝ → V} {J : ℝ × ℝ → AlmostComplexStructure V}
  {Jq : ℝ → V → AlmostComplexStructure V} {K : Set V} {W : Set (ℝ × V)} {r : ℝ}

/-- **Exponential `C¹` convergence at the end of the positive plane.** This is the case
`p = positive` of `exists_pos_eventually_norm_sub_add_norm_fderiv_sub_le_exp_pssPlanePerturbation`,
for an arbitrary Hamiltonian whose orbits in `K` are isolated and nondegenerate; the negative plane
is reduced to it. -/
private theorem exists_pos_eventually_norm_sub_add_norm_fderiv_sub_le_exp_positive
    (hH : Periodic H 1) (hHs : ContDiff ℝ 3 (uncurry H))
    (hu : ContDiffOn ℝ 3 u {z | r < ‖Complex.equivRealProdCLM.symm z‖}) (hK : IsCompact K)
    (huK : ∀ z, r < ‖Complex.equivRealProdCLM.symm z‖ → u z ∈ K)
    (hfloer : ∀ z, r < ‖Complex.equivRealProdCLM.symm z‖ →
      IsComplexLinearMap (AlmostComplexStructure.product ℝ) (J z)
        (ω.perturbedFDeriv
          (fun z x ↦ positive.perturbation H (Complex.equivRealProdCLM.symm z) x 1)
          (fun z x ↦ positive.perturbation H (Complex.equivRealProdCLM.symm z) x Complex.I)
          u z : ℝ × ℝ →ₗ[ℝ] V))
    (hE : ∫⁻ z in {z | r < ‖Complex.equivRealProdCLM.symm z‖},
      ENNReal.ofReal (ω.floerEnergyDensity
        (fun z x ↦ positive.perturbation H (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ positive.perturbation H (Complex.equivRealProdCLM.symm z) x Complex.I)
        u z) ≠ ⊤)
    (hW : IsOpen W)
    (hJq : ContDiffOn ℝ 2 (fun p : ℝ × V ↦ (Jq p.1 p.2).toLinearMap.toContinuousLinearMap) W)
    (hJqper : Periodic Jq 1) (hKW : univ ×ˢ K ⊆ W) (hJqt : ∀ t, ∀ x ∈ K, ω.Tames (Jq t x))
    (hJ : ∀ z, r < ‖Complex.equivRealProdCLM.symm z‖ →
      J z = Jq (positive.endCoord (Complex.equivRealProdCLM.symm z)).im (u z))
    (hiso : ∀ x : ℝ → V, Periodic x 1 →
      (∀ t, HasDerivAt x (ω.hamiltonianVectorField (H t) (x t)) t) → (∀ t, x t ∈ K) →
      ∃ ε > 0, ∀ y : ℝ → V, Periodic y 1 →
        (∀ t, HasDerivAt y (ω.hamiltonianVectorField (H t) (y t)) t) →
        dist (y 0) (x 0) < ε → y = x)
    (hnd : ∀ x : ℝ → V, Periodic x 1 →
      (∀ t, HasDerivAt x (ω.hamiltonianVectorField (H t) (x t)) t) → (∀ t, x t ∈ K) →
      ∀ v, dysonSeriesLeft (fun t ↦ fderiv ℝ (ω.hamiltonianVectorField (H t)) (x t)) 1 v = v →
        v = 0) :
    ∃ x : ℝ → V, Periodic x 1 ∧ (∀ t, HasDerivAt x (ω.hamiltonianVectorField (H t) (x t)) t) ∧
      ∃ κ > 0, ∃ A, ∀ᶠ s in atTop, ∀ t,
        ‖u (realChart positive.cylindricalEndLift (s, t)) - x t‖ +
            ‖fderiv ℝ (u ∘ realChart positive.cylindricalEndLift) (s, t) -
              (ContinuousLinearMap.snd ℝ ℝ ℝ).smulRight (ω.hamiltonianVectorField (H t) (x t))‖ ≤
          A * Real.exp (-(κ * s)) := by
  obtain ⟨c, -, M, hcM⟩ := exists_pos_forall_mul_norm_sq_le_and_norm_le hK
    (hJq.continuousOn.mono hKW) hJqper hJqt
  -- Read through the end lift, the end is a finite-energy Floer half-cylinder for `H(t) dt`.
  set J' : ℝ × ℝ → AlmostComplexStructure V :=
    fun z ↦ Jq (positive.endCoord (Complex.equivRealProdCLM.symm z)).im (u z) with hJ'def
  obtain ⟨a, hu', hper, huK', -, -, hfloer', hE'⟩ :=
    ω.exists_halfCylinder_comp_realChart_positive (J := J') three_ne_zero hH
      (hHs.of_le (by norm_num)) hu huK (fun z hz v ↦ (hcM _ _ (huK z hz) v).1)
      (fun z hz v ↦ (hcM _ _ (huK z hz) v).2)
      (fun z hz ↦ by have h := hfloer z hz; rwa [hJ z hz] at h) hE
  -- There the structure is the cylindrical one, `J_t(u ∘ φ)`.
  have hJ' (z : ℝ × ℝ) : (J' ∘ realChart positive.cylindricalEndLift) z =
      Jq z.2 ((u ∘ realChart positive.cylindricalEndLift) z) := by
    simp only [comp_apply, hJ'def, realChart_apply, ContinuousLinearEquiv.symm_apply_apply,
      apply_im_endCoord_cylindricalEndLift hJqper]
    simp
  exact exists_pos_eventually_norm_sub_add_norm_fderiv_sub_smulRight_le_exp hHs hH hW hJq hJqper
    hK hKW hJqt hu' hper huK' (fun z hz ↦ hJ' z ▸ hfloer' z hz) hE' hiso hnd

/-- The end lift of the negative plane is that of the positive plane after the reflection
`z ↦ -z`, and `X_{-H(t)} = -X_{H_t}`. So, read through the end lift of the negative plane at
`(-s, t)`, the distance of the derivative of `u` from that of the stationary cylinder of the orbit
`t ↦ x(-t)` of `H` is the distance, read through the end lift of the positive plane at `(s, -t)`,
of the derivative of `u` from that of the stationary cylinder of the orbit `x` of `-H(-t)`. -/
private theorem norm_fderiv_comp_realChart_negative_sub_smulRight (u : ℝ × ℝ → V) (x : ℝ → V)
    (s t : ℝ) :
    ‖fderiv ℝ (u ∘ realChart negative.cylindricalEndLift) (negative.endSign * s, t) -
        (ContinuousLinearMap.snd ℝ ℝ ℝ).smulRight (ω.hamiltonianVectorField (H t) (x (-t)))‖ =
      ‖fderiv ℝ (u ∘ realChart positive.cylindricalEndLift) (s, -t) -
        (ContinuousLinearMap.snd ℝ ℝ ℝ).smulRight
          (ω.hamiltonianVectorField (fun y ↦ -H (-(-t)) y) (x (-t)))‖ := by
  have h : u ∘ realChart negative.cylindricalEndLift =
      fun z ↦ (u ∘ realChart positive.cylindricalEndLift) ((-1 : ℝ) • z) := by
    funext z
    simp [realChart_apply, cylindricalEndLift_negative]
  have hX : ω.hamiltonianVectorField (fun y ↦ -H (-(-t)) y) (x (-t)) =
      -ω.hamiltonianVectorField (H t) (x (-t)) := by
    simpa only [neg_neg, Pi.neg_def] using ω.hamiltonianVectorField_neg (H t) (x (-t))
  rw [h, fderiv_comp_smul, neg_one_smul, hX, ← norm_neg]
  congr 1
  ext <;> simp [add_comm]

/-- **Exponential `C¹` convergence at the end of a PSS plane.** Let `𝔎` be the perturbation of a
PSS plane `p` given by a period-one `C³` Hamiltonian `H` whose suspended Hamiltonian vector field
is globally Lipschitz, and let `ε = p.endSign`. Let `u` be `C³` on a part `‖w‖ > r` of the end, with
image in a compact set `K`, solving the Floer equation `(du - X_𝔎)^{0,1} = 0` there with finite
energy there. Suppose that the almost complex structure is cylindrical there,
`J(w) = J_t(u(w))` with `t = (p.endCoord w).im` the angular coordinate of `w`, for a one-periodic
family `J_t(x)` which is `C²` on an open set `W ⊇ ℝ × K` and tamed by `ω` on `ℝ × K`, and that every
one-periodic orbit `x` of `H` in `K` is nondegenerate: `x(0)` is a nondegenerate fixed point of the
time-one map. Then the end of `u` converges exponentially fast in `C¹` to the stationary cylinder of
a one-periodic orbit `x` of `H`: with `φ` the end lift `p.cylindricalEndLift`, for some `κ > 0` and
`C`, eventually

`‖u(φ(ε s + i t)) - x(t)‖ + ‖d(u ∘ φ)(ε s, t) - dt ⊗ X_{H_t}(x(t))‖ ≤ C exp (-κ s)`

for every `t`. -/
theorem exists_pos_eventually_norm_sub_add_norm_fderiv_sub_le_exp_pssPlanePerturbation
    (p : PSSPlane) (hH : Periodic H 1) (hHs : ContDiff ℝ 3 (uncurry H))
    (hu : ContDiffOn ℝ 3 u {z | r < ‖Complex.equivRealProdCLM.symm z‖}) (hK : IsCompact K)
    (huK : ∀ z, r < ‖Complex.equivRealProdCLM.symm z‖ → u z ∈ K)
    (hfloer : ∀ z, r < ‖Complex.equivRealProdCLM.symm z‖ →
      IsComplexLinearMap (AlmostComplexStructure.product ℝ) (J z)
        (ω.perturbedFDeriv
          (fun z x ↦ p.perturbation H (Complex.equivRealProdCLM.symm z) x 1)
          (fun z x ↦ p.perturbation H (Complex.equivRealProdCLM.symm z) x Complex.I)
          u z : ℝ × ℝ →ₗ[ℝ] V))
    (hE : ∫⁻ z in {z | r < ‖Complex.equivRealProdCLM.symm z‖},
      ENNReal.ofReal (ω.floerEnergyDensity
        (fun z x ↦ p.perturbation H (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ p.perturbation H (Complex.equivRealProdCLM.symm z) x Complex.I)
        u z) ≠ ⊤)
    (hW : IsOpen W)
    (hJq : ContDiffOn ℝ 2 (fun q : ℝ × V ↦ (Jq q.1 q.2).toLinearMap.toContinuousLinearMap) W)
    (hJqper : Periodic Jq 1) (hKW : univ ×ˢ K ⊆ W) (hJqt : ∀ t, ∀ x ∈ K, ω.Tames (Jq t x))
    (hJ : ∀ z, r < ‖Complex.equivRealProdCLM.symm z‖ →
      J z = Jq (p.endCoord (Complex.equivRealProdCLM.symm z)).im (u z))
    {L : ℝ≥0} (hL : LipschitzWith L (ω.timeDependentHamiltonianSuspension H))
    (hnd : ∀ x : ℝ → V, Periodic x 1 →
      (∀ t, HasDerivAt x (ω.hamiltonianVectorField (H t) (x t)) t) → (∀ t, x t ∈ K) →
      IsNondegenerateFixedPt 𝓘(ℝ, V) (ω.timeDependentHamiltonianFlow H hL 0 1) (x 0)) :
    ∃ x : ℝ → V, Periodic x 1 ∧ (∀ t, HasDerivAt x (ω.hamiltonianVectorField (H t) (x t)) t) ∧
      ∃ κ > 0, ∃ A, ∀ᶠ s in atTop, ∀ t,
        ‖u (Complex.equivRealProdCLM
            (p.cylindricalEndLift (↑(p.endSign * s) + ↑t * Complex.I))) - x t‖ +
            ‖fderiv ℝ (u ∘ realChart p.cylindricalEndLift) (p.endSign * s, t) -
              (ContinuousLinearMap.snd ℝ ℝ ℝ).smulRight (ω.hamiltonianVectorField (H t) (x t))‖ ≤
          A * Real.exp (-(κ * s)) := by
  have hHs2 : ContDiff ℝ 2 (uncurry H) := hHs.of_le (by norm_num)
  cases p
  · obtain ⟨x, hxper, hx, κ, hκ, A, h⟩ :=
      exists_pos_eventually_norm_sub_add_norm_fderiv_sub_le_exp_positive hH hHs hu hK huK hfloer
        hE hW hJq hJqper hKW hJqt hJ
        (fun x hxper hx hxK ↦
          ω.exists_pos_forall_eq_of_isNondegenerateFixedPt hL hx (hnd x hxper hx hxK))
        fun x hxper hx hxK _ hv ↦
          ω.eq_zero_of_dysonSeriesLeft_apply_eq_self hL hHs2 hx (hnd x hxper hx hxK) hv
    refine ⟨x, hxper, hx, κ, hκ, A, h.mono fun s hs t ↦ ?_⟩
    rw [← realChart_positive_mk, endSign_positive, one_mul]
    exact hs t
  -- The negative plane is the positive plane for the reversed Hamiltonian `-H(-t)`, whose
  -- angular coordinate is reversed, so that its cylindrical structure is `J_{-t}`.
  rw [perturbation_negative] at hfloer hE
  set W' : Set (ℝ × V) := (fun q : ℝ × V ↦ (-q.1, q.2)) ⁻¹' W
  have hneg : Continuous fun q : ℝ × V ↦ (-q.1, q.2) := by fun_prop
  -- An orbit of `-H(-t)` in `K` is an orbit of `H` in `K` run backwards, so it is nondegenerate.
  have hndrev (x : ℝ → V) (hxper : Periodic x 1)
      (hx : ∀ t, HasDerivAt x (ω.hamiltonianVectorField (fun y ↦ -H (-t) y) (x t)) t)
      (hxK : ∀ t, x t ∈ K) :
      IsNondegenerateFixedPt 𝓘(ℝ, V) (ω.timeDependentHamiltonianFlow H hL 0 1) (x 0) := by
    simpa only [neg_zero] using hnd (fun t ↦ x (-t)) hxper.comp_neg
      (ω.hasDerivAt_comp_neg_of_hasDerivAt_hamiltonianVectorField_reverse hx) fun t ↦ hxK (-t)
  obtain ⟨x, hxper, hx, κ, hκ, A, h⟩ :=
    exists_pos_eventually_norm_sub_add_norm_fderiv_sub_le_exp_positive (W := W')
      (H := fun t y ↦ -H (-t) y) (Jq := fun t ↦ Jq (-t)) (hH.comp_neg.comp Neg.neg)
      ((hHs.comp (contDiff_fst.neg.prodMk contDiff_snd)).neg) hu hK huK hfloer hE
      (hW.preimage hneg)
      (hJq.comp (f := fun q : ℝ × V ↦ (-q.1, q.2)) (by fun_prop : ContDiff ℝ 2 _).contDiffOn
        fun q hq ↦ hq)
      hJqper.comp_neg (fun q hq ↦ hKW ⟨mem_univ _, hq.2⟩) (fun t ↦ hJqt (-t))
      (fun z hz ↦ by rw [hJ z hz, im_endCoord_negative])
      (fun x hxper hx hxK ↦ ω.exists_pos_forall_eq_of_isNondegenerateFixedPt_reverse hL hx
        (hndrev x hxper hx hxK))
      fun x hxper hx hxK _ hv ↦ ω.eq_zero_of_dysonSeriesLeft_reverse_apply_eq_self hL hHs2 hH hxper
        hx (hndrev x hxper hx hxK) hv
  refine ⟨_, hxper.comp_neg, ω.hasDerivAt_comp_neg_of_hasDerivAt_hamiltonianVectorField_reverse hx,
    κ, hκ, A, h.mono fun s hs t ↦ ?_⟩
  rw [norm_fderiv_comp_realChart_negative_sub_smulRight, cylindricalEndLift_negative_endSign_mul,
    ← realChart_positive_mk]
  exact hs (-t)

/-- **Exponential convergence at the end of a PSS plane.** Under the hypotheses of
`exists_pos_eventually_norm_sub_add_norm_fderiv_sub_le_exp_pssPlanePerturbation`, the loops
`ℓ_s(t) = u(φ(ε s + i t))` along the end converge exponentially fast to a one-periodic orbit `x`
of `H`: for some `κ > 0` and `C`, eventually `‖ℓ_s(t) - x(t)‖ ≤ C exp (-κ s)` for every `t`. -/
theorem exists_pos_eventually_norm_sub_le_exp_pssPlanePerturbation
    (p : PSSPlane) (hH : Periodic H 1) (hHs : ContDiff ℝ 3 (uncurry H))
    (hu : ContDiffOn ℝ 3 u {z | r < ‖Complex.equivRealProdCLM.symm z‖}) (hK : IsCompact K)
    (huK : ∀ z, r < ‖Complex.equivRealProdCLM.symm z‖ → u z ∈ K)
    (hfloer : ∀ z, r < ‖Complex.equivRealProdCLM.symm z‖ →
      IsComplexLinearMap (AlmostComplexStructure.product ℝ) (J z)
        (ω.perturbedFDeriv
          (fun z x ↦ p.perturbation H (Complex.equivRealProdCLM.symm z) x 1)
          (fun z x ↦ p.perturbation H (Complex.equivRealProdCLM.symm z) x Complex.I)
          u z : ℝ × ℝ →ₗ[ℝ] V))
    (hE : ∫⁻ z in {z | r < ‖Complex.equivRealProdCLM.symm z‖},
      ENNReal.ofReal (ω.floerEnergyDensity
        (fun z x ↦ p.perturbation H (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ p.perturbation H (Complex.equivRealProdCLM.symm z) x Complex.I)
        u z) ≠ ⊤)
    (hW : IsOpen W)
    (hJq : ContDiffOn ℝ 2 (fun q : ℝ × V ↦ (Jq q.1 q.2).toLinearMap.toContinuousLinearMap) W)
    (hJqper : Periodic Jq 1) (hKW : univ ×ˢ K ⊆ W) (hJqt : ∀ t, ∀ x ∈ K, ω.Tames (Jq t x))
    (hJ : ∀ z, r < ‖Complex.equivRealProdCLM.symm z‖ →
      J z = Jq (p.endCoord (Complex.equivRealProdCLM.symm z)).im (u z))
    {L : ℝ≥0} (hL : LipschitzWith L (ω.timeDependentHamiltonianSuspension H))
    (hnd : ∀ x : ℝ → V, Periodic x 1 →
      (∀ t, HasDerivAt x (ω.hamiltonianVectorField (H t) (x t)) t) → (∀ t, x t ∈ K) →
      IsNondegenerateFixedPt 𝓘(ℝ, V) (ω.timeDependentHamiltonianFlow H hL 0 1) (x 0)) :
    ∃ x : ℝ → V, Periodic x 1 ∧ (∀ t, HasDerivAt x (ω.hamiltonianVectorField (H t) (x t)) t) ∧
      ∃ κ > 0, ∃ A, ∀ᶠ s in atTop, ∀ t,
        ‖u (Complex.equivRealProdCLM
            (p.cylindricalEndLift (↑(p.endSign * s) + ↑t * Complex.I))) - x t‖ ≤
          A * Real.exp (-(κ * s)) := by
  obtain ⟨x, hxper, hx, κ, hκ, A, h⟩ :=
    exists_pos_eventually_norm_sub_add_norm_fderiv_sub_le_exp_pssPlanePerturbation p hH hHs hu hK
      huK hfloer hE hW hJq hJqper hKW hJqt hJ hL hnd
  exact ⟨x, hxper, hx, κ, hκ, A,
    h.mono fun s hs t ↦ (le_add_of_nonneg_right (norm_nonneg _)).trans (hs t)⟩

/-- **The end of a PSS plane converges to a nondegenerate orbit.** Under the hypotheses of
`exists_pos_eventually_norm_sub_add_norm_fderiv_sub_le_exp_pssPlanePerturbation`, the loops
`ℓ_s(t) = u(φ(ε s + i t))` along the end converge uniformly, as `s → ∞`, to a one-periodic orbit
of `H`. -/
theorem exists_periodic_hasDerivAt_tendstoUniformly_atTop_pssPlanePerturbation
    (p : PSSPlane) (hH : Periodic H 1) (hHs : ContDiff ℝ 3 (uncurry H))
    (hu : ContDiffOn ℝ 3 u {z | r < ‖Complex.equivRealProdCLM.symm z‖}) (hK : IsCompact K)
    (huK : ∀ z, r < ‖Complex.equivRealProdCLM.symm z‖ → u z ∈ K)
    (hfloer : ∀ z, r < ‖Complex.equivRealProdCLM.symm z‖ →
      IsComplexLinearMap (AlmostComplexStructure.product ℝ) (J z)
        (ω.perturbedFDeriv
          (fun z x ↦ p.perturbation H (Complex.equivRealProdCLM.symm z) x 1)
          (fun z x ↦ p.perturbation H (Complex.equivRealProdCLM.symm z) x Complex.I)
          u z : ℝ × ℝ →ₗ[ℝ] V))
    (hE : ∫⁻ z in {z | r < ‖Complex.equivRealProdCLM.symm z‖},
      ENNReal.ofReal (ω.floerEnergyDensity
        (fun z x ↦ p.perturbation H (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ p.perturbation H (Complex.equivRealProdCLM.symm z) x Complex.I)
        u z) ≠ ⊤)
    (hW : IsOpen W)
    (hJq : ContDiffOn ℝ 2 (fun q : ℝ × V ↦ (Jq q.1 q.2).toLinearMap.toContinuousLinearMap) W)
    (hJqper : Periodic Jq 1) (hKW : univ ×ˢ K ⊆ W) (hJqt : ∀ t, ∀ x ∈ K, ω.Tames (Jq t x))
    (hJ : ∀ z, r < ‖Complex.equivRealProdCLM.symm z‖ →
      J z = Jq (p.endCoord (Complex.equivRealProdCLM.symm z)).im (u z))
    {L : ℝ≥0} (hL : LipschitzWith L (ω.timeDependentHamiltonianSuspension H))
    (hnd : ∀ x : ℝ → V, Periodic x 1 →
      (∀ t, HasDerivAt x (ω.hamiltonianVectorField (H t) (x t)) t) → (∀ t, x t ∈ K) →
      IsNondegenerateFixedPt 𝓘(ℝ, V) (ω.timeDependentHamiltonianFlow H hL 0 1) (x 0)) :
    ∃ x : ℝ → V, Periodic x 1 ∧ (∀ t, HasDerivAt x (ω.hamiltonianVectorField (H t) (x t)) t) ∧
      TendstoUniformly (fun s t ↦ u (Complex.equivRealProdCLM
        (p.cylindricalEndLift (↑(p.endSign * s) + ↑t * Complex.I)))) x atTop := by
  obtain ⟨x, hxper, hx, κ, hκ, A, h⟩ :=
    exists_pos_eventually_norm_sub_le_exp_pssPlanePerturbation p hH hHs hu hK huK hfloer hE hW
      hJq hJqper hKW hJqt hJ hL hnd
  refine ⟨x, hxper, hx, Metric.tendstoUniformly_iff.2 fun δ hδ ↦ ?_⟩
  -- The bound `A exp (-κ s)` tends to `0`.
  have h0 : Tendsto (fun s ↦ A * Real.exp (-(κ * s))) atTop (𝓝 0) := by
    simpa using (Real.tendsto_exp_neg_atTop_nhds_zero.comp
      (tendsto_id.const_mul_atTop hκ)).const_mul A
  filter_upwards [h, h0.eventually (gt_mem_nhds hδ)] with s hs hsδ t
  rw [dist_comm, dist_eq_norm]
  exact (hs t).trans_lt hsδ

end InnerProductSpace

end TauCeti.SymplecticForm
