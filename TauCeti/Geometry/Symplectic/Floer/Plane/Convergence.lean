/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Floer.CylindricalEnd
public import TauCeti.Geometry.Symplectic.Floer.Plane.Orbit.Basic
import TauCeti.Algebra.Ring.Periodic

/-!
# Convergence and bounded derivatives at the end of a PSS plane

Let `p` be a PSS plane (`TauCeti.Floer.PSSPlane`) with end sign `ε = p.endSign = ±1` at `∞` and end
lift `φ` (`p.cylindricalEndLift`), and let `𝔎 : ℂ → V → ℂ →L[ℝ] ℝ` be a Hamiltonian perturbation on
`ℂ` with values in a symplectic vector space `(V, ω)` that equals `H(t) dt` beyond signed
longitudinal height `T₀` on the end of `p`, for a period-one Hamiltonian `H : ℝ → V → ℝ` (for
instance `𝔎 = p.perturbation H` with `T₀ = 2`, or `TauCeti.Floer.negativePlanePerturbation H` on the
negative plane). Adapting `TauCeti.Geometry.Symplectic.Floer.PairOfPants.End.Convergence` to the PSS
planes, this file upgrades the subsequential orbit breaking of
`TauCeti.Geometry.Symplectic.Floer.Plane.Orbit.Basic` to uniform convergence along the entire end
and establishes uniform derivative bounds on cylindrical ends.

**Full-end convergence under orbit isolation.** When `u` is a finite-energy `C¹` Floer solution on
an exterior `{‖w‖ > r}` with image in a compact set `K` in which the `1`-periodic orbits of `H` are
uniformly isolated, and `u ∘ realChart φ` has bounded derivative with uniformly tame almost complex
structures on some half-cylinder `ε s > b`, the end loops `t ↦ u(φ(ε R + i t))` converge uniformly
as `R → ∞` to a single `1`-periodic orbit `x` of `H`
(`exists_periodic_hasDerivAt_tendstoUniformly_atTop_of_eq_smul_endAngularForm_of_isolated`), without
requiring a global Lipschitz hypothesis on `H`. In particular this holds when `H` has globally
Lipschitz suspension and every `1`-periodic orbit in `K` starts at a nondegenerate fixed point of
the time-one map (`exists_periodic_hasDerivAt_tendstoUniformly_atTop_of_eq_smul_endAngularForm`).
For a whole PSS plane with `𝔎 = p.perturbation H`, combining this with
`exists_periodic_hasDerivAt_lintegral_floerEnergyDensity_pssPlanePerturbation_eq` yields the
whole-plane energy identity `E(u) = ε A_H(x) - ∫_ℂ R_𝔎(u)` with full-end uniform convergence
(`exists_lintegral_floerEnergyDensity_pssPlanePerturbation_eq_of_isolated`).

**Bounded derivatives on cylindrical ends.** When `H` and `u` are `C³` and the almost complex
structure is cylindrical beyond `T₀` on the end of `p`,
`J(realChart φ (ε s, t)) = Jq(t, u(realChart φ (ε s, t)))`, for a `1`-periodic family `Jq` which is
`C²` on an open set `W ⊇ ℝ × K` and tamed by `ω` on `ℝ × K`,
`TauCeti.Geometry.Symplectic.Floer.CylindricalEnd` bounds `d(u ∘ realChart φ)` on `ε s ≥ b` whenever
`T₀ < b` and `r < exp (2πb)` (`exists_forall_norm_fderiv_comp_realChart_cylindricalEndLift_le`),
discharging both the derivative bound and uniform tameness hypotheses automatically
(`exists_forall_norm_fderiv_comp_realChart_cylindricalEndLift_le_and_tame`,
`exists_periodic_hasDerivAt_tendstoUniformly_atTop_of_cylindrical_of_isolated`,
`exists_lintegral_floerEnergyDensity_pssPlanePerturbation_eq_of_cylindrical_of_isolated`,
`exists_lintegral_floerEnergyDensity_pssPlanePerturbation_eq_of_cylindrical`).

## References

* S. Piunikhin, D. Salamon and M. Schwarz, *Symplectic Floer–Donaldson theory and quantum
  cohomology*, in *Contact and symplectic geometry*, Publ. Newton Inst. 8 (1996), 171–200.
* D. Salamon, *Lectures on Floer homology*, in *Symplectic geometry and topology*, IAS/Park City
  Math. Ser. 7 (1999), Lecture 1, on finite-energy Floer trajectories and their limits.
* D. McDuff and D. Salamon, *J-holomorphic curves and symplectic topology*, 2nd ed., Section 4.3
  and Section 4.6, on mean-value derivative bounds on cylindrical ends.
-/

public section

open Set Real Filter Function MeasureTheory
open TauCeti.Complex (realChart realChart_apply contDiff_realChart)
open scoped ENNReal NNReal Manifold Topology

namespace TauCeti.SymplecticForm

open Floer Floer.PSSPlane

section NormedSpace

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  {ω : SymplecticForm V} {𝔎 : ℂ → V → ℂ →L[ℝ] ℝ} {H : ℝ → V → ℝ} {T₀ : ℝ}
  {u : ℝ × ℝ → V} {J : ℝ × ℝ → AlmostComplexStructure V} {c M : ℝ} {K : Set V}

/-- Nondegeneracy of the time-one map at `x 0` for every `1`-periodic orbit `x` of `H` in `K`
implies uniform isolation of `1`-periodic orbits of `H` in `K`. -/
private theorem isolated_of_isNondegenerateFixedPt {L : ℝ≥0}
    (hL : LipschitzWith L (ω.timeDependentHamiltonianSuspension H))
    (hnd : ∀ x : ℝ → V, Periodic x 1 →
      (∀ t, HasDerivAt x (ω.hamiltonianVectorField (H t) (x t)) t) → (∀ t, x t ∈ K) →
      IsNondegenerateFixedPt 𝓘(ℝ, V) (ω.timeDependentHamiltonianFlow H hL 0 1) (x 0))
    (x : ℝ → V) (hxper : Periodic x 1)
    (hx : ∀ t, HasDerivAt x (ω.hamiltonianVectorField (H t) (x t)) t) (hxK : ∀ t, x t ∈ K) :
    ∃ δ > 0, ∀ y : ℝ → V, Periodic y 1 →
      (∀ t, HasDerivAt y (ω.hamiltonianVectorField (H t) (y t)) t) → (∀ t, y t ∈ K) →
      (∀ t, dist (y t) (x t) < δ) → y = x := by
  obtain ⟨δ, hδ, h⟩ := ω.exists_pos_forall_eq_of_isNondegenerateFixedPt hL hx (hnd x hxper hx hxK)
  exact ⟨δ, hδ, fun y hyper hy _ hyx ↦ h y hyper hy (hyx 0)⟩

/-- Full-end convergence on the positive PSS plane under orbit isolation. -/
private theorem exists_periodic_hasDerivAt_tendstoUniformly_atTop_positive_of_isolated
    (h𝔎 : ∀ w x, w ≠ 0 → T₀ ≤ (positive.endCoord w).re →
      𝔎 w x = H (positive.endCoord w).im x • positive.endAngularForm w)
    (hH : Periodic H 1) (hHs : ContDiff ℝ 1 (uncurry H)) {r : ℝ}
    (hu : ContDiffOn ℝ 1 u {z | r < ‖Complex.equivRealProdCLM.symm z‖}) (hK : IsCompact K)
    (huK : ∀ z, r < ‖Complex.equivRealProdCLM.symm z‖ → u z ∈ K)
    (hfloer : ∀ z, r < ‖Complex.equivRealProdCLM.symm z‖ →
      IsComplexLinearMap (AlmostComplexStructure.product ℝ) (J z)
        (ω.perturbedFDeriv
          (fun z x ↦ 𝔎 (Complex.equivRealProdCLM.symm z) x 1)
          (fun z x ↦ 𝔎 (Complex.equivRealProdCLM.symm z) x Complex.I) u z : ℝ × ℝ →ₗ[ℝ] V))
    (hE : ∫⁻ z in {z | r < ‖Complex.equivRealProdCLM.symm z‖},
      ENNReal.ofReal (ω.floerEnergyDensity
        (fun z x ↦ 𝔎 (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ 𝔎 (Complex.equivRealProdCLM.symm z) x Complex.I) u z) ≠ ⊤)
    (hiso : ∀ x : ℝ → V, Periodic x 1 →
      (∀ t, HasDerivAt x (ω.hamiltonianVectorField (H t) (x t)) t) → (∀ t, x t ∈ K) →
      ∃ δ > 0, ∀ y : ℝ → V, Periodic y 1 →
        (∀ t, HasDerivAt y (ω.hamiltonianVectorField (H t) (y t)) t) → (∀ t, y t ∈ K) →
        (∀ t, dist (y t) (x t) < δ) → y = x)
    {b C : ℝ}
    (hC : ∀ z : ℝ × ℝ, b < z.1 → ‖fderiv ℝ (u ∘ realChart positive.cylindricalEndLift) z‖ ≤ C)
    (hc : 0 < c)
    (hJc : ∀ z : ℝ × ℝ, b < z.1 →
      ∀ v, c * ‖v‖ ^ 2 ≤ ω v (J (realChart positive.cylindricalEndLift z) v))
    (hJM : ∀ z : ℝ × ℝ, b < z.1 →
      ∀ v, ‖J (realChart positive.cylindricalEndLift z) v‖ ≤ M * ‖v‖) :
    ∃ x : ℝ → V, Periodic x 1 ∧ (∀ t, HasDerivAt x (ω.hamiltonianVectorField (H t) (x t)) t) ∧
      TendstoUniformly (fun R t ↦ u (Complex.equivRealProdCLM
        (positive.cylindricalEndLift (↑(positive.endSign * R) + ↑t * Complex.I)))) x atTop := by
  obtain ⟨a, ha, hr⟩ := exists_le_and_le_exp r (max T₀ b)
  have haT : T₀ ≤ a := (le_max_left _ _).trans ha
  have hab {z : ℝ × ℝ} (hz : a < z.1) : b < z.1 := ((le_max_right _ _).trans ha).trans_lt hz
  obtain ⟨hu', hper', huK', hfloer', hE'⟩ :=
    ω.floer_comp_realChart_positive_of_eq_smul_endAngularForm h𝔎 hH
      (fun t ↦ (hHs.differentiable one_ne_zero).comp
        ((differentiable_const t).prodMk differentiable_id)) one_ne_zero haT hr hu huK hfloer hE
  have hfin := lintegral_norm_sq_sliceDefect_ne_top (measurableSet_Ioi.prod measurableSet_Icc) hc
    (fun z hz v ↦ hJc z (hab hz.1) v) (fun z hz v ↦ hJM z (hab hz.1) v) hfloer' hE'
  obtain ⟨x, hxper, hx, hux⟩ := exists_periodic_hasDerivAt_tendstoUniformly_atTop hu' hper' hK
    huK' (ω.contDiff_hamiltonianVectorField_uncurry (n := 0) (by simpa using hHs)).continuous
    (fun v t ↦ by simp only [hH t]) hfin (fun z hz ↦ hC z (hab hz.1)) hiso
  simp only [comp_apply, realChart_positive_mk] at hux
  exact ⟨x, hxper, hx, hux⟩

/-! ### Uniform convergence along the end under orbit isolation -/

/-- **Full-end convergence on a PSS plane under orbit isolation.** Let `𝔎` agree with `H(t) dt`
beyond signed height `T₀` on the end of `p` for a `1`-periodic `C¹` Hamiltonian `H`, and let `u` be
`C¹` on `{‖w‖ > r}`, with image in a compact set `K` in which the `1`-periodic orbits of `H` are
uniformly isolated, solving `(du - X_𝔎)^{0,1} = 0` there with finite energy. If on some
half-cylinder `ε s > b` the derivative of `u ∘ realChart φ` is bounded and `J` is uniformly tame,
then the end loops `t ↦ u(φ(ε R + i t))` converge uniformly as `R → ∞` to a single `1`-periodic
orbit of `H`. -/
theorem exists_periodic_hasDerivAt_tendstoUniformly_atTop_of_eq_smul_endAngularForm_of_isolated
    (p : PSSPlane)
    (h𝔎 : ∀ w x, w ≠ 0 → T₀ ≤ p.endSign * (p.endCoord w).re →
      𝔎 w x = H (p.endCoord w).im x • p.endAngularForm w)
    (hH : Periodic H 1) (hHs : ContDiff ℝ 1 (uncurry H)) {r : ℝ}
    (hu : ContDiffOn ℝ 1 u {z | r < ‖Complex.equivRealProdCLM.symm z‖}) (hK : IsCompact K)
    (huK : ∀ z, r < ‖Complex.equivRealProdCLM.symm z‖ → u z ∈ K)
    (hfloer : ∀ z, r < ‖Complex.equivRealProdCLM.symm z‖ →
      IsComplexLinearMap (AlmostComplexStructure.product ℝ) (J z)
        (ω.perturbedFDeriv
          (fun z x ↦ 𝔎 (Complex.equivRealProdCLM.symm z) x 1)
          (fun z x ↦ 𝔎 (Complex.equivRealProdCLM.symm z) x Complex.I) u z : ℝ × ℝ →ₗ[ℝ] V))
    (hE : ∫⁻ z in {z | r < ‖Complex.equivRealProdCLM.symm z‖},
      ENNReal.ofReal (ω.floerEnergyDensity
        (fun z x ↦ 𝔎 (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ 𝔎 (Complex.equivRealProdCLM.symm z) x Complex.I) u z) ≠ ⊤)
    (hiso : ∀ x : ℝ → V, Periodic x 1 →
      (∀ t, HasDerivAt x (ω.hamiltonianVectorField (H t) (x t)) t) → (∀ t, x t ∈ K) →
      ∃ δ > 0, ∀ y : ℝ → V, Periodic y 1 →
        (∀ t, HasDerivAt y (ω.hamiltonianVectorField (H t) (y t)) t) → (∀ t, y t ∈ K) →
        (∀ t, dist (y t) (x t) < δ) → y = x)
    {b C : ℝ}
    (hC : ∀ z : ℝ × ℝ, b < p.endSign * z.1 →
      ‖fderiv ℝ (u ∘ realChart p.cylindricalEndLift) z‖ ≤ C)
    (hc : 0 < c)
    (hJc : ∀ z : ℝ × ℝ, b < p.endSign * z.1 →
      ∀ v, c * ‖v‖ ^ 2 ≤ ω v (J (realChart p.cylindricalEndLift z) v))
    (hJM : ∀ z : ℝ × ℝ, b < p.endSign * z.1 →
      ∀ v, ‖J (realChart p.cylindricalEndLift z) v‖ ≤ M * ‖v‖) :
    ∃ x : ℝ → V, Periodic x 1 ∧ (∀ t, HasDerivAt x (ω.hamiltonianVectorField (H t) (x t)) t) ∧
      TendstoUniformly (fun R t ↦ u (Complex.equivRealProdCLM
        (p.cylindricalEndLift (↑(p.endSign * R) + ↑t * Complex.I)))) x atTop := by
  cases p
  · exact exists_periodic_hasDerivAt_tendstoUniformly_atTop_positive_of_isolated
      (fun w x hw hz ↦ h𝔎 w x hw (by simpa [endSign_positive] using hz)) hH hHs hu hK huK hfloer
      hE hiso (fun z hz ↦ hC z (by simpa [endSign_positive] using hz)) hc
      (fun z hz ↦ hJc z (by simpa [endSign_positive] using hz))
      (fun z hz ↦ hJM z (by simpa [endSign_positive] using hz))
  -- Reduce the negative plane to the positive plane for `-H(-t)` via `z ↦ -z`.
  obtain ⟨hH', hHs'⟩ := periodic_contDiff_reverse hH hHs
  have hchart (z : ℝ × ℝ) :
      realChart positive.cylindricalEndLift z =
        realChart negative.cylindricalEndLift ((-1 : ℝ) • z) := by
    simp [realChart_apply, cylindricalEndLift_negative]
  have hC' (z : ℝ × ℝ) (hz : b < z.1) :
      ‖fderiv ℝ (u ∘ realChart positive.cylindricalEndLift) z‖ ≤ C := by
    have hcomp : u ∘ realChart positive.cylindricalEndLift =
        fun w ↦ (u ∘ realChart negative.cylindricalEndLift) ((-1 : ℝ) • w) :=
      funext fun w ↦ by simp only [comp_apply, hchart]
    rw [hcomp, fderiv_comp_smul, neg_one_smul, neg_one_smul, norm_neg]
    exact hC (-z) (by simpa [endSign_negative] using hz)
  have hiso' (x : ℝ → V) (hxper : Periodic x 1)
      (hx : ∀ t, HasDerivAt x (ω.hamiltonianVectorField (fun y ↦ -H (-t) y) (x t)) t)
      (hxK : ∀ t, x t ∈ K) :
      ∃ δ > 0, ∀ y : ℝ → V, Periodic y 1 →
        (∀ t, HasDerivAt y (ω.hamiltonianVectorField (fun w ↦ -H (-t) w) (y t)) t) →
        (∀ t, y t ∈ K) → (∀ t, dist (y t) (x t) < δ) → y = x := by
    obtain ⟨δ, hδ, h⟩ := hiso (fun t ↦ x (-t)) hxper.comp_neg
      (ω.hasDerivAt_comp_neg_of_hasDerivAt_hamiltonianVectorField_reverse hx) fun t ↦ hxK (-t)
    refine ⟨δ, hδ, fun y hyper hy hyK hyx ↦ funext fun t ↦ ?_⟩
    have hxy := congrFun (h (fun s ↦ y (-s)) hyper.comp_neg
      (ω.hasDerivAt_comp_neg_of_hasDerivAt_hamiltonianVectorField_reverse hy)
      (fun s ↦ hyK (-s)) fun s ↦ hyx (-s)) (-t)
    simpa only [neg_neg] using hxy
  obtain ⟨y, hyper, hy, huy⟩ :=
    exists_periodic_hasDerivAt_tendstoUniformly_atTop_positive_of_isolated
      (fun w x hw hz ↦ eq_smul_endAngularForm_positive_of_negative h𝔎 x hw hz)
      hH' hHs' hu hK huK hfloer hE hiso' hC' hc
      (fun z hz ↦ by
        rw [hchart, neg_one_smul]
        exact hJc (-z) (by simpa [endSign_negative] using hz))
      (fun z hz ↦ by
        rw [hchart, neg_one_smul]
        exact hJM (-z) (by simpa [endSign_negative] using hz))
  exact ⟨_, ω.periodic_hasDerivAt_tendstoUniformly_negative hyper hy huy⟩

/-- **Full-end convergence on a PSS plane at nondegenerate fixed points.** Specialization of
`exists_periodic_hasDerivAt_tendstoUniformly_atTop_of_eq_smul_endAngularForm_of_isolated` when the
suspension of `H` is globally Lipschitz and every `1`-periodic orbit in `K` starts at a
nondegenerate fixed point of the time-one map. -/
theorem exists_periodic_hasDerivAt_tendstoUniformly_atTop_of_eq_smul_endAngularForm
    (p : PSSPlane)
    (h𝔎 : ∀ w x, w ≠ 0 → T₀ ≤ p.endSign * (p.endCoord w).re →
      𝔎 w x = H (p.endCoord w).im x • p.endAngularForm w)
    (hH : Periodic H 1) (hHs : ContDiff ℝ 1 (uncurry H)) {r : ℝ}
    (hu : ContDiffOn ℝ 1 u {z | r < ‖Complex.equivRealProdCLM.symm z‖}) (hK : IsCompact K)
    (huK : ∀ z, r < ‖Complex.equivRealProdCLM.symm z‖ → u z ∈ K)
    (hfloer : ∀ z, r < ‖Complex.equivRealProdCLM.symm z‖ →
      IsComplexLinearMap (AlmostComplexStructure.product ℝ) (J z)
        (ω.perturbedFDeriv
          (fun z x ↦ 𝔎 (Complex.equivRealProdCLM.symm z) x 1)
          (fun z x ↦ 𝔎 (Complex.equivRealProdCLM.symm z) x Complex.I) u z : ℝ × ℝ →ₗ[ℝ] V))
    (hE : ∫⁻ z in {z | r < ‖Complex.equivRealProdCLM.symm z‖},
      ENNReal.ofReal (ω.floerEnergyDensity
        (fun z x ↦ 𝔎 (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ 𝔎 (Complex.equivRealProdCLM.symm z) x Complex.I) u z) ≠ ⊤)
    {L : ℝ≥0} (hL : LipschitzWith L (ω.timeDependentHamiltonianSuspension H))
    (hnd : ∀ x : ℝ → V, Periodic x 1 →
      (∀ t, HasDerivAt x (ω.hamiltonianVectorField (H t) (x t)) t) → (∀ t, x t ∈ K) →
      IsNondegenerateFixedPt 𝓘(ℝ, V) (ω.timeDependentHamiltonianFlow H hL 0 1) (x 0))
    {b C : ℝ}
    (hC : ∀ z : ℝ × ℝ, b < p.endSign * z.1 →
      ‖fderiv ℝ (u ∘ realChart p.cylindricalEndLift) z‖ ≤ C)
    (hc : 0 < c)
    (hJc : ∀ z : ℝ × ℝ, b < p.endSign * z.1 →
      ∀ v, c * ‖v‖ ^ 2 ≤ ω v (J (realChart p.cylindricalEndLift z) v))
    (hJM : ∀ z : ℝ × ℝ, b < p.endSign * z.1 →
      ∀ v, ‖J (realChart p.cylindricalEndLift z) v‖ ≤ M * ‖v‖) :
    ∃ x : ℝ → V, Periodic x 1 ∧ (∀ t, HasDerivAt x (ω.hamiltonianVectorField (H t) (x t)) t) ∧
      TendstoUniformly (fun R t ↦ u (Complex.equivRealProdCLM
        (p.cylindricalEndLift (↑(p.endSign * R) + ↑t * Complex.I)))) x atTop :=
  exists_periodic_hasDerivAt_tendstoUniformly_atTop_of_eq_smul_endAngularForm_of_isolated p h𝔎 hH
    hHs hu hK huK hfloer hE (isolated_of_isNondegenerateFixedPt hL hnd) hC hc hJc hJM

/-- **Whole-plane energy of a finite-energy PSS plane with isolated orbits.** Let `𝔎` be the
perturbation of a PSS plane `p` given by a `1`-periodic `C¹` Hamiltonian `H`, and let `u` be a `C²`
solution of `(du - X_𝔎)^{0,1} = 0` on the whole plane for tamed almost complex structures `J(z)`,
with finite energy. Suppose that on `{‖w‖ > r}` the image of `u` lies in a compact set `K` in which
the `1`-periodic orbits of `H` are uniformly isolated, `c ‖v‖² ≤ ω(v, J(z) v)` and
`‖J(z) v‖ ≤ M ‖v‖` with `c > 0`, and `u ∘ realChart φ` has bounded derivative on some half-cylinder
`ε s > b`. Then the end loops `ℓ_R(t) = u(φ(ε R + i t))` converge uniformly as `R → ∞` to a
`1`-periodic orbit `x` of `H`, their actions `A_H(ℓ_R)` converge to `A_H(x)`, and
`E(u) = ε A_H(x) - ∫_ℂ R_𝔎(u)`. -/
theorem exists_lintegral_floerEnergyDensity_pssPlanePerturbation_eq_of_isolated
    (p : PSSPlane) (hH : Periodic H 1) (hHs : ContDiff ℝ 1 (uncurry H)) (hu : ContDiff ℝ 2 u)
    (hK : IsCompact K) {r : ℝ}
    (huK : ∀ z, r < ‖Complex.equivRealProdCLM.symm z‖ → u z ∈ K) (hc : 0 < c)
    (hJc : ∀ z, r < ‖Complex.equivRealProdCLM.symm z‖ → ∀ v, c * ‖v‖ ^ 2 ≤ ω v (J z v))
    (hJM : ∀ z, r < ‖Complex.equivRealProdCLM.symm z‖ → ∀ v, ‖J z v‖ ≤ M * ‖v‖)
    (hJ : ∀ z, ω.Tames (J z))
    (hfloer : ∀ z, IsComplexLinearMap (AlmostComplexStructure.product ℝ) (J z)
      (ω.perturbedFDeriv
        (fun z x ↦ p.perturbation H (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ p.perturbation H (Complex.equivRealProdCLM.symm z) x Complex.I)
        u z : ℝ × ℝ →ₗ[ℝ] V))
    (hE : ∫⁻ z, ENNReal.ofReal (ω.floerEnergyDensity
        (fun z x ↦ p.perturbation H (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ p.perturbation H (Complex.equivRealProdCLM.symm z) x Complex.I) u z) ≠ ⊤)
    (hiso : ∀ x : ℝ → V, Periodic x 1 →
      (∀ t, HasDerivAt x (ω.hamiltonianVectorField (H t) (x t)) t) → (∀ t, x t ∈ K) →
      ∃ δ > 0, ∀ y : ℝ → V, Periodic y 1 →
        (∀ t, HasDerivAt y (ω.hamiltonianVectorField (H t) (y t)) t) → (∀ t, y t ∈ K) →
        (∀ t, dist (y t) (x t) < δ) → y = x)
    {b C : ℝ}
    (hC : ∀ z : ℝ × ℝ, b < p.endSign * z.1 →
      ‖fderiv ℝ (u ∘ realChart p.cylindricalEndLift) z‖ ≤ C) :
    ∃ x : ℝ → V, Periodic x 1 ∧ (∀ t, HasDerivAt x (ω.hamiltonianVectorField (H t) (x t)) t) ∧
      TendstoUniformly (fun R t ↦ u (Complex.equivRealProdCLM
        (p.cylindricalEndLift (↑(p.endSign * R) + ↑t * Complex.I)))) x atTop ∧
      Tendsto (fun R ↦ ω.hamiltonianAction H (fun t ↦ u (Complex.equivRealProdCLM
        (p.cylindricalEndLift (↑(p.endSign * R) + ↑t * Complex.I))))) atTop
        (𝓝 (ω.hamiltonianAction H x)) ∧
      ∫⁻ z, ENNReal.ofReal (ω.floerEnergyDensity
          (fun z x ↦ p.perturbation H (Complex.equivRealProdCLM.symm z) x 1)
          (fun z x ↦ p.perturbation H (Complex.equivRealProdCLM.symm z) x Complex.I) u z) =
        ENNReal.ofReal (p.endSign * ω.hamiltonianAction H x - ∫ z, ω.hamiltonianCurvature
          (fun z x ↦ p.perturbation H (Complex.equivRealProdCLM.symm z) x 1)
          (fun z x ↦ p.perturbation H (Complex.equivRealProdCLM.symm z) x Complex.I) z (u z)) := by
  obtain ⟨x, hxper, hx, ⟨σ, hσ, hσx⟩, hA, hEx⟩ :=
    exists_periodic_hasDerivAt_lintegral_floerEnergyDensity_pssPlanePerturbation_eq p hH hHs hu hK
      huK hc hJc hJM hJ hfloer hE
  obtain ⟨b', hbb', hrb'⟩ := exists_le_and_le_exp r b
  have hmem {z : ℝ × ℝ} (hz : b' < p.endSign * z.1) :
      r < ‖Complex.equivRealProdCLM.symm (realChart p.cylindricalEndLift z)‖ :=
    hrb'.trans_lt (p.exp_lt_norm_symm_realChart_cylindricalEndLift_iff.2 hz)
  obtain ⟨x', -, -, hx'⟩ :=
    exists_periodic_hasDerivAt_tendstoUniformly_atTop_of_eq_smul_endAngularForm_of_isolated p
      (𝔎 := p.perturbation H) (T₀ := 2) (fun _ y _ hw ↦ p.perturbation_eq_smul_endAngularForm hw y)
      hH hHs (hu.of_le one_le_two).contDiffOn hK huK (fun z _ ↦ hfloer z)
      ((setLIntegral_le_lintegral _ _).trans_lt hE.lt_top).ne hiso
      (fun z hz ↦ hC z (hbb'.trans_lt hz)) hc (fun z hz v ↦ hJc _ (hmem hz) v)
      (fun z hz v ↦ hJM _ (hmem hz) v)
  have hxx' : x = x' := funext fun t ↦
    tendsto_nhds_unique (hσx.tendsto_at t) ((hx'.tendsto_at t).comp hσ)
  exact ⟨x, hxper, hx, hxx' ▸ hx', hA, hEx⟩

end NormedSpace

section InnerProductSpace

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  {ω : SymplecticForm V} {𝔎 : ℂ → V → ℂ →L[ℝ] ℝ} {H : ℝ → V → ℝ} {T₀ : ℝ}
  {u : ℝ × ℝ → V} {J : ℝ × ℝ → AlmostComplexStructure V} {K : Set V} {W : Set (ℝ × V)}
  {Jq : ℝ → V → AlmostComplexStructure V}

/-- Given `T₀ < b` and `r < exp (2πb)`, there is `a` with `T₀ ≤ a`, `r ≤ exp (2πa)`, and `a < b`. -/
private theorem exists_le_and_le_exp_and_lt {r T₀ b : ℝ} (hb : T₀ < b)
    (hbr : r < Real.exp (2 * π * b)) :
    ∃ a : ℝ, T₀ ≤ a ∧ r ≤ Real.exp (2 * π * a) ∧ a < b := by
  have hne : (𝓝[<] b).NeBot := nhdsLT_neBot b
  have hmem : {a | r < Real.exp (2 * π * a)} ∩ Ico T₀ b ∈ 𝓝[<] b :=
    inter_mem (nhdsWithin_le_nhds
      (((Real.continuous_exp.comp (continuous_const.mul continuous_id)).continuousAt).eventually
        (lt_mem_nhds hbr))) (Ico_mem_nhdsLT hb)
  obtain ⟨a, har, haT, hab⟩ := hne.nonempty_of_mem hmem
  exact ⟨a, haT, har.le, hab⟩

/-- **Cylindrical half-cylinder pullback on `(a, ∞)` of the positive plane.** Where `𝔎 = H(t) dt`
and `J(realChart φ_+ (s, t)) = Jq(t, u(realChart φ_+ (s, t)))` for `s ≥ T₀` on the positive plane,
for any `a ≥ T₀` with `r ≤ exp (2πa)`, `u ∘ realChart φ_+` solves the cylindrical Floer equation for
`(Jq, H)` on `(a, ∞) × [0, 1]` with finite energy. -/
theorem floer_comp_realChart_positive_of_cylindrical (ω : SymplecticForm V)
    (h𝔎 : ∀ w x, w ≠ 0 → T₀ ≤ (positive.endCoord w).re →
      𝔎 w x = H (positive.endCoord w).im x • positive.endAngularForm w)
    (hH : Periodic H 1) (hHd : ∀ t, Differentiable ℝ (H t)) {n : WithTop ℕ∞} (hn : n ≠ 0)
    {r a : ℝ} (ha : T₀ ≤ a) (hr : r ≤ Real.exp (2 * π * a))
    (hu : ContDiffOn ℝ n u {z | r < ‖Complex.equivRealProdCLM.symm z‖})
    (huK : ∀ z, r < ‖Complex.equivRealProdCLM.symm z‖ → u z ∈ K)
    (hfloer : ∀ z, r < ‖Complex.equivRealProdCLM.symm z‖ →
      IsComplexLinearMap (AlmostComplexStructure.product ℝ) (J z)
        (ω.perturbedFDeriv
          (fun z x ↦ 𝔎 (Complex.equivRealProdCLM.symm z) x 1)
          (fun z x ↦ 𝔎 (Complex.equivRealProdCLM.symm z) x Complex.I) u z : ℝ × ℝ →ₗ[ℝ] V))
    (hE : ∫⁻ z in {z | r < ‖Complex.equivRealProdCLM.symm z‖},
      ENNReal.ofReal (ω.floerEnergyDensity
        (fun z x ↦ 𝔎 (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ 𝔎 (Complex.equivRealProdCLM.symm z) x Complex.I) u z) ≠ ⊤)
    (hJ : ∀ s t, T₀ ≤ s →
      J (realChart positive.cylindricalEndLift (s, t)) =
        Jq t (u (realChart positive.cylindricalEndLift (s, t)))) :
    ContDiffOn ℝ n (u ∘ realChart positive.cylindricalEndLift) (Ioi a ×ˢ univ) ∧
      (∀ s, a < s → Periodic (fun t ↦ (u ∘ realChart positive.cylindricalEndLift) (s, t)) 1) ∧
      (∀ s, a < s → ∀ t, (u ∘ realChart positive.cylindricalEndLift) (s, t) ∈ K) ∧
      (∀ z ∈ Ioi a ×ˢ Icc 0 1, IsComplexLinearMap (AlmostComplexStructure.product ℝ)
        (Jq z.2 ((u ∘ realChart positive.cylindricalEndLift) z))
        (ω.perturbedFDeriv (fun _ _ ↦ 0) (fun w ↦ H w.2)
          (u ∘ realChart positive.cylindricalEndLift) z : ℝ × ℝ →ₗ[ℝ] V)) ∧
      ∫⁻ z in Ioi a ×ˢ Icc 0 1, ENNReal.ofReal (ω.floerEnergyDensity (fun _ _ ↦ 0)
        (fun w ↦ H w.2) (u ∘ realChart positive.cylindricalEndLift) z) ≠ ⊤ := by
  obtain ⟨hu', hper', huK', hfloer', hE'⟩ :=
    ω.floer_comp_realChart_positive_of_eq_smul_endAngularForm h𝔎 hH hHd hn ha hr hu huK hfloer hE
  refine ⟨hu', hper', huK', fun z hz ↦ ?_, hE'⟩
  have h := hfloer' z hz
  rwa [comp_apply, hJ z.1 z.2 (ha.trans hz.1.le)] at h

/-! ### Bounded derivatives and convergence on cylindrical ends -/

/-- **Bounded derivative in end coordinates on a cylindrical end of a PSS plane.** Let `𝔎` agree
with `H(t) dt` beyond signed height `T₀` on the end of `p` for a `1`-periodic `C³` Hamiltonian `H`,
and let `u` be `C³` on `{‖w‖ > r}`, with image in a compact set `K`, solving `(du - X_𝔎)^{0,1} = 0`
there with finite energy. Suppose that for `s ≥ T₀` the almost complex structure is cylindrical,
`J(realChart φ (ε s, t)) = Jq(t, u(realChart φ (ε s, t)))`, for a `1`-periodic family `Jq` which is
`C²` on an open set `W ⊇ ℝ × K` and tamed by `ω` on `ℝ × K`. Then for every `b > T₀` with
`r < exp (2πb)` the derivative of `u ∘ realChart φ` is bounded on `ε s ≥ b`. -/
theorem exists_forall_norm_fderiv_comp_realChart_cylindricalEndLift_le (p : PSSPlane)
    (h𝔎 : ∀ w x, w ≠ 0 → T₀ ≤ p.endSign * (p.endCoord w).re →
      𝔎 w x = H (p.endCoord w).im x • p.endAngularForm w)
    (hH : Periodic H 1) (hHs : ContDiff ℝ 3 (uncurry H)) {r : ℝ}
    (hu : ContDiffOn ℝ 3 u {z | r < ‖Complex.equivRealProdCLM.symm z‖}) (hK : IsCompact K)
    (huK : ∀ z, r < ‖Complex.equivRealProdCLM.symm z‖ → u z ∈ K)
    (hfloer : ∀ z, r < ‖Complex.equivRealProdCLM.symm z‖ →
      IsComplexLinearMap (AlmostComplexStructure.product ℝ) (J z)
        (ω.perturbedFDeriv
          (fun z x ↦ 𝔎 (Complex.equivRealProdCLM.symm z) x 1)
          (fun z x ↦ 𝔎 (Complex.equivRealProdCLM.symm z) x Complex.I) u z : ℝ × ℝ →ₗ[ℝ] V))
    (hE : ∫⁻ z in {z | r < ‖Complex.equivRealProdCLM.symm z‖},
      ENNReal.ofReal (ω.floerEnergyDensity
        (fun z x ↦ 𝔎 (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ 𝔎 (Complex.equivRealProdCLM.symm z) x Complex.I) u z) ≠ ⊤)
    (hW : IsOpen W)
    (hJq : ContDiffOn ℝ 2 (fun q : ℝ × V ↦ (Jq q.1 q.2).toLinearMap.toContinuousLinearMap) W)
    (hJqper : Periodic Jq 1) (hKW : univ ×ˢ K ⊆ W) (hJqt : ∀ t, ∀ x ∈ K, ω.Tames (Jq t x))
    (hJ : ∀ s t, T₀ ≤ s →
      J (realChart p.cylindricalEndLift (p.endSign * s, t)) =
        Jq t (u (realChart p.cylindricalEndLift (p.endSign * s, t))))
    {b : ℝ} (hb : T₀ < b) (hbr : r < Real.exp (2 * π * b)) :
    ∃ C, ∀ z : ℝ × ℝ, b ≤ p.endSign * z.1 →
      ‖fderiv ℝ (u ∘ realChart p.cylindricalEndLift) z‖ ≤ C := by
  obtain ⟨a, haT, hr, hab⟩ := exists_le_and_le_exp_and_lt hb hbr
  cases p
  · obtain ⟨hu', hper', huK', hfloer', hE'⟩ :=
      ω.floer_comp_realChart_positive_of_cylindrical
        (fun w x hw hz ↦ h𝔎 w x hw (by simpa [endSign_positive] using hz)) hH
        (fun t ↦ (hHs.differentiable (by norm_num)).comp
          ((differentiable_const t).prodMk differentiable_id)) (by norm_num) haT hr hu huK hfloer hE
        fun s t hs ↦ by simpa [endSign_positive] using hJ s t hs
    obtain ⟨C, hC⟩ := exists_forall_norm_fderiv_le_of_floer hHs hH hW hJq hJqper hK hKW hJqt hu'
      hper' huK' hfloer' hE' hab
    exact ⟨C, fun z hz ↦ hC z (by simpa [endSign_positive] using hz)⟩
  -- On the negative plane, reduce to `(s, t) ↦ (s, -t)` via `z ↦ -z`.
  obtain ⟨hH', hHs'⟩ := periodic_contDiff_reverse hH hHs
  have hneg : Continuous fun q : ℝ × V ↦ (-q.1, q.2) := by fun_prop
  have hchart (s t : ℝ) :
      realChart positive.cylindricalEndLift (s, t) =
        realChart negative.cylindricalEndLift (negative.endSign * s, -t) := by
    have hsymm : -Complex.equivRealProdCLM.symm (-s, -t) = Complex.equivRealProdCLM.symm (s, t) :=
      by rw [← map_neg]; simp
    rw [realChart_apply, realChart_apply, endSign_negative, neg_one_mul,
      cylindricalEndLift_negative, hsymm]
  obtain ⟨hu', hper', huK', hfloer', hE'⟩ :=
    ω.floer_comp_realChart_positive_of_cylindrical (Jq := fun t ↦ Jq (-t))
      (fun w x hw hz ↦ eq_smul_endAngularForm_positive_of_negative h𝔎 x hw hz) hH'
      (fun t ↦ (hHs'.differentiable (by norm_num)).comp
        ((differentiable_const t).prodMk differentiable_id)) (by norm_num) haT hr hu huK hfloer hE
      fun s t hs ↦ by rw [hchart, hJ s (-t) hs]
  set W' : Set (ℝ × V) := (fun q : ℝ × V ↦ (-q.1, q.2)) ⁻¹' W
  obtain ⟨C, hC⟩ := exists_forall_norm_fderiv_le_of_floer (W := W') (J := fun t ↦ Jq (-t))
    hHs' hH' (hW.preimage hneg)
    (hJq.comp (f := fun q : ℝ × V ↦ (-q.1, q.2)) (by fun_prop : ContDiff ℝ 2 _).contDiffOn
      fun q hq ↦ hq)
    hJqper.comp_neg hK (fun q hq ↦ hKW ⟨mem_univ _, hq.2⟩) (fun t ↦ hJqt (-t)) hu' hper' huK'
    hfloer' hE' hab
  refine ⟨C, fun z hz ↦ ?_⟩
  have hcomp : u ∘ realChart negative.cylindricalEndLift =
      fun w ↦ (u ∘ realChart positive.cylindricalEndLift) ((-1 : ℝ) • w) :=
    funext fun w ↦ by simp [realChart_apply, cylindricalEndLift_negative]
  rw [hcomp, fderiv_comp_smul, neg_one_smul, neg_one_smul, norm_neg]
  exact hC (-z) (by simpa [endSign_negative] using hz)

/-- **Derivative and tameness bounds on a cylindrical end of a PSS plane.** Under the hypotheses
of `exists_forall_norm_fderiv_comp_realChart_cylindricalEndLift_le`, on some half-cylinder `ε s > b`
the derivative of `u ∘ realChart φ` is bounded and the almost complex structures are uniformly
tame. -/
theorem exists_forall_norm_fderiv_comp_realChart_cylindricalEndLift_le_and_tame (p : PSSPlane)
    (h𝔎 : ∀ w x, w ≠ 0 → T₀ ≤ p.endSign * (p.endCoord w).re →
      𝔎 w x = H (p.endCoord w).im x • p.endAngularForm w)
    (hH : Periodic H 1) (hHs : ContDiff ℝ 3 (uncurry H)) {r : ℝ}
    (hu : ContDiffOn ℝ 3 u {z | r < ‖Complex.equivRealProdCLM.symm z‖}) (hK : IsCompact K)
    (huK : ∀ z, r < ‖Complex.equivRealProdCLM.symm z‖ → u z ∈ K)
    (hfloer : ∀ z, r < ‖Complex.equivRealProdCLM.symm z‖ →
      IsComplexLinearMap (AlmostComplexStructure.product ℝ) (J z)
        (ω.perturbedFDeriv
          (fun z x ↦ 𝔎 (Complex.equivRealProdCLM.symm z) x 1)
          (fun z x ↦ 𝔎 (Complex.equivRealProdCLM.symm z) x Complex.I) u z : ℝ × ℝ →ₗ[ℝ] V))
    (hE : ∫⁻ z in {z | r < ‖Complex.equivRealProdCLM.symm z‖},
      ENNReal.ofReal (ω.floerEnergyDensity
        (fun z x ↦ 𝔎 (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ 𝔎 (Complex.equivRealProdCLM.symm z) x Complex.I) u z) ≠ ⊤)
    (hW : IsOpen W)
    (hJq : ContDiffOn ℝ 2 (fun q : ℝ × V ↦ (Jq q.1 q.2).toLinearMap.toContinuousLinearMap) W)
    (hJqper : Periodic Jq 1) (hKW : univ ×ˢ K ⊆ W) (hJqt : ∀ t, ∀ x ∈ K, ω.Tames (Jq t x))
    (hJ : ∀ s t, T₀ ≤ s →
      J (realChart p.cylindricalEndLift (p.endSign * s, t)) =
        Jq t (u (realChart p.cylindricalEndLift (p.endSign * s, t)))) :
    ∃ b C c, 0 < c ∧ ∃ M,
      (∀ z : ℝ × ℝ, b < p.endSign * z.1 →
        ‖fderiv ℝ (u ∘ realChart p.cylindricalEndLift) z‖ ≤ C) ∧
      (∀ z : ℝ × ℝ, b < p.endSign * z.1 →
        ∀ v, c * ‖v‖ ^ 2 ≤ ω v (J (realChart p.cylindricalEndLift z) v)) ∧
      ∀ z : ℝ × ℝ, b < p.endSign * z.1 →
        ∀ v, ‖J (realChart p.cylindricalEndLift z) v‖ ≤ M * ‖v‖ := by
  obtain ⟨a, haT, hr⟩ := exists_le_and_le_exp r T₀
  set b := a + 1
  have hb : T₀ < b := haT.trans_lt (lt_add_one a)
  have hbr : r < Real.exp (2 * π * b) :=
    hr.trans_lt (Real.exp_lt_exp.2 (mul_lt_mul_of_pos_left (lt_add_one a) Real.two_pi_pos))
  obtain ⟨C, hC⟩ := exists_forall_norm_fderiv_comp_realChart_cylindricalEndLift_le p h𝔎 hH hHs hu
    hK huK hfloer hE hW hJq hJqper hKW hJqt hJ hb hbr
  obtain ⟨c, hc, M, hcM⟩ := exists_pos_forall_mul_norm_sq_le_and_norm_le hK
    (hJq.continuousOn.mono hKW) hJqper hJqt
  have hJz {z : ℝ × ℝ} (hz : b < p.endSign * z.1) :
      J (realChart p.cylindricalEndLift z) =
        Jq z.2 (u (realChart p.cylindricalEndLift z)) ∧
        u (realChart p.cylindricalEndLift z) ∈ K := by
    have h1 : p.endSign * (p.endSign * z.1) = z.1 := by
      rw [← mul_assoc, endSign_mul_endSign, one_mul]
    refine ⟨?_, huK _ (hr.trans_lt (p.exp_lt_norm_symm_realChart_cylindricalEndLift_iff.2
      ((lt_add_one a).trans hz)))⟩
    have h := hJ (p.endSign * z.1) z.2 (hb.trans hz).le
    rwa [h1] at h
  refine ⟨b, C, c, hc, M, fun z hz ↦ hC z hz.le, fun z hz v ↦ ?_, fun z hz v ↦ ?_⟩
  · rw [(hJz hz).1]
    exact (hcM _ _ (hJz hz).2 v).1
  · rw [(hJz hz).1]
    exact (hcM _ _ (hJz hz).2 v).2

/-- **Full-end convergence on a cylindrical end of a PSS plane under orbit isolation.** Let `𝔎`
agree with `H(t) dt` beyond signed height `T₀` on the end of `p` for a `1`-periodic `C³` Hamiltonian
`H`, and let `u` be `C³` on `{‖w‖ > r}`, with image in a compact set `K` in which the `1`-periodic
orbits of `H` are uniformly isolated, solving `(du - X_𝔎)^{0,1} = 0` there with finite energy. If
for `s ≥ T₀` the almost complex structure is cylindrical,
`J(realChart φ (ε s, t)) = Jq(t, u(realChart φ (ε s, t)))`, for a `1`-periodic family `Jq` which is
`C²` on an open set `W ⊇ ℝ × K` and tamed by `ω` on `ℝ × K`, then the end loops
`t ↦ u(φ(ε R + i t))` converge uniformly as `R → ∞` to a single `1`-periodic orbit of `H`. -/
theorem exists_periodic_hasDerivAt_tendstoUniformly_atTop_of_cylindrical_of_isolated
    (p : PSSPlane)
    (h𝔎 : ∀ w x, w ≠ 0 → T₀ ≤ p.endSign * (p.endCoord w).re →
      𝔎 w x = H (p.endCoord w).im x • p.endAngularForm w)
    (hH : Periodic H 1) (hHs : ContDiff ℝ 3 (uncurry H)) {r : ℝ}
    (hu : ContDiffOn ℝ 3 u {z | r < ‖Complex.equivRealProdCLM.symm z‖}) (hK : IsCompact K)
    (huK : ∀ z, r < ‖Complex.equivRealProdCLM.symm z‖ → u z ∈ K)
    (hfloer : ∀ z, r < ‖Complex.equivRealProdCLM.symm z‖ →
      IsComplexLinearMap (AlmostComplexStructure.product ℝ) (J z)
        (ω.perturbedFDeriv
          (fun z x ↦ 𝔎 (Complex.equivRealProdCLM.symm z) x 1)
          (fun z x ↦ 𝔎 (Complex.equivRealProdCLM.symm z) x Complex.I) u z : ℝ × ℝ →ₗ[ℝ] V))
    (hE : ∫⁻ z in {z | r < ‖Complex.equivRealProdCLM.symm z‖},
      ENNReal.ofReal (ω.floerEnergyDensity
        (fun z x ↦ 𝔎 (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ 𝔎 (Complex.equivRealProdCLM.symm z) x Complex.I) u z) ≠ ⊤)
    (hW : IsOpen W)
    (hJq : ContDiffOn ℝ 2 (fun q : ℝ × V ↦ (Jq q.1 q.2).toLinearMap.toContinuousLinearMap) W)
    (hJqper : Periodic Jq 1) (hKW : univ ×ˢ K ⊆ W) (hJqt : ∀ t, ∀ x ∈ K, ω.Tames (Jq t x))
    (hJ : ∀ s t, T₀ ≤ s →
      J (realChart p.cylindricalEndLift (p.endSign * s, t)) =
        Jq t (u (realChart p.cylindricalEndLift (p.endSign * s, t))))
    (hiso : ∀ x : ℝ → V, Periodic x 1 →
      (∀ t, HasDerivAt x (ω.hamiltonianVectorField (H t) (x t)) t) → (∀ t, x t ∈ K) →
      ∃ δ > 0, ∀ y : ℝ → V, Periodic y 1 →
        (∀ t, HasDerivAt y (ω.hamiltonianVectorField (H t) (y t)) t) → (∀ t, y t ∈ K) →
        (∀ t, dist (y t) (x t) < δ) → y = x) :
    ∃ x : ℝ → V, Periodic x 1 ∧ (∀ t, HasDerivAt x (ω.hamiltonianVectorField (H t) (x t)) t) ∧
      TendstoUniformly (fun R t ↦ u (Complex.equivRealProdCLM
        (p.cylindricalEndLift (↑(p.endSign * R) + ↑t * Complex.I)))) x atTop := by
  obtain ⟨b, C, c, hc, M, hC, hJc, hJM⟩ :=
    exists_forall_norm_fderiv_comp_realChart_cylindricalEndLift_le_and_tame p h𝔎 hH hHs hu hK huK
      hfloer hE hW hJq hJqper hKW hJqt hJ
  exact exists_periodic_hasDerivAt_tendstoUniformly_atTop_of_eq_smul_endAngularForm_of_isolated p
    h𝔎 hH (hHs.of_le (by norm_num)) (hu.of_le (by norm_num)) hK huK hfloer hE hiso hC hc hJc hJM

/-- **Whole-plane energy of a finite-energy PSS plane with a cylindrical end and isolated orbits.**
Let `𝔎` be the perturbation of a PSS plane `p` given by a `1`-periodic `C³` Hamiltonian `H`, and let
`u` be a `C³` solution of `(du - X_𝔎)^{0,1} = 0` on the whole plane for tamed almost complex
structures `J(z)`, with finite energy. Suppose that on `{‖w‖ > r}` the image of `u` lies in a
compact set `K` in which the `1`-periodic orbits of `H` are uniformly isolated, and that for
`s ≥ T₀` the almost complex structure is cylindrical,
`J(realChart φ (ε s, t)) = Jq(t, u(realChart φ (ε s, t)))`, for a `1`-periodic family `Jq` which is
`C²` on an open set `W ⊇ ℝ × K` and tamed by `ω` on `ℝ × K`. Then the end loops
`ℓ_R(t) = u(φ(ε R + i t))` converge uniformly as `R → ∞` to a `1`-periodic orbit `x` of `H`, their
actions `A_H(ℓ_R)` converge to `A_H(x)`, and `E(u) = ε A_H(x) - ∫_ℂ R_𝔎(u)`. -/
theorem exists_lintegral_floerEnergyDensity_pssPlanePerturbation_eq_of_cylindrical_of_isolated
    (p : PSSPlane) (hH : Periodic H 1) (hHs : ContDiff ℝ 3 (uncurry H)) (hu : ContDiff ℝ 3 u)
    (hK : IsCompact K) {r : ℝ}
    (huK : ∀ z, r < ‖Complex.equivRealProdCLM.symm z‖ → u z ∈ K)
    (hJ : ∀ z, ω.Tames (J z))
    (hfloer : ∀ z, IsComplexLinearMap (AlmostComplexStructure.product ℝ) (J z)
      (ω.perturbedFDeriv
        (fun z x ↦ p.perturbation H (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ p.perturbation H (Complex.equivRealProdCLM.symm z) x Complex.I)
        u z : ℝ × ℝ →ₗ[ℝ] V))
    (hE : ∫⁻ z, ENNReal.ofReal (ω.floerEnergyDensity
        (fun z x ↦ p.perturbation H (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ p.perturbation H (Complex.equivRealProdCLM.symm z) x Complex.I) u z) ≠ ⊤)
    (hW : IsOpen W)
    (hJq : ContDiffOn ℝ 2 (fun q : ℝ × V ↦ (Jq q.1 q.2).toLinearMap.toContinuousLinearMap) W)
    (hJqper : Periodic Jq 1) (hKW : univ ×ˢ K ⊆ W) (hJqt : ∀ t, ∀ x ∈ K, ω.Tames (Jq t x))
    (hJcyl : ∀ s t, T₀ ≤ s →
      J (realChart p.cylindricalEndLift (p.endSign * s, t)) =
        Jq t (u (realChart p.cylindricalEndLift (p.endSign * s, t))))
    (hiso : ∀ x : ℝ → V, Periodic x 1 →
      (∀ t, HasDerivAt x (ω.hamiltonianVectorField (H t) (x t)) t) → (∀ t, x t ∈ K) →
      ∃ δ > 0, ∀ y : ℝ → V, Periodic y 1 →
        (∀ t, HasDerivAt y (ω.hamiltonianVectorField (H t) (y t)) t) → (∀ t, y t ∈ K) →
        (∀ t, dist (y t) (x t) < δ) → y = x) :
    ∃ x : ℝ → V, Periodic x 1 ∧ (∀ t, HasDerivAt x (ω.hamiltonianVectorField (H t) (x t)) t) ∧
      TendstoUniformly (fun R t ↦ u (Complex.equivRealProdCLM
        (p.cylindricalEndLift (↑(p.endSign * R) + ↑t * Complex.I)))) x atTop ∧
      Tendsto (fun R ↦ ω.hamiltonianAction H (fun t ↦ u (Complex.equivRealProdCLM
        (p.cylindricalEndLift (↑(p.endSign * R) + ↑t * Complex.I))))) atTop
        (𝓝 (ω.hamiltonianAction H x)) ∧
      ∫⁻ z, ENNReal.ofReal (ω.floerEnergyDensity
          (fun z x ↦ p.perturbation H (Complex.equivRealProdCLM.symm z) x 1)
          (fun z x ↦ p.perturbation H (Complex.equivRealProdCLM.symm z) x Complex.I) u z) =
        ENNReal.ofReal (p.endSign * ω.hamiltonianAction H x - ∫ z, ω.hamiltonianCurvature
          (fun z x ↦ p.perturbation H (Complex.equivRealProdCLM.symm z) x 1)
          (fun z x ↦ p.perturbation H (Complex.equivRealProdCLM.symm z) x Complex.I) z (u z)) := by
  have hE' : ∫⁻ z in {z | r < ‖Complex.equivRealProdCLM.symm z‖},
      ENNReal.ofReal (ω.floerEnergyDensity
        (fun z x ↦ p.perturbation H (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ p.perturbation H (Complex.equivRealProdCLM.symm z) x Complex.I) u z) ≠ ⊤ :=
    ((setLIntegral_le_lintegral _ _).trans_lt hE.lt_top).ne
  obtain ⟨b, C, c, hc, M, hC, hJc, hJM⟩ :=
    exists_forall_norm_fderiv_comp_realChart_cylindricalEndLift_le_and_tame p
      (𝔎 := p.perturbation H) (T₀ := max T₀ 2)
      (fun _ x _ hw ↦ p.perturbation_eq_smul_endAngularForm ((le_max_right _ _).trans hw) x)
      hH hHs hu.contDiffOn hK huK (fun z _ ↦ hfloer z) hE' hW hJq hJqper hKW hJqt
      fun s t hs ↦ hJcyl s t ((le_max_left _ _).trans hs)
  set r' := max r (Real.exp (2 * π * b))
  have hr'r {z : ℝ × ℝ} (hz : r' < ‖Complex.equivRealProdCLM.symm z‖) :
      r < ‖Complex.equivRealProdCLM.symm z‖ :=
    (le_max_left _ _).trans_lt hz
  have hzb {z : ℝ × ℝ} (hz : r' < ‖Complex.equivRealProdCLM.symm z‖) :
      ∃ ζ : ℝ × ℝ, b < p.endSign * ζ.1 ∧ realChart p.cylindricalEndLift ζ = z := by
    obtain ⟨ζ, hζ₁, _, hζ⟩ :=
      p.exists_realChart_cylindricalEndLift_eq ((le_max_right _ _).trans_lt hz)
    exact ⟨ζ, hζ₁, hζ⟩
  exact exists_lintegral_floerEnergyDensity_pssPlanePerturbation_eq_of_isolated
    p hH (hHs.of_le (by norm_num)) (hu.of_le (by norm_num)) hK (r := r')
    (fun z hz ↦ huK z (hr'r hz)) hc
    (fun z hz v ↦ by obtain ⟨ζ, hζ, rfl⟩ := hzb hz; exact hJc ζ hζ v)
    (fun z hz v ↦ by obtain ⟨ζ, hζ, rfl⟩ := hzb hz; exact hJM ζ hζ v)
    hJ hfloer hE hiso hC

/-- **Whole-plane energy of a finite-energy PSS plane with a cylindrical end.** Specialization of
`exists_lintegral_floerEnergyDensity_pssPlanePerturbation_eq_of_cylindrical_of_isolated`
when the suspension of `H` is globally Lipschitz and every `1`-periodic orbit in `K` starts at a
nondegenerate fixed point of the time-one map. -/
theorem exists_lintegral_floerEnergyDensity_pssPlanePerturbation_eq_of_cylindrical
    (p : PSSPlane) (hH : Periodic H 1) (hHs : ContDiff ℝ 3 (uncurry H)) (hu : ContDiff ℝ 3 u)
    (hK : IsCompact K) {r : ℝ}
    (huK : ∀ z, r < ‖Complex.equivRealProdCLM.symm z‖ → u z ∈ K)
    (hJ : ∀ z, ω.Tames (J z))
    (hfloer : ∀ z, IsComplexLinearMap (AlmostComplexStructure.product ℝ) (J z)
      (ω.perturbedFDeriv
        (fun z x ↦ p.perturbation H (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ p.perturbation H (Complex.equivRealProdCLM.symm z) x Complex.I)
        u z : ℝ × ℝ →ₗ[ℝ] V))
    (hE : ∫⁻ z, ENNReal.ofReal (ω.floerEnergyDensity
        (fun z x ↦ p.perturbation H (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ p.perturbation H (Complex.equivRealProdCLM.symm z) x Complex.I) u z) ≠ ⊤)
    (hW : IsOpen W)
    (hJq : ContDiffOn ℝ 2 (fun q : ℝ × V ↦ (Jq q.1 q.2).toLinearMap.toContinuousLinearMap) W)
    (hJqper : Periodic Jq 1) (hKW : univ ×ˢ K ⊆ W) (hJqt : ∀ t, ∀ x ∈ K, ω.Tames (Jq t x))
    (hJcyl : ∀ s t, T₀ ≤ s →
      J (realChart p.cylindricalEndLift (p.endSign * s, t)) =
        Jq t (u (realChart p.cylindricalEndLift (p.endSign * s, t))))
    {L : ℝ≥0} (hL : LipschitzWith L (ω.timeDependentHamiltonianSuspension H))
    (hnd : ∀ x : ℝ → V, Periodic x 1 →
      (∀ t, HasDerivAt x (ω.hamiltonianVectorField (H t) (x t)) t) → (∀ t, x t ∈ K) →
      IsNondegenerateFixedPt 𝓘(ℝ, V) (ω.timeDependentHamiltonianFlow H hL 0 1) (x 0)) :
    ∃ x : ℝ → V, Periodic x 1 ∧ (∀ t, HasDerivAt x (ω.hamiltonianVectorField (H t) (x t)) t) ∧
      TendstoUniformly (fun R t ↦ u (Complex.equivRealProdCLM
        (p.cylindricalEndLift (↑(p.endSign * R) + ↑t * Complex.I)))) x atTop ∧
      Tendsto (fun R ↦ ω.hamiltonianAction H (fun t ↦ u (Complex.equivRealProdCLM
        (p.cylindricalEndLift (↑(p.endSign * R) + ↑t * Complex.I))))) atTop
        (𝓝 (ω.hamiltonianAction H x)) ∧
      ∫⁻ z, ENNReal.ofReal (ω.floerEnergyDensity
          (fun z x ↦ p.perturbation H (Complex.equivRealProdCLM.symm z) x 1)
          (fun z x ↦ p.perturbation H (Complex.equivRealProdCLM.symm z) x Complex.I) u z) =
        ENNReal.ofReal (p.endSign * ω.hamiltonianAction H x - ∫ z, ω.hamiltonianCurvature
          (fun z x ↦ p.perturbation H (Complex.equivRealProdCLM.symm z) x 1)
          (fun z x ↦ p.perturbation H (Complex.equivRealProdCLM.symm z) x Complex.I) z (u z)) :=
  exists_lintegral_floerEnergyDensity_pssPlanePerturbation_eq_of_cylindrical_of_isolated
    p hH hHs hu hK huK hJ hfloer hE hW hJq hJqper hKW hJqt hJcyl
    (isolated_of_isNondegenerateFixedPt hL hnd)

end InnerProductSpace

end TauCeti.SymplecticForm
