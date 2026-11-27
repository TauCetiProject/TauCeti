/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Floer.Plane.Fredholm
import TauCeti.Analysis.Complex.EquivRealProd
import TauCeti.Analysis.Fredholm.ContinuousFamily
import TauCeti.Geometry.Symplectic.Floer.Continuation.Path

/-!
# The index of a PSS plane does not depend on the almost complex structure over the disc

Let `u` be a finite-energy solution of the Floer equation of the positive PSS plane for a
period-one Hamiltonian `H` on a finite-dimensional symplectic inner product space `(V, ω)`, on the
end `‖w‖ > r` of the plane, asymptotic to nondegenerate one-periodic orbits of `H`. The realization
`D_u : W^{1,2}(ℂ, V) → L²(ℂ, V)` of its linearized Floer operator is Fredholm for every choice of
almost complex structures `J` that are compatible with `ω` along `u` on the disc `‖w‖ ≤ r` and equal
on the end to a fixed family `J_q(t)`
(`TauCeti.SymplecticForm.isFredholm_floerConformalSobolevOperator_of_finite_energy_positive`). This
file proves that its index is the same for any two such choices that moreover tame `ω` everywhere
and are `C³` along `u`
(`TauCeti.SymplecticForm.index_floerConformalSobolevOperator_eq_of_pssPlane_almostComplex`). So the
index of a PSS plane may be computed for any convenient structure over the disc, one step toward
expressing it through the asymptotic data of the plane.

This is the PSS-plane counterpart of the invariance under the data for the pair of pants
(`TauCeti.SymplecticForm.index_floerConformalSobolevOperator_eq_of_pairOfPants_data`), and the proof
follows the same route. Two such choices `J` and `J'` are joined by the path of almost complex
structures `J_μ` whose Cayley coordinates relative to a fixed compatible structure run along the
segment between those of `J` and `J'` (`TauCeti.Floer.pathAlmostComplex`). Every `J_μ` is
compatible along `u` on the disc and equal to `J_q(t)` on the end, so the operator of every `J_μ`
is Fredholm. The coefficient fields of the members agree on the end, and on the compact disc they
are jointly continuous in `(μ, z)`, so they depend continuously on `μ` in `L^∞`; the operators then
form a continuous path of Fredholm operators, along which the index is constant
(`Continuous.index_eq_of_preconnectedSpace`).

Every PSS plane is the positive plane for a rescaled Hamiltonian
(`TauCeti.Floer.PSSPlane.perturbation_eq_positive`), so the statement covers the negative plane as
well.

## References

* D. Salamon, *Lectures on Floer homology*, in *Symplectic geometry and topology*, IAS/Park City
  Math. Ser. 7 (1999), Lecture 2, on the Fredholm index of `∂s + J ∂t + S(s, t)`, which depends
  only on the asymptotic operators.
* S. Piunikhin, D. Salamon and M. Schwarz, *Symplectic Floer–Donaldson theory and quantum
  cohomology*, in *Contact and symplectic geometry*, Publ. Newton Inst. 8 (1996), 171–200, on the
  PSS planes and their Fredholm theory.
-/

public section

noncomputable section

open Set Function Filter MeasureTheory Topology
open scoped ENNReal NNReal Manifold

namespace TauCeti.SymplecticForm

open Floer Floer.PSSPlane ConformalSobolev

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]

/-- Along the path of almost complex structures `J_μ` from `J` to `J'` (`pathAlmostComplex`), for
`J` and `J'` that are `C¹` along `u` and agree on the end `‖w‖ > r`, the realizations of the
linearized Floer operators of the positive PSS plane depend continuously on `μ` in operator norm,
provided their coefficient fields on conformal jets are essentially bounded. -/
private theorem continuous_floerConformalSobolevOperator_pathAlmostComplex (ω : SymplecticForm V)
    {H : ℝ → V → ℝ} (hH : Periodic H 1) (hHs : ContDiff ℝ 2 (uncurry H))
    {J₀ : AlmostComplexStructure V} (h₀ : ω.Compatible J₀)
    {J J' : ℝ × ℝ → V → AlmostComplexStructure V} (hJt : ∀ z y, ω.Tames (J z y))
    (hJ't : ∀ z y, ω.Tames (J' z y)) {r : ℝ} {u : ℝ × ℝ → V}
    (hJ : ∀ z, ContDiffAt ℝ 1
      (fun q : (ℝ × ℝ) × V ↦ (J q.1 q.2).toLinearMap.toContinuousLinearMap) (z, u z))
    (hJ' : ∀ z, ContDiffAt ℝ 1
      (fun q : (ℝ × ℝ) × V ↦ (J' q.1 q.2).toLinearMap.toContinuousLinearMap) (z, u z))
    (hu : ContDiff ℝ 1 u) (hJJ' : ∀ z, r < ‖Complex.equivRealProdCLM.symm z‖ → J z = J' z)
    (hM : ∀ μ, MemLp (ω.floerConformalJetCoeff cylindricalWeight
      (fun z y ↦ (pathAlmostComplex h₀ hJt hJ't (μ, z) y).toLinearMap.toContinuousLinearMap)
      (fun z x ↦ positive.perturbation H (Complex.equivRealProdCLM.symm z) x 1)
      (fun z x ↦ positive.perturbation H (Complex.equivRealProdCLM.symm z) x Complex.I) u) ∞
      (volume.restrict univ)) :
    Continuous fun μ ↦ ω.floerConformalSobolevOperator univ cylindricalWeight
      (fun z y ↦ (pathAlmostComplex h₀ hJt hJ't (μ, z) y).toLinearMap.toContinuousLinearMap)
      (fun z x ↦ positive.perturbation H (Complex.equivRealProdCLM.symm z) x 1)
      (fun z x ↦ positive.perturbation H (Complex.equivRealProdCLM.symm z) x Complex.I) u := by
  -- The perturbation of the plane, as a family that does not depend on the parameter.
  have hK (c : ℂ) (p : ℝ × (ℝ × ℝ)) : ContDiffAt ℝ 2
      (uncurry fun (q : ℝ × (ℝ × ℝ)) x ↦
        positive.perturbation H (Complex.equivRealProdCLM.symm q.2) x c) (p, u p.2) :=
    ((contDiff_uncurry_perturbation (p := positive) hH hHs c).comp
      ((contDiff_fst.snd).prodMk contDiff_snd)).contDiffAt
  -- On the end every member of the path is the common value of `J` and `J'`.
  have hend (μ : ℝ) (z : ℝ × ℝ) (hz : r < ‖Complex.equivRealProdCLM.symm z‖) :
      pathAlmostComplex h₀ hJt hJ't (μ, z) = J z :=
    funext fun y ↦ pathAlmostComplex_of_eq h₀ μ (congrFun (hJJ' z hz) y)
  -- So the coefficient fields only change over the compact disc `‖w‖ ≤ r`, where they are jointly
  -- continuous in the parameter and the domain point.
  rw [← continuousOn_univ]
  simp only [floerConformalSobolevOperator_def]
  exact (continuousOn_jetOperator (fun μ _ ↦ hM μ) fun lam _ ↦ tendsto_nhdsWithin_of_tendsto_nhds
    (tendsto_eLpNorm_floerConformalJetCoeff_family ω MeasurableSet.univ
      (isCompact_setOf_norm_equivRealProdCLM_symm_le r)
      (J := fun p y ↦ (pathAlmostComplex h₀ hJt hJ't p y).toLinearMap.toContinuousLinearMap)
      (Ks := fun q x ↦ positive.perturbation H (Complex.equivRealProdCLM.symm q.2) x 1)
      (Kt := fun q x ↦ positive.perturbation H (Complex.equivRealProdCLM.symm q.2) x Complex.I)
      (fun z _ ↦ contDiffAt_pathAlmostComplex h₀ hJt hJ't (p := (lam, z)) (hJ z) (hJ' z))
      (fun z _ ↦ hK 1 _) (fun z _ ↦ hK Complex.I _) (fun z _ ↦ hu.contDiffAt)
      (fun z _ ↦ continuous_cylindricalWeight.continuousAt)
      (fun z _ ↦ isWeight_cylindricalWeight.pos _ (mem_univ z))
      (.of_forall fun μ z _ hzK ↦ ⟨funext fun y ↦ by
        simp only [hend μ z (not_le.1 hzK), hend lam z (not_le.1 hzK)], rfl, rfl⟩)
      (.of_forall fun μ ↦ (hM μ).aestronglyMeasurable))).clm_comp continuousOn_const

/-- **The index of a PSS plane does not depend on the almost complex structure over the disc.**
Let `H` be a `C⁴` Hamiltonian of period one in time, with globally Lipschitz suspended vector field,
whose one-periodic orbits in a compact set `K` are nondegenerate. Let `u` be a `C³` map of the plane
that solves the Floer equation of the positive PSS plane for `H` on the end `‖w‖ > r`, with finite
energy there and values in `K`, for almost complex structures `J` that are `C³` along `u` and equal
on the end to a `C²` family `J_q(t)` of period one compatible with `ω` on `K`. Let `J'` be another
family of almost complex structures, `C³` along `u` and equal to `J_q(t)` on the end, and let `J`
and `J'` both tame `ω` and be compatible with `ω` along `u` on the disc `‖w‖ ≤ r`. Then the
realizations `D_u : W^{1,2}(ℂ, V) → L²(ℂ, V)` of the linearized Floer operators of `J` and of `J'`,
which are Fredholm (`isFredholm_floerConformalSobolevOperator_of_finite_energy_positive`), have the
same index. -/
theorem index_floerConformalSobolevOperator_eq_of_pssPlane_almostComplex (ω : SymplecticForm V)
    {H : ℝ → V → ℝ} (hH : Periodic H 1) (hHs : ContDiff ℝ 4 (uncurry H)) {L : ℝ≥0}
    (hL : LipschitzWith L (ω.timeDependentHamiltonianSuspension H)) {K : Set V}
    (hK : IsCompact K) {Jq : ℝ → V → AlmostComplexStructure V}
    (hJq : ContDiff ℝ 2 fun q : ℝ × V ↦ (Jq q.1 q.2).toLinearMap.toContinuousLinearMap)
    (hJqper : Periodic Jq 1) (hJqK : ∀ t, ∀ y ∈ K, ω.Compatible (Jq t y))
    {J J' : ℝ × ℝ → V → AlmostComplexStructure V} {r : ℝ} {u : ℝ × ℝ → V}
    (hJ : ∀ z, ContDiffAt ℝ 3
      (fun q : (ℝ × ℝ) × V ↦ (J q.1 q.2).toLinearMap.toContinuousLinearMap) (z, u z))
    (hJ' : ∀ z, ContDiffAt ℝ 3
      (fun q : (ℝ × ℝ) × V ↦ (J' q.1 q.2).toLinearMap.toContinuousLinearMap) (z, u z))
    (hJt : ∀ z y, ω.Tames (J z y)) (hJ't : ∀ z y, ω.Tames (J' z y))
    (hJr : ∀ z, r < ‖Complex.equivRealProdCLM.symm z‖ →
      J z = Jq (positive.endCoord (Complex.equivRealProdCLM.symm z)).im)
    (hJr' : ∀ z, r < ‖Complex.equivRealProdCLM.symm z‖ →
      J' z = Jq (positive.endCoord (Complex.equivRealProdCLM.symm z)).im)
    (hu : ContDiff ℝ 3 u)
    (hc : ∀ z, ‖Complex.equivRealProdCLM.symm z‖ ≤ r → ω.Compatible (J z (u z)))
    (hc' : ∀ z, ‖Complex.equivRealProdCLM.symm z‖ ≤ r → ω.Compatible (J' z (u z)))
    (huK : ∀ z, r < ‖Complex.equivRealProdCLM.symm z‖ → u z ∈ K)
    (hF : ∀ z, r < ‖Complex.equivRealProdCLM.symm z‖ →
      IsComplexLinearMap (AlmostComplexStructure.product ℝ) (J z (u z))
        (ω.perturbedFDeriv
          (fun z x ↦ positive.perturbation H (Complex.equivRealProdCLM.symm z) x 1)
          (fun z x ↦ positive.perturbation H (Complex.equivRealProdCLM.symm z) x Complex.I) u
          z : ℝ × ℝ →ₗ[ℝ] V))
    (hE : ∫⁻ z in {z | r < ‖Complex.equivRealProdCLM.symm z‖},
      ENNReal.ofReal (ω.floerEnergyDensity
        (fun z x ↦ positive.perturbation H (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ positive.perturbation H (Complex.equivRealProdCLM.symm z) x Complex.I)
        u z) ≠ ⊤)
    (hnd : ∀ x : ℝ → V, Periodic x 1 →
      (∀ t, HasDerivAt x (ω.hamiltonianVectorField (H t) (x t)) t) → (∀ t, x t ∈ K) →
      IsNondegenerateFixedPt 𝓘(ℝ, V) (ω.timeDependentHamiltonianFlow H hL 0 1) (x 0)) :
    (ω.floerConformalSobolevOperator univ cylindricalWeight
      (fun z y ↦ (J' z y).toLinearMap.toContinuousLinearMap)
      (fun z x ↦ positive.perturbation H (Complex.equivRealProdCLM.symm z) x 1)
      (fun z x ↦ positive.perturbation H (Complex.equivRealProdCLM.symm z) x Complex.I) u).index =
      (ω.floerConformalSobolevOperator univ cylindricalWeight
        (fun z y ↦ (J z y).toLinearMap.toContinuousLinearMap)
        (fun z x ↦ positive.perturbation H (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ positive.perturbation H (Complex.equivRealProdCLM.symm z) x Complex.I)
        u).index := by
  -- A structure compatible with `ω`, for the Cayley coordinates of the path: `J_q(t)` at a point
  -- of `K` reached by `u` on the end.
  obtain ⟨z₀, hz₀⟩ : ∃ z : ℝ × ℝ, r < ‖Complex.equivRealProdCLM.symm z‖ :=
    ⟨Complex.equivRealProdCLM ((|r| + 1 : ℝ) : ℂ), by
      rw [ContinuousLinearEquiv.symm_apply_apply, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos (by positivity)]
      linarith [le_abs_self r]⟩
  have h₀ := hJqK 0 (u z₀) (huK z₀ hz₀)
  -- The path `J_μ` from `J` at `μ = 0` to `J'` at `μ = 1`. On the end `J` and `J'` agree, hence
  -- so does every `J_μ`.
  have hend (μ : ℝ) (z : ℝ × ℝ) (hz : r < ‖Complex.equivRealProdCLM.symm z‖) :
      pathAlmostComplex h₀ hJt hJ't (μ, z) = J z :=
    funext fun y ↦ pathAlmostComplex_of_eq h₀ μ (congrFun ((hJr z hz).trans (hJr' z hz).symm) y)
  have hJμ (μ : ℝ) (z : ℝ × ℝ) : ContDiffAt ℝ 3 (fun q : (ℝ × ℝ) × V ↦
      (pathAlmostComplex h₀ hJt hJ't (μ, q.1) q.2).toLinearMap.toContinuousLinearMap) (z, u z) :=
    -- The structure at a fixed `μ` is the path composed with the slice `(z, y) ↦ ((μ, z), y)`;
    -- the ascription elaborates that composite before matching it.
    ((contDiffAt_pathAlmostComplex h₀ hJt hJ't (p := (μ, z)) (hJ z) (hJ' z)).comp (z, u z)
      ((contDiff_const.prodMk contDiff_fst).prodMk contDiff_snd).contDiffAt :)
  have hJμr (μ : ℝ) (z : ℝ × ℝ) (hz : r < ‖Complex.equivRealProdCLM.symm z‖) :
      pathAlmostComplex h₀ hJt hJ't (μ, z) =
        Jq (positive.endCoord (Complex.equivRealProdCLM.symm z)).im :=
    (hend μ z hz).trans (hJr z hz)
  -- The operators of the path.
  set T : ℝ → H1 V univ cylindricalWeight →L[ℝ] Lp V 2 (volume.restrict univ) := fun μ ↦
    ω.floerConformalSobolevOperator univ cylindricalWeight
      (fun z y ↦ (pathAlmostComplex h₀ hJt hJ't (μ, z) y).toLinearMap.toContinuousLinearMap)
      (fun z x ↦ positive.perturbation H (Complex.equivRealProdCLM.symm z) x 1)
      (fun z x ↦ positive.perturbation H (Complex.equivRealProdCLM.symm z) x Complex.I) u with hT
  have hFred (μ : ℝ) : (T μ).IsFredholm :=
    ω.isFredholm_floerConformalSobolevOperator_of_finite_energy_positive hH hHs hL hK hJq hJqper
      hJqK (hJμ μ) (hJμr μ) hu
      (fun z hz ↦ compatible_pathAlmostComplex h₀ (p := (μ, z)) (hc z hz) (hc' z hz)) huK
      (fun z hz ↦ hend μ z hz ▸ hF z hz) hE hnd
  have hM (μ : ℝ) := ω.memLp_floerConformalJetCoeff_of_finite_energy_positive hH
    (hHs.of_le (by norm_num)) hL hK hJq hJqper (fun t y hy ↦ (hJqK t y hy).tames)
    (fun z ↦ (hJμ μ z).of_le (by norm_num)) (hJμr μ) (hu.of_le (by norm_num)) hu.contDiffOn huK
    (fun z hz ↦ hend μ z hz ▸ hF z hz) hE hnd
  -- The path of operators is continuous, so its index is constant.
  have hTc : Continuous T := continuous_floerConformalSobolevOperator_pathAlmostComplex ω hH
    (hHs.of_le (by norm_num)) h₀ hJt hJ't (fun z ↦ (hJ z).of_le (by norm_num))
    (fun z ↦ (hJ' z).of_le (by norm_num)) (hu.of_le (by norm_num))
    (fun z hz ↦ (hJr z hz).trans (hJr' z hz).symm) hM
  simpa only [hT, pathAlmostComplex_zero, pathAlmostComplex_one] using
    hTc.index_eq_of_preconnectedSpace hFred 1 0

end TauCeti.SymplecticForm
