/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Floer.Plane.Fredholm
import TauCeti.Analysis.Complex.EquivRealProd
import TauCeti.Analysis.Fredholm.ContinuousFamily
import TauCeti.Geometry.Symplectic.ExistsCompatible
import TauCeti.Geometry.Symplectic.Floer.Continuation.Path
import TauCeti.MeasureTheory.Function.LpSeminorm.Tendsto

/-!
# The index of a PSS plane does not depend on the almost complex structure or the map over the disc

Let `u` be a finite-energy solution of the Floer equation of the positive PSS plane for a
period-one Hamiltonian `H` on a finite-dimensional symplectic inner product space `(V, ω)`, on the
end `‖w‖ > r` of the plane, asymptotic to nondegenerate one-periodic orbits of `H`. The realization
`D_u : W^{1,2}(ℂ, V) → L²(ℂ, V)` of its linearized Floer operator is Fredholm for every choice of
almost complex structures `J` that are compatible with `ω` along `u` on the disc `‖w‖ ≤ r` and equal
on the end to a fixed family `J_q(t)`
(`TauCeti.SymplecticForm.isFredholm_floerConformalSobolevOperator_of_finite_energy_positive`). This
file proves that its index is the same for any two such choices that moreover tame `ω` everywhere
and are `C³` along `u`
(`TauCeti.SymplecticForm.index_floerConformalSobolevOperator_eq_of_pssPlane_almostComplex`). It
also does not depend on the map over the disc: along any `C³` map `u'` equal to `u` on the end, for
structures that are `C³`, and compatible over the disc, at the points of the segments between `u`
and `u'`, the operator has the same index
(`TauCeti.SymplecticForm.index_floerConformalSobolevOperator_eq_of_pssPlane_map`); `u'` need not
solve the Floer equation over the disc. So the index of a PSS plane may be computed for any
convenient structure and any convenient map over the disc, one step toward expressing it through
the asymptotic data of the plane.

This is the PSS-plane counterpart of the invariance under the data for the pair of pants
(`TauCeti.SymplecticForm.index_floerConformalSobolevOperator_eq_of_pairOfPants_data`), and the proof
follows the same route. Two such choices `J` and `J'` are joined by the path of almost complex
structures `J_μ` whose Cayley coordinates relative to a fixed compatible structure run along the
segment between those of `J` and `J'` (`TauCeti.Floer.pathAlmostComplex`). Every `J_μ` is
compatible along `u` on the disc and equal to `J_q(t)` on the end, so the operator of every `J_μ`
is Fredholm. The coefficient fields of the members agree on the end, and on the compact disc they
are jointly continuous in `(μ, z)`, so they depend continuously on `μ` in `L^∞`; the operators then
form a continuous path of Fredholm operators, along which the index is constant
(`Continuous.index_eq_of_preconnectedSpace`). The continuity holds for every family of almost
complex structures indexed by a normed space, jointly `C¹` along `u` and constant on the end,
whose coefficient fields on conformal jets are essentially bounded
(`TauCeti.SymplecticForm.continuous_floerConformalSobolevOperator_positive_family`). For the map,
the path is the segment of maps `u + μ (u' - u)`, `0 ≤ μ ≤ 1`: every member agrees with `u` on the
end, where it inherits the Floer equation and the finite energy of `u`, so its operator is
Fredholm, and the coefficient fields are jointly continuous in `(μ, z)`
(`TauCeti.SymplecticForm.continuousAt_floerConformalJetCoeff_add_smul_sub`).

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

/-- **The realizations of the linearized Floer operator of a PSS plane depend continuously on the
almost complex structures.** Let `p ↦ J_p` be a family of almost complex structures on the plane,
indexed by a normed space `P`, jointly `C¹` in the parameter and the target point along `u`, whose
members all agree on the end `‖w‖ > r`. If the coefficient fields on conformal jets of the members
are essentially bounded, then the realizations `D_u : W^{1,2}(ℂ, V) → L²(ℂ, V)` of the linearized
Floer operators of the positive PSS plane for `J_p` depend continuously on `p` in operator norm. -/
theorem continuous_floerConformalSobolevOperator_positive_family {P : Type*}
    [NormedAddCommGroup P] [NormedSpace ℝ P] (ω : SymplecticForm V) {H : ℝ → V → ℝ}
    (hH : Periodic H 1) (hHs : ContDiff ℝ 2 (uncurry H))
    {J : P × (ℝ × ℝ) → V → AlmostComplexStructure V} {r : ℝ} {u : ℝ × ℝ → V}
    (hJ : ∀ p z, ContDiffAt ℝ 1
      (fun q : (P × (ℝ × ℝ)) × V ↦ (J q.1 q.2).toLinearMap.toContinuousLinearMap) ((p, z), u z))
    (hu : ContDiff ℝ 1 u)
    (hJr : ∀ p p' z, r < ‖Complex.equivRealProdCLM.symm z‖ → J (p, z) = J (p', z))
    (hM : ∀ p, MemLp (ω.floerConformalJetCoeff cylindricalWeight
      (fun z y ↦ (J (p, z) y).toLinearMap.toContinuousLinearMap)
      (fun z x ↦ positive.perturbation H (Complex.equivRealProdCLM.symm z) x 1)
      (fun z x ↦ positive.perturbation H (Complex.equivRealProdCLM.symm z) x Complex.I) u) ∞
      (volume.restrict univ)) :
    Continuous fun p ↦ ω.floerConformalSobolevOperator univ cylindricalWeight
      (fun z y ↦ (J (p, z) y).toLinearMap.toContinuousLinearMap)
      (fun z x ↦ positive.perturbation H (Complex.equivRealProdCLM.symm z) x 1)
      (fun z x ↦ positive.perturbation H (Complex.equivRealProdCLM.symm z) x Complex.I) u := by
  -- The perturbation of the plane, as a family that does not depend on the parameter.
  have hK (c : ℂ) (p : P × (ℝ × ℝ)) : ContDiffAt ℝ 2
      (uncurry fun (q : P × (ℝ × ℝ)) x ↦
        positive.perturbation H (Complex.equivRealProdCLM.symm q.2) x c) (p, u p.2) :=
    ((contDiff_uncurry_perturbation (p := positive) hH hHs c).comp
      ((contDiff_fst.snd).prodMk contDiff_snd)).contDiffAt
  -- The coefficient fields only change over the compact disc `‖w‖ ≤ r`, where they are jointly
  -- continuous in the parameter and the domain point.
  rw [← continuousOn_univ]
  simp only [floerConformalSobolevOperator_def]
  exact (continuousOn_jetOperator (fun p _ ↦ hM p) fun lam _ ↦ tendsto_nhdsWithin_of_tendsto_nhds
    (tendsto_eLpNorm_floerConformalJetCoeff_family ω MeasurableSet.univ
      (isCompact_setOf_norm_equivRealProdCLM_symm_le r)
      (J := fun p y ↦ (J p y).toLinearMap.toContinuousLinearMap)
      (Ks := fun q x ↦ positive.perturbation H (Complex.equivRealProdCLM.symm q.2) x 1)
      (Kt := fun q x ↦ positive.perturbation H (Complex.equivRealProdCLM.symm q.2) x Complex.I)
      (fun z _ ↦ hJ lam z) (fun z _ ↦ hK 1 _) (fun z _ ↦ hK Complex.I _)
      (fun z _ ↦ hu.contDiffAt) (fun z _ ↦ continuous_cylindricalWeight.continuousAt)
      (fun z _ ↦ isWeight_cylindricalWeight.pos _ (mem_univ z))
      (.of_forall fun p z _ hzK ↦ ⟨by rw [hJr p lam z (not_le.1 hzK)], rfl, rfl⟩)
      (.of_forall fun p ↦ (hM p).aestronglyMeasurable))).clm_comp continuousOn_const

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
  -- A structure compatible with `ω`, for the Cayley coordinates of the path.
  obtain ⟨J₀, h₀⟩ := ω.exists_compatible
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
  have hTc : Continuous T := continuous_floerConformalSobolevOperator_positive_family ω hH
    (hHs.of_le (by norm_num)) (fun μ z ↦ contDiffAt_pathAlmostComplex h₀ hJt hJ't (p := (μ, z))
      ((hJ z).of_le (by norm_num)) ((hJ' z).of_le (by norm_num))) (hu.of_le (by norm_num))
    (fun μ μ' z hz ↦ (hend μ z hz).trans (hend μ' z hz).symm) hM
  simpa only [hT, pathAlmostComplex_zero, pathAlmostComplex_one] using
    hTc.index_eq_of_preconnectedSpace hFred 1 0

/-- A `C³` map `v` of the plane that agrees with `u` near every point of the end `‖w‖ > r`
inherits there the Floer equation, the bound and the finite energy of `u`. So for structures that
are `C³` along `v` and compatible along `v` over the disc, its linearized operator is Fredholm, with
an essentially bounded coefficient field on conformal jets. -/
private theorem isFredholm_and_memLp_of_eventuallyEq_end (ω : SymplecticForm V)
    {H : ℝ → V → ℝ} (hH : Periodic H 1) (hHs : ContDiff ℝ 4 (uncurry H)) {L : ℝ≥0}
    (hL : LipschitzWith L (ω.timeDependentHamiltonianSuspension H)) {K : Set V}
    (hK : IsCompact K) {Jq : ℝ → V → AlmostComplexStructure V}
    (hJq : ContDiff ℝ 2 fun q : ℝ × V ↦ (Jq q.1 q.2).toLinearMap.toContinuousLinearMap)
    (hJqper : Periodic Jq 1) (hJqK : ∀ t, ∀ y ∈ K, ω.Compatible (Jq t y))
    {J : ℝ × ℝ → V → AlmostComplexStructure V} {r : ℝ} {u v : ℝ × ℝ → V}
    (hJ : ∀ z, ContDiffAt ℝ 3
      (fun q : (ℝ × ℝ) × V ↦ (J q.1 q.2).toLinearMap.toContinuousLinearMap) (z, v z))
    (hJr : ∀ z, r < ‖Complex.equivRealProdCLM.symm z‖ →
      J z = Jq (positive.endCoord (Complex.equivRealProdCLM.symm z)).im)
    (hv : ContDiff ℝ 3 v) (hvu : ∀ z, r < ‖Complex.equivRealProdCLM.symm z‖ → v =ᶠ[𝓝 z] u)
    (hc : ∀ z, ‖Complex.equivRealProdCLM.symm z‖ ≤ r → ω.Compatible (J z (v z)))
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
      (fun z y ↦ (J z y).toLinearMap.toContinuousLinearMap)
      (fun z x ↦ positive.perturbation H (Complex.equivRealProdCLM.symm z) x 1)
      (fun z x ↦ positive.perturbation H (Complex.equivRealProdCLM.symm z) x Complex.I)
      v).IsFredholm ∧
      MemLp (ω.floerConformalJetCoeff cylindricalWeight
        (fun z y ↦ (J z y).toLinearMap.toContinuousLinearMap)
        (fun z x ↦ positive.perturbation H (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ positive.perturbation H (Complex.equivRealProdCLM.symm z) x Complex.I) v) ∞
        (volume.restrict univ) := by
  have hEo : IsOpen {z : ℝ × ℝ | r < ‖Complex.equivRealProdCLM.symm z‖} :=
    isOpen_lt continuous_const (by fun_prop)
  have hvK (z : ℝ × ℝ) (hz : r < ‖Complex.equivRealProdCLM.symm z‖) : v z ∈ K := by
    rw [(hvu z hz).eq_of_nhds]
    exact huK z hz
  have hvF (z : ℝ × ℝ) (hz : r < ‖Complex.equivRealProdCLM.symm z‖) :
      IsComplexLinearMap (AlmostComplexStructure.product ℝ) (J z (v z))
        (ω.perturbedFDeriv
          (fun z x ↦ positive.perturbation H (Complex.equivRealProdCLM.symm z) x 1)
          (fun z x ↦ positive.perturbation H (Complex.equivRealProdCLM.symm z) x Complex.I) v
          z : ℝ × ℝ →ₗ[ℝ] V) := by
    rw [ω.perturbedFDeriv_congr_of_eventuallyEq _ _ (hvu z hz), (hvu z hz).eq_of_nhds]
    exact hF z hz
  have hvE : ∫⁻ z in {z | r < ‖Complex.equivRealProdCLM.symm z‖},
      ENNReal.ofReal (ω.floerEnergyDensity
        (fun z x ↦ positive.perturbation H (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ positive.perturbation H (Complex.equivRealProdCLM.symm z) x Complex.I)
        v z) ≠ ⊤ := by
    rwa [setLIntegral_congr_fun hEo.measurableSet fun z hz ↦ by
      rw [ω.floerEnergyDensity_congr_of_eventuallyEq _ _ (hvu z hz)]]
  exact ⟨ω.isFredholm_floerConformalSobolevOperator_of_finite_energy_positive hH hHs hL hK hJq
      hJqper hJqK hJ hJr hv hc hvK hvF hvE hnd,
    ω.memLp_floerConformalJetCoeff_of_finite_energy_positive hH (hHs.of_le (by norm_num)) hL hK
      hJq hJqper (fun t y hy ↦ (hJqK t y hy).tames) (fun z ↦ (hJ z).of_le (by norm_num)) hJr
      (hv.of_le (by norm_num)) hv.contDiffOn hvK hvF hvE hnd⟩

/-- The maps `u + c(ν) (u' - u)`, reparametrized by `c = projIcc 0 1`, take their values on the
segments between `u` and `u'`. -/
private theorem add_projIcc_smul_sub_mem_segment {E : Type*} [AddCommGroup E] [Module ℝ E]
    (u u' : ℝ × ℝ → E) (ν : ℝ) (z : ℝ × ℝ) :
    (u + (projIcc 0 1 zero_le_one ν : ℝ) • (u' - u)) z ∈ segment ℝ (u z) (u' z) := by
  rw [segment_eq_image']
  exact ⟨_, (projIcc 0 1 zero_le_one ν).prop, rfl⟩

/-- Along the segment of maps `u + c(ν) (u' - u)` from `u` to a map `u'` equal to `u` on the end
`‖w‖ > r`, reparametrized by `c = projIcc 0 1`, the realizations of the linearized Floer operators
of the plane depend continuously on `ν` in operator norm, when `J` is `C¹` at the points of the
segments between `u` and `u'` and the coefficient fields on conformal jets are essentially
bounded. -/
private theorem continuous_floerConformalSobolevOperator_projIcc (ω : SymplecticForm V)
    {H : ℝ → V → ℝ} (hH : Periodic H 1) (hHs : ContDiff ℝ 2 (uncurry H))
    {J : ℝ × ℝ → V → AlmostComplexStructure V} {r : ℝ} {u u' : ℝ × ℝ → V}
    (hJ : ∀ z, ∀ y ∈ segment ℝ (u z) (u' z), ContDiffAt ℝ 1
      (fun q : (ℝ × ℝ) × V ↦ (J q.1 q.2).toLinearMap.toContinuousLinearMap) (z, y))
    (hu : ContDiff ℝ 1 u) (hu' : ContDiff ℝ 1 u')
    (hu'r : ∀ z, r < ‖Complex.equivRealProdCLM.symm z‖ → u' =ᶠ[𝓝 z] u)
    (hM : ∀ ν : ℝ, MemLp (ω.floerConformalJetCoeff cylindricalWeight
      (fun z y ↦ (J z y).toLinearMap.toContinuousLinearMap)
      (fun z x ↦ positive.perturbation H (Complex.equivRealProdCLM.symm z) x 1)
      (fun z x ↦ positive.perturbation H (Complex.equivRealProdCLM.symm z) x Complex.I)
      (u + (projIcc 0 1 zero_le_one ν : ℝ) • (u' - u))) ∞ (volume.restrict univ)) :
    Continuous fun ν : ℝ ↦ ω.floerConformalSobolevOperator univ cylindricalWeight
      (fun z y ↦ (J z y).toLinearMap.toContinuousLinearMap)
      (fun z x ↦ positive.perturbation H (Complex.equivRealProdCLM.symm z) x 1)
      (fun z x ↦ positive.perturbation H (Complex.equivRealProdCLM.symm z) x Complex.I)
      (u + (projIcc 0 1 zero_le_one ν : ℝ) • (u' - u)) := by
  set c : ℝ → ℝ := fun ν ↦ (projIcc 0 1 zero_le_one ν : ℝ)
  set M : ℝ → ℝ × ℝ → V × V × V →L[ℝ] V := fun ν ↦
    ω.floerConformalJetCoeff cylindricalWeight
      (fun z y ↦ (J z y).toLinearMap.toContinuousLinearMap)
      (fun z x ↦ positive.perturbation H (Complex.equivRealProdCLM.symm z) x 1)
      (fun z x ↦ positive.perturbation H (Complex.equivRealProdCLM.symm z) x Complex.I)
      (u + c ν • (u' - u))
  have hKs (c' : ℂ) (p : (ℝ × ℝ) × V) : ContDiffAt ℝ 2
      (uncurry fun z x ↦ positive.perturbation H (Complex.equivRealProdCLM.symm z) x c') p :=
    (contDiff_uncurry_perturbation (p := positive) hH hHs c').contDiffAt
  -- The coefficient fields are jointly continuous in the parameter and the domain point.
  have hjoint (ν : ℝ) (z : ℝ × ℝ) : ContinuousAt (uncurry M) (ν, z) :=
    ContinuousAt.comp (f := fun x : ℝ × (ℝ × ℝ) ↦ (c x.1, x.2)) (x := (ν, z))
      (ω.continuousAt_floerConformalJetCoeff_add_smul_sub (u := u) (u' := u') (lam := c ν) (z := z)
        (J := fun z y ↦ (J z y).toLinearMap.toContinuousLinearMap)
        (hJ z _ (add_projIcc_smul_sub_mem_segment u u' ν z))
        (hKs 1 _) (hKs Complex.I _) hu.contDiffAt hu'.contDiffAt
        continuous_cylindricalWeight.continuousAt (isWeight_cylindricalWeight.pos _ (mem_univ z)))
      (((continuous_subtypeVal.comp continuous_projIcc).continuousAt.comp
        continuousAt_fst).prodMk continuousAt_snd)
  -- Off the compact disc `‖w‖ ≤ r` they do not depend on the parameter.
  have hoff (ν ν' : ℝ) (z : ℝ × ℝ) (hz : r < ‖Complex.equivRealProdCLM.symm z‖) :
      M ν' z = M ν z := by
    have hvE (ν : ℝ) : u + c ν • (u' - u) =ᶠ[𝓝 z] u :=
      (hu'r z hz).mono fun w hw ↦ by simp [hw]
    exact (ω.floerConformalJetCoeff_congr_of_eventuallyEq _ _ _ _ (hvE ν')).trans
      (ω.floerConformalJetCoeff_congr_of_eventuallyEq _ _ _ _ (hvE ν)).symm
  rw [← continuousOn_univ]
  simp only [floerConformalSobolevOperator_def]
  exact (continuousOn_jetOperator (fun ν _ ↦ hM ν) fun ν _ ↦
    tendsto_nhdsWithin_of_tendsto_nhds (tendsto_eLpNorm_top_sub_of_continuousAt_of_eq
      (μ := volume) (M := M) MeasurableSet.univ (isCompact_setOf_norm_equivRealProdCLM_symm_le r)
      (.of_forall fun ν' ↦ (hM ν').aestronglyMeasurable) (fun z _ ↦ hjoint ν z)
      (.of_forall fun ν' z _ hz ↦ hoff ν ν' z (not_le.1 hz)))).clm_comp continuousOn_const

/-- **The index of a PSS plane does not depend on the map over the disc.** Let `H` be a `C⁴`
Hamiltonian of period one in time, with globally Lipschitz suspended vector field, whose
one-periodic orbits in a compact set `K` are nondegenerate. Let `u` be a `C³` map of the plane
that solves the Floer equation of the positive PSS plane for `H` on the end `‖w‖ > r`, with finite
energy there and values in `K`, for almost complex structures `J` equal on the end to a `C²` family
`J_q(t)` of period one compatible with `ω` on `K`. Let `u'` be another `C³` map of the plane, equal
to `u` on the end, and let `J` be `C³` at the points of the segments between `u` and `u'`, and
compatible with `ω` at these points over the disc `‖w‖ ≤ r`. Then the realizations
`D_u, D_{u'} : W^{1,2}(ℂ, V) → L²(ℂ, V)` of the linearized Floer operators along `u` and along
`u'`, which are Fredholm (`isFredholm_floerConformalSobolevOperator_of_finite_energy_positive`),
have the same index. The map `u'` need not solve the Floer equation over the disc. -/
theorem index_floerConformalSobolevOperator_eq_of_pssPlane_map (ω : SymplecticForm V)
    {H : ℝ → V → ℝ} (hH : Periodic H 1) (hHs : ContDiff ℝ 4 (uncurry H)) {L : ℝ≥0}
    (hL : LipschitzWith L (ω.timeDependentHamiltonianSuspension H)) {K : Set V}
    (hK : IsCompact K) {Jq : ℝ → V → AlmostComplexStructure V}
    (hJq : ContDiff ℝ 2 fun q : ℝ × V ↦ (Jq q.1 q.2).toLinearMap.toContinuousLinearMap)
    (hJqper : Periodic Jq 1) (hJqK : ∀ t, ∀ y ∈ K, ω.Compatible (Jq t y))
    {J : ℝ × ℝ → V → AlmostComplexStructure V} {r : ℝ} {u u' : ℝ × ℝ → V}
    (hJ : ∀ z, ∀ y ∈ segment ℝ (u z) (u' z), ContDiffAt ℝ 3
      (fun q : (ℝ × ℝ) × V ↦ (J q.1 q.2).toLinearMap.toContinuousLinearMap) (z, y))
    (hJr : ∀ z, r < ‖Complex.equivRealProdCLM.symm z‖ →
      J z = Jq (positive.endCoord (Complex.equivRealProdCLM.symm z)).im)
    (hu : ContDiff ℝ 3 u) (hu' : ContDiff ℝ 3 u')
    (hu'r : ∀ z, r < ‖Complex.equivRealProdCLM.symm z‖ → u' z = u z)
    (hc : ∀ z, ‖Complex.equivRealProdCLM.symm z‖ ≤ r → ∀ y ∈ segment ℝ (u z) (u' z),
      ω.Compatible (J z y))
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
      (fun z y ↦ (J z y).toLinearMap.toContinuousLinearMap)
      (fun z x ↦ positive.perturbation H (Complex.equivRealProdCLM.symm z) x 1)
      (fun z x ↦ positive.perturbation H (Complex.equivRealProdCLM.symm z) x Complex.I)
      u').index =
      (ω.floerConformalSobolevOperator univ cylindricalWeight
        (fun z y ↦ (J z y).toLinearMap.toContinuousLinearMap)
        (fun z x ↦ positive.perturbation H (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ positive.perturbation H (Complex.equivRealProdCLM.symm z) x Complex.I)
        u).index := by
  have hEo : IsOpen {z : ℝ × ℝ | r < ‖Complex.equivRealProdCLM.symm z‖} :=
    isOpen_lt continuous_const (by fun_prop)
  -- The maps `u + c(ν) (u' - u)` of the segment, reparametrized by `c = projIcc 0 1` so that
  -- every member of the family lies on the segment. On the end they agree with `u`, so their
  -- operators are Fredholm.
  have hseg := add_projIcc_smul_sub_mem_segment u u'
  have hu'E (z : ℝ × ℝ) (hz : r < ‖Complex.equivRealProdCLM.symm z‖) : u' =ᶠ[𝓝 z] u :=
    Filter.eventuallyEq_of_mem (hEo.mem_nhds hz) hu'r
  have hfam (ν : ℝ) := isFredholm_and_memLp_of_eventuallyEq_end ω hH hHs hL hK hJq hJqper hJqK
    (fun z ↦ hJ z _ (hseg ν z)) hJr (hu.add ((hu'.sub hu).const_smul _))
    (fun z hz ↦ (hu'E z hz).mono fun w hw ↦ by simp [hw])
    (fun z hz ↦ hc z hz _ (hseg ν z)) huK hF hE hnd
  -- The operators form a continuous path of Fredholm operators from `u` at `0` to `u'` at `1`,
  -- along which the index is constant.
  have hT := continuous_floerConformalSobolevOperator_projIcc ω hH (hHs.of_le (by norm_num))
    (fun z y hy ↦ (hJ z y hy).of_le (by norm_num)) (hu.of_le (by norm_num))
    (hu'.of_le (by norm_num)) hu'E fun ν ↦ (hfam ν).2
  simpa only [projIcc_left, projIcc_right, zero_smul, add_zero, one_smul, add_sub_cancel] using
    hT.index_eq_of_preconnectedSpace (fun ν ↦ (hfam ν).1) 1 0
end TauCeti.SymplecticForm
