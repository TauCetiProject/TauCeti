/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Floer.Plane.Fredholm
public import TauCeti.Geometry.Symplectic.Floer.Transversality.Conformal

/-!
# Hamiltonian variations make the linearized operator of a PSS plane onto

Let `u` be a finite-energy PSS plane in a finite-dimensional symplectic vector space `(V, ω)`:
a map of the plane `ℂ ≅ ℝ × ℝ` solving the Floer equation of the positive PSS plane for a
Hamiltonian `H` on the end `‖w‖ > r`, whose one-periodic orbits are nondegenerate. Let
`D_u : W^{1,2}(ℂ, V) → L²(ℂ, V)` be the realization of its linearized Floer operator for the
cylindrical weight of the plane (`TauCeti.SymplecticForm.floerConformalSobolevOperator` with
`TauCeti.Floer.PSSPlane.cylindricalWeight`). The moduli spaces of PSS planes are made regular by
varying the Hamiltonian perturbation, which is free on the plane: adding a smooth compactly
supported `δK` to its `ds` component moves the Floer operator at `u` by `-X_{δK}(u)`, the
Hamiltonian variation of `TauCeti.SymplecticForm.hamiltonianVariationsOn`.

This file proves that finitely many such variations, supported near the graph of `u` over any
nonempty open set `O` of the plane, span `L²(ℂ, V)` together with the range of `D_u`
(`exists_finset_subset_hamiltonianVariationsOn_range_sup_span_eq_top_of_finite_energy_positive`,
in the namespace `TauCeti.SymplecticForm`).
This is the surjectivity of the universal linearized operator of the finite-dimensional family of
perturbations `K_s + ∑ cᵢ δKᵢ`, the linear input of the Sard–Smale argument for regular moduli
spaces of PSS planes. No hypothesis is placed on `u` over `O`, which may be constant there.

The proof combines three facts. The variations detect the cokernel of `D_u` on any connected
open set with a conformal weight
(`TauCeti.SymplecticForm.exists_finset_subset_hamiltonianVariationsOn_range_sup_span_eq_top`), here
the whole plane; this needs the coefficient field of `D_u` on conformal jets to be bounded, which
holds along a finite-energy plane
(`TauCeti.SymplecticForm.memLp_floerConformalJetCoeff_of_finite_energy_positive`); and `D_u` is
Fredholm
(`TauCeti.SymplecticForm.isFredholm_floerConformalSobolevOperator_of_finite_energy_positive`), so
its range is closed of finite codimension. Every PSS plane is the positive plane for a rescaled
Hamiltonian (`TauCeti.Floer.PSSPlane.perturbation_eq_positive`), so the theorem covers the
negative plane as well.

## References

* S. Piunikhin, D. Salamon and M. Schwarz, *Symplectic Floer–Donaldson theory and quantum
  cohomology*, in *Contact and symplectic geometry*, Publ. Newton Inst. 8 (1996), 171–200, on the
  transversality of the moduli spaces of perturbed planes.
* D. McDuff and D. Salamon, *J-holomorphic curves and symplectic topology*, 2nd ed., AMS
  Colloquium Publications 52, 2012, Proposition 3.2.1 and Section 8.1, on the surjectivity of the
  universal linearized operator and on Hamiltonian perturbations.
-/

public section

open Set Function Filter Topology MeasureTheory
open scoped ENNReal NNReal Manifold

namespace TauCeti

namespace SymplecticForm

open Floer Floer.PSSPlane

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]

/-- **Finitely many Hamiltonian variations make the linearized operator of a PSS plane onto.** Let
`H` be a `C⁴` Hamiltonian of period one in time, with globally Lipschitz suspended vector field,
whose one-periodic orbits in a compact set `K` are nondegenerate. Let `u` be a `C³` map of the plane
that solves the Floer equation of the positive PSS plane for `H` on the end `‖w‖ > r`, with finite
energy there and values in `K`, for almost complex structures `J` that are `C³` along `u`, equal on
the end to a `C²` family `J_q(t)` of period one compatible with `ω` on `K`, and compatible along `u`
on the disc `‖w‖ ≤ r`. Then for every nonempty open set `O` of the plane and every neighbourhood `W`
of the graph of `u` over `O`, finitely many Hamiltonian variations supported in `W` span
`L²(ℂ, V)` together with the range of `D_u : W^{1,2}(ℂ, V) → L²(ℂ, V)`. -/
theorem exists_finset_subset_hamiltonianVariationsOn_range_sup_span_eq_top_of_finite_energy_positive
    (ω : SymplecticForm V) {H : ℝ → V → ℝ} (hH : Periodic H 1) (hHs : ContDiff ℝ 4 (uncurry H))
    {L : ℝ≥0} (hL : LipschitzWith L (ω.timeDependentHamiltonianSuspension H)) {K : Set V}
    (hK : IsCompact K) {Jq : ℝ → V → AlmostComplexStructure V}
    (hJq : ContDiff ℝ 2 fun q : ℝ × V ↦ (Jq q.1 q.2).toLinearMap.toContinuousLinearMap)
    (hJqper : Periodic Jq 1) (hJqK : ∀ t, ∀ y ∈ K, ω.Compatible (Jq t y))
    {J : ℝ × ℝ → V → AlmostComplexStructure V} {r : ℝ} {u : ℝ × ℝ → V}
    (hJ : ∀ z, ContDiffAt ℝ 3
      (fun q : (ℝ × ℝ) × V ↦ (J q.1 q.2).toLinearMap.toContinuousLinearMap) (z, u z))
    (hJr : ∀ z, r < ‖Complex.equivRealProdCLM.symm z‖ →
      J z = Jq (positive.endCoord (Complex.equivRealProdCLM.symm z)).im)
    (hu : ContDiff ℝ 3 u)
    (hc : ∀ z, ‖Complex.equivRealProdCLM.symm z‖ ≤ r → ω.Compatible (J z (u z)))
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
      IsNondegenerateFixedPt 𝓘(ℝ, V) (ω.timeDependentHamiltonianFlow H hL 0 1) (x 0))
    {O : Set (ℝ × ℝ)} (hO : IsOpen O) (hOne : O.Nonempty)
    {W : Set ((ℝ × ℝ) × V)} (hW : ∀ z ∈ O, W ∈ 𝓝 (z, u z)) :
    ∃ t : Finset (Lp V 2 (volume.restrict (univ : Set (ℝ × ℝ)))),
      (t : Set _) ⊆ ω.hamiltonianVariationsOn univ u W ∧
      (ω.floerConformalSobolevOperator univ PSSPlane.cylindricalWeight
        (fun z y ↦ (J z y).toLinearMap.toContinuousLinearMap)
        (fun z x ↦ positive.perturbation H (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ positive.perturbation H (Complex.equivRealProdCLM.symm z) x Complex.I)
        u).range ⊔ Submodule.span ℝ t = ⊤ := by
  have hD := ω.isFredholm_floerConformalSobolevOperator_of_finite_energy_positive hH hHs hL hK
    hJq hJqper hJqK hJ hJr hu hc huK hF hE hnd
  have hM := ω.memLp_floerConformalJetCoeff_of_finite_energy_positive hH (hHs.of_le (by norm_num))
    hL hK hJq hJqper (fun t y hy ↦ (hJqK t y hy).tames) (fun z ↦ (hJ z).of_le (by norm_num)) hJr
    (hu.of_le (by norm_num)) hu.contDiffOn huK hF hE hnd
  exact exists_finset_subset_hamiltonianVariationsOn_range_sup_span_eq_top
    isWeight_cylindricalWeight isPreconnected_univ (fun z _ ↦ (hJ z).of_le (by norm_num))
    (fun z _ ↦ ContinuousLinearMap.ext fun v ↦ by simp)
    (fun z _ ↦ ((contDiff_uncurry_perturbation (p := positive) hH hHs 1).of_le
      (by norm_num)).contDiffAt)
    (fun z _ ↦ ((contDiff_uncurry_perturbation (p := positive) hH hHs Complex.I).of_le
      (by norm_num)).contDiffAt)
    (fun z _ ↦ (hu.of_le (by norm_num)).contDiffAt) hM hO hOne (subset_univ O) hW
    hD.isClosed_range hD.finite_coker

end SymplecticForm

end TauCeti
