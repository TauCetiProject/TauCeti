/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Floer.PairOfPants.MovingEnds.Sobolev
public import TauCeti.Geometry.Symplectic.Floer.Transversality.Conformal

/-!
# Hamiltonian variations on spheres with moving input ends detect the cokernel

The associativity of the pair-of-pants product is proved through a family of spheres with finitely
many moving input ends, with centers `c i` and nonzero scales `a i`, and an output end at `∞`,
carrying the Hamiltonian perturbations `K = TauCeti.Floer.puncturedSpherePerturbation c a H Hout`.
On the part `τ ∈ [0, 1]` of the associativity family this is its datum
(`TauCeti.Floer.associativityPerturbation_of_mem_Icc`); for plumbing factors `0 ≤ f ≤ 1 / 3`
the input discs along the associativity path stay disjoint
(`TauCeti.Floer.pairwise_add_le_norm_associativityCenter_sub`) and inside the disc where the
output datum vanishes (`TauCeti.Floer.norm_associativityCenter_add_le`), as the theorem below
requires. The moduli spaces of this
family are made regular by varying the perturbation on the core of the sphere, where it is free.

This file proves that these variations detect the whole cokernel of the linearized operator
`D_u : W^{1,2}_0 → L²` of the datum, the realization
`TauCeti.SymplecticForm.floerConformalSobolevOperator` on the sphere minus the centers for the
weight `TauCeti.Floer.movingEndsWeight`: for any nonempty open set `O` of the sphere minus the
centers and any neighbourhood `W` of the graph of `u` over `O`, the range of `D_u` and the
Hamiltonian variations supported in `W` (`TauCeti.SymplecticForm.hamiltonianVariationsOn`) span a
dense subspace of `L²`
(`topologicalClosure_range_sup_span_hamiltonianVariationsOn_puncturedSpherePerturbation_eq_top`,
in the namespace `TauCeti.SymplecticForm`). No hypothesis is placed on `u` over `O`, which may be
constant there.

This is the cokernel detection of `TauCeti.Geometry.Symplectic.Floer.Transversality.Conformal` on a
connected open set with a conformal weight. Its two inputs are that the sphere minus the centers,
the plane minus finitely many points, is connected, and that the coefficient field of `D_u` on
conformal jets is essentially bounded once the ends of `u` converge to their asymptotic loops
(`TauCeti.SymplecticForm.memLp_floerConformalJetCoeff_of_movingEnds`). Once `D_u` is known to have
range of finite codimension, its closed range
(`TauCeti.SymplecticForm.isClosed_range_floerConformalSobolevOperator_of_movingEnds`) turns this
density into surjectivity with finitely many variations, by
`TauCeti.SymplecticForm.exists_finset_subset_hamiltonianVariationsOn_range_sup_span_eq_top`.

## References

* D. McDuff and D. Salamon, *J-holomorphic curves and symplectic topology*, 2nd ed., AMS
  Colloquium Publications 52, 2012, Proposition 3.2.1 and Section 8.1.
* M. Schwarz, *Cohomology operations from S¹-cobordisms in Floer homology*, PhD thesis,
  ETH Zürich (1995), on the transversality of the moduli spaces of the pair-of-pants product and
  the associativity of the product through families of four-punctured spheres.
-/

public section

open Set Function Filter Topology MeasureTheory Real TauCeti.ThricePuncturedSphere
  TauCeti.ThricePuncturedSphere.Puncture
open TauCeti.Complex (realChart)

namespace TauCeti.SymplecticForm

open Floer

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  {ι : Type*} [Fintype ι] {c a : ι → ℂ} {H : ι → ℝ → V → ℝ} {Hout : ℝ → V → ℝ}

/-- **Hamiltonian variations make the linearized operator on a sphere with moving input ends
dense.** Let the discs `‖w - c i‖ < ‖a i‖ / 2` of the input ends be pairwise disjoint and lie in
the disc `‖w‖ ≤ 2 exp (2π)`, with nonzero scales, and let the Hamiltonians `H i` and `Hout` be
jointly `C³` of period one. Let `J` be a `C¹` family `J_e i (t)` beyond `s = 2` in the chart
`ψ_i = realChart (z ↦ c i + a i φ₀(z))` of each input end and `J_out (t)` beyond `s = 2` in the
positive end chart `φ'_∞` of the output end, let `u` and `J` along `u` be `C²` on the sphere minus
the centers, and let `u` solve the Floer equation of the datum
`TauCeti.Floer.puncturedSpherePerturbation c a H Hout` beyond `s = 2` on each end, with loops
converging uniformly to loops continuous on `[0, 1]` and slice defects tending uniformly to zero.
Then for every nonempty open set `O` of the sphere minus the centers and every neighbourhood `W` of
the graph of `u` over `O`, the range of the linearized operator `D_u : W^{1,2}_0 → L²` for the
weight `TauCeti.Floer.movingEndsWeight c` and the Hamiltonian variations supported in `W` span a
dense subspace of `L²`. -/
theorem topologicalClosure_range_sup_span_hamiltonianVariationsOn_puncturedSpherePerturbation_eq_top
    (ω : SymplecticForm V) (hH : ∀ i, Periodic (H i) 1) (hHs : ∀ i, ContDiff ℝ 3 (uncurry (H i)))
    (hHout : Periodic Hout 1) (hHouts : ContDiff ℝ 3 (uncurry Hout)) (ha : ∀ i, a i ≠ 0)
    (hsep : Pairwise fun i j ↦ ‖a i‖ / 2 + ‖a j‖ / 2 ≤ ‖c i - c j‖)
    (hout : ∀ i, ‖c i‖ + ‖a i‖ / 2 ≤ 2 * Real.exp (2 * π)) {x : ι → ℝ → V}
    (hx : ∀ i, ContinuousOn (x i) (Icc 0 1)) {Je : ι → ℝ → V → AlmostComplexStructure V}
    (hJe : ∀ i, ContDiff ℝ 1 fun p : ℝ × V ↦ (Je i p.1 p.2).toLinearMap.toContinuousLinearMap)
    {xout : ℝ → V} (hxout : ContinuousOn xout (Icc 0 1)) {Jout : ℝ → V → AlmostComplexStructure V}
    (hJout : ContDiff ℝ 1 fun p : ℝ × V ↦ (Jout p.1 p.2).toLinearMap.toContinuousLinearMap)
    {J : ℝ × ℝ → V → AlmostComplexStructure V}
    (hJeq : ∀ i (ζ : ℝ × ℝ), 2 < ζ.1 →
      J (realChart (fun z ↦ c i + a i * zero.cylindricalEndLift z) ζ) = Je i ζ.2)
    (hJoutq : ∀ ζ : ℝ × ℝ, 2 < ζ.1 → J (positiveEndChart inf ζ) = Jout ζ.2) {u : ℝ × ℝ → V}
    (hJ : ∀ z : ℝ × ℝ, (∀ i, Complex.equivRealProdCLM.symm z ≠ c i) → ContDiffAt ℝ 2
      (fun p : (ℝ × ℝ) × V ↦ (J p.1 p.2).toLinearMap.toContinuousLinearMap) (z, u z))
    (hu : ∀ z : ℝ × ℝ, (∀ i, Complex.equivRealProdCLM.symm z ≠ c i) → ContDiffAt ℝ 2 u z)
    (hF : ∀ i (ζ : ℝ × ℝ), 2 < ζ.1 → IsComplexLinearMap (AlmostComplexStructure.product ℝ)
      (J (realChart (fun z ↦ c i + a i * zero.cylindricalEndLift z) ζ)
        (u (realChart (fun z ↦ c i + a i * zero.cylindricalEndLift z) ζ)))
      (ω.perturbedFDeriv
        (fun z x ↦ puncturedSpherePerturbation c a H Hout (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ puncturedSpherePerturbation c a H Hout (Complex.equivRealProdCLM.symm z) x
          Complex.I) u
        (realChart (fun z ↦ c i + a i * zero.cylindricalEndLift z) ζ) : ℝ × ℝ →ₗ[ℝ] V))
    (hFout : ∀ ζ : ℝ × ℝ, 2 < ζ.1 → IsComplexLinearMap (AlmostComplexStructure.product ℝ)
      (J (positiveEndChart inf ζ) (u (positiveEndChart inf ζ)))
      (ω.perturbedFDeriv
        (fun z x ↦ puncturedSpherePerturbation c a H Hout (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ puncturedSpherePerturbation c a H Hout (Complex.equivRealProdCLM.symm z) x
          Complex.I) u (positiveEndChart inf ζ) : ℝ × ℝ →ₗ[ℝ] V))
    (hux : ∀ i, TendstoUniformlyOn
      (fun s t ↦ u (realChart (fun z ↦ c i + a i * zero.cylindricalEndLift z) (s, t))) (x i)
      atTop (Icc 0 1))
    (hδ : ∀ i, TendstoUniformlyOn (fun s t ↦ sliceDefect
      (fun t ↦ ω.hamiltonianVectorField (H i t))
      (u ∘ realChart fun z ↦ c i + a i * zero.cylindricalEndLift z) (s, t)) 0 atTop (Icc 0 1))
    (huxout : TendstoUniformlyOn (fun s t ↦ u (positiveEndChart inf (s, t))) xout atTop
      (Icc 0 1))
    (hδout : TendstoUniformlyOn (fun s t ↦ sliceDefect
      (fun t ↦ ω.hamiltonianVectorField fun y ↦ -Hout (-t) y) (u ∘ positiveEndChart inf) (s, t))
      0 atTop (Icc 0 1))
    {O : Set (ℝ × ℝ)} (hO : IsOpen O) (hOne : O.Nonempty)
    (hOS : O ⊆ {z | ∀ i, Complex.equivRealProdCLM.symm z ≠ c i})
    {W : Set ((ℝ × ℝ) × V)} (hW : ∀ z ∈ O, W ∈ 𝓝 (z, u z)) :
    ((ω.floerConformalSobolevOperator {z | ∀ i, Complex.equivRealProdCLM.symm z ≠ c i}
        (movingEndsWeight c) (fun z y ↦ (J z y).toLinearMap.toContinuousLinearMap)
        (fun z x ↦ puncturedSpherePerturbation c a H Hout (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ puncturedSpherePerturbation c a H Hout (Complex.equivRealProdCLM.symm z) x
          Complex.I) u).range ⊔
      Submodule.span ℝ (ω.hamiltonianVariationsOn {z | ∀ i, Complex.equivRealProdCLM.symm z ≠ c i}
        u W)).topologicalClosure = ⊤ := by
  -- The sphere minus the centers is the plane minus finitely many points, so it is connected.
  have hS : {z : ℝ × ℝ | ∀ i, Complex.equivRealProdCLM.symm z ≠ c i} =
      (range fun i ↦ Complex.equivRealProdCLM (c i))ᶜ := by
    ext z
    simp only [mem_ofPred_eq, mem_compl_iff, mem_range, not_exists]
    exact forall_congr' fun i ↦ not_congr (by rw [ContinuousLinearEquiv.symm_apply_eq, eq_comm])
  have hconn : IsConnected {z : ℝ × ℝ | ∀ i, Complex.equivRealProdCLM.symm z ≠ c i} := by
    rw [hS]
    refine (finite_range _).countable.isConnected_compl_of_one_lt_rank ?_
    rw [rank_prod', Module.rank_self, one_add_one_eq_two]
    exact Cardinal.one_lt_two
  exact
    topologicalClosure_range_floerConformalSobolevOperator_sup_span_hamiltonianVariationsOn_eq_top
      (isWeight_movingEndsWeight c) hconn.isPreconnected hJ
      (fun z _ ↦ ContinuousLinearMap.ext fun v ↦ by simp)
      (fun z hz ↦ contDiffAt_uncurry_puncturedSpherePerturbation hH hHs hHout hHouts ha hz _ 1)
      (fun z hz ↦
        contDiffAt_uncurry_puncturedSpherePerturbation hH hHs hHout hHouts ha hz _ Complex.I) hu
      (ω.memLp_floerConformalJetCoeff_of_movingEnds hH (fun i ↦ (hHs i).of_le (by norm_num))
        hHout (hHouts.of_le (by norm_num)) ha hsep hout hx hJe hxout hJout hJeq hJoutq
        (fun z hz ↦ (hJ z hz).of_le one_le_two) (fun z hz ↦ (hu z hz).of_le one_le_two) hF hFout
        hux hδ huxout hδout)
      hO hOne hOS hW

end TauCeti.SymplecticForm
