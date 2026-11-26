/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Floer.PairOfPants.Sobolev.SemiFredholm
public import TauCeti.Geometry.Symplectic.Floer.Transversality.Conformal

/-!
# Hamiltonian variations on the core of the pair of pants detect the cokernel

Let `u` be a map from the pair of pants `S = ℂ ∖ {0, 1}` to a symplectic vector space `(V, ω)`,
with Floer data `(J, K_s, K_t)` that equal the pair-of-pants data far out on the ends, and let
`D_u : W^{1,2}_0(S, V) → L²(S, V)` be the realization of its linearized Floer operator for the
cylindrical metric (`TauCeti.SymplecticForm.floerConformalSobolevOperator` with the weight
`TauCeti.Floer.cylindricalWeight`). The core of the pair of pants is an inhomogeneous region: the
Hamiltonian perturbation there is free, and the transversality of the moduli spaces of pairs of
pants is achieved by varying it. This file proves that these variations detect the whole cokernel
of `D_u`: for any nonempty open set `O ⊆ S` and any neighbourhood `W` of the graph of `u` over `O`,
the range of `D_u` and the Hamiltonian variations supported in `W`
(`TauCeti.SymplecticForm.hamiltonianVariationsOn`) span a dense subspace of `L²(S, V)`
(`topologicalClosure_range_sup_span_hamiltonianVariationsOn_pairOfPants_eq_top`, in the
namespace `TauCeti.SymplecticForm`). No hypothesis is placed on `u` over `O`, which may be constant
there.

This is the case of the pair of pants of the cokernel detection of
`TauCeti.Geometry.Symplectic.Floer.Transversality.Conformal` on a connected open set with a
conformal weight. Its two inputs are that `S` is connected
(`TauCeti.Floer.isConnected_thricePuncturedSphereReal`), as the complement of two points in the
plane, and that the coefficient field of `D_u` on conformal jets is essentially bounded, which holds
once the ends of `u` converge to their asymptotic loops
(`TauCeti.SymplecticForm.memLp_floerConformalJetCoeff_pairOfPants_of_tendstoUniformlyOn`). When
`D_u` is Fredholm, the closed range of finite codimension turns density into surjectivity, with
finitely many variations
(`TauCeti.SymplecticForm.exists_finset_subset_hamiltonianVariationsOn_range_sup_span_eq_top`).

## References

* D. McDuff and D. Salamon, *J-holomorphic curves and symplectic topology*, 2nd ed., AMS
  Colloquium Publications 52, 2012, Proposition 3.2.1 and Section 8.1.
* M. Schwarz, *Cohomology operations from S¹-cobordisms in Floer homology*, PhD thesis,
  ETH Zürich (1995), on the transversality of the moduli spaces of pairs of pants.
-/

public section

open Set Function Filter Topology MeasureTheory TauCeti.ThricePuncturedSphere
open scoped ENNReal NNReal Manifold

namespace TauCeti

namespace SymplecticForm

open Floer ConformalSobolev

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]

/-- **Hamiltonian variations make the linearized operator along a pair of pants dense.** Let `H_q`
be jointly `C²` period-one Hamiltonians on the three ends of `S = ℂ ∖ {0, 1}`, and let
`(J, K_s, K_t)` be Floer data on `S`, with `J` `C²` and `K_s`, `K_t` `C³` along `u`, which far out
on each end, beyond a height `R₁`, are cylindrical, `J(φ'_q(s, t)) = J_q(t)` for `C¹` families
`J_q`, with perturbation the pair-of-pants perturbation of `H`. Let `u` be `C²` on `S`, solve the
Floer equation for these data beyond `R₁` on each end, and have loops in each positive end chart
converging uniformly on `[0, 1]` to loops `x_q` continuous on `[0, 1]`, while the slice defects
tend uniformly to zero. Then for every nonempty open set `O ⊆ S` and every neighbourhood `W` of the
graph of `u` over `O`, the range of `D_u : W^{1,2}_0(S, V) → L²(S, V)` and the Hamiltonian
variations supported in `W` span a dense subspace of `L²(S, V)`. -/
theorem topologicalClosure_range_sup_span_hamiltonianVariationsOn_pairOfPants_eq_top
    (ω : SymplecticForm V) {H : Puncture → ℝ → V → ℝ} (hH : ∀ q, Periodic (H q) 1)
    (hHs : ∀ q, ContDiff ℝ 2 (uncurry (H q))) {x : Puncture → ℝ → V}
    (hx : ∀ q, ContinuousOn (x q) (Icc 0 1)) {J : ℝ × ℝ → V → AlmostComplexStructure V}
    {Je : Puncture → ℝ → V → AlmostComplexStructure V} {R₁ : ℝ}
    (hJe : ∀ q, ContDiff ℝ 1 fun p : ℝ × V ↦ (Je q p.1 p.2).toLinearMap.toContinuousLinearMap)
    (hJeq : ∀ q (ζ : ℝ × ℝ), R₁ ≤ ζ.1 → J (positiveEndChart q ζ) = Je q ζ.2)
    {Ks Kt : ℝ × ℝ → V → ℝ}
    (hK : ∀ q, ∀ z ∈ thricePuncturedSphereReal, R₁ ≤ (positiveEndCoord q z).1 →
      Ks z = (fun x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x 1) ∧
        Kt z = fun x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x Complex.I)
    {u : ℝ × ℝ → V}
    (hJ : ∀ z ∈ thricePuncturedSphereReal, ContDiffAt ℝ 2
      (fun p : (ℝ × ℝ) × V ↦ (J p.1 p.2).toLinearMap.toContinuousLinearMap) (z, u z))
    (hKs : ∀ z ∈ thricePuncturedSphereReal, ContDiffAt ℝ 3 (uncurry Ks) (z, u z))
    (hKt : ∀ z ∈ thricePuncturedSphereReal, ContDiffAt ℝ 3 (uncurry Kt) (z, u z))
    (hu : ∀ z ∈ thricePuncturedSphereReal, ContDiffAt ℝ 2 u z)
    (hF : ∀ q, ∀ z ∈ thricePuncturedSphereReal, R₁ ≤ (positiveEndCoord q z).1 →
      IsComplexLinearMap (AlmostComplexStructure.product ℝ) (J z (u z))
        (ω.perturbedFDeriv Ks Kt u z : ℝ × ℝ →ₗ[ℝ] V))
    (hux : ∀ q, TendstoUniformlyOn (fun s t ↦ u (positiveEndChart q (s, t))) (x q) atTop
      (Icc 0 1))
    (hδ : ∀ q, TendstoUniformlyOn (fun s t ↦ sliceDefect
      (fun t ↦ ω.hamiltonianVectorField (positiveEndHamiltonian H q t)) (u ∘ positiveEndChart q)
        (s, t)) 0 atTop (Icc 0 1))
    {O : Set (ℝ × ℝ)} (hO : IsOpen O) (hOne : O.Nonempty) (hOS : O ⊆ thricePuncturedSphereReal)
    {W : Set ((ℝ × ℝ) × V)} (hW : ∀ z ∈ O, W ∈ 𝓝 (z, u z)) :
    ((ω.floerConformalSobolevOperator thricePuncturedSphereReal cylindricalWeight
        (fun z y ↦ (J z y).toLinearMap.toContinuousLinearMap) Ks Kt u).range ⊔
      Submodule.span ℝ (ω.hamiltonianVariationsOn thricePuncturedSphereReal u W)).topologicalClosure
      = ⊤ :=
  topologicalClosure_range_floerConformalSobolevOperator_sup_span_hamiltonianVariationsOn_eq_top
    isWeight_cylindricalWeight isConnected_thricePuncturedSphereReal.isPreconnected hJ
    (fun z _ ↦ ContinuousLinearMap.ext fun v ↦ by simp) hKs hKt hu
    (ω.memLp_floerConformalJetCoeff_pairOfPants_of_tendstoUniformlyOn hH hHs hx hJe hJeq hK
      (fun z hz ↦ (hJ z hz).of_le one_le_two) (fun z hz ↦ (hKs z hz).of_le (by norm_num))
      (fun z hz ↦ (hKt z hz).of_le (by norm_num)) (fun z hz ↦ (hu z hz).of_le one_le_two) hF hux
      hδ)
    hO hOne hOS hW

end SymplecticForm

end TauCeti
