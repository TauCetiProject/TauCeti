/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Floer.PairOfPants.LeftCapping.Sobolev
public import TauCeti.Geometry.Symplectic.Floer.Transversality.Conformal
import TauCeti.Analysis.Complex.EquivRealProd

/-!
# Hamiltonian variations along the input-exchange family capped at `0` detect the cokernel

The pair-of-pants product is unital on the left because gluing the negative PSS plane of `H_0`
into the input at `0` of the pair of pants gives a cylinder whose counts compare with continuation
maps. The comparison counts the members of the input-exchange family capped at `0`,
`K_c = TauCeti.Floer.cappedExchangePerturbation H L c` for `0 ≤ c ≤ 1`, on a finite-dimensional
symplectic vector space `(V, ω)`. Its domain is the capped surface `ℂ ∖ {1}`: the input end at `1`
carries `H_1`, the output end, recentred at `c`, carries `H_∞`, and the capped puncture `0` is an
interior point. Away from the two ends the perturbation of a member is free, and the moduli spaces
of the family are made regular by varying it there.

This file proves that these variations detect the whole cokernel of the linearized operator
`D_u : W^{1,2}_0(ℂ ∖ {1}, V) → L²(ℂ ∖ {1}, V)` of any member, the realization
`TauCeti.SymplecticForm.floerConformalSobolevOperator` for the cylindrical weight of the capped
surface `TauCeti.Floer.cappedCylindricalWeight`: for any nonempty open set `O ⊆ ℂ ∖ {1}` and any
neighbourhood `W` of the graph of `u` over `O`, the range of `D_u` and the Hamiltonian variations
supported in `W` (`TauCeti.SymplecticForm.hamiltonianVariationsOn`) span a dense subspace of
`L²(ℂ ∖ {1}, V)`
(`topologicalClosure_range_sup_span_hamiltonianVariationsOn_cappedExchangePerturbation_eq_top`, in
the namespace `TauCeti.SymplecticForm`).

This is the cokernel detection of `TauCeti.Geometry.Symplectic.Floer.Transversality.Conformal` on
the connected set `ℂ ∖ {1}` (`TauCeti.isConnected_setOf_equivRealProdCLM_symm_ne`), with
the essential boundedness of the coefficient field of `D_u` on conformal jets
(`TauCeti.SymplecticForm.memLp_floerConformalJetCoeff_cappedExchangePerturbation`). No hypothesis
is placed on `u` over `O`, which may be constant there; in particular `O` may contain the capped
puncture `0`. When `D_u` is Fredholm, the closed range of finite codimension turns density into
surjectivity, with finitely many variations
(`TauCeti.SymplecticForm.exists_finset_subset_hamiltonianVariationsOn_range_sup_span_eq_top`).

## References

* S. Piunikhin, D. Salamon and M. Schwarz, *Symplectic Floer–Donaldson theory and quantum
  cohomology*, in *Contact and symplectic geometry*, Publ. Newton Inst. 8 (1996), 171–200, on the
  unit of the pair-of-pants product.
* D. McDuff and D. Salamon, *J-holomorphic curves and symplectic topology*, 2nd ed., AMS
  Colloquium Publications 52, 2012, Proposition 3.2.1 and Section 8.1.
-/

public section

open Set Function Filter Topology MeasureTheory TauCeti.ThricePuncturedSphere
  TauCeti.ThricePuncturedSphere.Puncture

namespace TauCeti.SymplecticForm

open Floer

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]

/-- **Hamiltonian variations make the linearized operator along the input-exchange family capped
at `0` dense.** Let `H_q` be jointly `C³` period-one Hamiltonians, let `L > 4`, and let
`K_c = TauCeti.Floer.cappedExchangePerturbation H L c` be the member `c ∈ [0, 1]` of the
input-exchange family capped at `0`, on the capped surface `ℂ ∖ {1}`. Let `J` be a family of
almost complex structures on `ℂ ∖ {1}`, `C²` along `u`, which far out on the two ends, beyond a
height `R₁`, is a `C¹` family `J_q(t)` in the positive end chart `φ'_1` of the input end at `1` and
in the recentred end chart `c + φ'_∞` of the output end. Let `u` be `C²` on `ℂ ∖ {1}`, solve the
Floer equation for `(J, K_c)` beyond `R₁` on both ends, and have loops, read in these end charts,
converging uniformly on `[0, 1]` to loops `x_q` continuous on `[0, 1]`, while the slice defects
tend uniformly to zero. Then for every nonempty open set `O ⊆ ℂ ∖ {1}` and every neighbourhood `W`
of the graph of `u` over `O`, the range of the linearized operator
`D_u : W^{1,2}_0(ℂ ∖ {1}, V) → L²(ℂ ∖ {1}, V)` of `(J, K_c)` and the Hamiltonian variations
supported in `W` span a dense subspace of `L²(ℂ ∖ {1}, V)`. -/
theorem topologicalClosure_range_sup_span_hamiltonianVariationsOn_cappedExchangePerturbation_eq_top
    (ω : SymplecticForm V) {H : Puncture → ℝ → V → ℝ} (hH : ∀ q, Periodic (H q) 1)
    (hHs : ∀ q, ContDiff ℝ 3 (uncurry (H q))) {L c : ℝ} (hL : 4 < L) (hc₀ : 0 ≤ c) (hc₁ : c ≤ 1)
    {x : Puncture → ℝ → V} (hx : ∀ q, q ≠ zero → ContinuousOn (x q) (Icc 0 1))
    {J : ℝ × ℝ → V → AlmostComplexStructure V}
    {Je : Puncture → ℝ → V → AlmostComplexStructure V} {R₁ : ℝ}
    (hJe : ∀ q, q ≠ zero →
      ContDiff ℝ 1 fun p : ℝ × V ↦ (Je q p.1 p.2).toLinearMap.toContinuousLinearMap)
    (hJeq : ∀ ζ : ℝ × ℝ, R₁ ≤ ζ.1 → J (positiveEndChart one ζ) = Je one ζ.2)
    (hJeq_inf : ∀ ζ : ℝ × ℝ, R₁ ≤ ζ.1 → J (positiveEndChart inf ζ + (c, 0)) = Je inf ζ.2)
    {u : ℝ × ℝ → V}
    (hJ : ∀ z, Complex.equivRealProdCLM.symm z ≠ 1 → ContDiffAt ℝ 2
      (fun p : (ℝ × ℝ) × V ↦ (J p.1 p.2).toLinearMap.toContinuousLinearMap) (z, u z))
    (hu : ∀ z, Complex.equivRealProdCLM.symm z ≠ 1 → ContDiffAt ℝ 2 u z)
    (hF : ∀ z ∈ thricePuncturedSphereReal, R₁ ≤ (positiveEndCoord one z).1 →
      IsComplexLinearMap (AlmostComplexStructure.product ℝ) (J z (u z)) (ω.perturbedFDeriv
        (fun z x ↦ cappedExchangePerturbation H L c (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ cappedExchangePerturbation H L c (Complex.equivRealProdCLM.symm z) x
          Complex.I)
        u z : ℝ × ℝ →ₗ[ℝ] V))
    (hF_inf : ∀ z : ℝ × ℝ, R₁ ≤ (positiveEndCoord inf z).1 →
      IsComplexLinearMap (AlmostComplexStructure.product ℝ) (J (z + (c, 0)) (u (z + (c, 0))))
        (ω.perturbedFDeriv
          (fun z x ↦ cappedExchangePerturbation H L c (Complex.equivRealProdCLM.symm z) x 1)
          (fun z x ↦ cappedExchangePerturbation H L c (Complex.equivRealProdCLM.symm z) x
            Complex.I)
          u (z + (c, 0)) : ℝ × ℝ →ₗ[ℝ] V))
    (hux : TendstoUniformlyOn (fun s t ↦ u (positiveEndChart one (s, t))) (x one) atTop
      (Icc 0 1))
    (hux_inf : TendstoUniformlyOn (fun s t ↦ u (positiveEndChart inf (s, t) + (c, 0))) (x inf)
      atTop (Icc 0 1))
    (hδ : TendstoUniformlyOn (fun s t ↦ sliceDefect
      (fun t ↦ ω.hamiltonianVectorField (positiveEndHamiltonian H one t))
        (u ∘ positiveEndChart one) (s, t)) 0 atTop (Icc 0 1))
    (hδ_inf : TendstoUniformlyOn (fun s t ↦ sliceDefect
      (fun t ↦ ω.hamiltonianVectorField (positiveEndHamiltonian H inf t))
        (fun ζ ↦ u (positiveEndChart inf ζ + (c, 0))) (s, t)) 0 atTop (Icc 0 1))
    {O : Set (ℝ × ℝ)} (hO : IsOpen O) (hOne : O.Nonempty)
    (hOS : O ⊆ {z | Complex.equivRealProdCLM.symm z ≠ 1})
    {W : Set ((ℝ × ℝ) × V)} (hW : ∀ z ∈ O, W ∈ 𝓝 (z, u z)) :
    ((ω.floerConformalSobolevOperator {z | Complex.equivRealProdCLM.symm z ≠ 1}
        cappedCylindricalWeight (fun z y ↦ (J z y).toLinearMap.toContinuousLinearMap)
        (fun z x ↦ cappedExchangePerturbation H L c (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ cappedExchangePerturbation H L c (Complex.equivRealProdCLM.symm z) x
          Complex.I)
        u).range ⊔
      Submodule.span ℝ (ω.hamiltonianVariationsOn {z | Complex.equivRealProdCLM.symm z ≠ 1} u
        W)).topologicalClosure = ⊤ :=
  topologicalClosure_range_floerConformalSobolevOperator_sup_span_hamiltonianVariationsOn_eq_top
    isWeight_cappedCylindricalWeight (isConnected_setOf_equivRealProdCLM_symm_ne 1).isPreconnected
    hJ (fun z _ ↦ ContinuousLinearMap.ext fun v ↦ by simp)
    (fun z hz ↦ contDiffAt_uncurry_cappedExchangePerturbation hH hHs hL c hz (u z) 1)
    (fun z hz ↦ contDiffAt_uncurry_cappedExchangePerturbation hH hHs hL c hz (u z) Complex.I) hu
    (ω.memLp_floerConformalJetCoeff_cappedExchangePerturbation hH
      (fun q ↦ (hHs q).of_le (by norm_num)) hL hc₀ hc₁ hx hJe hJeq hJeq_inf
      (fun z hz ↦ (hJ z hz).of_le one_le_two) (fun z hz ↦ (hu z hz).of_le one_le_two) hF hF_inf
      hux hux_inf hδ hδ_inf)
    hO hOne hOS hW

end TauCeti.SymplecticForm
