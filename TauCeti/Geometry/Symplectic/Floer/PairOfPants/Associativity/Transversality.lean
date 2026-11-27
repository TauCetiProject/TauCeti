/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Floer.PairOfPants.Associativity.SemiFredholm
public import TauCeti.Geometry.Symplectic.Floer.PairOfPants.MovingEnds.Transversality

/-!
# Hamiltonian variations along the associativity family detect the cokernel

The associativity of the pair-of-pants product compares the two compositions `(x₁ x₂) x₃` and
`x₁ (x₂ x₃)` through the one-parameter family of Floer data
`K_τ = TauCeti.Floer.associativityPerturbation H Hout G G' L τ`, `τ ∈ ℝ`, on spheres with three
moving input ends, with centers `c_τ = TauCeti.Floer.associativityCenter` and scales
`TauCeti.Floer.associativityScale` of plumbing factor `e^{-2πL} / 4`: the datum `Σ_τ` of the moving
input ends, plus the neck data of the two compositions switched on for `τ < 0` and for `τ > 1`. The
moduli spaces of this family are made regular by varying the perturbation on the core of the
sphere, where it is free.

This file proves that these variations detect the whole cokernel of the linearized operator
`D_u : W^{1,2}_0 → L²` of `K_τ` at every member `τ` of the family and every neck length `L > 4`:
for any nonempty open set `O` of the sphere minus the centers and any neighbourhood `W` of the graph
of `u` over `O`, the range of `D_u` and the Hamiltonian variations supported in `W`
(`TauCeti.SymplecticForm.hamiltonianVariationsOn`) span a dense subspace of `L²`
(`topologicalClosure_range_sup_span_hamiltonianVariationsOn_associativityPerturbation_eq_top`, in
the namespace `TauCeti.SymplecticForm`). No hypothesis is placed on `u` over `O`, which may be
constant there, or may meet the necks.

On the part `s > 0` of every input end and the part `s ≥ 1` of the output end `K_τ` is `Σ_τ`
(`TauCeti.Floer.associativityPerturbation_realChart_eq`,
`TauCeti.Floer.associativityPerturbation_positiveEndChart_inf_eq`), and `K_τ` is smooth off the
centers (`TauCeti.Floer.contDiffAt_uncurry_associativityPerturbation`). So this is the case for
Floer data equal to `Σ_τ` on the ends of the theorem on spheres with moving input ends,
`topologicalClosure_range_sup_span_hamiltonianVariationsOn_eq_top_of_movingEnds` in the namespace
`TauCeti.SymplecticForm`. Once `D_u` is known to have range of finite
codimension, its closed range
(`TauCeti.SymplecticForm.isClosed_range_floerConformalSobolevOperator_associativityPerturbation`)
turns this density into surjectivity with finitely many variations, by
`TauCeti.SymplecticForm.exists_finset_subset_hamiltonianVariationsOn_range_sup_span_eq_top`.

## References

* D. McDuff and D. Salamon, *J-holomorphic curves and symplectic topology*, 2nd ed., AMS
  Colloquium Publications 52, 2012, Proposition 3.2.1 and Section 8.1.
* M. Schwarz, *Cohomology operations from S¹-cobordisms in Floer homology*, PhD thesis,
  ETH Zürich (1995), on the transversality of the moduli spaces of the pair-of-pants product and
  the associativity of the product through families of four-punctured spheres.
-/

public section

open Filter Function Set MeasureTheory TauCeti.ThricePuncturedSphere
  TauCeti.ThricePuncturedSphere.Puncture
open scoped Real Topology
open TauCeti.Complex (realChart)

namespace TauCeti.SymplecticForm

open Floer

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]

/-- **Hamiltonian variations make the linearized operator along the associativity family dense.**
Let the Hamiltonians `H i`, `Hout`, `G` and `G'` be jointly `C³` of period one, let `L > 4`, and
let `K_τ` be the associativity family `TauCeti.Floer.associativityPerturbation H Hout G G' L τ` at
a parameter `τ`, a datum on the sphere with the input ends of centers `c i` and scales `a i` of the
associativity path of plumbing factor `e^{-2πL} / 4` at `τ`. Let `J` be a `C¹` family `J_e i (t)`
beyond `s = 2` in the chart `ψ_i = realChart (z ↦ c i + a i φ₀(z))` of each input end and
`J_out (t)` beyond `s = 2` in the positive end chart `φ'_∞` of the output end, let `u` and `J`
along `u` be `C²` on the sphere minus the centers, and let `u` solve the Floer equation of `K_τ`
beyond `s = 2` on each end, with loops converging uniformly to loops continuous on `[0, 1]` and
slice defects tending uniformly to zero. Then for every nonempty open set `O` of the sphere minus
the centers and every neighbourhood `W` of the graph of `u` over `O`, the range of the linearized
operator `D_u : W^{1,2}_0 → L²` of `K_τ` for the weight `TauCeti.Floer.movingEndsWeight c` and the
Hamiltonian variations supported in `W` span a dense subspace of `L²`. -/
theorem topologicalClosure_range_sup_span_hamiltonianVariationsOn_associativityPerturbation_eq_top
    (ω : SymplecticForm V) {H : Fin 3 → ℝ → V → ℝ} {Hout G G' : ℝ → V → ℝ}
    (hH : ∀ i, Periodic (H i) 1) (hHs : ∀ i, ContDiff ℝ 3 (uncurry (H i)))
    (hHout : Periodic Hout 1) (hHouts : ContDiff ℝ 3 (uncurry Hout)) (hG : Periodic G 1)
    (hGs : ContDiff ℝ 3 (uncurry G)) (hG' : Periodic G' 1) (hG's : ContDiff ℝ 3 (uncurry G'))
    {L : ℝ} (hL : 4 < L) (τ : ℝ) {x : Fin 3 → ℝ → V} (hx : ∀ i, ContinuousOn (x i) (Icc 0 1))
    {Je : Fin 3 → ℝ → V → AlmostComplexStructure V}
    (hJe : ∀ i, ContDiff ℝ 1 fun p : ℝ × V ↦ (Je i p.1 p.2).toLinearMap.toContinuousLinearMap)
    {xout : ℝ → V} (hxout : ContinuousOn xout (Icc 0 1)) {Jout : ℝ → V → AlmostComplexStructure V}
    (hJout : ContDiff ℝ 1 fun p : ℝ × V ↦ (Jout p.1 p.2).toLinearMap.toContinuousLinearMap)
    {J : ℝ × ℝ → V → AlmostComplexStructure V}
    (hJeq : ∀ i (ζ : ℝ × ℝ), 2 < ζ.1 →
      J (realChart (fun z ↦ associativityCenter (Real.exp (-(2 * π * L)) / 4) τ i +
        associativityScale (Real.exp (-(2 * π * L)) / 4) τ i * zero.cylindricalEndLift z) ζ) =
        Je i ζ.2)
    (hJoutq : ∀ ζ : ℝ × ℝ, 2 < ζ.1 → J (positiveEndChart inf ζ) = Jout ζ.2) {u : ℝ × ℝ → V}
    (hJ : ∀ z : ℝ × ℝ, (∀ i, Complex.equivRealProdCLM.symm z ≠
        associativityCenter (Real.exp (-(2 * π * L)) / 4) τ i) → ContDiffAt ℝ 2
      (fun p : (ℝ × ℝ) × V ↦ (J p.1 p.2).toLinearMap.toContinuousLinearMap) (z, u z))
    (hu : ∀ z : ℝ × ℝ, (∀ i, Complex.equivRealProdCLM.symm z ≠
      associativityCenter (Real.exp (-(2 * π * L)) / 4) τ i) → ContDiffAt ℝ 2 u z)
    (hF : ∀ i (ζ : ℝ × ℝ), 2 < ζ.1 →
      IsComplexLinearMap (AlmostComplexStructure.product ℝ)
        (J (realChart (fun z ↦ associativityCenter (Real.exp (-(2 * π * L)) / 4) τ i +
        associativityScale (Real.exp (-(2 * π * L)) / 4) τ i * zero.cylindricalEndLift z) ζ)
          (u (realChart (fun z ↦ associativityCenter (Real.exp (-(2 * π * L)) / 4) τ i +
        associativityScale (Real.exp (-(2 * π * L)) / 4) τ i * zero.cylindricalEndLift z) ζ)))
        (ω.perturbedFDeriv
          (fun z x ↦ associativityPerturbation H Hout G G' L τ (Complex.equivRealProdCLM.symm z) x
            1)
          (fun z x ↦ associativityPerturbation H Hout G G' L τ (Complex.equivRealProdCLM.symm z) x
            Complex.I) u
          (realChart (fun z ↦ associativityCenter (Real.exp (-(2 * π * L)) / 4) τ i +
        associativityScale (Real.exp (-(2 * π * L)) / 4) τ i * zero.cylindricalEndLift z) ζ) :
          ℝ × ℝ →ₗ[ℝ] V))
    (hFout : ∀ ζ : ℝ × ℝ, 2 < ζ.1 → IsComplexLinearMap (AlmostComplexStructure.product ℝ)
      (J (positiveEndChart inf ζ) (u (positiveEndChart inf ζ)))
      (ω.perturbedFDeriv
        (fun z x ↦ associativityPerturbation H Hout G G' L τ (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ associativityPerturbation H Hout G G' L τ (Complex.equivRealProdCLM.symm z) x
          Complex.I) u (positiveEndChart inf ζ) : ℝ × ℝ →ₗ[ℝ] V))
    (hux : ∀ i, TendstoUniformlyOn
      (fun s t ↦ u (realChart (fun z ↦ associativityCenter (Real.exp (-(2 * π * L)) / 4) τ i +
        associativityScale (Real.exp (-(2 * π * L)) / 4) τ i * zero.cylindricalEndLift z) (s, t)))
      (x i) atTop (Icc 0 1))
    (hδ : ∀ i, TendstoUniformlyOn (fun s t ↦ sliceDefect
      (fun t ↦ ω.hamiltonianVectorField (H i t))
      (u ∘ realChart fun z ↦ associativityCenter (Real.exp (-(2 * π * L)) / 4) τ i +
        associativityScale (Real.exp (-(2 * π * L)) / 4) τ i * zero.cylindricalEndLift z) (s, t))
      0 atTop (Icc 0 1))
    (huxout : TendstoUniformlyOn (fun s t ↦ u (positiveEndChart inf (s, t))) xout atTop
      (Icc 0 1))
    (hδout : TendstoUniformlyOn (fun s t ↦ sliceDefect
      (fun t ↦ ω.hamiltonianVectorField fun y ↦ -Hout (-t) y) (u ∘ positiveEndChart inf) (s, t))
      0 atTop (Icc 0 1))
    {O : Set (ℝ × ℝ)} (hO : IsOpen O) (hOne : O.Nonempty)
    (hOS : O ⊆ {z | ∀ i, Complex.equivRealProdCLM.symm z ≠
      associativityCenter (Real.exp (-(2 * π * L)) / 4) τ i})
    {W : Set ((ℝ × ℝ) × V)} (hW : ∀ z ∈ O, W ∈ 𝓝 (z, u z)) :
    ((ω.floerConformalSobolevOperator
        {z | ∀ i, Complex.equivRealProdCLM.symm z ≠
          associativityCenter (Real.exp (-(2 * π * L)) / 4) τ i}
        (movingEndsWeight (associativityCenter (Real.exp (-(2 * π * L)) / 4) τ))
        (fun z y ↦ (J z y).toLinearMap.toContinuousLinearMap)
        (fun z x ↦ associativityPerturbation H Hout G G' L τ (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ associativityPerturbation H Hout G G' L τ (Complex.equivRealProdCLM.symm z) x
          Complex.I) u).range ⊔
      Submodule.span ℝ (ω.hamiltonianVariationsOn
        {z | ∀ i, Complex.equivRealProdCLM.symm z ≠
          associativityCenter (Real.exp (-(2 * π * L)) / 4) τ i} u W)).topologicalClosure =
      ⊤ := by
  have hexp : Real.exp (-(2 * π * L)) ≤ 1 := Real.exp_le_one_iff.2 (by nlinarith [Real.pi_pos])
  -- Far out on the ends the family is the datum of the moving input ends; on the core only its
  -- smoothness off the centers is used.
  exact topologicalClosure_range_sup_span_hamiltonianVariationsOn_eq_top_of_movingEnds ω hH
    (fun i ↦ (hHs i).of_le (by norm_num)) hHout (hHouts.of_le (by norm_num))
    (associativityScale_ne_zero (by positivity) τ)
    (pairwise_add_le_norm_associativityCenter_sub (by positivity) (by linarith) τ)
    (norm_associativityCenter_add_le (by positivity) (by linarith) τ) hx hJe hxout hJout hJeq
    hJoutq
    (fun i ζ hζ ↦ by
      rw [associativityPerturbation_realChart_eq (G := G) (G' := G') (L := L) (by linarith) hH i
        (by linarith)]
      exact ⟨rfl, rfl⟩)
    (fun ζ hζ ↦ by
      rw [associativityPerturbation_positiveEndChart_inf_eq (H := H) (G := G) (G' := G') (L := L)
        (by linarith) hHout (by linarith)]
      exact ⟨rfl, rfl⟩) hJ
    (fun z hz ↦ contDiffAt_uncurry_associativityPerturbation hH hHs hHout hHouts hG hGs hG' hG's
      hL hz (u z) 1)
    (fun z hz ↦ contDiffAt_uncurry_associativityPerturbation hH hHs hHout hHouts hG hGs hG' hG's
      hL hz (u z) Complex.I) hu hF hFout hux hδ huxout hδout hO hOne hOS hW

end TauCeti.SymplecticForm
