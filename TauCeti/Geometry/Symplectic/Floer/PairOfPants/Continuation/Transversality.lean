/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Floer.PairOfPants.Continuation.SemiFredholm
public import TauCeti.Geometry.Symplectic.Floer.PairOfPants.Sobolev.Transversality

/-!
# Hamiltonian variations along a pair of pants with continuation necks detect the cokernel

Pair-of-pants products for two choices of end Hamiltonians are compared by gluing continuation
cylinders to the ends of the pair of pants `S = ℂ ∖ {0, 1}`. The datum of this gluing,
`TauCeti.Floer.pairOfPantsContinuationPerturbation G H L`, is the pair-of-pants datum of the inner
Hamiltonians `G` on the pants side of necks placed at the positions `L_q`, a continuation datum from
`G_q` to `H_q` along each neck, and `H_q(t) dt` beyond it. Its solutions, for neck positions moving
along a path, form the one-parameter families of pairs of pants whose ends compare continuation maps
with pair-of-pants products. Their moduli spaces are made regular by varying the perturbation on
the core of the pair of pants, where it is free.

This file proves that these variations detect the whole cokernel of the linearized operator
`D_u : W^{1,2}_0(S, V) → L²(S, V)` of the datum for any neck positions, the realization
`TauCeti.SymplecticForm.floerConformalSobolevOperator` for the cylindrical weight
`TauCeti.Floer.cylindricalWeight`: for any nonempty open set `O ⊆ S` and any neighbourhood `W` of
the graph of `u` over `O`, the range of `D_u` and the Hamiltonian variations supported in `W`
(`TauCeti.SymplecticForm.hamiltonianVariationsOn`) span a dense subspace of `L²(S, V)`.

Beyond the height `2 + ∑_q |L_q|` on each end, past every neck and collar, the datum is the
pair-of-pants datum of `H`
(`TauCeti.Floer.pairOfPantsContinuationPerturbation_components_eq`), so this is the
cokernel detection for data that agree with the pair-of-pants data far out on the ends
(`topologicalClosure_range_sup_span_hamiltonianVariationsOn_pairOfPants_eq_top`, in the namespace
`TauCeti.SymplecticForm`). No hypothesis is placed on `u` over `O`, which may be constant there,
and `O` may lie in a neck.

On a complex inner product space with `ω = Im ⟪·, ·⟫`, where `D_u` is Fredholm
(`TauCeti.SymplecticForm.isFredholm_floerConformalSobolevOperator_pairOfPants`), its closed range
of finite codimension turns density into surjectivity. Finitely many Hamiltonian variations
`y₁, …, y_N` supported in `W` make the universal operator `(ξ, a) ↦ D_u ξ + ∑ aᵢ yᵢ` onto
(`exists_surjective_floerConformalSobolevOperator_coprod_pairOfPantsContinuationPerturbation`, in
the namespace `TauCeti.SymplecticForm`), an instance of the same statement for the pair of pants
(`TauCeti.SymplecticForm.exists_surjective_floerConformalSobolevOperator_coprod_pairOfPants`). If
`yᵢ` is the class of `-X_{δKᵢ}(u)`, this operator is the linearization at `(u, 0)` of the Floer
operator of the perturbations `K_s + ∑ aᵢ δKᵢ`.

## References

* D. McDuff and D. Salamon, *J-holomorphic curves and symplectic topology*, 2nd ed., AMS
  Colloquium Publications 52, 2012, Proposition 3.2.1 and Section 8.1.
* M. Schwarz, *Cohomology operations from S¹-cobordisms in Floer homology*, PhD thesis,
  ETH Zürich (1995), on the transversality of the moduli spaces of pairs of pants and their
  compatibility with continuation maps.
-/

public section

open Set Function Filter Topology MeasureTheory TauCeti.ThricePuncturedSphere
open scoped NNReal Manifold

namespace TauCeti.SymplecticForm

open Floer

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]

/-- **Hamiltonian variations make the linearized operator along a pair of pants with continuation
necks dense.** Let `G_q` and `H_q` be jointly `C³` period-one Hamiltonians on the three ends of
`S = ℂ ∖ {0, 1}`, the inner and outer Hamiltonians of the pair-of-pants perturbation with
continuation necks at the positions `L_q` (`TauCeti.Floer.pairOfPantsContinuationPerturbation G H
L`). Let `J` be a family of almost complex structures on `S`, `C²` along `u`, which far out on each
end, beyond a height `R₁`, is a `C¹` family `J_q(t)` in the positive end chart `φ'_q`. Let `u` be
`C²` on `S`, solve the Floer equation for this datum beyond `R₁` on each end, and have loops in each
positive end chart converging uniformly on `[0, 1]` to loops `x_q` continuous on `[0, 1]`, while
the slice defects for the outer Hamiltonians tend uniformly to zero. Then for every nonempty open
set `O ⊆ S` and every neighbourhood `W` of the graph of `u` over `O`, the range of the linearized
operator `D_u : W^{1,2}_0(S, V) → L²(S, V)` of the datum and the Hamiltonian variations supported
in `W` span a dense subspace of `L²(S, V)`. -/
theorem
topologicalClosure_range_sup_span_hamiltonianVariationsOn_pairOfPantsContinuationPerturbation_eq_top
    (ω : SymplecticForm V) {G H : Puncture → ℝ → V → ℝ} (hG : ∀ q, Periodic (G q) 1)
    (hH : ∀ q, Periodic (H q) 1) (hGs : ∀ q, ContDiff ℝ 3 (uncurry (G q)))
    (hHs : ∀ q, ContDiff ℝ 3 (uncurry (H q))) (L : Puncture → ℝ) {x : Puncture → ℝ → V}
    (hx : ∀ q, ContinuousOn (x q) (Icc 0 1)) {J : ℝ × ℝ → V → AlmostComplexStructure V}
    {Je : Puncture → ℝ → V → AlmostComplexStructure V} {R₁ : ℝ}
    (hJe : ∀ q, ContDiff ℝ 1 fun p : ℝ × V ↦ (Je q p.1 p.2).toLinearMap.toContinuousLinearMap)
    (hJeq : ∀ q (ζ : ℝ × ℝ), R₁ ≤ ζ.1 → J (positiveEndChart q ζ) = Je q ζ.2)
    {u : ℝ × ℝ → V}
    (hJ : ∀ z ∈ thricePuncturedSphereReal, ContDiffAt ℝ 2
      (fun p : (ℝ × ℝ) × V ↦ (J p.1 p.2).toLinearMap.toContinuousLinearMap) (z, u z))
    (hu : ∀ z ∈ thricePuncturedSphereReal, ContDiffAt ℝ 2 u z)
    (hF : ∀ q, ∀ z ∈ thricePuncturedSphereReal, R₁ ≤ (positiveEndCoord q z).1 →
      IsComplexLinearMap (AlmostComplexStructure.product ℝ) (J z (u z)) (ω.perturbedFDeriv
        (fun z x ↦
          pairOfPantsContinuationPerturbation G H L (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦
          pairOfPantsContinuationPerturbation G H L (Complex.equivRealProdCLM.symm z) x
            Complex.I) u z : ℝ × ℝ →ₗ[ℝ] V))
    (hux : ∀ q, TendstoUniformlyOn (fun s t ↦ u (positiveEndChart q (s, t))) (x q) atTop
      (Icc 0 1))
    (hδ : ∀ q, TendstoUniformlyOn (fun s t ↦ sliceDefect
      (fun t ↦ ω.hamiltonianVectorField (positiveEndHamiltonian H q t)) (u ∘ positiveEndChart q)
        (s, t)) 0 atTop (Icc 0 1))
    {O : Set (ℝ × ℝ)} (hO : IsOpen O) (hOne : O.Nonempty) (hOS : O ⊆ thricePuncturedSphereReal)
    {W : Set ((ℝ × ℝ) × V)} (hW : ∀ z ∈ O, W ∈ 𝓝 (z, u z)) :
    ((ω.floerConformalSobolevOperator thricePuncturedSphereReal cylindricalWeight
        (fun z y ↦ (J z y).toLinearMap.toContinuousLinearMap)
        (fun z x ↦
          pairOfPantsContinuationPerturbation G H L (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦
          pairOfPantsContinuationPerturbation G H L (Complex.equivRealProdCLM.symm z) x Complex.I)
        u).range ⊔
      Submodule.span ℝ (ω.hamiltonianVariationsOn thricePuncturedSphereReal u W)).topologicalClosure
      = ⊤ :=
  -- Beyond the height `max R₁ (2 + ∑_q |L_q|)` on every end the datum is the pair-of-pants datum
  -- of `H`.
  ω.topologicalClosure_range_sup_span_hamiltonianVariationsOn_pairOfPants_eq_top hH
    (fun q ↦ (hHs q).of_le (by norm_num)) hx hJe (R₁ := max R₁ (2 + ∑ r, |L r|))
    (fun q ζ hζ ↦ hJeq q ζ ((le_max_left _ _).trans hζ))
    (fun q _ _ hz ↦ pairOfPantsContinuationPerturbation_components_eq (le_max_right _ _) q hz) hJ
    (fun z hz ↦ contDiffAt_uncurry_pairOfPantsContinuationPerturbation hG hH hGs hHs L hz (u z) 1)
    (fun z hz ↦
      contDiffAt_uncurry_pairOfPantsContinuationPerturbation hG hH hGs hHs L hz (u z) Complex.I)
    hu (fun q z hz hR ↦ hF q z hz ((le_max_left _ _).trans hR)) hux hδ hO hOne hOS hW

section Surjective

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] [FiniteDimensional ℂ F]

/-- **The universal linearized operator along a pair of pants with continuation necks is onto.**
Let `F` be a finite-dimensional complex inner product space whose symplectic form `ω` is
`Im ⟪·, ·⟫`. Let `G_q` and `H_q` be jointly `C³` period-one Hamiltonians on the three ends of
`S = ℂ ∖ {0, 1}`, the inner and outer Hamiltonians of the pair-of-pants perturbation with
continuation necks at the positions `L_q` (`TauCeti.Floer.pairOfPantsContinuationPerturbation G H
L`), such that the positive end Hamiltonians of `H` have globally Lipschitz suspended vector fields
and periodic orbits `x_q` starting at nondegenerate fixed points of the time-one maps. Let `J` be a
family of almost complex structures on `S`, `C²` along `u`, which far out on each end, beyond a
height `R₁`, is a `C¹` family `J_q(t)` in the positive end chart `φ'_q`, compatible with `ω` and
`C²` in `t` along `x_q`. Let `u` be `C²` on `S`, with `J(z, u z)` compatible with `ω`, solve the
Floer equation for this datum beyond `R₁` on each end, and have loops in each positive end chart
converging uniformly to `x_q` while the slice defects for the outer Hamiltonians tend uniformly to
zero.

Then for every nonempty open set `O ⊆ S` and every neighbourhood `W` of the graph of `u` over `O`,
there are finitely many Hamiltonian variations `y₁, …, y_N` supported in `W` such that the operator
`(ξ, a) ↦ D_u ξ + ∑ aᵢ yᵢ` from `W^{1,2}_0(S, F) × ℝᴺ` to `L²(S, F)` is onto, where `D_u` is the
linearized operator of the datum with continuation necks. -/
theorem exists_surjective_floerConformalSobolevOperator_coprod_pairOfPantsContinuationPerturbation
    (ω : SymplecticForm F) (hω : ∀ v w, ω v w = (inner ℂ v w).im) {G H : Puncture → ℝ → F → ℝ}
    (hG : ∀ q, Periodic (G q) 1) (hH : ∀ q, Periodic (H q) 1)
    (hGs : ∀ q, ContDiff ℝ 3 (uncurry (G q))) (hHs : ∀ q, ContDiff ℝ 3 (uncurry (H q)))
    (L : Puncture → ℝ) {Λ : Puncture → ℝ≥0}
    (hX : ∀ q, LipschitzWith (Λ q)
      (ω.timeDependentHamiltonianSuspension (positiveEndHamiltonian H q)))
    {x : Puncture → ℝ → F}
    (hx : ∀ q t, HasDerivAt (x q)
      (ω.hamiltonianVectorField (positiveEndHamiltonian H q t) (x q t)) t)
    (hxp : ∀ q, Periodic (x q) 1)
    (hnd : ∀ q, IsNondegenerateFixedPt 𝓘(ℝ, F)
      (ω.timeDependentHamiltonianFlow (positiveEndHamiltonian H q) (hX q) 0 1) (x q 0))
    {J : ℝ × ℝ → F → AlmostComplexStructure F}
    {Je : Puncture → ℝ → F → AlmostComplexStructure F} {R₁ : ℝ}
    (hJe : ∀ q, ContDiff ℝ 1 fun p : ℝ × F ↦ (Je q p.1 p.2).toLinearMap.toContinuousLinearMap)
    (hJex : ∀ q t, ω.Compatible (Je q t (x q t)))
    (hJx : ∀ q, ContDiff ℝ 2 fun t ↦ (Je q t (x q t)).toLinearMap.toContinuousLinearMap)
    (hJeq : ∀ q (ζ : ℝ × ℝ), R₁ ≤ ζ.1 → J (positiveEndChart q ζ) = Je q ζ.2)
    {u : ℝ × ℝ → F}
    (hJ : ∀ z ∈ thricePuncturedSphereReal, ContDiffAt ℝ 2
      (fun p : (ℝ × ℝ) × F ↦ (J p.1 p.2).toLinearMap.toContinuousLinearMap) (z, u z))
    (hu : ∀ z ∈ thricePuncturedSphereReal, ContDiffAt ℝ 2 u z)
    (hc : ∀ z ∈ thricePuncturedSphereReal, ω.Compatible (J z (u z)))
    (hF : ∀ q, ∀ z ∈ thricePuncturedSphereReal, R₁ ≤ (positiveEndCoord q z).1 →
      IsComplexLinearMap (AlmostComplexStructure.product ℝ) (J z (u z)) (ω.perturbedFDeriv
        (fun z x ↦
          pairOfPantsContinuationPerturbation G H L (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦
          pairOfPantsContinuationPerturbation G H L (Complex.equivRealProdCLM.symm z) x
            Complex.I) u z : ℝ × ℝ →ₗ[ℝ] F))
    (hux : ∀ q, TendstoUniformlyOn (fun s t ↦ u (positiveEndChart q (s, t))) (x q) atTop
      (Icc 0 1))
    (hδ : ∀ q, TendstoUniformlyOn (fun s t ↦ sliceDefect
      (fun t ↦ ω.hamiltonianVectorField (positiveEndHamiltonian H q t)) (u ∘ positiveEndChart q)
        (s, t)) 0 atTop (Icc 0 1))
    {O : Set (ℝ × ℝ)} (hO : IsOpen O) (hOne : O.Nonempty) (hOS : O ⊆ thricePuncturedSphereReal)
    {W : Set ((ℝ × ℝ) × F)} (hW : ∀ z ∈ O, W ∈ 𝓝 (z, u z)) :
    ∃ (N : ℕ) (y : Fin N → Lp F 2 (volume.restrict thricePuncturedSphereReal)),
      (∀ i, y i ∈ ω.hamiltonianVariationsOn thricePuncturedSphereReal u W) ∧
      Function.Surjective ((ω.floerConformalSobolevOperator thricePuncturedSphereReal
        cylindricalWeight (fun z y ↦ (J z y).toLinearMap.toContinuousLinearMap)
        (fun z x ↦
          pairOfPantsContinuationPerturbation G H L (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦
          pairOfPantsContinuationPerturbation G H L (Complex.equivRealProdCLM.symm z) x Complex.I)
        u).coprod (Fintype.linearCombination ℝ y).toContinuousLinearMap) :=
  -- Beyond the height `max R₁ (2 + ∑_q |L_q|)` on every end the datum is the pair-of-pants datum
  -- of `H`.
  ω.exists_surjective_floerConformalSobolevOperator_coprod_pairOfPants hω hH hHs hX hx hxp hnd hJe
    hJex hJx (R₁ := max R₁ (2 + ∑ r, |L r|)) (fun q ζ hζ ↦ hJeq q ζ ((le_max_left _ _).trans hζ))
    (fun q _ _ hz ↦ pairOfPantsContinuationPerturbation_components_eq (le_max_right _ _) q hz) hJ
    (fun z hz ↦ contDiffAt_uncurry_pairOfPantsContinuationPerturbation hG hH hGs hHs L hz (u z) 1)
    (fun z hz ↦
      contDiffAt_uncurry_pairOfPantsContinuationPerturbation hG hH hGs hHs L hz (u z) Complex.I)
    hu hc (fun q z hz hR ↦ hF q z hz ((le_max_left _ _).trans hR)) hux hδ hO hOne hOS hW

end Surjective

end TauCeti.SymplecticForm
