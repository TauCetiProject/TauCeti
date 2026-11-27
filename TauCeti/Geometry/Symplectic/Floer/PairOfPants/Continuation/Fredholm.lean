/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Floer.PairOfPants.Continuation
public import TauCeti.Geometry.Symplectic.Floer.PairOfPants.Sobolev.Fredholm
public import TauCeti.Geometry.Symplectic.Floer.PairOfPants.Sobolev.Invariance

/-!
# The linearized operator of a pair of pants with continuation necks is Fredholm

Pair-of-pants products for two choices of end Hamiltonians are compared by gluing continuation
cylinders to the ends of the pair of pants `S = ℂ ∖ {0, 1}`. The datum of this gluing,
`TauCeti.Floer.pairOfPantsContinuationPerturbation G H L`, is the pair-of-pants datum of the inner
Hamiltonians `G` on the pants side of necks placed at the positions `L_q`, a continuation datum from
`G_q` to `H_q` along each neck, and `H_q(t) dt` beyond it. Moving the neck positions along a path
gives the one-parameter families of pairs of pants whose broken ends compare continuation maps with
pair-of-pants products. For fixed neck positions the moduli spaces are cut out by the linearized
operator `D_u` of this datum, and its index is their expected dimension (their dimension when they
are regular); the moduli space over a path of neck positions has expected dimension one more.

Let `F` be a finite-dimensional complex inner product space whose symplectic form `ω` is
`Im ⟪·, ·⟫`, and let `u` be a map on `S` whose ends converge to nondegenerate one-periodic orbits of
the outer Hamiltonians `H_q`, for almost complex structures which are cylindrical far out on the
ends and compatible along `u`. This file proves:

* the realization `D_u : W^{1,2}_0(S, F) → L²(S, F)` of the linearized Floer operator of the datum
  with continuation necks, for the cylindrical metric
  (`TauCeti.SymplecticForm.floerConformalSobolevOperator`), is Fredholm
  (`isFredholm_floerConformalSobolevOperator_pairOfPantsContinuationPerturbation`, in the
  namespace `TauCeti.SymplecticForm`);
* its index is the index of the pair-of-pants operator of the outer Hamiltonians, for any data
  over the core of `S` which agree with the same end data far out on the ends
  (`index_floerConformalSobolevOperator_pairOfPantsContinuationPerturbation_eq_of_pairOfPants_data`,
  in the namespace `TauCeti.SymplecticForm`);
* in particular the index does not depend on the neck positions, on the inner Hamiltonians or on the
  almost complex structures over the core
  (`index_floerConformalSobolevOperator_pairOfPantsContinuationPerturbation_eq`, in the namespace
  `TauCeti.SymplecticForm`). So for a fixed map `u` with the given asymptotic orbits, the index of
  `D_u` does not change as the neck positions move, and equals the index of the pair-of-pants
  operator of the outer Hamiltonians.

Beyond the height `2 + ∑_q |L_q|` on each end the datum is the pair-of-pants datum of `H`
(`TauCeti.Floer.pairOfPantsContinuationPerturbation_components_eq`), so these are instances of the
Fredholm property of the pair-of-pants operator for data that agree with the pair-of-pants data far
out on the ends (`TauCeti.SymplecticForm.isFredholm_floerConformalSobolevOperator_pairOfPants`) and
of the invariance of its index under changes of the data over the core
(`TauCeti.SymplecticForm.index_floerConformalSobolevOperator_eq_of_pairOfPants_data`). The value
of the index is not computed here.

## References

* D. Salamon, *Lectures on Floer homology*, in *Symplectic geometry and topology*, IAS/Park City
  Math. Ser. 7 (1999), Lectures 2 and 3, on the Fredholm property of the linearized operator and
  on continuation maps.
* M. Schwarz, *Cohomology operations from S¹-cobordisms in Floer homology*, PhD thesis,
  ETH Zürich (1995), on the Fredholm theory of the pair-of-pants product and its compatibility with
  continuation maps.
-/

public section

open Set Function Filter MeasureTheory TauCeti.ThricePuncturedSphere
  TauCeti.ThricePuncturedSphere.Puncture TauCeti.Floer
open scoped NNReal Manifold

namespace TauCeti.SymplecticForm

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] [FiniteDimensional ℂ F]

/-- **The linearized operator along a pair of pants with continuation necks is Fredholm.** Let
`F` be a finite-dimensional complex inner product space whose symplectic form `ω` is
`Im ⟪·, ·⟫`. Let `G_q` be jointly `C²` and `H_q` jointly `C³` period-one Hamiltonians on the three
ends of `S = ℂ ∖ {0, 1}`, the inner and outer Hamiltonians of the pair-of-pants perturbation with
continuation necks at the positions `L_q` (`TauCeti.Floer.pairOfPantsContinuationPerturbation`).
Suppose that the positive end Hamiltonians `H'_q` of the outer Hamiltonians have globally Lipschitz
suspended vector fields, and let `x_q` be one-periodic orbits of `H'_q` starting at nondegenerate
fixed points of the time-one maps. Let `J(z)` be a family of almost complex structures, `C¹` along
`u`, that is cylindrical far out on each end, `J(φ'_q(s, t)) = J_q(t)` for `s ≥ R₁` with `C¹`
families `J_q` compatible with `ω` and `C²` in `t` along `x_q`. Let `u` be a `C¹` map on `S`, along
which `J` is compatible, that solves the Floer equation for this datum beyond `R₁` on each end,
whose loops in each positive end chart `φ'_q` converge uniformly to `x_q` while the slice defects
`∂t (u ∘ φ'_q) - X_{H'_q}` tend uniformly to zero. Then the realization
`D_u : W^{1,2}_0(S, F) → L²(S, F)` of the linearized Floer operator of the datum, for the
cylindrical metric, is Fredholm. -/
theorem isFredholm_floerConformalSobolevOperator_pairOfPantsContinuationPerturbation
    (ω : SymplecticForm F) (hω : ∀ v w, ω v w = (inner ℂ v w).im) {G H : Puncture → ℝ → F → ℝ}
    (hG : ∀ q, Periodic (G q) 1) (hH : ∀ q, Periodic (H q) 1)
    (hGs : ∀ q, ContDiff ℝ 2 (uncurry (G q))) (hHs : ∀ q, ContDiff ℝ 3 (uncurry (H q)))
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
    (hJ : ∀ z ∈ thricePuncturedSphereReal, ContDiffAt ℝ 1
      (fun p : (ℝ × ℝ) × F ↦ (J p.1 p.2).toLinearMap.toContinuousLinearMap) (z, u z))
    (hu : ∀ z ∈ thricePuncturedSphereReal, ContDiffAt ℝ 1 u z)
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
        (s, t)) 0 atTop (Icc 0 1)) :
    (ω.floerConformalSobolevOperator thricePuncturedSphereReal cylindricalWeight
      (fun z y ↦ (J z y).toLinearMap.toContinuousLinearMap)
      (fun z x ↦
        pairOfPantsContinuationPerturbation G H L (Complex.equivRealProdCLM.symm z) x 1)
      (fun z x ↦
        pairOfPantsContinuationPerturbation G H L (Complex.equivRealProdCLM.symm z) x Complex.I)
      u).IsFredholm := by
  have hHs₂ (q : Puncture) : ContDiff ℝ 2 (uncurry (H q)) := (hHs q).of_le (by norm_num)
  -- Beyond the height `max R₁ (2 + ∑_q |L_q|)` on every end the datum is the pair-of-pants datum
  -- of `H`.
  exact ω.isFredholm_floerConformalSobolevOperator_pairOfPants hω hH hHs hX hx hxp hnd hJe hJex
    hJx (R₁ := max R₁ (2 + ∑ r, |L r|)) (fun q ζ hζ ↦ hJeq q ζ ((le_max_left _ _).trans hζ))
    (fun q _ _ hz ↦ pairOfPantsContinuationPerturbation_components_eq (le_max_right _ _) q hz) hJ
    (fun z hz ↦ contDiffAt_uncurry_pairOfPantsContinuationPerturbation hG hH hGs hHs₂ L hz (u z) 1)
    (fun z hz ↦
      contDiffAt_uncurry_pairOfPantsContinuationPerturbation hG hH hGs hHs₂ L hz (u z) Complex.I)
    hu hc (fun q z hz hR ↦ hF q z hz ((le_max_left _ _).trans hR)) hux hδ

/-- **The index along a pair of pants with continuation necks is the pair-of-pants index.** Under
the hypotheses of `isFredholm_floerConformalSobolevOperator_pairOfPantsContinuationPerturbation`,
suppose also that `J` is `ω`-tame. Let `(J', K'_s, K'_t)` be Floer data on `S` with `ω`-tame
almost complex structures, `C¹` (with `C²` Hamiltonians) along the graph of `u` and
`ω`-compatible along it, which beyond the height `R₁'` of every end are the end data: in the
positive end chart `φ'_q` the structures are `J_q(t)` and the perturbation is the pair-of-pants
perturbation of the outer Hamiltonians `H`. Then the realization
`D_u : W^{1,2}_0(S, F) → L²(S, F)` of the linearized Floer operator of the datum with continuation
necks has the index of the realization of the linearized Floer operator of `(J', K'_s, K'_t)`. -/
theorem
    index_floerConformalSobolevOperator_pairOfPantsContinuationPerturbation_eq_of_pairOfPants_data
    (ω : SymplecticForm F) (hω : ∀ v w, ω v w = (inner ℂ v w).im) {G H : Puncture → ℝ → F → ℝ}
    (hG : ∀ q, Periodic (G q) 1) (hH : ∀ q, Periodic (H q) 1)
    (hGs : ∀ q, ContDiff ℝ 2 (uncurry (G q))) (hHs : ∀ q, ContDiff ℝ 3 (uncurry (H q)))
    (L : Puncture → ℝ) {Λ : Puncture → ℝ≥0}
    (hX : ∀ q, LipschitzWith (Λ q)
      (ω.timeDependentHamiltonianSuspension (positiveEndHamiltonian H q)))
    {x : Puncture → ℝ → F}
    (hx : ∀ q t, HasDerivAt (x q)
      (ω.hamiltonianVectorField (positiveEndHamiltonian H q t) (x q t)) t)
    (hxp : ∀ q, Periodic (x q) 1)
    (hnd : ∀ q, IsNondegenerateFixedPt 𝓘(ℝ, F)
      (ω.timeDependentHamiltonianFlow (positiveEndHamiltonian H q) (hX q) 0 1) (x q 0))
    {J J' : ℝ × ℝ → F → AlmostComplexStructure F}
    {Je : Puncture → ℝ → F → AlmostComplexStructure F} {R₁ R₁' : ℝ}
    (hJe : ∀ q, ContDiff ℝ 1 fun p : ℝ × F ↦ (Je q p.1 p.2).toLinearMap.toContinuousLinearMap)
    (hJex : ∀ q t, ω.Compatible (Je q t (x q t)))
    (hJx : ∀ q, ContDiff ℝ 2 fun t ↦ (Je q t (x q t)).toLinearMap.toContinuousLinearMap)
    (hJeq : ∀ q (ζ : ℝ × ℝ), R₁ ≤ ζ.1 → J (positiveEndChart q ζ) = Je q ζ.2)
    (hJeq' : ∀ q (ζ : ℝ × ℝ), R₁' ≤ ζ.1 → J' (positiveEndChart q ζ) = Je q ζ.2)
    {Ks' Kt' : ℝ × ℝ → F → ℝ}
    (hK' : ∀ q, ∀ z ∈ thricePuncturedSphereReal, R₁' ≤ (positiveEndCoord q z).1 →
      Ks' z = (fun x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x 1) ∧
        Kt' z = fun x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x Complex.I)
    {u : ℝ × ℝ → F}
    (hJ : ∀ z ∈ thricePuncturedSphereReal, ContDiffAt ℝ 1
      (fun p : (ℝ × ℝ) × F ↦ (J p.1 p.2).toLinearMap.toContinuousLinearMap) (z, u z))
    (hJ' : ∀ z ∈ thricePuncturedSphereReal, ContDiffAt ℝ 1
      (fun p : (ℝ × ℝ) × F ↦ (J' p.1 p.2).toLinearMap.toContinuousLinearMap) (z, u z))
    (hKs' : ∀ z ∈ thricePuncturedSphereReal, ContDiffAt ℝ 2 (uncurry Ks') (z, u z))
    (hKt' : ∀ z ∈ thricePuncturedSphereReal, ContDiffAt ℝ 2 (uncurry Kt') (z, u z))
    (hJt : ∀ z y, ω.Tames (J z y)) (hJ't : ∀ z y, ω.Tames (J' z y))
    (hu : ∀ z ∈ thricePuncturedSphereReal, ContDiffAt ℝ 1 u z)
    (hc : ∀ z ∈ thricePuncturedSphereReal, ω.Compatible (J z (u z)))
    (hc' : ∀ z ∈ thricePuncturedSphereReal, ω.Compatible (J' z (u z)))
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
        (s, t)) 0 atTop (Icc 0 1)) :
    (ω.floerConformalSobolevOperator thricePuncturedSphereReal cylindricalWeight
      (fun z y ↦ (J z y).toLinearMap.toContinuousLinearMap)
      (fun z x ↦
        pairOfPantsContinuationPerturbation G H L (Complex.equivRealProdCLM.symm z) x 1)
      (fun z x ↦
        pairOfPantsContinuationPerturbation G H L (Complex.equivRealProdCLM.symm z) x Complex.I)
      u).index =
      (ω.floerConformalSobolevOperator thricePuncturedSphereReal cylindricalWeight
        (fun z y ↦ (J' z y).toLinearMap.toContinuousLinearMap) Ks' Kt' u).index := by
  let : InnerProductSpace ℝ F := InnerProductSpace.complexToReal
  have hHs₂ (q : Puncture) : ContDiff ℝ 2 (uncurry (H q)) := (hHs q).of_le (by norm_num)
  -- Beyond the height `max R₁ (2 + ∑_q |L_q|)` on every end the datum with continuation necks is
  -- the pair-of-pants datum of `H`, so both sets of data have the same end data.
  exact (index_floerConformalSobolevOperator_eq_of_pairOfPants_data ω hH hHs₂ hX hx hnd hJe hJex
    (R₁ := max R₁ (2 + ∑ r, |L r|)) (fun q ζ hζ ↦ hJeq q ζ ((le_max_left _ _).trans hζ)) hJeq'
    (fun q _ _ hz ↦ pairOfPantsContinuationPerturbation_components_eq (le_max_right _ _) q hz) hK'
    hJ hJ'
    (fun z hz ↦ contDiffAt_uncurry_pairOfPantsContinuationPerturbation hG hH hGs hHs₂ L hz (u z) 1)
    (fun z hz ↦
      contDiffAt_uncurry_pairOfPantsContinuationPerturbation hG hH hGs hHs₂ L hz (u z) Complex.I)
    hKs' hKt' hJt hJ't hc hc' hu (fun q z hz hR ↦ hF q z hz ((le_max_left _ _).trans hR)) hux hδ
    (ω.isFredholm_floerConformalSobolevOperator_pairOfPantsContinuationPerturbation hω hG hH hGs
      hHs L hX hx hxp hnd hJe hJex hJx hJeq hJ hu hc hF hux hδ)).symm

/-- **The index along a pair of pants with continuation necks does not depend on the necks.**
Under the hypotheses of
`isFredholm_floerConformalSobolevOperator_pairOfPantsContinuationPerturbation`, suppose also
that `J` is `ω`-tame. Let `G'_q` be other jointly `C²` period-one inner Hamiltonians,
`L'_q` other neck positions, and `J'` other `ω`-tame almost complex structures, `C¹` along `u` and
`ω`-compatible along it, equal to the same structures `J_q(t)` beyond the height `R₁'` of each end.
Then the realizations `D_u : W^{1,2}_0(S, F) → L²(S, F)` of the linearized Floer operators of the
data with continuation necks `(J, G, H, L)` and `(J', G', H, L')` have the same index. -/
theorem index_floerConformalSobolevOperator_pairOfPantsContinuationPerturbation_eq
    (ω : SymplecticForm F) (hω : ∀ v w, ω v w = (inner ℂ v w).im) {G G' H : Puncture → ℝ → F → ℝ}
    (hG : ∀ q, Periodic (G q) 1) (hG' : ∀ q, Periodic (G' q) 1) (hH : ∀ q, Periodic (H q) 1)
    (hGs : ∀ q, ContDiff ℝ 2 (uncurry (G q))) (hGs' : ∀ q, ContDiff ℝ 2 (uncurry (G' q)))
    (hHs : ∀ q, ContDiff ℝ 3 (uncurry (H q))) (L L' : Puncture → ℝ) {Λ : Puncture → ℝ≥0}
    (hX : ∀ q, LipschitzWith (Λ q)
      (ω.timeDependentHamiltonianSuspension (positiveEndHamiltonian H q)))
    {x : Puncture → ℝ → F}
    (hx : ∀ q t, HasDerivAt (x q)
      (ω.hamiltonianVectorField (positiveEndHamiltonian H q t) (x q t)) t)
    (hxp : ∀ q, Periodic (x q) 1)
    (hnd : ∀ q, IsNondegenerateFixedPt 𝓘(ℝ, F)
      (ω.timeDependentHamiltonianFlow (positiveEndHamiltonian H q) (hX q) 0 1) (x q 0))
    {J J' : ℝ × ℝ → F → AlmostComplexStructure F}
    {Je : Puncture → ℝ → F → AlmostComplexStructure F} {R₁ R₁' : ℝ}
    (hJe : ∀ q, ContDiff ℝ 1 fun p : ℝ × F ↦ (Je q p.1 p.2).toLinearMap.toContinuousLinearMap)
    (hJex : ∀ q t, ω.Compatible (Je q t (x q t)))
    (hJx : ∀ q, ContDiff ℝ 2 fun t ↦ (Je q t (x q t)).toLinearMap.toContinuousLinearMap)
    (hJeq : ∀ q (ζ : ℝ × ℝ), R₁ ≤ ζ.1 → J (positiveEndChart q ζ) = Je q ζ.2)
    (hJeq' : ∀ q (ζ : ℝ × ℝ), R₁' ≤ ζ.1 → J' (positiveEndChart q ζ) = Je q ζ.2)
    {u : ℝ × ℝ → F}
    (hJ : ∀ z ∈ thricePuncturedSphereReal, ContDiffAt ℝ 1
      (fun p : (ℝ × ℝ) × F ↦ (J p.1 p.2).toLinearMap.toContinuousLinearMap) (z, u z))
    (hJ' : ∀ z ∈ thricePuncturedSphereReal, ContDiffAt ℝ 1
      (fun p : (ℝ × ℝ) × F ↦ (J' p.1 p.2).toLinearMap.toContinuousLinearMap) (z, u z))
    (hJt : ∀ z y, ω.Tames (J z y)) (hJ't : ∀ z y, ω.Tames (J' z y))
    (hu : ∀ z ∈ thricePuncturedSphereReal, ContDiffAt ℝ 1 u z)
    (hc : ∀ z ∈ thricePuncturedSphereReal, ω.Compatible (J z (u z)))
    (hc' : ∀ z ∈ thricePuncturedSphereReal, ω.Compatible (J' z (u z)))
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
        (s, t)) 0 atTop (Icc 0 1)) :
    (ω.floerConformalSobolevOperator thricePuncturedSphereReal cylindricalWeight
      (fun z y ↦ (J z y).toLinearMap.toContinuousLinearMap)
      (fun z x ↦
        pairOfPantsContinuationPerturbation G H L (Complex.equivRealProdCLM.symm z) x 1)
      (fun z x ↦
        pairOfPantsContinuationPerturbation G H L (Complex.equivRealProdCLM.symm z) x Complex.I)
      u).index =
      (ω.floerConformalSobolevOperator thricePuncturedSphereReal cylindricalWeight
        (fun z y ↦ (J' z y).toLinearMap.toContinuousLinearMap)
        (fun z x ↦
          pairOfPantsContinuationPerturbation G' H L' (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦
          pairOfPantsContinuationPerturbation G' H L' (Complex.equivRealProdCLM.symm z) x
            Complex.I)
        u).index := by
  have hHs₂ (q : Puncture) : ContDiff ℝ 2 (uncurry (H q)) := (hHs q).of_le (by norm_num)
  -- Beyond the height `max R₁' (2 + ∑_q |L'_q|)` on every end the second datum is the
  -- pair-of-pants datum of `H`.
  exact
    index_floerConformalSobolevOperator_pairOfPantsContinuationPerturbation_eq_of_pairOfPants_data
    ω hω hG hH hGs hHs L hX hx hxp hnd hJe hJex hJx hJeq (R₁' := max R₁' (2 + ∑ r, |L' r|))
    (fun q ζ hζ ↦ hJeq' q ζ ((le_max_left _ _).trans hζ))
    (fun q _ _ hz ↦ pairOfPantsContinuationPerturbation_components_eq (le_max_right _ _) q hz) hJ
    hJ'
    (fun z hz ↦
      contDiffAt_uncurry_pairOfPantsContinuationPerturbation hG' hH hGs' hHs₂ L' hz (u z) 1)
    (fun z hz ↦
      contDiffAt_uncurry_pairOfPantsContinuationPerturbation hG' hH hGs' hHs₂ L' hz (u z)
        Complex.I)
    hJt hJ't hu hc hc' hF hux hδ

end TauCeti.SymplecticForm
