/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Floer.PairOfPants.Exchange.Sobolev
public import TauCeti.Geometry.Symplectic.Floer.Transversality.Conformal

/-!
# Hamiltonian variations along the input-exchange family detect the cokernel

Graded commutativity of the pair-of-pants product counts the members of the input-exchange family
`K_c = TauCeti.Floer.exchangePerturbation H c`, `0 ≤ c ≤ 1`, on the pair of pants
`S = ℂ ∖ {0, 1}`, on a finite-dimensional symplectic vector space `(V, ω)`. Each member is the
pair-of-pants datum far out on the two input ends, and on the output end it is the pair-of-pants
datum translated by `c`. Away from the ends the perturbation of a member is free, and the moduli
spaces of the family are made regular by varying it there. This file proves that these variations
detect the whole cokernel of the linearized operator
`D_u : W^{1,2}_0(S, V) → L²(S, V)` of any member, the realization
`TauCeti.SymplecticForm.floerConformalSobolevOperator` for the cylindrical weight
`TauCeti.Floer.cylindricalWeight`: for any nonempty open set `O ⊆ S` and any neighbourhood `W` of
the graph of `u` over `O`, the range of `D_u` and the Hamiltonian variations supported in `W`
(`TauCeti.SymplecticForm.hamiltonianVariationsOn`) span a dense subspace of `L²(S, V)`.

* **Data with a recentred output end.** The statement holds for all Floer data that are the
  pair-of-pants data far out on the input ends and their translate by `c`, `|c| ≤ 1`, far out on
  the output end, read in the recentred end chart `c + φ'_∞`
  (`topologicalClosure_range_sup_span_hamiltonianVariationsOn_eq_top_of_recentered`).
* **The input-exchange family.** Every member `K_c` is such a datum
  (`topologicalClosure_range_sup_span_hamiltonianVariationsOn_exchangePerturbation_eq_top`).

Both theorems are in the namespace `TauCeti.SymplecticForm`, and both are the cokernel detection of
`TauCeti.Geometry.Symplectic.Floer.Transversality.Conformal` on the connected set `S`
(`TauCeti.Floer.isConnected_thricePuncturedSphereReal`), with the essential boundedness of the
coefficient field of `D_u` on conformal jets
(`TauCeti.SymplecticForm.memLp_floerConformalJetCoeff_of_recentered`). No hypothesis is placed on
`u` over `O`, which may be constant there. When `D_u` is Fredholm, the closed range of finite
codimension turns density into surjectivity, with finitely many variations
(`TauCeti.SymplecticForm.exists_finset_subset_hamiltonianVariationsOn_range_sup_span_eq_top`).

## References

* D. McDuff and D. Salamon, *J-holomorphic curves and symplectic topology*, 2nd ed., AMS
  Colloquium Publications 52, 2012, Proposition 3.2.1 and Section 8.1.
* M. Schwarz, *Cohomology operations from S¹-cobordisms in Floer homology*, PhD thesis,
  ETH Zürich (1995), on the transversality of the moduli spaces of pairs of pants and their
  graded commutativity.
-/

public section

open Set Function Filter Topology MeasureTheory TauCeti.ThricePuncturedSphere
  TauCeti.ThricePuncturedSphere.Puncture

namespace TauCeti.SymplecticForm

open Floer

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]

/-- **Hamiltonian variations make the linearized operator with a recentred output end dense.**
Let `H_q` be jointly `C²` period-one Hamiltonians on the three ends of `S = ℂ ∖ {0, 1}`, let
`|c| ≤ 1`, and let `(J, K_s, K_t)` be Floer data on `S`, with `J` `C²` and `K_s`, `K_t` `C³` along
`u`, which far out on each end, beyond a height `R₁`, are cylindrical: on the input ends `q = 0, 1`
they are `C¹` families `J_q(t)` and the pair-of-pants perturbation of `H` in the positive end
charts `φ'_q`, and on the output end they are a `C¹` family `J_∞(t)` and the pair-of-pants
perturbation translated by `c`, in the recentred end chart `c + φ'_∞`. Let `u` be `C²` on `S`,
solve the Floer equation beyond `R₁` on each end, and have loops, read in these end charts,
converging uniformly on `[0, 1]` to loops `x_q` continuous on `[0, 1]`, while the slice defects
tend uniformly to zero. Then for every nonempty open set `O ⊆ S` and every neighbourhood `W` of the
graph of `u` over `O`, the range of `D_u : W^{1,2}_0(S, V) → L²(S, V)` and the Hamiltonian
variations supported in `W` span a dense subspace of `L²(S, V)`. -/
theorem topologicalClosure_range_sup_span_hamiltonianVariationsOn_eq_top_of_recentered
    (ω : SymplecticForm V) {H : Puncture → ℝ → V → ℝ} (hH : ∀ q, Periodic (H q) 1)
    (hHs : ∀ q, ContDiff ℝ 2 (uncurry (H q))) {c : ℝ} (hc : |c| ≤ 1) {x : Puncture → ℝ → V}
    (hx : ∀ q, ContinuousOn (x q) (Icc 0 1)) {J : ℝ × ℝ → V → AlmostComplexStructure V}
    {Je : Puncture → ℝ → V → AlmostComplexStructure V} {R₁ : ℝ}
    (hJe : ∀ q, ContDiff ℝ 1 fun p : ℝ × V ↦ (Je q p.1 p.2).toLinearMap.toContinuousLinearMap)
    (hJeq : ∀ q, q ≠ inf → ∀ ζ : ℝ × ℝ, R₁ ≤ ζ.1 → J (positiveEndChart q ζ) = Je q ζ.2)
    (hJeq_inf : ∀ ζ : ℝ × ℝ, R₁ ≤ ζ.1 → J (positiveEndChart inf ζ + (c, 0)) = Je inf ζ.2)
    {Ks Kt : ℝ × ℝ → V → ℝ}
    (hK : ∀ q, q ≠ inf → ∀ z ∈ thricePuncturedSphereReal, R₁ ≤ (positiveEndCoord q z).1 →
      Ks z = (fun x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x 1) ∧
        Kt z = fun x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x Complex.I)
    (hK_inf : ∀ z : ℝ × ℝ, R₁ ≤ (positiveEndCoord inf z).1 →
      Ks (z + (c, 0)) = (fun x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x 1) ∧
        Kt (z + (c, 0)) =
          fun x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x Complex.I)
    {u : ℝ × ℝ → V}
    (hJ : ∀ z ∈ thricePuncturedSphereReal, ContDiffAt ℝ 2
      (fun p : (ℝ × ℝ) × V ↦ (J p.1 p.2).toLinearMap.toContinuousLinearMap) (z, u z))
    (hKs : ∀ z ∈ thricePuncturedSphereReal, ContDiffAt ℝ 3 (uncurry Ks) (z, u z))
    (hKt : ∀ z ∈ thricePuncturedSphereReal, ContDiffAt ℝ 3 (uncurry Kt) (z, u z))
    (hu : ∀ z ∈ thricePuncturedSphereReal, ContDiffAt ℝ 2 u z)
    (hF : ∀ q, q ≠ inf → ∀ z ∈ thricePuncturedSphereReal, R₁ ≤ (positiveEndCoord q z).1 →
      IsComplexLinearMap (AlmostComplexStructure.product ℝ) (J z (u z))
        (ω.perturbedFDeriv Ks Kt u z : ℝ × ℝ →ₗ[ℝ] V))
    (hF_inf : ∀ z : ℝ × ℝ, R₁ ≤ (positiveEndCoord inf z).1 →
      IsComplexLinearMap (AlmostComplexStructure.product ℝ) (J (z + (c, 0)) (u (z + (c, 0))))
        (ω.perturbedFDeriv Ks Kt u (z + (c, 0)) : ℝ × ℝ →ₗ[ℝ] V))
    (hux : ∀ q, q ≠ inf →
      TendstoUniformlyOn (fun s t ↦ u (positiveEndChart q (s, t))) (x q) atTop (Icc 0 1))
    (hux_inf : TendstoUniformlyOn (fun s t ↦ u (positiveEndChart inf (s, t) + (c, 0))) (x inf)
      atTop (Icc 0 1))
    (hδ : ∀ q, q ≠ inf → TendstoUniformlyOn (fun s t ↦ sliceDefect
      (fun t ↦ ω.hamiltonianVectorField (positiveEndHamiltonian H q t)) (u ∘ positiveEndChart q)
        (s, t)) 0 atTop (Icc 0 1))
    (hδ_inf : TendstoUniformlyOn (fun s t ↦ sliceDefect
      (fun t ↦ ω.hamiltonianVectorField (positiveEndHamiltonian H inf t))
        (fun ζ ↦ u (positiveEndChart inf ζ + (c, 0))) (s, t)) 0 atTop (Icc 0 1))
    {O : Set (ℝ × ℝ)} (hO : IsOpen O) (hOne : O.Nonempty) (hOS : O ⊆ thricePuncturedSphereReal)
    {W : Set ((ℝ × ℝ) × V)} (hW : ∀ z ∈ O, W ∈ 𝓝 (z, u z)) :
    ((ω.floerConformalSobolevOperator thricePuncturedSphereReal cylindricalWeight
        (fun z y ↦ (J z y).toLinearMap.toContinuousLinearMap) Ks Kt u).range ⊔
      Submodule.span ℝ (ω.hamiltonianVariationsOn thricePuncturedSphereReal u W)).topologicalClosure
      = ⊤ :=
  topologicalClosure_range_floerConformalSobolevOperator_sup_span_hamiltonianVariationsOn_eq_top
    isWeight_cylindricalWeight isConnected_thricePuncturedSphereReal.isPreconnected hJ
    (fun z _ ↦ ContinuousLinearMap.ext fun v ↦ by simp) hKs hKt hu
    (ω.memLp_floerConformalJetCoeff_of_recentered hH hHs hc hx hJe hJeq hJeq_inf hK hK_inf
      (fun z hz ↦ (hJ z hz).of_le one_le_two) (fun z hz ↦ (hKs z hz).of_le (by norm_num))
      (fun z hz ↦ (hKt z hz).of_le (by norm_num)) (fun z hz ↦ (hu z hz).of_le one_le_two) hF
      hF_inf hux hux_inf hδ hδ_inf)
    hO hOne hOS hW

/-- **Hamiltonian variations make the linearized operator along the input-exchange family dense.**
Let `H_q` be jointly `C³` period-one Hamiltonians on the three ends of `S = ℂ ∖ {0, 1}`, and let
`K_c = TauCeti.Floer.exchangePerturbation H c` be the member `c ∈ [0, 1]` of the input-exchange
family. Let `J` be a family of almost complex structures on `S`, `C²` along `u`, which far out on
each end, beyond a height `R₁`, is a `C¹` family `J_q(t)` in the positive end chart `φ'_q` of an
input end and in the recentred end chart `c + φ'_∞` of the output end. Let `u` be `C²` on `S`,
solve the Floer equation for `(J, K_c)` beyond `R₁` on each end, and have loops, read in these end
charts, converging uniformly on `[0, 1]` to loops `x_q` continuous on `[0, 1]`, while the slice
defects tend uniformly to zero. Then for every nonempty open set `O ⊆ S` and every neighbourhood
`W` of the graph of `u` over `O`, the range of the linearized operator
`D_u : W^{1,2}_0(S, V) → L²(S, V)` of `(J, K_c)` and the Hamiltonian variations supported in `W`
span a dense subspace of `L²(S, V)`. -/
theorem topologicalClosure_range_sup_span_hamiltonianVariationsOn_exchangePerturbation_eq_top
    (ω : SymplecticForm V) {H : Puncture → ℝ → V → ℝ} (hH : ∀ q, Periodic (H q) 1)
    (hHs : ∀ q, ContDiff ℝ 3 (uncurry (H q))) {c : ℝ} (hc₀ : 0 ≤ c) (hc₁ : c ≤ 1)
    {x : Puncture → ℝ → V} (hx : ∀ q, ContinuousOn (x q) (Icc 0 1))
    {J : ℝ × ℝ → V → AlmostComplexStructure V}
    {Je : Puncture → ℝ → V → AlmostComplexStructure V} {R₁ : ℝ}
    (hJe : ∀ q, ContDiff ℝ 1 fun p : ℝ × V ↦ (Je q p.1 p.2).toLinearMap.toContinuousLinearMap)
    (hJeq : ∀ q, q ≠ inf → ∀ ζ : ℝ × ℝ, R₁ ≤ ζ.1 → J (positiveEndChart q ζ) = Je q ζ.2)
    (hJeq_inf : ∀ ζ : ℝ × ℝ, R₁ ≤ ζ.1 → J (positiveEndChart inf ζ + (c, 0)) = Je inf ζ.2)
    {u : ℝ × ℝ → V}
    (hJ : ∀ z ∈ thricePuncturedSphereReal, ContDiffAt ℝ 2
      (fun p : (ℝ × ℝ) × V ↦ (J p.1 p.2).toLinearMap.toContinuousLinearMap) (z, u z))
    (hu : ∀ z ∈ thricePuncturedSphereReal, ContDiffAt ℝ 2 u z)
    (hF : ∀ q, q ≠ inf → ∀ z ∈ thricePuncturedSphereReal, R₁ ≤ (positiveEndCoord q z).1 →
      IsComplexLinearMap (AlmostComplexStructure.product ℝ) (J z (u z)) (ω.perturbedFDeriv
        (fun z x ↦ exchangePerturbation H c (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ exchangePerturbation H c (Complex.equivRealProdCLM.symm z) x Complex.I)
        u z : ℝ × ℝ →ₗ[ℝ] V))
    (hF_inf : ∀ z : ℝ × ℝ, R₁ ≤ (positiveEndCoord inf z).1 →
      IsComplexLinearMap (AlmostComplexStructure.product ℝ) (J (z + (c, 0)) (u (z + (c, 0))))
        (ω.perturbedFDeriv
          (fun z x ↦ exchangePerturbation H c (Complex.equivRealProdCLM.symm z) x 1)
          (fun z x ↦ exchangePerturbation H c (Complex.equivRealProdCLM.symm z) x Complex.I)
          u (z + (c, 0)) : ℝ × ℝ →ₗ[ℝ] V))
    (hux : ∀ q, q ≠ inf →
      TendstoUniformlyOn (fun s t ↦ u (positiveEndChart q (s, t))) (x q) atTop (Icc 0 1))
    (hux_inf : TendstoUniformlyOn (fun s t ↦ u (positiveEndChart inf (s, t) + (c, 0))) (x inf)
      atTop (Icc 0 1))
    (hδ : ∀ q, q ≠ inf → TendstoUniformlyOn (fun s t ↦ sliceDefect
      (fun t ↦ ω.hamiltonianVectorField (positiveEndHamiltonian H q t)) (u ∘ positiveEndChart q)
        (s, t)) 0 atTop (Icc 0 1))
    (hδ_inf : TendstoUniformlyOn (fun s t ↦ sliceDefect
      (fun t ↦ ω.hamiltonianVectorField (positiveEndHamiltonian H inf t))
        (fun ζ ↦ u (positiveEndChart inf ζ + (c, 0))) (s, t)) 0 atTop (Icc 0 1))
    {O : Set (ℝ × ℝ)} (hO : IsOpen O) (hOne : O.Nonempty) (hOS : O ⊆ thricePuncturedSphereReal)
    {W : Set ((ℝ × ℝ) × V)} (hW : ∀ z ∈ O, W ∈ 𝓝 (z, u z)) :
    ((ω.floerConformalSobolevOperator thricePuncturedSphereReal cylindricalWeight
        (fun z y ↦ (J z y).toLinearMap.toContinuousLinearMap)
        (fun z x ↦ exchangePerturbation H c (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ exchangePerturbation H c (Complex.equivRealProdCLM.symm z) x Complex.I)
        u).range ⊔
      Submodule.span ℝ (ω.hamiltonianVariationsOn thricePuncturedSphereReal u W)).topologicalClosure
      = ⊤ := by
  -- Beyond the height `max R₁ 2`, `K_c` is the pair-of-pants datum on the input ends and its
  -- translate by `c` on the output end.
  have hR₁ : R₁ ≤ max R₁ 2 := le_max_left _ _
  have h1 {r : ℝ} (hr : max R₁ 2 ≤ r) : 1 < r := by linarith [le_max_right R₁ 2]
  exact ω.topologicalClosure_range_sup_span_hamiltonianVariationsOn_eq_top_of_recentered hH
    (fun q ↦ (hHs q).of_le (by norm_num)) (abs_le.2 ⟨by linarith, hc₁⟩) hx hJe
    (fun q hq ζ hζ ↦ hJeq q hq ζ (hR₁.trans hζ)) (fun ζ hζ ↦ hJeq_inf ζ (hR₁.trans hζ))
    (fun _ hq _ _ hz ↦
      exchangePerturbation_components_eq_of_pos_fst_positiveEndCoord hc₀ hc₁ hq
        (zero_lt_one.trans (h1 hz)))
    (fun _ hz ↦ exchangePerturbation_add_components_eq_of_one_lt_fst_positiveEndCoord hc₀ hc₁
      (h1 hz)) hJ
    (fun z hz ↦ contDiffAt_uncurry_exchangePerturbation hH hHs c hz (u z) 1)
    (fun z hz ↦ contDiffAt_uncurry_exchangePerturbation hH hHs c hz (u z) Complex.I) hu
    (fun q hq z hz hzR ↦ hF q hq z hz (hR₁.trans hzR)) (fun z hz ↦ hF_inf z (hR₁.trans hz)) hux
    hux_inf hδ hδ_inf hO hOne hOS hW

end TauCeti.SymplecticForm
