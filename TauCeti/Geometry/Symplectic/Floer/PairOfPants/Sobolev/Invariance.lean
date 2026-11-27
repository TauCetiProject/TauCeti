/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Floer.PairOfPants.Sobolev.SemiFredholm
import TauCeti.Analysis.Calculus.ContDiff.Prod
import TauCeti.Analysis.Fredholm.ContinuousFamily
import TauCeti.Analysis.Fredholm.SemiFredholm
import TauCeti.Geometry.Symplectic.Floer.Continuation.Path
import TauCeti.MeasureTheory.Function.LpSeminorm.Tendsto

/-!
# The Fredholm property and index of the pair-of-pants operator do not depend on the core data

Let `u` be a `C¹` map on the pair of pants `S = ℂ ∖ {0, 1}` into a finite-dimensional symplectic
inner product space `(V, ω)`, and let `(J, K_s, K_t)` and `(J', K'_s, K'_t)` be two sets of Floer
data on `S` which agree far out on the ends: beyond some height of every end `q`, read in the
positive end chart `φ'_q`, both are a `C¹` family `J_q(t)` of almost complex structures, compatible
along the limit orbits `x_q`, together with the pair-of-pants perturbation of the same period-one
Hamiltonians `H_q`, and `u` solves the Floer equation there and converges to nondegenerate
one-periodic orbits `x_q` of the end-chart Hamiltonians `H'_q` along the ends. Over the compact
core of `S` the two sets of data are arbitrary: `ω`-tame almost complex structures, compatible with
`ω` along the graph of `u`, and `C¹` (with `C²` Hamiltonians) along it. This file proves that the
realizations `D_u : W^{1,2}_0(S, V) → L²(S, V)` of the linearized Floer operators of the two sets of
data (`TauCeti.SymplecticForm.floerConformalSobolevOperator` for the cylindrical weight) are
Fredholm together
(`TauCeti.SymplecticForm.isFredholm_floerConformalSobolevOperator_iff_of_pairOfPants_data`), and
then have the same index
(`TauCeti.SymplecticForm.index_floerConformalSobolevOperator_eq_of_pairOfPants_data`). So the
Fredholm property and the index of the pair-of-pants operator only depend on the data on the ends,
and they may be computed for any convenient choice of the data over the core.

This is the pair-of-pants counterpart of the invariance under the data for cylinders
(`TauCeti.SymplecticForm.index_floerSobolevOperator_eq_of_cylindrical_data`), and the proof follows
the same route. The two sets of data are joined by the path of data `(J_μ, K_{s,μ}, K_{t,μ})`,
`0 ≤ μ ≤ 1`, whose almost complex structures run along the path of Cayley coordinates relative to a
fixed compatible structure (`TauCeti.Floer.pathAlmostComplex`) and whose Hamiltonians run
along the segment (`TauCeti.Floer.pathHamiltonian`). Every `J_μ` is compatible along
`u`, and where the two sets of data agree, in particular on the ends, so does every member of the
path. Hence the operator of every member of the path satisfies the semi-Fredholm estimate and has
finite-dimensional kernel and closed range
(`TauCeti.SymplecticForm.finiteDimensional_ker_floerConformalSobolevOperator_pairOfPants`,
`TauCeti.SymplecticForm.isClosed_range_floerConformalSobolevOperator_pairOfPants`). The coefficient
fields of the members agree on the ends, and on the compact core they are uniformly continuous in
`(μ, z)`, so they depend continuously on `μ` in `L^∞`. The operators then form a continuous path of
operators with finite-dimensional kernel and closed range
(`continuousOn_floerConformalSobolevOperator_pairOfPants_family`, for a family of data over any set
of parameters in a normed space), along which the Fredholm property and the index are constant
(`ContinuousOn.isFredholm_of_isPreconnected`, `ContinuousOn.index_eq_of_isPreconnected`).

## References

* D. Salamon, *Lectures on Floer homology*, in *Symplectic geometry and topology*, IAS/Park City
  Math. Ser. 7 (1999), Lecture 2, on the Fredholm index of `∂s + J ∂t + S(s, t)`, which depends
  only on the asymptotic operators.
* M. Schwarz, *Cohomology operations from S¹-cobordisms in Floer homology*, PhD thesis,
  ETH Zürich (1995), on the Fredholm theory of the pair-of-pants operator.
-/

public section

noncomputable section

open Set Function Filter MeasureTheory Metric Topology TauCeti.ThricePuncturedSphere
  TauCeti.ThricePuncturedSphere.Puncture
open scoped ENNReal NNReal Manifold

namespace TauCeti.SymplecticForm

open Floer ConformalSobolev

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]

omit [FiniteDimensional ℝ V] in
/-- Two sets of data equal to the same end data `J_q(t)` beyond the heights `R₁` and `R₁'` of the
ends agree at every point of `S` beyond the height `max R₁ R₁'` of some end. -/
private theorem eq_of_max_le_fst_positiveEndCoord {J J' : ℝ × ℝ → V → AlmostComplexStructure V}
    {Je : Puncture → ℝ → V → AlmostComplexStructure V} {R₁ R₁' : ℝ}
    (hJeq : ∀ q (ζ : ℝ × ℝ), R₁ ≤ ζ.1 → J (positiveEndChart q ζ) = Je q ζ.2)
    (hJeq' : ∀ q (ζ : ℝ × ℝ), R₁' ≤ ζ.1 → J' (positiveEndChart q ζ) = Je q ζ.2)
    {q : Puncture} {z : ℝ × ℝ} (hz : z ∈ thricePuncturedSphereReal)
    (hR : max R₁ R₁' ≤ (positiveEndCoord q z).1) : J z = J' z := by
  rw [← positiveEndChart_positiveEndCoord q
      (ne_endCenter (mem_thricePuncturedSphereReal_iff.1 hz) q),
    hJeq q _ ((le_max_left _ _).trans hR), hJeq' q _ ((le_max_right _ _).trans hR)]

/-- **Continuity of the pair-of-pants operator along a family of data.** Let `H_q` be jointly `C²`
period-one Hamiltonians on the three ends of `S = ℂ ∖ {0, 1}`, on a finite-dimensional symplectic
inner product space `(V, ω)`, and `J_q(t)` a `C¹` family of almost complex structures for each end
`q`. Let `(J_μ, K_{s,μ}, K_{t,μ})` be a family of Floer data on `S`, depending on a parameter `μ` of
a normed space `E`, and `C¹` (with `C²` Hamiltonians) jointly in `μ`, the domain point and the
target point along the graph of a map `u` which is `C¹` on `S`, at every `μ ∈ P`. Suppose that for
`μ ∈ P`, beyond the height `R` of every end, the data are the end data (in the positive end chart
`φ'_q` the structures are `J_q(t)` and the perturbation is the pair-of-pants perturbation of `H`),
and that there `u` solves the Floer equation, with loops in each end chart converging uniformly to
continuous loops `x_q` and slice defects tending uniformly to zero. Then the realization
`D_u : W^{1,2}_0(S, V) → L²(S, V)` of the linearized Floer operator of the data at `μ` depends
continuously on `μ ∈ P` in the operator norm.

Off the compact truncation `S_R` the data do not depend on `μ ∈ P`, and on `S_R` their
coefficient fields are jointly continuous in `(μ, z)` at each `(μ, z)` with `μ ∈ P`, so the
coefficient fields depend continuously on `μ ∈ P` in `L^∞(S)`. -/
theorem continuousOn_floerConformalSobolevOperator_pairOfPants_family {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] (ω : SymplecticForm V)
    {H : Puncture → ℝ → V → ℝ} (hH : ∀ q, Periodic (H q) 1)
    (hHs : ∀ q, ContDiff ℝ 2 (uncurry (H q))) {x : Puncture → ℝ → V}
    (hx : ∀ q, ContinuousOn (x q) (Icc 0 1))
    {Je : Puncture → ℝ → V → AlmostComplexStructure V}
    (hJe : ∀ q, ContDiff ℝ 1 fun p : ℝ × V ↦ (Je q p.1 p.2).toLinearMap.toContinuousLinearMap)
    {J : E × (ℝ × ℝ) → V → AlmostComplexStructure V} {Ks Kt : E × (ℝ × ℝ) → V → ℝ} {R : ℝ}
    {P : Set E}
    (hJeq : ∀ μ ∈ P, ∀ q (ζ : ℝ × ℝ), R ≤ ζ.1 → J (μ, positiveEndChart q ζ) = Je q ζ.2)
    (hK : ∀ μ ∈ P, ∀ q, ∀ z ∈ thricePuncturedSphereReal, R ≤ (positiveEndCoord q z).1 →
      Ks (μ, z) = (fun x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x 1) ∧
        Kt (μ, z) = fun x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x Complex.I)
    {u : ℝ × ℝ → V}
    (hJ : ∀ μ ∈ P, ∀ z ∈ thricePuncturedSphereReal, ContDiffAt ℝ 1
      (fun p : (E × (ℝ × ℝ)) × V ↦ (J p.1 p.2).toLinearMap.toContinuousLinearMap) ((μ, z), u z))
    (hKs : ∀ μ ∈ P, ∀ z ∈ thricePuncturedSphereReal, ContDiffAt ℝ 2 (uncurry Ks) ((μ, z), u z))
    (hKt : ∀ μ ∈ P, ∀ z ∈ thricePuncturedSphereReal, ContDiffAt ℝ 2 (uncurry Kt) ((μ, z), u z))
    (hu : ∀ z ∈ thricePuncturedSphereReal, ContDiffAt ℝ 1 u z)
    (hF : ∀ μ ∈ P, ∀ q, ∀ z ∈ thricePuncturedSphereReal, R ≤ (positiveEndCoord q z).1 →
      IsComplexLinearMap (AlmostComplexStructure.product ℝ) (J (μ, z) (u z))
        (ω.perturbedFDeriv (fun w ↦ Ks (μ, w)) (fun w ↦ Kt (μ, w)) u z : ℝ × ℝ →ₗ[ℝ] V))
    (hux : ∀ q, TendstoUniformlyOn (fun s t ↦ u (positiveEndChart q (s, t))) (x q) atTop
      (Icc 0 1))
    (hδ : ∀ q, TendstoUniformlyOn (fun s t ↦ sliceDefect
      (fun t ↦ ω.hamiltonianVectorField (positiveEndHamiltonian H q t)) (u ∘ positiveEndChart q)
        (s, t)) 0 atTop (Icc 0 1)) :
    ContinuousOn (fun μ ↦ ω.floerConformalSobolevOperator thricePuncturedSphereReal
      cylindricalWeight (fun z y ↦ (J (μ, z) y).toLinearMap.toContinuousLinearMap)
        (fun z ↦ Ks (μ, z)) (fun z ↦ Kt (μ, z)) u) P := by
  set S := thricePuncturedSphereReal
  set M : E → ℝ × ℝ → V × V × V →L[ℝ] V := fun μ ↦ ω.floerConformalJetCoeff cylindricalWeight
    (fun z y ↦ (J (μ, z) y).toLinearMap.toContinuousLinearMap) (fun z ↦ Ks (μ, z))
    (fun z ↦ Kt (μ, z)) u
  have hM (μ : E) (hμ : μ ∈ P) : MemLp (M μ) ∞ (volume.restrict S) :=
    ω.memLp_floerConformalJetCoeff_pairOfPants_of_tendstoUniformlyOn hH hHs hx hJe (hJeq μ hμ)
      (hK μ hμ) (fun z hz ↦ contDiffAt_comp_prodMap_prodMk_right (hJ μ hμ z hz))
      (fun z hz ↦ contDiffAt_comp_prodMap_prodMk_right (hKs μ hμ z hz))
      (fun z hz ↦ contDiffAt_comp_prodMap_prodMk_right (hKt μ hμ z hz)) hu (hF μ hμ) hux hδ
  -- Beyond the height `R` of an end the data are the end data, whatever `μ ∈ P`.
  have heq {μ lam : E} (hμ : μ ∈ P) (hlam : lam ∈ P) {z : ℝ × ℝ} (hz : z ∈ S)
      (hzK : z ∉ Complex.equivRealProdCLM.symm ⁻¹' truncation R) : M μ z = M lam z := by
    obtain ⟨q, hq⟩ := exists_lt_fst_positiveEndCoord_of_notMem_truncation hz hzK
    have hzq := positiveEndChart_positiveEndCoord q
      (ne_endCenter (mem_thricePuncturedSphereReal_iff.1 hz) q)
    obtain ⟨hsμ, htμ⟩ := hK μ hμ q z hz hq.le
    obtain ⟨hsl, htl⟩ := hK lam hlam q z hz hq.le
    refine ω.floerConformalJetCoeff_congr_data _ u ?_ (hsμ.trans hsl.symm) (htμ.trans htl.symm)
    rw [← hzq, hJeq μ hμ q _ hq.le, hJeq lam hlam q _ hq.le]
  simp only [floerConformalSobolevOperator_def]
  refine (continuousOn_jetOperator hM fun lam hlam ↦ ?_).clm_comp continuousOn_const
  -- On the compact truncation `S_R` the coefficient field is jointly continuous in `(μ, z)`, and
  -- off it the coefficient fields do not depend on `μ ∈ P`; read the limit along `P` in `P`.
  rw [tendsto_nhdsWithin_iff_subtype hlam]
  refine tendsto_eLpNorm_top_sub_of_continuousAt_of_eq (M := fun μ : P ↦ M μ)
    isOpen_thricePuncturedSphereReal.measurableSet (isCompact_preimage_truncation R)
    (.of_forall fun μ ↦ (hM μ μ.property).aestronglyMeasurable) (fun z hzK ↦ ?_)
    (.of_forall fun μ z hz hzK ↦ heq μ.property hlam hz hzK)
  have hz := preimage_truncation_subset_thricePuncturedSphereReal R hzK
  have hc := continuousAt_floerConformalJetCoeff_family ω
    (J := fun p y ↦ (J p y).toLinearMap.toContinuousLinearMap) (p := (lam, z)) (hJ lam hlam z hz)
    (hKs lam hlam z hz) (hKt lam hlam z hz) (hu z hz)
    (isWeight_cylindricalWeight.continuousOn.continuousAt
      (isOpen_thricePuncturedSphereReal.mem_nhds hz))
    (isWeight_cylindricalWeight.pos _ hz)
  exact hc.comp (f := Prod.map Subtype.val id) (x := ((⟨lam, hlam⟩ : P), z))
    (continuous_subtypeVal.prodMap continuous_id).continuousAt

/-- **The Fredholm property and the index along a family of data on the pair of pants.** Let
`(J_μ, K_{s,μ}, K_{t,μ})` be a family of Floer data on `S`, `C¹` (with `C²` Hamiltonians) jointly in
the parameter `μ`, the domain point and the target point along the graph of `u`, compatible with
`ω` along `u`, all equal to the same end data beyond the height `R` of every end, along which `u`
solves the Floer equation and converges to nondegenerate orbits. If the operator of the data at
`μ = 0` is Fredholm, then so is the operator of the data at `μ = 1`, with the same index. -/
private theorem isFredholm_and_index_eq_of_family (ω : SymplecticForm V)
    {H : Puncture → ℝ → V → ℝ} (hH : ∀ q, Periodic (H q) 1)
    (hHs : ∀ q, ContDiff ℝ 2 (uncurry (H q))) {L : Puncture → ℝ≥0}
    (hX : ∀ q, LipschitzWith (L q)
      (ω.timeDependentHamiltonianSuspension (positiveEndHamiltonian H q)))
    {x : Puncture → ℝ → V}
    (hx : ∀ q t, HasDerivAt (x q)
      (ω.hamiltonianVectorField (positiveEndHamiltonian H q t) (x q t)) t)
    (hnd : ∀ q, IsNondegenerateFixedPt 𝓘(ℝ, V)
      (ω.timeDependentHamiltonianFlow (positiveEndHamiltonian H q) (hX q) 0 1) (x q 0))
    {Je : Puncture → ℝ → V → AlmostComplexStructure V}
    (hJe : ∀ q, ContDiff ℝ 1 fun p : ℝ × V ↦ (Je q p.1 p.2).toLinearMap.toContinuousLinearMap)
    (hJex : ∀ q t, ω.Compatible (Je q t (x q t)))
    {J : ℝ × (ℝ × ℝ) → V → AlmostComplexStructure V} {Ks Kt : ℝ × (ℝ × ℝ) → V → ℝ} {R : ℝ}
    (hJeq : ∀ μ q (ζ : ℝ × ℝ), R ≤ ζ.1 → J (μ, positiveEndChart q ζ) = Je q ζ.2)
    (hK : ∀ μ q, ∀ z ∈ thricePuncturedSphereReal, R ≤ (positiveEndCoord q z).1 →
      Ks (μ, z) = (fun x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x 1) ∧
        Kt (μ, z) = fun x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x Complex.I)
    {u : ℝ × ℝ → V}
    (hJ : ∀ μ, ∀ z ∈ thricePuncturedSphereReal, ContDiffAt ℝ 1
      (fun p : (ℝ × (ℝ × ℝ)) × V ↦ (J p.1 p.2).toLinearMap.toContinuousLinearMap) ((μ, z), u z))
    (hKs : ∀ μ, ∀ z ∈ thricePuncturedSphereReal, ContDiffAt ℝ 2 (uncurry Ks) ((μ, z), u z))
    (hKt : ∀ μ, ∀ z ∈ thricePuncturedSphereReal, ContDiffAt ℝ 2 (uncurry Kt) ((μ, z), u z))
    (hu : ∀ z ∈ thricePuncturedSphereReal, ContDiffAt ℝ 1 u z)
    (hc : ∀ μ, ∀ z ∈ thricePuncturedSphereReal, ω.Compatible (J (μ, z) (u z)))
    (hF : ∀ μ q, ∀ z ∈ thricePuncturedSphereReal, R ≤ (positiveEndCoord q z).1 →
      IsComplexLinearMap (AlmostComplexStructure.product ℝ) (J (μ, z) (u z))
        (ω.perturbedFDeriv (fun w ↦ Ks (μ, w)) (fun w ↦ Kt (μ, w)) u z : ℝ × ℝ →ₗ[ℝ] V))
    (hux : ∀ q, TendstoUniformlyOn (fun s t ↦ u (positiveEndChart q (s, t))) (x q) atTop
      (Icc 0 1))
    (hδ : ∀ q, TendstoUniformlyOn (fun s t ↦ sliceDefect
      (fun t ↦ ω.hamiltonianVectorField (positiveEndHamiltonian H q t)) (u ∘ positiveEndChart q)
        (s, t)) 0 atTop (Icc 0 1))
    (h : (ω.floerConformalSobolevOperator thricePuncturedSphereReal cylindricalWeight
      (fun z y ↦ (J (0, z) y).toLinearMap.toContinuousLinearMap) (fun z ↦ Ks (0, z))
        (fun z ↦ Kt (0, z)) u).IsFredholm) :
    (ω.floerConformalSobolevOperator thricePuncturedSphereReal cylindricalWeight
      (fun z y ↦ (J (1, z) y).toLinearMap.toContinuousLinearMap) (fun z ↦ Ks (1, z))
        (fun z ↦ Kt (1, z)) u).IsFredholm ∧
      (ω.floerConformalSobolevOperator thricePuncturedSphereReal cylindricalWeight
      (fun z y ↦ (J (1, z) y).toLinearMap.toContinuousLinearMap) (fun z ↦ Ks (1, z))
        (fun z ↦ Kt (1, z)) u).index =
        (ω.floerConformalSobolevOperator thricePuncturedSphereReal cylindricalWeight
      (fun z y ↦ (J (0, z) y).toLinearMap.toContinuousLinearMap) (fun z ↦ Ks (0, z))
        (fun z ↦ Kt (0, z)) u).index := by
  set S := thricePuncturedSphereReal
  -- The data at a fixed `μ` are regular along `u`, as slices of the family.
  have hJμ (μ : ℝ) (z : ℝ × ℝ) (hz : z ∈ S) : ContDiffAt ℝ 1
      (fun p : (ℝ × ℝ) × V ↦ (J (μ, p.1) p.2).toLinearMap.toContinuousLinearMap) (z, u z) :=
    contDiffAt_comp_prodMap_prodMk_right (hJ μ z hz)
  have hKsμ (μ : ℝ) (z : ℝ × ℝ) (hz : z ∈ S) :
      ContDiffAt ℝ 2 (uncurry fun w ↦ Ks (μ, w)) (z, u z) :=
    contDiffAt_comp_prodMap_prodMk_right (hKs μ z hz)
  have hKtμ (μ : ℝ) (z : ℝ × ℝ) (hz : z ∈ S) :
      ContDiffAt ℝ 2 (uncurry fun w ↦ Kt (μ, w)) (z, u z) :=
    contDiffAt_comp_prodMap_prodMk_right (hKt μ z hz)
  -- The operators of the family.
  set T : ℝ → H1 V S cylindricalWeight →L[ℝ] Lp V 2 (volume.restrict S) := fun μ ↦
    ω.floerConformalSobolevOperator S cylindricalWeight
      (fun z y ↦ (J (μ, z) y).toLinearMap.toContinuousLinearMap) (fun z ↦ Ks (μ, z))
      (fun z ↦ Kt (μ, z)) u
  have hker (μ : ℝ) (_ : μ ∈ Icc (0 : ℝ) 1) : FiniteDimensional ℝ (T μ).ker :=
    ω.finiteDimensional_ker_floerConformalSobolevOperator_pairOfPants hH hHs hX hx hnd hJe hJex
      (hJeq μ) (hK μ) (hJμ μ) (hKsμ μ) (hKtμ μ) hu (hc μ) (hF μ) hux hδ
  have hrange (μ : ℝ) (_ : μ ∈ Icc (0 : ℝ) 1) :
      IsClosed ((T μ).range : Set (Lp V 2 (volume.restrict S))) :=
    ω.isClosed_range_floerConformalSobolevOperator_pairOfPants hH hHs hX hx hnd hJe hJex
      (hJeq μ) (hK μ) (hJμ μ) (hKsμ μ) (hKtμ μ) hu (hc μ) (hF μ) hux hδ
  have hT : ContinuousOn T (Icc 0 1) :=
    ω.continuousOn_floerConformalSobolevOperator_pairOfPants_family hH hHs
      (fun q ↦ continuous_iff_continuousAt.2 (fun t ↦ (hx q t).continuousAt) |>.continuousOn) hJe
      (fun μ _ ↦ hJeq μ) (fun μ _ ↦ hK μ) (fun μ _ ↦ hJ μ) (fun μ _ ↦ hKs μ) (fun μ _ ↦ hKt μ)
      hu (fun μ _ ↦ hF μ) hux hδ
  have h0 : (0 : ℝ) ∈ Icc (0 : ℝ) 1 := left_mem_Icc.2 zero_le_one
  have h1 : (1 : ℝ) ∈ Icc (0 : ℝ) 1 := right_mem_Icc.2 zero_le_one
  have hFred (μ : ℝ) (hμ : μ ∈ Icc (0 : ℝ) 1) : (T μ).IsFredholm :=
    hT.isFredholm_of_isPreconnected hker hrange isPreconnected_Icc h0 h hμ
  exact ⟨hFred 1 h1, hT.index_eq_of_isPreconnected hFred isPreconnected_Icc h1 h0⟩

/-- The Fredholm property and the index pass from the data `(J, K_s, K_t)` to the data
`(J', K'_s, K'_t)` with the same end data, along the path of data joining them. -/
private theorem isFredholm_and_index_eq_of_pairOfPants_data (ω : SymplecticForm V)
    {H : Puncture → ℝ → V → ℝ} (hH : ∀ q, Periodic (H q) 1)
    (hHs : ∀ q, ContDiff ℝ 2 (uncurry (H q))) {L : Puncture → ℝ≥0}
    (hX : ∀ q, LipschitzWith (L q)
      (ω.timeDependentHamiltonianSuspension (positiveEndHamiltonian H q)))
    {x : Puncture → ℝ → V}
    (hx : ∀ q t, HasDerivAt (x q)
      (ω.hamiltonianVectorField (positiveEndHamiltonian H q t) (x q t)) t)
    (hnd : ∀ q, IsNondegenerateFixedPt 𝓘(ℝ, V)
      (ω.timeDependentHamiltonianFlow (positiveEndHamiltonian H q) (hX q) 0 1) (x q 0))
    {Je : Puncture → ℝ → V → AlmostComplexStructure V}
    (hJe : ∀ q, ContDiff ℝ 1 fun p : ℝ × V ↦ (Je q p.1 p.2).toLinearMap.toContinuousLinearMap)
    (hJex : ∀ q t, ω.Compatible (Je q t (x q t)))
    {J J' : ℝ × ℝ → V → AlmostComplexStructure V} {R₁ R₁' : ℝ}
    (hJeq : ∀ q (ζ : ℝ × ℝ), R₁ ≤ ζ.1 → J (positiveEndChart q ζ) = Je q ζ.2)
    (hJeq' : ∀ q (ζ : ℝ × ℝ), R₁' ≤ ζ.1 → J' (positiveEndChart q ζ) = Je q ζ.2)
    {Ks Kt Ks' Kt' : ℝ × ℝ → V → ℝ}
    (hK : ∀ q, ∀ z ∈ thricePuncturedSphereReal, R₁ ≤ (positiveEndCoord q z).1 →
      Ks z = (fun x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x 1) ∧
        Kt z = fun x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x Complex.I)
    (hK' : ∀ q, ∀ z ∈ thricePuncturedSphereReal, R₁' ≤ (positiveEndCoord q z).1 →
      Ks' z = (fun x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x 1) ∧
        Kt' z = fun x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x Complex.I)
    {u : ℝ × ℝ → V}
    (hJ : ∀ z ∈ thricePuncturedSphereReal, ContDiffAt ℝ 1
      (fun p : (ℝ × ℝ) × V ↦ (J p.1 p.2).toLinearMap.toContinuousLinearMap) (z, u z))
    (hJ' : ∀ z ∈ thricePuncturedSphereReal, ContDiffAt ℝ 1
      (fun p : (ℝ × ℝ) × V ↦ (J' p.1 p.2).toLinearMap.toContinuousLinearMap) (z, u z))
    (hKs : ∀ z ∈ thricePuncturedSphereReal, ContDiffAt ℝ 2 (uncurry Ks) (z, u z))
    (hKt : ∀ z ∈ thricePuncturedSphereReal, ContDiffAt ℝ 2 (uncurry Kt) (z, u z))
    (hKs' : ∀ z ∈ thricePuncturedSphereReal, ContDiffAt ℝ 2 (uncurry Ks') (z, u z))
    (hKt' : ∀ z ∈ thricePuncturedSphereReal, ContDiffAt ℝ 2 (uncurry Kt') (z, u z))
    (hJt : ∀ z y, ω.Tames (J z y)) (hJ't : ∀ z y, ω.Tames (J' z y))
    (hc : ∀ z ∈ thricePuncturedSphereReal, ω.Compatible (J z (u z)))
    (hc' : ∀ z ∈ thricePuncturedSphereReal, ω.Compatible (J' z (u z)))
    (hu : ∀ z ∈ thricePuncturedSphereReal, ContDiffAt ℝ 1 u z)
    (hF : ∀ q, ∀ z ∈ thricePuncturedSphereReal, R₁ ≤ (positiveEndCoord q z).1 →
      IsComplexLinearMap (AlmostComplexStructure.product ℝ) (J z (u z))
        (ω.perturbedFDeriv Ks Kt u z : ℝ × ℝ →ₗ[ℝ] V))
    (hux : ∀ q, TendstoUniformlyOn (fun s t ↦ u (positiveEndChart q (s, t))) (x q) atTop
      (Icc 0 1))
    (hδ : ∀ q, TendstoUniformlyOn (fun s t ↦ sliceDefect
      (fun t ↦ ω.hamiltonianVectorField (positiveEndHamiltonian H q t)) (u ∘ positiveEndChart q)
        (s, t)) 0 atTop (Icc 0 1))
    (h : (ω.floerConformalSobolevOperator thricePuncturedSphereReal cylindricalWeight
      (fun z y ↦ (J z y).toLinearMap.toContinuousLinearMap) Ks Kt u).IsFredholm) :
    (ω.floerConformalSobolevOperator thricePuncturedSphereReal cylindricalWeight
      (fun z y ↦ (J' z y).toLinearMap.toContinuousLinearMap) Ks' Kt' u).IsFredholm ∧
      (ω.floerConformalSobolevOperator thricePuncturedSphereReal cylindricalWeight
      (fun z y ↦ (J' z y).toLinearMap.toContinuousLinearMap) Ks' Kt' u).index =
        (ω.floerConformalSobolevOperator thricePuncturedSphereReal cylindricalWeight
      (fun z y ↦ (J z y).toLinearMap.toContinuousLinearMap) Ks Kt u).index := by
  set S := thricePuncturedSphereReal
  set R := max (max R₁ R₁') 1
  have hR₁ : R₁ ≤ R := (le_max_left _ _).trans (le_max_left _ _)
  have hR₁' : R₁' ≤ R := (le_max_right _ _).trans (le_max_left _ _)
  -- The path of data from `(J, K_s, K_t)` at `μ = 0` to `(J', K'_s, K'_t)` at `μ = 1`, in
  -- Cayley coordinates relative to a structure compatible with `ω`.
  have h₀ := hc (2, 0) (by norm_num [S, mem_thricePuncturedSphereReal_iff, Complex.ext_iff])
  -- Beyond the height `R` of an end, the two sets of data agree, hence so does every member of
  -- the path.
  have hend {q : Puncture} {z : ℝ × ℝ} (hz : z ∈ S) (hzR : R ≤ (positiveEndCoord q z).1)
      (μ : ℝ) : pathAlmostComplex h₀ hJt hJ't (μ, z) = J z ∧
        pathHamiltonian Ks Ks' (μ, z) = Ks z ∧ pathHamiltonian Kt Kt' (μ, z) = Kt z := by
    have hJz := eq_of_max_le_fst_positiveEndCoord hJeq hJeq' hz ((le_max_left _ _).trans hzR)
    obtain ⟨hs, ht⟩ := hK q z hz (hR₁.trans hzR)
    obtain ⟨hs', ht'⟩ := hK' q z hz (hR₁'.trans hzR)
    exact ⟨funext fun y ↦ pathAlmostComplex_of_eq h₀ μ (congrFun hJz y),
      pathHamiltonian_of_eq μ (hs.trans hs'.symm), pathHamiltonian_of_eq μ (ht.trans ht'.symm)⟩
  have key := isFredholm_and_index_eq_of_family ω hH hHs hX hx hnd hJe hJex
    (J := pathAlmostComplex h₀ hJt hJ't) (Ks := pathHamiltonian Ks Ks')
    (Kt := pathHamiltonian Kt Kt') (R := R)
    (fun μ q ζ hζ ↦ by
      have hz := positiveEndChart_mem_thricePuncturedSphereReal (q := q)
        (zero_lt_one.trans_le ((le_max_right _ _).trans hζ))
      rw [(hend hz (by rw [fst_positiveEndCoord_positiveEndChart]; exact hζ) μ).1,
        hJeq q ζ (hR₁.trans hζ)])
    (fun μ q z hz hzR ↦ by
      rw [(hend hz hzR μ).2.1, (hend hz hzR μ).2.2]
      exact hK q z hz (hR₁.trans hzR))
    (fun μ z hz ↦ contDiffAt_pathAlmostComplex h₀ hJt hJ't (p := (μ, z)) (hJ z hz) (hJ' z hz))
    (fun μ z hz ↦ contDiffAt_pathHamiltonian (p := (μ, z)) (hKs z hz) (hKs' z hz))
    (fun μ z hz ↦ contDiffAt_pathHamiltonian (p := (μ, z)) (hKt z hz) (hKt' z hz)) hu
    (fun μ z hz ↦ compatible_pathAlmostComplex h₀ (hc z hz) (hc' z hz))
    (fun μ q z hz hzR ↦ by
      obtain ⟨hJz, hs, ht⟩ := hend hz hzR μ
      rw [hJz, ω.perturbedFDeriv_congr u (Ks' := Ks) (Kt' := Kt) hs ht]
      exact hF q z hz (hR₁.trans hzR))
    hux hδ
    (by simpa only [pathAlmostComplex_zero, pathHamiltonian_zero] using h)
  simpa only [pathAlmostComplex_zero, pathAlmostComplex_one, pathHamiltonian_zero,
    pathHamiltonian_one] using key

/-- **The Fredholm property of the pair-of-pants operator does not depend on the data over the
core.** Let `H_q` be jointly `C²` period-one Hamiltonians on the three ends of `S = ℂ ∖ {0, 1}`, on
a finite-dimensional symplectic inner product space `(V, ω)`, and `J_q(t)` a `C¹` family of almost
complex structures for each end `q`. Let `(J, K_s, K_t)` and `(J', K'_s, K'_t)` be Floer data on `S`
with `ω`-tame almost complex structures, `C¹` (with `C²` Hamiltonians) along the graph of a map `u`
which is `C¹` on `S`, and `ω`-compatible along it. Suppose that beyond the heights `R₁` and `R₁'` of
every end both sets of data are the end data: in the positive end chart `φ'_q` the structures are
`J_q(t)` and the perturbation is the pair-of-pants perturbation of `H`. Suppose also that beyond the
height `R₁` the map `u` solves the Floer equation, and that its loops in each end chart converge
uniformly to a nondegenerate one-periodic orbit `x_q` of the end-chart Hamiltonian
`H'_q(t, x) = ±H_q(±t, x)` (`TauCeti.Floer.positiveEndHamiltonian`), along which `J_q` is
compatible, with slice defects tending uniformly to zero. Then the realization
`D_u : W^{1,2}_0(S, V) → L²(S, V)` of the linearized Floer operator of the first data is Fredholm if
and only if that of the second data is. -/
theorem isFredholm_floerConformalSobolevOperator_iff_of_pairOfPants_data (ω : SymplecticForm V)
    {H : Puncture → ℝ → V → ℝ} (hH : ∀ q, Periodic (H q) 1)
    (hHs : ∀ q, ContDiff ℝ 2 (uncurry (H q))) {L : Puncture → ℝ≥0}
    (hX : ∀ q, LipschitzWith (L q)
      (ω.timeDependentHamiltonianSuspension (positiveEndHamiltonian H q)))
    {x : Puncture → ℝ → V}
    (hx : ∀ q t, HasDerivAt (x q)
      (ω.hamiltonianVectorField (positiveEndHamiltonian H q t) (x q t)) t)
    (hnd : ∀ q, IsNondegenerateFixedPt 𝓘(ℝ, V)
      (ω.timeDependentHamiltonianFlow (positiveEndHamiltonian H q) (hX q) 0 1) (x q 0))
    {Je : Puncture → ℝ → V → AlmostComplexStructure V}
    (hJe : ∀ q, ContDiff ℝ 1 fun p : ℝ × V ↦ (Je q p.1 p.2).toLinearMap.toContinuousLinearMap)
    (hJex : ∀ q t, ω.Compatible (Je q t (x q t)))
    {J J' : ℝ × ℝ → V → AlmostComplexStructure V} {R₁ R₁' : ℝ}
    (hJeq : ∀ q (ζ : ℝ × ℝ), R₁ ≤ ζ.1 → J (positiveEndChart q ζ) = Je q ζ.2)
    (hJeq' : ∀ q (ζ : ℝ × ℝ), R₁' ≤ ζ.1 → J' (positiveEndChart q ζ) = Je q ζ.2)
    {Ks Kt Ks' Kt' : ℝ × ℝ → V → ℝ}
    (hK : ∀ q, ∀ z ∈ thricePuncturedSphereReal, R₁ ≤ (positiveEndCoord q z).1 →
      Ks z = (fun x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x 1) ∧
        Kt z = fun x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x Complex.I)
    (hK' : ∀ q, ∀ z ∈ thricePuncturedSphereReal, R₁' ≤ (positiveEndCoord q z).1 →
      Ks' z = (fun x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x 1) ∧
        Kt' z = fun x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x Complex.I)
    {u : ℝ × ℝ → V}
    (hJ : ∀ z ∈ thricePuncturedSphereReal, ContDiffAt ℝ 1
      (fun p : (ℝ × ℝ) × V ↦ (J p.1 p.2).toLinearMap.toContinuousLinearMap) (z, u z))
    (hJ' : ∀ z ∈ thricePuncturedSphereReal, ContDiffAt ℝ 1
      (fun p : (ℝ × ℝ) × V ↦ (J' p.1 p.2).toLinearMap.toContinuousLinearMap) (z, u z))
    (hKs : ∀ z ∈ thricePuncturedSphereReal, ContDiffAt ℝ 2 (uncurry Ks) (z, u z))
    (hKt : ∀ z ∈ thricePuncturedSphereReal, ContDiffAt ℝ 2 (uncurry Kt) (z, u z))
    (hKs' : ∀ z ∈ thricePuncturedSphereReal, ContDiffAt ℝ 2 (uncurry Ks') (z, u z))
    (hKt' : ∀ z ∈ thricePuncturedSphereReal, ContDiffAt ℝ 2 (uncurry Kt') (z, u z))
    (hJt : ∀ z y, ω.Tames (J z y)) (hJ't : ∀ z y, ω.Tames (J' z y))
    (hc : ∀ z ∈ thricePuncturedSphereReal, ω.Compatible (J z (u z)))
    (hc' : ∀ z ∈ thricePuncturedSphereReal, ω.Compatible (J' z (u z)))
    (hu : ∀ z ∈ thricePuncturedSphereReal, ContDiffAt ℝ 1 u z)
    (hF : ∀ q, ∀ z ∈ thricePuncturedSphereReal, R₁ ≤ (positiveEndCoord q z).1 →
      IsComplexLinearMap (AlmostComplexStructure.product ℝ) (J z (u z))
        (ω.perturbedFDeriv Ks Kt u z : ℝ × ℝ →ₗ[ℝ] V))
    (hux : ∀ q, TendstoUniformlyOn (fun s t ↦ u (positiveEndChart q (s, t))) (x q) atTop
      (Icc 0 1))
    (hδ : ∀ q, TendstoUniformlyOn (fun s t ↦ sliceDefect
      (fun t ↦ ω.hamiltonianVectorField (positiveEndHamiltonian H q t)) (u ∘ positiveEndChart q)
        (s, t)) 0 atTop (Icc 0 1)) :
    (ω.floerConformalSobolevOperator thricePuncturedSphereReal cylindricalWeight
      (fun z y ↦ (J z y).toLinearMap.toContinuousLinearMap) Ks Kt u).IsFredholm ↔
      (ω.floerConformalSobolevOperator thricePuncturedSphereReal cylindricalWeight
        (fun z y ↦ (J' z y).toLinearMap.toContinuousLinearMap) Ks' Kt' u).IsFredholm := by
  refine ⟨fun h ↦ (isFredholm_and_index_eq_of_pairOfPants_data ω hH hHs hX hx hnd hJe hJex hJeq
    hJeq' hK hK' hJ hJ' hKs hKt hKs' hKt' hJt hJ't hc hc' hu hF hux hδ h).1, fun h ↦ ?_⟩
  -- Beyond the height `max R₁ R₁'` of an end the two sets of data agree, so `u` solves the
  -- Floer equation of the second data there.
  have hF' : ∀ q, ∀ z ∈ thricePuncturedSphereReal, max R₁ R₁' ≤ (positiveEndCoord q z).1 →
      IsComplexLinearMap (AlmostComplexStructure.product ℝ) (J' z (u z))
        (ω.perturbedFDeriv Ks' Kt' u z : ℝ × ℝ →ₗ[ℝ] V) := fun q z hz hzR ↦ by
    obtain ⟨hs, ht⟩ := hK q z hz ((le_max_left _ _).trans hzR)
    obtain ⟨hs', ht'⟩ := hK' q z hz ((le_max_right _ _).trans hzR)
    rw [← eq_of_max_le_fst_positiveEndCoord hJeq hJeq' hz hzR,
      ω.perturbedFDeriv_congr u (hs'.trans hs.symm) (ht'.trans ht.symm)]
    exact hF q z hz ((le_max_left _ _).trans hzR)
  exact (isFredholm_and_index_eq_of_pairOfPants_data ω hH hHs hX hx hnd hJe hJex
    (fun q ζ hζ ↦ hJeq' q ζ ((le_max_right _ _).trans hζ)) hJeq
    (fun q z hz hzR ↦ hK' q z hz ((le_max_right _ _).trans hzR)) hK hJ' hJ hKs' hKt' hKs hKt hJ't
    hJt hc' hc hu hF' hux hδ h).1

/-- **The index of the pair-of-pants operator does not depend on the data over the core.** Under
the hypotheses of
`TauCeti.SymplecticForm.isFredholm_floerConformalSobolevOperator_iff_of_pairOfPants_data`, if the
realization `D_u : W^{1,2}_0(S, V) → L²(S, V)` of the linearized Floer operator of the first data is
Fredholm, then that of the second data has the same index. -/
theorem index_floerConformalSobolevOperator_eq_of_pairOfPants_data (ω : SymplecticForm V)
    {H : Puncture → ℝ → V → ℝ} (hH : ∀ q, Periodic (H q) 1)
    (hHs : ∀ q, ContDiff ℝ 2 (uncurry (H q))) {L : Puncture → ℝ≥0}
    (hX : ∀ q, LipschitzWith (L q)
      (ω.timeDependentHamiltonianSuspension (positiveEndHamiltonian H q)))
    {x : Puncture → ℝ → V}
    (hx : ∀ q t, HasDerivAt (x q)
      (ω.hamiltonianVectorField (positiveEndHamiltonian H q t) (x q t)) t)
    (hnd : ∀ q, IsNondegenerateFixedPt 𝓘(ℝ, V)
      (ω.timeDependentHamiltonianFlow (positiveEndHamiltonian H q) (hX q) 0 1) (x q 0))
    {Je : Puncture → ℝ → V → AlmostComplexStructure V}
    (hJe : ∀ q, ContDiff ℝ 1 fun p : ℝ × V ↦ (Je q p.1 p.2).toLinearMap.toContinuousLinearMap)
    (hJex : ∀ q t, ω.Compatible (Je q t (x q t)))
    {J J' : ℝ × ℝ → V → AlmostComplexStructure V} {R₁ R₁' : ℝ}
    (hJeq : ∀ q (ζ : ℝ × ℝ), R₁ ≤ ζ.1 → J (positiveEndChart q ζ) = Je q ζ.2)
    (hJeq' : ∀ q (ζ : ℝ × ℝ), R₁' ≤ ζ.1 → J' (positiveEndChart q ζ) = Je q ζ.2)
    {Ks Kt Ks' Kt' : ℝ × ℝ → V → ℝ}
    (hK : ∀ q, ∀ z ∈ thricePuncturedSphereReal, R₁ ≤ (positiveEndCoord q z).1 →
      Ks z = (fun x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x 1) ∧
        Kt z = fun x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x Complex.I)
    (hK' : ∀ q, ∀ z ∈ thricePuncturedSphereReal, R₁' ≤ (positiveEndCoord q z).1 →
      Ks' z = (fun x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x 1) ∧
        Kt' z = fun x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x Complex.I)
    {u : ℝ × ℝ → V}
    (hJ : ∀ z ∈ thricePuncturedSphereReal, ContDiffAt ℝ 1
      (fun p : (ℝ × ℝ) × V ↦ (J p.1 p.2).toLinearMap.toContinuousLinearMap) (z, u z))
    (hJ' : ∀ z ∈ thricePuncturedSphereReal, ContDiffAt ℝ 1
      (fun p : (ℝ × ℝ) × V ↦ (J' p.1 p.2).toLinearMap.toContinuousLinearMap) (z, u z))
    (hKs : ∀ z ∈ thricePuncturedSphereReal, ContDiffAt ℝ 2 (uncurry Ks) (z, u z))
    (hKt : ∀ z ∈ thricePuncturedSphereReal, ContDiffAt ℝ 2 (uncurry Kt) (z, u z))
    (hKs' : ∀ z ∈ thricePuncturedSphereReal, ContDiffAt ℝ 2 (uncurry Ks') (z, u z))
    (hKt' : ∀ z ∈ thricePuncturedSphereReal, ContDiffAt ℝ 2 (uncurry Kt') (z, u z))
    (hJt : ∀ z y, ω.Tames (J z y)) (hJ't : ∀ z y, ω.Tames (J' z y))
    (hc : ∀ z ∈ thricePuncturedSphereReal, ω.Compatible (J z (u z)))
    (hc' : ∀ z ∈ thricePuncturedSphereReal, ω.Compatible (J' z (u z)))
    (hu : ∀ z ∈ thricePuncturedSphereReal, ContDiffAt ℝ 1 u z)
    (hF : ∀ q, ∀ z ∈ thricePuncturedSphereReal, R₁ ≤ (positiveEndCoord q z).1 →
      IsComplexLinearMap (AlmostComplexStructure.product ℝ) (J z (u z))
        (ω.perturbedFDeriv Ks Kt u z : ℝ × ℝ →ₗ[ℝ] V))
    (hux : ∀ q, TendstoUniformlyOn (fun s t ↦ u (positiveEndChart q (s, t))) (x q) atTop
      (Icc 0 1))
    (hδ : ∀ q, TendstoUniformlyOn (fun s t ↦ sliceDefect
      (fun t ↦ ω.hamiltonianVectorField (positiveEndHamiltonian H q t)) (u ∘ positiveEndChart q)
        (s, t)) 0 atTop (Icc 0 1))
    (h : (ω.floerConformalSobolevOperator thricePuncturedSphereReal cylindricalWeight
        (fun z y ↦ (J z y).toLinearMap.toContinuousLinearMap) Ks Kt u).IsFredholm) :
    (ω.floerConformalSobolevOperator thricePuncturedSphereReal cylindricalWeight
      (fun z y ↦ (J' z y).toLinearMap.toContinuousLinearMap) Ks' Kt' u).index =
      (ω.floerConformalSobolevOperator thricePuncturedSphereReal cylindricalWeight
        (fun z y ↦ (J z y).toLinearMap.toContinuousLinearMap) Ks Kt u).index :=
  (isFredholm_and_index_eq_of_pairOfPants_data ω hH hHs hX hx hnd hJe hJex hJeq hJeq' hK hK' hJ hJ'
    hKs hKt hKs' hKt' hJt hJ't hc hc' hu hF hux hδ h).2

end TauCeti.SymplecticForm
