/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Floer.Continuation.Path
public import TauCeti.Geometry.Symplectic.Floer.PairOfPants.Sobolev.SemiFredholm
import TauCeti.Analysis.Calculus.ContDiff.Prod
import TauCeti.Analysis.Fredholm.ContinuousFamily
import TauCeti.Analysis.Fredholm.SemiFredholm

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
(`TauCeti.SymplecticForm.index_floerConformalSobolevOperator_eq_of_pairOfPants_data`).

The same holds for the map over the core. Let `u'` be a map equal to `u` far out on the ends, with
`u' - u` of class `C³` on `S`, along which the data are regular and `J` is compatible with `ω`; it
need not solve the Floer equation over the core. Then `D_{u'}` is Fredholm exactly when `D_u` is
(`TauCeti.SymplecticForm.isFredholm_floerConformalSobolevOperator_iff_of_pairOfPants_map`), and
then with the same index
(`TauCeti.SymplecticForm.index_floerConformalSobolevOperator_eq_of_pairOfPants_map`). So the
Fredholm property and the index of the pair-of-pants operator only depend on the data and the map
on the ends, and they may be computed for any convenient choice of both over the core.

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
operators with finite-dimensional kernel and closed range, along which the Fredholm property and the
index are constant (`ContinuousOn.isFredholm_of_isPreconnected`,
`ContinuousOn.index_eq_of_isPreconnected`). The continuity holds along every family of data with
fixed end data, parametrized by a subset of a normed space, that is jointly `C¹` (with `C²`
Hamiltonians) along the graph of `u`, where `u` solves the Floer equation of every member on the
ends and its loops converge uniformly along them, with slice defects tending to zero
(`TauCeti.SymplecticForm.continuousOn_floerConformalSobolevOperator_pairOfPants_family`). Far out
on the ends every member of the path of data is the end data
(`TauCeti.SymplecticForm.pathAlmostComplex_pathHamiltonian_eq_pairOfPants_endData`).

Moving the map is moving the data. With `d = u' - u`, the operator along `u'` is the operator along
`u` of the data `J(z, y + d(z))`, `K_s(z, y + d(z))` and `K_t(z, y + d(z)) - ω(∂t d(z), y)`
(`TauCeti.SymplecticForm.floerConformalSobolevOperator_fun_add_eq_comp_add_right`): the target
point is moved by `d(z)`, and the linear correction of `K_t`, whose Hamiltonian vector field is
`-∂t d(z)`, keeps the slice defect `∂t u - X_{K_t}(u)` of the moved map. These data are as regular
along `u` as the original data along `u'`, the correction being `C²` because `d` is `C³`, and they
are the original data wherever `d` vanishes near `z`, in particular far out on the ends. So the
invariance under the data gives the invariance under the map.

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

/-- **Far out on the ends, the path of data between two sets of pair-of-pants data with the same
end data is that end data.** Let `(J, K_s, K_t)` and `(J', K'_s, K'_t)` be data on a space `Z`, read
on `S` along a map `ι : ℝ × ℝ → Z`, for instance the identity or the slice `w ↦ (μ, w)` of a family
of data. If beyond the heights `R₁` and `R₁'` of every end the data read along `ι` are the end data,
a `C¹` family `J_q(t)` in the positive end chart `φ'_q` and the pair-of-pants perturbation of `H`,
then beyond every positive height `R ≥ R₁, R₁'` so is every member `σ` of the path of data between
them (`TauCeti.Floer.pathAlmostComplex`, `TauCeti.Floer.pathHamiltonian`), read along `ι`, and `u`
solves its Floer equation there when it solves that of `(J, K_s, K_t)`. -/
theorem pathAlmostComplex_pathHamiltonian_eq_pairOfPants_endData {J₀ : AlmostComplexStructure V}
    (ω : SymplecticForm V) (h₀ : ω.Compatible J₀) {H : Puncture → ℝ → V → ℝ}
    {Je : Puncture → ℝ → V → AlmostComplexStructure V} {Z : Type*} {ι : ℝ × ℝ → Z}
    {J J' : Z → V → AlmostComplexStructure V} (hJt : ∀ z y, ω.Tames (J z y))
    (hJt' : ∀ z y, ω.Tames (J' z y)) {Ks Kt Ks' Kt' : Z → V → ℝ} {R₁ R₁' R : ℝ}
    (hR₁ : R₁ ≤ R) (hR₁' : R₁' ≤ R) (hR : 0 < R) {u : ℝ × ℝ → V}
    (hJeq : ∀ q (ζ : ℝ × ℝ), R₁ ≤ ζ.1 → J (ι (positiveEndChart q ζ)) = Je q ζ.2)
    (hJeq' : ∀ q (ζ : ℝ × ℝ), R₁' ≤ ζ.1 → J' (ι (positiveEndChart q ζ)) = Je q ζ.2)
    (hK : ∀ q, ∀ z ∈ thricePuncturedSphereReal, R₁ ≤ (positiveEndCoord q z).1 →
      Ks (ι z) = (fun x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x 1) ∧
        Kt (ι z) = fun x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x Complex.I)
    (hK' : ∀ q, ∀ z ∈ thricePuncturedSphereReal, R₁' ≤ (positiveEndCoord q z).1 →
      Ks' (ι z) = (fun x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x 1) ∧
        Kt' (ι z) = fun x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x Complex.I)
    (hF : ∀ q, ∀ z ∈ thricePuncturedSphereReal, R₁ ≤ (positiveEndCoord q z).1 →
      IsComplexLinearMap (AlmostComplexStructure.product ℝ) (J (ι z) (u z))
        (ω.perturbedFDeriv (fun w ↦ Ks (ι w)) (fun w ↦ Kt (ι w)) u z : ℝ × ℝ →ₗ[ℝ] V))
    (σ : ℝ) :
    (∀ q (ζ : ℝ × ℝ), R ≤ ζ.1 →
      pathAlmostComplex h₀ hJt hJt' (σ, ι (positiveEndChart q ζ)) = Je q ζ.2) ∧
    (∀ q, ∀ z ∈ thricePuncturedSphereReal, R ≤ (positiveEndCoord q z).1 →
      pathHamiltonian Ks Ks' (σ, ι z) =
          (fun x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x 1) ∧
        pathHamiltonian Kt Kt' (σ, ι z) =
          fun x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x Complex.I) ∧
    (∀ q, ∀ z ∈ thricePuncturedSphereReal, R ≤ (positiveEndCoord q z).1 →
      IsComplexLinearMap (AlmostComplexStructure.product ℝ)
        (pathAlmostComplex h₀ hJt hJt' (σ, ι z) (u z))
        (ω.perturbedFDeriv (fun w ↦ pathHamiltonian Ks Ks' (σ, ι w))
          (fun w ↦ pathHamiltonian Kt Kt' (σ, ι w)) u z : ℝ × ℝ →ₗ[ℝ] V)) := by
  -- Beyond the height `R` both sets of data are the end data, hence so is the path between them.
  have hend {q : Puncture} {z : ℝ × ℝ} (hz : z ∈ thricePuncturedSphereReal)
      (hzR : R ≤ (positiveEndCoord q z).1) :
      pathAlmostComplex h₀ hJt hJt' (σ, ι z) = J (ι z) ∧
        pathHamiltonian Ks Ks' (σ, ι z) = Ks (ι z) ∧
          pathHamiltonian Kt Kt' (σ, ι z) = Kt (ι z) := by
    have hJz := eq_of_max_le_fst_positiveEndCoord (J := fun w ↦ J (ι w)) (J' := fun w ↦ J' (ι w))
      hJeq hJeq' hz ((max_le hR₁ hR₁').trans hzR)
    obtain ⟨hs, ht⟩ := hK q z hz (hR₁.trans hzR)
    obtain ⟨hs', ht'⟩ := hK' q z hz (hR₁'.trans hzR)
    exact ⟨funext fun y ↦ pathAlmostComplex_of_eq h₀ σ (congrFun hJz y),
      pathHamiltonian_of_eq σ (hs.trans hs'.symm), pathHamiltonian_of_eq σ (ht.trans ht'.symm)⟩
  refine ⟨fun q ζ hζ ↦ ?_, fun q z hz hzR ↦ ?_, fun q z hz hzR ↦ ?_⟩
  · have hz := positiveEndChart_mem_thricePuncturedSphereReal (q := q) (hR.trans_le hζ)
    rw [(hend hz (by rw [fst_positiveEndCoord_positiveEndChart]; exact hζ)).1,
      hJeq q ζ (hR₁.trans hζ)]
  · rw [(hend hz hzR).2.1, (hend hz hzR).2.2]
    exact hK q z hz (hR₁.trans hzR)
  · obtain ⟨hJz, hs, ht⟩ := hend hz hzR
    rw [hJz, ω.perturbedFDeriv_congr u (Ks' := fun w ↦ Ks (ι w)) (Kt' := fun w ↦ Kt (ι w)) hs ht]
    exact hF q z hz (hR₁.trans hzR)

/-- **Continuity of the pair-of-pants operators along a family of data with fixed end data.** Let
`(J_p, K_{s,p}, K_{t,p})`, for `p` in a subset `s` of a normed space `P`, be a family of Floer data
on `S` which beyond the height `R` of every end are the same end data: in the positive end chart
`φ'_q` the structures are a `C¹` family `J_q(t)` and the perturbation is the pair-of-pants
perturbation of period-one Hamiltonians `H_q`. Suppose that the data are `C¹` (with `C²`
Hamiltonians) jointly in the parameter, the domain point and the target point along the graph of a
map `u` which is `C¹` on `S`, at every parameter of `s`, and that beyond the height `R` the map `u`
solves the Floer equation of every member, its loops in each end chart converging uniformly to a
loop `x_q`, continuous on `[0, 1]`, with slice defects tending uniformly to zero. Then the
realizations `D_u : W^{1,2}_0(S, V) → L²(S, V)` of the linearized Floer operators of the members
depend continuously on `p ∈ s` in the operator norm. -/
theorem continuousOn_floerConformalSobolevOperator_pairOfPants_family (ω : SymplecticForm V)
    {H : Puncture → ℝ → V → ℝ} (hH : ∀ q, Periodic (H q) 1)
    (hHs : ∀ q, ContDiff ℝ 2 (uncurry (H q))) {x : Puncture → ℝ → V}
    (hx : ∀ q, ContinuousOn (x q) (Icc 0 1)) {Je : Puncture → ℝ → V → AlmostComplexStructure V}
    (hJe : ∀ q, ContDiff ℝ 1 fun p : ℝ × V ↦ (Je q p.1 p.2).toLinearMap.toContinuousLinearMap)
    {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P] {s : Set P}
    {J : P × (ℝ × ℝ) → V → AlmostComplexStructure V} {Ks Kt : P × (ℝ × ℝ) → V → ℝ} {R : ℝ}
    (hJeq : ∀ p ∈ s, ∀ q (ζ : ℝ × ℝ), R ≤ ζ.1 → J (p, positiveEndChart q ζ) = Je q ζ.2)
    (hK : ∀ p ∈ s, ∀ q, ∀ z ∈ thricePuncturedSphereReal, R ≤ (positiveEndCoord q z).1 →
      Ks (p, z) = (fun x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x 1) ∧
        Kt (p, z) = fun x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x Complex.I)
    {u : ℝ × ℝ → V}
    (hJ : ∀ p ∈ s, ∀ z ∈ thricePuncturedSphereReal, ContDiffAt ℝ 1
      (fun q : (P × (ℝ × ℝ)) × V ↦ (J q.1 q.2).toLinearMap.toContinuousLinearMap) ((p, z), u z))
    (hKs : ∀ p ∈ s, ∀ z ∈ thricePuncturedSphereReal, ContDiffAt ℝ 2 (uncurry Ks) ((p, z), u z))
    (hKt : ∀ p ∈ s, ∀ z ∈ thricePuncturedSphereReal, ContDiffAt ℝ 2 (uncurry Kt) ((p, z), u z))
    (hu : ∀ z ∈ thricePuncturedSphereReal, ContDiffAt ℝ 1 u z)
    (hF : ∀ p ∈ s, ∀ q, ∀ z ∈ thricePuncturedSphereReal, R ≤ (positiveEndCoord q z).1 →
      IsComplexLinearMap (AlmostComplexStructure.product ℝ) (J (p, z) (u z))
        (ω.perturbedFDeriv (fun w ↦ Ks (p, w)) (fun w ↦ Kt (p, w)) u z : ℝ × ℝ →ₗ[ℝ] V))
    (hux : ∀ q, TendstoUniformlyOn (fun s t ↦ u (positiveEndChart q (s, t))) (x q) atTop
      (Icc 0 1))
    (hδ : ∀ q, TendstoUniformlyOn (fun s t ↦ sliceDefect
      (fun t ↦ ω.hamiltonianVectorField (positiveEndHamiltonian H q t)) (u ∘ positiveEndChart q)
        (s, t)) 0 atTop (Icc 0 1)) :
    ContinuousOn (fun p ↦ ω.floerConformalSobolevOperator thricePuncturedSphereReal
      cylindricalWeight (fun z y ↦ (J (p, z) y).toLinearMap.toContinuousLinearMap)
      (fun z ↦ Ks (p, z)) (fun z ↦ Kt (p, z)) u) s := by
  -- The data change only over the compact truncation `S_R`, a subset of `S`.
  have hR := preimage_truncation_subset_thricePuncturedSphereReal R
  refine ω.continuousOn_floerConformalSobolevOperator_family
    isOpen_thricePuncturedSphereReal.measurableSet (isCompact_preimage_truncation R)
    (J := fun p y ↦ (J p y).toLinearMap.toContinuousLinearMap)
    (fun p hp z hz ↦ hJ p hp z (hR hz)) (fun p hp z hz ↦ hKs p hp z (hR hz))
    (fun p hp z hz ↦ hKt p hp z (hR hz)) (fun z hz ↦ hu z (hR hz))
    (fun z hz ↦ isWeight_cylindricalWeight.continuousOn.continuousAt
      (isOpen_thricePuncturedSphereReal.mem_nhds (hR hz)))
    (fun z hz ↦ isWeight_cylindricalWeight.pos _ (hR hz))
    (fun p hp p' hp' z hz hzK ↦ ?_) fun p hp ↦ ?_
  -- Off the truncation `S_R` every member is the end data.
  · obtain ⟨q, hq⟩ := exists_lt_fst_positiveEndCoord_of_notMem_truncation hz hzK
    obtain ⟨hs, ht⟩ := hK p hp q z hz hq.le
    obtain ⟨hs', ht'⟩ := hK p' hp' q z hz hq.le
    have hJz : J (p, z) = J (p', z) :=
      eq_of_max_le_fst_positiveEndCoord (J := fun w ↦ J (p, w)) (J' := fun w ↦ J (p', w))
        (hJeq p hp) (hJeq p' hp') hz (by simpa using hq.le)
    exact ⟨by rw [hJz], hs.trans hs'.symm, ht.trans ht'.symm⟩
  · exact ω.memLp_floerConformalJetCoeff_pairOfPants_of_tendstoUniformlyOn hH hHs hx hJe
      (J := fun z ↦ J (p, z)) (hJeq p hp) (hK p hp)
      (fun z hz ↦ (hJ p hp z hz).comp_prodMap_prodMk_right)
      (fun z hz ↦ (hKs p hp z hz).comp_prodMap_prodMk_right)
      (fun z hz ↦ (hKt p hp z hz).comp_prodMap_prodMk_right) hu (hF p hp) hux hδ

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
  -- The data at a fixed `μ` are regular along `u`: each is a slice of the family.
  have hJμ (μ : ℝ) (z : ℝ × ℝ) (hz : z ∈ S) : ContDiffAt ℝ 1
      (fun p : (ℝ × ℝ) × V ↦ (J (μ, p.1) p.2).toLinearMap.toContinuousLinearMap) (z, u z) :=
    (hJ μ z hz).comp_prodMap_prodMk_right
  have hKsμ (μ : ℝ) (z : ℝ × ℝ) (hz : z ∈ S) :
      ContDiffAt ℝ 2 (uncurry fun w ↦ Ks (μ, w)) (z, u z) :=
    (hKs μ z hz).comp_prodMap_prodMk_right
  have hKtμ (μ : ℝ) (z : ℝ × ℝ) (hz : z ∈ S) :
      ContDiffAt ℝ 2 (uncurry fun w ↦ Kt (μ, w)) (z, u z) :=
    (hKt μ z hz).comp_prodMap_prodMk_right
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
      (fun μ _ ↦ hJeq μ) (fun μ _ ↦ hK μ) (fun μ _ ↦ hJ μ) (fun μ _ ↦ hKs μ) (fun μ _ ↦ hKt μ) hu
      (fun μ _ ↦ hF μ) hux hδ
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
  -- Beyond the height `R` of an end, every member of the path is the end data.
  have hend := pathAlmostComplex_pathHamiltonian_eq_pairOfPants_endData ω h₀ (ι := fun z ↦ z)
    hJt hJ't hR₁ hR₁'
    (zero_lt_one.trans_le (le_max_right _ _)) hJeq hJeq' hK hK' hF
  have key := isFredholm_and_index_eq_of_family ω hH hHs hX hx hnd hJe hJex
    (J := pathAlmostComplex h₀ hJt hJ't) (Ks := pathHamiltonian Ks Ks')
    (Kt := pathHamiltonian Kt Kt') (R := R) (fun μ ↦ (hend μ).1) (fun μ ↦ (hend μ).2.1)
    (fun μ z hz ↦ contDiffAt_pathAlmostComplex h₀ hJt hJ't (p := (μ, z)) (hJ z hz) (hJ' z hz))
    (fun μ z hz ↦ contDiffAt_pathHamiltonian (p := (μ, z)) (hKs z hz) (hKs' z hz))
    (fun μ z hz ↦ contDiffAt_pathHamiltonian (p := (μ, z)) (hKt z hz) (hKt' z hz)) hu
    (fun μ z hz ↦ compatible_pathAlmostComplex h₀ (hc z hz) (hc' z hz)) (fun μ ↦ (hend μ).2.2)
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

/-! ### Changing the map over the core -/

namespace TauCeti.SymplecticForm

open Floer ConformalSobolev

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]

omit [FiniteDimensional ℝ V] in
/-- If two maps agree on `S` beyond the height `R₀` of every end, their difference and its
derivative vanish at every point of `S` beyond the height `R₀` of some end. -/
private theorem sub_eq_zero_and_fderiv_sub_eq_zero_of_lt_fst_positiveEndCoord
    {u u' : ℝ × ℝ → V} {R₀ : ℝ}
    (huu' : ∀ q, ∀ z ∈ thricePuncturedSphereReal, R₀ ≤ (positiveEndCoord q z).1 → u' z = u z)
    {q : Puncture} {z : ℝ × ℝ} (hz : z ∈ thricePuncturedSphereReal)
    (hR : R₀ < (positiveEndCoord q z).1) :
    u' z - u z = 0 ∧ fderiv ℝ (fun w ↦ u' w - u w) z = 0 := by
  have hc := continuousAt_fst_positiveEndCoord q
    (ne_endCenter (mem_thricePuncturedSphereReal_iff.1 hz) q)
  have hev : (fun w ↦ u' w - u w) =ᶠ[𝓝 z] 0 := by
    filter_upwards [isOpen_thricePuncturedSphereReal.mem_nhds hz, hc.eventually (lt_mem_nhds hR)]
      with w hw hwR
    simp [huu' q w hw hwR.le]
  exact ⟨hev.eq_of_nhds, by rw [hev.fderiv_eq]; simp⟩

/-- For a `C³` map `d`, the linear functions `ω(∂t d(z), ·)` form a `C²` function of `(z, y)`. -/
private theorem contDiffAt_apply_fderiv_stdComplexLineImag (ω : SymplecticForm V)
    {d : ℝ × ℝ → V} {z : ℝ × ℝ} (y : V) (hd : ContDiffAt ℝ 3 d z) :
    ContDiffAt ℝ 2 (fun p : (ℝ × ℝ) × V ↦ ω (fderiv ℝ d p.1 stdComplexLineImag) p.2) (z, y) := by
  have hdt : ContDiffAt ℝ 2 ((fun w ↦ fderiv ℝ d w stdComplexLineImag) ∘ Prod.fst) (z, y) :=
    (((hd.fderiv_right (m := 2) (by norm_num)).clm_apply contDiffAt_const).comp (z, y)
      contDiffAt_fst)
  exact ω.contDiffAt_apply_comp hdt contDiffAt_snd

/-- Along a map `u'` with `u' - u` of class `C³` on `S`, the pair-of-pants operator is the operator
along `u` of the data read at the target point moved by `u' - u`, with `K_t` corrected by
`-ω(∂t (u' - u), ·)`
(`TauCeti.SymplecticForm.floerConformalSobolevOperator_fun_add_eq_comp_add_right`). -/
private theorem floerConformalSobolevOperator_pairOfPants_eq_of_sub (ω : SymplecticForm V)
    {J : ℝ × ℝ → V → AlmostComplexStructure V} {Ks Kt : ℝ × ℝ → V → ℝ} {u u' : ℝ × ℝ → V}
    (hu : ∀ z ∈ thricePuncturedSphereReal, ContDiffAt ℝ 1 u z)
    (hd : ∀ z ∈ thricePuncturedSphereReal, ContDiffAt ℝ 3 (fun w ↦ u' w - u w) z)
    (hKt' : ∀ z ∈ thricePuncturedSphereReal, ContDiffAt ℝ 2 (uncurry Kt) (z, u' z)) :
    ω.floerConformalSobolevOperator thricePuncturedSphereReal cylindricalWeight
        (fun z y ↦ (J z y).toLinearMap.toContinuousLinearMap) Ks Kt u' =
      ω.floerConformalSobolevOperator thricePuncturedSphereReal cylindricalWeight
        (fun z y ↦ (J z (y + (u' z - u z))).toLinearMap.toContinuousLinearMap)
        (fun z y ↦ Ks z (y + (u' z - u z)))
        (fun z y ↦ Kt z (y + (u' z - u z)) -
          ω (fderiv ℝ (fun w ↦ u' w - u w) z stdComplexLineImag) y) u := by
  have hud (z : ℝ × ℝ) : u z + (u' z - u z) = u' z := add_sub_cancel _ _
  have hKtd (z : ℝ × ℝ) (hz : z ∈ thricePuncturedSphereReal) :
      ∀ᶠ y in 𝓝 (u z + (u' z - u z)), DifferentiableAt ℝ (Kt z) y := by
    have h : ContDiffAt ℝ 2 (Kt z) (u z + (u' z - u z)) := by
      rw [hud]; exact (hKt' z hz).comp (u' z) (contDiffAt_const.prodMk contDiffAt_id)
    exact (h.eventually (by simp)).mono fun y hy ↦ hy.differentiableAt (by norm_num)
  conv_lhs => rw [show u' = fun w ↦ u w + (u' w - u w) from funext fun w ↦ (hud w).symm]
  exact ω.floerConformalSobolevOperator_fun_add_eq_comp_add_right
    isOpen_thricePuncturedSphereReal.measurableSet _ Ks Kt
    (fun z hz ↦ (hu z hz).differentiableAt one_ne_zero)
    (fun z hz ↦ (hd z hz).differentiableAt (by norm_num)) hKtd

/-- The Fredholm property and the index of the pair-of-pants operator along `u'` and along `u`
agree, for maps `u` and `u'` equal on the ends. This is
`isFredholm_floerConformalSobolevOperator_iff_of_pairOfPants_data` and
`index_floerConformalSobolevOperator_eq_of_pairOfPants_data` for the data read at the moved target
point `y + d(z)`, `d = u' - u`, with `K_t` corrected by `-ω(∂t d(z), ·)`: along `u` these data have
the operator of the original data along `u'`
(`floerConformalSobolevOperator_fun_add_eq_comp_add_right`), and they agree with the original data
where `d` vanishes near `z`, in particular far out on the ends. -/
private theorem isFredholm_iff_and_index_eq_of_pairOfPants_map (ω : SymplecticForm V)
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
    {J : ℝ × ℝ → V → AlmostComplexStructure V} {R₁ : ℝ}
    (hJeq : ∀ q (ζ : ℝ × ℝ), R₁ ≤ ζ.1 → J (positiveEndChart q ζ) = Je q ζ.2)
    {Ks Kt : ℝ × ℝ → V → ℝ}
    (hK : ∀ q, ∀ z ∈ thricePuncturedSphereReal, R₁ ≤ (positiveEndCoord q z).1 →
      Ks z = (fun x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x 1) ∧
        Kt z = fun x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x Complex.I)
    {u u' : ℝ × ℝ → V} {R₀ : ℝ}
    (huu' : ∀ q, ∀ z ∈ thricePuncturedSphereReal, R₀ ≤ (positiveEndCoord q z).1 → u' z = u z)
    (hJ : ∀ z ∈ thricePuncturedSphereReal, ContDiffAt ℝ 1
      (fun p : (ℝ × ℝ) × V ↦ (J p.1 p.2).toLinearMap.toContinuousLinearMap) (z, u z))
    (hJ' : ∀ z ∈ thricePuncturedSphereReal, ContDiffAt ℝ 1
      (fun p : (ℝ × ℝ) × V ↦ (J p.1 p.2).toLinearMap.toContinuousLinearMap) (z, u' z))
    (hKs : ∀ z ∈ thricePuncturedSphereReal, ContDiffAt ℝ 2 (uncurry Ks) (z, u z))
    (hKt : ∀ z ∈ thricePuncturedSphereReal, ContDiffAt ℝ 2 (uncurry Kt) (z, u z))
    (hKs' : ∀ z ∈ thricePuncturedSphereReal, ContDiffAt ℝ 2 (uncurry Ks) (z, u' z))
    (hKt' : ∀ z ∈ thricePuncturedSphereReal, ContDiffAt ℝ 2 (uncurry Kt) (z, u' z))
    (hJt : ∀ z y, ω.Tames (J z y))
    (hc : ∀ z ∈ thricePuncturedSphereReal, ω.Compatible (J z (u z)))
    (hc' : ∀ z ∈ thricePuncturedSphereReal, ω.Compatible (J z (u' z)))
    (hu : ∀ z ∈ thricePuncturedSphereReal, ContDiffAt ℝ 1 u z)
    (hd : ∀ z ∈ thricePuncturedSphereReal, ContDiffAt ℝ 3 (fun w ↦ u' w - u w) z)
    (hF : ∀ q, ∀ z ∈ thricePuncturedSphereReal, R₁ ≤ (positiveEndCoord q z).1 →
      IsComplexLinearMap (AlmostComplexStructure.product ℝ) (J z (u z))
        (ω.perturbedFDeriv Ks Kt u z : ℝ × ℝ →ₗ[ℝ] V))
    (hux : ∀ q, TendstoUniformlyOn (fun s t ↦ u (positiveEndChart q (s, t))) (x q) atTop
      (Icc 0 1))
    (hδ : ∀ q, TendstoUniformlyOn (fun s t ↦ sliceDefect
      (fun t ↦ ω.hamiltonianVectorField (positiveEndHamiltonian H q t)) (u ∘ positiveEndChart q)
        (s, t)) 0 atTop (Icc 0 1)) :
    ((ω.floerConformalSobolevOperator thricePuncturedSphereReal cylindricalWeight
        (fun z y ↦ (J z y).toLinearMap.toContinuousLinearMap) Ks Kt u').IsFredholm ↔
      (ω.floerConformalSobolevOperator thricePuncturedSphereReal cylindricalWeight
        (fun z y ↦ (J z y).toLinearMap.toContinuousLinearMap) Ks Kt u).IsFredholm) ∧
    ((ω.floerConformalSobolevOperator thricePuncturedSphereReal cylindricalWeight
        (fun z y ↦ (J z y).toLinearMap.toContinuousLinearMap) Ks Kt u).IsFredholm →
      (ω.floerConformalSobolevOperator thricePuncturedSphereReal cylindricalWeight
        (fun z y ↦ (J z y).toLinearMap.toContinuousLinearMap) Ks Kt u').index =
      (ω.floerConformalSobolevOperator thricePuncturedSphereReal cylindricalWeight
        (fun z y ↦ (J z y).toLinearMap.toContinuousLinearMap) Ks Kt u).index) := by
  set d : ℝ × ℝ → V := fun w ↦ u' w - u w
  have hud (z : ℝ × ℝ) : u z + d z = u' z := by simp [d]
  -- The data read at the moved target point `y + d(z)`, with `K_t` corrected.
  set J' : ℝ × ℝ → V → AlmostComplexStructure V := fun w y ↦ J w (y + d w)
  set Ks' : ℝ × ℝ → V → ℝ := fun w y ↦ Ks w (y + d w)
  set Kt' : ℝ × ℝ → V → ℝ :=
    fun w y ↦ Kt w (y + d w) - ω (fderiv ℝ d w stdComplexLineImag) y
  -- Beyond the height `R₁'` of an end `d` vanishes near `z`: the new data are the original ones.
  set R₁' := max R₁ (max R₀ 0 + 1)
  have hdata (q : Puncture) (z : ℝ × ℝ) (hz : z ∈ thricePuncturedSphereReal)
      (hzR : R₁' ≤ (positiveEndCoord q z).1) : J' z = J z ∧ Ks' z = Ks z ∧ Kt' z = Kt z := by
    obtain ⟨hd₀, hd₁⟩ :=
      sub_eq_zero_and_fderiv_sub_eq_zero_of_lt_fst_positiveEndCoord (q := q) huu' hz
      (by linarith [le_max_left R₀ 0, le_max_right R₁ (max R₀ 0 + 1)])
    refine ⟨funext fun y ↦ ?_, funext fun y ↦ ?_, funext fun y ↦ ?_⟩ <;>
      simp [J', Ks', Kt', d, hd₀, hd₁]
  have hJeq' (q : Puncture) (ζ : ℝ × ℝ) (hζ : R₁' ≤ ζ.1) :
      J' (positiveEndChart q ζ) = Je q ζ.2 := by
    have hpos : 0 < ζ.1 := by linarith [le_max_right R₀ 0, le_max_right R₁ (max R₀ 0 + 1)]
    rw [(hdata q _ (positiveEndChart_mem_thricePuncturedSphereReal hpos)
      (by rwa [fst_positiveEndCoord_positiveEndChart])).1,
      hJeq q ζ ((le_max_left _ _).trans hζ)]
  have hK' (q : Puncture) (z : ℝ × ℝ) (hz : z ∈ thricePuncturedSphereReal)
      (hzR : R₁' ≤ (positiveEndCoord q z).1) :
      Ks' z = (fun x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x 1) ∧
        Kt' z =
          fun x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x Complex.I := by
    rw [(hdata q z hz hzR).2.1, (hdata q z hz hzR).2.2]
    exact hK q z hz ((le_max_left _ _).trans hzR)
  -- The new data are as regular along `u` as the original data along `u'`.
  have hJ'' (z : ℝ × ℝ) (hz : z ∈ thricePuncturedSphereReal) : ContDiffAt ℝ 1
      (fun p : (ℝ × ℝ) × V ↦ (J' p.1 p.2).toLinearMap.toContinuousLinearMap) (z, u z) :=
    ContDiffAt.comp_prodMk_add (by rw [hud]; exact hJ' z hz) ((hd z hz).of_le (by norm_num))
  have hKs'' (z : ℝ × ℝ) (hz : z ∈ thricePuncturedSphereReal) :
      ContDiffAt ℝ 2 (uncurry Ks') (z, u z) :=
    ContDiffAt.comp_prodMk_add (by rw [hud]; exact hKs' z hz) ((hd z hz).of_le (by norm_num))
  have hKt'' (z : ℝ × ℝ) (hz : z ∈ thricePuncturedSphereReal) :
      ContDiffAt ℝ 2 (uncurry Kt') (z, u z) :=
    (ContDiffAt.comp_prodMk_add (by rw [hud]; exact hKt' z hz) ((hd z hz).of_le (by norm_num))).sub
      (contDiffAt_apply_fderiv_stdComplexLineImag ω (u z) (hd z hz))
  have hc'' (z : ℝ × ℝ) (hz : z ∈ thricePuncturedSphereReal) : ω.Compatible (J' z (u z)) := by
    simpa only [J', hud] using hc' z hz
  -- Along `u` the new data have the operator of the original data along `u'`.
  rw [floerConformalSobolevOperator_pairOfPants_eq_of_sub ω hu hd hKt']
  exact ⟨(isFredholm_floerConformalSobolevOperator_iff_of_pairOfPants_data ω hH hHs hX hx hnd hJe
      hJex hJeq hJeq' hK hK' hJ hJ'' hKs hKt hKs'' hKt'' hJt (fun z y ↦ hJt z (y + d z)) hc hc''
      hu hF hux hδ).symm,
    index_floerConformalSobolevOperator_eq_of_pairOfPants_data ω hH hHs hX hx hnd hJe hJex hJeq
      hJeq' hK hK' hJ hJ'' hKs hKt hKs'' hKt'' hJt (fun z y ↦ hJt z (y + d z)) hc hc'' hu hF hux
      hδ⟩


/-- **The Fredholm property of the pair-of-pants operator does not depend on the map over the
core.** Let `u` satisfy the hypotheses of
`TauCeti.SymplecticForm.isFredholm_floerConformalSobolevOperator_iff_of_pairOfPants_data` for the
Floer data `(J, K_s, K_t)`: far out on the ends the data are the end data, `u` solves the Floer
equation there and converges to nondegenerate orbits. Let `u'` be a map equal to `u` on `S` beyond
the height `R₀` of every end, with `u' - u` of class `C³` on `S`, along which `J` is `C¹` and
compatible with `ω` and the Hamiltonians are `C²`. The map `u'` need not solve the Floer equation
over the core. Then the realization `D_{u'} : W^{1,2}_0(S, V) → L²(S, V)` of the linearized Floer
operator along `u'` is Fredholm if and only if `D_u` is. -/
theorem isFredholm_floerConformalSobolevOperator_iff_of_pairOfPants_map (ω : SymplecticForm V)
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
    {J : ℝ × ℝ → V → AlmostComplexStructure V} {R₁ : ℝ}
    (hJeq : ∀ q (ζ : ℝ × ℝ), R₁ ≤ ζ.1 → J (positiveEndChart q ζ) = Je q ζ.2)
    {Ks Kt : ℝ × ℝ → V → ℝ}
    (hK : ∀ q, ∀ z ∈ thricePuncturedSphereReal, R₁ ≤ (positiveEndCoord q z).1 →
      Ks z = (fun x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x 1) ∧
        Kt z = fun x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x Complex.I)
    {u u' : ℝ × ℝ → V} {R₀ : ℝ}
    (huu' : ∀ q, ∀ z ∈ thricePuncturedSphereReal, R₀ ≤ (positiveEndCoord q z).1 → u' z = u z)
    (hJ : ∀ z ∈ thricePuncturedSphereReal, ContDiffAt ℝ 1
      (fun p : (ℝ × ℝ) × V ↦ (J p.1 p.2).toLinearMap.toContinuousLinearMap) (z, u z))
    (hJ' : ∀ z ∈ thricePuncturedSphereReal, ContDiffAt ℝ 1
      (fun p : (ℝ × ℝ) × V ↦ (J p.1 p.2).toLinearMap.toContinuousLinearMap) (z, u' z))
    (hKs : ∀ z ∈ thricePuncturedSphereReal, ContDiffAt ℝ 2 (uncurry Ks) (z, u z))
    (hKt : ∀ z ∈ thricePuncturedSphereReal, ContDiffAt ℝ 2 (uncurry Kt) (z, u z))
    (hKs' : ∀ z ∈ thricePuncturedSphereReal, ContDiffAt ℝ 2 (uncurry Ks) (z, u' z))
    (hKt' : ∀ z ∈ thricePuncturedSphereReal, ContDiffAt ℝ 2 (uncurry Kt) (z, u' z))
    (hJt : ∀ z y, ω.Tames (J z y))
    (hc : ∀ z ∈ thricePuncturedSphereReal, ω.Compatible (J z (u z)))
    (hc' : ∀ z ∈ thricePuncturedSphereReal, ω.Compatible (J z (u' z)))
    (hu : ∀ z ∈ thricePuncturedSphereReal, ContDiffAt ℝ 1 u z)
    (hd : ∀ z ∈ thricePuncturedSphereReal, ContDiffAt ℝ 3 (fun w ↦ u' w - u w) z)
    (hF : ∀ q, ∀ z ∈ thricePuncturedSphereReal, R₁ ≤ (positiveEndCoord q z).1 →
      IsComplexLinearMap (AlmostComplexStructure.product ℝ) (J z (u z))
        (ω.perturbedFDeriv Ks Kt u z : ℝ × ℝ →ₗ[ℝ] V))
    (hux : ∀ q, TendstoUniformlyOn (fun s t ↦ u (positiveEndChart q (s, t))) (x q) atTop
      (Icc 0 1))
    (hδ : ∀ q, TendstoUniformlyOn (fun s t ↦ sliceDefect
      (fun t ↦ ω.hamiltonianVectorField (positiveEndHamiltonian H q t)) (u ∘ positiveEndChart q)
        (s, t)) 0 atTop (Icc 0 1)) :
    (ω.floerConformalSobolevOperator thricePuncturedSphereReal cylindricalWeight
        (fun z y ↦ (J z y).toLinearMap.toContinuousLinearMap) Ks Kt u').IsFredholm ↔
      (ω.floerConformalSobolevOperator thricePuncturedSphereReal cylindricalWeight
        (fun z y ↦ (J z y).toLinearMap.toContinuousLinearMap) Ks Kt u).IsFredholm :=
  (isFredholm_iff_and_index_eq_of_pairOfPants_map ω hH hHs hX hx hnd hJe hJex hJeq hK huu' hJ
    hJ' hKs hKt hKs' hKt' hJt hc hc' hu hd hF hux hδ).1

/-- **The index of the pair-of-pants operator does not depend on the map over the core.** Under
the hypotheses of
`TauCeti.SymplecticForm.isFredholm_floerConformalSobolevOperator_iff_of_pairOfPants_map`, if the
realization `D_u : W^{1,2}_0(S, V) → L²(S, V)` of the linearized Floer operator along `u` is
Fredholm, then the realization `D_{u'}` along any map `u'` equal to `u` on the ends has the same
index. -/
theorem index_floerConformalSobolevOperator_eq_of_pairOfPants_map (ω : SymplecticForm V)
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
    {J : ℝ × ℝ → V → AlmostComplexStructure V} {R₁ : ℝ}
    (hJeq : ∀ q (ζ : ℝ × ℝ), R₁ ≤ ζ.1 → J (positiveEndChart q ζ) = Je q ζ.2)
    {Ks Kt : ℝ × ℝ → V → ℝ}
    (hK : ∀ q, ∀ z ∈ thricePuncturedSphereReal, R₁ ≤ (positiveEndCoord q z).1 →
      Ks z = (fun x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x 1) ∧
        Kt z = fun x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x Complex.I)
    {u u' : ℝ × ℝ → V} {R₀ : ℝ}
    (huu' : ∀ q, ∀ z ∈ thricePuncturedSphereReal, R₀ ≤ (positiveEndCoord q z).1 → u' z = u z)
    (hJ : ∀ z ∈ thricePuncturedSphereReal, ContDiffAt ℝ 1
      (fun p : (ℝ × ℝ) × V ↦ (J p.1 p.2).toLinearMap.toContinuousLinearMap) (z, u z))
    (hJ' : ∀ z ∈ thricePuncturedSphereReal, ContDiffAt ℝ 1
      (fun p : (ℝ × ℝ) × V ↦ (J p.1 p.2).toLinearMap.toContinuousLinearMap) (z, u' z))
    (hKs : ∀ z ∈ thricePuncturedSphereReal, ContDiffAt ℝ 2 (uncurry Ks) (z, u z))
    (hKt : ∀ z ∈ thricePuncturedSphereReal, ContDiffAt ℝ 2 (uncurry Kt) (z, u z))
    (hKs' : ∀ z ∈ thricePuncturedSphereReal, ContDiffAt ℝ 2 (uncurry Ks) (z, u' z))
    (hKt' : ∀ z ∈ thricePuncturedSphereReal, ContDiffAt ℝ 2 (uncurry Kt) (z, u' z))
    (hJt : ∀ z y, ω.Tames (J z y))
    (hc : ∀ z ∈ thricePuncturedSphereReal, ω.Compatible (J z (u z)))
    (hc' : ∀ z ∈ thricePuncturedSphereReal, ω.Compatible (J z (u' z)))
    (hu : ∀ z ∈ thricePuncturedSphereReal, ContDiffAt ℝ 1 u z)
    (hd : ∀ z ∈ thricePuncturedSphereReal, ContDiffAt ℝ 3 (fun w ↦ u' w - u w) z)
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
        (fun z y ↦ (J z y).toLinearMap.toContinuousLinearMap) Ks Kt u').index =
      (ω.floerConformalSobolevOperator thricePuncturedSphereReal cylindricalWeight
        (fun z y ↦ (J z y).toLinearMap.toContinuousLinearMap) Ks Kt u).index :=
  (isFredholm_iff_and_index_eq_of_pairOfPants_map ω hH hHs hX hx hnd hJe hJex hJeq hK huu' hJ
    hJ' hKs hKt hKs' hKt' hJt hc hc' hu hd hF hux hδ).2 h

end TauCeti.SymplecticForm
