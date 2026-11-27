/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Fredholm.DeterminantLine.Homotopy
public import TauCeti.Geometry.Symplectic.Floer.PairOfPants.Sobolev.Invariance
import TauCeti.Analysis.Calculus.ContDiff.Prod
import TauCeti.Geometry.Symplectic.Floer.Continuation.Path

/-!
# Orientation transport for the pair-of-pants operator along paths of core data

Let `u` be a `C¹` map on the pair of pants `S = ℂ ∖ {0, 1}` into a finite-dimensional symplectic
inner product space `(V, ω)`, and let `D_u : W^{1,2}_0(S, V) → L²(S, V)` be the realization
(`TauCeti.SymplecticForm.floerConformalSobolevOperator` for the cylindrical weight) of the
linearized Floer operator along `u` for Floer data `(J, K_s, K_t)` on `S`. Far out on every end `q`
the data are fixed end data: a `C¹` family `J_q(t)` of almost complex structures and the
pair-of-pants perturbation of period-one Hamiltonians `H_q`, along which `u` solves the Floer
equation and converges to nondegenerate one-periodic orbits. When `D_u` is Fredholm it has a
determinant line `det (ker D_u) ⊗ (det (coker D_u))^*`, and the moduli spaces of pairs of pants are
oriented by orienting these lines. The orientations must be compared for different choices of the
data over the core of `S`.

Along a path `μ ↦ (J_μ, K_{s,μ}, K_{t,μ})` of such data, `C¹` jointly in the parameter (with `C²`
Hamiltonians), the operators `D_u` depend continuously on `μ` in the operator norm
(`TauCeti.SymplecticForm.continuousOn_floerConformalSobolevOperator_pairOfPants_family`), so
orientations of their determinant lines are transported along the path
(`TauCeti.detLineOrientationTransport`). This file proves that the transport depends only on the
endpoints of the path: for two paths of data with the same end data, defined on `[[a, b]]` and
agreeing at `a` and at `b`, the transports from `a` to `b` along the two paths agree, once the
determinant lines of the equal operators at `a` and at `b` are identified. In particular, transport
around a loop of core data is trivial, so the determinant lines of the pair-of-pants operator are
orientable over every loop of data with fixed end data. This is the pair-of-pants counterpart of
`TauCeti.SymplecticForm.detLineOrientationTransport_floerSobolevOperator_congr` for cylinders.

The proof joins the two paths by a homotopy of data relative to the endpoints, at
`(σ, μ) ∈ [0, 1] × [[a, b]]`: the Hamiltonians run along the segment between those of the two paths
(`TauCeti.Floer.pathHamiltonian`), and the almost complex structures along the path of Cayley
coordinates between them relative to a fixed compatible structure
(`TauCeti.Floer.pathAlmostComplex`), so that they stay compatible along `u`. Where the two paths
agree, in particular on the ends, so does every member of the homotopy. Hence the operators of the
homotopy depend continuously on `(σ, μ)`, and each is Fredholm since it has the same end data as the
operator of the first path at `μ`
(`TauCeti.SymplecticForm.isFredholm_floerConformalSobolevOperator_iff_of_pairOfPants_data`).
Orientation transport is invariant under such a homotopy
(`TauCeti.detLineOrientationTransport_eq_of_homotopy_of_eq`).

## Main results

All results are in the namespace `TauCeti.SymplecticForm`.

* `detLineOrientationTransport_floerConformalSobolevOperator_pairOfPants_congr`: orientation
  transport of the determinant lines of the pair-of-pants operator along a path of core data with
  fixed end data depends only on the data at the endpoints.
* `detLineOrientationTransport_floerConformalSobolevOperator_pairOfPants_eq_map`: orientation
  transport around a loop of core data with fixed end data is trivial.

## References

* A. Floer and H. Hofer, *Coherent orientations for periodic orbit problems in symplectic
  geometry*, Math. Z. 212 (1993), 13–38, on orienting the determinant lines of the linearized
  Floer operators through the contractibility of the spaces of data with fixed asymptotics.
* M. Schwarz, *Cohomology operations from S¹-cobordisms in Floer homology*, PhD thesis,
  ETH Zürich (1995), on the Fredholm theory and orientations of the pair-of-pants operator.
* D. McDuff and D. Salamon, *J-holomorphic Curves and Symplectic Topology*, second edition,
  AMS Colloquium Publications 52, 2012, Section A.2 (determinant line bundles).
-/

public section

open Set Function Filter MeasureTheory TauCeti.ThricePuncturedSphere
  TauCeti.ThricePuncturedSphere.Puncture
open scoped NNReal Manifold

namespace TauCeti.SymplecticForm

open Floer ConformalSobolev

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]

section PathData

/-! ### The path of data between two paths of core data -/

variable {ω : SymplecticForm V} {J₀ : AlmostComplexStructure V}
  {J₁ J₂ : ℝ × (ℝ × ℝ) → V → AlmostComplexStructure V} {hJt₁ : ∀ p y, ω.Tames (J₁ p y)}
  {hJt₂ : ∀ p y, ω.Tames (J₂ p y)} {Je : Puncture → ℝ → V → AlmostComplexStructure V} {R μ : ℝ}

/-- Where the almost complex structures of two paths of data at the parameter `μ` are both the end
structures `J_q(t)`, beyond the height `R` of the end `q`, so is every member `σ` of the path of
almost complex structures between them. -/
private theorem pathAlmostComplex_positiveEndChart (h₀ : ω.Compatible J₀)
    (hJeq₁ : ∀ q (ζ : ℝ × ℝ), R ≤ ζ.1 → J₁ (μ, positiveEndChart q ζ) = Je q ζ.2)
    (hJeq₂ : ∀ q (ζ : ℝ × ℝ), R ≤ ζ.1 → J₂ (μ, positiveEndChart q ζ) = Je q ζ.2) (σ : ℝ)
    (q : Puncture) (ζ : ℝ × ℝ) (hζ : R ≤ ζ.1) :
    pathAlmostComplex h₀ hJt₁ hJt₂ (σ, (μ, positiveEndChart q ζ)) = Je q ζ.2 := by
  funext y
  rw [← hJeq₁ q ζ hζ]
  exact pathAlmostComplex_of_eq h₀ σ (by rw [hJeq₁ q ζ hζ, hJeq₂ q ζ hζ])

/-- Beyond the height `R` of an end, where two paths of data are the same end data at the
parameter `μ`, every member `σ` of the path of data between them is the first path at `μ`. -/
private theorem pathData_eq_of_le_fst_positiveEndCoord (h₀ : ω.Compatible J₀)
    {H : Puncture → ℝ → V → ℝ} {Ks₁ Kt₁ Ks₂ Kt₂ : ℝ × (ℝ × ℝ) → V → ℝ}
    (hJeq₁ : ∀ q (ζ : ℝ × ℝ), R ≤ ζ.1 → J₁ (μ, positiveEndChart q ζ) = Je q ζ.2)
    (hJeq₂ : ∀ q (ζ : ℝ × ℝ), R ≤ ζ.1 → J₂ (μ, positiveEndChart q ζ) = Je q ζ.2)
    (hK₁ : ∀ q, ∀ z ∈ thricePuncturedSphereReal, R ≤ (positiveEndCoord q z).1 →
      Ks₁ (μ, z) = (fun x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x 1) ∧
        Kt₁ (μ, z) =
          fun x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x Complex.I)
    (hK₂ : ∀ q, ∀ z ∈ thricePuncturedSphereReal, R ≤ (positiveEndCoord q z).1 →
      Ks₂ (μ, z) = (fun x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x 1) ∧
        Kt₂ (μ, z) =
          fun x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x Complex.I)
    (σ : ℝ) {q : Puncture} {z : ℝ × ℝ} (hz : z ∈ thricePuncturedSphereReal)
    (hzR : R ≤ (positiveEndCoord q z).1) :
    pathAlmostComplex h₀ hJt₁ hJt₂ (σ, (μ, z)) = J₁ (μ, z) ∧
      pathHamiltonian Ks₁ Ks₂ (σ, (μ, z)) = Ks₁ (μ, z) ∧
        pathHamiltonian Kt₁ Kt₂ (σ, (μ, z)) = Kt₁ (μ, z) := by
  obtain ⟨hs₁, ht₁⟩ := hK₁ q z hz hzR
  obtain ⟨hs₂, ht₂⟩ := hK₂ q z hz hzR
  refine ⟨?_, pathHamiltonian_of_eq σ (hs₁.trans hs₂.symm),
    pathHamiltonian_of_eq σ (ht₁.trans ht₂.symm)⟩
  rw [← positiveEndChart_positiveEndCoord q
      (ne_endCenter (mem_thricePuncturedSphereReal_iff.1 hz) q),
    pathAlmostComplex_positiveEndChart h₀ hJeq₁ hJeq₂ σ q _ hzR, hJeq₁ q _ hzR]

/-- The path of almost complex structures between two paths of data, read at the parameter
`(σ, μ)`, is `Cⁿ` at `(((σ, μ), z), y)` when the two paths are `Cⁿ` at `((μ, z), y)`. -/
private theorem contDiffAt_pathAlmostComplex_assoc {n : ℕ∞} (h₀ : ω.Compatible J₀) {p : ℝ × ℝ}
    {z : ℝ × ℝ} {y : V}
    (hJ₁ : ContDiffAt ℝ n (fun r : (ℝ × (ℝ × ℝ)) × V ↦
      (J₁ r.1 r.2).toLinearMap.toContinuousLinearMap) ((p.2, z), y))
    (hJ₂ : ContDiffAt ℝ n (fun r : (ℝ × (ℝ × ℝ)) × V ↦
      (J₂ r.1 r.2).toLinearMap.toContinuousLinearMap) ((p.2, z), y)) :
    ContDiffAt ℝ n (fun r : ((ℝ × ℝ) × (ℝ × ℝ)) × V ↦ (pathAlmostComplex h₀ hJt₁ hJt₂
      (r.1.1.1, (r.1.1.2, r.1.2)) r.2).toLinearMap.toContinuousLinearMap) ((p, z), y) :=
  -- The ascription elaborates the composite before matching it with the statement; matched
  -- against the statement first, `ContDiffAt.comp` would split off the wrong outer map.
  ((contDiffAt_pathAlmostComplex h₀ hJt₁ hJt₂ (p := (p.1, (p.2, z))) hJ₁ hJ₂).comp ((p, z), y)
    ((contDiff_fst.fst.fst.prodMk (contDiff_fst.fst.snd.prodMk contDiff_fst.snd)).prodMk
      contDiff_snd).contDiffAt :)

/-- The segment of Hamiltonians between two paths of data, read at the parameter `(σ, μ)`, is `Cⁿ`
at `(((σ, μ), z), y)` when the two paths are `Cⁿ` at `((μ, z), y)`. -/
private theorem contDiffAt_pathHamiltonian_assoc {W : Type*} [NormedAddCommGroup W]
    [NormedSpace ℝ W] {n : ℕ∞} {K₁ K₂ : ℝ × (ℝ × ℝ) → W → ℝ} {p : ℝ × ℝ} {z : ℝ × ℝ} {y : W}
    (hK₁ : ContDiffAt ℝ n (uncurry K₁) ((p.2, z), y))
    (hK₂ : ContDiffAt ℝ n (uncurry K₂) ((p.2, z), y)) :
    ContDiffAt ℝ n (uncurry fun r : (ℝ × ℝ) × (ℝ × ℝ) ↦
      pathHamiltonian K₁ K₂ (r.1.1, (r.1.2, r.2))) ((p, z), y) :=
  -- The ascription elaborates the composite before matching it with the statement.
  ((contDiffAt_pathHamiltonian (p := (p.1, (p.2, z))) hK₁ hK₂).comp ((p, z), y)
    ((contDiff_fst.fst.fst.prodMk (contDiff_fst.fst.snd.prodMk contDiff_fst.snd)).prodMk
      contDiff_snd).contDiffAt :)

end PathData

/-- The operators of the homotopy of data between two paths of core data with the same end data,
at `(σ, μ) ∈ [0, 1] × [[a, b]]`, depend continuously on `(σ, μ)`. -/
private theorem continuousOn_floerConformalSobolevOperator_pathData (ω : SymplecticForm V)
    {H : Puncture → ℝ → V → ℝ} (hH : ∀ q, Periodic (H q) 1)
    (hHs : ∀ q, ContDiff ℝ 2 (uncurry (H q))) {x : Puncture → ℝ → V}
    (hx : ∀ q, ContinuousOn (x q) (Icc 0 1)) {Je : Puncture → ℝ → V → AlmostComplexStructure V}
    (hJe : ∀ q, ContDiff ℝ 1 fun p : ℝ × V ↦ (Je q p.1 p.2).toLinearMap.toContinuousLinearMap)
    {J₀ : AlmostComplexStructure V} (h₀ : ω.Compatible J₀)
    {J₁ J₂ : ℝ × (ℝ × ℝ) → V → AlmostComplexStructure V} (hJt₁ : ∀ p y, ω.Tames (J₁ p y))
    (hJt₂ : ∀ p y, ω.Tames (J₂ p y)) {Ks₁ Kt₁ Ks₂ Kt₂ : ℝ × (ℝ × ℝ) → V → ℝ} {R : ℝ}
    {u : ℝ × ℝ → V} {a b : ℝ}
    (hJeq₁ : ∀ μ ∈ uIcc a b, ∀ q (ζ : ℝ × ℝ), R ≤ ζ.1 → J₁ (μ, positiveEndChart q ζ) = Je q ζ.2)
    (hJeq₂ : ∀ μ ∈ uIcc a b, ∀ q (ζ : ℝ × ℝ), R ≤ ζ.1 → J₂ (μ, positiveEndChart q ζ) = Je q ζ.2)
    (hK₁ : ∀ μ ∈ uIcc a b, ∀ q, ∀ z ∈ thricePuncturedSphereReal, R ≤ (positiveEndCoord q z).1 →
      Ks₁ (μ, z) = (fun x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x 1) ∧
        Kt₁ (μ, z) =
          fun x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x Complex.I)
    (hK₂ : ∀ μ ∈ uIcc a b, ∀ q, ∀ z ∈ thricePuncturedSphereReal, R ≤ (positiveEndCoord q z).1 →
      Ks₂ (μ, z) = (fun x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x 1) ∧
        Kt₂ (μ, z) =
          fun x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x Complex.I)
    (hJ₁ : ∀ μ ∈ uIcc a b, ∀ z ∈ thricePuncturedSphereReal, ContDiffAt ℝ 1
      (fun p : (ℝ × (ℝ × ℝ)) × V ↦ (J₁ p.1 p.2).toLinearMap.toContinuousLinearMap) ((μ, z), u z))
    (hJ₂ : ∀ μ ∈ uIcc a b, ∀ z ∈ thricePuncturedSphereReal, ContDiffAt ℝ 1
      (fun p : (ℝ × (ℝ × ℝ)) × V ↦ (J₂ p.1 p.2).toLinearMap.toContinuousLinearMap) ((μ, z), u z))
    (hKs₁ : ∀ μ ∈ uIcc a b, ∀ z ∈ thricePuncturedSphereReal,
      ContDiffAt ℝ 2 (uncurry Ks₁) ((μ, z), u z))
    (hKt₁ : ∀ μ ∈ uIcc a b, ∀ z ∈ thricePuncturedSphereReal,
      ContDiffAt ℝ 2 (uncurry Kt₁) ((μ, z), u z))
    (hKs₂ : ∀ μ ∈ uIcc a b, ∀ z ∈ thricePuncturedSphereReal,
      ContDiffAt ℝ 2 (uncurry Ks₂) ((μ, z), u z))
    (hKt₂ : ∀ μ ∈ uIcc a b, ∀ z ∈ thricePuncturedSphereReal,
      ContDiffAt ℝ 2 (uncurry Kt₂) ((μ, z), u z))
    (hu : ∀ z ∈ thricePuncturedSphereReal, ContDiffAt ℝ 1 u z)
    (hF : ∀ μ ∈ uIcc a b, ∀ q, ∀ z ∈ thricePuncturedSphereReal, R ≤ (positiveEndCoord q z).1 →
      IsComplexLinearMap (AlmostComplexStructure.product ℝ) (J₁ (μ, z) (u z))
        (ω.perturbedFDeriv (fun w ↦ Ks₁ (μ, w)) (fun w ↦ Kt₁ (μ, w)) u z : ℝ × ℝ →ₗ[ℝ] V))
    (hux : ∀ q, TendstoUniformlyOn (fun s t ↦ u (positiveEndChart q (s, t))) (x q) atTop
      (Icc 0 1))
    (hδ : ∀ q, TendstoUniformlyOn (fun s t ↦ sliceDefect
      (fun t ↦ ω.hamiltonianVectorField (positiveEndHamiltonian H q t)) (u ∘ positiveEndChart q)
        (s, t)) 0 atTop (Icc 0 1)) :
    ContinuousOn (fun p : ℝ × ℝ ↦ ω.floerConformalSobolevOperator thricePuncturedSphereReal
      cylindricalWeight (fun z y ↦
        (pathAlmostComplex h₀ hJt₁ hJt₂ (p.1, (p.2, z)) y).toLinearMap.toContinuousLinearMap)
      (fun z ↦ pathHamiltonian Ks₁ Ks₂ (p.1, (p.2, z)))
      (fun z ↦ pathHamiltonian Kt₁ Kt₂ (p.1, (p.2, z))) u) (uIcc 0 1 ×ˢ uIcc a b) := by
  -- Beyond the height `R`, every member of the homotopy at `(σ, μ)` is the first path at `μ`.
  have hend {p : ℝ × ℝ} (hp : p ∈ uIcc 0 1 ×ˢ uIcc a b) {q : Puncture} {z : ℝ × ℝ}
      (hz : z ∈ thricePuncturedSphereReal) (hzR : R ≤ (positiveEndCoord q z).1) :=
    pathData_eq_of_le_fst_positiveEndCoord (hJt₁ := hJt₁) (hJt₂ := hJt₂) h₀ (hJeq₁ p.2 hp.2)
      (hJeq₂ p.2 hp.2) (hK₁ p.2 hp.2) (hK₂ p.2 hp.2) p.1 hz hzR
  refine ω.continuousOn_floerConformalSobolevOperator_pairOfPants_family hH hHs hx hJe
    (P := uIcc 0 1 ×ˢ uIcc a b)
    (J := fun p : (ℝ × ℝ) × (ℝ × ℝ) ↦ pathAlmostComplex h₀ hJt₁ hJt₂ (p.1.1, (p.1.2, p.2)))
    (Ks := fun p ↦ pathHamiltonian Ks₁ Ks₂ (p.1.1, (p.1.2, p.2)))
    (Kt := fun p ↦ pathHamiltonian Kt₁ Kt₂ (p.1.1, (p.1.2, p.2)))
    (fun p hp ↦ pathAlmostComplex_positiveEndChart (hJt₁ := hJt₁) (hJt₂ := hJt₂) h₀
      (hJeq₁ p.2 hp.2) (hJeq₂ p.2 hp.2) p.1)
    (fun p hp q z hz hzR ↦ ?_)
    (fun p hp z hz ↦ contDiffAt_pathAlmostComplex_assoc (hJt₁ := hJt₁) (hJt₂ := hJt₂) h₀
      (hJ₁ p.2 hp.2 z hz) (hJ₂ p.2 hp.2 z hz))
    (fun p hp z hz ↦
      contDiffAt_pathHamiltonian_assoc (hKs₁ p.2 hp.2 z hz) (hKs₂ p.2 hp.2 z hz))
    (fun p hp z hz ↦
      contDiffAt_pathHamiltonian_assoc (hKt₁ p.2 hp.2 z hz) (hKt₂ p.2 hp.2 z hz))
    hu (fun p hp q z hz hzR ↦ ?_) hux hδ
  · rw [(hend hp hz hzR).2.1, (hend hp hz hzR).2.2]
    exact hK₁ p.2 hp.2 q z hz hzR
  · obtain ⟨hJz, hs, ht⟩ := hend hp hz hzR
    rw [hJz, ω.perturbedFDeriv_congr u (Ks' := fun w ↦ Ks₁ (p.2, w))
      (Kt' := fun w ↦ Kt₁ (p.2, w)) hs ht]
    exact hF p.2 hp.2 q z hz hzR

/-- Every operator of the homotopy of data between two paths of core data with the same end data,
at `(σ, μ) ∈ [0, 1] × [[a, b]]`, is Fredholm when the operator of the first path at `μ` is. -/
private theorem isFredholm_floerConformalSobolevOperator_pathData (ω : SymplecticForm V)
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
    {J₀ : AlmostComplexStructure V} (h₀ : ω.Compatible J₀)
    {J₁ J₂ : ℝ × (ℝ × ℝ) → V → AlmostComplexStructure V} (hJt₁ : ∀ p y, ω.Tames (J₁ p y))
    (hJt₂ : ∀ p y, ω.Tames (J₂ p y)) {Ks₁ Kt₁ Ks₂ Kt₂ : ℝ × (ℝ × ℝ) → V → ℝ} {R : ℝ}
    {u : ℝ × ℝ → V} {p : ℝ × ℝ}
    (hJeq₁ : ∀ q (ζ : ℝ × ℝ), R ≤ ζ.1 → J₁ (p.2, positiveEndChart q ζ) = Je q ζ.2)
    (hJeq₂ : ∀ q (ζ : ℝ × ℝ), R ≤ ζ.1 → J₂ (p.2, positiveEndChart q ζ) = Je q ζ.2)
    (hK₁ : ∀ q, ∀ z ∈ thricePuncturedSphereReal, R ≤ (positiveEndCoord q z).1 →
      Ks₁ (p.2, z) = (fun x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x 1) ∧
        Kt₁ (p.2, z) =
          fun x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x Complex.I)
    (hK₂ : ∀ q, ∀ z ∈ thricePuncturedSphereReal, R ≤ (positiveEndCoord q z).1 →
      Ks₂ (p.2, z) = (fun x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x 1) ∧
        Kt₂ (p.2, z) =
          fun x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x Complex.I)
    (hJ₁ : ∀ z ∈ thricePuncturedSphereReal, ContDiffAt ℝ 1
      (fun r : (ℝ × (ℝ × ℝ)) × V ↦ (J₁ r.1 r.2).toLinearMap.toContinuousLinearMap) ((p.2, z), u z))
    (hJ₂ : ∀ z ∈ thricePuncturedSphereReal, ContDiffAt ℝ 1
      (fun r : (ℝ × (ℝ × ℝ)) × V ↦ (J₂ r.1 r.2).toLinearMap.toContinuousLinearMap) ((p.2, z), u z))
    (hKs₁ : ∀ z ∈ thricePuncturedSphereReal, ContDiffAt ℝ 2 (uncurry Ks₁) ((p.2, z), u z))
    (hKt₁ : ∀ z ∈ thricePuncturedSphereReal, ContDiffAt ℝ 2 (uncurry Kt₁) ((p.2, z), u z))
    (hKs₂ : ∀ z ∈ thricePuncturedSphereReal, ContDiffAt ℝ 2 (uncurry Ks₂) ((p.2, z), u z))
    (hKt₂ : ∀ z ∈ thricePuncturedSphereReal, ContDiffAt ℝ 2 (uncurry Kt₂) ((p.2, z), u z))
    (hc₁ : ∀ z ∈ thricePuncturedSphereReal, ω.Compatible (J₁ (p.2, z) (u z)))
    (hc₂ : ∀ z ∈ thricePuncturedSphereReal, ω.Compatible (J₂ (p.2, z) (u z)))
    (hu : ∀ z ∈ thricePuncturedSphereReal, ContDiffAt ℝ 1 u z)
    (hF : ∀ q, ∀ z ∈ thricePuncturedSphereReal, R ≤ (positiveEndCoord q z).1 →
      IsComplexLinearMap (AlmostComplexStructure.product ℝ) (J₁ (p.2, z) (u z))
        (ω.perturbedFDeriv (fun w ↦ Ks₁ (p.2, w)) (fun w ↦ Kt₁ (p.2, w)) u z : ℝ × ℝ →ₗ[ℝ] V))
    (hux : ∀ q, TendstoUniformlyOn (fun s t ↦ u (positiveEndChart q (s, t))) (x q) atTop
      (Icc 0 1))
    (hδ : ∀ q, TendstoUniformlyOn (fun s t ↦ sliceDefect
      (fun t ↦ ω.hamiltonianVectorField (positiveEndHamiltonian H q t)) (u ∘ positiveEndChart q)
        (s, t)) 0 atTop (Icc 0 1))
    (hF₁ : (ω.floerConformalSobolevOperator thricePuncturedSphereReal
      cylindricalWeight (fun z y ↦ (J₁ (p.2, z) y).toLinearMap.toContinuousLinearMap)
        (fun z ↦ Ks₁ (p.2, z)) (fun z ↦ Kt₁ (p.2, z)) u).IsFredholm) :
    (ω.floerConformalSobolevOperator thricePuncturedSphereReal cylindricalWeight (fun z y ↦
        (pathAlmostComplex h₀ hJt₁ hJt₂ (p.1, (p.2, z)) y).toLinearMap.toContinuousLinearMap)
      (fun z ↦ pathHamiltonian Ks₁ Ks₂ (p.1, (p.2, z)))
      (fun z ↦ pathHamiltonian Kt₁ Kt₂ (p.1, (p.2, z))) u).IsFredholm := by
  -- Beyond the height `R` the homotopy at `p` is the first path at `p.2`, so the two have the
  -- same end data, and the Fredholm property passes from one to the other.
  have hend {q : Puncture} {z : ℝ × ℝ} (hz : z ∈ thricePuncturedSphereReal)
      (hzR : R ≤ (positiveEndCoord q z).1) :=
    pathData_eq_of_le_fst_positiveEndCoord (hJt₁ := hJt₁) (hJt₂ := hJt₂) h₀ hJeq₁ hJeq₂ hK₁ hK₂
      p.1 hz hzR
  refine (isFredholm_floerConformalSobolevOperator_iff_of_pairOfPants_data ω hH hHs hX hx hnd hJe
    hJex (J := fun z ↦ J₁ (p.2, z)) (J' := fun z ↦ pathAlmostComplex h₀ hJt₁ hJt₂ (p.1, (p.2, z)))
    (Ks := fun z ↦ Ks₁ (p.2, z)) (Kt := fun z ↦ Kt₁ (p.2, z))
    (Ks' := fun z ↦ pathHamiltonian Ks₁ Ks₂ (p.1, (p.2, z)))
    (Kt' := fun z ↦ pathHamiltonian Kt₁ Kt₂ (p.1, (p.2, z))) (u := u) hJeq₁
    (pathAlmostComplex_positiveEndChart (hJt₁ := hJt₁) (hJt₂ := hJt₂) h₀ hJeq₁ hJeq₂ p.1) hK₁
    (fun q z hz hzR ↦ ?_)
    -- The data at the parameter `p` are regular along `u`, as slices of the families.
    (fun z hz ↦ contDiffAt_comp_prodMap_prodMk_right (hJ₁ z hz))
    (fun z hz ↦ contDiffAt_comp_prodMap_prodMk_right (contDiffAt_pathAlmostComplex_assoc
      (hJt₁ := hJt₁) (hJt₂ := hJt₂) h₀ (hJ₁ z hz) (hJ₂ z hz)))
    (fun z hz ↦ contDiffAt_comp_prodMap_prodMk_right (hKs₁ z hz))
    (fun z hz ↦ contDiffAt_comp_prodMap_prodMk_right (hKt₁ z hz))
    (fun z hz ↦ contDiffAt_comp_prodMap_prodMk_right
      (contDiffAt_pathHamiltonian_assoc (hKs₁ z hz) (hKs₂ z hz)))
    (fun z hz ↦ contDiffAt_comp_prodMap_prodMk_right
      (contDiffAt_pathHamiltonian_assoc (hKt₁ z hz) (hKt₂ z hz)))
    (fun z y ↦ hJt₁ _ y) (fun z y ↦ tames_pathAlmostComplex h₀ _ y) hc₁
    (fun z hz ↦ compatible_pathAlmostComplex h₀ (hc₁ z hz) (hc₂ z hz)) hu hF hux hδ).1 hF₁
  rw [(hend hz hzR).2.1, (hend hz hzR).2.2]
  exact hK₁ q z hz hzR

/-- **Orientation transport for the pair-of-pants operator depends only on the endpoints of the
path of core data.** Let `H_q` be jointly `C²` period-one Hamiltonians on the three ends of
`S = ℂ ∖ {0, 1}`, on a finite-dimensional symplectic inner product space `(V, ω)`, whose
end-chart Hamiltonians `H'_q` (`TauCeti.Floer.positiveEndHamiltonian`) have globally Lipschitz
suspended vector fields and nondegenerate one-periodic orbits `x_q`, and let `J_q(t)` be a `C¹`
family of almost complex structures for each end `q`, compatible with `ω` along `x_q`. Let
`μ ↦ (J_{i,μ}, K_{s,i,μ}, K_{t,i,μ})`, `i = 1, 2`, be two paths of Floer data on `S` with `ω`-tame
almost complex structures, and let `u` be `C¹` on `S`. Suppose that for `μ ∈ [[a, b]]` the data are
`C¹` (with `C²` Hamiltonians) jointly in `μ`, the domain point and the target point along the graph
of `u`, compatible with `ω` along `u`, and beyond the height `R` of every end equal to the end data
(in the positive end chart `φ'_q` the structures are `J_q(t)` and the perturbation is the
pair-of-pants perturbation of `H`). Suppose that beyond the height `R` the map `u` solves the Floer
equation, and that its loops in each end chart converge uniformly to `x_q`, with slice defects
tending uniformly to zero. If the two paths have the same data at `μ = a` and at `μ = b`, then
transporting an orientation of the determinant line of `D_u` for the data at `a` to `b` along the
first path, and along the second path, gives the same orientation of the determinant line of `D_u`
for the data at `b`, once the determinant lines of the equal operators of the two paths at `a` and
at `b` are identified by `LinearMap.detLineCongrOfEq`.

The continuity of the two paths of operators, which orientation transport needs, holds by
`TauCeti.SymplecticForm.continuousOn_floerConformalSobolevOperator_pairOfPants_family`; their
Fredholm property along the whole path follows from that at one parameter by
`TauCeti.SymplecticForm.isFredholm_floerConformalSobolevOperator_iff_of_pairOfPants_data`. -/
theorem detLineOrientationTransport_floerConformalSobolevOperator_pairOfPants_congr
    (ω : SymplecticForm V) {H : Puncture → ℝ → V → ℝ} (hH : ∀ q, Periodic (H q) 1)
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
    {J₁ J₂ : ℝ × (ℝ × ℝ) → V → AlmostComplexStructure V}
    {Ks₁ Kt₁ Ks₂ Kt₂ : ℝ × (ℝ × ℝ) → V → ℝ} {R : ℝ} {u : ℝ × ℝ → V} {a b : ℝ}
    (hJeq₁ : ∀ μ ∈ uIcc a b, ∀ q (ζ : ℝ × ℝ), R ≤ ζ.1 → J₁ (μ, positiveEndChart q ζ) = Je q ζ.2)
    (hJeq₂ : ∀ μ ∈ uIcc a b, ∀ q (ζ : ℝ × ℝ), R ≤ ζ.1 → J₂ (μ, positiveEndChart q ζ) = Je q ζ.2)
    (hK₁ : ∀ μ ∈ uIcc a b, ∀ q, ∀ z ∈ thricePuncturedSphereReal, R ≤ (positiveEndCoord q z).1 →
      Ks₁ (μ, z) = (fun x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x 1) ∧
        Kt₁ (μ, z) =
          fun x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x Complex.I)
    (hK₂ : ∀ μ ∈ uIcc a b, ∀ q, ∀ z ∈ thricePuncturedSphereReal, R ≤ (positiveEndCoord q z).1 →
      Ks₂ (μ, z) = (fun x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x 1) ∧
        Kt₂ (μ, z) =
          fun x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x Complex.I)
    (hJ₁ : ∀ μ ∈ uIcc a b, ∀ z ∈ thricePuncturedSphereReal, ContDiffAt ℝ 1
      (fun p : (ℝ × (ℝ × ℝ)) × V ↦ (J₁ p.1 p.2).toLinearMap.toContinuousLinearMap) ((μ, z), u z))
    (hJ₂ : ∀ μ ∈ uIcc a b, ∀ z ∈ thricePuncturedSphereReal, ContDiffAt ℝ 1
      (fun p : (ℝ × (ℝ × ℝ)) × V ↦ (J₂ p.1 p.2).toLinearMap.toContinuousLinearMap) ((μ, z), u z))
    (hKs₁ : ∀ μ ∈ uIcc a b, ∀ z ∈ thricePuncturedSphereReal,
      ContDiffAt ℝ 2 (uncurry Ks₁) ((μ, z), u z))
    (hKt₁ : ∀ μ ∈ uIcc a b, ∀ z ∈ thricePuncturedSphereReal,
      ContDiffAt ℝ 2 (uncurry Kt₁) ((μ, z), u z))
    (hKs₂ : ∀ μ ∈ uIcc a b, ∀ z ∈ thricePuncturedSphereReal,
      ContDiffAt ℝ 2 (uncurry Ks₂) ((μ, z), u z))
    (hKt₂ : ∀ μ ∈ uIcc a b, ∀ z ∈ thricePuncturedSphereReal,
      ContDiffAt ℝ 2 (uncurry Kt₂) ((μ, z), u z))
    (hJt₁ : ∀ p y, ω.Tames (J₁ p y)) (hJt₂ : ∀ p y, ω.Tames (J₂ p y))
    (hc₁ : ∀ μ ∈ uIcc a b, ∀ z ∈ thricePuncturedSphereReal, ω.Compatible (J₁ (μ, z) (u z)))
    (hc₂ : ∀ μ ∈ uIcc a b, ∀ z ∈ thricePuncturedSphereReal, ω.Compatible (J₂ (μ, z) (u z)))
    (hu : ∀ z ∈ thricePuncturedSphereReal, ContDiffAt ℝ 1 u z)
    (hF : ∀ μ ∈ uIcc a b, ∀ q, ∀ z ∈ thricePuncturedSphereReal, R ≤ (positiveEndCoord q z).1 →
      IsComplexLinearMap (AlmostComplexStructure.product ℝ) (J₁ (μ, z) (u z))
        (ω.perturbedFDeriv (fun w ↦ Ks₁ (μ, w)) (fun w ↦ Kt₁ (μ, w)) u z : ℝ × ℝ →ₗ[ℝ] V))
    (hux : ∀ q, TendstoUniformlyOn (fun s t ↦ u (positiveEndChart q (s, t))) (x q) atTop
      (Icc 0 1))
    (hδ : ∀ q, TendstoUniformlyOn (fun s t ↦ sliceDefect
      (fun t ↦ ω.hamiltonianVectorField (positiveEndHamiltonian H q t)) (u ∘ positiveEndChart q)
        (s, t)) 0 atTop (Icc 0 1))
    (hJa : ∀ w, J₁ (a, w) = J₂ (a, w)) (hKsa : ∀ w, Ks₁ (a, w) = Ks₂ (a, w))
    (hKta : ∀ w, Kt₁ (a, w) = Kt₂ (a, w)) (hJb : ∀ w, J₁ (b, w) = J₂ (b, w))
    (hKsb : ∀ w, Ks₁ (b, w) = Ks₂ (b, w)) (hKtb : ∀ w, Kt₁ (b, w) = Kt₂ (b, w))
    (hT₁ : ContinuousOn (fun μ ↦ ω.floerConformalSobolevOperator thricePuncturedSphereReal
      cylindricalWeight (fun z y ↦ (J₁ (μ, z) y).toLinearMap.toContinuousLinearMap)
        (fun z ↦ Ks₁ (μ, z)) (fun z ↦ Kt₁ (μ, z)) u) (uIcc a b))
    (hF₁ : ∀ μ ∈ uIcc a b, (ω.floerConformalSobolevOperator thricePuncturedSphereReal
      cylindricalWeight (fun z y ↦ (J₁ (μ, z) y).toLinearMap.toContinuousLinearMap)
        (fun z ↦ Ks₁ (μ, z)) (fun z ↦ Kt₁ (μ, z)) u).IsFredholm)
    (hT₂ : ContinuousOn (fun μ ↦ ω.floerConformalSobolevOperator thricePuncturedSphereReal
      cylindricalWeight (fun z y ↦ (J₂ (μ, z) y).toLinearMap.toContinuousLinearMap)
        (fun z ↦ Ks₂ (μ, z)) (fun z ↦ Kt₂ (μ, z)) u) (uIcc a b))
    (hF₂ : ∀ μ ∈ uIcc a b, (ω.floerConformalSobolevOperator thricePuncturedSphereReal
      cylindricalWeight (fun z y ↦ (J₂ (μ, z) y).toLinearMap.toContinuousLinearMap)
        (fun z ↦ Ks₂ (μ, z)) (fun z ↦ Kt₂ (μ, z)) u).IsFredholm) :
    detLineOrientationTransport a b hT₂ hF₂ ∘
        Module.Ray.map (LinearMap.detLineCongrOfEq (by simp only [hJa, hKsa, hKta])) =
      Module.Ray.map (LinearMap.detLineCongrOfEq (by simp only [hJb, hKsb, hKtb])) ∘
        detLineOrientationTransport a b hT₁ hF₁ := by
  funext o
  -- The paths of almost complex structures are joined relative to a compatible structure.
  have h₀ := hc₁ a left_mem_uIcc (2, 0)
    (by norm_num [mem_thricePuncturedSphereReal_iff, Complex.ext_iff])
  -- The homotopy from the first path (`σ = 0`) to the second (`σ = 1`) is the path of data between
  -- them at `(σ, μ)`. Its operators are continuous and Fredholm on `[0, 1] × [[a, b]]`, and at the
  -- ends `μ = a` and `μ = b`, where the two paths agree, it is constant in `σ`.
  refine detLineOrientationTransport_eq_of_homotopy_of_eq (s₀ := 0) (s₁ := 1)
    (H := fun p ↦ ω.floerConformalSobolevOperator thricePuncturedSphereReal cylindricalWeight
      (fun z y ↦
        (pathAlmostComplex h₀ hJt₁ hJt₂ (p.1, (p.2, z)) y).toLinearMap.toContinuousLinearMap)
      (fun z ↦ pathHamiltonian Ks₁ Ks₂ (p.1, (p.2, z)))
      (fun z ↦ pathHamiltonian Kt₁ Kt₂ (p.1, (p.2, z))) u)
    (continuousOn_floerConformalSobolevOperator_pathData ω hH hHs
      (fun q ↦ continuous_iff_continuousAt.2 (fun t ↦ (hx q t).continuousAt) |>.continuousOn) hJe
      h₀ hJt₁ hJt₂ hJeq₁ hJeq₂ hK₁ hK₂ hJ₁ hJ₂ hKs₁ hKt₁ hKs₂ hKt₂ hu hF hux hδ)
    (fun p hp ↦ isFredholm_floerConformalSobolevOperator_pathData ω hH hHs hX hx hnd hJe hJex h₀
      hJt₁ hJt₂ (hJeq₁ p.2 hp.2) (hJeq₂ p.2 hp.2) (hK₁ p.2 hp.2) (hK₂ p.2 hp.2) (hJ₁ p.2 hp.2)
      (hJ₂ p.2 hp.2) (hKs₁ p.2 hp.2) (hKt₁ p.2 hp.2) (hKs₂ p.2 hp.2) (hKt₂ p.2 hp.2)
      (hc₁ p.2 hp.2) (hc₂ p.2 hp.2) hu (hF p.2 hp.2) hux hδ (hF₁ p.2 hp.2))
    ?_ ?_ ?_ ?_ hT₁ hF₁ hT₂ hF₂ _ _ o
  · exact fun μ ↦ by simp only [pathAlmostComplex_zero, pathHamiltonian_zero]
  · exact fun μ ↦ by simp only [pathAlmostComplex_one, pathHamiltonian_one]
  · exact fun σ _ ↦ by
      simp only [pathAlmostComplex_of_eq h₀ _ (congrFun (hJa _) _),
        pathHamiltonian_of_eq _ (hKsa _), pathHamiltonian_of_eq _ (hKta _)]
  · exact fun σ _ ↦ by
      simp only [pathAlmostComplex_of_eq h₀ _ (congrFun (hJb _) _),
        pathHamiltonian_of_eq _ (hKsb _), pathHamiltonian_of_eq _ (hKtb _)]

/-- **Orientation transport around a loop of core data on the pair of pants is trivial.** Under
the hypotheses of
`TauCeti.SymplecticForm.detLineOrientationTransport_floerConformalSobolevOperator_pairOfPants_congr`
on a single path `μ ↦ (J_μ, K_{s,μ}, K_{t,μ})` of Floer data on `S = ℂ ∖ {0, 1}` with fixed end data
and the same data at `μ = a` and at `μ = b`, transporting an orientation of the determinant line of
the pair-of-pants operator `D_u` from `a` to `b` along the path is the identification of the
determinant lines of the equal operators at `a` and at `b`. So the determinant lines of the
pair-of-pants operator are orientable over every loop of core data with fixed end data. -/
theorem detLineOrientationTransport_floerConformalSobolevOperator_pairOfPants_eq_map
    (ω : SymplecticForm V) {H : Puncture → ℝ → V → ℝ} (hH : ∀ q, Periodic (H q) 1)
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
    {u : ℝ × ℝ → V} {a b : ℝ}
    (hJeq : ∀ μ ∈ uIcc a b, ∀ q (ζ : ℝ × ℝ), R ≤ ζ.1 → J (μ, positiveEndChart q ζ) = Je q ζ.2)
    (hK : ∀ μ ∈ uIcc a b, ∀ q, ∀ z ∈ thricePuncturedSphereReal, R ≤ (positiveEndCoord q z).1 →
      Ks (μ, z) = (fun x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x 1) ∧
        Kt (μ, z) = fun x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x Complex.I)
    (hJ : ∀ μ ∈ uIcc a b, ∀ z ∈ thricePuncturedSphereReal, ContDiffAt ℝ 1
      (fun p : (ℝ × (ℝ × ℝ)) × V ↦ (J p.1 p.2).toLinearMap.toContinuousLinearMap) ((μ, z), u z))
    (hKs : ∀ μ ∈ uIcc a b, ∀ z ∈ thricePuncturedSphereReal,
      ContDiffAt ℝ 2 (uncurry Ks) ((μ, z), u z))
    (hKt : ∀ μ ∈ uIcc a b, ∀ z ∈ thricePuncturedSphereReal,
      ContDiffAt ℝ 2 (uncurry Kt) ((μ, z), u z))
    (hJt : ∀ p y, ω.Tames (J p y))
    (hc : ∀ μ ∈ uIcc a b, ∀ z ∈ thricePuncturedSphereReal, ω.Compatible (J (μ, z) (u z)))
    (hu : ∀ z ∈ thricePuncturedSphereReal, ContDiffAt ℝ 1 u z)
    (hF : ∀ μ ∈ uIcc a b, ∀ q, ∀ z ∈ thricePuncturedSphereReal, R ≤ (positiveEndCoord q z).1 →
      IsComplexLinearMap (AlmostComplexStructure.product ℝ) (J (μ, z) (u z))
        (ω.perturbedFDeriv (fun w ↦ Ks (μ, w)) (fun w ↦ Kt (μ, w)) u z : ℝ × ℝ →ₗ[ℝ] V))
    (hux : ∀ q, TendstoUniformlyOn (fun s t ↦ u (positiveEndChart q (s, t))) (x q) atTop
      (Icc 0 1))
    (hδ : ∀ q, TendstoUniformlyOn (fun s t ↦ sliceDefect
      (fun t ↦ ω.hamiltonianVectorField (positiveEndHamiltonian H q t)) (u ∘ positiveEndChart q)
        (s, t)) 0 atTop (Icc 0 1))
    (hJab : ∀ w, J (a, w) = J (b, w)) (hKsab : ∀ w, Ks (a, w) = Ks (b, w))
    (hKtab : ∀ w, Kt (a, w) = Kt (b, w))
    (hT : ContinuousOn (fun μ ↦ ω.floerConformalSobolevOperator thricePuncturedSphereReal
      cylindricalWeight (fun z y ↦ (J (μ, z) y).toLinearMap.toContinuousLinearMap)
        (fun z ↦ Ks (μ, z)) (fun z ↦ Kt (μ, z)) u) (uIcc a b))
    (hFr : ∀ μ ∈ uIcc a b, (ω.floerConformalSobolevOperator thricePuncturedSphereReal
      cylindricalWeight (fun z y ↦ (J (μ, z) y).toLinearMap.toContinuousLinearMap)
        (fun z ↦ Ks (μ, z)) (fun z ↦ Kt (μ, z)) u).IsFredholm) :
    ∀ o, detLineOrientationTransport a b hT hFr o =
      Module.Ray.map (LinearMap.detLineCongrOfEq (by simp only [hJab, hKsab, hKtab])) o := by
  intro o
  have ha : a ∈ uIcc a b := left_mem_uIcc
  have hT₀ := hFr a ha
  -- Compare the path with the constant path at the data at `a`, along which transport is the
  -- identity: its operator at `μ` is that at `a`.
  have hconst (μ : ℝ) :
      ω.floerConformalSobolevOperator thricePuncturedSphereReal cylindricalWeight
          (fun z y ↦ (J (a, (μ, z).2) y).toLinearMap.toContinuousLinearMap)
          (fun z ↦ Ks (a, (μ, z).2)) (fun z ↦ Kt (a, (μ, z).2)) u =
        ω.floerConformalSobolevOperator thricePuncturedSphereReal cylindricalWeight
          (fun z y ↦ (J (a, z) y).toLinearMap.toContinuousLinearMap)
          (fun z ↦ Ks (a, z)) (fun z ↦ Kt (a, z)) u := by
    simp only
  have key := detLineOrientationTransport_floerConformalSobolevOperator_pairOfPants_congr ω hH hHs
    hX hx hnd hJe hJex (J₂ := fun p ↦ J (a, p.2)) (Ks₂ := fun p ↦ Ks (a, p.2))
    (Kt₂ := fun p ↦ Kt (a, p.2)) hJeq (fun _ _ ↦ hJeq a ha) hK (fun _ _ ↦ hK a ha) hJ
    (fun _ _ z hz ↦ contDiffAt_comp_prodMap_prodMap_const (hJ a ha z hz)) hKs hKt
    (fun _ _ z hz ↦ contDiffAt_comp_prodMap_prodMap_const (hKs a ha z hz))
    (fun _ _ z hz ↦ contDiffAt_comp_prodMap_prodMap_const (hKt a ha z hz)) hJt
    (fun p ↦ hJt (a, p.2)) hc (fun _ _ ↦ hc a ha) hu hF hux hδ (fun _ ↦ rfl) (fun _ ↦ rfl)
    (fun _ ↦ rfl) (fun w ↦ (hJab w).symm) (fun w ↦ (hKsab w).symm) (fun w ↦ (hKtab w).symm) hT hFr
    (continuousOn_const.congr fun μ _ ↦ hconst μ) (fun μ _ ↦ by rw [hconst μ]; exact hT₀)
  have := congrFun key o
  rw [Function.comp_apply, Function.comp_apply, detLineOrientationTransport_eq_map_of_forall_eq _ _
    fun μ _ ↦ (hconst μ).trans (hconst a).symm] at this
  rw [← (Equiv.symm_apply_eq _).2 this, Module.Ray.map_symm, LinearMap.detLineCongrOfEq_symm]
  simp only [LinearMap.map_detLineCongrOfEq_map_detLineCongrOfEq]

end TauCeti.SymplecticForm
