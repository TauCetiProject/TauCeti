/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Fredholm.DeterminantLine.Homotopy
public import TauCeti.Geometry.Symplectic.Floer.PairOfPants.Sobolev.Invariance
import TauCeti.Geometry.Symplectic.Floer.Continuation.Path

/-!
# Orientation transport for the pair-of-pants operator along paths of data

Let `u` be a `C¹` map on the pair of pants `S = ℂ ∖ {0, 1}` into a finite-dimensional symplectic
inner product space `(V, ω)`, converging along the three ends to nondegenerate one-periodic orbits
`x_q` of the end Hamiltonians, and let `D_u : W^{1,2}_0(S, V) → L²(S, V)` be the realization
(`TauCeti.SymplecticForm.floerConformalSobolevOperator` for the cylindrical weight) of the
linearized Floer operator of Floer data `(J, K_s, K_t)` on `S` which, far out on every end `q`, are
the end data: a `C¹` family `J_q(t)` of almost complex structures and the pair-of-pants
perturbation of the period-one Hamiltonians `H_q`. When `D_u` is Fredholm it has a determinant line
`det (ker D_u) ⊗ (det (coker D_u))^*`, and orienting the moduli spaces of pairs of pants, hence
counting them with signs, starts from orientations of these lines. They must be compared for
different choices of the data over the core of `S`.

Along a path `μ ↦ (J_μ, K_{s,μ}, K_{t,μ})` of such data with fixed end data, jointly `C¹` in the
parameter (with `C²` Hamiltonians), the operators depend continuously on `μ`, so orientations of
their determinant lines are transported along the path (`TauCeti.detLineOrientationTransport`).
This file proves, in the namespace `TauCeti.SymplecticForm`, that the transport depends only on
the endpoints of the path
(`detLineOrientationTransport_floerConformalSobolevOperator_pairOfPants_congr`): for two such
paths on `[[a, b]]` with the same end data, agreeing at `a` and at `b`, the transports from `a` to
`b` along the two paths agree, once the determinant lines of the equal operators at `a` and at `b`
are identified. In particular transport around a loop of data is trivial
(`detLineOrientationTransport_floerConformalSobolevOperator_pairOfPants_eq_map`), so the
determinant lines are orientable over every loop of pair-of-pants data with fixed end data,
and an orientation for one choice of data over the core determines one for every other choice. This
is the pair-of-pants counterpart of the statement for cylinders
(`TauCeti.SymplecticForm.detLineOrientationTransport_floerSobolevOperator_congr`).

The proof joins the two paths by a homotopy of data relative to the endpoints. At `(σ, μ)` its
almost complex structures run along the path of Cayley coordinates, relative to a structure
compatible with `ω`, from those of the first path at `μ` to those of the second
(`TauCeti.Floer.pathAlmostComplex`), and its Hamiltonians along the segment between them
(`TauCeti.Floer.pathHamiltonian`). Far out on the ends both paths are the end data, hence so is the
homotopy, and along `u` its structures stay compatible with `ω`. So every member of the homotopy is
Fredholm, by the invariance of the Fredholm property under a change of the data over the core
(`TauCeti.SymplecticForm.isFredholm_floerConformalSobolevOperator_iff_of_pairOfPants_data`), and
the members depend continuously on `(σ, μ)`, as a family of data with fixed end data
(`TauCeti.SymplecticForm.continuousOn_floerConformalSobolevOperator_pairOfPants_family`).
Orientation transport is invariant under such a homotopy
(`TauCeti.detLineOrientationTransport_eq_of_homotopy_of_eq`).

## Main results

In the namespace `TauCeti.SymplecticForm`:

* `detLineOrientationTransport_floerConformalSobolevOperator_pairOfPants_congr`: orientation
  transport of the determinant lines of the pair-of-pants operator along a path of data with fixed
  end data depends only on the data at the endpoints.
* `detLineOrientationTransport_floerConformalSobolevOperator_pairOfPants_eq_map`: orientation
  transport around a loop of pair-of-pants data with fixed end data is trivial.

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

noncomputable section

open Set Function Filter MeasureTheory TauCeti.ThricePuncturedSphere
  TauCeti.ThricePuncturedSphere.Puncture
open scoped NNReal Manifold

namespace TauCeti.SymplecticForm

open Floer ConformalSobolev

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]

/-- Far out on the ends, the path of data between two sets of pair-of-pants data with the same end
data is that end data: if beyond the heights `R₁` and `R₂` of every end the data `J₁(μ)` and
`J₂(μ)` at a parameter `μ` are the end data, then beyond every height `R ≥ R₁, R₂` so is every
member `σ` of the path between them, and `u` solves its Floer equation there when it solves that of
`J₁(μ)`. -/
private theorem path_eq_endData {J₀ : AlmostComplexStructure V} (ω : SymplecticForm V)
    (h₀ : ω.Compatible J₀) {H : Puncture → ℝ → V → ℝ}
    {Je : Puncture → ℝ → V → AlmostComplexStructure V}
    {J₁ J₂ : ℝ × (ℝ × ℝ) → V → AlmostComplexStructure V} (hJt₁ : ∀ p y, ω.Tames (J₁ p y))
    (hJt₂ : ∀ p y, ω.Tames (J₂ p y)) {Ks₁ Kt₁ Ks₂ Kt₂ : ℝ × (ℝ × ℝ) → V → ℝ} {R₁ R₂ R : ℝ}
    (hR₁ : R₁ ≤ R) (hR₂ : R₂ ≤ R) (hR : 0 < R) {u : ℝ × ℝ → V} {μ : ℝ}
    (hJeq₁ : ∀ q (ζ : ℝ × ℝ), R₁ ≤ ζ.1 → J₁ (μ, positiveEndChart q ζ) = Je q ζ.2)
    (hJeq₂ : ∀ q (ζ : ℝ × ℝ), R₂ ≤ ζ.1 → J₂ (μ, positiveEndChart q ζ) = Je q ζ.2)
    (hK₁ : ∀ q, ∀ z ∈ thricePuncturedSphereReal, R₁ ≤ (positiveEndCoord q z).1 →
      Ks₁ (μ, z) = (fun x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x 1) ∧
        Kt₁ (μ, z) =
          fun x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x Complex.I)
    (hK₂ : ∀ q, ∀ z ∈ thricePuncturedSphereReal, R₂ ≤ (positiveEndCoord q z).1 →
      Ks₂ (μ, z) = (fun x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x 1) ∧
        Kt₂ (μ, z) =
          fun x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x Complex.I)
    (hF₁ : ∀ q, ∀ z ∈ thricePuncturedSphereReal, R₁ ≤ (positiveEndCoord q z).1 →
      IsComplexLinearMap (AlmostComplexStructure.product ℝ) (J₁ (μ, z) (u z))
        (ω.perturbedFDeriv (fun w ↦ Ks₁ (μ, w)) (fun w ↦ Kt₁ (μ, w)) u z : ℝ × ℝ →ₗ[ℝ] V))
    (σ : ℝ) :
    (∀ q (ζ : ℝ × ℝ), R ≤ ζ.1 →
      pathAlmostComplex h₀ hJt₁ hJt₂ (σ, (μ, positiveEndChart q ζ)) = Je q ζ.2) ∧
    (∀ q, ∀ z ∈ thricePuncturedSphereReal, R ≤ (positiveEndCoord q z).1 →
      pathHamiltonian Ks₁ Ks₂ (σ, (μ, z)) =
          (fun x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x 1) ∧
        pathHamiltonian Kt₁ Kt₂ (σ, (μ, z)) =
          fun x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x Complex.I) ∧
    (∀ q, ∀ z ∈ thricePuncturedSphereReal, R ≤ (positiveEndCoord q z).1 →
      IsComplexLinearMap (AlmostComplexStructure.product ℝ)
        (pathAlmostComplex h₀ hJt₁ hJt₂ (σ, (μ, z)) (u z))
        (ω.perturbedFDeriv (fun w ↦ pathHamiltonian Ks₁ Ks₂ (σ, (μ, w)))
          (fun w ↦ pathHamiltonian Kt₁ Kt₂ (σ, (μ, w))) u z : ℝ × ℝ →ₗ[ℝ] V)) := by
  -- Beyond the height `R` both sets of data are the end data, hence so is the path between them.
  have hend {q : Puncture} {z : ℝ × ℝ} (hz : z ∈ thricePuncturedSphereReal)
      (hzR : R ≤ (positiveEndCoord q z).1) :
      pathAlmostComplex h₀ hJt₁ hJt₂ (σ, (μ, z)) = J₁ (μ, z) ∧
        pathHamiltonian Ks₁ Ks₂ (σ, (μ, z)) = Ks₁ (μ, z) ∧
          pathHamiltonian Kt₁ Kt₂ (σ, (μ, z)) = Kt₁ (μ, z) := by
    have hJz := eq_of_max_le_fst_positiveEndCoord (J := fun w ↦ J₁ (μ, w))
      (J' := fun w ↦ J₂ (μ, w)) hJeq₁ hJeq₂ hz ((max_le hR₁ hR₂).trans hzR)
    obtain ⟨hs, ht⟩ := hK₁ q z hz (hR₁.trans hzR)
    obtain ⟨hs', ht'⟩ := hK₂ q z hz (hR₂.trans hzR)
    exact ⟨funext fun y ↦ pathAlmostComplex_of_eq h₀ σ (congrFun hJz y),
      pathHamiltonian_of_eq σ (hs.trans hs'.symm), pathHamiltonian_of_eq σ (ht.trans ht'.symm)⟩
  refine ⟨fun q ζ hζ ↦ ?_, fun q z hz hzR ↦ ?_, fun q z hz hzR ↦ ?_⟩
  · have hz := positiveEndChart_mem_thricePuncturedSphereReal (q := q) (hR.trans_le hζ)
    rw [(hend hz (by rw [fst_positiveEndCoord_positiveEndChart]; exact hζ)).1,
      hJeq₁ q ζ (hR₁.trans hζ)]
  · rw [(hend hz hzR).2.1, (hend hz hzR).2.2]
    exact hK₁ q z hz (hR₁.trans hzR)
  · obtain ⟨hJz, hs, ht⟩ := hend hz hzR
    rw [hJz, ω.perturbedFDeriv_congr u (Ks' := fun w ↦ Ks₁ (μ, w))
      (Kt' := fun w ↦ Kt₁ (μ, w)) hs ht]
    exact hF₁ q z hz (hR₁.trans hzR)

/-- The path of data between two families of data `(J_i(μ), K_{s,i}(μ), K_{t,i}(μ))`, read as a
family in the parameter `(σ, μ)`, is `C¹` (with `C²` Hamiltonians) wherever both families are. -/
private theorem contDiffAt_path {J₀ : AlmostComplexStructure V} {ω : SymplecticForm V}
    (h₀ : ω.Compatible J₀) {J₁ J₂ : ℝ × (ℝ × ℝ) → V → AlmostComplexStructure V}
    (hJt₁ : ∀ p y, ω.Tames (J₁ p y)) (hJt₂ : ∀ p y, ω.Tames (J₂ p y))
    {Ks₁ Kt₁ Ks₂ Kt₂ : ℝ × (ℝ × ℝ) → V → ℝ} {p : ℝ × ℝ} {z : ℝ × ℝ} {y : V}
    (hJ₁ : ContDiffAt ℝ 1
      (fun r : (ℝ × (ℝ × ℝ)) × V ↦ (J₁ r.1 r.2).toLinearMap.toContinuousLinearMap) ((p.2, z), y))
    (hJ₂ : ContDiffAt ℝ 1
      (fun r : (ℝ × (ℝ × ℝ)) × V ↦ (J₂ r.1 r.2).toLinearMap.toContinuousLinearMap) ((p.2, z), y))
    (hKs₁ : ContDiffAt ℝ 2 (uncurry Ks₁) ((p.2, z), y))
    (hKs₂ : ContDiffAt ℝ 2 (uncurry Ks₂) ((p.2, z), y))
    (hKt₁ : ContDiffAt ℝ 2 (uncurry Kt₁) ((p.2, z), y))
    (hKt₂ : ContDiffAt ℝ 2 (uncurry Kt₂) ((p.2, z), y)) :
    ContDiffAt ℝ 1 (fun r : ((ℝ × ℝ) × (ℝ × ℝ)) × V ↦ (pathAlmostComplex h₀ hJt₁ hJt₂
      (r.1.1.1, (r.1.1.2, r.1.2)) r.2).toLinearMap.toContinuousLinearMap) ((p, z), y) ∧
    ContDiffAt ℝ 2 (uncurry fun r : (ℝ × ℝ) × (ℝ × ℝ) ↦
      pathHamiltonian Ks₁ Ks₂ (r.1.1, (r.1.2, r.2))) ((p, z), y) ∧
    ContDiffAt ℝ 2 (uncurry fun r : (ℝ × ℝ) × (ℝ × ℝ) ↦
      pathHamiltonian Kt₁ Kt₂ (r.1.1, (r.1.2, r.2))) ((p, z), y) := by
  -- Each is the corresponding path, a function of `((σ, (μ, z)), y)`, after reassociation.
  have hg : ContDiffAt ℝ ⊤ (fun r : ((ℝ × ℝ) × (ℝ × ℝ)) × V ↦
      ((r.1.1.1, (r.1.1.2, r.1.2)), r.2)) ((p, z), y) :=
    ((contDiff_fst.fst.fst.prodMk (contDiff_fst.fst.snd.prodMk contDiff_fst.snd)).prodMk
      contDiff_snd).contDiffAt
  exact ⟨((contDiffAt_pathAlmostComplex h₀ hJt₁ hJt₂ (p := (p.1, (p.2, z))) hJ₁ hJ₂).comp
      ((p, z), y) (hg.of_le le_top) :),
    ((contDiffAt_pathHamiltonian (p := (p.1, (p.2, z))) hKs₁ hKs₂).comp ((p, z), y)
      (hg.of_le le_top) :),
    ((contDiffAt_pathHamiltonian (p := (p.1, (p.2, z))) hKt₁ hKt₂).comp ((p, z), y)
      (hg.of_le le_top) :)⟩

/-- **Orientation transport for the pair-of-pants operator depends only on the endpoints of the
path of data.** Let `H_q` be jointly `C²` period-one Hamiltonians on the three ends of
`S = ℂ ∖ {0, 1}`, on a finite-dimensional symplectic inner product space `(V, ω)`, and `J_q(t)` a
`C¹` family of almost complex structures for each end `q`. Let `u` be a `C¹` map on `S` whose loops
in each end chart converge uniformly to a nondegenerate one-periodic orbit `x_q` of the end-chart
Hamiltonian `H'_q(t, x) = ±H_q(±t, x)`, along which `J_q` is compatible with `ω`, with slice defects
tending uniformly to zero.

Let `μ ↦ (J_{i,μ}, K_{s,i,μ}, K_{t,i,μ})`, `i = 1, 2`, be two paths of Floer data on `S` with
`ω`-tame almost complex structures such that for `μ ∈ [[a, b]]` the data are `C¹` (with `C²`
Hamiltonians) jointly in the parameter, the domain point and the target point along the graph of
`u`, are compatible with `ω` along `u`, and are the end data beyond the height `R_i` of every end,
where `u` solves the Floer equation of the first path. Suppose the two paths have the same data at
`μ = a` and at `μ = b`, and that their operators `D_u` are continuous in `μ` and Fredholm on
`[[a, b]]`, as orientation transport requires; the continuity holds by
`TauCeti.SymplecticForm.continuousOn_floerConformalSobolevOperator_pairOfPants_family`. Then
transporting an orientation of the determinant line of `D_u` for the data at `a` to `b` along the
first path, and along the second path, gives the same orientation of the determinant line of `D_u`
for the data at `b`, once the determinant lines of the equal operators of the two paths at `a`
and at `b` are identified by `LinearMap.detLineCongrOfEq`. -/
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
    {Ks₁ Kt₁ Ks₂ Kt₂ : ℝ × (ℝ × ℝ) → V → ℝ} {R₁ R₂ : ℝ} {u : ℝ × ℝ → V} {a b : ℝ}
    (hJeq₁ : ∀ μ ∈ uIcc a b, ∀ q (ζ : ℝ × ℝ), R₁ ≤ ζ.1 →
      J₁ (μ, positiveEndChart q ζ) = Je q ζ.2)
    (hJeq₂ : ∀ μ ∈ uIcc a b, ∀ q (ζ : ℝ × ℝ), R₂ ≤ ζ.1 →
      J₂ (μ, positiveEndChart q ζ) = Je q ζ.2)
    (hK₁ : ∀ μ ∈ uIcc a b, ∀ q, ∀ z ∈ thricePuncturedSphereReal, R₁ ≤ (positiveEndCoord q z).1 →
      Ks₁ (μ, z) = (fun x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x 1) ∧
        Kt₁ (μ, z) =
          fun x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x Complex.I)
    (hK₂ : ∀ μ ∈ uIcc a b, ∀ q, ∀ z ∈ thricePuncturedSphereReal, R₂ ≤ (positiveEndCoord q z).1 →
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
    (hF₁ : ∀ μ ∈ uIcc a b, ∀ q, ∀ z ∈ thricePuncturedSphereReal, R₁ ≤ (positiveEndCoord q z).1 →
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
    (hFr₁ : ∀ μ ∈ uIcc a b, (ω.floerConformalSobolevOperator thricePuncturedSphereReal
      cylindricalWeight (fun z y ↦ (J₁ (μ, z) y).toLinearMap.toContinuousLinearMap)
      (fun z ↦ Ks₁ (μ, z)) (fun z ↦ Kt₁ (μ, z)) u).IsFredholm)
    (hT₂ : ContinuousOn (fun μ ↦ ω.floerConformalSobolevOperator thricePuncturedSphereReal
      cylindricalWeight (fun z y ↦ (J₂ (μ, z) y).toLinearMap.toContinuousLinearMap)
      (fun z ↦ Ks₂ (μ, z)) (fun z ↦ Kt₂ (μ, z)) u) (uIcc a b))
    (hFr₂ : ∀ μ ∈ uIcc a b, (ω.floerConformalSobolevOperator thricePuncturedSphereReal
      cylindricalWeight (fun z y ↦ (J₂ (μ, z) y).toLinearMap.toContinuousLinearMap)
      (fun z ↦ Ks₂ (μ, z)) (fun z ↦ Kt₂ (μ, z)) u).IsFredholm) :
    detLineOrientationTransport a b hT₂ hFr₂ ∘
        Module.Ray.map (LinearMap.detLineCongrOfEq (by simp only [hJa, hKsa, hKta])) =
      Module.Ray.map (LinearMap.detLineCongrOfEq (by simp only [hJb, hKsb, hKtb])) ∘
        detLineOrientationTransport a b hT₁ hFr₁ := by
  funext o
  obtain ⟨R, hR₁, hR₂, hR⟩ : ∃ R, R₁ ≤ R ∧ R₂ ≤ R ∧ 0 < R := ⟨max (max R₁ R₂) 1,
    le_max_of_le_left (le_max_left _ _), le_max_of_le_left (le_max_right _ _), by positivity⟩
  -- The homotopy is taken in Cayley coordinates relative to a structure compatible with `ω`.
  have h₀ := hc₁ a left_mem_uIcc (2, 0)
    (by norm_num [mem_thricePuncturedSphereReal_iff, Complex.ext_iff])
  -- Every member `p = (σ, μ)` of the homotopy is pair-of-pants data with the same end data beyond
  -- the height `R`, regular and compatible along `u`.
  have hdata (p : ℝ × ℝ) (hp : p.2 ∈ uIcc a b) := path_eq_endData ω h₀ hJt₁ hJt₂ hR₁ hR₂ hR
    (hJeq₁ p.2 hp) (hJeq₂ p.2 hp) (hK₁ p.2 hp) (hK₂ p.2 hp) (hF₁ p.2 hp) p.1
  have hreg (p : ℝ × ℝ) (hp : p.2 ∈ uIcc a b) (z : ℝ × ℝ) (hz : z ∈ thricePuncturedSphereReal) :=
    contDiffAt_path h₀ hJt₁ hJt₂ (p := p) (hJ₁ p.2 hp z hz) (hJ₂ p.2 hp z hz) (hKs₁ p.2 hp z hz)
      (hKs₂ p.2 hp z hz) (hKt₁ p.2 hp z hz) (hKt₂ p.2 hp z hz)
  -- The data at a fixed parameter are the family composed with a slice.
  have hslice {P : Type} [NormedAddCommGroup P] [NormedSpace ℝ P] (p : P) (z : ℝ × ℝ) :
      ContDiffAt ℝ ⊤ (fun r : (ℝ × ℝ) × V ↦ (((p, r.1), r.2) : (P × (ℝ × ℝ)) × V)) (z, u z) :=
    ((contDiff_const.prodMk contDiff_fst).prodMk contDiff_snd).contDiffAt
  refine detLineOrientationTransport_eq_of_homotopy_of_eq (s₀ := 0) (s₁ := 1)
    (H := fun p ↦ ω.floerConformalSobolevOperator thricePuncturedSphereReal cylindricalWeight
      (fun z y ↦
        (pathAlmostComplex h₀ hJt₁ hJt₂ (p.1, (p.2, z)) y).toLinearMap.toContinuousLinearMap)
      (fun z ↦ pathHamiltonian Ks₁ Ks₂ (p.1, (p.2, z)))
      (fun z ↦ pathHamiltonian Kt₁ Kt₂ (p.1, (p.2, z))) u)
    ?_ ?_ ?_ ?_ ?_ ?_ hT₁ hFr₁ hT₂ hFr₂ _ _ o
  · exact ω.continuousOn_floerConformalSobolevOperator_pairOfPants_family hH hHs
      (fun q ↦ continuous_iff_continuousAt.2 (fun t ↦ (hx q t).continuousAt) |>.continuousOn) hJe
      (s := uIcc (0 : ℝ) 1 ×ˢ uIcc a b)
      (J := fun r ↦ pathAlmostComplex h₀ hJt₁ hJt₂ (r.1.1, (r.1.2, r.2)))
      (Ks := fun r ↦ pathHamiltonian Ks₁ Ks₂ (r.1.1, (r.1.2, r.2)))
      (Kt := fun r ↦ pathHamiltonian Kt₁ Kt₂ (r.1.1, (r.1.2, r.2)))
      (fun p hp ↦ (hdata p hp.2).1) (fun p hp ↦ (hdata p hp.2).2.1)
      (fun p hp z hz ↦ (hreg p hp.2 z hz).1) (fun p hp z hz ↦ (hreg p hp.2 z hz).2.1)
      (fun p hp z hz ↦ (hreg p hp.2 z hz).2.2) hu (fun p hp ↦ (hdata p hp.2).2.2) hux hδ
  -- Each member differs from the data of the first path at `μ` only over the core of `S`.
  · exact fun p hp ↦ (isFredholm_floerConformalSobolevOperator_iff_of_pairOfPants_data ω hH hHs hX
      hx hnd hJe hJex (J := fun z ↦ J₁ (p.2, z))
      (J' := fun z ↦ pathAlmostComplex h₀ hJt₁ hJt₂ (p.1, (p.2, z))) (hJeq₁ p.2 hp.2)
      (hdata p hp.2).1 (hK₁ p.2 hp.2) (hdata p hp.2).2.1
      (fun z hz ↦ ((hJ₁ p.2 hp.2 z hz).comp (z, u z) ((hslice p.2 z).of_le le_top) :))
      (fun z hz ↦ ((hreg p hp.2 z hz).1.comp (z, u z) ((hslice p z).of_le le_top) :))
      (fun z hz ↦ ((hKs₁ p.2 hp.2 z hz).comp (z, u z) ((hslice p.2 z).of_le le_top) :))
      (fun z hz ↦ ((hKt₁ p.2 hp.2 z hz).comp (z, u z) ((hslice p.2 z).of_le le_top) :))
      (fun z hz ↦ ((hreg p hp.2 z hz).2.1.comp (z, u z) ((hslice p z).of_le le_top) :))
      (fun z hz ↦ ((hreg p hp.2 z hz).2.2.comp (z, u z) ((hslice p z).of_le le_top) :))
      (fun _ y ↦ hJt₁ _ y) (fun _ y ↦ tames_pathAlmostComplex h₀ _ y) (hc₁ p.2 hp.2)
      (fun z hz ↦ compatible_pathAlmostComplex h₀ (hc₁ p.2 hp.2 z hz) (hc₂ p.2 hp.2 z hz)) hu
      (hF₁ p.2 hp.2) hux hδ).1 (hFr₁ p.2 hp.2)
  · exact fun μ ↦ by simp only [pathAlmostComplex_zero, pathHamiltonian_zero]
  · exact fun μ ↦ by simp only [pathAlmostComplex_one, pathHamiltonian_one]
  · exact fun σ _ ↦ by
      simp only [pathAlmostComplex_of_eq h₀ _ (congrFun (hJa _) _),
        pathHamiltonian_of_eq _ (hKsa _), pathHamiltonian_of_eq _ (hKta _)]
  · exact fun σ _ ↦ by
      simp only [pathAlmostComplex_of_eq h₀ _ (congrFun (hJb _) _),
        pathHamiltonian_of_eq _ (hKsb _), pathHamiltonian_of_eq _ (hKtb _)]

/-- **Orientation transport around a loop of pair-of-pants data is trivial.** Under the
hypotheses of
`TauCeti.SymplecticForm.detLineOrientationTransport_floerConformalSobolevOperator_pairOfPants_congr`
on a single path `μ ↦ (J_μ, K_{s,μ}, K_{t,μ})` of pair-of-pants data with fixed end data and the
same data at `μ = a` and at `μ = b`, transporting an orientation of the determinant line of `D_u`
from `a` to `b` along the path is the identification of the determinant lines of the equal operators
at `a` and at `b`. So the determinant lines of the pair-of-pants operator are orientable over every
loop of data with fixed end data. -/
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
    {J : ℝ × (ℝ × ℝ) → V → AlmostComplexStructure V} {Ks Kt : ℝ × (ℝ × ℝ) → V → ℝ} {R₁ : ℝ}
    {u : ℝ × ℝ → V} {a b : ℝ}
    (hJeq : ∀ μ ∈ uIcc a b, ∀ q (ζ : ℝ × ℝ), R₁ ≤ ζ.1 → J (μ, positiveEndChart q ζ) = Je q ζ.2)
    (hK : ∀ μ ∈ uIcc a b, ∀ q, ∀ z ∈ thricePuncturedSphereReal, R₁ ≤ (positiveEndCoord q z).1 →
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
    (hF : ∀ μ ∈ uIcc a b, ∀ q, ∀ z ∈ thricePuncturedSphereReal, R₁ ≤ (positiveEndCoord q z).1 →
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
  have hg : ContDiff ℝ ⊤ fun p : (ℝ × (ℝ × ℝ)) × V ↦ ((a, p.1.2), p.2) :=
    (contDiff_const.prodMk contDiff_fst.snd).prodMk contDiff_snd
  have key := detLineOrientationTransport_floerConformalSobolevOperator_pairOfPants_congr ω hH
    hHs hX hx hnd hJe hJex (J₂ := fun p ↦ J (a, p.2)) (Ks₂ := fun p ↦ Ks (a, p.2))
    (Kt₂ := fun p ↦ Kt (a, p.2)) hJeq (fun _ _ ↦ hJeq a ha) hK (fun _ _ ↦ hK a ha) hJ
    (fun μ _ z hz ↦ ((hJ a ha z hz).comp ((μ, z), u z) (hg.of_le le_top).contDiffAt :)) hKs hKt
    (fun μ _ z hz ↦ ((hKs a ha z hz).comp ((μ, z), u z) (hg.of_le le_top).contDiffAt :))
    (fun μ _ z hz ↦ ((hKt a ha z hz).comp ((μ, z), u z) (hg.of_le le_top).contDiffAt :))
    hJt (fun p ↦ hJt (a, p.2)) hc (fun _ _ ↦ hc a ha) hu hF hux hδ (fun _ ↦ rfl) (fun _ ↦ rfl)
    (fun _ ↦ rfl) (fun w ↦ (hJab w).symm) (fun w ↦ (hKsab w).symm) (fun w ↦ (hKtab w).symm) hT hFr
    (continuousOn_const.congr fun μ _ ↦ hconst μ) (fun μ _ ↦ by rw [hconst μ]; exact hFr a ha)
  have := congrFun key o
  rw [Function.comp_apply, Function.comp_apply, detLineOrientationTransport_eq_map_of_forall_eq _ _
    fun μ _ ↦ (hconst μ).trans (hconst a).symm] at this
  rw [← (Equiv.symm_apply_eq _).2 this, Module.Ray.map_symm, LinearMap.detLineCongrOfEq_symm]
  simp only [LinearMap.map_detLineCongrOfEq_map_detLineCongrOfEq]

end TauCeti.SymplecticForm
