/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Fredholm.DeterminantLine.Homotopy
public import TauCeti.Geometry.Symplectic.Floer.Plane.Invariance
import TauCeti.Geometry.Symplectic.ExistsCompatible
import TauCeti.Geometry.Symplectic.Floer.Continuation.Path

/-!
# Orientation transport for a PSS plane along paths of almost complex structures

Let `u` be a finite-energy solution of the Floer equation of the positive PSS plane for a
period-one Hamiltonian `H` on a finite-dimensional symplectic inner product space `(V, ω)`, on the
end `‖w‖ > r` of the plane, asymptotic to nondegenerate one-periodic orbits of `H`. For almost
complex structures `J` that are compatible with `ω` along `u` on the disc `‖w‖ ≤ r` and equal on the
end to a fixed family `J_q(t)`, the realization `D_u : W^{1,2}(ℂ, V) → L²(ℂ, V)` of the linearized
Floer operator is Fredholm
(`TauCeti.SymplecticForm.isFredholm_floerConformalSobolevOperator_of_finite_energy_positive`), so it
has a determinant line `det (ker D_u) ⊗ (det (coker D_u))^*`. Orienting the moduli spaces of PSS
planes starts from orientations of these lines, and they must be compared for different choices of
the structure over the disc.

Along a path `μ ↦ J_μ` of such structures, jointly `C¹` in the parameter along `u`, the operators
`D_u` depend continuously on `μ` in operator norm
(`TauCeti.SymplecticForm.continuous_floerConformalSobolevOperator_positive_family`), so orientations
of their determinant lines are transported along the path (`TauCeti.detLineOrientationTransport`).
This file proves that the transport depends only on the endpoints of the path
(`TauCeti.SymplecticForm.detLineOrientationTransport_floerConformalSobolevOperator_pssPlane_congr`):
for two paths of structures defined on `[[a, b]]` and agreeing at `a` and at `b`, the transports
from `a` to `b` along the two paths agree, once the determinant lines of the equal operators at `a`
and at `b` are identified. In particular, transport around a loop of structures is trivial
(`detLineOrientationTransport_floerConformalSobolevOperator_pssPlane_eq_map`, in the namespace
`TauCeti.SymplecticForm`), so the determinant lines of a PSS plane are orientable over every loop
of almost complex structures with fixed end values. These are the PSS-plane counterparts of the
cylinder statements
`TauCeti.SymplecticForm.detLineOrientationTransport_floerSobolevOperator_congr` and
`TauCeti.SymplecticForm.detLineOrientationTransport_floerSobolevOperator_eq_map`.

The proof joins the two paths by a homotopy relative to the endpoints: at `(σ, μ)` it takes the
structure whose Cayley coordinates, relative to a fixed compatible structure, lie at `σ` on the
segment between those of the two paths at `μ` (`TauCeti.Floer.pathAlmostComplex`). This homotopy
is compatible along `u` on the disc, agrees with `J_q(t)` on the end, and is `C³` along `u` in both
parameters, so its operators are Fredholm and depend continuously on `(σ, μ)`, and orientation
transport is invariant under it (`TauCeti.detLineOrientationTransport_eq_of_homotopy_of_eq`).

Every PSS plane is the positive plane for a rescaled Hamiltonian
(`TauCeti.Floer.PSSPlane.perturbation_eq_positive`), so the statements cover the negative plane as
well.

## Main results

* `TauCeti.SymplecticForm.detLineOrientationTransport_floerConformalSobolevOperator_pssPlane_congr`:
  orientation transport of the determinant lines of `D_u` along a path of almost complex structures
  with fixed end values depends only on the structures at the endpoints.
* `TauCeti.SymplecticForm.detLineOrientationTransport_floerConformalSobolevOperator_pssPlane_eq_map`
  states that orientation transport around a loop of such structures is trivial.

## References

* A. Floer and H. Hofer, *Coherent orientations for periodic orbit problems in symplectic
  geometry*, Math. Z. 212 (1993), 13–38, on orienting the determinant lines of the linearized
  Floer operators through the contractibility of the spaces of data with fixed asymptotics.
* S. Piunikhin, D. Salamon and M. Schwarz, *Symplectic Floer–Donaldson theory and quantum
  cohomology*, in *Contact and symplectic geometry*, Publ. Newton Inst. 8 (1996), 171–200, on the
  PSS planes and their Fredholm theory.
* D. McDuff and D. Salamon, *J-holomorphic Curves and Symplectic Topology*, second edition,
  AMS Colloquium Publications 52, 2012, Section A.2 (determinant line bundles).
-/

public section

noncomputable section

open Set Function Filter MeasureTheory
open scoped ENNReal NNReal Manifold

namespace TauCeti.SymplecticForm

open Floer Floer.PSSPlane ConformalSobolev

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]

/-- The homotopy of almost complex structures between two paths `μ ↦ J_{1,μ}` and `μ ↦ J_{2,μ}`,
`((σ, μ), z) ↦ J_{σ,μ}(z)` with `J_{σ,μ}` at `σ` on the path between `J_{1,μ}` and `J_{2,μ}`
(`TauCeti.Floer.pathAlmostComplex`), is `Cⁿ` along `u` jointly in `(σ, μ)` and the domain point when
the two paths are. -/
private theorem contDiffAt_pathAlmostComplex_homotopy {n : ℕ∞} {ω : SymplecticForm V}
    {J₀ : AlmostComplexStructure V} (h₀ : ω.Compatible J₀)
    {J₁ J₂ : ℝ × (ℝ × ℝ) → V → AlmostComplexStructure V} (hJt₁ : ∀ p y, ω.Tames (J₁ p y))
    (hJt₂ : ∀ p y, ω.Tames (J₂ p y)) {u : ℝ × ℝ → V}
    (hJ₁ : ∀ p, ContDiffAt ℝ n
      (fun q : (ℝ × (ℝ × ℝ)) × V ↦ (J₁ q.1 q.2).toLinearMap.toContinuousLinearMap) (p, u p.2))
    (hJ₂ : ∀ p, ContDiffAt ℝ n
      (fun q : (ℝ × (ℝ × ℝ)) × V ↦ (J₂ q.1 q.2).toLinearMap.toContinuousLinearMap) (p, u p.2))
    (p z : ℝ × ℝ) :
    ContDiffAt ℝ n (fun q : ((ℝ × ℝ) × (ℝ × ℝ)) × V ↦
      (pathAlmostComplex h₀ hJt₁ hJt₂ (q.1.1.1, (q.1.1.2, q.1.2)) q.2).toLinearMap
        |>.toContinuousLinearMap) ((p, z), u z) :=
  -- The homotopy is the path of structures composed with the reassociation
  -- `((σ, μ), z) ↦ (σ, (μ, z))`; the ascription elaborates that composite before matching it.
  ((contDiffAt_pathAlmostComplex h₀ hJt₁ hJt₂ (p := (p.1, (p.2, z))) (hJ₁ (p.2, z))
    (hJ₂ (p.2, z))).comp ((p, z), u z)
    (((contDiff_fst.fst.fst.prodMk (contDiff_fst.fst.snd.prodMk contDiff_fst.snd)).prodMk
      contDiff_snd).contDiffAt) :)

/-- The operators of a PSS plane along the homotopy of almost complex structures between two paths
of structures with the end values `J_q(t)` are continuous in `(σ, μ)`, and Fredholm where both
paths are compatible with `ω` along `u` on the disc. -/
private theorem continuousOn_and_isFredholm_pathAlmostComplex_homotopy
    (ω : SymplecticForm V) {H : ℝ → V → ℝ} (hH : Periodic H 1) (hHs : ContDiff ℝ 4 (uncurry H))
    {L : ℝ≥0} (hL : LipschitzWith L (ω.timeDependentHamiltonianSuspension H)) {K : Set V}
    (hK : IsCompact K) {Jq : ℝ → V → AlmostComplexStructure V}
    (hJq : ContDiff ℝ 2 fun q : ℝ × V ↦ (Jq q.1 q.2).toLinearMap.toContinuousLinearMap)
    (hJqper : Periodic Jq 1) (hJqK : ∀ t, ∀ y ∈ K, ω.Compatible (Jq t y))
    {J₁ J₂ : ℝ × (ℝ × ℝ) → V → AlmostComplexStructure V} {r : ℝ} {u : ℝ × ℝ → V} {a b : ℝ}
    (hJ₁ : ∀ p, ContDiffAt ℝ 3
      (fun q : (ℝ × (ℝ × ℝ)) × V ↦ (J₁ q.1 q.2).toLinearMap.toContinuousLinearMap) (p, u p.2))
    (hJ₂ : ∀ p, ContDiffAt ℝ 3
      (fun q : (ℝ × (ℝ × ℝ)) × V ↦ (J₂ q.1 q.2).toLinearMap.toContinuousLinearMap) (p, u p.2))
    (hJt₁ : ∀ p y, ω.Tames (J₁ p y)) (hJt₂ : ∀ p y, ω.Tames (J₂ p y))
    (hJr₁ : ∀ μ z, r < ‖Complex.equivRealProdCLM.symm z‖ →
      J₁ (μ, z) = Jq (positive.endCoord (Complex.equivRealProdCLM.symm z)).im)
    (hJr₂ : ∀ μ z, r < ‖Complex.equivRealProdCLM.symm z‖ →
      J₂ (μ, z) = Jq (positive.endCoord (Complex.equivRealProdCLM.symm z)).im)
    (hc₁ : ∀ μ ∈ uIcc a b, ∀ z, ‖Complex.equivRealProdCLM.symm z‖ ≤ r →
      ω.Compatible (J₁ (μ, z) (u z)))
    (hc₂ : ∀ μ ∈ uIcc a b, ∀ z, ‖Complex.equivRealProdCLM.symm z‖ ≤ r →
      ω.Compatible (J₂ (μ, z) (u z)))
    (hu : ContDiff ℝ 3 u) (huK : ∀ z, r < ‖Complex.equivRealProdCLM.symm z‖ → u z ∈ K)
    (hF : ∀ z, r < ‖Complex.equivRealProdCLM.symm z‖ →
      IsComplexLinearMap (AlmostComplexStructure.product ℝ)
        (Jq (positive.endCoord (Complex.equivRealProdCLM.symm z)).im (u z))
        (ω.perturbedFDeriv
          (fun z x ↦ positive.perturbation H (Complex.equivRealProdCLM.symm z) x 1)
          (fun z x ↦ positive.perturbation H (Complex.equivRealProdCLM.symm z) x Complex.I) u
          z : ℝ × ℝ →ₗ[ℝ] V))
    (hE : ∫⁻ z in {z | r < ‖Complex.equivRealProdCLM.symm z‖},
      ENNReal.ofReal (ω.floerEnergyDensity
        (fun z x ↦ positive.perturbation H (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ positive.perturbation H (Complex.equivRealProdCLM.symm z) x Complex.I)
        u z) ≠ ⊤)
    (hnd : ∀ x : ℝ → V, Periodic x 1 →
      (∀ t, HasDerivAt x (ω.hamiltonianVectorField (H t) (x t)) t) → (∀ t, x t ∈ K) →
      IsNondegenerateFixedPt 𝓘(ℝ, V) (ω.timeDependentHamiltonianFlow H hL 0 1) (x 0))
    {J₀ : AlmostComplexStructure V} (h₀ : ω.Compatible J₀) :
    ContinuousOn (fun p : ℝ × ℝ ↦ ω.floerConformalSobolevOperator univ cylindricalWeight
      (fun z y ↦
        (pathAlmostComplex h₀ hJt₁ hJt₂ (p.1, (p.2, z)) y).toLinearMap.toContinuousLinearMap)
      (fun z x ↦ positive.perturbation H (Complex.equivRealProdCLM.symm z) x 1)
      (fun z x ↦ positive.perturbation H (Complex.equivRealProdCLM.symm z) x Complex.I) u)
      (uIcc 0 1 ×ˢ uIcc a b) ∧
    ∀ p ∈ uIcc 0 1 ×ˢ uIcc a b, (ω.floerConformalSobolevOperator univ cylindricalWeight
      (fun z y ↦
        (pathAlmostComplex h₀ hJt₁ hJt₂ (p.1, (p.2, z)) y).toLinearMap.toContinuousLinearMap)
      (fun z x ↦ positive.perturbation H (Complex.equivRealProdCLM.symm z) x 1)
      (fun z x ↦ positive.perturbation H (Complex.equivRealProdCLM.symm z) x Complex.I)
      u).IsFredholm := by
  -- On the end both paths are `J_q(t)`, hence so is every member of the homotopy.
  have hend (σ μ : ℝ) (z : ℝ × ℝ) (hz : r < ‖Complex.equivRealProdCLM.symm z‖) :
      pathAlmostComplex h₀ hJt₁ hJt₂ (σ, (μ, z)) =
        Jq (positive.endCoord (Complex.equivRealProdCLM.symm z)).im :=
    funext fun y ↦ (pathAlmostComplex_of_eq h₀ σ
      (congrFun ((hJr₁ μ z hz).trans (hJr₂ μ z hz).symm) y)).trans (congrFun (hJr₁ μ z hz) y)
  have hJH := contDiffAt_pathAlmostComplex_homotopy h₀ hJt₁ hJt₂ hJ₁ hJ₂
  -- The members at fixed `(σ, μ)` are `C³` along `u`.
  have hJμ (p : ℝ × ℝ) (z : ℝ × ℝ) : ContDiffAt ℝ 3 (fun q : (ℝ × ℝ) × V ↦
      (pathAlmostComplex h₀ hJt₁ hJt₂ (p.1, (p.2, q.1)) q.2).toLinearMap.toContinuousLinearMap)
      (z, u z) :=
    ((hJH p z).comp (z, u z)
      (((contDiff_const.prodMk contDiff_fst).prodMk contDiff_snd).contDiffAt) :)
  -- The Floer equation on the end, for every member of the homotopy.
  have hFμ (p : ℝ × ℝ) (z : ℝ × ℝ) (hz : r < ‖Complex.equivRealProdCLM.symm z‖) :
      IsComplexLinearMap (AlmostComplexStructure.product ℝ)
        (pathAlmostComplex h₀ hJt₁ hJt₂ (p.1, (p.2, z)) (u z))
        (ω.perturbedFDeriv
          (fun z x ↦ positive.perturbation H (Complex.equivRealProdCLM.symm z) x 1)
          (fun z x ↦ positive.perturbation H (Complex.equivRealProdCLM.symm z) x Complex.I) u
          z : ℝ × ℝ →ₗ[ℝ] V) := by
    rw [hend p.1 p.2 z hz]
    exact hF z hz
  refine ⟨(continuous_floerConformalSobolevOperator_positive_family ω hH
      (hHs.of_le (by norm_num)) (J := fun q : (ℝ × ℝ) × (ℝ × ℝ) ↦
        pathAlmostComplex h₀ hJt₁ hJt₂ (q.1.1, (q.1.2, q.2)))
      (fun p z ↦ (hJH p z).of_le (by norm_num)) (hu.of_le (by norm_num))
      (fun p p' z hz ↦ (hend p.1 p.2 z hz).trans (hend p'.1 p'.2 z hz).symm)
      fun p ↦ ?_).continuousOn, fun p hp ↦ ?_⟩
  · exact ω.memLp_floerConformalJetCoeff_of_finite_energy_positive hH (hHs.of_le (by norm_num))
      hL hK hJq hJqper (fun t y hy ↦ (hJqK t y hy).tames) (fun z ↦ (hJμ p z).of_le (by norm_num))
      (hend p.1 p.2) (hu.of_le (by norm_num)) hu.contDiffOn huK (hFμ p) hE hnd
  · -- Over the parameter rectangle the homotopy is compatible along `u` on the disc.
    exact ω.isFredholm_floerConformalSobolevOperator_of_finite_energy_positive hH hHs
      hL hK hJq hJqper hJqK (hJμ p) (hend p.1 p.2) hu
      (fun z hz ↦ compatible_pathAlmostComplex h₀ (p := (p.1, (p.2, z))) (hc₁ p.2 hp.2 z hz)
        (hc₂ p.2 hp.2 z hz)) huK (hFμ p) hE hnd

/-- **Orientation transport for a PSS plane depends only on the endpoints of the path of almost
complex structures.** Let `H` be a `C⁴` Hamiltonian of period one in time, with globally Lipschitz
suspended vector field, whose one-periodic orbits in a compact set `K` are nondegenerate. Let `u`
be a `C³` map of the plane that solves the Floer equation of the positive PSS plane for `H` on the
end `‖w‖ > r`, with finite energy there and values in `K`, for a `C²` family `J_q(t)` of period one
compatible with `ω` on `K`. Let `μ ↦ J_{i,μ}`, `i = 1, 2`, be two paths of almost complex structures
on the plane, jointly `C³` along `u` in the parameter, taming `ω`, equal to `J_q(t)` on the end, and
compatible with `ω` along `u` on the disc `‖w‖ ≤ r` for `μ ∈ [[a, b]]`, with the same structures at
`μ = a` and at `μ = b`. Then transporting an orientation of the determinant line of `D_u` for the
structure at `a` to `b` along the first path, and along the second path, gives the same orientation
of the determinant line of `D_u` for the structure at `b`, once the determinant lines of the equal
operators of the two paths at `a` and at `b` are identified by `LinearMap.detLineCongrOfEq`.

The continuity and the Fredholm property of the two paths of operators, which orientation
transport needs, hold by
`TauCeti.SymplecticForm.continuous_floerConformalSobolevOperator_positive_family` and
`TauCeti.SymplecticForm.isFredholm_floerConformalSobolevOperator_of_finite_energy_positive`. -/
theorem detLineOrientationTransport_floerConformalSobolevOperator_pssPlane_congr
    (ω : SymplecticForm V) {H : ℝ → V → ℝ} (hH : Periodic H 1) (hHs : ContDiff ℝ 4 (uncurry H))
    {L : ℝ≥0} (hL : LipschitzWith L (ω.timeDependentHamiltonianSuspension H)) {K : Set V}
    (hK : IsCompact K) {Jq : ℝ → V → AlmostComplexStructure V}
    (hJq : ContDiff ℝ 2 fun q : ℝ × V ↦ (Jq q.1 q.2).toLinearMap.toContinuousLinearMap)
    (hJqper : Periodic Jq 1) (hJqK : ∀ t, ∀ y ∈ K, ω.Compatible (Jq t y))
    {J₁ J₂ : ℝ × (ℝ × ℝ) → V → AlmostComplexStructure V} {r : ℝ} {u : ℝ × ℝ → V} {a b : ℝ}
    (hJ₁ : ∀ p, ContDiffAt ℝ 3
      (fun q : (ℝ × (ℝ × ℝ)) × V ↦ (J₁ q.1 q.2).toLinearMap.toContinuousLinearMap) (p, u p.2))
    (hJ₂ : ∀ p, ContDiffAt ℝ 3
      (fun q : (ℝ × (ℝ × ℝ)) × V ↦ (J₂ q.1 q.2).toLinearMap.toContinuousLinearMap) (p, u p.2))
    (hJt₁ : ∀ p y, ω.Tames (J₁ p y)) (hJt₂ : ∀ p y, ω.Tames (J₂ p y))
    (hJr₁ : ∀ μ z, r < ‖Complex.equivRealProdCLM.symm z‖ →
      J₁ (μ, z) = Jq (positive.endCoord (Complex.equivRealProdCLM.symm z)).im)
    (hJr₂ : ∀ μ z, r < ‖Complex.equivRealProdCLM.symm z‖ →
      J₂ (μ, z) = Jq (positive.endCoord (Complex.equivRealProdCLM.symm z)).im)
    (hc₁ : ∀ μ ∈ uIcc a b, ∀ z, ‖Complex.equivRealProdCLM.symm z‖ ≤ r →
      ω.Compatible (J₁ (μ, z) (u z)))
    (hc₂ : ∀ μ ∈ uIcc a b, ∀ z, ‖Complex.equivRealProdCLM.symm z‖ ≤ r →
      ω.Compatible (J₂ (μ, z) (u z)))
    (hu : ContDiff ℝ 3 u) (huK : ∀ z, r < ‖Complex.equivRealProdCLM.symm z‖ → u z ∈ K)
    (hF : ∀ z, r < ‖Complex.equivRealProdCLM.symm z‖ →
      IsComplexLinearMap (AlmostComplexStructure.product ℝ)
        (Jq (positive.endCoord (Complex.equivRealProdCLM.symm z)).im (u z))
        (ω.perturbedFDeriv
          (fun z x ↦ positive.perturbation H (Complex.equivRealProdCLM.symm z) x 1)
          (fun z x ↦ positive.perturbation H (Complex.equivRealProdCLM.symm z) x Complex.I) u
          z : ℝ × ℝ →ₗ[ℝ] V))
    (hE : ∫⁻ z in {z | r < ‖Complex.equivRealProdCLM.symm z‖},
      ENNReal.ofReal (ω.floerEnergyDensity
        (fun z x ↦ positive.perturbation H (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ positive.perturbation H (Complex.equivRealProdCLM.symm z) x Complex.I)
        u z) ≠ ⊤)
    (hnd : ∀ x : ℝ → V, Periodic x 1 →
      (∀ t, HasDerivAt x (ω.hamiltonianVectorField (H t) (x t)) t) → (∀ t, x t ∈ K) →
      IsNondegenerateFixedPt 𝓘(ℝ, V) (ω.timeDependentHamiltonianFlow H hL 0 1) (x 0))
    (hJa : ∀ z, J₁ (a, z) = J₂ (a, z)) (hJb : ∀ z, J₁ (b, z) = J₂ (b, z))
    (hT₁ : ContinuousOn (fun μ ↦ ω.floerConformalSobolevOperator univ cylindricalWeight
      (fun z y ↦ (J₁ (μ, z) y).toLinearMap.toContinuousLinearMap)
      (fun z x ↦ positive.perturbation H (Complex.equivRealProdCLM.symm z) x 1)
      (fun z x ↦ positive.perturbation H (Complex.equivRealProdCLM.symm z) x Complex.I) u)
      (uIcc a b))
    (hF₁ : ∀ μ ∈ uIcc a b, (ω.floerConformalSobolevOperator univ cylindricalWeight
      (fun z y ↦ (J₁ (μ, z) y).toLinearMap.toContinuousLinearMap)
      (fun z x ↦ positive.perturbation H (Complex.equivRealProdCLM.symm z) x 1)
      (fun z x ↦ positive.perturbation H (Complex.equivRealProdCLM.symm z) x Complex.I)
      u).IsFredholm)
    (hT₂ : ContinuousOn (fun μ ↦ ω.floerConformalSobolevOperator univ cylindricalWeight
      (fun z y ↦ (J₂ (μ, z) y).toLinearMap.toContinuousLinearMap)
      (fun z x ↦ positive.perturbation H (Complex.equivRealProdCLM.symm z) x 1)
      (fun z x ↦ positive.perturbation H (Complex.equivRealProdCLM.symm z) x Complex.I) u)
      (uIcc a b))
    (hF₂ : ∀ μ ∈ uIcc a b, (ω.floerConformalSobolevOperator univ cylindricalWeight
      (fun z y ↦ (J₂ (μ, z) y).toLinearMap.toContinuousLinearMap)
      (fun z x ↦ positive.perturbation H (Complex.equivRealProdCLM.symm z) x 1)
      (fun z x ↦ positive.perturbation H (Complex.equivRealProdCLM.symm z) x Complex.I)
      u).IsFredholm) :
    detLineOrientationTransport a b hT₂ hF₂ ∘
        Module.Ray.map (LinearMap.detLineCongrOfEq (by simp only [hJa])) =
      Module.Ray.map (LinearMap.detLineCongrOfEq (by simp only [hJb])) ∘
        detLineOrientationTransport a b hT₁ hF₁ := by
  funext o
  -- A structure compatible with `ω`, for the Cayley coordinates of the homotopy.
  obtain ⟨J₀, h₀⟩ := ω.exists_compatible
  -- The homotopy from the first path (`σ = 0`) to the second (`σ = 1`): at `(σ, μ)`, the path of
  -- almost complex structures between the two paths at `μ`, taken at `σ`.
  obtain ⟨hHc, hHF⟩ := continuousOn_and_isFredholm_pathAlmostComplex_homotopy ω hH hHs hL hK hJq
    hJqper hJqK hJ₁ hJ₂ hJt₁ hJt₂ hJr₁ hJr₂ hc₁ hc₂ hu huK hF hE hnd h₀
  refine detLineOrientationTransport_eq_of_homotopy_of_eq (s₀ := 0) (s₁ := 1) hHc hHF ?_ ?_ ?_ ?_
    hT₁ hF₁ hT₂ hF₂ _ _ o
  · exact fun μ ↦ by simp only [pathAlmostComplex_zero]
  · exact fun μ ↦ by simp only [pathAlmostComplex_one]
  · exact fun σ _ ↦ by simp only [pathAlmostComplex_of_eq h₀ _ (congrFun (hJa _) _)]
  · exact fun σ _ ↦ by simp only [pathAlmostComplex_of_eq h₀ _ (congrFun (hJb _) _)]

/-- **Orientation transport for a PSS plane around a loop of almost complex structures is
trivial.** Under the hypotheses of
`TauCeti.SymplecticForm.detLineOrientationTransport_floerConformalSobolevOperator_pssPlane_congr` on
a single path `μ ↦ J_μ` of almost complex structures with the same structure at `μ = a` and at
`μ = b`, transporting an orientation of the determinant line of `D_u` from `a` to `b` along the
path is the identification of the determinant lines of the equal operators at `a` and at `b`. So
the determinant lines of a PSS plane are orientable over every loop of almost complex structures
with fixed end values. -/
theorem detLineOrientationTransport_floerConformalSobolevOperator_pssPlane_eq_map
    (ω : SymplecticForm V) {H : ℝ → V → ℝ} (hH : Periodic H 1) (hHs : ContDiff ℝ 4 (uncurry H))
    {L : ℝ≥0} (hL : LipschitzWith L (ω.timeDependentHamiltonianSuspension H)) {K : Set V}
    (hK : IsCompact K) {Jq : ℝ → V → AlmostComplexStructure V}
    (hJq : ContDiff ℝ 2 fun q : ℝ × V ↦ (Jq q.1 q.2).toLinearMap.toContinuousLinearMap)
    (hJqper : Periodic Jq 1) (hJqK : ∀ t, ∀ y ∈ K, ω.Compatible (Jq t y))
    {J : ℝ × (ℝ × ℝ) → V → AlmostComplexStructure V} {r : ℝ} {u : ℝ × ℝ → V} {a b : ℝ}
    (hJ : ∀ p, ContDiffAt ℝ 3
      (fun q : (ℝ × (ℝ × ℝ)) × V ↦ (J q.1 q.2).toLinearMap.toContinuousLinearMap) (p, u p.2))
    (hJt : ∀ p y, ω.Tames (J p y))
    (hJr : ∀ μ z, r < ‖Complex.equivRealProdCLM.symm z‖ →
      J (μ, z) = Jq (positive.endCoord (Complex.equivRealProdCLM.symm z)).im)
    (hc : ∀ μ ∈ uIcc a b, ∀ z, ‖Complex.equivRealProdCLM.symm z‖ ≤ r →
      ω.Compatible (J (μ, z) (u z)))
    (hu : ContDiff ℝ 3 u) (huK : ∀ z, r < ‖Complex.equivRealProdCLM.symm z‖ → u z ∈ K)
    (hF : ∀ z, r < ‖Complex.equivRealProdCLM.symm z‖ →
      IsComplexLinearMap (AlmostComplexStructure.product ℝ)
        (Jq (positive.endCoord (Complex.equivRealProdCLM.symm z)).im (u z))
        (ω.perturbedFDeriv
          (fun z x ↦ positive.perturbation H (Complex.equivRealProdCLM.symm z) x 1)
          (fun z x ↦ positive.perturbation H (Complex.equivRealProdCLM.symm z) x Complex.I) u
          z : ℝ × ℝ →ₗ[ℝ] V))
    (hE : ∫⁻ z in {z | r < ‖Complex.equivRealProdCLM.symm z‖},
      ENNReal.ofReal (ω.floerEnergyDensity
        (fun z x ↦ positive.perturbation H (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ positive.perturbation H (Complex.equivRealProdCLM.symm z) x Complex.I)
        u z) ≠ ⊤)
    (hnd : ∀ x : ℝ → V, Periodic x 1 →
      (∀ t, HasDerivAt x (ω.hamiltonianVectorField (H t) (x t)) t) → (∀ t, x t ∈ K) →
      IsNondegenerateFixedPt 𝓘(ℝ, V) (ω.timeDependentHamiltonianFlow H hL 0 1) (x 0))
    (hJab : ∀ z, J (a, z) = J (b, z))
    (hT : ContinuousOn (fun μ ↦ ω.floerConformalSobolevOperator univ cylindricalWeight
      (fun z y ↦ (J (μ, z) y).toLinearMap.toContinuousLinearMap)
      (fun z x ↦ positive.perturbation H (Complex.equivRealProdCLM.symm z) x 1)
      (fun z x ↦ positive.perturbation H (Complex.equivRealProdCLM.symm z) x Complex.I) u)
      (uIcc a b))
    (hFr : ∀ μ ∈ uIcc a b, (ω.floerConformalSobolevOperator univ cylindricalWeight
      (fun z y ↦ (J (μ, z) y).toLinearMap.toContinuousLinearMap)
      (fun z x ↦ positive.perturbation H (Complex.equivRealProdCLM.symm z) x 1)
      (fun z x ↦ positive.perturbation H (Complex.equivRealProdCLM.symm z) x Complex.I)
      u).IsFredholm) :
    ∀ o, detLineOrientationTransport a b hT hFr o =
      Module.Ray.map (LinearMap.detLineCongrOfEq (by simp only [hJab])) o := by
  intro o
  have hT₀ := hFr a left_mem_uIcc
  -- Compare the path with the constant path at the structure at `a`, along which transport is the
  -- identity: its operator at `μ` is that at `a`.
  have hconst (μ : ℝ) :
      ω.floerConformalSobolevOperator univ cylindricalWeight
          (fun z y ↦ (J (a, (μ, z).2) y).toLinearMap.toContinuousLinearMap)
          (fun z x ↦ positive.perturbation H (Complex.equivRealProdCLM.symm z) x 1)
          (fun z x ↦ positive.perturbation H (Complex.equivRealProdCLM.symm z) x Complex.I) u =
        ω.floerConformalSobolevOperator univ cylindricalWeight
          (fun z y ↦ (J (a, z) y).toLinearMap.toContinuousLinearMap)
          (fun z x ↦ positive.perturbation H (Complex.equivRealProdCLM.symm z) x 1)
          (fun z x ↦ positive.perturbation H (Complex.equivRealProdCLM.symm z) x Complex.I) u := by
    simp only
  have hg : ContDiff ℝ ⊤ fun p : (ℝ × (ℝ × ℝ)) × V ↦ ((a, p.1.2), p.2) :=
    (contDiff_const.prodMk contDiff_fst.snd).prodMk contDiff_snd
  have key := detLineOrientationTransport_floerConformalSobolevOperator_pssPlane_congr ω hH hHs hL
    hK hJq hJqper hJqK (J₂ := fun p ↦ J (a, p.2)) hJ
    (fun p ↦ ((hJ (a, p.2)).comp (p, u p.2) (hg.of_le le_top).contDiffAt :)) hJt
    (fun p ↦ hJt (a, p.2)) hJr (fun _ ↦ hJr a) hc (fun _ _ ↦ hc a left_mem_uIcc) hu huK hF hE hnd
    (fun _ ↦ rfl) (fun z ↦ (hJab z).symm) hT hFr
    (continuousOn_const.congr fun μ _ ↦ hconst μ) (fun μ _ ↦ by rw [hconst μ]; exact hT₀)
  exact detLineOrientationTransport_eq_map_of_comp_eq_of_forall_eq hT _ _ _
    (fun μ _ ↦ (hconst μ).trans (hconst a).symm) _ _ key o

end TauCeti.SymplecticForm
