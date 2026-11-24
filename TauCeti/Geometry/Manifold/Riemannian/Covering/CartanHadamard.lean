/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicTopology.FundamentalGroupoid.SimplyConnected
public import Mathlib.Geometry.Manifold.LocalDiffeomorph
public import Mathlib.Geometry.Manifold.Riemannian.Basic
public import Mathlib.Geometry.Manifold.VectorBundle.CovariantDerivative.LeviCivita
public import Mathlib.Topology.Covering.Basic
public import Mathlib.Topology.Homotopy.Contractible
public import TauCeti.Geometry.Manifold.Riemannian.Geodesic.Exponential
public import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.Curvature.Sectional.Basic
import Mathlib.Analysis.Convex.Contractible
import TauCeti.Geometry.Manifold.Riemannian.Covering.Criterion
import TauCeti.Geometry.Manifold.Riemannian.Geodesic.Completeness
import TauCeti.Geometry.Manifold.Riemannian.Jacobi.Comparison
import TauCeti.Geometry.Manifold.Riemannian.Jacobi.Nonsingular
import TauCeti.Geometry.Manifold.LocalDiffeomorph.Basic
import TauCeti.Topology.Covering.Clopen
import TauCeti.Topology.Homotopy.Covering

/-!
# The Cartan–Hadamard theorem

Let `M` be a complete Riemannian manifold of nonpositive sectional curvature and `p ∈ M`. By the
Hopf–Rinow theorem the exponential map `exp_p` is defined on all of `T_p M`. Nonpositive curvature
makes its differential nondecreasing on lengths,
`|w| ≤ |d(exp_p)_v(w)|` (`norm_le_norm_mfderiv_riemannianExp_of_sectionalCurvature_nonpos`), so
in particular `exp_p` is a local diffeomorphism. The flat space `T_p M` is complete, so the
covering criterion for length-nondecreasing local diffeomorphisms
(`TauCeti.Manifold.isCoveringMap_of_norm_le_norm_mfderiv`) makes `exp_p` a covering map. It is
surjective when `M` is connected, since `T_p M` is nonempty.

When `M` is moreover simply connected, a covering map from the connected space `T_p M` is
injective, so `exp_p` is a diffeomorphism `T_p M ≃ M`, and `M` is contractible.

## Main results

* `TauCeti.Manifold.cartanHadamard_isCoveringMap`: **the Cartan–Hadamard theorem**, `exp_p` is a
  covering map.
* `TauCeti.Manifold.isLocalDiffeomorph_riemannianExp_of_sectionalCurvature_nonpos`: `exp_p` is
  a smooth local diffeomorphism on all of `T_p M`.
* `TauCeti.Manifold.cartanHadamard_surjective`: `exp_p` is surjective when `M` is connected.
* `TauCeti.Manifold.cartanHadamard_bijective`: `exp_p` is bijective when `M` is simply connected.
* `TauCeti.Manifold.cartanHadamardDiffeomorph`: for simply connected `M`, `exp_p` is a smooth
  diffeomorphism `T_p M ≃ M`.
* `TauCeti.Manifold.cartanHadamard_contractibleSpace`: a simply connected complete manifold of
  nonpositive sectional curvature is contractible.

## References

* L. I. Nicolaescu, *Lectures on the Geometry of Manifolds*, 3rd ed., World Scientific, 2020,
  Theorem 6.2.6.
* M. P. do Carmo, *Riemannian Geometry*, Birkhäuser, 1992, Ch. 7, §3, Theorem 3.1.
-/

public section

open Bundle CovariantDerivative Function Set
open scoped ContDiff Manifold

noncomputable section

namespace TauCeti.Manifold

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [EMetricSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)]
  [IsRiemannianManifold I M] [CompleteSpace M]

/-- On a complete Riemannian manifold of nonpositive sectional curvature, the exponential map at
any point is a smooth local diffeomorphism on the whole tangent space. -/
theorem isLocalDiffeomorph_riemannianExp_of_sectionalCurvature_nonpos
    (hK : ∀ x : M, ∀ u w : TangentSpace I x, LinearIndependent ℝ ![u, w] →
      (leviCivitaConnection I M).sectionalCurvature (isMetricCompatible_leviCivitaConnection I)
        x u w ≤ 0) (p : M) :
    IsLocalDiffeomorph 𝓘(ℝ, TangentSpace I p) I ∞ (riemannianExp I M p) := by
  have hdom : expDomain I M p = univ := expDomain_eq_univ_of_completeSpace p
  exact fun v ↦ isLocalDiffeomorphAt_riemannianExp_of_sectionalCurvature_nonpos
    (hdom ▸ mem_univ v) fun t _ ↦ hK (riemannianExp I M p (t • v))

/-- **The Cartan–Hadamard theorem.** On a complete Riemannian manifold of nonpositive sectional
curvature, the exponential map at any point is a covering map from the tangent space. -/
theorem cartanHadamard_isCoveringMap
    (hK : ∀ x : M, ∀ u w : TangentSpace I x, LinearIndependent ℝ ![u, w] →
      (leviCivitaConnection I M).sectionalCurvature (isMetricCompatible_leviCivitaConnection I)
        x u w ≤ 0) (p : M) :
    IsCoveringMap (riemannianExp I M p) := by
  have hdom : expDomain I M p = univ := expDomain_eq_univ_of_completeSpace p
  exact isCoveringMap_of_norm_le_norm_mfderiv
    (isLocalDiffeomorph_riemannianExp_of_sectionalCurvature_nonpos hK p) fun v w ↦
      norm_le_norm_mfderiv_riemannianExp_of_sectionalCurvature_nonpos (hdom ▸ mem_univ v)
        (fun t _ ↦ hK (riemannianExp I M p (t • v))) w

/-- On a connected complete Riemannian manifold of nonpositive sectional curvature, the
exponential map at any point is surjective. -/
theorem cartanHadamard_surjective [PreconnectedSpace M]
    (hK : ∀ x : M, ∀ u w : TangentSpace I x, LinearIndependent ℝ ![u, w] →
      (leviCivitaConnection I M).sectionalCurvature (isMetricCompatible_leviCivitaConnection I)
        x u w ≤ 0) (p : M) :
    Surjective (riemannianExp I M p) :=
  (cartanHadamard_isCoveringMap hK p).surjective

/-- On a simply connected complete Riemannian manifold of nonpositive sectional curvature, the
exponential map at any point is bijective. -/
theorem cartanHadamard_bijective [SimplyConnectedSpace M]
    (hK : ∀ x : M, ∀ u w : TangentSpace I x, LinearIndependent ℝ ![u, w] →
      (leviCivitaConnection I M).sectionalCurvature (isMetricCompatible_leviCivitaConnection I)
        x u w ≤ 0) (p : M) :
    Bijective (riemannianExp I M p) :=
  ⟨(cartanHadamard_isCoveringMap hK p).injective, cartanHadamard_surjective hK p⟩

/-- **The Cartan–Hadamard theorem, simply connected form.** On a simply connected complete
Riemannian manifold of nonpositive sectional curvature, the exponential map at any point is a
smooth diffeomorphism from the tangent space onto the manifold. -/
def cartanHadamardDiffeomorph [SimplyConnectedSpace M]
    (hK : ∀ x : M, ∀ u w : TangentSpace I x, LinearIndependent ℝ ![u, w] →
      (leviCivitaConnection I M).sectionalCurvature (isMetricCompatible_leviCivitaConnection I)
        x u w ≤ 0) (p : M) :
    TangentSpace I p ≃ₘ^∞⟮𝓘(ℝ, TangentSpace I p), I⟯ M :=
  (isLocalDiffeomorph_riemannianExp_of_sectionalCurvature_nonpos hK p).diffeomorphOfBijective
    (cartanHadamard_bijective hK p)

/-- The forward map of `cartanHadamardDiffeomorph` is the exponential map. -/
@[simp]
theorem coe_cartanHadamardDiffeomorph [SimplyConnectedSpace M]
    (hK : ∀ x : M, ∀ u w : TangentSpace I x, LinearIndependent ℝ ![u, w] →
      (leviCivitaConnection I M).sectionalCurvature (isMetricCompatible_leviCivitaConnection I)
        x u w ≤ 0) (p : M) :
    ⇑(cartanHadamardDiffeomorph hK p) = riemannianExp I M p :=
  IsLocalDiffeomorph.coe_diffeomorphOfBijective _ _

/-- A simply connected complete Riemannian manifold of nonpositive sectional curvature is
contractible. -/
theorem cartanHadamard_contractibleSpace [SimplyConnectedSpace M]
    (hK : ∀ x : M, ∀ u w : TangentSpace I x, LinearIndependent ℝ ![u, w] →
      (leviCivitaConnection I M).sectionalCurvature (isMetricCompatible_leviCivitaConnection I)
        x u w ≤ 0) :
    ContractibleSpace M := by
  obtain ⟨p⟩ : Nonempty M := inferInstance
  exact (cartanHadamardDiffeomorph hK p).toHomeomorph.symm.contractibleSpace

end TauCeti.Manifold
