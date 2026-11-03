/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Riemannian.Isometry.Ext
import TauCeti.Geometry.Manifold.IsManifold.Basic
import Mathlib.Topology.Connected.LocallyConnected

/-!
# Finite frame determination of Riemannian isometries

On a possibly disconnected manifold, a smooth Riemannian isometry is determined by its
value and differential on one tangent basis in each connected component. The tangent
vectors are evaluated in the total tangent bundle of the target, so their image base points
are retained. A separate point evaluation also handles zero-dimensional manifolds, whose
frames are empty.

On a compact manifold only finitely many components occur. We choose one point and an
orthonormal tangent frame per component and prove that the resulting finite evaluation map
is injective. The image points retain the destinations of all the components; in particular
no assumption that an isometry preserves each component is made. These are rigidity
statements, not assertions about continuity or derivative bounds for the evaluation map.

## References

* J. M. Lee, *Introduction to Riemannian Manifolds*, second edition, Proposition 5.22
  (determination by first-order data).
* S. B. Myers and N. E. Steenrod, *The group of isometries of a Riemannian manifold*,
  Ann. of Math. 40 (1939), 400–416, for the use of frame evaluation in isometry groups.
-/

public section

noncomputable section

open Bundle Manifold Set
open scoped ContDiff Manifold

namespace TauCeti.RiemannianIsometry

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [FiniteDimensional ℝ E] [I.Boundaryless] [T2Space M]
  [RiemannianBundle (fun x : M => TangentSpace I x)] [IsManifold I ∞ M]
  [IsContMDiffRiemannianBundle I ∞ E (fun x : M => TangentSpace I x)]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {H' : Type*} [TopologicalSpace H'] {J : ModelWithCorners ℝ F H'}
  {N : Type*} [TopologicalSpace N] [ChartedSpace H' N]
  [FiniteDimensional ℝ F] [J.Boundaryless] [T2Space N]
  [RiemannianBundle (fun y : N => TangentSpace J y)] [IsManifold J ∞ N]
  [IsContMDiffRiemannianBundle J ∞ F (fun y : N => TangentSpace J y)]

/-- Agreement on a tangent basis at one point determines an isometry on that point's
connected component. The images of basis vectors are compared in the total tangent bundle. -/
theorem eqOn_connectedComponent_of_tangentMap_basis_eq {ι : Type*}
    (Φ Ψ : RiemannianIsometry I J M N) {p : M} (b : Module.Basis ι ℝ (TangentSpace I p))
    (hp : Φ p = Ψ p)
    (hb : ∀ i, tangentMap I J Φ ⟨p, b i⟩ = tangentMap I J Ψ ⟨p, b i⟩) :
    EqOn Φ Ψ (connectedComponent p) := by
  apply Φ.eqOn_connectedComponent_of_mfderiv_eq Ψ hp
  apply ContinuousLinearMap.coe_injective
  apply b.ext
  intro i
  exact congrArg (fun z : TangentBundle J N => (z.2 : F)) (hb i)

/-- Frame evaluation is injective if the sampled points meet every connected component.
The bases need not be orthonormal, and neither compactness nor finiteness of the sample
family is required. -/
theorem injective_tangentMap_basis_of_forall_mem_connectedComponent {κ ι : Type*} (p : κ → M)
    (hp : ∀ x : M, ∃ c, x ∈ connectedComponent (p c))
    (b : ∀ c, Module.Basis ι ℝ (TangentSpace I (p c))) :
    Function.Injective (fun Φ : RiemannianIsometry I J M N =>
      fun c => (Φ (p c), fun i => tangentMap I J Φ ⟨p c, b c i⟩)) := by
  intro Φ Ψ h
  apply ext
  intro x
  obtain ⟨c, hc⟩ := hp x
  have he := congrFun h c
  exact Φ.eqOn_connectedComponent_of_tangentMap_basis_eq Ψ (b c)
    (congrArg Prod.fst he) (fun i => congrFun (congrArg Prod.snd he) i) hc

/-- On a compact manifold, one orthonormal tangent frame in each of finitely many components
determines a smooth Riemannian isometry. The component map of the sampled points is bijective,
so the data include exactly one point per component. Image points are recorded even in
dimension zero. -/
theorem exists_orthonormalBasis_injective_tangentMap [CompactSpace M] :
    ∃ (k : ℕ) (p : Fin k → M)
      (b : ∀ c, OrthonormalBasis (Fin (Module.finrank ℝ E)) ℝ (TangentSpace I (p c))),
      Function.Bijective (fun c => ConnectedComponents.mk (p c)) ∧
      Function.Injective (fun Φ : RiemannianIsometry I J M N =>
        fun c => (Φ (p c), fun i => tangentMap I J Φ ⟨p c, b c i⟩)) := by
  classical
  have : LocallyConnectedSpace H := I.toHomeomorph.locallyConnectedSpace
  have : LocallyConnectedSpace M := ChartedSpace.locallyConnectedSpace H M
  let := Fintype.ofFinite (ConnectedComponents M)
  let e := (Fintype.equivFin (ConnectedComponents M)).symm
  choose r hr using ConnectedComponents.surjective_coe (α := M)
  let p := r ∘ e
  have hp (c) : ConnectedComponents.mk (p c) = e c := hr (e c)
  let b (c) := (stdOrthonormalBasis ℝ (TangentSpace I (p c))).reindex
    (finCongr (TauCeti.finrank_tangentSpace (I := I) (p c)))
  refine ⟨_, p, b, ?_,
    injective_tangentMap_basis_of_forall_mem_connectedComponent p ?_ (fun c => (b c).toBasis)⟩
  · have heq : (fun c => ConnectedComponents.mk (p c)) = e := funext hp
    rw [heq]
    exact e.bijective
  · intro x
    obtain ⟨c, hc⟩ := e.surjective (ConnectedComponents.mk x)
    refine ⟨c, ConnectedComponents.coe_eq_coe'.1 ?_⟩
    exact hc.symm.trans (hp c).symm

end TauCeti.RiemannianIsometry
