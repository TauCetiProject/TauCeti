/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.DGLocalSystem.Transport
public import TauCeti.Topology.PathSpace.Moore.Replacement.FiberHomotopyEquiv

/-!
# Invariance of the DG local system of a map

The DG local system `C_*(F')` of a map `p : E → B` at `b` is built from the fibre `F'` of the
Moore-path replacement of `p` (`TauCeti.fibrationLocalSystem`). This file shows that, up to
quasi-isomorphism, it depends only on `p` up to fibre homotopy equivalence, and that it does not
change when `p` is replaced by its own Moore-path replacement.

* A fibre homotopy equivalence `Φ` from `p` to `q` over `B` induces a homotopy equivalence of the
  fibres of the replacements whose forward map is strictly equivariant, so the induced morphism
  `C_*(F'_p) → C_*(F'_q)` of DG local systems is a quasi-isomorphism
  (`TauCeti.FiberHomotopyEquiv.isQuasiIso_fibrationLocalSystemMap`).
* For every map `p`, the inclusion `E → E'`, `e ↦ (e, const)`, into the Moore-path replacement,
  whose endpoint map `p'` has a transitive lifting function, induces a quasi-isomorphism
  `C_*(F'_p) → C_*(F'_{p'})` (`TauCeti.isQuasiIso_fibrationLocalSystemMap_incl`). Followed by
  transport along that lifting function, it is the identity of the underlying chains, so the
  quasi-isomorphism follows from the one for transport
  (`TauCeti.isQuasiIso_transportLocalSystemHom`). No fibration hypothesis on `p` is needed.

This is the coefficient-side comparison used in the step of Barraud–Damian–Humilière–Oancea that
passes from fibrations with a transitive lifting function to arbitrary fibrations, by transport
along the Moore-path replacement.

## Main results

* `TauCeti.FiberHomotopyEquiv.isQuasiIso_fibrationLocalSystemMap`: a fibre homotopy equivalence
  induces a quasi-isomorphism of DG local systems.
* `TauCeti.isQuasiIso_fibrationLocalSystemMap_incl`: the DG local system of a map is
  quasi-isomorphic to that of its Moore-path replacement.

## References

* J.-F. Barraud, M. Damian, V. Humilière, A. Oancea, *Morse homology with differential graded
  coefficients*, Progress in Mathematics 360, Birkhäuser, 2025, §7.1.
-/

public section

noncomputable section

open CategoryTheory MulOpposite ContinuousMap

namespace TauCeti

universe u

variable {E E' B : Type u} [TopologicalSpace E] [TopologicalSpace E'] [TopologicalSpace B]
  (R : Type u) [CommRing R]

/-- **A fibre homotopy equivalence induces a quasi-isomorphism of DG local systems**: for a fibre
homotopy equivalence `Φ` from `p` to `q` over `B`, the morphism `C_*(F'_p) → C_*(F'_q)` induced by
its forward map is a quasi-isomorphism. -/
theorem FiberHomotopyEquiv.isQuasiIso_fibrationLocalSystemMap {p : C(E, B)} {q : C(E', B)}
    (Φ : FiberHomotopyEquiv p q) (b : B) :
    DGRightModuleCat.IsQuasiIso (fibrationLocalSystemMap R (b := b) Φ.toFun Φ.comp_toFun) :=
  isQuasiIso_of_apply_eq (G' := MooreLoopSpace B b) R _ (Φ.mooreReplacementFiberHomotopyEquiv b)
    fun x ↦ by rw [fibrationLocalSystemMap_apply, Φ.mooreReplacementFiberHomotopyEquiv_toFun]

/-- **The DG local system of a map is that of its Moore-path replacement**: for every map `p`, the
inclusion `E → E'`, `e ↦ (e, const)`, into the Moore-path replacement induces a quasi-isomorphism
`C_*(F'_p) → C_*(F'_{p'})` of DG local systems, where `p'` is the endpoint map of the
replacement. -/
theorem isQuasiIso_fibrationLocalSystemMap_incl (p : C(E, B)) (b : B) :
    DGRightModuleCat.IsQuasiIso (fibrationLocalSystemMap R (b := b) (MooreReplacement.incl p)
      (MooreReplacement.endpoint_comp_incl p)) := by
  have hΦ := MooreReplacement.isTransitive_endpointLiftingFunction p
  let := hΦ.mulAction b
  let := hΦ.continuousSMul b
  have hcomp : DGRightModuleCat.IsQuasiIso (fibrationLocalSystemMap R (b := b)
      (MooreReplacement.incl p) (MooreReplacement.endpoint_comp_incl p) ≫
        transportLocalSystemHom hΦ b) := by
    -- The composite is induced by the identification of `F'` with the fibre of `p'` over `b`.
    refine isQuasiIso_of_apply_eq (G' := MooreLoopSpace B b) R _
      (MooreReplacement.Fiber.homeomorphEndpointFiber p b).toHomotopyEquiv fun x ↦ ?_
    rw [DGRightModuleCat.comp_apply, transportLocalSystemHom_apply, fibrationLocalSystemMap_apply,
      ← LinearMap.comp_apply, ← cubicalChainModuleLinearMap_comp]
    congr 2
    refine ContinuousMap.ext fun y ↦
      Subtype.ext ((MooreReplacement.Fiber.coe_transport_map_incl y).trans ?_)
    simp
  rw [DGRightModuleCat.comp_eq_comp] at hcomp
  exact (isQuasiIso_transportLocalSystemHom hΦ b).of_comp_left hcomp

end TauCeti

end
