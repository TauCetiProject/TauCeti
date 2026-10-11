/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.DGLocalSystem.Fibration
public import TauCeti.AlgebraicTopology.Singular.Cubical.MonoidAlgebra.HomotopyInvariance

/-!
# Transport is a quasi-isomorphism of DG local systems

An equivariant homotopy equivalence induces a quasi-isomorphism of the DG right modules of cubical
chains (`TauCeti.isQuasiIso_cubicalChainModuleMap`).  For a transitive lifting function `Φ` of
`p : E → B`, transport `F' → F` is a strictly equivariant homotopy equivalence, so the strict
morphism `C_*(F') → C_*(F)_Φ` of DG local systems is a quasi-isomorphism
(`TauCeti.isQuasiIso_transportLocalSystemHom`).  Two transitive lifting functions `Φ₀`, `Φ₁` are
therefore compared by the specified zigzag of strict quasi-isomorphisms
`C_*(F)_{Φ₀} ← C_*(F') → C_*(F)_{Φ₁}` (`TauCeti.liftingLocalSystemRoof`), with no homotopy
between the lifting functions.

## Main results

* `TauCeti.isQuasiIso_transportLocalSystemHom`: transport is a quasi-isomorphism.
* `TauCeti.liftingLocalSystemRoof`: the zigzag comparing two transitive lifting functions.

## References

* J.-F. Barraud, M. Damian, V. Humilière, A. Oancea, *Morse homology with differential graded
  coefficients*, Progress in Mathematics 360, Birkhäuser, 2025, §7.1.
-/

public section

noncomputable section

open CategoryTheory MulOpposite ContinuousMap

namespace TauCeti

universe u

section Transport

variable {E B : Type u} [TopologicalSpace E] [TopologicalSpace B] {R : Type u} [CommRing R]
  {p : C(E, B)}

/-- **Transport is a quasi-isomorphism of DG local systems**: for a transitive lifting function
`Φ`, the strict morphism `C_*(F') → C_*(F)_Φ` induced by transport is a quasi-isomorphism, since
transport is an equivariant homotopy equivalence. -/
theorem isQuasiIso_transportLocalSystemHom {Φ : MooreLiftingFunction p} (hΦ : Φ.IsTransitive)
    (b : B) : DGRightModuleCat.IsQuasiIso (transportLocalSystemHom (R := R) hΦ b) := by
  let := hΦ.mulAction b
  let := hΦ.continuousSMul b
  exact isQuasiIso_cubicalChainModuleMap (G := MooreLoopSpace B b) R (Φ.transport b) _
    (Φ.transportHomotopyEquiv b)
    (ContinuousMap.ext fun x ↦ congrFun (Φ.coe_transportHomotopyEquiv b) x)

/-- **The zigzag comparing two transitive lifting functions**: the strict quasi-isomorphisms
`C_*(F)_{Φ₀} ← C_*(F') → C_*(F)_{Φ₁}` induced by transport, with no homotopy between `Φ₀` and
`Φ₁`. -/
def liftingLocalSystemRoof {Φ₀ Φ₁ : MooreLiftingFunction p} (hΦ₀ : Φ₀.IsTransitive)
    (hΦ₁ : Φ₁.IsTransitive) (b : B) :
    DGRightModuleCat.QuasiIsoRoof (liftingLocalSystem (R := R) hΦ₀ b) (liftingLocalSystem hΦ₁ b)
    where
  apex := fibrationLocalSystem R p b
  left := transportLocalSystemHom hΦ₀ b
  right := transportLocalSystemHom hΦ₁ b
  isQuasiIso_left := isQuasiIso_transportLocalSystemHom hΦ₀ b
  isQuasiIso_right := isQuasiIso_transportLocalSystemHom hΦ₁ b

end Transport

end TauCeti

end
