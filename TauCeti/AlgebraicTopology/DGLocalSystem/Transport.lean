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
* `TauCeti.liftingLocalSystemRoof`: the zigzag comparing two transitive lifting functions, a
  right fraction for the quasi-isomorphisms.

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
  exact isQuasiIso_of_apply_eq (G' := MooreLoopSpace B b) R (transportLocalSystemHom hΦ b)
    (Φ.transportHomotopyEquiv b) fun x ↦ by
      rw [transportLocalSystemHom_apply]
      exact congrArg (fun k : C(_, _) ↦ cubicalChainModuleLinearMap R k x)
        (ContinuousMap.ext fun y ↦ congrFun (Φ.coe_transportHomotopyEquiv b) y).symm

/-- **The zigzag comparing two transitive lifting functions**: the roof
`C_*(F)_{Φ₀} ← C_*(F') → C_*(F)_{Φ₁}` of strict morphisms induced by transport, as a right fraction
for the quasi-isomorphisms, with no homotopy between `Φ₀` and `Φ₁`.  Its second leg is also a
quasi-isomorphism (`isQuasiIso_liftingLocalSystemRoof_f`). -/
def liftingLocalSystemRoof {Φ₀ Φ₁ : MooreLiftingFunction p} (hΦ₀ : Φ₀.IsTransitive)
    (hΦ₁ : Φ₁.IsTransitive) (b : B) :
    (DGRightModuleCat.quasiIsos (loopChain_isDGAlgebra B b R)).RightFraction
      (liftingLocalSystem (R := R) hΦ₀ b) (liftingLocalSystem hΦ₁ b) where
  X' := fibrationLocalSystem R p b
  s := transportLocalSystemHom hΦ₀ b
  hs := (DGRightModuleCat.quasiIsos_iff _).2 (isQuasiIso_transportLocalSystemHom hΦ₀ b)
  f := transportLocalSystemHom hΦ₁ b

/-- The apex of the zigzag is the DG local system `C_*(F')` of the Moore-path replacement. -/
@[simp]
theorem liftingLocalSystemRoof_X' {Φ₀ Φ₁ : MooreLiftingFunction p} (hΦ₀ : Φ₀.IsTransitive)
    (hΦ₁ : Φ₁.IsTransitive) (b : B) :
    (liftingLocalSystemRoof (R := R) hΦ₀ hΦ₁ b).X' = fibrationLocalSystem R p b :=
  (rfl)

/-- The left leg of the zigzag is the strict morphism of transport along `Φ₀`, up to the identity
of the apex. -/
@[simp]
theorem liftingLocalSystemRoof_s {Φ₀ Φ₁ : MooreLiftingFunction p} (hΦ₀ : Φ₀.IsTransitive)
    (hΦ₁ : Φ₁.IsTransitive) (b : B) :
    (liftingLocalSystemRoof (R := R) hΦ₀ hΦ₁ b).s =
      eqToHom (liftingLocalSystemRoof_X' hΦ₀ hΦ₁ b) ≫ transportLocalSystemHom hΦ₀ b := by
  unfold liftingLocalSystemRoof
  exact (Category.id_comp _).symm

/-- The right leg of the zigzag is the strict morphism of transport along `Φ₁`, up to the identity
of the apex. -/
@[simp]
theorem liftingLocalSystemRoof_f {Φ₀ Φ₁ : MooreLiftingFunction p} (hΦ₀ : Φ₀.IsTransitive)
    (hΦ₁ : Φ₁.IsTransitive) (b : B) :
    (liftingLocalSystemRoof (R := R) hΦ₀ hΦ₁ b).f =
      eqToHom (liftingLocalSystemRoof_X' hΦ₀ hΦ₁ b) ≫ transportLocalSystemHom hΦ₁ b := by
  unfold liftingLocalSystemRoof
  exact (Category.id_comp _).symm

/-- The second leg of the zigzag is a quasi-isomorphism too. -/
theorem isQuasiIso_liftingLocalSystemRoof_f {Φ₀ Φ₁ : MooreLiftingFunction p}
    (hΦ₀ : Φ₀.IsTransitive) (hΦ₁ : Φ₁.IsTransitive) (b : B) :
    DGRightModuleCat.IsQuasiIso (liftingLocalSystemRoof (R := R) hΦ₀ hΦ₁ b).f := by
  exact isQuasiIso_transportLocalSystemHom hΦ₁ b

end Transport

end TauCeti

end
