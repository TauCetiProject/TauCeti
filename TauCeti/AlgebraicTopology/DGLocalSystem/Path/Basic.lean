/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.DGLocalSystem.Basic
public import TauCeti.AlgebraicTopology.Singular.Cubical.MonoidAlgebra.HomotopyInvariance
public import TauCeti.Topology.PathSpace.Moore.Between.Equiv

/-!
# The right DG module of chains on paths between basepoints

Normalized cubical chains on Moore paths from `a` to `b` form a right DG module over the
chains on loops at `b`, using concatenation at the target. Prepending a chosen path gives
strict morphisms of these modules, and each is a quasi-isomorphism. In particular, prepending
a path from `a` to `b` gives a quasi-isomorphism from the chains on loops at `b` to the chains
on paths from `a` to `b`.

This identifies the right-module homology of the path carrier used for basepoint change.
It does not yet equip these chains with the left loop-chain action or construct derived
basepoint change. Homotopy invariance is the existing cubical-chain comparison theorem;
no homology calculation is repeated here.

The chain objects and maps allow independent universes for the space and coefficient ring.
The quasi-isomorphism statements require a shared universe, as in the cubical-chain
homotopy-invariance theorem.

## References

* J.-F. Barraud, M. Damian, V. Humilière, A. Oancea, *Morse homology with differential graded
  coefficients*, Progress in Mathematics 360, Birkhäuser, 2025, §7.1.
-/

public noncomputable section

open CategoryTheory ContinuousMap

namespace TauCeti

universe u v

variable {B : Type u} [TopologicalSpace B] (R : Type v) [CommRing R] {a b c : B}

/-- Chains on Moore paths from `a` to `b`, as a DG local system based at `b` through
concatenation on the right. -/
abbrev pathChainLocalSystem (a b : B) : DGLocalSystem B b R :=
  cubicalChainModuleDG (MoorePathBetween B a b) (MooreLoopSpace B b) R

/-- The strict DG module morphism induced by prepending a chosen path. -/
def pathChainPrepend (γ : MoorePathBetween B a b) (c : B) :
    pathChainLocalSystem R b c ⟶ pathChainLocalSystem R a c :=
  cubicalChainModuleMap R (γ.prepend c) fun ω δ ↦ γ.prepend_op_smul δ ω

/-- Prepending on chains is push-forward along path concatenation. -/
theorem pathChainPrepend_apply (γ : MoorePathBetween B a b) (c : B)
    (x : pathChainLocalSystem R b c) :
    pathChainPrepend R γ c x = cubicalChainModuleLinearMap R (γ.prepend c) x :=
  cubicalChainModuleMap_apply _ _ x

variable (R : Type u) [CommRing R] in
/-- Prepending a chosen path is a quasi-isomorphism of right DG modules. -/
theorem isQuasiIso_pathChainPrepend (γ : MoorePathBetween B a b) (c : B) :
    DGRightModuleCat.IsQuasiIso (pathChainPrepend R γ c) :=
  isQuasiIso_cubicalChainModuleMap R (γ.prepend c) (fun ω δ ↦ γ.prepend_op_smul δ ω)
    (γ.prependHomotopyEquiv c) (ContinuousMap.ext fun δ ↦
      (γ.prependHomotopyEquiv_apply δ).trans (γ.prepend_apply δ).symm)

/-- The strict DG module morphism from loop chains to path chains obtained by appending
loops to a chosen path. The source uses the canonical chain-module wrapper. -/
def loopChainPrepend (γ : MoorePathBetween B a b) :
    cubicalChainModuleDG (MooreLoopSpace B b) (MooreLoopSpace B b) R ⟶
      pathChainLocalSystem R a b :=
  cubicalChainModuleMap R γ.loopPrependHomotopyEquiv.toFun fun ω η ↦
    γ.loopPrependHomotopyEquiv_op_smul η ω

/-- The loop-to-path morphism is push-forward along concatenation with the chosen path. -/
theorem loopChainPrepend_apply (γ : MoorePathBetween B a b)
    (x : cubicalChainModuleDG (MooreLoopSpace B b) (MooreLoopSpace B b) R) :
    loopChainPrepend R γ x =
      cubicalChainModuleLinearMap R γ.loopPrependHomotopyEquiv.toFun x :=
  cubicalChainModuleMap_apply _ _ x

variable (R : Type u) [CommRing R] in
/-- Loop chains and path chains are quasi-isomorphic as right DG modules, after choosing
a path between the basepoints. -/
theorem isQuasiIso_loopChainPrepend (γ : MoorePathBetween B a b) :
    DGRightModuleCat.IsQuasiIso (loopChainPrepend R γ) :=
  isQuasiIso_cubicalChainModuleMap R γ.loopPrependHomotopyEquiv.toFun
    (fun ω η ↦ γ.loopPrependHomotopyEquiv_op_smul η ω) γ.loopPrependHomotopyEquiv rfl

end TauCeti
