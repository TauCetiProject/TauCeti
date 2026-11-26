/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.VectorBundle.OrthonormalFrame.Extension.Pullback
public import TauCeti.Topology.VectorBundle.SpinStructure.Twist.Basic

/-!
# Twisting a `Spinᶜ` structure commutes with pullback

For a `Spinᶜ` structure `s` on a real vector bundle `V → X` with fibre inner products, a principal
`U(1)`-bundle `L` over `X` and a continuous map `g : Y → X`, twisting commutes with pulling back
along `g`: `(g^* s).twist (g^* L) ≃ g^* (s.twist L)`
(`TauCeti.SpinCStructure.twistPullbackEquiv`). Both principal bundles are, over `y ∈ Y`,
`(P_{g y} × L_{g y}) ×_μ Spinᶜ(n)`, and the equivalence is the identity `[(p, l), a] ↦ [(p, l), a]`.
It combines the two general facts that the fibre product of a lift with a principal bundle
commutes with pullback (`TauCeti.OrthonormalFrameLift.fiberProdPullbackEquiv`) and that the
extension of a lift commutes with pullback (`TauCeti.OrthonormalFrameLift.extendPullbackEquiv`).

Mathlib's `FiberBundle.pullback` asks for nonempty fibres of `L`, which the equivalence assumes,
as `TauCeti.PrincipalBundle.pullback` does.

## Main definitions

* `TauCeti.SpinCStructure.twistPullbackEquiv`: `(g^* s).twist (g^* L) ≃ g^* (s.twist L)`.

## Main results

* `TauCeti.SpinCStructure.toFrame_pullback_twist_inl`: the frame of `[(p, l), 1]` in
  `g^* (s.twist L)` is the frame of `p` in `g^* s`.
* `TauCeti.SpinCStructure.twistPullbackEquiv_toEquiv_mk`,
  `TauCeti.SpinCStructure.twistPullbackEquiv_toEquiv_inl`: the equivalence sends `[(p, l), a]` to
  `[(p, l), a]`, and in particular `[(p, l), 1]` to `[(p, l), 1]`.
-/

public section

open Bundle MulOpposite CliffordAlgebra TauCeti.PrincipalBundle

namespace TauCeti

namespace SpinCStructure

open OrthonormalFrameLift

variable {X : Type*} [TopologicalSpace X] {F : Type*} {V : X → Type}
  [∀ x, NormedAddCommGroup (V x)] [∀ x, InnerProductSpace ℝ (V x)]
  [TopologicalSpace (TotalSpace F V)] [NormedAddCommGroup F] [NormedSpace ℝ F] [FiberBundle F V]
  [VectorBundle ℝ F V] {n : ℕ} [NeZero n]
  {L : X → Type} [TopologicalSpace (TotalSpace Circle L)] [∀ x, TopologicalSpace (L x)]
  [FiberBundle Circle L] [∀ x, MulAction Circleᵐᵒᵖ (L x)] [PrincipalBundle Circle L]
  {Y : Type*} [TopologicalSpace Y] {K : Type*} [FunLike K Y X] [ContinuousMapClass K Y X]

/-- The proof that the standard form on `ℝⁿ`, `n ≥ 1`, is nonzero, on which `Spinᶜ(n)` depends. -/
local notation "hQ" => QuadraticMap.Nondegenerate.ne_zero (nondegenerate_realCliffordForm n 0)

/-- **The frame of `[(p, l), 1]`** in the pullback of the twist of a `Spinᶜ` structure `s` by `L`
is the frame of `p` in the pullback of `s`. -/
@[simp]
theorem toFrame_pullback_twist_inl (g : K) (s : SpinCStructure F V n) (y : Y) (p : s.P (g y))
    (l : L (g y)) :
    ((s.twist L).pullback g).toFrame
        ⟨y, Extend.inl (spinCGroup.mulCircle _ hQ) (spinCGroup.continuous_mulCircle _ _)
          (P := (s.fiberProd Circle L).P) (FiberProd.mk p l)⟩ =
      (s.pullback g).toFrame ⟨y, p⟩ :=
  ((s.fiberProd Circle L).toFrame_pullback_extend_inl _ _ _ _ _ g y (FiberProd.mk p l)).trans
    (s.toFrame_pullback_fiberProd_mk g y p l)

variable [∀ x, Nonempty (L x)]

/-- **Twisting commutes with pullback**: for a continuous map `g : Y → X`,
`(g^* s).twist (g^* L) ≃ g^* (s.twist L)`. Over `y`, both principal bundles are
`(P_{g y} × L_{g y}) ×_μ Spinᶜ(n)`, and the equivalence is `[(p, l), a] ↦ [(p, l), a]`. -/
noncomputable def twistPullbackEquiv (g : K) (s : SpinCStructure F V n) :
    (twist ((g : Y → X) *ᵖ L) (s.pullback g)).Equiv ((s.twist L).pullback g) :=
  ((fiberProdPullbackEquiv (H := Circle) (Q := L) s g).extend (spinCGroup.mulCircle _ hQ)
    (spinCGroup.continuous_mulCircle _ _) _ _ _).trans
      ((s.fiberProd Circle L).extendPullbackEquiv _ _ _ _ _ g)

/-- The equivalence `(g^* s).twist (g^* L) ≃ g^* (s.twist L)` sends `[(p, l), a]` to
`[(p, l), a]`. -/
theorem twistPullbackEquiv_toEquiv_mk (g : K) (s : SpinCStructure F V n) (y : Y) (p : s.P (g y))
    (l : L (g y)) (a : spinCGroup (realCliffordForm n 0) hQ) :
    (twistPullbackEquiv (L := L) g s).toEquiv y
        (Extend.mk (spinCGroup.mulCircle _ hQ) (spinCGroup.continuous_mulCircle _ _)
          (P := ((s.pullback g).fiberProd Circle ((g : Y → X) *ᵖ L)).P) (FiberProd.mk p l) a) =
      Extend.mk (spinCGroup.mulCircle _ hQ) (spinCGroup.continuous_mulCircle _ _)
        (P := (s.fiberProd Circle L).P) (FiberProd.mk p l) a := by
  unfold twistPullbackEquiv
  refine (DFunLike.congr_fun (OrthonormalFrameLift.Equiv.trans_toEquiv _ _ y) _).trans ?_
  refine (congrArg (((s.fiberProd Circle L).extendPullbackEquiv _ _ _ _ _ g).toEquiv y)
    ((Equiv.extend_toEquiv_mk _ _ _ _ _ _ y _ a).trans ?_)).trans
      ((s.fiberProd Circle L).extendPullbackEquiv_toEquiv_mk _ _ _ _ _ g y _ a)
  exact congrArg (Extend.mk _ _ · a) (fiberProdPullbackEquiv_toEquiv_mk s g y p l)

/-- The equivalence `(g^* s).twist (g^* L) ≃ g^* (s.twist L)` sends `[(p, l), 1]` to
`[(p, l), 1]`. -/
theorem twistPullbackEquiv_toEquiv_inl (g : K) (s : SpinCStructure F V n) (y : Y) (p : s.P (g y))
    (l : L (g y)) :
    (twistPullbackEquiv (L := L) g s).toEquiv y
        (Extend.inl (spinCGroup.mulCircle _ hQ) (spinCGroup.continuous_mulCircle _ _)
          (P := ((s.pullback g).fiberProd Circle ((g : Y → X) *ᵖ L)).P) (FiberProd.mk p l)) =
      Extend.inl (spinCGroup.mulCircle _ hQ) (spinCGroup.continuous_mulCircle _ _)
        (P := (s.fiberProd Circle L).P) (FiberProd.mk p l) :=
  (congrArg _ (Extend.inl_def _ _ _)).trans
    ((twistPullbackEquiv_toEquiv_mk g s y p l 1).trans (Extend.inl_def _ _ _).symm)

end SpinCStructure

end TauCeti
