/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.VectorBundle.Pullback
public import TauCeti.Topology.VectorBundle.SpinStructure.Twist

/-!
# Twisting a `Spinᶜ` structure commutes with pullback

For a `Spinᶜ` structure `s` on a real vector bundle `V → X` with fibre inner products, a principal
`U(1)`-bundle `L` over `X` and a continuous map `g : Y → X`, twisting commutes with pulling back
along `g`: `(g^* s).twist (g^* L) ≃ g^* (s.twist L)`
(`TauCeti.SpinCStructure.twistPullbackEquiv`). Both principal bundles are, over `y ∈ Y`,
`(P_{g y} × L_{g y}) ×_μ Spinᶜ(n)`; the equivalence is the identity `[(p, l), a] ↦ [(p, l), a]`,
obtained from the universal property of the extension
(`TauCeti.OrthonormalFrameLift.extendEquivOfEquivariant`) applied to `(p, l) ↦ [(p, l), 1]`, which
preserves frames (`TauCeti.SpinCStructure.toFrame_pullback_twist_inl`).

The universal property needs the pulled-back bundle `g *ᵖ V` to be a vector bundle whose fibres
carry the topology of their norms, so this file uses `Bundle.Pullback.normedFiberBundle` and
`Bundle.Pullback.normedVectorBundle` as local instances. Mathlib's `FiberBundle.pullback` asks for
nonempty fibres of `L`, which the statements here assume, as `TauCeti.PrincipalBundle.pullback`
does.

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

variable {X : Type*} [TopologicalSpace X] {F : Type*} {V : X → Type}
  [∀ x, NormedAddCommGroup (V x)] [∀ x, InnerProductSpace ℝ (V x)]
  [TopologicalSpace (TotalSpace F V)] [NormedAddCommGroup F] [NormedSpace ℝ F] [FiberBundle F V]
  [VectorBundle ℝ F V] {n : ℕ} [NeZero n]
  {L : X → Type} [TopologicalSpace (TotalSpace Circle L)] [∀ x, TopologicalSpace (L x)]
  [FiberBundle Circle L] [∀ x, MulAction Circleᵐᵒᵖ (L x)] [PrincipalBundle Circle L]
  {Y : Type*} [TopologicalSpace Y] {K : Type*} [FunLike K Y X] [ContinuousMapClass K Y X]

/-- The proof that the standard form on `ℝⁿ`, `n ≥ 1`, is nonzero, on which `Spinᶜ(n)` depends. -/
local notation "hQ" => QuadraticMap.Nondegenerate.ne_zero (nondegenerate_realCliffordForm n 0)

attribute [local instance] Pullback.normedFiberBundle Pullback.normedVectorBundle

/-- **The frame of `[(p, l), 1]`** in the pullback of the twist of a `Spinᶜ` structure `s` by `L`
is the frame of `p` in the pullback of `s`. -/
theorem toFrame_pullback_twist_inl (g : K) (s : SpinCStructure F V n) (y : Y) (p : s.P (g y))
    (l : L (g y)) :
    ((s.twist L).pullback g).toFrame
        ⟨y, Extend.inl (spinCGroup.mulCircle _ hQ) (spinCGroup.continuous_mulCircle _ _)
          (P := (s.fiberProd Circle L).P) (FiberProd.mk p l)⟩ =
      (s.pullback g).toFrame ⟨y, p⟩ := by
  obtain ⟨φ, hφ⟩ := s.exists_toFrame_eq_mk ⟨g y, p⟩
  rw [(s.twist L).toFrame_pullback_mk g y _ ((s.toFrame_twist_inl (g y) p l).trans hφ),
    s.toFrame_pullback_mk g y p hφ]

variable [∀ x, Nonempty (L x)]

/-- The map `(p, l) ↦ [(p, l), 1]` from the fibre product of the pullbacks of `P` and `L` to the
pullback of the twist is continuous. -/
private theorem continuous_twistPullback_inl (g : K) (s : SpinCStructure F V n) :
    Continuous fun z : TotalSpace (spinCGroup (realCliffordForm n 0) hQ × Circle)
        ((s.pullback g).fiberProd Circle ((g : Y → X) *ᵖ L)).P ↦
      (⟨z.proj, Extend.inl (spinCGroup.mulCircle _ hQ) (spinCGroup.continuous_mulCircle _ _)
          (P := (s.fiberProd Circle L).P) (FiberProd.mk (P := s.P) (Q := L) z.snd.fst z.snd.snd)⟩ :
        TotalSpace (spinCGroup (realCliffordForm n 0) hQ) ((s.twist L).pullback g).P) := by
  have hfst := FiberProd.continuous_totalSpaceMk_fst (P := (g : Y → X) *ᵖ s.P)
    (Q := (g : Y → X) *ᵖ L) (G := spinCGroup (realCliffordForm n 0) hQ) (H := Circle)
  have hsnd := FiberProd.continuous_totalSpaceMk_snd (P := (g : Y → X) *ᵖ s.P)
    (Q := (g : Y → X) *ᵖ L) (G := spinCGroup (realCliffordForm n 0) hQ) (H := Circle)
  have h₁ : Continuous fun z : TotalSpace (spinCGroup (realCliffordForm n 0) hQ × Circle)
      ((s.pullback g).fiberProd Circle ((g : Y → X) *ᵖ L)).P ↦
        TotalSpace.mk' (spinCGroup (realCliffordForm n 0) hQ) ((g : Y → X) z.proj)
          (z.snd.fst : s.P ((g : Y → X) z.proj)) :=
    (Pullback.continuous_lift _ _ _).comp hfst
  have h₂ : Continuous fun z : TotalSpace (spinCGroup (realCliffordForm n 0) hQ × Circle)
      ((s.pullback g).fiberProd Circle ((g : Y → X) *ᵖ L)).P ↦
        TotalSpace.mk' Circle ((g : Y → X) z.proj) (z.snd.snd : L ((g : Y → X) z.proj)) :=
    (Pullback.continuous_lift _ _ _).comp hsnd
  have h₄ : Continuous fun z : TotalSpace (spinCGroup (realCliffordForm n 0) hQ × Circle)
      ((s.pullback g).fiberProd Circle ((g : Y → X) *ᵖ L)).P ↦
        (⟨(g : Y → X) z.proj, FiberProd.mk (P := s.P) (Q := L) z.snd.fst z.snd.snd⟩ :
          TotalSpace (spinCGroup (realCliffordForm n 0) hQ × Circle) (s.fiberProd Circle L).P) :=
    h₁.totalSpaceMk_fiberProdMk (P := s.P) (Q := L) h₂
  have hproj : Continuous fun z : TotalSpace (spinCGroup (realCliffordForm n 0) hQ × Circle)
      ((s.pullback g).fiberProd Circle ((g : Y → X) *ᵖ L)).P ↦ z.proj :=
    (Pullback.continuous_proj (spinCGroup (realCliffordForm n 0) hQ) s.P (g : Y → X)).comp hfst
  exact (Pullback.continuous_iff (F := spinCGroup (realCliffordForm n 0) hQ)
    (E := (s.twist L).P) (f := (g : Y → X))).2
      ⟨hproj, (Extend.continuous_inl (s.fiberProd Circle L).P _ _).comp h₄⟩

/-- **Twisting commutes with pullback**: for a continuous map `g : Y → X`,
`(g^* s).twist (g^* L) ≃ g^* (s.twist L)`. Over `y`, both principal bundles are
`(P_{g y} × L_{g y}) ×_μ Spinᶜ(n)`, and the equivalence is `[(p, l), a] ↦ [(p, l), a]`. -/
noncomputable def twistPullbackEquiv (g : K) (s : SpinCStructure F V n) :
    (twist ((g : Y → X) *ᵖ L) (s.pullback g)).Equiv ((s.twist L).pullback g) :=
  ((s.pullback g).fiberProd Circle ((g : Y → X) *ᵖ L)).extendEquivOfEquivariant _ _ _ _ _
    ((s.twist L).pullback g)
    (fun _ z ↦ Extend.inl (spinCGroup.mulCircle _ hQ) (spinCGroup.continuous_mulCircle _ _)
      (P := (s.fiberProd Circle L).P) (FiberProd.mk (P := s.P) (Q := L) z.fst z.snd))
    (fun _ z a ↦ Extend.inl_smul _ _ (FiberProd.mk (P := s.P) (Q := L) z.fst z.snd) a)
    (continuous_twistPullback_inl g s)
    (fun y z ↦ (toFrame_pullback_twist_inl g s y z.fst z.snd).trans
      ((s.pullback g).toFrame_fiberProd_mk Circle ((g : Y → X) *ᵖ L) y z.fst z.snd).symm)

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
  exact (OrthonormalFrameLift.extendEquivOfEquivariant_toEquiv_mk ..).trans
    (Extend.smul_inl (P := (s.fiberProd Circle L).P) _ _ (FiberProd.mk p l) a)

/-- The equivalence `(g^* s).twist (g^* L) ≃ g^* (s.twist L)` sends `[(p, l), 1]` to
`[(p, l), 1]`. -/
theorem twistPullbackEquiv_toEquiv_inl (g : K) (s : SpinCStructure F V n) (y : Y) (p : s.P (g y))
    (l : L (g y)) :
    (twistPullbackEquiv (L := L) g s).toEquiv y
        (Extend.inl (spinCGroup.mulCircle _ hQ) (spinCGroup.continuous_mulCircle _ _)
          (P := ((s.pullback g).fiberProd Circle ((g : Y → X) *ᵖ L)).P) (FiberProd.mk p l)) =
      Extend.inl (spinCGroup.mulCircle _ hQ) (spinCGroup.continuous_mulCircle _ _)
        (P := (s.fiberProd Circle L).P) (FiberProd.mk p l) := by
  unfold twistPullbackEquiv
  apply OrthonormalFrameLift.extendEquivOfEquivariant_toEquiv_inl

end SpinCStructure

end TauCeti
