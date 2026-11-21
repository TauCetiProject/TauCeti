/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.Algebra.GroupAction.InternalHom.Basic
public import Mathlib.GroupTheory.Finiteness

/-!
# Pointwise convergence on additive homomorphisms with conjugation action

`TauCeti.PointwiseHom G M N` is the additive group of homomorphisms from `M` to `N`,
with the topology induced from `M → N` and the conjugation action of `G`. Unlike
`TauCeti.InternalHom`, it is not given the discrete topology unconditionally.
Evaluation is jointly continuous when `M` is discrete, and so is the conjugation action
when the actions on `M` and `N` are jointly continuous. No compactness of `G` is needed.

For finitely generated `M` and discrete `N`, the pointwise topology is discrete.
In particular the comparison with `InternalHom` is then a homeomorphism. These facts
allow splitting cocycles of additively split sequences to take values in a continuous
coefficient module even when the quotient is not finitely generated.

The algebraic action is reused from `TauCeti.InternalHom` and `TauCeti.homAction`.
For splitting torsors, pointwise convergence replaces the discrete Hom used in
Harpaz–Wittenberg, *The Massey vanishing conjecture for number fields*, §5, Lemma 5.5;
the discrete topology suffices there only for finitely generated sources.
-/

public section

namespace TauCeti

/-- Additive homomorphisms with pointwise convergence and the conjugation action.
The algebraic carrier is the existing `InternalHom`; only the topology changes.
The synonym is exposed so its inherited algebraic instances can compute across modules. -/
@[expose] def PointwiseHom (G M N : Type*) [AddMonoid M] [AddCommGroup N] := InternalHom G M N

namespace PointwiseHom

section Basic

variable {G M N : Type*} [AddMonoid M] [AddCommGroup N]

instance : AddCommGroup (PointwiseHom G M N) :=
  inferInstanceAs (AddCommGroup (InternalHom G M N))

/-- Forget the pointwise topology, retaining the algebraic internal hom. -/
def equivInternalHom : PointwiseHom G M N ≃+ InternalHom G M N := AddEquiv.refl _

/-- Evaluation as an additive pairing. -/
def eval : PointwiseHom G M N →+ (M →+ N) where
  toFun f := (equivInternalHom f).toAddMonoidHom
  map_zero' := InternalHom.toAddMonoidHom_zero
  map_add' _ _ := InternalHom.toAddMonoidHom_add _ _

@[simp]
theorem toAddMonoidHom_equivInternalHom (f : PointwiseHom G M N) :
    (equivInternalHom f).toAddMonoidHom = eval f := (rfl)

@[simp]
theorem eval_equivInternalHom_symm (f : InternalHom G M N) :
    eval (equivInternalHom.symm f) = f.toAddMonoidHom := (rfl)

/-- Regard an additive homomorphism as a pointwise homomorphism. -/
def of : (M →+ N) ≃+ PointwiseHom G M N where
  toFun := InternalHom.of G
  invFun := eval
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl

@[simp]
theorem eval_of (f : M →+ N) : eval (of f : PointwiseHom G M N) = f := (rfl)

@[simp]
theorem of_eval (f : PointwiseHom G M N) : of (eval f) = f := (rfl)

@[ext]
theorem ext {f g : PointwiseHom G M N} (h : ∀ m, eval f m = eval g m) : f = g := by
  apply equivInternalHom.injective
  apply InternalHom.ext
  simpa only [toAddMonoidHom_equivInternalHom] using AddMonoidHom.ext h

instance [Finite M] [Finite N] : Finite (PointwiseHom G M N) :=
  Finite.of_equiv _ equivInternalHom.toEquiv.symm

instance [Subsingleton M] : Subsingleton (PointwiseHom G M N) :=
  equivInternalHom.injective.subsingleton

instance [TopologicalSpace N] : TopologicalSpace (PointwiseHom G M N) :=
  TopologicalSpace.induced (fun f m => eval f m) inferInstance

/-- The defining embedding into the product of the target groups. -/
theorem isEmbedding_eval [TopologicalSpace N] :
    Topology.IsEmbedding (fun (f : PointwiseHom G M N) m => eval f m) :=
  ⟨⟨rfl⟩, fun _ _ h => ext (congrFun h)⟩

/-- Continuity into the pointwise hom is equivalent to continuity at each argument. -/
theorem continuous_iff [TopologicalSpace N] {X : Type*} [TopologicalSpace X]
    {f : X → PointwiseHom G M N} :
    Continuous f ↔ ∀ m, Continuous fun x => eval (f x) m :=
  isEmbedding_eval.isInducing.continuous_iff.trans continuous_pi_iff

/-- Each evaluation at a fixed argument is continuous. -/
theorem continuous_eval [TopologicalSpace N] (m : M) :
    Continuous fun f : PointwiseHom G M N => eval f m :=
  (continuous_apply m).comp isEmbedding_eval.continuous

instance [TopologicalSpace N] [IsTopologicalAddGroup N] :
    IsTopologicalAddGroup (PointwiseHom G M N) where
  continuous_add := continuous_iff.mpr fun m =>
    ((continuous_eval m).comp continuous_fst).add ((continuous_eval m).comp continuous_snd)
  continuous_neg := continuous_iff.mpr fun m =>
    ((continuous_eval (G := G) m).neg).congr fun f => by
      simp only [map_neg, AddMonoidHom.neg_apply]
      rfl

instance [TopologicalSpace N] [T2Space N] : T2Space (PointwiseHom G M N) :=
  isEmbedding_eval.t2Space

/-- Evaluation is jointly continuous for a discrete source, even if that source is infinite. -/
theorem continuous_uncurry_eval [TopologicalSpace M] [DiscreteTopology M] [TopologicalSpace N] :
    Continuous fun p : PointwiseHom G M N × M => eval p.1 p.2 :=
  continuous_prod_of_discrete_right.mpr continuous_eval

section Action

variable [Group G] [DistribMulAction G M] [DistribMulAction G N]

instance : DistribMulAction G (PointwiseHom G M N) :=
  inferInstanceAs (DistribMulAction G (InternalHom G M N))

/-- The algebraic comparison preserves the conjugation action. -/
@[simp]
theorem equivInternalHom_smul (g : G) (f : PointwiseHom G M N) :
    equivInternalHom (g • f) = g • equivInternalHom f := (rfl)

/-- Pointwise homomorphisms carry the existing conjugation action, not the codomain-only action. -/
@[simp]
theorem eval_smul (g : G) (f : PointwiseHom G M N) (m : M) :
    eval (g • f) m = g • eval f (g⁻¹ • m) :=
  homAction_apply g (eval f) m

/-- Evaluation is equivariant for simultaneous actions on both arguments. -/
theorem eval_smul_smul (g : G) (f : PointwiseHom G M N) (m : M) :
    eval (g • f) (g • m) = g • eval f m := by
  simp

instance [TopologicalSpace G] [ContinuousInv G]
    [TopologicalSpace M] [DiscreteTopology M] [ContinuousSMul G M]
    [TopologicalSpace N] [ContinuousSMul G N] : ContinuousSMul G (PointwiseHom G M N) where
  continuous_smul := continuous_iff.mpr fun m => by
    have harg : Continuous fun p : G × PointwiseHom G M N => p.1⁻¹ • m :=
      continuous_fst.inv.smul continuous_const
    convert continuous_fst.smul
      (continuous_uncurry_eval.comp (continuous_snd.prodMk harg)) using 1
    ext p
    exact eval_smul p.1 p.2 m

end Action

end Basic

section FinitelyGenerated

variable {G M N : Type*} [AddGroup M] [AddCommGroup N]
  [TopologicalSpace N] [DiscreteTopology N]

/-- A finite generating set detects equality of homomorphisms, so pointwise convergence
into a discrete target is discrete for a finitely generated source. -/
instance [AddGroup.FG M] : DiscreteTopology (PointwiseHom G M N) := by
  obtain ⟨s, hs, hfin⟩ := AddGroup.fg_iff.mp (inferInstance : AddGroup.FG M)
  let := hfin.to_subtype
  apply DiscreteTopology.of_continuous_injective
    (f := fun (f : PointwiseHom G M N) (m : s) => eval f m)
  · exact continuous_pi fun m => continuous_eval (m : M)
  · intro f g h
    apply ext
    exact DFunLike.congr_fun (AddMonoidHom.eq_of_eqOn_dense hs
      (f := eval f) (g := eval g) fun m hm => congrFun h ⟨m, hm⟩)

/-- For a finitely generated source and discrete target, the pointwise and discrete
internal homs are homeomorphic by the identity on underlying homomorphisms. -/
def homeomorphInternalHom [AddGroup.FG M] :
    PointwiseHom G M N ≃ₜ InternalHom G M N where
  toEquiv := equivInternalHom.toEquiv
  continuous_toFun := continuous_of_discreteTopology
  continuous_invFun := continuous_of_discreteTopology

@[simp]
theorem homeomorphInternalHom_apply [AddGroup.FG M] (f : PointwiseHom G M N) :
    homeomorphInternalHom f = equivInternalHom f := (rfl)

end FinitelyGenerated

end PointwiseHom
end TauCeti
