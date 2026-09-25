/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Algebra.MulAction
public import TauCeti.Algebra.GroupAction.TypeTags

/-!
# Continuity of the distributive action on the additive type tag

`TauCeti.Algebra.GroupAction.TypeTags` makes a monoid `M` acting on a monoid `A` by monoid
endomorphisms act distributively on `Additive A`. The topology of `Additive A` is that of `A`, and
the two actions are the same map `M × A → A`, so continuity of one is continuity of the other. This
file records that as the instance `Additive.continuousSMul`. It is what lets a multiplicative
coefficient module — a finite discrete `G`-module written multiplicatively, as in the extension
dictionary — be fed to the continuous cohomology of `Additive M`, whose hypotheses ask for a
continuous action. Likewise a continuous equivariant homomorphism of such modules stays continuous
when read additively (`MulDistribMulActionHom.continuous_toAdditive`), as the coefficient maps of
that cohomology require.
-/

public section

namespace Additive

variable {M A : Type*} [Monoid M] [Monoid A] [MulDistribMulAction M A] [TopologicalSpace M]
  [TopologicalSpace A]

/-- The distributive action of `M` on `Additive A` is continuous when the action on `A` is: the two
are the same map between the same topological spaces. -/
instance continuousSMul [ContinuousSMul M A] : ContinuousSMul M (Additive A) where
  continuous_smul :=
    continuous_ofMul.comp (continuous_fst.smul (continuous_toMul.comp continuous_snd))

end Additive

namespace MulDistribMulActionHom

variable {M A B : Type*} [Monoid M] [Monoid A] [Monoid B] [MulDistribMulAction M A]
  [MulDistribMulAction M B] [TopologicalSpace A] [TopologicalSpace B]

/-- An equivariant monoid homomorphism read additively, `MulDistribMulActionHom.toAdditive`, is
continuous when the homomorphism is: it is the same map between the same topological spaces. -/
theorem continuous_toAdditive (f : A →*[M] B) (hf : Continuous f) : Continuous f.toAdditive :=
  (continuous_ofMul.comp (hf.comp continuous_toMul)).congr fun x => (f.toAdditive_apply x).symm

end MulDistribMulActionHom
