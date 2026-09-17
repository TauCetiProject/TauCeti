/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Algebra.AlgebraicGroup.Tangent.Zero
public import TauCeti.Algebra.AlgebraicGroup.Tangent.FiniteType
public import TauCeti.Algebra.AlgebraicGroup.Connected.ComponentGroup.TrivialIdentity
public import TauCeti.Algebra.AlgebraicGroup.HopfIdeal.Cotangent
public import TauCeti.Algebra.AlgebraicGroup.HopfIdeal.BaseChange
import Mathlib.RingTheory.Etale.Descent

/-!
# Étale affine groups and their Lie algebras

An affine group of finite type over a field is étale exactly when its Lie algebra at the
identity is zero. No smoothness, reducedness, or connectedness assumption is needed.
This criterion detects infinitesimal structure in finite group schemes, and applies to the
scheme-theoretic kernel of a homomorphism via the kernel of its differential.

Over an algebraically closed field, a zero Lie algebra forces the identity component to be
trivial. The component-group classification then identifies the group with a finite constant
group. The general criterion descends from the algebraic closure: vanishing of the augmentation
cotangent space is idempotence of the augmentation ideal, which is preserved by base change.

## References

* J. S. Milne, *Algebraic Groups* (2017), §§2 and 10.
* W. C. Waterhouse, *Introduction to Affine Group Schemes*, §§6 and 11.
-/

public section

namespace TauCeti

universe u

open scoped TensorProduct

namespace FiniteTypeCommHopfAlgCat

variable {k : Type u} [Field k] [IsAlgClosed k]

/-- A finite-type affine group with zero Lie algebra has trivial identity component. -/
theorem identityComponentHopfIdeal_eq_augmentation_of_finrank_lie_eq_zero
    (H : FiniteTypeCommHopfAlgCat.{u, u} k)
    (h : Module.finrank k (Derivation k H (Bialgebra.CounitAlgebra k H k)) = 0) :
    HopfAlgebra.identityComponentHopfIdeal (k := k) (H := H) =
      HopfIdeal.augmentation k H := by
  let I := HopfAlgebra.identityComponentHopfIdeal (k := k) (H := H)
  let Q := identityComponent H
  have hQ : Module.finrank k
      (Derivation k Q (Bialgebra.CounitAlgebra k Q k)) = 0 :=
    Nat.eq_zero_of_le_zero (h ▸ HopfIdeal.finrank_quotientLie_le I)
  have haug :=
    (geometricallyConnected_identityComponent H).augmentation_eq_bot_of_finrank_lie_eq_zero hQ
  apply le_antisymm (HopfIdeal.le_augmentation k H I)
  intro x hx
  have hxQ : (CommHopfAlgCat.mkQuotient H.obj I).hom x ∈ HopfIdeal.augmentation k Q := by
    rw [HopfIdeal.mem_augmentation, CoalgHomClass.counit_comp_apply]
    exact (HopfIdeal.mem_augmentation k H).mp hx
  rw [haug, HopfIdeal.mem_bot] at hxQ
  exact HopfIdeal.mem_toIdeal.mp ((CommHopfAlgCat.mkQuotient_eq_zero_iff H.obj I x).mp hxQ)

end FiniteTypeCommHopfAlgCat

namespace HopfAlgebra

variable {k H : Type u} [Field k] [CommRing H] [_root_.HopfAlgebra k H]
variable [Algebra.FiniteType k H]

/-- A finite-type affine group over a field is étale if and only if its Lie algebra is zero. -/
theorem algebraEtale_iff_finrank_lie_eq_zero :
    Algebra.Etale k H ↔
      Module.finrank k (Derivation k H (Bialgebra.CounitAlgebra k H k)) = 0 := by
  constructor
  · intro h
    let _ := h
    have : Subsingleton (Derivation k H (Bialgebra.CounitAlgebra k H k)) :=
      (KaehlerDifferential.linearMapEquivDerivation k H).toEquiv.surjective.subsingleton
    exact Module.finrank_zero_of_subsingleton
  · intro h
    let A := _root_.CommHopfAlgCat.of k H
    let K := AlgebraicClosure k
    let AK := CommHopfAlgCat.baseChange (K := K) A
    have hcot : Subsingleton (Bialgebra.CotangentSpace k H) := by
      apply (Module.finrank_zero_iff (R := k)).mp
      rwa [← Derivation.finrank_eq_finrank_cotangentSpace]
    have hidem := (Ideal.cotangent_subsingleton_iff
      (I := Bialgebra.AugmentationIdeal k H)).mp hcot
    have hcotK : Subsingleton (Bialgebra.CotangentSpace K AK) := by
      apply (Ideal.cotangent_subsingleton_iff
        (I := Bialgebra.AugmentationIdeal K AK)).mpr
      have heq := congrArg HopfIdeal.toIdeal
        (CommHopfAlgCat.baseChangeHopfIdeal_augmentation (K := K) (H := A))
      rw [CommHopfAlgCat.baseChangeHopfIdeal_toIdeal, HopfIdeal.augmentation_toIdeal,
        HopfIdeal.augmentation_toIdeal] at heq
      simp only [Bialgebra.AugmentationIdeal, RingHom.ker_coe_toRingHom] at hidem ⊢
      rw [← heq]
      rw [IsIdempotentElem, ← Ideal.map_mul]
      exact congrArg
        (Ideal.map (Algebra.TensorProduct.includeRight : H →ₐ[k] K ⊗[k] H)) hidem.eq
    let _ := hcotK
    have hlieK : Module.finrank K
        (Derivation K AK (Bialgebra.CounitAlgebra K AK K)) = 0 := by
      rw [Derivation.finrank_eq_finrank_cotangentSpace]
      exact Module.finrank_zero_of_subsingleton
    let HK := FiniteTypeCommHopfAlgCat.of K AK
    have hidentity :=
      FiniteTypeCommHopfAlgCat.identityComponentHopfIdeal_eq_augmentation_of_finrank_lie_eq_zero
        HK hlieK
    let _ : Algebra.Etale K AK :=
      FiniteTypeCommHopfAlgCat.algebraEtale_of_identityComponentHopfIdeal_eq_augmentation
        HK hidentity
    exact Algebra.Etale.of_etale_tensorProduct_of_faithfullyFlat K

end HopfAlgebra

end TauCeti
