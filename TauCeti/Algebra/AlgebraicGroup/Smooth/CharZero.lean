/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.Smooth.GeometricallyReduced
import Mathlib.RingTheory.HopfAlgebra.TensorProduct
import TauCeti.Algebra.AlgebraicGroup.Hopf.Translation
import TauCeti.Algebra.AlgebraicGroup.HopfIdeal.Cotangent
import TauCeti.Algebra.AlgebraicGroup.Smooth.AlgebraicallyClosed
import TauCeti.Algebra.AlgebraicGroup.Tangent.FiniteType
import TauCeti.Algebra.AlgebraicGroup.Tangent.InvariantDerivation
import TauCeti.Algebra.AlgebraicGroup.Tangent.KrullDimension
import TauCeti.Algebra.HopfAlgebra.HopfIdeal.Reduction
import TauCeti.AlgebraicGeometry.Scheme.RegularLocalRing
import TauCeti.RingTheory.FiniteType.PointSeparation
import TauCeti.RingTheory.FiniteType.Tensor.Product
import TauCeti.RingTheory.KrullDimension.Quotient
import TauCeti.RingTheory.RegularLocalRing.Basic
import TauCeti.RingTheory.Smooth.GeometricallyReduced
import TauCeti.RingTheory.Smooth.Regular

/-!
# Cartier's theorem

**Every affine group scheme of finite type over a field of characteristic zero is smooth.**
In Hopf coordinates: a finite-type commutative Hopf algebra over a field of characteristic zero
is smooth, and in particular reduced. Nonreduced groups such as `μ_p` and `αₚ` therefore occur
only in positive characteristic.

The proof runs over an algebraically closed field `k` first. Let `H` be the coordinate ring and
`N` its nilradical, a Hopf ideal since `k` is perfect.

* Every tangent vector at the identity extends to an invariant derivation of `H`, and in
  characteristic zero derivations send nilpotent functions into the augmentation ideal. Hence
  `N` lies in the square of the augmentation ideal, and the reduced group `H ⧸ N` has the same
  Lie algebra as `H`.
* The reduced group is smooth over `k`, so it is regular at the identity, and its Lie algebra has
  dimension `dim (H ⧸ N) = dim H`.
* So the Lie algebra of `H` has dimension `dim H`, which makes the local ring of `H` at the
  identity regular, hence a domain. Each nilpotent function is then killed by a function not
  vanishing at the identity.
* Translating by rational points moves the identity to every closed point, so each nilpotent
  function is killed by a function outside every maximal ideal, and is zero.

Over a general field of characteristic zero, each extension field embeds in an algebraically
closed one, over which the base-changed Hopf algebra is reduced. This is geometric reducedness,
which for finite-type Hopf algebras is equivalent to smoothness.

## Main results

* `TauCeti.smoothCommHopfAlgProperty_of_charZero`: **Cartier's theorem**, a finite-type
  commutative Hopf algebra over a field of characteristic zero is smooth.
* `TauCeti.HopfAlgebra.isReduced_of_charZero`: such a Hopf algebra is reduced.

## References

* J. S. Milne, *Algebraic Groups* (2017), Chapter 3 (Cartier's theorem).
* W. C. Waterhouse, *Introduction to Affine Group Schemes*, §11.4.
-/

public section

open AlgebraicGeometry
open scoped TensorProduct

namespace TauCeti

universe u v

namespace HopfAlgebra

section IsAlgClosed

variable {k : Type u} [Field k] [IsAlgClosed k] [CharZero k]
variable {H : Type v} [CommRing H] [_root_.HopfAlgebra k H] [Algebra.FiniteType k H]

/-- Over an algebraically closed field of characteristic zero, the Lie algebra of a finite-type
affine group has the dimension of the group. The reduced group has the same Lie algebra, since
nilpotent functions vanish to second order at the identity, and it is smooth. -/
private theorem finrank_lie_eq_ringKrullDim :
    (Module.finrank k (Derivation k H (Bialgebra.CounitAlgebra k H k)) : WithBot ℕ∞) =
      ringKrullDim H := by
  have _ : Algebra.Smooth k (H ⧸ (HopfIdeal.reduction k H).toIdeal) :=
    (smoothCommHopfAlgProperty_iff _).mp <| smoothCommHopfAlgProperty_of_isAlgClosed_of_isReduced
      k (CommHopfAlgCat.of k (H ⧸ (HopfIdeal.reduction k H).toIdeal))
  have _ : IsRegularRing (H ⧸ (HopfIdeal.reduction k H).toIdeal) := IsRegularRing.of_smooth (R := k)
  have hconormal : (HopfIdeal.reduction k H).conormalSubspace = ⊥ := by
    rw [HopfIdeal.conormalSubspace_eq_bot_iff_toIdeal_le_sq_augmentationIdeal,
      HopfIdeal.reduction_toIdeal]
    exact Bialgebra.nilradical_le_augmentationIdeal_sq
  have hlie := HopfIdeal.finrank_quotientLie_add_finrank_conormal (HopfIdeal.reduction k H)
  rw [hconormal, finrank_bot, add_zero] at hlie
  rw [← hlie, isRegularLocalRing_augmentationStalk_iff.mp inferInstance,
    HopfIdeal.reduction_toIdeal, ringKrullDim_quotient_nilradical]

/-- Over an algebraically closed field of characteristic zero, a nilpotent function on a
finite-type affine group is killed by a function not vanishing at the identity: the local ring
at the identity is regular, hence a domain. -/
private theorem exists_mul_eq_zero_of_isNilpotent {x : H} (hx : IsNilpotent x) :
    ∃ s : H, _root_.Bialgebra.counitAlgHom k H s ≠ 0 ∧ s * x = 0 := by
  have _ : IsRegularLocalRing
      ((Spec (CommRingCat.of H)).presheaf.stalk (Bialgebra.augmentationPoint k H)) :=
    isRegularLocalRing_augmentationStalk_iff.mpr finrank_lie_eq_ringKrullDim
  obtain ⟨⟨s, hs⟩, hsx⟩ := (IsLocalization.map_eq_zero_iff
    (Bialgebra.AugmentationIdeal k H).primeCompl
    ((Spec (CommRingCat.of H)).presheaf.stalk (Bialgebra.augmentationPoint k H)) x).mp
    (hx.map _).eq_zero
  exact ⟨s, hs, hsx⟩

end IsAlgClosed

/-- Over an algebraically closed field of characteristic zero, the coordinate ring of a
finite-type affine group is reduced. -/
private theorem isReduced_of_isAlgClosed_of_charZero (k : Type u) [Field k] [IsAlgClosed k]
    [CharZero k] (H : Type v) [CommRing H] [_root_.HopfAlgebra k H] [Algebra.FiniteType k H] :
    IsReduced H := by
  -- A nonzero nilpotent has a proper annihilator vanishing at a rational point `g`.
  -- Translation by `g` contradicts annihilation by a function nonzero at the identity.
  refine ⟨fun x hx ↦ by_contra fun hx0 ↦ ?_⟩
  let J : Ideal H := (Submodule.span H {x}).annihilator
  have hJ : (1 : H) ∉ J.radical := by
    rintro ⟨n, hn⟩
    rw [one_pow, Submodule.mem_annihilator_span_singleton, one_smul] at hn
    exact hx0 hn
  obtain ⟨g, hJg, -⟩ := exists_algHom_apply_ne_zero_of_notMem_radical (k := k) (K := k) J hJ
  let τ := rightTranslationAlgEquiv (WithConv.toConv g)
  obtain ⟨t, ht, htx⟩ := exists_mul_eq_zero_of_isNilpotent (k := k) (hx.map τ)
  have hs : τ.symm t ∈ J := by
    rw [Submodule.mem_annihilator_span_singleton, smul_eq_mul]
    apply τ.injective
    rw [map_mul, AlgEquiv.apply_symm_apply, htx, map_zero]
  have hg : g (τ.symm t) = _root_.Bialgebra.counitAlgHom k H t := by
    have h := AlgHom.congr_fun (counitAlgHom_comp_rightTranslationAlgHom (WithConv.toConv g))
      (τ.symm t)
    rw [AlgHom.comp_apply, ← rightTranslationAlgEquiv_toAlgHom, AlgEquiv.coe_toAlgHom,
      AlgEquiv.apply_symm_apply, WithConv.ofConv_toConv] at h
    exact h.symm
  exact ht (hg ▸ hJg hs)

end HopfAlgebra

/-- **Cartier's theorem**: a finite-type commutative Hopf algebra over a field of characteristic
zero is smooth. Equivalently, every affine group scheme of finite type over such a field is
smooth. -/
theorem smoothCommHopfAlgProperty_of_charZero (k : Type u) [Field k] [CharZero k]
    (H : CommHopfAlgCat.{v} k) [Algebra.FiniteType k H] : smoothCommHopfAlgProperty k H := by
  apply smoothCommHopfAlgProperty_of_geometricallyReduced
  rw [geometricallyReducedCommHopfAlgProperty_iff]
  intro K _ _
  let L := AlgebraicClosure K
  have _ : CharZero L := charZero_of_injective_algebraMap (algebraMap k L).injective
  have _ : IsReduced (L ⊗[k] H) := HopfAlgebra.isReduced_of_isAlgClosed_of_charZero L (L ⊗[k] H)
  let f : H ⊗[k] K →ₐ[k] L ⊗[k] H :=
    (Algebra.TensorProduct.comm k H L).toAlgHom.comp
      (Algebra.TensorProduct.map (AlgHom.id k H) (IsScalarTower.toAlgHom k K L))
  have hf : Function.Injective f :=
    (Algebra.TensorProduct.comm k H L).injective.comp
      (Module.Flat.lTensor_preserves_injective_linearMap _ (algebraMap K L).injective)
  exact isReduced_of_injective f hf

/-- **A finite-type commutative Hopf algebra over a field of characteristic zero is reduced**:
affine group schemes of finite type in characteristic zero have no nilpotent functions. -/
theorem HopfAlgebra.isReduced_of_charZero (k : Type u) [Field k] [CharZero k] (H : Type v)
    [CommRing H] [_root_.HopfAlgebra k H] [Algebra.FiniteType k H] : IsReduced H := by
  have _ : Algebra.Smooth k H :=
    (smoothCommHopfAlgProperty_iff _).mp (smoothCommHopfAlgProperty_of_charZero k
      (CommHopfAlgCat.of k H))
  exact isReduced_of_smooth k H

end TauCeti
