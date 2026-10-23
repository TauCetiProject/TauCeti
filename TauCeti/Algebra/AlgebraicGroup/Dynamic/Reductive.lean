/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.Dynamic.LeviDecomposition.Coordinate
public import TauCeti.Algebra.AlgebraicGroup.Dynamic.Smooth
public import TauCeti.Algebra.AlgebraicGroup.Dynamic.Tangent.CharZero
public import TauCeti.Algebra.AlgebraicGroup.Dynamic.Unipotent.Basic
public import TauCeti.Algebra.AlgebraicGroup.Dynamic.Unipotent.Connected
public import TauCeti.Algebra.AlgebraicGroup.HopfIdeal.Points.Order
public import TauCeti.Algebra.AlgebraicGroup.Unipotent.Radical.Reductive.Basic

/-!
# Dynamic subgroups of reductive groups

Let `λ : 𝔾ₘ → G` be a cocharacter of an affine group, with dynamic parabolic `P(λ)`, dynamic
unipotent subgroup `U(λ)` and dynamic Levi subgroup `Z(λ)`. This file proves that for a reductive
group `G` over a field, `P(λ) = G` holds exactly when `λ` is central, that is, when `Z(λ) = G`.

The argument is the standard one. Multiplication identifies `P(λ)` with `U(λ) × Z(λ)` as a
scheme, so both factors are retracts of `P(λ)` and inherit formal smoothness from it. When
`P(λ) = G`, the subgroup `U(λ)` is normalized by every point of `G`; it is geometrically connected
and its geometric points are unipotent. If `G` is moreover smooth, `U(λ)` is therefore a
connected normal smooth unipotent closed subgroup, and reductivity forces it to be trivial.
Hence `Z(λ) = P(λ) = G`.

On Lie algebras, `Lie P(λ)` is the sum of the nonnegative weight spaces of `λ` and `Lie U(λ)` is
the sum of the positive ones. So a cocharacter of a reductive group with `P(λ) = G` has no
nontrivial adjoint weights. Over an algebraically closed field of characteristic zero, Cartier's
theorem makes `P(λ)` smooth, and a smooth closed subgroup with the full Lie algebra is the whole
group. There, `P(λ) = G` exactly when `λ` has no negative weights. In particular, the adjoint
weights of a noncentral cocharacter of a reductive group cannot all be nonnegative.

## Main declarations

* `BialgHom.isUnipotentRadicalCandidate_unipotentDefiningHopfIdeal`: in a smooth group, if
  `P(λ) = G` then `U(λ)` is a connected normal smooth unipotent closed subgroup.
* `TauCeti.reductiveCommHopfAlgProperty.unipotentDefiningHopfIdeal_eq_augmentation`: in a
  reductive group, if `P(λ) = G` then `U(λ)` is trivial.
* `TauCeti.reductiveCommHopfAlgProperty.leviDefiningHopfIdeal_eq_bot_iff`: in a reductive group,
  `Z(λ) = G` if and only if `P(λ) = G`.
* `TauCeti.reductiveCommHopfAlgProperty.nontrivialAdjointWeights_eq_empty`: in a reductive group,
  if `P(λ) = G` then `λ` has no nontrivial adjoint weights.
* `TauCeti.reductiveCommHopfAlgProperty.parabolicDefiningHopfIdeal_eq_bot_iff_of_charZero`: over
  an algebraically closed field of characteristic zero, `P(λ) = G` if and only if `λ` has no
  negative adjoint weights.

## References

* B. Conrad, O. Gabber, G. Prasad, *Pseudo-reductive Groups*, §2.1.
* J. S. Milne, *Algebraic Groups* (2017), Chapter 13.
-/

public section

open CategoryTheory WithConv TauCeti TauCeti.Cocharacter
open scoped TensorProduct

namespace BialgHom

universe u

variable {k : Type u} [Field k] {H : FiniteTypeCommHopfAlgCat.{u, u} k}

/-- In a smooth affine group of finite type over a field, the dynamic unipotent subgroup of a
cocharacter whose dynamic parabolic is the whole group is a connected normal smooth unipotent
closed subgroup. -/
theorem isUnipotentRadicalCandidate_unipotentDefiningHopfIdeal [Algebra.Smooth k H]
    (l : H →ₐc[k] LaurentPolynomial k) (hl : parabolicDefiningHopfIdeal l = ⊥) :
    HopfIdeal.IsUnipotentRadicalCandidate H l.unipotentDefiningHopfIdeal := by
  refine .mk (isNormal_unipotentDefiningHopfIdeal_of_parabolicDefiningHopfIdeal_eq_bot l hl)
    (Cocharacter.geometricallyConnectedCommHopfAlgProperty_quotient_unipotentDefiningHopfIdeal l)
    ?_
  rw [smoothUnipotentCommHopfAlgProperty_iff]
  refine ⟨?_, fun g ↦ isUnipotentPoint_quotient_of_le_unipotent _ _ l (AlgebraicClosure k) ?_ g⟩
  · exact (smoothCommHopfAlgProperty_iff _).mp
      (smoothCommHopfAlgProperty_quotient_unipotentDefiningHopfIdeal l)
  · rw [quotientPointsSubgroup_unipotentDefiningHopfIdeal]

end BialgHom

namespace TauCeti.reductiveCommHopfAlgProperty

universe u w

variable {k : Type u} [Field k] {H : FiniteTypeCommHopfAlgCat.{u, u} k}

/-- **A cocharacter of a reductive group whose dynamic parabolic is the whole group has trivial
dynamic unipotent subgroup.** -/
theorem unipotentDefiningHopfIdeal_eq_augmentation (hH : reductiveCommHopfAlgProperty k H)
    (l : H →ₐc[k] LaurentPolynomial k) (hl : parabolicDefiningHopfIdeal l = ⊥) :
    l.unipotentDefiningHopfIdeal = HopfIdeal.augmentation k H := by
  have := hH.smooth
  refine le_antisymm (HopfIdeal.le_augmentation k H _) ?_
  rw [← hH.unipotentRadicalDefiningIdeal_eq_augmentation]
  exact FiniteTypeCommHopfAlgCat.unipotentRadicalDefiningIdeal_le H _
    (l.isUnipotentRadicalCandidate_unipotentDefiningHopfIdeal hl)

/-- If the dynamic parabolic of a cocharacter of a reductive group is the whole group, then its
dynamic unipotent subgroup has only the identity point over every value algebra. -/
theorem unipotent_eq_bot (hH : reductiveCommHopfAlgProperty k H)
    (l : H →ₐc[k] LaurentPolynomial k) (hl : parabolicDefiningHopfIdeal l = ⊥)
    (A : Type w) [CommRing A] [Algebra k A] :
    unipotent A l = ⊥ := by
  rw [← BialgHom.quotientPointsSubgroup_unipotentDefiningHopfIdeal,
    hH.unipotentDefiningHopfIdeal_eq_augmentation l hl, eq_bot_iff]
  intro g hg
  exact (CommHopfAlgCat.mem_quotientPointsSubgroup_augmentation_iff
    (_root_.CommHopfAlgCat.of k H) (CommAlgCat.of k A) g).mp hg

/-- If the dynamic parabolic of a cocharacter of a reductive group is the whole group, then every
point is centralized by the cocharacter. -/
theorem levi_eq_top (hH : reductiveCommHopfAlgProperty k H)
    (l : H →ₐc[k] LaurentPolynomial k) (hl : parabolicDefiningHopfIdeal l = ⊥)
    (A : Type w) [CommRing A] [Algebra k A] :
    levi A l = ⊤ := by
  rw [← l.parabolic_eq_top_of_parabolicDefiningHopfIdeal_eq_bot hl A, ← unipotent_sup_levi,
    hH.unipotent_eq_bot l hl A, bot_sup_eq]

/-- **A cocharacter of a reductive group has the whole group as its dynamic parabolic exactly
when it is central**, that is, when its dynamic Levi subgroup is the whole group. -/
theorem leviDefiningHopfIdeal_eq_bot_iff (hH : reductiveCommHopfAlgProperty k H)
    (l : H →ₐc[k] LaurentPolynomial k) :
    leviDefiningHopfIdeal l = ⊥ ↔ parabolicDefiningHopfIdeal l = ⊥ := by
  refine ⟨fun h ↦ ?_, fun hl ↦ ?_⟩
  · rw [← le_bot_iff, ← h, leviDefiningHopfIdeal_def]
    exact le_sup_left
  apply HopfIdeal.eq_of_forall_quotientPointsSubgroup_eq (H := _root_.CommHopfAlgCat.of k H)
  rintro ⟨A⟩
  rw [quotientPointsSubgroup_leviDefiningHopfIdeal, CommHopfAlgCat.quotientPointsSubgroup_bot]
  exact hH.levi_eq_top l hl A

section Lie

/-- If the dynamic parabolic of a cocharacter of a reductive group is the whole group, then the
cocharacter acts trivially on the Lie algebra: it has no nontrivial adjoint weights. -/
theorem nontrivialAdjointWeights_eq_empty (hH : reductiveCommHopfAlgProperty k H)
    (l : H →ₐc[k] LaurentPolynomial k) (hl : parabolicDefiningHopfIdeal l = ⊥) :
    Derivation.nontrivialAdjointWeights
      ((AddMonoidAlgebra.toMultiplicativeBialgEquiv k k ℤ).toBialgHom.comp l) = ∅ := by
  set π := (AddMonoidAlgebra.toMultiplicativeBialgEquiv k k ℤ).toBialgHom.comp l
  -- The strictly positive weight spaces span the Lie algebra of the trivial unipotent subgroup.
  have hpos : (⨆ n : ℤ, ⨆ (_ : 0 < n), Derivation.adjointWeightSpace π
      (Multiplicative.ofAdd n)) = ⊥ := by
    have h := BialgHom.lieSubalgebra_unipotentDefiningHopfIdeal_toSubmodule l
    rw [hH.unipotentDefiningHopfIdeal_eq_augmentation l hl, HopfIdeal.lieSubalgebra_augmentation,
      LieSubalgebra.bot_toSubmodule, eq_comm, Submodule.map_eq_bot_iff] at h
    exact h
  -- The nonnegative weight spaces span the Lie algebra of the whole group.
  have hnonneg : (⨆ n : ℤ, ⨆ (_ : 0 ≤ n), Derivation.adjointWeightSpace π
      (Multiplicative.ofAdd n)) = ⊤ := by
    have h := BialgHom.lieSubalgebra_parabolicDefiningHopfIdeal_toSubmodule l
    rw [hl, HopfIdeal.lieSubalgebra_bot, LieSubalgebra.top_toSubmodule, eq_comm,
      Submodule.map_eq_top_iff] at h
    exact h
  -- The weight decomposition was stated with classical decidable equality on the characters.
  let : DecidableEq (Multiplicative ℤ) := Classical.decEq _
  ext α
  simp only [Set.mem_empty_iff_false, iff_false, Derivation.mem_nontrivialAdjointWeights]
  rintro ⟨hα, hne⟩
  obtain ⟨n, rfl⟩ : ∃ n : ℤ, Multiplicative.ofAdd n = α := ⟨α.toAdd, rfl⟩
  rcases lt_trichotomy n 0 with hn | rfl | hn
  · -- A negative weight space is independent of the nonnegative ones, which span everything.
    apply hne
    have hdisj := (Derivation.isInternal_adjointWeightSpace π).submodule_iSupIndep
      (Multiplicative.ofAdd n)
    rw [← disjoint_top, ← hnonneg]
    refine hdisj.mono_right (iSup₂_le fun m hm ↦ ?_)
    exact le_iSup₂_of_le (Multiplicative.ofAdd m) (by simpa using (hm.trans_lt' hn).ne') le_rfl
  · exact hα rfl
  · exact hne (le_bot_iff.mp (hpos ▸ le_iSup₂_of_le n hn le_rfl))

variable [IsAlgClosed k] [CharZero k]

/-- **Over an algebraically closed field of characteristic zero, a cocharacter of a reductive
group has the whole group as its dynamic parabolic exactly when it has no negative adjoint
weights.** -/
theorem parabolicDefiningHopfIdeal_eq_bot_iff_of_charZero (hH : reductiveCommHopfAlgProperty k H)
    (l : H →ₐc[k] LaurentPolynomial k) :
    parabolicDefiningHopfIdeal l = ⊥ ↔ ∀ n : ℤ, n < 0 →
      Derivation.adjointWeightSpace
        ((AddMonoidAlgebra.toMultiplicativeBialgEquiv k k ℤ).toBialgHom.comp l)
        (Multiplicative.ofAdd n) = ⊥ := by
  refine ⟨fun hl n hn ↦ ?_, fun hneg ↦ ?_⟩
  · by_contra hne
    have hmem : Multiplicative.ofAdd n ∈ Derivation.nontrivialAdjointWeights
        ((AddMonoidAlgebra.toMultiplicativeBialgEquiv k k ℤ).toBialgHom.comp l) :=
      Derivation.mem_nontrivialAdjointWeights.mpr ⟨by simpa using hn.ne, hne⟩
    rw [hH.nontrivialAdjointWeights_eq_empty l hl] at hmem
    exact hmem
  have := geometricallyConnectedCommHopfAlgProperty.connectedSpace k H.obj hH.geometricallyConnected
  exact l.parabolicDefiningHopfIdeal_eq_bot_of_adjointWeightSpace_neg_eq_bot hneg

end Lie

end TauCeti.reductiveCommHopfAlgProperty
