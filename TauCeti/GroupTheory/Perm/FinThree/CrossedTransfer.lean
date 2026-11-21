/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.GroupTheory.Complement.Gaschutz
public import TauCeti.GroupTheory.Perm.FinThree.Complement
import TauCeti.GroupTheory.GroupAction.Stabilizer.Basic
import TauCeti.GroupTheory.Perm.AlternatingCharacter

/-!
# Crossed transfer and change-of-transversal normalization in `S₃`

For the normal alternating subgroup `A₃ = alternatingGroup (Fin 3)` of
`S₃ = Equiv.Perm (Fin 3)`, this file evaluates the Gaschütz crossed transfer and its
change-of-transversal behavior along the canonical splitting transversals
`TauCeti.alternatingGroupFinThreeSplittingEquiv a` (`a : Fin 3`):

* Along any transversal of `A₃`, the untwisted transversal-word product vanishes identically
  (`TauCeti.prod_lWord_alternatingGroup_fin_three`) because it computes the classical transfer
  homomorphism `S₃ →* A₃`.
* With the conjugation twist along `TauCeti.alternatingGroupFinThreeSplittingEquiv a`, the crossed
  transfer of the local projection on `A₃` equals `(c_a ·) ^ 2`
  (`TauCeti.crossedTransfer_leftProjection_alternatingGroup_fin_three`), whose modular-inverse
  power recovers `TauCeti.symmetricThreeCrossedProjection a`
  (`TauCeti.crossedTransfer_leftProjection_pow_inv_index_alternatingGroup_fin_three`) and yields
  `gaschutzComplement = stabilizer a`
  (`TauCeti.gaschutzComplement_alternatingGroup_fin_three`).
* Comparing `a` and `b` produces the unnormalized change-of-transversal element
  `TauCeti.symmetricThreeChangeTransversal a b` with permutation coercion
  `finRotate 3 ^ (a - b).val` (`TauCeti.coe_symmetricThreeChangeTransversal`). Conjugating
  `stabilizer a` by `symmetricThreeChangeTransversal a b` yields `stabilizer (-(a + b))`
  (`TauCeti.conj_symmetricThreeChangeTransversal_smul_stabilizer`), which for `a ≠ b` is the third
  complement distinct from `stabilizer b`
  (`TauCeti.gaschutzComplement_ne_conj_symmetricThreeChangeTransversal_smul`), showing why the
  inverse-exponent power in `Subgroup.IsLocalComplement.gaschutzComplement_changeTransversal`
  cannot be omitted.

## References

* W. Gaschütz, *Zur Erweiterungstheorie der endlichen Gruppen*, J. reine angew. Math. 190
  (1952), 93–107.
* B. Sambale, *On the converse of Gaschütz' complement theorem*, arXiv:2303.00254.
-/

public section

open scoped IsMulCommutative Pointwise

namespace TauCeti

attribute [local instance] Subgroup.conjugationAction Subgroup.fintypeQuotientOfFiniteIndex

/-- Omitting the conjugation action `t u • ·` from `crossedTransfer` collapses the product of
transversal words in `A₃` to `1` for *every* transversal `t` and *every* `g ∈ S₃`, because the
untwisted product computes the classical transfer homomorphism `S₃ →* A₃`. -/
@[simp]
theorem prod_lWord_alternatingGroup_fin_three
    (t : Equiv.Perm (Fin 3) ⧸ alternatingGroup (Fin 3) → Equiv.Perm (Fin 3))
    (ht : ∀ q : Equiv.Perm (Fin 3) ⧸ alternatingGroup (Fin 3),
      (QuotientGroup.mk (t q) : Equiv.Perm (Fin 3) ⧸ alternatingGroup (Fin 3)) = q)
    (g : Equiv.Perm (Fin 3)) :
    (∏ q : Equiv.Perm (Fin 3) ⧸ alternatingGroup (Fin 3),
      (⟨lWord (alternatingGroup (Fin 3)) t q g,
        lWord_mem (alternatingGroup (Fin 3)) t ht q g⟩ : alternatingGroup (Fin 3))) = 1 := by
  have htr := transfer_eq_prod_lWord t ht (MonoidHom.id (alternatingGroup (Fin 3))) g
  rw [monoidHom_perm_alternatingGroup_fin_three_apply_eq_one] at htr
  simpa only [MonoidHom.id_apply] using htr.symm

/-- Along `alternatingGroupFinThreeSplittingEquiv a`, the unnormalized crossed transfer of the
local projection on `A₃` equals the square `(c_a ·) ^ 2` of `symmetricThreeCrossedProjection a`. -/
theorem crossedTransfer_leftProjection_alternatingGroup_fin_three
    (h : (alternatingGroup (Fin 3)).IsLocalComplement ⊥ (alternatingGroup (Fin 3))) (a : Fin 3)
    (g : Equiv.Perm (Fin 3)) :
    crossedTransfer (alternatingGroup (Fin 3)) (alternatingGroupFinThreeSplittingEquiv a)
      (mk_alternatingGroupFinThreeSplittingEquiv a) h.leftProjection g =
        symmetricThreeCrossedProjection a g ^ 2 := by
  rw [h.crossedTransfer_leftProjection_apply
    (alternatingGroupFinThreeSplittingEquiv a) (mk_alternatingGroupFinThreeSplittingEquiv a)
    (isComplement'_alternatingGroup_stabilizer_perm_fin_three a) bot_le
    (alternatingGroupFinThreeSplittingEquiv_mem_stabilizer a) g,
    alternatingGroup.index_eq_two, ← symmetricThreeCrossedProjection_def]

/-- Normalizing the crossed transfer by the inverse exponent `e = 2` recovers
`symmetricThreeCrossedProjection a`. -/
theorem crossedTransfer_leftProjection_pow_inv_index_alternatingGroup_fin_three
    (h : (alternatingGroup (Fin 3)).IsLocalComplement ⊥ (alternatingGroup (Fin 3))) (a : Fin 3)
    (g : Equiv.Perm (Fin 3)) :
    crossedTransfer (alternatingGroup (Fin 3)) (alternatingGroupFinThreeSplittingEquiv a)
      (mk_alternatingGroupFinThreeSplittingEquiv a) h.leftProjection g ^
        (((alternatingGroup (Fin 3)).index :
          ZMod (Nat.card (alternatingGroup (Fin 3))))⁻¹).val =
      symmetricThreeCrossedProjection a g := by
  rw [h.crossedTransfer_leftProjection_pow_inv_index_eq_crossedProjection
    (alternatingGroupFinThreeSplittingEquiv a) (mk_alternatingGroupFinThreeSplittingEquiv a)
    coprime_index_card_alternatingGroup_fin_three
    (isComplement'_alternatingGroup_stabilizer_perm_fin_three a) bot_le
    (alternatingGroupFinThreeSplittingEquiv_mem_stabilizer a),
    ← symmetricThreeCrossedProjection_def]

/-- The Gaschütz complement of `⊥` in `A₃` along `alternatingGroupFinThreeSplittingEquiv a` is
`stabilizer a`. -/
theorem gaschutzComplement_alternatingGroup_fin_three
    (h : (alternatingGroup (Fin 3)).IsLocalComplement ⊥ (alternatingGroup (Fin 3))) (a : Fin 3) :
    h.gaschutzComplement
      (alternatingGroupFinThreeSplittingEquiv a)
      (mk_alternatingGroupFinThreeSplittingEquiv a) =
        MulAction.stabilizer (Equiv.Perm (Fin 3)) a :=
  h.gaschutzComplement_eq_of_forall_mem
    (alternatingGroupFinThreeSplittingEquiv a) (mk_alternatingGroupFinThreeSplittingEquiv a)
    coprime_index_card_alternatingGroup_fin_three
    (isComplement'_alternatingGroup_stabilizer_perm_fin_three a) bot_le
    (alternatingGroupFinThreeSplittingEquiv_mem_stabilizer a)

/-- Any transposition `swap (a + 1) (a + 2)` inverts every element `m ∈ A₃` by conjugation, so
in the order-`3` group `A₃` the coboundary value `(swap • m) / m` equals `m` itself. -/
private theorem swap_smul_div_self_alternatingGroup_fin_three (a : Fin 3)
    (m : alternatingGroup (Fin 3)) :
    (Equiv.swap (a + 1) (a + 2) : Equiv.Perm (Fin 3)) • m / m = m := by
  have hs : Equiv.swap (a + 1) (a + 2) ∉ alternatingGroup (Fin 3) := by
    rw [Equiv.Perm.mem_alternatingGroup, Equiv.Perm.sign_swap (by revert a; decide)]
    decide
  have hsmul : (Equiv.swap (a + 1) (a + 2) : Equiv.Perm (Fin 3)) • m = m⁻¹ := by
    have hconj : (Equiv.swap (a + 1) (a + 2) : Equiv.Perm (Fin 3)) • m =
        MulAut.conjNormal (Equiv.swap (a + 1) (a + 2)) m :=
      Subtype.ext (by rw [Subgroup.coe_conjugationAction_smul, MulAut.conjNormal_apply])
    simpa only [MonoidHom.id_apply] using hconj.trans
      ((MonoidHom.id (alternatingGroup (Fin 3))).map_conjNormal_alternatingGroup_eq_inv hs m)
  have hcube : m * (m * m) = 1 := by
    simpa only [card_alternatingGroup_fin_three, pow_three] using pow_card_eq_one' (x := m)
  rw [hsmul, div_eq_mul_inv, ← mul_inv_rev, inv_eq_of_mul_eq_one_left hcube]

/-- The unnormalized change-of-transversal element in `A₃` comparing
`alternatingGroupFinThreeSplittingEquiv a` and `alternatingGroupFinThreeSplittingEquiv b`. -/
noncomputable def symmetricThreeChangeTransversal (a b : Fin 3) : alternatingGroup (Fin 3) :=
  ∏ v : Equiv.Perm (Fin 3) ⧸ alternatingGroup (Fin 3),
    alternatingGroupFinThreeSplittingEquiv a v •
      (alternatingGroup (Fin 3)).isLocalComplement_bot_self.leftProjection
        ⟨transversalDiff (alternatingGroup (Fin 3))
          (alternatingGroupFinThreeSplittingEquiv a)
          (alternatingGroupFinThreeSplittingEquiv b) v,
          transversalDiff_mem (alternatingGroup (Fin 3))
            (alternatingGroupFinThreeSplittingEquiv a)
            (alternatingGroupFinThreeSplittingEquiv b)
            (mk_alternatingGroupFinThreeSplittingEquiv a)
            (mk_alternatingGroupFinThreeSplittingEquiv b) v⟩

/-- Unfolding formula for `symmetricThreeChangeTransversal` as the twisted product of transversal
differences across `S₃ ⧸ A₃`. -/
theorem symmetricThreeChangeTransversal_def (a b : Fin 3) :
    symmetricThreeChangeTransversal a b =
      ∏ v : Equiv.Perm (Fin 3) ⧸ alternatingGroup (Fin 3),
        alternatingGroupFinThreeSplittingEquiv a v •
          (alternatingGroup (Fin 3)).isLocalComplement_bot_self.leftProjection
            ⟨transversalDiff (alternatingGroup (Fin 3))
              (alternatingGroupFinThreeSplittingEquiv a)
              (alternatingGroupFinThreeSplittingEquiv b) v,
              transversalDiff_mem (alternatingGroup (Fin 3))
                (alternatingGroupFinThreeSplittingEquiv a)
                (alternatingGroupFinThreeSplittingEquiv b)
                (mk_alternatingGroupFinThreeSplittingEquiv a)
                (mk_alternatingGroupFinThreeSplittingEquiv b) v⟩ :=
  (rfl)

/-- `symmetricThreeChangeTransversal a b` equals the square (hence inverse) of
`(alternatingGroupFinThreeOrbitEquiv a).symm b`. -/
theorem symmetricThreeChangeTransversal_eq_orbitEquiv_symm_sq (a b : Fin 3) :
    symmetricThreeChangeTransversal a b =
      ((alternatingGroupFinThreeOrbitEquiv a).symm b) ^ 2 := by
  let r := (alternatingGroupFinThreeOrbitEquiv a).symm b
  let s := Equiv.swap (a + 1) (a + 2)
  have hchg := crossedTransfer_changeTransversal (alternatingGroup (Fin 3))
    (alternatingGroupFinThreeSplittingEquiv a) (mk_alternatingGroupFinThreeSplittingEquiv a)
    (alternatingGroupFinThreeSplittingEquiv b) (mk_alternatingGroupFinThreeSplittingEquiv b)
    (alternatingGroup (Fin 3)).isLocalComplement_bot_self.isMulCocycle₁_leftProjection s
  rw [← symmetricThreeChangeTransversal_def,
    crossedTransfer_leftProjection_alternatingGroup_fin_three,
    crossedTransfer_leftProjection_alternatingGroup_fin_three,
    symmetricThreeCrossedProjection_swap_add_one_add_two, one_pow, one_mul,
    swap_smul_div_self_alternatingGroup_fin_three] at hchg
  have hprinc :=
    (forall_symmetricThreeCrossedProjection_eq_mul_smul_div_iff a b r).mpr rfl s
  rw [symmetricThreeCrossedProjection_swap_add_one_add_two, one_mul,
    swap_smul_div_self_alternatingGroup_fin_three] at hprinc
  exact hchg.symm.trans (by rw [hprinc])

/-- Closed form for `symmetricThreeChangeTransversal a b` as a permutation:
`finRotate 3 ^ (a - b).val`. -/
@[simp]
theorem coe_symmetricThreeChangeTransversal (a b : Fin 3) :
    (symmetricThreeChangeTransversal a b : Equiv.Perm (Fin 3)) =
      finRotate 3 ^ (a - b).val := by
  rw [symmetricThreeChangeTransversal_eq_orbitEquiv_symm_sq, Subgroup.coe_pow,
    coe_alternatingGroupFinThreeOrbitEquiv_symm]
  revert b a
  decide

/-- Along identical transversals `a = b`, `symmetricThreeChangeTransversal a a` is `1`. -/
@[simp]
theorem symmetricThreeChangeTransversal_self (a : Fin 3) :
    symmetricThreeChangeTransversal a a = 1 := by
  rw [symmetricThreeChangeTransversal_eq_orbitEquiv_symm_sq,
    alternatingGroupFinThreeOrbitEquiv_symm_self, one_pow]

/-- Conjugating `stabilizer a` by the unnormalized change-of-transversal element
`symmetricThreeChangeTransversal a b` gives `stabilizer (-(a + b))` (which equals `stabilizer a`
when `a = b`, and the third complement distinct from both `stabilizer a` and `stabilizer b` when
`a ≠ b`). -/
theorem conj_symmetricThreeChangeTransversal_smul_stabilizer (a b : Fin 3) :
    MulAut.conj (symmetricThreeChangeTransversal a b : Equiv.Perm (Fin 3)) •
      MulAction.stabilizer (Equiv.Perm (Fin 3)) a =
        MulAction.stabilizer (Equiv.Perm (Fin 3)) (-(a + b)) := by
  rw [MulAction.conj_smul_stabilizer, stabilizer_perm_fin_three_inj,
    coe_symmetricThreeChangeTransversal, Equiv.Perm.smul_def]
  revert b a
  decide

/-- For any two distinct points `a ≠ b`, the Gaschütz complements along
`alternatingGroupFinThreeSplittingEquiv a` and `alternatingGroupFinThreeSplittingEquiv b` are *not*
conjugate by the unnormalized change-of-transversal element
`symmetricThreeChangeTransversal a b`. -/
theorem gaschutzComplement_ne_conj_symmetricThreeChangeTransversal_smul
    (h : (alternatingGroup (Fin 3)).IsLocalComplement ⊥ (alternatingGroup (Fin 3))) {a b : Fin 3}
    (hab : a ≠ b) :
    h.gaschutzComplement
      (alternatingGroupFinThreeSplittingEquiv b)
      (mk_alternatingGroupFinThreeSplittingEquiv b) ≠
    MulAut.conj (symmetricThreeChangeTransversal a b : Equiv.Perm (Fin 3)) •
      h.gaschutzComplement
        (alternatingGroupFinThreeSplittingEquiv a)
        (mk_alternatingGroupFinThreeSplittingEquiv a) := by
  rw [gaschutzComplement_alternatingGroup_fin_three,
    gaschutzComplement_alternatingGroup_fin_three,
    conj_symmetricThreeChangeTransversal_smul_stabilizer, ne_eq, stabilizer_perm_fin_three_inj]
  revert hab b a
  decide

end TauCeti
