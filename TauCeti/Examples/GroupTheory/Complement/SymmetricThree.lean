/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.GroupTheory.Complement.Invariant.Internal
public import TauCeti.GroupTheory.Complement.Sylow
public import TauCeti.GroupTheory.GroupExtension.Quotient.Cohomology
public import TauCeti.GroupTheory.Perm.FinThree.CrossedTransfer

/-!
# Complements of `A₃` in `S₃`

The alternating subgroup `A₃` of `S₃ = Equiv.Perm (Fin 3)` is an abelian normal subgroup with
exactly three complements, the point stabilizers
(`TauCeti.isComplement'_alternatingGroup_fin_three_iff`), whereas `⊤` is not a complement
(`TauCeti.Examples.SymmetricThree.not_isComplement'_alternatingGroup_top`). This file works through
the splitting theory of `A₃ → S₃ → S₃ ⧸ A₃` on this example.

* **Splittings and crossed maps.** The quotient extension has three splittings, and there are
  three normalized crossed maps `S₃ → A₃`. The crossed projection along `⟨(0 1)⟩` is not a
  homomorphism: `(0 1) * (0 1 2)` has projection `(0 2 1)`, while the product of the projections
  of `(0 1)` and `(0 1 2)` is `(0 1 2)`. Conversely, the normalized map
  `TauCeti.Examples.SymmetricThree.swapZeroOneFinRotateMap` whose zero locus `{1, (0 2), (1 2)}` is
  not a subgroup fails the `1`-cocycle identity
  (`TauCeti.Examples.SymmetricThree.not_isMulCocycle₁_swapZeroOneFinRotateMap`).
* **Conjugation.** Conjugating by the three-cycle `(0 1 2) ∈ A₃` carries `⟨(0 1)⟩` to `⟨(1 2)⟩`,
  and multiplies the crossed projection by the principal crossed map of `(0 1 2)`.
* **The crossed transfer from `A₃`.** Along the transversal of `A₃` given by the splitting with
  range the stabilizer of `a`, the crossed transfer of the identity of `A₃` is the square of the
  crossed projection along that stabilizer; it sends `(0 1 2)` to `(0 2 1)`. The inverse exponent of
  `[S₃ : A₃] = 2` modulo `3` is `2`, and Gaschütz's construction from the local complement `⊥` of
  `A₃` in itself returns the stabilizer of `a`. Different transversals thus give different, but
  `A₃`-conjugate, complements: between `a = 2` and `b = 0`, conjugating `stabilizer 2` by the
  unnormalized change-of-transversal element `(0 2 1)` lands on `stabilizer 1 ≠ stabilizer 0`,
  whereas raising to the inverse exponent `2` recovers `stabilizer 0`.
* **Cohomology.** The quotient `S₃ ⧸ A₃` acts on `A₃` by inversion, and the class of the quotient
  extension in `H²(S₃ ⧸ A₃, A₃)` vanishes for every normalized section.
* **Sylow subgroups and invariance.** The unique Sylow `3`-subgroup of `S₃` is `A₃`, in which `A₃`
  has the local complement `⊥`. Each point stabilizer is the only complement of `A₃` that it
  normalizes, so the complement invariant under conjugation by `⟨(0 1)⟩` is `⟨(0 1)⟩` itself,
  although `2` divides `|S₃|`; `Subgroup.exists_invariant_complement` and
  `Subgroup.exists_invariant_local_complement` likewise apply to `stabilizer 2` acting on `S₃`.

The points of `Fin 3` are `0, 1, 2`, so the transposition `(0 1)` generates the stabilizer of `2`
and `finRotate 3` is the three-cycle `(0 1 2)`.

## References

* W. Gaschütz, *Zur Erweiterungstheorie der endlichen Gruppen*, J. reine angew. Math. 190
  (1952), 93–107.
-/

public section

open Equiv groupCohomology
open scoped IsMulCommutative Pointwise

namespace TauCeti.Examples.SymmetricThree

attribute [local instance] Subgroup.conjugationAction

/-! ### Splittings and normalized crossed maps -/

/-- The whole group `⊤` does not complement `A₃` in `S₃`. -/
theorem not_isComplement'_alternatingGroup_top :
    ¬ (alternatingGroup (Fin 3)).IsComplement' ⊤ := by
  rw [Subgroup.isComplement'_top_right, Subgroup.eq_bot_iff_card, card_alternatingGroup_fin_three]
  decide

/-- **The quotient extension of `S₃` by `A₃` has exactly three splittings**, one for each
complement. -/
theorem card_splitting_quotientExtension :
    Nat.card (alternatingGroup (Fin 3)).quotientExtension.Splitting = 3 := by
  rw [Nat.card_congr (alternatingGroup (Fin 3)).quotientSplittingEquiv,
    card_isComplement'_alternatingGroup_fin_three]

/-- **There are exactly three normalized crossed maps `S₃ → A₃`**, read additively: one for each
complement. -/
theorem card_normalized_isCocycle₁ :
    Nat.card {c : Perm (Fin 3) → Additive (alternatingGroup (Fin 3)) //
      IsCocycle₁ c ∧ ∀ n : alternatingGroup (Fin 3), c n = Additive.ofMul n} = 3 := by
  rw [← Nat.card_congr (Subgroup.crossedProjectionEquiv (alternatingGroup (Fin 3))),
    card_isComplement'_alternatingGroup_fin_three]

/-- The three-cycle `(0 1 2)`, as an element of `A₃`. -/
def threeCycle : alternatingGroup (Fin 3) :=
  ⟨finRotate 3, Perm.finRotate_bit1_mem_alternatingGroup (n := 1)⟩

/-- The three-cycle of `A₃` is `finRotate 3`. -/
@[simp]
theorem coe_threeCycle : (threeCycle : Perm (Fin 3)) = finRotate 3 := (rfl)

/-- Every crossed projection onto `A₃` sends the three-cycle to itself. This is
`Subgroup.IsComplement'.crossedProjection_coe` at `threeCycle`, in the simp normal form produced by
`coe_threeCycle`. -/
@[simp]
theorem crossedProjection_finRotate {D : Subgroup (Perm (Fin 3))}
    (h : (alternatingGroup (Fin 3)).IsComplement' D) :
    h.crossedProjection (finRotate 3) = threeCycle :=
  h.crossedProjection_coe threeCycle

section CrossedProjection

variable
  (h₀ : (alternatingGroup (Fin 3)).IsComplement' (MulAction.stabilizer (Perm (Fin 3)) (0 : Fin 3)))
  (h₂ : (alternatingGroup (Fin 3)).IsComplement' (MulAction.stabilizer (Perm (Fin 3)) (2 : Fin 3)))

/-- The crossed projection along `⟨(0 1)⟩` sends `(0 2) = (0 1 2) * (0 1)` to `(0 1 2)`. -/
theorem coe_crossedProjection_swap_zero_two :
    (h₂.crossedProjection (swap 0 2) : Perm (Fin 3)) = finRotate 3 := by
  have h : swap (0 : Fin 3) 2 = finRotate 3 * swap 0 1 := by decide
  rw [h]
  exact congrArg Subtype.val
    (h₂.crossedProjection_mul threeCycle ⟨swap 0 1, swap_mem_stabilizer_perm_fin_three 2⟩)

/-- The crossed projection along `⟨(0 1)⟩` sends `(1 2) = (0 2 1) * (0 1)` to `(0 2 1)`. -/
theorem coe_crossedProjection_swap_one_two :
    (h₂.crossedProjection (swap 1 2) : Perm (Fin 3)) = (finRotate 3)⁻¹ := by
  have h : swap (1 : Fin 3) 2 = (finRotate 3)⁻¹ * swap 0 1 := by decide
  rw [h]
  exact congrArg Subtype.val
    (h₂.crossedProjection_mul threeCycle⁻¹ ⟨swap 0 1, swap_mem_stabilizer_perm_fin_three 2⟩)

/-- The crossed projection along `⟨(0 1)⟩` sends `(0 1) * (0 1 2) = (0 2 1) * (0 1)` to
`(0 2 1)`. -/
theorem coe_crossedProjection_swap_mul_finRotate :
    (h₂.crossedProjection (swap 0 1 * finRotate 3) : Perm (Fin 3)) = (finRotate 3)⁻¹ := by
  have h : swap (0 : Fin 3) 1 * finRotate 3 = (finRotate 3)⁻¹ * swap 0 1 := by decide
  rw [h]
  exact congrArg Subtype.val
    (h₂.crossedProjection_mul threeCycle⁻¹ ⟨swap 0 1, swap_mem_stabilizer_perm_fin_three 2⟩)

/-- **A crossed projection need not be a homomorphism**: the projection along `⟨(0 1)⟩` of
`(0 1) * (0 1 2)` is not the product of the projections of `(0 1)` and `(0 1 2)`. -/
theorem crossedProjection_mul_ne :
    h₂.crossedProjection (swap 0 1 * finRotate 3) ≠
      h₂.crossedProjection (swap 0 1) * h₂.crossedProjection (finRotate 3) := by
  intro h
  have h' := congrArg Subtype.val h
  rw [coe_crossedProjection_swap_mul_finRotate, h₂.crossedProjection_coe_right
      ⟨swap 0 1, swap_mem_stabilizer_perm_fin_three 2⟩, one_mul,
    crossedProjection_finRotate h₂, coe_threeCycle] at h'
  revert h'
  decide

/-- **Conjugating `⟨(0 1)⟩` by `(0 1 2)` gives `⟨(1 2)⟩`**: the stabilizer of `2` goes to the
stabilizer of `0`. -/
theorem conj_finRotate_smul_stabilizer :
    MulAut.conj (finRotate 3) • MulAction.stabilizer (Perm (Fin 3)) (2 : Fin 3) =
      MulAction.stabilizer (Perm (Fin 3)) (0 : Fin 3) := by
  have h : finRotate 3 • (2 : Fin 3) = 0 := by decide
  rw [← h, MulAction.stabilizer_smul_eq_stabilizer_map_conj, MulEquiv.toMonoidHom_eq_coe,
    map_conj_eq_conj_smul]

/-- **Principal crossed maps move complements.** The crossed projection along `⟨(1 2)⟩` is the
crossed projection along `⟨(0 1)⟩` times the principal crossed map `x ↦ x • a / a` of the
three-cycle `a = (0 1 2) ∈ A₃`. -/
theorem crossedProjection_zero_eq (x : Perm (Fin 3)) :
    h₀.crossedProjection x = h₂.crossedProjection x *
      (x • threeCycle / threeCycle) :=
  (h₂.eq_conj_smul_iff_crossedProjection_eq h₀ threeCycle).mp
    conj_finRotate_smul_stabilizer.symm x

end CrossedProjection

/-- Normalized candidate map `S₃ → A₃` that restricts to the identity on `A₃`, sends `swap 0 1`
to `threeCycle`, and sends `swap 0 2` and `swap 1 2` to `1`. -/
def swapZeroOneFinRotateMap (σ : Perm (Fin 3)) : alternatingGroup (Fin 3) :=
  if h : Perm.sign σ = 1 then
    ⟨σ, Perm.mem_alternatingGroup.mpr h⟩
  else if σ = swap 0 1 then
    threeCycle
  else
    1

/-- Unfolding formula for `swapZeroOneFinRotateMap`. -/
theorem swapZeroOneFinRotateMap_def (σ : Perm (Fin 3)) :
    swapZeroOneFinRotateMap σ =
      if h : Perm.sign σ = 1 then
        ⟨σ, Perm.mem_alternatingGroup.mpr h⟩
      else if σ = swap 0 1 then
        threeCycle
      else
        1 :=
  (rfl)

/-- `swapZeroOneFinRotateMap` restricts to the identity on `A₃`. -/
@[simp]
theorem swapZeroOneFinRotateMap_coe (n : alternatingGroup (Fin 3)) :
    swapZeroOneFinRotateMap n = n := by
  simp only [swapZeroOneFinRotateMap_def, Perm.mem_alternatingGroup.mp n.property, ↓reduceDIte]

/-- `swapZeroOneFinRotateMap` sends `swap 0 1` to `threeCycle`. -/
@[simp]
theorem swapZeroOneFinRotateMap_swap_zero_one :
    swapZeroOneFinRotateMap (swap 0 1) = threeCycle := by
  rw [swapZeroOneFinRotateMap_def]
  decide

/-- `swapZeroOneFinRotateMap` sends `swap 0 2` to `1`. -/
@[simp]
theorem swapZeroOneFinRotateMap_swap_zero_two : swapZeroOneFinRotateMap (swap 0 2) = 1 := by
  rw [swapZeroOneFinRotateMap_def]
  decide

/-- `swapZeroOneFinRotateMap` sends `swap 1 2` to `1`. -/
@[simp]
theorem swapZeroOneFinRotateMap_swap_one_two : swapZeroOneFinRotateMap (swap 1 2) = 1 := by
  rw [swapZeroOneFinRotateMap_def]
  decide

/-- `swapZeroOneFinRotateMap` is not a multiplicative `1`-cocycle, because its zero locus
`{1, swap 0 2, swap 1 2}` is not closed under multiplication. -/
theorem not_isMulCocycle₁_swapZeroOneFinRotateMap : ¬ IsMulCocycle₁ swapZeroOneFinRotateMap := by
  intro hc
  have hmul := hc (swap 1 2) (swap 0 2)
  have hprod : (swap (1 : Fin 3) 2 * swap 0 2 : Perm (Fin 3)) = (threeCycle : Perm (Fin 3)) := by
    decide
  rw [hprod, swapZeroOneFinRotateMap_coe, swapZeroOneFinRotateMap_swap_one_two,
    swapZeroOneFinRotateMap_swap_zero_two, smul_one, mul_one, ← Subtype.coe_inj, coe_threeCycle,
    Subgroup.coe_one] at hmul
  revert hmul
  decide

/-! ### The crossed transfer from `A₃` and Gaschütz complements -/

/-- The transversal of `A₃` given by the splitting with range the stabilizer of `a`: it sends the
odd coset to the transposition of the two points other than `a`. -/
noncomputable def transversal (a : Fin 3) :
    Perm (Fin 3) ⧸ alternatingGroup (Fin 3) → Perm (Fin 3) :=
  fun q => (isComplement'_alternatingGroup_stabilizer_perm_fin_three a).quotientSplitting q

/-- The transversal along the stabilizer of `a` is the splitting of the quotient extension with
range that stabilizer. -/
theorem transversal_apply (a : Fin 3) (q : Perm (Fin 3) ⧸ alternatingGroup (Fin 3)) :
    transversal a q =
      (isComplement'_alternatingGroup_stabilizer_perm_fin_three a).quotientSplitting q :=
  (rfl)

/-- The transversal along the stabilizer of `a` sends the trivial coset to `1`. -/
@[simp]
theorem transversal_one (a : Fin 3) : transversal a 1 = 1 :=
  (transversal_apply a 1).trans (map_one _)

/-- The transversal along the stabilizer of `a` is a transversal: it represents each coset. -/
@[simp]
theorem mk_transversal (a : Fin 3) (q : Perm (Fin 3) ⧸ alternatingGroup (Fin 3)) :
    (QuotientGroup.mk (transversal a q) : Perm (Fin 3) ⧸ alternatingGroup (Fin 3)) = q :=
  GroupExtension.Splitting.mk_quotientExtension
    (isComplement'_alternatingGroup_stabilizer_perm_fin_three a).quotientSplitting q

/-- The transversal along the stabilizer of `a` takes values in that stabilizer. -/
theorem transversal_mem (a : Fin 3) (q : Perm (Fin 3) ⧸ alternatingGroup (Fin 3)) :
    transversal a q ∈ MulAction.stabilizer (Perm (Fin 3)) a := by
  rw [transversal, Subgroup.IsComplement'.quotientSplitting_apply]
  exact Subtype.property _

/-- The transversal along the stabilizer of `a` sends the odd coset to the transposition of the two
points other than `a`. -/
theorem transversal_mk_swap (a : Fin 3) :
    transversal a (swap (a + 1) (a + 2) : Perm (Fin 3)) = swap (a + 1) (a + 2) :=
  (isComplement'_alternatingGroup_stabilizer_perm_fin_three a).quotientSplitting_mk
    ⟨_, swap_mem_stabilizer_perm_fin_three a⟩

/-- **The crossed transfer of the identity of `A₃`** along the transversal in the stabilizer of
`a` is the square of the crossed projection along that stabilizer. -/
theorem crossedTransfer_id_apply {a : Fin 3}
    (h : (alternatingGroup (Fin 3)).IsComplement' (MulAction.stabilizer (Perm (Fin 3)) a))
    (g : Perm (Fin 3)) :
    crossedTransfer (alternatingGroup (Fin 3)) (transversal a) (mk_transversal a)
      (id : alternatingGroup (Fin 3) → alternatingGroup (Fin 3)) g =
      h.crossedProjection g ^ 2 := by
  rw [h.crossedTransfer_id_apply _ _ (transversal_mem a), alternatingGroup.index_eq_two]

/-- **The crossed transfer of the identity of `A₃` sends `(0 1 2)` to its square `(0 2 1)`**, along
the transversal in the stabilizer of any point. -/
theorem coe_crossedTransfer_id_finRotate (a : Fin 3) :
    ((crossedTransfer (alternatingGroup (Fin 3)) (transversal a) (mk_transversal a)
      (id : alternatingGroup (Fin 3) → alternatingGroup (Fin 3)) (finRotate 3) :
        alternatingGroup (Fin 3)) : Perm (Fin 3)) = (finRotate 3)⁻¹ := by
  have h := isComplement'_alternatingGroup_stabilizer_perm_fin_three a
  rw [crossedTransfer_id_apply h,
    crossedProjection_finRotate h, Subgroup.coe_pow, coe_threeCycle]
  decide

/-- The crossed transfer of the identity of `A₃` along the transversal in `⟨(0 1)⟩` vanishes at
`(0 1)`. -/
theorem crossedTransfer_id_swap :
    crossedTransfer (alternatingGroup (Fin 3)) (transversal 2) (mk_transversal 2)
      (id : alternatingGroup (Fin 3) → alternatingGroup (Fin 3))
      (swap 0 1) = 1 := by
  have h := isComplement'_alternatingGroup_stabilizer_perm_fin_three 2
  rw [crossedTransfer_id_apply h,
    h.crossedProjection_coe_right ⟨swap 0 1, swap_mem_stabilizer_perm_fin_three 2⟩, one_pow]

/-- **The inverse exponent is `2`**: the inverse of `[S₃ : A₃] = 2` modulo `|A₃| = 3`. -/
theorem val_inv_index :
    (((alternatingGroup (Fin 3)).index : ZMod (Nat.card (alternatingGroup (Fin 3))))⁻¹).val =
      2 := by
  rw [alternatingGroup.index_eq_two, card_alternatingGroup_fin_three]
  decide +kernel

section Gaschutz

variable (h : (alternatingGroup (Fin 3)).IsLocalComplement ⊥ (alternatingGroup (Fin 3)))

/-- **Gaschütz's construction from `A₃`.** Along the transversal in the stabilizer of `a`, the
Gaschütz complement of the local complement `⊥` of `A₃` in itself is the stabilizer of `a`. -/
theorem gaschutzComplement_transversal (a : Fin 3) :
    h.gaschutzComplement (transversal a) (mk_transversal a) =
      MulAction.stabilizer (Perm (Fin 3)) a :=
  h.gaschutzComplement_eq_of_forall_mem _ _ coprime_index_card_alternatingGroup_fin_three
    (isComplement'_alternatingGroup_stabilizer_perm_fin_three a) bot_le (transversal_mem a)

/-- **The Gaschütz complement depends on the transversal.** The transversals through `(0 1)` and
through `(1 2)` give the complements `⟨(0 1)⟩` and `⟨(1 2)⟩`, which are distinct but conjugate by
`(0 1 2) ∈ A₃` (`TauCeti.Examples.SymmetricThree.conj_finRotate_smul_stabilizer`). -/
theorem gaschutzComplement_transversal_ne :
    h.gaschutzComplement (transversal 2) (mk_transversal 2) ≠
      h.gaschutzComplement (transversal 0) (mk_transversal 0) := by
  rw [gaschutzComplement_transversal, gaschutzComplement_transversal]
  exact stabilizer_perm_fin_three_injective.ne (by decide)

end Gaschutz

/-- The unnormalized change-of-transversal element from `a = 2` to `b = 0` equals
`(finRotate 3)⁻¹`. -/
theorem coe_symmetricThreeChangeTransversal_two_zero :
    (symmetricThreeChangeTransversal 2 0 : Perm (Fin 3)) = (finRotate 3)⁻¹ := by
  rw [coe_symmetricThreeChangeTransversal]
  decide

/-- Conjugating `stabilizer 2` (`⟨swap 0 1⟩`) by the unnormalized change-of-transversal element
`symmetricThreeChangeTransversal 2 0` yields `stabilizer 1` (`⟨swap 0 2⟩`). -/
theorem conj_symmetricThreeChangeTransversal_two_zero_smul_stabilizer :
    MulAut.conj (symmetricThreeChangeTransversal 2 0 : Perm (Fin 3)) •
      MulAction.stabilizer (Perm (Fin 3)) (2 : Fin 3) =
        MulAction.stabilizer (Perm (Fin 3)) (1 : Fin 3) :=
  (conj_symmetricThreeChangeTransversal_smul_stabilizer 2 0).trans
    (congrArg (MulAction.stabilizer (Perm (Fin 3))) (by decide))

/-- Conjugating `stabilizer 2` by the unnormalized change-of-transversal element
`symmetricThreeChangeTransversal 2 0` does *not* yield `stabilizer 0`. -/
theorem conj_symmetricThreeChangeTransversal_two_zero_smul_stabilizer_ne :
    MulAut.conj (symmetricThreeChangeTransversal 2 0 : Perm (Fin 3)) •
      MulAction.stabilizer (Perm (Fin 3)) (2 : Fin 3) ≠
        MulAction.stabilizer (Perm (Fin 3)) (0 : Fin 3) := by
  have hne := gaschutzComplement_ne_conj_symmetricThreeChangeTransversal_smul
    (alternatingGroup (Fin 3)).isLocalComplement_bot_self (a := 2) (b := 0) (by decide)
  rw [gaschutzComplement_alternatingGroup_fin_three,
    gaschutzComplement_alternatingGroup_fin_three] at hne
  exact hne.symm

/-- Conjugating `stabilizer 2` by the inverse-exponent normalized power
`symmetricThreeChangeTransversal 2 0 ^ 2` yields `stabilizer 0`. -/
theorem conj_symmetricThreeChangeTransversal_two_zero_sq_smul_stabilizer :
    MulAut.conj ((symmetricThreeChangeTransversal 2 0 ^ 2 : alternatingGroup (Fin 3)) :
      Perm (Fin 3)) • MulAction.stabilizer (Perm (Fin 3)) (2 : Fin 3) =
        MulAction.stabilizer (Perm (Fin 3)) (0 : Fin 3) := by
  let _ := Subgroup.fintypeQuotientOfFiniteIndex (H := alternatingGroup (Fin 3))
  have hchg :=
    (alternatingGroup (Fin 3)).isLocalComplement_bot_self.gaschutzComplement_changeTransversal
      (alternatingGroupFinThreeSplittingEquiv 2) (mk_alternatingGroupFinThreeSplittingEquiv 2)
      coprime_index_card_alternatingGroup_fin_three
      (alternatingGroupFinThreeSplittingEquiv 0) (mk_alternatingGroupFinThreeSplittingEquiv 0)
  rw [← symmetricThreeChangeTransversal_def, val_inv_index,
    gaschutzComplement_alternatingGroup_fin_three,
    gaschutzComplement_alternatingGroup_fin_three] at hchg
  exact hchg.symm

/-! ### The quotient action and the extension class -/

section Cohomology

attribute [local instance] Subgroup.quotientConjugationAction

/-- **`S₃ ⧸ A₃` acts on `A₃` by inversion**: an odd permutation inverts every element of `A₃`. -/
theorem mk_smul_eq_inv {g : Perm (Fin 3)} (hg : g ∉ alternatingGroup (Fin 3))
    (n : alternatingGroup (Fin 3)) :
    (g : Perm (Fin 3) ⧸ alternatingGroup (Fin 3)) • n = n⁻¹ := by
  have key : ∀ g n : Perm (Fin 3), Perm.sign g ≠ 1 → Perm.sign n = 1 → g * n * g⁻¹ = n⁻¹ := by
    decide
  rw [Subgroup.quotientConjugationAction_mk_smul]
  apply Subtype.ext
  rw [MulAut.conjNormal_apply, Subgroup.coe_inv]
  exact key g n (by rwa [Perm.mem_alternatingGroup] at hg) (Perm.mem_alternatingGroup.mp n.property)

/-- **The extension class of `A₃ → S₃ → S₃ ⧸ A₃` vanishes** in `H²(S₃ ⧸ A₃, A₃)`, for every
normalized section, since `A₃` has a complement. -/
theorem cohomologyClass_factorSet_eq_zero
    (σ : (alternatingGroup (Fin 3)).quotientExtension.Section) (hσ : σ 1 = 1) :
    (GroupExtension.factorSet σ hσ
      (alternatingGroup (Fin 3)).quotientExtension_inducesAction).cohomologyClass = 0 :=
  ((alternatingGroup (Fin 3)).exists_complement_iff_cohomologyClass_eq_zero σ hσ).mp
    ⟨_, isComplement'_alternatingGroup_stabilizer_perm_fin_three 0⟩

end Cohomology

/-! ### Sylow subgroups and invariant complements -/

/-- **The unique Sylow `3`-subgroup of `S₃` is `A₃`.** -/
theorem coe_sylow_eq_alternatingGroup (P : Sylow 3 (Perm (Fin 3))) :
    (P : Subgroup (Perm (Fin 3))) = alternatingGroup (Fin 3) := by
  rw [sylow_three_perm_fin_three_eq P, coe_alternatingGroupSylowThree]

/-- `⊥` is a local complement of `A₃` in every Sylow `3`-subgroup of `S₃`, which is `A₃` itself;
by Sylow detection (`IsPGroup.exists_isComplement'_iff_sylow`) this recovers that `A₃` has a
complement in `S₃`. -/
theorem isLocalComplement_bot_sylow_three (P : Sylow 3 (Perm (Fin 3))) :
    (alternatingGroup (Fin 3)).IsLocalComplement ⊥ P := by
  rw [coe_sylow_eq_alternatingGroup]
  exact Subgroup.isLocalComplement_self_left.mpr rfl

/-- The alternating subgroup `A₃` has a complement in `S₃`. -/
theorem exists_isComplement'_alternatingGroup_fin_three :
    ∃ D : Subgroup (Perm (Fin 3)), (alternatingGroup (Fin 3)).IsComplement' D :=
  -- Recover global splitting from the local complement `⊥` in `alternatingGroupSylowThree`.
  (isPGroup_three_alternatingGroup_fin_three.exists_isComplement'_iff_sylow
    alternatingGroupSylowThree).mpr
    ⟨⊥, isLocalComplement_bot_sylow_three alternatingGroupSylowThree⟩

/-- **Each point stabilizer is the only complement of `A₃` that it normalizes.** In particular the
complement invariant under conjugation by the `2`-group `⟨(0 1)⟩` is `⟨(0 1)⟩` itself, although `2`
divides `|S₃|`. -/
theorem isComplement'_and_le_normalizer_iff (a : Fin 3) (D : Subgroup (Perm (Fin 3))) :
    ((alternatingGroup (Fin 3)).IsComplement' D ∧
        MulAction.stabilizer (Perm (Fin 3)) a ≤ Subgroup.normalizer (D : Set (Perm (Fin 3)))) ↔
      D = MulAction.stabilizer (Perm (Fin 3)) a := by
  refine ⟨fun ⟨hD, hle⟩ => ?_, by
    rintro rfl
    exact ⟨isComplement'_alternatingGroup_stabilizer_perm_fin_three a, Subgroup.le_normalizer⟩⟩
  obtain ⟨b, rfl⟩ := (isComplement'_alternatingGroup_fin_three_iff D).mp hD
  -- point stabilizers are self-normalizing, and any two have the same order
  rw [(isFrobeniusComplement_stabilizer_perm_fin_three b).normalizer_eq_self] at hle
  exact (Subgroup.eq_of_le_of_card_ge hle
    (by rw [card_stabilizer_perm_fin_three, card_stabilizer_perm_fin_three])).symm

/-- `A₃` admits a complement in `S₃` closed under conjugation by every element of
`stabilizer 2`. -/
theorem exists_isComplement'_and_stabilizer_two_conj_mem :
    ∃ D : Subgroup (Perm (Fin 3)),
      (alternatingGroup (Fin 3)).IsComplement' D ∧
        ∀ a ∈ MulAction.stabilizer (Perm (Fin 3)) (2 : Fin 3),
          ∀ d ∈ D, a * d * a⁻¹ ∈ D := by
  let S := MulAction.stabilizer (Perm (Fin 3)) (2 : Fin 3)
  let _ : MulDistribMulAction (ConjAct S) (Perm (Fin 3)) :=
    MulDistribMulAction.compHom (Perm (Fin 3))
      ((MulAut.conj : Perm (Fin 3) →* MulAut (Perm (Fin 3))).comp
        (S.subtype.comp (ConjAct.ofConjAct (G := S)).toMonoidHom))
  have hsmul (a : ConjAct S) (x : Perm (Fin 3)) :
      a • x = ((ConjAct.ofConjAct a : S) : Perm (Fin 3)) * x *
        ((ConjAct.ofConjAct a : S) : Perm (Fin 3))⁻¹ := by
    rw [MulAction.compHom_smul_def, MonoidHom.comp_apply, MonoidHom.comp_apply,
      Subgroup.subtype_apply, MulEquiv.coe_toMonoidHom, MulAut.smul_def, MulAut.conj_apply]
  -- Apply `Subgroup.exists_invariant_complement` to `ConjAct (stabilizer 2)` acting on `S₃`.
  obtain ⟨D, hD, hinv⟩ :=
    Subgroup.exists_invariant_complement (A := ConjAct S) (p := 3) (q := 2)
      (alternatingGroup (Fin 3))
      isPGroup_three_alternatingGroup_fin_three
      ((isPGroup_two_stabilizer_perm_fin_three 2).of_equiv ConjAct.toConjAct)
      (by decide)
      (fun a n hn => by
        rw [hsmul]
        exact (inferInstance : (alternatingGroup (Fin 3)).Normal).conj_mem n hn _)
      alternatingGroupSylowThree
      ⟨⊥, isLocalComplement_bot_sylow_three alternatingGroupSylowThree⟩
  refine ⟨D, hD, fun a ha d hd => ?_⟩
  have hmem := hinv (ConjAct.toConjAct (⟨a, ha⟩ : S)) d hd
  rwa [hsmul, ConjAct.ofConjAct_toConjAct] at hmem

/-- `A₃` admits a local complement in `⊤` normalized by `stabilizer 2`. -/
theorem exists_isLocalComplement_top_and_stabilizer_two_le_normalizer :
    ∃ D : Subgroup (Perm (Fin 3)),
      (alternatingGroup (Fin 3)).IsLocalComplement D ⊤ ∧
        MulAction.stabilizer (Perm (Fin 3)) (2 : Fin 3) ≤
          Subgroup.normalizer (D : Set (Perm (Fin 3))) := by
  -- Apply `Subgroup.exists_invariant_local_complement` with `H = ⊤` and `A = stabilizer 2`.
  refine Subgroup.exists_invariant_local_complement (p := 3) (q := 2)
    (⊤ : Subgroup (Perm (Fin 3))) le_top
    (by rw [(⊤ : Subgroup (Perm (Fin 3))).normalizer_eq_top]; exact le_top)
    (by rw [(alternatingGroup (Fin 3)).normalizer_eq_top]; exact le_top)
    isPGroup_three_alternatingGroup_fin_three (isPGroup_two_stabilizer_perm_fin_three 2)
    (by decide) (alternatingGroupSylowThree.subtype le_top) ⟨⊥, ?_⟩
  rw [Sylow.coe_subtype, coe_alternatingGroupSylowThree, Subgroup.map_subgroupOf_eq_of_le le_top]
  exact (alternatingGroup (Fin 3)).isLocalComplement_bot_self

end TauCeti.Examples.SymmetricThree
