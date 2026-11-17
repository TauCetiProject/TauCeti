/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.GroupTheory.Complement.Gaschutz
public import TauCeti.GroupTheory.Complement.Sylow
public import TauCeti.GroupTheory.GroupExtension.Quotient.Cohomology
public import TauCeti.GroupTheory.Perm.FinThree.Alternating
public import TauCeti.GroupTheory.Perm.FinThree.Subgroup

/-!
# Complements of `A₃` in `S₃`

The alternating subgroup `A₃` of `S₃ = Equiv.Perm (Fin 3)` is an abelian normal subgroup with
exactly three complements, the point stabilizers
(`TauCeti.isComplement'_alternatingGroup_fin_three_iff`). This file works through the splitting
theory of `A₃ → S₃ → S₃ ⧸ A₃` on this example.

* **Splittings and crossed maps.** The quotient extension has three splittings, and there are
  three normalized crossed maps `S₃ → A₃`. The crossed projection along `⟨(0 1)⟩` is not a
  homomorphism: `(0 1) * (0 1 2)` has projection `(0 2 1)`, while the product of the projections
  of `(0 1)` and `(0 1 2)` is `(0 1 2)`.
* **Conjugation.** Conjugating by the three-cycle `(0 1 2) ∈ A₃` carries `⟨(0 1)⟩` to `⟨(1 2)⟩`,
  and multiplies the crossed projection by the principal crossed map of `(0 1 2)`.
* **The crossed transfer from `A₃`.** Along the transversal of `A₃` given by the splitting with
  range the stabilizer of `a`, the crossed transfer of the identity of `A₃` is the square of the
  crossed projection along that stabilizer; it sends `(0 1 2)` to `(0 2 1)`. The inverse exponent of
  `[S₃ : A₃] = 2` modulo `3` is `2`, and Gaschütz's construction from the local complement `⊥` of
  `A₃` in itself returns the stabilizer of `a`. Different transversals thus give different, but
  `A₃`-conjugate, complements.
* **Cohomology.** The quotient `S₃ ⧸ A₃` acts on `A₃` by inversion, and the class of the quotient
  extension in `H²(S₃ ⧸ A₃, A₃)` vanishes for every normalized section.
* **Sylow subgroups and invariance.** The unique Sylow `3`-subgroup of `S₃` is `A₃`, in which `A₃`
  has the local complement `⊥`. Each point stabilizer is the only complement of `A₃` that it
  normalizes, so the complement invariant under conjugation by `⟨(0 1)⟩` is `⟨(0 1)⟩` itself,
  although `2` divides `|S₃|`.

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
    (QuotientGroup.mk (transversal a q) : Perm (Fin 3) ⧸ alternatingGroup (Fin 3)) = q := by
  have h := isComplement'_alternatingGroup_stabilizer_perm_fin_three a
  simpa [transversal] using h.quotientSplitting.rightHom_splitting q

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

/-- The index `[S₃ : A₃] = 2` is prime to `|A₃| = 3`. -/
theorem coprime_index_card :
    Nat.Coprime (alternatingGroup (Fin 3)).index (Nat.card (alternatingGroup (Fin 3))) := by
  rw [alternatingGroup.index_eq_two, card_alternatingGroup_fin_three]
  decide

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
  h.gaschutzComplement_eq_of_forall_mem _ _ coprime_index_card
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
  exact key g n (by rwa [Perm.mem_alternatingGroup] at hg) (Perm.mem_alternatingGroup.mp n.2)

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
  -- `A₃` is a normal subgroup of order `3` and index `2`, hence a normal Sylow `3`-subgroup
  have h3 : IsPGroup 3 (alternatingGroup (Fin 3)) :=
    IsPGroup.of_card (n := 1) (by rw [card_alternatingGroup_fin_three, pow_one])
  let Q : Sylow 3 (Perm (Fin 3)) := h3.toSylow (by rw [alternatingGroup.index_eq_two]; decide)
  have hQ : (Q : Subgroup (Perm (Fin 3))).Normal := by
    rw [h3.toSylow_coe]
    infer_instance
  have := Sylow.unique_of_normal Q hQ
  rw [Subsingleton.elim P Q, h3.toSylow_coe]

/-- `⊥` is a local complement of `A₃` in every Sylow `3`-subgroup of `S₃`, which is `A₃` itself;
by Sylow detection (`IsPGroup.exists_isComplement'_iff_sylow`) this recovers that `A₃` has a
complement in `S₃`. -/
theorem isLocalComplement_bot_sylow_three (P : Sylow 3 (Perm (Fin 3))) :
    (alternatingGroup (Fin 3)).IsLocalComplement ⊥ P := by
  rw [coe_sylow_eq_alternatingGroup]
  exact Subgroup.isLocalComplement_self_left.mpr rfl

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

end TauCeti.Examples.SymmetricThree
