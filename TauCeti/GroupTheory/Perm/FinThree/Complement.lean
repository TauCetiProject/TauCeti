/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.GroupTheory.Sylow
public import TauCeti.GroupTheory.Complement.Stabilizer
public import TauCeti.GroupTheory.Perm.FinThree.Subgroup
import Mathlib.Data.Finite.Perm

/-!
# Complements, quotient splittings, and Sylow subgroups of `S₃`

Inside `S₃ = Equiv.Perm (Fin 3)`, the alternating subgroup `A₃ = alternatingGroup (Fin 3)` has
prime order `3` and acts regularly on `Fin 3`, with orbit equivalence
`TauCeti.alternatingGroupFinThreeOrbitEquiv` sending `(finRotate 3) ^ (b - a).val` at base point
`a` to `b`.

The three point stabilizers `MulAction.stabilizer (Equiv.Perm (Fin 3)) a` (`a : Fin 3`) are
pairwise distinct, self-normalizing subgroups of order `2`. Using `Subgroup.fin_three_cases`, they
exhaust:
* the subgroup complements of `A₃` in `S₃` (`TauCeti.alternatingGroupFinThreeComplementEquiv`),
* the homomorphic splittings of the quotient extension `1 → A₃ → S₃ → S₃ ⧸ A₃ → 1`
  (`TauCeti.alternatingGroupFinThreeSplittingEquiv`), and
* the Sylow `2`-subgroups of `S₃` (`TauCeti.stabilizerSylowTwoPermFinThreeEquiv`),

whereas `A₃` itself is the unique Sylow `3`-subgroup of `S₃`
(`TauCeti.alternatingGroupSylowThree`), in which `A₃` has unique local complement `⊥`.
-/

public section

open scoped IsMulCommutative Pointwise

namespace TauCeti

/-- The alternating group `A₃` is commutative. -/
instance instIsMulCommutativeAlternatingGroupFinThree :
    IsMulCommutative (alternatingGroup (Fin 3)) :=
  alternatingGroup.isMulCommutative_of_card_le_three (by simp)

/-- The three-cycle `finRotate 3` is an even permutation. -/
theorem finRotate_three_mem_alternatingGroup : finRotate 3 ∈ alternatingGroup (Fin 3) := by
  rw [Equiv.Perm.mem_alternatingGroup]
  decide

/-! ### Regular action of `A₃` on `Fin 3` -/

/-- Evaluation at a base point `a : Fin 3` identifies `A₃` with `Fin 3`. -/
noncomputable def alternatingGroupFinThreeOrbitEquiv (a : Fin 3) :
    alternatingGroup (Fin 3) ≃ Fin 3 :=
  (isComplement'_alternatingGroup_stabilizer_perm_fin_three a).stabilizerOrbitEquiv

/-- `alternatingGroupFinThreeOrbitEquiv a` evaluates an even permutation at `a`. -/
@[simp]
theorem alternatingGroupFinThreeOrbitEquiv_apply (a : Fin 3) (n : alternatingGroup (Fin 3)) :
    alternatingGroupFinThreeOrbitEquiv a n = (n : Equiv.Perm (Fin 3)) a := by
  simpa only [alternatingGroupFinThreeOrbitEquiv, Equiv.Perm.smul_def] using
    (isComplement'_alternatingGroup_stabilizer_perm_fin_three a).stabilizerOrbitEquiv_apply n

/-- The unique element of `A₃` carrying `a` to `b` is `finRotate 3 ^ (b - a).val`. -/
@[simp]
theorem coe_alternatingGroupFinThreeOrbitEquiv_symm (a b : Fin 3) :
    ((alternatingGroupFinThreeOrbitEquiv a).symm b : Equiv.Perm (Fin 3)) =
      finRotate 3 ^ (b - a).val := by
  let r : alternatingGroup (Fin 3) :=
    ⟨finRotate 3, finRotate_three_mem_alternatingGroup⟩ ^ (b - a).val
  have hr : alternatingGroupFinThreeOrbitEquiv a r = b := by
    rw [alternatingGroupFinThreeOrbitEquiv_apply, Subgroup.coe_pow, Subgroup.coe_mk,
      Equiv.Perm.coe_pow, ← finCycle_eq_finRotate_iterate, finCycle_apply, add_sub_cancel]
  exact congrArg Subtype.val ((Equiv.symm_apply_eq _).mpr hr.symm)

/-! ### Point stabilizers and their normalizers -/

/-- Distinct points of `Fin 3` have distinct stabilizers in `S₃`. -/
theorem stabilizer_perm_fin_three_injective :
    Function.Injective
      (MulAction.stabilizer (Equiv.Perm (Fin 3)) : Fin 3 → Subgroup (Equiv.Perm (Fin 3))) := by
  intro a b hab
  have hmem : Equiv.swap (a + 1) (a + 2) ∈ MulAction.stabilizer (Equiv.Perm (Fin 3)) b := by
    rw [← hab, mem_stabilizer_perm_fin_three_iff]
    exact Or.inr rfl
  clear hab
  rw [mem_stabilizer_perm_fin_three_iff] at hmem
  revert hmem b a
  decide

/-- Two point stabilizers in `S₃` coincide if and only if their stabilized points coincide. -/
@[simp]
theorem stabilizer_perm_fin_three_inj (a b : Fin 3) :
    MulAction.stabilizer (Equiv.Perm (Fin 3)) a =
      MulAction.stabilizer (Equiv.Perm (Fin 3)) b ↔ a = b :=
  stabilizer_perm_fin_three_injective.eq_iff

/-- Every point stabilizer in `S₃` is self-normalizing. -/
@[simp]
theorem normalizer_stabilizer_perm_fin_three (a : Fin 3) :
    Subgroup.normalizer
      (MulAction.stabilizer (Equiv.Perm (Fin 3)) a : Set (Equiv.Perm (Fin 3))) =
        MulAction.stabilizer (Equiv.Perm (Fin 3)) a :=
  MulAction.normalizer_stabilizer_of_injective stabilizer_perm_fin_three_injective a

/-! ### Classification of subgroup complements and quotient splittings -/

/-- A subgroup of `S₃` complements `A₃` if and only if it is one of the three point
stabilizers. -/
theorem isComplement'_alternatingGroup_fin_three_iff (D : Subgroup (Equiv.Perm (Fin 3))) :
    (alternatingGroup (Fin 3)).IsComplement' D ↔
      ∃ a : Fin 3, D = MulAction.stabilizer (Equiv.Perm (Fin 3)) a := by
  refine ⟨fun hD => ?_, ?_⟩
  · have hmul := hD.card_mul_card
    simp only [card_alternatingGroup_fin_three, Nat.card_perm, Nat.card_fin,
      Nat.factorial] at hmul
    rcases Subgroup.fin_three_cases D with rfl | rfl | rfl | rfl | rfl | rfl
    · rw [Subgroup.card_bot] at hmul
      omega
    · exact ⟨0, rfl⟩
    · exact ⟨1, rfl⟩
    · exact ⟨2, rfl⟩
    · rw [card_alternatingGroup_fin_three] at hmul
      omega
    · simp only [Subgroup.card_top, Nat.card_perm, Nat.card_fin, Nat.factorial] at hmul
      omega
  · rintro ⟨a, rfl⟩
    exact isComplement'_alternatingGroup_stabilizer_perm_fin_three a

/-- The three points of `Fin 3` parameterize the subgroup complements of `A₃` in `S₃`. -/
noncomputable def alternatingGroupFinThreeComplementEquiv :
    Fin 3 ≃ {D : Subgroup (Equiv.Perm (Fin 3)) // (alternatingGroup (Fin 3)).IsComplement' D} :=
  Equiv.ofBijective
    (fun a => ⟨MulAction.stabilizer (Equiv.Perm (Fin 3)) a,
      isComplement'_alternatingGroup_stabilizer_perm_fin_three a⟩)
    ⟨fun _ _ h => stabilizer_perm_fin_three_injective (congrArg Subtype.val h),
      fun ⟨D, hD⟩ =>
        let ⟨a, ha⟩ := (isComplement'_alternatingGroup_fin_three_iff D).mp hD
        ⟨a, Subtype.ext ha.symm⟩⟩

/-- `alternatingGroupFinThreeComplementEquiv` sends `a` to `stabilizer a`. -/
@[simp]
theorem coe_alternatingGroupFinThreeComplementEquiv (a : Fin 3) :
    (alternatingGroupFinThreeComplementEquiv a : Subgroup (Equiv.Perm (Fin 3))) =
      MulAction.stabilizer (Equiv.Perm (Fin 3)) a :=
  (rfl)

/-- The inverse of `alternatingGroupFinThreeComplementEquiv` recovers the stabilized point. -/
@[simp]
theorem alternatingGroupFinThreeComplementEquiv_symm_stabilizer (a : Fin 3) :
    alternatingGroupFinThreeComplementEquiv.symm
      ⟨MulAction.stabilizer (Equiv.Perm (Fin 3)) a,
        isComplement'_alternatingGroup_stabilizer_perm_fin_three a⟩ = a := by
  apply alternatingGroupFinThreeComplementEquiv.injective
  rw [Equiv.apply_symm_apply]
  exact Subtype.ext (coe_alternatingGroupFinThreeComplementEquiv a).symm

/-- There are exactly three subgroup complements of `A₃` in `S₃`. -/
@[simp]
theorem card_isComplement'_alternatingGroup_fin_three :
    Nat.card {D : Subgroup (Equiv.Perm (Fin 3)) // (alternatingGroup (Fin 3)).IsComplement' D} =
      3 := by
  simpa using Nat.card_congr alternatingGroupFinThreeComplementEquiv.symm

/-- Along the `a`-stabilizer complement of `A₃`, the normal component of `σ` in Mathlib's
complement decomposition is `finRotate 3 ^ (σ a - a).val`. -/
theorem coe_equiv_fst_stabilizer_perm_fin_three (a : Fin 3) (σ : Equiv.Perm (Fin 3)) :
    (((isComplement'_alternatingGroup_stabilizer_perm_fin_three a).equiv σ).1 :
      Equiv.Perm (Fin 3)) = finRotate 3 ^ (σ a - a).val := by
  let h := isComplement'_alternatingGroup_stabilizer_perm_fin_three a
  have hfix : ((h.equiv σ).2 : Equiv.Perm (Fin 3)) a = a :=
    MulAction.mem_stabilizer_iff.mp (h.equiv σ).2.property
  have hsmul : alternatingGroupFinThreeOrbitEquiv a (h.equiv σ).1 = σ a := by
    calc alternatingGroupFinThreeOrbitEquiv a (h.equiv σ).1
      _ = ((h.equiv σ).1 : Equiv.Perm (Fin 3)) a := alternatingGroupFinThreeOrbitEquiv_apply a _
      _ = ((h.equiv σ).1 : Equiv.Perm (Fin 3)) (((h.equiv σ).2 : Equiv.Perm (Fin 3)) a) := by
          rw [hfix]
      _ = (((h.equiv σ).1 : Equiv.Perm (Fin 3)) * (h.equiv σ).2) a := rfl
      _ = σ a := by rw [h.equiv_fst_mul_equiv_snd]
  exact (congrArg Subtype.val ((Equiv.eq_symm_apply _).mpr hsmul)).trans
    (coe_alternatingGroupFinThreeOrbitEquiv_symm a (σ a))

/-- Along the `a`-stabilizer complement of `A₃`, the stabilizer component of `σ` in Mathlib's
complement decomposition is `(finRotate 3 ^ (σ a - a).val)⁻¹ * σ`. -/
theorem coe_equiv_snd_stabilizer_perm_fin_three (a : Fin 3) (σ : Equiv.Perm (Fin 3)) :
    (((isComplement'_alternatingGroup_stabilizer_perm_fin_three a).equiv σ).2 :
      Equiv.Perm (Fin 3)) = (finRotate 3 ^ (σ a - a).val)⁻¹ * σ := by
  have hmul :=
    (isComplement'_alternatingGroup_stabilizer_perm_fin_three a).equiv_fst_mul_equiv_snd σ
  rw [coe_equiv_fst_stabilizer_perm_fin_three] at hmul
  exact (inv_mul_eq_iff_eq_mul.mpr hmul.symm).symm

/-- The three points of `Fin 3` parameterize the splittings of
`1 → A₃ → S₃ → S₃ ⧸ A₃ → 1`. -/
noncomputable def alternatingGroupFinThreeSplittingEquiv :
    Fin 3 ≃ (alternatingGroup (Fin 3)).quotientExtension.Splitting :=
  alternatingGroupFinThreeComplementEquiv.trans
    (alternatingGroup (Fin 3)).quotientSplittingEquiv.symm

/-- `alternatingGroupFinThreeSplittingEquiv a` is the quotient splitting induced by
`stabilizer a`. -/
@[simp]
theorem alternatingGroupFinThreeSplittingEquiv_apply (a : Fin 3) :
    alternatingGroupFinThreeSplittingEquiv a =
      (isComplement'_alternatingGroup_stabilizer_perm_fin_three a).quotientSplitting := by
  apply DFunLike.ext
  intro q
  simp only [alternatingGroupFinThreeSplittingEquiv, Equiv.trans_apply,
    Subgroup.quotientSplittingEquiv_symm_apply]
  have heq : alternatingGroupFinThreeComplementEquiv a =
      ⟨MulAction.stabilizer (Equiv.Perm (Fin 3)) a,
        isComplement'_alternatingGroup_stabilizer_perm_fin_three a⟩ :=
    Subtype.ext (coe_alternatingGroupFinThreeComplementEquiv a)
  rw [heq]

/-- The range of the `a`-th quotient splitting of `S₃` over `A₃` is `stabilizer a`. -/
theorem range_alternatingGroupFinThreeSplittingEquiv (a : Fin 3) :
    (alternatingGroupFinThreeSplittingEquiv a).toMonoidHom.range =
      MulAction.stabilizer (Equiv.Perm (Fin 3)) a := by
  rw [alternatingGroupFinThreeSplittingEquiv_apply]
  exact (isComplement'_alternatingGroup_stabilizer_perm_fin_three a).range_quotientSplitting

/-- The `a`-th quotient splitting lifts the nontrivial coset of `S₃ ⧸ A₃` to
`swap (a + 1) (a + 2)`. -/
theorem alternatingGroupFinThreeSplittingEquiv_mk_swap (a : Fin 3) :
    alternatingGroupFinThreeSplittingEquiv a
      (Equiv.swap (a + 1) (a + 2) : Equiv.Perm (Fin 3) ⧸ alternatingGroup (Fin 3)) =
        Equiv.swap (a + 1) (a + 2) := by
  rw [alternatingGroupFinThreeSplittingEquiv_apply]
  exact (isComplement'_alternatingGroup_stabilizer_perm_fin_three a).quotientSplitting_mk
    ⟨Equiv.swap (a + 1) (a + 2), (mem_stabilizer_perm_fin_three_iff a _).mpr (Or.inr rfl)⟩

/-! ### Sylow `3`- and `2`-subgroups of `S₃` -/

/-- The alternating group `A₃` is a `3`-group. -/
theorem isPGroup_three_alternatingGroup_fin_three :
    IsPGroup 3 (alternatingGroup (Fin 3)) :=
  IsPGroup.of_card (n := 1) (by rw [pow_one, card_alternatingGroup_fin_three])

/-- Each point stabilizer in `S₃` is a `2`-group. -/
theorem isPGroup_two_stabilizer_perm_fin_three (a : Fin 3) :
    IsPGroup 2 (MulAction.stabilizer (Equiv.Perm (Fin 3)) a) :=
  IsPGroup.of_card (n := 1) (by rw [pow_one, card_stabilizer_perm_fin_three])

/-- The alternating subgroup `A₃` packaged as a Sylow `3`-subgroup of `S₃`. -/
noncomputable def alternatingGroupSylowThree : Sylow 3 (Equiv.Perm (Fin 3)) :=
  isPGroup_three_alternatingGroup_fin_three.toSylow <| by
    have hmul := Subgroup.card_mul_index (alternatingGroup (Fin 3))
    simp only [card_alternatingGroup_fin_three, Nat.card_perm, Nat.card_fin,
      Nat.factorial] at hmul
    omega

/-- The underlying subgroup of `alternatingGroupSylowThree` is `A₃`. -/
theorem coe_alternatingGroupSylowThree :
    (alternatingGroupSylowThree : Subgroup (Equiv.Perm (Fin 3))) = alternatingGroup (Fin 3) :=
  (rfl)

/-- Because `A₃` is normal in `S₃`, `S₃` has a unique Sylow `3`-subgroup. -/
instance instSubsingletonSylowThreePermFinThree :
    Subsingleton (Sylow 3 (Equiv.Perm (Fin 3))) :=
  have hnorm : alternatingGroupSylowThree.Normal := by
    rw [coe_alternatingGroupSylowThree]
    infer_instance
  have := Sylow.unique_of_normal alternatingGroupSylowThree hnorm
  inferInstance

/-- Every Sylow `3`-subgroup of `S₃` equals `alternatingGroupSylowThree`. -/
theorem sylow_three_perm_fin_three_eq (P : Sylow 3 (Equiv.Perm (Fin 3))) :
    P = alternatingGroupSylowThree :=
  Subsingleton.elim P alternatingGroupSylowThree

/-- Every Sylow `3`-subgroup of `S₃` has underlying subgroup `A₃`. -/
@[simp]
theorem coe_sylow_three_perm_fin_three (P : Sylow 3 (Equiv.Perm (Fin 3))) :
    (P : Subgroup (Equiv.Perm (Fin 3))) = alternatingGroup (Fin 3) := by
  rw [sylow_three_perm_fin_three_eq P, coe_alternatingGroupSylowThree]

/-- Because `A₃` is itself the unique Sylow `3`-subgroup of `S₃`, its only local complement in a
Sylow `3`-subgroup is `⊥`. -/
theorem isLocalComplement_alternatingGroup_sylow_three_iff
    (P : Sylow 3 (Equiv.Perm (Fin 3))) (K : Subgroup (Equiv.Perm (Fin 3))) :
    (alternatingGroup (Fin 3)).IsLocalComplement K P ↔ K = ⊥ := by
  rw [coe_sylow_three_perm_fin_three, Subgroup.isLocalComplement_self_left]

/-- Each point stabilizer in `S₃` packaged as a Sylow `2`-subgroup. -/
noncomputable def stabilizerSylowTwoPermFinThree (a : Fin 3) : Sylow 2 (Equiv.Perm (Fin 3)) :=
  (isPGroup_two_stabilizer_perm_fin_three a).toSylow <| by
    have hmul := Subgroup.card_mul_index (MulAction.stabilizer (Equiv.Perm (Fin 3)) a)
    simp only [card_stabilizer_perm_fin_three, Nat.card_perm, Nat.card_fin,
      Nat.factorial] at hmul
    omega

/-- The underlying subgroup of `stabilizerSylowTwoPermFinThree a` is `stabilizer a`. -/
@[simp]
theorem coe_stabilizerSylowTwoPermFinThree (a : Fin 3) :
    (stabilizerSylowTwoPermFinThree a : Subgroup (Equiv.Perm (Fin 3))) =
      MulAction.stabilizer (Equiv.Perm (Fin 3)) a :=
  (rfl)

/-- The three points of `Fin 3` parameterize the Sylow `2`-subgroups of `S₃`. -/
noncomputable def stabilizerSylowTwoPermFinThreeEquiv :
    Fin 3 ≃ Sylow 2 (Equiv.Perm (Fin 3)) :=
  Equiv.ofBijective stabilizerSylowTwoPermFinThree
    ⟨fun a b h => stabilizer_perm_fin_three_injective (congrArg Sylow.toSubgroup h),
      fun P => by
        obtain ⟨g, rfl⟩ :=
          MulAction.exists_smul_eq (Equiv.Perm (Fin 3)) (stabilizerSylowTwoPermFinThree 0) P
        refine ⟨g • 0, Sylow.ext ?_⟩
        rw [coe_stabilizerSylowTwoPermFinThree, Sylow.coe_subgroup_smul,
          coe_stabilizerSylowTwoPermFinThree, MulAction.conj_smul_stabilizer]⟩

/-- `stabilizerSylowTwoPermFinThreeEquiv` sends `a` to `stabilizerSylowTwoPermFinThree a`. -/
@[simp]
theorem stabilizerSylowTwoPermFinThreeEquiv_apply (a : Fin 3) :
    stabilizerSylowTwoPermFinThreeEquiv a = stabilizerSylowTwoPermFinThree a :=
  (rfl)

end TauCeti
