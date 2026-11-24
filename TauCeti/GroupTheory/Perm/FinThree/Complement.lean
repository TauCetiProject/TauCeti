/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.GroupTheory.Sylow
public import TauCeti.GroupTheory.Complement.Stabilizer
public import TauCeti.GroupTheory.Perm.FinThree.Alternating
public import TauCeti.GroupTheory.Perm.FinThree.Subgroup
import TauCeti.GroupTheory.GroupAction.Stabilizer.Basic

/-!
# Quotient splittings, crossed projections, and the Sylow `3`-subgroup of `S₃`

Inside `S₃ = Equiv.Perm (Fin 3)`, the alternating subgroup `A₃ = alternatingGroup (Fin 3)` has
prime order `3` and acts regularly on `Fin 3`, with orbit equivalence
`TauCeti.alternatingGroupFinThreeOrbitEquiv` sending `(finRotate 3) ^ (b - a).val` at base point
`a` to `b`.

The three point stabilizers `MulAction.stabilizer (Equiv.Perm (Fin 3)) a` (`a : Fin 3`) are
pairwise distinct, self-normalizing `2`-subgroups of order `2`
(`TauCeti.isPGroup_two_stabilizer_perm_fin_three`) that exhaust the subgroup complements of `A₃` in
`S₃` (`TauCeti.alternatingGroupFinThreeComplementEquiv`). Building on that classification, this file
shows that `Fin 3` also parameterizes:
* the homomorphic splittings of the quotient extension `1 → A₃ → S₃ → S₃ ⧸ A₃ → 1`
  (`TauCeti.alternatingGroupFinThreeSplittingEquiv`), and
* via their induced crossed projections `TauCeti.symmetricThreeCrossedProjection a` with closed
  form `(c_a σ : Equiv.Perm (Fin 3)) = finRotate 3 ^ (σ a - a).val`, all normalized `1`-cocycles
  `S₃ → A₃` (`TauCeti.isMulCocycle₁_and_forall_coe_eq_iff_exists_symmetricThreeCrossedProjection`,
  `TauCeti.symmetricThreeCrossedProjectionEquiv`), transforming equivariantly under conjugation
  (`TauCeti.symmetricThreeCrossedProjection_smul`) and differing pairwise by a unique `A₃`
  coboundary (`TauCeti.forall_symmetricThreeCrossedProjection_eq_mul_smul_div_iff`).

Finally, `A₃` is a `3`-group (`TauCeti.isPGroup_three_alternatingGroup_fin_three`) and packages as
the unique Sylow `3`-subgroup of `S₃` (`TauCeti.alternatingGroupSylowThree`,
`TauCeti.instSubsingletonSylowThreePermFinThree`).

## References

* B. Sambale, *On the converse of Gaschütz' complement theorem*, arXiv:2303.00254.
-/

public section

open scoped IsMulCommutative Pointwise
open groupCohomology

namespace TauCeti

attribute [local instance] Subgroup.conjugationAction

/-! ### Regular action of `A₃` on `Fin 3` -/

/-- Evaluation at a base point `a : Fin 3` identifies `A₃` with `Fin 3`. -/
noncomputable def alternatingGroupFinThreeOrbitEquiv (a : Fin 3) :
    alternatingGroup (Fin 3) ≃ Fin 3 :=
  (isComplement'_alternatingGroup_stabilizer_perm_fin_three a).stabilizerOrbitEquiv

/-- `alternatingGroupFinThreeOrbitEquiv a` is the point-stabilizer orbit equivalence at `a`. -/
theorem alternatingGroupFinThreeOrbitEquiv_def (a : Fin 3) :
    alternatingGroupFinThreeOrbitEquiv a =
      (isComplement'_alternatingGroup_stabilizer_perm_fin_three a).stabilizerOrbitEquiv :=
  (rfl)

/-- `alternatingGroupFinThreeOrbitEquiv a` evaluates an even permutation at `a`. -/
@[simp]
theorem alternatingGroupFinThreeOrbitEquiv_apply (a : Fin 3) (n : alternatingGroup (Fin 3)) :
    alternatingGroupFinThreeOrbitEquiv a n = (n : Equiv.Perm (Fin 3)) a := by
  simpa only [alternatingGroupFinThreeOrbitEquiv_def, Equiv.Perm.smul_def] using
    (isComplement'_alternatingGroup_stabilizer_perm_fin_three a).stabilizerOrbitEquiv_apply n

/-- The unique element of `A₃` carrying `a` to `b` is `finRotate 3 ^ (b - a).val`. -/
@[simp]
theorem coe_alternatingGroupFinThreeOrbitEquiv_symm (a b : Fin 3) :
    ((alternatingGroupFinThreeOrbitEquiv a).symm b : Equiv.Perm (Fin 3)) =
      finRotate 3 ^ (b - a).val := by
  let r : alternatingGroup (Fin 3) :=
    ⟨finRotate 3, Equiv.Perm.finRotate_bit1_mem_alternatingGroup (n := 1)⟩ ^ (b - a).val
  have hr : alternatingGroupFinThreeOrbitEquiv a r = b := by
    rw [alternatingGroupFinThreeOrbitEquiv_apply, Subgroup.coe_pow, Subgroup.coe_mk,
      Equiv.Perm.coe_pow, ← finCycle_eq_finRotate_iterate, finCycle_apply, add_sub_cancel]
  exact congrArg Subtype.val ((Equiv.symm_apply_eq _).mpr hr.symm)

/-- Evaluating an element `n ∈ A₃` at `a` and applying `(alternatingGroupFinThreeOrbitEquiv a).symm`
recovers `n`. -/
@[simp]
theorem alternatingGroupFinThreeOrbitEquiv_symm_coe_apply (a : Fin 3)
    (n : alternatingGroup (Fin 3)) :
    (alternatingGroupFinThreeOrbitEquiv a).symm ((n : Equiv.Perm (Fin 3)) a) = n := by
  apply (alternatingGroupFinThreeOrbitEquiv a).injective
  rw [Equiv.apply_symm_apply, alternatingGroupFinThreeOrbitEquiv_apply]

/-- The inverse of `alternatingGroupFinThreeOrbitEquiv a` maps the base point `a` to `1`. -/
@[simp]
theorem alternatingGroupFinThreeOrbitEquiv_symm_self (a : Fin 3) :
    (alternatingGroupFinThreeOrbitEquiv a).symm a = 1 := by
  rw [alternatingGroupFinThreeOrbitEquiv_def]
  exact (isComplement'_alternatingGroup_stabilizer_perm_fin_three a).stabilizerOrbitEquiv_symm_self

/-! ### Classification of quotient splittings -/

/-- `alternatingGroupFinThreeComplementEquiv a` packages `stabilizer a` with its complement
proof. -/
theorem alternatingGroupFinThreeComplementEquiv_apply (a : Fin 3) :
    alternatingGroupFinThreeComplementEquiv a =
      ⟨MulAction.stabilizer (Equiv.Perm (Fin 3)) a,
        isComplement'_alternatingGroup_stabilizer_perm_fin_three a⟩ :=
  Subtype.ext (coe_alternatingGroupFinThreeComplementEquiv_apply a)

/-- The inverse of `alternatingGroupFinThreeComplementEquiv` recovers the stabilized point. -/
@[simp]
theorem alternatingGroupFinThreeComplementEquiv_symm_stabilizer (a : Fin 3) :
    alternatingGroupFinThreeComplementEquiv.symm
      ⟨MulAction.stabilizer (Equiv.Perm (Fin 3)) a,
        isComplement'_alternatingGroup_stabilizer_perm_fin_three a⟩ = a := by
  apply alternatingGroupFinThreeComplementEquiv.injective
  rw [Equiv.apply_symm_apply, alternatingGroupFinThreeComplementEquiv_apply]

/-- The three points of `Fin 3` parameterize the splittings of
`1 → A₃ → S₃ → S₃ ⧸ A₃ → 1`. -/
noncomputable def alternatingGroupFinThreeSplittingEquiv :
    Fin 3 ≃ (alternatingGroup (Fin 3)).quotientExtension.Splitting :=
  alternatingGroupFinThreeComplementEquiv.trans
    (alternatingGroup (Fin 3)).quotientSplittingEquiv.symm

/-- `alternatingGroupFinThreeSplittingEquiv` composes `alternatingGroupFinThreeComplementEquiv`
with `Subgroup.quotientSplittingEquiv.symm`. -/
theorem alternatingGroupFinThreeSplittingEquiv_def :
    alternatingGroupFinThreeSplittingEquiv =
      alternatingGroupFinThreeComplementEquiv.trans
        (alternatingGroup (Fin 3)).quotientSplittingEquiv.symm :=
  (rfl)

/-- `alternatingGroupFinThreeSplittingEquiv a` is the quotient splitting induced by
`stabilizer a`. -/
@[simp]
theorem alternatingGroupFinThreeSplittingEquiv_apply (a : Fin 3) :
    alternatingGroupFinThreeSplittingEquiv a =
      (isComplement'_alternatingGroup_stabilizer_perm_fin_three a).quotientSplitting := by
  apply DFunLike.ext
  intro q
  rw [alternatingGroupFinThreeSplittingEquiv_def, Equiv.trans_apply,
    alternatingGroupFinThreeComplementEquiv_apply, Subgroup.quotientSplittingEquiv_symm_apply]

/-- `alternatingGroupFinThreeSplittingEquiv.symm` sends a splitting `s` to the stabilized point of
its range complement. -/
theorem alternatingGroupFinThreeSplittingEquiv_symm_apply
    (s : (alternatingGroup (Fin 3)).quotientExtension.Splitting) :
    alternatingGroupFinThreeSplittingEquiv.symm s =
      alternatingGroupFinThreeComplementEquiv.symm
        ((alternatingGroup (Fin 3)).quotientSplittingEquiv s) :=
  (rfl)

/-- The inverse of `alternatingGroupFinThreeSplittingEquiv` maps the quotient splitting of
`stabilizer a` back to `a`. -/
@[simp]
theorem alternatingGroupFinThreeSplittingEquiv_symm_quotientSplitting (a : Fin 3) :
    alternatingGroupFinThreeSplittingEquiv.symm
      (isComplement'_alternatingGroup_stabilizer_perm_fin_three a).quotientSplitting = a := by
  apply alternatingGroupFinThreeSplittingEquiv.injective
  rw [Equiv.apply_symm_apply, alternatingGroupFinThreeSplittingEquiv_apply]

/-- The range of the `a`-th quotient splitting of `S₃` over `A₃` is `stabilizer a`. -/
theorem range_alternatingGroupFinThreeSplittingEquiv (a : Fin 3) :
    (alternatingGroupFinThreeSplittingEquiv a).toMonoidHom.range =
      MulAction.stabilizer (Equiv.Perm (Fin 3)) a := by
  rw [alternatingGroupFinThreeSplittingEquiv_apply]
  exact (isComplement'_alternatingGroup_stabilizer_perm_fin_three a).range_quotientSplitting

/-- `alternatingGroupFinThreeSplittingEquiv a` is a coset section of `S₃ → S₃ ⧸ A₃`. -/
theorem mk_alternatingGroupFinThreeSplittingEquiv (a : Fin 3)
    (u : Equiv.Perm (Fin 3) ⧸ alternatingGroup (Fin 3)) :
    (QuotientGroup.mk (alternatingGroupFinThreeSplittingEquiv a u) :
      Equiv.Perm (Fin 3) ⧸ alternatingGroup (Fin 3)) = u :=
  (alternatingGroupFinThreeSplittingEquiv a).mk_quotientExtension u

/-- The `a`-th quotient splitting lifts the nontrivial coset of `S₃ ⧸ A₃` to
`swap (a + 1) (a + 2)`. -/
theorem alternatingGroupFinThreeSplittingEquiv_mk_swap (a : Fin 3) :
    alternatingGroupFinThreeSplittingEquiv a
      (Equiv.swap (a + 1) (a + 2) : Equiv.Perm (Fin 3) ⧸ alternatingGroup (Fin 3)) =
        Equiv.swap (a + 1) (a + 2) := by
  rw [alternatingGroupFinThreeSplittingEquiv_apply]
  exact (isComplement'_alternatingGroup_stabilizer_perm_fin_three a).quotientSplitting_mk
    ⟨Equiv.swap (a + 1) (a + 2), swap_mem_stabilizer_perm_fin_three a⟩

/-- Every coset representative chosen by `alternatingGroupFinThreeSplittingEquiv a` fixes `a`. -/
theorem alternatingGroupFinThreeSplittingEquiv_mem_stabilizer (a : Fin 3)
    (u : Equiv.Perm (Fin 3) ⧸ alternatingGroup (Fin 3)) :
    alternatingGroupFinThreeSplittingEquiv a u ∈ MulAction.stabilizer (Equiv.Perm (Fin 3)) a := by
  rw [← range_alternatingGroupFinThreeSplittingEquiv a]
  exact ⟨u, rfl⟩

/-! ### The three crossed projections `S₃ → A₃` -/

/-- The normalized crossed projection `S₃ → A₃` along the `a`-stabilizer complement. -/
noncomputable def symmetricThreeCrossedProjection (a : Fin 3) :
    Equiv.Perm (Fin 3) → alternatingGroup (Fin 3) :=
  (isComplement'_alternatingGroup_stabilizer_perm_fin_three a).crossedProjection

/-- `symmetricThreeCrossedProjection a` is the crossed projection of the `a`-stabilizer
complement of `A₃`. -/
theorem symmetricThreeCrossedProjection_def (a : Fin 3) :
    symmetricThreeCrossedProjection a =
      (isComplement'_alternatingGroup_stabilizer_perm_fin_three a).crossedProjection :=
  (rfl)

/-- `symmetricThreeCrossedProjection a` maps `1` to `1`. -/
@[simp]
theorem symmetricThreeCrossedProjection_one (a : Fin 3) :
    symmetricThreeCrossedProjection a 1 = 1 := by
  rw [symmetricThreeCrossedProjection_def]
  exact (isComplement'_alternatingGroup_stabilizer_perm_fin_three a).crossedProjection_one

/-- `symmetricThreeCrossedProjection a σ` agrees with `σ` at `a`. -/
theorem coe_symmetricThreeCrossedProjection_apply_self (a : Fin 3) (σ : Equiv.Perm (Fin 3)) :
    (symmetricThreeCrossedProjection a σ : Equiv.Perm (Fin 3)) a = σ a := by
  rw [symmetricThreeCrossedProjection_def, ← Equiv.Perm.smul_def, ← Equiv.Perm.smul_def σ]
  exact (isComplement'_alternatingGroup_stabilizer_perm_fin_three
    a).coe_crossedProjection_smul_of_stabilizer σ

/-- `symmetricThreeCrossedProjection a σ = n` holds exactly when `n a = σ a`. -/
theorem symmetricThreeCrossedProjection_eq_iff (a : Fin 3) (σ : Equiv.Perm (Fin 3))
    (n : alternatingGroup (Fin 3)) :
    symmetricThreeCrossedProjection a σ = n ↔ (n : Equiv.Perm (Fin 3)) a = σ a := by
  let ha := isComplement'_alternatingGroup_stabilizer_perm_fin_three a
  rw [symmetricThreeCrossedProjection_def, ha.crossedProjection_eq_iff_smul_eq,
    Equiv.Perm.smul_def, Equiv.Perm.smul_def]

/-- `symmetricThreeCrossedProjection a σ` is the inverse orbit element of `σ a` from `a`. -/
theorem symmetricThreeCrossedProjection_eq_orbitEquiv_symm (a : Fin 3) (σ : Equiv.Perm (Fin 3)) :
    symmetricThreeCrossedProjection a σ = (alternatingGroupFinThreeOrbitEquiv a).symm (σ a) := by
  rw [symmetricThreeCrossedProjection_eq_iff, ← alternatingGroupFinThreeOrbitEquiv_apply,
    Equiv.apply_symm_apply]

/-- Closed-form formula for the `a`-crossed projection: `c_a σ = finRotate 3 ^ (σ a - a).val`. -/
@[simp]
theorem coe_symmetricThreeCrossedProjection (a : Fin 3) (σ : Equiv.Perm (Fin 3)) :
    (symmetricThreeCrossedProjection a σ : Equiv.Perm (Fin 3)) =
      finRotate 3 ^ (σ a - a).val := by
  rw [symmetricThreeCrossedProjection_eq_orbitEquiv_symm,
    coe_alternatingGroupFinThreeOrbitEquiv_symm]

/-- `symmetricThreeCrossedProjection a` restricts to the identity on `A₃`. -/
@[simp]
theorem symmetricThreeCrossedProjection_coe (a : Fin 3) (n : alternatingGroup (Fin 3)) :
    symmetricThreeCrossedProjection a n = n := by
  rw [symmetricThreeCrossedProjection_def]
  exact (isComplement'_alternatingGroup_stabilizer_perm_fin_three a).crossedProjection_coe n

/-- `symmetricThreeCrossedProjection a σ = 1` holds if and only if `σ` fixes `a`. -/
@[simp]
theorem symmetricThreeCrossedProjection_eq_one_iff (a : Fin 3) (σ : Equiv.Perm (Fin 3)) :
    symmetricThreeCrossedProjection a σ = 1 ↔
      σ ∈ MulAction.stabilizer (Equiv.Perm (Fin 3)) a := by
  rw [symmetricThreeCrossedProjection_def]
  exact (isComplement'_alternatingGroup_stabilizer_perm_fin_three a).crossedProjection_eq_one_iff σ

/-- `symmetricThreeCrossedProjection a` vanishes on `swap (a + 1) (a + 2)`. -/
@[simp]
theorem symmetricThreeCrossedProjection_swap_add_one_add_two (a : Fin 3) :
    symmetricThreeCrossedProjection a (Equiv.swap (a + 1) (a + 2)) = 1 :=
  (symmetricThreeCrossedProjection_eq_one_iff a _).mpr (swap_mem_stabilizer_perm_fin_three a)

/-- Each `symmetricThreeCrossedProjection a` is a multiplicative `1`-cocycle for ambient
conjugation on `A₃`. -/
theorem isMulCocycle₁_symmetricThreeCrossedProjection (a : Fin 3) :
    IsMulCocycle₁ (symmetricThreeCrossedProjection a) := by
  rw [symmetricThreeCrossedProjection_def]
  exact (isComplement'_alternatingGroup_stabilizer_perm_fin_three a).isMulCocycle₁_crossedProjection

/-- None of the three crossed projections is multiplicative: on `swap (a + 1) (a + 2)` and
`finRotate 3`, `c_a (s * r) ≠ c_a s * c_a r`. -/
theorem symmetricThreeCrossedProjection_swap_mul_finRotate_ne (a : Fin 3) :
    symmetricThreeCrossedProjection a (Equiv.swap (a + 1) (a + 2) * finRotate 3) ≠
      symmetricThreeCrossedProjection a (Equiv.swap (a + 1) (a + 2)) *
        symmetricThreeCrossedProjection a (finRotate 3) := by
  intro heq
  have hval := congrArg (fun x : alternatingGroup (Fin 3) => (x : Equiv.Perm (Fin 3))) heq
  clear heq
  simp only [Subgroup.coe_mul, coe_symmetricThreeCrossedProjection] at hval
  revert hval a
  decide

/-- No group homomorphism `S₃ →* A₃` agrees with any `symmetricThreeCrossedProjection a`. -/
theorem not_exists_monoidHom_eq_symmetricThreeCrossedProjection (a : Fin 3) :
    ¬ ∃ φ : Equiv.Perm (Fin 3) →* alternatingGroup (Fin 3),
      ∀ σ, φ σ = symmetricThreeCrossedProjection a σ := by
  rintro ⟨φ, hφ⟩
  have hrot := hφ (finRotate 3)
  rw [monoidHom_perm_alternatingGroup_fin_three_apply_eq_one, ← Subtype.coe_inj, Subgroup.coe_one,
    coe_symmetricThreeCrossedProjection] at hrot
  clear hφ φ
  revert hrot a
  decide

/-! ### Equivariance, coboundary differences, and classification of normalized crossed maps -/

/-- Conjugation equivariance among the three crossed projections of `S₃`. -/
theorem symmetricThreeCrossedProjection_smul (a : Fin 3) (g σ : Equiv.Perm (Fin 3)) :
    symmetricThreeCrossedProjection (g • a) σ =
      g • symmetricThreeCrossedProjection a (g⁻¹ * σ * g) :=
  (isComplement'_alternatingGroup_stabilizer_perm_fin_three
    a).crossedProjection_eq_smul_of_stabilizer g
    (isComplement'_alternatingGroup_stabilizer_perm_fin_three (g • a)) σ

/-- An element `n ∈ A₃` conjugates `stabilizer a` to `stabilizer b` if and only if `n` is the
unique element of `A₃` carrying `a` to `b`. -/
theorem conj_coe_smul_stabilizer_perm_fin_three_eq_iff (a b : Fin 3)
    (n : alternatingGroup (Fin 3)) :
    MulAut.conj (n : Equiv.Perm (Fin 3)) • MulAction.stabilizer (Equiv.Perm (Fin 3)) a =
      MulAction.stabilizer (Equiv.Perm (Fin 3)) b ↔
        n = (alternatingGroupFinThreeOrbitEquiv a).symm b := by
  rw [MulAction.conj_smul_stabilizer, stabilizer_perm_fin_three_inj, Equiv.Perm.smul_def,
    ← alternatingGroupFinThreeOrbitEquiv_apply, (Equiv.eq_symm_apply _).symm]

/-- Two crossed projections `c_a` and `c_b` differ by the `A₃` coboundary `σ ↦ σ • n / n` if and
only if `n = (alternatingGroupFinThreeOrbitEquiv a).symm b`. -/
theorem forall_symmetricThreeCrossedProjection_eq_mul_smul_div_iff (a b : Fin 3)
    (n : alternatingGroup (Fin 3)) :
    (∀ σ : Equiv.Perm (Fin 3),
      symmetricThreeCrossedProjection b σ =
        symmetricThreeCrossedProjection a σ * (σ • n / n)) ↔
      n = (alternatingGroupFinThreeOrbitEquiv a).symm b := by
  let ha := isComplement'_alternatingGroup_stabilizer_perm_fin_three a
  let hb := isComplement'_alternatingGroup_stabilizer_perm_fin_three b
  simp_rw [symmetricThreeCrossedProjection_def]
  rw [← ha.eq_conj_smul_iff_crossedProjection_eq hb n, eq_comm,
    conj_coe_smul_stabilizer_perm_fin_three_eq_iff]

/-- Every pair of crossed projections `c_a, c_b` on `S₃` differs by `σ ↦ σ • n / n` for a unique
`n ∈ A₃`. -/
theorem existsUnique_forall_symmetricThreeCrossedProjection_eq_mul_smul_div (a b : Fin 3) :
    ∃! n : alternatingGroup (Fin 3), ∀ σ : Equiv.Perm (Fin 3),
      symmetricThreeCrossedProjection b σ =
        symmetricThreeCrossedProjection a σ * (σ • n / n) :=
  ⟨(alternatingGroupFinThreeOrbitEquiv a).symm b,
    (forall_symmetricThreeCrossedProjection_eq_mul_smul_div_iff a b _).mpr rfl,
    fun n hn => (forall_symmetricThreeCrossedProjection_eq_mul_smul_div_iff a b n).mp hn⟩

/-- The three points of `Fin 3` parameterize all normalized additive `1`-cocycles
`S₃ → A₃`. -/
noncomputable def symmetricThreeCrossedProjectionEquiv :
    Fin 3 ≃
      {c : Equiv.Perm (Fin 3) → Additive (alternatingGroup (Fin 3)) //
        IsCocycle₁ c ∧ ∀ n : alternatingGroup (Fin 3), c n = Additive.ofMul n} :=
  alternatingGroupFinThreeComplementEquiv.trans (alternatingGroup (Fin 3)).crossedProjectionEquiv

/-- `symmetricThreeCrossedProjectionEquiv` composes `alternatingGroupFinThreeComplementEquiv` with
`Subgroup.crossedProjectionEquiv`. -/
theorem symmetricThreeCrossedProjectionEquiv_def :
    symmetricThreeCrossedProjectionEquiv =
      alternatingGroupFinThreeComplementEquiv.trans
        (alternatingGroup (Fin 3)).crossedProjectionEquiv :=
  (rfl)

/-- `symmetricThreeCrossedProjectionEquiv a` evaluates at `σ` to
`Additive.ofMul (symmetricThreeCrossedProjection a σ)`. -/
@[simp]
theorem symmetricThreeCrossedProjectionEquiv_apply (a : Fin 3) (σ : Equiv.Perm (Fin 3)) :
    (symmetricThreeCrossedProjectionEquiv a).val σ =
      Additive.ofMul (symmetricThreeCrossedProjection a σ) := by
  rw [symmetricThreeCrossedProjectionEquiv_def, Equiv.trans_apply,
    alternatingGroupFinThreeComplementEquiv_apply, Subgroup.crossedProjectionEquiv_apply,
    ← symmetricThreeCrossedProjection_def]

/-- `symmetricThreeCrossedProjectionEquiv.symm` sends a normalized additive `1`-cocycle `c` to the
stabilized point of its zero-locus complement. -/
theorem symmetricThreeCrossedProjectionEquiv_symm_apply
    (c : {c : Equiv.Perm (Fin 3) → Additive (alternatingGroup (Fin 3)) //
      IsCocycle₁ c ∧ ∀ n : alternatingGroup (Fin 3), c n = Additive.ofMul n}) :
    symmetricThreeCrossedProjectionEquiv.symm c =
      alternatingGroupFinThreeComplementEquiv.symm
        ((alternatingGroup (Fin 3)).crossedProjectionEquiv.symm c) :=
  (rfl)

/-- The inverse of `symmetricThreeCrossedProjectionEquiv` maps the additive form of
`symmetricThreeCrossedProjection a` back to `a`. -/
@[simp]
theorem symmetricThreeCrossedProjectionEquiv_symm_ofMul (a : Fin 3)
    (h : IsCocycle₁ (fun σ => Additive.ofMul (symmetricThreeCrossedProjection a σ)) ∧
      ∀ n : alternatingGroup (Fin 3),
        Additive.ofMul (symmetricThreeCrossedProjection a n) = Additive.ofMul n) :
    symmetricThreeCrossedProjectionEquiv.symm
      ⟨fun σ => Additive.ofMul (symmetricThreeCrossedProjection a σ), h⟩ = a := by
  have heq :
      (⟨fun σ => Additive.ofMul (symmetricThreeCrossedProjection a σ), h⟩ :
        {c : Equiv.Perm (Fin 3) → Additive (alternatingGroup (Fin 3)) //
          IsCocycle₁ c ∧ ∀ n : alternatingGroup (Fin 3), c n = Additive.ofMul n}) =
      symmetricThreeCrossedProjectionEquiv a := by
    ext σ
    rw [symmetricThreeCrossedProjectionEquiv_apply]
  rw [heq, Equiv.symm_apply_apply]

/-- A map `c : S₃ → A₃` is a normalized multiplicative `1`-cocycle if and only if it is one of
the three point-stabilizer crossed projections. -/
theorem isMulCocycle₁_and_forall_coe_eq_iff_exists_symmetricThreeCrossedProjection
    (c : Equiv.Perm (Fin 3) → alternatingGroup (Fin 3)) :
    (IsMulCocycle₁ c ∧ ∀ n : alternatingGroup (Fin 3), c n = n) ↔
      ∃ a : Fin 3, c = symmetricThreeCrossedProjection a := by
  refine ⟨fun ⟨hc, hn⟩ => ?_, ?_⟩
  · let ca : {f : Equiv.Perm (Fin 3) → Additive (alternatingGroup (Fin 3)) //
        IsCocycle₁ f ∧ ∀ n : alternatingGroup (Fin 3), f n = Additive.ofMul n} :=
      ⟨fun σ => Additive.ofMul (c σ), fun g k => congrArg Additive.ofMul (hc g k),
        fun n => congrArg Additive.ofMul (hn n)⟩
    refine ⟨symmetricThreeCrossedProjectionEquiv.symm ca, funext fun σ => ?_⟩
    have h := congrFun
      (congrArg Subtype.val (symmetricThreeCrossedProjectionEquiv.apply_symm_apply ca)) σ
    rw [symmetricThreeCrossedProjectionEquiv_apply] at h
    exact Additive.ofMul.injective h.symm
  · rintro ⟨a, rfl⟩
    exact ⟨isMulCocycle₁_symmetricThreeCrossedProjection a,
      symmetricThreeCrossedProjection_coe a⟩

/-! ### `p`-group properties and the Sylow `3`-subgroup of `S₃` -/

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
    rw [alternatingGroup.index_eq_two]
    decide

/-- The underlying subgroup of `alternatingGroupSylowThree` is `A₃`. -/
@[simp]
theorem coe_alternatingGroupSylowThree :
    (alternatingGroupSylowThree : Subgroup (Equiv.Perm (Fin 3))) = alternatingGroup (Fin 3) :=
  (rfl)

/-- Membership in `alternatingGroupSylowThree` coincides with membership in `A₃`. -/
@[simp]
theorem mem_alternatingGroupSylowThree {g : Equiv.Perm (Fin 3)} :
    g ∈ alternatingGroupSylowThree ↔ g ∈ alternatingGroup (Fin 3) :=
  Iff.rfl

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

end TauCeti
