/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.GroupTheory.Complement.Gaschutz
public import TauCeti.GroupTheory.GroupExtension.Quotient.Cohomology
public import TauCeti.GroupTheory.Perm.FinThree.Complement
import Mathlib.Data.Finite.Perm

/-!
# Crossed projections, crossed transfer, and invariant complements in `S₃`

For the normal alternating subgroup `A₃ = alternatingGroup (Fin 3)` of
`S₃ = Equiv.Perm (Fin 3)`, each point-stabilizer complement
`MulAction.stabilizer (Equiv.Perm (Fin 3)) a` (`a : Fin 3`) induces a normalized crossed
projection
`TauCeti.symmetricThreeCrossedProjection a : Equiv.Perm (Fin 3) → alternatingGroup (Fin 3)`
with closed form `(c_a σ : Equiv.Perm (Fin 3)) = finRotate 3 ^ (σ a - a).val`.

This file establishes the structure of the `S₃` over `A₃` extension across normalized crossed
maps, crossed transfer, quotient cohomology, and subgroup-invariant complements:

* **Crossed projections and principal twists.** Every group homomorphism `S₃ →* A₃` is
  trivial, so none of the three maps `c_a` is a homomorphism; they exhaust all normalized
  `1`-cocycles `S₃ → A₃`
  (`TauCeti.isMulCocycle₁_and_forall_coe_eq_iff_exists_symmetricThreeCrossedProjection`,
  `TauCeti.symmetricThreeCrossedProjectionEquiv`), satisfy conjugation equivariance
  `c_{g • a} σ = g • c_a (g⁻¹ * σ * g)`, and any pair `c_a, c_b` is linked by a unique
  principal crossed map from `A₃`
  (`TauCeti.forall_symmetricThreeCrossedProjection_eq_mul_principal_iff`).
* **Crossed transfer and change-of-transversal normalization.** Along any transversal of `A₃`,
  the untwisted transversal-word product vanishes identically
  (`TauCeti.prod_lWord_alternatingGroup_fin_three`) because it computes the classical transfer
  `S₃ →* A₃`. With the conjugation twist along the canonical splitting transversal `t_a`, the
  crossed transfer of the local projection on `A₃` equals `(c_a ·) ^ 2`
  (`TauCeti.crossedTransfer_leftProjection_alternatingGroup_fin_three`), whose `e = 2` power
  recovers `c_a` and yields `gaschutzComplement = stabilizer a`. Conjugating `stabilizer a` by
  the unnormalized change-of-transversal element `TauCeti.symmetricThreeChangeTransversal a b`
  gives `stabilizer (-(a + b))`
  (`TauCeti.conj_symmetricThreeChangeTransversal_smul_stabilizer`), which for `a ≠ b` is the
  third complement distinct from `stabilizer b`
  (`TauCeti.gaschutzComplement_ne_conj_symmetricThreeChangeTransversal_smul`), showing why the
  inverse-exponent power in `Subgroup.IsLocalComplement.gaschutzComplement_changeTransversal`
  cannot be omitted.
* **Quotient action, cohomology, and invariant complements.** The nontrivial coset in
  `S₃ ⧸ A₃` acts on `A₃` by inversion
  (`TauCeti.quotientConjugationAction_alternatingGroup_smul_of_ne_one`), the quotient
  extension class vanishes
  (`TauCeti.cohomologyClass_factorSet_alternatingGroup_fin_three_eq_zero`),
  and although `gcd(|stabilizer a|, |S₃|) = 2`, `stabilizer a` is the unique
  `stabilizer a`-normalized complement of `A₃` in `S₃`
  (`TauCeti.isComplement'_alternatingGroup_and_stabilizer_le_normalizer_iff`), while swapping
  the other two complements `stabilizer (a + 1)` and `stabilizer (a + 2)`.

## References

* W. Gaschütz, *Zur Erweiterungstheorie der endlichen Gruppen*, J. reine angew. Math. 190
  (1952), 93–107.
* B. Sambale, *On the converse of Gaschütz' complement theorem*, arXiv:2303.00254.
-/

public section

open scoped IsMulCommutative Pointwise
open groupCohomology

namespace TauCeti

attribute [local instance] Subgroup.conjugationAction Subgroup.fintypeQuotientOfFiniteIndex

/-! ### Triviality of homomorphisms `S₃ →* A₃` -/

/-- Because `[S₃, S₃] = A₃` and `[S₃ : A₃] = 2` is coprime to `|A₃| = 3`, the trivial
homomorphism is the only group homomorphism `S₃ →* A₃`. -/
instance instSubsingletonMonoidHomPermAlternatingFinThree :
    Subsingleton (Equiv.Perm (Fin 3) →* alternatingGroup (Fin 3)) where
  allEq φ ψ := by
    have htriv : ∀ χ : Equiv.Perm (Fin 3) →* alternatingGroup (Fin 3),
        ∀ g : Equiv.Perm (Fin 3), χ g = 1 := by
      intro χ g
      have hker : alternatingGroup (Fin 3) ≤ χ.ker := by
        intro x hx
        apply Group.Abelianization.commutator_le_ker χ
        rwa [commutator_perm_fin_three_eq_alternatingGroup]
      have hsq : χ g ^ 2 = 1 := by
        rw [← map_pow]
        exact hker (Equiv.Perm.mem_alternatingGroup.mpr (by rw [map_pow, Int.units_sq]))
      have hcube : χ g ^ 3 = 1 := by
        simpa only [card_alternatingGroup_fin_three] using pow_card_eq_one' (x := χ g)
      calc χ g = χ g ^ 3 * (χ g ^ 2)⁻¹ := by group
        _ = 1 := by rw [hcube, hsq, inv_one, mul_one]
    ext g
    rw [htriv φ g, htriv ψ g]

/-- Every group homomorphism `S₃ →* A₃` sends every permutation to `1`. -/
@[simp]
theorem monoidHom_alternatingGroup_fin_three_apply
    (φ : Equiv.Perm (Fin 3) →* alternatingGroup (Fin 3)) (g : Equiv.Perm (Fin 3)) :
    φ g = 1 :=
  DFunLike.congr_fun (Subsingleton.elim φ 1) g

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
  exact
    (isComplement'_alternatingGroup_stabilizer_perm_fin_three a).crossedProjection_stabilizer_smul σ

/-- `symmetricThreeCrossedProjection a σ = n` holds exactly when `n a = σ a`. -/
theorem symmetricThreeCrossedProjection_eq_iff (a : Fin 3) (σ : Equiv.Perm (Fin 3))
    (n : alternatingGroup (Fin 3)) :
    symmetricThreeCrossedProjection a σ = n ↔ (n : Equiv.Perm (Fin 3)) a = σ a := by
  let ha := isComplement'_alternatingGroup_stabilizer_perm_fin_three a
  rw [symmetricThreeCrossedProjection_def, ha.crossedProjection_stabilizer_eq_iff,
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

/-- `symmetricThreeCrossedProjection a` vanishes on the transposition fixing `a`. -/
@[simp]
theorem symmetricThreeCrossedProjection_swap_stabilizer (a : Fin 3) :
    symmetricThreeCrossedProjection a (Equiv.swap (a + 1) (a + 2)) = 1 :=
  (symmetricThreeCrossedProjection_eq_one_iff a _).mpr
    ((mem_stabilizer_perm_fin_three_iff a _).mpr (Or.inr rfl))

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
  rw [monoidHom_alternatingGroup_fin_three_apply, ← Subtype.coe_inj, Subgroup.coe_one,
    coe_symmetricThreeCrossedProjection] at hrot
  clear hφ φ
  revert hrot a
  decide

/-! ### Equivariance, principal twists, and classification of normalized crossed maps -/

/-- Conjugation equivariance among the three crossed projections of `S₃`. -/
theorem symmetricThreeCrossedProjection_conj (a : Fin 3) (g σ : Equiv.Perm (Fin 3)) :
    symmetricThreeCrossedProjection (g • a) σ =
      g • symmetricThreeCrossedProjection a (g⁻¹ * σ * g) := by
  let ha := isComplement'_alternatingGroup_stabilizer_perm_fin_three a
  let hga := isComplement'_alternatingGroup_stabilizer_perm_fin_three (g • a)
  rw [symmetricThreeCrossedProjection_def, symmetricThreeCrossedProjection_def,
    ← ha.crossedProjection_conj_smul, eq_comm, (ha.conj_smul g).crossedProjection_eq_iff,
    MulAction.conj_smul_stabilizer, ← hga.crossedProjection_eq_iff]

/-- An element `n ∈ A₃` conjugates `stabilizer a` to `stabilizer b` if and only if `n` is the
unique element of `A₃` carrying `a` to `b`. -/
theorem conj_coe_smul_stabilizer_perm_fin_three_eq_iff (a b : Fin 3)
    (n : alternatingGroup (Fin 3)) :
    MulAut.conj (n : Equiv.Perm (Fin 3)) • MulAction.stabilizer (Equiv.Perm (Fin 3)) a =
      MulAction.stabilizer (Equiv.Perm (Fin 3)) b ↔
        n = (alternatingGroupFinThreeOrbitEquiv a).symm b := by
  rw [MulAction.conj_smul_stabilizer, stabilizer_perm_fin_three_inj, Equiv.Perm.smul_def,
    ← alternatingGroupFinThreeOrbitEquiv_apply, (Equiv.eq_symm_apply _).symm]

/-- Two crossed projections `c_a` and `c_b` differ by the principal crossed map of `n ∈ A₃` if
and only if `n = (alternatingGroupFinThreeOrbitEquiv a).symm b`. -/
theorem forall_symmetricThreeCrossedProjection_eq_mul_principal_iff (a b : Fin 3)
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

/-- Every pair of crossed projections `c_a, c_b` on `S₃` differs by a unique principal crossed
map from `A₃`. -/
theorem existsUnique_principal_twist_symmetricThreeCrossedProjection (a b : Fin 3) :
    ∃! n : alternatingGroup (Fin 3), ∀ σ : Equiv.Perm (Fin 3),
      symmetricThreeCrossedProjection b σ =
        symmetricThreeCrossedProjection a σ * (σ • n / n) :=
  ⟨(alternatingGroupFinThreeOrbitEquiv a).symm b,
    (forall_symmetricThreeCrossedProjection_eq_mul_principal_iff a b _).mpr rfl,
    fun n hn => (forall_symmetricThreeCrossedProjection_eq_mul_principal_iff a b n).mp hn⟩

/-- The three points of `Fin 3` parameterize all normalized additive `1`-cocycles
`S₃ → A₃`. -/
noncomputable def symmetricThreeCrossedProjectionEquiv :
    Fin 3 ≃
      {c : Equiv.Perm (Fin 3) → Additive (alternatingGroup (Fin 3)) //
        IsCocycle₁ c ∧ ∀ n : alternatingGroup (Fin 3), c n = Additive.ofMul n} :=
  alternatingGroupFinThreeComplementEquiv.trans (alternatingGroup (Fin 3)).crossedProjectionEquiv

/-- `symmetricThreeCrossedProjectionEquiv a` evaluates at `σ` to
`Additive.ofMul (symmetricThreeCrossedProjection a σ)`. -/
@[simp]
theorem symmetricThreeCrossedProjectionEquiv_apply (a : Fin 3) (σ : Equiv.Perm (Fin 3)) :
    (symmetricThreeCrossedProjectionEquiv a).val σ =
      Additive.ofMul (symmetricThreeCrossedProjection a σ) := by
  rw [symmetricThreeCrossedProjectionEquiv, Equiv.trans_apply,
    alternatingGroupFinThreeComplementEquiv_apply, Subgroup.crossedProjectionEquiv_apply,
    ← symmetricThreeCrossedProjection_def]

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

/-! ### Crossed transfer, Gaschütz complements, and change of transversal -/

/-- The index `[S₃ : A₃] = 2` is coprime to `|A₃| = 3`. -/
theorem coprime_index_card_alternatingGroup_fin_three :
    Nat.Coprime (alternatingGroup (Fin 3)).index (Nat.card (alternatingGroup (Fin 3))) := by
  rw [alternatingGroup.index_eq_two, card_alternatingGroup_fin_three]
  decide

/-- The modular inverse exponent `([S₃ : A₃] : ZMod |A₃|)⁻¹` appearing in Gaschütz's
normalization equals `2`. -/
theorem inv_index_alternatingGroup_fin_three :
    (((alternatingGroup (Fin 3)).index : ZMod (Nat.card (alternatingGroup (Fin 3))))⁻¹).val =
      2 := by
  rw [alternatingGroup.index_eq_two, card_alternatingGroup_fin_three, Nat.cast_ofNat,
    ZMod.inv_eq_of_mul_eq_one 3 2 2 (by decide)]
  decide

/-- The canonical transversal `S₃ ⧸ A₃ → S₃` picking `{1, swap (a + 1) (a + 2)}`. -/
noncomputable def symmetricThreeTransversal (a : Fin 3) :
    Equiv.Perm (Fin 3) ⧸ alternatingGroup (Fin 3) → Equiv.Perm (Fin 3) :=
  alternatingGroupFinThreeSplittingEquiv a

/-- `symmetricThreeTransversal a` is the underlying function of
`alternatingGroupFinThreeSplittingEquiv a`. -/
theorem symmetricThreeTransversal_def (a : Fin 3) :
    symmetricThreeTransversal a = ⇑(alternatingGroupFinThreeSplittingEquiv a) :=
  (rfl)

/-- `symmetricThreeTransversal a` is a coset section of `S₃ → S₃ ⧸ A₃`. -/
theorem symmetricThreeTransversal_mk (a : Fin 3)
    (u : Equiv.Perm (Fin 3) ⧸ alternatingGroup (Fin 3)) :
    (QuotientGroup.mk (symmetricThreeTransversal a u) :
      Equiv.Perm (Fin 3) ⧸ alternatingGroup (Fin 3)) = u := by
  simpa only [symmetricThreeTransversal_def, Subgroup.quotientExtension_rightHom,
    QuotientGroup.mk'_apply] using
    (alternatingGroupFinThreeSplittingEquiv a).rightHom_splitting u

/-- `symmetricThreeTransversal a` sends the trivial coset to `1`. -/
@[simp]
theorem symmetricThreeTransversal_one (a : Fin 3) :
    symmetricThreeTransversal a 1 = 1 := by
  rw [symmetricThreeTransversal_def]
  exact map_one (alternatingGroupFinThreeSplittingEquiv a)

/-- `symmetricThreeTransversal a` sends the nontrivial coset to `swap (a + 1) (a + 2)`. -/
@[simp]
theorem symmetricThreeTransversal_mk_swap (a : Fin 3) :
    symmetricThreeTransversal a
      (Equiv.swap (a + 1) (a + 2) : Equiv.Perm (Fin 3) ⧸ alternatingGroup (Fin 3)) =
        Equiv.swap (a + 1) (a + 2) := by
  rw [symmetricThreeTransversal_def]
  exact alternatingGroupFinThreeSplittingEquiv_mk_swap a

/-- Every representative chosen by `symmetricThreeTransversal a` fixes `a`. -/
theorem symmetricThreeTransversal_mem_stabilizer (a : Fin 3)
    (u : Equiv.Perm (Fin 3) ⧸ alternatingGroup (Fin 3)) :
    symmetricThreeTransversal a u ∈ MulAction.stabilizer (Equiv.Perm (Fin 3)) a := by
  rw [symmetricThreeTransversal_def, ← range_alternatingGroupFinThreeSplittingEquiv a]
  exact ⟨u, rfl⟩

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
  rw [monoidHom_alternatingGroup_fin_three_apply] at htr
  simpa only [MonoidHom.id_apply] using htr.symm

/-- The trivial subgroup `⊥` is a local complement of `A₃` inside `A₃`. -/
theorem isLocalComplement_bot_alternatingGroup_fin_three :
    (alternatingGroup (Fin 3)).IsLocalComplement ⊥ (alternatingGroup (Fin 3)) :=
  Subgroup.isLocalComplement_self_left.mpr rfl

/-- The left projection of the local complement `⊥` of `A₃` in `A₃` is the identity. -/
@[simp]
theorem leftProjection_isLocalComplement_bot_alternatingGroup_fin_three
    (n : alternatingGroup (Fin 3)) :
    isLocalComplement_bot_alternatingGroup_fin_three.leftProjection n = n :=
  isLocalComplement_bot_alternatingGroup_fin_three.leftProjection_left n

/-- Along `symmetricThreeTransversal a`, the unnormalized crossed transfer of the local projection
on `A₃` equals the square `(c_a ·) ^ 2` of `symmetricThreeCrossedProjection a`. -/
theorem crossedTransfer_leftProjection_alternatingGroup_fin_three (a : Fin 3)
    (g : Equiv.Perm (Fin 3)) :
    crossedTransfer (alternatingGroup (Fin 3)) (symmetricThreeTransversal a)
      (symmetricThreeTransversal_mk a)
      isLocalComplement_bot_alternatingGroup_fin_three.leftProjection g =
        symmetricThreeCrossedProjection a g ^ 2 := by
  have hres : isLocalComplement_bot_alternatingGroup_fin_three.leftProjection =
      fun x : alternatingGroup (Fin 3) => symmetricThreeCrossedProjection a x := by
    ext x
    rw [leftProjection_isLocalComplement_bot_alternatingGroup_fin_three,
      symmetricThreeCrossedProjection_coe]
  have hprod : (∏ u : Equiv.Perm (Fin 3) ⧸ alternatingGroup (Fin 3),
      symmetricThreeCrossedProjection a (symmetricThreeTransversal a u)) = 1 :=
    Finset.prod_eq_one fun u _ =>
      (symmetricThreeCrossedProjection_eq_one_iff a _).mpr
        (symmetricThreeTransversal_mem_stabilizer a u)
  rw [hres, crossedTransfer_restrict (alternatingGroup (Fin 3)) (symmetricThreeTransversal a)
    (symmetricThreeTransversal_mk a) (isMulCocycle₁_symmetricThreeCrossedProjection a) g,
    alternatingGroup.index_eq_two, hprod, smul_one, div_one, mul_one]

/-- Normalizing the crossed transfer by the inverse exponent `e = 2` recovers
`symmetricThreeCrossedProjection a`. -/
theorem crossedTransfer_leftProjection_pow_inv_index_alternatingGroup_fin_three (a : Fin 3)
    (g : Equiv.Perm (Fin 3)) :
    crossedTransfer (alternatingGroup (Fin 3)) (symmetricThreeTransversal a)
      (symmetricThreeTransversal_mk a)
      isLocalComplement_bot_alternatingGroup_fin_three.leftProjection g ^
        (((alternatingGroup (Fin 3)).index :
          ZMod (Nat.card (alternatingGroup (Fin 3))))⁻¹).val =
      symmetricThreeCrossedProjection a g := by
  rw [crossedTransfer_leftProjection_alternatingGroup_fin_three,
    inv_index_alternatingGroup_fin_three, ← pow_mul]
  have hcube : symmetricThreeCrossedProjection a g ^ 3 = 1 := by
    simpa only [card_alternatingGroup_fin_three] using
      pow_card_eq_one' (x := symmetricThreeCrossedProjection a g)
  calc symmetricThreeCrossedProjection a g ^ (2 * 2)
    _ = symmetricThreeCrossedProjection a g ^ 3 * symmetricThreeCrossedProjection a g := by group
    _ = symmetricThreeCrossedProjection a g := by rw [hcube, one_mul]

/-- The Gaschütz complement of `⊥` in `A₃` along `symmetricThreeTransversal a` is
`stabilizer a`. -/
@[simp]
theorem gaschutzComplement_alternatingGroup_fin_three (a : Fin 3) :
    isLocalComplement_bot_alternatingGroup_fin_three.gaschutzComplement
      (symmetricThreeTransversal a) (symmetricThreeTransversal_mk a) =
        MulAction.stabilizer (Equiv.Perm (Fin 3)) a := by
  ext g
  rw [Subgroup.IsLocalComplement.mem_gaschutzComplement_iff_pow_eq_one,
    crossedTransfer_leftProjection_pow_inv_index_alternatingGroup_fin_three,
    symmetricThreeCrossedProjection_eq_one_iff]

/-- Any transposition `swap (a + 1) (a + 2)` inverts every element `m ∈ A₃` by conjugation, so
in the order-`3` group `A₃` the principal value `(swap • m) / m` equals `m` itself. -/
private theorem swap_smul_div_self_alternatingGroup_fin_three (a : Fin 3)
    (m : alternatingGroup (Fin 3)) :
    (Equiv.swap (a + 1) (a + 2) : Equiv.Perm (Fin 3)) • m / m = m := by
  apply Subtype.ext
  rcases m with ⟨m, hm⟩
  simp only [Subgroup.coe_div, Subgroup.coe_conjugationAction_smul]
  rw [Equiv.Perm.mem_alternatingGroup] at hm
  revert hm m a
  decide

/-- The unnormalized change-of-transversal element in `A₃` comparing
`symmetricThreeTransversal a` and `symmetricThreeTransversal b`. -/
noncomputable def symmetricThreeChangeTransversal (a b : Fin 3) : alternatingGroup (Fin 3) :=
  ∏ v : Equiv.Perm (Fin 3) ⧸ alternatingGroup (Fin 3),
    symmetricThreeTransversal a v •
      isLocalComplement_bot_alternatingGroup_fin_three.leftProjection
        ⟨transversalDiff (alternatingGroup (Fin 3))
          (symmetricThreeTransversal a) (symmetricThreeTransversal b) v,
          transversalDiff_mem (alternatingGroup (Fin 3))
            (symmetricThreeTransversal a) (symmetricThreeTransversal b)
            (symmetricThreeTransversal_mk a) (symmetricThreeTransversal_mk b) v⟩

/-- Unfolding formula for `symmetricThreeChangeTransversal` as the twisted product of transversal
differences across `S₃ ⧸ A₃`. -/
theorem symmetricThreeChangeTransversal_def (a b : Fin 3) :
    symmetricThreeChangeTransversal a b =
      ∏ v : Equiv.Perm (Fin 3) ⧸ alternatingGroup (Fin 3),
        symmetricThreeTransversal a v •
          isLocalComplement_bot_alternatingGroup_fin_three.leftProjection
            ⟨transversalDiff (alternatingGroup (Fin 3))
              (symmetricThreeTransversal a) (symmetricThreeTransversal b) v,
              transversalDiff_mem (alternatingGroup (Fin 3))
                (symmetricThreeTransversal a) (symmetricThreeTransversal b)
                (symmetricThreeTransversal_mk a) (symmetricThreeTransversal_mk b) v⟩ :=
  (rfl)

/-- Closed form for `symmetricThreeChangeTransversal a b`: it equals the square (hence inverse)
of `(alternatingGroupFinThreeOrbitEquiv a).symm b`. -/
theorem symmetricThreeChangeTransversal_eq_orbitEquiv_symm_sq (a b : Fin 3) :
    symmetricThreeChangeTransversal a b =
      ((alternatingGroupFinThreeOrbitEquiv a).symm b) ^ 2 := by
  let r := (alternatingGroupFinThreeOrbitEquiv a).symm b
  let s := Equiv.swap (a + 1) (a + 2)
  have hchg := crossedTransfer_changeTransversal (alternatingGroup (Fin 3))
    (symmetricThreeTransversal a) (symmetricThreeTransversal_mk a)
    (symmetricThreeTransversal b) (symmetricThreeTransversal_mk b)
    isLocalComplement_bot_alternatingGroup_fin_three.isMulCocycle₁_leftProjection s
  rw [← symmetricThreeChangeTransversal_def,
    crossedTransfer_leftProjection_alternatingGroup_fin_three,
    crossedTransfer_leftProjection_alternatingGroup_fin_three,
    symmetricThreeCrossedProjection_swap_stabilizer, one_pow, one_mul,
    swap_smul_div_self_alternatingGroup_fin_three] at hchg
  have hprinc :=
    (forall_symmetricThreeCrossedProjection_eq_mul_principal_iff a b r).mpr rfl s
  rw [symmetricThreeCrossedProjection_swap_stabilizer, one_mul,
    swap_smul_div_self_alternatingGroup_fin_three] at hprinc
  exact hchg.symm.trans (by rw [hprinc])

/-- Conjugating `stabilizer a` by the unnormalized change-of-transversal element
`symmetricThreeChangeTransversal a b` gives `stabilizer (-(a + b))` (which equals `stabilizer a`
when `a = b`, and the third complement distinct from both `stabilizer a` and `stabilizer b` when
`a ≠ b`). -/
theorem conj_symmetricThreeChangeTransversal_smul_stabilizer (a b : Fin 3) :
    MulAut.conj (symmetricThreeChangeTransversal a b : Equiv.Perm (Fin 3)) •
      MulAction.stabilizer (Equiv.Perm (Fin 3)) a =
        MulAction.stabilizer (Equiv.Perm (Fin 3)) (-(a + b)) := by
  rw [symmetricThreeChangeTransversal_eq_orbitEquiv_symm_sq, MulAction.conj_smul_stabilizer,
    stabilizer_perm_fin_three_inj, Subgroup.coe_pow,
    coe_alternatingGroupFinThreeOrbitEquiv_symm, Equiv.Perm.smul_def]
  revert b a
  decide

/-- For any two distinct points `a ≠ b`, the Gaschütz complements along
`symmetricThreeTransversal a` and `symmetricThreeTransversal b` are *not* conjugate by the
unnormalized change-of-transversal element `symmetricThreeChangeTransversal a b` itself (only by
its square). -/
theorem gaschutzComplement_ne_conj_symmetricThreeChangeTransversal_smul {a b : Fin 3}
    (hab : a ≠ b) :
    isLocalComplement_bot_alternatingGroup_fin_three.gaschutzComplement
      (symmetricThreeTransversal b) (symmetricThreeTransversal_mk b) ≠
    MulAut.conj (symmetricThreeChangeTransversal a b : Equiv.Perm (Fin 3)) •
      isLocalComplement_bot_alternatingGroup_fin_three.gaschutzComplement
        (symmetricThreeTransversal a) (symmetricThreeTransversal_mk a) := by
  rw [gaschutzComplement_alternatingGroup_fin_three,
    gaschutzComplement_alternatingGroup_fin_three,
    conj_symmetricThreeChangeTransversal_smul_stabilizer, ne_eq, stabilizer_perm_fin_three_inj]
  revert hab b a
  decide

/-! ### Quotient conjugation action and vanishing of the extension class -/

section QuotientCohomology

attribute [local instance] Subgroup.quotientConjugationAction

/-- Under `Subgroup.quotientConjugationAction`, the nontrivial coset of `S₃ ⧸ A₃` acts on `A₃`
by inversion, independently of the chosen representative. -/
theorem quotientConjugationAction_alternatingGroup_smul_of_ne_one
    {q : Equiv.Perm (Fin 3) ⧸ alternatingGroup (Fin 3)} (hq : q ≠ 1)
    (m : alternatingGroup (Fin 3)) :
    q • m = m⁻¹ := by
  obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective q
  have hg : g ∉ alternatingGroup (Fin 3) := by
    rwa [← QuotientGroup.eq_one_iff]
  clear hq
  rw [Subgroup.quotientConjugationAction_mk_smul]
  apply Subtype.ext
  rcases m with ⟨m, hm⟩
  simp only [MulAut.conjNormal_apply, Subgroup.coe_inv]
  rw [Equiv.Perm.mem_alternatingGroup] at hg hm
  revert hg hm m g
  decide

/-- For any normalized section of `1 → A₃ → S₃ → S₃ ⧸ A₃ → 1`, the factor-set class in
`H²(S₃ ⧸ A₃, A₃)` vanishes. -/
theorem cohomologyClass_factorSet_alternatingGroup_fin_three_eq_zero
    (σ : (alternatingGroup (Fin 3)).quotientExtension.Section) (hσ : σ 1 = 1) :
    (GroupExtension.factorSet σ hσ
      (alternatingGroup (Fin 3)).quotientExtension_inducesAction).cohomologyClass = 0 :=
  ((alternatingGroup (Fin 3)).exists_complement_iff_cohomologyClass_eq_zero σ hσ).mp
    ⟨_, isComplement'_alternatingGroup_stabilizer_perm_fin_three 0⟩

end QuotientCohomology

/-! ### Subgroup-invariant complements in `S₃` beyond coprime order -/

/-- The order of a point stabilizer (`2`) is not coprime to the order of `S₃` (`6`), placing the
`stabilizer a`-action on `S₃` outside coprime-action complement theorems. -/
theorem gcd_card_stabilizer_card_perm_fin_three (a : Fin 3) :
    Nat.gcd (Nat.card (MulAction.stabilizer (Equiv.Perm (Fin 3)) a))
      (Nat.card (Equiv.Perm (Fin 3))) = 2 := by
  rw [card_stabilizer_perm_fin_three, Nat.card_perm, Nat.card_fin]
  decide

/-- Among all subgroups of `S₃`, `stabilizer a` is the unique `stabilizer a`-normalized complement
of `A₃`. -/
@[simp]
theorem isComplement'_alternatingGroup_and_stabilizer_le_normalizer_iff (a : Fin 3)
    (D : Subgroup (Equiv.Perm (Fin 3))) :
    ((alternatingGroup (Fin 3)).IsComplement' D ∧
      MulAction.stabilizer (Equiv.Perm (Fin 3)) a ≤
        Subgroup.normalizer (D : Set (Equiv.Perm (Fin 3)))) ↔
      D = MulAction.stabilizer (Equiv.Perm (Fin 3)) a := by
  refine ⟨fun ⟨hD, hnorm⟩ => ?_, ?_⟩
  · obtain ⟨b, rfl⟩ := (isComplement'_alternatingGroup_fin_three_iff D).mp hD
    rw [normalizer_stabilizer_perm_fin_three] at hnorm
    exact (Subgroup.eq_of_le_of_card_ge hnorm
      (by rw [card_stabilizer_perm_fin_three, card_stabilizer_perm_fin_three])).symm
  · rintro rfl
    exact ⟨isComplement'_alternatingGroup_stabilizer_perm_fin_three a, Subgroup.le_normalizer⟩

/-- Existence and uniqueness of a `stabilizer a`-normalized complement of `A₃` in `S₃`. -/
theorem existsUnique_invariant_complement_alternatingGroup_fin_three (a : Fin 3) :
    ∃! D : Subgroup (Equiv.Perm (Fin 3)),
      (alternatingGroup (Fin 3)).IsComplement' D ∧
        MulAction.stabilizer (Equiv.Perm (Fin 3)) a ≤
          Subgroup.normalizer (D : Set (Equiv.Perm (Fin 3))) :=
  ⟨MulAction.stabilizer (Equiv.Perm (Fin 3)) a,
    (isComplement'_alternatingGroup_and_stabilizer_le_normalizer_iff a _).mpr rfl,
    fun D hD => (isComplement'_alternatingGroup_and_stabilizer_le_normalizer_iff a D).mp hD⟩

/-- Conjugating by the generator `swap (a + 1) (a + 2)` of `stabilizer a` swaps the two other
complements `stabilizer (a + 1)` and `stabilizer (a + 2)`. -/
theorem conj_swap_smul_stabilizer_add_one (a : Fin 3) :
    MulAut.conj (Equiv.swap (a + 1) (a + 2)) •
      MulAction.stabilizer (Equiv.Perm (Fin 3)) (a + 1) =
        MulAction.stabilizer (Equiv.Perm (Fin 3)) (a + 2) := by
  rw [MulAction.conj_smul_stabilizer, Equiv.Perm.smul_def, Equiv.swap_apply_left]

end TauCeti
