/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Polynomial.Laurent
public import Mathlib.RingTheory.Localization.Away.Basic
public import Mathlib.RingTheory.TensorProduct.Basic
public import TauCeti.RingTheory.MvPolynomial.FlagMinor.StandardMonomial
public import TauCeti.RingTheory.MvPolynomial.Subalgebra.WeightFiltration
public import TauCeti.Algebra.Group.Submonoid.NSMulSaturation
import Mathlib.RingTheory.TensorProduct.Maps

/-!
# Diagonal SAGBI basis, Gelfand-Tsetlin initial algebra, and weight-Rees degeneration

For the generic `n × n` matrix `(z_(r,c))` with variables ordered row by row along `toLex` and
equipped with the lexicographic monomial order `MonomialOrder.lex`, this file proves that the
`2 ^ n - 1` nonempty flag minors (including the full determinant `flagMinor R univ`) form a finite
monic SAGBI basis of the flag-minor subalgebra over **every** commutative ring `R`, identifies its
initial algebra with the semigroup algebra of nonnegative Gelfand-Tsetlin patterns, proves the
saturation and finite generation of the leading-exponent monoid, and constructs the flat positive
weight-Rees degeneration over any field.

Note that it is the **initial** algebra
`lex.initialAlgebra ((flagMinorAlgebra n R).map (rename toLex))` that is isomorphic to the affine
semigroup algebra `AddMonoidAlgebra R (AddSubmonoid.nonneg (GTPattern n))`; the flag-minor algebra
`flagMinorAlgebra n R` itself is not thereby toric, and instead admits a flat one-parameter Rees
degeneration to this toric initial algebra.

## Main definitions

* `TauCeti.leadingExponentsFlagMinorEquiv`: over `[CommRing R] [NoZeroDivisors R] [Nontrivial R]`,
  the additive isomorphism `lex.leadingExponents ((flagMinorAlgebra n R).map (rename toLex)) ≃+
  AddSubmonoid.nonneg (GTPattern n)`.
* `TauCeti.initialAlgebraFlagMinorEquiv`: over **every** `[CommRing R]`, the `R`-algebra isomorphism
  `AddMonoidAlgebra R (AddSubmonoid.nonneg (GTPattern n)) ≃ₐ[R]
  lex.initialAlgebra ((flagMinorAlgebra n R).map (rename toLex))`.

## Main results

* `TauCeti.GTPattern.nsmulSaturated_nonneg` and
  `TauCeti.GTPattern.nsmulSaturated_closure_range_flagDiagonalExponent`: saturation of the
  nonnegative Gelfand-Tsetlin patterns and of the diagonal-exponent monoid inside
  `Fin n ×ₗ Fin n →₀ ℕ`.
* `TauCeti.card_nonempty_finset_fin`, `TauCeti.card_image_nonempty_flagMinor`, and
  `TauCeti.fg_flagMinorAlgebra`: the `2 ^ n - 1` nonempty row-subset minors generate
  `flagMinorAlgebra n R`.
* `TauCeti.isSAGBIBasis_image_nonempty_rename_toLex_flagMinor` and
  `TauCeti.isSAGBIBasis_range_rename_toLex_flagMinor`: over **every** commutative ring `R`, the
  nonempty flag minors (and all `2 ^ n` flag minors) form a `lex`-SAGBI basis of
  `(flagMinorAlgebra n R).map (rename toLex)`.
* `TauCeti.mem_initialAlgebra_rename_toLex_flagMinorAlgebra_iff`: over **every** commutative ring
  `R`, a polynomial lies in `lex.initialAlgebra ((flagMinorAlgebra n R).map (rename toLex))` if and
  only if its support lies in `AddSubmonoid.closure (Set.range flagDiagonalExponent)`.
* `TauCeti.coe_initialAlgebraFlagMinorEquiv_single_one_eq_leadingTerm`: compatibility of the
  initial-algebra isomorphism with the standard-monomial tableau bijection
  `GTPattern.nonnegEquivBoundedSSYT`.
* `TauCeti.leadingExponents_rename_toLex_flagMinorAlgebra`,
  `TauCeti.nsmulSaturated_leadingExponents_rename_toLex_flagMinorAlgebra`, and
  `TauCeti.fg_leadingExponents_rename_toLex_flagMinorAlgebra`: explicit description, saturation,
  and finite generation of the leading-exponent monoid.
* `TauCeti.exists_pos_weight_flagMinorAlgebra_degeneration`: over a field `k`, existence of a
  strictly positive integral weight `w : (Fin n ×ₗ Fin n) → ℕ` realizing the diagonal monomials as
  top `w`-homogeneous components of all flag minors, identifying the `w`-initial algebra with the
  `lex`-initial algebra, identifying the image of `weightReesAeval` on the `2 ^ n - 1` nonempty
  flag minors with the embedded weight-Rees algebra, proving flatness over `k[X]`, identifying the
  special fiber at `t = 0` (`k ⊗[k[X]] A.weightReesAlgebra w`) with
  `AddMonoidAlgebra k (AddSubmonoid.nonneg (GTPattern n))`, and identifying the localization away
  from `t` with `LaurentPolynomial (flagMinorAlgebra n k)`.

## References

* N. Gonciulea and V. Lakshmibai, *Degenerations of flag and Schubert varieties to toric
  varieties*, Transform. Groups **1** (1996), 215–248.
* M. Kogan and E. Miller, *Toric degeneration of Schubert varieties and Gelfand-Tsetlin polytopes*,
  Adv. Math. **193** (2005), 1–17.
* E. Miller and B. Sturmfels, *Combinatorial Commutative Algebra*, GTM 227, Springer, 2005,
  Chapter 14.
* B. Sturmfels, *Gröbner Bases and Convex Polytopes*, University Lecture Series 8, AMS, 1996,
  Chapter 11.
-/

public section

open Finset MvPolynomial MonomialOrder
open scoped Polynomial TensorProduct

namespace TauCeti

namespace GTPattern

/-! ### Saturation of nonnegative Gelfand-Tsetlin patterns and diagonal exponents -/

/-- The submonoid of nonnegative Gelfand-Tsetlin patterns is saturated under positive natural
multiples inside `GTPattern n`. -/
theorem nsmulSaturated_nonneg (n : ℕ) : (AddSubmonoid.nonneg (GTPattern n)).NSMulSaturated := by
  intro k P hkP
  rcases eq_or_ne k 0 with rfl | hk
  · exact .inl rfl
  · refine .inr (AddSubmonoid.mem_nonneg.mpr (zero_le_iff.mpr fun i j ↦ ?_))
    have h := (zero_le_iff.mp (AddSubmonoid.mem_nonneg.mp hkP)) i j
    rw [nsmul_apply, nsmul_eq_mul] at h
    by_contra! hlt
    exact (mul_neg_of_pos_of_neg (Nat.cast_pos.mpr (Nat.pos_of_ne_zero hk)) hlt).not_ge h

@[simp]
theorem nsmulSaturation_nonneg (n : ℕ) :
    (AddSubmonoid.nonneg (GTPattern n)).nsmulSaturation = AddSubmonoid.nonneg (GTPattern n) :=
  AddSubmonoid.nsmulSaturation_eq_self (nsmulSaturated_nonneg n)

/-- **Saturation of the diagonal-exponent monoid.** Inside the ambient exponent monoid
`Fin n ×ₗ Fin n →₀ ℕ`, if a positive multiple `k • e` lies in the submonoid generated by the
diagonal exponents of the flag minors, then `e` already lies in it. -/
theorem nsmulSaturated_closure_range_flagDiagonalExponent (n : ℕ) :
    (AddSubmonoid.closure (Set.range (flagDiagonalExponent (n := n)))).NSMulSaturated := by
  intro k e hke
  rcases eq_or_ne k 0 with rfl | hk
  · exact .inl rfl
  · right
    obtain ⟨Q, -, hQe⟩ := mem_closure_range_flagDiagonalExponent_iff.mp hke
    have hk_pos : (0 : ℤ) < k := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hk)
    have hQ (i j : ℕ) : Q i j = (k : ℤ) * exponentEntries e i j := by
      rw [hQe, map_nsmul, Pi.smul_apply, Pi.smul_apply, nsmul_eq_mul]
    let P : GTPattern n :=
      { entry := exponentEntries e
        zeros' := fun {i j} h ↦
          (mul_eq_zero.mp (hQ i j ▸ Q.entry_eq_zero h)).resolve_left hk_pos.ne'
        interlacing' := fun {i j} hij hj ↦
          ⟨le_of_mul_le_mul_left (hQ i j ▸ hQ i (j + 1) ▸ Q.entry_le_entry_succ_row hij hj) hk_pos,
            le_of_mul_le_mul_left
              (hQ (i + 1) (j + 1) ▸ hQ i j ▸ Q.entry_succ_succ_le_entry (i := i) hj) hk_pos⟩ }
    refine mem_closure_range_flagDiagonalExponent_iff.mpr ⟨P, zero_le_iff.mpr fun i j ↦ ?_, rfl⟩
    rw [← entry_eq_coe]; dsimp only [P]; rw [exponentEntries_apply]
    split_ifs
    · exact sum_nonneg fun _ _ ↦ Nat.cast_nonneg _
    · exact le_rfl

@[simp]
theorem nsmulSaturation_closure_range_flagDiagonalExponent (n : ℕ) :
    (AddSubmonoid.closure (Set.range (flagDiagonalExponent (n := n)))).nsmulSaturation =
      AddSubmonoid.closure (Set.range (flagDiagonalExponent (n := n))) :=
  AddSubmonoid.nsmulSaturation_eq_self (nsmulSaturated_closure_range_flagDiagonalExponent n)

end GTPattern

/-! ### Generator count and finite generation -/

/-- There are `2 ^ n - 1` nonempty subsets of `Fin n`, indexing the nonconstant flag-minor
generators (including the full determinant `flagMinor R univ` when `1 ≤ n`). -/
@[simp]
theorem card_nonempty_finset_fin (n : ℕ) :
    Fintype.card {I : Finset (Fin n) // I.Nonempty} = 2 ^ n - 1 := by
  rw [Fintype.card_subtype, show (univ.filter fun I : Finset (Fin n) ↦ I.Nonempty) = univ.erase ∅
      by ext; simp [Finset.ne_empty_iff_nonempty],
    card_erase_of_mem (mem_univ ∅), card_univ, Fintype.card_finset, Fintype.card_fin]

/-- Over a nontrivial commutative ring, the nonempty row subsets give `2 ^ n - 1` distinct flag
minors. -/
theorem card_image_nonempty_flagMinor (n : ℕ) (R : Type*) [CommRing R] [Nontrivial R] :
    Nat.card (flagMinor R '' {I : Finset (Fin n) | I.Nonempty}) = 2 ^ n - 1 := by
  rw [Nat.card_image_of_injective (flagMinor_injective R), Nat.card_eq_fintype_card]
  exact card_nonempty_finset_fin n

/-- The flag-minor algebra is finitely generated over every commutative ring `R`. -/
theorem fg_flagMinorAlgebra (n : ℕ) (R : Type*) [CommRing R] : (flagMinorAlgebra n R).FG := by
  classical
  exact ⟨univ.image (flagMinor R),
    by rw [coe_image, coe_univ, Set.image_univ, flagMinorAlgebra_def]⟩

/-! ### Diagonal SAGBI basis over every commutative ring -/

section SAGBI

variable {n : ℕ}

/-- **Diagonal SAGBI basis of the flag-minor algebra.** Over **every** commutative ring `R`, the
`2 ^ n - 1` nonempty flag minors (renamed to the row-major variable order along `toLex`) form a
`lex`-SAGBI basis of `(flagMinorAlgebra n R).map (rename toLex)`. -/
theorem isSAGBIBasis_image_nonempty_rename_toLex_flagMinor (R : Type*) [CommRing R] :
    lex.IsSAGBIBasis
      ((fun I : Finset (Fin n) ↦ rename toLex (flagMinor R I)) '' {I | I.Nonempty})
      ((flagMinorAlgebra n R).map (rename toLex)) := by
  rw [isSAGBIBasis_iff_initialAlgebra_le, initialAlgebra_def]
  refine ⟨fun _ ⟨I, _, h⟩ ↦ h ▸ Subalgebra.mem_map.mpr
    ⟨flagMinor R I, flagMinor_mem_flagMinorAlgebra R I, rfl⟩, Algebra.adjoin_le ?_⟩
  rintro _ ⟨F, hFA, rfl⟩
  obtain ⟨f, hfA, rfl⟩ := Subalgebra.mem_map.mp hFA
  let x : flagMinorAlgebra n R := ⟨f, hfA⟩
  let l := (flagMinorBasis n R).repr x
  have hf_eq : f = Finsupp.linearCombination R (fun s ↦ s.2.flagMinorProd R) l := by
    have hrepr := congrArg (flagMinorAlgebra n R).val
      ((flagMinorBasis n R).linearCombination_repr x)
    rw [Finsupp.linearCombination_apply, Finsupp.sum, map_sum] at hrepr
    simpa [x, Finsupp.linearCombination_apply, Finsupp.sum] using hrepr.symm
  rcases eq_or_ne l 0 with hl0 | hl
  · simp [hf_eq, hl0]
  · obtain ⟨s₀, -, -, hdeg, hlc⟩ := exists_mem_support_degree_and_leadingCoeff_flagMinorProd hl
    have : Nontrivial R :=
      let ⟨s, hs⟩ := Finsupp.support_nonempty_iff.mpr hl
      ⟨⟨l s, 0, Finsupp.mem_support_iff.mp hs⟩⟩
    rw [hf_eq, MonomialOrder.leadingTerm, hdeg, hlc, s₀.2.degree_rename_toLex_flagMinorProd R,
      monomial_sum_index]
    refine mul_mem (Subalgebra.algebraMap_mem _ (l s₀)) (Subalgebra.prod_mem _ fun m hm ↦ ?_)
    rw [← leadingTerm_rename_toLex_flagMinor (R := R)]
    exact Algebra.subset_adjoin ⟨_,
      ⟨s₀.2.colFinset m, s₀.2.colFinset_nonempty_of_lt_rowLen_zero (mem_range.mp hm), rfl⟩, rfl⟩

/-- Over **every** commutative ring `R`, the full family of `2 ^ n` flag minors (renamed along
`toLex`) forms a `lex`-SAGBI basis of `(flagMinorAlgebra n R).map (rename toLex)`. -/
theorem isSAGBIBasis_range_rename_toLex_flagMinor (R : Type*) [CommRing R] :
    lex.IsSAGBIBasis
      (Set.range fun I : Finset (Fin n) ↦ rename toLex (flagMinor R I))
      ((flagMinorAlgebra n R).map (rename toLex)) :=
  (isSAGBIBasis_image_nonempty_rename_toLex_flagMinor R).mono (Set.image_subset_range _ _)
    fun _ ⟨I, h⟩ ↦ h ▸ Subalgebra.mem_map.mpr
      ⟨flagMinor R I, flagMinor_mem_flagMinorAlgebra R I, rfl⟩

/-! ### Initial algebra and Gelfand-Tsetlin semigroup algebra over every commutative ring -/

/-- Every monomial whose exponent lies in the diagonal-exponent monoid belongs to the `lex`-initial
algebra of `(flagMinorAlgebra n R).map (rename toLex)`. -/
theorem monomial_mem_initialAlgebra_rename_toLex_flagMinorAlgebra (R : Type*) [CommRing R]
    {e : Fin n ×ₗ Fin n →₀ ℕ}
    (he : e ∈ AddSubmonoid.closure (Set.range (flagDiagonalExponent (n := n)))) (r : R) :
    monomial e r ∈ lex.initialAlgebra ((flagMinorAlgebra n R).map (rename toLex)) := by
  suffices h1 : monomial e (1 : R) ∈
      lex.initialAlgebra ((flagMinorAlgebra n R).map (rename toLex)) by
    simpa [smul_monomial] using Subalgebra.smul_mem _ h1 r
  induction he using AddSubmonoid.closure_induction with
  | mem _ hx =>
    obtain ⟨I, rfl⟩ := hx
    rw [← leadingTerm_rename_toLex_flagMinor (R := R)]
    exact leadingTerm_mem_initialAlgebra
      (Subalgebra.mem_map.mpr ⟨flagMinor R I, flagMinor_mem_flagMinorAlgebra R I, rfl⟩)
  | zero => simp
  | add _ _ _ _ iha ihb => simpa [monomial_mul_monomial] using mul_mem iha ihb

/-- **Support characterization of the initial algebra over every commutative ring.** A polynomial
belongs to `lex.initialAlgebra ((flagMinorAlgebra n R).map (rename toLex))` if and only if every
exponent in its support lies in `AddSubmonoid.closure (Set.range flagDiagonalExponent)`. -/
theorem mem_initialAlgebra_rename_toLex_flagMinorAlgebra_iff (R : Type*) [CommRing R]
    {p : MvPolynomial (Fin n ×ₗ Fin n) R} :
    p ∈ lex.initialAlgebra ((flagMinorAlgebra n R).map (rename toLex)) ↔
      (p.support : Set (Fin n ×ₗ Fin n →₀ ℕ)) ⊆
        AddSubmonoid.closure (Set.range (flagDiagonalExponent (n := n))) := by
  classical
  refine ⟨fun hp ↦ ?_, fun hp ↦ p.as_sum ▸ Subalgebra.sum_mem _ fun e he ↦
    monomial_mem_initialAlgebra_rename_toLex_flagMinorAlgebra R (hp he) (p.coeff e)⟩
  rw [← (isSAGBIBasis_range_rename_toLex_flagMinor R).adjoin_leadingTerm] at hp
  induction hp using Algebra.adjoin_induction with
  | mem _ hx =>
    obtain ⟨_, ⟨I, rfl⟩, rfl⟩ := hx
    rw [leadingTerm_rename_toLex_flagMinor]
    exact (Finset.coe_subset.mpr support_monomial_subset).trans
      (Finset.coe_singleton _ ▸ Set.singleton_subset_iff.mpr (AddSubmonoid.subset_closure ⟨I, rfl⟩))
  | algebraMap c => rcases eq_or_ne c 0 with rfl | hc <;> simp [support_C, *]
  | add x y _ _ hx hy =>
    exact (Finset.coe_subset.mpr support_add).trans
      (Finset.coe_union x.support y.support ▸ Set.union_subset hx hy)
  | mul x y _ _ hx hy =>
    exact (Finset.coe_subset.mpr (support_mul x y)).trans
      (Finset.coe_add x.support y.support ▸
        Set.add_subset_iff.mpr fun _ ha _ hb ↦ add_mem (hx ha) (hy hb))

/-- The image of the monoid algebra of `AddSubmonoid.closure (Set.range flagDiagonalExponent)` in
`MvPolynomial (Fin n ×ₗ Fin n) R` is the `lex`-initial algebra of the flag-minor algebra, over
**every** commutative ring `R`. -/
theorem range_mapDomainAlgHom_closure_flagDiagonalExponent (R : Type*) [CommRing R] :
    (AddMonoidAlgebra.mapDomainAlgHom R R
        (AddSubmonoid.closure (Set.range (flagDiagonalExponent (n := n)))).subtype).range =
      lex.initialAlgebra ((flagMinorAlgebra n R).map (rename toLex)) := by
  refine le_antisymm ?_ ?_
  · intro _ hp
    obtain ⟨x, rfl⟩ := (AddMonoidAlgebra.mapDomainAlgHom R R _).mem_range.mp hp
    clear hp
    induction x using AddMonoidAlgebra.induction_linear with
    | zero => simp
    | add _ _ hx hy => rw [map_add]; exact add_mem hx hy
    | single a c =>
      rw [AddMonoidAlgebra.mapDomainAlgHom_apply, AddMonoidAlgebra.mapDomain_single,
        single_eq_monomial]
      exact monomial_mem_initialAlgebra_rename_toLex_flagMinorAlgebra R a.property c
  · rw [← (isSAGBIBasis_range_rename_toLex_flagMinor R).adjoin_leadingTerm]
    refine Algebra.adjoin_le ?_
    rintro _ ⟨_, ⟨I, rfl⟩, rfl⟩
    exact (AddMonoidAlgebra.mapDomainAlgHom R R _).mem_range.mpr
      ⟨AddMonoidAlgebra.single ⟨flagDiagonalExponent I, AddSubmonoid.subset_closure ⟨I, rfl⟩⟩ 1, by
        simp [leadingTerm_rename_toLex_flagMinor, single_eq_monomial]⟩

/-- **The initial algebra of the flag-minor algebra is the Gelfand-Tsetlin pattern semigroup
algebra**, over **every** commutative ring `R`. -/
noncomputable def initialAlgebraFlagMinorEquiv (n : ℕ) (R : Type*) [CommRing R] :
    AddMonoidAlgebra R (AddSubmonoid.nonneg (GTPattern n)) ≃ₐ[R]
      lex.initialAlgebra ((flagMinorAlgebra n R).map (rename toLex)) :=
  (AddMonoidAlgebra.domCongr R R GTPattern.flagExponentEquiv.symm).trans
    ((AlgEquiv.ofInjective
        (AddMonoidAlgebra.mapDomainAlgHom R R
          (AddSubmonoid.closure (Set.range (flagDiagonalExponent (n := n)))).subtype)
        (AddMonoidAlgebra.mapDomain_injective Subtype.val_injective)).trans
      (Subalgebra.equivOfEq _ _ (range_mapDomainAlgHom_closure_flagDiagonalExponent R)))

@[simp]
theorem coe_initialAlgebraFlagMinorEquiv_single (R : Type*) [CommRing R]
    (P : AddSubmonoid.nonneg (GTPattern n)) (r : R) :
    (initialAlgebraFlagMinorEquiv n R (AddMonoidAlgebra.single P r) :
        MvPolynomial (Fin n ×ₗ Fin n) R) =
      monomial (GTPattern.flagExponentEquiv.symm P : Fin n ×ₗ Fin n →₀ ℕ) r := by
  rw [initialAlgebraFlagMinorEquiv, AlgEquiv.trans_apply, AlgEquiv.trans_apply,
    AddMonoidAlgebra.domCongr_single, Subalgebra.equivOfEq_apply]
  exact (AlgEquiv.ofInjective_apply _
    (AddMonoidAlgebra.mapDomain_injective Subtype.val_injective) _).trans <| by
    rw [AddMonoidAlgebra.mapDomainAlgHom_apply, AddMonoidAlgebra.mapDomain_single,
      AddSubmonoid.coe_subtype, single_eq_monomial]

/-- **Pattern/tableau/initial-algebra compatibility.** Under `initialAlgebraFlagMinorEquiv`, the
monomial basis element `single P 1` of a nonnegative Gelfand-Tsetlin pattern `P` maps to the
row-major lexicographic leading term of the standard-monomial tableau product associated to `P`
under `GTPattern.nonnegEquivBoundedSSYT`. -/
theorem coe_initialAlgebraFlagMinorEquiv_single_one_eq_leadingTerm (R : Type*) [CommRing R]
    (P : AddSubmonoid.nonneg (GTPattern n)) :
    (initialAlgebraFlagMinorEquiv n R (AddMonoidAlgebra.single P 1) :
        MvPolynomial (Fin n ×ₗ Fin n) R) =
      lex.leadingTerm
        (rename toLex ((GTPattern.nonnegEquivBoundedSSYT n P).2.flagMinorProd R)) := by
  rw [coe_initialAlgebraFlagMinorEquiv_single]
  nontriviality R
  let s := GTPattern.nonnegEquivBoundedSSYT n P
  have hdeg : (GTPattern.flagExponentEquiv.symm P : Fin n ×ₗ Fin n →₀ ℕ) =
      lex.degree (rename toLex (s.2.flagMinorProd R)) := by
    apply GTPattern.exponentEntries_injective
    rw [← GTPattern.coe_flagExponentEquiv_apply, AddEquiv.apply_symm_apply,
      s.2.exponentEntries_degree_rename_toLex_flagMinorProd R,
      ← GTPattern.coe_nonnegEquivBoundedSSYT_symm_apply s, Equiv.symm_apply_apply]
  rw [hdeg, MonomialOrder.leadingTerm, (s.2.monic_rename_toLex_flagMinorProd R).leadingCoeff_eq_one]

/-- The `lex`-initial algebra of `(flagMinorAlgebra n R).map (rename toLex)` is finitely generated
as an `R`-algebra over every commutative ring `R`. -/
theorem fg_initialAlgebra_rename_toLex_flagMinorAlgebra (n : ℕ) (R : Type*) [CommRing R] :
    (lex.initialAlgebra ((flagMinorAlgebra n R).map (rename toLex))).FG := by
  classical
  rw [← (isSAGBIBasis_range_rename_toLex_flagMinor R).adjoin_leadingTerm]
  exact ⟨univ.image fun I : Finset (Fin n) ↦ lex.leadingTerm (rename toLex (flagMinor R I)), by
    rw [coe_image, coe_univ, Set.image_univ, ← Set.range_comp]; rfl⟩

/-! ### Leading-exponent monoid, saturation, and finite generation -/

/-- Over `[CommRing R] [NoZeroDivisors R] [Nontrivial R]`, the leading-exponent monoid of
`(flagMinorAlgebra n R).map (rename toLex)` equals the submonoid generated by the diagonal
exponents of the flag minors. -/
theorem leadingExponents_rename_toLex_flagMinorAlgebra (R : Type*) [CommRing R]
    [NoZeroDivisors R] [Nontrivial R] :
    lex.leadingExponents ((flagMinorAlgebra n R).map (rename toLex)) =
      AddSubmonoid.closure (Set.range (flagDiagonalExponent (n := n))) := by
  ext e
  rw [mem_leadingExponents_iff]
  refine ⟨fun ⟨F, hFA, hF0, h⟩ ↦ h ▸ (mem_initialAlgebra_rename_toLex_flagMinorAlgebra_iff R).mp
    (leadingTerm_mem_initialAlgebra hFA) (by simp [support_leadingTerm' hF0]), fun he ↦ ?_⟩
  obtain ⟨s, rfl⟩ :=
    (BoundedSSYT.range_degree_rename_toLex_flagMinorProd R (n := n)).symm.subset he
  exact ⟨_, Subalgebra.mem_map.mpr ⟨_, s.2.flagMinorProd_mem_flagMinorAlgebra R, rfl⟩,
    (s.2.monic_rename_toLex_flagMinorProd R).ne_zero, rfl⟩

/-- The leading-exponent monoid of `(flagMinorAlgebra n R).map (rename toLex)` is saturated inside
`Fin n ×ₗ Fin n →₀ ℕ`. -/
theorem nsmulSaturated_leadingExponents_rename_toLex_flagMinorAlgebra (R : Type*) [CommRing R]
    [NoZeroDivisors R] [Nontrivial R] :
    (lex.leadingExponents ((flagMinorAlgebra n R).map (rename toLex))).NSMulSaturated := by
  rw [leadingExponents_rename_toLex_flagMinorAlgebra R]
  exact GTPattern.nsmulSaturated_closure_range_flagDiagonalExponent n

@[simp]
theorem nsmulSaturation_leadingExponents_rename_toLex_flagMinorAlgebra (R : Type*) [CommRing R]
    [NoZeroDivisors R] [Nontrivial R] :
    (lex.leadingExponents ((flagMinorAlgebra n R).map (rename toLex))).nsmulSaturation =
      lex.leadingExponents ((flagMinorAlgebra n R).map (rename toLex)) :=
  AddSubmonoid.nsmulSaturation_eq_self
    (nsmulSaturated_leadingExponents_rename_toLex_flagMinorAlgebra R)

/-- **Additive isomorphism between the leading-exponent monoid of the flag-minor algebra and the
monoid of nonnegative Gelfand-Tsetlin patterns.** -/
noncomputable def leadingExponentsFlagMinorEquiv (n : ℕ) (R : Type*) [CommRing R]
    [NoZeroDivisors R] [Nontrivial R] :
    lex.leadingExponents ((flagMinorAlgebra n R).map (rename toLex)) ≃+
      AddSubmonoid.nonneg (GTPattern n) :=
  (AddEquiv.addSubmonoidCongr (leadingExponents_rename_toLex_flagMinorAlgebra R)).trans
    GTPattern.flagExponentEquiv

@[simp]
theorem coe_leadingExponentsFlagMinorEquiv_apply (R : Type*) [CommRing R] [NoZeroDivisors R]
    [Nontrivial R] (e : lex.leadingExponents ((flagMinorAlgebra n R).map (rename toLex))) :
    ⇑(leadingExponentsFlagMinorEquiv n R e : GTPattern n) =
      GTPattern.exponentEntries (e : Fin n ×ₗ Fin n →₀ ℕ) := by
  rw [leadingExponentsFlagMinorEquiv, AddEquiv.trans_apply, GTPattern.coe_flagExponentEquiv_apply]
  rfl

/-- The leading-exponent monoid of `(flagMinorAlgebra n R).map (rename toLex)` is finitely
generated. -/
theorem fg_leadingExponents_rename_toLex_flagMinorAlgebra (n : ℕ) (R : Type*) [CommRing R]
    [NoZeroDivisors R] [Nontrivial R] :
    (lex.leadingExponents ((flagMinorAlgebra n R).map (rename toLex))).FG :=
  (AddSubmonoid.fg_iff _).mpr
    ⟨Set.range (flagDiagonalExponent (n := n)),
      (leadingExponents_rename_toLex_flagMinorAlgebra R).symm, Set.finite_range _⟩

/-! ### Flat positive weight-Rees degeneration over a field -/

private theorem baseChange_eval_zero_equiv
    {R B S : Type*} [CommRing R] [CommRing B] [Algebra R B] [CommRing S] [Algebra R S]
    (M : ℕ → Submodule R B) [SetLike.GradedMonoid M] (h1 : (1 : B) ∈ M 1)
    (φ : TauCeti.coeffSubalgebra M →ₐ[R] S) (hsurj : Function.Surjective φ)
    (hker : RingHom.ker φ = Ideal.span {TauCeti.coeffSubalgebra.X M h1}) :
    letI := TauCeti.coeffSubalgebra.algebra M h1
    letI := Algebra.compHom R (Polynomial.evalRingHom (0 : R))
    Nonempty ((R ⊗[R[X]] TauCeti.coeffSubalgebra M) ≃ₐ[R] S) := by
  let := TauCeti.coeffSubalgebra.algebra M h1
  let := Algebra.compHom R (Polynomial.evalRingHom (0 : R))
  let := Algebra.compHom S (Polynomial.evalRingHom (0 : R))
  let : IsScalarTower R[X] R S :=
    IsScalarTower.of_algebraMap_eq fun _ ↦ by simp [Algebra.compHom_algebraMap_apply]
  let : IsScalarTower R R[X] R :=
    IsScalarTower.of_algebraMap_eq fun _ ↦ by simp [Algebra.compHom_algebraMap_apply]
  let : IsScalarTower R R[X] (TauCeti.coeffSubalgebra M) :=
    TauCeti.coeffSubalgebra.isScalarTower M h1
  have hcomm : φ.toRingHom.comp (algebraMap R[X] (TauCeti.coeffSubalgebra M)) =
      algebraMap R[X] S := Polynomial.ringHom_ext'
    (RingHom.ext fun r ↦ by
      change φ (algebraMap R[X] _ (Polynomial.C r)) =
        algebraMap R S (Polynomial.eval 0 (Polynomial.C r))
      rw [Polynomial.eval_C, ← Polynomial.algebraMap_eq,
        ← IsScalarTower.algebraMap_apply R R[X], AlgHom.commutes])
    (by simp [Algebra.compHom_algebraMap_apply, TauCeti.coeffSubalgebra.algebraMap_X,
      RingHom.mem_ker.mp (hker.symm ▸ Ideal.subset_span rfl)])
  let φ' : TauCeti.coeffSubalgebra M →ₐ[R[X]] S :=
    { __ := φ.toRingHom, commutes' p := RingHom.congr_fun hcomm p }
  let Φ := AlgHom.liftEquiv R[X] R (TauCeti.coeffSubalgebra M) S φ'
  let i := (Algebra.TensorProduct.includeRight :
    TauCeti.coeffSubalgebra M →ₐ[R[X]] R ⊗[R[X]] TauCeti.coeffSubalgebra M).restrictScalars R
  have hi : Function.Surjective i := Algebra.TensorProduct.includeRight_surjective _
    fun r ↦ ⟨Polynomial.C r, by simp [Algebra.compHom_algebraMap_apply]⟩
  have hfi (p) : Φ (i p) = φ p := by simp [Φ, i, φ']
  have hiX : i (TauCeti.coeffSubalgebra.X M h1) = 0 := by
    simpa [i, Algebra.compHom_algebraMap_apply, Algebra.TensorProduct.algebraMap_apply,
      TauCeti.coeffSubalgebra.algebraMap_X] using (Algebra.TensorProduct.includeRight :
        TauCeti.coeffSubalgebra M →ₐ[R[X]] R ⊗[R[X]] TauCeti.coeffSubalgebra M).commutes
      Polynomial.X
  refine ⟨AlgEquiv.ofBijective Φ ⟨(injective_iff_map_eq_zero Φ).mpr fun x hx ↦ ?_,
    fun s ↦ let ⟨p, hp⟩ := hsurj s; ⟨i p, (hfi p).trans hp⟩⟩⟩
  obtain ⟨p, rfl⟩ := hi x
  obtain ⟨q, rfl⟩ := Ideal.mem_span_singleton.mp (by rwa [← hker, RingHom.mem_ker, ← hfi])
  rw [map_mul, hiX, zero_mul]

private theorem weightReesAlgebra_specialFiber_equiv
    {σ R : Type*} [CommRing R] (A : Subalgebra R (MvPolynomial σ R)) (w : σ → ℕ) :
    letI := TauCeti.coeffSubalgebra.algebra (A.weightFiltration w)
      (A.one_mem_weightFiltration_one w)
    letI := Algebra.compHom R (Polynomial.evalRingHom (0 : R))
    Nonempty ((R ⊗[R[X]] A.weightReesAlgebra w) ≃ₐ[R]
      Algebra.adjoin R (MvPolynomial.weightInitialForm w '' (A : Set (MvPolynomial σ R)))) := by
  classical
  let t : A.weightReesAlgebra w :=
    TauCeti.coeffSubalgebra.X (A.weightFiltration w) (A.one_mem_weightFiltration_one w)
  let ι : A.weightReesAlgebra w →ₐ[R] TauCeti.MvPolynomial.weightReesAlgebra R w :=
    ((Polynomial.mapAlgHom A.val).comp (A.weightReesAlgebra w).val).codRestrict _ fun g ↦
      TauCeti.mem_coeffSubalgebra_iff.mpr fun m ↦ by
        simpa [Polynomial.coeff_map] using
          (A.mem_weightFiltration_iff w).mp (TauCeti.mem_coeffSubalgebra_iff.mp g.property m)
  let φ : A.weightReesAlgebra w →ₐ[R] MvPolynomial σ R :=
    (TauCeti.MvPolynomial.weightReesSymbol R w).comp ι
  have hker : RingHom.ker φ = Ideal.span {t} := by
    ext g
    rw [RingHom.mem_ker, AlgHom.comp_apply, ← RingHom.mem_ker,
      TauCeti.MvPolynomial.ker_weightReesSymbol, Ideal.mem_span_singleton,
      Ideal.mem_span_singleton]
    refine ⟨fun ⟨q, hq⟩ ↦ ?_, fun ⟨q, hq⟩ ↦
      ⟨ι q, by rw [hq, map_mul]; congr 1; exact Subtype.ext (by simp [ι, t])⟩⟩
    have hcoeff (m : ℕ) : (g.val.coeff m : MvPolynomial σ R) = (Polynomial.X * q.val).coeff m := by
      simpa [ι, Polynomial.coeff_map] using
        congrArg (fun p : (MvPolynomial σ R)[X] ↦ p.coeff m) (congrArg Subtype.val hq)
    have h0 : g.val.coeff 0 = 0 := Subtype.ext (by simpa using hcoeff 0)
    obtain ⟨q', hq'⟩ := Polynomial.X_dvd_iff.mpr h0
    refine ⟨⟨q', TauCeti.mem_coeffSubalgebra_iff.mpr fun m ↦ (A.mem_weightFiltration_iff w).mpr ?_⟩,
      Subtype.ext (by simpa [t] using hq')⟩
    have hm : (q'.coeff m : MvPolynomial σ R) = q.val.coeff m := by
      simpa [hq', Polynomial.coeff_X_mul] using hcoeff (m + 1)
    exact hm ▸ TauCeti.mem_coeffSubalgebra_iff.mp q.property m
  have hrange : φ.range = Algebra.adjoin R (MvPolynomial.weightInitialForm w '' (A : Set _)) := by
    refine le_antisymm ?_ (Algebra.adjoin_le ?_)
    · rintro _ ⟨g, rfl⟩
      have hι_sum : ι g = ∑ m ∈ g.val.support,
          TauCeti.coeffSubalgebra.monomial _ m (g.val.coeff m : MvPolynomial σ R)
            ((A.mem_weightFiltration_iff w).mp
              (TauCeti.mem_coeffSubalgebra_iff.mp g.property m)) :=
        Subtype.ext <| by
          rw [AddSubmonoidClass.coe_finsetSum]
          simpa [ι, Polynomial.map_sum] using
            congrArg (Polynomial.map A.val.toRingHom) g.val.as_sum_support
      change TauCeti.MvPolynomial.weightReesSymbol R w (ι g) ∈ _
      rw [hι_sum, map_sum]
      refine Subalgebra.sum_mem _ fun m _ ↦ ?_
      rw [TauCeti.MvPolynomial.weightReesSymbol_monomial]
      set b : MvPolynomial σ R := (g.val.coeff m).val
      rcases (TauCeti.MvPolynomial.mem_weightFiltration_iff_weightedTotalDegree_le.mp
          ((A.mem_weightFiltration_iff w).mp
            (TauCeti.mem_coeffSubalgebra_iff.mp g.property m))).eq_or_lt
        with heq | hlt
      · rw [← heq, ← MvPolynomial.weightInitialForm_def]
        exact Algebra.subset_adjoin ⟨b, (g.val.coeff m).property, rfl⟩
      · rw [MvPolynomial.weightedHomogeneousComponent_eq_zero m b hlt]; exact zero_mem _
    · rintro _ ⟨b, hb, rfl⟩
      have hbm : (⟨b, hb⟩ : A) ∈ A.weightFiltration w (b.weightedTotalDegree w) :=
        (A.mem_weightFiltration_iff w).mpr
          (TauCeti.MvPolynomial.mem_weightFiltration_iff_weightedTotalDegree_le.mpr le_rfl)
      refine ⟨TauCeti.coeffSubalgebra.monomial _ _ ⟨b, hb⟩ hbm, ?_⟩
      change TauCeti.MvPolynomial.weightReesSymbol R w (ι _) = MvPolynomial.weightInitialForm w b
      rw [show ι (TauCeti.coeffSubalgebra.monomial _ _ ⟨b, hb⟩ hbm) =
          TauCeti.coeffSubalgebra.monomial _ _ b ((A.mem_weightFiltration_iff w).mp hbm)
          from Subtype.ext (by simp [ι]),
        TauCeti.MvPolynomial.weightReesSymbol_monomial, MvPolynomial.weightInitialForm_def]
  let S := Algebra.adjoin R (MvPolynomial.weightInitialForm w '' (A : Set (MvPolynomial σ R)))
  let φ' : A.weightReesAlgebra w →ₐ[R] S :=
    φ.codRestrict S fun g ↦ (SetLike.ext_iff.mp hrange (φ g)).mp (AlgHom.mem_range_self φ g)
  exact baseChange_eval_zero_equiv (A.weightFiltration w) (A.one_mem_weightFiltration_one w) φ'
    (fun ⟨y, hy⟩ ↦ let ⟨g, hg⟩ := (SetLike.ext_iff.mp hrange y).mpr hy; ⟨g, Subtype.ext hg⟩)
    (by ext g; rw [RingHom.mem_ker, ← hker, RingHom.mem_ker]; exact Subtype.ext_iff)

private theorem localization_away_X_equiv_laurent
    {R B : Type*} [CommSemiring R] [CommSemiring B] [Algebra R B]
    (M : ℕ → Submodule R B) [SetLike.GradedMonoid M] (h1 : (1 : B) ∈ M 1)
    (hM : Monotone M) (hex : (⨆ n, M n) = ⊤) :
    ∃ e : Localization.Away (TauCeti.coeffSubalgebra.X M h1) ≃ₐ[R] LaurentPolynomial B,
      e (algebraMap _ _ (TauCeti.coeffSubalgebra.X M h1)) = LaurentPolynomial.T 1 := by
  classical
  set t := TauCeti.coeffSubalgebra.X M h1
  let ψ : TauCeti.coeffSubalgebra M →ₐ[R] LaurentPolynomial B :=
    ((Polynomial.toLaurentAlg : B[X] →ₐ[B] LaurentPolynomial B).restrictScalars R).comp
      (TauCeti.coeffSubalgebra M).val
  let Ψ := IsLocalization.Away.liftAlgHom (S := Localization.Away t) (f := ψ) t
    (by simpa [ψ, t] using LaurentPolynomial.isUnit_T (R := B) 1)
  have hΨ (y) : Ψ (algebraMap _ _ y) = ψ y := by
    simp [Ψ, IsLocalization.Away.liftAlgHom_apply, IsLocalization.Away.lift, IsLocalization.lift_eq]
  refine ⟨AlgEquiv.ofBijective Ψ ⟨fun x₁ x₂ h ↦ ?_, fun z ↦ ?_⟩,
    (hΨ t).trans (by simp [ψ, t])⟩
  · obtain ⟨m₁, y₁, h₁⟩ := IsLocalization.Away.surj t x₁
    obtain ⟨m₂, y₂, h₂⟩ := IsLocalization.Away.surj t x₂
    have hy : y₁ * t ^ m₂ = y₂ * t ^ m₁ := Subtype.ext <| Polynomial.toLaurent_injective <| by
      change ψ (y₁ * t ^ m₂) = ψ (y₂ * t ^ m₁)
      rw [← hΨ, ← hΨ]; simp only [map_mul, map_pow, ← h₁, ← h₂, h]; ring
    refine ((IsLocalization.Away.algebraMap_isUnit (S := Localization.Away t) t).pow
      (m₁ + m₂)).mul_right_cancel ?_
    calc x₁ * algebraMap _ _ t ^ (m₁ + m₂)
        = algebraMap _ _ (y₁ * t ^ m₂) := by rw [pow_add, ← mul_assoc, h₁, map_mul, map_pow]
      _ = algebraMap _ _ (y₂ * t ^ m₁) := congrArg _ hy
      _ = x₂ * algebraMap _ _ t ^ (m₁ + m₂) := by
        rw [map_mul, map_pow, ← h₂, mul_assoc, ← pow_add, add_comm]
  · obtain ⟨m, f, hf⟩ := LaurentPolynomial.exists_T_pow z
    choose deg hdeg using fun i : ℕ ↦
      (Submodule.mem_iSup_of_directed M hM.directed_le).mp (hex.symm ▸ trivial : f.coeff i ∈ _)
    let d₀ := f.support.sup deg
    let num : TauCeti.coeffSubalgebra M := ⟨Polynomial.X ^ d₀ * f,
      TauCeti.mem_coeffSubalgebra_iff.mpr fun j ↦ by
        rw [Polynomial.coeff_X_pow_mul']
        split_ifs with h
        · by_cases hi : j - d₀ ∈ f.support
          · exact hM ((Finset.le_sup hi).trans h) (hdeg _)
          · rw [Polynomial.notMem_support_iff.mp hi]; exact zero_mem _
        · exact zero_mem _⟩
    let den : Submonoid.powers t :=
      ⟨t ^ (d₀ + m), Submonoid.pow_mem _ (Submonoid.mem_powers t) (d₀ + m)⟩
    refine ⟨IsLocalization.mk' (Localization.Away t) num den,
      (LaurentPolynomial.isUnit_T (R := B) ((d₀ + m : ℕ) : ℤ)).mul_left_cancel ?_⟩
    have hspec := congrArg Ψ (IsLocalization.mk'_spec' (Localization.Away t) num den)
    rw [map_mul, hΨ, hΨ] at hspec
    have h1 : ψ den = LaurentPolynomial.T ((d₀ + m : ℕ) : ℤ) := by simp [den, ψ, t]
    have h2 : ψ num = LaurentPolynomial.T (d₀ : ℤ) * Polynomial.toLaurent f := by
      simp [num, ψ, map_mul, Polynomial.toLaurent_X_pow]
    rw [h1, h2] at hspec
    rw [hspec, hf, mul_left_comm, ← LaurentPolynomial.T_add, Nat.cast_add, mul_comm]

/-- **Positive integral weight-Rees degeneration of the flag-minor algebra.** Over any field `k`,
there exists a strictly positive weight `w : (Fin n ×ₗ Fin n) → ℕ` such that, writing
`A = (flagMinorAlgebra n k).map (rename toLex)` and `t` for the Rees parameter
`coeffSubalgebra.X (A.weightFiltration w) (A.one_mem_weightFiltration_one w)` in
`A.weightReesAlgebra w`:
1. on every flag minor `flagMinor k I`, the top `w`-homogeneous component is its diagonal monomial
   `monomial (flagDiagonalExponent I) 1`;
2. the `w`-weight initial algebra of `A` equals its row-major lexicographic initial algebra
   (isomorphic to `AddMonoidAlgebra k (AddSubmonoid.nonneg (GTPattern n))` via
   `initialAlgebraFlagMinorEquiv`);
3. the Rees presentation map `weightReesAeval` on the `2 ^ n - 1` nonempty flag minors has image
   the embedded weight-Rees algebra `(A.weightReesAlgebra w).map (Polynomial.mapAlgHom A.val)`;
4. `A.weightReesAlgebra w` is flat over `k[X]` and its special fiber at `t = 0`
   (`k ⊗[k[X]] A.weightReesAlgebra w` along `Polynomial.evalRingHom 0`) is `k`-algebra isomorphic
   to `AddMonoidAlgebra k (AddSubmonoid.nonneg (GTPattern n))`;
5. the invertible-`t` fiber `Localization.Away t` is `k`-algebra isomorphic to
   `LaurentPolynomial (flagMinorAlgebra n k)` via an isomorphism sending `t` to `T 1`. -/
theorem exists_pos_weight_flagMinorAlgebra_degeneration (k : Type*) [Field k] :
    ∃ w : (Fin n ×ₗ Fin n) → ℕ,
      (∀ s, 0 < w s) ∧
      (∀ I : Finset (Fin n),
        weightedHomogeneousComponent w (Finsupp.weight w (flagDiagonalExponent I))
          (rename toLex (flagMinor k I)) = monomial (flagDiagonalExponent I) 1) ∧
      Algebra.adjoin k
          (MvPolynomial.weightInitialForm w ''
            (((flagMinorAlgebra n k).map (rename toLex)) : Set _)) =
        lex.initialAlgebra ((flagMinorAlgebra n k).map (rename toLex)) ∧
      (TauCeti.MvPolynomial.weightReesAeval
          (fun I : {I : Finset (Fin n) // I.Nonempty} ↦ rename toLex (flagMinor k I.val))
          (fun I ↦ Finsupp.weight w (flagDiagonalExponent I.val))).range =
        (((flagMinorAlgebra n k).map (rename toLex)).weightReesAlgebra w).map
          (Polynomial.mapAlgHom ((flagMinorAlgebra n k).map (rename toLex)).val) ∧
      (letI := TauCeti.coeffSubalgebra.algebra
          (((flagMinorAlgebra n k).map (rename toLex)).weightFiltration w)
          (((flagMinorAlgebra n k).map (rename toLex)).one_mem_weightFiltration_one w)
      letI := Algebra.compHom k (Polynomial.evalRingHom (0 : k))
      Module.Flat k[X] (((flagMinorAlgebra n k).map (rename toLex)).weightReesAlgebra w) ∧
      Nonempty ((k ⊗[k[X]] (((flagMinorAlgebra n k).map (rename toLex)).weightReesAlgebra w))
        ≃ₐ[k] AddMonoidAlgebra k (AddSubmonoid.nonneg (GTPattern n)))) ∧
      ∃ e : Localization.Away
          (TauCeti.coeffSubalgebra.X
            (((flagMinorAlgebra n k).map (rename toLex)).weightFiltration w)
            (((flagMinorAlgebra n k).map (rename toLex)).one_mem_weightFiltration_one w)) ≃ₐ[k]
          LaurentPolynomial (flagMinorAlgebra n k),
        e (algebraMap _ _ (TauCeti.coeffSubalgebra.X
            (((flagMinorAlgebra n k).map (rename toLex)).weightFiltration w)
            (((flagMinorAlgebra n k).map (rename toLex)).one_mem_weightFiltration_one w))) =
          LaurentPolynomial.T 1 := by
  classical
  set A : Subalgebra k (MvPolynomial (Fin n ×ₗ Fin n) k) :=
    (flagMinorAlgebra n k).map (rename toLex)
  let c : {I : Finset (Fin n) // I.Nonempty} → MvPolynomial (Fin n ×ₗ Fin n) k :=
    fun I ↦ rename toLex (flagMinor k I.val)
  have hrange : Set.range c =
      (fun I : Finset (Fin n) ↦ rename toLex (flagMinor k I)) '' {I | I.Nonempty} := by
    ext p; simp [c]
  have hadj : Algebra.adjoin k (Set.range c) = A := by
    rw [hrange, ← Set.image_image, ← AlgHom.map_adjoin, adjoin_flagMinor_nonempty]
  have hsagbi : lex.IsSAGBIBasis (Set.range c) (Algebra.adjoin k (Set.range c)) := by
    rw [hadj, hrange]; exact isSAGBIBasis_image_nonempty_rename_toLex_flagMinor k
  obtain ⟨w, hw, htop, hinit, hrees⟩ :=
    hsagbi.exists_pos_weight_range_weightReesAeval
      fun I : {I : Finset (Fin n) // I.Nonempty} ↦ monic_rename_toLex_flagMinor k I.val
  have hdeg : (fun I : {I : Finset (Fin n) // I.Nonempty} ↦ Finsupp.weight w (lex.degree (c I))) =
      fun I ↦ Finsupp.weight w (flagDiagonalExponent I.val) :=
    funext fun I ↦ by rw [degree_rename_toLex_flagMinor (R := k) I.val]
  have hrees_eq : (TauCeti.MvPolynomial.weightReesAeval c
      (fun I ↦ Finsupp.weight w (flagDiagonalExponent I.val))).range =
      (A.weightReesAlgebra w).map (Polynomial.mapAlgHom A.val) := by
    rw [← hdeg, hrees, Subalgebra.map_weightReesAlgebra]; congr 1; ext p
    have hc' : p ∈ (Polynomial.mapAlgHom (aeval c)).range ↔
        ∀ m, p.coeff m ∈ (aeval (R := k) c).range :=
      Polynomial.mem_map_rangeS (aeval (R := k) c).toRingHom
    have hv' : p ∈ (Polynomial.mapAlgHom A.val).range ↔ ∀ m, p.coeff m ∈ A.val.range :=
      Polynomial.mem_map_rangeS A.val.toRingHom
    rw [hc', hv', Subalgebra.range_val, aeval_range, hadj]
  have hinit' : Algebra.adjoin k (MvPolynomial.weightInitialForm w '' (A : Set _)) =
      lex.initialAlgebra A := by rwa [hadj] at hinit
  refine ⟨w, hw, fun I ↦ ?_, hinit', hrees_eq, ⟨A.flat_weightReesAlgebra w, ?_⟩, ?_⟩
  · rcases I.eq_empty_or_nonempty with rfl | hI
    · have h0 : flagDiagonalExponent (∅ : Finset (Fin n)) = 0 := by
        rw [← degree_rename_toLex_flagMinor (R := k), flagMinor_empty, map_one, degree_one]
      rw [h0, map_zero, flagMinor_empty, map_one, monomial_zero', C_1]
      exact MvPolynomial.weightedHomogeneousComponent_eq_self (isWeightedHomogeneous_one k w)
    · simpa [c, degree_rename_toLex_flagMinor (R := k) I] using htop ⟨I, hI⟩
  · obtain ⟨e0⟩ := weightReesAlgebra_specialFiber_equiv A w
    exact ⟨e0.trans ((Subalgebra.equivOfEq _ _ hinit').trans
      (initialAlgebraFlagMinorEquiv n k).symm)⟩
  · obtain ⟨e1, he1⟩ := localization_away_X_equiv_laurent (A.weightFiltration w)
      (A.one_mem_weightFiltration_one w) (A.weightFiltration_mono w) (A.iSup_weightFiltration w)
    let eA : A ≃ₐ[k] flagMinorAlgebra n k :=
      ((flagMinorAlgebra n k).equivMapOfInjective (rename toLex)
        (rename_injective _ toLex.injective)).symm
    refine ⟨e1.trans (AddMonoidAlgebra.mapAlgEquiv k ℤ eA), ?_⟩
    rw [AlgEquiv.trans_apply, he1]
    exact (AddMonoidAlgebra.mapAlgHom_single eA.toAlgHom 1 1).trans (by rw [map_one]; rfl)

end SAGBI

end TauCeti
