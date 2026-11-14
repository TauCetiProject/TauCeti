/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.MvPolynomial.FlagMinor.StandardMonomial
public import TauCeti.RingTheory.MvPolynomial.Subalgebra.WeightFiltration
public import TauCeti.Algebra.Group.Submonoid.NSMulSaturation

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
  `lex`-initial algebra, and identifying the image of `weightReesAeval` on the `2 ^ n - 1` nonempty
  flag minors with the embedded weight-Rees algebra (which is flat over `k[X]` by
  `Subalgebra.flat_weightReesAlgebra`).

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
open scoped Polynomial

namespace TauCeti

namespace GTPattern

/-! ### Saturation of nonnegative Gelfand-Tsetlin patterns and diagonal exponents -/

/-- The submonoid of nonnegative Gelfand-Tsetlin patterns is saturated under positive natural
multiples inside `GTPattern n`. -/
theorem nsmulSaturated_nonneg (n : ℕ) : (AddSubmonoid.nonneg (GTPattern n)).NSMulSaturated := by
  intro k P hkP
  rcases eq_or_ne k 0 with rfl | hk
  · exact .inl rfl
  · right
    rw [AddSubmonoid.mem_nonneg, zero_le_iff] at hkP ⊢
    intro i j
    have h := hkP i j
    rw [nsmul_apply, nsmul_eq_mul] at h
    rcases lt_or_ge (P i j) 0 with hlt | hge
    · exfalso
      have hneg : (k : ℤ) * P i j < 0 :=
        mul_neg_of_pos_of_neg (Nat.cast_pos.mpr (Nat.pos_of_ne_zero hk)) hlt
      omega
    · exact hge

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
    have hQ_apply (i j : ℕ) : Q i j = (k : ℤ) * exponentEntries e i j := by
      rw [hQe, map_nsmul, Pi.smul_apply, Pi.smul_apply, nsmul_eq_mul]
    let P : GTPattern n :=
      { entry := exponentEntries e
        zeros' := fun {i j} h ↦ by
          have h0 := Q.entry_eq_zero h
          rw [hQ_apply] at h0
          exact (mul_eq_zero.mp h0).resolve_left hk_pos.ne'
        interlacing' := fun {i j} hij hj ↦ by
          have h1 := Q.entry_le_entry_succ_row hij hj
          have h2 := Q.entry_succ_succ_le_entry (i := i) hj
          rw [hQ_apply, hQ_apply] at h1 h2
          exact ⟨le_of_mul_le_mul_left h1 hk_pos, le_of_mul_le_mul_left h2 hk_pos⟩ }
    have hP0 : 0 ≤ P := zero_le_iff.mpr fun i j ↦ by
      rw [← entry_eq_coe]
      dsimp only [P]
      rw [exponentEntries_apply]
      split_ifs
      · exact sum_nonneg fun _ _ ↦ Nat.cast_nonneg _
      · exact le_rfl
    exact mem_closure_range_flagDiagonalExponent_iff.mpr ⟨P, hP0, rfl⟩

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
  rw [Fintype.card_subtype]
  have hfilter : (univ.filter fun I : Finset (Fin n) ↦ I.Nonempty) = univ.erase ∅ := by
    ext I
    simp [Finset.nonempty_iff_ne_empty]
  rw [hfilter, card_erase_of_mem (mem_univ ∅), card_univ, Fintype.card_finset, Fintype.card_fin]

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

private theorem monomial_sum_one_eq_prod {R : Type*} [CommRing R] (s : Finset ℕ)
    (f : ℕ → Fin n ×ₗ Fin n →₀ ℕ) :
    (monomial (∑ m ∈ s, f m) (1 : R) : MvPolynomial (Fin n ×ₗ Fin n) R) =
      ∏ m ∈ s, monomial (f m) 1 := by
  induction s using Finset.cons_induction with
  | empty => simp
  | cons a s ha ih => rw [sum_cons, prod_cons, ← ih, monomial_mul_monomial, mul_one]

/-- **Diagonal SAGBI basis of the flag-minor algebra.** Over **every** commutative ring `R`, the
`2 ^ n - 1` nonempty flag minors (renamed to the row-major variable order along `toLex`) form a
`lex`-SAGBI basis of `(flagMinorAlgebra n R).map (rename toLex)`. -/
theorem isSAGBIBasis_image_nonempty_rename_toLex_flagMinor (R : Type*) [CommRing R] :
    lex.IsSAGBIBasis
      ((fun I : Finset (Fin n) ↦ rename toLex (flagMinor R I)) '' {I | I.Nonempty})
      ((flagMinorAlgebra n R).map (rename toLex)) := by
  set B : Set (MvPolynomial (Fin n ×ₗ Fin n) R) :=
    (fun I : Finset (Fin n) ↦ rename toLex (flagMinor R I)) '' {I | I.Nonempty}
  set A : Subalgebra R (MvPolynomial (Fin n ×ₗ Fin n) R) :=
    (flagMinorAlgebra n R).map (rename toLex)
  rw [isSAGBIBasis_iff_initialAlgebra_le, initialAlgebra_def]
  refine ⟨?_, Algebra.adjoin_le ?_⟩
  · rintro _ ⟨I, -, rfl⟩
    exact Subalgebra.mem_map.mpr ⟨flagMinor R I, flagMinor_mem_flagMinorAlgebra R I, rfl⟩
  · rintro _ ⟨F, hFA, rfl⟩
    obtain ⟨f, hfA, rfl⟩ := Subalgebra.mem_map.mp hFA
    let x : flagMinorAlgebra n R := ⟨f, hfA⟩
    let l := (flagMinorBasis n R).repr x
    have hf_eq : f = Finsupp.linearCombination R (fun s ↦ s.2.flagMinorProd R) l := by
      have hrepr :=
        congrArg (flagMinorAlgebra n R).val ((flagMinorBasis n R).linearCombination_repr x)
      rw [Finsupp.linearCombination_apply, Finsupp.sum, map_sum] at hrepr
      simpa [x, Finsupp.linearCombination_apply, Finsupp.sum] using hrepr.symm
    rcases eq_or_ne l 0 with hl0 | hl
    · simp [hf_eq, hl0]
    · obtain ⟨s₀, -, -, hdeg, hlc⟩ := exists_mem_support_degree_and_leadingCoeff_flagMinorProd hl
      have : Nontrivial R :=
        let ⟨s, hs⟩ := Finsupp.support_nonempty_iff.mpr hl
        ⟨⟨l s, 0, Finsupp.mem_support_iff.mp hs⟩⟩
      have hsmul :
          monomial (∑ m ∈ range (s₀.1.1.rowLen 0), flagDiagonalExponent (s₀.2.colFinset m)) (l s₀) =
            l s₀ • monomial (∑ m ∈ range (s₀.1.1.rowLen 0),
              flagDiagonalExponent (s₀.2.colFinset m)) (1 : R) := by
        rw [smul_monomial, smul_eq_mul, mul_one]
      rw [hf_eq, MonomialOrder.leadingTerm, hdeg, hlc, s₀.2.degree_rename_toLex_flagMinorProd R,
        hsmul, monomial_sum_one_eq_prod]
      refine Subalgebra.smul_mem _ ?_ (l s₀)
      refine Subalgebra.prod_mem _ fun m hm ↦ ?_
      rw [← leadingTerm_rename_toLex_flagMinor (R := R)]
      exact Algebra.subset_adjoin
        ⟨rename toLex (flagMinor R (s₀.2.colFinset m)),
          ⟨s₀.2.colFinset m, s₀.2.colFinset_nonempty_of_lt_rowLen_zero (mem_range.mp hm), rfl⟩, rfl⟩

/-- Over **every** commutative ring `R`, the full family of `2 ^ n` flag minors (renamed along
`toLex`) forms a `lex`-SAGBI basis of `(flagMinorAlgebra n R).map (rename toLex)`. -/
theorem isSAGBIBasis_range_rename_toLex_flagMinor (R : Type*) [CommRing R] :
    lex.IsSAGBIBasis
      (Set.range fun I : Finset (Fin n) ↦ rename toLex (flagMinor R I))
      ((flagMinorAlgebra n R).map (rename toLex)) := by
  refine (isSAGBIBasis_image_nonempty_rename_toLex_flagMinor R).mono (Set.image_subset_range _ _) ?_
  rintro _ ⟨I, rfl⟩
  exact Subalgebra.mem_map.mpr ⟨flagMinor R I, flagMinor_mem_flagMinorAlgebra R I, rfl⟩

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
  | add a b _ _ iha ihb => simpa [monomial_mul_monomial] using mul_mem iha ihb

/-- **Support characterization of the initial algebra over every commutative ring.** A polynomial
belongs to `lex.initialAlgebra ((flagMinorAlgebra n R).map (rename toLex))` if and only if every
exponent in its support lies in `AddSubmonoid.closure (Set.range flagDiagonalExponent)`. -/
theorem mem_initialAlgebra_rename_toLex_flagMinorAlgebra_iff (R : Type*) [CommRing R]
    {p : MvPolynomial (Fin n ×ₗ Fin n) R} :
    p ∈ lex.initialAlgebra ((flagMinorAlgebra n R).map (rename toLex)) ↔
      (p.support : Set (Fin n ×ₗ Fin n →₀ ℕ)) ⊆
        AddSubmonoid.closure (Set.range (flagDiagonalExponent (n := n))) := by
  classical
  refine ⟨fun hp ↦ ?_, fun hp ↦ ?_⟩
  · rw [← (isSAGBIBasis_range_rename_toLex_flagMinor R).adjoin_leadingTerm] at hp
    induction hp using Algebra.adjoin_induction with
    | mem _ hx =>
      obtain ⟨_, ⟨I, rfl⟩, rfl⟩ := hx
      rw [leadingTerm_rename_toLex_flagMinor]
      refine (Finset.coe_subset.mpr support_monomial_subset).trans ?_
      rw [Finset.coe_singleton]
      exact Set.singleton_subset_iff.mpr
        (SetLike.mem_coe.mpr (AddSubmonoid.subset_closure (Set.mem_range_self I)))
    | algebraMap c =>
      rcases eq_or_ne c 0 with rfl | hc
      · simp
      · simp [support_C, hc]
    | add x y _ _ hx hy =>
      refine (Finset.coe_subset.mpr support_add).trans ?_
      rw [Finset.coe_union]
      exact Set.union_subset hx hy
    | mul x y _ _ hx hy =>
      refine (Finset.coe_subset.mpr (support_mul x y)).trans ?_
      rw [Finset.coe_add]
      exact Set.add_subset_iff.mpr fun a ha b hb ↦ add_mem (hx ha) (hy hb)
  · rw [p.as_sum]
    exact Subalgebra.sum_mem _ fun e he ↦
      monomial_mem_initialAlgebra_rename_toLex_flagMinorAlgebra R (hp he) (p.coeff e)

/-- The image of the monoid algebra of `AddSubmonoid.closure (Set.range flagDiagonalExponent)` in
`MvPolynomial (Fin n ×ₗ Fin n) R` is the `lex`-initial algebra of the flag-minor algebra, over
**every** commutative ring `R`. -/
theorem range_mapDomainAlgHom_closure_flagDiagonalExponent (R : Type*) [CommRing R] :
    (AddMonoidAlgebra.mapDomainAlgHom R R
        (AddSubmonoid.closure (Set.range (flagDiagonalExponent (n := n)))).subtype).range =
      lex.initialAlgebra ((flagMinorAlgebra n R).map (rename toLex)) := by
  have hmem (x : AddMonoidAlgebra R
      (AddSubmonoid.closure (Set.range (flagDiagonalExponent (n := n))))) :
      AddMonoidAlgebra.mapDomainAlgHom R R
          (AddSubmonoid.closure (Set.range (flagDiagonalExponent (n := n)))).subtype x ∈
        lex.initialAlgebra ((flagMinorAlgebra n R).map (rename toLex)) := by
    induction x using AddMonoidAlgebra.induction_linear with
    | zero => simp
    | add x y hx hy => rw [map_add]; exact add_mem hx hy
    | single a c =>
      rw [AddMonoidAlgebra.mapDomainAlgHom_apply, AddMonoidAlgebra.mapDomain_single,
        single_eq_monomial]
      exact monomial_mem_initialAlgebra_rename_toLex_flagMinorAlgebra R a.2 c
  refine le_antisymm ?_ ?_
  · rintro _ ⟨x, rfl⟩
    exact hmem x
  · rw [← (isSAGBIBasis_range_rename_toLex_flagMinor R).adjoin_leadingTerm]
    refine Algebra.adjoin_le ?_
    rintro _ ⟨_, ⟨I, rfl⟩, rfl⟩
    have hI : flagDiagonalExponent I ∈
        AddSubmonoid.closure (Set.range (flagDiagonalExponent (n := n))) :=
      AddSubmonoid.subset_closure (Set.mem_range_self I)
    exact (AddMonoidAlgebra.mapDomainAlgHom R R _).mem_range.mpr
      ⟨AddMonoidAlgebra.single ⟨flagDiagonalExponent I, hI⟩ 1, by
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
  refine ⟨univ.image fun I : Finset (Fin n) ↦ lex.leadingTerm (rename toLex (flagMinor R I)), ?_⟩
  rw [coe_image, coe_univ, Set.image_univ, ← Set.range_comp]
  rfl

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
  constructor
  · rintro ⟨F, hFA, hF0, rfl⟩
    have hlt : lex.leadingTerm F ∈
        lex.initialAlgebra ((flagMinorAlgebra n R).map (rename toLex)) :=
      leadingTerm_mem_initialAlgebra hFA
    exact (mem_initialAlgebra_rename_toLex_flagMinorAlgebra_iff R).mp hlt
      (by simp [support_leadingTerm' hF0])
  · intro he
    have he' : e ∈ Set.range
        (fun s : (Σ μ : {μ : YoungDiagram // μ.colLen 0 ≤ n}, BoundedSSYT n μ.1) ↦
          lex.degree (rename toLex (s.2.flagMinorProd R))) := by
      rw [BoundedSSYT.range_degree_rename_toLex_flagMinorProd R]
      exact he
    obtain ⟨s, rfl⟩ := he'
    exact ⟨rename toLex (s.2.flagMinorProd R),
      Subalgebra.mem_map.mpr
        ⟨s.2.flagMinorProd R, s.2.flagMinorProd_mem_flagMinorAlgebra R, rfl⟩,
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

/-- **Positive integral weight-Rees degeneration of the flag-minor algebra.** Over any field `k`,
there exists a strictly positive weight `w : (Fin n ×ₗ Fin n) → ℕ` such that:
1. on every flag minor `flagMinor k I`, the top `w`-homogeneous component is its diagonal monomial
   `monomial (flagDiagonalExponent I) 1`;
2. the `w`-weight initial algebra of `(flagMinorAlgebra n k).map (rename toLex)` equals its
   row-major lexicographic initial algebra (which is isomorphic to
   `AddMonoidAlgebra k (AddSubmonoid.nonneg (GTPattern n))` via `initialAlgebraFlagMinorEquiv`);
3. the Rees presentation map `weightReesAeval` on the `2 ^ n - 1` nonempty flag minors has image
   the embedded weight-Rees algebra
   `(((flagMinorAlgebra n k).map (rename toLex)).weightReesAlgebra w).map
     (Polynomial.mapAlgHom ((flagMinorAlgebra n k).map (rename toLex)).val)`, whose domain
   `((flagMinorAlgebra n k).map (rename toLex)).weightReesAlgebra w` is flat over `k[X]` by
   `Subalgebra.flat_weightReesAlgebra`. -/
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
          (fun I : {I : Finset (Fin n) // I.Nonempty} ↦ rename toLex (flagMinor k I.1))
          (fun I ↦ Finsupp.weight w (flagDiagonalExponent I.1))).range =
        (((flagMinorAlgebra n k).map (rename toLex)).weightReesAlgebra w).map
          (Polynomial.mapAlgHom ((flagMinorAlgebra n k).map (rename toLex)).val) := by
  let c : {I : Finset (Fin n) // I.Nonempty} → MvPolynomial (Fin n ×ₗ Fin n) k :=
    fun I ↦ rename toLex (flagMinor k I.1)
  have hrange : Set.range c =
      (fun I : Finset (Fin n) ↦ rename toLex (flagMinor k I)) '' {I | I.Nonempty} := by
    ext p
    simp [c]
  have hadj : Algebra.adjoin k (Set.range c) = (flagMinorAlgebra n k).map (rename toLex) := by
    rw [hrange, ← Set.image_image, ← AlgHom.map_adjoin, adjoin_flagMinor_nonempty]
  have hc_monic : ∀ I, lex.Monic (c I) := fun I ↦ monic_rename_toLex_flagMinor k I.1
  have hsagbi : lex.IsSAGBIBasis (Set.range c) (Algebra.adjoin k (Set.range c)) := by
    rw [hadj, hrange]
    exact isSAGBIBasis_image_nonempty_rename_toLex_flagMinor k
  obtain ⟨w, hw, htop, hinit, hrees⟩ :=
    hsagbi.exists_pos_weight_range_weightReesAeval hc_monic
  have hdeg :
      (fun I : {I : Finset (Fin n) // I.Nonempty} ↦ Finsupp.weight w (lex.degree (c I))) =
        fun I ↦ Finsupp.weight w (flagDiagonalExponent I.1) :=
    funext fun I ↦ by rw [degree_rename_toLex_flagMinor (R := k) I.1]
  refine ⟨w, hw, fun I ↦ ?_, by rwa [hadj] at hinit, ?_⟩
  · rcases I.eq_empty_or_nonempty with rfl | hI
    · have h0 : flagDiagonalExponent (∅ : Finset (Fin n)) = 0 := by
        rw [← degree_rename_toLex_flagMinor (R := k), flagMinor_empty, map_one, degree_one]
      rw [h0, map_zero, flagMinor_empty, map_one, monomial_zero', C_1]
      exact MvPolynomial.weightedHomogeneousComponent_eq_self (isWeightedHomogeneous_one k w)
    · simpa [c, degree_rename_toLex_flagMinor (R := k) I] using htop ⟨I, hI⟩
  · rw [← hdeg, hrees, Subalgebra.map_weightReesAlgebra]
    congr 1
    ext p
    have hc' : p ∈ (Polynomial.mapAlgHom (aeval c)).range ↔
        ∀ m, p.coeff m ∈ (aeval (R := k) c).range :=
      Polynomial.mem_map_rangeS (aeval (R := k) c).toRingHom
    have hv' : p ∈ (Polynomial.mapAlgHom ((flagMinorAlgebra n k).map (rename toLex)).val).range ↔
        ∀ m, p.coeff m ∈ ((flagMinorAlgebra n k).map (rename toLex)).val.range :=
      Polynomial.mem_map_rangeS ((flagMinorAlgebra n k).map (rename toLex)).val.toRingHom
    rw [hc', hv', Subalgebra.range_val, aeval_range, hadj]

end SAGBI

end TauCeti
