/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.MvPolynomial.FlagMinor.StandardMonomial
public import TauCeti.RingTheory.MvPolynomial.SAGBI.Basic

/-!
# Diagonal SAGBI basis and Gelfand-Tsetlin initial algebra

For the generic `n × n` matrix `(z_(r,c))` with variables ordered row by row along `toLex` and
equipped with the lexicographic monomial order `MonomialOrder.lex`, this file proves that the flag
minors indexed by the `2 ^ n - 1` nonempty subsets of `Fin n` (which include the full determinant
`flagMinor R univ` when `0 < n`, and are pairwise distinct over `[Nontrivial R]`) form a finite
monic SAGBI basis of the flag-minor subalgebra over **every** commutative ring `R`, identifies its
initial algebra with the semigroup algebra of nonnegative Gelfand-Tsetlin patterns over every
commutative ring `R`, and characterizes and proves saturation and finite generation of the
leading-exponent monoid `lex.leadingExponents` over `[NoZeroDivisors R] [Nontrivial R]`.

Note that it is the **initial** algebra
`lex.initialAlgebra ((flagMinorAlgebra n R).map (rename toLex))` that is isomorphic to the affine
semigroup algebra `AddMonoidAlgebra R (AddSubmonoid.nonneg (GTPattern n))`; the flag-minor algebra
`flagMinorAlgebra n R` itself is not thereby toric, and instead over any field `k` admits a flat
one-parameter Rees degeneration to this toric initial algebra
(`TauCeti.RingTheory.MvPolynomial.FlagMinor.Degeneration`).

## Main definitions

* `TauCeti.leadingExponentsFlagMinorEquiv`: over `[CommRing R] [NoZeroDivisors R] [Nontrivial R]`,
  the additive isomorphism `lex.leadingExponents ((flagMinorAlgebra n R).map (rename toLex)) ≃+
  AddSubmonoid.nonneg (GTPattern n)`.
* `TauCeti.initialAlgebraFlagMinorEquiv`: over **every** `[CommRing R]`, the `R`-algebra isomorphism
  `AddMonoidAlgebra R (AddSubmonoid.nonneg (GTPattern n)) ≃ₐ[R]
  lex.initialAlgebra ((flagMinorAlgebra n R).map (rename toLex))`.

## Main results

* `TauCeti.isSAGBIBasis_image_nonempty_rename_toLex_flagMinor` and
  `TauCeti.isSAGBIBasis_range_rename_toLex_flagMinor`: over **every** commutative ring `R`, the
  flag minors indexed by the `2 ^ n - 1` nonempty subsets (and by all `2 ^ n` subsets) of `Fin n`
  form a `lex`-SAGBI basis of `(flagMinorAlgebra n R).map (rename toLex)`.
* `TauCeti.mem_initialAlgebra_rename_toLex_flagMinorAlgebra_iff`: over **every** commutative ring
  `R`, a polynomial lies in `lex.initialAlgebra ((flagMinorAlgebra n R).map (rename toLex))` if and
  only if its support lies in `AddSubmonoid.closure (Set.range flagDiagonalExponent)`.
* `TauCeti.coe_initialAlgebraFlagMinorEquiv_single_one_eq_leadingTerm`: compatibility of the
  initial-algebra isomorphism with the standard-monomial tableau bijection
  `GTPattern.nonnegEquivBoundedSSYT`.
* `TauCeti.leadingExponents_rename_toLex_flagMinorAlgebra`,
  `TauCeti.nsmulSaturated_leadingExponents_rename_toLex_flagMinorAlgebra`, and
  `TauCeti.fg_leadingExponents_rename_toLex_flagMinorAlgebra`: over `[CommRing R] [NoZeroDivisors R]
  [Nontrivial R]`, explicit description, saturation, and finite generation of the leading-exponent
  monoid.

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

namespace TauCeti

/-! ### Diagonal SAGBI basis over every commutative ring -/

section SAGBI

variable {n : ℕ}

/-- **Diagonal SAGBI basis of the flag-minor algebra.** Over **every** commutative ring `R`, the
flag minors indexed by the `2 ^ n - 1` nonempty subsets of `Fin n` (renamed to the row-major
variable order along `toLex`; pairwise distinct when `[Nontrivial R]`) form a `lex`-SAGBI basis of
`(flagMinorAlgebra n R).map (rename toLex)`. -/
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
    rw [Finsupp.linearCombination_apply, Finsupp.sum]
    exact flagMinorBasis_repr_sum_eq x
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
    have hmem : rename toLex (flagMinor R (s₀.2.colFinset m)) ∈
        (fun I : Finset (Fin n) ↦ rename toLex (flagMinor R I)) '' {I | I.Nonempty} :=
      ⟨s₀.2.colFinset m, s₀.2.colFinset_nonempty_of_lt_rowLen_zero (mem_range.mp hm), rfl⟩
    exact Algebra.subset_adjoin ⟨_, hmem, rfl⟩

/-- Over **every** commutative ring `R`, the full family of flag minors indexed by all `2 ^ n`
subsets of `Fin n` (renamed along `toLex`; pairwise distinct when `[Nontrivial R]`) forms a
`lex`-SAGBI basis of `(flagMinorAlgebra n R).map (rename toLex)`. -/
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
    rw [BoundedSSYT.degree_rename_toLex_flagMinorProd_eq_coe_flagExponentEquiv_symm R s,
      Equiv.symm_apply_apply]
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

/-- Coercing the inverse image of a nonnegative Gelfand-Tsetlin pattern `P` under
`leadingExponentsFlagMinorEquiv` recovers the exponent entries by successive differences
`(P : GTPattern n) c (r + 1) - (P : GTPattern n) c r`. -/
@[simp]
theorem coe_leadingExponentsFlagMinorEquiv_symm_apply (R : Type*) [CommRing R]
    [NoZeroDivisors R] [Nontrivial R] (P : AddSubmonoid.nonneg (GTPattern n)) (r c : Fin n) :
    (((leadingExponentsFlagMinorEquiv n R).symm P : Fin n ×ₗ Fin n →₀ ℕ) (toLex (r, c)) : ℤ) =
      (P : GTPattern n) c (r + 1) - (P : GTPattern n) c r := by
  rw [leadingExponentsFlagMinorEquiv, AddEquiv.symm_trans_apply]
  exact GTPattern.flagExponentEquiv_symm_apply P r c

/-- The leading-exponent monoid of `(flagMinorAlgebra n R).map (rename toLex)` is finitely
generated. -/
theorem fg_leadingExponents_rename_toLex_flagMinorAlgebra (n : ℕ) (R : Type*) [CommRing R]
    [NoZeroDivisors R] [Nontrivial R] :
    (lex.leadingExponents ((flagMinorAlgebra n R).map (rename toLex))).FG :=
  (AddSubmonoid.fg_iff _).mpr
    ⟨Set.range (flagDiagonalExponent (n := n)),
      (leadingExponents_rename_toLex_flagMinorAlgebra R).symm, Set.finite_range _⟩

end SAGBI

end TauCeti
