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
import TauCeti.Data.Finsupp.Weight
import TauCeti.RingTheory.GradedAlgebra.CoeffSubalgebra.Laurent

/-!
# Diagonal SAGBI basis, Gelfand-Tsetlin initial algebra, and weight-Rees degeneration

For the generic `n × n` matrix `(z_(r,c))` with variables ordered row by row along `toLex` and
equipped with the lexicographic monomial order `MonomialOrder.lex`, this file proves that the flag
minors indexed by the `2 ^ n - 1` nonempty subsets of `Fin n` (which include the full determinant
`flagMinor R univ` when `0 < n`, and are pairwise distinct over `[Nontrivial R]`) form a finite
monic SAGBI basis of the flag-minor subalgebra over **every** commutative ring `R`, identifies its
initial algebra with the semigroup algebra of nonnegative Gelfand-Tsetlin patterns over every
commutative ring `R`, characterizes and proves saturation and finite generation of the
leading-exponent monoid `lex.leadingExponents` over `[NoZeroDivisors R] [Nontrivial R]`, and
constructs the flat positive weight-Rees degeneration over any field.

Note that it is the **initial** algebra
`lex.initialAlgebra ((flagMinorAlgebra n R).map (rename toLex))` that is isomorphic to the affine
semigroup algebra `AddMonoidAlgebra R (AddSubmonoid.nonneg (GTPattern n))`; the flag-minor algebra
`flagMinorAlgebra n R` itself is not thereby toric, and instead over any field `k` admits a flat
one-parameter Rees degeneration to this toric initial algebra.

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
* `TauCeti.exists_pos_weight_flagMinorAlgebra_degeneration`: over any field `k`, existence of a
  strictly positive integral weight `w : (Fin n ×ₗ Fin n) → ℕ` realizing the diagonal monomials as
  weight-initial forms of all flag minors (with weighted degree equal to the diagonal weight),
  identifying the `w`-initial algebra with the `lex`-initial algebra, identifying the image of
  `weightReesAeval` on the `2 ^ n - 1` nonempty-subset flag minors with the embedded weight-Rees
  algebra, proving flatness over `k[X]`, constructing a `k`-algebra isomorphism from the special
  fiber at `t = 0` (`k ⊗[k[X]] A.weightReesAlgebra w`) to
  `AddMonoidAlgebra k (AddSubmonoid.nonneg (GTPattern n))` sending each homogenized flag minor to
  `single ⟨GTPattern.rowSubset I, GTPattern.zero_le_rowSubset I⟩ 1`, and identifying the
  localization away from `t` with `LaurentPolynomial (flagMinorAlgebra n k)`.

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

/-! ### Flat positive weight-Rees degeneration over a field -/

/-- **Positive integral weight-Rees degeneration of the flag-minor algebra.** Over any field `k`,
there exists a strictly positive weight `w : (Fin n ×ₗ Fin n) → ℕ` such that, writing
`A = (flagMinorAlgebra n k).map (rename toLex)` and `t` for the Rees parameter
`coeffSubalgebra.X (A.weightFiltration w) (A.one_mem_weightFiltration_one w)` in
`A.weightReesAlgebra w`:
1. on every flag minor `flagMinor k I`, its `w`-initial form is its diagonal monomial
   `monomial (flagDiagonalExponent I) 1` and its weighted total degree is
   `Finsupp.weight w (flagDiagonalExponent I)`;
2. the `w`-weight initial algebra of `A` equals its row-major lexicographic initial algebra
   (isomorphic to `AddMonoidAlgebra k (AddSubmonoid.nonneg (GTPattern n))` via
   `initialAlgebraFlagMinorEquiv`);
3. the Rees presentation map `weightReesAeval` on the `2 ^ n - 1` nonempty-subset flag minors has
   image the embedded weight-Rees algebra
   `(A.weightReesAlgebra w).map (Polynomial.mapAlgHom A.val)`;
4. `A.weightReesAlgebra w` is flat over `k[X]` and admits a `k`-algebra isomorphism from its
   special fiber at `t = 0` (`k ⊗[k[X]] A.weightReesAlgebra w` along `Polynomial.evalRingHom 0`)
   to `AddMonoidAlgebra k (AddSubmonoid.nonneg (GTPattern n))` sending each homogenized flag minor
   to `AddMonoidAlgebra.single ⟨GTPattern.rowSubset I, GTPattern.zero_le_rowSubset I⟩ 1`;
5. the invertible-`t` fiber `Localization.Away t` is `k`-algebra isomorphic to
   `LaurentPolynomial (flagMinorAlgebra n k)` via an isomorphism sending `t` to `T 1`. -/
theorem exists_pos_weight_flagMinorAlgebra_degeneration (k : Type*) [Field k] :
    ∃ w : (Fin n ×ₗ Fin n) → ℕ,
      (∀ s, 0 < w s) ∧
      (∀ I : Finset (Fin n),
        MvPolynomial.weightInitialForm w (rename toLex (flagMinor k I)) =
          monomial (flagDiagonalExponent I) 1 ∧
        (rename toLex (flagMinor k I)).weightedTotalDegree w =
          Finsupp.weight w (flagDiagonalExponent I)) ∧
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
      ∃ e0 : (k ⊗[k[X]] (((flagMinorAlgebra n k).map (rename toLex)).weightReesAlgebra w)) ≃ₐ[k]
          AddMonoidAlgebra k (AddSubmonoid.nonneg (GTPattern n)),
        ∀ (I : Finset (Fin n))
          (hIm : ⟨rename toLex (flagMinor k I), Subalgebra.mem_map.mpr
            ⟨flagMinor k I, flagMinor_mem_flagMinorAlgebra k I, rfl⟩⟩ ∈
              ((flagMinorAlgebra n k).map (rename toLex)).weightFiltration w
                (Finsupp.weight w (flagDiagonalExponent I))),
          e0 (1 ⊗ₜ[k[X]] TauCeti.coeffSubalgebra.monomial
            (((flagMinorAlgebra n k).map (rename toLex)).weightFiltration w)
            (Finsupp.weight w (flagDiagonalExponent I))
            ⟨rename toLex (flagMinor k I), Subalgebra.mem_map.mpr
              ⟨flagMinor k I, flagMinor_mem_flagMinorAlgebra k I, rfl⟩⟩ hIm) =
            AddMonoidAlgebra.single ⟨GTPattern.rowSubset I, GTPattern.zero_le_rowSubset I⟩ 1) ∧
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
  have hc_monic : ∀ I : {I : Finset (Fin n) // I.Nonempty}, lex.Monic (c I) :=
    fun I ↦ monic_rename_toLex_flagMinor k I.val
  set a := fun I : {I : Finset (Fin n) // I.Nonempty} ↦ lex.degree (c I)
  obtain ⟨B, hB, hspan⟩ := TauCeti.exists_finset_toricIdeal_eq_span a
  let b : B → MvPolynomial {I : Finset (Fin n) // I.Nonempty} k :=
    fun j ↦ monomial j.val.1 1 - monomial j.val.2 1
  have hJ : TauCeti.toricIdeal k a = Ideal.span (Set.range b) := by
    rw [hspan k]
    congr 1
    exact Set.image_eq_range _ _
  choose Q hQc hQ using fun j : B ↦
    hsagbi.exists_aeval_eq_aeval_sub hc_monic (hB j.val j.property)
  obtain ⟨w, hw, hcw, hgw, hQw⟩ :=
    exists_pos_weight_forall_mem_weightFiltrationLT hc_monic hQ
  let d := fun I ↦ Finsupp.weight w (a I)
  have hwA (u : {I : Finset (Fin n) // I.Nonempty} →₀ ℕ) :
      Finsupp.weight d u = Finsupp.weight w (Finsupp.linearCombination ℕ a u) :=
    Finsupp.weight_comp_eq_apply_linearCombination (Finsupp.weight w) a u
  have hb (j : B) : (b j).IsWeightedHomogeneous d (Finsupp.weight d j.val.1) :=
    (isWeightedHomogeneous_monomial _ _ _ rfl).sub
      (isWeightedHomogeneous_monomial _ _ _ (by rw [hwA, hwA, hB j.val j.property]))
  have hker : RingHom.ker (aeval (fun I ↦ monomial (a I) (1 : k))) =
      Ideal.span (Set.range b) := by
    rw [← TauCeti.toricIdeal_eq_ker_aeval_monomial, hJ]
  have hinit := TauCeti.MvPolynomial.adjoin_weightInitialForm_eq hcw hgw hker hb hQw hQc
  have hlead : Algebra.adjoin k (Set.range fun I ↦ monomial (a I) (1 : k)) =
      lex.initialAlgebra (Algebra.adjoin k (Set.range c)) := by
    rw [← hsagbi.adjoin_leadingTerm, ← Set.range_comp]
    congr 1
    apply congrArg Set.range
    funext I
    simp [MonomialOrder.leadingTerm, (hc_monic I).leadingCoeff_eq_one, a]
  have hinit' : Algebra.adjoin k (MvPolynomial.weightInitialForm w '' (A : Set _)) =
      lex.initialAlgebra A := by
    rw [← hadj]
    exact hinit.trans hlead
  have hd_eq : d = fun I ↦ Finsupp.weight w (flagDiagonalExponent I.val) :=
    funext fun I ↦ by simp [d, a, c]
  have hrees_eq : (TauCeti.MvPolynomial.weightReesAeval c
      (fun I ↦ Finsupp.weight w (flagDiagonalExponent I.val))).range =
      (A.weightReesAlgebra w).map (Polynomial.mapAlgHom A.val) := by
    rw [← hd_eq]
    exact (A.map_weightReesAlgebra_eq_range_weightReesAeval w hadj.symm
      hcw hgw hker hb hQw hQc).symm
  have htop : ∀ I : Finset (Fin n),
      MvPolynomial.weightInitialForm w (rename toLex (flagMinor k I)) =
        monomial (flagDiagonalExponent I) 1 ∧
      (rename toLex (flagMinor k I)).weightedTotalDegree w =
        Finsupp.weight w (flagDiagonalExponent I) := by
    intro I
    rcases I.eq_empty_or_nonempty with rfl | hI
    · have h0 : flagDiagonalExponent (∅ : Finset (Fin n)) = 0 := by
        rw [← degree_rename_toLex_flagMinor (R := k), flagMinor_empty, map_one, degree_one]
      rw [h0, map_zero, flagMinor_empty, map_one, monomial_zero', C_1,
        MvPolynomial.weightInitialForm_one]
      exact ⟨rfl, Nat.eq_zero_of_le_zero
        (TauCeti.MvPolynomial.mem_weightFiltration_iff_weightedTotalDegree_le.mp
          SetLike.GradedOne.one_mem)⟩
    · let J : {I : Finset (Fin n) // I.Nonempty} := ⟨I, hI⟩
      have hdeg_le : (c J).weightedTotalDegree w ≤ d J :=
        TauCeti.MvPolynomial.mem_weightFiltration_iff_weightedTotalDegree_le.mp (hcw J)
      have hdeg_eq : (c J).weightedTotalDegree w = d J := by
        refine le_antisymm hdeg_le (le_of_not_gt fun hlt ↦ ?_)
        have h0 := MvPolynomial.weightedHomogeneousComponent_eq_zero (d J) (c J) hlt
        rw [hgw J] at h0
        exact one_ne_zero (MvPolynomial.monomial_eq_zero.mp h0)
      have haJ : a J = flagDiagonalExponent I := degree_rename_toLex_flagMinor (R := k) I
      have hdJ : d J = Finsupp.weight w (flagDiagonalExponent I) := by simp [d, haJ]
      have hinit_J :
          MvPolynomial.weightInitialForm w (c J) = monomial (flagDiagonalExponent I) 1 := by
        rw [MvPolynomial.weightInitialForm_def, hdeg_eq, hgw J]
        exact congrArg (fun e ↦ monomial e (1 : k)) haJ
      exact ⟨hinit_J, by simpa [J, c, hdJ] using hdeg_eq⟩
  refine ⟨w, hw, htop, hinit', hrees_eq, ⟨A.flat_weightReesAlgebra w, ?_⟩, ?_⟩
  · let := TauCeti.coeffSubalgebra.algebra (A.weightFiltration w) (A.one_mem_weightFiltration_one w)
    let := Algebra.compHom k (Polynomial.evalRingHom (0 : k))
    let e0 : (k ⊗[k[X]] A.weightReesAlgebra w) ≃ₐ[k]
        AddMonoidAlgebra k (AddSubmonoid.nonneg (GTPattern n)) :=
      (A.weightReesAlgebraSpecialFiberEquiv w).trans
        ((Subalgebra.equivOfEq _ _ hinit').trans (initialAlgebraFlagMinorEquiv n k).symm)
    refine ⟨e0, fun I hIm ↦ ?_⟩
    rw [AlgEquiv.trans_apply, AlgEquiv.trans_apply, AlgEquiv.symm_apply_eq]
    apply Subtype.ext
    rw [Subalgebra.equivOfEq_apply, Subalgebra.coe_weightReesAlgebraSpecialFiberEquiv_tmul_monomial]
    have hcomp : weightedHomogeneousComponent w (Finsupp.weight w (flagDiagonalExponent I))
        (rename toLex (flagMinor k I)) = monomial (flagDiagonalExponent I) 1 := by
      rw [← (htop I).2, ← MvPolynomial.weightInitialForm_def, (htop I).1]
    rw [hcomp, coe_initialAlgebraFlagMinorEquiv_single,
      ← GTPattern.flagExponentEquiv_flagDiagonalExponent I, AddEquiv.symm_apply_apply]
  · let e1 := TauCeti.coeffSubalgebra.localizationAwayXEquivLaurent (A.weightFiltration w)
      (A.one_mem_weightFiltration_one w) (A.weightFiltration_mono w) (A.iSup_weightFiltration w)
    have he1 := TauCeti.coeffSubalgebra.localizationAwayXEquivLaurent_algebraMap_X
      (A.weightFiltration w) (A.one_mem_weightFiltration_one w) (A.weightFiltration_mono w)
      (A.iSup_weightFiltration w)
    let eA : A ≃ₐ[k] flagMinorAlgebra n k :=
      ((flagMinorAlgebra n k).equivMapOfInjective (rename toLex)
        (rename_injective _ toLex.injective)).symm
    refine ⟨e1.trans (AddMonoidAlgebra.mapAlgEquiv k ℤ eA), ?_⟩
    rw [AlgEquiv.trans_apply, he1]
    exact (AddMonoidAlgebra.mapAlgHom_single eA.toAlgHom 1 1).trans (by rw [map_one]; rfl)

end SAGBI

end TauCeti
