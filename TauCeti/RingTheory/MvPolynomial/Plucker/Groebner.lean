/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.Young.Rect
public import TauCeti.RingTheory.MvPolynomial.Groebner.NormalForm
public import TauCeti.RingTheory.MvPolynomial.Plucker.Basic
public import TauCeti.RingTheory.MvPolynomial.SAGBI.Basic
import TauCeti.Data.Finsupp.Multiset
import TauCeti.Data.Finsupp.Order

/-!
# Certified Gröbner basis, standard monomials and SAGBI basis for maximal minors

For the generic `n × d` matrix (`d ≠ 0`) over a commutative ring `R`,
`TauCeti.pluckerQuadrics R n d` is a Gröbner basis of `TauCeti.pluckerIdeal R n d` for
`TauCeti.MonomialOrder.degRevLex` on `TauCeti.pluckerVar I`, yielding:

* **Presentation, base change and initial ideal:** `TauCeti.pluckerIdeal_eq_span_pluckerQuadrics`,
  `TauCeti.map_pluckerIdeal`, `TauCeti.isHomogeneous_pluckerIdeal`, and
  `TauCeti.span_leadingTerm_pluckerIdeal`.
* **Tableau bijection & standard-monomial bases:** `TauCeti.pluckerTableauExponentEquiv`,
  `TauCeti.injOn_pluckerDiagonalWeight_isPluckerChainExponent`, `TauCeti.pluckerNormalForm`,
  `TauCeti.pluckerBasisQuotient`, and `TauCeti.pluckerBasisSubalgebra`.
* **Diagonal SAGBI basis (all `n, d`):** `TauCeti.isSAGBIBasis_range_rename_toLex_maximalMinor` and
  `TauCeti.leadingExponents_map_rename_toLex_maximalMinorSubalgebra`.

## References

* E. Miller and B. Sturmfels, *Combinatorial Commutative Algebra*, GTM 227, Springer, 2005, Ch. 14.
* W. Bruns and U. Vetter, *Determinantal Rings*, LNM 1327, Springer, 1988, Section 4.A.
* B. Sturmfels, *Gröbner Bases and Convex Polytopes*, ULS 8, AMS, 1996, Chapter 11.
-/

public section

namespace TauCeti

open MvPolynomial Finset
open scoped _root_.MonomialOrder

section ChainExponents

variable {n d : ℕ}

/-- An exponent on the Plücker variables is a **chain exponent** when any two row embeddings
occurring in its support are comparable in the componentwise order on `Fin d ↪o Fin n`. -/
def IsPluckerChainExponent (e : (Lex (Fin d ↪o Fin n))ᵒᵈ →₀ ℕ) : Prop :=
  ∀ ⦃I J : Fin d ↪o Fin n⦄, pluckerVar I ∈ e.support → pluckerVar J ∈ e.support → I ≤ J ∨ J ≤ I

theorem isPluckerChainExponent_def {e : (Lex (Fin d ↪o Fin n))ᵒᵈ →₀ ℕ} :
    IsPluckerChainExponent e ↔ ∀ ⦃I J : Fin d ↪o Fin n⦄,
      pluckerVar I ∈ e.support → pluckerVar J ∈ e.support → I ≤ J ∨ J ≤ I := Iff.rfl

@[simp]
theorem isPluckerChainExponent_zero :
    IsPluckerChainExponent (0 : (Lex (Fin d ↪o Fin n))ᵒᵈ →₀ ℕ) := by simp [IsPluckerChainExponent]

@[simp]
theorem isPluckerChainExponent_single (v : (Lex (Fin d ↪o Fin n))ᵒᵈ) (k : ℕ) :
    IsPluckerChainExponent (Finsupp.single v k) := fun _ _ hI hJ ↦
  Or.inl <| le_of_eq <| pluckerVar.injective <|
    (mem_singleton.1 (Finsupp.support_single_subset hI)).trans
      (mem_singleton.1 (Finsupp.support_single_subset hJ)).symm

/-- An exponent is a chain exponent iff it is not divisible by `X_I * X_J` for any pair `(I, J)`
with `toLex I < toLex J` and `¬ I ≤ J`. -/
theorem isPluckerChainExponent_iff_forall_not_le (e : (Lex (Fin d ↪o Fin n))ᵒᵈ →₀ ℕ) :
    IsPluckerChainExponent e ↔
      ∀ ⦃I J : Fin d ↪o Fin n⦄, ¬ I ≤ J → toLex I < toLex J →
        ¬ Finsupp.single (pluckerVar I) 1 + Finsupp.single (pluckerVar J) 1 ≤ e := by
  refine ⟨fun he I J hIJ hlt hle ↦ ?_, fun h I J hI hJ ↦ ?_⟩
  · obtain ⟨hI, hJ⟩ := (Finsupp.single_one_add_single_one_le_iff
      (fun hv ↦ hlt.ne (congrArg toLex (pluckerVar.injective hv)))).1 hle
    exact (OrderEmbedding.not_le_iff_not_le_or_ge_of_toLex_lt hlt).1 hIJ (he hI hJ)
  · have step {A B : Fin d ↪o Fin n} (hA : pluckerVar A ∈ e.support)
        (hB : pluckerVar B ∈ e.support) (hlt : toLex A < toLex B) : A ≤ B ∨ B ≤ A :=
      by_contra fun hinc ↦ h ((OrderEmbedding.not_le_iff_not_le_or_ge_of_toLex_lt hlt).2 hinc) hlt
        ((Finsupp.single_one_add_single_one_le_iff
          (fun hv ↦ hlt.ne (congrArg toLex (pluckerVar.injective hv)))).2 ⟨hA, hB⟩)
    rcases lt_trichotomy (toLex I) (toLex J) with hlt | heq | hlt
    · exact step hI hJ hlt
    · exact Or.inl (le_of_eq (toLex.injective heq))
    · exact (step hJ hI hlt).symm

/-- The Plücker exponent attached to a monotone chain `C : Fin m →o (Fin d ↪o Fin n)`: the sum of
the unit steps at the Plücker variables of its columns. -/
noncomputable def pluckerChainExponent {m : ℕ} (C : Fin m →o (Fin d ↪o Fin n)) :
    (Lex (Fin d ↪o Fin n))ᵒᵈ →₀ ℕ :=
  ∑ a : Fin m, Finsupp.single (pluckerVar (C a)) 1

theorem pluckerChainExponent_def {m : ℕ} (C : Fin m →o (Fin d ↪o Fin n)) :
    pluckerChainExponent C = ∑ a : Fin m, Finsupp.single (pluckerVar (C a)) 1 := (rfl)

@[simp]
theorem pluckerChainExponent_apply [DecidableEq (Fin d ↪o Fin n)] {m : ℕ}
    (C : Fin m →o (Fin d ↪o Fin n)) (I : Fin d ↪o Fin n) :
    pluckerChainExponent C (pluckerVar I) = #{a : Fin m | C a = I} := by
  classical
  rw [pluckerChainExponent_def, Finsupp.sum_single_one_apply]
  congr 1; ext a; simp [pluckerVar.injective.eq_iff]

@[simp]
theorem degree_pluckerChainExponent {m : ℕ} (C : Fin m →o (Fin d ↪o Fin n)) :
    (pluckerChainExponent C).degree = m := by simp [pluckerChainExponent_def]

@[simp]
theorem isPluckerChainExponent_pluckerChainExponent {m : ℕ} (C : Fin m →o (Fin d ↪o Fin n)) :
    IsPluckerChainExponent (pluckerChainExponent C) := by
  intro I J hI hJ
  rw [Finsupp.mem_support_iff, pluckerChainExponent_def, Finsupp.sum_single_one_apply_ne_zero_iff]
    at hI hJ
  obtain ⟨a₁, ha₁⟩ := hI; obtain ⟨a₂, ha₂⟩ := hJ
  have hI' := pluckerVar.injective ha₁; have hJ' := pluckerVar.injective ha₂
  exact (le_total a₁ a₂).imp (fun h ↦ hI' ▸ hJ' ▸ C.monotone h) fun h ↦ hJ' ▸ hI' ▸ C.monotone h

variable (n d) in
/-- Monotone chains `(m : ℕ) × (Fin m →o (Fin d ↪o Fin n))` correspond bijectively via
`pluckerChainExponent` to chain exponents `{e | IsPluckerChainExponent e}`. -/
noncomputable def pluckerChainExponentEquiv :
    ((m : ℕ) × (Fin m →o (Fin d ↪o Fin n))) ≃
      {e : (Lex (Fin d ↪o Fin n))ᵒᵈ →₀ ℕ | IsPluckerChainExponent e} :=
  Equiv.ofBijective
    (fun p ↦ ⟨pluckerChainExponent p.2, isPluckerChainExponent_pluckerChainExponent p.2⟩)
    ⟨by rintro ⟨m₁, C₁⟩ ⟨m₂, C₂⟩ h
        have heq : pluckerChainExponent C₁ = pluckerChainExponent C₂ := congrArg Subtype.val h
        obtain rfl : m₁ = m₂ := by simpa using congrArg Finsupp.degree heq
        classical
        exact Sigma.ext rfl (heq_of_eq (DFunLike.coe_injective
          (Monotone.eq_of_card_filter_eq C₁.monotone C₂.monotone fun I ↦ by
            simpa only [pluckerChainExponent_apply] using
              congrArg (fun e ↦ e (pluckerVar I)) heq))),
     by rintro ⟨e, he⟩
        obtain ⟨f', hf'⟩ :=
          (Finsupp.exists_sum_single_eq_iff (n := e.degree) e).2 (Finsupp.degree_apply e).symm
        set f : Fin e.degree → Fin d ↪o Fin n := fun a ↦ pluckerVar.symm (f' a)
        set σ := Tuple.sort (toLex ∘ f)
        have hmem (a : Fin e.degree) : pluckerVar (f (σ a)) ∈ e.support :=
          Finsupp.mem_support_iff.2 (congrArg (· (pluckerVar (f (σ a)))) hf' ▸
            Finsupp.sum_single_one_apply_ne_zero_iff.2 ⟨σ a, by simp [f]⟩)
        refine ⟨⟨e.degree, ⟨f ∘ σ, fun a₁ a₂ ha ↦
            (OrderEmbedding.le_iff_toLex_le_of_le_or_ge (he (hmem a₁) (hmem a₂))).2
              (Tuple.monotone_sort (toLex ∘ f) ha)⟩⟩, Subtype.ext ?_⟩
        simp only [pluckerChainExponent_def]
        exact (Equiv.sum_comp σ fun a ↦ Finsupp.single (pluckerVar (f a)) 1).trans
          (by simpa [f] using hf')⟩

@[simp]
theorem coe_pluckerChainExponentEquiv_apply {m : ℕ} (C : Fin m →o (Fin d ↪o Fin n)) :
    (pluckerChainExponentEquiv n d ⟨m, C⟩ : (Lex (Fin d ↪o Fin n))ᵒᵈ →₀ ℕ) =
      pluckerChainExponent C := (rfl)

variable (n d) in
/-- **Tableau parametrization of chain exponents.** Pairs `(m, T)` of a width `m : ℕ` and a bounded
semistandard Young tableau `T : BoundedSSYT n (YoungDiagram.rect d m)` correspond bijectively to
chain exponents via `BoundedSSYT.rectColsEquiv` and `pluckerChainExponentEquiv`. -/
noncomputable def pluckerTableauExponentEquiv :
    ((m : ℕ) × BoundedSSYT n (YoungDiagram.rect d m)) ≃
      {e : (Lex (Fin d ↪o Fin n))ᵒᵈ →₀ ℕ | IsPluckerChainExponent e} :=
  (Equiv.sigmaCongrRight (BoundedSSYT.rectColsEquiv n d)).symm.trans (pluckerChainExponentEquiv n d)

@[simp]
theorem coe_pluckerTableauExponentEquiv_apply {m : ℕ}
    (T : BoundedSSYT n (YoungDiagram.rect d m)) :
    (pluckerTableauExponentEquiv n d ⟨m, T⟩ : (Lex (Fin d ↪o Fin n))ᵒᵈ →₀ ℕ) =
      pluckerChainExponent ((BoundedSSYT.rectColsEquiv n d m).symm T) := (rfl)

end ChainExponents

section DiagonalWeight

variable (n d : ℕ)

/-- The diagonal-exponent weight map sending a Plücker exponent `e` to the sum of the diagonal
exponents `maximalMinorDiagonalExponent I` weighted by `e (pluckerVar I)`. -/
noncomputable def pluckerDiagonalWeight :
    ((Lex (Fin d ↪o Fin n))ᵒᵈ →₀ ℕ) →ₗ[ℕ] (Fin n ×ₗ Fin d →₀ ℕ) :=
  Finsupp.linearCombination ℕ fun v ↦ maximalMinorDiagonalExponent (pluckerVar.symm v)

theorem pluckerDiagonalWeight_def :
    pluckerDiagonalWeight n d =
      Finsupp.linearCombination ℕ fun v ↦ maximalMinorDiagonalExponent (pluckerVar.symm v) := (rfl)

variable {n d}

@[simp]
theorem pluckerDiagonalWeight_single (v : (Lex (Fin d ↪o Fin n))ᵒᵈ) (k : ℕ) :
    pluckerDiagonalWeight n d (Finsupp.single v k) =
      k • maximalMinorDiagonalExponent (pluckerVar.symm v) := by simp [pluckerDiagonalWeight]

theorem pluckerDiagonalWeight_single_pluckerVar (I : Fin d ↪o Fin n) (k : ℕ) :
    pluckerDiagonalWeight n d (Finsupp.single (pluckerVar I) k) =
      k • maximalMinorDiagonalExponent I := by simp

@[simp]
theorem degree_pluckerDiagonalWeight (e : (Lex (Fin d ↪o Fin n))ᵒᵈ →₀ ℕ) :
    (pluckerDiagonalWeight n d e).degree = e.degree * d := by
  induction e using Finsupp.induction_linear with
  | zero | single => simp
  | add e₁ e₂ ih₁ ih₂ =>
    simp only [Finsupp.degree_eq_weight_one] at ih₁ ih₂ ⊢; simp [ih₁, ih₂, add_mul]

@[simp]
theorem pluckerDiagonalWeight_pluckerChainExponent {m : ℕ} (C : Fin m →o (Fin d ↪o Fin n)) :
    pluckerDiagonalWeight n d (pluckerChainExponent C) =
      ∑ a : Fin m, maximalMinorDiagonalExponent (C a) := by
  simp [pluckerChainExponent_def, map_sum]

theorem pluckerDiagonalWeight_pluckerChainExponent_apply {m : ℕ} (C : Fin m →o (Fin d ↪o Fin n))
    (r : Fin n) (c : Fin d) :
    pluckerDiagonalWeight n d (pluckerChainExponent C) (toLex (r, c)) =
      #{a : Fin m | C a c = r} := by
  rw [pluckerDiagonalWeight_pluckerChainExponent, Finsupp.finsetSum_apply, card_filter]
  exact sum_congr rfl fun a _ ↦ maximalMinorDiagonalExponent_apply (C a) r c

theorem degree_pluckerDiagonalWeight_pluckerChainExponent {m : ℕ}
    (C : Fin m →o (Fin d ↪o Fin n)) :
    (pluckerDiagonalWeight n d (pluckerChainExponent C)).degree = m * d := by simp

/-- **Distinct diagonal leading exponents.** When `d ≠ 0`, distinct chain exponents have distinct
diagonal weights in `Fin n ×ₗ Fin d →₀ ℕ`. -/
theorem injOn_pluckerDiagonalWeight_isPluckerChainExponent [NeZero d] :
    Set.InjOn (pluckerDiagonalWeight n d) {e | IsPluckerChainExponent e} := by
  intro e₁ he₁ e₂ he₂ h
  obtain ⟨⟨m₁, C₁⟩, h₁⟩ := (pluckerChainExponentEquiv n d).surjective ⟨e₁, he₁⟩
  obtain ⟨⟨m₂, C₂⟩, h₂⟩ := (pluckerChainExponentEquiv n d).surjective ⟨e₂, he₂⟩
  have he₁' : pluckerChainExponent C₁ = e₁ :=
    (coe_pluckerChainExponentEquiv_apply C₁).symm.trans (congrArg Subtype.val h₁)
  have he₂' : pluckerChainExponent C₂ = e₂ :=
    (coe_pluckerChainExponentEquiv_apply C₂).symm.trans (congrArg Subtype.val h₂)
  rw [← he₁', ← he₂'] at h ⊢
  obtain rfl : m₁ = m₂ := Nat.eq_of_mul_eq_mul_right (NeZero.pos d) <| by
    simpa only [degree_pluckerDiagonalWeight_pluckerChainExponent] using congrArg Finsupp.degree h
  classical
  have hcol (c : Fin d) : (fun a ↦ C₁ a c) = fun a ↦ C₂ a c :=
    Monotone.eq_of_card_filter_eq (fun _ _ ha ↦ C₁.monotone ha c) (fun _ _ ha ↦ C₂.monotone ha c)
      fun r ↦ by
        simpa only [pluckerDiagonalWeight_pluckerChainExponent_apply] using
          congrArg (fun w ↦ w (toLex (r, c))) h
  exact congrArg pluckerChainExponent (by ext a c; exact congrArg Fin.val (congrFun (hcol c) a))

end DiagonalWeight

section Groebner

variable (R : Type*) [CommRing R] (n d : ℕ)

private theorem linearCombination_degree_rename_toLex_maximalMinor [Nontrivial R] :
    (Finsupp.linearCombination ℕ fun v : (Lex (Fin d ↪o Fin n))ᵒᵈ ↦
      _root_.MonomialOrder.lex.degree (rename toLex (maximalMinor R (pluckerVar.symm v)))) =
      pluckerDiagonalWeight n d := by ext v; simp

/-- For `d ≠ 0` and nonzero `r` supported on `{e | IsPluckerChainExponent e}`, the `lex` leading
exponent and coefficient of `rename toLex (pluckerEval R n d r)` come from some `e₀ ∈ r.support`. -/
theorem exists_mem_support_degree_rename_toLex_pluckerEval_eq_and_leadingCoeff_eq [NeZero d]
    {r : MvPolynomial (Lex (Fin d ↪o Fin n))ᵒᵈ R}
    (hr : r ∈ restrictSupport R {e | IsPluckerChainExponent e}) (hr0 : r ≠ 0) :
    ∃ e₀ ∈ r.support,
      _root_.MonomialOrder.lex.degree (rename toLex (pluckerEval R n d r)) =
        pluckerDiagonalWeight n d e₀ ∧
      _root_.MonomialOrder.lex.leadingCoeff (rename toLex (pluckerEval R n d r)) =
        r.coeff e₀ := by
  have : Nontrivial R := not_subsingleton_iff_nontrivial.1 fun _ ↦ hr0 (Subsingleton.elim _ _)
  rw [pluckerEval_def, comp_aeval_apply]
  have hlin := linearCombination_degree_rename_toLex_maximalMinor R n d
  simpa only [Function.comp_def, hlin] using
    _root_.MonomialOrder.lex.exists_mem_support_degree_aeval_eq_and_leadingCoeff_eq
      (fun v ↦ monic_rename_toLex_maximalMinor R (pluckerVar.symm v))
      (hlin.symm ▸ injOn_pluckerDiagonalWeight_isPluckerChainExponent.mono
        ((mem_restrictSupport_iff R).1 hr)) hr0

/-- For `d ≠ 0` and nonzero `r` supported on chain exponents,
`rename toLex (pluckerEval R n d r) ≠ 0`. -/
theorem rename_toLex_pluckerEval_ne_zero [NeZero d]
    {r : MvPolynomial (Lex (Fin d ↪o Fin n))ᵒᵈ R}
    (hr : r ∈ restrictSupport R {e | IsPluckerChainExponent e}) (hr0 : r ≠ 0) :
    rename toLex (pluckerEval R n d r) ≠ 0 := by
  obtain ⟨e₀, he₀, -, hlc⟩ :=
    exists_mem_support_degree_rename_toLex_pluckerEval_eq_and_leadingCoeff_eq R n d hr hr0
  exact fun h0 ↦ MvPolynomial.mem_support_iff.1 he₀ (by simpa [h0] using hlc.symm)

/-- **Linear independence of chain monomials.** Over any commutative ring `R`, when `d ≠ 0`, no
nonzero polynomial supported on `{e | IsPluckerChainExponent e}` lies in `pluckerIdeal R n d`. -/
theorem eq_zero_of_mem_restrictSupport_isPluckerChainExponent_of_mem_pluckerIdeal [NeZero d]
    {r : MvPolynomial (Lex (Fin d ↪o Fin n))ᵒᵈ R}
    (hr : r ∈ restrictSupport R {e | IsPluckerChainExponent e})
    (hmem : r ∈ pluckerIdeal R n d) : r = 0 :=
  by_contra fun hr0 ↦ rename_toLex_pluckerEval_ne_zero R n d hr hr0
    (by rw [(mem_pluckerIdeal_iff R).1 hmem, map_zero])

private theorem mem_restrictSupport_of_isRemainder_pluckerQuadrics
    {f r : MvPolynomial (Lex (Fin d ↪o Fin n))ᵒᵈ R}
    (hr : MonomialOrder.degRevLex.IsRemainder f (pluckerQuadrics R n d) r) :
    r ∈ restrictSupport R {e | IsPluckerChainExponent e} :=
  (subsingleton_or_nontrivial R).elim (fun _ ↦ Subsingleton.elim r 0 ▸ zero_mem _) fun _ ↦
    (mem_restrictSupport_iff R).2 fun e he ↦
      (isPluckerChainExponent_iff_forall_not_le e).2 fun _ _ hIJ hlt ↦
        degree_pluckerQuadric R hIJ hlt ▸ hr.not_degree_le he
          (mem_pluckerQuadrics_iff.2 ⟨_, _, hIJ, hlt, rfl⟩) (monic_pluckerQuadric R hIJ hlt).ne_zero

private theorem pluckerQuadrics_isUnit_leadingCoeff :
    ∀ g ∈ pluckerQuadrics R n d, g ≠ 0 → IsUnit (MonomialOrder.degRevLex.leadingCoeff g) :=
  fun _ hg _ ↦ (monic_of_mem_pluckerQuadrics hg).leadingCoeff_eq_one ▸ isUnit_one

/-- **Certified Gröbner basis of the Plücker ideal.** Over any commutative ring `R`, when `d ≠ 0`,
`pluckerQuadrics R n d` is a Gröbner basis of `pluckerIdeal R n d` for
`TauCeti.MonomialOrder.degRevLex`. -/
theorem isGroebnerBasis_pluckerQuadrics [NeZero d] :
    MonomialOrder.degRevLex.IsGroebnerBasis (pluckerQuadrics R n d) (pluckerIdeal R n d) := by
  refine _root_.MonomialOrder.isGroebnerBasis_iff_isRemainder_zero.2
    ⟨pluckerQuadrics_subset_pluckerIdeal R n d, fun f hf ↦ ?_⟩
  obtain ⟨r, hr⟩ := _root_.MonomialOrder.exists_isRemainder
    (pluckerQuadrics_isUnit_leadingCoeff R n d) f
  exact eq_zero_of_mem_restrictSupport_isPluckerChainExponent_of_mem_pluckerIdeal R n d
    (mem_restrictSupport_of_isRemainder_pluckerQuadrics R n d hr)
    (by simpa only [sub_sub_cancel] using ((pluckerIdeal R n d).sub_mem hf
      (Ideal.span_le.2 (pluckerQuadrics_subset_pluckerIdeal R n d) hr.sub_mem_span))) ▸ hr

/-- **Polynomial presentation of the Plücker ideal.** For `d ≠ 0`, `pluckerIdeal R n d` is generated
by `pluckerQuadrics R n d` over every commutative ring `R`. -/
theorem pluckerIdeal_eq_span_pluckerQuadrics [NeZero d] :
    pluckerIdeal R n d = Ideal.span (pluckerQuadrics R n d) :=
  (isGroebnerBasis_pluckerQuadrics R n d).ideal_eq_span

/-- **Base change of the Plücker ideal.** `pluckerIdeal` commutes with arbitrary ring homomorphisms
for all `n` and `d`. -/
theorem map_pluckerIdeal {R S : Type*} [CommRing R] [CommRing S] (φ : R →+* S) (n d : ℕ) :
    Ideal.map (MvPolynomial.map φ) (pluckerIdeal R n d) = pluckerIdeal S n d := by
  rcases eq_or_ne d 0 with rfl | hd
  · simp [pluckerIdeal_zero, Ideal.map_span]
  · have : NeZero d := ⟨hd⟩
    rw [pluckerIdeal_eq_span_pluckerQuadrics R n d, pluckerIdeal_eq_span_pluckerQuadrics S n d,
      Ideal.map_span, image_map_pluckerQuadrics]

attribute [local instance] MvPolynomial.gradedAlgebra in
/-- For `d ≠ 0`, `pluckerIdeal R n d` is homogeneous for the standard total-degree grading. -/
theorem isHomogeneous_pluckerIdeal [NeZero d] :
    (pluckerIdeal R n d).IsHomogeneous (homogeneousSubmodule (Lex (Fin d ↪o Fin n))ᵒᵈ R) :=
  pluckerIdeal_eq_span_pluckerQuadrics R n d ▸ Ideal.homogeneous_span _ _ fun _ hg ↦ by
    obtain ⟨_, _, hIJ, -, rfl⟩ := mem_pluckerQuadrics_iff.1 hg
    exact ⟨2, isHomogeneous_pluckerQuadric R hIJ⟩

/-- The `degRevLex` leading terms of `pluckerQuadrics R n d` are the quadratic monomials
`X (pluckerVar I) * X (pluckerVar J)` for componentwise incomparable `(I, J)`. -/
theorem image_leadingTerm_pluckerQuadrics :
    MonomialOrder.degRevLex.leadingTerm '' pluckerQuadrics R n d =
      {m | ∃ I J : Fin d ↪o Fin n,
        ¬ (I ≤ J ∨ J ≤ I) ∧ X (pluckerVar I) * X (pluckerVar J) = m} := by
  ext m
  simp only [Set.mem_image, mem_pluckerQuadrics_iff, Set.mem_ofPred_eq]
  refine ⟨by rintro ⟨_, ⟨I, J, hIJ, hlt, rfl⟩, rfl⟩
             exact ⟨I, J, (OrderEmbedding.not_le_iff_not_le_or_ge_of_toLex_lt hlt).1 hIJ,
               (leadingTerm_pluckerQuadric hIJ hlt).symm⟩, ?_⟩
  rintro ⟨I, J, hinc, rfl⟩
  rcases lt_or_gt_of_ne (fun h ↦ hinc (Or.inl (le_of_eq (toLex.injective h)))) with hlt | hlt
  · have hIJ := (OrderEmbedding.not_le_iff_not_le_or_ge_of_toLex_lt hlt).2 hinc
    exact ⟨_, ⟨I, J, hIJ, hlt, rfl⟩, leadingTerm_pluckerQuadric hIJ hlt⟩
  · have hJI := (OrderEmbedding.not_le_iff_not_le_or_ge_of_toLex_lt hlt).2 (Or.symm.mt hinc)
    exact ⟨_, ⟨J, I, hJI, hlt, rfl⟩, (leadingTerm_pluckerQuadric hJI hlt).trans (mul_comm _ _)⟩

/-- **Initial ideal of the Plücker ideal.** For `d ≠ 0`, the `degRevLex` initial ideal of
`pluckerIdeal R n d` is generated by `X (pluckerVar I) * X (pluckerVar J)` for incomparable
pairs `(I, J)`. -/
theorem span_leadingTerm_pluckerIdeal [NeZero d] :
    Ideal.span (MonomialOrder.degRevLex.leadingTerm ''
        (pluckerIdeal R n d : Set (MvPolynomial (Lex (Fin d ↪o Fin n))ᵒᵈ R))) =
      Ideal.span {m | ∃ I J : Fin d ↪o Fin n,
        ¬ (I ≤ J ∨ J ≤ I) ∧ X (pluckerVar I) * X (pluckerVar J) = m} := by
  rw [(isGroebnerBasis_pluckerQuadrics R n d).span_leadingTerm_image,
    image_leadingTerm_pluckerQuadrics]

/-- Over a nontrivial ring with `d ≠ 0`, the `degRevLex` standard monomials of `pluckerIdeal R n d`
are the chain exponents. -/
theorem standardMonomials_pluckerIdeal [Nontrivial R] [NeZero d] :
    MonomialOrder.degRevLex.standardMonomials (pluckerIdeal R n d) =
      {e | IsPluckerChainExponent e} := by
  ext e
  rw [(isGroebnerBasis_pluckerQuadrics R n d).mem_standardMonomials_iff, Set.mem_ofPred_eq,
    isPluckerChainExponent_iff_forall_not_le]
  exact ⟨fun h _ _ hIJ hlt ↦ degree_pluckerQuadric R hIJ hlt ▸
      h _ (mem_pluckerQuadrics_iff.2 ⟨_, _, hIJ, hlt, rfl⟩)
        (monic_pluckerQuadric R hIJ hlt).ne_zero,
    fun h _ hg _ ↦ by
      obtain ⟨_, _, hIJ, hlt, rfl⟩ := mem_pluckerQuadrics_iff.1 hg
      exact degree_pluckerQuadric R hIJ hlt ▸ h hIJ hlt⟩

end Groebner

section StandardMonomialBasis

variable (R : Type*) [CommRing R] (n d : ℕ) [NeZero d]

private theorem restrictSupport_standardMonomials_pluckerIdeal :
    restrictSupport R (MonomialOrder.degRevLex.standardMonomials (pluckerIdeal R n d)) =
      restrictSupport R {e : (Lex (Fin d ↪o Fin n))ᵒᵈ →₀ ℕ | IsPluckerChainExponent e} :=
  (subsingleton_or_nontrivial R).elim
    (fun _ ↦ Submodule.ext fun p ↦ by simp [Subsingleton.elim p 0])
    fun _ ↦ by rw [standardMonomials_pluckerIdeal]

/-- For `d ≠ 0`, the quotient map restricts to an `R`-linear isomorphism from polynomials supported
on `{e | IsPluckerChainExponent e}` onto the quotient modulo `pluckerIdeal R n d`. -/
noncomputable def restrictSupportEquivQuotientPluckerIdeal :
    restrictSupport R {e : (Lex (Fin d ↪o Fin n))ᵒᵈ →₀ ℕ | IsPluckerChainExponent e} ≃ₗ[R]
      MvPolynomial (Lex (Fin d ↪o Fin n))ᵒᵈ R ⧸ pluckerIdeal R n d :=
  (LinearEquiv.ofEq _ _ (restrictSupport_standardMonomials_pluckerIdeal R n d).symm).trans
    ((isGroebnerBasis_pluckerQuadrics R n d).restrictSupportEquivQuotient
      (pluckerQuadrics_isUnit_leadingCoeff R n d))

@[simp]
theorem restrictSupportEquivQuotientPluckerIdeal_apply
    (r : restrictSupport R {e : (Lex (Fin d ↪o Fin n))ᵒᵈ →₀ ℕ | IsPluckerChainExponent e}) :
    restrictSupportEquivQuotientPluckerIdeal R n d r =
      Ideal.Quotient.mk (pluckerIdeal R n d) (r : MvPolynomial _ R) := by
  simp [restrictSupportEquivQuotientPluckerIdeal]

/-- **Straightening normal form** modulo `pluckerIdeal R n d` (`d ≠ 0`): the `R`-linear map sending
`f` to the unique polynomial supported on `{e | IsPluckerChainExponent e}` congruent to `f` modulo
`pluckerIdeal R n d`. -/
noncomputable def pluckerNormalForm :
    MvPolynomial (Lex (Fin d ↪o Fin n))ᵒᵈ R →ₗ[R] MvPolynomial (Lex (Fin d ↪o Fin n))ᵒᵈ R :=
  (isGroebnerBasis_pluckerQuadrics R n d).normalForm (pluckerQuadrics_isUnit_leadingCoeff R n d)

@[simp]
theorem coe_restrictSupportEquivQuotientPluckerIdeal_symm_mk
    (f : MvPolynomial (Lex (Fin d ↪o Fin n))ᵒᵈ R) :
    ((restrictSupportEquivQuotientPluckerIdeal R n d).symm
        (Ideal.Quotient.mk (pluckerIdeal R n d) f) : MvPolynomial (Lex (Fin d ↪o Fin n))ᵒᵈ R) =
      pluckerNormalForm R n d f := by
  simp [restrictSupportEquivQuotientPluckerIdeal, pluckerNormalForm]

@[simp]
theorem pluckerNormalForm_mem_restrictSupport (f : MvPolynomial (Lex (Fin d ↪o Fin n))ᵒᵈ R) :
    pluckerNormalForm R n d f ∈
      restrictSupport R {e : (Lex (Fin d ↪o Fin n))ᵒᵈ →₀ ℕ | IsPluckerChainExponent e} :=
  restrictSupport_standardMonomials_pluckerIdeal R n d ▸
    (isGroebnerBasis_pluckerQuadrics R n d).normalForm_mem_restrictSupport _ f

@[simp]
theorem mk_pluckerNormalForm (f : MvPolynomial (Lex (Fin d ↪o Fin n))ᵒᵈ R) :
    Ideal.Quotient.mk (pluckerIdeal R n d) (pluckerNormalForm R n d f) =
      Ideal.Quotient.mk (pluckerIdeal R n d) f :=
  (isGroebnerBasis_pluckerQuadrics R n d).mk_normalForm _ f

theorem sub_pluckerNormalForm_mem (f : MvPolynomial (Lex (Fin d ↪o Fin n))ᵒᵈ R) :
    f - pluckerNormalForm R n d f ∈ pluckerIdeal R n d :=
  (isGroebnerBasis_pluckerQuadrics R n d).sub_normalForm_mem _ f

@[simp]
theorem pluckerEval_pluckerNormalForm (f : MvPolynomial (Lex (Fin d ↪o Fin n))ᵒᵈ R) :
    pluckerEval R n d (pluckerNormalForm R n d f) = pluckerEval R n d f :=
  (sub_eq_zero.1 <| map_sub (pluckerEval R n d) f _ ▸
    (mem_pluckerIdeal_iff R).1 (sub_pluckerNormalForm_mem R n d f)).symm

/-- `pluckerNormalForm R n d f` is the unique chain-supported polynomial congruent to `f` modulo
`pluckerIdeal R n d`. -/
theorem pluckerNormalForm_eq_iff {f r : MvPolynomial (Lex (Fin d ↪o Fin n))ᵒᵈ R} :
    pluckerNormalForm R n d f = r ↔
      r ∈ restrictSupport R {e | IsPluckerChainExponent e} ∧ f - r ∈ pluckerIdeal R n d :=
  restrictSupport_standardMonomials_pluckerIdeal R n d ▸
    (isGroebnerBasis_pluckerQuadrics R n d).normalForm_eq_iff _

@[simp]
theorem pluckerNormalForm_of_mem_restrictSupport {r : MvPolynomial (Lex (Fin d ↪o Fin n))ᵒᵈ R}
    (hr : r ∈ restrictSupport R {e | IsPluckerChainExponent e}) :
    pluckerNormalForm R n d r = r :=
  (isGroebnerBasis_pluckerQuadrics R n d).normalForm_of_mem_restrictSupport _
    (restrictSupport_standardMonomials_pluckerIdeal R n d ▸ hr)

/-- **Plücker ideal membership.** `pluckerNormalForm R n d f = 0` iff `f ∈ pluckerIdeal R n d`. -/
@[simp]
theorem pluckerNormalForm_eq_zero_iff {f : MvPolynomial (Lex (Fin d ↪o Fin n))ᵒᵈ R} :
    pluckerNormalForm R n d f = 0 ↔ f ∈ pluckerIdeal R n d :=
  (isGroebnerBasis_pluckerQuadrics R n d).normalForm_eq_zero_iff _

/-- For `d ≠ 0`, remainders of `f` modulo `pluckerQuadrics R n d` equal
`pluckerNormalForm R n d f`. -/
theorem isRemainder_pluckerQuadrics_iff_eq_pluckerNormalForm
    {f r : MvPolynomial (Lex (Fin d ↪o Fin n))ᵒᵈ R} :
    MonomialOrder.degRevLex.IsRemainder f (pluckerQuadrics R n d) r ↔
      r = pluckerNormalForm R n d f :=
  (isGroebnerBasis_pluckerQuadrics R n d).isRemainder_iff_eq_normalForm _

/-- **Standard-monomial basis of the Plücker quotient.** For `d ≠ 0`,
`(m : ℕ) × BoundedSSYT n (YoungDiagram.rect d m)` indexes an `R`-basis of
`MvPolynomial (Lex (Fin d ↪o Fin n))ᵒᵈ R ⧸ pluckerIdeal R n d`. -/
noncomputable def pluckerBasisQuotient :
    Module.Basis ((m : ℕ) × BoundedSSYT n (YoungDiagram.rect d m)) R
      (MvPolynomial (Lex (Fin d ↪o Fin n))ᵒᵈ R ⧸ pluckerIdeal R n d) :=
  open Classical in if hR : Nontrivial R then
    ((isGroebnerBasis_pluckerQuadrics R n d).basisQuotient
        (pluckerQuadrics_isUnit_leadingCoeff R n d)).reindex
      ((Set.equivOfEq (standardMonomials_pluckerIdeal R n d)).trans
        (pluckerTableauExponentEquiv n d).symm)
  else letI : Subsingleton R := not_nontrivial_iff_subsingleton.1 hR; default

@[simp]
theorem pluckerBasisQuotient_apply (p : (m : ℕ) × BoundedSSYT n (YoungDiagram.rect d m)) :
    pluckerBasisQuotient R n d p =
      Ideal.Quotient.mk (pluckerIdeal R n d)
        (∏ c : Fin p.1, X (pluckerVar ((BoundedSSYT.rectColsEquiv n d p.1).symm p.2 c))) := by
  nontriviality R; rcases p with ⟨m, T⟩
  simp [pluckerBasisQuotient, dite_eq_left ‹Nontrivial R›, pluckerChainExponent_def,
    monomial_sum_one, X]

@[simp]
theorem pluckerBasisQuotient_repr_mk (f : MvPolynomial (Lex (Fin d ↪o Fin n))ᵒᵈ R)
    (p : (m : ℕ) × BoundedSSYT n (YoungDiagram.rect d m)) :
    (pluckerBasisQuotient R n d).repr (Ideal.Quotient.mk (pluckerIdeal R n d) f) p =
      (pluckerNormalForm R n d f).coeff (pluckerTableauExponentEquiv n d p) := by
  nontriviality R; simp [pluckerBasisQuotient, pluckerNormalForm, dite_eq_left ‹Nontrivial R›]

/-- **Standard-monomial basis of the maximal-minor subalgebra.** For `d ≠ 0`,
`(m : ℕ) × BoundedSSYT n (YoungDiagram.rect d m)` indexes an `R`-basis of
`maximalMinorSubalgebra R n d`, sending `(m, T)` to the product of its column maximal minors. -/
noncomputable def pluckerBasisSubalgebra :
    Module.Basis ((m : ℕ) × BoundedSSYT n (YoungDiagram.rect d m)) R
      (maximalMinorSubalgebra R n d) :=
  (pluckerBasisQuotient R n d).map (quotientPluckerIdealAlgEquiv R n d).toLinearEquiv

@[simp]
theorem coe_pluckerBasisSubalgebra_apply (p : (m : ℕ) × BoundedSSYT n (YoungDiagram.rect d m)) :
    (pluckerBasisSubalgebra R n d p : MvPolynomial (Fin n × Fin d) R) =
      ∏ c : Fin p.1, maximalMinor R ((BoundedSSYT.rectColsEquiv n d p.1).symm p.2 c) := by
  simp [pluckerBasisSubalgebra]

theorem pluckerBasisSubalgebra_repr_apply (x : maximalMinorSubalgebra R n d) :
    (pluckerBasisSubalgebra R n d).repr x =
      (pluckerBasisQuotient R n d).repr ((quotientPluckerIdealAlgEquiv R n d).symm x) := (rfl)

@[simp]
theorem pluckerBasisSubalgebra_repr_pluckerEval (f : MvPolynomial (Lex (Fin d ↪o Fin n))ᵒᵈ R)
    (hf : pluckerEval R n d f ∈ maximalMinorSubalgebra R n d)
    (p : (m : ℕ) × BoundedSSYT n (YoungDiagram.rect d m)) :
    (pluckerBasisSubalgebra R n d).repr ⟨pluckerEval R n d f, hf⟩ p =
      (pluckerNormalForm R n d f).coeff (pluckerTableauExponentEquiv n d p) := by
  have h : ⟨pluckerEval R n d f, hf⟩ =
      quotientPluckerIdealAlgEquiv R n d (Ideal.Quotient.mk _ f) :=
    Subtype.ext (coe_quotientPluckerIdealAlgEquiv_mk R n d f).symm
  simp [pluckerBasisSubalgebra, h]

end StandardMonomialBasis

section SAGBI

variable (R : Type*) [CommRing R] (n d : ℕ)

/-- Mapping `maximalMinorSubalgebra R n d` along `rename toLex` gives the subalgebra generated by
the `toLex`-renamed maximal minors. -/
theorem map_rename_toLex_maximalMinorSubalgebra :
    (maximalMinorSubalgebra R n d).map (rename (toLex : Fin n × Fin d → Fin n ×ₗ Fin d)) =
      Algebra.adjoin R (Set.range fun I : Fin d ↪o Fin n ↦ rename toLex (maximalMinor R I)) := by
  rw [maximalMinorSubalgebra_def, AlgHom.map_adjoin, ← Set.range_comp]; rfl

private theorem exists_chain_degree_eq_of_mem_map_maximalMinorSubalgebra
    {p : MvPolynomial (Fin n ×ₗ Fin d) R}
    (hp : p ∈ (maximalMinorSubalgebra R n d).map
      (rename (toLex : Fin n × Fin d → Fin n ×ₗ Fin d)))
    (hp0 : p ≠ 0) :
    ∃ (m : ℕ) (C : Fin m →o (Fin d ↪o Fin n)),
      _root_.MonomialOrder.lex.degree p = ∑ a : Fin m, maximalMinorDiagonalExponent (C a) := by
  rcases eq_or_ne d 0 with rfl | hd
  · rw [maximalMinorSubalgebra_zero, Subalgebra.mem_map] at hp
    obtain ⟨_, hq, rfl⟩ := hp; obtain ⟨c, rfl⟩ := Algebra.mem_bot.1 hq
    exact ⟨0, ⟨Fin.elim0, fun a ↦ Fin.elim0 a⟩, by simp [algebraMap_eq]⟩
  · have : NeZero d := ⟨hd⟩
    obtain ⟨q, hq, rfl⟩ := Subalgebra.mem_map.1 hp
    obtain ⟨⟨r, hrsupp⟩, hr⟩ := ((restrictSupportEquivQuotientPluckerIdeal R n d).trans
      (quotientPluckerIdealAlgEquiv R n d).toLinearEquiv).surjective ⟨q, hq⟩
    have hrq : pluckerEval R n d r = q := by simpa using congrArg Subtype.val hr
    obtain ⟨e₀, he₀, hdeg, -⟩ :=
      exists_mem_support_degree_rename_toLex_pluckerEval_eq_and_leadingCoeff_eq R n d hrsupp
        (fun h0 ↦ hp0 (by simp [← hrq, h0]))
    obtain ⟨⟨m, C⟩, hC⟩ := (pluckerChainExponentEquiv n d).surjective
      ⟨e₀, (mem_restrictSupport_iff R).1 hrsupp he₀⟩
    have he₀' : pluckerChainExponent C = e₀ :=
      (coe_pluckerChainExponentEquiv_apply C).symm.trans (congrArg Subtype.val hC)
    exact ⟨m, C, by rw [← hrq, hdeg, ← he₀', pluckerDiagonalWeight_pluckerChainExponent]⟩

/-- **Diagonal SAGBI basis of maximal minors.** Over any commutative ring `R` and for all `n` and
`d`, the `toLex`-renamed maximal minors form a SAGBI basis for row-major `MonomialOrder.lex`. -/
theorem isSAGBIBasis_range_rename_toLex_maximalMinor :
    _root_.MonomialOrder.lex.IsSAGBIBasis
      (Set.range fun I : Fin d ↪o Fin n ↦ rename toLex (maximalMinor R I))
      (Algebra.adjoin R (Set.range fun I : Fin d ↪o Fin n ↦ rename toLex (maximalMinor R I))) := by
  refine _root_.MonomialOrder.isSAGBIBasis_iff_initialAlgebra_le.2 ⟨Algebra.subset_adjoin, ?_⟩
  rw [_root_.MonomialOrder.initialAlgebra_def]
  refine Algebra.adjoin_le fun _ ⟨p, hp, hp'⟩ ↦ hp' ▸ ?_
  rw [SetLike.mem_coe] at hp ⊢
  rcases eq_or_ne p 0 with rfl | hp0
  · simp
  rw [← map_rename_toLex_maximalMinorSubalgebra] at hp
  obtain ⟨m, C, hdeg⟩ := exists_chain_degree_eq_of_mem_map_maximalMinorSubalgebra R n d hp hp0
  rw [_root_.MonomialOrder.leadingTerm, hdeg, monomial_sum_index]
  exact Subalgebra.mul_mem _ (Subalgebra.algebraMap_mem _ _) (Subalgebra.prod_mem _ fun a _ ↦
    leadingTerm_rename_toLex_maximalMinor (R := R) (C a) ▸
      Algebra.subset_adjoin ⟨_, ⟨C a, rfl⟩, rfl⟩)

/-- Over a domain (any `[NoZeroDivisors R] [Nontrivial R]`), the `MonomialOrder.lex` leading
exponents of the `toLex`-renamed maximal-minor subalgebra form the additive submonoid generated by
`maximalMinorDiagonalExponent I`. -/
theorem leadingExponents_map_rename_toLex_maximalMinorSubalgebra [NoZeroDivisors R] [Nontrivial R] :
    _root_.MonomialOrder.lex.leadingExponents
        ((maximalMinorSubalgebra R n d).map (rename (toLex : Fin n × Fin d → Fin n ×ₗ Fin d))) =
      AddSubmonoid.closure (Set.range (maximalMinorDiagonalExponent (n := n) (d := d))) := by
  refine le_antisymm (fun a ha ↦ ?_) (AddSubmonoid.closure_le.2 ?_)
  · obtain ⟨p, hp, hp0, rfl⟩ := _root_.MonomialOrder.mem_leadingExponents_iff.1 ha
    obtain ⟨m, C, hdeg⟩ := exists_chain_degree_eq_of_mem_map_maximalMinorSubalgebra R n d hp hp0
    exact hdeg ▸ sum_mem fun a _ ↦ AddSubmonoid.subset_closure ⟨C a, rfl⟩
  · rintro _ ⟨I, rfl⟩
    exact degree_rename_toLex_maximalMinor (R := R) I ▸
      _root_.MonomialOrder.degree_mem_leadingExponents
        (Subalgebra.mem_map.2 ⟨maximalMinor R I, maximalMinor_mem_maximalMinorSubalgebra R I, rfl⟩)
        (monic_rename_toLex_maximalMinor R I).ne_zero

end SAGBI

end TauCeti
