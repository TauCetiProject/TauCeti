/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.GradedAlgebra.CoeffSubalgebra.Laurent
public import TauCeti.RingTheory.MvPolynomial.FlagMinor.SAGBI
public import TauCeti.RingTheory.MvPolynomial.Subalgebra.WeightFiltration
import TauCeti.Data.Finsupp.Weight

/-!
# Flat positive weight-Rees degeneration of the flag-minor algebra

Over any field `k`, the diagonal `lex`-SAGBI basis of `flagMinorAlgebra n k` from
`TauCeti.RingTheory.MvPolynomial.FlagMinor.SAGBI` can be realized by a strictly positive integral
weight `w : (Fin n ×ₗ Fin n) → ℕ`. With respect to `w`, the embedded weight-Rees algebra
`(A.weightReesAlgebra w)` of `A = (flagMinorAlgebra n k).map (rename toLex)` is presented by
`TauCeti.MvPolynomial.weightReesAeval` on the `2 ^ n - 1` nonempty flag minors, is flat over
`k[X]`, specializes at `t = 0` to `AddMonoidAlgebra k (AddSubmonoid.nonneg (GTPattern n))`, and
localizes away from `t` to `LaurentPolynomial (flagMinorAlgebra n k)`.

## Main results

* `TauCeti.exists_pos_weight_flagMinorAlgebra_degeneration`: existence of a strictly positive
  integral weight `w` realizing the flat one-parameter weight-Rees degeneration of
  `flagMinorAlgebra n k` to the Gelfand-Tsetlin semigroup algebra over any field `k`.

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

section Degeneration

variable {n : ℕ}

/-- The `2 ^ n - 1` nonempty flag minors generate `(flagMinorAlgebra n k).map (rename toLex)`
and form a `lex`-SAGBI basis of it. -/
private theorem adjoin_and_isSAGBIBasis_nonempty_flagMinor (k : Type*) [CommRing k] :
    let c : {I : Finset (Fin n) // I.Nonempty} → MvPolynomial (Fin n ×ₗ Fin n) k :=
      fun I ↦ rename toLex (flagMinor k I.val)
    Algebra.adjoin k (Set.range c) = (flagMinorAlgebra n k).map (rename toLex) ∧
      lex.IsSAGBIBasis (Set.range c) (Algebra.adjoin k (Set.range c)) := by
  intro c
  have hrange : Set.range c =
      (fun I : Finset (Fin n) ↦ rename toLex (flagMinor k I)) '' {I | I.Nonempty} := by
    ext p; simp [c]
  have hadj : Algebra.adjoin k (Set.range c) = (flagMinorAlgebra n k).map (rename toLex) := by
    rw [hrange, ← Set.image_image, ← AlgHom.map_adjoin, adjoin_flagMinor_nonempty]
  exact ⟨hadj, hadj ▸ hrange ▸ isSAGBIBasis_image_nonempty_rename_toLex_flagMinor k⟩

/-- Constructs a strictly positive integral weight `w` and a bounded SAGBI weight certificate on
the `2 ^ n - 1` nonempty flag minors over a field `k`. -/
private theorem exists_pos_weight_flagMinor_certificate (k : Type*) [Field k] :
    let c : {I : Finset (Fin n) // I.Nonempty} → MvPolynomial (Fin n ×ₗ Fin n) k :=
      fun I ↦ rename toLex (flagMinor k I.val)
    let a : {I : Finset (Fin n) // I.Nonempty} → Fin n ×ₗ Fin n →₀ ℕ :=
      fun I ↦ flagDiagonalExponent I.val
    ∃ (w : (Fin n ×ₗ Fin n) → ℕ) (ι : Type)
      (r Q : ι → MvPolynomial {I : Finset (Fin n) // I.Nonempty} k) (e : ι → ℕ),
      (∀ s, 0 < w s) ∧
      (∀ I, c I ∈ TauCeti.MvPolynomial.weightFiltration k w (Finsupp.weight w (a I))) ∧
      (∀ I, MvPolynomial.weightedHomogeneousComponent w (Finsupp.weight w (a I)) (c I) =
        monomial (a I) 1) ∧
      RingHom.ker (aeval fun I ↦ monomial (a I) (1 : k)) = Ideal.span (Set.range r) ∧
      (∀ j, (r j).IsWeightedHomogeneous (fun I ↦ Finsupp.weight w (a I)) (e j)) ∧
      (∀ j, Q j ∈ TauCeti.MvPolynomial.weightFiltrationLT k
        (fun I ↦ Finsupp.weight w (a I)) (e j)) ∧
      (∀ j, aeval c (Q j) = aeval c (r j)) := by
  classical
  let c : {I : Finset (Fin n) // I.Nonempty} → MvPolynomial (Fin n ×ₗ Fin n) k :=
    fun I ↦ rename toLex (flagMinor k I.val)
  -- 1. Use the nonempty-minor SAGBI basis and finite binomial generators of its toric ideal.
  obtain ⟨-, hsagbi⟩ := adjoin_and_isSAGBIBasis_nonempty_flagMinor (n := n) k
  have hc_monic : ∀ I : {I : Finset (Fin n) // I.Nonempty}, lex.Monic (c I) :=
    fun I ↦ monic_rename_toLex_flagMinor k I.val
  let a : {I : Finset (Fin n) // I.Nonempty} → Fin n ×ₗ Fin n →₀ ℕ := fun I ↦ lex.degree (c I)
  have haI (I : {I : Finset (Fin n) // I.Nonempty}) :
      lex.degree (c I) = flagDiagonalExponent I.val :=
    degree_rename_toLex_flagMinor (R := k) I.val
  have ha : a = fun I ↦ flagDiagonalExponent I.val := funext haI
  obtain ⟨B, hB, hspan⟩ := TauCeti.exists_finset_toricIdeal_eq_span a
  let r : B → MvPolynomial {I : Finset (Fin n) // I.Nonempty} k :=
    fun j ↦ monomial j.val.1 1 - monomial j.val.2 1
  have hker : RingHom.ker (aeval (fun I ↦ monomial (a I) (1 : k))) =
      Ideal.span (Set.range r) := by
    rw [← TauCeti.toricIdeal_eq_ker_aeval_monomial, hspan k, Set.image_eq_range]; rfl
  -- 2. Subduct each binomial relation and extract a positive weight realizing all reductions.
  choose Q hQc hQ using fun j : B ↦
    hsagbi.exists_aeval_eq_aeval_sub hc_monic (hB j.val j.property)
  obtain ⟨w, hw, hcw, hgw, hQw⟩ :=
    exists_pos_weight_forall_mem_weightFiltrationLT hc_monic hQ
  let d := fun I ↦ Finsupp.weight w (a I)
  have hwA (u : {I : Finset (Fin n) // I.Nonempty} →₀ ℕ) :
      Finsupp.weight d u = Finsupp.weight w (Finsupp.linearCombination ℕ a u) :=
    Finsupp.weight_comp_eq_apply_linearCombination (Finsupp.weight w) a u
  have hr (j : B) : (r j).IsWeightedHomogeneous d (Finsupp.weight d j.val.1) :=
    (isWeightedHomogeneous_monomial _ _ _ rfl).sub
      (isWeightedHomogeneous_monomial _ _ _ (by rw [hwA, hwA, hB j.val j.property]))
  -- 3. Transport `a = lex.degree ∘ c` to `flagDiagonalExponent ∘ Subtype.val`.
  exact ⟨w, B, r, Q, _, hw, fun I ↦ by simpa only [haI I] using hcw I,
    fun I ↦ by simpa only [haI I] using hgw I,
    by simpa only [ha] using hker, by simpa only [d, ha] using hr,
    by simpa only [haI] using hQw, hQc⟩

/-- Converts the nonempty-family weight filtration and top-homogeneous-component certificate into
the weight-initial form and weighted total degree of every flag minor `flagMinor k I`. -/
private theorem weightInitialForm_and_weightedTotalDegree_flagMinor {k : Type*} [Field k]
    (w : (Fin n ×ₗ Fin n) → ℕ)
    (hcw : ∀ I : {I : Finset (Fin n) // I.Nonempty},
      rename toLex (flagMinor k I.val) ∈
        TauCeti.MvPolynomial.weightFiltration k w (Finsupp.weight w (flagDiagonalExponent I.val)))
    (hgw : ∀ I : {I : Finset (Fin n) // I.Nonempty},
      MvPolynomial.weightedHomogeneousComponent w (Finsupp.weight w (flagDiagonalExponent I.val))
          (rename toLex (flagMinor k I.val)) =
        monomial (flagDiagonalExponent I.val) 1)
    (I : Finset (Fin n)) :
    MvPolynomial.weightInitialForm w (rename toLex (flagMinor k I)) =
        monomial (flagDiagonalExponent I) 1 ∧
      (rename toLex (flagMinor k I)).weightedTotalDegree w =
        Finsupp.weight w (flagDiagonalExponent I) := by
  rcases I.eq_empty_or_nonempty with rfl | hI
  · have h0 : flagDiagonalExponent (∅ : Finset (Fin n)) = 0 := by
      rw [← degree_rename_toLex_flagMinor (R := k), flagMinor_empty, map_one, degree_one]
    rw [h0, map_zero, flagMinor_empty, map_one, monomial_zero', C_1,
      MvPolynomial.weightInitialForm_one]
    exact ⟨rfl, Nat.eq_zero_of_le_zero
      (TauCeti.MvPolynomial.mem_weightFiltration_iff_weightedTotalDegree_le.mp
        SetLike.GradedOne.one_mem)⟩
  · let J : {I : Finset (Fin n) // I.Nonempty} := ⟨I, hI⟩
    have hdeg_eq : (rename toLex (flagMinor k I)).weightedTotalDegree w =
        Finsupp.weight w (flagDiagonalExponent I) := by
      refine le_antisymm
        (TauCeti.MvPolynomial.mem_weightFiltration_iff_weightedTotalDegree_le.mp (hcw J))
        (le_of_not_gt fun hlt ↦ one_ne_zero <| MvPolynomial.monomial_eq_zero.mp <| hgw J ▸
          MvPolynomial.weightedHomogeneousComponent_eq_zero _ (rename toLex (flagMinor k I)) hlt)
    exact ⟨by rw [MvPolynomial.weightInitialForm_def, hdeg_eq]; exact hgw J, hdeg_eq⟩

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
   `LaurentPolynomial (flagMinorAlgebra n k)` via an isomorphism sending `t` to `T 1` and every
   `p : A.weightReesAlgebra w` to `Polynomial.toLaurent p` mapped along the inverse of
   `rename toLex`. -/
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
          LaurentPolynomial.T 1 ∧
        ∀ p : ((flagMinorAlgebra n k).map (rename toLex)).weightReesAlgebra w,
          e (algebraMap _ _ p) =
            AddMonoidAlgebra.mapAlgEquiv k ℤ
              ((flagMinorAlgebra n k).equivMapOfInjective (rename toLex)
                (rename_injective _ toLex.injective)).symm
              (Polynomial.toLaurent (p : ((flagMinorAlgebra n k).map (rename toLex))[X])) := by
  classical
  -- 1. Match the `w`-initial algebra and Rees presentation with the diagonal SAGBI basis.
  obtain ⟨hadj, hsagbi⟩ := adjoin_and_isSAGBIBasis_nonempty_flagMinor (n := n) k
  set A : Subalgebra _ _ := (flagMinorAlgebra n k).map (rename toLex)
  let c : {I : Finset (Fin n) // I.Nonempty} → MvPolynomial (Fin n ×ₗ Fin n) k :=
    fun I ↦ rename toLex (flagMinor k I.val)
  obtain ⟨w, ι, r, Q, e, hw, hcw, hgw, hker, hr, hQw, hQc⟩ :=
    exists_pos_weight_flagMinor_certificate (n := n) k
  have hinit' : Algebra.adjoin k (MvPolynomial.weightInitialForm w '' (A : Set _)) =
      lex.initialAlgebra A := by
    rw [← hadj]
    refine (TauCeti.MvPolynomial.adjoin_weightInitialForm_eq hcw hgw hker hr hQw hQc).trans ?_
    rw [← hsagbi.adjoin_leadingTerm, ← Set.range_comp]
    exact congrArg (Algebra.adjoin k) (congrArg Set.range
      (funext fun I ↦ by simp [leadingTerm_rename_toLex_flagMinor]))
  have hrees_eq : (TauCeti.MvPolynomial.weightReesAeval c
      (fun I ↦ Finsupp.weight w (flagDiagonalExponent I.val))).range =
      (A.weightReesAlgebra w).map (Polynomial.mapAlgHom A.val) :=
    (A.map_weightReesAlgebra_eq_range_weightReesAeval w hadj.symm hcw hgw hker hr hQw hQc).symm
  have htop := weightInitialForm_and_weightedTotalDegree_flagMinor w hcw hgw
  refine ⟨w, hw, htop, hinit', hrees_eq, ⟨A.flat_weightReesAlgebra w, ?_⟩, ?_⟩
  · -- 2. Identify the special fiber `t = 0` with the Gelfand-Tsetlin semigroup algebra.
    let := TauCeti.coeffSubalgebra.algebra (A.weightFiltration w) (A.one_mem_weightFiltration_one w)
    let := Algebra.compHom k (Polynomial.evalRingHom (0 : k))
    refine ⟨(A.weightReesAlgebraSpecialFiberEquiv w).trans
        ((Subalgebra.equivOfEq _ _ hinit').trans (initialAlgebraFlagMinorEquiv n k).symm),
      fun I hIm ↦ ?_⟩
    rw [AlgEquiv.trans_apply, AlgEquiv.trans_apply, AlgEquiv.symm_apply_eq]
    apply Subtype.ext
    rw [Subalgebra.equivOfEq_apply, Subalgebra.coe_weightReesAlgebraSpecialFiberEquiv_tmul_monomial]
    have hcomp : weightedHomogeneousComponent w (Finsupp.weight w (flagDiagonalExponent I))
        (rename toLex (flagMinor k I)) = monomial (flagDiagonalExponent I) 1 := by
      rw [← (htop I).2, ← MvPolynomial.weightInitialForm_def, (htop I).1]
    rw [hcomp, coe_initialAlgebraFlagMinorEquiv_single,
      ← GTPattern.flagExponentEquiv_flagDiagonalExponent I, AddEquiv.symm_apply_apply]
  · -- 3. Identify the localized fiber away from `t` with `LaurentPolynomial`.
    let e1 := TauCeti.coeffSubalgebra.localizationAwayXEquivLaurent (A.weightFiltration w)
      (A.one_mem_weightFiltration_one w) (A.weightFiltration_mono w) (A.iSup_weightFiltration w)
    have he1 := TauCeti.coeffSubalgebra.localizationAwayXEquivLaurent_algebraMap_X
      (A.weightFiltration w) (A.one_mem_weightFiltration_one w) (A.weightFiltration_mono w)
      (A.iSup_weightFiltration w)
    let eA : A ≃ₐ[k] flagMinorAlgebra n k :=
      ((flagMinorAlgebra n k).equivMapOfInjective (rename toLex)
        (rename_injective _ toLex.injective)).symm
    refine ⟨e1.trans (AddMonoidAlgebra.mapAlgEquiv k ℤ eA), ?_, fun p ↦ ?_⟩
    · rw [AlgEquiv.trans_apply, he1]
      exact (AddMonoidAlgebra.mapAlgHom_single eA.toAlgHom 1 1).trans (by rw [map_one]; rfl)
    · rw [AlgEquiv.trans_apply, TauCeti.coeffSubalgebra.localizationAwayXEquivLaurent_algebraMap]

end Degeneration

end TauCeti
