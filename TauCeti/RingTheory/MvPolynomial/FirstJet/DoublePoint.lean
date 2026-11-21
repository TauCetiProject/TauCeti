/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import TauCeti.RingTheory.MvPolynomial.FirstJet.Basic
public import TauCeti.RingTheory.TrivSqZeroExt
import Mathlib.Data.ZMod.Defs
import TauCeti.RingTheory.MvPolynomial.Ideal

/-!
# Double points in affine space

For a family of points `Pᵢ : σ → R`, `TauCeti.doubleIdeal P` is the square `(⋂ᵢ 𝔪_{Pᵢ})²` of the
common vanishing ideal `⋂ᵢ 𝔪_{Pᵢ}` (`𝔪_P = ker (eval P)`). In general, `R[X] ⧸ doubleIdeal P`
is the thickening defined by the square of that common vanishing ideal.

For finitely many points over a commutative ring whose evaluation ideals `𝔪_{Pᵢ}` are pairwise
comaximal (for example, distinct points over a field), `doubleIdeal P` equals the intersection
`⋂ᵢ 𝔪_{Pᵢ}²` of the individual double-point ideals, so the quotient represents the union of the
individual doubled points `2Pᵢ`, and the Chinese remainder theorem splits the quotient into the
quotient factors `R[X] ⧸ 𝔪_{Pᵢ}²`. For finitely many variables, each quotient factor is the
algebra of first jets `TrivSqZeroExt R (σ → R)` (`TauCeti.ker_jetAlgebra`), so
`R[X] ⧸ doubleIdeal P ≃ₐ[R] ∏ᵢ TrivSqZeroExt R (σ → R)`, sending the class of `f` to its values
and gradients at the points. In particular, values and first derivatives can be prescribed
independently by a single polynomial, and for `r` variables and `n` points over a commutative ring
satisfying `StrongRankCondition`, the quotient has rank `n (r + 1)` (which over a field is the
length of `n` double points in `r`-space). The product of square-zero algebras keeps the nilpotents:
it is not the product of the residue rings.

## Main definitions

* `TauCeti.doubleIdeal P`: the square `(⋂ᵢ ker (eval (P i)))²` of the common vanishing ideal.
* `TauCeti.doublePointQuotientEquiv`: for finitely many points in finitely many variables with
  pairwise comaximal evaluation ideals over a commutative ring, the quotient by `doubleIdeal P` is
  the product of the first-jet algebras at the points.

## Main results

* `TauCeti.doubleIdeal_le_iInf_sq`, `TauCeti.doubleIdeal_isEmpty`, `TauCeti.doubleIdeal_unique`:
  containment and degenerate-index formulas for `doubleIdeal`.
* `TauCeti.doubleIdeal_eq_iInf`: for finitely many points with pairwise comaximal ideals,
  `doubleIdeal P = ⋂ᵢ 𝔪_{Pᵢ}²`.
* `TauCeti.mem_doubleIdeal_iff`: for finitely many points with pairwise comaximal ideals, a
  polynomial lies in `doubleIdeal P` exactly when its value and first partial derivatives vanish at
  every point.
* `TauCeti.exists_forall_jetAlgebra_eq`: for finitely many points in finitely many variables with
  pairwise comaximal ideals, first jets can be prescribed independently.
* `TauCeti.doublePointQuotientEquiv_comp_equiv`: reindexing invariance of
  `doublePointQuotientEquiv`.
* `TauCeti.finrank_quotient_doubleIdeal`: for `n` points in `r` variables with pairwise comaximal
  evaluation ideals over a commutative ring satisfying `StrongRankCondition`, the quotient by
  `doubleIdeal P` has rank `n (r + 1)` (over a field, the length of `n` double points).

## References

* J.-M. Couveignes, *Enumerating number fields*, Ann. of Math. 192 (2020), 487–497, §3.
-/

public section

namespace TauCeti

open MvPolynomial

variable {σ ι κ : Type*}

/-- The square of the common vanishing ideal `⋂ᵢ ker (eval (P i))` of a family of points `Pᵢ`.
When the family is finite and its evaluation ideals are pairwise comaximal, this equals
`⋂ᵢ ker (eval (P i)) ^ 2` (`TauCeti.doubleIdeal_eq_iInf`), the ideal of the individual doubled
points `2Pᵢ`. Repetitions among the points are allowed. -/
noncomputable def doubleIdeal {R : Type*} [CommSemiring R] (P : ι → σ → R) :
    Ideal (MvPolynomial σ R) :=
  (⨅ i, RingHom.ker (eval (P i))) ^ 2

theorem doubleIdeal_def {R : Type*} [CommSemiring R] (P : ι → σ → R) :
    doubleIdeal P = (⨅ i, RingHom.ker (eval (P i))) ^ 2 :=
  (rfl)

/-- Reindexing the points does not change the double-point ideal. -/
theorem doubleIdeal_comp {R : Type*} [CommSemiring R] (P : ι → σ → R) (e : κ ≃ ι) :
    doubleIdeal (P ∘ e) = doubleIdeal P := by
  simp only [doubleIdeal_def, Function.comp_apply]
  rw [e.iInf_comp (g := fun i ↦ RingHom.ker (eval (P i)))]

/-- The squared intersection ideal is always contained in the intersection of the squared point
ideals. -/
theorem doubleIdeal_le_iInf_sq {R : Type*} [CommSemiring R] (P : ι → σ → R) :
    doubleIdeal P ≤ ⨅ i, RingHom.ker (eval (P i)) ^ 2 := by
  rw [doubleIdeal_def]
  exact le_iInf fun i ↦ Ideal.pow_right_mono (iInf_le _ i) 2

@[simp]
theorem doubleIdeal_isEmpty {R : Type*} [CommSemiring R] [IsEmpty ι] (P : ι → σ → R) :
    doubleIdeal P = ⊤ := by
  simp [doubleIdeal_def]

@[simp]
theorem doubleIdeal_unique {R : Type*} [CommSemiring R] [Unique ι] (P : ι → σ → R) :
    doubleIdeal P = RingHom.ker (eval (P default)) ^ 2 := by
  simp [doubleIdeal_def]

section CommRing

variable {R : Type*} [CommRing R] {P : ι → σ → R}

/-- For a finite family of points whose evaluation ideals are pairwise comaximal, the square of the
common vanishing ideal is the intersection of the squares of the ideals of the individual points. -/
theorem doubleIdeal_eq_iInf [Finite ι]
    (hP : Pairwise (Function.onFun IsCoprime fun i ↦ RingHom.ker (eval (P i)))) :
    doubleIdeal P = ⨅ i, RingHom.ker (eval (P i)) ^ 2 := by
  cases nonempty_fintype ι
  have hcop {f : ι → Ideal (MvPolynomial σ R)} (hf : Pairwise (Function.onFun IsCoprime f)) :
      ∏ i, f i = ⨅ i, f i := by
    simpa using Ideal.prod_eq_iInf_of_pairwise_isCoprime (s := Finset.univ) fun i _ j _ h ↦ hf h
  rw [doubleIdeal_def, ← hcop hP, ← hcop fun _ _ hij ↦ (hP hij).pow, Finset.prod_pow]

section JetAlgebra

variable [DecidableEq σ]

/-- For a finite family of points whose evaluation ideals are pairwise comaximal, `doubleIdeal P`
is the intersection of the kernels of the first jets at the points. -/
theorem doubleIdeal_eq_iInf_ker_jetAlgebra [Finite ι]
    (hP : Pairwise (Function.onFun IsCoprime fun i ↦ RingHom.ker (eval (P i)))) :
    doubleIdeal P = ⨅ i, RingHom.ker (jetAlgebra (P i)) := by
  simp only [doubleIdeal_eq_iInf hP, ker_jetAlgebra]

/-- **Chinese remainder for double points.** For finitely many points in finitely many variables
over a commutative ring whose evaluation ideals are pairwise comaximal, the coordinate ring of the
doubled points is isomorphic as an `R`-algebra to the product of the first-jet algebras at the
points: the class of `f` is sent to the values and gradients of `f` at the points
(`TauCeti.doublePointQuotientEquiv_mk`). -/
noncomputable def doublePointQuotientEquiv [Finite σ] [Finite ι]
    (hP : Pairwise (Function.onFun IsCoprime fun i ↦ RingHom.ker (eval (P i)))) :
    (MvPolynomial σ R ⧸ doubleIdeal P) ≃ₐ[R] (ι → TrivSqZeroExt R (σ → R)) :=
  let hpow : Pairwise (Function.onFun IsCoprime fun i ↦ RingHom.ker (eval (P i)) ^ 2) :=
    fun _ _ hij ↦ (hP hij).pow
  let crt : (MvPolynomial σ R ⧸ ⨅ i, RingHom.ker (eval (P i)) ^ 2) ≃ₐ[R]
      ((i : ι) → MvPolynomial σ R ⧸ RingHom.ker (eval (P i)) ^ 2) :=
    AlgEquiv.ofRingEquiv (f := Ideal.quotientInfRingEquivPiQuotient _ hpow) fun r ↦ by
      funext i
      exact Ideal.quotientInfRingEquivPiQuotient_mk_apply hpow (C r) i
  (Ideal.quotientEquivAlgOfEq R (doubleIdeal_eq_iInf hP)).trans <|
    crt.trans <| AlgEquiv.piCongrRight fun i ↦ jetAlgebraEquiv (P i)

/-- The class of `f` modulo `doubleIdeal P` corresponds to the first jets of `f` at the points. -/
@[simp]
theorem doublePointQuotientEquiv_mk [Finite σ] [Finite ι]
    (hP : Pairwise (Function.onFun IsCoprime fun i ↦ RingHom.ker (eval (P i))))
    (f : MvPolynomial σ R) :
    doublePointQuotientEquiv hP (Ideal.Quotient.mk _ f) = fun i ↦ jetAlgebra (P i) f := by
  funext i
  unfold doublePointQuotientEquiv
  simp only [AlgEquiv.trans_apply, Ideal.quotientEquivAlgOfEq_mk, AlgEquiv.piCongrRight_apply,
    AlgEquiv.ofRingEquiv_apply]
  rw [Ideal.quotientInfRingEquivPiQuotient_mk_apply (fun _ _ hij ↦ (hP hij).pow) f i,
    jetAlgebraEquiv_mk]

/-- Reindexing a point tuple along an equivalence commutes with `doublePointQuotientEquiv`. -/
theorem doublePointQuotientEquiv_comp_equiv [Finite σ] [Finite ι] [Finite κ]
    (hP : Pairwise (Function.onFun IsCoprime fun i ↦ RingHom.ker (eval (P i)))) (e : κ ≃ ι)
    (x : MvPolynomial σ R ⧸ doubleIdeal (P ∘ e)) (j : κ) :
    doublePointQuotientEquiv (P := P ∘ e) (fun _ _ h ↦ hP (e.injective.ne h)) x j =
      doublePointQuotientEquiv hP
        (Ideal.quotientEquivAlgOfEq R (doubleIdeal_comp P e) x) (e j) := by
  obtain ⟨f, rfl⟩ := Ideal.Quotient.mk_surjective x
  rw [congrFun (doublePointQuotientEquiv_mk (P := P ∘ e)
    (fun _ _ h ↦ hP (e.injective.ne h)) f) j,
    Ideal.quotientEquivAlgOfEq_mk, congrFun (doublePointQuotientEquiv_mk hP f) (e j)]
  rfl

/-- **Simultaneous first-jet interpolation.** At finitely many points in finitely many variables
over a commutative ring whose evaluation ideals are pairwise comaximal, any values and gradients are
the values and gradients of a single polynomial. -/
theorem exists_forall_jetAlgebra_eq [Finite σ] [Finite ι]
    (hP : Pairwise (Function.onFun IsCoprime fun i ↦ RingHom.ker (eval (P i))))
    (y : ι → TrivSqZeroExt R (σ → R)) : ∃ f : MvPolynomial σ R, ∀ i, jetAlgebra (P i) f = y i := by
  obtain ⟨q, hq⟩ := (doublePointQuotientEquiv hP).surjective y
  obtain ⟨f, rfl⟩ := Ideal.Quotient.mk_surjective q
  exact ⟨f, fun i ↦ by simpa using congrFun hq i⟩

end JetAlgebra

/-- For finitely many points with pairwise comaximal evaluation ideals, a polynomial lies in
`doubleIdeal P` exactly when its value and all its first partial derivatives vanish at every
point. -/
theorem mem_doubleIdeal_iff [Finite ι]
    (hP : Pairwise (Function.onFun IsCoprime fun i ↦ RingHom.ker (eval (P i))))
    {f : MvPolynomial σ R} :
    f ∈ doubleIdeal P ↔ ∀ i, eval (P i) f = 0 ∧ ∀ j, eval (P i) (pderiv j f) = 0 := by
  classical
  simp [doubleIdeal_eq_iInf_ker_jetAlgebra hP, RingHom.mem_ker, jetAlgebra_eq_zero_iff]

/-- **Rank of a double-point quotient.** Over a commutative ring satisfying `StrongRankCondition`,
for `n` points in `r` variables with pairwise comaximal evaluation ideals, the quotient by
`doubleIdeal P` has rank `n (r + 1)` (which over a field is the length of `n` double points in
affine `r`-space). -/
theorem finrank_quotient_doubleIdeal [StrongRankCondition R] [Fintype ι] [Fintype σ]
    (hP : Pairwise (Function.onFun IsCoprime fun i ↦ RingHom.ker (eval (P i)))) :
    Module.finrank R (MvPolynomial σ R ⧸ doubleIdeal P) =
      Fintype.card ι * (Fintype.card σ + 1) := by
  classical
  rw [(doublePointQuotientEquiv hP).toLinearEquiv.finrank_eq, Module.finrank_pi_fintype]
  simp [TrivSqZeroExt.finrank_eq_finrank_add_one]

end CommRing

/-! ### Examples -/

/-- At the origin, `X 0` maps to `(0, e₀)` and `X 0 ^ 2` maps to `0` in the square-zero first-jet
algebra. -/
example {R : Type*} [CommSemiring R] :
    jetAlgebra (0 : Fin 2 → R) (X 0) = TrivSqZeroExt.inr (Pi.single 0 1) ∧
    jetAlgebra (0 : Fin 2 → R) (X 0 ^ 2) = 0 := by
  refine ⟨by simp, ?_⟩
  rw [map_pow, jetAlgebra_X]
  simp [sq, TrivSqZeroExt.inr_mul_inr]

/-- For the two distinct points `0` and `1` on the affine line over `ℚ`, the class of
`X 0 * (X 0 - 1)` in the double-point quotient is nonzero, while its square is zero: the quotient
retains its nonreduced structure. -/
example :
    let P : Fin 2 → Fin 1 → ℚ := ![fun _ ↦ 0, fun _ ↦ 1]
    let f : MvPolynomial (Fin 1) ℚ := X 0 * (X 0 - 1)
    Ideal.Quotient.mk (doubleIdeal P) f ≠ 0 ∧ Ideal.Quotient.mk (doubleIdeal P) f ^ 2 = 0 := by
  intro P f
  have hP : Pairwise (Function.onFun IsCoprime fun i ↦ RingHom.ker (eval (P i))) := by
    refine fun i j hij ↦ isCoprime_ker_eval ?_
    intro h
    have h0 := congrFun h 0
    fin_cases i <;> fin_cases j <;> simp [P] at hij h0
  refine ⟨?_, ?_⟩
  · intro h0
    have hmem : f ∈ doubleIdeal P := Ideal.Quotient.eq_zero_iff_mem.1 h0
    have hd := ((mem_doubleIdeal_iff hP).1 hmem 0).2 0
    simp [f, P] at hd
  · rw [← map_pow, Ideal.Quotient.eq_zero_iff_mem, mem_doubleIdeal_iff hP]
    intro i
    fin_cases i <;> simp [f, P, sq]

/-- Over `ℤ`, the distinct points `0` and `2` on the affine line do not have comaximal evaluation
ideals: their sum is contained in the ideal `(X 0, 2)`, which is proper. -/
example :
    ¬ IsCoprime (RingHom.ker (eval (fun _ : Fin 1 ↦ (0 : ℤ))))
      (RingHom.ker (eval (fun _ : Fin 1 ↦ (2 : ℤ)))) := by
  intro h
  obtain ⟨a, ha, b, hb, hab⟩ := Ideal.isCoprime_iff_exists.1 h
  let φ : ℤ →+* ZMod 2 := Int.castRingHom (ZMod 2)
  have h02 : (φ ∘ fun _ : Fin 1 ↦ (0 : ℤ)) = φ ∘ fun _ : Fin 1 ↦ (2 : ℤ) := by
    funext _
    rw [Function.comp_apply, Function.comp_apply]
    exact (by decide : φ 0 = φ 2)
  have hmod : eval (φ ∘ fun _ : Fin 1 ↦ (0 : ℤ)) (map φ (a + b)) = 1 := by
    rw [hab, map_one, map_one]
  have ha0 : eval (φ ∘ fun _ : Fin 1 ↦ (0 : ℤ)) (map φ a) = 0 := by
    rw [eval_map, ← eval₂_comp, RingHom.mem_ker.1 ha, map_zero]
  have hb0 : eval (φ ∘ fun _ : Fin 1 ↦ (0 : ℤ)) (map φ b) = 0 := by
    rw [h02, eval_map, ← eval₂_comp, RingHom.mem_ker.1 hb, map_zero]
  rw [map_add, map_add, ha0, hb0, add_zero] at hmod
  exact zero_ne_one hmod

/-- The empty point tuple has zero-dimensional double-point quotient. -/
example {k : Type*} [Field k] (r : ℕ) (P : Fin 0 → Fin r → k) :
    Module.finrank k (MvPolynomial (Fin r) k ⧸ doubleIdeal P) = 0 := by
  simpa using finrank_quotient_doubleIdeal (P := P) fun i ↦ isEmptyElim i

end TauCeti
