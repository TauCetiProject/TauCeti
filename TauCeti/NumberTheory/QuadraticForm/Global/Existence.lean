/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.QuadraticForm.Global.CorrectionPlanes
public import TauCeti.NumberTheory.QuadraticForm.Global.Predicates
public import TauCeti.NumberTheory.QuadraticForm.Global.SummandExchange
import TauCeti.LinearAlgebra.QuadraticForm.Representation

/-!
# Correcting a global form at finitely many places

Let `W` be a regular quadratic form over a number field `K`, and let `U_v` be regular forms over
the completions `K_v` with the rank of `W` and with discriminant the image of the discriminant of
`W`. Let `α, β ∈ Kˣ`, with `β` positive at every real place, be such that

```text
W_v ≅ U_v   ↔   (α, β)_v = 1     at every finite place v.
```

With the correction planes `P = ⟨1, -β⟩` and `P' = ⟨α, -αβ⟩`, this file proves:

* `P'` is represented by `P ⊥ W` at every finite and real place. Where `(α, β)_v = 1` the two
  planes are isometric; where `(α, β)_v = -1`, the forms `W_v` and `U_v` are two different classes
  with the same rank and discriminant, and exchanging summands gives `(P ⊥ W)_v ≅ P'_v ⊥ U_v`.
* If `P'` is represented by `P ⊥ W` over `K`, its orthogonal complement `Q` is a regular global
  form of the rank and discriminant of `W` with `Q_v ≅ U_v` at every finite place and
  `Q_w ≅ W_w` at every real place.

This is the correction step of O'Meara's construction of a global form with prescribed
localizations. There `W` is a first global approximation that matches the targets `U_v` except
at a finite set `R` of finite places, `β` is a square at every archimedean place and a nonsquare
at every place of `R`, and `α` is chosen by Hilbert sign prescription with `(α, β)_v = -1`
exactly on `R`. The local representation of `P'` by `P ⊥ W` is the input of the local-global
principle for representations, whose global representation produces `Q`.

## Main results

* `QuadraticForm.locallyRepresents_weightedSumSquares_neg_self_mul_prod`: `P'` is locally
  represented by `P ⊥ W`.
* `QuadraticForm.atFinitePlace_equivalent_of_weightedSumSquares_neg_self_mul_prod_equivalent`,
  `QuadraticForm.atRealPlace_equivalent_of_weightedSumSquares_neg_self_mul_prod_equivalent`,
  `QuadraticForm.discr_eq_of_weightedSumSquares_neg_self_mul_prod_equivalent`: if
  `P' ⊥ Q ≅ P ⊥ W` over `K`, then `Q_v ≅ U_v` at every finite place, `Q_w ≅ W_w` at every real
  place, and `Q` and `W` have the same discriminant.
* `QuadraticForm.exists_discr_eq_equivalent_of_isRepresentedBy_prod`: a global representation of
  `P'` by `P ⊥ W` produces a regular global form on `Fin n → K` with these localizations and the
  discriminant of `W`.

## References

* O. T. O'Meara, *Introduction to Quadratic Forms*, Springer (1963), 72:1.
-/

public section

open IsDedekindDomain NumberField NumberField.InfinitePlace QuadraticMap TauCeti

namespace QuadraticForm

variable {K : Type*} [Field K] [NumberField K]
variable {V : Type*} [AddCommGroup V] [Module K V] [FiniteDimensional K V]
  {W : _root_.QuadraticForm K V}

/-- **The local representation of the correction plane.** Let `W` be a regular form over `K` and
`α, β ∈ Kˣ` with `β` positive at every real place. Suppose that at each finite place `v` with
`(α, β)_v = -1` the localization `W_v` is not isometric to a given regular form `U_v` over `K_v`
having the rank of `W` and the discriminant of `W_v`. Then `⟨α, -αβ⟩` is represented by
`⟨1, -β⟩ ⊥ W` at every finite and real place. -/
theorem locallyRepresents_weightedSumSquares_neg_self_mul_prod (hW : W.Nondegenerate)
    (a b : Kˣ)
    (hb : ∀ w : {w : InfinitePlace K // w.IsReal}, 0 < embedding_of_isReal w.2 (b : K))
    {n : ℕ} (hn : Module.finrank K V = n)
    (U : ∀ v : HeightOneSpectrum (𝓞 K),
      _root_.QuadraticForm (v.adicCompletion K) (Fin n → v.adicCompletion K))
    (hU : ∀ v, (U v).Nondegenerate)
    (hUd : ∀ v, (algebraMap K (v.adicCompletion K)).squareClassMap
        (RegularFormClass.discr (formClass W hW)) = RegularFormClass.discr (formClass _ (hU v)))
    (hWU : ∀ v, hilbertSymbol (v.unitAtFinitePlace a) (v.unitAtFinitePlace b) = -1 →
        ¬ (W.atFinitePlace v).Equivalent (U v)) :
    LocallyRepresents (weightedSumSquares K ![(a : K), -(a * b : K)])
      ((weightedSumSquares K ![1, -(b : K)]).prod W) := by
  refine (locallyRepresents_iff _ _).mpr ⟨fun v => ?_, fun w => ?_⟩
  · by_cases hPP' : (atFinitePlace (weightedSumSquares K ![1, -(b : K)]) v).Equivalent
        (atFinitePlace (weightedSumSquares K ![(a : K), -(a * b : K)]) v)
    · -- Where the planes are isometric, `P'_v` is the first summand of `(P ⊥ W)_v`.
      exact hPP'.symm.isRepresentedBy.trans ((isRepresentedBy_prod_left _ _).trans
        (Equivalent.isRepresentedBy ⟨(atFinitePlaceProd _ W v).symm⟩))
    · -- Elsewhere `(α, β)_v = -1`, and exchanging summands gives `(P ⊥ W)_v ≅ P'_v ⊥ U_v`.
      have hab := (Int.units_eq_one_or _).resolve_left
        ((equivalent_atFinitePlace_binary_one_neg_iff_hilbertSymbol_eq_one a b v).not.mp hPP')
      exact (isRepresentedBy_prod_left _ _).trans
        (atFinitePlace_prod_equivalent_prod_of_not_equivalent
          (nondegenerate_weightedSumSquares_one_neg b)
          (nondegenerate_weightedSumSquares_neg_self_mul a b) hW rfl
          (congrArg _ (discr_formClass_weightedSumSquares_neg_self_mul a b).symm) hPP' (hU v)
          (by simp [hn]) (hUd v) (hWU v hab)).symm.isRepresentedBy
  · exact (equivalent_atRealPlace_binary_one_neg_of_pos a (hb w)).symm.isRepresentedBy.trans
      ((isRepresentedBy_prod_left _ _).trans
        (Equivalent.isRepresentedBy ⟨(atRealPlaceProd _ W w).symm⟩))

variable {V' : Type*} [AddCommGroup V'] [Module K V'] {Q : _root_.QuadraticForm K V'}

/-- **The corrected form at a finite place.** Suppose `⟨α, -αβ⟩ ⊥ Q ≅ ⟨1, -β⟩ ⊥ W` over `K`, and
let `U` be a regular form over `K_v` with the rank of `W` and the discriminant of `W_v` such that
`W_v ≅ U` exactly when `(α, β)_v = 1`. Then `Q_v ≅ U`. -/
theorem atFinitePlace_equivalent_of_weightedSumSquares_neg_self_mul_prod_equivalent
    (hW : W.Nondegenerate) {a b : Kˣ}
    (h : ((weightedSumSquares K ![(a : K), -(a * b : K)]).prod Q).Equivalent
      ((weightedSumSquares K ![1, -(b : K)]).prod W))
    {v : HeightOneSpectrum (𝓞 K)} {X : Type*} [AddCommGroup X] [Module (v.adicCompletion K) X]
    [FiniteDimensional (v.adicCompletion K) X] {U : _root_.QuadraticForm (v.adicCompletion K) X}
    (hU : U.Nondegenerate) (hUr : Module.finrank K V = Module.finrank (v.adicCompletion K) X)
    (hUd : (algebraMap K (v.adicCompletion K)).squareClassMap
        (RegularFormClass.discr (formClass W hW)) = RegularFormClass.discr (formClass U hU))
    (hWU : (W.atFinitePlace v).Equivalent U ↔
      hilbertSymbol (v.unitAtFinitePlace a) (v.unitAtFinitePlace b) = 1) :
    (Q.atFinitePlace v).Equivalent U := by
  have hPP' := equivalent_atFinitePlace_binary_one_neg_iff_hilbertSymbol_eq_one a b v
  by_cases hab : hilbertSymbol (v.unitAtFinitePlace a) (v.unitAtFinitePlace b) = 1
  · exact (atFinitePlace_equivalent_of_prod_equivalent_prod_of_equivalent
      (nondegenerate_weightedSumSquares_neg_self_mul a b) h (hPP'.mpr hab)).trans (hWU.mpr hab)
  · exact atFinitePlace_equivalent_of_prod_equivalent_prod_of_not_equivalent
      (nondegenerate_weightedSumSquares_one_neg b)
      (nondegenerate_weightedSumSquares_neg_self_mul a b) hW h rfl
      (congrArg _ (discr_formClass_weightedSumSquares_neg_self_mul a b).symm) (hPP'.not.mpr hab)
      hU hUr hUd (hWU.not.mpr hab)

omit [FiniteDimensional K V] in
/-- **The corrected form at a real place.** If `⟨α, -αβ⟩ ⊥ Q ≅ ⟨1, -β⟩ ⊥ W` over `K` and `β` is
positive at the real place `w`, then `Q_w ≅ W_w`. -/
theorem atRealPlace_equivalent_of_weightedSumSquares_neg_self_mul_prod_equivalent {a b : Kˣ}
    (h : ((weightedSumSquares K ![(a : K), -(a * b : K)]).prod Q).Equivalent
      ((weightedSumSquares K ![1, -(b : K)]).prod W))
    {w : {w : InfinitePlace K // w.IsReal}} (hb : 0 < embedding_of_isReal w.2 (b : K)) :
    (Q.atRealPlace w).Equivalent (W.atRealPlace w) :=
  atRealPlace_equivalent_of_prod_equivalent_prod_of_equivalent
    (nondegenerate_weightedSumSquares_neg_self_mul a b) h
    (equivalent_atRealPlace_binary_one_neg_of_pos a hb)

omit [NumberField K] in
/-- **The corrected form has the discriminant of `W`.** If `⟨α, -αβ⟩ ⊥ Q ≅ ⟨1, -β⟩ ⊥ W` over
`K` with `Q` and `W` regular, then `Q` and `W` have the same discriminant, because the two planes
do. -/
theorem discr_eq_of_weightedSumSquares_neg_self_mul_prod_equivalent [Invertible (2 : K)]
    [FiniteDimensional K V']
    (hQ : Q.Nondegenerate) (hW : W.Nondegenerate) {a b : Kˣ}
    (h : ((weightedSumSquares K ![(a : K), -(a * b : K)]).prod Q).Equivalent
      ((weightedSumSquares K ![1, -(b : K)]).prod W)) :
    RegularFormClass.discr (formClass Q hQ) = RegularFormClass.discr (formClass W hW) := by
  have hP := nondegenerate_weightedSumSquares_one_neg b
  have hP' := nondegenerate_weightedSumSquares_neg_self_mul a b
  have key := (formClass_eq_iff _ (hP'.prod hQ) _ (hP.prod hW)).mpr h
  rw [formClass_prod _ hP' _ hQ, formClass_prod _ hP _ hW] at key
  have hd := congrArg RegularFormClass.discr key
  rw [RegularFormClass.discr_add, RegularFormClass.discr_add,
    discr_formClass_weightedSumSquares_neg_self_mul] at hd
  simpa using congrArg (-RegularFormClass.discr (formClass _ hP) + ·) hd

/-- **The corrected global form.** Let `W` be a regular form over `K` of rank `n`, let `U_v` be
regular forms over the completions with rank `n` and the discriminant of `W_v`, and let
`α, β ∈ Kˣ`, with `β` positive at every real place, satisfy `W_v ≅ U_v ↔ (α, β)_v = 1` at every
finite place. If `⟨α, -αβ⟩` is represented by `⟨1, -β⟩ ⊥ W` over `K`, then there is a regular
form `Q` on `Fin n → K` with the discriminant of `W`, with `Q_v ≅ U_v` at every finite place and
with `Q_w ≅ W_w` at every real place. -/
theorem exists_discr_eq_equivalent_of_isRepresentedBy_prod (hW : W.Nondegenerate) (a b : Kˣ)
    (hb : ∀ w : {w : InfinitePlace K // w.IsReal}, 0 < embedding_of_isReal w.2 (b : K))
    {n : ℕ} (hn : Module.finrank K V = n)
    (U : ∀ v : HeightOneSpectrum (𝓞 K),
      _root_.QuadraticForm (v.adicCompletion K) (Fin n → v.adicCompletion K))
    (hU : ∀ v, (U v).Nondegenerate)
    (hUd : ∀ v, (algebraMap K (v.adicCompletion K)).squareClassMap
        (RegularFormClass.discr (formClass W hW)) = RegularFormClass.discr (formClass _ (hU v)))
    (hWU : ∀ v, (W.atFinitePlace v).Equivalent (U v) ↔
      hilbertSymbol (v.unitAtFinitePlace a) (v.unitAtFinitePlace b) = 1)
    (hrep : (weightedSumSquares K ![(a : K), -(a * b : K)]).IsRepresentedBy
      ((weightedSumSquares K ![1, -(b : K)]).prod W)) :
    ∃ (Q : _root_.QuadraticForm K (Fin n → K)) (hQ : Q.Nondegenerate),
      RegularFormClass.discr (formClass Q hQ) = RegularFormClass.discr (formClass W hW) ∧
      (∀ v, (Q.atFinitePlace v).Equivalent (U v)) ∧
      ∀ w, (Q.atRealPlace w).Equivalent (W.atRealPlace w) := by
  -- Split `P'` off `P ⊥ W`; its orthogonal complement `S` has the rank of `W`.
  obtain ⟨S, hS, hsplit⟩ := hrep.exists_equivalent_prod
    (nondegenerate_weightedSumSquares_neg_self_mul a b)
    ((nondegenerate_weightedSumSquares_one_neg b).prod hW)
  have hrank : Module.finrank K S = Module.finrank K (Fin n → K) := by
    have := hsplit.some.toLinearEquiv.finrank_eq
    simp only [Module.finrank_prod, Module.finrank_fin_fun] at this
    simp only [Module.finrank_fin_fun]
    omega
  -- Transport the complement to the coordinate space `Fin n → K`.
  obtain ⟨e⟩ := FiniteDimensional.nonempty_linearEquiv_of_finrank_eq hrank
  let Q := (((weightedSumSquares K ![1, -(b : K)]).prod W).restrict S).comp
    (e.symm : (Fin n → K) →ₗ[K] S)
  have hQS : (((weightedSumSquares K ![1, -(b : K)]).prod W).restrict S).Equivalent Q :=
    ⟨isometryEquivOfCompLinearEquiv _ e.symm⟩
  have hQ : Q.Nondegenerate := hQS.some.nondegenerate_iff.mp hS
  have h : ((weightedSumSquares K ![(a : K), -(a * b : K)]).prod Q).Equivalent
      ((weightedSumSquares K ![1, -(b : K)]).prod W) :=
    (hsplit.trans ((Equivalent.refl _).prod hQS)).symm
  refine ⟨Q, hQ, discr_eq_of_weightedSumSquares_neg_self_mul_prod_equivalent hQ hW h,
    fun v => ?_,
    fun w => atRealPlace_equivalent_of_weightedSumSquares_neg_self_mul_prod_equivalent h (hb w)⟩
  exact atFinitePlace_equivalent_of_weightedSumSquares_neg_self_mul_prod_equivalent hW h (hU v)
    (by simp [hn]) (hUd v) (hWU v)

end QuadraticForm
