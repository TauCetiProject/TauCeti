/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.QuadraticForm.Global.LocalRealization
import TauCeti.NumberTheory.NumberField.WorkedExamples.Sqrt5.Invariants

/-!
# Mixed-signature admissible data over `ℚ(√5)`

Present `K = ℚ(√5)` by an integral generator `θ` with minimal polynomial `X² - X - 1`.
There are two real places and the ideal `(2)` is prime. We construct an admissible system
of rank three and trivial plain discriminant, with positive indices three and one at the
two real places and finite Hasse sign `-1` exactly at `(2)`.

The real negative indices are zero and two, so their Hasse signs are `1` and `-1`.
The single finite sign `-1` therefore makes the total Hasse product one. The two
small-rank realization exceptions do not apply in rank three.

The system has regular local realizations at every finite and real place, by the local
realization theorem. This supplies concrete mixed-signature input for existence with
prescribed local behavior. No global form realizing the system is constructed here.

## References

* O. T. O'Meara, *Introduction to Quadratic Forms*, Springer (1963), 72:1.
-/

public section

open IsDedekindDomain NumberField NumberField.InfinitePlace Polynomial

namespace TauCeti.NumberField.QuadraticForm.Sqrt5

variable {K : Type*} [Field K] [NumberField K] {θ : 𝓞 K}

open scoped Classical in
/-- Over `ℚ(√5)` there is an admissible rank-three system of trivial discriminant, with
positive indices three and one at its two real places and Hasse sign `-1` exactly at the
prime `(2)`. The finite and real local forms realizing this system are regular. -/
theorem exists_admissible_rank_three
    (hmin : minpoly ℤ θ = X ^ 2 - X - 1)
    (hgen : Algebra.adjoin ℚ {(θ : K)} = ⊤) :
    ∃ (v₂ : HeightOneSpectrum (𝓞 K))
      (w₁ w₂ : {w : InfinitePlace K // w.IsReal}),
      v₂.asIdeal = Ideal.span {(2 : 𝓞 K)} ∧ w₁ ≠ w₂ ∧
      (∀ w, w = w₁ ∨ w = w₂) ∧
      ∃ I : GlobalFormInvariants K,
        I.IsAdmissible ∧ I.rank = 3 ∧ I.discr = 0 ∧
        (∀ v, I.finiteHasse v = if v = v₂ then -1 else 1) ∧
        I.realPositiveIndex w₁ = 3 ∧ I.realPositiveIndex w₂ = 1 ∧
        ∃ (U : ∀ v : HeightOneSpectrum (𝓞 K),
            _root_.QuadraticForm (v.adicCompletion K) (Fin I.rank → v.adicCompletion K))
          (R : {w : InfinitePlace K // w.IsReal} → _root_.QuadraticForm ℝ (Fin I.rank → ℝ)),
          I.IsLocalRealization U R := by
  classical
  -- The inert prime above two is the principal ideal `(2)`.
  have hprime : (Ideal.span {(2 : 𝓞 K)}).IsPrime := by
    simpa only [Ideal.map_span, Set.image_singleton, map_ofNat] using
      TauCeti.NumberField.Sqrt5.isPrime_map_span_two hmin hgen
  let v₂ : HeightOneSpectrum (𝓞 K) :=
    ⟨Ideal.span {(2 : 𝓞 K)}, hprime, by simp⟩
  -- Enumerate both real places, so the real Hasse product has exactly two factors.
  have hcard : (Finset.univ : Finset {w : InfinitePlace K // w.IsReal}).card = 2 :=
    TauCeti.NumberField.Sqrt5.nrRealPlaces_eq_two hmin hgen
  obtain ⟨w₁, w₂, hne, hw⟩ := Finset.card_eq_two.mp hcard
  let I : GlobalFormInvariants K :=
    { rank := 3
      discr := 0
      finiteHasse := fun v => if v = v₂ then -1 else 1
      realPositiveIndex := fun w => if w = w₁ then 3 else 1 }
  have hs : Function.mulSupport I.finiteHasse ⊆ {v₂} := by
    intro v hv
    by_contra h
    exact hv (by simp_all [I])
  have hI : I.IsAdmissible := by
    refine
      { one_le_rank := by norm_num [I]
        realPositiveIndex_le_rank := fun w => by simp [I]; split <;> omega
        discrAtRealPlace_eq := ?_
        hasFiniteMulSupport_finiteHasse := (Set.finite_singleton v₂).subset hs
        finiteHasse_eq_one_of_rank_eq_one := by simp [I]
        finiteHasse_eq_one_of_rank_eq_two := by simp [I]
        hasseProduct_eq_one := ?_ }
    · intro w
      by_cases h : w = w₁ <;>
        simp [GlobalFormInvariants.discrAtRealPlace_def, GlobalFormInvariants.realNegativeIndex_def,
          I, h, ← squareClass_pow]
    · rw [GlobalFormInvariants.hasseProduct_eq_prod_of_mulSupport_subset I
        (S := {v₂}) (by simpa using hs)]
      simp [I, GlobalFormInvariants.realHasse_def, GlobalFormInvariants.realNegativeIndex_def,
        hw, hne, hne.symm]
  refine ⟨v₂, w₁, w₂, rfl, hne, ?_, I, hI, rfl, rfl, fun _ => rfl, ?_, ?_,
    hI.exists_isLocalRealization⟩
  · intro w
    have : w ∈ (Finset.univ : Finset {w : InfinitePlace K // w.IsReal}) := Finset.mem_univ w
    simpa [hw] using this
  · simp [I]
  · simp [I, hne.symm]

end TauCeti.NumberField.QuadraticForm.Sqrt5
