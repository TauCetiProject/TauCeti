/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.QuadraticForm.Global.FormInvariants
public import TauCeti.NumberTheory.QuadraticForm.Global.LocalRealization
import TauCeti.NumberTheory.HilbertSymbol.NormSubgroup
import TauCeti.NumberTheory.NumberField.WorkedExamples.Sqrt5.Invariants
import TauCeti.NumberTheory.NumberField.WorkedExamples.Sqrt5.Units
import TauCeti.NumberTheory.QuadraticForm.Global.ArchimedeanSymbol
import TauCeti.NumberTheory.QuadraticForm.Global.ProductFormula

/-!
# A mixed-signature global form over `ℚ(√5)`

Present `K = ℚ(√5)` by an integral generator `θ` with minimal polynomial `X² - X - 1`.
There are two real places and the ideal `(2)` is prime. We construct an admissible system
of rank three and trivial plain discriminant, with positive indices three and one at the
two real places and finite Hasse sign `-1` exactly at `(2)`.

The real negative indices are zero and two, so their Hasse signs are `1` and `-1`.
The single finite sign `-1` therefore makes the total Hasse product one. The two
small-rank realization exceptions do not apply in rank three.

The system has regular local realizations at every finite and real place, by the local
realization theorem. It is also realized by an explicit regular global form, `⟨1, θ, θ⟩`. Its
discriminant is the class of `θ²`. Since `θ` has norm `-1`, it is positive at one real place and
negative at the other, which gives the two positive indices. Its Hasse sign at a finite place `v`
is `(θ, θ)_v = (θ, -1)_v`. Away from `(2)` both entries are units at an odd place, so the symbol is
`1`. At `(2)` the sign comes from Hilbert's product formula for `θ` and `-1`: the two real symbols
multiply to `-1`, so the remaining finite symbol at `(2)` is `-1`. The global form is written down
directly rather than produced by the existence theorem for admissible systems.

## Main results

* `TauCeti.NumberField.QuadraticForm.Sqrt5.globalInvariants_weightedSumSquares_one_self_self`:
  the system of local invariants of `⟨1, θ, θ⟩`.
* `TauCeti.NumberField.QuadraticForm.Sqrt5.exists_admissible_rank_three`: the admissible
  mixed-signature system, its local realizations, and its realization by `⟨1, θ, θ⟩`.

## References

* O. T. O'Meara, *Introduction to Quadratic Forms*, Springer (1963), 72:1, and 71:18 for the
  product formula.
* J.-P. Serre, *A Course in Arithmetic*, Springer (1973), Chapter III, §2, Theorem 3.
-/

public section

open IsDedekindDomain NumberField NumberField.InfinitePlace Polynomial

namespace TauCeti.NumberField.QuadraticForm.Sqrt5

variable {K : Type} [Field K] [NumberField K] {θ : 𝓞 K}

open _root_.QuadraticMap

section GlobalForm

/-- The golden-ratio generator `θ` as a unit of `K`. -/
private def thetaUnit (hmin : minpoly ℤ θ = X ^ 2 - X - 1) : Kˣ :=
  Units.mk0 (θ : K) fun h => by
    have h1 := congrArg ((↑) : 𝓞 K → K) (TauCeti.NumberField.Sqrt5.mul_sub_one_eq_one hmin)
    simp [h] at h1

private theorem coe_thetaUnit (hmin : minpoly ℤ θ = X ^ 2 - X - 1) :
    (thetaUnit hmin : K) = θ :=
  rfl

/-- Away from the prime `(2)`, the symbol `(θ, -1)_v` is trivial: `2`, `θ` and `-1` are all
`v`-adic units. -/
private theorem hilbertSymbol_thetaUnit_neg_one_of_ne (hmin : minpoly ℤ θ = X ^ 2 - X - 1)
    (hgen : Algebra.adjoin ℚ {(θ : K)} = ⊤) {v : HeightOneSpectrum (𝓞 K)}
    (hv : v.asIdeal ≠ Ideal.span {(2 : 𝓞 K)}) :
    hilbertSymbol (v.unitAtFinitePlace (thetaUnit hmin)) (v.unitAtFinitePlace (-1)) = 1 := by
  have hprime : (Ideal.span {(2 : 𝓞 K)}).IsPrime := by
    simpa only [Ideal.map_span, Set.image_singleton, map_ofNat] using
      TauCeti.NumberField.Sqrt5.isPrime_map_span_two hmin hgen
  -- The prime `(2)` is maximal, so it is the only finite place containing `2`.
  have h2 : (2 : 𝓞 K) ∉ v.asIdeal := fun h2 => hv <|
    ((hprime.isMaximal (by simp)).eq_of_le v.isPrime.ne_top
      ((Ideal.span_singleton_le_iff_mem _).mpr h2)).symm
  -- `θ` is a unit of `𝓞 K`, since `θ (θ - 1) = 1`.
  have hθ : θ ∉ v.asIdeal := fun hθ => v.isPrime.ne_top <| (Ideal.eq_top_iff_one _).mpr <| by
    simpa [TauCeti.NumberField.Sqrt5.mul_sub_one_eq_one hmin] using
      v.asIdeal.mul_mem_right (θ - 1) hθ
  refine hilbertSymbol_unitAtFinitePlace_eq_one ?_ ?_ (by simp)
  · have h := (v.valuation_eq_one_iff_notMem (K := K)).mpr h2
    rwa [map_ofNat] at h
  · rw [coe_thetaUnit]
    exact (v.valuation_eq_one_iff_notMem (K := K)).mpr hθ

open scoped Classical in
/-- At the prime `(2)` the symbol `(θ, -1)_2` is `-1`. This is read off from Hilbert's product
formula: the symbol is trivial at every other finite place, and of
the two real symbols exactly one is `-1`, because `θ` is negative at exactly one real place. -/
private theorem hilbertSymbol_thetaUnit_neg_one_of_eq (hmin : minpoly ℤ θ = X ^ 2 - X - 1)
    (hgen : Algebra.adjoin ℚ {(θ : K)} = ⊤) {v₂ : HeightOneSpectrum (𝓞 K)}
    (hv₂ : v₂.asIdeal = Ideal.span {(2 : 𝓞 K)}) :
    hilbertSymbol (v₂.unitAtFinitePlace (thetaUnit hmin)) (v₂.unitAtFinitePlace (-1)) = -1 := by
  have hpf := hilbertSymbol_productFormula (thetaUnit hmin) (-1)
  rw [finprod_eq_single _ v₂ fun v hv =>
    hilbertSymbol_thetaUnit_neg_one_of_ne hmin hgen (hv₂ ▸ fun h => hv (HeightOneSpectrum.ext h))]
    at hpf
  -- The two real symbols multiply to `-1`.
  obtain ⟨w₁, w₂, hne, hw, hθ₁, hθ₂⟩ :=
    TauCeti.NumberField.Sqrt5.exists_realPlaces_pos_neg hmin hgen
  have hreal : ∏ w : {w : InfinitePlace K // w.IsReal},
      hilbertSymbol (unitAtRealPlace w (thetaUnit hmin)) (unitAtRealPlace w (-1)) = -1 := by
    rw [hw, Finset.prod_pair hne,
      (hilbertSymbol_unitAtRealPlace_eq_one_iff _ _ _).mpr (by simp [coe_thetaUnit, hθ₁]),
      (hilbertSymbol_unitAtRealPlace_eq_neg_one_iff _ _ _).mpr (by simp [coe_thetaUnit, hθ₂]),
      one_mul]
  rwa [hreal, mul_neg_one, neg_eq_iff_eq_neg] at hpf

open scoped Classical in
/-- **The local invariants of `⟨1, θ, θ⟩` over `ℚ(√5)`.** The diagonal form `⟨1, θ, θ⟩` has rank
three and trivial plain discriminant; its finite Hasse sign is `-1` exactly at the prime `(2)`,
and its positive index at a real place `w` is three where `θ` is positive and one where `θ` is
negative. -/
theorem globalInvariants_weightedSumSquares_one_self_self (hmin : minpoly ℤ θ = X ^ 2 - X - 1)
    (hgen : Algebra.adjoin ℚ {(θ : K)} = ⊤)
    (h : (weightedSumSquares K ![1, (θ : K), (θ : K)]).Nondegenerate) :
    _root_.QuadraticForm.globalInvariants (weightedSumSquares K ![1, (θ : K), (θ : K)]) h =
      { rank := 3, discr := 0,
        finiteHasse := fun v => if v.asIdeal = Ideal.span {(2 : 𝓞 K)} then -1 else 1,
        realPositiveIndex := fun w => if 0 < embedding_of_isReal w.2 (θ : K) then 3 else 1 } := by
  set u := thetaUnit hmin
  have he : (weightedSumSquares K ![1, (θ : K), (θ : K)]).Equivalent
      (weightedSumSquares K fun i => ((![1, u, u] : Fin 3 → Kˣ) i : K)) := by
    have hcoeff : (fun i => ((![1, u, u] : Fin 3 → Kˣ) i : K)) = ![1, (θ : K), (θ : K)] := by
      funext i
      fin_cases i <;> simp [u, coe_thetaUnit]
    rw [hcoeff]
  refine GlobalFormInvariants.ext ?_ ?_ ?_ ?_
  · simp
  · rw [_root_.QuadraticForm.globalInvariants_discr, discr_formClass _ _ ⟨3, ![1, u, u]⟩
      (by rwa [presentedForm_eq_weightedSumSquares_coe]), Fin.prod_univ_three,
      squareClass_eq_zero_iff]
    exact ⟨u, by simp⟩
  · funext v
    have hneg : v.unitAtFinitePlace (-1) = -1 := Units.ext (by simp)
    rw [_root_.QuadraticForm.globalInvariants_finiteHasse,
      _root_.QuadraticForm.finiteHasse_eq_prod_hilbertSymbol _ _ he v]
    simp only [Fin.prod_univ_three, show Finset.Ioi (0 : Fin 3) = {1, 2} by decide,
      show Finset.Ioi (1 : Fin 3) = {2} by decide, show Finset.Ioi (2 : Fin 3) = ∅ by decide]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
      Matrix.tail_cons, map_one, hilbertSymbol_one_left, Finset.prod_const_one,
      Finset.prod_singleton, Finset.prod_empty, one_mul, mul_one]
    rw [hilbertSymbol_self, ← hneg]
    split_ifs with hv
    · exact hilbertSymbol_thetaUnit_neg_one_of_eq hmin hgen hv
    · exact hilbertSymbol_thetaUnit_neg_one_of_ne hmin hgen hv
  · funext w
    rw [_root_.QuadraticForm.globalInvariants_realPositiveIndex,
      _root_.QuadraticForm.realPositiveIndex_weightedSumSquares]
    dsimp only
    split_ifs with hθ
    · have hset : {i | 0 < embedding_of_isReal w.2 (![1, (θ : K), (θ : K)] i)} = Set.univ := by
        ext i
        fin_cases i <;> simp [hθ]
      rw [hset, Set.ncard_univ, Nat.card_eq_fintype_card, Fintype.card_fin]
    · have hset : {i | 0 < embedding_of_isReal w.2 (![1, (θ : K), (θ : K)] i)} = {0} := by
        ext i
        fin_cases i <;> simp [hθ]
      rw [hset, Set.ncard_singleton]

end GlobalForm

open scoped Classical in
/-- Over `ℚ(√5)` there is an admissible rank-three system of trivial discriminant, with
positive indices three and one at its two real places and Hasse sign `-1` exactly at the
prime `(2)`. The finite and real local forms realizing this system are regular, and the system is
that of the regular global form `⟨1, θ, θ⟩`. -/
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
        (∃ (U : ∀ v : HeightOneSpectrum (𝓞 K),
            _root_.QuadraticForm (v.adicCompletion K) (Fin I.rank → v.adicCompletion K))
          (R : {w : InfinitePlace K // w.IsReal} → _root_.QuadraticForm ℝ (Fin I.rank → ℝ)),
          I.IsLocalRealization U R) ∧
        ∃ (Q : _root_.QuadraticForm K (Fin 3 → K)) (hQ : Q.Nondegenerate),
          Q.globalInvariants hQ = I := by
  classical
  -- The inert prime above two is the principal ideal `(2)`.
  have hprime : (Ideal.span {(2 : 𝓞 K)}).IsPrime := by
    simpa only [Ideal.map_span, Set.image_singleton, map_ofNat] using
      TauCeti.NumberField.Sqrt5.isPrime_map_span_two hmin hgen
  let v₂ : HeightOneSpectrum (𝓞 K) :=
    ⟨Ideal.span {(2 : 𝓞 K)}, hprime, by simp⟩
  -- Enumerate both real places, so the real Hasse product has exactly two factors.
  -- Order them so that `θ` is positive at the first and negative at the second.
  obtain ⟨w₁, w₂, hne, hw, hθ₁, hθ₂⟩ :=
    TauCeti.NumberField.Sqrt5.exists_realPlaces_pos_neg hmin hgen
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
  have hw' (w : {w : InfinitePlace K // w.IsReal}) : w = w₁ ∨ w = w₂ := by
    have : w ∈ (Finset.univ : Finset {w : InfinitePlace K // w.IsReal}) := Finset.mem_univ w
    simpa [hw] using this
  have hQ : (weightedSumSquares K ![1, (θ : K), (θ : K)]).Nondegenerate :=
    nondegenerate_weightedSumSquares fun i => by
      fin_cases i
      exacts [isRegular_one, (thetaUnit hmin).isUnit.isRegular, (thetaUnit hmin).isUnit.isRegular]
  refine ⟨v₂, w₁, w₂, rfl, hne, hw', I, hI, rfl, rfl, fun _ => rfl, ?_, ?_,
    hI.exists_isLocalRealization, _, hQ, ?_⟩
  · simp [I]
  · simp [I, hne.symm]
  -- The global form `⟨1, θ, θ⟩` has exactly these invariants.
  rw [globalInvariants_weightedSumSquares_one_self_self hmin hgen hQ]
  refine GlobalFormInvariants.ext rfl rfl (funext fun v => ?_) (funext fun w => ?_)
  · simp [I, v₂, HeightOneSpectrum.ext_iff]
  · rcases hw' w with rfl | rfl
    · simp [I, hθ₁]
    · simp [I, hθ₂.not_gt, hne.symm]

end TauCeti.NumberField.QuadraticForm.Sqrt5
