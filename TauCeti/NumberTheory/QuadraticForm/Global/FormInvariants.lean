/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.QuadraticForm.Global.HasseSupport
public import TauCeti.NumberTheory.QuadraticForm.Global.Invariants
public import TauCeti.NumberTheory.QuadraticForm.Global.RealHasse
import Mathlib.Algebra.FiniteSupport.Basic
import TauCeti.NumberTheory.QuadraticForm.Global.HilbertSymbol

/-!
# The system of local invariants of a global quadratic form

A regular quadratic form `Q` of rank `n` over a number field `K` determines a system of local
invariants `Q.globalInvariants hQ : GlobalFormInvariants K`: its rank `n`, its plain discriminant
`d(Q) ∈ Kˣ/(Kˣ)²`, its Hasse sign `s_v(Q)` at every finite place `v`, and its positive index
`p_w(Q)` at every real place `w`. Isometric forms have the same system.

Apart from the positivity of the rank and the product relation, every condition of
`GlobalFormInvariants.IsAdmissible` holds for such a system:

* at a real place `p_w ≤ n`, and the image of `d(Q)` is `(-1)^(n - p_w)`, by the determinant-sign
  formula;
* the finite Hasse signs are trivial at almost every place;
* in rank one every finite Hasse sign is trivial, and in rank two `s_v(Q) = 1` wherever the image
  of `d(Q)` in `K_v` is the class of `-1`, since the localization is then a hyperbolic plane.

So the system of a form of positive rank is admissible exactly when its Hasse product is one. For
a diagonalization `Q ≅ ⟨a₁, …, aₙ⟩` over `K`, the Hasse product is
`∏_{i<j} (∏_v (aᵢ, aⱼ)_v · ∏_w (aᵢ, aⱼ)_w)` over the finite places `v` and real places `w`, so
the product relation follows from the product formula for the Hilbert symbol applied to each pair
of coefficients.

## Main definitions

* `QuadraticForm.globalInvariants`: the system of local invariants of a regular global form.

## Main results

* `QuadraticMap.Equivalent.globalInvariants_eq`: isometric forms have the same system.
* `QuadraticForm.globalInvariants_realHasse_eq_prod_hilbertSymbol`: the real Hasse sign of the
  system is `∏_{i<j} (aᵢ, aⱼ)_w` for any diagonalization.
* `QuadraticForm.globalInvariants_hasseProduct_eq_prod`: the Hasse product of the system as a
  product over the pairs of coefficients of a diagonalization.
* `QuadraticForm.isAdmissible_globalInvariants_iff`: the system is admissible exactly when the rank
  is positive and the Hasse product is one.
* `TauCeti.NumberField.QuadraticForm.globalInvariants_weightedSumSquares_one_self_neg`: the system
  of `⟨1, a, -a⟩` does not depend on `a`.

## References

* O. T. O'Meara, *Introduction to Quadratic Forms*, Springer (1963), 63:20–23 and 66:5–6 for the
  local invariants and their finite support, and 72:1 for the conditions they satisfy.
* J.-P. Serre, *A Course in Arithmetic*, Springer (1973), Chapter IV, §3.1 and §3.3, the same
  invariants and conditions over `ℚ`.
-/

public section
noncomputable section

open Finset IsDedekindDomain NumberField NumberField.InfinitePlace TauCeti
open TauCeti.NumberField.QuadraticForm (GlobalFormInvariants)

universe u v w

namespace QuadraticForm

variable {K : Type u} [Field K] [NumberField K]
variable {V : Type v} [AddCommGroup V] [Module K V] [FiniteDimensional K V]

/-- **The system of local invariants of a regular quadratic form** `Q` over a number field: its
rank, its plain discriminant `d(Q) ∈ Kˣ/(Kˣ)²`, its Hasse sign at every finite place and its
positive index at every real place. -/
def globalInvariants (Q : _root_.QuadraticForm K V) (hQ : Q.Nondegenerate) :
    GlobalFormInvariants K :=
  letI : Invertible (2 : K) := invertibleOfNonzero two_ne_zero
  { rank := Module.finrank K V
    discr := RegularFormClass.discr (formClass Q hQ)
    finiteHasse := Q.finiteHasse hQ
    realPositiveIndex := Q.realPositiveIndex }

variable (Q : _root_.QuadraticForm K V) (hQ : Q.Nondegenerate)

/-- The rank of the system of a form is the dimension of its space. -/
@[simp]
theorem globalInvariants_rank : (Q.globalInvariants hQ).rank = Module.finrank K V :=
  (rfl)

/-- The discriminant of the system of a form is its plain discriminant. -/
@[simp]
theorem globalInvariants_discr :
    letI : Invertible (2 : K) := invertibleOfNonzero two_ne_zero
    (Q.globalInvariants hQ).discr = RegularFormClass.discr (formClass Q hQ) :=
  (rfl)

/-- The finite Hasse signs of the system of a form are those of the form. -/
@[simp]
theorem globalInvariants_finiteHasse : (Q.globalInvariants hQ).finiteHasse = Q.finiteHasse hQ :=
  (rfl)

/-- The real positive indices of the system of a form are those of the form. -/
@[simp]
theorem globalInvariants_realPositiveIndex :
    (Q.globalInvariants hQ).realPositiveIndex = Q.realPositiveIndex :=
  (rfl)

/-- The discriminant of the system of a form at a finite place `v` is the discriminant of the
localization of the form at `v`. -/
theorem globalInvariants_discrAtFinitePlace (v : HeightOneSpectrum (𝓞 K)) :
    letI : Invertible (2 : v.adicCompletion K) :=
      (Invertible.map (algebraMap K (v.adicCompletion K)) 2).copy 2 (map_ofNat _ _).symm
    (Q.globalInvariants hQ).discrAtFinitePlace v =
      RegularFormClass.discr
        (formClass (Q.atFinitePlace v) (Nondegenerate.atFinitePlace hQ v)) := by
  rw [GlobalFormInvariants.discrAtFinitePlace_def, globalInvariants_discr, discr_atFinitePlace]

/-- The negative index of the system of a form at a real place is that of the form. -/
theorem globalInvariants_realNegativeIndex (w : {w : InfinitePlace K // w.IsReal}) :
    (Q.globalInvariants hQ).realNegativeIndex w = Q.realNegativeIndex w := by
  rw [GlobalFormInvariants.realNegativeIndex_def, globalInvariants_rank,
    globalInvariants_realPositiveIndex, ← realPositiveIndex_add_realNegativeIndex_eq_finrank hQ w,
    Nat.add_sub_cancel_left]

/-- **The real Hasse sign of the system of a form.** If `Q ≅ ⟨a₁, …, aₙ⟩` over `K`, the real
Hasse sign of the system of `Q` at a real place `w` is `∏_{i<j} (aᵢ, aⱼ)_w`, the product of the
real Hilbert symbols of the images of the coefficients. -/
theorem globalInvariants_realHasse_eq_prod_hilbertSymbol {n : ℕ} {a : Fin n → Kˣ}
    (h : Q.Equivalent (QuadraticMap.weightedSumSquares K fun i => (a i : K)))
    (w : {w : InfinitePlace K // w.IsReal}) :
    (Q.globalInvariants hQ).realHasse w =
      ∏ i, ∏ j ∈ Ioi i, hilbertSymbol (unitAtRealPlace w (a i)) (unitAtRealPlace w (a j)) := by
  rw [GlobalFormInvariants.realHasse_def, globalInvariants_realNegativeIndex,
    ← prod_hilbertSymbol_unitAtRealPlace_of_equiv_weightedSumSquares h w, prod_filter,
    Fintype.prod_prod_type]
  refine prod_congr rfl fun i _ => ?_
  rw [← prod_filter, filter_lt_eq_Ioi]

open scoped Classical in
/-- **The Hasse product of the system of a form**, computed on a diagonalization
`Q ≅ ⟨a₁, …, aₙ⟩` over `K`: it is the product over the pairs `i < j` of the products
`∏_v (aᵢ, aⱼ)_v · ∏_w (aᵢ, aⱼ)_w` of the Hilbert symbols of `aᵢ` and `aⱼ` over all finite places
`v` and all real places `w`. -/
theorem globalInvariants_hasseProduct_eq_prod {n : ℕ} {a : Fin n → Kˣ}
    (h : Q.Equivalent (QuadraticMap.weightedSumSquares K fun i => (a i : K))) :
    (Q.globalInvariants hQ).hasseProduct =
      ∏ i, ∏ j ∈ Ioi i,
        ((∏ᶠ v : HeightOneSpectrum (𝓞 K),
            hilbertSymbol (v.unitAtFinitePlace (a i)) (v.unitAtFinitePlace (a j))) *
          ∏ w : {w : InfinitePlace K // w.IsReal},
            hilbertSymbol (unitAtRealPlace w (a i)) (unitAtRealPlace w (a j))) := by
  rw [GlobalFormInvariants.hasseProduct_def, globalInvariants_finiteHasse,
    funext (Q.finiteHasse_eq_prod_hilbertSymbol hQ h),
    prod_congr rfl fun w _ => Q.globalInvariants_realHasse_eq_prod_hilbertSymbol hQ h w,
    finprod_prod_comm _ _ fun i _ => by fun_prop, prod_comm, ← prod_mul_distrib]
  refine prod_congr rfl fun i _ => ?_
  rw [finprod_prod_comm _ _ fun j _ => by fun_prop, prod_comm, ← prod_mul_distrib]

/-- **Admissibility of the system of a form.** The system of local invariants of a regular form
satisfies every admissibility condition except possibly the positivity of the rank and the
product relation, so it is admissible exactly when the rank is positive and the Hasse product is
one. -/
theorem isAdmissible_globalInvariants_iff :
    (Q.globalInvariants hQ).IsAdmissible ↔
      1 ≤ Module.finrank K V ∧ (Q.globalInvariants hQ).hasseProduct = 1 := by
  refine ⟨fun hI => ⟨hI.one_le_rank, hI.hasseProduct_eq_one⟩, fun ⟨hn, hprod⟩ => ⟨hn,
    fun w => ?_, fun w => ?_, ?_, fun h1 v => ?_, fun h2 v hd => ?_, hprod⟩⟩
  · rw [globalInvariants_rank, globalInvariants_realPositiveIndex,
      ← realPositiveIndex_add_realNegativeIndex_eq_finrank hQ w]
    exact Nat.le_add_right _ _
  · rw [GlobalFormInvariants.discrAtRealPlace_def, globalInvariants_discr,
      squareClassMap_discr_formClass_eq_realNegativeIndex_nsmul,
      globalInvariants_realNegativeIndex]
  · rw [globalInvariants_finiteHasse]
    exact hasFiniteMulSupport_finiteHasse Q hQ
  · rw [globalInvariants_finiteHasse]
    exact finiteHasse_eq_one_of_finrank_le_one Q hQ h1.le v
  · rw [GlobalFormInvariants.discrAtFinitePlace_def, globalInvariants_discr] at hd
    rw [globalInvariants_finiteHasse]
    exact finiteHasse_eq_one_of_finrank_eq_two Q hQ h2 hd

end QuadraticForm

namespace QuadraticMap.Equivalent

variable {K : Type u} [Field K] [NumberField K]
variable {V : Type v} [AddCommGroup V] [Module K V] [FiniteDimensional K V]
variable {W : Type w} [AddCommGroup W] [Module K W] [FiniteDimensional K W]

/-- Isometric regular forms have the same system of local invariants. -/
theorem globalInvariants_eq {Q : _root_.QuadraticForm K V} {R : _root_.QuadraticForm K W}
    (h : Q.Equivalent R) (hQ : Q.Nondegenerate) (hR : R.Nondegenerate) :
    Q.globalInvariants hQ = R.globalInvariants hR := by
  let _ : Invertible (2 : K) := invertibleOfNonzero two_ne_zero
  refine TauCeti.NumberField.QuadraticForm.GlobalFormInvariants.ext ?_ ?_ ?_ ?_
  · rw [QuadraticForm.globalInvariants_rank, QuadraticForm.globalInvariants_rank,
      h.some.toLinearEquiv.finrank_eq]
  · rw [QuadraticForm.globalInvariants_discr, QuadraticForm.globalInvariants_discr,
      (formClass_eq_iff Q hQ R hR).mpr h]
  · rw [QuadraticForm.globalInvariants_finiteHasse, QuadraticForm.globalInvariants_finiteHasse]
    exact funext (h.finiteHasse_eq hQ hR)
  · rw [QuadraticForm.globalInvariants_realPositiveIndex,
      QuadraticForm.globalInvariants_realPositiveIndex]
    exact funext h.realPositiveIndex_eq

end QuadraticMap.Equivalent

section OneSelfNeg

open QuadraticMap

namespace TauCeti.NumberField.QuadraticForm

/-- **The local invariants of `⟨1⟩ ⊥ ⟨a, -a⟩`.** Over a number field the system of local
invariants of `⟨1, a, -a⟩` does not depend on `a`: rank `3`, discriminant the class of `-1`,
trivial Hasse sign at every finite place, and positive index `2` at every real place. -/
theorem globalInvariants_weightedSumSquares_one_self_neg {K : Type*} [Field K] [NumberField K]
    (a : Kˣ) (h : (weightedSumSquares K ![1, (a : K), -(a : K)]).Nondegenerate) :
    _root_.QuadraticForm.globalInvariants (weightedSumSquares K ![1, (a : K), -(a : K)]) h =
      { rank := 3, discr := squareClass (-1), finiteHasse := 1,
        realPositiveIndex := fun _ => 2 } := by
  have he : (weightedSumSquares K ![1, (a : K), -(a : K)]).Equivalent
      (weightedSumSquares K fun i => ((![1, a, -a] : Fin 3 → Kˣ) i : K)) := by
    have hcoeff : (fun i => ((![1, a, -a] : Fin 3 → Kˣ) i : K)) = ![1, (a : K), -(a : K)] := by
      funext i
      fin_cases i <;> simp
    rw [hcoeff]
  refine GlobalFormInvariants.ext ?_ ?_ ?_ ?_
  · simp
  · rw [_root_.QuadraticForm.globalInvariants_discr, discr_formClass _ _ ⟨3, ![1, a, -a]⟩
      (by rwa [presentedForm_eq_weightedSumSquares_coe]), Fin.prod_univ_three,
      squareClass_eq_iff_isSquare_mul]
    exact ⟨a, by simp⟩
  · funext v
    have hneg : v.unitAtFinitePlace (-a) = -v.unitAtFinitePlace a := Units.ext (by simp)
    rw [_root_.QuadraticForm.globalInvariants_finiteHasse,
      _root_.QuadraticForm.finiteHasse_eq_prod_hilbertSymbol _ _ he v]
    simp [Fin.prod_univ_three, show Finset.Ioi (1 : Fin 3) = {2} by decide,
      show Finset.Ioi (2 : Fin 3) = ∅ by decide, hneg]
  · funext w
    rw [_root_.QuadraticForm.globalInvariants_realPositiveIndex,
      _root_.QuadraticForm.realPositiveIndex_weightedSumSquares]
    dsimp only
    -- Exactly one of `a` and `-a` is positive at `w`.
    rcases (map_ne_zero (InfinitePlace.embedding_of_isReal w.2)).mpr a.ne_zero |>.lt_or_gt with
      ha | ha
    · convert Set.ncard_pair (a := (0 : Fin 3)) (b := 2) (by decide)
      ext i
      fin_cases i <;> simp [ha, ha.not_gt]
    · convert Set.ncard_pair (a := (0 : Fin 3)) (b := 1) (by decide)
      ext i
      fin_cases i <;> simp [ha, ha.not_gt]

end TauCeti.NumberField.QuadraticForm

end OneSelfNeg
