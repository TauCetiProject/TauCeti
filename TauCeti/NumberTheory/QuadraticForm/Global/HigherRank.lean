/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.QuadraticForm.RegularFormClass.Basic
public import TauCeti.NumberTheory.QuadraticForm.Global.ApproximateValue
public import TauCeti.NumberTheory.QuadraticForm.Global.LocalValues
import TauCeti.NumberTheory.QuadraticForm.Global.AnisotropicPlaces

/-!
# The Hasse–Minkowski induction step in rank at least five

Let `Q` be a regular quadratic form over a number field `K` of rank `n ≥ 5` which is isotropic at
every finite and real place. This file shows that `Q` is isotropic over `K` as soon as every
locally isotropic regular form of rank `n - 1` is isotropic over `K`. Together with the cases of
rank two, three and four, this is the inductive structure of the Hasse–Minkowski theorem.

## Main results

* `QuadraticForm.LocallyRepresentsScalar.isLocallyIsotropic_smul_sq_prod`: if `W` represents a
  nonzero scalar `a` at every finite and real place, then `⟨-a⟩ ⊥ W` is locally isotropic.
* `QuadraticForm.not_anisotropic_prod_of_isLocallyIsotropic`: if `U ⊥ W` is locally isotropic,
  with `U` regular on a nonzero space and `W` regular of rank at least three, and every locally
  isotropic form `⟨c⟩ ⊥ W` is isotropic over `K`, then `U ⊥ W` is isotropic over `K`.
* `QuadraticForm.not_anisotropic_of_isLocallyIsotropic_of_five_le_finrank`: the induction step
  from rank `n - 1` to rank `n ≥ 5`, with the induction hypothesis stated for diagonal forms.

## References

* O. T. O'Meara, *Introduction to Quadratic Forms* (1973), 66:1, the case of dimension at least
  five.
* J.-P. Serre, *A Course in Arithmetic*, Chapter IV, §3.2, Theorem 8, the case `n ≥ 5`.
-/

/- Write `Q ≅ U ⊥ W` with `U` binary and `W` of rank `n - 2 ≥ 3`. The form `W` is anisotropic
at only finitely many finite places, and at each finite or real place where it is anisotropic,
local isotropy of `Q` gives vectors `x_v` of `U` and `y_v` of `W` with
`U(x_v) = -W(y_v) ≠ 0`. Weak approximation of vectors then produces a global vector `x` of `U`
with `b := U(x) ≠ 0` such that `-b` is represented by `W` at every finite and real place.
Thus `⟨b⟩ ⊥ W` is locally isotropic; the induction hypothesis makes it isotropic over `K`,
hence `W` represents `-b` over `K`, and the two global vectors give an isotropic vector of
`U ⊥ W`. The summand `U` need not be binary for this argument: any regular form on a nonzero
space works, as in `QuadraticForm.not_anisotropic_prod_of_isLocallyIsotropic`. -/

public section

open IsDedekindDomain NumberField NumberField.InfinitePlace QuadraticMap
open scoped TensorProduct

namespace TauCeti

variable {K : Type*} [Field K] [NumberField K]
  {X Y : Type*} [AddCommGroup X] [Module K X] [AddCommGroup Y] [Module K Y]

variable [FiniteDimensional K X] [FiniteDimensional K Y]

/-- Let `U` be a regular quadratic form on a nonzero space and `W` a regular quadratic form of rank
at least three over a number field, such that `U ⊥ W` is isotropic at every finite and real place.
If every form `⟨c⟩ ⊥ W` with `c ≠ 0` that is isotropic at every finite and real place is isotropic
over `K`, then `U ⊥ W` is isotropic over `K`. -/
theorem _root_.QuadraticForm.not_anisotropic_prod_of_isLocallyIsotropic [Nontrivial X]
    {U : QuadraticForm K X} {W : QuadraticForm K Y} (hU : U.Nondegenerate)
    (hW : W.Nondegenerate) (hY : 3 ≤ Module.finrank K Y)
    (hUW : QuadraticForm.IsLocallyIsotropic (U.prod W))
    (ih : ∀ c : K, c ≠ 0 →
      QuadraticForm.IsLocallyIsotropic ((c • (sq : QuadraticForm K K)).prod W) →
      ¬((c • (sq : QuadraticForm K K)).prod W).Anisotropic) :
    ¬(U.prod W).Anisotropic := by
  have : Nontrivial Y := Module.nontrivial_of_finrank_pos (R := K) (by omega)
  rw [QuadraticForm.isLocallyIsotropic_iff] at hUW
  refine U.not_anisotropic_prod_of_forall_represents W hU.ne_zero hW
    (W.finite_setOfPred_anisotropic_atFinitePlace hY)
    (fun v hv => QuadraticForm.exists_atFinitePlace_ne_zero_eq_neg (hUW.1 v) hU hv)
    (fun w hw => QuadraticForm.exists_atRealPlace_ne_zero_eq_neg (hUW.2 w) hU hw)
    fun b hb hloc => ?_
  -- `⟨-b⟩ ⊥ W` is locally isotropic, hence isotropic, so `W` represents `b` over `K`.
  have hiso := ih (-b) (neg_ne_zero.mpr hb) (hloc.isLocallyIsotropic_smul_sq_prod hb)
  rw [Equivalent.anisotropic_iff ⟨IsometryEquiv.prodComm _ W⟩] at hiso
  exact mem_unitValueSet.mp
    ((mem_unitValueSet_iff_not_anisotropic_prod W hW (Units.mk0 b hb)).mpr hiso)

/-- **The Hasse–Minkowski induction step in rank at least five.** Let `Q` be a regular quadratic
form of rank `n ≥ 5` over a number field that is isotropic at every finite and real place. If every
diagonal regular form of rank `n - 1` that is isotropic at every finite and real place is isotropic
over `K`, then `Q` is isotropic over `K`. -/
theorem _root_.QuadraticForm.not_anisotropic_of_isLocallyIsotropic_of_five_le_finrank
    {Q : QuadraticForm K X} (hQ : Q.Nondegenerate) (hX : 5 ≤ Module.finrank K X)
    (hloc : Q.IsLocallyIsotropic)
    (ih : ∀ p : RegularFormPresentation K, p.1 + 1 = Module.finrank K X →
      (presentedForm p).IsLocallyIsotropic → ¬(presentedForm p).Anisotropic) :
    ¬Q.Anisotropic := by
  let : Invertible (2 : K) := invertibleOfNonzero two_ne_zero
  obtain ⟨⟨n, w⟩, hQw⟩ := exists_presentedForm_equivalent Q hQ
  have hn : n = Module.finrank K X := by
    obtain ⟨e⟩ := hQw
    simpa using e.toLinearEquiv.finrank_eq.symm
  obtain ⟨m, rfl⟩ : ∃ m, n = 2 + m := ⟨n - 2, by omega⟩
  -- Split the diagonalization as a binary summand `U` and a complement `W` of rank `m ≥ 3`.
  let U := presentedForm ⟨2, fun i => w (Fin.castAdd m i)⟩
  let W := presentedForm ⟨m, fun j => w (Fin.natAdd 2 j)⟩
  have hsplit : Q.Equivalent (U.prod W) := by
    refine hQw.trans ?_
    have happ : RegularFormPresentation.append ⟨2, fun i => w (Fin.castAdd m i)⟩
        ⟨m, fun j => w (Fin.natAdd 2 j)⟩ = ⟨2 + m, w⟩ := by
      refine RegularFormPresentation.ext (RegularFormPresentation.fst_append _ _) fun i => ?_
      obtain ⟨j, rfl⟩ : ∃ j, i = Fin.cast (RegularFormPresentation.fst_append _ _).symm j :=
        ⟨Fin.cast (RegularFormPresentation.fst_append _ _) i, by simp⟩
      induction j using Fin.addCases with
      | left k => exact RegularFormPresentation.append_apply_castAdd _ _ k
      | right k => exact RegularFormPresentation.append_apply_natAdd _ _ k
    have := equivalent_presentedForm_append_prod ⟨2, fun i => w (Fin.castAdd m i)⟩
      ⟨m, fun j => w (Fin.natAdd 2 j)⟩
    rwa [happ] at this
  rw [hsplit.anisotropic_iff]
  refine QuadraticForm.not_anisotropic_prod_of_isLocallyIsotropic (nondegenerate_presentedForm _)
    (nondegenerate_presentedForm _) (by rw [Module.finrank_fin_fun]; dsimp only; omega)
    ((QuadraticForm.QuadraticMap.Equivalent.isLocallyIsotropic_iff hsplit).mp hloc)
    fun c hc hcW => ?_
  -- `⟨c⟩ ⊥ W` is the diagonal form of rank `m + 1` obtained by prepending the weight `c`.
  have hcons : ((c • (sq : QuadraticForm K K)).prod W).Equivalent
      (presentedForm ⟨m + 1, Fin.cons (Units.mk0 c hc) fun j => w (Fin.natAdd 2 j)⟩) :=
    ⟨presentedFormConsIsometryEquiv (Fin.cons (Units.mk0 c hc) fun j => w (Fin.natAdd 2 j))⟩
  rw [hcons.anisotropic_iff]
  exact ih _ (by dsimp only; omega)
    ((QuadraticForm.QuadraticMap.Equivalent.isLocallyIsotropic_iff hcons).mp hcW)

end TauCeti
