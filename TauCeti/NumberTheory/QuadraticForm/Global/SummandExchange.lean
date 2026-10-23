/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.QuadraticForm.Global.Classification
public import TauCeti.NumberTheory.QuadraticForm.Global.Operations
import TauCeti.LinearAlgebra.QuadraticForm.Witt.Cancellation

/-!
# Exchanging orthogonal summands at a place

Let `P`, `P'` and `W` be regular quadratic forms over a number field `K`, where `P` and `P'` have
the same rank and the same discriminant at a finite place `v`. At `v` there are at most two
isometry classes with a given rank and discriminant, distinguished by the local Hasse invariant.
So if `P_v ≄ P'_v`, and `U` is a regular form over `K_v` with the rank and discriminant of `W_v`
but `W_v ≄ U`, the Hasse invariants change twice and

```text
(P ⊥ W)_v ≅ P'_v ⊥ U.
```

In particular `P'_v` is represented by `(P ⊥ W)_v`, with orthogonal complement `U`.

Now let `V` be a regular form with `P' ⊥ V ≅ P ⊥ W` over `K`. Witt cancellation identifies the
localizations of `V`:

* where `P` and `P'` are isometric, at a finite or a real place, `V` is isometric to `W`;
* at a finite place `v` where `P_v ≄ P'_v`, `V_v` is isometric to every regular form `U` of the
  rank and discriminant of `W_v` with `W_v ≄ U`.

This is the local half of O'Meara's construction of a global form with prescribed localizations.
There `W` matches the prescribed local forms `U_v` except at a finite set `R` of finite places, and
the correction planes `P = ⟨1, -β⟩` and `P' = ⟨α, -αβ⟩` are chosen to be nonisometric exactly at the
places of `R`. A global representation of `P'` by `P ⊥ W` then has an orthogonal complement `V`
with `V_v ≅ U_v` at every place.

## Main results

* `QuadraticForm.atFinitePlace_prod_equivalent_prod_of_not_equivalent`: the local exchange
  `(P ⊥ W)_v ≅ P'_v ⊥ U`.
* `QuadraticForm.atFinitePlace_equivalent_of_prod_equivalent_prod_of_equivalent`,
  `QuadraticForm.atRealPlace_equivalent_of_prod_equivalent_prod_of_equivalent`: if
  `P' ⊥ V ≅ P ⊥ W` and `P` and `P'` are isometric at a place, so are `V` and `W`.
* `QuadraticForm.atFinitePlace_equivalent_of_prod_equivalent_prod_of_not_equivalent`: if
  `P' ⊥ V ≅ P ⊥ W` and `P_v ≄ P'_v`, then `V_v ≅ U` for every `U` as above.

## References

* O. T. O'Meara, *Introduction to Quadratic Forms*, Springer (1963), 63:20 and 72:1.
-/

public section

open IsDedekindDomain NumberField TauCeti

universe u

namespace QuadraticForm

variable {K : Type u} [Field K]
variable {V₁ V₂ V₃ V₄ : Type*} [AddCommGroup V₁] [Module K V₁] [AddCommGroup V₂] [Module K V₂]
  [AddCommGroup V₃] [Module K V₃] [AddCommGroup V₄] [Module K V₄]
variable {P : _root_.QuadraticForm K V₁} {P' : _root_.QuadraticForm K V₂}
  {W : _root_.QuadraticForm K V₃} {V : _root_.QuadraticForm K V₄}

/-- **Exchanging summands at a finite place.** Suppose `P` and `P'` have the same rank and the same
discriminant at `v` but `P_v ≄ P'_v`, and `U` is a regular form over `K_v` with the rank and
discriminant of `W_v` but `W_v ≄ U`. Then `(P ⊥ W)_v ≅ P'_v ⊥ U`. -/
theorem atFinitePlace_prod_equivalent_prod_of_not_equivalent [NumberField K]
    [FiniteDimensional K V₁] [FiniteDimensional K V₂] [FiniteDimensional K V₃]
    (hP : P.Nondegenerate) (hP' : P'.Nondegenerate) (hW : W.Nondegenerate)
    {v : HeightOneSpectrum (𝓞 K)} (hPr : Module.finrank K V₁ = Module.finrank K V₂)
    (hPd : (algebraMap K (v.adicCompletion K)).squareClassMap
        (RegularFormClass.discr (formClass P hP)) =
      (algebraMap K (v.adicCompletion K)).squareClassMap
        (RegularFormClass.discr (formClass P' hP')))
    (hPP' : ¬ (P.atFinitePlace v).Equivalent (P'.atFinitePlace v))
    {X : Type*} [AddCommGroup X] [Module (v.adicCompletion K) X]
    [FiniteDimensional (v.adicCompletion K) X] {U : _root_.QuadraticForm (v.adicCompletion K) X}
    (hU : U.Nondegenerate) (hUr : Module.finrank K V₃ = Module.finrank (v.adicCompletion K) X)
    (hUd : (algebraMap K (v.adicCompletion K)).squareClassMap
        (RegularFormClass.discr (formClass W hW)) = RegularFormClass.discr (formClass U hU))
    (hWU : ¬ (W.atFinitePlace v).Equivalent U) :
    (atFinitePlace (P.prod W) v).Equivalent ((P'.atFinitePlace v).prod U) := by
  have hPv := Nondegenerate.atFinitePlace hP v
  have hP'v := Nondegenerate.atFinitePlace hP' v
  have hWv := Nondegenerate.atFinitePlace hW v
  -- Compare the classes `[P_v] + [W_v]` and `[P'_v] + [U]` by the local exchange lemma.
  have key : formClass _ hPv + formClass _ hWv = formClass _ hP'v + formClass _ hU := by
    refine (RegularFormClass.add_eq_add_iff_ne ?_ ?_ ?_ ?_ ?_).mpr ?_
    · simp [hPr]
    · rw [formClass_atFinitePlace P hP, formClass_atFinitePlace P' hP',
        RegularFormClass.discr_baseChange, RegularFormClass.discr_baseChange, hPd]
    · rwa [Ne, formClass_eq_iff]
    · simp [hUr]
    · rw [formClass_atFinitePlace W hW, RegularFormClass.discr_baseChange, hUd]
    · rwa [Ne, formClass_eq_iff]
  rw [← formClass_prod, ← formClass_prod, formClass_eq_iff] at key
  have hprod : (atFinitePlace (P.prod W) v).Equivalent
      ((P.atFinitePlace v).prod (W.atFinitePlace v)) := ⟨atFinitePlaceProd P W v⟩
  exact hprod.trans key

/-- If `P' ⊥ V ≅ P ⊥ W` over `K` and `P_v ≅ P'_v` at a finite place `v`, then `V_v ≅ W_v`. -/
theorem atFinitePlace_equivalent_of_prod_equivalent_prod_of_equivalent [NumberField K]
    [FiniteDimensional K V₂] (hP' : P'.Nondegenerate) (h : (P'.prod V).Equivalent (P.prod W))
    {v : HeightOneSpectrum (𝓞 K)} (hPP' : (P.atFinitePlace v).Equivalent (P'.atFinitePlace v)) :
    (V.atFinitePlace v).Equivalent (W.atFinitePlace v) := by
  have h₁ : ((P'.atFinitePlace v).prod (V.atFinitePlace v)).Equivalent
      (atFinitePlace (P'.prod V) v) := ⟨(atFinitePlaceProd P' V v).symm⟩
  have h₂ : (atFinitePlace (P.prod W) v).Equivalent
      ((P.atFinitePlace v).prod (W.atFinitePlace v)) := ⟨atFinitePlaceProd P W v⟩
  exact equivalent_of_equivalent_prod (Nondegenerate.atFinitePlace hP' v)
    (h₁.trans ((h.atFinitePlace v).trans (h₂.trans (hPP'.prod (.refl _)))))

/-- If `P' ⊥ V ≅ P ⊥ W` over `K` and `P_w ≅ P'_w` at a real place `w`, then `V_w ≅ W_w`. -/
theorem atRealPlace_equivalent_of_prod_equivalent_prod_of_equivalent [FiniteDimensional K V₂]
    (hP' : P'.Nondegenerate) (h : (P'.prod V).Equivalent (P.prod W))
    {w : {w : InfinitePlace K // w.IsReal}}
    (hPP' : (P.atRealPlace w).Equivalent (P'.atRealPlace w)) :
    (V.atRealPlace w).Equivalent (W.atRealPlace w) := by
  have h₁ : ((P'.atRealPlace w).prod (V.atRealPlace w)).Equivalent
      (atRealPlace (P'.prod V) w) := ⟨(atRealPlaceProd P' V w).symm⟩
  have h₂ : (atRealPlace (P.prod W) w).Equivalent
      ((P.atRealPlace w).prod (W.atRealPlace w)) := ⟨atRealPlaceProd P W w⟩
  exact equivalent_of_equivalent_prod (Nondegenerate.atRealPlace hP' w)
    (h₁.trans ((h.atRealPlace w).trans (h₂.trans (hPP'.prod (.refl _)))))

/-- **The local complement after an exchange.** Suppose `P' ⊥ V ≅ P ⊥ W` over `K`, where `P` and
`P'` have the same rank and the same discriminant at a finite place `v` but `P_v ≄ P'_v`. Then
`V_v` is isometric to every regular form `U` over `K_v` with the rank and discriminant of `W_v`
and `W_v ≄ U`. -/
theorem atFinitePlace_equivalent_of_prod_equivalent_prod_of_not_equivalent [NumberField K]
    [FiniteDimensional K V₁] [FiniteDimensional K V₂] [FiniteDimensional K V₃]
    (hP : P.Nondegenerate) (hP' : P'.Nondegenerate) (hW : W.Nondegenerate)
    (h : (P'.prod V).Equivalent (P.prod W)) {v : HeightOneSpectrum (𝓞 K)}
    (hPr : Module.finrank K V₁ = Module.finrank K V₂)
    (hPd : (algebraMap K (v.adicCompletion K)).squareClassMap
        (RegularFormClass.discr (formClass P hP)) =
      (algebraMap K (v.adicCompletion K)).squareClassMap
        (RegularFormClass.discr (formClass P' hP')))
    (hPP' : ¬ (P.atFinitePlace v).Equivalent (P'.atFinitePlace v))
    {X : Type*} [AddCommGroup X] [Module (v.adicCompletion K) X]
    [FiniteDimensional (v.adicCompletion K) X] {U : _root_.QuadraticForm (v.adicCompletion K) X}
    (hU : U.Nondegenerate) (hUr : Module.finrank K V₃ = Module.finrank (v.adicCompletion K) X)
    (hUd : (algebraMap K (v.adicCompletion K)).squareClassMap
        (RegularFormClass.discr (formClass W hW)) = RegularFormClass.discr (formClass U hU))
    (hWU : ¬ (W.atFinitePlace v).Equivalent U) :
    (V.atFinitePlace v).Equivalent U := by
  have h₁ : ((P'.atFinitePlace v).prod (V.atFinitePlace v)).Equivalent
      (atFinitePlace (P'.prod V) v) := ⟨(atFinitePlaceProd P' V v).symm⟩
  exact equivalent_of_equivalent_prod (Nondegenerate.atFinitePlace hP' v)
    (h₁.trans ((h.atFinitePlace v).trans
      (atFinitePlace_prod_equivalent_prod_of_not_equivalent hP hP' hW hPr hPd hPP' hU hUr hUd
        hWU)))

end QuadraticForm
