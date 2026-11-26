/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.Padics.HeightOneSpectrum
public import TauCeti.RingTheory.DedekindDomain.AdicValuation.LocalDegree

import TauCeti.RingTheory.DedekindDomain.AdicValuation.Norm

/-!
# Completions of a number field of local degree one over `ℚ_p`

Let `L` be a number field and `w` a finite place of `L` over the prime `p`. If the local degree
`[L_w : ℚ_p]` is `1`, then `L_w` is isomorphic to `ℚ_[p]` as a topological `ℚ`-algebra.

## Main results

* `IsDedekindDomain.HeightOneSpectrum.adicCompletionEquivPadic`: when `[L_w : ℚ_p] = 1`, the
  continuous `ℚ`-algebra isomorphism `L_w ≃A[ℚ] ℚ_[p]`. It inverts the completion map from the
  `p`-adic completion of `ℚ` to `L_w` and then applies the inverse of Mathlib's
  `Padic.adicCompletionEquiv`.
-/

public section

noncomputable section

open NumberField
open scoped AdicCompletionExtension

namespace IsDedekindDomain.HeightOneSpectrum

variable {L : Type*} [Field L] [NumberField L] (w : HeightOneSpectrum (𝓞 L))

/-- **Completions of local degree one over `ℚ_p` are `ℚ_p`.** If `w` is a finite place of the
number field `L` over the prime `p` and the local degree `[L_w : ℚ_p]` is `1`, then `L_w` is
isomorphic to `ℚ_[p]` as a topological `ℚ`-algebra. The isomorphism inverts the completion map from
the `p`-adic completion of `ℚ` to `L_w`
(`IsDedekindDomain.HeightOneSpectrum.adicCompletionExtensionEquiv`) and then applies the inverse of
Mathlib's `Padic.adicCompletionEquiv`; `adicCompletionEquivPadic_symm_apply` and
`adicCompletionEquivPadic_adicCompletionExtension` record how it acts. -/
noncomputable def adicCompletionEquivPadic (p : ℕ) [Fact p.Prime]
    [w.asIdeal.LiesOver ((Rat.HeightOneSpectrum.primesEquiv (R := ℤ)).symm ⟨p, Fact.out⟩).asIdeal]
    (h : Module.finrank
      (((Rat.HeightOneSpectrum.primesEquiv (R := ℤ)).symm ⟨p, Fact.out⟩).adicCompletion ℚ)
      (w.adicCompletion L) = 1) :
    w.adicCompletion L ≃A[ℚ] ℚ_[p] :=
  -- `adicCompletionExtensionEquiv` is linear over the `p`-adic completion of `ℚ`, and the
  -- `ℚ`-algebra structure on that completion in `Padic.adicCompletionEquiv` is not reducibly
  -- `DivisionRing.toRatAlgebra`, so the two are composed as ring isomorphisms.
  let v := (Rat.HeightOneSpectrum.primesEquiv (R := ℤ)).symm ⟨p, Fact.out⟩
  let f := adicCompletionExtensionEquiv v w h
  let φ := Padic.adicCompletionEquiv ℤ ⟨p, Fact.out⟩
  { (f.symm.toAlgEquiv.toRingEquiv.trans
      (φ : ℚ_[p] ≃+* v.adicCompletion ℚ).symm).toRatAlgEquiv with
    continuous_toFun := (HomeomorphClass.inv_continuous φ).comp f.symm.continuous
    continuous_invFun := f.continuous.comp (map_continuous φ) }

/-- The inverse of `adicCompletionEquivPadic` is Mathlib's `Padic.adicCompletionEquiv` followed by
the completion map from the `p`-adic completion of `ℚ` to `L_w`. -/
@[simp]
theorem adicCompletionEquivPadic_symm_apply (p : ℕ) [Fact p.Prime]
    [w.asIdeal.LiesOver ((Rat.HeightOneSpectrum.primesEquiv (R := ℤ)).symm ⟨p, Fact.out⟩).asIdeal]
    (h : Module.finrank
      (((Rat.HeightOneSpectrum.primesEquiv (R := ℤ)).symm ⟨p, Fact.out⟩).adicCompletion ℚ)
      (w.adicCompletion L) = 1) (x : ℚ_[p]) :
    (adicCompletionEquivPadic w p h).symm x = adicCompletionExtension ℚ L
      ((Rat.HeightOneSpectrum.primesEquiv (R := ℤ)).symm ⟨p, Fact.out⟩) w
      (Padic.adicCompletionEquiv ℤ ⟨p, Fact.out⟩ x) := by
  let f := adicCompletionExtensionEquiv _ w h
  let φ : ℚ_[p] ≃+*
      ((Rat.HeightOneSpectrum.primesEquiv (R := ℤ)).symm ⟨p, Fact.out⟩).adicCompletion ℚ :=
    Padic.adicCompletionEquiv ℤ ⟨p, Fact.out⟩
  rw [ContinuousAlgEquiv.symm_apply_eq, ← coe_adicCompletionExtensionEquiv _ w h]
  -- By definition, `adicCompletionEquivPadic` applies `f.symm` and then `φ.symm`, which cancel
  -- `φ` and `f`.
  exact (φ.symm_apply_apply x).symm.trans (congr_arg φ.symm (f.symm_apply_apply (φ x)).symm)

/-- `adicCompletionEquivPadic` sends the image in `L_w` of `x ∈ ℚ_[p]` under the completion map
back to `x`. -/
@[simp]
theorem adicCompletionEquivPadic_adicCompletionExtension (p : ℕ) [Fact p.Prime]
    [w.asIdeal.LiesOver ((Rat.HeightOneSpectrum.primesEquiv (R := ℤ)).symm ⟨p, Fact.out⟩).asIdeal]
    (h : Module.finrank
      (((Rat.HeightOneSpectrum.primesEquiv (R := ℤ)).symm ⟨p, Fact.out⟩).adicCompletion ℚ)
      (w.adicCompletion L) = 1) (x : ℚ_[p]) :
    adicCompletionEquivPadic w p h (adicCompletionExtension ℚ L
      ((Rat.HeightOneSpectrum.primesEquiv (R := ℤ)).symm ⟨p, Fact.out⟩) w
      (Padic.adicCompletionEquiv ℤ ⟨p, Fact.out⟩ x)) = x := by
  rw [← adicCompletionEquivPadic_symm_apply w p h, ContinuousAlgEquiv.apply_symm_apply]

end IsDedekindDomain.HeightOneSpectrum
