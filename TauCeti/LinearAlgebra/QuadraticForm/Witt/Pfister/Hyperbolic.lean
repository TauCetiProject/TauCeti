/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Quaternion.SplittingCriterion
public import TauCeti.LinearAlgebra.QuadraticForm.Quaternary.Basic
public import TauCeti.LinearAlgebra.QuadraticForm.Witt.Pfister.Basic

/-!
# Isotropic two-fold Pfister forms are hyperbolic

For units `a, b` of a field `K` in which `2` is invertible, the two-fold Pfister form
`<<a, b>> = <1, -a, -b, ab>` is the norm form of the quaternion algebra `ℍ[K,a,b]`. This file
proves that the following are equivalent:

1. `ℍ[K,a,b]` is split, that is isomorphic to `M₂(K)`;
2. `<<a, b>>` is isotropic;
3. `<<a, b>>` is hyperbolic, that is isometric to the sum of two hyperbolic planes;
4. the Witt class of `<<a, b>>` vanishes.

The equivalence of (2) and (3), that an isotropic two-fold Pfister form is hyperbolic, is the
first case of the theorem that isotropic Pfister forms are hyperbolic. The equivalence of (1) and
(4) says that the Witt class of `<<a, b>>` detects whether `ℍ[K,a,b]` is split.

## Main results

* `TauCeti.anisotropic_pfisterFormClass_two_iff`: `<<a, b>>` is anisotropic exactly when the norm
  form of `ℍ[K,a,b]` is.
* `TauCeti.pfisterFormClass_two_tfae`: the four conditions above are equivalent, with the
  individual equivalences `TauCeti.not_anisotropic_pfisterFormClass_two_iff`,
  `TauCeti.pfisterFormClass_two_eq_two_nsmul_hyperbolicClass_iff` and
  `TauCeti.pfisterClass_two_eq_zero_iff`.

## References

* T. Y. Lam, *Introduction to Quadratic Forms over Fields* (2005), Chapter III, §2 (the splitting
  criterion, Theorem 2.7) and Chapter X, §1 (isotropic Pfister forms are hyperbolic), with the
  convention `<<a>> = <1, -a>`.
-/

public section

open QuadraticMap
open scoped Quaternion

namespace TauCeti

universe u

variable {K : Type u} [Field K] [Invertible (2 : K)]

/-- The two-fold Pfister form `<<a, b>>` is anisotropic exactly when the norm form of the
quaternion algebra `ℍ[K,a,b]` is. -/
theorem anisotropic_pfisterFormClass_two_iff (a b : Kˣ) :
    (pfisterFormClass ![a, b]).Anisotropic ↔
      (_root_.QuaternionAlgebra.normForm (a : K) 0 (b : K)).Anisotropic := by
  have hw : (fun i => ((![1, -a, -b, a * b] i : Kˣ) : K)) =
      ![(1 : K), -(a : K), -(b : K), (a : K) * b] := by
    funext i
    fin_cases i <;> simp
  rw [pfisterFormClass_two, RegularFormClass.anisotropic_mk,
    presentedForm_eq_weightedSumSquares_coe, hw,
    (QuaternionAlgebra.equivalent_normForm_weightedSumSquares (a : K) (b : K)).anisotropic_iff]

/-- **A two-fold Pfister form is isotropic exactly when it is hyperbolic.** -/
theorem not_anisotropic_pfisterFormClass_two_iff (a b : Kˣ) :
    ¬ (pfisterFormClass ![a, b]).Anisotropic ↔
      pfisterFormClass ![a, b] = 2 • hyperbolicClass K := by
  refine ⟨fun h => ?_, fun h => ?_⟩
  -- Pfister forms of fold at least two have trivial discriminant (`discr_pfisterFormClass`), and
  -- a regular isotropic quaternary form of trivial discriminant is the sum of two hyperbolic
  -- planes (`QuadraticMap.Nondegenerate.equivalent_hyperbolicPlane_prod_self`).
  · let p : RegularFormPresentation K := ⟨4, ![1, -a, -b, a * b]⟩
    have hp : formClass (presentedForm p) (nondegenerate_presentedForm p) =
        pfisterFormClass ![a, b] := by
      rw [formClass_presentedForm, pfisterFormClass_two]
    have hiso : ¬ (presentedForm p).Anisotropic := by
      rwa [pfisterFormClass_two, RegularFormClass.anisotropic_mk] at h
    have hQ := (nondegenerate_presentedForm p).equivalent_hyperbolicPlane_prod_self
      (by simp [p]) (by rw [hp]; exact discr_pfisterFormClass _ le_rfl) hiso
    rw [← hp, (formClass_eq_iff _ _ _
      (nondegenerate_hyperbolicPlane.prod nondegenerate_hyperbolicPlane)).mpr hQ,
      formClass_prod _ nondegenerate_hyperbolicPlane _ nondegenerate_hyperbolicPlane,
      formClass_hyperbolicPlane, two_nsmul]
  · rw [h, two_nsmul]
    exact not_anisotropic_hyperbolicClass_add _

/-- **Isotropy, hyperbolicity and splitting for two-fold Pfister forms.** For units `a, b`, the
following are equivalent:
1. `ℍ[K,a,b]` is isomorphic to `M₂(K)`;
2. `<<a, b>>` is isotropic;
3. `<<a, b>>` is the sum of two hyperbolic planes;
4. the Witt class of `<<a, b>>` vanishes. -/
theorem pfisterFormClass_two_tfae (a b : Kˣ) :
    [Nonempty (ℍ[K,(a : K),(b : K)] ≃ₐ[K] Matrix (Fin 2) (Fin 2) K),
      ¬ (pfisterFormClass ![a, b]).Anisotropic,
      pfisterFormClass ![a, b] = 2 • hyperbolicClass K,
      pfisterClass ![a, b] = 0].TFAE := by
  -- The splitting criterion for quaternion algebras, read through the identification of the
  -- norm form of `ℍ[K,a,b]` with `<1, -a, -b, ab>`.
  tfae_have 1 ↔ 2 := by
    rw [anisotropic_pfisterFormClass_two_iff,
      QuaternionAlgebra.nonempty_algEquiv_matrix_iff_not_anisotropic_normForm]
  tfae_have 2 ↔ 3 := not_anisotropic_pfisterFormClass_two_iff a b
  tfae_have 3 → 4 := fun h => by
    rw [← wittClass_pfisterFormClass, h, map_nsmul, wittClass_hyperbolicClass, smul_zero]
  -- The only anisotropic class with vanishing Witt class is the zero class.
  tfae_have 4 → 2 := fun h hani => by
    rw [← wittClass_pfisterFormClass, wittClass_eq_zero_iff,
      RegularFormClass.anisotropicPart_eq_self hani] at h
    simpa [h] using rank_pfisterFormClass ![a, b]
  tfae_finish

/-- **Hyperbolicity criterion for two-fold Pfister forms**: the regular form class of `<<a, b>>`
is the sum of two hyperbolic planes exactly when `ℍ[K,a,b]` is split. -/
theorem pfisterFormClass_two_eq_two_nsmul_hyperbolicClass_iff (a b : Kˣ) :
    pfisterFormClass ![a, b] = 2 • hyperbolicClass K ↔
      Nonempty (ℍ[K,(a : K),(b : K)] ≃ₐ[K] Matrix (Fin 2) (Fin 2) K) :=
  (pfisterFormClass_two_tfae a b).out 3 1

/-- The Witt class of the two-fold Pfister form `<<a, b>>` vanishes exactly when `ℍ[K,a,b]` is
split. -/
theorem pfisterClass_two_eq_zero_iff (a b : Kˣ) :
    pfisterClass ![a, b] = 0 ↔
      Nonempty (ℍ[K,(a : K),(b : K)] ≃ₐ[K] Matrix (Fin 2) (Fin 2) K) :=
  (pfisterFormClass_two_tfae a b).out 4 1

end TauCeti
