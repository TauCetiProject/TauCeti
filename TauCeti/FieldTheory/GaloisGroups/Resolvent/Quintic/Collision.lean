/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Complex.Polynomial.Basic
public import Mathlib.FieldTheory.Separable
public import TauCeti.FieldTheory.GaloisGroups.Resolvent.Quintic.Trinomial
public import TauCeti.RingTheory.Polynomial.Resultant.Discriminant
import TauCeti.Algebra.BigOperators.Finset.Pairs
import TauCeti.FieldTheory.GaloisGroups.Orbits
import TauCeti.GroupTheory.Perm.Partition
import TauCeti.GroupTheory.Perm.TransitiveGroupLabel.Classification

/-!
# A collision in the quintic resolvent

The quintic `X⁵ - X` is separable (with discriminant `-256`), while Dummit's sextic resolvent
is `(X - 2)⁴ (X² + 16)` and is inseparable with rational root `2`. Its Galois image nevertheless
lies in no conjugate of the Frobenius group `F₂₀`: complex conjugation fixes the roots `0, ±1`
and exchanges `±i`, so it acts as a transposition, and `F₂₀` contains no transposition.

So `X⁵ - X` satisfies every hypothesis of
`TauCeti.ResolventSpec.exists_le_map_conj_of_isRoot_specialize` for the `F₂₀` specification,
except separability of the specialized resolvent, and the conclusion fails. A rational root of
the resolvent confines the Galois image to a conjugate of `F₂₀` only when the six orbit values
are distinct, and separability of `f` does not ensure that: here the six values at the roots
`0, 1, -1, i, -i` are `2`, four times, and `±4i`.

## Main results

* `TauCeti.discr_X_pow_five_sub_X`: the discriminant is `-256`.
* `TauCeti.separable_X_pow_five_sub_X`: the quintic is separable over `ℚ`.
* `TauCeti.resolventSextic_X_pow_five_sub_X`: the sextic is `(X - 2)⁴ (X² + 16)`.
* `TauCeti.isRoot_resolventSextic_X_pow_five_sub_X`: `2` is an integral root.
* `TauCeti.discr_resolventSextic_X_pow_five_sub_X`: the sextic has discriminant zero.
* `TauCeti.not_separable_map_resolventSextic_X_pow_five_sub_X`: the sextic is inseparable over `ℚ`.
* `TauCeti.isRoot_specialize_quinticF20Spec_X_pow_five_sub_X`: the `F₂₀` resolvent specialized
  over `ℚ` has the root `2`.
* `TauCeti.not_exists_le_map_conj_quinticF20Spec_X_pow_five_sub_X`: the Galois image of `X⁵ - X`
  lies in no conjugate of `F₂₀`, for any splitting extension and any numbering of the roots.
* `TauCeti.not_forall_exists_le_map_conj_of_isRoot_specialize_quinticF20Spec`: hence the
  resolvent criterion fails without its separability hypothesis on the specialized resolvent.
-/

public section

open Polynomial

namespace TauCeti

/-- The polynomial `X⁵ - X` is monic over `ℤ`. -/
theorem monic_X_pow_five_sub_X : (X ^ 5 - X : ℤ[X]).Monic := by monicity!

/-- The discriminant of `X⁵ - X` is `-256`. Its nonzero value proves separability over `ℚ`. -/
@[simp]
theorem discr_X_pow_five_sub_X : (X ^ 5 - X : ℤ[X]).discr = -256 := by
  have h := monic_X_pow_five_sub_X.discr_map (Int.castRingHom ℂ)
  simp only [Polynomial.map_sub, Polynomial.map_pow, Polynomial.map_X] at h
  rw [X_pow_five_sub_X_eq_prod_X_sub_C_rootsXPowFiveSubX, discr_prod_X_sub_C] at h
  have hcalc : (∏ i : Fin 5, ∏ j ∈ Finset.Ioi i,
      (rootsXPowFiveSubX i - rootsXPowFiveSubX j) ^ 2) = (-256 : ℂ) := by
    rw [prod_prod_Ioi_eq_of_two (m := 3), prod_prod_Ioi_eq_of_two (m := 1)]
    norm_num [Fin.prod_univ_three, Fin.prod_univ_one, Fin.prod_Ioi_zero,
      Fin.prod_univ_zero, rootsXPowFiveSubX_def]
    linear_combination (16 * Complex.I ^ 8 - 80 * Complex.I ^ 6 +
      176 * Complex.I ^ 4 - 240 * Complex.I ^ 2 + 256) * Complex.I_sq
  rw [hcalc] at h
  apply Int.cast_injective (α := ℂ)
  simpa using h.symm

/-- The quintic `X⁵ - X` is separable over `ℚ`. -/
theorem separable_X_pow_five_sub_X : (X ^ 5 - X : ℚ[X]).Separable := by
  have hsep := (monic_X_pow_five_sub_X.discr_ne_zero_iff_separable_map ℚ).mp (by
    rw [discr_X_pow_five_sub_X]
    norm_num)
  simpa using hsep

/-- Dummit's sextic of `X⁵ - X` has a quadruple root at `2` and two nonreal roots. -/
@[simp]
theorem resolventSextic_X_pow_five_sub_X :
    resolventSextic (X ^ 5 - X : ℤ[X]) = (X - 2) ^ 4 * (X ^ 2 + 16) := by
  have hf : (X ^ 5 - X : ℤ[X]) = X ^ 5 + C (-1) * X + C 0 := by simp [sub_eq_add_neg]
  rw [hf, resolventSextic_X_pow_five_add_C_mul_X_add_C]
  norm_num
  ring

/-- The quintic `X⁵ - X` has `2` as an integral root of its sextic resolvent. -/
theorem isRoot_resolventSextic_X_pow_five_sub_X :
    (resolventSextic (X ^ 5 - X : ℤ[X])).IsRoot 2 := by
  rw [resolventSextic_X_pow_five_sub_X]
  simp

/-- The sextic resolvent of `X⁵ - X` has discriminant zero. -/
theorem discr_resolventSextic_X_pow_five_sub_X :
    (resolventSextic (X ^ 5 - X : ℤ[X])).discr = 0 := by
  by_contra h
  have hsep : (Polynomial.Separable
      ((resolventSextic (X ^ 5 - X : ℤ[X])).map (Int.castRingHom ℚ))) := by
    simpa using ((monic_resolventSextic _).discr_ne_zero_iff_separable_map ℚ).mp h
  have hformula : (resolventSextic (X ^ 5 - X : ℤ[X])).map (Int.castRingHom ℚ) =
      (X - 2) ^ 4 * (X ^ 2 + 16 : ℚ[X]) := by
    rw [resolventSextic_X_pow_five_sub_X]
    simp
  rw [hformula] at hsep
  exact absurd (hsep.of_mul_left.of_pow (not_isUnit_X_sub_C (2 : ℚ)) (by decide)).2
    (by norm_num)

/-- The specialized sextic of `X⁵ - X` over `ℚ` is inseparable, despite the quintic having
distinct roots. -/
theorem not_separable_map_resolventSextic_X_pow_five_sub_X :
    ¬ (Polynomial.Separable
      ((resolventSextic (X ^ 5 - X : ℤ[X])).map (Int.castRingHom ℚ))) := by
  intro hsep
  exact ((monic_resolventSextic _).discr_ne_zero_iff_separable_map ℚ).mpr hsep
    discr_resolventSextic_X_pow_five_sub_X

/-- The `F₂₀` resolvent of `X⁵ - X`, specialized over `ℚ`, has the root `2`. -/
theorem isRoot_specialize_quinticF20Spec_X_pow_five_sub_X :
    (quinticF20Spec.specialize ℚ (X ^ 5 - X : ℚ[X])).IsRoot 2 := by
  have h := isRoot_resolventSextic_X_pow_five_sub_X.map (f := Int.castRingHom ℚ)
  rwa [resolventSextic_def, ResolventSpec.specialize_map, Polynomial.map_sub,
    Polynomial.map_pow, Polynomial.map_X, map_ofNat] at h

attribute [local instance] Gal.splits_ℚ_ℂ

/-- `i` is a root of `X⁵ - X` in `ℂ`. -/
private theorem I_mem_rootSet_X_pow_five_sub_X : Complex.I ∈ (X ^ 5 - X : ℚ[X]).rootSet ℂ := by
  rw [mem_rootSet_of_ne separable_X_pow_five_sub_X.ne_zero]
  simp [pow_succ, Complex.I_mul_I]

/-- `-i` is a root of `X⁵ - X` in `ℂ`. -/
private theorem neg_I_mem_rootSet_X_pow_five_sub_X :
    -Complex.I ∈ (X ^ 5 - X : ℚ[X]).rootSet ℂ := by
  rw [mem_rootSet_of_ne separable_X_pow_five_sub_X.ne_zero]
  simp [pow_succ, Complex.I_mul_I]

/-- Complex conjugation acts on the roots `0, ±1, ±i` of `X⁵ - X` in `ℂ` as the transposition of
`i` and `-i`. -/
private theorem galActionHom_conj_X_pow_five_sub_X :
    Gal.galActionHom (X ^ 5 - X : ℚ[X]) ℂ
        (Gal.restrict _ ℂ (Complex.conjAe.restrictScalars ℚ)) =
      Equiv.swap ⟨Complex.I, I_mem_rootSet_X_pow_five_sub_X⟩
        ⟨-Complex.I, neg_I_mem_rootSet_X_pow_five_sub_X⟩ := by
  ext ⟨x, hx⟩ : 2
  rw [Gal.galActionHom_restrict]
  -- Read `x` off the factorization of `X⁵ - X` into the linear factors `X - rᵢ` over `ℂ`.
  have hprod := congrArg (eval x) X_pow_five_sub_X_eq_prod_X_sub_C_rootsXPowFiveSubX
  simp only [eval_sub, eval_pow, eval_X, eval_prod, eval_C] at hprod
  have hx' : x ^ 5 - x = 0 := by
    simpa [mem_rootSet_of_ne separable_X_pow_five_sub_X.ne_zero] using hx
  obtain ⟨i, -, hi⟩ := Finset.prod_eq_zero_iff.mp (hprod ▸ hx')
  rw [sub_eq_zero] at hi
  subst hi
  fin_cases i <;>
    simp [Equiv.swap_apply_def, Complex.ext_iff, Complex.conj_I]

/-- **The collision is not a containment.** The Galois image of `X⁵ - X` over `ℚ`, in any
splitting extension and through any numbering of its roots, lies in no conjugate of the Frobenius
group `F₂₀`.

By `TauCeti.isRoot_specialize_quinticF20Spec_X_pow_five_sub_X`, the specialized `F₂₀` resolvent
nevertheless has the root `2` in `ℚ`. As `X⁵ - X` is monic and separable of degree five, this
shows that `TauCeti.ResolventSpec.exists_le_map_conj_of_isRoot_specialize` fails without its
hypothesis that the specialized resolvent is separable. -/
theorem not_exists_le_map_conj_quinticF20Spec_X_pow_five_sub_X {E : Type*} [Field E]
    [Algebra ℚ E] [Fact (((X ^ 5 - X : ℚ[X])).map (algebraMap ℚ E)).Splits]
    (e : (X ^ 5 - X : ℚ[X]).rootSet E ≃ Fin 5) :
    ¬ ∃ τ : Equiv.Perm (Fin 5),
      (Gal.galActionHom (X ^ 5 - X : ℚ[X]) E).range.map
          (e.permCongrHom : _ →* Equiv.Perm (Fin 5)) ≤
        quinticF20Spec.H.map (MulAut.conj τ).toMonoidHom := by
  classical
  rintro ⟨τ, hle⟩
  let c : (X ^ 5 - X : ℚ[X]).Gal := Gal.restrict _ ℂ (Complex.conjAe.restrictScalars ℚ)
  have hmem : e.permCongr (Gal.galActionHom (X ^ 5 - X : ℚ[X]) E c) ∈
      quinticF20Spec.H.map (MulAut.conj τ).toMonoidHom :=
    hle ⟨_, ⟨c, rfl⟩, rfl⟩
  rw [Subgroup.mem_map_equiv, MulAut.conj_symm_apply, quinticF20Spec_H] at hmem
  refine not_isSwap_of_mem_referenceSubgroup_five_two hmem (Equiv.Perm.card_support_eq_two.mp ?_)
  -- Conjugating and relabelling preserve the size of the support, and `c` moves only `±i`.
  -- The first two rewrites present `τ⁻¹ * _ * τ` as `τ⁻¹ * _ * τ⁻¹⁻¹`, the form of
  -- `Equiv.Perm.card_support_conj`.
  rw [← inv_inv τ, inv_inv τ⁻¹, Equiv.Perm.card_support_conj,
    Equiv.Perm.card_support_permCongr, Gal.galActionHom_eq_permCongr _ ℂ E c,
    Equiv.Perm.card_support_permCongr, galActionHom_conj_X_pow_five_sub_X,
    Equiv.Perm.card_support_swap]
  norm_num [Subtype.ext_iff, Complex.ext_iff]

/-- **The separability hypothesis on the resolvent cannot be dropped.** For the `F₂₀`
specification, a rational root of the specialized resolvent of a monic separable quintic over
`ℚ` does not in general confine the Galois image to a conjugate of `F₂₀`: `X⁵ - X` is a
counterexample. This is `TauCeti.ResolventSpec.exists_le_map_conj_of_isRoot_specialize` with
its separability hypothesis on the specialized resolvent removed. -/
theorem not_forall_exists_le_map_conj_of_isRoot_specialize_quinticF20Spec :
    ¬ ∀ f : ℚ[X], f.Monic → f.Separable → f.natDegree = 5 →
      ∀ e : f.rootSet ℂ ≃ Fin 5, ∀ a : ℚ, (quinticF20Spec.specialize ℚ f).IsRoot a →
        ∃ τ : Equiv.Perm (Fin 5),
          (Gal.galActionHom f ℂ).range.map (e.permCongrHom : _ →* Equiv.Perm (Fin 5)) ≤
            quinticF20Spec.H.map (MulAut.conj τ).toMonoidHom := by
  intro h
  have hdeg : (X ^ 5 - X : ℚ[X]).natDegree = 5 := by compute_degree!
  have hcard : Fintype.card ((X ^ 5 - X : ℚ[X]).rootSet ℂ) = 5 := by
    rw [card_rootSet_eq_natDegree separable_X_pow_five_sub_X (IsAlgClosed.splits _), hdeg]
  let e := (Fintype.equivFin _).trans (finCongr hcard)
  exact not_exists_le_map_conj_quinticF20Spec_X_pow_five_sub_X e
    (h _ (by monicity!) separable_X_pow_five_sub_X hdeg e 2
      isRoot_specialize_quinticF20Spec_X_pow_five_sub_X)

end TauCeti
