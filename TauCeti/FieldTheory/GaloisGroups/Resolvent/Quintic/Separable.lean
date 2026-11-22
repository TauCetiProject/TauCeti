/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.FieldTheory.PolynomialGaloisGroup
public import TauCeti.FieldTheory.GaloisGroups.Resolvent.Quintic.Orbit

import TauCeti.Algebra.Polynomial.SpecificDegree
import TauCeti.Data.ZMod.Periodic
import TauCeti.FieldTheory.GaloisGroups.Orbits
import TauCeti.FieldTheory.GaloisGroups.Resolvent.Quintic.Solvable

/-!
# Separation of the quintic `F₂₀` resolvent sextic

The criterion `TauCeti.isSolvable_gal_iff_exists_isRoot_specialize_quinticF20Spec` reads the
solvability of the Galois group of a monic, separable, irreducible quintic from a root of Dummit's
`F₂₀` resolvent sextic, provided the specialized sextic is separable. This file proves, following
Chapman, that the separation hypothesis always holds over a field in which `5 ≠ 0`: the sextic of a
monic irreducible quintic is separable. Dummit's criterion then holds without it, and a root of the
sextic in the base field splits off a linear factor whose cofactor is an irreducible quintic. The
radical form of the criterion, in characteristic zero, is in
`TauCeti.FieldTheory.GaloisGroups.Resolvent.Quintic.Radicals`.

Both hypotheses are needed. Over `𝔽₅` the Artin–Schreier quintic `X ^ 5 - X - 1`, with roots
`α, α + 1, …, α + 4`, has an inseparable sextic; over `ℚ` the reducible quintic `X ^ 5 - X` has
one too (`TauCeti.not_separable_map_resolventSextic_X_pow_five_sub_X`).

## Main results

* `TauCeti.separable_galResolvent_quinticF20Invariant`: if a ring endomorphism rotates five
  distinct elements of a field in which `5 ≠ 0`, the orbit resolvent of Dummit's invariant at them
  is separable.
* `TauCeti.separable_specialize_quinticF20Spec`: **the resolvent sextic of a monic irreducible
  quintic is separable** when `5 ≠ 0`.
* `TauCeti.isSolvable_gal_iff_exists_isRoot_specialize_quinticF20Spec_of_five_ne_zero`:
  **Dummit's criterion, group form**: when `5 ≠ 0`, a monic irreducible quintic has solvable Galois
  group exactly when its sextic has a root in the base field.
* `TauCeti.exists_eq_X_sub_C_mul_of_isRoot_specialize_quinticF20Spec`: when `5 ≠ 0`, a root `a`
  of the sextic in the base field factors it as `(X - C a) * q` with `q` an irreducible quintic.

## Implementation notes

The argument is about the six values `θ_σ = (σ Φ)(x)` of the conjugates of Dummit's invariant `Φ`
at the five roots `x 0, …, x 4`, numbered so that some Galois automorphism `g` acts on them as the
rotation `a ↦ a + 1` (`TauCeti.exists_gal_apply_rootSet_numbering_eq_finRotate`). The rotation
fixes `Φ` (`TauCeti.rename_finRotate_quinticF20Invariant`), and it permutes the five other formal
conjugates `σ Φ` in a single cycle. Evaluating at `x`, `g` fixes the value of `Φ` and advances the
five other values along that cycle, a cyclically indexed list whose entries may a priori coincide.
A coincidence of two of the six values is therefore carried by the powers of `g` to the coincidence
of all five values of the list (`ZMod.apply_eq_of_semiconj_add_one`,
`ZMod.apply_eq_apply_of_semiconj_add_one`). Each difference of two of them factors as two
differences of roots times a quadratic bracket, and two of those brackets vanish only if
`2 x 0 = x 1 + x 4 = x 2 + x 3`, that is, `5 x 0 = x 0 + ⋯ + x 4`. The sum is fixed by `g`, so also
`5 x 1` is the sum, and `5 ≠ 0` gives `x 0 = x 1`, which is impossible.

## References

* D. S. Dummit, *Solving solvable quintics*, Mathematics of Computation **57** (1991), §2 and
  Theorem 1.
* R. Chapman, *Note on Dummit's paper Solving solvable quintics* (1992): the factorizations of
  the differences and the separation argument, given there over `ℚ`.
-/

public section

open Equiv Equiv.Perm Polynomial

namespace TauCeti

section Rotation

variable {K : Type*} [Field K] {x : Fin 5 → K}

/-- The five conjugates of Dummit's invariant other than the invariant itself, in the order in
which the rotation `a ↦ a + 1` cycles them (`rename_finRotate_mul_rotationRep`). -/
private def rotationRep : Fin 5 → Perm (Fin 5) :=
  ![swap 2 3, swap 3 4, swap 2 3 * swap 3 4, swap 2 4, swap 3 4 * swap 2 3]

/-- The value at `x` of the conjugate `σ Φ` of Dummit's invariant. -/
private noncomputable def conjValue (x : Fin 5 → K) (σ : Perm (Fin 5)) : K :=
  MvPolynomial.eval₂ (Int.castRingHom K) x (MvPolynomial.rename (⇑σ) quinticF20Invariant)

/-- The orbit representatives are the identity followed by the five entries of `rotationRep`. -/
private theorem prod_quinticF20OrbitRepresentatives_eq_mul_prod_rotationRep {M : Type*}
    [CommMonoid M] (h : Perm (Fin 5) → M) :
    ∏ σ ∈ quinticF20OrbitRepresentatives, h σ = h 1 * ∏ k, h (rotationRep k) := by
  rw [prod_quinticF20OrbitRepresentatives, Fin.prod_univ_five]
  simp only [rotationRep, Matrix.cons_val]
  ac_rfl

/-- **The rotation advances the conjugates.** Renaming the conjugate `rotationRep k` of Dummit's
invariant along the rotation `a ↦ a + 1` gives the conjugate `rotationRep (k + 1)`. -/
private theorem rename_finRotate_mul_rotationRep (k : Fin 5) :
    MvPolynomial.rename (⇑(finRotate 5 * rotationRep k)) quinticF20Invariant =
      MvPolynomial.rename (⇑(rotationRep (k + 1))) quinticF20Invariant := by
  -- Both sides are their own evaluations at the formal roots, written out as ten monomials.
  have hC : Int.castRingHom (MvPolynomial (Fin 5) ℤ) = MvPolynomial.C := RingHom.ext_int _ _
  rw [← MvPolynomial.eval₂_eta (MvPolynomial.rename _ quinticF20Invariant),
    ← MvPolynomial.eval₂_eta (MvPolynomial.rename (⇑(rotationRep (k + 1))) quinticF20Invariant),
    ← hC, eval₂_rename_quinticF20Invariant, eval₂_rename_quinticF20Invariant]
  fin_cases k <;> simp [rotationRep, finRotate_apply, swap_apply_def] <;> ring

variable (g : K →+* K) (hg : ∀ a, g (x a) = x (finRotate 5 a))
include hg

/-- A ring endomorphism that rotates the five roots sends the value of a conjugate of Dummit's
invariant to the value of the conjugate renamed by the rotation. -/
private theorem map_conjValue (σ : Perm (Fin 5)) :
    g (conjValue x σ) = conjValue x (finRotate 5 * σ) := by
  rw [conjValue, conjValue, MvPolynomial.apply_eval₂_intCastRingHom_of_comp_eq g (funext hg),
    MvPolynomial.rename_rename, coe_mul]

/-- The rotation fixes the value of Dummit's invariant itself. -/
private theorem map_conjValue_one : g (conjValue x 1) = conjValue x 1 := by
  rw [map_conjValue g hg, mul_one, conjValue, conjValue, rename_finRotate_quinticF20Invariant,
    coe_one, MvPolynomial.rename_id_apply]

/-- The rotation advances the values of the five other conjugates along `rotationRep`. -/
private theorem map_conjValue_rotationRep (k : Fin 5) :
    g (conjValue x (rotationRep k)) = conjValue x (rotationRep (k + 1)) := by
  rw [map_conjValue g hg, conjValue, conjValue, rename_finRotate_mul_rotationRep]

/-- Chapman's identities. If a ring endomorphism rotates five distinct roots `x 0, …, x 4` in a
field where `5 ≠ 0`, the values of the five conjugates listed by `rotationRep` are not all equal:
already the values of `(3 4)Φ` and `(3 4)(2 3)Φ`, or those of `(2 3)(3 4)Φ` and `(2 4)Φ`, differ. -/
private theorem not_forall_conjValue_rotationRep_eq (h5 : (5 : K) ≠ 0)
    (hx : Function.Injective x) :
    ¬ ∀ k l, conjValue x (rotationRep k) = conjValue x (rotationRep l) := by
  intro hc
  have h₁ := hc 1 4
  have h₂ := hc 2 3
  simp only [rotationRep, Matrix.cons_val] at h₁ h₂
  simp only [conjValue, eval₂_rename_quinticF20Invariant, coe_mul, Function.comp_apply,
    swap_apply_def] at h₁ h₂
  simp only [Fin.isValue, Fin.reduceEq, ↓reduceIte] at h₁ h₂
  have hne : ∀ {a b : Fin 5}, a ≠ b → x a - x b ≠ 0 := fun h => sub_ne_zero.2 (hx.ne h)
  -- Each coincidence factors as two root differences times a quadratic bracket.
  have hB₁ : (x 0 - x 4) * (x 0 - x 2) - (x 0 - x 3) * (x 0 - x 1) = 0 := by
    have : (x 3 - x 1) * (x 4 - x 2) *
        ((x 0 - x 4) * (x 0 - x 2) - (x 0 - x 3) * (x 0 - x 1)) = 0 := by
      linear_combination h₁
    simpa [hne (by decide : (3 : Fin 5) ≠ 1), hne (by decide : (4 : Fin 5) ≠ 2)] using this
  have hB₂ : (x 0 - x 4) * (x 0 - x 3) - (x 0 - x 2) * (x 0 - x 1) = 0 := by
    have : (x 2 - x 1) * (x 3 - x 4) *
        ((x 0 - x 4) * (x 0 - x 3) - (x 0 - x 2) * (x 0 - x 1)) = 0 := by
      linear_combination -h₂
    simpa [hne (by decide : (2 : Fin 5) ≠ 1), hne (by decide : (3 : Fin 5) ≠ 4)] using this
  -- Their difference and sum force `2 x 0 = x 1 + x 4 = x 2 + x 3`, so `5 x 0` is the sum.
  have h₁₄ : 2 * x 0 - x 1 - x 4 = 0 := by
    have : (x 3 - x 2) * (2 * x 0 - x 1 - x 4) = 0 := by linear_combination hB₁ - hB₂
    simpa [hne (by decide : (3 : Fin 5) ≠ 2)] using this
  have h₂₃ : 2 * x 0 - x 2 - x 3 = 0 := by
    have : (2 * x 0 - x 2 - x 3) * (x 1 - x 4) = 0 := by linear_combination hB₁ + hB₂
    simpa [hne (by decide : (1 : Fin 5) ≠ 4)] using this
  have hsum : 5 * x 0 = x 0 + x 1 + x 2 + x 3 + x 4 := by linear_combination h₁₄ + h₂₃
  -- The rotation fixes the sum, so also `5 x 1` is the sum, and `x 0 = x 1`.
  have hsum' := congrArg g hsum
  simp only [map_mul, map_add, map_ofNat, hg, finRotate_apply, Fin.isValue, Fin.reduceAdd]
    at hsum'
  have : 5 * (x 0 - x 1) = 0 := by linear_combination hsum - hsum'
  exact hne (by decide : (0 : Fin 5) ≠ 1) ((mul_eq_zero.1 this).resolve_left h5)

/-- The values of the five conjugates listed by `rotationRep` are distinct: a coincidence would
be carried around the cycle to all five, against Chapman's identities. -/
private theorem injective_conjValue_rotationRep (h5 : (5 : K) ≠ 0) (hx : Function.Injective x) :
    Function.Injective fun k => conjValue x (rotationRep k) := by
  have : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  intro k l hkl
  by_contra hne
  exact not_forall_conjValue_rotationRep_eq g hg h5 hx
    (ZMod.apply_eq_apply_of_semiconj_add_one (p := 5) (g := g)
      (fun k => (map_conjValue_rotationRep g hg k).symm) hne hkl)

/-- The value of Dummit's invariant differs from the values of its five other conjugates: it is
fixed by the rotation, which would make all five equal to it. -/
private theorem conjValue_one_ne_conjValue_rotationRep (h5 : (5 : K) ≠ 0)
    (hx : Function.Injective x) (k : Fin 5) : conjValue x 1 ≠ conjValue x (rotationRep k) := by
  intro hk
  have hall := ZMod.apply_eq_of_semiconj_add_one (N := 5) (g := g)
    (u := fun k => conjValue x (rotationRep k)) (fun k => (map_conjValue_rotationRep g hg k).symm)
    (map_conjValue_one g hg) (k := k) hk.symm
  exact not_forall_conjValue_rotationRep_eq g hg h5 hx fun k l => (hall k).trans (hall l).symm

omit hg in
/-- The orbit resolvent of Dummit's invariant at `x` is the linear factor of the value of the
invariant times the linear factors of the five values listed by `rotationRep`. -/
private theorem galResolvent_quinticF20Invariant_eq (x : Fin 5 → K) :
    MvPolynomial.galResolvent quinticF20Invariant x =
      (X - C (conjValue x 1)) * ∏ k, (X - C (conjValue x (rotationRep k))) := by
  rw [← MvPolynomial.map_universalResolvent_eq_galResolvent,
    universalResolvent_quinticF20Invariant, Polynomial.map_prod,
    prod_quinticF20OrbitRepresentatives_eq_mul_prod_rotationRep]
  simp [conjValue]

omit hg in
/-- **The six values of Dummit's invariant at rotated roots are distinct.** Let `x 0, …, x 4` be
distinct elements of a field in which `5 ≠ 0`, and suppose a ring endomorphism `g` rotates them,
`g (x a) = x (a + 1)`. Then the orbit resolvent of Dummit's `F₂₀`-invariant at `x` is separable:
the six conjugates of the invariant take six distinct values at `x`. -/
theorem separable_galResolvent_quinticF20Invariant (h5 : (5 : K) ≠ 0)
    (hx : Function.Injective x) (g : K →+* K) (hg : ∀ a, g (x a) = x (finRotate 5 a)) :
    (MvPolynomial.galResolvent quinticF20Invariant x).Separable := by
  have hcons : ∏ i : Fin 6,
      (X - C ((Fin.cons (conjValue x 1) fun k => conjValue x (rotationRep k) : Fin 6 → K) i)) =
      (X - C (conjValue x 1)) * ∏ k, (X - C (conjValue x (rotationRep k))) := by
    rw [Fin.prod_univ_succ]
    simp only [Fin.cons_zero, Fin.cons_succ]
  rw [galResolvent_quinticF20Invariant_eq, ← hcons, separable_prod_X_sub_C_iff]
  refine Fin.cons_injective_of_injective ?_ (injective_conjValue_rotationRep g hg h5 hx)
  rintro ⟨k, hk⟩
  exact conjValue_one_ne_conjValue_rotationRep g hg h5 hx k hk.symm

end Rotation

section Quintic

variable {F : Type*} [Field F] {f : F[X]}

/-- **The quintic `F₂₀` resolvent sextic is separable** (Chapman). Over a field in which
`5 ≠ 0`, the specialization of Dummit's `F₂₀` resolvent at a monic irreducible quintic is
separable. Over `𝔽₅` the irreducible quintic `X ^ 5 - X - 1` shows that `5 ≠ 0` cannot be
dropped, and the reducible `X ^ 5 - X` over `ℚ` that irreducibility cannot. -/
theorem separable_specialize_quinticF20Spec (h5 : (5 : F) ≠ 0) (hf : f.Monic)
    (hirr : Irreducible f) (hdeg : f.natDegree = 5) :
    (quinticF20Spec.specialize F f).Separable := by
  -- An inseparable irreducible polynomial has degree divisible by the characteristic.
  have hsep : f.Separable := Polynomial.Irreducible.separable_of_natDegree_cast_ne_zero hirr
    (by rw [hdeg]; exact_mod_cast h5)
  have : Fact ((f.map (algebraMap F f.SplittingField)).Splits) := ⟨SplittingField.splits f⟩
  obtain ⟨e, g, hg⟩ := exists_gal_apply_rootSet_numbering_eq_finRotate f.SplittingField hsep hirr
    hdeg Nat.prime_five
  rw [← Polynomial.separable_map (algebraMap F f.SplittingField),
    quinticF20Spec.map_specialize_eq_galResolvent_numbering hf hdeg e, quinticF20Spec_Φ]
  refine separable_galResolvent_quinticF20Invariant ?_
    (Subtype.val_injective.comp e.symm.injective) (g : f.SplittingField →+* f.SplittingField) hg
  rw [← map_ofNat (algebraMap F f.SplittingField) 5]
  exact (_root_.map_ne_zero _).2 h5

/-- **Dummit's criterion, group form.** Over a field in which `5 ≠ 0`, the Galois group of a
monic irreducible quintic is solvable exactly when its `F₂₀` resolvent sextic has a root in the
base field. Unlike `TauCeti.isSolvable_gal_iff_exists_isRoot_specialize_quinticF20Spec`, neither
the separability of the quintic nor that of the sextic is assumed: the first follows from
irreducibility and `5 ≠ 0`, the second is `TauCeti.separable_specialize_quinticF20Spec`. -/
theorem isSolvable_gal_iff_exists_isRoot_specialize_quinticF20Spec_of_five_ne_zero
    (h5 : (5 : F) ≠ 0) (hf : f.Monic) (hirr : Irreducible f) (hdeg : f.natDegree = 5) :
    Group.IsSolvable f.Gal ↔ ∃ a : F, (quinticF20Spec.specialize F f).IsRoot a :=
  isSolvable_gal_iff_exists_isRoot_specialize_quinticF20Spec hf
    (Polynomial.Irreducible.separable_of_natDegree_cast_ne_zero hirr
      (by rw [hdeg]; exact_mod_cast h5)) hirr hdeg
    ⟨separable_specialize_quinticF20Spec h5 hf hirr hdeg⟩

/-- A polynomial whose linear factors over an extension `K` are those of five distinct elements
cycled by an automorphism of `K` is irreducible: the minimal polynomial of the first element has
all five as roots, so it is the whole polynomial. -/
private theorem irreducible_of_map_eq_prod_X_sub_C_of_cycle {K : Type*} [Field K] [Algebra F K]
    [Algebra.IsIntegral F K] {q : F[X]} {u : Fin 5 → K} (g : K ≃ₐ[F] K)
    (hinj : Function.Injective u) (hu : ∀ k, g (u k) = u (k + 1))
    (hq : q.map (algebraMap F K) = ∏ k, (X - C (u k))) : Irreducible q := by
  classical
  have hqmon : q.Monic := by
    rw [← monic_map_iff (f := algebraMap F K), hq]
    exact monic_prod_of_monic _ _ fun _ _ => monic_X_sub_C _
  have hint : IsIntegral F (u 0) := Algebra.IsIntegral.isIntegral _
  set r := minpoly F (u 0)
  -- The automorphism `g` carries roots of `r` to roots of `r`, so every `u k` is a root.
  have hstep : ∀ k, aeval (u k) r = 0 → aeval (u (k + 1)) r = 0 := fun k h => by
    rw [← hu, ← AlgEquiv.coe_toAlgHom, Polynomial.aeval_algHom_apply, h, map_zero]
  have hroots : ∀ k, aeval (u k) r = 0 := by
    have h0 : aeval (u 0) r = 0 := minpoly.aeval F _
    intro k
    fin_cases k
    exacts [h0, hstep 0 h0, hstep 1 (hstep 0 h0), hstep 2 (hstep 1 (hstep 0 h0)),
      hstep 3 (hstep 2 (hstep 1 (hstep 0 h0)))]
  have hr0 : r ≠ 0 := minpoly.ne_zero hint
  have hrdeg : q.natDegree ≤ r.natDegree := by
    calc q.natDegree = (Finset.univ.image u).card := by
          rw [← natDegree_map (algebraMap F K), hq,
            natDegree_prod_of_monic _ _ fun _ _ => monic_X_sub_C _,
            Finset.card_image_of_injective _ hinj]
          simp
      _ ≤ (r.map (algebraMap F K)).roots.toFinset.card := by
          refine Finset.card_le_card fun y hy => ?_
          obtain ⟨k, -, rfl⟩ := Finset.mem_image.1 hy
          rw [Multiset.mem_toFinset, mem_roots_map hr0, ← aeval_def]
          exact hroots k
      _ ≤ r.natDegree :=
          (Multiset.toFinset_card_le _).trans ((card_roots' _).trans (natDegree_map _).le)
  have hdvd : r ∣ q := minpoly.dvd F _ <| by
    rw [aeval_def, eval₂_eq_eval_map, hq, eval_prod]
    exact Finset.prod_eq_zero (Finset.mem_univ 0) (by simp)
  rw [eq_of_monic_of_dvd_of_natDegree_le (minpoly.monic hint) hqmon hdvd hrdeg]
  exact minpoly.irreducible hint

/-- **A root of the sextic splits off an irreducible quintic** (Dummit, Theorem 1). Over a field in
which `5 ≠ 0`, if the `F₂₀` resolvent sextic of a monic irreducible quintic has a root `a` in the
base field, then it is `(X - C a) * q` with `q` irreducible of degree five: in the splitting field
the root `a` is the value of Dummit's invariant, and a Galois automorphism cycles the five other
values, which are distinct. -/
theorem exists_eq_X_sub_C_mul_of_isRoot_specialize_quinticF20Spec (h5 : (5 : F) ≠ 0)
    (hf : f.Monic) (hirr : Irreducible f) (hdeg : f.natDegree = 5) {a : F}
    (ha : (quinticF20Spec.specialize F f).IsRoot a) :
    ∃ q : F[X], quinticF20Spec.specialize F f = (X - C a) * q ∧ Irreducible q ∧
      q.natDegree = 5 := by
  classical
  set K := f.SplittingField
  have hsep : f.Separable := Polynomial.Irreducible.separable_of_natDegree_cast_ne_zero hirr
    (by rw [hdeg]; exact_mod_cast h5)
  have : Fact ((f.map (algebraMap F K)).Splits) := ⟨SplittingField.splits f⟩
  obtain ⟨e, g, hg⟩ := exists_gal_apply_rootSet_numbering_eq_finRotate K hsep hirr hdeg
    Nat.prime_five
  set x : Fin 5 → K := fun i => (e.symm i : K)
  have hx : Function.Injective x := Subtype.val_injective.comp e.symm.injective
  have h5K : (5 : K) ≠ 0 := by
    rw [← map_ofNat (algebraMap F K) 5]
    exact (_root_.map_ne_zero _).2 h5
  set u : Fin 5 → K := fun k => conjValue x (rotationRep k)
  have hu : ∀ k, g (u k) = u (k + 1) := map_conjValue_rotationRep (g : K →+* K) hg
  have hmap : (quinticF20Spec.specialize F f).map (algebraMap F K) =
      (X - C (conjValue x 1)) * ∏ k, (X - C (u k)) := by
    rw [quinticF20Spec.map_specialize_eq_galResolvent_numbering hf hdeg e, quinticF20Spec_Φ,
      galResolvent_quinticF20Invariant_eq]
  -- The root `a` is fixed by `g`, so it is not one of the cycled values `u k`.
  have hav : algebraMap F K a = conjValue x 1 := by
    have hroot := ha.map (f := algebraMap F K)
    rw [hmap, IsRoot, eval_mul, eval_prod, mul_eq_zero, Finset.prod_eq_zero_iff] at hroot
    rcases hroot with h | ⟨k, -, hk⟩
    · simpa [sub_eq_zero] using h
    · rw [eval_sub, eval_X, eval_C, sub_eq_zero] at hk
      have hfix : u (k + 1) = u k := by rw [← hu, ← hk, AlgEquiv.commutes]
      have hne : ∀ k : Fin 5, k + 1 ≠ k := by decide
      exact (hne k (injective_conjValue_rotationRep (g : K →+* K) hg h5K hx hfix)).elim
  set q := quinticF20Spec.specialize F f /ₘ (X - C a)
  have hSq : quinticF20Spec.specialize F f = (X - C a) * q :=
    (mul_divByMonic_eq_iff_isRoot.2 ha).symm
  have hq : q.map (algebraMap F K) = ∏ k, (X - C (u k)) := by
    have := congrArg (Polynomial.map (algebraMap F K)) hSq
    rw [hmap, Polynomial.map_mul, Polynomial.map_sub, map_X, map_C, hav] at this
    exact (mul_left_cancel₀ (X_sub_C_ne_zero _) this).symm
  have hqdeg : q.natDegree = 5 := by
    rw [← natDegree_map (algebraMap F K), hq,
      natDegree_prod_of_monic _ _ fun _ _ => monic_X_sub_C _]
    simp
  exact ⟨q, hSq, irreducible_of_map_eq_prod_X_sub_C_of_cycle g
    (injective_conjValue_rotationRep (g : K →+* K) hg h5K hx) hu hq, hqdeg⟩

end Quintic

end TauCeti
