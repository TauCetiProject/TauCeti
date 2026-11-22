/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.FieldTheory.AbelRuffini
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
public import TauCeti.FieldTheory.GaloisGroups.Resolvent.Quintic.Orbit

import TauCeti.Algebra.Polynomial.SpecificDegree
import TauCeti.FieldTheory.AbelRuffini
import TauCeti.FieldTheory.GaloisGroups.Quintic
import TauCeti.FieldTheory.GaloisGroups.Resolvent.Quintic.Solvable
import TauCeti.GroupTheory.Perm.TransitiveGroupLabel.Cyclic

/-!
# Separation of the quintic `F₂₀` resolvent sextic

The criterion `TauCeti.isSolvable_gal_iff_exists_isRoot_specialize_quinticF20Spec` reads the
solvability of a quintic Galois group from a root of Dummit's `F₂₀` resolvent sextic, provided the
specialized sextic is separable. This file proves, following Chapman, that the separation
hypothesis always holds over a field in which `5 ≠ 0`: the sextic of a monic irreducible quintic
is separable. Dummit's criterion then holds without it, and in characteristic zero it decides
whether the roots of the quintic are expressible by radicals.

Both hypotheses are needed. Over `𝔽₅` the Artin–Schreier quintic `X ^ 5 - X - 1`, with roots
`α, α + 1, …, α + 4`, has an inseparable sextic; over `ℚ` the reducible quintic `X ^ 5 - X` has
one too (`TauCeti.not_separable_map_resolventSextic_X_pow_five_sub_X`).

## Main results

* `TauCeti.separable_galResolvent_quinticF20Invariant`: if a ring endomorphism rotates five
  distinct elements of a field in which `5 ≠ 0`, the orbit resolvent of Dummit's invariant at them
  is separable.
* `TauCeti.separable_specialize_quinticF20Spec`: **the resolvent sextic of a monic irreducible
  quintic is separable** when `5 ≠ 0`.
* `TauCeti.isSolvable_gal_iff_exists_isRoot_quinticF20`: **Dummit's criterion, group form**: when
  `5 ≠ 0`, a monic irreducible quintic has solvable Galois group exactly when its sextic has a root
  in the base field.
* `TauCeti.forall_rootSet_mem_solvableByRad_iff_exists_isRoot_quinticF20`: **Dummit's criterion,
  radical form**: in characteristic zero, the roots of a monic irreducible quintic are expressible
  by radicals exactly when its sextic has a root in the base field.

## Implementation notes

The argument is about the six values `θ_σ = (σ Φ)(x)` of the conjugates of Dummit's invariant `Φ`
at the five roots `x 0, …, x 4`, numbered so that some Galois automorphism `g` acts on them as the
rotation `a ↦ a + 1` (`TauCeti.exists_rootSet_equiv_fin_five_apply_symm_eq_finRotate`). The
rotation lies in the stabilizer `F₂₀` of `Φ`, so `g` fixes the value of `Φ` and permutes the other
five values in a single cycle. A coincidence of two of the six values is therefore carried by the
powers of `g` to the coincidence of all five values of the cycle. Each difference of two of them
factors as two differences of roots times a quadratic bracket, and two of those brackets vanish
only if `2 x 0 = x 1 + x 4 = x 2 + x 3`, that is, `5 x 0 = x 0 + ⋯ + x 4`. The sum is fixed by `g`,
so also `5 x 1` is the sum, and `5 ≠ 0` gives `x 0 = x 1`, which is impossible.

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

/-- A ring endomorphism that rotates the five roots sends the value of a conjugate of Dummit's
invariant to the value of the conjugate renamed by the rotation. -/
private theorem map_eval₂_rename_quinticF20Invariant (g : K →+* K)
    (hg : ∀ a, g (x a) = x (finRotate 5 a)) (σ : Perm (Fin 5)) :
    g (MvPolynomial.eval₂ (Int.castRingHom K) x (MvPolynomial.rename (⇑σ) quinticF20Invariant)) =
      MvPolynomial.eval₂ (Int.castRingHom K) x
        (MvPolynomial.rename (⇑(finRotate 5 * σ)) quinticF20Invariant) := by
  rw [MvPolynomial.eval₂_comp_left, MvPolynomial.eval₂_rename, MvPolynomial.eval₂_rename,
    Subsingleton.elim (g.comp (Int.castRingHom K)) (Int.castRingHom K)]
  congr 1
  ext a
  simp [hg]

open Fin.CommRing in
/-- **Propagation of a coincidence under a rotation.** Let a map `g` fix `v` and rotate the five
values `u 0, …, u 4`. If two of the six values `v, u 0, …, u 4` coincide, then all five values `u k`
coincide. -/
private theorem forall_eq_of_rotate {α : Type*} {g : α → α} {v : α} {u : Fin 5 → α}
    (hv : g v = v) (hu : ∀ k, g (u k) = u (k + 1))
    (h : (∃ k, v = u k) ∨ ∃ k l, k ≠ l ∧ u k = u l) (k l : Fin 5) : u k = u l := by
  have hiter : ∀ (n : ℕ) (k : Fin 5), g^[n] (u k) = u (k + (n : Fin 5)) := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      intro k
      rw [Function.iterate_succ_apply, hu, ih]
      congr 1
      push_cast
      ring
  have hreach : ∀ k m : Fin 5, k + (((m - k : Fin 5) : ℕ) : Fin 5) = m := by
    intro k m
    simp
  rcases h with ⟨k₀, hk₀⟩ | ⟨k₀, l₀, hne, heq⟩
  · -- `v` is one of the `u k`, and rotating that coincidence reaches every `u m`.
    have hall : ∀ m, u m = v := fun m => by
      rw [← hreach k₀ m, ← hiter, ← hk₀, Function.iterate_fixed hv]
    rw [hall, hall]
  · -- Two of the `u k` coincide; rotating gives `u m = u (m + d)` with `d = l₀ - k₀ ≠ 0`, and
    -- the multiples of `d` exhaust `Fin 5`.
    have hshift : ∀ m, u m = u (m + (l₀ - k₀)) := fun m => by
      have := congrArg g^[((m - k₀ : Fin 5) : ℕ)] heq
      rwa [hiter, hiter, hreach,
        show l₀ + (((m - k₀ : Fin 5) : ℕ) : Fin 5) = m + (l₀ - k₀) by simp; ring] at this
    have hmul : ∀ (n : ℕ) (m : Fin 5), u m = u (m + (n : Fin 5) * (l₀ - k₀)) := by
      intro n
      induction n with
      | zero => simp
      | succ n ih =>
        intro m
        rw [ih, hshift]
        congr 1
        push_cast
        ring
    have hgen : ∀ d : Fin 5, d ≠ 0 → ∀ k l : Fin 5,
        ∃ n ∈ Finset.range 5, k + (n : Fin 5) * d = l := by
      decide
    obtain ⟨n, -, hn⟩ := hgen _ (sub_ne_zero.2 hne.symm) k l
    rw [hmul n k, hn]

/-- Chapman's identities. If a ring endomorphism rotates five distinct roots `x 0, …, x 4` in a
field where `5 ≠ 0`, the values of the conjugates `(3 4)Φ` and `(3 4)(2 3)Φ` of Dummit's invariant
differ, or those of `(2 3)(3 4)Φ` and `(2 4)Φ` do. -/
private theorem not_eval₂_rename_quinticF20Invariant_eq_and_eq (h5 : (5 : K) ≠ 0)
    (hx : Function.Injective x) (g : K →+* K) (hg : ∀ a, g (x a) = x (finRotate 5 a)) :
    ¬ (MvPolynomial.eval₂ (Int.castRingHom K) x
          (MvPolynomial.rename (⇑(swap (3 : Fin 5) 4)) quinticF20Invariant) =
        MvPolynomial.eval₂ (Int.castRingHom K) x
          (MvPolynomial.rename (⇑(swap 3 4 * swap 2 3 : Perm (Fin 5))) quinticF20Invariant) ∧
      MvPolynomial.eval₂ (Int.castRingHom K) x
          (MvPolynomial.rename (⇑(swap 2 3 * swap 3 4 : Perm (Fin 5))) quinticF20Invariant) =
        MvPolynomial.eval₂ (Int.castRingHom K) x
          (MvPolynomial.rename (⇑(swap (2 : Fin 5) 4)) quinticF20Invariant)) := by
  rintro ⟨h₁, h₂⟩
  simp only [eval₂_rename_quinticF20Invariant, coe_mul, Function.comp_apply, swap_apply_def]
    at h₁ h₂
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

/-- **The six values of Dummit's invariant at rotated roots are distinct.** Let `x 0, …, x 4` be
distinct elements of a field in which `5 ≠ 0`, and suppose a ring endomorphism `g` rotates them,
`g (x a) = x (a + 1)`. Then the orbit resolvent of Dummit's `F₂₀`-invariant at `x` is separable:
the six conjugates of the invariant take six distinct values at `x`. -/
theorem separable_galResolvent_quinticF20Invariant (h5 : (5 : K) ≠ 0)
    (hx : Function.Injective x) (g : K →+* K) (hg : ∀ a, g (x a) = x (finRotate 5 a)) :
    (MvPolynomial.galResolvent quinticF20Invariant x).Separable := by
  set θ : Perm (Fin 5) → K := fun σ =>
    MvPolynomial.eval₂ (Int.castRingHom K) x (MvPolynomial.rename (⇑σ) quinticF20Invariant)
    with hθ
  -- The five conjugates other than the invariant itself, in the order in which the rotation
  -- cycles them.
  let rep : Fin 5 → Perm (Fin 5) :=
    ![swap 2 3, swap 3 4, swap 2 3 * swap 3 4, swap 2 4, swap 3 4 * swap 2 3]
  let t : Fin 6 → Perm (Fin 5) := Fin.cons 1 rep
  have hreps : ∀ σ ∈ quinticF20OrbitRepresentatives, ∃ i, t i = σ := by
    intro σ hσ
    rw [mem_quinticF20OrbitRepresentatives] at hσ
    rcases hσ with rfl | rfl | rfl | rfl | rfl | rfl
    exacts [⟨0, rfl⟩, ⟨1, rfl⟩, ⟨2, rfl⟩, ⟨4, rfl⟩, ⟨3, rfl⟩, ⟨5, rfl⟩]
  have hres : MvPolynomial.galResolvent quinticF20Invariant x =
      ∏ σ ∈ quinticF20OrbitRepresentatives, (X - C (θ σ)) := by
    rw [← MvPolynomial.map_universalResolvent_eq_galResolvent,
      universalResolvent_quinticF20Invariant, Polynomial.map_prod]
    simp [θ]
  have hv : g (θ 1) = θ 1 := by
    have hc : MvPolynomial.rename (⇑(finRotate 5)) quinticF20Invariant = quinticF20Invariant :=
      (rename_quinticF20Invariant_eq_self_iff _).2 (finRotate_mem_referenceSubgroup_five _)
    simpa [hθ, hc] using map_eval₂_rename_quinticF20Invariant g hg 1
  have hu : ∀ k, g (θ (rep k)) = θ (rep (k + 1)) := by
    intro k
    rw [hθ, map_eval₂_rename_quinticF20Invariant g hg]
    fin_cases k <;>
      simp [rep, eval₂_rename_quinticF20Invariant, finRotate_apply, swap_apply_def] <;> ring
  have hall := forall_eq_of_rotate hv hu
  have hinj : Function.Injective (fun i => θ (t i)) := by
    rw [show (fun i => θ (t i)) = Fin.cons (θ 1) (θ ∘ rep) from
      Fin.comp_cons θ 1 rep]
    refine Fin.cons_injective_of_injective ?_ fun k l hkl => ?_
    · rintro ⟨k, hk⟩
      exact not_eval₂_rename_quinticF20Invariant_eq_and_eq h5 hx g hg
        ⟨hall (Or.inl ⟨k, hk.symm⟩) 1 4, hall (Or.inl ⟨k, hk.symm⟩) 2 3⟩
    · by_contra hne
      exact not_eval₂_rename_quinticF20Invariant_eq_and_eq h5 hx g hg
        ⟨hall (Or.inr ⟨k, l, hne, hkl⟩) 1 4, hall (Or.inr ⟨k, l, hne, hkl⟩) 2 3⟩
  rw [hres, separable_prod_X_sub_C_iff']
  intro σ hσ τ hτ h
  obtain ⟨i, rfl⟩ := hreps σ hσ
  obtain ⟨j, rfl⟩ := hreps τ hτ
  rw [hinj h]

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
  obtain ⟨e, g, hg⟩ := exists_rootSet_equiv_fin_five_apply_symm_eq_finRotate hsep hirr hdeg
  rw [← Polynomial.separable_map (algebraMap F f.SplittingField),
    quinticF20Spec.map_specialize_eq_galResolvent_numbering hf hdeg e, quinticF20Spec_Φ]
  refine separable_galResolvent_quinticF20Invariant ?_
    (Subtype.val_injective.comp e.symm.injective) (g : f.SplittingField →+* f.SplittingField) hg
  rw [← map_ofNat (algebraMap F f.SplittingField) 5]
  exact (_root_.map_ne_zero _).2 h5

/-- **Dummit's criterion, group form.** Over a field in which `5 ≠ 0`, the Galois group of a
monic irreducible quintic is solvable exactly when its `F₂₀` resolvent sextic has a root in the
base field. Unlike `TauCeti.isSolvable_gal_iff_exists_isRoot_specialize_quinticF20Spec`, no
separation hypothesis on the sextic is needed: it holds by
`TauCeti.separable_specialize_quinticF20Spec`. -/
theorem isSolvable_gal_iff_exists_isRoot_quinticF20 (h5 : (5 : F) ≠ 0) (hf : f.Monic)
    (hirr : Irreducible f) (hdeg : f.natDegree = 5) :
    Group.IsSolvable f.Gal ↔ ∃ a : F, (quinticF20Spec.specialize F f).IsRoot a :=
  isSolvable_gal_iff_exists_isRoot_specialize_quinticF20Spec hf
    (Polynomial.Irreducible.separable_of_natDegree_cast_ne_zero hirr
      (by rw [hdeg]; exact_mod_cast h5)) hirr hdeg
    ⟨separable_specialize_quinticF20Spec h5 hf hirr hdeg⟩

/-- **Dummit's criterion, radical form** (Dummit, Theorem 1). In characteristic zero, the roots
of a monic irreducible quintic in an algebraic closure are all expressible by radicals exactly
when its `F₂₀` resolvent sextic has a root in the base field. -/
theorem forall_rootSet_mem_solvableByRad_iff_exists_isRoot_quinticF20 [CharZero F]
    (hf : f.Monic) (hirr : Irreducible f) (hdeg : f.natDegree = 5) :
    (∀ x ∈ f.rootSet (AlgebraicClosure F), x ∈ solvableByRad F (AlgebraicClosure F)) ↔
      ∃ a : F, (quinticF20Spec.specialize F f).IsRoot a := by
  rw [← isSolvable_gal_iff_forall_rootSet_mem_solvableByRad]
  exact isSolvable_gal_iff_exists_isRoot_quinticF20 (by norm_num) hf hirr hdeg

end Quintic

end TauCeti
