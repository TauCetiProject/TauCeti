/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Basic.Real.Basic
public import TauCeti.NumberTheory.ArithmeticStatistics.FormDensity.Basic
public import TauCeti.NumberTheory.ArithmeticStatistics.FormDensity.PrimitiveVectors

import TauCeti.LinearAlgebra.Unimodular

/-!
# Local densities of forms modulo `Q`

For a form `f_a` of degree `d` in `n + 1` variables with coefficient vector `a` over `ZMod Q`, its
local density is the normalized number of its primitive zeros,

`σ(a; Q) = Q⁻ⁿ · #{b ∈ R_{n+1}(Q) : f_a(b) = 0}`.

It is the factor at `Q` of the local-to-global heuristic for the number of rational points of the
hypersurface `f_a = 0`, and the quantity whose moments over random primitive coefficient vectors
are studied by Browning, Le Boudec and Sawin. The density is a normalized count, not a
probability: it can exceed one.

The definitions are made over an arbitrary finite commutative ring `R`, normalizing by
`(#R) ^ n`, so that the Chinese remainder theorem becomes a statement about product rings:

* `FormDensity.primitiveZeros a`, the primitive zeros of `f_a`;
* `FormDensity.localDensity a`, the local density `σ(a; R)`;
* `FormDensity.localDensity_pos_iff`: `σ(a; R) > 0` exactly when `f_a` has a primitive zero;
* `FormDensity.localDensity_le_card`: `σ(a; R) ≤ #R`;
* `FormDensity.localDensity_smul_of_isUnit`: scaling `a` by a unit does not change `σ`, so `σ` is
  a function of the hypersurface;
* `FormDensity.localDensity_prod` and `FormDensity.localDensity_zmod_mul`: multiplicativity
  `σ(a; Q₁ Q₂) = σ(a; Q₁) σ(a; Q₂)` for coprime moduli and an integral coefficient vector `a`.

## References

* T. Browning, P. Le Boudec, W. Sawin, *The Hasse principle for random Fano hypersurfaces*,
  arXiv:2006.02356v1, §5.1, (5.2)–(5.3), and §5.2, (5.11).
-/

public section

open Finset MvPolynomial

namespace TauCeti.FormDensity

variable {σ R S : Type*} [Fintype σ] [DecidableEq σ] [CommRing R] [Fintype R] [CommRing S]
  [Fintype S] {d n : ℕ}

/-- The primitive zeros `b` of the form `f_a`. -/
noncomputable def primitiveZeros (a : Monomials σ d → R) : Finset (σ → R) := by
  classical
  exact (primitiveVectors σ R).filter fun b ↦ eval b (form a) = 0

@[simp]
theorem mem_primitiveZeros {a : Monomials σ d → R} {b : σ → R} :
    b ∈ primitiveZeros a ↔ b ∈ primitiveVectors σ R ∧ eval b (form a) = 0 := by
  simp [primitiveZeros]

/-- Scaling the coefficient vector by a unit does not change the primitive zeros. -/
theorem primitiveZeros_smul_of_isUnit {u : R} (hu : IsUnit u) (a : Monomials σ d → R) :
    primitiveZeros (u • a) = primitiveZeros a := by
  ext b
  simp [form_smul, smul_eval, hu.mul_right_eq_zero]

/-- A ring isomorphism identifies the primitive zeros of `f_a` with those of the transported
form. -/
theorem comp_mem_primitiveZeros_iff (e : R ≃+* S) {a : Monomials σ d → R} {b : σ → R} :
    ⇑e ∘ b ∈ primitiveZeros (⇑e ∘ a) ↔ b ∈ primitiveZeros a := by
  have h : eval (e ∘ b) (form (e ∘ a)) = e (eval b (form a)) := eval_form_comp (e : R →+* S) b a
  simp [h]

/-- Over a product ring, the primitive zeros of `f_a` are the pairs of primitive zeros of its two
components. -/
theorem mem_primitiveZeros_prod_iff {a : Monomials σ d → R × S} {b : σ → R × S} :
    b ∈ primitiveZeros a ↔
      Prod.fst ∘ b ∈ primitiveZeros (Prod.fst ∘ a) ∧
        Prod.snd ∘ b ∈ primitiveZeros (Prod.snd ∘ a) := by
  have h₁ : eval (Prod.fst ∘ b) (form (Prod.fst ∘ a)) = (eval b (form a)).1 :=
    eval_form_comp (RingHom.fst R S) b a
  have h₂ : eval (Prod.snd ∘ b) (form (Prod.snd ∘ a)) = (eval b (form a)).2 :=
    eval_form_comp (RingHom.snd R S) b a
  simp [TauCeti.Module.isUnimodular_pi_prod_iff, h₁, h₂, Prod.ext_iff, and_and_and_comm]

/-- Ring isomorphisms preserve the number of primitive zeros. -/
theorem card_primitiveZeros_comp (e : R ≃+* S) (a : Monomials σ d → R) :
    #(primitiveZeros (⇑e ∘ a)) = #(primitiveZeros a) :=
  (card_equiv (Equiv.piCongrRight fun _ ↦ e.toEquiv) fun _ ↦
    (comp_mem_primitiveZeros_iff e).symm).symm

/-- Over a product ring, the number of primitive zeros of `f_a` is the product of the numbers for
its two components. -/
theorem card_primitiveZeros_prod (a : Monomials σ d → R × S) :
    #(primitiveZeros a) = #(primitiveZeros (Prod.fst ∘ a)) * #(primitiveZeros (Prod.snd ∘ a)) := by
  rw [← card_product]
  refine card_equiv (Equiv.arrowProdEquivProdArrow σ (fun _ ↦ R) (fun _ ↦ S)) fun b ↦ ?_
  rw [Equiv.arrowProdEquivProdArrow_apply, mem_product]
  exact mem_primitiveZeros_prod_iff

/-- The local density `σ(a; R) = (#R)⁻ⁿ · #{b primitive : f_a(b) = 0}` of a form of degree `d` in
`n + 1` variables with coefficient vector `a` over a finite commutative ring `R`. For
`R = ZMod Q` this is the local density `σ(a; Q)` of `f_a` modulo `Q`. -/
noncomputable def localDensity (a : Monomials (Fin (n + 1)) d → R) : ℝ :=
  #(primitiveZeros a) / (Fintype.card R : ℝ) ^ n

theorem localDensity_def (a : Monomials (Fin (n + 1)) d → R) :
    localDensity a = #(primitiveZeros a) / (Fintype.card R : ℝ) ^ n :=
  (rfl)

/-- The normalizing factor `(#R) ^ n` of the local density is positive. -/
private theorem card_pow_pos : (0 : ℝ) < (Fintype.card R : ℝ) ^ n := by
  have := Fintype.card_pos (α := R)
  positivity

theorem localDensity_nonneg (a : Monomials (Fin (n + 1)) d → R) : 0 ≤ localDensity a := by
  rw [localDensity_def]
  positivity

/-- The local density is positive exactly when the form has a primitive zero. -/
theorem localDensity_pos_iff {a : Monomials (Fin (n + 1)) d → R} :
    0 < localDensity a ↔ ∃ b ∈ primitiveVectors (Fin (n + 1)) R, eval b (form a) = 0 := by
  rw [localDensity_def, div_pos_iff_of_pos_right card_pow_pos, Nat.cast_pos, card_pos]
  simp [Finset.Nonempty]

/-- The local density is at most `#R`: there are at most `(#R) ^ (n + 1)` zeros. -/
theorem localDensity_le_card (a : Monomials (Fin (n + 1)) d → R) :
    localDensity a ≤ Fintype.card R := by
  rw [localDensity_def, div_le_iff₀ card_pow_pos, ← pow_succ']
  have h := card_le_univ (primitiveZeros a)
  rw [Fintype.card_fun, Fintype.card_fin] at h
  exact_mod_cast h

/-- Scaling the coefficient vector by a unit does not change the local density, which is
therefore a function of the hypersurface `f_a = 0`. -/
@[simp]
theorem localDensity_smul_of_isUnit {u : R} (hu : IsUnit u) (a : Monomials (Fin (n + 1)) d → R) :
    localDensity (u • a) = localDensity a := by
  rw [localDensity_def, localDensity_def, primitiveZeros_smul_of_isUnit hu]

/-- Ring isomorphisms preserve local densities. -/
@[simp]
theorem localDensity_comp (e : R ≃+* S) (a : Monomials (Fin (n + 1)) d → R) :
    localDensity (⇑e ∘ a) = localDensity a := by
  rw [localDensity_def, localDensity_def, card_primitiveZeros_comp,
    Fintype.card_congr e.toEquiv]

/-- Over a product ring the local density is the product of the local densities of the two
components. -/
theorem localDensity_prod (a : Monomials (Fin (n + 1)) d → R × S) :
    localDensity a = localDensity (Prod.fst ∘ a) * localDensity (Prod.snd ∘ a) := by
  simp only [localDensity_def, card_primitiveZeros_prod a, Fintype.card_prod, Nat.cast_mul,
    mul_pow]
  rw [mul_div_mul_comm]

/-- **Multiplicativity of local densities.** For coprime moduli `Q₁` and `Q₂` and an integral
coefficient vector `a`, the local density modulo `Q₁ Q₂` is the product of the local densities
modulo `Q₁` and modulo `Q₂`. -/
theorem localDensity_zmod_mul {Q₁ Q₂ : ℕ} [NeZero Q₁] [NeZero Q₂] (h : Q₁.Coprime Q₂)
    (a : Monomials (Fin (n + 1)) d → ℤ) :
    localDensity (fun m ↦ (a m : ZMod (Q₁ * Q₂))) =
      localDensity (fun m ↦ (a m : ZMod Q₁)) * localDensity (fun m ↦ (a m : ZMod Q₂)) := by
  rw [← localDensity_comp (ZMod.chineseRemainder h), localDensity_prod]
  simp [Function.comp_def]

/-- Over the zero ring, such as `ZMod 1`, the local density is one. -/
theorem localDensity_of_subsingleton [Subsingleton R] (a : Monomials (Fin (n + 1)) d → R) :
    localDensity a = 1 := by
  have hzeros : primitiveZeros a = primitiveVectors (Fin (n + 1)) R := by
    ext b
    rw [mem_primitiveZeros]
    exact and_iff_left (Subsingleton.elim _ _)
  rw [localDensity_def, hzeros, card_primitiveVectors_of_subsingleton,
    Fintype.card_eq_one_iff.mpr ⟨0, fun _ ↦ Subsingleton.elim _ _⟩]
  simp

end TauCeti.FormDensity
