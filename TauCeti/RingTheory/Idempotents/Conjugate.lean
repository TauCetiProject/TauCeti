/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.Idempotents.Hom
public import TauCeti.Order.Atoms
public import Mathlib.LinearAlgebra.Projection
public import Mathlib.RingTheory.SimpleModule.Basic

/-!
# Conjugate idempotents

Let `e` and `f` be idempotents of a ring `A`. An isomorphism of left ideals `Ae ≅ Af` is right
multiplication by an element `a ∈ eAf`, with inverse right multiplication by `b ∈ fAe`, and then
`a b = e` and `b a = f`. If moreover `A(1 - e) ≅ A(1 - f)`, given in the same way by `a'` and `b'`,
then `u = a + a'` is a unit with inverse `b + b'`, and `u⁻¹ e u = f`.

If `1` is a sum of orthogonal idempotents `fᵢ` with simple left ideals `Afᵢ`, every idempotent `x`
is conjugate to a partial sum of the `fᵢ`: the left ideals of a subfamily give a complement of `Ax`
(`TauCeti.exists_isCompl_finset_sup_of_isAtom`), and complements of the same left ideal are
isomorphic.

## Main results

* `IsIdempotentElem.exists_mul_eq_of_linearEquiv`: an isomorphism `Ae ≅ Af` gives `a ∈ eAf` and
  `b ∈ fAe` with `a b = e` and `b a = f`.
* `IsIdempotentElem.exists_units_mul_mul_eq_of_linearEquiv`: if `Ae ≅ Af` and
  `A(1 - e) ≅ A(1 - f)`, then `f = u⁻¹ e u` for a unit `u`.
* `IsIdempotentElem.isCompl_span_singleton_one_sub`: `Ay` and `A(1 - y)` are complementary.
* `OrthogonalIdempotents.span_singleton_sum_eq_sup`: the left ideal of a partial sum of orthogonal
  idempotents is the sum of the left ideals of its terms.
* `CompleteOrthogonalIdempotents.exists_units_mul_mul_eq_sum`: every idempotent is conjugate to a
  partial sum of a complete family of orthogonal idempotents with simple left ideals.

## References

* T. Y. Lam, *A First Course in Noncommutative Rings*, 2nd ed., GTM 131, Springer (2001),
  Exercise 21.16, as used in the proof of Theorem (23.6).
-/

public section

namespace IsIdempotentElem

open TauCeti

variable {A : Type*} [Ring A] {e f : A}

/-- An isomorphism of left ideals `Ae ≅ Af` between idempotent generators is right multiplication
by some `a ∈ eAf`, with inverse right multiplication by some `b ∈ fAe`; then `a b = e` and
`b a = f`. -/
theorem exists_mul_eq_of_linearEquiv (he : IsIdempotentElem e) (hf : IsIdempotentElem f)
    (φ : (Ideal.span {e} : Ideal A) ≃ₗ[A] (Ideal.span {f} : Ideal A)) :
    ∃ a b : A, e * a = a ∧ a * f = a ∧ f * b = b ∧ b * e = b ∧ a * b = e ∧ b * a = f := by
  -- `a` and `b` are the values of `φ` and `φ⁻¹` at the generators `e` and `f`.
  have hea : e * (φ (spanSingletonGenerator e) : A) = φ (spanSingletonGenerator e) := by
    simpa only [coe_spanSingletonGenerator, LinearEquiv.coe_coe] using
      (coe_apply_eq_mul_apply_generator he φ.toLinearMap (spanSingletonGenerator e)).symm
  have hfb : f * (φ.symm (spanSingletonGenerator f) : A) = φ.symm (spanSingletonGenerator f) := by
    simpa only [coe_spanSingletonGenerator, LinearEquiv.coe_coe] using
      (coe_apply_eq_mul_apply_generator hf φ.symm.toLinearMap (spanSingletonGenerator f)).symm
  have haf : (φ (spanSingletonGenerator e) : A) * f = φ (spanSingletonGenerator e) := by
    obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.mp (φ (spanSingletonGenerator e)).2
    rw [← hc, mul_assoc, hf.eq]
  have hbe : (φ.symm (spanSingletonGenerator f) : A) * e = φ.symm (spanSingletonGenerator f) := by
    obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.mp (φ.symm (spanSingletonGenerator f)).2
    rw [← hc, mul_assoc, he.eq]
  -- The value of `φ` at the generator is `a` times the generator of `Af`, and dually.
  have hφ : φ (spanSingletonGenerator e) =
      (φ (spanSingletonGenerator e) : A) • spanSingletonGenerator f :=
    Subtype.ext (by simp [haf])
  have hφ' : φ.symm (spanSingletonGenerator f) =
      (φ.symm (spanSingletonGenerator f) : A) • spanSingletonGenerator e :=
    Subtype.ext (by simp [hbe])
  refine ⟨_, _, hea, haf, hfb, hbe, ?_, ?_⟩
  · have := congrArg Subtype.val (φ.symm_apply_apply (spanSingletonGenerator e))
    rw [hφ, map_smul] at this
    simpa using this
  · have := congrArg Subtype.val (φ.apply_symm_apply (spanSingletonGenerator f))
    rw [hφ', map_smul] at this
    simpa using this

/-- **Idempotents with isomorphic left ideals and complements are conjugate**: if `Ae ≅ Af` and
`A(1 - e) ≅ A(1 - f)` as left `A`-modules, then `f = u⁻¹ e u` for a unit `u`. -/
theorem exists_units_mul_mul_eq_of_linearEquiv (he : IsIdempotentElem e) (hf : IsIdempotentElem f)
    (φ : (Ideal.span {e} : Ideal A) ≃ₗ[A] (Ideal.span {f} : Ideal A))
    (ψ : (Ideal.span {1 - e} : Ideal A) ≃ₗ[A] (Ideal.span {1 - f} : Ideal A)) :
    ∃ u : Aˣ, (↑u⁻¹ : A) * e * u = f := by
  obtain ⟨a, b, hea, haf, hfb, hbe, hab, hba⟩ := he.exists_mul_eq_of_linearEquiv hf φ
  obtain ⟨a', b', hea', haf', hfb', hbe', hab', hba'⟩ :=
    he.one_sub.exists_mul_eq_of_linearEquiv hf.one_sub ψ
  -- The cross terms vanish, as `f (1 - f) = 0` and `(1 - e) e = 0`.
  have h₁ : a * b' = 0 := by
    rw [← haf, ← hfb', mul_assoc, ← mul_assoc f, hf.mul_one_sub_self, zero_mul, mul_zero]
  have h₂ : a' * b = 0 := by
    rw [← haf', ← hfb, mul_assoc, ← mul_assoc (1 - f), hf.one_sub_mul_self, zero_mul, mul_zero]
  have h₃ : b * a' = 0 := by
    rw [← hbe, ← hea', mul_assoc, ← mul_assoc e, he.mul_one_sub_self, zero_mul, mul_zero]
  have h₄ : b' * a = 0 := by
    rw [← hbe', ← hea, mul_assoc, ← mul_assoc (1 - e), he.one_sub_mul_self, zero_mul, mul_zero]
  let u : Aˣ := ⟨a + a', b + b', by simp [add_mul, mul_add, hab, hab', h₁, h₂],
    by simp [add_mul, mul_add, hba, hba', h₃, h₄]⟩
  refine ⟨u, ?_⟩
  -- `e u = a`, and `u⁻¹ a = b a = f`.
  have heu : e * (a + a') = a := by
    rw [mul_add, hea, ← hea', ← mul_assoc, he.mul_one_sub_self, zero_mul, add_zero]
  change (b + b') * e * (a + a') = f
  rw [mul_assoc, heu, add_mul, hba, h₄, add_zero]

/-- The left ideals `Ay` and `A(1 - y)` of an idempotent `y` are complementary. -/
theorem isCompl_span_singleton_one_sub {y : A} (hy : IsIdempotentElem y) :
    IsCompl (Ideal.span {y} : Ideal A) (Ideal.span {1 - y}) := by
  refine ⟨Submodule.disjoint_def.2 fun z hz hz' ↦ ?_, codisjoint_iff.2 ?_⟩
  · obtain ⟨a, rfl⟩ := Ideal.mem_span_singleton'.mp hz
    obtain ⟨b, hb⟩ := Ideal.mem_span_singleton'.mp hz'
    -- `z y = z` as `z ∈ Ay`, and `z y = 0` as `z ∈ A(1 - y)`.
    have h₁ : b * (1 - y) * y = 0 := by rw [mul_assoc, hy.one_sub_mul_self, mul_zero]
    rwa [hb, mul_assoc, hy.eq] at h₁
  · refine Ideal.eq_top_of_isUnit_mem _ ?_ isUnit_one
    simpa using Submodule.add_mem_sup (Ideal.mem_span_singleton_self y)
      (Ideal.mem_span_singleton_self (1 - y))

end IsIdempotentElem

namespace OrthogonalIdempotents

variable {A : Type*} [Ring A] {ι : Type*} {f : ι → A}

/-- For orthogonal idempotents, the left ideal generated by a partial sum is the sum of the left
ideals generated by its terms. -/
theorem span_singleton_sum_eq_sup (hf : OrthogonalIdempotents f) (s : Finset ι) :
    (Ideal.span {∑ i ∈ s, f i} : Ideal A) = s.sup fun i ↦ Ideal.span {f i} := by
  refine le_antisymm ?_ (Finset.sup_le fun i hi ↦ ?_)
  · rw [Ideal.span_singleton_le_iff_mem]
    exact Submodule.sum_mem _ fun i hi ↦
      Finset.le_sup (f := fun i ↦ (Ideal.span {f i} : Ideal A)) hi
        (Ideal.mem_span_singleton_self _)
  · -- `fᵢ = fᵢ ∑ⱼ fⱼ` for `i ∈ s`.
    rw [Ideal.span_singleton_le_iff_mem, Ideal.mem_span_singleton']
    exact ⟨f i, hf.mul_sum_of_mem hi⟩

end OrthogonalIdempotents

namespace CompleteOrthogonalIdempotents

open IsIdempotentElem

variable {A : Type*} [Ring A] {ι : Type*} [Fintype ι] {f : ι → A}

/-- **Idempotents are conjugate to partial sums**: if `1` is a sum of orthogonal idempotents `fᵢ`
whose left ideals `Afᵢ` are simple, then every idempotent `x` is conjugate to a partial sum
`∑ i ∈ t, fᵢ`. A subfamily whose left ideals give a complement of `Ax` exists by
`TauCeti.exists_isCompl_finset_sup_of_isAtom`; complements of the same left ideal are isomorphic,
which supplies the two isomorphisms of `IsIdempotentElem.exists_units_mul_mul_eq_of_linearEquiv`. -/
theorem exists_units_mul_mul_eq_sum (hf : CompleteOrthogonalIdempotents f)
    (hsimple : ∀ i, IsSimpleModule A (Ideal.span {f i} : Ideal A)) {x : A}
    (hx : IsIdempotentElem x) :
    ∃ (t : Finset ι) (v : Aˣ), (↑v⁻¹ : A) * (∑ i ∈ t, f i) * v = x := by
  classical
  let N : ι → Submodule A A := fun i ↦ Ideal.span {f i}
  have hatom (i : ι) : IsAtom (N i) := isSimpleModule_iff_isAtom.mp (hsimple i)
  have htop : Finset.univ.sup N = ⊤ := by
    rw [← hf.toOrthogonalIdempotents.span_singleton_sum_eq_sup, hf.complete,
      Ideal.span_singleton_one]
  obtain ⟨s, hs⟩ := TauCeti.exists_isCompl_finset_sup_of_isAtom hatom htop (Ideal.span {x})
  -- With `g = ∑ i ∉ s, fᵢ`, the left ideal of `1 - g` is the complement `⨆ i ∈ s, Afᵢ`.
  set g : A := ∑ i ∈ sᶜ, f i
  have hg : IsIdempotentElem g := hf.toOrthogonalIdempotents.isIdempotentElem_sum
  have hg' : 1 - g = ∑ i ∈ s, f i := by
    rw [← hf.complete, ← Finset.sum_compl_add_sum s, add_sub_cancel_left]
  have hH : (Ideal.span {1 - g} : Ideal A) = s.sup N := by
    rw [hg', hf.toOrthogonalIdempotents.span_singleton_sum_eq_sup]
  have hgH : IsCompl (Ideal.span {g} : Ideal A) (s.sup N) :=
    hH ▸ isCompl_span_singleton_one_sub hg
  -- Complements of the same left ideal are isomorphic.
  let φ : (Ideal.span {g} : Ideal A) ≃ₗ[A] (Ideal.span {x} : Ideal A) :=
    (Submodule.quotientEquivOfIsCompl _ _ hgH.symm).symm.trans
      (Submodule.quotientEquivOfIsCompl _ _ hs.symm)
  let ψ : (Ideal.span {1 - g} : Ideal A) ≃ₗ[A] (Ideal.span {1 - x} : Ideal A) :=
    (LinearEquiv.ofEq _ _ hH).trans ((Submodule.quotientEquivOfIsCompl _ _ hs).symm.trans
      (Submodule.quotientEquivOfIsCompl _ _ (isCompl_span_singleton_one_sub hx)))
  obtain ⟨v, hv⟩ := hg.exists_units_mul_mul_eq_of_linearEquiv hx φ ψ
  exact ⟨sᶜ, v, hv⟩

end CompleteOrthogonalIdempotents
