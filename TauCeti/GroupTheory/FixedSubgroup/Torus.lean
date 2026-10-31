/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.GroupTheory.FixedSubgroup.Lang
public import Mathlib.FieldTheory.IsAlgClosed.Basic
import TauCeti.Algebra.Group.Hom.Iterate

/-!
# Lang maps on Frobenius-twisted tori

On a split torus `(ι → Kˣ)` over an algebraically closed field, an endomorphism with an
iterate equal to a power map of exponent greater than one has surjective Lang map.
This includes a power map composed with any finite-order torus automorphism, not just
an automorphism permuting coordinates. No characteristic assumption is needed for this
statement about points.

Consequently, if an equivariant surjection has this torus as its kernel, every fixed
point in the target has a fixed lift. For a torus normalizer mapping to its Weyl group,
this is the torus-correction step: one must still identify the torus, prove its
Frobenius/twist formula, and check that the desired Weyl element is fixed.

## References

* R. Steinberg, *Lectures on Chevalley Groups*, Chapter 11, Theorem 33.
-/

public section

namespace MonoidHom

variable {K ι : Type*} [Field K] [IsAlgClosed K]

/-- A power-map iterate of exponent greater than one makes the Lang map surjective
on the points of a split torus over an algebraically closed field. -/
theorem surjective_commutatorMap_of_torus_iterate_eq_pow
    (f : (ι → Kˣ) →* (ι → Kˣ)) {m Q : ℕ} (hQ : 1 < Q)
    (hf : ∀ t, (⇑f)^[m] t = t ^ Q) :
    Function.Surjective (commutatorMap f) := by
  apply f.surjective_commutatorMap_of_iterate_eq_pow (by omega) hf
  intro a
  have hroot (i : ι) : ∃ u : Kˣ, u ^ (Q - 1) = a i := by
    obtain ⟨x, hx⟩ := IsAlgClosed.exists_pow_nat_eq (a i : K) (by omega : 0 < Q - 1)
    have hx0 : x ≠ 0 := by
      intro h
      rw [h, zero_pow (by omega : Q - 1 ≠ 0)] at hx
      exact (a i).ne_zero hx.symm
    exact ⟨Units.mk0 x hx0, Units.ext hx⟩
  choose t ht using hroot
  exact ⟨t, funext ht⟩

/-- The Lang map is surjective for a power map of exponent greater than one twisted
by a finite-order endomorphism of a split torus. -/
theorem surjective_commutatorMap_of_torus_twist (f : (ι → Kˣ) →* (ι → Kˣ))
    (θ : (ι → Kˣ) →* (ι → Kˣ)) {q m : ℕ} (hq : 1 < q) (hm : 0 < m)
    (hθ : ∀ t, (⇑θ)^[m] t = t) (hf : ∀ t, f t = θ t ^ q) :
    Function.Surjective (commutatorMap f) := by
  apply f.surjective_commutatorMap_of_torus_iterate_eq_pow (m := m)
    (Nat.one_lt_pow hm.ne' hq)
  intro t
  rw [f.iterate_apply_eq_iterate_pow θ q hf m t, hθ]

variable {G H : Type*} [Group G] [Group H]

/-- An equivariant surjection with a split torus kernel admits fixed lifts when the
endomorphism on that torus is a finite-order twist of a power map of exponent greater
than one. In particular, a fixed Weyl element has a fixed normalizer representative
once these hypotheses have been verified for its torus and normalizer. -/
theorem exists_fixed_lift_of_torus_twist (ψ : G →* H)
    (j : (ι → Kˣ) →* G) (hker : j.range = ψ.ker)
    (f : (ι → Kˣ) →* (ι → Kˣ)) (F : G →* G) (F' : H →* H)
    (hψ : ∀ x, ψ (F x) = F' (ψ x)) (hj : ∀ t, F (j t) = j (f t))
    (hsurj : Function.Surjective ψ) (θ : (ι → Kˣ) →* (ι → Kˣ))
    {q m : ℕ} (hq : 1 < q) (hm : 0 < m) (hθ : ∀ t, (⇑θ)^[m] t = t)
    (hf : ∀ t, f t = θ t ^ q) {y : H} (hy : F' y = y) :
    ∃ x : G, F x = x ∧ ψ x = y := by
  obtain ⟨n, hn⟩ := hsurj y
  have hd : n / F n ∈ j.range := by
    rw [hker, mem_ker, map_div, hψ, hn, hy, div_self']
  obtain ⟨t, ht⟩ := j.exists_fixed_inv_mul_of_surjective_commutatorMap f F hj
    (f.surjective_commutatorMap_of_torus_twist θ hq hm hθ hf) hd
  refine ⟨(j t)⁻¹ * n, ht, ?_⟩
  have htker : ψ (j t) = 1 := mem_ker.mp (hker ▸ ⟨t, rfl⟩)
  simp [htker, hn]

end MonoidHom
