/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Trace
public import TauCeti.Algebra.AlgebraicGroup.FunctorOfPoints
public import TauCeti.Algebra.HopfAlgebra.Frobenius

/-!
# The modular character and the Hopf form of the Nakayama automorphism

The left integrals of a bialgebra `H` form a right ideal, so right multiplication by `h : H`
restricts to an endomorphism of the space of left integrals. When this space is a line, spanned
by a nonzero left integral `Λ`, that endomorphism is a scalar, and the **modular character**
`α : H → k` is defined by `Λ * h = α h • Λ`. Here `α h` is defined as the trace of right
multiplication by `h` on the space of left integrals, so that no choice of `Λ` enters the
definition; in particular `α` does not change when `Λ` is rescaled.

Over a field the space of left integrals is a line whenever `H` is finite-dimensional and has a
Frobenius functional (`LinearMap.IsFrobeniusFunctional.finrank_leftIntegral`), for instance a
nonzero right invariant functional on a finite-dimensional Hopf algebra. The results on `α` below
take the one-dimensionality of the left integrals as their hypothesis.

For a nonzero right invariant functional `φ` (a right cointegral, `∑ φ(x₁) x₂ = φ(x) 1`) on a
finite-dimensional Hopf algebra, Tau Ceti's Nakayama automorphism `ν` of the Frobenius functional
`φ` is defined in the stable convention `φ (a * b) = φ (b * ν a)`. The Hopf-algebra Nakayama
automorphism, in the convention `φ (x * y) = φ (ν_H y * x)`, is its inverse, and it is the
winding automorphism `ν_H y = ∑ α(y₁) S²(y₂)`
(`LinearMap.IsRightInvariantIntegral.nakayamaAut_symm_eq_winding`).

The proof reads the inverse Nakayama automorphism off the Frobenius dual bases
`{Λ₁}`, `{S(Λ₂)}` of the left integral `Λ` normalized by `φ Λ = 1`: the reconstruction formula
`z = ∑ φ(z Λ₁) S(Λ₂)` gives `ν⁻¹ y = S (∑ φ(Λ₁ y) Λ₂)`, and strong invariance turns the inner
sum into `∑ φ(Λ y₁) S(y₂) = ∑ α(y₁) S(y₂)`.

## Main definitions

* `TauCeti.HopfAlgebra.mulRightLeftIntegral`: right multiplication on the space of left
  integrals.
* `TauCeti.HopfAlgebra.modularCharacter`: the modular character `α`, as a linear functional on
  `H`.
* `TauCeti.HopfAlgebra.modularCharacterAlgHom`: the modular character as an algebra map
  `H →ₐ[k] k`, when the left integrals form a line.

## Main results

* `TauCeti.HopfAlgebra.mul_eq_modularCharacter_smul`: `t * h = α h • t` for every left integral
  `t`.
* `TauCeti.HopfAlgebra.modularCharacter_eq_of_mul_eq_smul`: `α h` is the only scalar `c` with
  `Λ * h = c • Λ` for a nonzero left integral `Λ`.
* `TauCeti.HopfAlgebra.modularCharacter_eq_counit_iff`: `α` is the counit exactly when every left
  integral is a right integral.
* `LinearMap.IsRightInvariantIntegral.nakayamaAut_symm_eq_winding`: the inverse of the Nakayama
  automorphism of a nonzero right cointegral is `y ↦ ∑ α(y₁) S²(y₂)`.
* `LinearMap.IsRightInvariantIntegral.apply_mul_eq_sum_modularCharacter`: the twisted trace
  property `φ (x * y) = ∑ α(y₁) φ (S²(y₂) * x)`.

## References

* D. Fischman, S. Montgomery and H.-J. Schneider, *Frobenius extensions of subalgebras of Hopf
  algebras*, Trans. Amer. Math. Soc. 349 (1997), Lemma 1.5, p. 4862. The formula there is
  stated through the modular character `α' = α⁻¹ = α ∘ S` of the right integrals.
* K. Erdmann, Ø. Solberg and X. Wang, *On the structure and cohomology ring of connected Hopf
  algebras*, J. Algebra 527 (2019), 366–398, arXiv:1710.11558, Theorem 2.2.
* D. E. Radford, *The trace function and Hopf algebras*, J. Algebra 163 (1994).
-/

public section

open Coalgebra HopfAlgebra Module

namespace TauCeti.HopfAlgebra

section Bialgebra

variable (k H : Type*) [Field k] [Ring H] [Bialgebra k H]

/-- Right multiplication on the space of left integrals, which is a right ideal:
`mulRightLeftIntegral k H h` sends a left integral `t` to `t * h`. -/
def mulRightLeftIntegral : H →ₗ[k] Module.End k (leftIntegral k H) where
  toFun h := (LinearMap.mulRight k h).restrict fun t ht ↦ by
    rw [LinearMap.mulRight_apply]; exact mul_mem_leftIntegral ht h
  map_add' a b := by ext x; simp [mul_add]
  map_smul' c a := by ext x; simp

@[simp]
theorem coe_mulRightLeftIntegral_apply (h : H) (t : leftIntegral k H) :
    (mulRightLeftIntegral k H h t : H) = t * h :=
  (rfl)

/-- The **modular character** of a bialgebra `H` over a field: `modularCharacter k H h` is the
trace of right multiplication by `h` on the space of left integrals. When the left integrals form
a line spanned by `Λ`, it is the scalar `α h` with `Λ * h = α h • Λ`
(`TauCeti.HopfAlgebra.mul_eq_modularCharacter_smul`). -/
noncomputable def modularCharacter : H →ₗ[k] k :=
  LinearMap.trace k (leftIntegral k H) ∘ₗ mulRightLeftIntegral k H

/-- The modular character at `h` is the trace of right multiplication by `h` on the left
integrals. -/
theorem modularCharacter_apply (h : H) :
    modularCharacter k H h = LinearMap.trace k (leftIntegral k H) (mulRightLeftIntegral k H h) :=
  (rfl)

variable {k H}

/-- **The defining property of the modular character.** If the left integrals form a line, then
right multiplication by `h` acts on every left integral `t` as the scalar `α h`. -/
theorem mul_eq_modularCharacter_smul (hH : finrank k (leftIntegral k H) = 1) {t : H}
    (ht : t ∈ leftIntegral k H) (h : H) : t * h = modularCharacter k H h • t := by
  have : Module.Finite k (leftIntegral k H) := Module.finite_of_finrank_eq_succ hH
  obtain ⟨c, hc, -⟩ :=
    LinearMap.existsUnique_eq_smul_id_of_finrank_eq_one hH (mulRightLeftIntegral k H h)
  have hα : modularCharacter k H h = c := by
    rw [modularCharacter_apply, hc, map_smul, LinearMap.trace_id, hH]
    simp
  rw [hα]
  simpa using congrArg Subtype.val (LinearMap.congr_fun hc ⟨t, ht⟩)

/-- **Uniqueness of the modular character.** If the left integrals form a line and `Λ` is a
nonzero left integral with `Λ * h = c • Λ`, then `c` is the modular character at `h`. In
particular the modular character does not depend on the choice of `Λ`. -/
theorem modularCharacter_eq_of_mul_eq_smul (hH : finrank k (leftIntegral k H) = 1) {t : H}
    (ht : t ∈ leftIntegral k H) (ht0 : t ≠ 0) {h : H} {c : k} (hc : t * h = c • t) :
    modularCharacter k H h = c :=
  smul_left_injective k ht0 ((mul_eq_modularCharacter_smul hH ht h).symm.trans hc)

/-- A nonzero left integral, which exists when the left integrals form a line. -/
private theorem exists_mem_leftIntegral_ne_zero (hH : finrank k (leftIntegral k H) = 1) :
    ∃ t ∈ leftIntegral k H, t ≠ 0 := by
  have : Module.Finite k (leftIntegral k H) := Module.finite_of_finrank_eq_succ hH
  obtain ⟨t, ht⟩ := finrank_pos_iff_exists_ne_zero.mp (hH ▸ Nat.one_pos)
  exact ⟨t, t.property, fun h ↦ ht (Subtype.ext h)⟩

/-- The modular character is unital when the left integrals form a line. -/
theorem modularCharacter_one (hH : finrank k (leftIntegral k H) = 1) :
    modularCharacter k H 1 = 1 := by
  obtain ⟨t, ht, ht0⟩ := exists_mem_leftIntegral_ne_zero hH
  exact modularCharacter_eq_of_mul_eq_smul hH ht ht0 (by simp)

/-- The modular character is multiplicative when the left integrals form a line. -/
theorem modularCharacter_mul (hH : finrank k (leftIntegral k H) = 1) (a b : H) :
    modularCharacter k H (a * b) = modularCharacter k H a * modularCharacter k H b := by
  obtain ⟨t, ht, ht0⟩ := exists_mem_leftIntegral_ne_zero hH
  refine modularCharacter_eq_of_mul_eq_smul hH ht ht0 ?_
  rw [← mul_assoc, mul_eq_modularCharacter_smul hH ht a, smul_mul_assoc,
    mul_eq_modularCharacter_smul hH ht b, smul_smul]

/-- The modular character as an algebra map `H →ₐ[k] k`, when the left integrals form a line. -/
noncomputable def modularCharacterAlgHom (hH : finrank k (leftIntegral k H) = 1) :
    H →ₐ[k] k :=
  .ofLinearMap (modularCharacter k H) (modularCharacter_one hH) (modularCharacter_mul hH)

@[simp]
theorem modularCharacterAlgHom_apply (hH : finrank k (leftIntegral k H) = 1) (h : H) :
    modularCharacterAlgHom hH h = modularCharacter k H h :=
  (rfl)

/-- **Unimodularity through the modular character.** If the left integrals form a line, the
modular character is the counit exactly when every left integral is also a right integral. -/
theorem modularCharacter_eq_counit_iff (hH : finrank k (leftIntegral k H) = 1) :
    modularCharacter k H = counit ↔ leftIntegral k H ≤ rightIntegral k H := by
  constructor
  · intro hα t ht
    rw [mem_rightIntegral_iff]
    intro h
    rw [mul_eq_modularCharacter_smul hH ht, hα]
  · intro hle
    obtain ⟨t, ht, ht0⟩ := exists_mem_leftIntegral_ne_zero hH
    ext h
    exact modularCharacter_eq_of_mul_eq_smul hH ht ht0 (mem_rightIntegral_iff.mp (hle ht) h)

end Bialgebra

section Hopf

variable {k H : Type*} [Field k] [Ring H] [HopfAlgebra k H]

/-- The modular character is invariant under the square of the antipode, `α ∘ S² = α`. Its
convolution inverse is `α ∘ S`, see `AlgHom.antipodeComp` and `WithConv.algHom_inv_apply`. -/
theorem modularCharacter_antipode_antipode (hH : finrank k (leftIntegral k H) = 1) (h : H) :
    modularCharacter k H (antipode k (antipode k h)) = modularCharacter k H h := by
  simpa only [modularCharacterAlgHom_apply] using
    (modularCharacterAlgHom hH).apply_antipode_antipode h

/-- In finite dimension, unimodularity is triviality of the modular character. -/
theorem isUnimodular_iff_modularCharacter_eq_counit [FiniteDimensional k H] :
    IsUnimodular k H ↔ modularCharacter k H = counit := by
  rw [isUnimodular_iff, modularCharacter_eq_counit_iff (finrank_leftIntegral k H)]
  exact ⟨fun h => h.le, fun h => Submodule.eq_of_le_of_finrank_eq h (by simp)⟩

end Hopf

end TauCeti.HopfAlgebra

namespace LinearMap

open TauCeti TauCeti.HopfAlgebra

variable {k H : Type*} [Field k] [Ring H]

/-- A Frobenius functional `φ` on a finite-dimensional bialgebra reads off the modular character
from a left integral `t` normalized by `φ t = 1`: `φ (t * h) = α h`. -/
theorem IsFrobeniusFunctional.apply_mul_eq_modularCharacter [Bialgebra k H]
    [FiniteDimensional k H] {φ : H →ₗ[k] k} (hφ : φ.IsFrobeniusFunctional) {t : H}
    (ht : t ∈ leftIntegral k H) (htφ : φ t = 1) (h : H) : φ (t * h) = modularCharacter k H h := by
  rw [mul_eq_modularCharacter_smul hφ.finrank_leftIntegral ht, map_smul, htφ, smul_eq_mul,
    mul_one]

variable [HopfAlgebra k H] [FiniteDimensional k H] {φ : H →ₗ[k] k}

/-- **The Hopf form of the Nakayama automorphism.** For a nonzero right invariant functional
`φ` (a right cointegral) on a finite-dimensional Hopf algebra, the inverse of the Nakayama
automorphism `ν` of the Frobenius functional `φ`, defined by `φ (a * b) = φ (b * ν a)`, is the
winding automorphism `y ↦ ∑ α(y₁) S²(y₂)`, where `α` is the modular character. The coproduct
representation of `y` is arbitrary. -/
theorem IsRightInvariantIntegral.nakayamaAut_symm_eq_winding (hφ : φ.IsRightInvariantIntegral)
    (h0 : φ ≠ 0) {y : H} {ι : Type*} (r : Coalgebra.Repr k y ι) :
    (hφ.isFrobeniusFunctional h0).nakayamaAut.symm y =
      ∑ i ∈ r.index, modularCharacter k H (r.left i) • antipode k (antipode k (r.right i)) := by
  classical
  have hF := hφ.isFrobeniusFunctional h0
  obtain ⟨⟨t, ht⟩, htφ, -⟩ := hF.existsUnique_leftIntegral_apply_eq_one
  let rt := ℛ k t
  set z := hF.nakayamaAut.symm y
  -- The pairing against the Frobenius dual basis `{tᵢ}` moves `z` across as `y`.
  have hz (i) : φ (z * rt.left i) = φ (rt.left i * y) := by
    rw [← hF.apply_mul_nakayamaAut z, AlgEquiv.apply_symm_apply]
  calc z = ∑ i ∈ rt.index, φ (z * rt.left i) • antipode k (rt.right i) :=
        (hφ.sum_apply_mul_smul_antipode ht htφ rt z).symm
    _ = antipode k (∑ i ∈ rt.index, φ (rt.left i * y) • rt.right i) := by
        simp [hz, map_sum]
    _ = antipode k (∑ j ∈ r.index, φ (t * r.left j) • antipode k (r.right j)) := by
        rw [hφ.strong_invariance rt r]
    _ = _ := by
        simp [hF.apply_mul_eq_modularCharacter ht htφ, map_sum]

/-- For a unimodular finite-dimensional Hopf algebra, the inverse Nakayama automorphism of a
nonzero right cointegral is the square of the antipode. -/
theorem IsRightInvariantIntegral.nakayamaAut_symm_eq_antipode_antipode
    (hφ : φ.IsRightInvariantIntegral) (h0 : φ ≠ 0) (hH : IsUnimodular k H) (y : H) :
    (hφ.isFrobeniusFunctional h0).nakayamaAut.symm y = antipode k (antipode k y) := by
  rw [hφ.nakayamaAut_symm_eq_winding h0 (ℛ k y),
    isUnimodular_iff_modularCharacter_eq_counit.mp hH]
  simpa only [map_sum, map_smul] using
    congrArg (fun x => antipode k (antipode k x)) (sum_counit_smul (ℛ k y))

/-- **The twisted trace property of a right cointegral.** For a nonzero right invariant
functional `φ` on a finite-dimensional Hopf algebra, `φ (x * y) = ∑ α(y₁) φ (S²(y₂) * x)`, where
`α` is the modular character. The coproduct representation of `y` is arbitrary. -/
theorem IsRightInvariantIntegral.apply_mul_eq_sum_modularCharacter
    (hφ : φ.IsRightInvariantIntegral) (h0 : φ ≠ 0) (x : H) {y : H} {ι : Type*}
    (r : Coalgebra.Repr k y ι) :
    φ (x * y) = ∑ i ∈ r.index,
      modularCharacter k H (r.left i) * φ (antipode k (antipode k (r.right i)) * x) := by
  have hF := hφ.isFrobeniusFunctional h0
  have h := hF.apply_mul_nakayamaAut (hF.nakayamaAut.symm y) x
  rw [AlgEquiv.apply_symm_apply] at h
  rw [h, hφ.nakayamaAut_symm_eq_winding h0 r]
  simp [Finset.sum_mul]

end LinearMap
