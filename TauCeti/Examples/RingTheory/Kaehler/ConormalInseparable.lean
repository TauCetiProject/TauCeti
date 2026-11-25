/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Kaehler.Basic
public import Mathlib.Algebra.Polynomial.Degree.Operations
public import Mathlib.RingTheory.Ideal.Cotangent

/-!
# Check: the conormal map of `k[X] → k[X] / (X ^ p - t)` in characteristic `p`

Tau Ceti's `KaehlerDifferential.kerCotangentToTensor_bijective_of_formallyEtale` says that for a
surjection `P → S` with kernel `I` onto a formally étale `k`-algebra `S`, the conormal map
`I/I² → S ⊗[P] Ω[P⁄k]` is bijective, identifying `I/I²` with `S ⊗[P] Ω[P⁄k]`. The formal
étaleness cannot be dropped: for a field `k` of characteristic `p`, any `t : k` and
`f = X ^ p - t`, the class of `f` spans `I/I²` for `I = (f)` and is nonzero, but it maps to
`1 ⊗ df = 1 ⊗ p X ^ (p - 1) dX = 0`
(`TauCeti.ConormalInseparableExample.not_injective_kerCotangentToTensor`). For `k = 𝔽_p(t)` the
quotient `k[X] / (f)` is the inseparable field `k(t ^ (1 / p))`.
-/

public section

open Polynomial KaehlerDifferential

namespace TauCeti.ConormalInseparableExample

variable {k : Type*} [Field k]

/-- **Check.** In characteristic `p`, for `f = X ^ p - t`, the conormal map
`(f) / (f)² → (k[X] / (f)) ⊗[k[X]] Ω[k[X]⁄k]` is not injective: it kills the nonzero class of `f`,
since `df = p X ^ (p - 1) dX = 0`. -/
theorem not_injective_kerCotangentToTensor (p : ℕ) [Fact p.Prime] [CharP k p] (t : k) :
    ¬ Function.Injective
      (kerCotangentToTensor k k[X] (k[X] ⧸ Ideal.span {X ^ p - C t})) := by
  set f : k[X] := X ^ p - C t with hfdef
  have hker : RingHom.ker (algebraMap k[X] (k[X] ⧸ Ideal.span {f})) = Ideal.span {f} := by
    rw [Ideal.Quotient.algebraMap_eq, Ideal.mk_ker]
  have hf : f ∈ RingHom.ker (algebraMap k[X] (k[X] ⧸ Ideal.span {f})) := by
    rw [hker]
    exact Ideal.mem_span_singleton_self f
  have hD : D k k[X] f = 0 := by
    have hC : D k k[X] (C t) = 0 := (D k k[X]).map_algebraMap t
    simp [hfdef, hC, Derivation.leibniz_pow, ← Nat.cast_smul_eq_nsmul k[X], CharP.cast_eq_zero]
  intro h
  have h0 : (RingHom.ker (algebraMap k[X] (k[X] ⧸ Ideal.span {f}))).toCotangent ⟨f, hf⟩ = 0 :=
    h (by rw [map_zero, kerCotangentToTensor_toCotangent, hD, TensorProduct.tmul_zero])
  rw [Ideal.toCotangent_eq_zero] at h0
  have h0' : f ∈ Ideal.span {f} ^ 2 := hker ▸ h0
  rw [Ideal.span_singleton_pow, Ideal.mem_span_singleton] at h0'
  -- `f ^ 2 ∣ f` forces `f` to be a unit, but `f` has degree `p > 0`.
  obtain ⟨g, hg⟩ := h0'
  have hp := (Fact.out : p.Prime)
  have hf0 : f ≠ 0 := X_pow_sub_C_ne_zero hp.pos t
  have hunit : IsUnit f := IsUnit.of_mul_eq_one g (by
    have : f * (f * g) = f * 1 := by rw [mul_one, ← mul_assoc, ← sq, ← hg]
    exact mul_left_cancel₀ hf0 this)
  have hdeg : f.natDegree = p := by rw [hfdef, natDegree_X_pow_sub_C]
  exact hp.ne_zero (hdeg ▸ natDegree_eq_zero_of_isUnit hunit)

end TauCeti.ConormalInseparableExample
