/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic

/-!
# Automorphisms fixing a generating set are the identity

If a set `s` generates a field extension `E/F` (`IntermediateField.adjoin F s = ⊤`), then an
`F`-algebra automorphism of `E` fixing every element of `s` is the identity. This is the
whole-field counterpart of Mathlib's `IntermediateField.algHom_ext_of_eq_adjoin` (which
compares homomorphisms out of the *subfield* `adjoin F s`), proved by the same adjoin
induction.

It is the extensionality step shared by the multiquadratic Layer 1 arguments: the splitting
law shows a decomposition-group element fixes every generator `√dᵢ` and concludes it is
trivial, and the Frobenius computation concludes the same when every Legendre symbol is `1`.

## Main result

* `TauCeti.IntermediateField.algEquiv_eq_one_of_adjoin_eq_top`: an automorphism fixing each
  element of a generating set is `1`.
-/

public section

namespace TauCeti.IntermediateField

/-- An `F`-algebra automorphism of `E` that fixes every element of a set generating `E` over
`F` is the identity. -/
theorem algEquiv_eq_one_of_adjoin_eq_top {F E : Type*} [Field F] [Field E] [Algebra F E]
    {s : Set E} (htop : IntermediateField.adjoin F s = ⊤)
    {σ : E ≃ₐ[F] E} (hfix : ∀ x ∈ s, σ x = x) : σ = 1 := by
  refine AlgEquiv.ext fun y => ?_
  rw [AlgEquiv.one_apply]
  have hy : y ∈ (⊤ : IntermediateField F E) := IntermediateField.mem_top
  rw [← htop] at hy
  induction hy using IntermediateField.adjoin_induction with
  | mem z hz => exact hfix z hz
  | algebraMap q => exact σ.commutes q
  | add a b _ _ ha hb => rw [map_add, ha, hb]
  | inv a _ ha => rw [map_inv₀, ha]
  | mul a b _ _ ha hb => rw [map_mul, ha, hb]

end TauCeti.IntermediateField
