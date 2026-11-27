/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.ZMod.QuotientRing
public import Mathlib.SetTheory.Cardinal.Finite
public import TauCeti.LinearAlgebra.Unimodular

/-!
# Counting unimodular vectors over products of rings

The number of unimodular coordinate vectors `v : ι → R` is invariant under ring isomorphisms, and
over a product `R × S` it is the product of the numbers over `R` and over `S`, because a vector
over `R × S` is unimodular exactly when both of its components are
(`TauCeti.Module.isUnimodular_pi_prod_iff`). Through the Chinese remainder theorem this makes the
number of unimodular vectors modulo `Q` multiplicative in coprime moduli. Modulo a prime power the
count is the local-ring count `TauCeti.IsLocalRing.card_isUnimodular`.

## Main results

* `TauCeti.Module.card_isUnimodular_congr`: ring isomorphisms preserve the count.
* `TauCeti.Module.card_isUnimodular_prod`: the count over `R × S` is the product of the counts.
* `TauCeti.Module.card_isUnimodular_pi`: the analogous product for a finite family of semirings.
* `TauCeti.Module.card_isUnimodular_zmod_mul`: for coprime `Q₁` and `Q₂`, the count modulo
  `Q₁ Q₂` is the product of the counts modulo `Q₁` and modulo `Q₂`.
-/

public section

namespace TauCeti.Module

variable {ι R S : Type*} [Finite ι] [Semiring R] [Semiring S]

variable (ι) in
/-- Ring isomorphisms preserve the number of unimodular coordinate vectors. -/
theorem card_isUnimodular_congr (e : R ≃+* S) :
    Nat.card {v : ι → S // Module.IsUnimodular S v} =
      Nat.card {v : ι → R // Module.IsUnimodular R v} :=
  (Nat.card_congr ((Equiv.piCongrRight fun _ ↦ e.toEquiv).subtypeEquiv fun _ ↦
    (e.isUnimodular_comp_iff).symm)).symm

variable (ι R S) in
/-- The number of unimodular coordinate vectors over a product of semirings is the product of the
numbers over the factors. -/
theorem card_isUnimodular_prod :
    Nat.card {v : ι → R × S // Module.IsUnimodular (R × S) v} =
      Nat.card {v : ι → R // Module.IsUnimodular R v} *
        Nat.card {v : ι → S // Module.IsUnimodular S v} := by
  rw [← Nat.card_prod]
  exact Nat.card_congr (((Equiv.arrowProdEquivProdArrow ι (fun _ ↦ R) (fun _ ↦ S)).subtypeEquiv
    fun _ ↦ isUnimodular_pi_prod_iff).trans (Equiv.subtypeProdEquivProd))

omit [Finite ι] in
variable (ι) in
/-- The number of unimodular rows over a finite product of semirings is the product of
the numbers of unimodular rows over its factors. -/
theorem card_isUnimodular_pi {κ : Type*} [Fintype κ] (B : κ → Type*) [∀ k, Semiring (B k)] :
    Nat.card {v : ι → ∀ k, B k // Module.IsUnimodular (∀ k, B k) v} =
      ∏ k, Nat.card {v : ι → B k // Module.IsUnimodular (B k) v} := by
  rw [← Nat.card_pi]
  exact Nat.card_congr (((Equiv.piComm fun (_ : ι) k ↦ B k).subtypeEquiv
    fun _ ↦ isUnimodular_pi_pi_iff).trans Equiv.subtypePiEquivPi)

variable (ι) in
/-- **Chinese remainder theorem for unimodular vectors.** For coprime moduli, the number of
unimodular coordinate vectors modulo `Q₁ Q₂` is the product of the numbers modulo `Q₁` and
modulo `Q₂`. -/
theorem card_isUnimodular_zmod_mul {Q₁ Q₂ : ℕ} (h : Q₁.Coprime Q₂) :
    Nat.card {v : ι → ZMod (Q₁ * Q₂) // Module.IsUnimodular (ZMod (Q₁ * Q₂)) v} =
      Nat.card {v : ι → ZMod Q₁ // Module.IsUnimodular (ZMod Q₁) v} *
        Nat.card {v : ι → ZMod Q₂ // Module.IsUnimodular (ZMod Q₂) v} := by
  rw [← card_isUnimodular_prod, card_isUnimodular_congr ι (ZMod.chineseRemainder h)]

end TauCeti.Module
