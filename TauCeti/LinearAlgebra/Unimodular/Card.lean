/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.ZMod.QuotientRing
public import Mathlib.SetTheory.Cardinal.Finite
public import TauCeti.LinearAlgebra.Unimodular

import Mathlib.Algebra.Ring.Fin

/-!
# Counting unimodular vectors over products of rings

The `Nat.card` of the unimodular coordinate vectors `v : ι → R` is invariant under ring
isomorphisms and multiplicative over a finite family of factors. Each infinite row set contributes
zero. Through the Chinese remainder theorem this gives multiplicativity in coprime moduli.
Modulo a prime power the count is the local-ring count `TauCeti.IsLocalRing.card_isUnimodular`.

## Main results

* `TauCeti.Module.card_isUnimodular_congr`: ring isomorphisms preserve the cardinality.
* `TauCeti.Module.card_isUnimodular_prod`: the binary product formula.
* `TauCeti.Module.card_isUnimodular_pi`: the product of the `Nat.card` values for a finite family.
* `TauCeti.Module.card_isUnimodular_zmod_mul`: for coprime `Q₁` and `Q₂`, the count modulo
  `Q₁ Q₂` is the product of the counts modulo `Q₁` and modulo `Q₂`.
-/

public section

namespace TauCeti.Module

universe u v

variable {ι : Type*} {R : Type u} {S : Type v} [Semiring R] [Semiring S]

variable (ι) in
/-- Ring isomorphisms preserve the `Nat.card` of unimodular coordinate vectors. -/
theorem card_isUnimodular_congr (e : R ≃+* S) :
    Nat.card {v : ι → S // Module.IsUnimodular S v} =
      Nat.card {v : ι → R // Module.IsUnimodular R v} :=
  (Nat.card_congr ((Equiv.piCongrRight fun _ ↦ e.toEquiv).subtypeEquiv fun _ ↦
    (e.isUnimodular_comp_iff).symm)).symm

variable (ι) in
/-- The `Nat.card` of unimodular rows over a finite product of semirings is the product of
the corresponding `Nat.card` values over its factors, each of which is zero for an infinite row
set. -/
theorem card_isUnimodular_pi {κ : Type*} [Fintype κ] (B : κ → Type*) [∀ k, Semiring (B k)] :
    Nat.card {v : ι → ∀ k, B k // Module.IsUnimodular (∀ k, B k) v} =
      ∏ k, Nat.card {v : ι → B k // Module.IsUnimodular (B k) v} := by
  rw [← Nat.card_pi]
  exact Nat.card_congr (((Equiv.piComm fun (_ : ι) k ↦ B k).subtypeEquiv
    fun _ ↦ isUnimodular_pi_pi_iff).trans Equiv.subtypePiEquivPi)

variable (ι R S) in
/-- The `Nat.card` of unimodular coordinate vectors over a binary product of semirings is the
product of the corresponding `Nat.card` values over the factors. -/
theorem card_isUnimodular_prod :
    Nat.card {v : ι → R × S // Module.IsUnimodular (R × S) v} =
      Nat.card {v : ι → R // Module.IsUnimodular R v} *
        Nat.card {v : ι → S // Module.IsUnimodular S v} := by
  let B : Fin 2 → Type (max u v) := Fin.cons (ULift.{v} R) (fun _ ↦ ULift.{u} S)
  let (k : Fin 2) : Semiring (B k) := Fin.cases (inferInstance : Semiring (ULift.{v} R))
    (fun _ ↦ (inferInstance : Semiring (ULift.{u} S))) k
  let e := (RingEquiv.piFinTwo B).trans (RingEquiv.prodCongr ULift.ringEquiv ULift.ringEquiv)
  rw [card_isUnimodular_congr ι e, card_isUnimodular_pi, Fin.prod_univ_two]
  -- Reduce the local family `B` and its `Fin.cases` instances at the two indices
  -- so that the two cardinality factors can be rewritten using `ULift.ringEquiv`.
  change Nat.card {w : ι → ULift.{v} R // Module.IsUnimodular (ULift.{v} R) w} *
    Nat.card {w : ι → ULift.{u} S // Module.IsUnimodular (ULift.{u} S) w} = _
  rw [← card_isUnimodular_congr ι (ULift.ringEquiv : ULift.{v} R ≃+* R),
    ← card_isUnimodular_congr ι (ULift.ringEquiv : ULift.{u} S ≃+* S)]

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
