/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.RootSystem.Weyl.ParabolicQuotient
public import TauCeti.LinearAlgebra.RootSystem.Weyl.TypeA.Presentation

/-!
# Type `A` minimal coset representatives

On a finite reduced crystallographic root pairing `(P, b)` of Cartan type `Aₙ` over a commutative
domain of characteristic zero, a weight `λ` that lies off every simple root wall
(`∀ i : b.support, ⟨λ, αᵢ^∨⟩ ≠ 0`, so `P.wallIndices b lam = ∅`; when `λ` is dominant this means
`λ` is regular and its stabilizer `W_λ` is trivial) has all `(n + 1)!` Weyl group elements as
minimal coset representatives.

This file lifts the marked Weyl group isomorphism `RootPairing.typeAWeylGroupEquiv` to the subtype
of minimal coset representatives (`RootPairing.typeAMinimalCosetRepEquiv`), transfers the Bruhat
order along it and its inverse, and records the cardinality `(n + 1)!`.

## Main definitions

* `RootPairing.typeAMinimalCosetRepEquiv`: Bruhat-preserving equivalence between minimal coset
  representatives for `P.wallIndices b lam` in type `Aₙ` (when `∀ i : b.support, ⟨λ, αᵢ^∨⟩ ≠ 0`)
  and `Equiv.Perm (Fin (n + 1))`.

## Main results

* `RootPairing.typeAMinimalCosetRepEquiv_apply` and
  `RootPairing.coe_typeAMinimalCosetRepEquiv_symm`: defining evaluation lemmas relating
  `typeAMinimalCosetRepEquiv` to `RootPairing.typeAWeylGroupEquiv`.
* `RootPairing.bruhatLE_typeAMinimalCosetRepEquiv_iff` and
  `RootPairing.bruhatLE_typeAMinimalCosetRepEquiv_symm_iff`: `typeAMinimalCosetRepEquiv` and its
  inverse preserve and reflect the Bruhat order.
* `RootPairing.card_minimalCosetRep_of_hasCartanType_A`: in type `Aₙ` off all simple root walls,
  there are `(n + 1)!` minimal coset representatives for `P.wallIndices b lam`.

## References

* A. Björner and F. Brenti, *Combinatorics of Coxeter Groups*, GTM 231, Springer (2005), §§2.2–2.5.
-/

public section

open TauCeti

namespace RootPairing

variable {ι R M N : Type*} [CommRing R] [AddCommGroup M] [Module R M] [AddCommGroup N]
  [Module R N] (P : RootPairing ι R M N) [Finite ι] [CharZero R] [IsDomain R]
  [P.IsCrystallographic] [P.IsReduced] (b : P.Base) {lam : M}

/-- On a root pairing of Cartan type `Aₙ` at a weight `λ` off all simple root walls
(`∀ i : b.support, ⟨λ, αᵢ^∨⟩ ≠ 0`, so `P.wallIndices b lam = ∅`; when `λ` is dominant this means
`λ` is regular and `W_λ` is trivial), the minimal coset representatives for `P.wallIndices b lam`
identify with `Equiv.Perm (Fin (n + 1))` via `RootPairing.typeAWeylGroupEquiv`. -/
noncomputable def typeAMinimalCosetRepEquiv {n : ℕ} (e : b.support ≃ Fin n)
    (he : ∀ i j, b.cartanMatrix i j = CartanMatrix.A n (e i) (e j))
    (hreg : ∀ i : b.support, P.coroot' i lam ≠ 0) :
    {w // (weylCoxeterSystem P b).IsMinimalCosetRep (P.wallIndices b lam) w} ≃
      Equiv.Perm (Fin (n + 1)) where
  toFun u := P.typeAWeylGroupEquiv b e he u.val
  invFun σ := ⟨(P.typeAWeylGroupEquiv b e he).symm σ, by
    have hwall : P.wallIndices b lam = ∅ :=
      Set.eq_empty_iff_forall_notMem.mpr fun i hi ↦ hreg i (mem_wallIndices.mp hi)
    simp [hwall]⟩
  left_inv u := Subtype.ext ((P.typeAWeylGroupEquiv b e he).symm_apply_apply u.val)
  right_inv σ := (P.typeAWeylGroupEquiv b e he).apply_symm_apply σ

/-- Applying `typeAMinimalCosetRepEquiv` applies `RootPairing.typeAWeylGroupEquiv` to the
underlying Weyl group element. -/
@[simp]
theorem typeAMinimalCosetRepEquiv_apply {n : ℕ} (e : b.support ≃ Fin n)
    (he : ∀ i j, b.cartanMatrix i j = CartanMatrix.A n (e i) (e j))
    (hreg : ∀ i : b.support, P.coroot' i lam ≠ 0)
    (u : {w // (weylCoxeterSystem P b).IsMinimalCosetRep (P.wallIndices b lam) w}) :
    P.typeAMinimalCosetRepEquiv b e he hreg u = P.typeAWeylGroupEquiv b e he u.val :=
  (rfl)

/-- The underlying Weyl group element of `(typeAMinimalCosetRepEquiv e he hreg).symm σ` is
`(P.typeAWeylGroupEquiv b e he).symm σ`. -/
@[simp]
theorem coe_typeAMinimalCosetRepEquiv_symm {n : ℕ} (e : b.support ≃ Fin n)
    (he : ∀ i j, b.cartanMatrix i j = CartanMatrix.A n (e i) (e j))
    (hreg : ∀ i : b.support, P.coroot' i lam ≠ 0) (σ : Equiv.Perm (Fin (n + 1))) :
    ((P.typeAMinimalCosetRepEquiv b e he hreg).symm σ).val =
      (P.typeAWeylGroupEquiv b e he).symm σ :=
  (rfl)

/-- `typeAMinimalCosetRepEquiv` preserves and reflects the Bruhat order. -/
-- Fires before `typeAMinimalCosetRepEquiv_apply` unfolds the equivalence to `typeAWeylGroupEquiv`.
@[simp↓]
theorem bruhatLE_typeAMinimalCosetRepEquiv_iff {n : ℕ} (e : b.support ≃ Fin n)
    (he : ∀ i j, b.cartanMatrix i j = CartanMatrix.A n (e i) (e j))
    (hreg : ∀ i : b.support, P.coroot' i lam ≠ 0)
    {u v : {w // (weylCoxeterSystem P b).IsMinimalCosetRep (P.wallIndices b lam) w}} :
    (permCoxeterSystem (n + 1)).BruhatLE
        (P.typeAMinimalCosetRepEquiv b e he hreg u)
        (P.typeAMinimalCosetRepEquiv b e he hreg v) ↔
      (weylCoxeterSystem P b).BruhatLE u.val v.val :=
  P.bruhatLE_typeAWeylGroupEquiv_iff b e he

/-- The inverse of `typeAMinimalCosetRepEquiv` preserves and reflects the Bruhat order. -/
-- Fires before `coe_typeAMinimalCosetRepEquiv_symm` unfolds the inverse to `typeAWeylGroupEquiv`.
@[simp↓]
theorem bruhatLE_typeAMinimalCosetRepEquiv_symm_iff {n : ℕ} (e : b.support ≃ Fin n)
    (he : ∀ i j, b.cartanMatrix i j = CartanMatrix.A n (e i) (e j))
    (hreg : ∀ i : b.support, P.coroot' i lam ≠ 0)
    {σ τ : Equiv.Perm (Fin (n + 1))} :
    (weylCoxeterSystem P b).BruhatLE
        ((P.typeAMinimalCosetRepEquiv b e he hreg).symm σ).val
        ((P.typeAMinimalCosetRepEquiv b e he hreg).symm τ).val ↔
      (permCoxeterSystem (n + 1)).BruhatLE σ τ :=
  P.bruhatLE_typeAWeylGroupEquiv_symm_iff b e he

/-- On a root pairing of Cartan type `Aₙ` at a weight `λ` off all simple root walls, there are
`(n + 1)!` minimal coset representatives for `P.wallIndices b lam`. -/
theorem card_minimalCosetRep_of_hasCartanType_A {n : ℕ} (hA : HasCartanType P b (.A n))
    (hreg : ∀ i : b.support, P.coroot' i lam ≠ 0) :
    Nat.card {w // (weylCoxeterSystem P b).IsMinimalCosetRep (P.wallIndices b lam) w} =
      (n + 1).factorial := by
  obtain ⟨e, he⟩ := (hasCartanType_iff b (.A n)).mp hA
  rw [DynkinType.cartanMatrix_A] at he
  rw [Nat.card_congr (P.typeAMinimalCosetRepEquiv b e he hreg), Nat.card_perm, Nat.card_fin]
  simp

end RootPairing
