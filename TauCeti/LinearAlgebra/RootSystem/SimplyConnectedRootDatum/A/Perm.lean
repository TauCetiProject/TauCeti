/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Group.End
public import TauCeti.LinearAlgebra.RootSystem.SimplyConnectedRootDatum.A

/-!
# Permuting the roots of type `Aₙ`

The roots of the pinned type `Aₙ` datum `TauCeti.DynkinType.typeASimplyConnectedRootDatum` are the
`n * (n + 1)` vectors `e_a - e_b` with `a ≠ b` in `Fin (n + 1)`, indexed by the ordered pairs
`TauCeti.DynkinType.TypeAIndex n` and, through the Bourbaki enumeration
`TauCeti.DynkinType.typeAIndexEquiv`, by `Fin (n * (n + 1))`. A permutation of the `n + 1`
coordinates of the classical model acts entrywise on those pairs, hence on the root indices. This
file records that action as a group homomorphism and proves it faithful.

Faithfulness is read off the first entry: a pair with any prescribed first entry exists unless
`n = 0`, where the permutation group is trivial anyway.

## Main definitions

* `TauCeti.DynkinType.typeAPairPermHom`: the entrywise action of `Equiv.Perm (Fin (n + 1))` on the
  ordered pairs of distinct elements indexing the roots.
* `TauCeti.DynkinType.typeAIndexPermHom`: the same action read through the Bourbaki enumeration of
  the roots by `Fin (n * (n + 1))`.

## Main results

* `TauCeti.DynkinType.typeAPairPermHom_injective` and
  `TauCeti.DynkinType.typeAIndexPermHom_injective`: both actions are faithful.

## References

See N. Bourbaki, *Lie Groups and Lie Algebras, Chapters 4--6*, Ch. VI §4.7 for the classical model
of the roots of type `Aₙ` that this action permutes.
-/

public section

namespace TauCeti

open Function

namespace DynkinType

variable {n : ℕ}

/-- The entrywise action of `Equiv.Perm (Fin (n + 1))` on the ordered pairs of distinct entries
indexing the roots of type `Aₙ`, as a group homomorphism. -/
def typeAPairPermHom (n : ℕ) : Equiv.Perm (Fin (n + 1)) →* Equiv.Perm (TypeAIndex n) where
  toFun σ := Equiv.subtypeEquiv (σ.prodCongr σ) fun _ ↦ by simp
  map_one' := Equiv.ext fun _ ↦ Subtype.ext (rfl)
  map_mul' _ _ := Equiv.ext fun _ ↦ Subtype.ext (rfl)

@[simp]
theorem coe_typeAPairPermHom (σ : Equiv.Perm (Fin (n + 1))) (p : TypeAIndex n) :
    ((typeAPairPermHom n σ p : TypeAIndex n) : Fin (n + 1) × Fin (n + 1)) =
      (σ p.val.1, σ p.val.2) :=
  (rfl)

/-- **The entrywise action on ordered pairs is faithful.** A permutation of `Fin (n + 1)` is
recovered from its action on pairs by reading off the first entry, there being a pair with any
prescribed first entry unless `n = 0`, where the permutation group is trivial anyway. -/
theorem typeAPairPermHom_injective : Injective (typeAPairPermHom (n := n)) := by
  intro σ τ hστ
  refine Equiv.ext fun a ↦ ?_
  obtain _ | m := n
  · have h₁ := (σ a).isLt
    have h₂ := (τ a).isLt
    exact Fin.ext (by omega)
  · obtain ⟨b, hb⟩ := exists_ne a
    have h : typeAPairPermHom (m + 1) σ ⟨(a, b), Ne.symm hb⟩ =
        typeAPairPermHom (m + 1) τ ⟨(a, b), Ne.symm hb⟩ := by
      rw [hστ]
    simpa using congrArg (fun p : TypeAIndex (m + 1) ↦ (p : Fin (m + 2) × Fin (m + 2)).1) h

/-- The entrywise action of `Equiv.Perm (Fin (n + 1))` on the roots of type `Aₙ`, read through the
Bourbaki enumeration of the roots by `Fin (n * (n + 1))`. -/
def typeAIndexPermHom (n : ℕ) :
    Equiv.Perm (Fin (n + 1)) →* Equiv.Perm (Fin (n * (n + 1))) :=
  (Equiv.permCongrHom (typeAIndexEquiv n)).toMonoidHom.comp (typeAPairPermHom n)

theorem typeAIndexPermHom_apply (σ : Equiv.Perm (Fin (n + 1))) (k : Fin (n * (n + 1))) :
    typeAIndexPermHom n σ k =
      typeAIndexEquiv n (typeAPairPermHom n σ ((typeAIndexEquiv n).symm k)) :=
  (rfl)

/-- The action on root indices is faithful, the Bourbaki enumeration being a bijection. -/
theorem typeAIndexPermHom_injective : Injective (typeAIndexPermHom (n := n)) :=
  (Equiv.permCongrHom (typeAIndexEquiv n)).injective.comp typeAPairPermHom_injective

end DynkinType

end TauCeti
