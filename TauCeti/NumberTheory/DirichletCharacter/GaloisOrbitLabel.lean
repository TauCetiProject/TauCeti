/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Basic.Real.Basic
public import Mathlib.NumberTheory.DirichletCharacter.Basic
public import Mathlib.Order.PiLex
public import TauCeti.NumberTheory.MulChar.GaloisOrbit
import Mathlib.Data.Set.Card
import Mathlib.NumberTheory.MulChar.Duality
import Mathlib.Order.Interval.Set.Nat

/-!
# The LMFDB labels of Galois orbits of Dirichlet characters

The LMFDB groups the Dirichlet characters modulo `N` into Galois orbits (`MulChar.galoisOrbit`)
and labels the orbits `N.a`, `N.b`, `N.c`, … in a fixed order: first by the order of the
characters, then lexicographically by the vector of traces
`(tr χ(1), tr χ(2), …, tr χ(N))`, where `tr χ(n)` is the sum of `ψ(n)` over the orbit
(`MulChar.galoisTrace`). This letter is the character component `a` of the label `N.k.a.x` of a
classical modular form.

For the order to be a labelling, the sort key must be constant on Galois orbits and must
separate them. Constancy holds by construction. Separation holds already for the trace vector:
every residue modulo `N` is the class of one of `1, …, N`, and the Galois trace determines the
Galois orbit by Dedekind's independence of characters (`MulChar.galoisTrace_eq_galoisTrace_iff`).
The traces are real (`MulChar.galoisTrace_im`; in fact they are rational integers), so the key
records their real parts.

We record the label as its index `0, 1, 2, …` in this order; the LMFDB writes the index in
base `26` with the digits `a, …, z`, so that index `0` is written `a`.

## Main definitions

* `DirichletCharacter.galoisOrbitKey χ`: the LMFDB sort key of the Galois orbit of `χ`.
* `DirichletCharacter.galoisOrbitIndex χ`: the position of the Galois orbit of `χ` among the
  Galois orbits modulo `N`, counted from `0`.

## Main results

* `DirichletCharacter.galoisOrbitKey_eq_galoisOrbitKey_iff`: the sort key separates the Galois
  orbits.
* `DirichletCharacter.galoisOrbitIndex_eq_galoisOrbitIndex_iff`: two characters have the same
  index exactly when they lie in one Galois orbit.
* `DirichletCharacter.galoisOrbitIndex_lt_galoisOrbitIndex_iff`: the index lists the orbits in
  the order of their keys.
* `DirichletCharacter.range_galoisOrbitIndex`: the indices are `0, 1, …, n - 1`, where `n` is the
  number of Galois orbits.
* `DirichletCharacter.galoisOrbitIndex_eq_zero_iff`: the orbit with index `0`, labelled `a`, is
  that of the trivial character.

## References

* The LMFDB Collaboration, *Dirichlet characters: Galois orbit labels*,
  <https://www.lmfdb.org/knowledge/show/character.dirichlet.galois_orbit_label>.
* J. Best, J. Bober, A. R. Booker, E. Costa, J. E. Cremona, M. Derickx, M. Lee, D. Lowry-Duda,
  D. Roe, A. V. Sutherland, J. Voight, *Computing classical modular forms*.
-/

public section

noncomputable section

namespace DirichletCharacter

variable {N : ℕ}

/-- **The LMFDB sort key** of the Galois orbit of a Dirichlet character `χ` modulo `N`: the order
of `χ`, followed by the vector of Galois traces `(tr χ(1), …, tr χ(N))`, compared
lexicographically. The Galois traces are real (`MulChar.galoisTrace_im`), so the key records
their real parts. -/
def galoisOrbitKey (χ : DirichletCharacter ℂ N) : Lex (ℕ × Lex (Fin N → ℝ)) :=
  toLex (orderOf χ, toLex fun i : Fin N ↦ (χ.galoisTrace (((i : ℕ) + 1 : ℕ) : ZMod N)).re)

/-- The sort key as the order followed by the real parts of the Galois traces. -/
theorem galoisOrbitKey_def (χ : DirichletCharacter ℂ N) :
    χ.galoisOrbitKey =
      toLex (orderOf χ, toLex fun i : Fin N ↦ (χ.galoisTrace (((i : ℕ) + 1 : ℕ) : ZMod N)).re) :=
  (rfl)

/-- The sort key compares the orders first and then the vectors of Galois traces,
lexicographically. -/
theorem galoisOrbitKey_lt_galoisOrbitKey_iff {χ ψ : DirichletCharacter ℂ N} :
    ψ.galoisOrbitKey < χ.galoisOrbitKey ↔ orderOf ψ < orderOf χ ∨ orderOf ψ = orderOf χ ∧
      toLex (fun i : Fin N ↦ (ψ.galoisTrace (((i : ℕ) + 1 : ℕ) : ZMod N)).re) <
        toLex fun i : Fin N ↦ (χ.galoisTrace (((i : ℕ) + 1 : ℕ) : ZMod N)).re :=
  Prod.Lex.toLex_lt_toLex

/-- The trivial character has the smallest sort key. -/
theorem galoisOrbitKey_one_le (χ : DirichletCharacter ℂ N) :
    (1 : DirichletCharacter ℂ N).galoisOrbitKey ≤ χ.galoisOrbitKey := by
  obtain h | h := (Nat.one_le_iff_ne_zero.mpr χ.orderOf_pos.ne').lt_or_eq
  · exact (galoisOrbitKey_lt_galoisOrbitKey_iff.mpr (.inl (by rwa [orderOf_one]))).le
  · rw [orderOf_eq_one_iff.mp h.symm]

/-- The finite set of sort keys of the Galois orbits modulo `N`. -/
private def galoisOrbitKeys (N : ℕ) : Finset (Lex (ℕ × Lex (Fin N → ℝ))) :=
  (Set.finite_range (galoisOrbitKey (N := N))).toFinset

private theorem galoisOrbitKey_mem_galoisOrbitKeys (χ : DirichletCharacter ℂ N) :
    χ.galoisOrbitKey ∈ galoisOrbitKeys N :=
  (Set.Finite.mem_toFinset _).mpr ⟨χ, rfl⟩

/-- The numbering of the sort keys in increasing order. -/
private def galoisOrbitKeysIso (N : ℕ) :
    Fin (galoisOrbitKeys N).card ≃o galoisOrbitKeys N :=
  (galoisOrbitKeys N).orderIsoOfFin rfl

/-- **The LMFDB index of the Galois orbit** of a Dirichlet character `χ` modulo `N`: its
position, counted from `0`, when the Galois orbits modulo `N` are listed in increasing order of
their sort keys `DirichletCharacter.galoisOrbitKey`. The LMFDB writes it in base `26` with the
digits `a, …, z`, as the letter `a` of the orbit label `N.a`. -/
def galoisOrbitIndex (χ : DirichletCharacter ℂ N) : ℕ :=
  (galoisOrbitKeysIso N).symm ⟨χ.galoisOrbitKey, galoisOrbitKey_mem_galoisOrbitKeys χ⟩

/-- **The index lists the Galois orbits in the order of their sort keys.** -/
theorem galoisOrbitIndex_lt_galoisOrbitIndex_iff {χ ψ : DirichletCharacter ℂ N} :
    ψ.galoisOrbitIndex < χ.galoisOrbitIndex ↔ ψ.galoisOrbitKey < χ.galoisOrbitKey := by
  rw [galoisOrbitIndex, galoisOrbitIndex, Fin.val_fin_lt, OrderIso.lt_iff_lt, Subtype.mk_lt_mk]

/-- The index is monotone in the sort key. -/
theorem galoisOrbitIndex_le_galoisOrbitIndex_iff {χ ψ : DirichletCharacter ℂ N} :
    ψ.galoisOrbitIndex ≤ χ.galoisOrbitIndex ↔ ψ.galoisOrbitKey ≤ χ.galoisOrbitKey := by
  rw [← not_lt, ← not_lt, galoisOrbitIndex_lt_galoisOrbitIndex_iff]

/-- Characters of smaller order come first. -/
theorem galoisOrbitIndex_lt_galoisOrbitIndex_of_orderOf_lt {χ ψ : DirichletCharacter ℂ N}
    (h : orderOf ψ < orderOf χ) : ψ.galoisOrbitIndex < χ.galoisOrbitIndex :=
  galoisOrbitIndex_lt_galoisOrbitIndex_iff.mpr (galoisOrbitKey_lt_galoisOrbitKey_iff.mpr (.inl h))

variable [NeZero N]

/-- **The sort key separates the Galois orbits**: two Dirichlet characters have the same key
exactly when they lie in one Galois orbit. -/
theorem galoisOrbitKey_eq_galoisOrbitKey_iff {χ ψ : DirichletCharacter ℂ N} :
    ψ.galoisOrbitKey = χ.galoisOrbitKey ↔ ψ ∈ χ.galoisOrbit := by
  refine ⟨fun h ↦ MulChar.galoisTrace_eq_galoisTrace_iff.mp (funext fun x ↦ ?_), fun h ↦ ?_⟩
  · -- Every residue modulo `N` is the class of one of `1, …, N`.
    obtain ⟨i, rfl⟩ : ∃ i : Fin N, (((i : ℕ) + 1 : ℕ) : ZMod N) = x :=
      ⟨⟨(x - 1).val, ZMod.val_lt _⟩, by simp⟩
    have hre := congrFun (toLex.injective (Prod.ext_iff.mp (toLex.injective h)).2) i
    exact Complex.ext hre (by simp)
  · rw [galoisOrbitKey_def ψ, galoisOrbitKey_def χ, MulChar.orderOf_eq_of_mem_galoisOrbit h,
      MulChar.galoisTrace_eq_of_mem_galoisOrbit h]

/-- **The index labels the Galois orbits**: two Dirichlet characters have the same index exactly
when they lie in one Galois orbit. -/
theorem galoisOrbitIndex_eq_galoisOrbitIndex_iff {χ ψ : DirichletCharacter ℂ N} :
    ψ.galoisOrbitIndex = χ.galoisOrbitIndex ↔ ψ ∈ χ.galoisOrbit := by
  rw [← galoisOrbitKey_eq_galoisOrbitKey_iff, le_antisymm_iff, le_antisymm_iff,
    galoisOrbitIndex_le_galoisOrbitIndex_iff, galoisOrbitIndex_le_galoisOrbitIndex_iff]

/-- The sort keys are as many as the Galois orbits. -/
private theorem card_galoisOrbitKeys :
    (galoisOrbitKeys N).card = (Set.range (MulChar.galoisOrbit (M := ZMod N) (R := ℂ))).ncard := by
  -- The orbit is a function of the sort key, injective on the keys that occur.
  have hfac : Function.FactorsThrough (MulChar.galoisOrbit (M := ZMod N) (R := ℂ))
      galoisOrbitKey := fun χ ψ h ↦
    MulChar.galoisOrbit_eq_galoisOrbit_iff.mpr (galoisOrbitKey_eq_galoisOrbitKey_iff.mp h)
  set e := Function.extend galoisOrbitKey MulChar.galoisOrbit (fun _ ↦ ∅)
  have he (χ : DirichletCharacter ℂ N) : e χ.galoisOrbitKey = χ.galoisOrbit := hfac.extend_apply _ χ
  have hrange : Set.range (MulChar.galoisOrbit (M := ZMod N) (R := ℂ)) =
      e '' Set.range galoisOrbitKey := by
    rw [← Set.range_comp]
    exact congrArg Set.range (funext fun χ ↦ (he χ).symm)
  rw [hrange, Set.InjOn.ncard_image, galoisOrbitKeys,
    ← Set.ncard_eq_toFinset_card _ (Set.finite_range _)]
  rintro _ ⟨χ, rfl⟩ _ ⟨ψ, rfl⟩ h
  rw [he, he, MulChar.galoisOrbit_eq_galoisOrbit_iff] at h
  exact galoisOrbitKey_eq_galoisOrbitKey_iff.mpr h

/-- **The indices are `0, 1, …, n - 1`**, where `n` is the number of Galois orbits of Dirichlet
characters modulo `N`. -/
theorem range_galoisOrbitIndex :
    Set.range (galoisOrbitIndex (N := N)) =
      Set.Iio (Set.range (MulChar.galoisOrbit (M := ZMod N) (R := ℂ))).ncard := by
  rw [← card_galoisOrbitKeys]
  ext n
  refine ⟨fun ⟨χ, hχ⟩ ↦ hχ ▸ Fin.isLt _, fun hn ↦ ?_⟩
  obtain ⟨χ, hχ⟩ := (Set.Finite.mem_toFinset _).mp (galoisOrbitKeysIso N ⟨n, hn⟩).2
  refine ⟨χ, ?_⟩
  rw [galoisOrbitIndex, show (⟨χ.galoisOrbitKey, galoisOrbitKey_mem_galoisOrbitKeys χ⟩ :
    galoisOrbitKeys N) = galoisOrbitKeysIso N ⟨n, hn⟩ from Subtype.ext hχ,
    OrderIso.symm_apply_apply]

/-- **The trivial character has index `0`**: its Galois orbit is labelled `a`. -/
@[simp]
theorem galoisOrbitIndex_one : (1 : DirichletCharacter ℂ N).galoisOrbitIndex = 0 := by
  have h1 : (1 : DirichletCharacter ℂ N).galoisOrbitIndex ∈ Set.range galoisOrbitIndex :=
    Set.mem_range_self 1
  obtain ⟨ψ, hψ⟩ : 0 ∈ Set.range (galoisOrbitIndex (N := N)) := by
    rw [range_galoisOrbitIndex] at h1 ⊢
    exact Nat.zero_lt_of_lt h1
  by_contra hne
  exact (galoisOrbitKey_one_le ψ).not_gt
    (galoisOrbitIndex_lt_galoisOrbitIndex_iff.mp (hψ ▸ Nat.pos_of_ne_zero hne))

/-- The Galois orbit labelled `a` contains only the trivial character. -/
theorem galoisOrbitIndex_eq_zero_iff {χ : DirichletCharacter ℂ N} :
    χ.galoisOrbitIndex = 0 ↔ χ = 1 := by
  rw [← galoisOrbitIndex_one (N := N), galoisOrbitIndex_eq_galoisOrbitIndex_iff]
  refine ⟨fun h ↦ orderOf_eq_one_iff.mp ?_, fun h ↦ h ▸ MulChar.mem_galoisOrbit_self 1⟩
  rw [MulChar.orderOf_eq_of_mem_galoisOrbit h, orderOf_one]

end DirichletCharacter
