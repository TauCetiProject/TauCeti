/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

import TauCeti.RingTheory.UniversallyJapanese

/-!
# Examples of universally Japanese rings

Fields are universally Japanese, and so are their algebras of finite type, which are therefore
Nagata: for instance polynomial rings in finitely many variables over a field and their quotients.
The ring of all `ZMod 2`-valued sequences is universally Japanese, every element being idempotent,
but it is not Noetherian, so it is not Nagata: the Noetherian hypothesis of
`IsUniversallyJapanese.isNagata` cannot be dropped.
-/

open TauCeti.Ring

-- Fields are universally Japanese.
example (k : Type*) [Field k] : IsUniversallyJapanese k := inferInstance

-- A domain of finite type over a field is Japanese, inseparable extensions included.
example (k : Type*) [Field k] (n : ℕ) (p : Ideal (MvPolynomial (Fin n) k)) [p.IsPrime] :
    IsJapanese (MvPolynomial (Fin n) k ⧸ p) :=
  IsUniversallyJapanese.isJapanese k _

-- Algebras of finite type over a field, such as quotients of polynomial rings, are Nagata.
example (k : Type*) [Field k] (n : ℕ) (I : Ideal (MvPolynomial (Fin n) k)) :
    IsNagata (MvPolynomial (Fin n) k ⧸ I) :=
  IsUniversallyJapanese.isNagata_of_finiteType k _

-- Algebras of finite type over a field are universally Japanese.
example (k : Type*) [Field k] : IsUniversallyJapanese (Polynomial k) :=
  .of_finiteType k _

-- The ring of `ZMod 2`-valued sequences is universally Japanese, as all its elements are
-- idempotent.
example : IsUniversallyJapanese (ℕ → ZMod 2) :=
  .of_forall_isIdempotentElem fun f ↦ funext fun i ↦ (by decide : ∀ a : ZMod 2, a * a = a) (f i)

-- The ring of `ZMod 2`-valued sequences is not Noetherian, hence not Nagata: the ideals of
-- sequences vanishing from the `n`-th term on form a strictly increasing chain.
example : ¬ IsNagata (ℕ → ZMod 2) := by
  intro _
  let I (n : ℕ) : Ideal (ℕ → ZMod 2) := Ideal.pi fun i ↦ if n ≤ i then ⊥ else ⊤
  have hI : StrictMono I := strictMono_nat_of_lt_succ fun n ↦ by
    refine lt_of_le_of_ne (fun f hf ↦ (Ideal.mem_pi _ _).mpr fun i ↦ ?_) fun h ↦ ?_
    · have := (Ideal.mem_pi _ _).mp hf i
      split_ifs at this ⊢ with h₁ h₂ <;> first | trivial | omega
    · have hmem : Pi.single n 1 ∈ I (n + 1) := (Ideal.mem_pi _ _).mpr fun i ↦ by
        by_cases hi : n + 1 ≤ i
        · simp [hi, show i ≠ n by omega]
        · simp [hi]
      have := (Ideal.mem_pi _ _).mp (h ▸ hmem) n
      simp at this
  obtain ⟨n, hn⟩ := WellFoundedGT.monotone_chain_condition' ⟨I, hI.monotone⟩
  exact hn (n + 1) n.le_succ (hI n.lt_succ_self)
