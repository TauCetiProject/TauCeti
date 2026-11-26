/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.ModelTheory.Semantics
public import TauCeti.ModelTheory.SequentCalculus.Derivation
public import TauCeti.ModelTheory.SequentCalculus.Valid

/-!
# Soundness of the sequent calculus `LK`

Every rule of the sequent calculus `LK` with equality preserves truth: if a sequent `Γ ⇒ Δ` has a
derivation, then in every structure, on a carrier in any universe, every assignment of the free
variables that makes all of `Γ` true makes some formula of `Δ` true. In particular a derivable
sequent is valid, and a sequent that is not valid has no derivation.

The proof is by induction on the derivation. For the right universal rule, the eigenvariable does
not occur free in the conclusion, so the premise may be applied to the assignment updated at the
eigenvariable; for the replacement rule, an equation is interpreted as equality.

## Main results

* `TauCeti.SequentCalculus.LKDerivation.sound`: soundness, in every structure in any universe.
* `TauCeti.SequentCalculus.LKDerivation.valid`: a derivable sequent is valid.
* `TauCeti.SequentCalculus.isEmpty_lkDerivation_of_not_valid`: a sequent that is not valid has no
  derivation.

## References

* Samuel R. Buss, *An introduction to proof theory*, in *Handbook of Proof Theory*, Elsevier,
  1998, Theorem 2.3.6 (1).
* Jean H. Gallier, *Logic for Computer Science: Foundations of Automatic Theorem Proving*, second
  edition, Dover, 2015, Lemma 5.6.3 (soundness of the calculus with equality).
-/

public section

universe u v w

open FirstOrder Language BoundedFormula

namespace TauCeti.SequentCalculus

variable {L : Language.{u, v}} {Γ Δ : Finset (L.Formula ℕ)}

/-- Soundness of `LK`: if `Γ ⇒ Δ` has a derivation, then in every structure, on a carrier in any
universe, every assignment of the free variables that makes every formula of `Γ` true makes some
formula of `Δ` true. -/
theorem LKDerivation.sound (d : LKDerivation Γ Δ) {M : Type w} [L.Structure M] (v : ℕ → M)
    (hΓ : ∀ φ ∈ Γ, φ.Realize v) : ∃ ψ ∈ Δ, ψ.Realize v := by
  classical
  induction d generalizing v with
  | ax φ _ hφΓ hφΔ => exact ⟨φ, hφΔ, hΓ φ hφΓ⟩
  | botL h => exact (Formula.realize_bot.1 (hΓ _ h)).elim
  | impL φ ψ h _ _ ih₁ ih₂ =>
    obtain ⟨χ, hχ, hχv⟩ := ih₁ v hΓ
    rcases Finset.mem_insert.1 hχ with rfl | hχ
    · exact ih₂ v <| Finset.forall_mem_insert _ _ _ |>.2
        ⟨Formula.realize_imp.1 (hΓ _ h) hχv, hΓ⟩
    · exact ⟨χ, hχ, hχv⟩
  | impR φ ψ h _ ih =>
    by_cases hφ : φ.Realize v
    · obtain ⟨χ, hχ, hχv⟩ := ih v <| Finset.forall_mem_insert _ _ _ |>.2 ⟨hφ, hΓ⟩
      rcases Finset.mem_insert.1 hχ with rfl | hχ
      · exact ⟨_, h, Formula.realize_imp.2 fun _ => hχv⟩
      · exact ⟨χ, hχ, hχv⟩
    · exact ⟨_, h, Formula.realize_imp.2 fun h' => (hφ h').elim⟩
  | allL φ t h _ ih =>
    refine ih v <| Finset.forall_mem_insert _ _ _ |>.2 ⟨?_, hΓ⟩
    exact (realize_inst₁ φ t v).2 (Formula.realize_all.1 (hΓ _ h) _)
  | @allR Γ Δ φ y h hy _ ih =>
    -- The eigenvariable `y` is not free in the conclusion, so updating `v` at `y` changes the
    -- value of no formula of the conclusion.
    have hupd (a : M) {χ : L.Formula ℕ} (hχ : χ ∈ Γ ∪ Δ) :
        χ.Realize (Function.update v y a) ↔ χ.Realize v :=
      realize_update_of_notMem_freeVarFinset (hy χ hχ) v a _
    by_contra hΔ
    refine hΔ ⟨_, h, Formula.realize_all.2 fun a => ?_⟩
    obtain ⟨χ, hχ, hχv⟩ := ih (Function.update v y a) fun χ hχ =>
      (hupd a (Finset.mem_union_left _ hχ)).2 (hΓ χ hχ)
    rcases Finset.mem_insert.1 hχ with rfl | hχ
    · have hyφ : y ∉ φ.freeVarFinset := by
        simpa [freeVarFinset] using hy _ (Finset.mem_union_right _ h)
      rwa [realize_inst₁, Term.realize_var, Function.update_self,
        realize_update_of_notMem_freeVarFinset hyφ] at hχv
    · exact (hΔ ⟨χ, hχ, (hupd a (Finset.mem_union_right _ hχ)).1 hχv⟩).elim
  | ref t _ ih =>
    exact ih v <| Finset.forall_mem_insert _ _ _ |>.2 ⟨Formula.realize_equal.2 rfl, hΓ⟩
  | repl φ _ s t h₁ h₂ _ ih =>
    refine ih v <| Finset.forall_mem_insert _ _ _ |>.2 ⟨?_, hΓ⟩
    rw [realize_inst₁, ← Formula.realize_equal.1 (hΓ _ h₁), ← realize_inst₁]
    exact hΓ _ h₂
  | cut φ _ _ ih₁ ih₂ =>
    by_cases hφ : φ.Realize v
    · exact ih₂ v <| Finset.forall_mem_insert _ _ _ |>.2 ⟨hφ, hΓ⟩
    · obtain ⟨χ, hχ, hχv⟩ := ih₁ v hΓ
      rcases Finset.mem_insert.1 hχ with rfl | hχ
      · exact (hφ hχv).elim
      · exact ⟨χ, hχ, hχv⟩

/-- A derivable sequent is valid. -/
theorem LKDerivation.valid (d : LKDerivation Γ Δ) : Valid Γ Δ :=
  valid_iff.2 fun _ _ v hv => d.sound v hv

/-- A sequent that is not valid has no derivation. -/
theorem isEmpty_lkDerivation_of_not_valid (h : ¬Valid Γ Δ) : IsEmpty (LKDerivation Γ Δ) :=
  ⟨fun d => h d.valid⟩

end TauCeti.SequentCalculus
