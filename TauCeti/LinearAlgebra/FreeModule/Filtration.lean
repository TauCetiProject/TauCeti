/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Module.Projective
public import Mathlib.LinearAlgebra.DirectSum.Basis

/-!
# Free modules with an exhaustive filtration by free subquotients

Let `N 0 ≤ N 1 ≤ ⋯` be an increasing sequence of submodules of `M`, starting at `⊥` and with
supremum `⊤`. If every subquotient `N (j + 1) ⧸ N j` is free, then `M` is free. Splitting each
subquotient off `N (j + 1)` identifies `M` with the direct sum of the subquotients.

No finiteness is assumed: this is the form needed when a module that is not finitely generated
over the base, such as a polynomial ring, is filtered by degree.

## Main declarations

* `Module.Free.of_filtration`: a module with an exhaustive filtration by free subquotients is
  free.
-/

public section

open DirectSum

namespace Module.Free

variable {R M : Type*} [Ring R] [AddCommGroup M] [Module R M]

/-- A module with an exhaustive increasing filtration `⊥ = N 0 ≤ N 1 ≤ ⋯`, all of whose
subquotients `N (j + 1) ⧸ N j` are free, is free. -/
theorem of_filtration (N : ℕ → Submodule R M) (hN : Monotone N) (h0 : N 0 = ⊥)
    (htop : ⨆ j, N j = ⊤)
    (hfree : ∀ j, Module.Free R (N (j + 1) ⧸ (N j).submoduleOf (N (j + 1)))) :
    Module.Free R M := by
  classical
  let Q : ℕ → Type _ := fun j ↦ N (j + 1) ⧸ (N j).submoduleOf (N (j + 1))
  -- `Q` is a local abbreviation, so its additive groups are recorded for the direct sum.
  let _ (j : ℕ) : AddCommGroup (Q j) := Submodule.Quotient.addCommGroup _
  -- Split each subquotient off the next filtration step.
  have hsplit : ∀ j, ∃ s : Q j →ₗ[R] N (j + 1),
      ((N j).submoduleOf (N (j + 1))).mkQ ∘ₗ s = LinearMap.id := fun j ↦
    LinearMap.exists_rightInverse_of_surjective _ (Submodule.range_mkQ _)
  choose s hs using hsplit
  have hs' (j : ℕ) (q : Q j) : Submodule.Quotient.mk (s j q) = q :=
    LinearMap.congr_fun (hs j) q
  let ψ : (⨁ j, Q j) →ₗ[R] M := DirectSum.toModule R ℕ M fun j ↦ (N (j + 1)).subtype ∘ₗ s j
  have hψ (j : ℕ) (q : Q j) : ψ (DFinsupp.single j q) = s j q :=
    DirectSum.toModule_lof R j q
  have hψof (j : ℕ) (q : Q j) : ψ (DirectSum.of Q j q) = s j q :=
    DirectSum.toModule_lof R j q
  -- An element supported below `J` maps into `N J`, and only `0` maps to `0`.
  have key (J : ℕ) : ∀ d : ⨁ j, Q j, (∀ j ∈ d.support, j < J) →
      ψ d ∈ N J ∧ (ψ d = 0 → d = 0) := by
    induction J with
    | zero =>
      intro d hd
      have : d = 0 := DFinsupp.support_eq_empty.mp <|
        Finset.eq_empty_of_forall_notMem fun j hj ↦ Nat.not_lt_zero _ (hd j hj)
      subst this
      simp
    | succ J ih =>
      intro d hd
      have hd' : ∀ j ∈ (d.erase J).support, j < J := by
        intro j hj
        rw [DFinsupp.support_erase, Finset.mem_erase] at hj
        exact lt_of_le_of_ne (Nat.lt_succ_iff.mp (hd j hj.2)) hj.1
      obtain ⟨hmem, hzero⟩ := ih _ hd'
      have hd_eq : d = d.erase J + DFinsupp.single J (d J) := (DFinsupp.erase_add_single J d).symm
      have hψd : ψ d = ψ (d.erase J) + (s J (d J) : M) := by
        rw [hd_eq, map_add, hψ, DFinsupp.erase_add_single]
      refine ⟨hψd ▸ add_mem (hN J.le_succ hmem) (s J (d J)).2, fun h ↦ ?_⟩
      have hJ : d J = 0 := by
        have hmemJ : (s J (d J) : M) ∈ N J := by
          have : (s J (d J) : M) = -ψ (d.erase J) :=
            eq_neg_of_add_eq_zero_right (hψd.symm.trans h)
          exact this ▸ neg_mem hmem
        rw [← hs' J (d J), Submodule.Quotient.mk_eq_zero]
        exact hmemJ
      have herase : d.erase J = 0 := hzero (by simpa [hJ] using hψd.symm.trans h)
      rw [hd_eq, herase, hJ, zero_add, DFinsupp.single_zero]
  have hinj : Function.Injective ψ := by
    apply LinearMap.ker_eq_bot.mp
    rw [Submodule.eq_bot_iff]
    intro d hd
    refine (key (d.support.sup id + 1) d fun j hj ↦ ?_).2 (LinearMap.mem_ker.mp hd)
    exact Nat.lt_succ_of_le (Finset.le_sup (f := id) hj)
  have hsurj : Function.Surjective ψ := by
    rw [← LinearMap.range_eq_top, eq_top_iff, ← htop, iSup_le_iff]
    intro J
    induction J with
    | zero => simp [h0]
    | succ J ih =>
      intro x hx
      let y : N (J + 1) := ⟨x, hx⟩
      have hrest : y - s J (Submodule.Quotient.mk y) ∈ (N J).submoduleOf (N (J + 1)) := by
        rw [← Submodule.Quotient.mk_eq_zero, Submodule.Quotient.mk_sub, hs', sub_self]
      obtain ⟨d, hd⟩ := ih hrest
      refine ⟨d + DirectSum.of Q J (Submodule.Quotient.mk y), ?_⟩
      rw [map_add, hd, hψof, Submodule.subtype_apply, Submodule.coe_sub, sub_add_cancel]
  exact Module.Free.of_equiv (LinearEquiv.ofBijective ψ ⟨hinj, hsurj⟩)

end Module.Free
