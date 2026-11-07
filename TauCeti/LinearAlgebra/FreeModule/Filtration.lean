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

namespace DirectSum

variable {R M : Type*} [Ring R] [AddCommGroup M] [Module R M] {Q : ℕ → Type*}
  [∀ j, AddCommGroup (Q j)] [∀ j, Module R (Q j)]

/-- The sum of maps `f j : Q j → M` out of the pieces of a direct sum is injective when `f j`
lands in the `(j + 1)`-st step of an increasing filtration of `M` and meets the `j`-th step only
in `0`. -/
theorem toModule_injective_of_filtration (N : ℕ → Submodule R M) (hN : Monotone N)
    (f : ∀ j, Q j →ₗ[R] M) (hmem : ∀ j q, f j q ∈ N (j + 1))
    (hzero : ∀ j q, f j q ∈ N j → q = 0) :
    Function.Injective (DirectSum.toModule R ℕ M f) := by
  classical
  have key (J : ℕ) : ∀ d : ⨁ j, Q j, (∀ j ∈ d.support, j < J) →
      DirectSum.toModule R ℕ M f d ∈ N J ∧ (DirectSum.toModule R ℕ M f d = 0 → d = 0) := by
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
      obtain ⟨hmemJ, hzeroJ⟩ := ih _ hd'
      have hd_eq : d = d.erase J + DFinsupp.single J (d J) := (DFinsupp.erase_add_single J d).symm
      have hψd : DirectSum.toModule R ℕ M f d =
          DirectSum.toModule R ℕ M f (d.erase J) + f J (d J) := by
        have hsingle : DirectSum.toModule R ℕ M f (DFinsupp.single J (d J)) = f J (d J) :=
          DirectSum.toModule_lof R J (d J)
        rw [hd_eq, map_add, hsingle, DFinsupp.erase_add_single]
      refine ⟨hψd ▸ add_mem (hN J.le_succ hmemJ) (hmem J (d J)), fun h ↦ ?_⟩
      have hJ : d J = 0 := by
        refine hzero J (d J) ?_
        have : f J (d J) = -DirectSum.toModule R ℕ M f (d.erase J) :=
          eq_neg_of_add_eq_zero_right (hψd.symm.trans h)
        exact this ▸ neg_mem hmemJ
      have herase : d.erase J = 0 := hzeroJ (by simpa [hJ] using hψd.symm.trans h)
      rw [hd_eq, herase, hJ, zero_add, DFinsupp.single_zero]
  apply LinearMap.ker_eq_bot.mp
  rw [Submodule.eq_bot_iff]
  intro d hd
  refine (key (d.support.sup id + 1) d fun j hj ↦ ?_).2 (LinearMap.mem_ker.mp hd)
  exact Nat.lt_succ_of_le (Finset.le_sup (f := id) hj)

/-- The sum of maps `f j : Q j → M` out of the pieces of a direct sum is surjective when the
filtration `N` of `M` starts at `⊥`, is exhaustive, and every element of `N (J + 1)` is congruent
modulo `N J` to a value of `f J`. -/
theorem toModule_surjective_of_filtration (N : ℕ → Submodule R M) (h0 : N 0 = ⊥)
    (htop : ⨆ j, N j = ⊤) (f : ∀ j, Q j →ₗ[R] M)
    (hsplit : ∀ J, ∀ x ∈ N (J + 1), ∃ q, x - f J q ∈ N J) :
    Function.Surjective (DirectSum.toModule R ℕ M f) := by
  classical
  rw [← LinearMap.range_eq_top, eq_top_iff, ← htop, iSup_le_iff]
  intro J
  induction J with
  | zero => simp [h0]
  | succ J ih =>
    intro x hx
    obtain ⟨q, hq⟩ := hsplit J x hx
    obtain ⟨d, hd⟩ := ih hq
    refine ⟨d + DirectSum.of Q J q, ?_⟩
    have hof : DirectSum.toModule R ℕ M f (DirectSum.of Q J q) = f J q :=
      DirectSum.toModule_lof R J q
    rw [map_add, hd, hof, sub_add_cancel]

end DirectSum

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
  let f (j : ℕ) : Q j →ₗ[R] M := (N (j + 1)).subtype ∘ₗ s j
  have hψinj : Function.Injective (DirectSum.toModule R ℕ M f) :=
    DirectSum.toModule_injective_of_filtration N hN f (fun j q ↦ (s j q).2) fun j q hq ↦ by
      rw [← hs' j q, Submodule.Quotient.mk_eq_zero]
      exact hq
  have hψsurj : Function.Surjective (DirectSum.toModule R ℕ M f) :=
    DirectSum.toModule_surjective_of_filtration N h0 htop f fun J x hx ↦ by
      refine ⟨Submodule.Quotient.mk ⟨x, hx⟩, ?_⟩
      change (⟨x, hx⟩ - s J (Submodule.Quotient.mk ⟨x, hx⟩) : N (J + 1)) ∈
        (N J).submoduleOf (N (J + 1))
      rw [← Submodule.Quotient.mk_eq_zero, Submodule.Quotient.mk_sub, hs', sub_self]
  exact Module.Free.of_equiv (LinearEquiv.ofBijective _ ⟨hψinj, hψsurj⟩)

end Module.Free
