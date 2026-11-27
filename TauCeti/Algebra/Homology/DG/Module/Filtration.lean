/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Module.Submodule.Lattice
import Mathlib.Data.Int.Init
import Mathlib.LinearAlgebra.Span.Defs
import Mathlib.Order.Directed
import Mathlib.Tactic.Abel

/-!
# Comparing filtered complexes on their graded pieces

Let `M` and `N` be `R`-modules with square-zero differentials `dM` and `dN`, and let `f : M → N`
commute with them. We say that the relative cycles of `f` are relative boundaries when every pair
`(u, w)` with `dM u = 0` and `f u = dN w` is of the form `(dM u', f u' + dN w')`: for a degree-zero
map of differential graded modules this is the acyclicity of the mapping cone of `f`, written on
elements, so it says that `f` is a quasi-isomorphism (compare
`TauCeti.DGRightModuleHom.isQuasiIso_iff_forall_exists`). The same statement, with `u` and `u'` in
a submodule `M₁` and `w` and `w'` in a submodule `N₁`, says that `f` is a quasi-isomorphism from
`M₁` to `N₁` when these are subcomplexes with `f(M₁) ⊆ N₁`; and with the equations only required
modulo submodules `M₀ ≤ M₁` and `N₀ ≤ N₁`, that `f` is a quasi-isomorphism from `M₁ / M₀` to
`N₁ / N₀`.

This file proves the **comparison theorem for filtered complexes** in this element form. For one
step (`TauCeti.exists_differential_eq_and_add_eq_of_le`): if the relative cycles of `f` from `M₀`
to `N₀` are relative boundaries there, and so are those from `M₁` to `N₁` modulo `M₀` and `N₀`,
then the relative cycles of `f` from `M₁` to `N₁` are relative boundaries there. This is the five
lemma for the short exact sequences `0 → M₀ → M₁ → M₁ / M₀ → 0` and `0 → N₀ → N₁ → N₁ / N₀ → 0`,
written as a chase on elements so that no quotient complex is formed. Iterating along increasing
filtrations `F` of `M` and `G` of `N` indexed by `ℤ`, starting from a stage `q₀`, gives the same
conclusion at every later stage (`TauCeti.exists_differential_eq_and_add_eq_of_monotone`), and
when both filtrations are exhaustive, for `f` itself
(`TauCeti.exists_differential_eq_and_add_eq_of_iSup_eq_top`): a map of filtered complexes that is
a quasi-isomorphism on the graded pieces, between filtrations that are exhaustive and start with a
stage on which it is a quasi-isomorphism, is a quasi-isomorphism.

No grading is used, and the submodules need not be stable under the differentials, nor need `f`
preserve the filtrations: the hypotheses are statements about elements. This is the form in which
the comparison maps of Brown's twisted tensor products, filtered by the cells of a CW complex on
one side and by the preimages of its skeleta on the other, are shown to be quasi-isomorphisms one
skeleton at a time, as in the Serre spectral sequence.

## Main results

* `TauCeti.exists_differential_eq_and_add_eq_of_le`: one step of the comparison.
* `TauCeti.exists_differential_eq_and_add_eq_of_monotone`: the comparison at every stage of two
  increasing filtrations.
* `TauCeti.exists_differential_eq_and_add_eq_of_iSup_eq_top`: the comparison for exhaustive
  filtrations.

## References

* C. A. Weibel, *An Introduction to Homological Algebra*, Cambridge University Press, 1994,
  Theorem 5.5.11 (the comparison theorem for filtered complexes).
* E. H. Brown, *Twisted tensor products, I*, Ann. of Math. (2) 69 (1959), 223–246.
-/

public section

namespace TauCeti

variable {R M N : Type*} [Ring R] [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
  {dM : M →ₗ[R] M} {dN : N →ₗ[R] N} {f : M →ₗ[R] N}

/-- **One step of the comparison of filtered complexes.** Let `f : M → N` commute with the
square-zero differentials `dM` and `dN`, and let `M₀ ≤ M₁` and `N₀ ≤ N₁` be submodules. Suppose
that every relative cycle of `f` from `M₀` to `N₀` is a relative boundary there, and that every
relative cycle of `f` from `M₁` to `N₁` modulo `M₀` and `N₀` is a relative boundary there. Then
every relative cycle `(u, w)` of `f` from `M₁` to `N₁`, with `dM u = 0` and `f u = dN w`, is a
relative boundary `(dM u', f u' + dN w')` with `u' ∈ M₁` and `w' ∈ N₁`. -/
theorem exists_differential_eq_and_add_eq_of_le (hf : ∀ x, f (dM x) = dN (f x))
    (hdM : ∀ x, dM (dM x) = 0) (hdN : ∀ x, dN (dN x) = 0) {M₀ M₁ : Submodule R M}
    {N₀ N₁ : Submodule R N} (hM : M₀ ≤ M₁) (hN : N₀ ≤ N₁)
    (h₀ : ∀ u ∈ M₀, ∀ w ∈ N₀, dM u = 0 → f u = dN w →
      ∃ u' ∈ M₀, ∃ w' ∈ N₀, dM u' = u ∧ f u' + dN w' = w)
    (h₁ : ∀ u ∈ M₁, ∀ w ∈ N₁, dM u ∈ M₀ → f u - dN w ∈ N₀ →
      ∃ u' ∈ M₁, ∃ w' ∈ N₁, dM u' - u ∈ M₀ ∧ f u' + dN w' - w ∈ N₀)
    {u : M} (hu : u ∈ M₁) {w : N} (hw : w ∈ N₁) (hdu : dM u = 0) (huw : f u = dN w) :
    ∃ u' ∈ M₁, ∃ w' ∈ N₁, dM u' = u ∧ f u' + dN w' = w := by
  -- Modulo the lower stages, `(u, w)` is a relative boundary `(dM u₁, f u₁ + dN w₁)`.
  obtain ⟨u₁, hu₁, w₁, hw₁, ha, hb⟩ := h₁ u hu w hw (by rw [hdu]; exact zero_mem _)
    (by rw [huw, sub_self]; exact zero_mem _)
  -- The errors `(dM u₁ - u, f u₁ + dN w₁ - w)` form a relative cycle of the lower stages.
  obtain ⟨u₀, hu₀, w₀, hw₀, hdu₀, hfu₀⟩ := h₀ _ ha _ hb
    (by rw [map_sub, hdM, hdu, sub_zero])
    (by rw [map_sub, hf, huw, map_sub, map_add, hdN, add_zero, ← map_sub])
  refine ⟨u₁ - u₀, M₁.sub_mem hu₁ (hM hu₀), w₁ - w₀, N₁.sub_mem hw₁ (hN hw₀), ?_, ?_⟩
  · rw [map_sub, hdu₀, sub_sub_cancel]
  · calc f (u₁ - u₀) + dN (w₁ - w₀) = f u₁ + dN w₁ - (f u₀ + dN w₀) := by
          rw [map_sub, map_sub]; abel
      _ = w := by rw [hfu₀]; abel

/-- **The comparison of filtered complexes, stage by stage.** Let `f : M → N` commute with the
square-zero differentials `dM` and `dN`, and let `F` and `G` be increasing filtrations of `M` and
`N` indexed by `ℤ`. Suppose that every relative cycle of `f` from `F q₀` to `G q₀` is a relative
boundary there, and that for every `q ≥ q₀`, every relative cycle of `f` from `F (q + 1)` to
`G (q + 1)` modulo `F q` and `G q` is a relative boundary there. Then for every `q ≥ q₀`, every
relative cycle of `f` from `F q` to `G q` is a relative boundary there. -/
theorem exists_differential_eq_and_add_eq_of_monotone (hf : ∀ x, f (dM x) = dN (f x))
    (hdM : ∀ x, dM (dM x) = 0) (hdN : ∀ x, dN (dN x) = 0) {F : ℤ → Submodule R M}
    {G : ℤ → Submodule R N} (hF : Monotone F) (hG : Monotone G) {q₀ : ℤ}
    (h₀ : ∀ u ∈ F q₀, ∀ w ∈ G q₀, dM u = 0 → f u = dN w →
      ∃ u' ∈ F q₀, ∃ w' ∈ G q₀, dM u' = u ∧ f u' + dN w' = w)
    (hsucc : ∀ q, q₀ ≤ q → ∀ u ∈ F (q + 1), ∀ w ∈ G (q + 1), dM u ∈ F q → f u - dN w ∈ G q →
      ∃ u' ∈ F (q + 1), ∃ w' ∈ G (q + 1), dM u' - u ∈ F q ∧ f u' + dN w' - w ∈ G q)
    {q : ℤ} (hq : q₀ ≤ q) :
    ∀ u ∈ F q, ∀ w ∈ G q, dM u = 0 → f u = dN w →
      ∃ u' ∈ F q, ∃ w' ∈ G q, dM u' = u ∧ f u' + dN w' = w := by
  induction q, hq using Int.leInduction with
  | base => exact h₀
  | succ q hq ih =>
    exact fun u hu w hw hdu huw ↦ exists_differential_eq_and_add_eq_of_le hf hdM hdN
      (hF (Int.le_add_one le_rfl)) (hG (Int.le_add_one le_rfl)) ih (hsucc q hq) hu hw hdu huw

/-- **The comparison theorem for filtered complexes.** Let `f : M → N` commute with the
square-zero differentials `dM` and `dN`, and let `F` and `G` be exhaustive increasing filtrations of
`M` and `N` indexed by `ℤ`. Suppose that every relative cycle of `f` from `F q₀` to `G q₀` is a
relative boundary there, and that for every `q ≥ q₀`, every relative cycle of `f` from `F (q + 1)`
to `G (q + 1)` modulo `F q` and `G q` is a relative boundary there. Then every relative cycle
`(u, w)` of `f`, with `dM u = 0` and `f u = dN w`, is a relative boundary `(dM u', f u' + dN w')`:
when the filtrations are by subcomplexes preserved by `f`, a map that is a quasi-isomorphism on
the stage `q₀` and on the later graded pieces is a quasi-isomorphism. -/
theorem exists_differential_eq_and_add_eq_of_iSup_eq_top (hf : ∀ x, f (dM x) = dN (f x))
    (hdM : ∀ x, dM (dM x) = 0) (hdN : ∀ x, dN (dN x) = 0) {F : ℤ → Submodule R M}
    {G : ℤ → Submodule R N} (hF : Monotone F) (hG : Monotone G) (hFtop : ⨆ q, F q = ⊤)
    (hGtop : ⨆ q, G q = ⊤) {q₀ : ℤ}
    (h₀ : ∀ u ∈ F q₀, ∀ w ∈ G q₀, dM u = 0 → f u = dN w →
      ∃ u' ∈ F q₀, ∃ w' ∈ G q₀, dM u' = u ∧ f u' + dN w' = w)
    (hsucc : ∀ q, q₀ ≤ q → ∀ u ∈ F (q + 1), ∀ w ∈ G (q + 1), dM u ∈ F q → f u - dN w ∈ G q →
      ∃ u' ∈ F (q + 1), ∃ w' ∈ G (q + 1), dM u' - u ∈ F q ∧ f u' + dN w' - w ∈ G q)
    {u : M} {w : N} (hdu : dM u = 0) (huw : f u = dN w) :
    ∃ u' w', dM u' = u ∧ f u' + dN w' = w := by
  -- Both `u` and `w` lie in a common stage of the filtrations, at or above `q₀`.
  obtain ⟨q₁, hq₁⟩ := (Submodule.mem_iSup_of_directed F hF.directed_le).1
    (hFtop ▸ Submodule.mem_top (x := u))
  obtain ⟨q₂, hq₂⟩ := (Submodule.mem_iSup_of_directed G hG.directed_le).1
    (hGtop ▸ Submodule.mem_top (x := w))
  obtain ⟨u', -, w', -, h⟩ := exists_differential_eq_and_add_eq_of_monotone hf hdM hdN hF hG h₀
    hsucc (q := max q₀ (max q₁ q₂)) (le_max_left _ _) u
    (hF ((le_max_left _ _).trans (le_max_right _ _)) hq₁) w
    (hG ((le_max_right _ _).trans (le_max_right _ _)) hq₂) hdu huw
  exact ⟨u', w', h⟩

end TauCeti
