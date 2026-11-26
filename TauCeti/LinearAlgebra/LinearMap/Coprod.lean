/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.LinearIndependent.Lemmas
public import Mathlib.LinearAlgebra.Prod

/-!
# Bijectivity and surjectivity of a coproduct of linear maps

The linear map `f.coprod g : M₁ × M₂ → M`, `(a, b) ↦ f a + g b`, is bijective exactly when `f`
and `g` are injective and their ranges are complementary submodules of `M`. This is the linear
algebra behind recognising an internal direct sum decomposition `M = range f ⊕ range g`, and
behind inverse-function-theorem arguments whose differential has the form `(a, b) ↦ f a + g b`.
For two vectors `a` and `b`, the map `(s, t) ↦ s • a - t • b` out of `R × R` is injective exactly
when `a` and `b` are linearly independent
(`LinearMap.injective_fst_smulRight_sub_snd_smulRight_iff`).

The coproduct is onto when it can be solved slow first through a splitting `y = P y + (y - P y)`
of `M`: if `g` reaches every part `P y`, and `f` read modulo `P` reaches every part `y - P y`,
then first `f` solves the second part and then `g` the remaining first part
(`LinearMap.surjective_coprod_of_forall_exists_eq`).
-/

public section

namespace LinearMap

section Coprod

variable {R M₁ M₂ M : Type*} [Semiring R] [AddCommGroup M₁] [Module R M₁] [AddCommGroup M₂]
  [Module R M₂] [AddCommGroup M] [Module R M]

/-- The map `(a, b) ↦ f a + g b` is bijective exactly when `f` and `g` are injective and the
ranges of `f` and `g` are complementary. -/
theorem bijective_coprod_iff {f : M₁ →ₗ[R] M} {g : M₂ →ₗ[R] M} :
    Function.Bijective (f.coprod g) ↔
      Function.Injective f ∧ Function.Injective g ∧ IsCompl (range f) (range g) := by
  refine ⟨fun h ↦ ⟨fun a b hab ↦ ?_, fun a b hab ↦ ?_, ⟨?_, ?_⟩⟩, fun ⟨hf, hg, hc⟩ ↦ ⟨?_, ?_⟩⟩
  · simpa using congrArg Prod.fst (h.1 (a₁ := (a, 0)) (a₂ := (b, 0)) (by simpa using hab))
  · simpa using congrArg Prod.snd (h.1 (a₁ := (0, a)) (a₂ := (0, b)) (by simpa using hab))
  · -- A common value `f a = g b` gives `f.coprod g (a, -b) = 0`, so `a = 0`.
    rw [Submodule.disjoint_def]
    rintro _ ⟨a, rfl⟩ ⟨b, hb⟩
    have ha : a = 0 := congrArg Prod.fst (h.1 (a₁ := (a, -b)) (a₂ := 0) (by simp [hb]))
    simp [ha]
  · rw [codisjoint_iff, ← range_coprod, range_eq_top]
    exact h.2
  · rw [injective_iff_map_eq_zero]
    rintro ⟨a, b⟩ hab
    have hk : (a, b) ∈ ker (f.coprod g) := hab
    rw [ker_coprod_of_disjoint_range f g hc.disjoint] at hk
    exact Prod.ext ((injective_iff_map_eq_zero f).1 hf a hk.1)
      ((injective_iff_map_eq_zero g).1 hg b hk.2)
  · rw [← range_eq_top, range_coprod, hc.sup_eq_top]

/-- **Slow-first solution of a block equation.** Let `f : M₁ → M` and `g : M₂ → M` be the slow and
fast columns of a block operator, and `P : M → M` a linear map splitting `y = P y + (y - P y)` into
a fast and a slow part. If `g` reaches every fast part `P y`, and `f` read in the slow part reaches
every slow part `y - P y`, then `(a, b) ↦ f a + g b` is onto: first `a` solves the slow equation,
then `b` solves the fast equation for the remaining fast part. -/
theorem surjective_coprod_of_forall_exists_eq {f : M₁ →ₗ[R] M} {g : M₂ →ₗ[R] M}
    (P : M →ₗ[R] M) (hg : ∀ y, ∃ b, g b = P y) (hf : ∀ y, ∃ a, f a - P (f a) = y - P y) :
    Function.Surjective (f.coprod g) := by
  intro y
  obtain ⟨a, ha⟩ := hf y
  obtain ⟨b, hb⟩ := hg (y - f a)
  refine ⟨(a, b), ?_⟩
  rw [coprod_apply, hb, map_sub, ← add_sub_assoc, add_sub_right_comm, ha, sub_add_cancel]

end Coprod

/-- The map `(s, t) ↦ s • a - t • b` out of `R × R` is injective exactly when `a` and `b` are
linearly independent. -/
theorem injective_fst_smulRight_sub_snd_smulRight_iff {R M : Type*} [Ring R] [AddCommGroup M]
    [Module R M] {a b : M} :
    Function.Injective ((fst R R R).smulRight a - (snd R R R).smulRight b) ↔
      LinearIndependent R ![a, b] := by
  refine ⟨fun h ↦ LinearIndependent.pair_iff.2 fun s t hst ↦ ?_, fun hab ↦ ?_⟩
  · have hp := h (a₁ := (s, -t)) (a₂ := 0) (by simpa [sub_eq_add_neg] using hst)
    exact ⟨congrArg Prod.fst hp, neg_eq_zero.1 (congrArg Prod.snd hp)⟩
  · refine (injective_iff_map_eq_zero _).2 fun p hp ↦ ?_
    have h := LinearIndependent.pair_iff.1 hab p.1 (-p.2) (by simpa [sub_eq_add_neg] using hp)
    exact Prod.ext h.1 (neg_eq_zero.1 h.2)

end LinearMap
