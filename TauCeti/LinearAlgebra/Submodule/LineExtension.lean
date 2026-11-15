/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Dual.Lemmas
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-!
# Extending a subspace by a line

For a subspace `W` of a vector space `F` over a field `𝕜`, a `Submodule.LineExtension W` is a
subspace `W' = W ⊕ 𝕜v` of one more dimension, together with a functional `φ` on `W'` whose kernel
is `W` and a vector `v ∈ W'` with `φ v = 1`. Every proper subspace of a finite-dimensional space
admits one (`Submodule.nonempty_lineExtension`); `Submodule.lineExtension` is a chosen one.

Over a linearly ordered field, for any extension `ψ` of `φ` to `F` (`LinearMap.exists_extend`),
the complements of the two closed half-subspaces `{x ∈ W' | ψ x ≤ 0}` and `{x ∈ W' | 0 ≤ ψ x}`,
which do not depend on the choice of `ψ`, cover the complement of `W`
(`Submodule.LineExtension.compl_union_compl`) and intersect in the complement of `W'`
(`Submodule.LineExtension.compl_inter_compl`). Each of them is star-convex, about `v` and `-v`
respectively (`TauCeti.starConvex_compl_setOf_mem_and_nonpos`), which is what lets a
Mayer–Vietoris argument remove one dimension of `W'` at a time in relative homology computations
modulo the complement of a subspace.
-/

public section

open Module

namespace Submodule

variable {𝕜 F : Type*} [Field 𝕜] [AddCommGroup F] [Module 𝕜 F]

/-- An extension of a subspace `W` by a line: a subspace `W'` containing `W` with one more
dimension, together with a functional `φ` on `W'` whose kernel is `W` and a vector `v ∈ W'` with
`φ v = 1`. -/
structure LineExtension (W : Submodule 𝕜 F) where
  /-- The larger subspace. -/
  W' : Submodule 𝕜 F
  /-- The functional on `W'` cutting out `W`. -/
  φ : W' →ₗ[𝕜] 𝕜
  /-- The vector of `W'` on which `φ` is one. -/
  v : W'
  apply_v : φ v = 1
  le : W ≤ W'
  apply_eq_zero_iff (x : W') : φ x = 0 ↔ (x : F) ∈ W
  finrank_eq : finrank 𝕜 W' = finrank 𝕜 W + 1

/-- Every proper subspace of a finite-dimensional space admits an extension by a line. -/
lemma nonempty_lineExtension [FiniteDimensional 𝕜 F] {W : Submodule 𝕜 F} (hW : W ≠ ⊤) :
    Nonempty (LineExtension W) := by
  obtain ⟨v, hv⟩ : ∃ v, v ∉ W := by
    by_contra! h
    exact hW (eq_top_iff.2 fun x _ ↦ h x)
  obtain ⟨f, hfv, hfW⟩ := W.exists_dual_map_eq_bot_of_notMem hv inferInstance
  replace hfW : ∀ x ∈ W, f x = 0 := fun x hx ↦
    (Submodule.mem_bot 𝕜).1 (hfW ▸ Submodule.mem_map_of_mem hx)
  have hvW' : v ∈ W ⊔ 𝕜 ∙ v := Submodule.mem_sup_right (Submodule.mem_span_singleton_self v)
  refine ⟨⟨W ⊔ 𝕜 ∙ v, ((f v)⁻¹ • f).comp (W ⊔ 𝕜 ∙ v).subtype, ⟨v, hvW'⟩, ?_, le_sup_left,
    fun x ↦ ⟨fun hφx ↦ ?_, fun hx ↦ ?_⟩, ?_⟩⟩
  · simp [inv_mul_cancel₀ hfv]
  · obtain ⟨y, hy, z, hz, hyz⟩ := Submodule.mem_sup.1 x.2
    obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.1 hz
    have ha : a = 0 := by simpa [← hyz, hfW y hy, hfv] using hφx
    simpa [← hyz, ha] using hy
  · simp [hfW _ hx]
  · exact Submodule.finrank_sup_span_singleton hv

/-- A chosen extension of a proper subspace by a line. -/
noncomputable def lineExtension [FiniteDimensional 𝕜 F] (W : Submodule 𝕜 F) (hW : W ≠ ⊤) :
    LineExtension W :=
  (nonempty_lineExtension hW).some

namespace LineExtension

variable [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜] {W : Submodule 𝕜 F} (s : LineExtension W)
  {ψ : F →ₗ[𝕜] 𝕜}

/-- For an extension `ψ` of `φ` to `F`, the complements of the two closed half-subspaces
`{x ∈ W' | ±ψ x ≤ 0}` of an extension by a line cover the complement of `W`. -/
lemma compl_union_compl (hψ : ψ ∘ₗ s.W'.subtype = s.φ) :
    {x | x ∈ s.W' ∧ ψ x ≤ 0}ᶜ ∪ {x | x ∈ s.W' ∧ (-ψ) x ≤ 0}ᶜ = (W : Set F)ᶜ := by
  have key (x : F) (hx : x ∈ s.W') : ψ x = s.φ ⟨x, hx⟩ := LinearMap.congr_fun hψ ⟨x, hx⟩
  ext x
  simp only [Set.mem_union, Set.mem_compl_iff, Set.mem_ofPred_eq, LinearMap.neg_apply, neg_nonpos,
    SetLike.mem_coe]
  constructor
  · rintro (h | h) hx <;>
      exact h ⟨s.le hx, by simp [key x (s.le hx), (s.apply_eq_zero_iff ⟨x, s.le hx⟩).2 hx]⟩
  · intro hx
    by_contra! h
    exact hx ((s.apply_eq_zero_iff ⟨x, h.1.1⟩).1
      (key x h.1.1 ▸ le_antisymm h.1.2 h.2.2))

/-- For any functional `ψ` on `F`, in particular an extension of `φ`, the complements of the two
closed half-subspaces `{x ∈ W' | ±ψ x ≤ 0}` of an extension by a line intersect in the complement
of `W'`. -/
lemma compl_inter_compl :
    {x | x ∈ s.W' ∧ ψ x ≤ 0}ᶜ ∩ {x | x ∈ s.W' ∧ (-ψ) x ≤ 0}ᶜ = (s.W' : Set F)ᶜ := by
  ext x
  simp only [Set.mem_inter_iff, Set.mem_compl_iff, Set.mem_ofPred_eq, LinearMap.neg_apply,
    neg_nonpos, SetLike.mem_coe]
  constructor
  · rintro ⟨h₁, h₂⟩ hx
    rcases le_total (ψ x) 0 with h | h
    exacts [h₁ ⟨hx, h⟩, h₂ ⟨hx, h⟩]
  · intro hx
    exact ⟨fun h ↦ hx h.1, fun h ↦ hx h.1⟩

end LineExtension

end Submodule
