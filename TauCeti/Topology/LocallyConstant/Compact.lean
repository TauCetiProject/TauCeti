/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.LocallyConstant.Basic

/-!
# Uniform local constancy on compact sets

A locally constant family `f : X × P → A` is locally constant in its parameter `p : P`,
uniformly over any compact set `K ⊆ X`. The neighbourhood of a parameter can therefore be
chosen independently of the point of `K`. This is the compactness input for uniform local
constancy of translations on compact groups.
-/

public section

namespace IsLocallyConstant

variable {X P A : Type*} [TopologicalSpace X] [TopologicalSpace P]

/-- A locally constant family is locally constant in its parameter, uniformly on a compact set. -/
theorem exists_isOpen_forall_mem_eq {f : X × P → A} (hf : IsLocallyConstant f)
    {K : Set X} (hK : IsCompact K) (p₀ : P) :
    ∃ V : Set P, IsOpen V ∧ p₀ ∈ V ∧ ∀ p ∈ V, ∀ x ∈ K, f (x, p) = f (x, p₀) := by
  have hfixed : IsLocallyConstant fun q : X × P ↦ f (q.1, p₀) :=
    hf.comp_continuous (continuous_fst.prodMk continuous_const)
  have hopen : IsOpen {q : X × P | f q = f (q.1, p₀)} :=
    (hf.prodMk hfixed) {a : A × A | a.1 = a.2}
  -- Mathlib's tube lemma applies to this open agreement locus containing `K × {p₀}`.
  obtain ⟨u, v, -, hvopen, hKu, hv, huv⟩ :=
    generalized_tube_lemma hK (isCompact_singleton (x := p₀)) hopen (by
      rintro ⟨x, p⟩ ⟨_, rfl⟩
      rfl)
  exact ⟨v, hvopen, hv rfl, fun p hp x hx ↦ huv (Set.mk_mem_prod (hKu hx) hp)⟩

end IsLocallyConstant
