/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.VectorBundle.Section.VanishingIdeal
public import TauCeti.RingTheory.Derivation.DifferentialOperator

/-!
# Differential operators between sections of vector bundles

Let `V` and `W` be real vector bundles over a finite-dimensional Hausdorff smooth manifold `M`.
The smooth sections `Γ(V)` and `Γ(W)` are modules over `C^∞(M)`, so Grothendieck's algebraic
notion of a differential operator of order `r` (`TauCeti.differentialOperators`) applies to real
linear maps `P : Γ(V) → Γ(W)`. This file reads that notion pointwise through the ideals `I_x` of
smooth functions vanishing at `x`.

A differential operator of order `r` sends `I_x ^ (r + 1) Γ(V)` into `I_x Γ(W)`. A section that
vanishes near `x` lies in every `I_x ^ (r + 1) Γ(V)`, and a section in `I_x Γ(W)` vanishes at `x`,
so differential operators are local. For a finite-rank smooth bundle `W` the sections vanishing at
`x` are exactly `I_x Γ(W)`, and the algebraic criterion
`TauCeti.mem_differentialOperators_iff_forall_apply_mem_smul_top` shows that `P` has order `r`
exactly when `(P s) x = 0` for every `x` and every `s ∈ I_x ^ (r + 1) Γ(V)`. Neither fact needs
compactness, any assumption on `V`, or any assumption on the boundary of `M`.

Peetre's theorem (`TauCeti.Geometry.Manifold.DifferentialOperator.Peetre.Section`) supplies the
converse to locality: on a compact manifold every local operator has finite order.

## Main results

* `TauCeti.differentialOperators_section_apply_eq_zero_of_eventuallyEq`: differential operators
  between sections are local.
* `TauCeti.mem_differentialOperators_section_iff_forall_apply_eq_zero`: a linear map between
  sections has order `r` exactly when it kills `I_x ^ (r + 1) Γ(V)` at every point `x`.

## References

* A. Grothendieck, *Éléments de géométrie algébrique IV*, Quatrième partie, §16.8.
-/

public section

open Bundle Filter
open scoped ContDiff Manifold Topology

noncomputable section

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {V : M → Type*} [TopologicalSpace (TotalSpace F V)]
  [∀ x, AddCommGroup (V x)] [∀ x, Module ℝ (V x)] [∀ x, TopologicalSpace (V x)]
  [FiberBundle F V] [VectorBundle ℝ F V]
  {F' : Type*} [NormedAddCommGroup F'] [NormedSpace ℝ F']
  {W : M → Type*} [TopologicalSpace (TotalSpace F' W)]
  [∀ x, AddCommGroup (W x)] [∀ x, Module ℝ (W x)] [∀ x, TopologicalSpace (W x)]
  [FiberBundle F' W] [VectorBundle ℝ F' W]

/-- **Differential operators between sections are local.** If `P : Γ(V) → Γ(W)` is a differential
operator of order `r` in Grothendieck's sense and `s` vanishes near `x`, then `(P s) x = 0`. -/
theorem differentialOperators_section_apply_eq_zero_of_eventuallyEq
    {P : Cₛ^∞⟮I; F, V⟯ →ₗ[ℝ] Cₛ^∞⟮I; F', W⟯} {r : ℕ}
    (hP : P ∈ differentialOperators ℝ C^∞⟮I, M; ℝ⟯ Cₛ^∞⟮I; F, V⟯ Cₛ^∞⟮I; F', W⟯ r)
    {s : Cₛ^∞⟮I; F, V⟯} {x : M} (hs : ∀ᶠ y in 𝓝 x, s y = 0) : P s x = 0 :=
  apply_eq_zero_of_mem_smoothVanishingIdeal_smul_top (apply_mem_smul_top_of_mem_pow_smul_top hP _
    (mem_smoothVanishingIdeal_pow_smul_top_of_eventuallyEq_zero hs (r + 1)))

/-- **Differential operators between sections, pointwise.** For a smooth real vector bundle `W` of
finite rank, a linear map `P : Γ(V) → Γ(W)` is a differential operator of order `r` in
Grothendieck's sense if and only if `(P s) x = 0` for every point `x` and every
`s ∈ I_x ^ (r + 1) Γ(V)`. -/
theorem mem_differentialOperators_section_iff_forall_apply_eq_zero
    [FiniteDimensional ℝ F'] [ContMDiffVectorBundle ∞ F' W I]
    {P : Cₛ^∞⟮I; F, V⟯ →ₗ[ℝ] Cₛ^∞⟮I; F', W⟯} {r : ℕ} :
    P ∈ differentialOperators ℝ C^∞⟮I, M; ℝ⟯ Cₛ^∞⟮I; F, V⟯ Cₛ^∞⟮I; F', W⟯ r ↔
      ∀ x, ∀ s ∈ smoothVanishingIdeal I x ^ (r + 1) •
        (⊤ : Submodule C^∞⟮I, M; ℝ⟯ Cₛ^∞⟮I; F, V⟯), P s x = 0 := by
  rw [mem_differentialOperators_iff_forall_apply_mem_smul_top
    (fun x : M ↦ (ContMDiffMap.evalAlgHom x : C^∞⟮I, M; ℝ⟯ →ₐ[ℝ] ℝ))
    ContMDiffSection.eq_zero_of_forall_mem_ker_evalAlgHom_smul_top]
  simp only [ker_evalAlgHom_eq_smoothVanishingIdeal, mem_smoothVanishingIdeal_smul_top_iff]

end TauCeti
