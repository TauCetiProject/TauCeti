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

Applied to `K` the whole of a compact space `X`, it shows that a family `f : P → X → A` of
functions on `X` is locally constant as soon as `Function.uncurry f` is
(`IsLocallyConstant.of_uncurry`); `IsLocallyConstant.of_uncurry_coe` is the same statement for a
family of bundled functions, valued in any `FunLike` type. For functions with values in a discrete
space, local constancy is continuity, so such a family `F : P → C` is continuous, for any topology
on `C`, as soon as `(p, x) ↦ F p x` is continuous (`TauCeti.continuous_of_continuous_uncurry`).
-/

public section

namespace IsLocallyConstant

variable {X P A : Type*} [TopologicalSpace X] [TopologicalSpace P]

/-- A locally constant family is locally constant in its parameter, uniformly on a compact set. -/
theorem exists_isOpen_forall_mem_eq {f : X × P → A} (hf : IsLocallyConstant f)
    {K : Set X} (hK : IsCompact K) (p₀ : P) :
    ∃ V : Set P, IsOpen V ∧ p₀ ∈ V ∧ ∀ p ∈ V, ∀ x ∈ K, f (x, p) = f (x, p₀) := by
  have hopen : IsOpen {q : X × P | f q = f (q.1, p₀)} :=
    (hf.prodMk (hf.comp_continuous (continuous_fst.prodMk continuous_const)))
      {a : A × A | a.1 = a.2}
  -- Mathlib's tube lemma applies to this open agreement locus containing `K × {p₀}`.
  obtain ⟨u, v, -, hvopen, hKu, hv, huv⟩ :=
    generalized_tube_lemma hK isCompact_singleton hopen fun q hq ↦ congrArg f (Prod.ext rfl hq.2)
  exact ⟨v, hvopen, hv rfl, fun p hp x hx ↦ huv (Set.mk_mem_prod (hKu hx) hp)⟩

/-- A family `f : P → X → A` of functions on a compact space `X` is locally constant if
`Function.uncurry f` is locally constant on `P × X`. -/
theorem of_uncurry [CompactSpace X] {f : P → X → A} (hf : IsLocallyConstant (Function.uncurry f)) :
    IsLocallyConstant f := by
  refine (IsLocallyConstant.iff_exists_open _).2 fun p₀ ↦ ?_
  obtain ⟨V, hVopen, hp₀, hV⟩ :=
    (hf.comp_continuous continuous_swap).exists_isOpen_forall_mem_eq isCompact_univ p₀
  exact ⟨V, hVopen, hp₀, fun p hp ↦ funext fun x ↦ hV p hp x (Set.mem_univ x)⟩

/-- A family `F : P → C` of bundled functions on a compact space `X`, valued in any `FunLike` type
`C`, is locally constant if `(p, x) ↦ F p x` is locally constant on `P × X`. This is
`IsLocallyConstant.of_uncurry` for the family of coercions `p ↦ ⇑(F p)`. -/
theorem of_uncurry_coe [CompactSpace X] {C : Type*} [FunLike C X A] {F : P → C}
    (hF : IsLocallyConstant (Function.uncurry fun p x ↦ F p x)) : IsLocallyConstant F :=
  desc F DFunLike.coe (of_uncurry hF) DFunLike.coe_injective

end IsLocallyConstant

namespace TauCeti

variable {X P A C : Type*} [TopologicalSpace X] [TopologicalSpace P] [TopologicalSpace A]
  [DiscreteTopology A] [TopologicalSpace C] [FunLike C X A]

/-- A family `F : P → C` of bundled functions on a compact space `X`, with values in a discrete
space `A`, is continuous for any topology on `C` if `(p, x) ↦ F p x` is continuous on `P × X`. -/
theorem continuous_of_continuous_uncurry [CompactSpace X] {F : P → C}
    (hF : Continuous (Function.uncurry fun p x ↦ F p x)) : Continuous F :=
  (IsLocallyConstant.of_uncurry_coe ((IsLocallyConstant.iff_continuous _).2 hF)).continuous

end TauCeti
