/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Logic.Function.DependsOn
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
on `C`, as soon as `(p, x) ↦ F p x` is continuous (`Continuous.of_uncurry_coe`).

A locally constant function takes only finitely many values on a compact set
(`IsLocallyConstant.finite_image_of_isCompact`), extending Mathlib's
`IsLocallyConstant.range_finite` for compact spaces. On a compact product, a locally constant
function depends on only finitely many coordinates (`IsLocallyConstant.exists_finset_dependsOn`).
-/

public section

namespace IsLocallyConstant

variable {X P A : Type*} [TopologicalSpace X] [TopologicalSpace P]

/-- A locally constant function takes finitely many values on a compact set. -/
theorem finite_image_of_isCompact {f : X → A} (hf : IsLocallyConstant f) {K : Set X}
    (hK : IsCompact K) : (f '' K).Finite := by
  have := isCompact_iff_compactSpace.1 hK
  rw [Set.image_eq_range]
  exact (hf.comp_continuous continuous_subtypeVal).range_finite

/-- A locally constant function on a compact product depends on only finitely many coordinates. -/
theorem exists_finset_dependsOn {ι : Type*} {π : ι → Type*} [∀ i, TopologicalSpace (π i)]
    [CompactSpace (Π i, π i)] {f : (Π i, π i) → A} (hf : IsLocallyConstant f) :
    ∃ s : Finset ι, DependsOn f s := by
  classical
  -- Each fibre of `f` is open, so it contains a basic cylinder around each of its points.
  choose I u hu hsub using fun x ↦ isOpen_pi_iff.1 (hf.isOpen_fiber (f x)) x rfl
  -- Finitely many of these cylinders cover the compact product.
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover (fun x ↦ (I x : Set ι).pi (u x))
    (fun x ↦ isOpen_set_pi (I x).finite_toSet fun i hi ↦ (hu x i hi).1)
    fun x _ ↦ Set.mem_iUnion.2 ⟨x, fun i hi ↦ (hu x i hi).2⟩
  refine ⟨t.biUnion I, fun y y' hyy' ↦ ?_⟩
  obtain ⟨x, hx, hy⟩ := Set.mem_iUnion₂.1 (ht (Set.mem_univ y))
  have hy' : y' ∈ (I x : Set ι).pi (u x) := fun i hi ↦
    hyy' i (Finset.mem_biUnion.2 ⟨x, hx, hi⟩) ▸ hy i hi
  exact (hsub x hy).trans (hsub x hy').symm

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

namespace Continuous

variable {X P A C : Type*} [TopologicalSpace X] [TopologicalSpace P] [TopologicalSpace A]
  [DiscreteTopology A] [TopologicalSpace C] [FunLike C X A]

/-- A family `F : P → C` of bundled functions on a compact space `X`, with values in a discrete
space `A`, is continuous for any topology on `C` if `(p, x) ↦ F p x` is continuous on `P × X`.
This is the continuity form of `IsLocallyConstant.of_uncurry_coe`. -/
theorem of_uncurry_coe [CompactSpace X] {F : P → C}
    (hF : Continuous (Function.uncurry fun p x ↦ F p x)) : Continuous F :=
  (IsLocallyConstant.of_uncurry_coe ((IsLocallyConstant.iff_continuous _).2 hF)).continuous

end Continuous
