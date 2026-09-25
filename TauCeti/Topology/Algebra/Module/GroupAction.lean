/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Algebra.MulAction
public import Mathlib.Topology.Algebra.OpenSubgroup
public import TauCeti.Algebra.Module.Submodule.GroupAction
public import TauCeti.Topology.Algebra.Module.Compact

/-!
# Continuous actions on a topological module

Let a monoid `Γ` act continuously and `R`-linearly on a topological `R`-module `M`.
Two compactness arguments, both instances of the tube lemma, control the interaction of the
action with the open submodules of `M`.

* When `Γ` is compact, the invariant core `V.invariantCore Γ` of an open submodule `V` is open:
  the set of pairs `(γ, x)` with `γ • x ∈ V` is an open neighbourhood of `Γ × {0}`, so it contains
  a tube `Γ × W`, and `W` lies in the core. Hence the `Γ`-invariant open submodules are cofinal
  among the open submodules; in a linearly topologized module they form a basis of neighbourhoods
  of zero, so continuity into `M` and equality in a Hausdorff `M` can both be tested modulo the
  invariant open submodules.
* When `Γ` is a group and `M` is compact, the action on the quotient `M ⧸ V` by an invariant open
  submodule `V` has open kernel: the set of pairs `(γ, x)` with `γ • x - x ∈ V` is an open
  neighbourhood of `{1} × M`, so it contains a tube `U × M`, and `U` lies in the kernel. The kernel
  is recorded as the open normal subgroup `Submodule.quotientActionKernel hV hVo`.

These are the two facts that turn a compact module with a continuous action of a profinite
group `Γ` into a module over the completed group algebra of `Γ`: the action on each finite
quotient `M ⧸ V` factors through a finite quotient of `Γ`, and the quotients `M ⧸ V` by the
invariant open `V` determine `M`.

## Main definitions

* `Submodule.quotientActionKernel`: the kernel of the action of `Γ` on the quotient by an
  invariant open submodule of a compact module, as an open normal subgroup of `Γ`.

## Main results

* `Submodule.isOpen_invariantCore`: for compact `Γ`, the invariant core of an open submodule
  is open.
* `Submodule.isOpen_ker_quotientToModuleEnd`: for compact `M`, the action on the quotient by an
  invariant open submodule has open kernel.
* `TauCeti.IsLinearTopology.continuous_iff_forall_invariant_continuous_mkQ`,
  `TauCeti.IsLinearTopology.eq_of_forall_invariant_mkQ_eq`: for compact `Γ`, continuity into a
  linearly topologized `M`, and equality in a `T1` one, can be tested modulo the `Γ`-invariant
  open submodules.
-/

public section

open Topology

namespace Submodule

section Monoid

variable {Γ R M : Type*} [Monoid Γ] [TopologicalSpace Γ] [Ring R] [AddCommGroup M] [Module R M]
  [TopologicalSpace M] [DistribMulAction Γ M] [SMulCommClass Γ R M] [ContinuousSMul Γ M]

variable (Γ) in
/-- **Invariant cores of open submodules are open** when the acting monoid is compact: by the
tube lemma, a neighbourhood of `0` is carried into `V` by the whole of `Γ`. -/
theorem isOpen_invariantCore [CompactSpace Γ] [ContinuousAdd M] (V : Submodule R M)
    (hV : IsOpen (V : Set M)) : IsOpen (V.invariantCore Γ : Set M) := by
  have hS : IsOpen {q : Γ × M | q.1 • q.2 ∈ V} := hV.preimage continuous_smul
  obtain ⟨u, w, -, hw, hu, h0w, huw⟩ := generalized_tube_lemma isCompact_univ
    (isCompact_singleton : IsCompact ({0} : Set M)) hS fun q hq ↦ by
      rw [Set.mem_prod, Set.mem_singleton_iff] at hq
      simp [hq.2]
  refine (V.invariantCore Γ).toAddSubgroup.isOpen_of_mem_nhds (g := 0)
    (Filter.mem_of_superset (hw.mem_nhds (h0w rfl)) fun x hx ↦ ?_)
  simpa [mem_invariantCore] using fun γ ↦ huw (Set.mk_mem_prod (hu (Set.mem_univ γ)) hx)

end Monoid

section Group

variable {Γ R M : Type*} [Group Γ] [TopologicalSpace Γ] [Ring R] [AddCommGroup M] [Module R M]
  [TopologicalSpace M] [DistribMulAction Γ M] [SMulCommClass Γ R M] [ContinuousSMul Γ M]
  [SeparatelyContinuousMul Γ] [CompactSpace M] [IsTopologicalAddGroup M] {V : Submodule R M}

/-- **The action on an open quotient has open kernel** when the module is compact: by the tube
lemma, a neighbourhood of `1` moves every element of `M` by an element of `V`. -/
theorem isOpen_ker_quotientToModuleEnd (hV : ∀ γ : Γ, ∀ x ∈ V, γ • x ∈ V)
    (hVo : IsOpen (V : Set M)) : IsOpen ((quotientToModuleEnd hV).ker : Set Γ) := by
  have hS : IsOpen {q : Γ × M | q.1 • q.2 - q.2 ∈ V} :=
    hVo.preimage (continuous_smul.sub continuous_snd)
  obtain ⟨u, w, hu, -, h1u, hw, huw⟩ := generalized_tube_lemma
    (isCompact_singleton : IsCompact ({1} : Set Γ)) isCompact_univ hS fun q hq ↦ by
      rw [Set.mem_prod, Set.mem_singleton_iff] at hq
      simp [hq.1]
  refine (quotientToModuleEnd hV).ker.isOpen_of_mem_nhds (g := 1)
    (Filter.mem_of_superset (hu.mem_nhds (h1u rfl)) fun γ hγ ↦ ?_)
  rw [SetLike.mem_coe, MonoidHom.mem_ker, ← MonoidHom.mem_mker, mem_mker_quotientToModuleEnd]
  exact fun x ↦ huw (Set.mk_mem_prod hγ (hw (Set.mem_univ x)))

/-- The kernel of the action of `Γ` on the quotient of a compact module by an invariant open
submodule, as an open normal subgroup of `Γ`. -/
def quotientActionKernel (hV : ∀ γ : Γ, ∀ x ∈ V, γ • x ∈ V) (hVo : IsOpen (V : Set M)) :
    OpenNormalSubgroup Γ where
  toSubgroup := (quotientToModuleEnd hV).ker
  isOpen' := isOpen_ker_quotientToModuleEnd hV hVo

@[simp]
theorem quotientActionKernel_toSubgroup (hV : ∀ γ : Γ, ∀ x ∈ V, γ • x ∈ V)
    (hVo : IsOpen (V : Set M)) :
    (quotientActionKernel hV hVo).toSubgroup = (quotientToModuleEnd hV).ker :=
  (rfl)

end Group

end Submodule

namespace TauCeti

variable {Γ R M : Type*} [Monoid Γ] [TopologicalSpace Γ] [CompactSpace Γ] [Ring R]
  [AddCommGroup M] [Module R M] [TopologicalSpace M] [DistribMulAction Γ M] [SMulCommClass Γ R M]
  [ContinuousSMul Γ M] [IsLinearTopology R M]

variable (Γ R) in
/-- **Continuity modulo the invariant open submodules.** For a compact monoid acting continuously
on a linearly topologized topological module `M`, a map into `M` is continuous exactly when it is
continuous modulo every `Γ`-invariant open submodule. -/
theorem IsLinearTopology.continuous_iff_forall_invariant_continuous_mkQ [IsTopologicalAddGroup M]
    {X : Type*} [TopologicalSpace X] {f : X → M} :
    Continuous f ↔ ∀ V : Submodule R M, IsOpen (V : Set M) → (∀ γ : Γ, ∀ x ∈ V, γ • x ∈ V) →
      Continuous (V.mkQ ∘ f) := by
  refine ⟨fun hf V _ _ ↦ V.continuous_mkQ.comp hf, fun h ↦
    (IsLinearTopology.continuous_iff_forall_continuous_mkQ R).2 fun N hN ↦ ?_⟩
  have := Submodule.Quotient.discreteTopology_of_isOpen _ (N.isOpen_invariantCore Γ hN)
  have hf : N.mkQ ∘ f = Submodule.factor (N.invariantCore_le Γ) ∘ ((N.invariantCore Γ).mkQ ∘ f) :=
    funext fun x ↦ (Submodule.factor_mk _ _).symm
  rw [hf]
  exact continuous_of_discreteTopology.comp
    (h _ (N.isOpen_invariantCore Γ hN) fun γ _ hx ↦ Submodule.smul_mem_invariantCore γ hx)

variable (Γ) in
/-- **Separation by the invariant open submodules.** For a compact monoid acting continuously on
a `T1` linearly topologized topological module, two elements that agree modulo every
`Γ`-invariant open submodule are equal. -/
theorem IsLinearTopology.eq_of_forall_invariant_mkQ_eq [ContinuousAdd M] [T1Space M] {m m' : M}
    (h : ∀ V : Submodule R M, IsOpen (V : Set M) → (∀ γ : Γ, ∀ x ∈ V, γ • x ∈ V) →
      V.mkQ m = V.mkQ m') : m = m' := by
  rw [← sub_eq_zero]
  refine IsLinearTopology.eq_zero_of_forall_mem_of_isOpen (R := R) fun N hN ↦
    N.invariantCore_le Γ ?_
  rw [← Submodule.Quotient.mk_eq_zero, ← Submodule.mkQ_apply, map_sub,
    h _ (N.isOpen_invariantCore Γ hN) (fun γ _ hx ↦ Submodule.smul_mem_invariantCore γ hx),
    sub_self]

end TauCeti
