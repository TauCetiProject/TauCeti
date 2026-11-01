/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Dimension.Finrank
public import Mathlib.RingTheory.SimpleModule.Isotypic

/-!
# Hom spaces and direct sums of isotypic components

Mathlib shows that the isotypic components of a module are independent
(`sSupIndep_isotypicComponents`) and, for a semisimple module, span it
(`sSup_isotypicComponents`); it reads off the consequence for endomorphisms
(`IsSemisimpleModule.endAlgEquiv`). This file records the consequence for the module itself: a
semisimple module is the internal direct sum of its isotypic components. When there are finitely
many components, for instance when the module is Noetherian, composing with
`DFinsupp.linearEquivFunOnFintype` presents it as their product.

Maps from a simple module `S` into `M` land in its `S`-isotypic component. Restricting the
codomain therefore gives an equivalence of hom spaces, without any semisimplicity or
finiteness assumption on `M`. A map from a simple module into an isotypic module of a different
type is zero (`IsIsotypicOfType.linearMap_eq_zero`). The isotypic components of pairwise
non-isomorphic simple modules are independent (`TauCeti.iSupIndep_isotypicComponent`); this is the
indexed form of Mathlib's `sSupIndep_isotypicComponents`, allowing types that do not occur in the
module.

## Main definitions

* `TauCeti.linearMapIsotypicComponentEquiv`: the hom space from `S` into its isotypic component
  is linearly equivalent to the hom space from `S` into the ambient module.

* `IsSemisimpleModule.linearEquivIsotypicComponents`: a semisimple module is linearly
  equivalent to the direct sum of its isotypic components.

## Main statements

* `TauCeti.finrank_linearMap_isotypicComponent`: restricting the target to its isotypic
  component preserves the `finrank` of the hom space out of the simple module.

* `IsSemisimpleModule.linearEquivIsotypicComponents_apply_coe` and
  `IsSemisimpleModule.linearEquivIsotypicComponents_symm_single`: the equivalence and its
  inverse on a single isotypic component.

* `IsSemisimpleModule.isCompl_isotypicComponent_sSup_sdiff`: an isotypic component is
  complementary to the sum of the other isotypic components.

* `IsSemisimpleModule.exists_forall_smul_eq_ite`: for a semisimple module finite over its
  endomorphism ring, an element of the ring acts as the identity on the simple submodules of a
  given type and as zero on all the others, by Jacobson density.
-/

public section

namespace TauCeti

section Hom

variable {R M S : Type*} [Ring R] [AddCommGroup M] [Module R M]
  [AddCommGroup S] [Module R S]

/-- A module is its own isotypic component: the top submodule is isomorphic to the module. -/
@[simp]
theorem isotypicComponent_self_eq_top : isotypicComponent R S S = ⊤ :=
  eq_top_iff.mpr <| (Submodule.le_isotypicComponent ⊤).trans_eq
    Submodule.topEquiv.isotypicComponent_eq

variable [IsSimpleModule R S]

/-- A map out of a simple module takes its values in the isotypic component of that type. -/
theorem _root_.LinearMap.apply_mem_isotypicComponent (f : S →ₗ[R] M) (s : S) :
    f s ∈ isotypicComponent R M S := by
  have h := LinearMap.le_comap_isotypicComponent (M := S) (N := M) S f
  rw [isotypicComponent_self_eq_top] at h
  exact h Submodule.mem_top

variable (k : Type*) [CommSemiring k] [Algebra k R] [Module k M] [IsScalarTower k R M]

/-- Composition with the inclusion of the `S`-isotypic component is an equivalence of hom
spaces out of the simple module `S`. Its inverse corestricts a map to that component.
The equivalence is linear over the scalar semiring acting on the target. -/
def linearMapIsotypicComponentEquiv :
    (S →ₗ[R] isotypicComponent R M S) ≃ₗ[k] (S →ₗ[R] M) where
  toFun g := (isotypicComponent R M S).subtype ∘ₗ g
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  invFun f := f.codRestrict _ f.apply_mem_isotypicComponent
  left_inv _ := by ext s; rfl
  right_inv _ := by ext s; rfl

/-- The forward equivalence composes a map into the isotypic component with its inclusion
into the ambient module. -/
@[simp]
theorem linearMapIsotypicComponentEquiv_apply
    (f : S →ₗ[R] isotypicComponent R M S) (s : S) :
    linearMapIsotypicComponentEquiv k f s = f s := (rfl)

/-- The inverse equivalence corestricts a map into the ambient module to its isotypic
component, preserving its values. -/
@[simp]
theorem linearMapIsotypicComponentEquiv_symm_apply (f : S →ₗ[R] M) (s : S) :
    (linearMapIsotypicComponentEquiv k).symm f s =
      ⟨f s, f.apply_mem_isotypicComponent s⟩ := (rfl)

variable {k} in
/-- The `finrank` of a hom space out of `S` is unchanged by restricting the target to its
`S`-isotypic component, because every map out of `S` lands there. The scalar semiring acts only
on the target; no field or scalar action on `S` is needed. -/
@[simp]
theorem finrank_linearMap_isotypicComponent :
    Module.finrank k (S →ₗ[R] isotypicComponent R M S) = Module.finrank k (S →ₗ[R] M) :=
  (linearMapIsotypicComponentEquiv k).finrank_eq

end Hom

end TauCeti

namespace IsIsotypicOfType

variable {R M N S : Type*} [Ring R] [AddCommGroup M] [Module R M]
  [AddCommGroup N] [Module R N] [AddCommGroup S] [Module R S]
  [IsSimpleModule R S]

/-- A map from a simple module into an isotypic module of a different type is zero. -/
theorem linearMap_eq_zero (h : IsIsotypicOfType R M N)
    (hne : ¬ Nonempty (S ≃ₗ[R] N)) (f : S →ₗ[R] M) : f = 0 := by
  obtain hinj | hzero := f.injective_or_eq_zero
  · let e := LinearEquiv.ofInjective f hinj
    have : IsSimpleModule R (LinearMap.range f) := .congr e.symm
    exact False.elim (hne ⟨e.trans (h (LinearMap.range f)).some⟩)
  · exact hzero

end IsIsotypicOfType

namespace IsSemisimpleModule

variable (R M : Type*) [Ring R] [AddCommGroup M] [Module R M] [IsSemisimpleModule R M]
  [DecidableEq (isotypicComponents R M)]

/-- **A semisimple module is the direct sum of its isotypic components.** The equivalence sends
an element to its family of components, and its inverse adds the components up. This is the
module-level counterpart of `IsSemisimpleModule.endAlgEquiv`. -/
noncomputable def linearEquivIsotypicComponents : M ≃ₗ[R] Π₀ c : isotypicComponents R M, c.1 :=
  .symm <| ((sSupIndep_iff _).mp <| sSupIndep_isotypicComponents R M).linearEquiv <|
    (sSup_eq_iSup' _).symm.trans <| sSup_isotypicComponents R M

variable {R M}

/-- The inverse of `linearEquivIsotypicComponents` sends the family that is `x` at the isotypic
component `c` and zero elsewhere to `x`, viewed as an element of `M`. -/
@[simp]
theorem linearEquivIsotypicComponents_symm_single (c : isotypicComponents R M) (x : c.1) :
    (linearEquivIsotypicComponents R M).symm (DFinsupp.single c x) = x := by
  simp [linearEquivIsotypicComponents]

/-- `linearEquivIsotypicComponents` sends an element `x` of an isotypic component `c`, viewed as an
element of `M`, to the family that is `x` at `c` and zero elsewhere. -/
@[simp]
theorem linearEquivIsotypicComponents_apply_coe {c : isotypicComponents R M} (x : c.1) :
    linearEquivIsotypicComponents R M x = DFinsupp.single c x := by
  rw [← linearEquivIsotypicComponents_symm_single, LinearEquiv.apply_symm_apply]

-- Not `@[simp]`: the component `c` does not occur in the left-hand side, so `simp` could only
-- find it by solving `x ∈ c.1` for `c`. The simp form is
-- `linearEquivIsotypicComponents_apply_coe`, as with `DirectSum.decompose_coe` and
-- `DirectSum.decompose_of_mem`.
/-- An element `x` of `M` lying in an isotypic component `c` is sent by
`linearEquivIsotypicComponents` to the family that is `x` at `c` and zero elsewhere. -/
theorem linearEquivIsotypicComponents_apply_of_mem {c : isotypicComponents R M} {x : M}
    (hx : x ∈ c.1) : linearEquivIsotypicComponents R M x = DFinsupp.single c ⟨x, hx⟩ :=
  linearEquivIsotypicComponents_apply_coe ⟨x, hx⟩

end IsSemisimpleModule

namespace IsSemisimpleModule

section Projection

variable {R : Type*} [Ring R] {M : Type*} [AddCommGroup M] [Module R M]

/-- **An isotypic component and the other isotypic components are complementary.** In a
semisimple module, the `S`-isotypic component and the sum of all the other isotypic components are
complements. This holds also when `S` does not occur, the component then being zero. -/
theorem isCompl_isotypicComponent_sSup_sdiff [IsSemisimpleModule R M]
    (S : Type*) [AddCommGroup S] [Module R S] [IsSimpleModule R S] :
    IsCompl (isotypicComponent R M S)
      (sSup (isotypicComponents R M \ {isotypicComponent R M S})) := by
  constructor
  · by_cases hc : isotypicComponent R M S ∈ isotypicComponents R M
    · exact sSupIndep_isotypicComponents R M hc
    · -- No submodule is isomorphic to `S`, so the isotypic component is zero.
      have hbot : isotypicComponent R M S = ⊥ := sSup_eq_bot.mpr fun m ⟨e⟩ =>
        absurd ⟨m, IsSimpleModule.congr e, e.isotypicComponent_eq.symm⟩ hc
      rw [hbot]
      exact disjoint_bot_left
  · rw [codisjoint_iff, eq_top_iff, ← sSup_isotypicComponents R M]
    refine sSup_le fun d hd => ?_
    by_cases h : d = isotypicComponent R M S
    · exact h ▸ le_sup_left
    · exact (le_sSup (Set.mem_sdiff_of_mem hd h)).trans le_sup_right

open scoped Classical in
/-- **Isotypic projections are actions of ring elements.** For a semisimple module `M` finite over
its endomorphism ring and a simple module `S`, some `a : R` acts as the identity on every simple
submodule of `M` isomorphic to `S` and as zero on every other simple submodule. Its action on `M`
is the projection onto the `S`-isotypic component along the sum of the other isotypic
components. -/
theorem exists_forall_smul_eq_ite [IsSemisimpleModule R M] [Module.Finite (Module.End R M) M]
    (S : Type*) [AddCommGroup S] [Module R S] [IsSimpleModule R S] :
    ∃ a : R, ∀ T : Submodule R M, IsSimpleModule R T → ∀ x ∈ T,
      a • x = if Nonempty (T ≃ₗ[R] S) then x else 0 := by
  classical
  set c := isotypicComponent R M S
  set c' := sSup (isotypicComponents R M \ {c})
  -- A simple submodule lies in `c` or in `c'`, according to whether it is isomorphic to `S`.
  have hle (T : Submodule R M) (hT : IsSimpleModule R T) :
      (Nonempty (T ≃ₗ[R] S) → T ≤ c) ∧ (¬ Nonempty (T ≃ₗ[R] S) → T ≤ c') := by
    refine ⟨fun h => le_sSup h, fun h => T.le_isotypicComponent.trans (le_sSup ⟨⟨T, hT, rfl⟩, ?_⟩)⟩
    intro hTc
    exact h (isIsotypicOfType_submodule_iff.mp (IsIsotypicOfType.isotypicComponent R M S) T
      (T.le_isotypicComponent.trans (Set.mem_singleton_iff.mp hTc).le))
  have hcompl : IsCompl c c' := isCompl_isotypicComponent_sSup_sdiff S
  -- Both summands are fully invariant, so the projection commutes with every endomorphism.
  have hc : c.IsFullyInvariant := .isotypicComponent R M S
  have hc' : c'.IsFullyInvariant :=
    isFullyInvariant_iff_sSup_isotypicComponents.mpr ⟨_, Set.sdiff_subset, rfl⟩
  let π := c.projection c' hcompl
  have hcomm (f : Module.End R M) (x : M) : π (f x) = f (π x) := by
    have hker : x - π x ∈ c' := by
      rw [← Submodule.projection_apply_eq_zero_iff hcompl, map_sub,
        Submodule.projection_apply_of_mem_left hcompl (Submodule.projection_apply_mem hcompl x),
        sub_self]
    have hx : f x = f (π x) + f (x - π x) := by rw [← map_add, add_sub_cancel]
    rw [hx, map_add, Submodule.projection_apply_of_mem_left hcompl
      (hc f (Submodule.projection_apply_mem hcompl x)),
      Submodule.projection_apply_of_mem_right hcompl (hc' f hker), add_zero]
  let F : Module.End (Module.End R M) M :=
    { toFun := π
      map_add' := π.map_add
      map_smul' := fun f x => hcomm f x }
  obtain ⟨a, ha⟩ := Module.Finite.toModuleEnd_moduleEnd_surjective (R := R) (M := M) F
  refine ⟨a, fun T hT x hx => ?_⟩
  have hax : a • x = π x := congrArg (fun t : Module.End (Module.End R M) M => t x) ha
  rw [hax]
  split_ifs with h
  · exact Submodule.projection_apply_of_mem_left hcompl ((hle T hT).1 h hx)
  · exact Submodule.projection_apply_of_mem_right hcompl ((hle T hT).2 h hx)

end Projection

end IsSemisimpleModule

namespace TauCeti

variable (R M : Type*) [Ring R] [AddCommGroup M] [Module R M]

/-- The isotypic components of a family of pairwise non-isomorphic simple modules are
independent. -/
theorem iSupIndep_isotypicComponent {κ : Type*} (S : κ → Type*) [∀ j, AddCommGroup (S j)]
    [∀ j, Module R (S j)] [∀ j, IsSimpleModule R (S j)]
    (hS : ∀ i j, Nonempty (S i ≃ₗ[R] S j) → i = j) :
    iSupIndep fun j => isotypicComponent R M (S j) := by
  -- Restricted to the nonzero components, the family is an injective reindexing of
  -- `isotypicComponents R M`.
  have hmem (j : κ) (hj : isotypicComponent R M (S j) ≠ ⊥) :
      isotypicComponent R M (S j) ∈ isotypicComponents R M := by
    obtain ⟨N, hN, _⟩ := (IsSemisimpleModule.eq_bot_or_exists_simple_le _).resolve_left hj
    obtain ⟨e⟩ := isIsotypicOfType_submodule_iff.mp
      (IsIsotypicOfType.isotypicComponent R M (S j)) N hN
    exact ⟨N, ‹_›, e.isotypicComponent_eq.symm⟩
  rw [← iSupIndep_ne_bot]
  refine ((sSupIndep_iff _).mp (sSupIndep_isotypicComponents R M)).comp
    (f := fun j : {j // isotypicComponent R M (S j) ≠ ⊥} => ⟨_, hmem j.1 j.2⟩) ?_
  intro ⟨i, hi⟩ ⟨j, _⟩ hij
  -- A simple submodule of the common component is a copy of both `S i` and `S j`.
  obtain ⟨N, hN, _⟩ := (IsSemisimpleModule.eq_bot_or_exists_simple_le _).resolve_left hi
  obtain ⟨e⟩ := isIsotypicOfType_submodule_iff.mp
    (IsIsotypicOfType.isotypicComponent R M (S i)) N hN
  obtain ⟨e'⟩ := isIsotypicOfType_submodule_iff.mp
    (IsIsotypicOfType.isotypicComponent R M (S j)) N (hN.trans (congrArg Subtype.val hij).le)
  exact Subtype.ext (hS i j ⟨e.symm.trans e'⟩)

end TauCeti
