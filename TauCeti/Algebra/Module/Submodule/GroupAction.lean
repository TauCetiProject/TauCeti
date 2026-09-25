/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Module.LinearMap.End
public import Mathlib.LinearAlgebra.Quotient.Basic

/-!
# Submodules invariant under a monoid action

Let a monoid `Γ` act on an `R`-module `M` by `R`-linear maps, that is by a `DistribMulAction Γ M`
commuting with the scalars. A submodule `V` is **`Γ`-invariant** when `γ • x ∈ V` for every
`γ : Γ` and `x ∈ V`. This file provides two constructions around that condition.

* The **invariant core** `V.invariantCore Γ = ⨅ γ, V.comap (γ • ·)` of a submodule `V`: the set
  of `x` with `γ • x ∈ V` for every `γ`. It is the largest `Γ`-invariant submodule contained in
  `V`, in the same way as `Subgroup.normalCore` is the largest normal subgroup contained in a
  subgroup, and it is monotone in `V`.
* The **induced action on the quotient** by a `Γ`-invariant submodule `V`: each `γ` descends to
  an `R`-linear endomorphism of `M ⧸ V`, and together they form a monoid homomorphism
  `Submodule.quotientToModuleEnd hV : Γ →* Module.End R (M ⧸ V)`, the quotient analogue of
  `DistribMulAction.toModuleEnd`. Its kernel consists of the `γ` with `γ • x - x ∈ V` for all
  `x`, it grows with `V`, and the action is compatible with the factor maps `M ⧸ V → M ⧸ V'`.

For a compact monoid acting continuously on a topological module the invariant cores of the open
submodules are open. If the module is linearly topologized, the invariant open submodules therefore
form a basis of neighbourhoods of zero; that is where the invariant core is used.

## Main definitions

* `Submodule.invariantCore`: the largest `Γ`-invariant submodule contained in a given one.
* `Submodule.quotientToModuleEnd`: the action of `Γ` on the quotient by an invariant submodule.

## Main results

* `Submodule.mem_invariantCore`, `Submodule.invariantCore_le`, `Submodule.smul_mem_invariantCore`,
  `Submodule.le_invariantCore_iff`, `Submodule.invariantCore_mono`,
  `Submodule.invariantCore_eq_self_iff`: the characteristic properties of the invariant core.
* `Submodule.quotientToModuleEnd_mk`, `Submodule.mem_mker_quotientToModuleEnd`,
  `Submodule.mker_quotientToModuleEnd_mono`, `Submodule.factor_quotientToModuleEnd`: the
  induced action on classes, its kernel, and its compatibility with the factor maps.
-/

public section

namespace Submodule

section InvariantCore

variable {Γ R M : Type*} [Monoid Γ] [Semiring R] [AddCommMonoid M] [Module R M]
  [DistribMulAction Γ M] [SMulCommClass Γ R M]

variable (Γ) in
/-- The **invariant core** of a submodule `V` under the action of a monoid `Γ`: the elements `x`
with `γ • x ∈ V` for every `γ : Γ`. It is the largest `Γ`-invariant submodule contained in `V`
(`Submodule.invariantCore_le`, `Submodule.smul_mem_invariantCore`,
`Submodule.le_invariantCore_iff`). -/
def invariantCore (V : Submodule R M) : Submodule R M :=
  ⨅ γ : Γ, V.comap (DistribSMul.toLinearMap R M γ)

/-- An element belongs to the invariant core exactly when its entire orbit lies in `V`. -/
@[simp]
theorem mem_invariantCore {V : Submodule R M} {x : M} :
    x ∈ V.invariantCore Γ ↔ ∀ γ : Γ, γ • x ∈ V := by
  simp [invariantCore, mem_iInf, mem_comap]

variable (Γ) in
/-- The invariant core is contained in the original submodule. -/
theorem invariantCore_le (V : Submodule R M) : V.invariantCore Γ ≤ V := fun x hx => by
  simpa using mem_invariantCore.1 hx 1

/-- The invariant core is preserved by the action of `Γ`. -/
theorem smul_mem_invariantCore {V : Submodule R M} (γ : Γ) {x : M} (hx : x ∈ V.invariantCore Γ) :
    γ • x ∈ V.invariantCore Γ := by
  rw [mem_invariantCore] at hx ⊢
  intro δ
  rw [smul_smul]
  exact hx _

/-- A submodule lies in the invariant core of `V` exactly when every translate lies in `V`. -/
theorem le_invariantCore_iff {V W : Submodule R M} :
    W ≤ V.invariantCore Γ ↔ ∀ γ : Γ, ∀ x ∈ W, γ • x ∈ V :=
  ⟨fun h γ _ hx => mem_invariantCore.1 (h hx) γ,
    fun h _ hx => mem_invariantCore.2 fun γ => h γ _ hx⟩

/-- Taking invariant cores preserves inclusions of submodules. -/
theorem invariantCore_mono : Monotone (invariantCore Γ : Submodule R M → Submodule R M) :=
  fun _ _ h => le_invariantCore_iff.2 fun γ _ hx => h (mem_invariantCore.1 hx γ)

/-- A submodule equals its invariant core exactly when it is preserved by the action. -/
theorem invariantCore_eq_self_iff {V : Submodule R M} :
    V.invariantCore Γ = V ↔ ∀ γ : Γ, ∀ x ∈ V, γ • x ∈ V :=
  ⟨fun h => le_invariantCore_iff.1 h.ge, fun h => le_antisymm (invariantCore_le Γ V)
    (le_invariantCore_iff.2 h)⟩

end InvariantCore

section Quotient

variable {Γ R M : Type*} [Monoid Γ] [Ring R] [AddCommGroup M] [Module R M]
  [DistribMulAction Γ M] [SMulCommClass Γ R M] {V V' : Submodule R M}

/-- The action of `Γ` on the quotient `M ⧸ V` by a `Γ`-invariant submodule `V`, as a monoid
homomorphism into the `R`-linear endomorphisms of the quotient: `γ` sends the class of `x` to the
class of `γ • x` (`Submodule.quotientToModuleEnd_mk`). This is the quotient analogue of
`DistribMulAction.toModuleEnd`. -/
def quotientToModuleEnd (hV : ∀ γ : Γ, ∀ x ∈ V, γ • x ∈ V) : Γ →* Module.End R (M ⧸ V) where
  toFun γ := V.mapQ V (DistribSMul.toLinearMap R M γ) fun x hx => by
    rw [mem_comap, DistribSMul.toLinearMap_apply]
    exact hV γ x hx
  map_one' := linearMap_qext _ (LinearMap.ext fun x => by simp)
  map_mul' γ δ := linearMap_qext _ (LinearMap.ext fun x => by simp [mul_smul])

/-- The induced action sends the class of `x` to the class of `γ • x`. -/
@[simp]
theorem quotientToModuleEnd_mk (hV : ∀ γ : Γ, ∀ x ∈ V, γ • x ∈ V) (γ : Γ) (x : M) :
    quotientToModuleEnd hV γ (Quotient.mk x) = Quotient.mk (γ • x) :=
  (rfl)

/-- An element acts trivially on the quotient exactly when it moves every `x` by an element
of `V`. The kernel is a submonoid, so no inverses in `Γ` are needed. -/
theorem mem_mker_quotientToModuleEnd (hV : ∀ γ : Γ, ∀ x ∈ V, γ • x ∈ V) {γ : Γ} :
    γ ∈ MonoidHom.mker (quotientToModuleEnd hV) ↔ ∀ x : M, γ • x - x ∈ V := by
  simp only [MonoidHom.mem_mker, LinearMap.ext_iff, Module.End.one_apply]
  refine ⟨fun h x => (Quotient.eq V).1 (by simpa using h (Quotient.mk x)), fun h y => ?_⟩
  induction y using Quotient.induction_on with | _ x => ?_
  rw [quotientToModuleEnd_mk]
  exact (Quotient.eq V).2 (h x)

/-- The kernel of the induced action grows with the submodule. -/
theorem mker_quotientToModuleEnd_mono (hV : ∀ γ : Γ, ∀ x ∈ V, γ • x ∈ V)
    (hV' : ∀ γ : Γ, ∀ x ∈ V', γ • x ∈ V') (h : V ≤ V') :
    MonoidHom.mker (quotientToModuleEnd hV) ≤ MonoidHom.mker (quotientToModuleEnd hV') := by
  intro γ hγ
  rw [mem_mker_quotientToModuleEnd] at hγ ⊢
  exact fun x => h (hγ x)

/-- The induced actions on `M ⧸ V` and `M ⧸ V'`, for invariant `V ≤ V'`, are compatible with
the factor map `M ⧸ V → M ⧸ V'`. -/
theorem factor_quotientToModuleEnd (hV : ∀ γ : Γ, ∀ x ∈ V, γ • x ∈ V)
    (hV' : ∀ γ : Γ, ∀ x ∈ V', γ • x ∈ V') (h : V ≤ V') (γ : Γ) (y : M ⧸ V) :
    factor h (quotientToModuleEnd hV γ y) = quotientToModuleEnd hV' γ (factor h y) := by
  induction y using Quotient.induction_on with | _ x => ?_
  simp only [quotientToModuleEnd_mk]
  simp only [← mkQ_apply, factor_mk]
  rw [mkQ_apply, mkQ_apply, quotientToModuleEnd_mk]

end Quotient

end Submodule
