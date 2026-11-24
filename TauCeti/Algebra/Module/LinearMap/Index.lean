/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Module.LinearMap.Index
public import Mathlib.LinearAlgebra.Dimension.Free
public import TauCeti.LinearAlgebra.Quotient.Prod

import TauCeti.LinearAlgebra.Prod

/-!
# Index of linear maps

This file extends Mathlib's algebraic `LinearMap.index` API with its invariance under composing
with a linear equivalence, its additivity under products with finite free kernels and cokernels,
and its behaviour under restriction of scalars along a tower of division rings `K → L`: the index
gets multiplied by `finrank K L`. For instance, the realification of a complex-linear map has
twice its complex index.

It also compares the kernels, cokernels and indices of two linear maps `f : M → N` and
`f' : M' → N'` related by injective maps `i : M' → M` and `j : N' → N` with
`f (i x) = j (f' x)`, when every `x` with `f x` in the image of `j` lies in the image of `i`
(and, for the cokernels and indices, `range f ⊔ range j = ⊤`)
(`LinearMap.kerEquivOfRegularity`, `LinearMap.cokerEquivOfRegularity`,
`LinearMap.index_eq_of_regularity`). This is the algebra behind the independence of the kernel,
cokernel and index of an elliptic operator `H^(s+m) → H^s` from the Sobolev order `s`, where `f'`
is the same operator `H^(t+m) → H^t` at a higher order `t` and the hypothesis is elliptic
regularity.

These lemmas are absent from `Mathlib.Algebra.Module.LinearMap.Index` and support the
continuous-linear-map results in `TauCeti.Topology.Algebra.Module.ContinuousLinearMap.Index`.
-/

public section

namespace LinearMap

variable {R M N P : Type*} [Ring R]
variable [AddCommGroup M] [Module R M]
variable [AddCommGroup N] [Module R N]
variable [AddCommGroup P] [Module R P]

/-- Postcomposition with a linear equivalence leaves the index unchanged. -/
@[simp]
lemma index_equiv_comp (f : M →ₗ[R] N) (e : N ≃ₗ[R] P) :
    ((e : N →ₗ[R] P).comp f).index = f.index := by
  rw [index_eq_finrank_sub, index_eq_finrank_sub]
  congr 1
  · rw [ker_comp_of_ker_eq_bot _ (ker_eq_bot.2 e.injective)]
  · rw [range_comp]
    exact_mod_cast (LinearEquiv.finrank_eq
      (Submodule.Quotient.equiv f.range (f.range.map (e : N →ₗ[R] P)) e rfl)).symm

/-- Precomposition with a linear equivalence leaves the index unchanged. -/
@[simp]
lemma index_comp_equiv (f : M →ₗ[R] N) (e : P ≃ₗ[R] M) :
    (f.comp (e : P →ₗ[R] M)).index = f.index := by
  rw [index_eq_finrank_sub, index_eq_finrank_sub]
  congr 1
  · rw [ker_comp, Submodule.comap_equiv_eq_map_symm, LinearEquiv.finrank_map_eq]
  · rw [range_comp_of_range_eq_top _ (range_eq_top.2 e.surjective)]

/-- The index is additive under Cartesian products when the kernels and cokernels are finite
free modules. -/
@[simp]
lemma index_prodMap {Q : Type*} [AddCommGroup Q] [Module R Q] [StrongRankCondition R]
    (f : M →ₗ[R] N) (g : P →ₗ[R] Q)
    [Module.Free R f.ker] [Module.Free R g.ker]
    [Module.Finite R f.ker] [Module.Finite R g.ker]
    [Module.Free R (N ⧸ f.range)] [Module.Free R (Q ⧸ g.range)]
    [Module.Finite R (N ⧸ f.range)] [Module.Finite R (Q ⧸ g.range)] :
    (f.prodMap g).index = f.index + g.index := by
  simp only [index_eq_finrank_sub, finrank_ker_prodMap, finrank_quotient_range_prodMap]
  omega

section Regularity

/-! ### Commutative squares with a regularity property

Let `f : M → N` and `f' : M' → N'` be linear maps intertwined by injective linear maps
`i : M' → M` and `j : N' → N`, so that `f (i x) = j (f' x)`. Think of `f'` as the restriction of
`f` to subspaces of more regular elements. The square has the *regularity property* when every
`x` with `f x` in the image of `j` is itself in the image of `i`. Then `i` identifies the kernels
of `f'` and `f`, and `j` embeds the cokernel of `f'` into that of `f`, onto it as soon as
`range f ⊔ range j = ⊤`. -/

variable {M' N' : Type*} [AddCommGroup M'] [Module R M'] [AddCommGroup N'] [Module R N']
  {f : M →ₗ[R] N} {f' : M' →ₗ[R] N'} {i : M' →ₗ[R] M} {j : N' →ₗ[R] N}

/-- If `f (i x) = j (f' x)` for all `x`, then `i` maps the kernel of `f'` into the kernel of
`f`. -/
theorem ker_le_comap_ker_of_apply_eq (hcomm : ∀ x, f (i x) = j (f' x)) :
    ker f' ≤ (ker f).comap i := fun x hx ↦ by
  simp_all [hcomm x]

/-- If `f (i x) = j (f' x)` for all `x`, then `j` maps the range of `f'` into the range of
`f`. -/
theorem range_le_comap_range_of_apply_eq (hcomm : ∀ x, f (i x) = j (f' x)) :
    range f' ≤ (range f).comap j := by
  rintro _ ⟨x, rfl⟩
  exact ⟨i x, hcomm x⟩

/-- In a commutative square with the regularity property and `j` injective, every element of
the kernel of `f` comes from the kernel of `f'`. -/
theorem map_ker_eq_ker_of_regularity (hcomm : ∀ x, f (i x) = j (f' x))
    (hj : Function.Injective j) (hreg : ∀ x y, f x = j y → ∃ x', i x' = x) :
    (ker f').map i = ker f := by
  refine le_antisymm (Submodule.map_le_iff_le_comap.2 (ker_le_comap_ker_of_apply_eq hcomm)) ?_
  intro x hx
  obtain ⟨x', rfl⟩ := hreg x 0 (by rw [map_zero, mem_ker.1 hx])
  exact ⟨x', hj (by rw [← hcomm, mem_ker.1 hx, map_zero]), rfl⟩

/-- In a commutative square with the regularity property and `j` injective, an element `y` lies
in the range of `f'` exactly when `j y` lies in the range of `f`. -/
theorem comap_range_eq_range_of_regularity (hcomm : ∀ x, f (i x) = j (f' x))
    (hj : Function.Injective j) (hreg : ∀ x y, f x = j y → ∃ x', i x' = x) :
    (range f).comap j = range f' := by
  refine le_antisymm ?_ (range_le_comap_range_of_apply_eq hcomm)
  rintro y ⟨x, hx⟩
  obtain ⟨x', rfl⟩ := hreg x y hx
  exact ⟨x', hj (by rw [← hcomm, hx])⟩

/-- The linear equivalence between the kernels of `f'` and `f` induced by `i`, in a commutative
square with the regularity property and `i`, `j` injective. -/
noncomputable def kerEquivOfRegularity (hcomm : ∀ x, f (i x) = j (f' x))
    (hi : Function.Injective i) (hj : Function.Injective j)
    (hreg : ∀ x y, f x = j y → ∃ x', i x' = x) : ker f' ≃ₗ[R] ker f :=
  (Submodule.equivMapOfInjective i hi (ker f')).trans
    (LinearEquiv.ofEq _ _ (map_ker_eq_ker_of_regularity hcomm hj hreg))

/-- The equivalence `kerEquivOfRegularity` is given by `i`. -/
@[simp]
theorem coe_kerEquivOfRegularity_apply (hcomm : ∀ x, f (i x) = j (f' x))
    (hi : Function.Injective i) (hj : Function.Injective j)
    (hreg : ∀ x y, f x = j y → ∃ x', i x' = x) (x : ker f') :
    (kerEquivOfRegularity hcomm hi hj hreg x : M) = i x :=
  (rfl)

/-- The linear equivalence between the cokernels of `f'` and `f` induced by `j`, in a commutative
square with the regularity property, `j` injective and `range f ⊔ range j = ⊤`. -/
noncomputable def cokerEquivOfRegularity (hcomm : ∀ x, f (i x) = j (f' x))
    (hj : Function.Injective j) (hreg : ∀ x y, f x = j y → ∃ x', i x' = x)
    (hsup : range f ⊔ range j = ⊤) : (N' ⧸ range f') ≃ₗ[R] N ⧸ range f :=
  LinearEquiv.ofBijective ((range f').mapQ (range f) j (range_le_comap_range_of_apply_eq hcomm))
    ⟨by
      rw [← ker_eq_bot, Submodule.ker_mapQ, comap_range_eq_range_of_regularity hcomm hj hreg,
        Submodule.mkQ_map_self],
    range_eq_top.1 (by rw [Submodule.range_mapQ, Submodule.map_mkQ_eq_top, hsup])⟩

/-- The equivalence `cokerEquivOfRegularity` is induced by `j`. -/
@[simp]
theorem cokerEquivOfRegularity_mk (hcomm : ∀ x, f (i x) = j (f' x))
    (hj : Function.Injective j) (hreg : ∀ x y, f x = j y → ∃ x', i x' = x)
    (hsup : range f ⊔ range j = ⊤) (y : N') :
    cokerEquivOfRegularity hcomm hj hreg hsup (Submodule.Quotient.mk y) =
      Submodule.Quotient.mk (j y) :=
  (rfl)

/-- **Invariance of the index under regularity.** In a commutative square `f (i x) = j (f' x)`
with `i`, `j` injective, the regularity property and `range f ⊔ range j = ⊤`, the maps `f'` and
`f` have the same index. -/
theorem index_eq_of_regularity (hcomm : ∀ x, f (i x) = j (f' x))
    (hi : Function.Injective i) (hj : Function.Injective j)
    (hreg : ∀ x y, f x = j y → ∃ x', i x' = x) (hsup : range f ⊔ range j = ⊤) :
    f'.index = f.index := by
  rw [index_eq_finrank_sub, index_eq_finrank_sub,
    (kerEquivOfRegularity hcomm hi hj hreg).finrank_eq,
    (cokerEquivOfRegularity hcomm hj hreg hsup).finrank_eq]

end Regularity

section RestrictScalars

open Module

variable (K : Type*) {L M N : Type*} [DivisionRing K] [DivisionRing L] [Module K L]
  [AddCommGroup M] [Module K M] [Module L M] [IsScalarTower K L M]
  [AddCommGroup N] [Module K N] [Module L N] [IsScalarTower K L N]

/-- Restricting scalars along a tower of division rings `K → L` multiplies the index by
`finrank K L`. No finiteness hypothesis is needed: an infinite-dimensional kernel or cokernel
has `finrank` zero over both `K` and `L`. -/
@[simp]
lemma index_restrictScalars (f : M →ₗ[L] N) :
    (f.restrictScalars K).index = finrank K L * f.index := by
  -- `(ker f).restrictScalars K` carries the `K`-module structure that `ker f` inherits from `M`.
  have hker : finrank K ((ker f).restrictScalars K) = finrank K L * finrank L (ker f) :=
    (finrank_mul_finrank K L (ker f)).symm
  rw [index_eq_finrank_sub, index_eq_finrank_sub, ker_restrictScalars, range_restrictScalars,
    (Submodule.Quotient.restrictScalarsEquiv K (range f)).finrank_eq, hker,
    ← finrank_mul_finrank K L (N ⧸ range f)]
  push_cast
  ring

end RestrictScalars

end LinearMap
