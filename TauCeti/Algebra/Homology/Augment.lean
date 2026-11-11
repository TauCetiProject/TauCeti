/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Homology.Augment

/-!
# Iterated truncation of chain complexes

Mathlib's `ChainComplex.truncate` drops the term in degree `0` of an `ℕ`-indexed chain complex.
Iterating it `m` times drops the first `m` terms: the term in degree `k` of the result is the
term of the original complex in degree `k + m` (`ChainComplex.truncate_iterate_obj_X`).
Isomorphic complexes have isomorphic iterated truncations
(`ChainComplex.truncateIterateMapIso`), with the components of the original isomorphism
(`ChainComplex.truncateIterateMapIso_hom_f`).
-/

public section

open CategoryTheory Limits

universe v u

namespace ChainComplex

variable {C : Type u} [Category.{v} C] [HasZeroMorphisms C]

/-- Dropping the first `m` terms of a chain complex puts its term in degree `k + m` in
degree `k`. -/
theorem truncate_iterate_obj_X (K : ChainComplex C ℕ) (m k : ℕ) :
    (truncate.obj^[m] K).X k = K.X (k + m) := by
  induction m generalizing K with
  | zero => rfl
  | succ m ih => exact (ih (truncate.obj K)).trans rfl

/-- Dropping the first `m` terms of isomorphic complexes gives isomorphic complexes. -/
def truncateIterateMapIso {K L : ChainComplex C ℕ} (e : K ≅ L) :
    ∀ m : ℕ, truncate.obj^[m] K ≅ truncate.obj^[m] L
  | 0 => e
  | m + 1 => truncateIterateMapIso (truncate.mapIso e) m

variable {K L : ChainComplex C ℕ} (e : K ≅ L)

/-- Dropping no terms of isomorphic complexes gives back the isomorphism. -/
@[simp]
theorem truncateIterateMapIso_zero : truncateIterateMapIso e 0 = e := by
  rw [truncateIterateMapIso]

/-- Dropping `m + 1` terms of isomorphic complexes drops `m` terms of their truncations. -/
theorem truncateIterateMapIso_succ (m : ℕ) :
    truncateIterateMapIso e (m + 1) = truncateIterateMapIso (truncate.mapIso e) m := by
  rw [truncateIterateMapIso]

/-- The component in degree `k` of `ChainComplex.truncateIterateMapIso e m` is the component of
`e` in degree `k + m`. -/
theorem truncateIterateMapIso_hom_f (m k : ℕ) :
    (truncateIterateMapIso e m).hom.f k =
      eqToHom (truncate_iterate_obj_X K m k) ≫ e.hom.f (k + m) ≫
        eqToHom (truncate_iterate_obj_X L m k).symm := by
  induction m generalizing K L with
  | zero =>
    rw [truncateIterateMapIso_zero]
    -- `truncate.obj^[0] K` is `K` and `k + 0` is `k` by definition, so both `eqToHom`s are
    -- identities.
    exact ((Category.id_comp _).trans (Category.comp_id _)).symm
  | succ m ih =>
    rw [truncateIterateMapIso_succ, ih, Functor.mapIso_hom, truncate_map_f]
    -- `truncate.obj^[m + 1] K` is `truncate.obj^[m] (truncate.obj K)`, the term of
    -- `truncate.obj K` in degree `k + m` is the term of `K` in degree `k + m + 1`, and
    -- `k + m + 1` is `k + (m + 1)`, all by definition, so both sides are equal.
    rfl

/-- The component in degree `k` of the inverse of `ChainComplex.truncateIterateMapIso e m` is
the component of the inverse of `e` in degree `k + m`. -/
theorem truncateIterateMapIso_inv_f (m k : ℕ) :
    (truncateIterateMapIso e m).inv.f k =
      eqToHom (truncate_iterate_obj_X L m k) ≫ e.inv.f (k + m) ≫
        eqToHom (truncate_iterate_obj_X K m k).symm := by
  induction m generalizing K L with
  | zero =>
    rw [truncateIterateMapIso_zero]
    -- `truncate.obj^[0] K` is `K` and `k + 0` is `k` by definition, so both `eqToHom`s are
    -- identities.
    exact ((Category.id_comp _).trans (Category.comp_id _)).symm
  | succ m ih =>
    rw [truncateIterateMapIso_succ, ih, Functor.mapIso_inv, truncate_map_f]
    -- `truncate.obj^[m + 1] K` is `truncate.obj^[m] (truncate.obj K)`, the term of
    -- `truncate.obj K` in degree `k + m` is the term of `K` in degree `k + m + 1`, and
    -- `k + m + 1` is `k + (m + 1)`, all by definition, so both sides are equal.
    rfl

end ChainComplex
