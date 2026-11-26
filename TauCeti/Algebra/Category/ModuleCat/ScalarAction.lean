/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Basic

/-!
# Commuting scalar actions on morphisms in `ModuleCat`

When a `k`-module `M` carries a commuting distributive scalar action of `S`
(`[DistribSMul S M] [SMulCommClass k S M]`), scalar multiplication by `s : S` on `M` is the
`k`-linear endomorphism `DistribSMul.toLinearMap k M s`. Postcomposing a morphism
`f : A ⟶ ModuleCat.of k M` in `ModuleCat k` with this endomorphism scales the underlying `k`-linear
map by `s` (`ModuleCat.comp_ofHom_distribSMul`).
-/

public section

open CategoryTheory

universe v u

namespace ModuleCat

/-- Postcomposing a morphism in `ModuleCat k` into `M` with scalar multiplication by `s : S` scales
the underlying `k`-linear map by `s`. -/
@[simp]
lemma comp_ofHom_distribSMul {k : Type u} [Ring k] {S : Type*}
    {M : Type v} [AddCommGroup M] [Module k M] [DistribSMul S M] [SMulCommClass k S M]
    {A : ModuleCat.{v} k} (f : A ⟶ ModuleCat.of k M) (s : S) :
    have := SMulCommClass.symm k S M
    f ≫ ModuleCat.ofHom (DistribSMul.toLinearMap k M s) = ModuleCat.ofHom (s • f.hom) := by
  ext x
  simp [ModuleCat.hom_comp, DistribSMul.toLinearMap]

end ModuleCat
