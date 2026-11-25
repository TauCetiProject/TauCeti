/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Preadditive.Schur
public import TauCeti.Algebra.Category.FiniteIsocrystal.Abelian

/-!
# Simple finite isocrystals

A finite isocrystal `D` over `(L, σ)` is a simple object of the abelian category of finite
isocrystals iff it is nonzero and its only Frobenius-stable `L`-subspaces are `0` and `D`
(`TauCeti.FiniteIsocrystal.simple_iff`). Since the category has kernels, Schur's lemma applies:
a nonzero morphism between simple finite isocrystals is an isomorphism
(`CategoryTheory.isIso_of_hom_simple`), and the endomorphism `E`-algebra of a simple finite
isocrystal is a division ring (the `DivisionRing (End X)` instance of
`Mathlib.CategoryTheory.Preadditive.Schur`). Over the completion of the maximal unramified
extension of a local field, the simple isocrystals are the standard blocks of coprime slope, and
their endomorphism algebras are the central division algebras of the Dieudonné–Manin theory.

## Main results

* `TauCeti.FiniteIsocrystal.simple_iff`: simplicity in terms of Frobenius-stable subspaces.
* `TauCeti.FiniteIsocrystal.simple_of_finrank_eq_one`: a one-dimensional finite isocrystal is
  simple.

## References

* L. Fargues and J.-M. Fontaine, *Courbes et fibrés vectoriels en théorie de Hodge p-adique*,
  Astérisque 406 (2018), §8.2.3, Proposition 8.2.8.
-/

public section

open CategoryTheory

universe u

namespace TauCeti

namespace FiniteIsocrystal

variable {E L : Type*} [CommRing E] [Field L] [Algebra E L] {σ : L ≃ₐ[E] L}

/-- A finite isocrystal is simple iff it is nonzero and its only Frobenius-stable subspaces are
zero and the whole space. -/
theorem simple_iff (D : FiniteIsocrystal.{u} σ) :
    Simple D ↔ Nontrivial D ∧
      ∀ W : Submodule L D, (∀ x ∈ W, D.frobenius x ∈ W) → W = ⊥ ∨ W = ⊤ := by
  refine ⟨fun _ => ⟨?_, fun W hW => ?_⟩,
    fun ⟨_, h⟩ => ⟨fun {Y} f _ => ⟨fun _ hf => ?_, fun hf => ?_⟩⟩⟩
  · rw [← not_subsingleton_iff_nontrivial, ← isZero_iff_subsingleton]
    exact Simple.not_isZero D
  · -- A nonzero stable subspace gives a nonzero monomorphism into `D`, hence an isomorphism.
    refine or_iff_not_imp_left.2 fun hW0 => ?_
    have hι : D.subι W hW ≠ 0 := by
      obtain ⟨x, hx, hx0⟩ := W.ne_bot_iff.1 hW0
      intro h
      exact hx0 (by simpa using LinearMap.congr_fun (congrArg Hom.hom h) ⟨x, hx⟩)
    have := (isIso_iff_bijective _).1 ((Simple.mono_isIso_iff_nonzero _).2 hι)
    exact eq_top_iff.2 fun y _ => by
      obtain ⟨w, rfl⟩ := this.surjective y
      simp
  · -- An isomorphism onto the nonzero space `D` is surjective, so it is not zero.
    obtain ⟨x, hx⟩ := exists_ne (0 : D)
    obtain ⟨y, rfl⟩ := ((isIso_iff_bijective f).1 ‹_›).surjective x
    exact hx (by simp [hf])
  · -- The range of a nonzero monomorphism is a nonzero stable subspace, hence everything.
    refine (isIso_iff_bijective f).2 ⟨(mono_iff_injective f).1 ‹_›, ?_⟩
    refine LinearMap.range_eq_top.1 ((h _ fun _ => frobenius_mem_range f).resolve_left ?_)
    exact fun h0 => hf (hom_ext (LinearMap.range_eq_bot.1 h0))

/-- A one-dimensional finite isocrystal is simple. -/
theorem simple_of_finrank_eq_one {D : FiniteIsocrystal.{u} σ} (h : Module.finrank L D = 1) :
    Simple D :=
  have := Module.nontrivial_of_finrank_eq_succ h
  (simple_iff D).2 ⟨this, fun W _ => (is_simple_module_of_finrank_eq_one h).eq_bot_or_eq_top W⟩

end FiniteIsocrystal

end TauCeti
