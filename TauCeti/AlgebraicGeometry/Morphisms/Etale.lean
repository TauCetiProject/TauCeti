/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.AlgebraicGeometry.Morphisms.FlatRank
public import Mathlib.CategoryTheory.Monoidal.Cartesian.Over
import TauCeti.AlgebraicGeometry.Morphisms.Flat.Rank
import TauCeti.RingTheory.TotallySplit

/-!
# Finite schemes over a field with many rational points are étale

Let `f : X ⟶ Spec K` be a finite morphism to the spectrum of a field. Then `X` is affine, and its
points with values in `Spec K`, that is the sections of `f`, are the characters
`Γ(X, ⊤) →ₐ[K] K` of its coordinate ring. A finite-dimensional `K`-algebra has at most as many
characters as its dimension, which is the rank of `f`
(`AlgebraicGeometry.Scheme.Hom.finrank_eq_finrank_of_field`). When `X` has at least that many
points over `Spec K`, its coordinate ring is a finite product of copies of `K`
(`Algebra.IsFiniteSplit.of_finrank_le_card_algHom`), so `f` is étale.

Points over `Spec K` are written as morphisms `𝟙_ (Over (Spec K)) ⟶ Over.mk f` of the cartesian
monoidal category `Over (Spec K)`, as for the points of group schemes over `Spec K`.

## Main results

* `AlgebraicGeometry.Scheme.Hom.etale_of_finrank_le_natCard`: a finite morphism `f : X ⟶ Spec K`
  with at least `f.finrank s` points of `X` over `Spec K` is étale.
-/

public section

open CategoryTheory MonoidalCategory

universe u

namespace AlgebraicGeometry

/-- **A finite scheme over a field with as many rational points as its degree is étale.** Let
`f : X ⟶ Spec K` be finite. If `X` has at least `f.finrank s` points over `Spec K`, then `f` is
étale: the coordinate ring of `X` is a finite product of copies of `K`. -/
theorem Scheme.Hom.etale_of_finrank_le_natCard {K : Type u} [Field K] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of K)) [IsFinite f] (s : Spec (.of K))
    (h : f.finrank s ≤ Nat.card (𝟙_ (Over (Spec (.of K))) ⟶ Over.mk f)) : Etale f := by
  have : IsAffine X := isAffine_of_isAffineHom f
  let := ((Scheme.ΓSpecIso (.of K)).inv ≫ f.appTop).hom.toAlgebra
  have hf : algebraMap K Γ(X, ⊤) = ((Scheme.ΓSpecIso (.of K)).inv ≫ f.appTop).hom := rfl
  have : Module.Finite K Γ(X, ⊤) := f.moduleFinite_appTop hf
  -- a point `x` of `X` over `Spec K` is a section of `f`, so pulling back functions along it is a
  -- character of `Γ(X, ⊤)`
  let χ (x : 𝟙_ (Over (Spec (.of K))) ⟶ Over.mk f) : Γ(X, ⊤) →ₐ[K] K :=
    { toRingHom := (x.left.appTop ≫ (Scheme.ΓSpecIso (.of K)).hom).hom
      commutes' c := by
        have hx : x.left ≫ f = 𝟙 _ := by simpa using Over.w x
        have h1 : (Scheme.ΓSpecIso (.of K)).inv ≫ f.appTop ≫ x.left.appTop ≫
            (Scheme.ΓSpecIso (.of K)).hom = 𝟙 _ := by
          rw [← Category.assoc f.appTop, ← Scheme.Hom.comp_appTop, hx, Scheme.Hom.id_appTop]
          simp
        simpa [hf] using congr($h1 c) }
  -- points over `Spec K` are determined by their characters, as `X` is affine
  have hχ : Function.Injective χ := by
    intro x y hxy
    refine Over.OverMorphism.ext (ext_of_isAffine (Y := X) ?_)
    have h1 : x.left.appTop ≫ (Scheme.ΓSpecIso (.of K)).hom =
        y.left.appTop ≫ (Scheme.ΓSpecIso (.of K)).hom :=
      CommRingCat.hom_ext congr(($hxy).toRingHom)
    simpa using h1
  have : Finite (Γ(X, ⊤) →ₐ[K] K) := Finite.algHom K Γ(X, ⊤) K
  have : Algebra.IsFiniteSplit K Γ(X, ⊤) := .of_finrank_le_card_algHom <| by
    rw [← f.finrank_eq_finrank_of_field hf s]
    exact h.trans (Nat.card_le_card_of_injective χ hχ)
  -- `f` is étale exactly when its map of global sections is, and that map is `algebraMap K Γ(X, ⊤)`
  -- up to the isomorphism `Γ(Spec K, ⊤) ≅ K`
  have hf' : f.appTop =
      (Scheme.ΓSpecIso (.of K)).hom ≫ CommRingCat.ofHom (algebraMap K Γ(X, ⊤)) := by
    simp [hf]
  rw [HasRingHomProperty.iff_of_isAffine (P := @Etale), hf', CommRingCat.hom_comp,
    RingHom.Etale.respectsIso.cancel_left_isIso, CommRingCat.hom_ofHom, RingHom.etale_algebraMap]
  infer_instance

end AlgebraicGeometry
