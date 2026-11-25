/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.Grassmannian.Relative.Properties
public import TauCeti.AlgebraicGeometry.VectorBundle.Free.OpenSections

/-!
# Grassmannians of finite free sheaves

For a finite type `I` and a scheme `X`, the sections of the free sheaf `𝒪_X^I` over every affine
open are free (`FiniteLocallyFreeSheaf.free_freeSections`), of rank `#I` at every prime
(`FiniteLocallyFreeSheaf.rankAtStalk_freeSections`). So the extreme ranks of the relative
Grassmannian give the computations

* `G(#I, 𝒪_X^I) = X`: its structure morphism is an isomorphism
  (`FiniteLocallyFreeSheaf.isIso_grassmannianToBase_free`);
* `G(k, 𝒪_X^I) = ∅` for `k > #I` (`FiniteLocallyFreeSheaf.isEmpty_grassmannian_free_of_lt`).

Together with `G(0, E) = X` for every quasi-coherent `E`
(`AlgebraicGeometry.Scheme.Modules.isIso_grassmannianToBase_zero`) these compute the Grassmannian
of the trivial bundle `𝒪_X^n` in the extreme ranks: `Grass_n(𝒪_X^n) = X` and `Grass_N(𝒪_X^n) = ∅`
for `N > n`.
-/

public section

universe u

open CategoryTheory

namespace TauCeti.AlgebraicGeometry.FiniteLocallyFreeSheaf

open _root_.AlgebraicGeometry Scheme.Modules

variable {X : Scheme.{u}} (I : Type u) [Finite I]

/-- **`G(#I, 𝒪_X^I) = X`.** The relative Grassmannian of rank-`#I` quotients of the free sheaf
`𝒪_X^I` is the base. -/
theorem isIso_grassmannianToBase_free : IsIso (grassmannianToBase (free X I).obj (Nat.card I)) :=
  isIso_grassmannianToBase_of_rankAtStalk_eq (fun _ ↦ inferInstance)
    fun U p ↦ rankAtStalk_freeSections I U.val p

/-- **`G(k, 𝒪_X^I) = ∅` for `k > #I`.** The free sheaf `𝒪_X^I` has no locally free quotients of
rank larger than `#I`. -/
theorem isEmpty_grassmannian_free_of_lt {k : ℕ} (hk : Nat.card I < k) :
    IsEmpty (grassmannian (free X I).obj k) :=
  isEmpty_grassmannian_of_rankAtStalk_lt (fun _ ↦ inferInstance)
    fun U p ↦ (rankAtStalk_freeSections I U.val p).trans_lt hk

end TauCeti.AlgebraicGeometry.FiniteLocallyFreeSheaf
