/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.Modules.Sheaf
public import TauCeti.CategoryTheory.Sites.ExactImageSieve

/-!
# Exact sequences of modules on a scheme lift kernel sections locally

Let `F' ⟶ F ⟶ F''` be an exact sequence of `𝒪_X`-modules on a scheme `X`. A section of `F` over
an open `U` whose image in `F''` vanishes comes from `F'` near every point of `U`. Forgetting the
module structures (`TauCeti.AlgebraicGeometry.Scheme.Modules.toSheaf`) keeps the sequence exact,
and in the abelian category of sheaves on the opens of `X` a section killed by the second map lifts
locally (`CategoryTheory.ShortComplex.Exact.imageSieve_mem`).

## Main declarations

* `AlgebraicGeometry.Scheme.Modules.exists_app_eq_of_exact`: in an exact sequence of
  `𝒪_X`-modules, a section of the middle term killed by the second map lifts locally.
-/

public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Scheme.Modules

open TauCeti.AlgebraicGeometry in
/-- **Kernel sections lift locally.** In an exact sequence `F' ⟶ F ⟶ F''` of `𝒪_X`-modules, a
section of `F` over `U` with image zero in `F''` comes from `F'` near every point of `U`. -/
theorem exists_app_eq_of_exact {X : Scheme.{u}} {K : ShortComplex X.Modules} (hK : K.Exact)
    {U : X.Opens} (s : Γ(K.X₂, U)) (hs : K.g.app U s = 0) {x : X} (hx : x ∈ U) :
    ∃ (V : X.Opens) (i : V ⟶ U) (t : Γ(K.X₁, V)), x ∈ V ∧
      K.f.app V t = K.X₂.presheaf.map i.op s := by
  obtain ⟨V, i, ⟨t, ht⟩, hxV⟩ := (hK.map (Scheme.Modules.toSheaf X)).imageSieve_mem s hs x hx
  exact ⟨V, i, t, hxV, ht⟩

end AlgebraicGeometry.Scheme.Modules
