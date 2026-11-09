/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.Ext.Basic
public import Mathlib.Algebra.Category.ModuleCat.Abelian

/-!
# Extending linear maps along short exact sequences of modules

Let `S : 0 ⟶ X₁ ⟶ X₂ ⟶ X₃ ⟶ 0` be a short exact sequence of modules over a ring `R`. If
`Ext¹(X₃, Y) = 0`, every linear map `X₁ ⟶ Y` extends along `X₁ ⟶ X₂`; conversely, when `X₂` is
projective, this extension property gives `Ext¹(X₃, Y) = 0`. These are the linear-map forms of
`CategoryTheory.ShortComplex.ShortExact.exists_f_comp_eq_of_ext_eq_zero` and
`CategoryTheory.ShortComplex.ShortExact.ext_eq_zero_of_exists_f_comp_eq`, stated with
`ψ ∘ₗ S.f.hom = φ` for use with the linear-algebra API.

## Main results

* `CategoryTheory.ShortComplex.ShortExact.moduleCat_exists_comp_eq_of_ext_eq_zero`
* `CategoryTheory.ShortComplex.ShortExact.moduleCat_ext_eq_zero_of_exists_comp_eq`
-/

public section

universe w v u

open CategoryTheory CategoryTheory.Abelian

namespace CategoryTheory.ShortComplex.ShortExact

variable {R : Type u} [Ring R] [HasExt.{w} (ModuleCat.{v} R)] {S : ShortComplex (ModuleCat.{v} R)}
  (hS : S.ShortExact) {Y : ModuleCat.{v} R}
include hS

/-- If `Ext¹(S.X₃, Y) = 0`, every linear map `S.X₁ ⟶ Y` extends along `S.f`. -/
lemma moduleCat_exists_comp_eq_of_ext_eq_zero (h : ∀ x : Ext.{w} S.X₃ Y 1, x = 0)
    (φ : S.X₁ →ₗ[R] Y) : ∃ ψ : S.X₂ →ₗ[R] Y, ψ ∘ₗ S.f.hom = φ := by
  obtain ⟨g, hg⟩ := hS.exists_f_comp_eq_of_ext_eq_zero h (ModuleCat.ofHom φ)
  exact ⟨g.hom, congrArg ModuleCat.Hom.hom hg⟩

/-- If `S.X₂` is projective and every linear map `S.X₁ ⟶ Y` extends along `S.f`, then
`Ext¹(S.X₃, Y) = 0`. -/
lemma moduleCat_ext_eq_zero_of_exists_comp_eq [Projective S.X₂]
    (h : ∀ φ : S.X₁ →ₗ[R] Y, ∃ ψ : S.X₂ →ₗ[R] Y, ψ ∘ₗ S.f.hom = φ) (x : Ext.{w} S.X₃ Y 1) :
    x = 0 :=
  hS.ext_eq_zero_of_exists_f_comp_eq (fun φ ↦
    let ⟨ψ, hψ⟩ := h φ.hom; ⟨ModuleCat.ofHom ψ, ModuleCat.hom_ext hψ⟩) x

end CategoryTheory.ShortComplex.ShortExact
