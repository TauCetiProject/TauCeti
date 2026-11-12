/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.Modules.Tilde.Basic
public import TauCeti.AlgebraicGeometry.Modules.Tilde.Monoidal
public import TauCeti.Algebra.Category.ModuleCat.FiniteProjective.Dualizable
public import TauCeti.CategoryTheory.Monoidal.Rigid.Functor
public import TauCeti.CategoryTheory.Monoidal.Closed.Presentation

/-!
# Internal Hom on an affine scheme

For a finitely presented `R`-module `M` and any `R`-module `N`, the associated sheaf of
`Hom_R(M, N)` is the internal Hom from `M~` to `N~`. The isomorphism is the canonical
internal-Hom comparison of the strong monoidal tilde functor; in particular it respects
evaluation and is natural in both modules. No projectivity or Noetherian hypothesis is needed.

This identifies the internal-Hom objects on affine charts with the modules to which
`Module.FinitePresentation.isBaseChange_map` applies. Finite presentation is essential: the
internal Hom of arbitrary quasicoherent sheaves need not be quasicoherent.

## References

* The Stacks Project, Section 26.24 (Tag 01LA), item (10).
* R. Hartshorne, *Algebraic Geometry*, Exercise II.5.3.
-/

public section

open CategoryTheory Limits MonoidalCategory MonoidalClosed

namespace TauCeti.AlgebraicGeometry

open _root_.AlgebraicGeometry

universe u

noncomputable section

variable {R : CommRingCat.{u}}

/-- The tilde functor preserves internal Hom from a finitely presented module, naturally in
every target module. -/
instance isIso_tildeIhomComparison (M : ModuleCat.{u} R) [Module.FinitePresentation R M] :
    IsIso ((tilde.functor R).ihomComparison M) := by
  obtain ⟨n, m, f, g, hf, hgf⟩ := Module.FinitePresentation.exists_fin' R M
  let a : ModuleCat.of R (Fin m → R) ⟶ ModuleCat.of R (Fin n → R) := ModuleCat.ofHom g
  let b : ModuleCat.of R (Fin n → R) ⟶ M := ModuleCat.ofHom f
  have w : a ≫ b = 0 := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    exact hgf.apply_apply_eq_zero x
  have h : IsColimit (CokernelCofork.ofπ b w) :=
    ModuleCat.isColimitCokernelCofork a b hgf hf
  have freeComparison (k : ℕ) :
      IsIso ((tilde.functor R).ihomComparison (ModuleCat.of R (Fin k → R))) :=
    (tilde.functor R).ihomComparison_isIso_of_exactPairing
      (ᘁ(ModuleCat.of R (Fin k → R))) (ModuleCat.of R (Fin k → R))
  have := freeComparison n
  have := freeComparison m
  rw [NatTrans.isIso_iff_isIso_app]
  intro N
  exact (tilde.functor R).ihomComparison_isIso_of_cokernel a b w h N

/-- The associated sheaf of internal Hom from a finitely presented module is the internal Hom
of the associated sheaves, naturally in the target module. -/
def tildeIhomIso (M : ModuleCat.{u} R) [Module.FinitePresentation R M] :
    ihom M ⋙ tilde.functor R ≅ tilde.functor R ⋙ ihom ((tilde.functor R).obj M) :=
  asIso ((tilde.functor R).ihomComparison M)

/-- The forward affine internal-Hom isomorphism is the canonical monoidal comparison. -/
@[simp]
theorem tildeIhomIso_hom (M : ModuleCat.{u} R) [Module.FinitePresentation R M] :
    (tildeIhomIso M).hom = (tilde.functor R).ihomComparison M :=
  (rfl)

/-- The inverse affine internal-Hom isomorphism inverts the canonical monoidal comparison. -/
@[simp]
theorem tildeIhomIso_inv (M : ModuleCat.{u} R) [Module.FinitePresentation R M] :
    (tildeIhomIso M).inv = inv ((tilde.functor R).ihomComparison M) :=
  (rfl)

end

end TauCeti.AlgebraicGeometry
