/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Closed
public import Mathlib.LinearAlgebra.Contraction

/-!
# Internal Hom from a finite projective module

For a finite projective module `M`, the canonical contraction from `Mᵛ ⊗ N` to
`Hom_R(M,N)` is an isomorphism, natural in both variables. This is the affine algebraic model for
the identification of the internal Hom from a finite locally free sheaf with tensoring by its dual.
The construction uses Mathlib's `dualTensorHomEquiv`.
-/

public section

open CategoryTheory MonoidalCategory MonoidalClosed

namespace TauCeti

open _root_.ModuleCat

universe u

noncomputable section

variable {R : Type u} [CommRing R] (M : ModuleCat.{u} R)
  [Module.Finite R M] [Module.Projective R M]

/-- The dual of a finite projective module tensored with `N` is the internal Hom from `M` to
`N`. Its forward map sends `f ⊗ n` to `m ↦ f(m) • n`. -/
def _root_.ModuleCat.dualTensorIhomIso (N : ModuleCat.{u} R) :
    ModuleCat.of R (Module.Dual R M) ⊗ N ≅ (ihom M).obj N :=
  ((dualTensorHomEquiv R M N).trans (homLinearEquiv (M := M) (N := N)).symm).toModuleIso

/-- The contraction isomorphism evaluates a pure tensor by applying its functional to the
argument and scaling the tensor's second factor. -/
@[simp]
theorem _root_.ModuleCat.dualTensorIhomIso_hom_tmul (N : ModuleCat.{u} R) (f : Module.Dual R M)
    (n : N) (m : M) :
    ((dualTensorIhomIso M N).hom (f ⊗ₜ[R] n)).hom m = f m • n := by
  rfl

/-- The contraction isomorphism is natural in the target module. -/
def _root_.ModuleCat.dualTensorIhomNatIso :
    MonoidalCategory.tensorLeft (ModuleCat.of R (Module.Dual R M)) ≅ ihom M :=
  NatIso.ofComponents (dualTensorIhomIso M) (fun {N P} g => by
    ext x
    induction x using TensorProduct.inductionOn with
    | tmul f n =>
      apply ModuleCat.Hom.ext
      ext m
      -- The two functor maps are categorical coercions of tensoring and postcomposition.
      change ((dualTensorIhomIso M P).hom (f ⊗ₜ[R] g n)).hom m =
        (((dualTensorIhomIso M N).hom (f ⊗ₜ[R] n)) ≫ g).hom m
      rw [dualTensorIhomIso_hom_tmul]
      change f m • g n = g.hom (((dualTensorIhomIso M N).hom (f ⊗ₜ[R] n)).hom m)
      rw [dualTensorIhomIso_hom_tmul]
      exact (g.hom.map_smul (f m) n).symm
    | add x y hx hy => simpa only [map_add] using congrArg₂ (· + ·) hx hy)

/-- The component of the natural tensor–Hom comparison is the contraction isomorphism. -/
@[simp]
theorem _root_.ModuleCat.dualTensorIhomNatIso_hom_app (N : ModuleCat.{u} R) :
    (dualTensorIhomNatIso M).hom.app N = (dualTensorIhomIso M N).hom := (rfl)

/-- Under the contraction isomorphism, internal-Hom evaluation sends
`m ⊗ (f ⊗ n)` to `f(m) • n`. -/
@[simp]
theorem _root_.ModuleCat.dualTensorIhomIso_ev (N : ModuleCat.{u} R)
    (m : M) (f : Module.Dual R M) (n : N) :
    ((𝟙 M ⊗ₘ (dualTensorIhomIso M N).hom) ≫ (ihom.ev M).app N)
      (m ⊗ₜ[R] (f ⊗ₜ[R] n)) = f m • n := by
  rw [ModuleCat.comp_apply, ModuleCat.MonoidalCategory.tensorHom_tmul, ModuleCat.id_apply]
  rw [ModuleCat.ihom_ev_app]
  -- The uncurry map evaluates the internal-Hom element at `m`.
  change ((dualTensorIhomIso M N).hom (f ⊗ₜ[R] n)).hom m = f m • n
  exact dualTensorIhomIso_hom_tmul M N f n m

/-- The tensor–Hom comparison is contravariantly natural in a finite projective source:
precomposing a linear map with `φ` corresponds to tensoring with the dual map of `φ`. -/
theorem _root_.ModuleCat.dualTensorIhomIso_naturality_left
    (M' : ModuleCat.{u} R) [Module.Finite R M'] [Module.Projective R M']
    (φ : M ⟶ M') (N : ModuleCat.{u} R) :
    (ModuleCat.ofHom φ.hom.dualMap ▷ N) ≫ (dualTensorIhomIso M N).hom =
      (dualTensorIhomIso M' N).hom ≫ (MonoidalClosed.pre φ).app N := by
  ext x
  induction x using TensorProduct.inductionOn with
  | tmul f n =>
    apply ModuleCat.Hom.ext
    ext m
    -- The categorical source map and precomposition are the ordinary dual and linear maps.
    change ((dualTensorIhomIso M N).hom (φ.hom.dualMap f ⊗ₜ[R] n)).hom m =
      ((dualTensorIhomIso M' N).hom (f ⊗ₜ[R] n)).hom (φ m)
    rw [dualTensorIhomIso_hom_tmul, dualTensorIhomIso_hom_tmul]
    rfl
  | add x y hx hy => simpa only [map_add] using congrArg₂ (· + ·) hx hy

end

end TauCeti
