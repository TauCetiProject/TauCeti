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
  -- `toModuleIso` and `homLinearEquiv` wrap the contraction in categorical Hom data;
  -- the Mathlib lemma states its value as a linear map.
  change dualTensorHomEquiv R M N (f ⊗ₜ[R] n) m = f m • n
  exact dualTensorHomEquiv_tmul f m n

/-- The contraction isomorphism is natural in the target module. -/
def _root_.ModuleCat.dualTensorIhomNatIso :
    MonoidalCategory.tensorLeft (ModuleCat.of R (Module.Dual R M)) ≅ ihom M :=
  NatIso.ofComponents (dualTensorIhomIso M) (fun {N P} g => by
    ext x
    apply ModuleCat.Hom.ext
    ext m
    -- Both sides unfold to the linear maps compared by Mathlib's contraction naturality.
    exact LinearMap.congr_fun (LinearMap.congr_fun (dualTensorHom_comp_lTensor g.hom) x) m)

/-- The component of the natural tensor–Hom comparison is the contraction isomorphism. -/
@[simp]
theorem _root_.ModuleCat.dualTensorIhomNatIso_hom_app (N : ModuleCat.{u} R) :
    (dualTensorIhomNatIso M).hom.app N = (dualTensorIhomIso M N).hom := (rfl)

/-- The inverse component of the natural tensor–Hom comparison is the inverse contraction
isomorphism. -/
@[simp]
theorem _root_.ModuleCat.dualTensorIhomNatIso_inv_app (N : ModuleCat.{u} R) :
    (dualTensorIhomNatIso M).inv.app N = (dualTensorIhomIso M N).inv := (rfl)

/-- Under the contraction isomorphism, internal-Hom evaluation sends
`m ⊗ (f ⊗ n)` to `f(m) • n`. -/
theorem _root_.ModuleCat.dualTensorIhomIso_ev (N : ModuleCat.{u} R)
    (m : M) (f : Module.Dual R M) (n : N) :
    (ihom.ev M).app N (m ⊗ₜ[R] (dualTensorIhomIso M N).hom (f ⊗ₜ[R] n)) = f m • n := by
  -- `ihom_ev_app` describes evaluation as uncurried application, which unfolds to applying
  -- the internal-Hom element to `m`.
  rw [ModuleCat.ihom_ev_app]
  exact dualTensorIhomIso_hom_tmul M N f n m

/-- The tensor–Hom comparison is contravariantly natural in a finite projective source:
precomposing a linear map with `φ` corresponds to tensoring with the dual map of `φ`. -/
theorem _root_.ModuleCat.dualTensorIhomIso_naturality_left
    (M' : ModuleCat.{u} R) [Module.Finite R M'] [Module.Projective R M']
    (φ : M ⟶ M') (N : ModuleCat.{u} R) :
    (ModuleCat.ofHom φ.hom.dualMap ▷ N) ≫ (dualTensorIhomIso M N).hom =
      (dualTensorIhomIso M' N).hom ≫ (MonoidalClosed.pre φ).app N := by
  ext x
  apply ModuleCat.Hom.ext
  ext m
  -- `pre` and tensoring by the dual map are categorical wrappers around the two
  -- linear-map compositions in `dualTensorHom_comp_rTensor_dualMap`.
  exact LinearMap.congr_fun (LinearMap.congr_fun (dualTensorHom_comp_rTensor_dualMap φ.hom) x) m

end

end TauCeti
