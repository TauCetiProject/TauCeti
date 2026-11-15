/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Category.ModuleCat.Sheaf.TensorProduct.Stalk
public import TauCeti.AlgebraicGeometry.Modules.Stalk
public import TauCeti.AlgebraicGeometry.Modules.Tensor.Sections

/-!
# Stalks of tensor products of `𝒪_X`-modules

For arbitrary `𝒪_X`-modules `M` and `N` on a scheme `X` and a point `x : X`, the stalk `(M ⊗ N)_x`
is canonically isomorphic as an `𝒪_{X,x}`-module to `M_x ⊗[𝒪_{X,x}] N_x` (`tensorStalkComparison`,
`tensorStalkEquiv`), specializing `TauCeti.SheafOfModules.tensorObjStalkEquiv` with explicit germ
formulas (`tensorStalkComparison_germ_μ_tmul`, `tensorStalkComparison_germ_tmulRight`,
`tensorStalkEquiv_symm_tmul_germ`) and naturality in `f ⊗ₘ g`.
-/

public section

open CategoryTheory MonoidalCategory AlgebraicGeometry Opposite
open scoped TensorProduct
universe u
noncomputable section
namespace AlgebraicGeometry.Scheme.Modules
variable {X : Scheme.{u}} (M N : X.Modules) (x : X)

/-- The canonical `𝒪_{X,x}`-linear comparison `(M ⊗ N)_x →ₗ[𝒪_{X,x}] M_x ⊗[𝒪_{X,x}] N_x`. -/
@[expose] def tensorStalkComparison :
    (M ⊗ N).presheaf.stalk x →ₗ[X.presheaf.stalk x]
      M.presheaf.stalk x ⊗[X.presheaf.stalk x] N.presheaf.stalk x :=
  TauCeti.SheafOfModules.tensorObjStalkComparison X.sheaf M N x

/-- `(M ⊗ N)_x →ₗ[𝒪_{X,x}] M_x ⊗[𝒪_{X,x}] N_x` is bijective for arbitrary `𝒪_X`-modules. -/
theorem tensorStalkComparison_bijective : Function.Bijective (tensorStalkComparison M N x) :=
  TauCeti.SheafOfModules.tensorObjStalkComparison_bijective X.sheaf M N x

/-- The canonical `𝒪_{X,x}`-linear equivalence `(M ⊗ N)_x ≃ₗ[𝒪_{X,x}] M_x ⊗[𝒪_{X,x}] N_x`. -/
@[expose] def tensorStalkEquiv :
    (M ⊗ N).presheaf.stalk x ≃ₗ[X.presheaf.stalk x]
      M.presheaf.stalk x ⊗[X.presheaf.stalk x] N.presheaf.stalk x :=
  TauCeti.SheafOfModules.tensorObjStalkEquiv X.sheaf M N x
@[simp] theorem tensorStalkEquiv_apply (t : (M ⊗ N).presheaf.stalk x) :
    tensorStalkEquiv M N x t = tensorStalkComparison M N x t :=
  TauCeti.SheafOfModules.tensorObjStalkEquiv_apply X.sheaf M N x t

/-- `tensorStalkComparison` sends the germ of `μ(m ⊗ₜ n)` to `germ(m) ⊗ₜ germ(n)`. -/
theorem tensorStalkComparison_germ_μ_tmul (U : X.Opens) (hx : x ∈ U) (m : Γ(M, U)) (n : Γ(N, U)) :
    tensorStalkComparison M N x ((M ⊗ N).presheaf.germ U x hx
        (Functor.LaxMonoidal.μ (sectionsFunctor U) M N (m ⊗ₜ[Γ(X, U)] n))) =
      M.presheaf.germ U x hx m ⊗ₜ[X.presheaf.stalk x] N.presheaf.germ U x hx n :=
  TauCeti.SheafOfModules.tensorObjStalkComparison_germ_μ_tmul X.sheaf M N x U hx m n

/-- `tensorStalkComparison` sends the germ of `tmulRight M n m` to `germ(m) ⊗ₜ germ(n)`. -/
@[simp] theorem tensorStalkComparison_germ_tmulRight (U : X.Opens) (hx : x ∈ U) (m : Γ(M, U))
    (n : Γ(N, U)) :
    tensorStalkComparison M N x ((M ⊗ N).presheaf.germ U x hx (tmulRight M n m)) =
      M.presheaf.germ U x hx m ⊗ₜ[X.presheaf.stalk x] N.presheaf.germ U x hx n := by
  rw [tmulRight_apply]; exact tensorStalkComparison_germ_μ_tmul M N x U hx m n

/-- `(tensorStalkEquiv M N x).symm` sends `germ(m) ⊗ₜ germ(n)` to `germ(μ(m ⊗ₜ n))`. -/
@[simp] theorem tensorStalkEquiv_symm_tmul_germ (U : X.Opens) (hx : x ∈ U) (m : Γ(M, U))
    (n : Γ(N, U)) :
    (tensorStalkEquiv M N x).symm
        (M.presheaf.germ U x hx m ⊗ₜ[X.presheaf.stalk x] N.presheaf.germ U x hx n) =
      (M ⊗ N).presheaf.germ U x hx
        (Functor.LaxMonoidal.μ (sectionsFunctor U) M N (m ⊗ₜ[Γ(X, U)] n)) :=
  TauCeti.SheafOfModules.tensorObjStalkEquiv_symm_tmul_germ X.sheaf M N x U hx m n

/-- Naturality of `tensorStalkComparison` with respect to `f ⊗ₘ g`. -/
theorem tensorStalkComparison_naturality {M' N' : X.Modules} (f : M ⟶ M') (g : N ⟶ N') :
    (tensorStalkComparison M' N' x).comp ((f ⊗ₘ g).stalkMap x) =
      (TensorProduct.map (f.stalkMap x) (g.stalkMap x)).comp (tensorStalkComparison M N x) :=
  TauCeti.SheafOfModules.tensorObjStalkComparison_naturality X.sheaf M N x f g

/-- Naturality of `tensorStalkEquiv` with respect to `f ⊗ₘ g`. -/
theorem tensorStalkEquiv_naturality {M' N' : X.Modules} (f : M ⟶ M') (g : N ⟶ N') :
    (tensorStalkEquiv M' N' x).toLinearMap.comp ((f ⊗ₘ g).stalkMap x) =
      (TensorProduct.map (f.stalkMap x) (g.stalkMap x)).comp (tensorStalkEquiv M N x).toLinearMap :=
  TauCeti.SheafOfModules.tensorObjStalkEquiv_naturality X.sheaf M N x f g
end AlgebraicGeometry.Scheme.Modules
end
