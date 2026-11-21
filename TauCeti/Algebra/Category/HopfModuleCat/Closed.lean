/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Monoidal.Closed.Basic
public import TauCeti.Algebra.Category.HopfModuleCat.Monoidal
public import TauCeti.Algebra.HopfAlgebra.Module.Hom

/-!
# The closed structure on all modules over a Hopf algebra

For a Hopf algebra `H` over a field `k` with bijective antipode, the monoidal category
`HopfModuleCat k H` of all left `H`-modules is closed. The internal Hom `ihom hS M` sends `N` to the
space `Hom_k(M, N)` of all `k`-linear maps with Qi's action `(h • f)(m) = ∑ h₂ • f(S⁻¹(h₁) • m)`
(`TauCeti.BialgebraModule.LinHom`), and it is right adjoint to `M ⊗ -` by currying
(`tensorHomEquiv`).

The bijectivity of the antipode is an explicit hypothesis `hS`, so the closed structure is a
definition, `monoidalClosed hS`, rather than an instance. For finite-dimensional `H` the antipode
is always bijective (Larson–Sweedler).

## Main declarations

* `TauCeti.HopfModuleCat.ihom`: the internal Hom functor `Hom_k(M, -)`.
* `TauCeti.HopfModuleCat.tensorHomEquiv`: `(M ⊗ X ⟶ N) ≃ (X ⟶ Hom_k(M, N))`.
* `TauCeti.HopfModuleCat.ihomAdjunction`: the adjunction `M ⊗ - ⊣ Hom_k(M, -)`.
* `TauCeti.HopfModuleCat.monoidalClosed`: the closed monoidal structure.

## References

* Y. Qi, *Hopfological algebra*, Compos. Math. 150 (2014), Lemma 2.3.

The packaging follows the closed structure on Mathlib's `Rep`.
-/

public noncomputable section

open CategoryTheory MonoidalCategory

namespace TauCeti.HopfModuleCat

open BialgebraModule

universe u v

variable {k : Type u} [Field k] {H : Type v} [Ring H] [HopfAlgebra k H]
  (hS : Function.Bijective (HopfAlgebra.antipode k : H →ₗ[k] H))

/-- The internal Hom functor `Hom_k(M, -)`, with Qi's action on `k`-linear maps. -/
-- Exposed so that elements of `(ihom hS M).obj N` are `LinHom` elements, to which
-- `linHomEquiv` and the evaluation lemmas apply.
@[expose]
def ihom (M : HopfModuleCat k H) : HopfModuleCat k H ⥤ HopfModuleCat k H where
  obj N := of (LinHom k H M N hS)
  map g := ofHom (linHomPostcomp M hS g.hom)
  map_id N := by ext f m; simp
  map_comp g g' := by ext f m; simp

variable {hS}

/-- The internal Hom functor postcomposes with a morphism. -/
@[simp]
theorem linHomEquiv_ihom_map_hom_apply {M N N' : HopfModuleCat k H} (g : N ⟶ N')
    (f : (ihom hS M).obj N) (m : M) :
    linHomEquiv k H M N' hS (((ihom hS M).map g).hom f) m =
      g.hom (linHomEquiv k H M N hS f m) :=
  linHomEquiv_linHomPostcomp_apply g.hom f m

variable (hS) in
/-- Morphisms out of `M ⊗ X` correspond to morphisms into `Hom_k(M, N)`, by currying. -/
def tensorHomEquiv (M X N : HopfModuleCat k H) : (M ⊗ X ⟶ N) ≃ (X ⟶ (ihom hS M).obj N) where
  toFun g := ofHom (tensorLinHomEquiv k H M X N hS g.hom)
  invFun φ := ofHom ((tensorLinHomEquiv k H M X N hS).symm φ.hom)
  left_inv g := hom_ext ((tensorLinHomEquiv k H M X N hS).symm_apply_apply g.hom)
  right_inv φ := hom_ext ((tensorLinHomEquiv k H M X N hS).apply_symm_apply φ.hom)

/-- Currying evaluates on pure tensors. -/
@[simp]
theorem linHomEquiv_tensorHomEquiv_apply_hom_apply {M X N : HopfModuleCat k H} (g : M ⊗ X ⟶ N)
    (x : X) (m : M) :
    linHomEquiv k H M N hS ((tensorHomEquiv hS M X N g).hom x) m = g.hom (tmul k H m x) :=
  linHomEquiv_tensorLinHomEquiv_apply g.hom x m

/-- Uncurrying evaluates the image of the second factor on the first. -/
@[simp]
theorem tensorHomEquiv_symm_apply_hom_tmul {M X N : HopfModuleCat k H}
    (φ : X ⟶ (ihom hS M).obj N) (m : M) (x : X) :
    ((tensorHomEquiv hS M X N).symm φ).hom (tmul k H m x) = linHomEquiv k H M N hS (φ.hom x) m :=
  tensorLinHomEquiv_symm_apply_tmul φ.hom m x

variable (hS) in
/-- Tensoring on the left with `M` is left adjoint to the internal Hom `Hom_k(M, -)`. -/
def ihomAdjunction (M : HopfModuleCat k H) : tensorLeft M ⊣ ihom hS M :=
  Adjunction.mkOfHomEquiv
    { homEquiv := tensorHomEquiv hS M
      homEquiv_naturality_left_symm f g := tensor_ext fun m x => by simp
      homEquiv_naturality_right f g :=
        hom_ext <| LinearMap.ext fun x => LinHom.ext fun m => by simp }

/-- The hom-set bijection of the adjunction is `tensorHomEquiv`. -/
@[simp]
theorem ihomAdjunction_homEquiv (M X N : HopfModuleCat k H) :
    (ihomAdjunction hS M).homEquiv X N = tensorHomEquiv hS M X N := by
  simp [ihomAdjunction]

variable (hS) in
/-- All modules over a Hopf algebra with bijective antipode form a closed monoidal category, with
internal Hom `Hom_k(M, N)` under Qi's action. -/
@[implicit_reducible]
def monoidalClosed : MonoidalClosed (HopfModuleCat k H) where
  closed M := { rightAdj := ihom hS M, adj := ihomAdjunction hS M }

end TauCeti.HopfModuleCat
