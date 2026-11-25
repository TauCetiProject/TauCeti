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
(`tensorHomEquiv`, a `k`-linear equivalence).

The bijectivity of the antipode is an explicit hypothesis `hS`, so the closed structure is a
definition, `monoidalClosed hS`, rather than an instance. For finite-dimensional `H` the antipode
is always bijective (Larson–Sweedler).

## Main declarations

* `TauCeti.HopfModuleCat.ihom`: the internal Hom functor `Hom_k(M, -)`.
* `TauCeti.HopfModuleCat.tensorHomEquiv`: `(M ⊗ X ⟶ N) ≃ₗ[k] (X ⟶ Hom_k(M, N))`.
* `TauCeti.HopfModuleCat.ihomAdjunction`: the adjunction `M ⊗ - ⊣ Hom_k(M, -)`, with counit the
  evaluation `linHomEval` and unit the coevaluation `linHomCoeval`.
* `TauCeti.HopfModuleCat.monoidalClosed`: the closed monoidal structure, with lemmas identifying
  its internal Hom, evaluation, coevaluation, currying and precomposition.

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

/-- The internal Hom functor sends a morphism to postcomposition with it. -/
theorem ihom_map_hom {M N N' : HopfModuleCat k H} (g : N ⟶ N') :
    ((ihom hS M).map g).hom = linHomPostcomp M hS g.hom :=
  (rfl)

/-- The internal Hom functor postcomposes with a morphism. -/
@[simp]
theorem linHomEquiv_ihom_map_hom_apply {M N N' : HopfModuleCat k H} (g : N ⟶ N')
    (f : (ihom hS M).obj N) (m : M) :
    linHomEquiv k H M N' hS (((ihom hS M).map g).hom f) m =
      g.hom (linHomEquiv k H M N hS f m) :=
  linHomEquiv_linHomPostcomp_apply g.hom f m

/-- The internal Hom functor is additive. -/
instance (M : HopfModuleCat k H) : (ihom hS M).Additive where
  map_add {_ _ g g'} := hom_ext (linHomPostcomp_add g.hom g'.hom)

/-- The internal Hom functor is `k`-linear. -/
instance (M : HopfModuleCat k H) : (ihom hS M).Linear k where
  map_smul g r := hom_ext (linHomPostcomp_smul r g.hom)

variable (hS) in
/-- Morphisms out of `M ⊗ X` correspond to morphisms into `Hom_k(M, N)`, by currying. The
correspondence is `k`-linear. -/
def tensorHomEquiv (M X N : HopfModuleCat k H) : (M ⊗ X ⟶ N) ≃ₗ[k] (X ⟶ (ihom hS M).obj N) where
  toFun g := ofHom (tensorLinHomEquiv k H M X N hS g.hom)
  map_add' g g' := hom_ext ((tensorLinHomEquiv k H M X N hS).map_add g.hom g'.hom)
  map_smul' r g := hom_ext ((tensorLinHomEquiv k H M X N hS).map_smul r g.hom)
  invFun φ := ofHom ((tensorLinHomEquiv k H M X N hS).symm φ.hom)
  left_inv g := hom_ext ((tensorLinHomEquiv k H M X N hS).symm_apply_apply g.hom)
  right_inv φ := hom_ext ((tensorLinHomEquiv k H M X N hS).apply_symm_apply φ.hom)

/-- Currying is currying of the underlying `H`-linear maps. -/
theorem tensorHomEquiv_apply_hom {M X N : HopfModuleCat k H} (g : M ⊗ X ⟶ N) :
    (tensorHomEquiv hS M X N g).hom = tensorLinHomEquiv k H M X N hS g.hom :=
  (rfl)

/-- Uncurrying is uncurrying of the underlying `H`-linear maps. -/
theorem tensorHomEquiv_symm_apply_hom {M X N : HopfModuleCat k H} (φ : X ⟶ (ihom hS M).obj N) :
    ((tensorHomEquiv hS M X N).symm φ).hom = (tensorLinHomEquiv k H M X N hS).symm φ.hom :=
  (rfl)

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
    { homEquiv X N := (tensorHomEquiv hS M X N).toEquiv
      homEquiv_naturality_left_symm f g := tensor_ext fun m x => by simp
      homEquiv_naturality_right f g :=
        hom_ext <| LinearMap.ext fun x => LinHom.ext fun m => by simp }

/-- The hom-set bijection of the adjunction is `tensorHomEquiv`. -/
@[simp]
theorem ihomAdjunction_homEquiv (M X N : HopfModuleCat k H) :
    (ihomAdjunction hS M).homEquiv X N = (tensorHomEquiv hS M X N).toEquiv := by
  simp [ihomAdjunction]

/-- The counit of the adjunction is evaluation `m ⊗ f ↦ f m`. -/
@[simp]
theorem ihomAdjunction_counit_app_hom (M N : HopfModuleCat k H) :
    ((ihomAdjunction hS M).counit.app N).hom = linHomEval k H M N hS :=
  Tensor.ext fun m f => by
    simp only [ihomAdjunction, Adjunction.mkOfHomEquiv_counit_app,
      LinearEquiv.coe_toEquiv_symm]
    exact (tensorHomEquiv_symm_apply_hom_tmul _ m f).trans (linHomEval_tmul m f).symm

/-- The unit of the adjunction is coevaluation `x ↦ (m ↦ m ⊗ x)`. -/
@[simp]
theorem ihomAdjunction_unit_app_hom (M X : HopfModuleCat k H) :
    ((ihomAdjunction hS M).unit.app X).hom = linHomCoeval k H M X hS :=
  LinearMap.ext fun x => LinHom.ext fun m => by
    simp only [ihomAdjunction, Adjunction.mkOfHomEquiv_unit_app]
    exact (linHomEquiv_tensorHomEquiv_apply_hom_apply _ x m).trans
      (linHomEquiv_linHomCoeval_apply x m).symm

variable (hS) in
/-- All modules over a Hopf algebra with bijective antipode form a closed monoidal category, with
internal Hom `Hom_k(M, N)` under Qi's action. -/
@[expose, instance_reducible]
def monoidalClosed : MonoidalClosed (HopfModuleCat k H) where
  closed M := { rightAdj := ihom hS M, adj := ihomAdjunction hS M }

/-- The internal Hom of `monoidalClosed` is `ihom`. Not a simp lemma, so that the simp lemmas
about `CategoryTheory.ihom` keep applying. -/
theorem monoidalClosed_ihom (M : HopfModuleCat k H) :
    letI := monoidalClosed hS
    CategoryTheory.ihom M = ihom hS M :=
  (rfl)

/-- The tensor-Hom adjunction of `monoidalClosed` is `ihomAdjunction`. Not a simp lemma, so that
the simp lemmas about `CategoryTheory.ihom.adjunction` keep applying. -/
theorem monoidalClosed_adjunction (M : HopfModuleCat k H) :
    letI := monoidalClosed hS
    ihom.adjunction M = ihomAdjunction hS M :=
  (rfl)

/-- The evaluation of `monoidalClosed` is `linHomEval`. -/
@[simp]
theorem monoidalClosed_ev_app_hom (M N : HopfModuleCat k H) :
    letI := monoidalClosed hS
    ((ihom.ev M).app N).hom = linHomEval k H M N hS :=
  ihomAdjunction_counit_app_hom M N

/-- The coevaluation of `monoidalClosed` is `linHomCoeval`. -/
@[simp]
theorem monoidalClosed_coev_app_hom (M X : HopfModuleCat k H) :
    letI := monoidalClosed hS
    ((ihom.coev M).app X).hom = linHomCoeval k H M X hS :=
  ihomAdjunction_unit_app_hom M X

/-- Currying in `monoidalClosed` is `tensorHomEquiv`. -/
@[simp]
theorem monoidalClosed_curry {M X N : HopfModuleCat k H} (g : M ⊗ X ⟶ N) :
    letI := monoidalClosed hS
    MonoidalClosed.curry g = tensorHomEquiv hS M X N g := by
  let := monoidalClosed hS
  exact (MonoidalClosed.homEquiv_apply_eq g).symm.trans
    (DFunLike.congr_fun (ihomAdjunction_homEquiv M X N) g)

/-- Uncurrying in `monoidalClosed` is the inverse of `tensorHomEquiv`. -/
@[simp]
theorem monoidalClosed_uncurry {M X N : HopfModuleCat k H} (φ : X ⟶ (ihom hS M).obj N) :
    letI := monoidalClosed hS
    MonoidalClosed.uncurry φ = (tensorHomEquiv hS M X N).symm φ := by
  let := monoidalClosed hS
  exact (MonoidalClosed.homEquiv_symm_apply_eq φ).symm.trans
    (DFunLike.congr_fun (congrArg Equiv.symm (ihomAdjunction_homEquiv M X N)) φ)

/-- Precomposition of internal Homs in `monoidalClosed` is `linHomPrecomp`. -/
@[simp]
theorem monoidalClosed_pre_app_hom {M M' : HopfModuleCat k H} (f : M' ⟶ M)
    (N : HopfModuleCat k H) :
    letI := monoidalClosed hS
    ((MonoidalClosed.pre f).app N).hom = linHomPrecomp N hS f.hom := by
  let := monoidalClosed hS
  -- Both sides uncurry to `m ⊗ g ↦ g (f m)`. The goals mix `CategoryTheory.ihom M` with
  -- `ihom hS M`, which agree only after unfolding `ihom`, so `rw` and `simp` cannot match there;
  -- those steps go through `refine` and `exact`, which unify at default transparency.
  have hev (m : M') (g : (CategoryTheory.ihom M).obj N) :
      (f ▷ _ ≫ (ihom.ev M).app N).hom (tmul k H m g) = linHomEquiv k H M N hS g (f.hom m) := by
    rw [ModuleCat.hom_comp, LinearMap.comp_apply, whiskerRight_tmul, monoidalClosed_ev_app_hom]
    exact linHomEval_tmul _ g
  have : (MonoidalClosed.pre f).app N = ofHom (linHomPrecomp N hS f.hom) := by
    refine MonoidalClosed.uncurry_injective ((MonoidalClosed.uncurry_pre f N).trans ?_)
    refine ((monoidalClosed_uncurry (X := (ihom hS M).obj N) _).trans ?_).symm
    ext m g
    exact (tensorHomEquiv_symm_apply_hom_tmul _ m g).trans <|
      (linHomEquiv_linHomPrecomp_apply f.hom g m).trans (hev m g).symm
  exact (congrArg ModuleCat.Hom.hom this).trans (ModuleCat.hom_ofHom _)

end TauCeti.HopfModuleCat
