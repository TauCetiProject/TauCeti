/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Category.FGModuleCat.Abelian
public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
public import Mathlib.RepresentationTheory.FDRep
public import TauCeti.RepresentationTheory.BaseChange
public import TauCeti.RepresentationTheory.Intertwining

/-!
# The reduction of a `G`-module as a finitely generated representation

Let `G` be a monoid, `V` a `G`-module (an abelian group with a distributive `G`-action) and `k` a
ring. The **reduction** of `V` is the representation `k ⊗_ℤ V` of `G`, with `G` acting
on the second factor (`Representation.baseChange`). When `k ⊗_ℤ V` is finitely generated over `k`
it is an object `TauCeti.reduction k G V` of `FDRep k G`, and an equivariant additive map
`f : V →+[G] W` induces the morphism `TauCeti.reductionMap k f : k ⊗_ℤ V ⟶ k ⊗_ℤ W`, functorially.

Reduction is **right exact**: a surjective equivariant map reduces to an epimorphism
(`TauCeti.epi_reductionMap`), and for `k` Noetherian, where `FDRep k G` is abelian, an exact
sequence `U → V → W → 0` of `G`-modules reduces to an exact sequence of representations
(`TauCeti.exact_reductionMap`), because tensoring over `ℤ` is right exact. It need not be left
exact, since `k` need not be flat over `ℤ`.

In characteristic `ℓ`, `k ⊗_ℤ V` is finitely generated as soon as `V ⧸ ℓV` is finite
(`TauCeti.finite_baseChange_of_finite_quotSMulTop`), even when `V` is not finitely generated, as
for the unit groups of local fields.

## Main definitions

* `TauCeti.reduction`: the reduction `k ⊗_ℤ V` of a `G`-module, as an object of `FDRep k G`.
* `TauCeti.reductionMap`: the morphism of reductions induced by an equivariant additive map.

## Main results

* `TauCeti.reductionMap_id`, `TauCeti.reductionMap_comp`: reduction is functorial.
* `TauCeti.exact_reductionMap`, `TauCeti.epi_reductionMap`: reduction is right exact.

## References

* J. Neukirch, A. Schmidt, K. Wingberg, *Cohomology of Number Fields*, 2nd ed., Springer (2008),
  §VII.3, (7.3.3).
-/

public section

namespace TauCeti

open CategoryTheory Function TensorProduct
open _root_.Representation (IntertwiningMap)

universe u v

variable (k : Type u) [Ring k] (G : Type v) [Monoid G]

/-- **The reduction** `k ⊗_ℤ V` of a `G`-module `V`, with `G` acting on the second factor, as a
finitely generated representation of `G` over `k`; it is defined when `k ⊗_ℤ V` is finitely
generated over `k`, for instance when `V` is a finitely generated abelian group or, in
characteristic `ℓ`, when `V ⧸ ℓV` is finite (`TauCeti.finite_baseChange_of_finite_quotSMulTop`). -/
@[expose]
noncomputable def reduction (V : Type u) [AddCommGroup V] [DistribMulAction G V]
    [Module.Finite k (k ⊗[ℤ] V)] : FDRep k G :=
  ⟨FGModuleCat.of k (k ⊗[ℤ] V),
    (MulEquiv.toMonoidHom (MulEquiv.symm InducedCategory.endEquiv)).comp
      ((ModuleCat.endRingEquiv (ModuleCat.of k (k ⊗[ℤ] V))).symm.toMonoidHom.comp
        (Representation.baseChange k (Representation.ofDistribMulAction ℤ G V)))⟩

variable {k G} {U V W : Type u} [AddCommGroup U] [DistribMulAction G U]
  [Module.Finite k (k ⊗[ℤ] U)] [AddCommGroup V] [DistribMulAction G V]
  [Module.Finite k (k ⊗[ℤ] V)] [AddCommGroup W] [DistribMulAction G W]
  [Module.Finite k (k ⊗[ℤ] W)]

/-- The action on the reduction is the base change of the action on `V`. -/
@[simp]
theorem reduction_ρ_hom_hom (g : G) :
    (Action.ρ (reduction k G V) g).hom.hom =
      Representation.baseChange k (Representation.ofDistribMulAction ℤ G V) g :=
  (rfl)

variable (k) in
/-- **The reduction of an equivariant additive map** `f : V →+[G] W`: the morphism
`k ⊗_ℤ V ⟶ k ⊗_ℤ W` of representations given by `a ⊗ v ↦ a ⊗ f v`. -/
noncomputable def reductionMap (f : V →+[G] W) : reduction k G V ⟶ reduction k G W :=
  { hom := ⟨ModuleCat.ofHom (f.toIntertwiningMap.baseChange k).toLinearMap⟩
    comm := by
      intro g
      apply InducedCategory.hom_ext
      apply ModuleCat.hom_ext
      exact (f.toIntertwiningMap.baseChange k).isIntertwining' g }

/-- The linear map underlying the reduction of `f` is the base change of `f`. -/
theorem reductionMap_hom_hom_hom (f : V →+[G] W) :
    (reductionMap k f).hom.hom.hom = f.toAddMonoidHom.toIntLinearMap.baseChange k := by
  -- The action morphism keeps the underlying base-changed linear map.
  change (f.toIntertwiningMap.baseChange k).toLinearMap = _
  rw [IntertwiningMap.toLinearMap_baseChange, DistribMulActionHom.toLinearMap_toIntertwiningMap]

/-- The reduction of `f` sends `a ⊗ v` to `a ⊗ f v`. -/
@[simp]
theorem reductionMap_tmul (f : V →+[G] W) (a : k) (v : V) :
    (reductionMap k f).hom.hom.hom (a ⊗ₜ[ℤ] v) = a ⊗ₜ[ℤ] f v :=
  (LinearMap.congr_fun (reductionMap_hom_hom_hom f) (a ⊗ₜ[ℤ] v)).trans
    (LinearMap.baseChange_tmul _ _ _)

/-- Two morphisms out of a reduction agree once they agree on the tensors `a ⊗ v`. -/
@[ext]
theorem reduction_hom_ext {X : FDRep k G} {φ ψ : reduction k G V ⟶ X}
    (h : ∀ (a : k) (v : V), φ.hom.hom.hom (a ⊗ₜ[ℤ] v) = ψ.hom.hom.hom (a ⊗ₜ[ℤ] v)) : φ = ψ :=
  Action.Hom.ext <| InducedCategory.hom_ext <| ModuleCat.hom_ext <|
    TensorProduct.AlgebraTensorModule.ext h

variable (k) in
/-- **Reduction preserves identities.** -/
@[simp]
theorem reductionMap_id : reductionMap k (DistribMulActionHom.id G : V →+[G] V) = 𝟙 _ := by
  -- both sides send `a ⊗ v` to `a ⊗ v`; the identity of `FDRep` is the identity linear map
  ext a v
  rw [reductionMap_tmul, DistribMulActionHom.id_apply]
  rfl

variable (k) in
/-- **Reduction preserves composition.** -/
@[simp]
theorem reductionMap_comp (f : U →+[G] V) (g : V →+[G] W) :
    reductionMap k (g.comp f) = reductionMap k f ≫ reductionMap k g := by
  -- both sides send `a ⊗ v` to `a ⊗ g (f v)`; composition in `FDRep` composes linear maps
  ext a v
  rw [reductionMap_tmul, DistribMulActionHom.comp_apply, ← reductionMap_tmul g,
    ← reductionMap_tmul f]
  rfl

variable (k) in
/-- The reductions of two equivariant maps with zero composite compose to zero. -/
theorem reductionMap_comp_reductionMap_eq_zero (f : U →+[G] V) (g : V →+[G] W)
    (h : ∀ x, g (f x) = 0) : reductionMap k f ≫ reductionMap k g = 0 := by
  ext a v
  rw [← reductionMap_comp, reductionMap_tmul, DistribMulActionHom.comp_apply, h, tmul_zero]
  -- the zero morphism of `FDRep` has the zero linear map underneath
  rfl

/-- The forgetful functor from `FDRep k G` to `ModuleCat k`, which is faithful and exact. -/
private abbrev forgetModuleCat : FDRep k G ⥤ ModuleCat k :=
  Action.forget (FGModuleCat k) G ⋙ forget₂ (FGModuleCat k) (ModuleCat k)

/-- The image of the reduction of `f` in `ModuleCat k` is `k ⊗ f`. -/
private theorem coe_forgetModuleCat_map_reductionMap (f : V →+[G] W) :
    ⇑(forgetModuleCat.map (reductionMap k f)).hom =
      ⇑(f.toAddMonoidHom.toIntLinearMap.lTensor k) := by
  -- `Action.forget` and `forget₂` keep the underlying linear map
  change ⇑(reductionMap k f).hom.hom.hom = _
  exact (congrArg DFunLike.coe (reductionMap_hom_hom_hom f)).trans
    (LinearMap.baseChange_eq_ltensor _)

variable (k) in
/-- **Reduction preserves epimorphisms**: a surjective equivariant map reduces to an epimorphism,
since tensoring preserves surjections. -/
theorem epi_reductionMap (g : V →+[G] W) (hg : Surjective g) : Epi (reductionMap k g) := by
  refine forgetModuleCat.epi_of_epi_map ((ModuleCat.epi_iff_surjective _).mpr ?_)
  rw [coe_forgetModuleCat_map_reductionMap]
  exact LinearMap.lTensor_surjective k hg

variable (k) [IsNoetherianRing k] in
/-- **Reduction is right exact**: for `k` Noetherian, where `FDRep k G` is abelian, an exact
sequence `U → V → W → 0` of `G`-modules reduces to an exact sequence `k ⊗_ℤ U → k ⊗_ℤ V → k ⊗_ℤ W`
of representations (and the last map is an epimorphism, `TauCeti.epi_reductionMap`). -/
theorem exact_reductionMap (f : U →+[G] V) (g : V →+[G] W) (hfg : Exact f g)
    (hg : Surjective g) :
    (ShortComplex.mk (reductionMap k f) (reductionMap k g)
      (reductionMap_comp_reductionMap_eq_zero k f g hfg.apply_apply_eq_zero)).Exact := by
  rw [← ShortComplex.exact_map_iff_of_faithful _ forgetModuleCat,
    ShortComplex.ShortExact.moduleCat_exact_iff_function_exact]
  dsimp only [ShortComplex.map_f, ShortComplex.map_g]
  rw [coe_forgetModuleCat_map_reductionMap, coe_forgetModuleCat_map_reductionMap]
  exact lTensor_exact k hfg hg

end TauCeti
