/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Category.FGModuleCat.Abelian
public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
public import TauCeti.RepresentationTheory.GrothendieckGroup.GroupAlgebra.LatticeDefect.Basic
public import TauCeti.RepresentationTheory.GrothendieckGroup.GroupAlgebra.Ring
-- Non-public: `QuotSMulTop.bijective_baseChange_mkQ` is used only in proofs.
import TauCeti.LinearAlgebra.TensorProduct.Quotient

/-!
# The reduction of a `G`-module as a finite-dimensional representation

Let `G` be a monoid, `V` a `G`-module (an abelian group with a distributive `G`-action) and `k` a
commutative ring. The **reduction** of `V` is the representation `k ⊗_ℤ V` of `G`, with `G` acting
on the second factor (`Representation.baseChange`). When `k ⊗_ℤ V` is finitely generated over `k`
it is an object `TauCeti.reduction k G V` of `FDRep k G`, and an equivariant additive map
`f : V →+[G] W` induces the morphism `TauCeti.reductionMap k f : k ⊗_ℤ V ⟶ k ⊗_ℤ W`, functorially.

Reduction is **right exact** (`TauCeti.exact_reductionMap`, `TauCeti.epi_reductionMap`): an exact
sequence `U → V → W → 0` of `G`-modules gives an exact sequence of reductions, because tensoring
over `ℤ` is right exact. It is not left exact, since `k` need not be flat over `ℤ`; this is why the
lattice defect also involves the torsion `V[ℓ]`.

In characteristic `ℓ`, the reduction `k ⊗_ℤ V` is the reduction of `V ⧸ ℓV`
(`Representation.baseChangeQuotSMulTopEquiv`), so it is finitely generated as soon as `V ⧸ ℓV` is
finite (`TauCeti.finite_baseChange_of_finite_quotSMulTop`), even when `V` is not finitely
generated, as for the unit groups of local fields. For a finite group `G` and a field `k` of
characteristic `ℓ`, the lattice defect `TauCeti.latticeDefect k G ℓ V`, defined as
`[k ⊗_ℤ (V ⧸ ℓV)] - [k ⊗_ℤ V[ℓ]]`, is therefore `[k ⊗_ℤ V] - [k ⊗_ℤ V[ℓ]]`
(`TauCeti.latticeDefect_eq_fdRepK0RingEquiv_reduction_sub`).

## Main definitions

* `TauCeti.reduction`: the reduction `k ⊗_ℤ V` of a `G`-module, as an object of `FDRep k G`.
* `TauCeti.reductionMap`: the morphism of reductions induced by an equivariant additive map.

## Main results

* `TauCeti.reductionMap_id`, `TauCeti.reductionMap_comp`: reduction is functorial.
* `TauCeti.exact_reductionMap`, `TauCeti.epi_reductionMap`: reduction is right exact.
* `TauCeti.finite_baseChange_of_finite_quotSMulTop`: in characteristic `ℓ`, `k ⊗_ℤ V` is finitely
  generated over `k` when `V ⧸ ℓV` is finite.
* `TauCeti.fdRepK0RingEquiv_of_reduction`: the class of the reduction is the reduction class
  `TauCeti.reductionK0`.
* `TauCeti.latticeDefect_eq_fdRepK0RingEquiv_reduction_sub`: in characteristic `ℓ`, the lattice
  defect is `[k ⊗_ℤ V] - [k ⊗_ℤ V[ℓ]]`.

## References

* J. Neukirch, A. Schmidt, K. Wingberg, *Cohomology of Number Fields*, 2nd ed., Springer (2008),
  §VII.3, (7.3.3).
-/

public section

namespace TauCeti

open CategoryTheory Function TensorProduct
open scoped _root_.MonoidAlgebra

-- The `ℤ`-module structures on quotients and tensor products agree with the canonical one of an
-- abelian group, but not definitionally; prefer the structural ones, as the reduction
-- representations do.
attribute [local instance high] Submodule.Quotient.module TensorProduct.instModule

universe u v

/-! ### The reduction functor -/

section Reduction

variable (k : Type u) [CommRing k] (G : Type v) [Monoid G]

/-- **The reduction** `k ⊗_ℤ V` of a `G`-module `V`, with `G` acting on the second factor, as a
finite-dimensional representation of `G` over `k`; it is defined when `k ⊗_ℤ V` is finitely
generated over `k`, for instance when `V` is a finitely generated abelian group or, in
characteristic `ℓ`, when `V ⧸ ℓV` is finite (`TauCeti.finite_baseChange_of_finite_quotSMulTop`). -/
@[expose]
noncomputable def reduction (V : Type u) [AddCommGroup V] [DistribMulAction G V]
    [Module.Finite k (k ⊗[ℤ] V)] : FDRep k G :=
  FDRep.of (Representation.baseChange k (Representation.ofDistribMulAction ℤ G V))

variable {k G} {U V W : Type u} [AddCommGroup U] [DistribMulAction G U]
  [Module.Finite k (k ⊗[ℤ] U)] [AddCommGroup V] [DistribMulAction G V]
  [Module.Finite k (k ⊗[ℤ] V)] [AddCommGroup W] [DistribMulAction G W]
  [Module.Finite k (k ⊗[ℤ] W)]

/-- The action on the reduction is the base change of the action on `V`. -/
@[simp]
theorem reduction_ρ :
    (reduction k G V).ρ = Representation.baseChange k (Representation.ofDistribMulAction ℤ G V) :=
  (rfl)

variable (k) in
/-- **The reduction of an equivariant additive map** `f : V →+[G] W`: the morphism
`k ⊗_ℤ V ⟶ k ⊗_ℤ W` of representations given by `a ⊗ v ↦ a ⊗ f v`. -/
noncomputable def reductionMap (f : V →+[G] W) : reduction k G V ⟶ reduction k G W :=
  FDRep.forget₂HomLinearEquiv _ _ <| Rep.ofHom <|
    (f.toAddMonoidHom.toIntLinearMap.baseChange k).intertwiningMap_of_isIntertwiningMap
      (Representation.baseChange k (Representation.ofDistribMulAction ℤ G V))
      (Representation.baseChange k (Representation.ofDistribMulAction ℤ G W)) fun g x ↦ by
        have h : f.toAddMonoidHom.toIntLinearMap ∘ₗ Representation.ofDistribMulAction ℤ G V g =
            Representation.ofDistribMulAction ℤ G W g ∘ₗ f.toAddMonoidHom.toIntLinearMap :=
          LinearMap.ext fun v ↦ map_smul f g v
        rw [Representation.baseChange_apply, Representation.baseChange_apply,
          ← LinearMap.comp_apply, ← LinearMap.comp_apply, ← LinearMap.baseChange_comp,
          ← LinearMap.baseChange_comp, h]

/-- The linear map underlying the reduction of `f` is the base change of `f`. -/
theorem hom_hom_hom_reductionMap (f : V →+[G] W) :
    (reductionMap k f).hom.hom.hom = f.toAddMonoidHom.toIntLinearMap.baseChange k :=
  (rfl)

/-- The reduction of `f` sends `a ⊗ v` to `a ⊗ f v`. -/
@[simp]
theorem reductionMap_tmul (f : V →+[G] W) (a : k) (v : V) :
    (reductionMap k f).hom.hom.hom (a ⊗ₜ[ℤ] v) = a ⊗ₜ[ℤ] f v :=
  (rfl)

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
  rfl

variable (k) in
/-- **Reduction preserves composition.** -/
@[simp]
theorem reductionMap_comp (f : U →+[G] V) (g : V →+[G] W) :
    reductionMap k (g.comp f) = reductionMap k f ≫ reductionMap k g := by
  -- both sides send `a ⊗ v` to `a ⊗ g (f v)`; composition in `FDRep` composes linear maps
  ext a v
  rfl

variable (k) in
/-- The reductions of two equivariant maps with zero composite compose to zero. -/
theorem reductionMap_comp_reductionMap_eq_zero (f : U →+[G] V) (g : V →+[G] W)
    (h : ∀ x, g (f x) = 0) : reductionMap k f ≫ reductionMap k g = 0 := by
  ext a v
  rw [← reductionMap_comp, reductionMap_tmul, DistribMulActionHom.comp_apply, h, tmul_zero]
  -- the zero morphism of `FDRep` has the zero linear map underneath
  rfl

variable (k) in
/-- **Reduction preserves epimorphisms**: a surjective equivariant map reduces to an epimorphism,
since tensoring preserves surjections. -/
theorem epi_reductionMap (g : V →+[G] W) (hg : Surjective g) : Epi (reductionMap k g) :=
  (Action.forget (FGModuleCat k) G ⋙ forget₂ (FGModuleCat k) (ModuleCat k)).epi_of_epi_map <|
    (ModuleCat.epi_iff_surjective _).mpr <|
      LinearMap.lTensor_surjective k (g := g.toAddMonoidHom.toIntLinearMap) hg

variable (k) [IsNoetherianRing k] in
/-- **Reduction is right exact**: an exact sequence `U → V → W → 0` of `G`-modules reduces to an
exact sequence `k ⊗_ℤ U → k ⊗_ℤ V → k ⊗_ℤ W` of representations (and the last map is an
epimorphism, `TauCeti.epi_reductionMap`). Exactness is checked on underlying `k`-modules, where it
is the right exactness of the tensor product. -/
theorem exact_reductionMap (f : U →+[G] V) (g : V →+[G] W) (hfg : Exact f g)
    (hg : Surjective g) :
    (ShortComplex.mk (reductionMap k f) (reductionMap k g)
      (reductionMap_comp_reductionMap_eq_zero k f g hfg.apply_apply_eq_zero)).Exact := by
  rw [← ShortComplex.exact_map_iff_of_faithful _
      (Action.forget (FGModuleCat k) G ⋙ forget₂ (FGModuleCat k) (ModuleCat k)),
    ShortComplex.ShortExact.moduleCat_exact_iff_function_exact]
  exact lTensor_exact k (f := f.toAddMonoidHom.toIntLinearMap)
    (g := g.toAddMonoidHom.toIntLinearMap) hfg hg

end Reduction

/-! ### Finiteness in characteristic `ℓ` -/

section Finite

variable (k : Type u) [CommRing k] (ℓ : ℕ)

/-- **Finiteness of the reduction in characteristic `ℓ`.** If `k` has characteristic `ℓ` and
`V ⧸ ℓV` is finite, then `k ⊗_ℤ V` is finitely generated over `k`: it is isomorphic to
`k ⊗_ℤ (V ⧸ ℓV)` (`QuotSMulTop.bijective_baseChange_mkQ`), the base change of a finitely generated
abelian group. -/
theorem finite_baseChange_of_finite_quotSMulTop [CharP k ℓ] (V : Type*) [AddCommGroup V]
    [Finite (QuotSMulTop (ℓ : ℤ) V)] : Module.Finite k (k ⊗[ℤ] V) := by
  have := AddMonoid.FG.to_moduleFinite_int (G := QuotSMulTop (ℓ : ℤ) V)
  have hℓ : algebraMap ℤ k ℓ = 0 := by rw [map_natCast, CharP.cast_eq_zero]
  exact Module.Finite.equiv
    (LinearEquiv.ofBijective _ (QuotSMulTop.bijective_baseChange_mkQ (M := V) hℓ)).symm

end Finite

/-! ### Classes of reductions -/

section Class

variable {k : Type u} [Field k] (G : Type u) [Monoid G] [Finite G] (ℓ : ℕ)

/-- **The class of the reduction is the reduction class**: for a finitely generated `G`-module
`V`, the class of `TauCeti.reduction k G V` in the Grothendieck ring of `FDRep k G` corresponds to
`TauCeti.reductionK0 k` of the representation on `V` under `TauCeti.fdRepK0RingEquiv`. -/
theorem fdRepK0RingEquiv_of_reduction (V : Type u) [AddCommGroup V] [DistribMulAction G V]
    [Module.Finite ℤ V] :
    fdRepK0RingEquiv k G (ExactK0.of (reduction k G V)) =
      reductionK0 k (Representation.ofDistribMulAction ℤ G V) := by
  rw [fdRepK0RingEquiv_of, reductionK0_def]
  rfl

/-- **The lattice defect is `[k ⊗_ℤ V] - [k ⊗_ℤ V[ℓ]]`** in characteristic `ℓ`: the reduction of
`V ⧸ ℓV` in the definition of `TauCeti.latticeDefect` may be replaced by the reduction of `V`
itself, which is then finite-dimensional (`TauCeti.finite_baseChange_of_finite_quotSMulTop`). -/
theorem latticeDefect_eq_fdRepK0RingEquiv_reduction_sub [CharP k ℓ] (V : Type u) [AddCommGroup V]
    [DistribMulAction G V] [Finite (QuotSMulTop (ℓ : ℤ) V)]
    [Finite (Submodule.torsionBy ℤ V ℓ)] :
    haveI := finite_baseChange_of_finite_quotSMulTop k ℓ V
    haveI := AddMonoid.FG.to_moduleFinite_int (G := Submodule.torsionBy ℤ V ℓ)
    latticeDefect k G ℓ V = fdRepK0RingEquiv k G (ExactK0.of (reduction k G V)) -
      reductionK0 k ((Representation.ofDistribMulAction ℤ G V).torsionBy ℓ) := by
  have := finite_baseChange_of_finite_quotSMulTop k ℓ V
  have hℓ : algebraMap ℤ k ℓ = 0 := by rw [map_natCast, CharP.cast_eq_zero]
  have : Module.Finite k[G] (Representation.asModule (reduction k G V).ρ) :=
    Module.Finite.of_restrictScalars_finite k k[G] _
  rw [latticeDefect_def, fdRepK0RingEquiv_of, reductionK0_def]
  congr 1
  exact ExactK0.of_congr (Representation.asModuleLinearEquivOfEquiv
    ((Representation.ofDistribMulAction ℤ G V).baseChangeQuotSMulTopEquiv hℓ).symm).toFGModuleCatIso

end Class

end TauCeti
