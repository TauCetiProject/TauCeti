/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Coalgebra.Comodule.EnoughInjectives
public import TauCeti.Algebra.Coalgebra.Comodule.Fixed
public import Mathlib.CategoryTheory.Abelian.RightDerived
public import Mathlib.RingTheory.Bialgebra.Basic
public import TauCeti.CategoryTheory.Abelian.RightDerived
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
import Mathlib.CategoryTheory.Abelian.Exact
import Mathlib.CategoryTheory.Preadditive.LeftExact

/-!
# Rational cohomology of comodules

Let `C` be a coalgebra over a commutative ring `R` with a distinguished element `1`, for instance
the coordinate Hopf algebra of an affine group scheme. Taking the invariants
`M^C = {m | coact m = m ⊗ 1}` of a right `C`-comodule is a functor `fixedFunctor R C` to
`R`-modules. When `C` is flat over `R` the comodules form an abelian category with enough
injectives, the invariants functor is left exact, and its right derived functors are the rational
cohomology modules `Hⁿ(C, M)`. In degree zero they recover the invariants, naturally in `M`.

For a bialgebra `C`, the invariants of the cofree comodule `N ⊗ C` are exactly the tensors
`n ⊗ 1`, and the counit identifies them with `N`. When `C` is moreover flat, the cofree functor is
exact and preserves injectives, so the cofree comodules are acyclic: `H⁰(C, N ⊗ C) ≅ N`, naturally
in `N`, and `Hⁿ(C, N ⊗ C) = 0` for `n > 0`. No flatness or finiteness condition is placed on the
coefficient modules `M` and `N`.

## Main declarations

* `TauCeti.ComoduleCat.fixedFunctor`: the invariants functor from comodules to modules.
* `TauCeti.ComoduleCat.fixedFunctor_preservesFiniteLimits`: over a flat coalgebra, taking
  invariants is left exact.
* `TauCeti.Comodule.cofreeFixedEquiv`: the invariants of a cofree comodule `N ⊗ C` over a
  bialgebra are `N`, through `n ↦ n ⊗ 1` and the counit.
* `TauCeti.ComoduleCat.cofreeFunctorCompFixedFunctorIso`: this identification as a natural
  isomorphism.
* `TauCeti.ComoduleCat.rationalCohomology`: the right derived functors of the invariants.
* `TauCeti.ComoduleCat.rationalCohomologyZeroIso`: `H⁰(C, M) ≅ M^C`, naturally in `M`.
* `TauCeti.ComoduleCat.cofreeFunctorCompRationalCohomologyZeroIso`: `H⁰(C, N ⊗ C) ≅ N`,
  naturally in `N`.
* `TauCeti.ComoduleCat.isZero_rationalCohomology_succ_obj_cofree`: `Hⁿ(C, N ⊗ C) = 0` for
  `n > 0`.

## References

* J. C. Jantzen, *Representations of Algebraic Groups*, Part I: §2.10 for invariants, §4.2 for
  the derived functors of the fixed-point functor, and §4.7 for the acyclicity of the comodules
  `N ⊗ k[G]`.
-/

public section

open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct

namespace TauCeti.Comodule.Hom

universe u v w x

variable {R : Type u} {C : Type v} {M : Type w} {N : Type x}

section CommSemiring

variable [CommSemiring R] [AddCommMonoid C] [Module R C] [Coalgebra R C] [One C]
variable [AddCommMonoid M] [Module R M] [Comodule R C M]
variable [AddCommMonoid N] [Module R N] [Comodule R C N]

/-- Restriction to invariants is additive in the comodule morphism. -/
@[simp]
theorem fixedMap_add (f g : Hom R C M N) : (f + g).fixedMap = f.fixedMap + g.fixedMap := by
  ext m
  simp

end CommSemiring

variable [CommRing R] [AddCommMonoid C] [Module R C] [Coalgebra R C] [One C]
variable [AddCommMonoid M] [Module R M] [Comodule R C M]
variable [AddCommMonoid N] [Module R N] [Comodule R C N]

/-- Over a flat coalgebra, the invariants of the kernel subcomodule of `f` are exactly the
invariant vectors killed by `f`: restriction to invariants is left exact. -/
theorem exact_fixedMap_subtype_ker_fixedMap [Module.Flat R C] (f : Hom R C M N) :
    Function.Exact (Subcomodule.subtype f.ker).fixedMap f.fixedMap := by
  rintro ⟨x, hx⟩
  rw [Subtype.ext_iff, fixedMap_apply, ZeroMemClass.coe_zero]
  refine ⟨fun hfx ↦ ?_, ?_⟩
  · -- The inclusion of the kernel reflects invariants because `C` is flat.
    have hker : x ∈ f.ker := mem_ker.mpr hfx
    have hfix : (⟨x, hker⟩ : f.ker) ∈ fixedSubcomodule R C f.ker :=
      ((Subcomodule.subtype f.ker).mem_fixedSubcomodule_iff_of_injective
        (fun a b h ↦ Subtype.ext (by rwa [Subcomodule.subtype_apply, Subcomodule.subtype_apply]
          at h)) ⟨x, hker⟩).mp
        (by rwa [Subcomodule.subtype_apply])
    exact ⟨⟨⟨x, hker⟩, hfix⟩, Subtype.ext (by rw [fixedMap_apply, Subcomodule.subtype_apply])⟩
  · rintro ⟨⟨y, hy⟩, hyx⟩
    rw [Subtype.ext_iff, fixedMap_apply, Subcomodule.subtype_apply] at hyx
    rw [← hyx]
    exact mem_ker.mp y.property

end TauCeti.Comodule.Hom

namespace TauCeti.Comodule

universe u v w

variable (R : Type u) (C : Type v) [CommSemiring R] [Semiring C] [Bialgebra R C]

-- As in the cofree adjunction, select the cofree coaction on `N ⊗[R] C` for this section.
attribute [local instance] cofree

/-- A vector of the cofree comodule `N ⊗ C` over a bialgebra is invariant exactly when it is
`n ⊗ 1` for some `n : N`. -/
theorem mem_fixedSubcomodule_cofree_iff {N : Type w} [AddCommMonoid N] [Module R N]
    (x : N ⊗[R] C) :
    x ∈ fixedSubcomodule R C (N ⊗[R] C) ↔ ∃ n : N, n ⊗ₜ[R] (1 : C) = x := by
  refine ⟨fun hx ↦ ⟨TensorProduct.rid R N (Coalgebra.counit.lTensor N x), ?_⟩, ?_⟩
  · -- Apply the counit to the middle factor of `coact x = x ⊗ 1`.
    have h := LinearMap.congr_fun
      (rTensor_rid_comp_lTensor_counit_comp_cofreeCoact (R := R) (C := C) (M := N)) x
    rw [LinearMap.comp_apply, cofreeCoact_def, ← cofree_coact, mem_fixedSubcomodule.mp hx] at h
    simpa using h
  · rintro ⟨n, rfl⟩
    rw [mem_fixedSubcomodule, cofree_coact_tmul, Bialgebra.comul_one,
      Algebra.TensorProduct.one_def, TensorProduct.assoc_symm_tmul]

/-- The invariants of the cofree comodule `N ⊗ C` over a bialgebra are identified with `N`:
`n` goes to `n ⊗ 1`, and an invariant tensor goes to its image under the counit of `C`. -/
noncomputable def cofreeFixedEquiv (N : Type w) [AddCommMonoid N] [Module R N] :
    N ≃ₗ[R] fixedSubcomodule R C (N ⊗[R] C) where
  toFun n := ⟨n ⊗ₜ[R] (1 : C), (mem_fixedSubcomodule_cofree_iff R C _).mpr ⟨n, rfl⟩⟩
  map_add' n n' := Subtype.ext (TensorProduct.add_tmul n n' 1)
  map_smul' r n := Subtype.ext (TensorProduct.smul_tmul' r n 1).symm
  invFun x := TensorProduct.rid R N (Coalgebra.counit.lTensor N (x : N ⊗[R] C))
  left_inv n := by simp
  right_inv := by
    rintro ⟨x, hx⟩
    obtain ⟨n, rfl⟩ := (mem_fixedSubcomodule_cofree_iff R C x).mp hx
    simp

variable {R C}

/-- The identification of cofree invariants sends `n` to `n ⊗ 1`. -/
@[simp]
theorem cofreeFixedEquiv_apply {N : Type w} [AddCommMonoid N] [Module R N] (n : N) :
    (cofreeFixedEquiv R C N n : N ⊗[R] C) = n ⊗ₜ[R] (1 : C) :=
  (rfl)

/-- The inverse identification of cofree invariants applies the counit of `C`. -/
@[simp]
theorem cofreeFixedEquiv_symm_apply {N : Type w} [AddCommMonoid N] [Module R N]
    (x : fixedSubcomodule R C (N ⊗[R] C)) :
    (cofreeFixedEquiv R C N).symm x =
      TensorProduct.rid R N (Coalgebra.counit.lTensor N (x : N ⊗[R] C)) :=
  (rfl)

/-- The identification of cofree invariants with the coefficient module is natural: restricting
`g ⊗ id` to invariants corresponds to `g`. -/
theorem cofreeFixedEquiv_symm_comp_fixedMap_cofreeMap {N N' : Type w} [AddCommMonoid N]
    [Module R N] [AddCommMonoid N'] [Module R N'] (g : N →ₗ[R] N') :
    (cofreeFixedEquiv R C N').symm.toLinearMap ∘ₗ (Hom.cofreeMap (C := C) g).fixedMap =
      g ∘ₗ (cofreeFixedEquiv R C N).symm.toLinearMap := by
  ext ⟨x, hx⟩
  obtain ⟨n, rfl⟩ := (mem_fixedSubcomodule_cofree_iff R C x).mp hx
  simp

end TauCeti.Comodule

namespace TauCeti.ComoduleCat

universe u v w

section Fixed

variable (R : Type u) (C : Type v) [CommRing R] [AddCommMonoid C] [Module R C] [Coalgebra R C]
  [One C]

/-- The invariants functor: a comodule `M` goes to its submodule of invariants
`{m | coact m = m ⊗ 1}`, and a comodule morphism to its restriction to invariants. -/
-- Expose the functor so that its values can be used as the fixed subcomodules they are.
@[expose] noncomputable def fixedFunctor : ComoduleCat.{u, v, w} R C ⥤ ModuleCat.{w} R where
  obj M := ModuleCat.of R (Comodule.fixedSubcomodule R C M)
  map f := ModuleCat.ofHom (Comodule.Hom.fixedMap f)
  map_id M := ModuleCat.hom_ext (Comodule.Hom.fixedMap_id (M := M))
  map_comp f g := ModuleCat.hom_ext (Comodule.Hom.fixedMap_comp g f)

variable {R C}

/-- The invariants functor sends a comodule to its fixed subcomodule. -/
@[simp]
theorem fixedFunctor_obj (M : ComoduleCat.{u, v, w} R C) :
    (fixedFunctor R C).obj M = ModuleCat.of R (Comodule.fixedSubcomodule R C M) :=
  (rfl)

/-- The invariants functor sends a comodule morphism to its restriction to invariants. -/
@[simp]
theorem fixedFunctor_map_hom {M N : ComoduleCat.{u, v, w} R C} (f : M ⟶ N) :
    ((fixedFunctor R C).map f).hom = Comodule.Hom.fixedMap f :=
  (rfl)

instance : (fixedFunctor.{u, v, w} R C).Additive where
  map_add {_ _ f g} := ModuleCat.hom_ext (Comodule.Hom.fixedMap_add f g)

variable [Module.Flat R C]

/-- Over a flat coalgebra, taking invariants preserves kernels: the invariants of the kernel
subcomodule are the kernel of the induced map on invariants. -/
instance {M N : ComoduleCat.{u, v, w} R C} (f : M ⟶ N) :
    PreservesLimit (parallelPair f 0) (fixedFunctor R C) := by
  have hι : ofHom (R := R) (C := C) (Subcomodule.subtype f.ker) ≫ f = 0 := by
    rw [← kernelIsoKer_inv_kernel_ι, Category.assoc, kernel.condition, comp_zero]
  have hlim : IsLimit (KernelFork.ofι (ofHom (R := R) (C := C) (Subcomodule.subtype f.ker)) hι) :=
    IsLimit.ofIsoLimit (kernelIsKernel f) (Fork.ext (kernelIsoKer f) (by
      simp only [Fork.ι_ofι, ← kernelIsoKer_inv_kernel_ι, Iso.hom_inv_id_assoc]))
  apply preservesLimit_of_preserves_limit_cone hlim
  apply (isLimitMapConeForkEquiv' (fixedFunctor R C) hι).symm.toFun
  apply ModuleCat.isLimitKernelFork
  · rw [fixedFunctor_map_hom, fixedFunctor_map_hom]
    exact Comodule.Hom.exact_fixedMap_subtype_ker_fixedMap f
  · rw [fixedFunctor_map_hom]
    exact Comodule.Hom.fixedMap_injective _ fun a b h ↦ Subtype.ext (by
      rwa [Subcomodule.subtype_apply, Subcomodule.subtype_apply] at h)

/-- Over a flat coalgebra, taking invariants is left exact. -/
instance fixedFunctor_preservesFiniteLimits :
    PreservesFiniteLimits (fixedFunctor.{u, v, w} R C) :=
  Functor.preservesFiniteLimits_of_preservesKernels _

end Fixed

section CofreeFunctor

variable (R : Type u) (C : Type v) [CommRing R] [Semiring C] [Bialgebra R C]

-- As in the cofree adjunction, select the cofree coaction on `N ⊗[R] C` for this section.
attribute [local instance] Comodule.cofree

/-- Over a bialgebra, taking invariants of cofree comodules recovers the coefficient module,
naturally: the component at `N` is the counit map `(N ⊗ C)^C ≅ N`. -/
noncomputable def cofreeFunctorCompFixedFunctorIso :
    cofreeFunctor.{u, v, w} R C ⋙ fixedFunctor R C ≅ 𝟭 (ModuleCat.{max v w} R) :=
  NatIso.ofComponents (fun N ↦ LinearEquiv.toModuleIso (Comodule.cofreeFixedEquiv R C N).symm)
    fun f ↦ ModuleCat.hom_ext (Comodule.cofreeFixedEquiv_symm_comp_fixedMap_cofreeMap f.hom)

-- The two component lemmas are not `simp` lemmas: `simp` would rewrite the composite functor in
-- the type of their left sides.
/-- The component of `cofreeFunctorCompFixedFunctorIso` at `N` applies the counit of `C`. -/
theorem cofreeFunctorCompFixedFunctorIso_hom_app_hom_apply (N : ModuleCat.{max v w} R)
    (x : Comodule.fixedSubcomodule R C (N ⊗[R] C)) :
    ((cofreeFunctorCompFixedFunctorIso R C).hom.app N).hom x =
      (Comodule.cofreeFixedEquiv R C N).symm x :=
  (rfl)

/-- The inverse component of `cofreeFunctorCompFixedFunctorIso` at `N` sends `n` to `n ⊗ 1`. -/
theorem cofreeFunctorCompFixedFunctorIso_inv_app_hom_apply (N : ModuleCat.{max v w} R) (n : N) :
    ((cofreeFunctorCompFixedFunctorIso R C).inv.app N).hom n = Comodule.cofreeFixedEquiv R C N n :=
  (rfl)

end CofreeFunctor

section CofreeExact

variable (R : Type u) (C : Type v) [CommRing R] [AddCommMonoid C] [Module R C] [Coalgebra R C]

/-- The cofree functor is additive: `(f + g) ⊗ id = f ⊗ id + g ⊗ id`. -/
instance : (cofreeFunctor.{u, v, w} R C).Additive where
  map_add {_ _ f g} := Comodule.Hom.toLinearMap_injective (by
    rw [toLinearMap_add, cofreeFunctor_map_toLinearMap, cofreeFunctor_map_toLinearMap,
      cofreeFunctor_map_toLinearMap, ModuleCat.hom_add, LinearMap.rTensor_add]
    -- The two sums of linear maps differ only in how the additive structure of the carrier
    -- `N ⊗[R] C` is presented: through the bundled cofree comodule or through the tensor product.
    rfl)

/-- The cofree functor sends injective modules to injective comodules. -/
instance [Module.Flat R C] : (cofreeFunctor.{u, v, w} R C).PreservesInjectiveObjects where
  injective_obj {M} _ := by
    rw [cofreeFunctor_obj]
    infer_instance

/-- Over a flat coalgebra the cofree functor `M ↦ M ⊗ C` is exact. -/
instance [Module.Flat R C] : (cofreeFunctor.{u, v, w} R C).PreservesHomology :=
  Functor.preservesHomology_of_map_exact _ fun S hS ↦ by
    -- Exactness of comodule complexes is detected on the underlying modules.
    rw [← ShortComplex.exact_map_iff_of_faithful _
      (forget₂ (ComoduleCat.{u, v, max v w} R C) (ModuleCat.{max v w} R)),
      ShortComplex.ShortExact.moduleCat_exact_iff_function_exact]
    rw [ShortComplex.ShortExact.moduleCat_exact_iff_function_exact] at hS
    simp only [ShortComplex.map_f, ShortComplex.map_g, forget₂_moduleCat_map,
      cofreeFunctor_map_toLinearMap]
    -- Flatness gives exactness of `- ⊗ C` in Mathlib's additive-group formulation.
    let := Module.addCommMonoidToAddCommGroup R (M := C)
    exact Module.Flat.rTensor_exact C hS

end CofreeExact

section Cohomology

variable (R : Type u) (C : Type v) [CommRing R] [AddCommMonoid C] [Module R C] [Coalgebra R C]
  [One C] [Module.Flat R C]

/-- The rational cohomology `Hⁿ(C, M)` of a comodule `M` over a flat coalgebra: the `n`-th right
derived functor of the invariants functor, computed from injective resolutions in the abelian
category of comodules. The carrier universe contains those of the ring and the coalgebra, so
that injective resolutions exist. -/
noncomputable def rationalCohomology (n : ℕ) :
    ComoduleCat.{u, v, max u v w} R C ⥤ ModuleCat.{max u v w} R :=
  (fixedFunctor R C).rightDerived n

instance (n : ℕ) : (rationalCohomology.{u, v, w} R C n).Additive :=
  Functor.additive_rightDerived _ n

/-- Rational cohomology in degree zero is the invariants functor. -/
noncomputable def rationalCohomologyZeroIso :
    rationalCohomology.{u, v, w} R C 0 ≅ fixedFunctor R C :=
  (fixedFunctor R C).rightDerivedZeroIsoSelf

/-- Rational cohomology vanishes in positive degrees on injective comodules. -/
theorem isZero_rationalCohomology_succ_obj_of_injective (n : ℕ)
    (M : ComoduleCat.{u, v, max u v w} R C) [Injective M] :
    IsZero ((rationalCohomology.{u, v, w} R C (n + 1)).obj M) :=
  (fixedFunctor R C).isZero_rightDerived_obj_injective_succ n M

end Cohomology

section CohomologyCofree

variable (R : Type u) (C : Type v) [CommRing R] [Semiring C] [Bialgebra R C] [Module.Flat R C]

/-- Over a flat bialgebra, the degree-zero rational cohomology of the cofree comodule `N ⊗ C` is
`N`, naturally in `N`, through the counit of `C`. -/
noncomputable def cofreeFunctorCompRationalCohomologyZeroIso :
    cofreeFunctor.{u, v, max u w} R C ⋙ rationalCohomology.{u, v, w} R C 0 ≅
      𝟭 (ModuleCat.{max u v w} R) :=
  Functor.isoWhiskerLeft _ (rationalCohomologyZeroIso R C) ≪≫
    cofreeFunctorCompFixedFunctorIso.{u, v, max u w} R C

/-- Over a flat bialgebra, the rational cohomology of a cofree comodule `N ⊗ C` vanishes in
positive degrees, for every coefficient module `N`. Indeed an injective resolution of `N` gives,
after tensoring with `C`, an injective resolution of `N ⊗ C` whose invariants are the original
resolution of `N`. -/
theorem isZero_rationalCohomology_succ_obj_cofree (N : ModuleCat.{max u v w} R) (n : ℕ) :
    IsZero ((rationalCohomology.{u, v, w} R C (n + 1)).obj
      ((cofreeFunctor.{u, v, max u w} R C).obj N)) :=
  ((𝟭 (ModuleCat.{max u v w} R)).isZero_rightDerived_succ N n).of_iso
    ((Functor.rightDerivedCompIso (𝟭 _) (𝟭 _) (cofreeFunctor.{u, v, max u w} R C)
      (fixedFunctor R C)
      (Functor.leftUnitor _ ≪≫ (cofreeFunctorCompFixedFunctorIso.{u, v, max u w} R C).symm)
      (n + 1)).app N).symm

end CohomologyCofree

end TauCeti.ComoduleCat
