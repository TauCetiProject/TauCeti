/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Singular.MappingTorus.Torsion
public import TauCeti.AlgebraicTopology.Cohomology.UniversalCoefficient

/-!
# The first cohomology of a mapping torus without invariant homology

Let `φ : F ≃ₜ F` be a homeomorphism of a path-connected space and `T_φ` its mapping torus, with
singular homology taken with coefficients in a domain `k`. Suppose `H₁(F)` is free of finite
rank and `det (𝟙 - φ_*) ≠ 0` on it, as for a surface mapping torus `Y_φ` with `b₁(Y_φ) = 1`.
The Wang sequence ends with

  `H₁(F) ⟶ H₁(T_φ) ⟶ H₀(F) ⟶ 0`,

with maps the fibre inclusion and the Wang connecting morphism `wangδ`. The image of the fibre is
torsion (`TauCeti.MappingTorus.torsion_homology_one_eq_range_homologyMap_fibreInclusionChainMap`),
so every linear map from `H₁(T_φ)` to a torsion-free module `M` factors uniquely through `wangδ`:
precomposition with `wangδ` is a linear equivalence `Hom(H₀(F), M) ≃ Hom(H₁(T_φ), M)`
(`TauCeti.MappingTorus.homologyOneHomEquiv`).

Since `H₀(T_φ)` is free, the universal coefficient theorem identifies `H¹(T_φ; M)` with
`Hom(H₁(T_φ), M)` through the Kronecker map, over any domain `k`. Since `H₀(F) ≅ k`, this gives a
linear equivalence `H¹(T_φ; M) ≃ M`
(`TauCeti.MappingTorus.singularCohomologyOneEquiv`). It evaluates a class on any `γ ∈ H₁(T_φ)`
whose image under `wangδ` is the class of a point, that is, on a loop that runs once around the
base circle (`TauCeti.MappingTorus.singularCohomologyOneEquiv_apply`); such a `γ` exists
(`TauCeti.MappingTorus.exists_singularHomology₀ε_wangδ_eq_one`). In particular `H¹(T_φ; k)` is
free of rank one, and `H¹(Y_φ; ℤ) ≅ ℤ` for a surface mapping torus with `b₁(Y_φ) = 1`, with
every torsion class of `H₁(Y_φ; ℤ)` invisible to it. Geometrically, the generator pairing to one
with such a loop is the class of the angular form `dt` of the fibration over the circle; that
de Rham comparison is not made here.

## Main results

* `TauCeti.MappingTorus.ker_wangδ_le_ker`: a linear map from `H₁(T_φ)` to a torsion-free module
  vanishes on the kernel of `wangδ`.
* `TauCeti.MappingTorus.homologyOneHomEquiv`: precomposition with `wangδ`,
  `Hom(H₀(F), M) ≃ₗ[k] Hom(H₁(T_φ), M)`.
* `TauCeti.MappingTorus.singularCohomologyOneEquiv`: `H¹(T_φ; M) ≃ₗ[k] M`, evaluation on a loop
  once around the base (`TauCeti.MappingTorus.singularCohomologyOneEquiv_apply`).
* `TauCeti.MappingTorus.free_singularCohomology_one`,
  `TauCeti.MappingTorus.finrank_singularCohomology_one`: `H¹(T_φ; k)` is free of rank one.

See A. Hatcher, *Algebraic Topology*, Section 2.2 for the Wang sequence of a mapping torus and
Section 3.1 for the universal coefficient theorem.
-/

public section

noncomputable section

open CategoryTheory Limits AlgebraicTopology HomologicalComplex

universe w

namespace TauCeti.MappingTorus

variable {k : Type w} [CommRing k] [IsDomain k] {F : Type w} [TopologicalSpace F]
  [PathConnectedSpace F] (φ : F ≃ₜ F)
  [Module.Free k ((((singularChainComplexFunctor (ModuleCat.{w} k)).obj
    (ModuleCat.of k k)).obj (TopCat.of F)).homology 1)]
  [Module.Finite k ((((singularChainComplexFunctor (ModuleCat.{w} k)).obj
    (ModuleCat.of k k)).obj (TopCat.of F)).homology 1)]
  (M : ModuleCat.{w} k) [Module.IsTorsionFree k M]

omit [PathConnectedSpace F] in
/-- If `H₁(F)` is free of finite rank and `det (𝟙 - φ_*) ≠ 0` on it, every linear map from
`H₁(T_φ)` to a torsion-free module vanishes on the kernel of the Wang connecting morphism, which
is the torsion image of the fibre. -/
theorem ker_wangδ_le_ker
    (hdet : (LinearMap.id -
      (homologyMap (monodromyChainMap φ (ModuleCat.of k k)) 1).hom).det ≠ 0)
    (f : (((singularChainComplexFunctor (ModuleCat.{w} k)).obj (ModuleCat.of k k)).obj
      (TopCat.of (MappingTorus φ))).homology 1 ⟶ M) :
    LinearMap.ker (wangδ φ (ModuleCat.of k k) 0).hom ≤ LinearMap.ker f.hom := by
  rw [← range_homologyMap_fibreInclusionChainMap]
  intro x hx
  obtain ⟨a, hax⟩ := range_homologyMap_fibreInclusionChainMap_le_torsion_homology φ 1 hdet hx
  rw [LinearMap.mem_ker]
  apply (isRegular_iff_mem_nonZeroDivisors.mpr a.2).isSMulRegular
  dsimp only
  rw [smul_zero, ← map_smul, ← Submonoid.smul_def, hax, map_zero]

/-- **Linear maps out of the first homology of a mapping torus.** If `H₁(F)` is free of finite
rank and `det (𝟙 - φ_*) ≠ 0` on it, precomposition with the Wang connecting morphism
`H₁(T_φ) ⟶ H₀(F)` is a linear equivalence `Hom(H₀(F), M) ≃ Hom(H₁(T_φ), M)` for every
torsion-free module `M`. -/
def homologyOneHomEquiv
    (hdet : (LinearMap.id -
      (homologyMap (monodromyChainMap φ (ModuleCat.of k k)) 1).hom).det ≠ 0) :
    ((((singularChainComplexFunctor (ModuleCat.{w} k)).obj (ModuleCat.of k k)).obj
        (TopCat.of F)).homology 0 ⟶ M) ≃ₗ[k]
      ((((singularChainComplexFunctor (ModuleCat.{w} k)).obj (ModuleCat.of k k)).obj
        (TopCat.of (MappingTorus φ))).homology 1 ⟶ M) := by
  refine LinearEquiv.ofBijective (Linear.leftComp k M (wangδ φ (ModuleCat.of k k) 0))
    ⟨fun g h hgh ↦ (cancel_epi _).1 hgh, fun f ↦ ?_⟩
  -- `f` vanishes on the kernel of the surjection `wangδ`, so it factors through it.
  have hδ : Function.Surjective (wangδ φ (ModuleCat.of k k) 0).hom :=
    (ModuleCat.epi_iff_surjective _).1 inferInstance
  let g : (((singularChainComplexFunctor (ModuleCat.{w} k)).obj (ModuleCat.of k k)).obj
      (TopCat.of F)).homology 0 ⟶ M :=
    ModuleCat.ofHom ((LinearMap.ker (wangδ φ (ModuleCat.of k k) 0).hom).liftQ f.hom
      (ker_wangδ_le_ker φ M hdet f) ∘ₗ
        ((wangδ φ (ModuleCat.of k k) 0).hom.quotKerEquivOfSurjective hδ).symm.toLinearMap)
  refine ⟨g, ModuleCat.hom_ext (LinearMap.ext fun x ↦ ?_)⟩
  have hx : ((wangδ φ (ModuleCat.of k k) 0).hom.quotKerEquivOfSurjective hδ).symm
      ((wangδ φ (ModuleCat.of k k) 0).hom x) = Submodule.Quotient.mk x := by
    rw [LinearEquiv.symm_apply_eq, LinearMap.quotKerEquivOfSurjective_apply_mk]
  -- `wangδ ≫ g` applied to `x` is `liftQ f` applied to the class of `x`, by definition of `g`.
  exact (congrArg ((LinearMap.ker (wangδ φ (ModuleCat.of k k) 0).hom).liftQ f.hom
    (ker_wangδ_le_ker φ M hdet f)) hx).trans (Submodule.liftQ_apply _ _ _)

/-- `homologyOneHomEquiv` is precomposition with the Wang connecting morphism. -/
@[simp]
theorem homologyOneHomEquiv_apply
    (hdet : (LinearMap.id -
      (homologyMap (monodromyChainMap φ (ModuleCat.of k k)) 1).hom).det ≠ 0)
    (g : (((singularChainComplexFunctor (ModuleCat.{w} k)).obj (ModuleCat.of k k)).obj
      (TopCat.of F)).homology 0 ⟶ M) :
    homologyOneHomEquiv φ M hdet g = wangδ φ (ModuleCat.of k k) 0 ≫ g :=
  (rfl)

/-- The factorization of a linear map `f` from `H₁(T_φ)` through the Wang connecting morphism:
`wangδ ≫ (homologyOneHomEquiv φ M hdet).symm f = f`. -/
@[reassoc (attr := simp)]
theorem wangδ_comp_homologyOneHomEquiv_symm_apply
    (hdet : (LinearMap.id -
      (homologyMap (monodromyChainMap φ (ModuleCat.of k k)) 1).hom).det ≠ 0)
    (f : (((singularChainComplexFunctor (ModuleCat.{w} k)).obj (ModuleCat.of k k)).obj
      (TopCat.of (MappingTorus φ))).homology 1 ⟶ M) :
    wangδ φ (ModuleCat.of k k) 0 ≫ (homologyOneHomEquiv φ M hdet).symm f = f := by
  rw [← homologyOneHomEquiv_apply φ M hdet, LinearEquiv.apply_symm_apply]

omit [IsDomain k] [Module.Free k ((((singularChainComplexFunctor (ModuleCat.{w} k)).obj
    (ModuleCat.of k k)).obj (TopCat.of F)).homology 1)]
  [Module.Finite k ((((singularChainComplexFunctor (ModuleCat.{w} k)).obj
    (ModuleCat.of k k)).obj (TopCat.of F)).homology 1)] in
/-- **A loop once around the base of a mapping torus**: some class of `H₁(T_φ)` is sent by the
Wang connecting morphism to the class of a point of the path-connected fibre, which the
augmentation sends to `1`. -/
theorem exists_singularHomology₀ε_wangδ_eq_one :
    ∃ γ : (((singularChainComplexFunctor (ModuleCat.{w} k)).obj (ModuleCat.of k k)).obj
        (TopCat.of (MappingTorus φ))).homology 1,
      ((TopCat.of F).singularHomology₀ε (ModuleCat.of k k)).hom
        ((wangδ φ (ModuleCat.of k k) 0).hom γ) = 1 := by
  obtain ⟨y, hy⟩ := (ModuleCat.epi_iff_surjective
    ((TopCat.of F).singularHomology₀ε (ModuleCat.of k k))).1 inferInstance 1
  obtain ⟨γ, rfl⟩ := (ModuleCat.epi_iff_surjective (wangδ φ (ModuleCat.of k k) 0)).1
    inferInstance y
  exact ⟨γ, hy⟩

/-- **The first cohomology of a mapping torus without invariant homology.** Over a domain `k`, if
the fibre is path-connected, `H₁(F)` is free of finite rank and `det (𝟙 - φ_*) ≠ 0` on it, then
`H¹(T_φ; M) ≃ₗ[k] M` for every torsion-free module `M`. The equivalence evaluates a class on a
loop once around the base (`TauCeti.MappingTorus.singularCohomologyOneEquiv_apply`). -/
def singularCohomologyOneEquiv
    (hdet : (LinearMap.id -
      (homologyMap (monodromyChainMap φ (ModuleCat.of k k)) 1).hom).det ≠ 0) :
    (TopCat.of (MappingTorus φ)).singularCohomology (ModuleCat.of k k) k M 1 ≃ₗ[k] M :=
  -- The Kronecker map is bijective in degree one since `H₀(T_φ)` is free.
  ((LinearEquiv.ofBijective _
      ((TopCat.of (MappingTorus φ)).singularKronecker_bijective_of_projective_homology_lt M 1
        fun j hj ↦ by
          obtain rfl : j = 0 := by omega
          exact ModuleCat.projective_of_free (Module.Free.chooseBasis k _))).trans
    (homologyOneHomEquiv φ M hdet).symm).trans
    ((Linear.homCongr k (asIso ((TopCat.of F).singularHomology₀ε (ModuleCat.of k k)))
      (Iso.refl M)).trans (ModuleCat.homLinearEquiv.trans (LinearMap.ringLmapEquivSelf k k M)))

/-- **Evaluation on a loop once around the base.** `singularCohomologyOneEquiv` sends a class of
`H¹(T_φ; M)` to its Kronecker pairing with any `γ ∈ H₁(T_φ)` whose image under the Wang
connecting morphism is the class of a point. -/
theorem singularCohomologyOneEquiv_apply
    (hdet : (LinearMap.id -
      (homologyMap (monodromyChainMap φ (ModuleCat.of k k)) 1).hom).det ≠ 0)
    {γ : (((singularChainComplexFunctor (ModuleCat.{w} k)).obj (ModuleCat.of k k)).obj
      (TopCat.of (MappingTorus φ))).homology 1}
    (hγ : ((TopCat.of F).singularHomology₀ε (ModuleCat.of k k)).hom
      ((wangδ φ (ModuleCat.of k k) 0).hom γ) = 1)
    (x : (TopCat.of (MappingTorus φ)).singularCohomology (ModuleCat.of k k) k M 1) :
    singularCohomologyOneEquiv φ M hdet x =
      ((TopCat.of (MappingTorus φ)).singularKronecker k 1 x).hom γ := by
  set ε := (TopCat.of F).singularHomology₀ε (ModuleCat.of k k)
  -- The inverse of the augmentation sends `1` to the image of `γ` under `wangδ`.
  have h₁ : (inv ε).hom 1 = (wangδ φ (ModuleCat.of k k) 0).hom γ := by
    rw [← hγ]
    exact congrArg (fun g ↦ g.hom ((wangδ φ (ModuleCat.of k k) 0).hom γ)) (IsIso.hom_inv_id ε)
  have h := congrArg (fun g ↦ g.hom γ) (wangδ_comp_homologyOneHomEquiv_symm_apply φ M hdet
    ((TopCat.of (MappingTorus φ)).singularKronecker k 1 x))
  simp only [ModuleCat.comp_apply] at h
  -- Unfolding the definition, the equivalence evaluates `(homologyOneHomEquiv φ M hdet).symm`
  -- of the Kronecker pairing at `inv ε 1`.
  have hdef : singularCohomologyOneEquiv φ M hdet x = ((homologyOneHomEquiv φ M hdet).symm
      ((TopCat.of (MappingTorus φ)).singularKronecker k 1 x)).hom ((inv ε).hom 1) := by
    rfl
  rw [hdef, h₁]
  exact h

/-- The class of `H¹(T_φ; M)` corresponding to `m ∈ M` pairs to `m` with every loop once around
the base. -/
theorem singularKronecker_singularCohomologyOneEquiv_symm_apply
    (hdet : (LinearMap.id -
      (homologyMap (monodromyChainMap φ (ModuleCat.of k k)) 1).hom).det ≠ 0)
    {γ : (((singularChainComplexFunctor (ModuleCat.{w} k)).obj (ModuleCat.of k k)).obj
      (TopCat.of (MappingTorus φ))).homology 1}
    (hγ : ((TopCat.of F).singularHomology₀ε (ModuleCat.of k k)).hom
      ((wangδ φ (ModuleCat.of k k) 0).hom γ) = 1)
    (m : M) :
    ((TopCat.of (MappingTorus φ)).singularKronecker k 1
      ((singularCohomologyOneEquiv φ M hdet).symm m)).hom γ = m := by
  rw [← singularCohomologyOneEquiv_apply φ M hdet hγ, LinearEquiv.apply_symm_apply]

/-- **The first cohomology of a mapping torus without invariant homology is free.** Over a domain
`k`, if the fibre is path-connected, `H₁(F)` is free of finite rank and `det (𝟙 - φ_*) ≠ 0` on it,
then `H¹(T_φ; k)` is a free `k`-module, of rank one by
`TauCeti.MappingTorus.finrank_singularCohomology_one`. -/
theorem free_singularCohomology_one
    (hdet : (LinearMap.id -
      (homologyMap (monodromyChainMap φ (ModuleCat.of k k)) 1).hom).det ≠ 0) :
    Module.Free k ((TopCat.of (MappingTorus φ)).singularCohomology (ModuleCat.of k k) k
      (ModuleCat.of k k) 1) :=
  Module.Free.of_equiv (singularCohomologyOneEquiv φ (ModuleCat.of k k) hdet).symm

/-- **The first cohomology of a mapping torus without invariant homology has rank one.** Over a
domain `k`, if the fibre is path-connected, `H₁(F)` is free of finite rank and
`det (𝟙 - φ_*) ≠ 0` on it, then `H¹(T_φ; k)` has rank one. For a surface mapping torus `Y_φ` with
`b₁(Y_φ) = 1` and `k = ℤ`, this is `H¹(Y_φ; ℤ) ≅ ℤ`. -/
theorem finrank_singularCohomology_one
    (hdet : (LinearMap.id -
      (homologyMap (monodromyChainMap φ (ModuleCat.of k k)) 1).hom).det ≠ 0) :
    Module.finrank k ((TopCat.of (MappingTorus φ)).singularCohomology (ModuleCat.of k k) k
      (ModuleCat.of k k) 1) = 1 :=
  (singularCohomologyOneEquiv φ (ModuleCat.of k k) hdet).finrank_eq.trans (Module.finrank_self k)

end TauCeti.MappingTorus
