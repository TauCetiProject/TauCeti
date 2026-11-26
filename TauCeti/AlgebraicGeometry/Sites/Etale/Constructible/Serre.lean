/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.ObjectProperty.Extensions
public import Mathlib.CategoryTheory.ObjectProperty.Kernels
public import TauCeti.Algebra.Homology.DerivedCategory.HomologyIn
public import TauCeti.AlgebraicGeometry.Sites.Etale.Constructible.Basic
public import TauCeti.AlgebraicGeometry.Sites.Etale.FiniteLisse.Serre

/-!
# Constructible étale sheaves form a weak Serre class

Let `X` be a scheme and `Λ` a ring. This file proves that constructible étale sheaves of
`Λ`-modules on `X` (`AlgebraicGeometry.Scheme.constructibleSheaf X Λ`) are closed under cokernels
over any ring `Λ`, and closed under kernels and extensions when `Λ` is left Noetherian. Together
with the instances `IsClosedUnderIsomorphisms` and `ContainsZero` from
`TauCeti.AlgebraicGeometry.Sites.Etale.Constructible.Basic`, constructible sheaves form a weak
Serre class in `Sheaf (smallEtaleTopology X) (ModuleCat.{u} Λ)` over any left Noetherian ring `Λ`.

For two sheaves `F` and `G` constructible on an open `U`, passing to the common refinement
`S.inf T` of constructible stratifications trivializing `F` and `G` reduces closure under kernels,
cokernels, and extensions to the corresponding closure properties for finite lisse sheaves
(`TauCeti.AlgebraicGeometry.Sites.Etale.FiniteLisse.Serre`), using the exactness of inverse image
along each stratum immersion.

In particular, over a left Noetherian ring `Λ`, complexes in `DerivedCategory` with constructible
cohomology sheaves (`DerivedCategory.homologyIn (X.constructibleSheaf Λ)`) form a triangulated
subcategory.

## Main results

* `CategoryTheory.Sheaf.IsConstructibleOn.of_isColimit_cokernelCofork`,
  `CategoryTheory.Sheaf.IsConstructibleOn.cokernel`: constructibility on an open is closed under
  cokernels over any ring `Λ`.
* `CategoryTheory.Sheaf.IsConstructibleOn.of_isLimit_kernelFork`,
  `CategoryTheory.Sheaf.IsConstructibleOn.kernel`: constructibility on an open is closed under
  kernels over any left Noetherian ring `Λ`.
* `CategoryTheory.Sheaf.IsConstructibleOn.of_shortExact`: constructibility on an open is closed
  under extensions over any left Noetherian ring `Λ`.
* `AlgebraicGeometry.Scheme.isClosedUnderCokernels_constructibleSheaf`:
  `X.constructibleSheaf Λ` is closed under cokernels over any ring `Λ`.
* `AlgebraicGeometry.Scheme.isClosedUnderKernels_constructibleSheaf`:
  `X.constructibleSheaf Λ` is closed under kernels over any left Noetherian ring `Λ`.
* `AlgebraicGeometry.Scheme.isClosedUnderExtensions_constructibleSheaf`:
  `X.constructibleSheaf Λ` is closed under extensions over any left Noetherian ring `Λ`.

## References

* M. Artin, A. Grothendieck, J.-L. Verdier, *SGA 4*, Exposé IX, §2.7.
* The Stacks Project, Section 59.71, Constructible sheaves, Tag 03RZ and Tag 095R.
-/

public section

universe u w

open CategoryTheory Limits AlgebraicGeometry Scheme

namespace CategoryTheory.Sheaf

variable {X : Scheme.{u}} {Λ : Type u} [Ring Λ]
  {F G : Sheaf (smallEtaleTopology X) (ModuleCat.{u} Λ)} {U : X.Opens}

/-- Over any ring `Λ`, the target of a colimit cokernel cofork between sheaves constructible on
`U` is constructible on `U`. -/
theorem IsConstructibleOn.of_isColimit_cokernelCofork {φ : F ⟶ G} {k : CokernelCofork φ}
    (hk : IsColimit k) (hF : F.IsConstructibleOn U) (hG : G.IsConstructibleOn U) :
    k.pt.IsConstructibleOn U := by
  obtain ⟨S, hS⟩ := isConstructibleOn_iff.mp hF
  obtain ⟨T, hT⟩ := isConstructibleOn_iff.mp hG
  refine isConstructibleOn_iff.mpr ⟨S.inf T, fun p ↦ ?_⟩
  let P := ((S.inf T).f p).smallEtalePullback (ModuleCat.{u} Λ)
  have hcok : (Limits.cokernel (P.map φ)).IsFiniteLisse :=
    IsFiniteLisse.cokernel ((S.inf_refines_left T).isFiniteLisse hS p)
      ((S.inf_refines_right T).isFiniteLisse hT p) (P.map φ)
  exact hcok.of_iso
    ((P.mapIso (hk.coconePointUniqueUpToIso (cokernelIsCokernel φ)) ≪≫
      PreservesCokernel.iso P φ).symm)

/-- Over any ring `Λ`, the cokernel of a morphism between sheaves constructible on `U` is
constructible on `U`. -/
theorem IsConstructibleOn.cokernel (hF : F.IsConstructibleOn U) (hG : G.IsConstructibleOn U)
    (φ : F ⟶ G) : (Limits.cokernel φ).IsConstructibleOn U :=
  (hF.of_isColimit_cokernelCofork (cokernelIsCokernel φ) hG :)

/-- Over a left Noetherian ring `Λ`, the source of a limit kernel fork between sheaves
constructible on `U` is constructible on `U`. -/
theorem IsConstructibleOn.of_isLimit_kernelFork [IsNoetherianRing Λ] {φ : F ⟶ G}
    {k : KernelFork φ} (hk : IsLimit k) (hF : F.IsConstructibleOn U)
    (hG : G.IsConstructibleOn U) : k.pt.IsConstructibleOn U := by
  obtain ⟨S, hS⟩ := isConstructibleOn_iff.mp hF
  obtain ⟨T, hT⟩ := isConstructibleOn_iff.mp hG
  refine isConstructibleOn_iff.mpr ⟨S.inf T, fun p ↦ ?_⟩
  let P := ((S.inf T).f p).smallEtalePullback (ModuleCat.{u} Λ)
  have hker : (Limits.kernel (P.map φ)).IsFiniteLisse :=
    IsFiniteLisse.kernel ((S.inf_refines_left T).isFiniteLisse hS p)
      ((S.inf_refines_right T).isFiniteLisse hT p) (P.map φ)
  exact hker.of_iso
    ((P.mapIso (hk.conePointUniqueUpToIso (kernelIsKernel φ)) ≪≫
      PreservesKernel.iso P φ).symm)

/-- Over a left Noetherian ring `Λ`, the kernel of a morphism between sheaves constructible on `U`
is constructible on `U`. -/
theorem IsConstructibleOn.kernel [IsNoetherianRing Λ] (hF : F.IsConstructibleOn U)
    (hG : G.IsConstructibleOn U) (φ : F ⟶ G) : (Limits.kernel φ).IsConstructibleOn U :=
  (hF.of_isLimit_kernelFork (kernelIsKernel φ) hG :)

/-- Over a left Noetherian ring `Λ`, the middle term of a short exact sequence of étale sheaves of
`Λ`-modules is constructible on `U` when both outer terms are constructible on `U`. -/
theorem IsConstructibleOn.of_shortExact [IsNoetherianRing Λ]
    {T : ShortComplex (Sheaf (smallEtaleTopology X) (ModuleCat.{u} Λ))} (hT : T.ShortExact)
    (h₁ : T.X₁.IsConstructibleOn U) (h₃ : T.X₃.IsConstructibleOn U) :
    T.X₂.IsConstructibleOn U := by
  obtain ⟨S₁, hS₁⟩ := isConstructibleOn_iff.mp h₁
  obtain ⟨S₃, hS₃⟩ := isConstructibleOn_iff.mp h₃
  refine isConstructibleOn_iff.mpr ⟨S₁.inf S₃, fun p ↦ ?_⟩
  exact IsFiniteLisse.of_shortExact (Hom.shortExact_map_smallEtalePullback ((S₁.inf S₃).f p) hT)
    ((S₁.inf_refines_left S₃).isFiniteLisse hS₁ p)
    ((S₁.inf_refines_right S₃).isFiniteLisse hS₃ p)

end CategoryTheory.Sheaf

namespace AlgebraicGeometry.Scheme

open CategoryTheory.Sheaf

variable {X : Scheme.{u}} {Λ : Type u} [Ring Λ]

/-- Over any ring `Λ`, constructible étale sheaves of `Λ`-modules on `X` are closed under
cokernels. -/
instance isClosedUnderCokernels_constructibleSheaf :
    (X.constructibleSheaf Λ).IsClosedUnderCokernels where
  cokernels_le := by
    rintro _ ⟨φ, k, hk, hF, hG⟩
    exact constructibleSheaf_iff.mpr fun U hU ↦
      (constructibleSheaf_iff.mp hF U hU).of_isColimit_cokernelCofork hk
        (constructibleSheaf_iff.mp hG U hU)

/-- Over a left Noetherian ring `Λ`, constructible étale sheaves of `Λ`-modules on `X` are closed
under kernels. -/
instance isClosedUnderKernels_constructibleSheaf [IsNoetherianRing Λ] :
    (X.constructibleSheaf Λ).IsClosedUnderKernels where
  kernels_le := by
    rintro _ ⟨φ, k, hk, hF, hG⟩
    exact constructibleSheaf_iff.mpr fun U hU ↦
      (constructibleSheaf_iff.mp hF U hU).of_isLimit_kernelFork hk
        (constructibleSheaf_iff.mp hG U hU)

/-- Over a left Noetherian ring `Λ`, constructible étale sheaves of `Λ`-modules on `X` are closed
under extensions. -/
instance isClosedUnderExtensions_constructibleSheaf [IsNoetherianRing Λ] :
    (X.constructibleSheaf Λ).IsClosedUnderExtensions where
  prop_X₂_of_shortExact hT h₁ h₃ :=
    constructibleSheaf_iff.mpr fun U hU ↦
      (constructibleSheaf_iff.mp h₁ U hU).of_shortExact hT (constructibleSheaf_iff.mp h₃ U hU)

example (X : Scheme.{u}) (Λ : Type u) [Ring Λ] [IsNoetherianRing Λ]
    [HasDerivedCategory.{w} (Sheaf (smallEtaleTopology X) (ModuleCat.{u} Λ))] :
    (DerivedCategory.homologyIn (X.constructibleSheaf Λ)).IsTriangulated :=
  inferInstance

end AlgebraicGeometry.Scheme
