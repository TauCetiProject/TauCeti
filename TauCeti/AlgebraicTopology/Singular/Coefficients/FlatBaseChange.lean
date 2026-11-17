/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Descent
public import Mathlib.RingTheory.Flat.Localization
public import TauCeti.Algebra.Category.ModuleCat.ChangeOfRings
public import TauCeti.Algebra.Module.Torsion.Localization
public import TauCeti.AlgebraicTopology.Singular.Coefficients.MapCoefficients
public import TauCeti.AlgebraicTopology.Singular.ModuleChains.Basic

/-!
# Flat base change in singular homology

Let `S` be a flat `R`-algebra. Extension of scalars `M ↦ S ⊗[R] M` is then an exact functor
from `R`-modules to `S`-modules which preserves coproducts, so it commutes with singular homology:

`S ⊗[R] Hₙ(X; R) ≅ Hₙ(X; S)`

(`TauCeti.singularHomologyTensorIso`). This is the universal coefficient theorem for flat
coefficients, where the `Tor` term vanishes.

The main example is a localization `S = M⁻¹R` of `R` at a submonoid `M`, for instance
`ℚ = (ℤ ∖ 0)⁻¹ℤ` or `ℤ[1/d]`. Since `M⁻¹R ⊗[R] N` vanishes exactly when every element of `N` is
killed by an element of `M`, the homology with coefficients in `M⁻¹R` vanishes in a degree exactly
when the homology with coefficients in `R` is `M`-torsion there
(`TauCeti.isTorsion'_singularChains_homology_iff`). For `R = ℤ` and `S = ℚ`: the rational homology
of a space vanishes in a degree exactly when its integral homology is a torsion group there
(`TauCeti.isAddTorsion_singularChains_homology_iff`).

## Main declarations

* `TauCeti.singularHomologyTensorIso`: `S ⊗[R] Hₙ(X; R) ≅ Hₙ(X; S)` for a flat `R`-algebra `S`.
* `TauCeti.isTorsion'_singularChains_homology_iff`: `Hₙ(X; R)` is `M`-torsion exactly when
  `Hₙ(X; M⁻¹R)` vanishes; `TauCeti.isTorsion'_singularChains_int_homology_iff` is the case
  `R = ℤ`.
* `TauCeti.isAddTorsion_singularChains_homology_iff`: `Hₙ(X; ℤ)` is a torsion group exactly when
  `Hₙ(X; ℚ)` vanishes.

## References

* A. Hatcher, *Algebraic Topology*, Cambridge University Press, 2002, Section 3.A.
-/

public section

noncomputable section

open CategoryTheory Limits AlgebraicTopology TensorProduct

universe u

namespace TauCeti

variable (R S : Type u) [CommRing R] [CommRing S] [Algebra R S]

/-- Extension of scalars along `algebraMap R S` carries the ring `R` to the ring `S`. -/
private def extendScalarsObjSelfIso :
    (ModuleCat.extendScalars.{u, u, u} (algebraMap R S)).obj (ModuleCat.of R R) ≅
      ModuleCat.of S S :=
  ModuleCat.extendScalarsAlgebraMapIso _ ≪≫ (AlgebraTensorModule.rid R S S).toModuleIso

/-- **Flat base change in singular homology.** For a flat `R`-algebra `S`, singular homology with
coefficients in `S` is the extension of scalars of singular homology with coefficients in `R`:
`S ⊗[R] Hₙ(X; R) ≅ Hₙ(X; S)`, as `S`-modules. -/
def singularHomologyTensorIso [Module.Flat R S] (X : TopCat.{u}) (n : ℕ) :
    ModuleCat.of S (S ⊗[R] ((singularChains R).obj X).homology n) ≅
      ((singularChains S).obj X).homology n :=
  have : PreservesFiniteLimits (ModuleCat.extendScalars.{u, u, u} (algebraMap R S)) :=
    ModuleCat.preservesFiniteLimits_extendScalars_of_flat
      (RingHom.flat_algebraMap_iff.2 inferInstance)
  -- An exact functor of abelian categories preserves homology.
  have : (ModuleCat.extendScalars.{u, u, u} (algebraMap R S)).PreservesHomology := {}
  (ModuleCat.extendScalarsAlgebraMapIso _).symm ≪≫
    (Functor.singularHomologyFunctorObjCompIso
      (ModuleCat.extendScalars.{u, u, u} (algebraMap R S)) (ModuleCat.of R R) n).app X ≪≫
    ((singularHomologyFunctor (ModuleCat.{u} S) n).mapIso (extendScalarsObjSelfIso R S)).app X

/-- For a flat `R`-algebra `S`, the homology with coefficients in `S` vanishes exactly when the
extension of scalars of the homology with coefficients in `R` does. -/
theorem subsingleton_singularChains_homology_iff_tensorProduct [Module.Flat R S]
    (X : TopCat.{u}) (n : ℕ) :
    Subsingleton (((singularChains S).obj X).homology n) ↔
      Subsingleton (S ⊗[R] ((singularChains R).obj X).homology n) :=
  (singularHomologyTensorIso R S X n).toLinearEquiv.toEquiv.subsingleton_congr.symm

/-- **Homology with localized coefficients detects torsion.** For a localization `S` of `R` at a
submonoid `M`, the singular homology `Hₙ(X; R)` is `M`-torsion, every class being killed by an
element of `M`, exactly when `Hₙ(X; S)` vanishes. -/
theorem isTorsion'_singularChains_homology_iff (M : Submonoid R) [IsLocalization M S]
    (X : TopCat.{u}) (n : ℕ) :
    Module.IsTorsion' (((singularChains R).obj X).homology n) M ↔
      Subsingleton (((singularChains S).obj X).homology n) := by
  have := IsLocalization.flat S M
  rw [subsingleton_singularChains_homology_iff_tensorProduct R S]
  exact M.isTorsion'_iff_subsingleton_tensorProduct S

/-- The case `R = ℤ` of `TauCeti.isTorsion'_singularChains_homology_iff`, for the canonical action
of `ℤ` on the abelian group `Hₙ(X; ℤ)`: for a localization `k` of `ℤ` at a submonoid `S`, every
class of `Hₙ(X; ℤ)` is killed by an element of `S` exactly when `Hₙ(X; k)` vanishes. -/
theorem isTorsion'_singularChains_int_homology_iff (S : Submonoid ℤ) (k : Type) [CommRing k]
    [Algebra ℤ k] [IsLocalization S k] (X : TopCat.{0}) (n : ℕ) :
    Module.IsTorsion' (((singularChains ℤ).obj X).homology n) S ↔
      Subsingleton (((singularChains k).obj X).homology n) := by
  rw [← isTorsion'_singularChains_homology_iff ℤ k S X n]
  -- The scalar action of `ℤ` from `ModuleCat ℤ` is the canonical action of the abelian group.
  exact ⟨fun h x ↦ (@h x).imp fun _ ha ↦ (int_smul_eq_zsmul _ _ _).trans ha,
    fun h x ↦ (@h x).imp fun _ ha ↦ (int_smul_eq_zsmul _ _ _).symm.trans ha⟩

/-- **Rational homology detects torsion in integral homology.** The integral singular homology
`Hₙ(X; ℤ)` of a space in the lowest universe is a torsion group exactly when its rational homology
`Hₙ(X; ℚ)` vanishes. -/
theorem isAddTorsion_singularChains_homology_iff (X : TopCat.{0}) (n : ℕ) :
    IsAddTorsion (((singularChains ℤ).obj X).homology n) ↔
      Subsingleton (((singularChains ℚ).obj X).homology n) := by
  have := IsLocalization.flat ℚ (nonZeroDivisors ℤ)
  rw [isAddTorsion_iff_subsingleton_rat_tensorProduct,
    subsingleton_singularChains_homology_iff_tensorProduct ℤ ℚ]
  -- The two sides use the canonical `ℤ`-module structure of an abelian group and the one of
  -- `ModuleCat ℤ`, which agree since `ℤ`-module structures are unique.
  convert Iff.rfl
  exact Subsingleton.elim _ _

end TauCeti
