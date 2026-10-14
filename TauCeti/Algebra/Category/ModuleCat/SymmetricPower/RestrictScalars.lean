/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Category.ModuleCat.SymmetricPower.Basic
public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings

/-!
# Symmetric powers and restriction of scalars

Let `f : S →+* R` be a morphism of commutative rings and `M` an `R`-module. Restriction of
scalars has a natural symmetric-power comparison `Symⁿ_S M ⟶ Symⁿ_R M`, sending a product
`m₁ ⋯ mₙ` of elements of `M` over `S` to the same product over `R`. It is the restriction to
degree-`n` parts of the ring homomorphism of symmetric algebras `SymmetricAlgebra.mapₛₗ` induced
by the identity of `M`, viewed as an `f`-semilinear map. It need not be an isomorphism. This
supplies the sectionwise maps for symmetric powers of pushforwards of module presheaves, in the
same way as `TauCeti.ModuleCat.restrictScalarsExteriorPowerComparison` does for exterior powers.
-/

public section

open CategoryTheory

namespace TauCeti.ModuleCat

open TauCeti.SymmetricAlgebra (homogeneousSubmoduleMapₛₗ)

universe u v w

noncomputable section

variable {S : Type u} {R : Type v} [CommRing S] [CommRing R] (f : S →+* R)

private def restrictScalarsSymmetricPowerApp (n : ℕ) (M : ModuleCat.{max u v w} R) :
    ((ModuleCat.restrictScalars f).obj M).symmetricPower n ⟶
      (ModuleCat.restrictScalars f).obj (M.symmetricPower n) :=
  ModuleCat.semilinearMapAddEquiv f _ _
    (homogeneousSubmoduleMapₛₗ ((ModuleCat.semilinearMapAddEquiv f _ M).symm (𝟙 _)) n)

private lemma coe_restrictScalarsSymmetricPowerApp_apply (n : ℕ) (M : ModuleCat.{max u v w} R)
    (x : ((ModuleCat.restrictScalars f).obj M).symmetricPower n) :
    Subtype.val (restrictScalarsSymmetricPowerApp f n M x) =
      SymmetricAlgebra.mapₛₗ ((ModuleCat.semilinearMapAddEquiv f _ M).symm (𝟙 _)) x.1 :=
  TauCeti.SymmetricAlgebra.coe_homogeneousSubmoduleMapₛₗ_apply _ n x

/-- Restriction of scalars carries the natural symmetric-power comparison, changing the
coefficient ring of a product of elements without changing its factors. -/
def restrictScalarsSymmetricPowerComparison (n : ℕ) :
    ModuleCat.restrictScalars.{max u v w} f ⋙ ModuleCat.symmetricPower.functor S n ⟶
      ModuleCat.symmetricPower.functor R n ⋙ ModuleCat.restrictScalars f where
  app := restrictScalarsSymmetricPowerApp f n
  naturality {M N} φ := by
    -- Both composites are restrictions of the ring homomorphism of symmetric algebras induced by
    -- `φ`, viewed as an `f`-semilinear map; ring homomorphisms out of a symmetric algebra are
    -- determined by their values on scalars and on generators.
    have key : (SymmetricAlgebra.mapₛₗ ((ModuleCat.semilinearMapAddEquiv f _ N).symm (𝟙 _))).comp
        (SymmetricAlgebra.map S ((ModuleCat.restrictScalars f).map φ).hom : _ →+* _) =
        (SymmetricAlgebra.map R φ.hom : _ →+* _).comp
          (SymmetricAlgebra.mapₛₗ ((ModuleCat.semilinearMapAddEquiv f _ M).symm (𝟙 _))) :=
      SymmetricAlgebra.ringHom_ext (by ext r; simp) fun m ↦ by
        -- Restriction of scalars gives `M` and `N` second module structures with the same
        -- carriers, so `simp` cannot match the generator formulas; apply them explicitly.
        rw [RingHom.comp_apply, RingHom.comp_apply, RingHom.coe_coe,
          SymmetricAlgebra.map_apply_ι, SymmetricAlgebra.mapₛₗ_ι, SymmetricAlgebra.mapₛₗ_ι]
        exact (SymmetricAlgebra.map_apply_ι R φ.hom m).symm
    ext x
    apply Subtype.ext
    exact (coe_restrictScalarsSymmetricPowerApp_apply f n N _).trans
      ((congrArg _ (ModuleCat.symmetricPower.coe_map_apply _ n x)).trans
        ((RingHom.congr_fun key x.1).trans
          ((congrArg (SymmetricAlgebra.map R φ.hom)
            (coe_restrictScalarsSymmetricPowerApp_apply f n M x).symm).trans
              (ModuleCat.symmetricPower.coe_map_apply φ n _).symm)))

/-- The restriction-of-scalars comparison is computed in the symmetric algebra by the ring
homomorphism induced by the identity of `M`, viewed as an `f`-semilinear map; it sends the
generator of `m` over `S` to the generator of `m` over `R` (`SymmetricAlgebra.mapₛₗ_ι`). -/
-- Explicit objects keep the coercion to a function in simp normal form.
@[simp]
theorem coe_restrictScalarsSymmetricPowerComparison_app_apply (n : ℕ)
    (M : ModuleCat.{max u v w} R) (x : ((ModuleCat.restrictScalars f).obj M).symmetricPower n) :
    Subtype.val (ConcreteCategory.hom
      (X := ((ModuleCat.restrictScalars f).obj M).symmetricPower n)
      (Y := (ModuleCat.restrictScalars f).obj (M.symmetricPower n))
      ((restrictScalarsSymmetricPowerComparison f n).app M) x) =
      SymmetricAlgebra.mapₛₗ ((ModuleCat.semilinearMapAddEquiv f _ M).symm (𝟙 _)) x.1 :=
  coe_restrictScalarsSymmetricPowerApp_apply f n M x

end

end TauCeti.ModuleCat
