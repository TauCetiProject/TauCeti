/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Category.ModuleCat.DerivationExtension.BaerSum
public import TauCeti.Algebra.Category.ModuleCat.DerivationExtension.Scalar
public import TauCeti.Algebra.Subalgebra.Center
public import Mathlib.Algebra.Homology.DerivedCategory.Ext.Linear

/-!
# The extension class map of continuous outer derivations

Let `A` be a topological `R`-algebra and `M` a discrete `A`-module. Every continuous derivation
`δ` of `A` gives the self-extension `0 → M → E_δ(M) → M → 0` and hence a class in `Ext¹(M, M)`,
computed in the abelian category of discrete `A`-modules
(`TauCeti.DerivationExtension.extClass`). This file assembles these classes into a center-linear
map out of the continuous outer derivations,

`OutDer_cont(A) →ₗ[Z(A)] Ext¹(M, M)`, `[δ] ↦ [E_δ(M)]`.

The category of `A`-modules is `R`-linear, with `r` acting on a module through `algebraMap R A r`,
so `Ext¹(M, M)` is an `R`-module. Scaling a derivation by `r ∈ R` is multiplication by the
central element `algebraMap R A r`, so the class of `E_(r • δ)(M)` is `r` times the class of
`E_δ(M)`. Together with additivity (`TauCeti.DerivationExtension.extClass_add`) this makes the
class map `R`-linear on continuous derivations, and invariance under an inner change
(`TauCeti.DerivationExtension.extClass_eq_of_inner`) makes it descend to the quotient
`TauCeti.ContinuousOuterDerivation R A` by the inner derivations. In fact both maps are
linear over the whole algebraic center `Z(A) = Subalgebra.center R A`: the center acts on the
category of discrete modules through its canonical inclusion into `A`, and the pushforward
formula `extClass_center_smul` identifies this action on Ext with scaling derivations.
No central coefficient is required to be invertible or to belong to the base ring.
The descended map is natural in `M`: pushforward of the class along a module map equals
pullback of the class of the target.

These classes are the first-order deformations of `M` in the directions of the outer derivations
of `A`. For the completed enveloping algebra at the critical level, they are the infinitesimal
deformations of modules in Frenkel's local categories.

## Main definitions

* `TauCeti.DerivationExtension.extClassHom M`: `δ ↦ [E_δ(M)]`, as a center-linear map from the
  continuous derivations to `Ext¹(M, M)`.
* `TauCeti.DerivationExtension.outerExtClass M`: the induced center-linear map from the continuous
  outer derivations to `Ext¹(M, M)`.

## Main results

* `TauCeti.DerivationExtension.extClass_center_smul'`: central scaling of a derivation scales
  its extension class by the same element of the center.
* `TauCeti.DerivationExtension.extClass_smul`: the base-ring specialization of this identity.
* `TauCeti.DerivationExtension.outerExtClass_mk`: the class map sends the outer class of `δ` to
  the class of `E_δ(M)`.
* `TauCeti.DerivationExtension.outerExtClass_naturality`: naturality of the class map in `M`.

## References

* Edward Frenkel, *Langlands Correspondence for Loop Groups*, Cambridge Studies in Advanced
  Mathematics 103, Cambridge University Press, 2007, for first-order deformations of modules
  over the completed enveloping algebra at the critical level.
-/

public section

namespace TauCeti.DerivationExtension

open CategoryTheory CategoryTheory.Abelian

attribute [local instance 100] LieRing.ofAssociativeRing

-- Only the scalar-linear structures of `ModuleCat A` are needed: opening `ModuleCat.Algebra`
-- would also install restricted scalar module structures on every `A`-module, including `A`.
attribute [local instance] ModuleCat.Algebra.instLinear

universe u w

variable {R : Type*} [CommRing R] {A : Type u} [Ring A] [Algebra R A] [TopologicalSpace A]

/-- The center-linear structure on discrete modules, using the canonical center algebra. -/
noncomputable local instance :
    Linear (Subalgebra.center R A) (discreteModules.{max u w} A).FullSubcategory :=
  Linear.fullSubcategory _

/-- A central scalar times the identity is the endomorphism given by central multiplication. -/
theorem center_smul_id_eq_homMk_smulLeft (z : Subalgebra.center R A)
    (M : (discreteModules.{max u w} A).FullSubcategory) :
    z • 𝟙 M = ObjectProperty.homMk
      (ModuleCat.ofHom (Module.End.smulLeft (z : A) z.property)) := by
  apply ObjectProperty.hom_ext
  ext m
  -- The restricted ModuleCat action uses the center's structure map, namely inclusion into A.
  change (z : A) • m = Module.End.smulLeft (z : A) z.property m
  exact (Module.End.smulLeft_apply (z : A) z.property m).symm

section Smul

variable [SeparatelyContinuousAdd A]

/-- Central scaling on Ext is pushforward along central multiplication on the target. -/
theorem center_smul_ext_eq_comp_mk₀ (z : Subalgebra.center R A)
    {M N : (discreteModules.{max u w} A).FullSubcategory} {n : ℕ}
    (e : Ext.{max u w} M N n) :
    z • e = e.comp (Ext.mk₀ (ObjectProperty.homMk
      (ModuleCat.ofHom (Module.End.smulLeft (z : A) z.property)))) (add_zero n) := by
  rw [Ext.smul_eq_comp_mk₀, center_smul_id_eq_homMk_smulLeft]

variable [SeparatelyContinuousMul A]

/-- The extension class of a centrally scaled continuous derivation is the corresponding
central multiple of its extension class. -/
theorem extClass_center_smul' (z : Subalgebra.center R A) {δ : derivationLieAlgebra R A}
    (hδ : Continuous (δ : Module.End R A))
    (M : (discreteModules.{max u w} A).FullSubcategory) :
    extClass (derivationLieAlgebra.continuous_center_smul z hδ) M = z • extClass hδ M := by
  rw [center_smul_ext_eq_comp_mk₀, extClass_def, extClass_def]
  exact extClass_center_smul z δ hδ M

/-- **The extension class is `R`-linear in the derivation**: the class of the self-extension
along `r • δ` is `r` times the class along `δ`, for the `R`-module structure on `Ext` coming from
the `R`-linear category of discrete `A`-modules. Continuity of `r • δ` is a separate hypothesis,
since scalar multiplication on `A` is not assumed continuous. -/
theorem extClass_smul (r : R) {δ : derivationLieAlgebra R A}
    (hδ : Continuous (δ : Module.End R A))
    (hrδ : Continuous ((r • δ : derivationLieAlgebra R A) : Module.End R A))
    (M : (discreteModules.{max u w} A).FullSubcategory) :
    extClass hrδ M = r • extClass hδ M := by
  let z : Subalgebra.center R A := ⟨algebraMap R A r, Subalgebra.algebraMap_mem _ r⟩
  have hz : r • δ = z • δ + innerDerivation R 0 := by
    ext a
    simp [z, Algebra.smul_def]
  have hscalar : z • 𝟙 M = r • 𝟙 M := by
    ext m
    -- Both scalar actions use the same element algebraMap R A r on the target module.
    rfl
  rw [← extClass_eq_of_inner (derivationLieAlgebra.continuous_center_smul z hδ) hrδ 0 hz,
    extClass_center_smul' z hδ M,
    Ext.smul_eq_comp_mk₀, Ext.smul_eq_comp_mk₀, hscalar]

end Smul

section Outer

variable [IsTopologicalAddGroup A] [SeparatelyContinuousMul A] [ContinuousConstSMul R A]

open continuousDerivationLieAlgebra (continuous)

/-- The `R`-linear structure of the category of discrete modules, fixed once for this section so
that every `R`-module structure on `Ext` below is elaborated through the same term. -/
noncomputable local instance : Linear R (discreteModules.{max u w} A).FullSubcategory :=
  Linear.fullSubcategory _

variable (R) in
/-- The extension class of the self-extension `E_δ(M)` of a discrete module `M`, as a center-linear
map `δ ↦ [E_δ(M)]` from the continuous derivations to `Ext¹(M, M)`. -/
noncomputable def extClassHom (M : (discreteModules.{max u w} A).FullSubcategory) :
    continuousDerivationLieAlgebra R A →ₗ[Subalgebra.center R A] Ext.{max u w} M M 1 where
  toFun D := extClass (continuous D) M
  map_add' D E := extClass_add (continuous D) (continuous E) (continuous (D + E)) M
  map_smul' z D := by
    -- Expose the underlying derivation and the continuity witness stored by the center action.
    change extClass (derivationLieAlgebra.continuous_center_smul z (continuous D)) M =
      z • extClass (continuous D) M
    exact extClass_center_smul' z (continuous D) M

/-- The class map evaluates to the extension class of the self-extension. -/
@[simp]
theorem extClassHom_apply (M : (discreteModules.{max u w} A).FullSubcategory)
    (D : continuousDerivationLieAlgebra R A) :
    extClassHom R M D = extClass (continuous D) M :=
  (rfl)

-- The existing Lie-ideal quotient is over R, so its liftQ needs the base-ring linear map.
private noncomputable def extClassHomBase (M : (discreteModules.{max u w} A).FullSubcategory) :
    continuousDerivationLieAlgebra R A →ₗ[R] Ext.{max u w} M M 1 :=
  { (extClassHom R M).toAddMonoidHom with
    map_smul' := fun r D => extClass_smul r (continuous D) (continuous (r • D)) M }

/-- The inner derivations lie in the kernel of the base-ring class map. -/
private theorem idealRange_le_ker_extClassHom
    (M : (discreteModules.{max u w} A).FullSubcategory) :
    (continuousInnerDerivation R :
      A →ₗ⁅R⁆ continuousDerivationLieAlgebra R A).idealRange.toSubmodule ≤
        LinearMap.ker (extClassHomBase M) :=
  IsConcreteLE.le_iff.mpr fun D hD => by
    obtain ⟨b, rfl⟩ := mem_continuousInnerDerivation_idealRange_iff.mp hD
    simp [extClassHomBase]

private noncomputable def outerExtClassBase
    (M : (discreteModules.{max u w} A).FullSubcategory) :
    ContinuousOuterDerivation R A →ₗ[R] Ext.{max u w} M M 1 :=
  (continuousInnerDerivation R :
    A →ₗ⁅R⁆ continuousDerivationLieAlgebra R A).idealRange.toSubmodule.liftQ
      (extClassHomBase M) (idealRange_le_ker_extClassHom M)

private theorem outerExtClassBase_apply
    (M : (discreteModules.{max u w} A).FullSubcategory)
    (D : continuousDerivationLieAlgebra R A) :
    outerExtClassBase M (Submodule.Quotient.mk D) = extClassHom R M D :=
  Submodule.liftQ_apply
    (continuousInnerDerivation R :
      A →ₗ⁅R⁆ continuousDerivationLieAlgebra R A).idealRange.toSubmodule
    (extClassHomBase M) D

private theorem outerExtClassBase_center_smul
    (M : (discreteModules.{max u w} A).FullSubcategory)
    (z : Subalgebra.center R A) (x : ContinuousOuterDerivation R A) :
    outerExtClassBase M (z • x) = z • outerExtClassBase M x := by
  obtain ⟨D, rfl⟩ := LieIdeal.surjective_mkQ
    (continuousInnerDerivation R :
      A →ₗ⁅R⁆ continuousDerivationLieAlgebra R A).idealRange x
  rw [← ContinuousOuterDerivation.mkQ_center_smul]
  -- Present the Lie quotient map as the submodule constructor used by liftQ_apply.
  change outerExtClassBase M (Submodule.Quotient.mk (z • D)) =
    z • outerExtClassBase M (Submodule.Quotient.mk D)
  rw [outerExtClassBase_apply, outerExtClassBase_apply]
  exact (extClassHom R M).map_smul z D

variable (R) in
/-- **The extension class map of continuous outer derivations**: the center-linear map
`OutDer_cont(A) → Ext¹(M, M)` sending the outer class of a continuous derivation `δ` to the class
of the self-extension `E_δ(M)` in the category of discrete modules. It is well defined because an
inner change `δ ↦ δ + ad b` does not change the class. The center acts on Ext through its
canonical scalar action on the category of discrete modules. -/
noncomputable def outerExtClass (M : (discreteModules.{max u w} A).FullSubcategory) :
    ContinuousOuterDerivation R A →ₗ[Subalgebra.center R A] Ext.{max u w} M M 1 :=
  { (outerExtClassBase M).toAddMonoidHom with
    map_smul' := outerExtClassBase_center_smul M }

/-- The class map sends the outer class of a continuous derivation `δ` to the class of the
self-extension `E_δ(M)`. -/
@[simp]
theorem outerExtClass_mk (M : (discreteModules.{max u w} A).FullSubcategory)
    (D : continuousDerivationLieAlgebra R A) :
    outerExtClass R M (Submodule.Quotient.mk D) = extClass (continuous D) M :=
  outerExtClassBase_apply M D

/-- **Naturality of the outer class map**: for a map `f : M ⟶ N` of discrete modules and a
continuous outer derivation `x`, pushforward along `f` of the class of `x` for `M` equals pullback
along `f` of the class of `x` for `N`, in `Ext¹(M, N)`. -/
theorem outerExtClass_naturality {M N : (discreteModules.{max u w} A).FullSubcategory}
    (f : M ⟶ N) (x : ContinuousOuterDerivation R A) :
    (outerExtClass R M x).comp (Ext.mk₀ f) (add_zero 1) =
      (Ext.mk₀ f).comp (outerExtClass R N x) (zero_add 1) := by
  obtain ⟨D, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  simpa only [outerExtClass_mk] using extClass_naturality (continuous D) f

end Outer

end TauCeti.DerivationExtension
