/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Category.ModuleCat.DerivationExtension.BaerSum
public import TauCeti.Algebra.Category.ModuleCat.DerivationExtension.Scalar
public import Mathlib.Algebra.Homology.DerivedCategory.Ext.Linear

/-!
# The extension class map of continuous outer derivations

Let `A` be a topological `R`-algebra and `M` a discrete `A`-module. Every continuous derivation
`δ` of `A` gives the self-extension `0 → M → E_δ(M) → M → 0` and hence a class in `Ext¹(M, M)`,
computed in the abelian category of discrete `A`-modules
(`TauCeti.DerivationExtension.extClass`). This file assembles these classes into an `R`-linear
map out of the continuous outer derivations,

`OutDer_cont(A) →ₗ[R] Ext¹(M, M)`, `[δ] ↦ [E_δ(M)]`.

The category of `A`-modules is `R`-linear, with `r` acting on a module through `algebraMap R A r`,
so `Ext¹(M, M)` is an `R`-module. Scaling a derivation by `r ∈ R` is multiplication by the
central element `algebraMap R A r`, so the class of `E_(r • δ)(M)` is `r` times the class of
`E_δ(M)`. Together with additivity (`TauCeti.DerivationExtension.extClass_add`) this makes the
class map `R`-linear on continuous derivations, and invariance under an inner change
(`TauCeti.DerivationExtension.extClass_eq_of_inner`) makes it descend to the quotient
`TauCeti.ContinuousOuterDerivation R A` by the inner derivations. The descended map is natural in
`M`: pushforward of the class along a module map equals pullback of the class of the target.

These classes are the first-order deformations of `M` in the directions of the outer derivations
of `A`. For the completed enveloping algebra at the critical level, they are the infinitesimal
deformations of modules in Frenkel's local categories.

## Main definitions

* `TauCeti.DerivationExtension.extClassHom M`: `δ ↦ [E_δ(M)]`, as an `R`-linear map from the
  continuous derivations to `Ext¹(M, M)`.
* `TauCeti.DerivationExtension.outerExtClass M`: the induced `R`-linear map from the continuous
  outer derivations to `Ext¹(M, M)`.

## Main results

* `TauCeti.DerivationExtension.extClass_smul`: the class of `E_(r • δ)(M)` is `r` times the class
  of `E_δ(M)`.
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

-- Only the `R`-linear structure of `ModuleCat A` is needed: opening `ModuleCat.Algebra` would also
-- make every `A`-module, including `A` itself, an `R`-module through `algebraMap`.
attribute [local instance] ModuleCat.Algebra.instLinear

universe u w

variable {R : Type*} [CommRing R] {A : Type u} [Ring A] [Algebra R A] [TopologicalSpace A]

section Smul

variable [SeparatelyContinuousAdd A] [SeparatelyContinuousMul A]

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
  have hscalar : ObjectProperty.homMk
      (ModuleCat.ofHom (Module.End.smulLeft (z : A) z.property)) = r • 𝟙 M := by
    ext m
    -- `r` acts on a module through `algebraMap R A r`, by definition of the `R`-linear structure
    -- `ModuleCat.Algebra.instLinear`.
    rfl
  rw [← extClass_eq_of_inner (derivationLieAlgebra.continuous_center_smul z hδ) hrδ 0 hz,
    Ext.smul_eq_comp_mk₀, ← hscalar, extClass_def, extClass_def]
  exact extClass_center_smul z δ hδ M

end Smul

section Outer

variable [IsTopologicalAddGroup A] [SeparatelyContinuousMul A] [ContinuousConstSMul R A]

open continuousDerivationLieAlgebra (continuous)

/-- The `R`-linear structure of the category of discrete modules, fixed once for this section so
that every `R`-module structure on `Ext` below is elaborated through the same term. -/
noncomputable local instance : Linear R (discreteModules.{max u w} A).FullSubcategory :=
  Linear.fullSubcategory _

variable (R) in
/-- The extension class of the self-extension `E_δ(M)` of a discrete module `M`, as an `R`-linear
map `δ ↦ [E_δ(M)]` from the continuous derivations to `Ext¹(M, M)`. -/
noncomputable def extClassHom (M : (discreteModules.{max u w} A).FullSubcategory) :
    continuousDerivationLieAlgebra R A →ₗ[R] Ext.{max u w} M M 1 where
  toFun D := extClass (continuous D) M
  map_add' D E := extClass_add (continuous D) (continuous E) (continuous (D + E)) M
  map_smul' r D := by
    rw [RingHom.id_apply, ← extClass_smul r (continuous D) (continuous (r • D)) M]

/-- The class map evaluates to the extension class of the self-extension. -/
@[simp]
theorem extClassHom_apply (M : (discreteModules.{max u w} A).FullSubcategory)
    (D : continuousDerivationLieAlgebra R A) :
    extClassHom R M D = extClass (continuous D) M :=
  (rfl)

/-- The inner derivations lie in the kernel of the class map. -/
private theorem idealRange_le_ker_extClassHom
    (M : (discreteModules.{max u w} A).FullSubcategory) :
    (continuousInnerDerivation R :
      A →ₗ⁅R⁆ continuousDerivationLieAlgebra R A).idealRange.toSubmodule ≤
        LinearMap.ker (extClassHom R M) :=
  IsConcreteLE.le_iff.mpr fun D hD => by
    obtain ⟨b, rfl⟩ := mem_continuousInnerDerivation_idealRange_iff.mp hD
    simp

variable (R) in
/-- **The extension class map of continuous outer derivations**: the `R`-linear map
`OutDer_cont(A) → Ext¹(M, M)` sending the outer class of a continuous derivation `δ` to the class
of the self-extension `E_δ(M)` in the category of discrete modules. It is well defined because an
inner change `δ ↦ δ + ad b` does not change the class. -/
noncomputable def outerExtClass (M : (discreteModules.{max u w} A).FullSubcategory) :
    ContinuousOuterDerivation R A →ₗ[R] Ext.{max u w} M M 1 :=
  (continuousInnerDerivation R :
      A →ₗ⁅R⁆ continuousDerivationLieAlgebra R A).idealRange.toSubmodule.liftQ
    (extClassHom R M) (idealRange_le_ker_extClassHom M)

/-- The class map sends the outer class of a continuous derivation `δ` to the class of the
self-extension `E_δ(M)`. -/
@[simp]
theorem outerExtClass_mk (M : (discreteModules.{max u w} A).FullSubcategory)
    (D : continuousDerivationLieAlgebra R A) :
    outerExtClass R M (Submodule.Quotient.mk D) = extClass (continuous D) M :=
  Submodule.liftQ_apply _ _ _

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
