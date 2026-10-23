/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.EulerCharacteristic.ExtEuler.Descent
public import TauCeti.Algebra.Homology.EulerCharacteristic.ExtEuler.FiniteLength
public import TauCeti.RepresentationTheory.GrothendieckGroup.Quiver.DimensionVector
public import TauCeti.RepresentationTheory.GrothendieckGroup.Quiver.SimpleBasis
public import TauCeti.RepresentationTheory.Quiver.Representation.Projective.Simple.ExtEuler

/-!
# The Ext-Euler pairing of a finite acyclic quiver is the Ringel form

Let `Q` be a finite quiver whose path algebra `kQ` is finite-dimensional, that is, a finite
acyclic quiver. Its simple modules are the vertex simples, each of which has a projective
resolution of length one, so every pair of finitely generated `kQ`-modules is Euler-admissible: no
Ext group above degree one survives, and every Hom and Ext group is finite-dimensional. The
categorical Ext-Euler pairing on the Grothendieck group of finitely generated modules therefore
exists, and it is the Ringel form of the dimension vectors,

`χ(M, N) = ∑ᵢ dim Mᵢ dim Nᵢ - ∑_{a : i ⟶ j} dim Mᵢ dim Nⱼ`.

Both sides are biadditive and the simple classes span, so the identity follows from the vertex
simple computation. Its symmetrization is the polarized Tits form; the raw pairing need not be
symmetric.

## Main results

* `TauCeti.isEulerAdmissibleOn_isFG_pathAlgebra`: every pair of finitely generated modules over
  a finite-dimensional path algebra is Euler-admissible.
* `TauCeti.extEulerPairing_eq_pathAlgebraEulerPairingK0`: the Ext-Euler pairing on `G₀(mod kQ)` is
  the Ringel form pulled back along dimension vectors.
* `TauCeti.extEuler_eq_eulerForm_dimVector`: the object-level Ext-Euler characteristic of two
  finitely generated modules is the Ringel form of their dimension vectors.
* `TauCeti.extEulerPairing_add_flip_eq_titsPolarForm`: the symmetrized Ext-Euler pairing is
  the polarized Tits form of the dimension vectors.

## References

* Ibrahim Assem, Daniel Simson, and Andrzej Skowroński, *Elements of the Representation Theory
  of Associative Algebras I*, Chapter III, Section 3, in particular Proposition 3.13.
-/

public section

namespace TauCeti

open CategoryTheory
open scoped ModuleCat

universe v w

variable (k : Type (max v w)) (Q : Type v) [Field k] [Quiver.{w} Q]

section Finite

variable [Finite Q] [FiniteDimensional k (pathAlgebra k Q)]

/-- **Every pair of finitely generated modules over a finite-dimensional path algebra is
Euler-admissible.** The simple modules are the vertex simples, whose first-arrow resolutions
bound Ext above degree one, and admissibility propagates along composition series. -/
theorem isEulerAdmissibleOn_isFG_pathAlgebra :
    IsEulerAdmissibleOn.{max v w} k (ModuleCat.isFG (pathAlgebra k Q))
      (ModuleCat.isFG (pathAlgebra k Q)) := by
  have : ∀ a b : Q, Finite (a ⟶ b) := finite_hom_of_module_finite_pathAlgebra k Q inferInstance
  refine isEulerAdmissibleOn_isFG_of_forall_isSimpleModule k fun S Y hS hY ↦ ?_
  have hQ : Quiver.IsAcyclic Q := isAcyclic_of_module_finite_pathAlgebra k Q inferInstance
  have : Simple S := (simple_iff_isSimpleModule' S).mpr hS
  obtain ⟨i, ⟨e⟩⟩ := exists_iso_vertexSimpleModule_of_simple k Q hQ S
  have hYk : FiniteDimensional k Y := Module.Finite.trans (pathAlgebra k Q) Y
  have hfin := isFinDim_iff.mp (isFinDim_quiverRepFunctor_obj k Q Y hYk)
  exact (isEulerAdmissible_vertexSimpleModule k Q i Y (hfin _) fun j _ ↦ hfin _).of_iso
    e.symm (Iso.refl Y)

end Finite

variable [Fintype Q] [∀ a b : Q, Fintype (a ⟶ b)] [FiniteDimensional k (pathAlgebra k Q)]

/-- **The Ext-Euler pairing of a finite acyclic quiver is the Ringel form.** On the Grothendieck
group of finitely generated modules over a finite-dimensional path algebra, the categorical
Ext-Euler pairing is the quiver Euler form pulled back along the dimension-vector map. -/
@[simp]
theorem extEulerPairing_eq_pathAlgebraEulerPairingK0
    (x y : ExactK0 (finiteModulesExactStructure (pathAlgebra k Q))) :
    extEulerPairing (isExtensionClosed_finiteModules (pathAlgebra k Q))
      (isExtensionClosed_finiteModules (pathAlgebra k Q))
      (isEulerAdmissibleOn_isFG_pathAlgebra k Q)
      (finiteModulesExactK0Equiv (pathAlgebra k Q) x)
      (finiteModulesExactK0Equiv (pathAlgebra k Q) y) =
    pathAlgebraEulerPairingK0 k Q x y := by
  set A := pathAlgebra k Q
  let e := finiteModulesExactK0Equiv A
  set Φ := extEulerPairing (isExtensionClosed_finiteModules A) (isExtensionClosed_finiteModules A)
    (isEulerAdmissibleOn_isFG_pathAlgebra k Q)
  -- For a fixed module class `[Y]`, both sides are additive in `x` and agree on the spanning
  -- family of vertex simple classes.
  have key (Y : FGModuleCat A) (x : ExactK0 (finiteModulesExactStructure A)) :
      Φ (e x) (ExactK0.of Y) = pathAlgebraEulerPairingK0 k Q x (ExactK0.of Y) := by
    let f : ExactK0 (finiteModulesExactStructure A) →+ ℤ :=
      (Φ.flip (ExactK0.of Y)).comp e.toAddMonoidHom
    let g : ExactK0 (finiteModulesExactStructure A) →+ ℤ :=
      ((pathAlgebraEulerPairingK0 k Q).flip (ExactK0.of Y)).toAddMonoidHom
    suffices f = g from DFunLike.congr_fun this x
    apply AddMonoidHom.toIntLinearMap_injective
    refine LinearMap.ext_on_range (span_range_exactK0OfFamily_eq_top (vertexSimpleModuleFG k Q)
      (isExhaustiveSimpleFamily_vertexSimpleModuleFG k Q)) fun i ↦ ?_
    have hYk : FiniteDimensional k Y.obj := Module.Finite.trans A Y.obj
    have hfin := isFinDim_iff.mp (isFinDim_quiverRepFunctor_obj k Q Y.obj hYk)
    simp only [f, g, AddMonoidHom.coe_toIntLinearMap, AddMonoidHom.comp_apply,
      AddMonoidHom.flip_apply, LinearMap.toAddMonoidHom_coe, LinearMap.BilinForm.flip_apply,
      AddEquiv.coe_toAddMonoidHom, exactK0OfFamily_apply, e, finiteModulesExactK0Equiv_of, Φ,
      extEulerPairing_of_of, vertexSimpleModuleFG_obj]
    rw [pathAlgebraEulerPairingK0_of_of]
    exact extEuler_vertexSimpleModule_eq_eulerForm k Q i Y.obj (hfin _) fun j _ ↦ hfin _
  -- Both sides are additive in `y`.
  suffices (Φ (e x)).comp e.toAddMonoidHom = (pathAlgebraEulerPairingK0 k Q x).toAddMonoidHom from
    DFunLike.congr_fun this y
  exact ExactK0.hom_ext fun Y ↦ by
    simpa only [AddMonoidHom.comp_apply, AddEquiv.coe_toAddMonoidHom,
      LinearMap.toAddMonoidHom_coe, e, finiteModulesExactK0Equiv_of] using key Y x

/-- **The Ext-Euler characteristic of two finitely generated modules over a finite-dimensional
path algebra is the Ringel form of their dimension vectors.** -/
@[simp]
theorem extEuler_eq_eulerForm_dimVector (X Y : ModuleCat (pathAlgebra k Q))
    [Module.Finite (pathAlgebra k Q) X] [Module.Finite (pathAlgebra k Q) Y]
    (h : IsEulerAdmissible.{max v w} k X Y) :
    extEuler k h =
      eulerForm Q (fun i ↦ (dimVector ((quiverRepFunctor k Q).obj X) i : ℤ))
        (fun i ↦ (dimVector ((quiverRepFunctor k Q).obj Y) i : ℤ)) := by
  have := extEulerPairing_eq_pathAlgebraEulerPairingK0 k Q (ExactK0.of (FGModuleCat.of _ X))
    (ExactK0.of (FGModuleCat.of _ Y))
  simpa only [finiteModulesExactK0Equiv_of, extEulerPairing_of_of, pathAlgebraEulerPairingK0_of_of]
    using this

/-- **The symmetrized Ext-Euler pairing is the polarized Tits form** of the dimension vectors. -/
theorem extEulerPairing_add_flip_eq_titsPolarForm
    (x y : ExactK0 (finiteModulesExactStructure (pathAlgebra k Q))) :
    extEulerPairing (isExtensionClosed_finiteModules (pathAlgebra k Q))
      (isExtensionClosed_finiteModules (pathAlgebra k Q))
      (isEulerAdmissibleOn_isFG_pathAlgebra k Q)
      (finiteModulesExactK0Equiv (pathAlgebra k Q) x)
      (finiteModulesExactK0Equiv (pathAlgebra k Q) y) +
    extEulerPairing (isExtensionClosed_finiteModules (pathAlgebra k Q))
      (isExtensionClosed_finiteModules (pathAlgebra k Q))
      (isEulerAdmissibleOn_isFG_pathAlgebra k Q)
      (finiteModulesExactK0Equiv (pathAlgebra k Q) y)
      (finiteModulesExactK0Equiv (pathAlgebra k Q) x) =
    titsPolarForm Q (pathAlgebraDimensionVectorK0 k Q x) (pathAlgebraDimensionVectorK0 k Q y) := by
  rw [extEulerPairing_eq_pathAlgebraEulerPairingK0, extEulerPairing_eq_pathAlgebraEulerPairingK0,
    pathAlgebraEulerPairingK0_apply, pathAlgebraEulerPairingK0_apply, titsPolarForm_def]

end TauCeti
