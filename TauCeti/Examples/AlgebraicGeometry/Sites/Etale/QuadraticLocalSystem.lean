/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Complex.Polynomial.Basic
public import Mathlib.FieldTheory.IsSepClosed
public import Mathlib.FieldTheory.KrullTopology
public import TauCeti.AlgebraicGeometry.FiniteEtale.Galois.ModuleSheaf
public import TauCeti.FieldTheory.Galois.Complex

/-!
# A nonconstant finite lisse `ℤ/3` sheaf on `Spec ℝ`

The quadratic character of `Gal(ℂ/ℝ)`, through which complex conjugation acts by `-1`, makes
`ℤ/3` a representation of `Gal(ℂ/ℝ)` (`TauCeti.AlgebraicGeometry.signRepresentation`). The
corresponding étale sheaf of `ℤ/3`-modules on `Spec ℝ`
(`TauCeti.AlgebraicGeometry.quadraticLocalSystem`, an instance of
`TauCeti.FiniteEtaleScheme.galoisModuleSheaf`) is finite lisse, because the cover
`Spec ℂ ⟶ Spec ℝ` is finite étale and surjective, but it is not constant. Its sections over
`Spec ℝ` vanish, since a section fixed by complex conjugation equals its negative, and `2` is
invertible in `ℤ/3`. On the other hand, over the finite étale `ℝ`-scheme corresponding to the
regular `Gal(ℂ/ℝ)`-set, the character itself is a nonzero section. A constant sheaf whose
sections over `Spec ℝ` vanish is zero, as its value is a retract of those sections.

This is a Check of EtaleCohomologyFoundations §F.0.1 in TauCetiRoadmap: on `Spec ℝ`, the quadratic
character yields a nonconstant rank-one `ℤ/3` local system. The identification of its stalk at
`Spec ℂ` with `ℤ/3`, on which complex conjugation acts by `-1`, is not part of this file.

## Main results

* `TauCeti.AlgebraicGeometry.isFiniteLisse_quadraticLocalSystem`: the sheaf is finite lisse.
* `TauCeti.AlgebraicGeometry.not_isConstant_quadraticLocalSystem`: the sheaf is not constant.
-/

public section

open CategoryTheory Limits Opposite AlgebraicGeometry FintypeCatDiscrete Complex
  TauCeti.FiniteEtaleScheme ContAction

namespace TauCeti.AlgebraicGeometry

private theorem eq_one_or_eq_conjAe (σ : Gal(ℂ/ℝ)) : σ = 1 ∨ σ = conjAe :=
  (real_algHom_eq_id_or_conj σ).imp
    (fun h ↦ AlgEquiv.coe_toAlgHom_injective (h.trans AlgEquiv.refl_toAlgHom.symm))
    fun h ↦ AlgEquiv.coe_toAlgHom_injective h

private theorem conjAe_mul_conjAe : (conjAe * conjAe : Gal(ℂ/ℝ)) = 1 :=
  AlgEquiv.ext fun z ↦ by simp

private theorem conjAe_ne_one : (conjAe : Gal(ℂ/ℝ)) ≠ 1 := fun h ↦ by
  have := congrArg (· I) h
  norm_num [Complex.ext_iff] at this

open scoped Classical in
/-- The quadratic character of `Gal(ℂ/ℝ)` as a representation on `ℤ/3`: the identity acts
trivially and complex conjugation acts by `-1`. -/
noncomputable def signRepresentation : Representation (ZMod 3) Gal(ℂ/ℝ) (ZMod 3) where
  toFun σ := if σ = 1 then 1 else -1
  map_one' := ite_eq_left_iff.2 fun h ↦ (h rfl).elim
  map_mul' σ τ := by
    rcases eq_one_or_eq_conjAe σ with rfl | rfl <;>
      rcases eq_one_or_eq_conjAe τ with rfl | rfl <;>
      simp only [one_mul, mul_one, conjAe_mul_conjAe, conjAe_ne_one, ↓reduceIte]
    exact ((neg_one_mul (-1 : Module.End (ZMod 3) (ZMod 3))).trans (neg_neg 1)).symm

/-- Complex conjugation acts on `signRepresentation` by `-1`. -/
theorem signRepresentation_conjAe (m : ZMod 3) : signRepresentation conjAe m = -m := by
  simp [signRepresentation, conjAe_ne_one]

/-- The étale sheaf of `ℤ/3`-modules on `Spec ℝ` given by the quadratic character of
`Gal(ℂ/ℝ)`. -/
noncomputable def quadraticLocalSystem :
    Sheaf (Scheme.smallEtaleTopology (Spec (.of ℝ))) (ModuleCat.{0} (ZMod 3)) :=
  galoisModuleSheaf ℝ ℂ signRepresentation

/-- **The quadratic local system is finite lisse.** It becomes constant on the finite étale
cover `Spec ℂ ⟶ Spec ℝ`. -/
theorem isFiniteLisse_quadraticLocalSystem : quadraticLocalSystem.IsFiniteLisse :=
  isFiniteLisse_galoisModuleSheaf ℝ ℂ _

/-- The regular `Gal(ℂ/ℝ)`-set, continuous since `Gal(ℂ/ℝ)` is discrete. -/
noncomputable abbrev regularGaloisSet : ContAction FintypeCat.{0} Gal(ℂ/ℝ) :=
  ⟨Action.FintypeCat.ofMulAction Gal(ℂ/ℝ) (FintypeCat.of Gal(ℂ/ℝ)),
    (Action.isContinuous_iff_isOpen_stabilizer _).2 fun _ ↦ isOpen_discrete _⟩

/-- The quadratic local system has no nonzero sections over `Spec ℝ`. -/
theorem subsingleton_quadraticLocalSystem_obj_ofHom_id :
    Subsingleton (quadraticLocalSystem.obj.obj
      (op ((toEtale _).obj (ofHom (𝟙 (Spec (.of ℝ))))))) := by
  have hT := (isTerminalOfHomId (Spec (.of ℝ))).isTerminalObj (galoisEquivalence ℝ ℂ).functor
  -- The Galois set of `Spec ℝ` is a point, so a section is fixed by conjugation, hence zero.
  have : Subsingleton ((fiberFunctor Gal(ℂ/ℝ)).obj ((galoisEquivalence ℝ ℂ).functor.obj
      (ofHom (𝟙 (Spec (.of ℝ)))))) :=
    (Types.isTerminalEquivUnique _ (hT.isTerminalObj (fiberFunctor Gal(ℂ/ℝ)))).instSubsingleton
  have key (φ : (modulePresheaf signRepresentation).obj (op ((galoisEquivalence ℝ ℂ).functor.obj
      (ofHom (𝟙 (Spec (.of ℝ))))))) (y) : φ.val y = 0 := by
    have h := φ.property conjAe y
    rw [Subsingleton.elim (conjAe • y) y, signRepresentation_conjAe] at h
    revert h
    generalize φ.val y = m
    revert m
    decide
  exact ⟨fun a b ↦ (galoisModuleSheafObjIso ℝ ℂ signRepresentation _).toLinearEquiv.injective
    (Subtype.ext (funext fun y ↦ (key _ y).trans (key _ y).symm))⟩

/-- Over the finite étale `ℝ`-scheme of the regular `Gal(ℂ/ℝ)`-set, the quadratic local system
has a nonzero section: the character itself. -/
theorem nontrivial_quadraticLocalSystem_obj_regularGaloisSet :
    Nontrivial (quadraticLocalSystem.obj.obj
      (op ((toEtale _).obj ((galoisEquivalence ℝ ℂ).inverse.obj regularGaloisSet)))) := by
  let e := galoisModuleSheafObjIso ℝ ℂ signRepresentation
      ((galoisEquivalence ℝ ℂ).inverse.obj regularGaloisSet) ≪≫
    (modulePresheaf signRepresentation).mapIso
      ((galoisEquivalence ℝ ℂ).counitIso.app regularGaloisSet).op.symm
  let φ : (modulePresheaf signRepresentation).obj (op regularGaloisSet) :=
    ⟨fun (g : Gal(ℂ/ℝ)) ↦ signRepresentation g 1, fun g (h : Gal(ℂ/ℝ)) ↦ by
      change signRepresentation (g * h) 1 = _
      rw [map_mul]; rfl⟩
  have : φ ≠ 0 := fun h ↦ by
    have h1 : φ.val (show (fiberFunctor _).obj regularGaloisSet from (1 : Gal(ℂ/ℝ))) = 1 := by
      simp [φ]
    rw [h] at h1
    exact zero_ne_one h1
  exact e.toLinearEquiv.nontrivial_congr.2 ⟨φ, 0, this⟩

/-- **The quadratic local system is not constant.** If it were the constant sheaf on a module
`N`, then `N` would embed into the sections over `Spec ℝ`, through the stalk at `Spec ℂ`, so
`N = 0`; but the sheaf has a nonzero section. -/
theorem not_isConstant_quadraticLocalSystem :
    ¬ quadraticLocalSystem.IsConstant (Scheme.smallEtaleTopology (Spec (.of ℝ))) := by
  rintro ⟨N, ⟨e⟩⟩
  let s : Spec (.of ℂ) ⟶ Spec (.of ℝ) := Spec.map (CommRingCat.ofHom (algebraMap ℝ ℂ))
  have : Algebra.Etale ℝ ℂ := Algebra.Etale.of_isSeparable ℝ ℂ
  have : Etale s :=
    (HasRingHomProperty.Spec_iff (P := @Etale)).mpr (RingHom.etale_algebraMap.mpr inferInstance)
  let T := (toEtale _).obj (ofHom (𝟙 (Spec (.of ℝ))))
  let i : Scheme.Etale.mk (𝟙 (Spec (.of ℝ))) ≅ T :=
    (Scheme.Etale.forgetFullyFaithful _).preimageIso
      (eqToIso (by rw [forget_obj_toEtale_obj, ofHom_obj]; rfl))
  let x : (Scheme.pointSmallEtale s).fiber.obj T :=
    (Scheme.pointSmallEtaleFiberCorepresentableBy s).homEquiv
      ((Scheme.Etale.mkIdTerminal _).from (Scheme.Etale.mk s) ≫ i.hom)
  -- `N` is a retract of the sections of the constant sheaf over `Spec ℝ`, through the stalk.
  have hmono := mono_of_mono_fac
    ((Scheme.pointSmallEtale s).toSheafify_toPresheafFiber_sheafFiberConstantSheafIso_hom N T x)
  have hT := subsingleton_quadraticLocalSystem_obj_ofHom_id
  have hC : Subsingleton (((constantSheaf _ _).obj N).obj.obj (op T)) :=
    ⟨fun a b ↦ (((ObjectProperty.ι _).mapIso e).app (op T)).toLinearEquiv.injective
      (@Subsingleton.elim _ hT _ _)⟩
  have : Subsingleton N :=
    ⟨fun a b ↦ (ModuleCat.mono_iff_injective _).1 hmono (@Subsingleton.elim _ hC _ _)⟩
  have hz : IsZero quadraticLocalSystem :=
    ((constantSheaf _ _).map_isZero (ModuleCat.isZero_of_subsingleton N)).of_iso e.symm
  obtain ⟨a, b, hab⟩ := nontrivial_quadraticLocalSystem_obj_regularGaloisSet.exists_pair_ne
  exact hab (@Subsingleton.elim _ (ModuleCat.subsingleton_of_isZero
    (((sheafSections _ _).obj (op ((toEtale _).obj
      ((galoisEquivalence ℝ ℂ).inverse.obj regularGaloisSet)))).map_isZero hz)) a b)

end TauCeti.AlgebraicGeometry
