/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Lie.UniversalEnveloping
public import Mathlib.Analysis.Complex.Basic
public import TauCeti.Algebra.Lie.UniversalEnveloping.Abelian
public import TauCeti.RingTheory.Semisimple.CentralCharacter

/-!
# The real rotation module: the centre need not act by real scalars

Let `𝔤 = ℝ` be the one-dimensional abelian real Lie algebra (the Lie algebra of the circle) and let
its generator act on `V = ℝ² = ℂ` by the rotation `J = [[0, -1], [1, 0]]`, multiplication by `i`.
Through `UniversalEnvelopingAlgebra.lift` the enveloping algebra `U = U(𝔤)` acts on `V`; it is
commutative, so every element is central. This file proves:

* `V` is a simple `U`-module (`TauCeti.RotationModule.isSimpleModule`): over `ℝ` the rotation has no
  eigenvector (`TauCeti.RotationModule.not_exists_eigenvector`);
* the central element `ι 1` acts by `J` (`TauCeti.RotationModule.centerToEnd_ιOne_apply`), with
  `J² = -1`, and not by a real scalar (`TauCeti.RotationModule.centerToEnd_ιOne_ne_algebraMap`);
* the commutant `End_U(V)` is `ℂ` as an `ℝ`-algebra (`TauCeti.RotationModule.endAlgEquiv`).

So for an irreducible real module the action `Z(U(𝔤)) → End_{U(𝔤)}(V)` can land in a division
algebra other than `ℝ`; here it is `ℂ`, and there is no real scalar central character.
-/

public section

open Complex

attribute [local instance 100] LieRing.ofAssociativeRing

namespace TauCeti

/-- The rotation generator `t ↦ t i` of `𝔤 = ℝ` into `ℂ`, as a Lie algebra homomorphism (both
sides are commutative). -/
noncomputable def rotationLieHom : ℝ →ₗ⁅ℝ⁆ ℂ where
  toFun t := t * I
  map_add' s t := by push_cast; ring
  map_smul' c t := by simp only [smul_eq_mul, ofReal_mul, RingHom.id_apply, real_smul]; ring
  map_lie' {s t} := by simp only [Ring.lie_def, mul_comm s t, sub_self, ofReal_zero, zero_mul]; ring

/-- The rotation generator sends `t` to `t i`. -/
@[simp]
theorem rotationLieHom_apply (t : ℝ) : rotationLieHom t = t * I := (rfl)

/-- The action `U(𝔤) → ℂ` of the enveloping algebra on the rotation module. -/
noncomputable def rotationAction : UniversalEnvelopingAlgebra ℝ ℝ →ₐ[ℝ] ℂ :=
  UniversalEnvelopingAlgebra.lift ℝ rotationLieHom

/-- The generator `t` of `𝔤 = ℝ` acts by `t i`. -/
theorem rotationAction_ι (t : ℝ) : rotationAction (UniversalEnvelopingAlgebra.ι ℝ t) = t * I :=
  UniversalEnvelopingAlgebra.lift_ι_apply ℝ rotationLieHom t

/-- The rotation action is onto `ℂ`. -/
theorem rotationAction_surjective : Function.Surjective rotationAction := fun z ↦
  ⟨algebraMap ℝ _ z.re + z.im • UniversalEnvelopingAlgebra.ι ℝ (1 : ℝ), by
    rw [map_add, AlgHom.commutes, map_smul, rotationAction_ι]
    apply Complex.ext <;> simp⟩

/-- The real rotation module: `ℂ = ℝ²`, on which `U(ℝ)` acts through `TauCeti.rotationAction`. -/
@[expose] def RotationModule : Type := ℂ

namespace RotationModule

instance instAddCommGroup : AddCommGroup RotationModule := inferInstanceAs (AddCommGroup ℂ)

noncomputable instance instModuleReal : Module ℝ RotationModule := inferInstanceAs (Module ℝ ℂ)

/-- `U(ℝ)` acts on the rotation module by multiplication by the image under `rotationAction`. -/
noncomputable instance instModule : Module (UniversalEnvelopingAlgebra ℝ ℝ) RotationModule :=
  Module.compHom ℂ rotationAction.toRingHom

/-- The identification of the rotation module with `ℂ`. -/
noncomputable def toComplex : RotationModule ≃ₗ[ℝ] ℂ := LinearEquiv.refl ℝ ℂ

@[simp]
theorem smul_def (u : UniversalEnvelopingAlgebra ℝ ℝ) (v : RotationModule) :
    toComplex (u • v) = rotationAction u * toComplex v :=
  smul_eq_mul (rotationAction u) (toComplex v)

instance instIsScalarTower : IsScalarTower ℝ (UniversalEnvelopingAlgebra ℝ ℝ) RotationModule :=
  ⟨fun c u v ↦ toComplex.injective <| by
    rw [smul_def, map_smul, map_smul, smul_def, smul_mul_assoc]⟩

/-- **The rotation module is simple.** -/
instance isSimpleModule : IsSimpleModule (UniversalEnvelopingAlgebra ℝ ℝ) RotationModule :=
  isSimpleModule_iff_toSpanSingleton_surjective.mpr ⟨inferInstanceAs (Nontrivial ℂ), fun v hv w ↦ by
    obtain ⟨u, hu⟩ := rotationAction_surjective (toComplex w / toComplex v)
    refine ⟨u, toComplex.injective ?_⟩
    rw [LinearMap.toSpanSingleton_apply, smul_def, hu,
      div_mul_cancel₀ _ (toComplex.map_ne_zero_iff.mpr hv)]⟩

/-- The central element `ι 1` of `U(ℝ)`. -/
noncomputable def ιOne : Subalgebra.center ℝ (UniversalEnvelopingAlgebra ℝ ℝ) :=
  ⟨UniversalEnvelopingAlgebra.ι ℝ (1 : ℝ),
    have : IsLieAbelian ℝ := isMulCommutative_iff_isLieAbelian.mp inferInstance
    UniversalEnvelopingAlgebra.ι_mem_center ℝ ℝ 1⟩

@[simp]
theorem coe_ιOne : (ιOne : UniversalEnvelopingAlgebra ℝ ℝ) = UniversalEnvelopingAlgebra.ι ℝ 1 :=
  (rfl)

/-- **The central element `ι 1` acts by the rotation `J`**, multiplication by `i`. -/
theorem centerToEnd_ιOne_apply (v : RotationModule) :
    toComplex (centerToEnd ℝ (UniversalEnvelopingAlgebra ℝ ℝ) RotationModule ιOne v) =
      I * toComplex v := by
  rw [centerToEnd_apply, smul_def, coe_ιOne, rotationAction_ι, ofReal_one, one_mul]

/-- **`J² = -1`.** -/
theorem centerToEnd_ιOne_sq :
    centerToEnd ℝ (UniversalEnvelopingAlgebra ℝ ℝ) RotationModule ιOne ^ 2 = -1 := by
  ext v
  apply toComplex.injective
  simp only [pow_two, mul_apply_eq_comp, centerToEnd_ιOne_apply]
  simp [← mul_assoc]

/-- **The rotation has no real eigenvector.** -/
theorem not_exists_eigenvector :
    ¬ ∃ (v : RotationModule) (c : ℝ), v ≠ 0 ∧
      centerToEnd ℝ (UniversalEnvelopingAlgebra ℝ ℝ) RotationModule ιOne v = c • v := by
  rintro ⟨v, c, hv0, h⟩
  have h' := congrArg toComplex h
  rw [centerToEnd_ιOne_apply, map_smul, real_smul] at h'
  have := congrArg Complex.im (mul_right_cancel₀ (toComplex.map_ne_zero_iff.mpr hv0) h')
  rw [I_im, ofReal_im] at this
  exact one_ne_zero this

/-- **The central element `ι 1` does not act by a real scalar.** -/
theorem centerToEnd_ιOne_ne_algebraMap (c : ℝ) :
    centerToEnd ℝ (UniversalEnvelopingAlgebra ℝ ℝ) RotationModule ιOne ≠
      algebraMap ℝ (Module.End (UniversalEnvelopingAlgebra ℝ ℝ) RotationModule) c := by
  intro h
  refine not_exists_eigenvector
    ⟨toComplex.symm 1, c, toComplex.symm.map_ne_zero_iff.mpr one_ne_zero, ?_⟩
  rw [h, Module.algebraMap_end_apply]

/-- A `U(ℝ)`-linear endomorphism of the rotation module is multiplication by its value at `1`. -/
theorem toComplex_end_apply (T : Module.End (UniversalEnvelopingAlgebra ℝ ℝ) RotationModule)
    (v : RotationModule) : toComplex (T v) = toComplex v * toComplex (T (toComplex.symm 1)) := by
  obtain ⟨u, hu⟩ := rotationAction_surjective (toComplex v)
  have hv : v = u • toComplex.symm 1 :=
    toComplex.injective (by rw [smul_def, hu, LinearEquiv.apply_symm_apply, mul_one])
  rw [hv, map_smul, smul_def, smul_def, hu, LinearEquiv.apply_symm_apply, mul_one]

/-- Multiplication by `c ∈ ℂ` as a `U(ℝ)`-linear endomorphism of the rotation module. -/
noncomputable def mulEnd (c : ℂ) : Module.End (UniversalEnvelopingAlgebra ℝ ℝ) RotationModule where
  toFun v := toComplex.symm (c * toComplex v)
  map_add' v w := toComplex.injective <| by
    simp only [LinearEquiv.apply_symm_apply, map_add, mul_add]
  map_smul' u v := toComplex.injective <| by
    simp only [LinearEquiv.apply_symm_apply, smul_def, RingHom.id_apply]
    ring

/-- `mulEnd c` is multiplication by `c`. -/
@[simp]
theorem toComplex_mulEnd (c : ℂ) (v : RotationModule) :
    toComplex (mulEnd c v) = c * toComplex v :=
  toComplex.apply_symm_apply _

/-- **The commutant of the rotation module is `ℂ`** as an `ℝ`-algebra: `T ↦ T 1`. -/
@[expose, simps]
noncomputable def endAlgEquiv :
    Module.End (UniversalEnvelopingAlgebra ℝ ℝ) RotationModule ≃ₐ[ℝ] ℂ where
  toFun T := toComplex (T (toComplex.symm 1))
  invFun := mulEnd
  left_inv T := LinearMap.ext fun v ↦ toComplex.injective <| by
    rw [toComplex_mulEnd, toComplex_end_apply T v, mul_comm]
  right_inv c := by
    dsimp only
    rw [toComplex_mulEnd, LinearEquiv.apply_symm_apply, mul_one]
  map_mul' S T := by
    rw [mul_apply_eq_comp, toComplex_end_apply S, mul_comm]
  map_add' S T := by
    rw [LinearMap.add_apply, map_add]
  commutes' c := by
    simp [Module.algebraMap_end_apply]

end RotationModule

end TauCeti
