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
* the central element `ι 1` acts by `J` (`TauCeti.RotationModule.centerToEnd_ι_one_apply`), with
  `J² = -1`, and not by a real scalar (`TauCeti.RotationModule.centerToEnd_ι_one_ne_algebraMap`);
* the commutant `End_U(V)` is `ℂ` (`TauCeti.RotationModule.endRingEquiv`).

So for an irreducible real module the action `Z(U(𝔤)) → End_{U(𝔤)}(V)` lands in a division algebra
that is not `ℝ`, and there is no real scalar central character. This is the first Check of
RepresentationTheory/LieGroups §5.4.
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

/-- The action `U(𝔤) → ℂ` of the enveloping algebra on the rotation module. -/
noncomputable def rotationAction : UniversalEnvelopingAlgebra ℝ ℝ →ₐ[ℝ] ℂ :=
  UniversalEnvelopingAlgebra.lift ℝ rotationLieHom

/-- The generator `t` of `𝔤 = ℝ` acts by `t i`. -/
theorem rotationAction_ι (t : ℝ) : rotationAction (UniversalEnvelopingAlgebra.ι ℝ t) = t * I :=
  UniversalEnvelopingAlgebra.lift_ι_apply ℝ rotationLieHom t

/-- The rotation action is onto `ℂ`: `a + b i` is the image of `a + b ι 1`. -/
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
def toComplex : RotationModule ≃ ℂ := Equiv.refl _

theorem smul_def (u : UniversalEnvelopingAlgebra ℝ ℝ) (v : RotationModule) :
    toComplex (u • v) = rotationAction u * toComplex v :=
  smul_eq_mul (rotationAction u) (toComplex v)

theorem toComplex_add (v w : RotationModule) : toComplex (v + w) = toComplex v + toComplex w :=
  (rfl)

theorem toComplex_zero : toComplex 0 = 0 :=
  (rfl)

theorem toComplex_realSmul (c : ℝ) (v : RotationModule) : toComplex (c • v) = c * toComplex v :=
  (Complex.real_smul (x := c) (z := toComplex v))

instance instIsScalarTower : IsScalarTower ℝ (UniversalEnvelopingAlgebra ℝ ℝ) RotationModule :=
  ⟨fun c u v ↦ toComplex.injective <| by
    rw [toComplex_realSmul, smul_def, smul_def, map_smul, Complex.real_smul, mul_assoc]⟩

/-- **The rotation module is simple.** A nonzero `v` generates everything, since every `w ∈ ℂ` is
`(w / v) v` and the action is onto `ℂ`. -/
instance isSimpleModule : IsSimpleModule (UniversalEnvelopingAlgebra ℝ ℝ) RotationModule := by
  have : Nontrivial RotationModule := inferInstanceAs (Nontrivial ℂ)
  have : IsSimpleOrder (Submodule (UniversalEnvelopingAlgebra ℝ ℝ) RotationModule) :=
    ⟨fun N ↦ or_iff_not_imp_left.mpr fun hN ↦ by
      obtain ⟨v, hv, hv0⟩ := (Submodule.ne_bot_iff N).mp hN
      refine eq_top_iff.mpr fun w _ ↦ ?_
      obtain ⟨u, hu⟩ := rotationAction_surjective (toComplex w / toComplex v)
      have hv0' : toComplex v ≠ 0 :=
        fun h ↦ hv0 (toComplex.injective (h.trans toComplex_zero.symm))
      convert N.smul_mem u hv
      apply toComplex.injective
      rw [smul_def, hu, div_mul_cancel₀ _ hv0']⟩
  exact ⟨⟩

/-- The real line is an abelian Lie algebra. -/
theorem isLieAbelian_real : IsLieAbelian ℝ :=
  ⟨fun x y ↦ by rw [Ring.lie_def, mul_comm, sub_self]⟩

/-- The central element `ι 1` of `U(ℝ)`. -/
noncomputable def ιOne : Subalgebra.center ℝ (UniversalEnvelopingAlgebra ℝ ℝ) :=
  ⟨UniversalEnvelopingAlgebra.ι ℝ (1 : ℝ),
    have := isLieAbelian_real
    UniversalEnvelopingAlgebra.ι_mem_center ℝ ℝ 1⟩

theorem coe_ιOne : (ιOne : UniversalEnvelopingAlgebra ℝ ℝ) = UniversalEnvelopingAlgebra.ι ℝ 1 :=
  (rfl)

/-- **The central element `ι 1` acts by the rotation `J`**, multiplication by `i`. -/
theorem centerToEnd_ι_one_apply (v : RotationModule) :
    toComplex (centerToEnd ℝ (UniversalEnvelopingAlgebra ℝ ℝ) RotationModule ιOne v) =
      I * toComplex v := by
  rw [centerToEnd_apply, smul_def, coe_ιOne, rotationAction_ι, ofReal_one, one_mul]

/-- **`J² = -1`.** -/
theorem centerToEnd_ι_one_sq :
    centerToEnd ℝ (UniversalEnvelopingAlgebra ℝ ℝ) RotationModule ιOne ^ 2 = -1 := by
  ext v
  apply toComplex.injective
  rw [pow_two, mul_apply_eq_comp, centerToEnd_ι_one_apply, centerToEnd_ι_one_apply,
    ← mul_assoc, I_mul_I, LinearMap.neg_apply, one_apply_eq_self, neg_one_mul]
  rfl

/-- **The rotation has no real eigenvector.** -/
theorem not_exists_eigenvector :
    ¬ ∃ (v : RotationModule) (c : ℝ), v ≠ 0 ∧
      centerToEnd ℝ (UniversalEnvelopingAlgebra ℝ ℝ) RotationModule ιOne v = c • v := by
  rintro ⟨v, c, hv0, h⟩
  have hv0' : toComplex v ≠ 0 := fun h ↦ hv0 (toComplex.injective (h.trans toComplex_zero.symm))
  have h' := congrArg toComplex h
  rw [centerToEnd_ι_one_apply, toComplex_realSmul] at h'
  have := congrArg Complex.im (mul_right_cancel₀ hv0' h')
  rw [I_im, ofReal_im] at this
  exact one_ne_zero this

/-- **The central element `ι 1` does not act by a real scalar.** -/
theorem centerToEnd_ι_one_ne_algebraMap (c : ℝ) :
    centerToEnd ℝ (UniversalEnvelopingAlgebra ℝ ℝ) RotationModule ιOne ≠
      algebraMap ℝ (Module.End (UniversalEnvelopingAlgebra ℝ ℝ) RotationModule) c := by
  intro h
  refine not_exists_eigenvector ⟨toComplex.symm 1, c, fun h0 ↦ one_ne_zero
    (congrArg toComplex h0), ?_⟩
  rw [h]
  rfl

/-- A `U(ℝ)`-linear endomorphism of the rotation module is multiplication by its value at `1`. -/
theorem toComplex_end_apply (T : Module.End (UniversalEnvelopingAlgebra ℝ ℝ) RotationModule)
    (v : RotationModule) : toComplex (T v) = toComplex v * toComplex (T (toComplex.symm 1)) := by
  obtain ⟨u, hu⟩ := rotationAction_surjective (toComplex v)
  have hv : v = u • toComplex.symm 1 :=
    toComplex.injective (by rw [smul_def, hu, Equiv.apply_symm_apply, mul_one])
  rw [hv, map_smul, smul_def, smul_def, hu, Equiv.apply_symm_apply, mul_one]

/-- Multiplication by `c ∈ ℂ` as a `U(ℝ)`-linear endomorphism of the rotation module. -/
noncomputable def mulEnd (c : ℂ) : Module.End (UniversalEnvelopingAlgebra ℝ ℝ) RotationModule where
  toFun v := toComplex.symm (c * toComplex v)
  map_add' v w := toComplex.injective <| by
    simp only [Equiv.apply_symm_apply, toComplex_add, mul_add]
  map_smul' u v := toComplex.injective <| by
    simp only [Equiv.apply_symm_apply, smul_def, RingHom.id_apply]
    ring

/-- **The commutant of the rotation module is `ℂ`**: `T ↦ T 1`. -/
noncomputable def endRingEquiv :
    Module.End (UniversalEnvelopingAlgebra ℝ ℝ) RotationModule ≃+* ℂ where
  toFun T := toComplex (T (toComplex.symm 1))
  invFun := mulEnd
  left_inv T := LinearMap.ext fun v ↦ toComplex.injective <| by
    change toComplex (toComplex.symm _) = _
    rw [Equiv.apply_symm_apply, toComplex_end_apply T v, mul_comm]
  right_inv c := by
    change toComplex (toComplex.symm _) = _
    rw [Equiv.apply_symm_apply, Equiv.apply_symm_apply, mul_one]
  map_mul' S T := by
    rw [mul_apply_eq_comp, toComplex_end_apply S, mul_comm]
  map_add' S T := (rfl)

end RotationModule

end TauCeti
