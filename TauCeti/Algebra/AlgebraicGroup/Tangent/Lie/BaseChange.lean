/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Algebra.AlgebraicGroup.Tangent.Dimension
public import TauCeti.Algebra.AlgebraicGroup.Tangent.Lie.Basic
public import TauCeti.Algebra.AlgebraicGroup.Tangent.Lie.Cotangent
public import TauCeti.Algebra.Lie.Killing.BaseChange
public import Mathlib.RingTheory.Bialgebra.TensorProduct
public import TauCeti.Algebra.Bialgebra.BaseChange
import Mathlib.RingTheory.Finiteness.Descent

/-!
# Base change of the tangent Lie algebra

For a commutative bialgebra `H` over `R` and a commutative `R`-algebra `K`, restriction
along `h ↦ 1 ⊗ h` identifies the tangent Lie algebra of `K ⊗[R] H` over `K` with the
`K`-valued tangent derivations of `H`. The inverse sends `d` to `a ⊗ h ↦ a * d h`.
This comparison requires neither flatness nor finiteness. It connects geometric base
change to the coefficient-valued tangent space and its convolution bracket. For an extension
of fields, `finrank_lie_baseChange` deduces invariance of Lie dimension, and
`isKilling_lie_baseChange_iff` shows that the Lie algebra has nondegenerate Killing form exactly
when its base change does.

When the augmentation cotangent space of `H` is finite projective, the Lie algebra of
`Spec H` is the dual of that space. For a commutative `R`-algebra `S`,
`Derivation.cotangentDualBaseChangeEquiv` composes the comparison above with scalar extension of
tangent vectors and cotangent duality, identifying the scalar extension of this dual with the
dual for `S ⊗[R] H`, again with no flatness assumption.

## Main declarations

* `TauCeti.tangentBaseChangeLieEquiv`: tangent vectors of `K ⊗[R] H` over `K` are the
  `K`-valued tangent vectors of `H`.
* `Derivation.cotangentDualBaseChangeEquiv`: the Lie algebra of `Spec (S ⊗[R] H)` is the scalar
  extension of the Lie algebra of `Spec H`.
* `Derivation.cotangentDualBaseChangeEquiv_tmul_apply_cotangentMap`: its value on the cotangent
  class of `1 ⊗ h`, which determines it (`TauCeti.Bialgebra.dual_ext_cotangentMap_one_tmul`).
* `Derivation.dualCotangentMap_map_cotangentDualBaseChangeEquiv_tmul`,
  `Derivation.dualCotangentMap_lid_symm_cotangentDualBaseChangeEquiv` and
  `Derivation.dualCotangentMap_baseChangeTowerBialgEquiv_cotangentDualBaseChangeEquiv_tmul`: the
  comparison is natural in `H`, trivial along the identity of `R`, and composes in stages.

## References

* J. S. Milne, *Algebraic Groups* (2017), §10.a.

The tensor calculation for compatibility with convolution follows the point comparison in
`TauCeti.Algebra.AlgebraicGroup.BaseChange.Basic`.
-/

public section

namespace TauCeti

open TensorProduct

noncomputable section

variable {R K H : Type*} [CommRing R] [CommRing K] [CommRing H]
  [Algebra R K] [Bialgebra R H]

/-- The `K`-linear extension of a tangent vector, with its coefficient type transported. -/
private def extendTangentLinear (d : Derivation R H (Bialgebra.CounitAlgebra R H K)) :
    K ⊗[R] H →ₗ[K] Bialgebra.CounitAlgebra K (K ⊗[R] H) K :=
  (Bialgebra.CounitAlgebra.algEquivSelf K (K ⊗[R] H) K).symm.toLinearMap.comp
    (AlgebraTensorModule.lift (LinearMap.toSpanSingleton K (H →ₗ[R] K)
      ((Bialgebra.CounitAlgebra.algEquivSelf R H K).toLinearMap.comp d.toLinearMap)))

private theorem extendTangentLinear_tmul
    (d : Derivation R H (Bialgebra.CounitAlgebra R H K)) (a : K) (h : H) :
    Bialgebra.CounitAlgebra.algEquivSelf K (K ⊗[R] H) K
      (extendTangentLinear d (a ⊗ₜ[R] h)) =
      a * Bialgebra.CounitAlgebra.algEquivSelf R H K (d h) := by
  simp only [extendTangentLinear, LinearMap.comp_apply, AlgebraTensorModule.lift_tmul,
    LinearMap.toSpanSingleton_apply, LinearMap.smul_apply, AlgEquiv.toLinearMap_apply,
    AlgEquiv.apply_symm_apply, smul_eq_mul, Derivation.coeFn_coe]

/-- Extend a counit-valued derivation to the base-changed coordinate algebra. -/
private def extendTangent (d : Derivation R H (Bialgebra.CounitAlgebra R H K)) :
    Derivation K (K ⊗[R] H) (Bialgebra.CounitAlgebra K (K ⊗[R] H) K) :=
  Derivation.mk' (extendTangentLinear d) fun x y ↦ by
    induction x using TensorProduct.inductionOn with
    | add x z hx hz => simp [add_mul, map_add, hx, hz, add_smul, smul_add]; abel
    | tmul a h =>
      induction y using TensorProduct.inductionOn with
      | add y z hy hz => simp [mul_add, map_add, hy, hz, add_smul, smul_add]; abel
      | tmul b j =>
        apply (Bialgebra.CounitAlgebra.algEquivSelf K (K ⊗[R] H) K).injective
        simp only [Algebra.TensorProduct.tmul_mul_tmul, map_add,
          Bialgebra.CounitAlgebra.algEquivSelf_smul, extendTangentLinear_tmul,
          TensorProduct.counit_tmul, CommSemiring.counit_apply, d.leibniz]
        simp only [Algebra.algebraMap_self, RingHom.id_apply, Algebra.smul_def]
        ring

private theorem extendTangent_tmul
    (d : Derivation R H (Bialgebra.CounitAlgebra R H K)) (a : K) (h : H) :
    Bialgebra.CounitAlgebra.algEquivSelf K (K ⊗[R] H) K
      (extendTangent d (a ⊗ₜ[R] h)) = a * Bialgebra.CounitAlgebra.algEquivSelf R H K (d h) := by
  rw [extendTangent, Derivation.coe_mk']
  exact extendTangentLinear_tmul d a h

/-- Restrict a tangent vector along the inclusion of the original coordinate algebra. -/
private def restrictTangent
    (d : Derivation K (K ⊗[R] H) (Bialgebra.CounitAlgebra K (K ⊗[R] H) K)) :
    Derivation R H (Bialgebra.CounitAlgebra R H K) :=
  Derivation.mk'
    ((Bialgebra.CounitAlgebra.algEquivSelf R H K).symm.toLinearMap.comp
      (((Bialgebra.CounitAlgebra.algEquivSelf K (K ⊗[R] H) K).toLinearMap.comp
        d.toLinearMap).restrictScalars R |>.comp
          Algebra.TensorProduct.includeRight.toLinearMap)) fun h j ↦ by
    apply (Bialgebra.CounitAlgebra.algEquivSelf R H K).injective
    simp only [LinearMap.comp_apply, LinearMap.restrictScalars_apply,
      AlgEquiv.toLinearMap_apply, AlgEquiv.apply_symm_apply,
      AlgHom.toLinearMap_apply, Derivation.coeFn_coe, map_add,
      Bialgebra.CounitAlgebra.algEquivSelf_smul,
      Algebra.TensorProduct.includeRight_apply]
    have ht : (1 : K) ⊗ₜ[R] (h * j) =
        (1 ⊗ₜ[R] h) * (1 ⊗ₜ[R] j) := by simp
    rw [ht, d.leibniz, map_add]
    simp only [Bialgebra.CounitAlgebra.algEquivSelf_smul]
    simp only [TensorProduct.counit_tmul, CommSemiring.counit_apply,
      Algebra.smul_def, mul_one, Algebra.algebraMap_self, RingHom.id_apply]

private theorem restrictTangent_apply
    (d : Derivation K (K ⊗[R] H) (Bialgebra.CounitAlgebra K (K ⊗[R] H) K)) (h : H) :
    Bialgebra.CounitAlgebra.algEquivSelf R H K (restrictTangent d h) =
      Bialgebra.CounitAlgebra.algEquivSelf K (K ⊗[R] H) K (d (1 ⊗ₜ[R] h)) := by
  simp only [restrictTangent, Derivation.coe_mk', LinearMap.comp_apply,
    LinearMap.restrictScalars_apply, AlgEquiv.toLinearMap_apply, AlgEquiv.apply_symm_apply,
    AlgHom.toLinearMap_apply, Algebra.TensorProduct.includeRight_apply, Derivation.coeFn_coe]

private theorem restrictTangent_extendTangent
    (d : Derivation R H (Bialgebra.CounitAlgebra R H K)) :
    restrictTangent (extendTangent d) = d := by
  ext h
  apply (Bialgebra.CounitAlgebra.algEquivSelf R H K).injective
  rw [restrictTangent_apply, extendTangent_tmul, one_mul]

private theorem extendTangent_restrictTangent
    (d : Derivation K (K ⊗[R] H) (Bialgebra.CounitAlgebra K (K ⊗[R] H) K)) :
    extendTangent (restrictTangent d) = d := by
  ext x
  induction x using TensorProduct.inductionOn with
  | add x y hx hy => simp only [map_add, hx, hy]
  | tmul a h =>
    apply (Bialgebra.CounitAlgebra.algEquivSelf K (K ⊗[R] H) K).injective
    rw [extendTangent_tmul, restrictTangent_apply]
    have ht : a ⊗ₜ[R] h = a • ((1 : K) ⊗ₜ[R] h) := by
      simp only [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
    rw [ht, d.map_smul, map_smul, smul_eq_mul]

/-- Restriction and extension identify coefficient-valued tangent vectors with tangent vectors
of the base-changed coordinate algebra. -/
private def tangentBaseChangeLinearEquiv :
    Derivation R H (Bialgebra.CounitAlgebra R H K) ≃ₗ[K]
      Derivation K (K ⊗[R] H) (Bialgebra.CounitAlgebra K (K ⊗[R] H) K) where
  toFun := extendTangent
  invFun := restrictTangent
  left_inv := restrictTangent_extendTangent
  right_inv := extendTangent_restrictTangent
  map_add' d e := by
    ext x
    induction x using TensorProduct.inductionOn with
    | add x y hx hy => simp only [map_add, hx, hy]
    | tmul a h =>
      apply (Bialgebra.CounitAlgebra.algEquivSelf K (K ⊗[R] H) K).injective
      simp only [_root_.add_apply, map_add, extendTangent_tmul, mul_add]
  map_smul' a d := by
    ext x
    apply (Bialgebra.CounitAlgebra.algEquivSelf K (K ⊗[R] H) K).injective
    simp only [RingHom.id_apply, algEquivSelf_derivation_smul_apply]
    induction x using TensorProduct.inductionOn with
    | add x y hx hy => simp only [map_add, mul_add, hx, hy]
    | tmul b h =>
      simp only [extendTangent_tmul, algEquivSelf_derivation_smul_apply]
      ring

/-- The linear comparison applies by extending the tangent vector. -/
private theorem tangentBaseChangeLinearEquiv_apply
    (d : Derivation R H (Bialgebra.CounitAlgebra R H K)) :
    tangentBaseChangeLinearEquiv d = extendTangent d := rfl

/-- The inverse linear comparison applies by restricting the tangent vector. -/
private theorem tangentBaseChangeLinearEquiv_symm_apply
    (d : Derivation K (K ⊗[R] H) (Bialgebra.CounitAlgebra K (K ⊗[R] H) K)) :
    tangentBaseChangeLinearEquiv.symm d = restrictTangent d := rfl

private theorem restrictTangent_lie
    (d e : Derivation K (K ⊗[R] H) (Bialgebra.CounitAlgebra K (K ⊗[R] H) K)) :
    restrictTangent ⁅d, e⁆ = ⁅restrictTangent d, restrictTangent e⁆ := by
  ext h
  apply (Bialgebra.CounitAlgebra.algEquivSelf R H K).injective
  rw [restrictTangent_apply, Derivation.bracket_apply, Derivation.bracket_apply]
  simp only [map_sub, TensorProduct.comul_tmul, CommSemiring.comul_apply]
  induction Coalgebra.comul (R := R) h using TensorProduct.inductionOn with
  | add x y hx hy =>
    simpa only [tmul_add, map_add, add_sub_add_comm] using congrArg₂ (· + ·) hx hy
  | tmul x y =>
    simp only [AlgebraTensorModule.tensorTensorTensorComm_tmul, TensorProduct.map_tmul,
      LinearMap.mul'_apply, Derivation.coeFn_coe, map_mul, restrictTangent_apply]

/-- The Lie algebra of a base-changed affine monoid is its coefficient-valued tangent Lie
algebra. The comparison preserves the convolution bracket and needs no flatness assumption. -/
def tangentBaseChangeLieEquiv :
    Derivation R H (Bialgebra.CounitAlgebra R H K) ≃ₗ⁅K⁆
      Derivation K (K ⊗[R] H) (Bialgebra.CounitAlgebra K (K ⊗[R] H) K) :=
  { tangentBaseChangeLinearEquiv with
    map_lie' := fun {d e} ↦ by
      apply tangentBaseChangeLinearEquiv.symm.injective
      exact (restrictTangent_extendTangent ⁅d, e⁆).trans
        ((congrArg₂ (fun x y ↦ ⁅x, y⁆)
          (restrictTangent_extendTangent d) (restrictTangent_extendTangent e)).symm.trans
            (restrictTangent_lie (extendTangent d) (extendTangent e)).symm) }

/-- Base change extends a tangent vector by `K`-linearity. -/
@[simp]
theorem tangentBaseChangeLieEquiv_tmul
    (d : Derivation R H (Bialgebra.CounitAlgebra R H K)) (a : K) (h : H) :
    tangentBaseChangeLieEquiv d (a ⊗ₜ[R] h) =
      (Bialgebra.CounitAlgebra.algEquivSelf K (K ⊗[R] H) K).symm
        (a * Bialgebra.CounitAlgebra.algEquivSelf R H K (d h)) := by
  apply (Bialgebra.CounitAlgebra.algEquivSelf K (K ⊗[R] H) K).injective
  rw [AlgEquiv.apply_symm_apply]
  -- The Lie comparison retains the underlying linear equivalence.
  change Bialgebra.CounitAlgebra.algEquivSelf K (K ⊗[R] H) K
    (tangentBaseChangeLinearEquiv d (a ⊗ₜ[R] h)) = _
  rw [tangentBaseChangeLinearEquiv_apply]
  exact extendTangent_tmul d a h

/-- The inverse Lie comparison restricts along `h ↦ 1 ⊗ h`. -/
@[simp]
theorem tangentBaseChangeLieEquiv_symm_apply
    (d : Derivation K (K ⊗[R] H) (Bialgebra.CounitAlgebra K (K ⊗[R] H) K)) (h : H) :
    tangentBaseChangeLieEquiv.symm d h =
      (Bialgebra.CounitAlgebra.algEquivSelf R H K).symm
        (Bialgebra.CounitAlgebra.algEquivSelf K (K ⊗[R] H) K (d (1 ⊗ₜ[R] h))) := by
  apply (Bialgebra.CounitAlgebra.algEquivSelf R H K).injective
  rw [AlgEquiv.apply_symm_apply]
  -- The inverse Lie comparison retains the inverse linear equivalence.
  change Bialgebra.CounitAlgebra.algEquivSelf R H K
    (tangentBaseChangeLinearEquiv.symm d h) = _
  rw [tangentBaseChangeLinearEquiv_symm_apply]
  exact restrictTangent_apply d h

end

/-- Extension of the ground field preserves the dimension of the Lie algebra of an affine
monoid. This compares the Lie algebras of the original and base-changed coordinate rings, not
merely their coefficient spaces. Without finiteness of the augmentation cotangent space, this is
an equality in Mathlib's finite-rank convention, where infinite-dimensional spaces have `finrank`
zero. -/
theorem finrank_lie_baseChange {k K H : Type*} [Field k] [Field K] [Algebra k K]
    [CommRing H] [Bialgebra k H] :
    Module.finrank K
        (Derivation K (K ⊗[k] H) (Bialgebra.CounitAlgebra K (K ⊗[k] H) K)) =
      Module.finrank k (Derivation k H (Bialgebra.CounitAlgebra k H k)) :=
  (tangentBaseChangeLieEquiv (R := k) (K := K) (H := H)).toLinearEquiv.finrank_eq.symm.trans
    Derivation.finrank_tangent_baseChange

/-- Extension of the ground field preserves and reflects nondegeneracy of the Killing form of the
Lie algebra of an affine monoid: the Lie algebra of `K ⊗[k] H` has nondegenerate Killing form
exactly when `Lie(G)` does. When the augmentation cotangent space is infinite-dimensional, neither
Lie algebra is Killing in Mathlib's convention, where the trace on a module without a finite
basis is zero. -/
theorem isKilling_lie_baseChange_iff {k K H : Type*} [Field k] [Field K] [Algebra k K]
    [CommRing H] [Bialgebra k H] :
    LieAlgebra.IsKilling K
        (Derivation K (K ⊗[k] H) (Bialgebra.CounitAlgebra K (K ⊗[k] H) K)) ↔
      LieAlgebra.IsKilling k (Derivation k H (Bialgebra.CounitAlgebra k H k)) := by
  by_cases hV : Module.Finite k (Bialgebra.CotangentSpace k H)
  · let e := Derivation.tangentScalarExtensionLieEquiv.trans
      (tangentBaseChangeLieEquiv (R := k) (K := K) (H := H))
    constructor
    · intro
      have := LieAlgebra.isKilling_of_equiv e.symm
      have := (isKilling_baseChange_iff k K _).1 this
      exact LieAlgebra.isKilling_of_equiv Derivation.cotangentDualLieEquiv
    · intro
      have : LieAlgebra.IsKilling k (Module.Dual k (Bialgebra.CotangentSpace k H)) :=
        LieAlgebra.isKilling_of_equiv Derivation.cotangentDualLieEquiv.symm
      have := (isKilling_baseChange_iff k K _).2 this
      exact LieAlgebra.isKilling_of_equiv e
  · refine iff_of_false (fun hK ↦ hV ?_) (fun hk ↦ hV ?_)
    · have := finite_of_isKilling (R := K)
        (L := Derivation K (K ⊗[k] H) (Bialgebra.CounitAlgebra K (K ⊗[k] H) K))
      have hdual : Module.Finite K (K ⊗[k] Bialgebra.CotangentSpace k H →ₗ[K] K) :=
        Module.Finite.equiv
          ((tangentBaseChangeLieEquiv (R := k) (K := K) (H := H)).toLinearEquiv.symm.trans
            ((Derivation.cotangentLinearEquiv (R := k) (A := H) (B := K)).symm.trans
              (LinearMap.liftBaseChangeEquiv K)))
      have : Module.Finite K (K ⊗[k] Bialgebra.CotangentSpace k H) :=
        (Module.finite_dual_iff K).1 hdual
      exact Module.Finite.of_finite_tensorProduct_of_faithfullyFlat K
    · have := finite_of_isKilling (R := k) (L := Derivation k H (Bialgebra.CounitAlgebra k H k))
      exact (Module.finite_dual_iff k).1
        (Module.Finite.equiv Derivation.cotangentDualLieEquiv.symm.toLinearEquiv)

end TauCeti

namespace TauCeti.Bialgebra

open scoped _root_.TensorProduct

variable {R S H : Type*} [CommRing R] [CommRing S] [Algebra R S] [CommRing H] [Bialgebra R H]

/-- The cotangent class of `s ⊗ h` in the cotangent space of `S ⊗[R] H` over `S` is `s` times the
class of `1 ⊗ h`. -/
theorem cotangentMap_tmul (s : S) (h : H) :
    Bialgebra.cotangentMap S (S ⊗[R] H) (s ⊗ₜ h) =
      s • Bialgebra.cotangentMap S (S ⊗[R] H) (1 ⊗ₜ h) := by
  rw [← LinearMap.map_smul, TensorProduct.smul_tmul', smul_eq_mul, mul_one]

/-- **A tangent vector of `Spec (S ⊗[R] H)` is determined by its values on `1 ⊗ H`**: two linear
functionals on the cotangent space of `S ⊗[R] H` over `S` agree once they agree on the cotangent
classes of the elements `1 ⊗ h`. -/
theorem dual_ext_cotangentMap_one_tmul
    {f g : Module.Dual S (Bialgebra.CotangentSpace S (S ⊗[R] H))}
    (hfg : ∀ h : H, f (Bialgebra.cotangentMap S (S ⊗[R] H) (1 ⊗ₜ h)) =
      g (Bialgebra.cotangentMap S (S ⊗[R] H) (1 ⊗ₜ h))) :
    f = g := by
  ext c
  obtain ⟨y, rfl⟩ := Bialgebra.cotangentMap_surjective S (S ⊗[R] H) c
  induction y using TensorProduct.inductionOn with
  | tmul s h => rw [cotangentMap_tmul, LinearMap.map_smul, LinearMap.map_smul, hfg]
  | add y z hy hz => simp only [map_add, hy, hz]

end TauCeti.Bialgebra

namespace Derivation

open TauCeti
open scoped TensorProduct

variable {R S H : Type*} [CommRing R] [CommRing S] [Algebra R S] [CommRing H] [Bialgebra R H]

variable [Module.Finite R (Bialgebra.CotangentSpace R H)]
  [Module.Projective R (Bialgebra.CotangentSpace R H)]

variable (R S H) in
/-- **Base change of the Lie algebra.** The Lie algebra of `Spec (S ⊗[R] H)` over `S` is the
scalar extension of the Lie algebra of `Spec H`. The comparison extends a tangent vector of `H`
`S`-linearly to `S ⊗[R] H`, through coefficient-valued tangent vectors. -/
noncomputable def cotangentDualBaseChangeEquiv :
    S ⊗[R] Module.Dual R (Bialgebra.CotangentSpace R H) ≃ₗ[S]
      Module.Dual S (Bialgebra.CotangentSpace S (S ⊗[R] H)) :=
  (tangentScalarExtensionEquiv (R := R) (A := H) (B := S)).trans
    ((tangentBaseChangeLieEquiv (R := R) (K := S) (H := H)).toLinearEquiv.trans
      (cotangentLinearEquiv (R := S) (A := S ⊗[R] H) (B := S)).symm)

/-- Under cotangent duality, the comparison of Lie algebras is the extension of tangent vectors
from `H` to `S ⊗[R] H`. -/
@[simp]
theorem cotangentLinearEquiv_cotangentDualBaseChangeEquiv
    (z : S ⊗[R] Module.Dual R (Bialgebra.CotangentSpace R H)) :
    cotangentLinearEquiv (R := S) (A := S ⊗[R] H) (B := S) (cotangentDualBaseChangeEquiv R S H z) =
      tangentBaseChangeLieEquiv (R := R) (K := S) (H := H)
        (tangentScalarExtensionEquiv (R := R) (A := H) (B := S) z) := by
  simp only [cotangentDualBaseChangeEquiv, LinearEquiv.trans_apply, LinearEquiv.apply_symm_apply,
    LieEquiv.coe_toLinearEquiv]

/-- The base-changed functional `s ⊗ x` takes the value `s * x (dh)` on the cotangent class of
`1 ⊗ h`. These classes span the cotangent space of `S ⊗[R] H` over `S`, so this determines the
comparison. -/
@[simp]
theorem cotangentDualBaseChangeEquiv_tmul_apply_cotangentMap (s : S)
    (x : Module.Dual R (Bialgebra.CotangentSpace R H)) (h : H) :
    cotangentDualBaseChangeEquiv R S H (s ⊗ₜ x)
        (Bialgebra.cotangentMap S (S ⊗[R] H) (1 ⊗ₜ h)) =
      s * algebraMap R S (x (Bialgebra.cotangentMap R H h)) := by
  rw [← cotangentLinearEquiv_apply_apply, ← algEquivSelf_tangentScalarExtensionEquiv_tmul_apply]
  simp only [cotangentDualBaseChangeEquiv, LinearEquiv.trans_apply, LinearEquiv.apply_symm_apply,
    LieEquiv.coe_toLinearEquiv, tangentBaseChangeLieEquiv_tmul, one_mul,
    Bialgebra.CounitAlgebra.algEquivSelf_symm_apply]

/-- The tangent vector of `Spec (S ⊗[R] H)` attached to the scalar extension `s ⊗ x` takes the
value `s * x (dh)` on `1 ⊗ h`, after identifying counit-valued coefficients with `S`. -/
theorem algEquivSelf_cotangentLinearEquiv_cotangentDualBaseChangeEquiv_tmul_apply (s : S)
    (x : Module.Dual R (Bialgebra.CotangentSpace R H)) (h : H) :
    Bialgebra.CounitAlgebra.algEquivSelf S (S ⊗[R] H) S
        (cotangentLinearEquiv (B := S) (cotangentDualBaseChangeEquiv R S H (s ⊗ₜ x)) (1 ⊗ₜ h)) =
      s * algebraMap R S (x (Bialgebra.cotangentMap R H h)) := by
  rw [algEquivSelf_cotangentLinearEquiv_apply, cotangentDualBaseChangeEquiv_tmul_apply_cotangentMap]

/-- **The comparison of Lie algebras is natural**: for a bialgebra morphism `φ : H →ₐc[R] L`, the
differential of its base change `id ⊗ φ` corresponds to the scalar extension of the differential
of `φ`. -/
theorem dualCotangentMap_map_cotangentDualBaseChangeEquiv_tmul {L : Type*} [CommRing L]
    [Bialgebra R L] [Module.Finite R (Bialgebra.CotangentSpace R L)]
    [Module.Projective R (Bialgebra.CotangentSpace R L)] (φ : H →ₐc[R] L) (s : S)
    (x : Module.Dual R (Bialgebra.CotangentSpace R L)) :
    dualCotangentMap (Bialgebra.TensorProduct.map (BialgHom.id S S) φ)
        (cotangentDualBaseChangeEquiv R S L (s ⊗ₜ x)) =
      cotangentDualBaseChangeEquiv R S H (s ⊗ₜ dualCotangentMap φ x) := by
  refine Bialgebra.dual_ext_cotangentMap_one_tmul fun h ↦ ?_
  rw [dualCotangentMap_apply_cotangentMap, Bialgebra.TensorProduct.map_tmul, BialgHom.id_apply,
    cotangentDualBaseChangeEquiv_tmul_apply_cotangentMap,
    cotangentDualBaseChangeEquiv_tmul_apply_cotangentMap, dualCotangentMap_apply_cotangentMap]

/-- **Base change along the identity is trivial on Lie algebras**: across the identification
`H ≃ R ⊗[R] H`, the comparison of Lie algebras is the identification
`R ⊗[R] Lie(G) ≃ Lie(G)`. -/
theorem dualCotangentMap_lid_symm_cotangentDualBaseChangeEquiv
    (z : R ⊗[R] Module.Dual R (Bialgebra.CotangentSpace R H)) :
    dualCotangentMap ((Bialgebra.TensorProduct.lid R H).symm : H →ₐc[R] R ⊗[R] H)
        (cotangentDualBaseChangeEquiv R R H z) =
      TensorProduct.lid R _ z := by
  induction z using TensorProduct.inductionOn with
  | add y z hy hz => simp only [map_add, hy, hz]
  | tmul c x =>
    ext v
    obtain ⟨h, rfl⟩ := Bialgebra.cotangentMap_surjective R H v
    rw [dualCotangentMap_apply_cotangentMap, BialgEquiv.coe_toBialgHom,
      Bialgebra.TensorProduct.lid_symm_apply, cotangentDualBaseChangeEquiv_tmul_apply_cotangentMap,
      TensorProduct.lid_tmul, LinearMap.smul_apply, smul_eq_mul, Algebra.algebraMap_self,
      RingHom.id_apply]

/-- **The comparison of Lie algebras composes in stages.** For a tower `R → S → T`, extending a
tangent vector of `Spec H` to `Spec (S ⊗[R] H)` and then to `Spec (T ⊗[S] (S ⊗[R] H))` agrees,
across the tower identification `T ⊗[S] (S ⊗[R] H) ≃ T ⊗[R] H`, with extending it to
`Spec (T ⊗[R] H)` in one step. -/
theorem dualCotangentMap_baseChangeTowerBialgEquiv_cotangentDualBaseChangeEquiv_tmul
    {T : Type*} [CommRing T] [Algebra R T] [Algebra S T] [IsScalarTower R S T]
    [Module.Finite S (Bialgebra.CotangentSpace S (S ⊗[R] H))]
    [Module.Projective S (Bialgebra.CotangentSpace S (S ⊗[R] H))]
    (t : T) (x : Module.Dual R (Bialgebra.CotangentSpace R H)) :
    dualCotangentMap (Bialgebra.TensorProduct.baseChangeTowerBialgEquiv R S H T :
          T ⊗[S] (S ⊗[R] H) →ₐc[T] T ⊗[R] H)
        (cotangentDualBaseChangeEquiv R T H (t ⊗ₜ x)) =
      cotangentDualBaseChangeEquiv S T (S ⊗[R] H)
        (t ⊗ₜ cotangentDualBaseChangeEquiv R S H (1 ⊗ₜ x)) := by
  refine Bialgebra.dual_ext_cotangentMap_one_tmul fun y ↦ ?_
  rw [dualCotangentMap_apply_cotangentMap, cotangentDualBaseChangeEquiv_tmul_apply_cotangentMap]
  induction y using TensorProduct.inductionOn with
  | add y z hy hz => simp only [TensorProduct.tmul_add, map_add, mul_add, hy, hz]
  | tmul s h =>
    rw [BialgEquiv.coe_toBialgHom, TensorProduct.baseChangeTowerBialgEquiv_one_tmul,
      Algebra.TensorProduct.map_tmul, AlgHom.id_apply, Bialgebra.cotangentMap_tmul,
      LinearMap.map_smul, cotangentDualBaseChangeEquiv_tmul_apply_cotangentMap,
      Bialgebra.cotangentMap_tmul, LinearMap.map_smul,
      cotangentDualBaseChangeEquiv_tmul_apply_cotangentMap, smul_eq_mul, smul_eq_mul, one_mul,
      map_mul, IsScalarTower.coe_toAlgHom', IsScalarTower.algebraMap_apply R S T]
    ring

end Derivation
