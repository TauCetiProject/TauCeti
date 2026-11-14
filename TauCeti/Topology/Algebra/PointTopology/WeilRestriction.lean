/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.HopfAlgebra.WeilRestriction
public import TauCeti.Topology.Algebra.PointTopology.Group
public import Mathlib.Topology.Algebra.Module.ModuleTopology
import TauCeti.Topology.Algebra.Module.ModuleTopology

/-!
# The point topology and Weil restriction

For a finite projective `A`-algebra `B` and a finitely presented `B`-algebra `C`, the Weil
restriction adjunction is a homeomorphism on `T`-points when `T` is a topological commutative
`A`-algebra and `B ⊗[A] T` carries its `T`-module topology (`homHomeomorph`).

For a topological ring `A` and `B` with its `A`-module topology, `pointsHomeomorph` specializes
this to a homeomorphism between `A`-points of the Weil restriction and `B`-points of `C`.
This identifies rational point topologies under restriction of scalars, for example for finite
extensions of local fields and for the real points of the Deligne torus.

When `H` is a finitely presented commutative `B`-bialgebra (or Hopf algebra), these homeomorphisms
upgrade to topological multiplicative equivalences of convolution monoids (or topological groups)
`pointsContinuousMulEquiv` and `basePointsContinuousMulEquiv`. Given a continuous scalar-extension
equivalence `T ⊗[A] B ≃A[T] S` sending `1 ⊗ b` to `algebraMap B S b`,
`pointsContinuousMulEquivOfBaseChange` combines `pointsContinuousMulEquiv` with the continuous
factor swap `baseChangeRightContinuousEquiv` to identify `(Res_{B/A} G)(T)` with `G(S)` as
topological monoids (or topological groups).

The comparison uses `TauCeti.Algebra.WeilRestriction.homEquiv` and the right tensor unitor.
The inverse is continuous because the linear coefficients of the universal point generate the
Weil restriction. No basis, Hausdorff assumption, or field hypothesis is needed.

## References

* B. Conrad, *Weil and Grothendieck approaches to adelic points*, Exercise 2.4, p. 3.
-/

public noncomputable section

open TensorProduct Topology
open scoped TauCeti.PointTopology

namespace TauCeti.Algebra.WeilRestriction

section Ring

variable (A B C : Type*) [CommRing A] [CommRing B] [CommRing C]
  [Algebra A B] [Algebra B C] [Module.Finite A B] [Module.Projective A B]
  [Algebra.FinitePresentation B C]

section General

attribute [local instance] Algebra.TensorProduct.rightAlgebra

variable (T : Type*) [CommRing T] [Algebra A T] [TopologicalSpace T] [IsTopologicalRing T]
  [TopologicalSpace (B ⊗[A] T)] [IsModuleTopology T (B ⊗[A] T)]

/-- The Weil restriction adjunction is a homeomorphism on points over any topological
`A`-algebra `T` when the tensor product has its `T`-module topology (acting on the right factor). -/
def homHomeomorph : (WeilRestriction A B C →ₐ[A] T) ≃ₜ (C →ₐ[B] B ⊗[A] T) where
  toEquiv := homEquiv A B C T
  continuous_toFun := by
    let _ : ContinuousAdd (B ⊗[A] T) := IsModuleTopology.toContinuousAdd T _
    have h (z : B ⊗[A] WeilRestriction A B C) :
        Continuous fun g : WeilRestriction A B C →ₐ[A] T ↦
          Algebra.TensorProduct.lTensor (S := B) B g z := by
      induction z using TensorProduct.inductionOn with
      | tmul b w =>
        have hb := IsModuleTopology.continuous_of_linearMap
          ((Algebra.TensorProduct.commRight A T B).toLinearMap.comp
            ((TensorProduct.AlgebraTensorModule.mk A T T B).flip b))
        simpa [Function.comp_def] using hb.comp (PointTopology.continuous_eval w)
      | add z w hz hw => simpa only [map_add] using hz.fun_add hw
    apply PointTopology.continuous_iff.2
    intro c
    simpa only [Equiv.toFun_as_coe, homEquiv_apply, AlgHom.comp_apply] using
      h (universalPoint A B C c)
  continuous_invFun := by
    apply (PointTopology.isEmbedding_eval_generators
      (adjoin_range_universalCoefficient (A := A) (B := B) (C := C))).isInducing.continuous_iff.2
    apply continuous_pi
    rintro ⟨φ, c⟩
    have hφ := IsModuleTopology.continuous_of_linearMap
      ((((Algebra.linearMap A T).comp φ).liftBaseChange T).comp
        (Algebra.TensorProduct.commRight A T B).symm.toLinearMap)
    convert hφ.comp (PointTopology.continuous_eval (k := B) (A := C) c) using 1
    ext x
    simp only [Equiv.invFun_as_coe, map_universalCoefficient, Equiv.apply_symm_apply,
      Function.comp_apply, LinearMap.comp_apply, LinearMap.tensorComponent_eq_liftBaseChange]
    induction x c using TensorProduct.inductionOn with
    | tmul b t => simp
    | add z w hz hw => simp only [map_add, hz, hw]

/-- The general point homeomorphism is the algebraic Weil restriction adjunction. -/
@[simp]
theorem homHomeomorph_apply (g : WeilRestriction A B C →ₐ[A] T) :
    homHomeomorph A B C T g = homEquiv A B C T g := (rfl)

/-- The inverse adjunction evaluates coefficients by contraction of the original point. -/
@[simp]
theorem homHomeomorph_symm_apply_universalCoefficient (x : C →ₐ[B] B ⊗[A] T)
    (φ : Module.Dual A B) (c : C) :
    (homHomeomorph A B C T).symm x (universalCoefficient φ c) =
      LinearMap.tensorComponent φ (TensorProduct.comm A B T (x c)) := by
  rw [map_universalCoefficient]
  exact congrArg (fun y : C →ₐ[B] B ⊗[A] T ↦
    LinearMap.tensorComponent φ (TensorProduct.comm A B T (y c)))
      ((homEquiv A B C T).apply_symm_apply x)

end General

variable [TopologicalSpace A] [IsTopologicalRing A]
  [TopologicalSpace B] [IsModuleTopology A B]

/-- Restriction of scalars identifies `A`-points of the Weil restriction with `B`-points,
homeomorphically when `B` carries its finite projective `A`-module topology. -/
def pointsHomeomorph : (WeilRestriction A B C →ₐ[A] A) ≃ₜ (C →ₐ[B] B) := by
  letI : TopologicalSpace (B ⊗[A] A) := moduleTopology A (B ⊗[A] A)
  letI : IsModuleTopology A (B ⊗[A] A) := ⟨rfl⟩
  letI : ContinuousAdd B := IsModuleTopology.toContinuousAdd A B
  letI : ContinuousAdd (B ⊗[A] A) := IsModuleTopology.toContinuousAdd A _
  -- For `T = A`, the right-factor scalar action agrees with the usual base-ring action.
  -- Identify them explicitly before specializing the general homeomorphism.
  have hright : (Algebra.TensorProduct.rightAlgebra : Algebra A (B ⊗[A] A)) =
      (inferInstance : Algebra A (B ⊗[A] A)) := by
    apply Algebra.algebra_ext
    intro a
    rw [Algebra.TensorProduct.right_algebraMap_apply]
    simpa using (Algebra.TensorProduct.includeRight (R := A) (A := B) (B := A)).commutes a
  letI : @IsModuleTopology A _ (B ⊗[A] A) _
      Algebra.TensorProduct.rightAlgebra.toSMul _ := by
    rw [hright]
    infer_instance
  let e := Algebra.TensorProduct.rid A B B
  let h : (C →ₐ[B] B ⊗[A] A) ≃ₜ (C →ₐ[B] B) :=
    { toEquiv := AlgEquiv.arrowCongr (AlgEquiv.refl : C ≃ₐ[B] C) e
      continuous_toFun := PointTopology.continuous_iff.2 fun c ↦
        by simpa [Function.comp_def, AlgEquiv.arrowCongr_apply] using
            (IsModuleTopology.continuous_of_linearMap
              (e.toLinearEquiv.restrictScalars A).toLinearMap).comp
                (PointTopology.continuous_eval c)
      continuous_invFun := PointTopology.continuous_iff.2 fun c ↦
        by simpa [Function.comp_def, AlgEquiv.arrowCongr_symm, AlgEquiv.arrowCongr_apply] using
            (IsModuleTopology.continuous_of_linearMap
              (e.symm.toLinearEquiv.restrictScalars A).toLinearMap).comp
                (PointTopology.continuous_eval c) }
  exact (homHomeomorph A B C A).trans h

/-- The point comparison is the algebraic adjunction followed by the right tensor unitor. -/
@[simp]
theorem pointsHomeomorph_apply (g : WeilRestriction A B C →ₐ[A] A) (c : C) :
    pointsHomeomorph A B C g c =
      Algebra.TensorProduct.rid A B B (homEquiv A B C A g c) := (rfl)

/-- Under the algebraic adjunction, the inverse comparison is the original point followed by
the inverse right tensor unitor. -/
-- Not a simp lemma: `homEquiv_apply` already expands its left-hand side.
theorem homEquiv_pointsHomeomorph_symm (x : C →ₐ[B] B) :
    homEquiv A B C A ((pointsHomeomorph A B C).symm x) =
      (Algebra.TensorProduct.rid A B B).symm.toAlgHom.comp x := by
  ext c
  apply (Algebra.TensorProduct.rid A B B).injective
  have hx := congrArg (fun y : C →ₐ[B] B ↦ y c)
    ((pointsHomeomorph A B C).apply_symm_apply x)
  rw [pointsHomeomorph_apply] at hx
  simpa only [AlgHom.comp_apply, AlgEquiv.coe_toAlgHom, AlgEquiv.apply_symm_apply] using hx

/-- The inverse comparison evaluates a universal coefficient by applying its linear functional
to the corresponding value of the original point. -/
@[simp]
theorem pointsHomeomorph_symm_apply_universalCoefficient (x : C →ₐ[B] B)
    (φ : Module.Dual A B) (c : C) :
    (pointsHomeomorph A B C).symm x (universalCoefficient φ c) = φ (x c) := by
  rw [map_universalCoefficient, homEquiv_pointsHomeomorph_symm]
  simp

end Ring

section Bialgebra

section General

attribute [local instance] Algebra.TensorProduct.rightAlgebra

variable (A B H T : Type*) [CommRing A] [CommRing B] [CommRing H] [CommRing T]
  [Algebra A B] [Module.Finite A B] [Module.Projective A B]
  [Bialgebra B H] [Algebra.FinitePresentation B H]
  [Algebra A T] [TopologicalSpace T] [IsTopologicalRing T]
  [TopologicalSpace (B ⊗[A] T)] [IsModuleTopology T (B ⊗[A] T)]

/-- **The Weil restriction adjunction as a topological multiplicative equivalence.** When `H` is a
finitely presented commutative `B`-bialgebra and `B ⊗[A] T` carries its right `T`-module topology,
`WeilRestriction.pointsMulEquiv` is a topological multiplicative equivalence (hence a topological
group isomorphism when `H` is a Hopf algebra). -/
def pointsContinuousMulEquiv :
    WithConv (WeilRestriction A B H →ₐ[A] T) ≃ₜ* WithConv (H →ₐ[B] B ⊗[A] T) where
  toMulEquiv := pointsMulEquiv A B H T
  continuous_toFun :=
    PointTopology.isHomeomorph_ofConv.isEmbedding.isInducing.continuous_iff.2 <|
      ((homHomeomorph A B H T).continuous.comp
        PointTopology.isHomeomorph_ofConv.continuous).congr
        fun f ↦ (pointsMulEquiv_apply f).symm
  continuous_invFun :=
    PointTopology.isHomeomorph_ofConv.isEmbedding.isInducing.continuous_iff.2 <|
      ((homHomeomorph A B H T).symm.continuous.comp
        PointTopology.isHomeomorph_ofConv.continuous).congr
        fun g ↦ (pointsMulEquiv_symm_apply g).symm

variable {A B H T}

/-- Forgetting continuity from `pointsContinuousMulEquiv` recovers `pointsMulEquiv`. -/
@[simp]
theorem toMulEquiv_pointsContinuousMulEquiv :
    (pointsContinuousMulEquiv A B H T :
        WithConv (WeilRestriction A B H →ₐ[A] T) ≃* WithConv (H →ₐ[B] B ⊗[A] T)) =
      pointsMulEquiv A B H T := (rfl)

/-- Evaluating `pointsContinuousMulEquiv` applies `homEquiv`. -/
@[simp]
theorem pointsContinuousMulEquiv_apply (f : WithConv (WeilRestriction A B H →ₐ[A] T)) :
    (pointsContinuousMulEquiv A B H T f).ofConv = homEquiv A B H T f.ofConv :=
  pointsMulEquiv_apply f

/-- Evaluating the inverse of `pointsContinuousMulEquiv` applies `(homEquiv A B H T).symm`. -/
@[simp]
theorem pointsContinuousMulEquiv_symm_apply (g : WithConv (H →ₐ[B] B ⊗[A] T)) :
    ((pointsContinuousMulEquiv A B H T).symm g).ofConv = (homEquiv A B H T).symm g.ofConv :=
  pointsMulEquiv_symm_apply g

end General

section BasePoints

variable (A B H : Type*) [CommRing A] [CommRing B] [CommRing H]
  [Algebra A B] [Module.Finite A B] [Module.Projective A B]
  [Bialgebra B H] [Algebra.FinitePresentation B H]
  [TopologicalSpace A] [IsTopologicalRing A] [TopologicalSpace B] [IsModuleTopology A B]

/-- **Rational points of the Weil restriction as a topological monoid or group.** When `B` carries
its `A`-module topology, `WeilRestriction.basePointsMulEquiv` is a topological multiplicative
equivalence `WithConv (WeilRestriction A B H →ₐ[A] A) ≃ₜ* WithConv (H →ₐ[B] B)`. -/
def basePointsContinuousMulEquiv :
    WithConv (WeilRestriction A B H →ₐ[A] A) ≃ₜ* WithConv (H →ₐ[B] B) where
  toMulEquiv := basePointsMulEquiv A B H
  continuous_toFun :=
    (PointTopology.isHomeomorph_ofConv.isEmbedding.isInducing.continuous_iff.2 <|
      (pointsHomeomorph A B H).continuous.comp PointTopology.isHomeomorph_ofConv.continuous).congr
      fun f ↦ WithConv.ofConv_injective <| AlgHom.ext fun h ↦ by simp
  continuous_invFun := by
    have hc : Continuous fun g : WithConv (H →ₐ[B] B) ↦
        WithConv.toConv ((pointsHomeomorph A B H).symm g.ofConv) :=
      PointTopology.isHomeomorph_ofConv.isEmbedding.isInducing.continuous_iff.2 <|
        (pointsHomeomorph A B H).symm.continuous.comp PointTopology.isHomeomorph_ofConv.continuous
    refine hc.congr fun g ↦ (pointsMulEquiv A B H A).injective ?_
    rw [MulEquiv.invFun_eq_symm, pointsMulEquiv_basePointsMulEquiv_symm]
    refine WithConv.ofConv_injective ?_
    rw [pointsMulEquiv_apply, WithConv.ofConv_toConv, homEquiv_pointsHomeomorph_symm,
      AlgHom.mapValue_apply, WithConv.ofConv_toConv]

variable {A B H}

/-- Forgetting continuity from `basePointsContinuousMulEquiv` recovers `basePointsMulEquiv`. -/
@[simp]
theorem toMulEquiv_basePointsContinuousMulEquiv :
    (basePointsContinuousMulEquiv A B H :
        WithConv (WeilRestriction A B H →ₐ[A] A) ≃* WithConv (H →ₐ[B] B)) =
      basePointsMulEquiv A B H := (rfl)

/-- Evaluating `basePointsContinuousMulEquiv` applies `pointsMulEquiv` followed by the right tensor
unitor. -/
@[simp]
theorem basePointsContinuousMulEquiv_apply (f : WithConv (WeilRestriction A B H →ₐ[A] A)) (h : H) :
    (basePointsContinuousMulEquiv A B H f).ofConv h =
      Algebra.TensorProduct.rid A B B ((pointsMulEquiv A B H A f).ofConv h) :=
  basePointsMulEquiv_apply f h

end BasePoints

section BaseChange

attribute [local instance] Algebra.TensorProduct.rightAlgebra

section Swap

variable {A B T S : Type*} [CommRing A] [CommRing B] [CommRing T] [CommRing S]
  [Algebra A B] [Algebra A T] [Algebra B S] [Algebra T S]
  [TopologicalSpace T] [TopologicalSpace S]
  [TopologicalSpace (B ⊗[A] T)] [IsModuleTopology T (B ⊗[A] T)]
  [TopologicalSpace (T ⊗[A] B)] [IsModuleTopology T (T ⊗[A] B)]

/-- Continuous upgrade of `WeilRestriction.baseChangeRightAlgEquiv`: when `B ⊗[A] T` and `T ⊗[A] B`
carry their `T`-module topologies, swapping tensor factors and applying `e : T ⊗[A] B ≃A[T] S` is a
continuous `B`-algebra equivalence `B ⊗[A] T ≃A[B] S`. -/
def baseChangeRightContinuousEquiv (e : T ⊗[A] B ≃A[T] S)
    (he : ∀ b : B, e (1 ⊗ₜ[A] b) = algebraMap B S b) : B ⊗[A] T ≃A[B] S where
  toAlgEquiv := baseChangeRightAlgEquiv e.toAlgEquiv he
  continuous_toFun := by
    let hcomm := (Algebra.TensorProduct.commRight A T B).symm.toLinearEquiv
      |>.toContinuousLinearEquivOfIsModuleTopology
    have hswap (z : B ⊗[A] T) :
        (Algebra.TensorProduct.commRight A T B).symm z =
          Algebra.TensorProduct.comm A B T z := by
      induction z using TensorProduct.inductionOn with
      | tmul b t => rfl
      | add x y hx hy => simp only [map_add, hx, hy]
    refine (e.continuous.comp hcomm.continuous).congr fun z ↦ ?_
    change e (hcomm z) = baseChangeRightAlgEquiv e.toAlgEquiv he z
    rw [LinearEquiv.coe_toContinuousLinearEquivOfIsModuleTopology, AlgEquiv.toLinearEquiv_apply,
      hswap, baseChangeRightAlgEquiv_apply]
    rfl
  continuous_invFun := by
    let hcomm := (Algebra.TensorProduct.commRight A T B).symm.toLinearEquiv
      |>.toContinuousLinearEquivOfIsModuleTopology
    have hswap (w : T ⊗[A] B) :
        (Algebra.TensorProduct.commRight A T B).symm.toLinearEquiv.symm w =
          (Algebra.TensorProduct.comm A B T).symm w := by
      induction w using TensorProduct.inductionOn with
      | tmul t b => rfl
      | add x y hx hy => simp only [map_add, hx, hy]
    refine (hcomm.symm.continuous.comp e.symm.continuous).congr fun s ↦ ?_
    change hcomm.symm (e.symm s) = (baseChangeRightAlgEquiv e.toAlgEquiv he).symm s
    rw [LinearEquiv.symm_toContinuousLinearEquivOfIsModuleTopology,
      LinearEquiv.coe_toContinuousLinearEquivOfIsModuleTopology, hswap,
      baseChangeRightAlgEquiv_symm_apply]
    rfl

/-- Forgetting continuity from `baseChangeRightContinuousEquiv` recovers
`baseChangeRightAlgEquiv`. -/
@[simp]
theorem baseChangeRightContinuousEquiv_toAlgEquiv (e : T ⊗[A] B ≃A[T] S)
    (he : ∀ b : B, e (1 ⊗ₜ[A] b) = algebraMap B S b) :
    (baseChangeRightContinuousEquiv e he).toAlgEquiv =
      baseChangeRightAlgEquiv e.toAlgEquiv he := (rfl)

/-- `baseChangeRightContinuousEquiv` swaps tensor factors and applies `e`. -/
@[simp]
theorem baseChangeRightContinuousEquiv_apply (e : T ⊗[A] B ≃A[T] S)
    (he : ∀ b : B, e (1 ⊗ₜ[A] b) = algebraMap B S b) (z : B ⊗[A] T) :
    baseChangeRightContinuousEquiv e he z = e (Algebra.TensorProduct.comm A B T z) :=
  baseChangeRightAlgEquiv_apply e.toAlgEquiv he z

end Swap

variable (A B H : Type*) [CommRing A] [CommRing B] [CommRing H] [Algebra A B]
  [Module.Finite A B] [Module.Projective A B] [Bialgebra B H] [Algebra.FinitePresentation B H]
variable {T S : Type*} [CommRing T] [CommRing S] [Algebra A T] [Algebra B S] [Algebra T S]
  [TopologicalSpace T] [IsTopologicalRing T] [TopologicalSpace S]
  [TopologicalSpace (T ⊗[A] B)] [IsModuleTopology T (T ⊗[A] B)]

private def pointsContinuousMulEquivOfBaseChangeAux (e : T ⊗[A] B ≃A[T] S)
    (he : ∀ b : B, e (1 ⊗ₜ[A] b) = algebraMap B S b) :
    WithConv (WeilRestriction A B H →ₐ[A] T) ≃ₜ* WithConv (H →ₐ[B] S) :=
  letI : TopologicalSpace (B ⊗[A] T) := moduleTopology T (B ⊗[A] T)
  haveI : IsModuleTopology T (B ⊗[A] T) := ⟨rfl⟩
  (pointsContinuousMulEquiv A B H T).trans
    (baseChangeRightContinuousEquiv e he).mapValueContinuousMulEquiv

private theorem toMulEquiv_pointsContinuousMulEquivOfBaseChangeAux (e : T ⊗[A] B ≃A[T] S)
    (he : ∀ b : B, e (1 ⊗ₜ[A] b) = algebraMap B S b) :
    (pointsContinuousMulEquivOfBaseChangeAux A B H e he).toMulEquiv =
      pointsMulEquivOfBaseChange A B H e.toAlgEquiv he := by
  let _ : TopologicalSpace (B ⊗[A] T) := moduleTopology T (B ⊗[A] T)
  have _ : IsModuleTopology T (B ⊗[A] T) := ⟨rfl⟩
  change (pointsContinuousMulEquiv A B H T).toMulEquiv.trans
    (baseChangeRightContinuousEquiv e he).mapValueContinuousMulEquiv.toMulEquiv = _
  simp only [ContinuousMulEquiv.toMulEquiv_eq_coe, toMulEquiv_pointsContinuousMulEquiv,
    ContinuousAlgEquiv.toMulEquiv_mapValueContinuousMulEquiv,
    baseChangeRightContinuousEquiv_toAlgEquiv, pointsMulEquivOfBaseChange_eq_trans]

/-- **Topological points of a Weil restriction along a scalar-extension equivalence.** Given a
continuous `T`-algebra equivalence `e : T ⊗[A] B ≃A[T] S` sending `1 ⊗ b` to `algebraMap B S b`
for the `T`-module topology on `T ⊗[A] B`, `WeilRestriction.pointsMulEquivOfBaseChange` is a
topological multiplicative equivalence `(Res_{B/A} G)(T) ≃ₜ* G(S)`. -/
def pointsContinuousMulEquivOfBaseChange (e : T ⊗[A] B ≃A[T] S)
    (he : ∀ b : B, e (1 ⊗ₜ[A] b) = algebraMap B S b) :
    WithConv (WeilRestriction A B H →ₐ[A] T) ≃ₜ* WithConv (H →ₐ[B] S) where
  toMulEquiv := pointsMulEquivOfBaseChange A B H e.toAlgEquiv he
  continuous_toFun :=
    (pointsContinuousMulEquivOfBaseChangeAux A B H e he).continuous.congr fun x ↦
      DFunLike.congr_fun (toMulEquiv_pointsContinuousMulEquivOfBaseChangeAux A B H e he) x
  continuous_invFun := by
    refine (pointsContinuousMulEquivOfBaseChangeAux A B H e he).symm.continuous.congr fun y ↦ ?_
    rw [MulEquiv.invFun_eq_symm,
      ← toMulEquiv_pointsContinuousMulEquivOfBaseChangeAux A B H e he]
    rfl

variable {A B H}

/-- Forgetting continuity from `pointsContinuousMulEquivOfBaseChange` recovers
`pointsMulEquivOfBaseChange`. -/
@[simp]
theorem toMulEquiv_pointsContinuousMulEquivOfBaseChange (e : T ⊗[A] B ≃A[T] S)
    (he : ∀ b : B, e (1 ⊗ₜ[A] b) = algebraMap B S b) :
    (pointsContinuousMulEquivOfBaseChange A B H e he :
        WithConv (WeilRestriction A B H →ₐ[A] T) ≃* WithConv (H →ₐ[B] S)) =
      pointsMulEquivOfBaseChange A B H e.toAlgEquiv he := (rfl)

/-- Evaluating `pointsContinuousMulEquivOfBaseChange` swaps the tensor factors of `pointsMulEquiv`
and applies `e`. -/
@[simp]
theorem pointsContinuousMulEquivOfBaseChange_apply (e : T ⊗[A] B ≃A[T] S)
    (he : ∀ b : B, e (1 ⊗ₜ[A] b) = algebraMap B S b)
    (x : WithConv (WeilRestriction A B H →ₐ[A] T)) (h : H) :
    (pointsContinuousMulEquivOfBaseChange A B H e he x).ofConv h =
      e (Algebra.TensorProduct.comm A B T ((pointsMulEquiv A B H T x).ofConv h)) :=
  pointsMulEquivOfBaseChange_apply e.toAlgEquiv he x h

end BaseChange

end Bialgebra

end TauCeti.Algebra.WeilRestriction
