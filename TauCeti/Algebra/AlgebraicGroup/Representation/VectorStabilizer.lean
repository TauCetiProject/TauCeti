/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.HopfIdeal.Conjugation
public import TauCeti.Algebra.AlgebraicGroup.HopfIdeal.Dimension
public import TauCeti.Algebra.AlgebraicGroup.Representation.Stabilizer
public import TauCeti.Algebra.Coalgebra.Comodule.Product
public import TauCeti.Algebra.Coalgebra.Comodule.Trivial
import TauCeti.Algebra.AlgebraicGroup.Representation.PointConjugation
import TauCeti.Algebra.AlgebraicGroup.Tangent.Dimension
import TauCeti.Algebra.AlgebraicGroup.Tangent.FiniteType
import TauCeti.Algebra.Coalgebra.Comodule.MatrixCoefficient.Product
import TauCeti.LinearAlgebra.TensorProduct.Separation

/-!
# The stabilizer of a vector in a representation

Let `H` be a commutative Hopf algebra over a field `k` and `M` a right `H`-comodule, that is, a
representation of the affine group `G = Spec H`. A vector `v ∈ M` has a stabilizer: the closed
subgroup of `G` whose points fix `v`. In coordinates it is cut out by the equations
`c(φ, v) = φ(v)` for the matrix coefficients of `v`, with `φ` running over the functionals on `M`.

The construction reduces to the stabilizer of a subspace. In `M × k`, with `k` the trivial
representation, a point fixes `v` exactly when it carries the line through `(v, 1)` onto itself,
because it cannot rescale the second coordinate. This file takes the stabilizer Hopf ideal of that
line and characterizes it intrinsically.

* Its points with values in any commutative `k`-algebra `A` are the points fixing `1 ⊗ v` in
  `A ⊗ M`. Its rational points are those fixing `v`. Nilpotent values of `A` are allowed, so this
  is the scheme-theoretic stabilizer.
* It is the smallest Hopf ideal containing the elements `c(φ, v) - φ(v)`.
* It is zero, so the stabilizer is all of `G`, exactly when `v` is a fixed vector.
* Its Lie algebra consists of the tangent vectors whose differentiated action kills `v`.
* Over a field of characteristic zero it is smooth, by Cartier's theorem, so its dimension is the
  dimension of that Lie algebra. Equivalently, the dimension of the group is the dimension of the
  stabilizer plus the dimension of the space `𝔤 • v` of images of `v` under the Lie algebra `𝔤`.
  Geometrically, `𝔤 • v` is the tangent space at `v` to the orbit of `v`, so this is the
  infinitesimal form of `dim G = dim Stab_G(v) + dim (G • v)`.

Applied to the adjoint representation, these statements say that the Lie algebra of the
centralizer of an element `x` of the Lie algebra is the kernel of `ad x`, and in characteristic
zero that the centralizer has dimension `dim ker (ad x)`.

## Main declarations

* `TauCeti.Comodule.stabilizerHopfIdeal`: the Hopf ideal of the stabilizer of a vector.
* `TauCeti.Comodule.stabilizerHopfIdeal_le_ker_iff`: its points are the points fixing `1 ⊗ v`.
* `TauCeti.Comodule.mem_quotientPointsSubgroup_stabilizerHopfIdeal_iff`: its rational points are
  the rational points fixing `v`.
* `TauCeti.Comodule.matrixCoefficient_sub_algebraMap_mem_stabilizerHopfIdeal` and
  `TauCeti.Comodule.stabilizerHopfIdeal_le_iff`: its defining equations, and its universal property
  among Hopf ideals.
* `TauCeti.Comodule.stabilizerHopfIdeal_basePointsRepresentation`: acting on the vector
  conjugates its scheme-theoretic stabilizer.
* `TauCeti.Comodule.stabilizerHopfIdeal_eq_bot_iff`: it vanishes exactly when `v` is fixed.
* `TauCeti.Comodule.mem_lieSubalgebra_stabilizerHopfIdeal_iff` and
  `TauCeti.Comodule.lieSubalgebra_stabilizerHopfIdeal`: its Lie algebra is the annihilator of `v`
  under the differentiated representation.
* `TauCeti.Comodule.ringKrullDim_quotient_stabilizerHopfIdeal` and
  `TauCeti.Comodule.ringKrullDim_quotient_stabilizerHopfIdeal_add_finrank_range`: in
  characteristic zero, the stabilizer has the dimension of its Lie algebra, and together with
  `𝔤 • v` it accounts for the dimension of the group.

## References

* J. S. Milne, *Algebraic Groups* (2017), §1.c and Chapter 10.
* J. E. Humphreys, *Linear Algebraic Groups*, §13.
-/

public section

open scoped TensorProduct
open TauCeti

universe u v w

noncomputable section

namespace TauCeti.Comodule

variable (k : Type u) (H : Type v) {M : Type w} [Field k] [CommRing H] [HopfAlgebra k H]
variable [AddCommGroup M] [Module k M] [Comodule k H M]

/-- The product `M × k` of a comodule with the trivial comodule `k`. -/
@[implicit_reducible]
private def prodTrivial : Comodule k H (M × k) :=
  letI : Comodule k H k := trivial
  Prod

attribute [local instance] prodTrivial

/-- The Hopf ideal of the stabilizer of a vector `v` of a comodule `M`.

It is the stabilizer Hopf ideal of the line through `(v, 1)` in `M × k`, where `k` carries the
trivial coaction. Contravariantly, it cuts out the closed subgroup of `Spec H` fixing `v`. -/
def stabilizerHopfIdeal (v : M) : HopfIdeal k H :=
  (k ∙ ((v, 1) : M × k)).stabilizerHopfIdeal H

private theorem stabilizerHopfIdeal_eq (v : M) :
    stabilizerHopfIdeal k H v = (k ∙ ((v, 1) : M × k)).stabilizerHopfIdeal H :=
  rfl

variable {k H}

/-- The comodule projection `M × k → M`. -/
private abbrev fstHom : Hom k H (M × k) M :=
  letI : Comodule k H k := trivial
  prodFst

/-- The comodule projection `M × k → k` onto the trivial factor. -/
private abbrev sndHom : letI : Comodule k H k := trivial
    Hom k H (M × k) k :=
  letI : Comodule k H k := trivial
  prodSnd

/-- A matrix coefficient of `(v, 1)` in `M × k` is a matrix coefficient of `v` plus a constant. -/
private theorem matrixCoefficient_prodTrivial (Φ : M × k →ₗ[k] k) (v : M) :
    matrixCoefficient (R := k) (C := H) Φ (v, 1) =
      matrixCoefficient (R := k) (C := H) (Φ ∘ₗ LinearMap.inl k M k) v +
        algebraMap k H (Φ (0, 1)) := by
  let : Comodule k H k := trivial
  rw [prodTrivial, matrixCoefficient_prod, matrixCoefficient_def (m := (1 : k)),
    trivial_coact_apply (R := k) (C := H)]
  simp [Algebra.algebraMap_eq_smul_one]

/-- Points act trivially on the trivial factor of `M × k`. -/
private theorem baseChange_snd_endOfPoint {A : Type*} [CommRing A] [Algebra k A]
    (g : H →ₐ[k] A) (x : A ⊗[k] (M × k)) :
    (LinearMap.snd k M k).baseChange A (endOfPoint (M × k) g x) =
      (LinearMap.snd k M k).baseChange A x := by
  let : Comodule k H k := trivial
  simpa [endOfPoint_trivial] using LinearMap.congr_fun (baseChange_comp_endOfPoint sndHom g) x

/-- The vector `v` is fixed by the action of an `A`-point exactly when `(v, 1)` is. -/
private theorem endOfPoint_prodTrivial_eq_iff (v : M) {A : Type*} [CommRing A] [Algebra k A]
    (g : H →ₐ[k] A) :
    endOfPoint (M × k) g (1 ⊗ₜ[k] (v, 1)) = 1 ⊗ₜ[k] (v, 1) ↔
      endOfPoint M g (1 ⊗ₜ[k] v) = 1 ⊗ₜ[k] v := by
  let : Comodule k H k := trivial
  have hfst (x : A ⊗[k] (M × k)) :
      (LinearMap.fst k M k).baseChange A (endOfPoint (M × k) g x) =
        endOfPoint M g ((LinearMap.fst k M k).baseChange A x) :=
    LinearMap.congr_fun (baseChange_comp_endOfPoint fstHom g) x
  -- The two projections jointly detect equality, through `A ⊗ (M × k) ≃ (A ⊗ M) × (A ⊗ k)`.
  have hprod (x : A ⊗[k] (M × k)) : TensorProduct.prodRight k k A M k x =
      ((LinearMap.fst k M k).baseChange A x, (LinearMap.snd k M k).baseChange A x) := by
    induction x using TensorProduct.inductionOn with
    | tmul a m => simp
    | add x y hx hy => simp [hx, hy]
  refine ⟨fun h ↦ by simpa using (hfst _).symm.trans congr((LinearMap.fst k M k).baseChange A $h),
    fun h ↦ (TensorProduct.prodRight k k A M k).injective ?_⟩
  rw [hprod, hprod, hfst, baseChange_snd_endOfPoint]
  simpa using h

/-- An algebra-valued point lies in the stabilizer of `v` exactly when it fixes `1 ⊗ v`. -/
theorem stabilizerHopfIdeal_le_ker_iff (v : M) {A : Type*} [CommRing A] [Algebra k A]
    (g : WithConv (H →ₐ[k] A)) :
    (stabilizerHopfIdeal k H v).toIdeal ≤ RingHom.ker g.ofConv ↔
      endOfPoint M g.ofConv (1 ⊗ₜ[k] v) = 1 ⊗ₜ[k] v := by
  let : Comodule k H k := trivial
  rw [stabilizerHopfIdeal_eq, Submodule.stabilizerHopfIdeal_le_ker_iff,
    ← endOfPoint_prodTrivial_eq_iff]
  -- Both sides of the stabilizer condition are spans of a single vector.
  simp only [Submodule.baseChange_span, Submodule.map_span, Set.image_singleton,
    TensorProduct.mk_apply]
  set w : A ⊗[k] (M × k) := 1 ⊗ₜ[k] (v, 1)
  refine ⟨fun h ↦ ?_, fun h ↦ by rw [h]⟩
  obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.mp (h ▸ Submodule.mem_span_singleton_self _)
  -- The action fixes the trivial coordinate of `w`, so the scalar `a` is `1`.
  have h1 : a ⊗ₜ[k] (1 : k) = (1 : A) ⊗ₜ[k] (1 : k) := by
    simpa [w, ← ha, TensorProduct.smul_tmul'] using baseChange_snd_endOfPoint g.ofConv w
  have ha1 : a = 1 := by simpa using congrArg (TensorProduct.rid k A) h1
  rw [← ha, ha1, one_smul]

/-- An algebra-valued point lies in the stabilizer precisely when it fixes the constant
extension of the vector. The value algebra may be nonreduced. -/
theorem mem_quotientPointsSubgroup_stabilizerHopfIdeal_iff_endOfPoint (v : M)
    {A : Type*} [CommRing A] [Algebra k A] (g : WithConv (H →ₐ[k] A)) :
    g ∈ CommHopfAlgCat.quotientPointsSubgroup (_root_.CommHopfAlgCat.of k H)
        (stabilizerHopfIdeal k H v) (CommAlgCat.of k A) ↔
      endOfPoint M g.ofConv (1 ⊗ₜ[k] v) = 1 ⊗ₜ[k] v := by
  rw [CommHopfAlgCat.mem_quotientPointsSubgroup_iff, ← stabilizerHopfIdeal_le_ker_iff]
  exact ⟨fun h _ hx ↦ h _ hx, fun h _ hx ↦ h hx⟩

/-- A rational point lies in the stabilizer of `v` exactly when it fixes `v`. -/
theorem mem_quotientPointsSubgroup_stabilizerHopfIdeal_iff (v : M)
    (g : WithConv (H →ₐ[k] k)) :
    g ∈ CommHopfAlgCat.quotientPointsSubgroup (_root_.CommHopfAlgCat.of k H)
        (stabilizerHopfIdeal k H v) (CommAlgCat.of k k) ↔
      basePointsRepresentation (H := H) M g v = v := by
  rw [mem_quotientPointsSubgroup_stabilizerHopfIdeal_iff_endOfPoint,
    basePointsRepresentation_apply, ← (TensorProduct.lid k M).injective.eq_iff,
    TensorProduct.lid_tmul, one_smul]

/-- The stabilizer Hopf ideal of `v` is the smallest Hopf ideal containing the elements
`c(φ, v) - φ(v)`; contravariantly, the stabilizer is the largest closed subgroup on which the
matrix coefficients of `v` take their values at the identity. -/
theorem stabilizerHopfIdeal_le_iff (v : M) (J : HopfIdeal k H) :
    stabilizerHopfIdeal k H v ≤ J ↔
      ∀ φ : Module.Dual k M,
        matrixCoefficient (R := k) (C := H) φ v - algebraMap k H (φ v) ∈ J := by
  rw [stabilizerHopfIdeal_eq, Submodule.stabilizerHopfIdeal_le_iff]
  constructor
  · intro h φ
    -- The functional `(m, a) ↦ φ m - a φ v` vanishes on the line through `(v, 1)`.
    let Φ : M × k →ₗ[k] k := φ ∘ₗ LinearMap.fst k M k - φ v • LinearMap.snd k M k
    have hΦ : k ∙ ((v, 1) : M × k) ≤ LinearMap.ker Φ := by
      rw [Submodule.span_singleton_le_iff_mem]
      simp [Φ]
    have := h ((k ∙ ((v, 1) : M × k)).liftQ Φ hΦ) (v, 1) (Submodule.mem_span_singleton_self _)
    have hcomp : (k ∙ ((v, 1) : M × k)).liftQ Φ hΦ ∘ₗ (k ∙ ((v, 1) : M × k)).mkQ = Φ :=
      Submodule.liftQ_mkQ _ _ _
    have hinl : Φ ∘ₗ LinearMap.inl k M k = φ := by
      ext m
      simp [Φ]
    rw [hcomp, matrixCoefficient_prodTrivial, hinl] at this
    simpa [Φ, sub_eq_add_neg] using this
  · intro h ψ w hw
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hw
    set Φ := ψ ∘ₗ (k ∙ ((v, 1) : M × k)).mkQ
    have hΦ : Φ (v, 1) = 0 := by
      simp [Φ, (Submodule.Quotient.mk_eq_zero _).mpr (Submodule.mem_span_singleton_self _)]
    have h01 : Φ (0, 1) = -(Φ ∘ₗ LinearMap.inl k M k) v := by
      have : ((0, 1) : M × k) = (v, 1) - LinearMap.inl k M k v := by simp
      conv_rhs => rw [LinearMap.comp_apply]
      rw [this, map_sub, hΦ, zero_sub]
    rw [matrixCoefficient_smul, matrixCoefficient_prodTrivial, h01, map_neg, ← sub_eq_add_neg,
      Algebra.smul_def]
    exact J.toIdeal.mul_mem_left _ (h _)

/-- The elements `c(φ, v) - φ(v)` lie in the stabilizer Hopf ideal of `v`. -/
theorem matrixCoefficient_sub_algebraMap_mem_stabilizerHopfIdeal (v : M) (φ : Module.Dual k M) :
    matrixCoefficient (R := k) (C := H) φ v - algebraMap k H (φ v) ∈ stabilizerHopfIdeal k H v :=
  (stabilizerHopfIdeal_le_iff v _).mp le_rfl φ

/-- The stabilizer of `v` is the whole group exactly when `v` is a fixed vector. -/
theorem stabilizerHopfIdeal_eq_bot_iff (v : M) :
    stabilizerHopfIdeal k H v = ⊥ ↔ coact (R := k) (C := H) v = v ⊗ₜ[k] (1 : H) := by
  rw [eq_bot_iff, stabilizerHopfIdeal_le_iff]
  simp only [HopfIdeal.mem_bot, sub_eq_zero]
  constructor
  · intro h
    rw [← sub_eq_zero]
    refine TauCeti.tensor_eq_zero_of_forall_rTensor_eq_zero (fun φ : Module.Dual k M ↦ φ)
      (fun x hx ↦ (Module.forall_dual_apply_eq_zero_iff k x).mp hx) _ fun φ ↦ ?_
    apply (TensorProduct.lid k H).injective
    rw [map_sub, map_sub, LinearMap.rTensor_def, ← matrixCoefficient_def, h φ, map_zero]
    simp [Algebra.algebraMap_eq_smul_one]
  · intro h φ
    simp [matrixCoefficient_def, h, Algebra.algebraMap_eq_smul_one]

/-- The stabilizer of `0` is the whole group. -/
@[simp]
theorem stabilizerHopfIdeal_zero : stabilizerHopfIdeal k H (0 : M) = ⊥ :=
  (stabilizerHopfIdeal_eq_bot_iff 0).mpr (by rw [map_zero, TensorProduct.zero_tmul])

/-- The Lie algebra of the stabilizer of `v` consists of the tangent vectors whose differentiated
action kills `v`. -/
theorem mem_lieSubalgebra_stabilizerHopfIdeal_iff (v : M)
    (d : Derivation k H (Bialgebra.CounitAlgebra k H k)) :
    d ∈ (stabilizerHopfIdeal k H v).lieSubalgebra (B := k) ↔
      differential (R := k) (H := H) d v = 0 := by
  let : Comodule k H k := trivial
  have hd : differential (R := k) (H := H) d ((v, 1) : M × k) =
      (differential (R := k) (H := H) d v, 0) := by
    have h1 := fstHom.map_differential d ((v, 1) : M × k)
    have h2 := sndHom.map_differential d ((v, 1) : M × k)
    simp only [fstHom, sndHom, prodFst_apply, prodSnd_apply] at h1 h2
    rw [differential_eq_zero_of_coact_eq_tmul_one
      (trivial_coact_apply (R := k) (C := H) (1 : k))] at h2
    exact Prod.ext h1 h2
  rw [stabilizerHopfIdeal_eq, Submodule.mem_lieSubalgebra_stabilizerHopfIdeal_iff]
  constructor
  · intro h
    obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp (h _ (Submodule.mem_span_singleton_self _))
    rw [hd, Prod.ext_iff] at hc
    simp only [Prod.smul_mk, smul_eq_mul, mul_one] at hc
    rw [← hc.1, hc.2, zero_smul]
  · intro h w hw
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hw
    rw [map_smul, hd, h, Prod.mk_zero_zero, smul_zero]
    exact zero_mem _

/-- Acting on a vector by a rational point conjugates its scheme-theoretic stabilizer.
This is an equality of defining Hopf ideals, including their equations on nonreduced
coefficient algebras. -/
theorem stabilizerHopfIdeal_basePointsRepresentation (v : M)
    (g : WithConv (H →ₐ[k] k)) :
    stabilizerHopfIdeal k H (basePointsRepresentation (H := H) M g v) =
      (stabilizerHopfIdeal k H v).conjugate g := by
  apply HopfIdeal.eq_conjugate_of_forall_mem_iff g
  intro A p
  rw [mem_quotientPointsSubgroup_stabilizerHopfIdeal_iff_endOfPoint,
    mem_quotientPointsSubgroup_stabilizerHopfIdeal_iff_endOfPoint]
  have hconj (q : WithConv (H →ₐ[k] A)) (a : WithConv (H →ₐ[k] k)) :
      (AlgHom.mapValue (H := H) (Algebra.ofId k A) a * q *
        (AlgHom.mapValue (H := H) (Algebra.ofId k A) a)⁻¹).ofConv =
      q.ofConv.comp (HopfAlgebra.pointConjugationAlgHom a) := by
    exact congrArg WithConv.ofConv (HopfAlgebra.comp_pointConjugationAlgHom a q).symm
  constructor
  · intro hp
    rw [hconj] at hp
    have hp' := endOfPoint_one_tmul_basePointsRepresentation_of_conj
      (V := M) p.ofConv g⁻¹ (y := 1) (by simpa only [inv_inv] using hp)
    simpa only [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one,
      Module.End.one_apply] using hp'
  · intro hp
    apply endOfPoint_one_tmul_basePointsRepresentation_of_conj
      (V := M) _ g (y := 1)
    rw [← hconj]
    simpa only [map_inv, inv_inv, mul_assoc, inv_mul_cancel_left, inv_mul_cancel,
      mul_one] using hp

section Orbit

attribute [local instance 100] LieRing.ofAssociativeRing

/-- **The Lie algebra of a stabilizer.** The Lie algebra of the stabilizer of `v` is the kernel of
the linear map `d ↦ d • v` given by the differentiated representation. -/
theorem lieSubalgebra_stabilizerHopfIdeal (v : M) :
    ((stabilizerHopfIdeal k H v).lieSubalgebra (B := k)).toSubmodule =
      LinearMap.ker ((differential (R := k) (H := H) (M := M)).toLinearMap.flip v) := by
  ext d
  rw [LieSubalgebra.mem_toSubmodule, mem_lieSubalgebra_stabilizerHopfIdeal_iff, LinearMap.mem_ker,
    LinearMap.flip_apply, LieHom.coe_toLinearMap]

section CharZero

variable [CharZero k] [Algebra.FiniteType k H]

/-- **The dimension of a stabilizer.** Over a field of characteristic zero, the stabilizer of `v`
in a finite-type affine group has the dimension of the space of tangent vectors killing `v`. -/
theorem ringKrullDim_quotient_stabilizerHopfIdeal (v : M) :
    ringKrullDim (H ⧸ (stabilizerHopfIdeal k H v).toIdeal) =
      Module.finrank k
        (LinearMap.ker ((differential (R := k) (H := H) (M := M)).toLinearMap.flip v)) := by
  rw [HopfIdeal.ringKrullDim_quotient_eq_finrank_lieSubalgebra, ← lieSubalgebra_stabilizerHopfIdeal]
  -- A Lie subalgebra and its underlying submodule have the same carrier, as `k`-modules.
  rfl

/-- **Dimension of a stabilizer and of an orbit tangent space.** Over a field of characteristic
zero, the dimension of a finite-type affine group is the dimension of the stabilizer of `v` plus
the dimension of the space `𝔤 • v` swept out by the differentiated representation. -/
theorem ringKrullDim_quotient_stabilizerHopfIdeal_add_finrank_range (v : M) :
    ringKrullDim (H ⧸ (stabilizerHopfIdeal k H v).toIdeal) +
        Module.finrank k
          (LinearMap.range ((differential (R := k) (H := H) (M := M)).toLinearMap.flip v)) =
      ringKrullDim H := by
  rw [ringKrullDim_quotient_stabilizerHopfIdeal,
    ← HopfAlgebra.finrank_lie_eq_ringKrullDim_of_charZero k H,
    ← LinearMap.finrank_range_add_finrank_ker
      ((differential (R := k) (H := H) (M := M)).toLinearMap.flip v)]
  push_cast
  exact add_comm _ _

end CharZero

end Orbit

end TauCeti.Comodule
