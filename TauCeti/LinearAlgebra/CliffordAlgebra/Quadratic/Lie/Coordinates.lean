/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.CliffordAlgebra.Quadratic.Lie.Representation

/-!
# Coordinate formulas for quadratic Clifford lifts

The quadratic realization of a skew-adjoint endomorphism has a simple expression after choosing
a basis: it is half the sum of the bivectors formed from the images of the basis vectors and the
dual basis for the polar form. This file proves that formula without unfolding the exterior-square
construction of `CliffordAlgebra.soEquivQuadratic`.

For the adjoint lift associated to the Killing quadratic form, the polar form is twice the Killing
form. Its polar-dual basis is therefore half the Killing-dual basis, and the two factors of one half
combine to give the familiar coefficient `1 / 4`:

```text
adjointCliffordHom K L x = 1 / 4 • ∑ i, bivector Q ([x, b i]) (killingDualBasis b i).
```

The bundled bilinear map `CliffordAlgebra.adjointBivector` puts the summand in the form consumed by
the basis-independent Killing contraction and root-space projection API.

## Main results

* `CliffordAlgebra.adjointBivector`: the bilinear map `(y, z) ↦ bivector Q [x, y] z`.
* `CliffordAlgebra.soEquivQuadratic_eq_sum_bivector`: the coordinate formula for an arbitrary
  skew-adjoint endomorphism.
* `CliffordAlgebra.adjointCliffordHom_eq_sum_bivector`: the adjoint lift as a `1 / 4`-scaled sum
  against a Killing-dual basis.

## References

* E. Meinrenken, *Clifford Algebras and Lie Theory*, Springer Ergebnisse 58 (2013), Chapters
  5--10, for the quadratic realization and the Killing-form construction underlying Kostant
  theory.
-/

public section


universe u v w

open TauCeti

namespace CliffordAlgebra

attribute [local instance 100] LieRing.ofAssociativeRing

variable {K : Type u} [Field K] {V : Type v} [AddCommGroup V] [Module K V]
  [Invertible (2 : K)]

/-- The bilinear Clifford bivector obtained by applying `ad x` in the first slot.

Bundling the summand in the adjoint coordinate formula lets the canonical Killing-dual contraction
lemmas, in particular `TauCeti.sum_apply_killingDualBasis_eq`, act on it directly. -/
noncomputable def adjointBivector {R : Type u} [CommRing R] [Invertible (2 : R)]
    {L : Type v} [LieRing L] [LieAlgebra R L]
    (Q : QuadraticForm R L) (x : L) : L →ₗ[R] L →ₗ[R] CliffordAlgebra Q :=
  LinearMap.mk₂ R (fun y z ↦ bivector Q ⁅x, y⁆ z)
    (fun y₁ y₂ z ↦ by simp only [lie_add, map_add, add_mul, mul_add, bivector_def]; module)
    (fun c y z ↦ by
      simp only [lie_smul, map_smul, smul_mul_assoc, mul_smul_comm, bivector_def]
      module)
    (fun y z₁ z₂ ↦ by simp only [map_add, add_mul, mul_add, bivector_def]; module)
    (fun c y z ↦ by
      simp only [map_smul, smul_mul_assoc, mul_smul_comm, bivector_def]
      module)

/-- The adjoint bivector map evaluates to the bivector of `[x, y]` and `z`. -/
@[simp]
theorem adjointBivector_apply {R : Type u} [CommRing R] [Invertible (2 : R)]
    {L : Type v} [LieRing L] [LieAlgebra R L]
    (Q : QuadraticForm R L) (x y z : L) :
    adjointBivector Q x y z = bivector Q ⁅x, y⁆ z := by
  rfl

/-- **The coordinate formula for the quadratic realization.** If `d` is the basis dual to `b`
for the polar form of `Q`, then the quadratic element realizing a skew-adjoint endomorphism `f` is
`1 / 2 • ∑ i, bivector Q (f (b i)) (d i)`. -/
theorem soEquivQuadratic_eq_sum_bivector {ι : Type w} [Fintype ι] [DecidableEq ι]
    (Q : QuadraticForm K V) (hQ : Q.Nondegenerate) (b : Module.Basis ι K V)
    (f : skewAdjointLieSubalgebra Q.polarBilin) :
    (@soEquivQuadratic K _ V _ _ b.finiteDimensional_of_finite _ Q hQ f :
        CliffordAlgebra Q) =
      (2 : K)⁻¹ • ∑ i, bivector Q ((f : Module.End K V) (b i))
        (LinearMap.BilinForm.dualBasis Q.polarBilin
          (QuadraticMap.nondegenerate_polar_iff.mpr hQ) b i) := by
  let _ := b.finiteDimensional_of_finite
  let d := LinearMap.BilinForm.dualBasis Q.polarBilin
    (QuadraticMap.nondegenerate_polar_iff.mpr hQ) b
  let a : quadraticLieSubalgebra Q :=
    ⟨(2 : K)⁻¹ • ∑ i, bivector Q ((f : Module.End K V) (b i)) (d i),
      (quadraticLieSubalgebra Q).smul_mem _ <|
        (quadraticLieSubalgebra Q).sum_mem fun i _ ↦
          bivector_mem_quadraticLieSubalgebra Q ((f : Module.End K V) (b i)) (d i)⟩
  have ha : soEquivQuadratic Q hQ f = a := by
    apply quadraticLieSubalgebra_ext Q hQ
    intro x
    rw [soEquivQuadratic_lie_ι]
    dsimp only [a]
    rw [smul_lie, sum_lie]
    simp_rw [bivector_lie_ι]
    rw [← map_sum, ← map_smul]
    congr 1
    rw [Finset.sum_sub_distrib]
    have hfirst :
        ∑ i, Q.polarBilin (d i) x • (f : Module.End K V) (b i) =
          (f : Module.End K V) x := by
      calc
        _ = (f : Module.End K V) (∑ i, Q.polarBilin (d i) x • b i) := by
          rw [map_sum]
          simp only [map_smul]
        _ = (f : Module.End K V) x := by
          congr 1
          calc
            _ = ∑ i, b.repr x i • b i := by
              apply Finset.sum_congr rfl
              intro i _
              congr 1
              calc
                Q.polarBilin (d i) x = Q.polarBilin x (d i) :=
                  QuadraticMap.polar_comm Q (d i) x
                _ = (LinearMap.BilinForm.dualBasis Q.polarBilin
                    (QuadraticMap.nondegenerate_polar_iff.mpr hQ) d).repr x i :=
                  (LinearMap.BilinForm.dualBasis_repr_apply
                    (QuadraticMap.nondegenerate_polar_iff.mpr hQ) d x i).symm
                _ = b.repr x i := by
                  rw [LinearMap.BilinForm.dualBasis_dualBasis
                    (QuadraticMap.nondegenerate_polar_iff.mpr hQ)
                    (LinearMap.BilinForm.isSymm_def.mpr fun y z ↦
                      QuadraticMap.polar_comm Q y z) b]
            _ = x := b.sum_repr x
    have hskew (i : ι) :
        Q.polarBilin ((f : Module.End K V) (b i)) x =
          -Q.polarBilin (b i) ((f : Module.End K V) x) := by
      simpa using f.property (b i) x
    have hsecond :
        ∑ i, Q.polarBilin ((f : Module.End K V) (b i)) x • d i =
          -(f : Module.End K V) x := by
      calc
        _ = ∑ i, -(Q.polarBilin (b i) ((f : Module.End K V) x) • d i) := by
          apply Finset.sum_congr rfl
          intro i _
          rw [hskew, neg_smul]
        _ = -(∑ i, Q.polarBilin (b i) ((f : Module.End K V) x) • d i) := by
          rw [Finset.sum_neg_distrib]
        _ = -(f : Module.End K V) x := by
          congr 1
          calc
            _ = ∑ i, d.repr ((f : Module.End K V) x) i • d i := by
              apply Finset.sum_congr rfl
              intro i _
              congr 1
              rw [LinearMap.BilinForm.dualBasis_repr_apply]
              exact QuadraticMap.polar_comm Q (b i) ((f : Module.End K V) x)
            _ = (f : Module.End K V) x := d.sum_repr ((f : Module.End K V) x)
    simp only [QuadraticMap.polarBilin_apply_apply] at hfirst hsecond
    rw [hfirst, hsecond, sub_neg_eq_add, ← two_smul K, ← mul_smul,
      inv_mul_cancel₀ (Invertible.ne_zero (2 : K)), one_smul]
  simpa [a, d] using congrArg Subtype.val ha

/-- **The adjoint quadratic lift in Killing-dual coordinates.** For any basis `b` of a
finite-dimensional Killing-semisimple Lie algebra,
`adjointCliffordHom K L x` is one quarter of the sum of the bivectors of `[x, b i]` with the
Killing-dual basis vectors.

The formula is independent of `b`: its sum is the contraction of `adjointBivector Q x` against
the canonical tensor represented by a basis and its Killing dual. -/
theorem adjointCliffordHom_eq_sum_bivector {ι : Type w} [Fintype ι]
    [DecidableEq ι] {L : Type v} [LieRing L] [LieAlgebra K L]
    [_root_.LieAlgebra.IsKilling K L]
    (b : Module.Basis ι K L) (x : L) :
    @adjointCliffordHom K L _ _ _ b.finiteDimensional_of_finite _ _ x =
      (4 : K)⁻¹ • ∑ i, adjointBivector
        (_root_.TauCeti.LieAlgebra.killingQuadraticForm K L) x
        (b i) (killingDualBasis b i) := by
  let _ := b.finiteDimensional_of_finite
  let Q := _root_.TauCeti.LieAlgebra.killingQuadraticForm K L
  rw [adjointCliffordHom_apply,
    soEquivQuadratic_eq_sum_bivector Q
      (_root_.TauCeti.LieAlgebra.killingQuadraticForm_nondegenerate K L) b]
  simp only [_root_.TauCeti.LieAlgebra.coe_killingAdjointSO, _root_.LieAlgebra.ad_apply]
  have hdual (i : ι) :
      LinearMap.BilinForm.dualBasis Q.polarBilin
          (QuadraticMap.nondegenerate_polar_iff.mpr
            (_root_.TauCeti.LieAlgebra.killingQuadraticForm_nondegenerate K L)) b i =
        (2 : K)⁻¹ • killingDualBasis b i := by
    simpa only [Q, _root_.TauCeti.LieAlgebra.polarBilin_killingQuadraticForm] using
      b.dualBasis_polarBilin_killingQuadraticForm_apply i
  simp_rw [hdual]
  have hbiv (y z : L) : bivector Q y ((2 : K)⁻¹ • z) =
      (2 : K)⁻¹ • bivector Q y z := by
    simp only [bivector_def, map_smul, smul_mul_assoc, mul_smul_comm]
    module
  simp_rw [hbiv, adjointBivector_apply]
  rw [← Finset.smul_sum, smul_smul]
  congr 1
  rw [← mul_inv_rev]
  norm_num

end CliffordAlgebra
