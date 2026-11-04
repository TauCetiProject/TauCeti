/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Lie.CliffordAlgebra.Spin.EvenRepresentation
public import TauCeti.LinearAlgebra.CliffordAlgebra.Spin.Real.Neg

/-!
# The smooth negative-metric realization of compact Spin

Compact real Spin has its established Lie structure on its range in the units of the
positive Clifford algebra. Geometric Clifford multiplication instead takes place in the
negative Clifford algebra. This file realizes the algebraic comparison
`CliffordAlgebra.realCliffordSpinGroupEquivNeg n 0` as a smooth homomorphism from that
positive units range to the units of `CliffordAlgebra (realCliffordForm 0 n)`.

The construction uses the even-algebra comparison, so it requires no isomorphism of the
full real Clifford algebras and no Lie structure on the negative Spin subgroup. Its value
agrees with the algebraic comparison, its conjugation action is the prescribed orthogonal
action, and its Lie differential sends a positive bivector to the negative of the
corresponding negative-metric bivector. These comparisons let negative-metric Clifford
modules carry smooth actions of the native compact Spin Lie group.

The construction includes rank zero, where the source is native trivial Spin. It does
not replace the separate geometric two-element group in that rank.

## References

* H. B. Lawson and M.-L. Michelsohn, *Spin Geometry* (1989), Chapter I, Sections 1–3.
* The smooth restriction and its differential use
  `AlgHom.realCliffordSpinEvenSmoothHom` and
  `AlgHom.unitsLieAlgebraLieEquiv_lieMap_realCliffordSpinEvenSmoothHom`.
-/

public section

open Manifold TauCeti CliffordAlgebra
open scoped ContDiff Manifold Matrix.Norms.Operator

noncomputable section

namespace TauCeti.CliffordAlgebra

attribute [local instance 100] LieRing.ofAssociativeRing
attribute [local instance] Matrix.linftyOpTopologicalSpace

local notation "SpinUnitsRange(" n ")" =>
  MonoidHom.range (spinGroup.toUnits (Q := realCliffordForm n 0))

local notation "SpinLieModel(" n ")" =>
  LieSubalgebra.toSubmodule (TauCeti.Lie.lieSubalgebraOfSubgroup
    (I := 𝓘(ℝ, CliffordAlgebra (realCliffordForm n 0))) (SpinUnitsRange(n)))

private def negativeEvenHom (n : ℕ) :
    even (realCliffordForm n 0) →ₐ[ℝ] CliffordAlgebra (realCliffordForm 0 n) :=
  (map (realCliffordFormNegIsometry n 0).toIsometry).comp
    ((even (-realCliffordForm n 0)).val.comp (evenEquivEvenNeg _).toAlgHom)

/-- The compact Spin Lie group mapped smoothly into the negative-metric Clifford units,
through the real even-algebra comparison. -/
def realCliffordSpinNegativeSmoothHom (n : ℕ) :
    ContMDiffMonoidMorphism 𝓘(ℝ, SpinLieModel(n))
      𝓘(ℝ, CliffordAlgebra (realCliffordForm 0 n)) ∞
      (SpinUnitsRange(n)) (CliffordAlgebra (realCliffordForm 0 n))ˣ :=
  (negativeEvenHom n).realCliffordSpinEvenSmoothHom

/-- The comparison is smooth as a map to the finite-dimensional negative Clifford algebra. -/
theorem contMDiff_realCliffordSpinNegativeSmoothHom (n : ℕ) :
    ContMDiff 𝓘(ℝ, SpinLieModel(n)) 𝓘(ℝ, CliffordAlgebra (realCliffordForm 0 n)) ∞
      (fun g : SpinUnitsRange(n) ↦
        (realCliffordSpinNegativeSmoothHom n g : CliffordAlgebra (realCliffordForm 0 n))) :=
  Units.contMDiff_val.comp (realCliffordSpinNegativeSmoothHom n).contMDiff_toFun

/-- The smooth comparison has exactly the algebraic positive-to-negative Clifford value,
using the canonical inverse identification of the units range with native Spin. -/
-- Evaluate before simp expands the dependent units-range representative.
@[simp↓]
theorem realCliffordSpinNegativeSmoothHom_apply (n : ℕ)
    (g : SpinUnitsRange(n)) :
    realCliffordSpinNegativeSmoothHom n g =
      spinGroup.toUnits (realCliffordSpinGroupEquivNeg n 0
        ((realCliffordSpinContinuousMulEquivUnitsRange n).symm g)) := by
  obtain ⟨s, rfl⟩ := (realCliffordSpinContinuousMulEquivUnitsRange n).surjective g
  rw [ContinuousMulEquiv.symm_apply_apply]
  apply Units.ext
  rw [spinGroup.val_toUnits_apply]
  rw [realCliffordSpinNegativeSmoothHom, AlgHom.realCliffordSpinEvenSmoothHom_apply,
    coe_realCliffordSpinGroupEquivNeg_apply]
  simp only [negativeEvenHom, AlgHom.comp_apply, AlgEquiv.coe_toAlgHom,
    Subalgebra.coe_val]
  apply congrArg (map (realCliffordFormNegIsometry n 0).toIsometry)
  apply congrArg (fun x : even (realCliffordForm n 0) ↦
    (evenEquivEvenNeg (realCliffordForm n 0) x : CliffordAlgebra (-realCliffordForm n 0)))
  apply Subtype.ext
  rw [coe_spinGroupToEven_apply]
  rw [realCliffordSpinContinuousMulEquivUnitsRange_apply]
  rfl

/-- The negative-metric realization is faithful, including in native rank zero. -/
theorem realCliffordSpinNegativeSmoothHom_injective (n : ℕ) :
    Function.Injective (realCliffordSpinNegativeSmoothHom n) := by
  intro x y h
  obtain ⟨s, rfl⟩ := (realCliffordSpinContinuousMulEquivUnitsRange n).surjective x
  obtain ⟨t, rfl⟩ := (realCliffordSpinContinuousMulEquivUnitsRange n).surjective y
  apply congrArg (realCliffordSpinContinuousMulEquivUnitsRange n)
  apply (realCliffordSpinGroupEquivNeg n 0).injective
  apply spinGroup.toUnits_injective
  simpa only [realCliffordSpinNegativeSmoothHom_apply,
    ContinuousMulEquiv.symm_apply_apply] using h

/-- Conjugation by the smooth negative-metric image realizes the same vector action,
with vectors transported by the signature-coordinate isometry. -/
theorem realCliffordSpinNegativeSmoothHom_conjugate_ι (n : ℕ)
    (s : realCliffordSpinGroup n 0) (v : Fin (n + 0) → ℝ) :
    let u := realCliffordSpinNegativeSmoothHom n
      (realCliffordSpinContinuousMulEquivUnitsRange n s)
    (u : CliffordAlgebra (realCliffordForm 0 n)) *
        ι (realCliffordForm 0 n) (realCliffordFormNegIsometry n 0 v) *
        (↑(u⁻¹) : CliffordAlgebra (realCliffordForm 0 n)) =
      ι (realCliffordForm 0 n)
        (realCliffordFormNegIsometry n 0 (spinVectorAction (realCliffordForm n 0) s v)) := by
  rw [realCliffordSpinNegativeSmoothHom_apply, ContinuousMulEquiv.symm_apply_apply]
  dsimp only
  rw [← map_inv, spinGroup.val_toUnits_apply, spinGroup.val_toUnits_apply,
    ← spinGroup.star_eq_inv, spinGroup.coe_star]
  simpa only [spinVectorAction_realCliffordSpinGroupEquivNeg] using
    (ι_spinVectorAction_apply (realCliffordForm 0 n) (realCliffordSpinGroupEquivNeg n 0 s)
      (realCliffordFormNegIsometry n 0 v)).symm

/-- The Lie differential of the negative-metric realization is the even-algebra
comparison applied to the quadratic Clifford coordinate. -/
theorem unitsLieAlgebraLieEquiv_lieMap_realCliffordSpinNegativeSmoothHom (n : ℕ)
    (X : LeftInvariantDerivation 𝓘(ℝ, SpinLieModel(n)) (SpinUnitsRange(n))) :
    TauCeti.Lie.unitsLieAlgebraLieEquiv (lieMap (realCliffordSpinNegativeSmoothHom n) X) =
      map (realCliffordFormNegIsometry n 0).toIsometry
        (evenEquivEvenNeg (realCliffordForm n 0)
          ⟨realCliffordSpinLieEquivQuadratic n X,
            quadraticLieSubalgebra_le_even _
              (realCliffordSpinLieEquivQuadratic n X).property⟩) := by
  exact AlgHom.unitsLieAlgebraLieEquiv_lieMap_realCliffordSpinEvenSmoothHom
    (negativeEvenHom n) X

/-- On a bivector the Lie differential has the geometric minus sign. The bivector uses
the half-normalized commutator, so this equation also pins its normalization. -/
theorem unitsLieAlgebraLieEquiv_lieMap_realCliffordSpinNegativeSmoothHom_bivector (n : ℕ)
    (a b : Fin (n + 0) → ℝ) :
    TauCeti.Lie.unitsLieAlgebraLieEquiv
        (lieMap (realCliffordSpinNegativeSmoothHom n)
          ((realCliffordSpinLieEquivQuadratic n).symm
            ⟨bivector (realCliffordForm n 0) a b,
              bivector_mem_quadraticLieSubalgebra _ a b⟩)) =
      -bivector (realCliffordForm 0 n)
        (realCliffordFormNegIsometry n 0 a) (realCliffordFormNegIsometry n 0 b) := by
  rw [unitsLieAlgebraLieEquiv_lieMap_realCliffordSpinNegativeSmoothHom,
    LieEquiv.apply_symm_apply]
  have hb : (⟨bivector (realCliffordForm n 0) a b,
      quadraticLieSubalgebra_le_even _ (bivector_mem_quadraticLieSubalgebra _ a b)⟩ :
      even (realCliffordForm n 0)) =
      (⅟ (2 : ℝ)) • ((even.ι (realCliffordForm n 0)).bilin a b -
        (even.ι (realCliffordForm n 0)).bilin b a) := by
    apply Subtype.ext
    -- Mathlib's even-generator bilinear map is the pair product by definition.
    simpa [even.ι] using
      bivector_def (realCliffordForm n 0) a b
  rw [hb]
  simp only [map_smul, map_sub, evenEquivEvenNeg_apply, evenToNeg_ι,
    Subalgebra.coe_smul, Subalgebra.coe_sub, Subalgebra.coe_neg, map_neg]
  -- Evaluate the native even generators as products before applying the coordinate map.
  simp only [even.ι, LinearMap.mk₂_apply, map_mul, map_apply_ι, bivector_def,
    QuadraticMap.IsometryEquiv.toIsometry_apply]
  module

end TauCeti.CliffordAlgebra
