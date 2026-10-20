/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.Padics.Measure.FiniteProjection
public import Mathlib.NumberTheory.Padics.RingHoms

/-!
# Joint finite and coefficient projections of p-adic measures

Reducing the coefficients of a finite projection modulo a power of `p` gives a finite coordinate
of an integral `p`-adic measure.  This file constructs these joint coordinates, proves their
compatibility in both the coefficient precision and the finite quotient, and shows that the full
family of joint coordinates determines a measure on a profinite space.

The construction follows the finite-coefficient description in Rodrigues Jacinto and Williams,
*An introduction to p-adic L-functions*, Sections 3.2--3.3.
-/

public noncomputable section

open ContinuousMap

variable {X A B : Type*} [TopologicalSpace X] [TopologicalSpace A] [TopologicalSpace B]
  {p : ℕ} [Fact p.Prime]

namespace AbstractMeasure

/-- The joint finite projection reduces every coefficient of a finite projection modulo `p ^ r`.

The precision `r` and the finite quotient `q` are independent parameters. -/
def jointFiniteProjection (r : ℕ) [Finite A] [DiscreteTopology A] (q : C(X, A)) :
    D(X, ℤ_[p]) →+ A →₀ ZMod (p ^ r) :=
  (Finsupp.mapRange.addMonoidHom (PadicInt.toZModPow r).toAddMonoidHom).comp
    (finiteProjection q).toAddMonoidHom

/-- A joint finite coefficient is the corresponding finite coefficient reduced modulo `p ^ r`. -/
@[simp]
theorem jointFiniteProjection_apply (r : ℕ) [Finite A] [DiscreteTopology A]
    (q : C(X, A)) (μ : D(X, ℤ_[p])) (a : A) :
    jointFiniteProjection r q μ a = PadicInt.toZModPow r (μ (fiberIndicator q a)) := by
  simp [jointFiniteProjection, finiteProjection_apply]

/-- The joint finite projection of the zero measure is zero. -/
@[simp]
theorem jointFiniteProjection_zero (r : ℕ) [Finite A] [DiscreteTopology A]
    (q : C(X, A)) :
    jointFiniteProjection r q (0 : D(X, ℤ_[p])) = 0 := by
  exact map_zero (jointFiniteProjection r q)

/-- Joint finite projection is additive in the measure. -/
@[simp]
theorem jointFiniteProjection_add (r : ℕ) [Finite A] [DiscreteTopology A]
    (q : C(X, A)) (μ ν : D(X, ℤ_[p])) :
    jointFiniteProjection r q (μ + ν) =
      jointFiniteProjection r q μ + jointFiniteProjection r q ν := by
  exact map_add (jointFiniteProjection r q) μ ν

/-- At coefficient precision zero every joint finite projection vanishes. -/
theorem jointFiniteProjection_zero_precision [Finite A] [DiscreteTopology A]
    (q : C(X, A)) (μ : D(X, ℤ_[p])) :
    jointFiniteProjection 0 q μ = 0 := by
  apply Finsupp.ext
  intro a
  rw [jointFiniteProjection_apply]
  have hsub : Subsingleton (ZMod (p ^ 0)) := by
    simpa only [pow_zero] using (inferInstance : Subsingleton (ZMod 1))
  exact @Subsingleton.elim _ hsub _ _

/-- Reducing a joint finite projection to a coarser coefficient precision gives the joint
projection at that precision. -/
theorem jointFiniteProjection_cast (r' r : ℕ) (h : r' ≤ r) [Finite A] [DiscreteTopology A]
    (q : C(X, A)) (μ : D(X, ℤ_[p])) :
    Finsupp.mapRange
        (ZMod.castHom (pow_dvd_pow p h) (ZMod (p ^ r')))
        (map_zero (ZMod.castHom (pow_dvd_pow p h) (ZMod (p ^ r'))))
        (jointFiniteProjection r q μ) =
      jointFiniteProjection r' q μ := by
  ext a
  simp [jointFiniteProjection_apply, PadicInt.cast_toZModPow r' r h]

/-- Joint finite projection is functorial when one finite quotient refines another. -/
theorem jointFiniteProjection_comp (r : ℕ) [Finite A] [Finite B]
    [DiscreteTopology A] [DiscreteTopology B] (q : C(X, A)) (t : C(A, B))
    (μ : D(X, ℤ_[p])) :
    jointFiniteProjection r (t.comp q) μ = (jointFiniteProjection r q μ).mapDomain t := by
  -- Expose the coefficient maps so `Finsupp.mapDomain_mapRange` applies directly.
  change Finsupp.mapRange (PadicInt.toZModPow r) (map_zero (PadicInt.toZModPow r))
      (finiteProjection (t.comp q) μ) =
    Finsupp.mapDomain t (Finsupp.mapRange (PadicInt.toZModPow r)
      (map_zero (PadicInt.toZModPow r)) (finiteProjection q μ))
  rw [finiteProjection_comp]
  exact (Finsupp.mapDomain_mapRange t (finiteProjection q μ) _ (map_zero _) (map_add _)).symm

/-- The joint finite projection of a Dirac measure is the point mass at its image, with coefficient
one in `ZMod (p ^ r)`. -/
@[simp]
theorem jointFiniteProjection_dirac (r : ℕ) [Finite A] [DiscreteTopology A]
    (q : C(X, A)) (x : X) :
    jointFiniteProjection r q (dirac ℤ_[p] x) = Finsupp.single (q x) 1 := by
  simp [jointFiniteProjection]

section Profinite

variable [CompactSpace X] [T2Space X] [TotallyDisconnectedSpace X]

/-- An integral `p`-adic measure on a profinite space is determined by its binary projections
at all coefficient precisions. -/
theorem jointFiniteProjection_ext (μ ν : D(X, ℤ_[p]))
    (h : ∀ (r : ℕ) (q : C(X, Fin 2)),
      jointFiniteProjection r q μ = jointFiniteProjection r q ν) :
    μ = ν := by
  apply finiteProjection_ext μ ν
  intro q
  apply Finsupp.ext
  intro a
  rw [← PadicInt.ext_of_toZModPow]
  intro r
  rw [finiteProjection_apply, finiteProjection_apply]
  simpa only [jointFiniteProjection_apply] using
    congrArg (fun c : Fin 2 →₀ ZMod (p ^ r) ↦ c a) (h r q)

end Profinite

example :
    jointFiniteProjection (p := 2) 2 (.id (Fin 1))
      (dirac ℤ_[2] (0 : Fin 1)) = Finsupp.single 0 1 := by
  exact jointFiniteProjection_dirac 2 (.id (Fin 1)) 0

example (μ : D(Fin 1, ℤ_[2])) :
    jointFiniteProjection 0 (.id (Fin 1)) μ = 0 := by
  exact jointFiniteProjection_zero_precision (.id (Fin 1)) μ

example :
    jointFiniteProjection (p := 2) 1 (.id (Fin 1))
      (2 • dirac ℤ_[2] (0 : Fin 1)) 0 = 0 ∧
    jointFiniteProjection (p := 2) 2 (.id (Fin 1))
      (2 • dirac ℤ_[2] (0 : Fin 1)) 0 = 2 := by
  constructor
  · rw [map_nsmul]
    rw [jointFiniteProjection_dirac]
    norm_num
    decide
  · rw [map_nsmul]
    rw [jointFiniteProjection_dirac]
    norm_num

end AbstractMeasure
