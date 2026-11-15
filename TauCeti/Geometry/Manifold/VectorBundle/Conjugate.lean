/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.VectorBundle.Basic
public import Mathlib.Geometry.Manifold.Diffeomorph
public import TauCeti.Topology.VectorBundle.Conjugate

/-!
# The conjugate of a smooth complex vector bundle

Over a real charted space, the conjugate `TauCeti.ConjugateBundle E` of a `C^n` vector bundle `E`
is again a `C^n` vector bundle (`TauCeti.ConjugateBundle.instContMDiffVectorBundle`): its real
vector bundle structure and its trivializations are those of `E`. The identity of total spaces is
then a `C^n` diffeomorphism covering the identity of the base and conjugate-linear on each fibre
(`TauCeti.ConjugateBundle.toConjDiffeomorph`).

Over a complex base, the coordinate changes of the conjugate are the complex conjugates of those
of `E`, so conjugation does not in general preserve holomorphicity over the same complex base.
Smoothness is therefore only asserted over a real base, which is the setting of the doubled bundle
of a bundle pair over a bordered Riemann surface.
-/

public section

noncomputable section

open Bundle
open scoped Manifold ContDiff

namespace TauCeti.ConjugateBundle

variable {EB : Type*} [NormedAddCommGroup EB] [NormedSpace ℝ EB] {HB : Type*} [TopologicalSpace HB]
  {IB : ModelWithCorners ℝ EB HB} {B : Type*} [TopologicalSpace B] [ChartedSpace HB B] {n : ℕ∞ω}
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {E : B → Type*} [TopologicalSpace (TotalSpace F E)] [∀ x, TopologicalSpace (E x)]
  [FiberBundle F E]

/-- The conjugate of a `C^n` vector bundle over a real charted space is a `C^n` vector bundle. -/
instance instContMDiffVectorBundle [∀ x, AddCommGroup (E x)] [∀ x, Module ℝ (E x)]
    [VectorBundle ℝ F E] [ContMDiffVectorBundle n F E IB] :
    ContMDiffVectorBundle n (Conjugate F) (ConjugateBundle E) IB :=
  inferInstanceAs (ContMDiffVectorBundle n F E IB)

variable (IB n F E) in
/-- The identity of total spaces `E → ConjugateBundle E` as a `C^n` diffeomorphism. On each fibre
it is the conjugate-linear equivalence `TauCeti.Conjugate.toConjL`. -/
def toConjDiffeomorph :
    TotalSpace F E ≃ₘ^n⟮IB.prod 𝓘(ℝ, F), IB.prod 𝓘(ℝ, Conjugate F)⟯
      TotalSpace (Conjugate F) (ConjugateBundle E) where
  toEquiv := (toConjHomeomorph F E).toEquiv
  contMDiff_toFun := contMDiff_id.congr toConjHomeomorph_apply
  contMDiff_invFun := contMDiff_id.congr toConjHomeomorph_symm_apply

@[simp] theorem toConjDiffeomorph_apply (p : TotalSpace F E) :
    toConjDiffeomorph IB n F E p = toConjHomeomorph F E p := (rfl)

@[simp] theorem toConjDiffeomorph_symm_apply (p : TotalSpace (Conjugate F) (ConjugateBundle E)) :
    (toConjDiffeomorph IB n F E).symm p = (toConjHomeomorph F E).symm p := (rfl)

end TauCeti.ConjugateBundle
