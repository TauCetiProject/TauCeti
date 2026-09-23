/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.UpperHalfPlane.Elliptic
public import Mathlib.Topology.Homeomorph.Lemmas

/-!
# Local charts at elliptic orbits

The quotient of a small hyperbolic disc around an elliptic point maps as an open subset into the
coarse orbit quotient. This file packages the local quotient coordinate as a homeomorphism from
that open subset to a Euclidean disc. In the disc coordinate at the fixed point, this chart sends
the orbit of `τ` to the `m`th power of its coordinate, where `m` is the stabilizer order. These
charts are the local models used to glue the elliptic points to the free quotient atlas. The
cyclic quotient model follows Farkas–Kra, *Riemann Surfaces*, Chapter I §§4–5, and Katok,
*Fuchsian Groups*, §2.4.
-/

public noncomputable section

open MulAction Set Topology UpperHalfPlane

open scoped MatrixGroups

namespace Subgroup

variable {Γ : Subgroup PSL(2, ℝ)} {z : ℍ} {ε : ℝ}

/-- The elliptic quotient chart on the image of the stabilizer quotient of a disc in the coarse
orbit quotient. Its target is the Euclidean disc of radius `tanh (ε / 2) ^ m`, where `m` is the
order of the stabilizer. -/
def stabilizerBallQuotientChart [Finite (stabilizer Γ z)] (hε : 0 < ε)
    (hopen : IsOpenEmbedding (stabilizerBallQuotientToQuotient Γ z ε)) :
    {q : orbitRel.Quotient Γ ℍ //
      q ∈ Set.range (stabilizerBallQuotientToQuotient Γ z ε)} ≃ₜ
      Metric.ball (0 : ℂ) (Real.tanh (ε / 2) ^ Nat.card (stabilizer Γ z)) :=
  hopen.toIsEmbedding.toHomeomorph.symm.trans
    (stabilizerBallQuotientHomeomorph Γ z ε hε.le)

/-- In the elliptic quotient chart, the orbit of a point in the stabilizer ball has coordinate
equal to the corresponding power of its disc coordinate. -/
@[simp]
theorem stabilizerBallQuotientChart_mk [Finite (stabilizer Γ z)] (hε : 0 < ε)
    (hopen : IsOpenEmbedding (stabilizerBallQuotientToQuotient Γ z ε))
    (τ : stabilizerBall Γ z ε) :
    (↑(stabilizerBallQuotientChart hε hopen
      ⟨Quotient.mk _ (τ : ℍ),
        ⟨Quotient.mk _ τ, stabilizerBallQuotientToQuotient_mk Γ z ε τ⟩⟩) : ℂ) =
      discCoordinate z τ ^ Nat.card (stabilizer Γ z) := by
  simpa only [stabilizerBallQuotientToQuotient_mk] using
    (show (↑(stabilizerBallQuotientChart hε hopen
      ⟨stabilizerBallQuotientToQuotient Γ z ε (Quotient.mk _ τ),
        ⟨Quotient.mk _ τ, rfl⟩⟩) : ℂ) =
      discCoordinate z τ ^ Nat.card (stabilizer Γ z) from by
        rw [stabilizerBallQuotientChart, Homeomorph.trans_apply,
          Topology.IsEmbedding.toHomeomorph_symm_apply]
        exact coe_stabilizerBallQuotientHomeomorph_mk Γ z ε hε.le τ)

end Subgroup
