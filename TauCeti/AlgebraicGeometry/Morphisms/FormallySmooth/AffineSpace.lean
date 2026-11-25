/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicGeometry.AffineSpace
public import TauCeti.AlgebraicGeometry.Morphisms.FormallySmooth

/-!
# Affine space is formally smooth

For a scheme `S`, the structure morphism `𝔸(σ; S) ⟶ S` is formally smooth: it is the base change
of `Spec ℤ[x_i, i ∈ σ] ⟶ Spec ℤ`, and `ℤ[x_i, i ∈ σ]` is a formally smooth `ℤ`-algebra.

## Main results

* `TauCeti.AlgebraicGeometry.FormallySmooth.affineSpace`: `𝔸(σ; S) ↘ S` is formally smooth.
-/

public section

universe u

open CategoryTheory Limits AlgebraicGeometry

namespace TauCeti.AlgebraicGeometry.FormallySmooth

/-- **Affine space is formally smooth**: `𝔸(σ; S) ⟶ S` is the base change of
`Spec ℤ[x_i, i ∈ σ] ⟶ Spec ℤ`, which is formally smooth. -/
instance affineSpace (σ : Type u) (S : Scheme.{u}) : FormallySmooth (𝔸(σ; S) ↘ S) := by
  -- `Spec (ULift ℤ)` is terminal, so `terminal.from (Spec (ULift ℤ))` is an isomorphism; this
  -- instance makes it formally smooth for the `infer_instance` on `Spec.map C ≫ terminal.from _`.
  have := isIso_of_isTerminal specULiftZIsTerminal.{u} terminalIsTerminal (terminal.from _)
  have : FormallySmooth (Spec.map (CommRingCat.ofHom
      (MvPolynomial.C : ULift.{u} ℤ →+* MvPolynomial σ (ULift.{u} ℤ)))) := by
    rw [formallySmooth_SpecMap_iff, CommRingCat.hom_ofHom, ← MvPolynomial.algebraMap_eq,
      RingHom.formallySmooth_algebraMap]
    infer_instance
  have : FormallySmooth (terminal.from (Spec (.of (MvPolynomial σ (ULift.{u} ℤ))))) := by
    rw [← terminal.comp_from (Spec.map (CommRingCat.ofHom MvPolynomial.C))]
    infer_instance
  -- By definition `𝔸(σ; S)` is `pullback (terminal.from S) (terminal.from (Spec ℤ[σ]))` and its
  -- structure map `𝔸(σ; S) ↘ S` is `pullback.fst`; Mathlib's own instances for `𝔸(σ; S) ↘ S`
  -- (`IsAffineHom`, `Surjective`, `SmoothOfRelativeDimension`) use this same unfolding.
  exact pullback_fst (terminal.from S) _

end TauCeti.AlgebraicGeometry.FormallySmooth
