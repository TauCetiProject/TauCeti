/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.Prod
public import TauCeti.Algebra.Lie.Solvable.Basic

/-!
# Automorphism decomposition on `Z(L) ⊕ [L, L]`

When the centre `Z(L)` and derived ideal `[L, L]` of a Lie algebra `L` are complementary,
`LieEquiv.ofIsCompl` reconstructs an automorphism of `L` from automorphisms of `Z(L)` and `[L, L]`.
This file records the restriction and uniqueness laws for that reconstruction, independently of any
Cartan-involution predicate.

## Main results

* `LieEquiv.centerCongr_ofIsCompl`: restricting `LieEquiv.ofIsCompl h θZ θD` to `Z(L)` recovers
  `θZ`.
* `LieEquiv.derivedSeriesCongr_ofIsCompl`: restricting `LieEquiv.ofIsCompl h θZ θD` to `[L, L]`
  recovers `θD`.
* `LieEquiv.eq_ofIsCompl_centerCongr_derivedSeriesCongr`: any automorphism of `L = Z(L) ⊕ [L, L]`
  equals the reconstruction from its restrictions to `Z(L)` and `[L, L]`.
-/

public section

open LieAlgebra

namespace LieEquiv

variable {R L : Type*} [CommRing R] [LieRing L] [LieAlgebra R L]

/-- Restricting `ofIsCompl` on `Z(L) ⊕ [L, L]` to the centre recovers `θZ`. -/
@[simp]
theorem centerCongr_ofIsCompl (h : IsCompl (center R L) (derivedSeries R L 1))
    (θZ : center R L ≃ₗ⁅R⁆ center R L) (θD : derivedSeries R L 1 ≃ₗ⁅R⁆ derivedSeries R L 1) :
    (ofIsCompl h θZ θD).centerCongr = θZ := by
  ext x
  simp

/-- Restricting `ofIsCompl` on `Z(L) ⊕ [L, L]` to the derived ideal recovers `θD`. -/
@[simp]
theorem derivedSeriesCongr_ofIsCompl (h : IsCompl (center R L) (derivedSeries R L 1))
    (θZ : center R L ≃ₗ⁅R⁆ center R L) (θD : derivedSeries R L 1 ≃ₗ⁅R⁆ derivedSeries R L 1) :
    (ofIsCompl h θZ θD).derivedSeriesCongr 1 = θD := by
  ext x
  simp

/-- Any automorphism of `L = Z(L) ⊕ [L, L]` is determined by its restrictions to the centre and
the derived ideal. -/
theorem eq_ofIsCompl_centerCongr_derivedSeriesCongr (θ : L ≃ₗ⁅R⁆ L)
    (h : IsCompl (center R L) (derivedSeries R L 1)) :
    θ = ofIsCompl h θ.centerCongr (θ.derivedSeriesCongr 1) := by
  ext x
  obtain ⟨⟨z, d⟩, rfl⟩ :=
    (LieIdeal.prodEquivOfIsCompl (center R L) (derivedSeries R L 1) h).surjective x
  simp [map_add]

end LieEquiv
