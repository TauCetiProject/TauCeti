/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.CartanInvolution.Basic
public import TauCeti.Algebra.Lie.Reductive.Decomposition
import TauCeti.Algebra.Lie.Killing.Perfect
import TauCeti.Algebra.Lie.Reductive.Basic
import TauCeti.Logic.Equiv.Basic

/-!
# Reductive Cartan involutions

On a reductive Lie algebra `L = Z(L) ⊕ [L, L]`, the Killing form vanishes on the centre `Z(L)`, so
the Cartan-involution condition is imposed on the derived algebra `[L, L]`: a Lie algebra
automorphism `θ : L ≃ₗ⁅R⁆ L` is a **reductive Cartan involution**
(`LieEquiv.IsReductiveCartanInvolution`) when `θ` is involutive and its restriction
`θ.derivedSeriesCongr 1` to `[L, L]` is a Cartan involution.

Over any ordered field `K`, with no finite-dimensionality assumption on `L` itself, a
reductive Cartan involution forces `[L, L]` to be Killing, finite-dimensional, and semisimple,
forces `L` to be reductive (`HasCentralRadical K L`), and splits `L = Z(L) ⊕ [L, L]` (every
derivation of the finite-dimensional Killing algebra `[L, L]` is inner). Conversely, whenever
`L = Z(L) ⊕ [L, L]`, any involutive automorphism of `Z(L)` and any Cartan involution of `[L, L]`
extend uniquely via `LieEquiv.ofIsCompl` to a reductive Cartan involution of `L`.

## Main definitions

* `LieEquiv.IsReductiveCartanInvolution`: predicate stating that `θ` is involutive and its
  restriction to `derivedSeries K L 1` is a Cartan involution.

## Main results

* `LieEquiv.isReductiveCartanInvolution_ofIsCompl_iff`: an automorphism built from `(θZ, θD)` on
  `Z(L) ⊕ [L, L]` is a reductive Cartan involution iff `θZ` is involutive and `θD` is a Cartan
  involution.
* `LieEquiv.IsReductiveCartanInvolution.hasCentralRadical` and
  `LieEquiv.IsReductiveCartanInvolution.isCompl_center_derivedSeries`: a reductive Cartan
  involution over an ordered field forces `L` to be reductive and split as `Z(L) ⊕ [L, L]`.
* `LieEquiv.IsCartanInvolution.isReductiveCartanInvolution` and
  `LieEquiv.IsReductiveCartanInvolution.isCartanInvolution_iff_center_eq_bot`: comparison with
  semisimple Cartan involutions.

## References

* A. W. Knapp, *Lie Groups Beyond an Introduction*, 2nd ed., Progress in Mathematics 140,
  Birkhäuser, 2002, Chapter VI, §2 and Chapter VII, §2.
-/

public section

open LieAlgebra

namespace LieEquiv

variable {K L L' : Type*} [Field K] [LinearOrder K]
  [LieRing L] [LieAlgebra K L] [LieRing L'] [LieAlgebra K L']

/-- A **reductive Cartan involution** of a Lie algebra `L`: an involutive Lie algebra automorphism
whose restriction to the derived ideal `[L, L]` is a Cartan involution. -/
def IsReductiveCartanInvolution (θ : L ≃ₗ⁅K⁆ L) : Prop :=
  Function.Involutive θ ∧ (θ.derivedSeriesCongr 1).IsCartanInvolution

/-- Unfolded characterization of a reductive Cartan involution. -/
theorem isReductiveCartanInvolution_iff (θ : L ≃ₗ⁅K⁆ L) :
    θ.IsReductiveCartanInvolution ↔
      Function.Involutive θ ∧ (θ.derivedSeriesCongr 1).IsCartanInvolution :=
  Iff.rfl

/-- Transport of `IsReductiveCartanInvolution` along an intertwining Lie equivalence. -/
theorem isReductiveCartanInvolution_iff_of_intertwine (e : L ≃ₗ⁅K⁆ L')
    {θ : L ≃ₗ⁅K⁆ L} {θ' : L' ≃ₗ⁅K⁆ L'} (h : ∀ x, θ' (e x) = e (θ x)) :
    θ'.IsReductiveCartanInvolution ↔ θ.IsReductiveCartanInvolution := by
  have hint : ∀ x : derivedSeries K L 1,
      θ'.derivedSeriesCongr 1 (e.derivedSeriesCongr 1 x) =
        e.derivedSeriesCongr 1 (θ.derivedSeriesCongr 1 x) :=
    fun x ↦ Subtype.ext (by simp [h])
  exact and_congr (e.toLinearEquiv.toEquiv.involutive_iff_of_intertwine h)
    (isCartanInvolution_iff_of_intertwine (e.derivedSeriesCongr 1) hint)

/-- Conjugating a Lie automorphism preserves the reductive Cartan-involution property. -/
theorem isReductiveCartanInvolution_conj (e : L ≃ₗ⁅K⁆ L') (θ : L ≃ₗ⁅K⁆ L) :
    ((e.symm.trans θ).trans e).IsReductiveCartanInvolution ↔ θ.IsReductiveCartanInvolution :=
  isReductiveCartanInvolution_iff_of_intertwine e fun x ↦ by simp

/-- On `L = Z(L) ⊕ [L, L]`, an automorphism built from `(θZ, θD)` is a reductive Cartan involution
if and only if `θZ` is involutive and `θD` is a Cartan involution. -/
theorem isReductiveCartanInvolution_ofIsCompl_iff (h : IsCompl (center K L) (derivedSeries K L 1))
    (θZ : center K L ≃ₗ⁅K⁆ center K L) (θD : derivedSeries K L 1 ≃ₗ⁅K⁆ derivedSeries K L 1) :
    (ofIsCompl h θZ θD).IsReductiveCartanInvolution ↔
      Function.Involutive θZ ∧ θD.IsCartanInvolution := by
  rw [IsReductiveCartanInvolution, involutive_ofIsCompl_iff, derivedSeriesCongr_ofIsCompl]
  exact ⟨fun ⟨⟨hZ, _⟩, hD⟩ ↦ ⟨hZ, hD⟩, fun ⟨hZ, hD⟩ ↦ ⟨⟨hZ, hD.involutive⟩, hD⟩⟩

namespace IsReductiveCartanInvolution

variable {θ : L ≃ₗ⁅K⁆ L}

/-- A reductive Cartan involution is involutive. -/
theorem involutive (hθ : θ.IsReductiveCartanInvolution) : Function.Involutive θ :=
  hθ.1

/-- The restriction of a reductive Cartan involution to `[L, L]` is a Cartan involution. -/
theorem isCartanInvolution_derivedSeries (hθ : θ.IsReductiveCartanInvolution) :
    (θ.derivedSeriesCongr 1).IsCartanInvolution :=
  hθ.2

/-- The restriction of a reductive Cartan involution to the centre is involutive. -/
theorem involutive_centerCongr (hθ : θ.IsReductiveCartanInvolution) :
    Function.Involutive θ.centerCongr :=
  LieEquiv.involutive_centerCongr hθ.1

/-- The derived algebra `[L, L]` has nondegenerate Killing form. -/
theorem isKilling_derivedSeries (hθ : θ.IsReductiveCartanInvolution) :
    LieAlgebra.IsKilling K (derivedSeries K L 1) :=
  hθ.2.isKilling

/-- The derived algebra `[L, L]` is finite-dimensional over `K`. -/
theorem finite_derivedSeries (hθ : θ.IsReductiveCartanInvolution) :
    Module.Finite K (derivedSeries K L 1) :=
  hθ.2.finiteDimensional

/-- The derived algebra `[L, L]` of a Lie algebra with a reductive Cartan involution is
semisimple. -/
theorem isSemisimple_derivedSeries (hθ : θ.IsReductiveCartanInvolution) :
    LieAlgebra.IsSemisimple K (derivedSeries K L 1) :=
  hθ.2.isSemisimple

/-- **Reductivity from a reductive Cartan involution.** A Lie algebra over an ordered field
admitting a reductive Cartan involution has central radical, with no finite-dimensionality
assumption on `L`. -/
theorem hasCentralRadical (hθ : θ.IsReductiveCartanInvolution) :
    LieAlgebra.HasCentralRadical K L := by
  have : LieAlgebra.IsSemisimple K (derivedSeries K L 1) := hθ.isSemisimple_derivedSeries
  exact TauCeti.hasCentralRadical_of_hasTrivialRadical_derivedSeries K L

/-- **Centre/derived splitting from a reductive Cartan involution.** A Lie algebra over an ordered
field admitting a reductive Cartan involution splits as `L = Z(L) ⊕ [L, L]`. -/
theorem isCompl_center_derivedSeries (hθ : θ.IsReductiveCartanInvolution) :
    IsCompl (center K L) (derivedSeries K L 1) :=
  have := hθ.isKilling_derivedSeries
  TauCeti.isCompl_center_derivedSeries_of_isKilling_derivedSeries K L

/-- A reductive Cartan involution equals the automorphism reconstructed from its restrictions to
the centre and the derived ideal. -/
theorem eq_ofIsCompl (hθ : θ.IsReductiveCartanInvolution) :
    θ = ofIsCompl hθ.isCompl_center_derivedSeries θ.centerCongr (θ.derivedSeriesCongr 1) :=
  θ.eq_ofIsCompl_centerCongr_derivedSeriesCongr hθ.isCompl_center_derivedSeries

end IsReductiveCartanInvolution

/-- Every semisimple Cartan involution is in particular a reductive Cartan involution, since a
Killing Lie algebra over a field is perfect. -/
theorem IsCartanInvolution.isReductiveCartanInvolution {θ : L ≃ₗ⁅K⁆ L}
    (hθ : θ.IsCartanInvolution) : θ.IsReductiveCartanInvolution := by
  have : LieAlgebra.IsKilling K L := hθ.isKilling
  let e := derivedSeriesTopEquiv (TauCeti.derivedSeries_one_eq_top_of_isKilling K L)
  refine ⟨hθ.involutive, (isCartanInvolution_iff_of_intertwine e fun x ↦ ?_).mp hθ⟩
  rw [coe_derivedSeriesTopEquiv, coe_derivedSeriesTopEquiv, coe_derivedSeriesCongr]

/-- A reductive Cartan involution is a (semisimple) Cartan involution if and only if the centre
vanishes. -/
theorem IsReductiveCartanInvolution.isCartanInvolution_iff_center_eq_bot {θ : L ≃ₗ⁅K⁆ L}
    (hθ : θ.IsReductiveCartanInvolution) :
    θ.IsCartanInvolution ↔ center K L = ⊥ := by
  constructor
  · intro h
    have := h.isSemisimple
    exact LieAlgebra.center_eq_bot K L
  · intro hZ
    have htop : derivedSeries K L 1 = ⊤ := by
      have hc := hθ.isCompl_center_derivedSeries
      rw [hZ] at hc
      rw [← hc.sup_eq_top, bot_sup_eq]
    let e := derivedSeriesTopEquiv htop
    refine (isCartanInvolution_iff_of_intertwine e fun x ↦ ?_).mpr hθ.2
    rw [coe_derivedSeriesTopEquiv, coe_derivedSeriesTopEquiv, coe_derivedSeriesCongr]

end LieEquiv
