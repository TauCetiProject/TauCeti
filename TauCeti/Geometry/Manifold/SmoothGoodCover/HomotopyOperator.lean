/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.DifferentialForm.HomotopyOperator
public import TauCeti.Geometry.Manifold.SmoothGoodCover
import TauCeti.Geometry.Manifold.DifferentialForm.Pullback.Smooth

/-!
# The homotopy operator of a smooth good cover

Every nonempty finite intersection `W` of a smooth good cover `C` carries a chosen smooth
contraction `Φ : W × [0, 1] → W` (`TauCeti.SmoothGoodCover.cylinderContract`) from the constant map
at the center of `W` to the identity. Composing pullback along `Φ` with the homotopy operator of
the cylinder `W × [0, 1]` gives an operator `K ω = h (Φ^* ω)` from `(k + 1)`-forms to `k`-forms on
`W` (`TauCeti.SmoothGoodCover.homotopyOperator`). By the homotopy formula for `Φ`,

`d (K ω) + K (d ω) = ω - Φ (·, 0)^* ω = ω`

for every `C¹` form `ω` of positive degree on `W`, since the end `Φ (·, 0)` of the contraction is
constant (`TauCeti.SmoothGoodCover.mextDeriv_homotopyOperator_add_homotopyOperator_mextDeriv`). In
particular every closed form of positive degree on `W` is exact, with the explicit primitive
`K ω` (`TauCeti.SmoothGoodCover.mextDeriv_homotopyOperator`). This is the local exactness of the
de Rham complex on the members of a good cover that underlies the Čech–de Rham double complex
argument.

The manifold may have boundary or corners. This applies in particular to the good covers of a
prism `M × [0, 1]` built as `C.prod (SmoothGoodCover.ofOrdConnected ...)`, whose members are
products of members of `C` with intervals, possibly containing an endpoint of `[0, 1]`.

## Main declarations

* `TauCeti.SmoothGoodCover.homotopyOperator`: the operator `K ω = h (Φ^* ω)` on a nonempty finite
  intersection of a smooth good cover.
* `TauCeti.SmoothGoodCover.isSmoothForm_homotopyOperator`: `K` preserves `C^r` regularity.
* `TauCeti.SmoothGoodCover.mextDeriv_homotopyOperator_add_homotopyOperator_mextDeriv`: the
  homotopy formula `d (K ω) + K (d ω) = ω` in positive degree.
* `TauCeti.SmoothGoodCover.mextDeriv_homotopyOperator`: `d (K ω) = ω` for a closed form `ω`.

## References

* R. Bott, L. W. Tu, *Differential Forms in Algebraic Topology*, Springer GTM 82 (1982), §4 and §8.
* John M. Lee, *Introduction to Smooth Manifolds*, 2nd ed., Chapter 17, section Homotopy
  Invariance.
-/

public section

noncomputable section

open Set TopologicalSpace
open scoped ContDiff Manifold

namespace TauCeti

namespace SmoothGoodCover

universe u

variable {E H F : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type u} [TopologicalSpace M] [ChartedSpace H M]
  [NormedAddCommGroup F] [NormedSpace ℝ F] {k : ℕ}
  (C : SmoothGoodCover I (M := M)) (s : Finset C.Index) (hs : s.Nonempty)
  (hW : ((s.inf C.openSet : Opens M) : Set M).Nonempty)

/-- The **homotopy operator of a smooth good cover** on a nonempty finite intersection `W` of its
members: the `k`-form `K θ = h (Φ^* θ)` on `W` built from a `(k + 1)`-form `θ`, where
`Φ : W × [0, 1] → W` is the chosen contraction `SmoothGoodCover.cylinderContract` and `h` is the
homotopy operator of the cylinder `W × [0, 1]`. For a `C¹` form, `d (K θ) + K (d θ) = θ`
(`SmoothGoodCover.mextDeriv_homotopyOperator_add_homotopyOperator_mextDeriv`). -/
def homotopyOperator (θ : RoughForm I ↥(s.inf C.openSet) F (k + 1)) :
    RoughForm I ↥(s.inf C.openSet) F k :=
  TauCeti.homotopyOperator (mpullback (I.prod (𝓡∂ 1)) I (C.cylinderContract s hs hW) θ)

/-- The homotopy operator of a smooth good cover is the homotopy operator of the cylinder applied
to the pullback along the chosen contraction. -/
theorem homotopyOperator_def (θ : RoughForm I ↥(s.inf C.openSet) F (k + 1)) :
    C.homotopyOperator s hs hW θ =
      TauCeti.homotopyOperator (mpullback (I.prod (𝓡∂ 1)) I (C.cylinderContract s hs hW) θ) :=
  (rfl)

/-- The homotopy operator of a smooth good cover preserves `C^r` regularity of forms. -/
theorem isSmoothForm_homotopyOperator {r : ℕ∞} [IsManifold I 1 M] [IsManifold I (r + 1) M]
    {θ : RoughForm I ↥(s.inf C.openSet) F (k + 1)} (hθ : IsSmoothForm I r θ) :
    IsSmoothForm I r (C.homotopyOperator s hs hW θ) :=
  (hθ.mpullback ((C.contMDiff_cylinderContract s hs hW).of_le
    (by exact_mod_cast (le_top : r + 1 ≤ ⊤)))).homotopyOperator

/-- **The homotopy formula on a member of a smooth good cover.** On a nonempty finite intersection
`W` of a smooth good cover of a `C²` manifold, possibly with boundary or corners, the homotopy
operator `K` of the cover satisfies `d (K θ) + K (d θ) = θ` for every `C¹` form `θ` of positive
degree on `W` with values in a Banach space. -/
theorem mextDeriv_homotopyOperator_add_homotopyOperator_mextDeriv [IsManifold I 2 M]
    [CompleteSpace F] {θ : RoughForm I ↥(s.inf C.openSet) F (k + 1)} (hθ : IsSmoothForm I 1 θ) :
    mextDeriv (C.homotopyOperator s hs hW θ) + C.homotopyOperator s hs hW (mextDeriv θ) = θ := by
  -- The homotopy formula for the contraction `Φ`, whose end at time `1` is the identity and whose
  -- end at time `0` is constant.
  have h := mextDeriv_homotopyOperator_mpullback_add_homotopyOperator_mpullback_mextDeriv
    ((C.contMDiff_cylinderContract s hs hW).of_le (by simp)) hθ
  simp only [cylinderContract_one, cylinderContract_zero, mpullback_const, sub_zero] at h
  exact h.trans (mpullback_id θ)

/-- **Local exactness on a smooth good cover.** On a nonempty finite intersection `W` of a smooth
good cover of a `C²` manifold, possibly with boundary or corners, every closed `C¹` form `θ` of
positive degree on `W` with values in a Banach space is the exterior derivative of `K θ`. -/
theorem mextDeriv_homotopyOperator [IsManifold I 2 M] [CompleteSpace F]
    {θ : RoughForm I ↥(s.inf C.openSet) F (k + 1)} (hθ : IsSmoothForm I 1 θ)
    (hclosed : mextDeriv θ = 0) :
    mextDeriv (C.homotopyOperator s hs hW θ) = θ := by
  simpa [hclosed, homotopyOperator_def] using
    C.mextDeriv_homotopyOperator_add_homotopyOperator_mextDeriv s hs hW hθ

end SmoothGoodCover

end TauCeti
