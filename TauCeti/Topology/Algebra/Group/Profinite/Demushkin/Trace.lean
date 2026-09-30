/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.Algebra.Group.Profinite.Demushkin.CupForm

/-!
# Normalized trace on the second cohomology of a Demushkin group

The second mod-`p` cohomology of a Demushkin group is a line. A choice of a nonzero class
`ω : H²(G, 𝔽_p)` determines a unique linear trace to `𝔽_p` taking `ω` to `1`. This makes the
scalar-valued cup pairing available with a specified normalization. Changing `ω` by a unit
rescales the trace by the inverse unit.

## Main results

* `TauCeti.IsDemushkin.traceEquiv`: the normalized trace isomorphism.
* `TauCeti.IsDemushkin.traceEquiv_unique`: its characterization by the chosen class.
* `TauCeti.IsDemushkin.traceEquiv_smul`: the change-of-normalization law.

## References

* J. P. Labute, *Classification of Demushkin groups*, Canad. J. Math. 19 (1967), p. 106.
-/

public section

namespace TauCeti

universe u

variable {p : ℕ} [Fact p.Prime] {G : Type u} [Group G] [TopologicalSpace G]
  [IsTopologicalGroup G]

namespace IsDemushkin

variable (hG : IsDemushkin p G)

/-- The unique linear isomorphism `H²(G, 𝔽_p) ≃ 𝔽_p` taking the chosen nonzero class `ω` to `1`.
It is the trace used to turn the Demushkin cup product into a scalar-valued pairing. -/
noncomputable def traceEquiv (ω : cohomFp p G 2) (hω : ω ≠ 0) :
    cohomFp p G 2 ≃ₗ[ZMod p] ZMod p := by
  let e := Classical.choice hG.nonempty_linearEquiv_cohomFp_two
  have heω : e ω ≠ 0 := fun h ↦ hω (e.map_eq_zero_iff.mp h)
  let a : (ZMod p)ˣ := Units.mk0 (e ω) heω
  exact e.trans ((a⁻¹).mulLeftLinearEquiv (ZMod p) (ZMod p))

/-- The trace of the class used to normalize it is `1`. -/
@[simp]
theorem traceEquiv_apply_self (ω : cohomFp p G 2) (hω : ω ≠ 0) :
    hG.traceEquiv ω hω ω = 1 := by
  simp only [traceEquiv, LinearEquiv.trans_apply, Units.mulLeftLinearEquiv_apply]
  exact Units.inv_mul _

/-- A linear map out of the one-dimensional `H²(G, 𝔽_p)` is determined by its value on a
nonzero class. In particular, the normalized trace is unique. -/
theorem traceEquiv_unique (ω : cohomFp p G 2) (hω : ω ≠ 0)
    (φ : cohomFp p G 2 →ₗ[ZMod p] ZMod p) (hφ : φ ω = 1) :
    φ = (hG.traceEquiv ω hω).toLinearMap := by
  ext x
  obtain ⟨c, rfl⟩ := (finrank_eq_one_iff_of_nonzero' ω hω).mp
    hG.finrank_cohomFp_two x
  simp [hφ]

/-- Rescaling the normalization class by a unit rescales the trace by its inverse. -/
theorem traceEquiv_smul (ω : cohomFp p G 2) (hω : ω ≠ 0) (a : (ZMod p)ˣ) :
    hG.traceEquiv ((a : ZMod p) • ω) (smul_ne_zero a.ne_zero hω) =
      (hG.traceEquiv ω hω).trans ((a⁻¹).mulLeftLinearEquiv (ZMod p) (ZMod p)) := by
  apply LinearEquiv.toLinearMap_injective
  symm
  apply hG.traceEquiv_unique ((a : ZMod p) • ω) (smul_ne_zero a.ne_zero hω)
  -- The composite equivalence evaluates by unit multiplication; its coercion does not
  -- simplify through the `LinearEquiv.trans` wrapper here.
  change ((a⁻¹ : (ZMod p)ˣ) : ZMod p) *
    hG.traceEquiv ω hω ((a : ZMod p) • ω) = 1
  rw [map_smul, smul_eq_mul, ← mul_assoc, ← Units.val_mul, inv_mul_cancel,
    Units.val_one, one_mul, hG.traceEquiv_apply_self]

end IsDemushkin

end TauCeti
