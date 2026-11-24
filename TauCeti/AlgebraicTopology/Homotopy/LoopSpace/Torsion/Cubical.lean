/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Homotopy.LoopSpace.Torsion.Basic
public import TauCeti.AlgebraicTopology.Singular.Cubical.Comparison.Basic

/-!
# Detection of non-torsion higher homotopy groups in cubical homology of double loop spaces

When `π₂(Q, q) = 0`, the double Moore loop space `ΩᴹΩᴹQ` is path-connected so `H~₀(ΩᴹΩᴹQ; ℤ) = 0`,
and reduced singular homology agrees with normalized cubical homology in positive degrees via
`TauCeti.singularCubicalHomologyIso`. Consequently, any non-`S`-torsion higher homotopy group
`π_{m + 2}(Q, q)` produces a positive-degree normalized cubical homology class (`1 ≤ k < m + 2`)
not annihilated by any `s ∈ S`
(`TauCeti.exists_forall_smul_ne_zero_homology_normalizedCubicalChainComplex_doubleMooreLoopSpace`).

## Main results

* `TauCeti.exists_forall_smul_ne_zero_homology_normalizedCubicalChainComplex_doubleMooreLoopSpace`:
  positive-degree non-`S`-torsion class in the normalized cubical homology of `ΩᴹΩᴹQ` when
  `π₂(Q, q)` vanishes.

## References

* J.-F. Barraud, M. Damian, V. Humilière, A. Oancea, *Floer homology with DG coefficients.
  Applications to cotangent bundles*, arXiv:2404.07953, Proposition 5.11.
-/

public section

noncomputable section

open AlgebraicTopology HomotopyGroup
open scoped Topology Topology.Homotopy

namespace TauCeti

variable {Q : Type} [TopologicalSpace Q]

/-- **Normalized cubical homology version when `π₂(Q, q)` vanishes.** When
`Subsingleton (π_ 2 Q q)`, `ΩᴹΩᴹQ` is path-connected so `H~₀(ΩᴹΩᴹQ; ℤ) = 0`, and any
non-`S`-torsion higher homotopy group `π_{m + 2}(Q, q)` produces a positive-degree normalized
cubical homology class (`1 ≤ k < m + 2`) not annihilated by any `s ∈ S`. -/
theorem exists_forall_smul_ne_zero_homology_normalizedCubicalChainComplex_doubleMooreLoopSpace
    (q : Q) [Subsingleton (π_ 2 Q q)] (S : Submonoid ℤ) (m : ℕ)
    (hπ : ¬ Module.IsTorsion' (Additive (π_ (m + 2) Q q)) S) :
    ∃ k, 1 ≤ k ∧ k < m + 2 ∧
      ∃ x : ((normalizedCubicalChainComplex ℤ).obj
        (TopCat.of (MooreLoopSpace (MooreLoopSpace Q q) 1))).homology k,
        ∀ s ∈ S, s • x ≠ 0 := by
  obtain ⟨k, hk, x, hx⟩ :=
    exists_forall_smul_ne_zero_reducedSingularHomology_doubleMooreLoopSpace q S m hπ
  have := MooreLoopSpace.pathConnectedSpace_double q
  cases k with
  | zero =>
    have := ModuleCat.isZero_iff_subsingleton.mp
      (isZero_reducedSingularHomologyFunctor_zero (ModuleCat.of ℤ ℤ)
        (TopCat.of (MooreLoopSpace (MooreLoopSpace Q q) 1)))
    exact (hx 1 S.one_mem (Subsingleton.elim _ _)).elim
  | succ r =>
    let e := ((reducedSingularHomologySuccIso (ModuleCat.of ℤ ℤ) r).app
      (TopCat.of (MooreLoopSpace (MooreLoopSpace Q q) 1))).trans
      (singularCubicalHomologyIso ℤ (TopCat.of (MooreLoopSpace (MooreLoopSpace Q q) 1)) (r + 1))
    exact ⟨r + 1, Nat.succ_le_succ (Nat.zero_le r), hk, e.hom.hom x, fun s hs h0 ↦
      hx s hs <| e.toLinearEquiv.toAddEquiv.injective
        (by rw [map_zsmul]; exact h0.trans (map_zero _).symm)⟩

end TauCeti
