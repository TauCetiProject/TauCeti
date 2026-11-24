/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.Coadjoint.Height
public import TauCeti.Algebra.Lie.InvariantForm.RootPlane
import Mathlib.Algebra.Module.Submodule.Union

/-!
# Root-plane decompositions from maximal abelian subspaces

Let `B` be a symmetric positive definite bilinear form on a finite-dimensional real Lie algebra
`L`, invariant under every `ad X`, as on the Lie algebra of a compact Lie group. For every abelian
subspace `t`, `L` is the direct sum of the centralizer of `t` and finitely many real root planes
of `t` (`TauCeti.exists_isInternal_isRootPlane`). This file chooses `t` so that this is a
root-plane decomposition in the sense of `TauCeti.IsRootPlaneDecomposition`, which asks `t` itself
and the planes to span `L`.

* A maximal abelian subspace `t` is its own centralizer
  (`TauCeti.iInf_ker_ad_eq_of_forall_lt`, over every commutative ring): if `Y` commutes with
  `t`, then `t + R Y` is abelian, so it is `t`.
* Hence the root planes of every maximal abelian subspace `t` form a root-plane decomposition
  `L = t + Σ E_k` with two-dimensional planes and nonzero roots `α_k`. As finitely many nonzero
  linear forms on a real vector space do not vanish simultaneously everywhere, `t` contains a
  **regular** element `X`, one with `α_k(X) ≠ 0` for every `k`
  (`TauCeti.exists_isRootPlaneDecomposition_of_forall_lt`).
* Maximal abelian subspaces exist, so some root-plane decomposition has a regular element
  (`TauCeti.exists_isRootPlaneDecomposition`).

The height of a regular element is a Morse function on every coadjoint orbit
(`TauCeti.IsRootPlaneDecomposition.isMorse_orbitMap_coadjointRepresentation_apply`).
The subspace `t` here is only a maximal abelian subspace of the Lie algebra; no maximal torus of a
Lie group is involved.

## References

* T. Bröcker and T. tom Dieck, *Representations of Compact Lie Groups*, Graduate Texts in
  Mathematics 98, Springer, 1985, Chapter V, § 1.
-/

public section

open Module (Dual finrank)

namespace TauCeti

variable {L : Type*} [LieRing L] [LieAlgebra ℝ L] [FiniteDimensional ℝ L]
  {B : LinearMap.BilinForm ℝ L}

/-- **Root-plane decompositions of a maximal abelian subspace.** For a symmetric positive
definite invariant bilinear form `B` on a finite-dimensional real Lie algebra `L` and a maximal
abelian subspace `t` of `L`, the root planes of `t` form a root-plane decomposition
`L = t + Σ E_k` (`TauCeti.IsRootPlaneDecomposition`) with two-dimensional planes, and some element
`X ∈ t` is regular: no root vanishes at it. -/
theorem exists_isRootPlaneDecomposition_of_forall_lt (hB : B.IsSymm)
    (hpos : ∀ x, x ≠ 0 → 0 < B x x) (hinv : B.lieInvariant L) {t : Submodule ℝ L}
    (ht : ∀ H ∈ t, ∀ H' ∈ t, ⁅H, H'⁆ = 0)
    (hmax : ∀ s : Submodule ℝ L, t < s → ¬ ∀ H ∈ s, ∀ H' ∈ s, ⁅H, H'⁆ = 0) :
    ∃ (r : ℕ) (α : Fin r → Dual ℝ t) (E : Fin r → Submodule ℝ L)
      (J : (k : Fin r) → Module.End ℝ (E k)),
      IsRootPlaneDecomposition B t α E J ∧ (∀ k, finrank ℝ (E k) = 2) ∧
        ∃ X : t, ∀ k, α k X ≠ 0 := by
  have hcent := iInf_ker_ad_eq_of_forall_lt ht hmax
  obtain ⟨r, α, E, J, hint, hroot, hα, hrank, -, horth⟩ :=
    exists_isInternal_isRootPlane hB hpos hinv ht
  rw [hcent] at hint
  refine ⟨r, α, E, J, ⟨hroot, fun hij ↦ horth hij.symm, fun _ _ _ hv0 ↦ hpos _ hv0,
    fun hH hH' ↦ ht _ hH _ hH', ?_⟩, hrank,
    Module.Dual.exists_forall_ne_zero_of_forall_exists α fun k ↦
      not_forall.1 fun h ↦ hα k (LinearMap.ext h)⟩
  rw [← hint.submodule_iSup_eq_top, iSup_option]
  simp only [Option.elim_none, Option.elim_some]

/-- **Root-plane decompositions with a regular element.** For a symmetric positive definite
invariant bilinear form `B` on a finite-dimensional real Lie algebra `L`, there is a root-plane
decomposition `L = t + Σ E_k` (`TauCeti.IsRootPlaneDecomposition`) with two-dimensional planes,
together with an element `X ∈ t` at which no root vanishes. -/
theorem exists_isRootPlaneDecomposition (hB : B.IsSymm) (hpos : ∀ x, x ≠ 0 → 0 < B x x)
    (hinv : B.lieInvariant L) :
    ∃ (t : Submodule ℝ L) (r : ℕ) (α : Fin r → Dual ℝ t) (E : Fin r → Submodule ℝ L)
      (J : (k : Fin r) → Module.End ℝ (E k)),
      IsRootPlaneDecomposition B t α E J ∧ (∀ k, finrank ℝ (E k) = 2) ∧
        ∃ X : t, ∀ k, α k X ≠ 0 := by
  -- Take `t` a maximal abelian subspace, which exists since the subspaces of `L` satisfy the
  -- ascending chain condition.
  obtain ⟨t, ht, hmax⟩ := (wellFounded_gt (α := Submodule ℝ L)).has_min
    {s | ∀ H ∈ s, ∀ H' ∈ s, ⁅H, H'⁆ = 0} ⟨⊥, fun H hH H' _ ↦ by simp_all⟩
  exact ⟨t, exists_isRootPlaneDecomposition_of_forall_lt hB hpos hinv ht
    fun s hs h ↦ hmax s h hs⟩

end TauCeti
