/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Module.ZLattice.Basic
public import Mathlib.GroupTheory.Index
public import Mathlib.LinearAlgebra.BilinearForm.DualLattice
import Mathlib.LinearAlgebra.FreeModule.Finite.Quotient
import TauCeti.Algebra.Module.Lattice

/-!
# Dual lattices for a nondegenerate real bilinear form

Let `B` be a nondegenerate real bilinear form on a finite-dimensional real normed space `V`, and
let `L` be a full lattice in `V` (`[DiscreteTopology L] [IsZLattice ℝ L]`). The dual
`L^⊥ = {v : B (v, l) ∈ ℤ for all l ∈ L}` of `L` for `B` is Mathlib's `B.dualSubmodule L`.
This file records the facts about it that follow from Mathlib's dual-basis description
(`LinearMap.BilinForm.dualSubmodule_span_of_basis`), since `L` is the `ℤ`-span of a real basis:

* `L^⊥` is the `ℤ`-span of the basis dual, for `B`, to a basis of `L`
  (`LinearMap.BilinForm.dualSubmodule_eq_span_dualBasis_ofZLatticeBasis`), hence a full lattice;
* **double duality**: `L` is the dual of `L^⊥` for the flipped form
  (`LinearMap.BilinForm.dualSubmodule_flip_dualSubmodule_of_isZLattice`);
* if `B` is integral on `L`, that is `L ≤ L^⊥`, then `L` has finite index in `L^⊥`
  (`LinearMap.BilinForm.finite_quotient_dualSubmodule`,
  `LinearMap.BilinForm.relIndex_dualSubmodule_ne_zero`), so `N L^⊥ ⊆ L` for `N = [L^⊥ : L]`.

These are used for the Riemann form of an Appell–Humbert datum in
`TauCeti.Analysis.Complex.AppellHumbert.Frobenius`.
-/

public section

open Module Set

namespace LinearMap.BilinForm

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  (B : LinearMap.BilinForm ℝ V) (hB : B.Nondegenerate) (L : Submodule ℤ V)
  [DiscreteTopology L] [IsZLattice ℝ L]

include hB

/-- The dual of a full lattice `L` for a nondegenerate form `B` is the `ℤ`-span of the basis dual,
for `B`, to a basis of `L`. -/
theorem dualSubmodule_eq_span_dualBasis_ofZLatticeBasis {ι : Type*} [Finite ι] [DecidableEq ι]
    (b : Basis ι ℤ L) :
    B.dualSubmodule L = Submodule.span ℤ (Set.range (B.dualBasis hB (b.ofZLatticeBasis ℝ L))) := by
  have h := B.dualSubmodule_span_of_basis (R := ℤ) hB (b.ofZLatticeBasis ℝ L)
  rwa [Basis.ofZLatticeBasis_span] at h

/-- **Double duality.** For a nondegenerate form `B`, a full lattice `L` is the dual of its dual
`L^⊥` for the flipped form: a vector `v` with `B (a, v) ∈ ℤ` for every `a ∈ L^⊥` lies in `L`. -/
theorem dualSubmodule_flip_dualSubmodule_of_isZLattice :
    B.flip.dualSubmodule (B.dualSubmodule L) = L := by
  classical
  have h := B.dualSubmodule_flip_dualSubmodule_of_basis (R := ℤ) hB
    ((Free.chooseBasis ℤ L).ofZLatticeBasis ℝ L)
  rwa [Basis.ofZLatticeBasis_span] at h

/-- For a nondegenerate form `B` integral on a full lattice `L`, that is `L ≤ L^⊥`, the lattice `L`
has finite index in its dual `L^⊥`. -/
theorem finite_quotient_dualSubmodule (hL : L ≤ B.dualSubmodule L) :
    Finite (B.dualSubmodule L ⧸ (L.submoduleOf (B.dualSubmodule L)).toAddSubgroup) := by
  classical
  -- `L^⊥` is the span of a real basis, so it is a full lattice of the same rank as `L`.
  have : ∃ _ : DiscreteTopology (B.dualSubmodule L), IsZLattice ℝ (B.dualSubmodule L) := by
    rw [B.dualSubmodule_eq_span_dualBasis_ofZLatticeBasis hB L (Free.chooseBasis ℤ L)]
    exact ⟨inferInstance, inferInstance⟩
  obtain ⟨_, _⟩ := this
  have := ZLattice.module_free ℝ (B.dualSubmodule L)
  have := ZLattice.module_finite ℝ (B.dualSubmodule L)
  refine (Submodule.finiteQuotient_iff _).mpr ?_
  rw [(Submodule.submoduleOfEquivOfLe hL).finrank_eq, ZLattice.rank ℝ L,
    ZLattice.rank ℝ (B.dualSubmodule L)]

/-- For a nondegenerate form `B` integral on a full lattice `L`, the index `N = [L^⊥ : L]` is not
zero; Mathlib's `AddSubgroup.nsmul_relIndex_mem` then gives `N L^⊥ ⊆ L`. -/
theorem relIndex_dualSubmodule_ne_zero (hL : L ≤ B.dualSubmodule L) :
    L.toAddSubgroup.relIndex (B.dualSubmodule L).toAddSubgroup ≠ 0 := by
  have := B.finite_quotient_dualSubmodule hB L hL
  rw [← Submodule.natCard_quotient_submoduleOf]
  exact Nat.card_pos.ne'

end LinearMap.BilinForm
