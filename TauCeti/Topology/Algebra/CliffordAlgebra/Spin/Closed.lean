/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.Algebra.CliffordAlgebra.Spin.Compact
public import TauCeti.LinearAlgebra.CliffordAlgebra.Lipschitz.CliffordGroup
public import Mathlib.Topology.Algebra.Star.Unitary

/-!
# Closed Spin carriers

For a nondegenerate quadratic form on a finite-dimensional space over a Hausdorff topological field
in which `2` is invertible, Mathlib's Spin group is closed in the Clifford algebra with its module
topology. In positive dimension the Spin group is the set of even unitary elements whose twisted
conjugation preserves the vectors, each of which is a closed condition: the unitary group is closed,
the even part and the space of vectors are finite-dimensional subspaces, and twisted conjugation is
continuous. On the zero space the Spin group is trivial. Over a locally compact field the Spin
group is therefore a locally compact Hausdorff topological group, the Spin point group over `ℝ` and
`ℚ_p`.

This module also proves that the compact real Spin carrier is closed in the units of its
Clifford algebra, providing the closed-subgroup input for its Lie-group structure. The corresponding
special-orthogonal carrier is provided separately in `RealSpecialOrthogonal.lean`.

## References

* H. B. Lawson and M.-L. Michelsohn, *Spin Geometry* (1989), Chapter I, Section 2.

## Main results

* `CliffordAlgebra.isClosed_spinGroup`: the Spin group of a nondegenerate form is closed in the
  Clifford algebra.
* `CliffordAlgebra.locallyCompactSpace_spinGroup`: over a locally compact field it is locally
  compact.
* `TauCeti.CliffordAlgebra.isClosed_range_realCliffordSpinGroupZero_toUnits`: the compact real Spin
  carrier is closed in the Clifford-algebra units.
-/

public section

open Set

namespace CliffordAlgebra

variable {K V : Type*} [Field K] [TopologicalSpace K] [IsTopologicalRing K] [T2Space K]
  [Invertible (2 : K)] [AddCommGroup V] [Module K V] [FiniteDimensional K V]
  (Q : QuadraticForm K V)

/-- The Spin group of a nondegenerate quadratic form on a finite-dimensional space over a
Hausdorff topological field in which `2` is invertible is closed in the Clifford algebra with its
module topology. -/
theorem isClosed_spinGroup (hQ : Q.Nondegenerate) :
    IsClosed (spinGroup Q : Set (CliffordAlgebra Q)) := by
  rcases subsingleton_or_nontrivial V with hV | hV
  · -- On the zero space the Lipschitz group is trivial, so the Spin group is `{1}`.
    have h : (spinGroup Q : Set (CliffordAlgebra Q)) = {1} := by
      refine Subset.antisymm (fun x hx => ?_) (singleton_subset_iff.mpr (spinGroup Q).one_mem)
      obtain ⟨u, hu, rfl⟩ := pinGroup.mem_lipschitzGroup (spinGroup.mem_pin hx)
      simp only [SetLike.mem_coe, Subgroup.mem_toSubmonoid, lipschitzGroup_eq_bot,
        Subgroup.mem_bot] at hu
      simp [hu]
    rw [h]
    exact isClosed_singleton
  · have h : (spinGroup Q : Set (CliffordAlgebra Q)) =
        (unitary (CliffordAlgebra Q) : Set (CliffordAlgebra Q)) ∩
          (even Q : Set (CliffordAlgebra Q)) ∩
          ⋂ m, (fun x : CliffordAlgebra Q => involute (Q := Q) x * ι Q m * star x) ⁻¹'
            (LinearMap.range (ι Q) : Set (CliffordAlgebra Q)) := by
      ext x
      simp only [SetLike.mem_coe,
        mem_spinGroup_iff_unitary_even_and_involute_act_ι_mem_range_ι Q hQ hQ.exists_isUnit,
        mem_inter_iff, mem_iInter, mem_preimage, and_assoc]
    have heven : (even Q : Set (CliffordAlgebra Q)) = (evenOdd Q 0 : Set (CliffordAlgebra Q)) := by
      rw [← even_toSubmodule, Subalgebra.coe_toSubmodule]
    rw [h, heven]
    refine (isClosed_unitary.inter (Submodule.isClosed_of_isModuleTopology _)).inter
      (isClosed_iInter fun m => (Submodule.isClosed_of_isModuleTopology _).preimage ?_)
    fun_prop

/-- The Spin group of a nondegenerate quadratic form on a finite-dimensional space over a
Hausdorff locally compact topological field in which `2` is invertible is locally compact, being
closed in the locally compact Clifford algebra. -/
theorem locallyCompactSpace_spinGroup [LocallyCompactSpace K] (hQ : Q.Nondegenerate) :
    LocallyCompactSpace (spinGroup Q) :=
  (isClosed_spinGroup Q hQ).locallyCompactSpace

end CliffordAlgebra

namespace TauCeti

namespace CliffordAlgebra

open _root_.CliffordAlgebra

noncomputable section

/-- The compact real Spin carrier is closed in the units of its Clifford algebra. -/
theorem isClosed_range_realCliffordSpinGroupZero_toUnits (n : ℕ) :
    IsClosed (Set.range (spinGroup.toUnits (Q := realCliffordForm n 0))) := by
  let A := CliffordAlgebra (realCliffordForm n 0)
  have hc : IsCompact (Set.univ : Set (realCliffordSpinGroupZero n)) := isCompact_univ
  have himage : IsClosed ((fun x : realCliffordSpinGroupZero n => (x : A)) '' Set.univ) :=
    (hc.image (continuous_subtype_val :
      Continuous ((↑) : realCliffordSpinGroupZero n → A))).isClosed
  have hsu : (fun x : realCliffordSpinGroupZero n => (x : A)) '' Set.univ =
      (realCliffordSpinGroupZero n : Set A) :=
    Subtype.coe_image_univ (realCliffordSpinGroupZero n : Set A)
  have hs : IsClosed (realCliffordSpinGroupZero n : Set A) := by
    rw [← hsu]
    exact himage
  let f : Aˣ → A := fun u => u
  have hu : IsClosed (f ⁻¹' (realCliffordSpinGroupZero n : Set A)) := by
    simpa only [f] using hs.preimage Units.continuous_val
  have hcoe (x : realCliffordSpinGroupZero n) :
      ((spinGroup.toUnits (Q := realCliffordForm n 0) x : Aˣ) : A) = (x : A) := by
    -- `spinGroup.toUnits` stores the subtype value as its unit value by definition.
    rfl
  have hset : Set.range (spinGroup.toUnits (Q := realCliffordForm n 0)) =
      f ⁻¹' (realCliffordSpinGroupZero n : Set A) := by
    ext u
    constructor
    · rintro ⟨x, rfl⟩
      have hx : (x : A) ∈ (realCliffordSpinGroupZero n : Set A) := x.2
      simpa only [f, Set.mem_preimage, hcoe x] using hx
    · intro hu'
      refine ⟨⟨u, hu'⟩, ?_⟩
      apply Units.ext
      exact hcoe ⟨u, hu'⟩
  rw [hset]
  exact hu

end

end CliffordAlgebra

end TauCeti

end
