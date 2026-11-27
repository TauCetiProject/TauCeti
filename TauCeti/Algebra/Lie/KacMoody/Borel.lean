/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.KacMoody.Triangular
public import TauCeti.Algebra.Lie.Subalgebra.Complement
import TauCeti.Algebra.Lie.Subalgebra.LieSpan

/-!
# The positive Borel subalgebra of a Kac–Moody presentation

The Cartan subalgebra normalizes the positive subalgebra, so their vector-space sum is a
Lie subalgebra `𝔟⁺ = 𝔥 + n⁺`. The triangular decomposition makes `n⁻` a complement of `𝔟⁺`,
and makes `𝔥` and `n⁺` complementary inside `𝔟⁺`. These are the two decompositions used by
PBW to factor the enveloping algebra and construct induced highest-weight modules.

The construction works over every field and for every integer matrix admitting a realization;
it needs neither a finite-dimensional algebra nor a nonsingular Cartan matrix.

The sum construction follows the finite-type Borel construction in
`TauCeti.Algebra.Lie.Weights.Borel`, using the generator relations in place of finite root theory.

## References

* V. G. Kac, *Infinite-dimensional Lie algebras*, third edition, §1.3 and §9.1.
-/

public section

namespace TauCeti.KacMoody

open LieSubalgebra

variable {I K H : Type*} [Field K] [AddCommGroup H] [Module K H] {A : Matrix I I ℤ}
  (R : CartanRealization (A.map (Int.cast : ℤ → K)) H)

/-- The Cartan subalgebra preserves the positive subalgebra under the adjoint action. -/
theorem lie_mem_positiveSubalgebra_of_mem_cartanSubalgebra
    {x y : PresentedLieAlgebra R} (hx : x ∈ cartanSubalgebra R)
    (hy : y ∈ positiveSubalgebra R) : ⁅x, y⁆ ∈ positiveSubalgebra R := by
  obtain ⟨h, rfl⟩ := (mem_cartanSubalgebra_iff R).1 hx
  rw [positiveSubalgebra_def] at hy ⊢
  refine lie_mem_of_mem_lieSpan ?_ hy
  rintro _ ⟨i, rfl⟩
  rw [lie_cartanElement_positiveGenerator]
  exact Submodule.smul_mem _ _ (subset_lieSpan ⟨i, rfl⟩)

private theorem lie_mem_cartan_sup_positive {x y : PresentedLieAlgebra R}
    (hx : x ∈ (cartanSubalgebra R).toSubmodule ⊔ (positiveSubalgebra R).toSubmodule)
    (hy : y ∈ (cartanSubalgebra R).toSubmodule ⊔ (positiveSubalgebra R).toSubmodule) :
    ⁅x, y⁆ ∈ (cartanSubalgebra R).toSubmodule ⊔ (positiveSubalgebra R).toSubmodule := by
  obtain ⟨h, hh, p, hp, rfl⟩ := Submodule.mem_sup.1 hx
  obtain ⟨k, hk, q, hq, rfl⟩ := Submodule.mem_sup.1 hy
  rw [add_lie, lie_add, lie_add]
  exact add_mem
    (add_mem (Submodule.mem_sup_left ((cartanSubalgebra R).lie_mem hh hk))
      (Submodule.mem_sup_right (lie_mem_positiveSubalgebra_of_mem_cartanSubalgebra R hh hq)))
    (add_mem (Submodule.mem_sup_right (by
      rw [← lie_skew]
      exact neg_mem (lie_mem_positiveSubalgebra_of_mem_cartanSubalgebra R hk hp)))
      (Submodule.mem_sup_right ((positiveSubalgebra R).lie_mem hp hq)))

/-- The positive Borel subalgebra `𝔟⁺ = 𝔥 + n⁺` of the full presentation. -/
noncomputable def borelSubalgebra : LieSubalgebra K (PresentedLieAlgebra R) where
  __ := (cartanSubalgebra R).toSubmodule ⊔ (positiveSubalgebra R).toSubmodule
  lie_mem' := lie_mem_cartan_sup_positive R

/-- The Borel subalgebra is the vector-space sum of its Cartan and positive parts. -/
@[simp]
theorem borelSubalgebra_toSubmodule :
    (borelSubalgebra R).toSubmodule =
      (cartanSubalgebra R).toSubmodule ⊔ (positiveSubalgebra R).toSubmodule := (rfl)

/-- An element of the Borel subalgebra is a sum of a Cartan element and a positive element. -/
theorem mem_borelSubalgebra_iff {z : PresentedLieAlgebra R} :
    z ∈ borelSubalgebra R ↔ ∃ h ∈ cartanSubalgebra R,
      ∃ p ∈ positiveSubalgebra R, h + p = z :=
  Submodule.mem_sup

/-- The Cartan subalgebra lies in the positive Borel subalgebra. -/
theorem cartanSubalgebra_le_borelSubalgebra : cartanSubalgebra R ≤ borelSubalgebra R :=
  fun _ hx => Submodule.mem_sup_left hx

/-- The positive subalgebra lies in the positive Borel subalgebra. -/
theorem positiveSubalgebra_le_borelSubalgebra : positiveSubalgebra R ≤ borelSubalgebra R :=
  fun _ hx => Submodule.mem_sup_right hx

/-- The Borel subalgebra is also the join in the lattice of Lie subalgebras. -/
theorem borelSubalgebra_eq_sup :
    borelSubalgebra R = cartanSubalgebra R ⊔ positiveSubalgebra R := by
  refine le_antisymm ?_ (sup_le (cartanSubalgebra_le_borelSubalgebra R)
    (positiveSubalgebra_le_borelSubalgebra R))
  intro z hz
  obtain ⟨h, hh, p, hp, rfl⟩ := (mem_borelSubalgebra_iff R).1 hz
  exact add_mem (le_sup_left (a := cartanSubalgebra R) hh)
    (le_sup_right (b := positiveSubalgebra R) hp)

/-- The positive subalgebra is stable under the adjoint action of the Borel subalgebra. -/
theorem lie_mem_positiveSubalgebra_of_mem_borelSubalgebra
    {x y : PresentedLieAlgebra R} (hx : x ∈ borelSubalgebra R)
    (hy : y ∈ positiveSubalgebra R) : ⁅x, y⁆ ∈ positiveSubalgebra R := by
  obtain ⟨h, hh, p, hp, rfl⟩ := (mem_borelSubalgebra_iff R).1 hx
  rw [add_lie]
  exact add_mem (lie_mem_positiveSubalgebra_of_mem_cartanSubalgebra R hh hy)
    ((positiveSubalgebra R).lie_mem hp hy)

/-- The negative subalgebra and the positive Borel subalgebra are complementary as subspaces. -/
theorem isCompl_negativeSubalgebra_borelSubalgebra :
    IsCompl (negativeSubalgebra R).toSubmodule (borelSubalgebra R).toSubmodule := by
  refine ⟨?_, ?_⟩
  · rw [borelSubalgebra_toSubmodule]
    exact disjoint_negativeSubalgebra_cartanSubalgebra_sup_positiveSubalgebra R
  · rw [codisjoint_iff, borelSubalgebra_toSubmodule, ← sup_assoc]
    exact negativeSubalgebra_sup_cartanSubalgebra_sup_positiveSubalgebra_eq_top R

/-- Inside the Borel subalgebra, the Cartan and positive subalgebras are complementary. -/
theorem isCompl_cartanSubalgebra_positiveSubalgebra_ofLe :
    IsCompl
      ((cartanSubalgebra R).ofLe (cartanSubalgebra_le_borelSubalgebra R)).toSubmodule
      ((positiveSubalgebra R).ofLe (positiveSubalgebra_le_borelSubalgebra R)).toSubmodule :=
  LieSubalgebra.isCompl_ofLe (cartanSubalgebra_le_borelSubalgebra R)
    (positiveSubalgebra_le_borelSubalgebra R)
    (disjoint_positiveSubalgebra_cartanSubalgebra R).symm
    (borelSubalgebra_toSubmodule R).symm

end TauCeti.KacMoody
