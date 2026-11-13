/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.RootSystem.SimplyConnectedRootDatum.Rational
public import TauCeti.LinearAlgebra.RootSystem.Positive

/-!
# Heights and positive roots in type F₄

The first twenty-four entries of the pinned F₄ root table are exactly its positive roots.
The height functional in fundamental-weight coordinates is `(11, 21, 15, 8)`; it takes value
one on each Bourbaki simple root. These formulas allow finite root-table calculations to use
the existing positive system, rather than introducing another choice of positive roots.

## References

* N. Bourbaki, *Lie Groups and Lie Algebras, Chapters 4--6*, Plate VIII.
-/

public section

namespace TauCeti.DynkinType

/-- The height of a pinned F₄ root in fundamental-weight coordinates. -/
-- Simplify before the dependent root-index type is normalized to Fin 48.
@[simp↓] theorem height_rationalBase_F4 (ht : F4.Valid) (i : Fin F4.numRoots) :
    (F4.rationalBase ht).height i =
      11 * f4Root i 0 + 21 * f4Root i 1 + 15 * f4Root i 2 + 8 * f4Root i 3 := by
  let f : (Fin F4.rank → ℚ) →+ ℚ :=
    11 • Pi.evalAddMonoidHom (fun _ : Fin F4.rank => ℚ) ⟨0, by decide⟩ +
      21 • Pi.evalAddMonoidHom (fun _ : Fin F4.rank => ℚ) ⟨1, by decide⟩ +
      15 • Pi.evalAddMonoidHom (fun _ : Fin F4.rank => ℚ) ⟨2, by decide⟩ +
      8 • Pi.evalAddMonoidHom (fun _ : Fin F4.rank => ℚ) ⟨3, by decide⟩
  have hsimple : ∀ j ∈ (F4.rationalBase ht).support,
      f ((F4.rationalRootSystem ht).root j) = 1 := by
    intro j hj
    norm_num only [f, AddMonoidHom.add_apply, AddMonoidHom.nsmul_apply,
      Pi.evalAddMonoidHom_apply, root_rationalRootSystem, simplyConnectedRootDatum_F4,
      f4SimplyConnectedRootDatum_root, nsmul_eq_mul]
    have hj' : j.val < 4 := (F4.mem_support_rationalBase ht).mp hj
    obtain ⟨j, rfl⟩ : ∃ k : Fin 4, Fin.castAdd 44 k = j :=
      ⟨⟨j, hj'⟩, Fin.ext rfl⟩
    exact (by decide +kernel : ∀ j : Fin 4,
      11 * (f4Root (Fin.castAdd 44 j) 0 : ℚ) +
        21 * (f4Root (Fin.castAdd 44 j) 1 : ℚ) +
        15 * (f4Root (Fin.castAdd 44 j) 2 : ℚ) +
        8 * (f4Root (Fin.castAdd 44 j) 3 : ℚ) = 1) j
  have h := TauCeti.apply_root_eq_height_zsmul (F4.rationalRootSystem ht)
    (F4.rationalBase ht) f hsimple i
  norm_num [f, AddMonoidHom.add_apply, AddMonoidHom.nsmul_apply,
    root_rationalRootSystem, simplyConnectedRootDatum_F4, f4SimplyConnectedRootDatum_root] at h
  rw [height_rationalBase]
  exact_mod_cast h.symm

/-- The height of an integral pinned F₄ root in fundamental-weight coordinates. -/
@[simp] theorem height_f4SimplyConnectedBase (i : Fin 48) :
    f4SimplyConnectedBase.height i =
      11 * f4Root i 0 + 21 * f4Root i 1 + 15 * f4Root i 2 + 8 * f4Root i 3 := by
  have h := height_rationalBase_F4 (by decide) i
  rw [height_rationalBase F4 (by decide) i] at h
  -- Transport the assembled base along the datum equation, without unfolding either base.
  have hb := heq_of_eqRec_eq _ (simplyConnectedBase_F4 (by decide))
  have hP := simplyConnectedRootDatum_F4 (by decide)
  have hh : (F4.simplyConnectedBase (by decide)).height i = f4SimplyConnectedBase.height i :=
    congr_heq (by congr 1) (HEq.refl i)
  exact hh.symm.trans h

/-- The uniform integral F₄ base has the pinned table's height formula. -/
-- Rewrite before simplification normalizes the dependent root-index type to Fin 48.
@[simp↓] theorem height_simplyConnectedBase_F4 (ht : F4.Valid) (i : Fin F4.numRoots) :
    (F4.simplyConnectedBase ht).height i =
      11 * f4Root i 0 + 21 * f4Root i 1 + 15 * f4Root i 2 + 8 * f4Root i 3 := by
  rw [← height_rationalBase F4 ht]
  exact height_rationalBase_F4 ht i

/-- Positivity in the integral pinned F₄ base is the first half of the root table. -/
@[simp] theorem isPos_f4SimplyConnectedBase_iff (i : Fin 48) :
    f4SimplyConnectedBase.IsPos i ↔ i.val < 24 := by
  rw [RootPairing.Base.isPos_iff, height_f4SimplyConnectedBase]
  decide +revert

/-- The uniform integral F₄ base has the pinned table's positive indices. -/
@[simp↓] theorem isPos_simplyConnectedBase_F4_iff (ht : F4.Valid) (i : Fin F4.numRoots) :
    (F4.simplyConnectedBase ht).IsPos i ↔ i.val < 24 := by
  rw [RootPairing.Base.isPos_iff, height_simplyConnectedBase_F4]
  decide +revert

/-- Rational base change preserves the pinned F₄ positive indices. -/
@[simp↓] theorem isPos_rationalBase_F4_iff (ht : F4.Valid) (i : Fin F4.numRoots) :
    (F4.rationalBase ht).IsPos i ↔ i.val < 24 := by
  rw [RootPairing.Base.isPos_iff, height_rationalBase, ← RootPairing.Base.isPos_iff]
  exact isPos_simplyConnectedBase_F4_iff ht i

/-- The positive integral F₄ roots are exactly the first half of the pinned root table. -/
theorem mem_posRoots_f4_iff (i : Fin 48) :
    i ∈ TauCeti.posRoots f4SimplyConnectedRootDatum f4SimplyConnectedBase ↔ i.val < 24 := by
  simp only [TauCeti.mem_posRoots, isPos_f4SimplyConnectedBase_iff]

/-- The positive integral F₄ root finset consists of the first twenty-four table indices. -/
theorem posRootsFinset_f4 :
    posRootsFinset f4SimplyConnectedRootDatum f4SimplyConnectedBase =
      Finset.univ.filter (fun i => i.val < 24) := by
  ext i
  simp only [mem_posRootsFinset, mem_posRoots_f4_iff, Finset.mem_filter,
    Finset.mem_univ, true_and]

/-- The positive F₄ roots are exactly the first half of the pinned root table. -/
-- The generic membership lemma does not match after dependent-index normalization.
@[simp↓] theorem mem_posRoots_F4_iff (ht : F4.Valid) (i : Fin F4.numRoots) :
    i ∈ TauCeti.posRoots (F4.rationalRootSystem ht) (F4.rationalBase ht) ↔ i.val < 24 := by
  simp only [TauCeti.mem_posRoots, RootPairing.Base.isPos_iff]
  rw [height_rationalBase_F4]
  decide +revert

/-- The negative F₄ roots are exactly the second half of the pinned root table. -/
@[simp↓] theorem mem_negRoots_F4_iff (ht : F4.Valid) (i : Fin F4.numRoots) :
    i ∈ TauCeti.negRoots (F4.rationalRootSystem ht) (F4.rationalBase ht) ↔ 24 ≤ i.val := by
  rw [TauCeti.mem_negRoots, isPos_rationalBase_F4_iff, not_lt]

/-- The positive F₄ root finset consists of the first twenty-four table indices. -/
theorem posRootsFinset_F4 (ht : F4.Valid) :
    posRootsFinset (F4.rationalRootSystem ht) (F4.rationalBase ht) =
      Finset.univ.filter (fun i => i.val < 24) := by
  ext i
  simp only [mem_posRootsFinset, mem_posRoots_F4_iff, Finset.mem_filter,
    Finset.mem_univ, true_and]

end TauCeti.DynkinType
