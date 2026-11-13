/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.RootSystem.SimplyConnectedRootDatum.F4.Basic
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

/-- The height of an integral pinned F₄ root in fundamental-weight coordinates. -/
@[simp] theorem height_f4SimplyConnectedBase (i : Fin 48) :
    f4SimplyConnectedBase.height i =
      11 * f4Root i 0 + 21 * f4Root i 1 + 15 * f4Root i 2 + 8 * f4Root i 3 := by
  let f : (Fin 4 → ℤ) →+ ℤ :=
    11 • Pi.evalAddMonoidHom (fun _ : Fin 4 => ℤ) 0 +
      21 • Pi.evalAddMonoidHom (fun _ : Fin 4 => ℤ) 1 +
      15 • Pi.evalAddMonoidHom (fun _ : Fin 4 => ℤ) 2 +
      8 • Pi.evalAddMonoidHom (fun _ : Fin 4 => ℤ) 3
  have hsimple : ∀ j ∈ f4SimplyConnectedBase.support,
      f (f4SimplyConnectedRootDatum.root j) = 1 := by
    intro j hj
    norm_num only [f, AddMonoidHom.add_apply, AddMonoidHom.nsmul_apply,
      Pi.evalAddMonoidHom_apply, f4SimplyConnectedRootDatum_root, nsmul_eq_mul]
    have hj' : j.val < 4 := mem_f4Support.mp (f4SimplyConnectedBase_support ▸ hj)
    obtain ⟨j, rfl⟩ : ∃ k : Fin 4, Fin.castAdd 44 k = j :=
      ⟨⟨j, hj'⟩, Fin.ext rfl⟩
    -- Check the height functional on the four pinned simple roots.
    exact (by decide +kernel : ∀ j : Fin 4,
      11 * f4Root (Fin.castAdd 44 j) 0 + 21 * f4Root (Fin.castAdd 44 j) 1 +
        15 * f4Root (Fin.castAdd 44 j) 2 + 8 * f4Root (Fin.castAdd 44 j) 3 = 1) j
  have h := TauCeti.apply_root_eq_height_zsmul f4SimplyConnectedRootDatum
    f4SimplyConnectedBase f hsimple i
  simpa [f, AddMonoidHom.add_apply, AddMonoidHom.nsmul_apply,
    f4SimplyConnectedRootDatum_root] using h.symm

/-- Positivity in the integral pinned F₄ base is the first half of the root table. -/
@[simp] theorem isPos_f4SimplyConnectedBase_iff (i : Fin 48) :
    f4SimplyConnectedBase.IsPos i ↔ i.val < 24 := by
  rw [RootPairing.Base.isPos_iff, height_f4SimplyConnectedBase]
  decide +revert

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

end TauCeti.DynkinType
