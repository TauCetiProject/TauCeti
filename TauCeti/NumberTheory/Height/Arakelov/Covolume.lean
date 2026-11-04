/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Module.ZLattice.Covolume
public import TauCeti.Algebra.Module.ZLattice.RationalSubspace
public import TauCeti.NumberTheory.Height.Arakelov.Subspace.Basic

import TauCeti.NumberTheory.Height.Arakelov.Subspace.Covolume

/-!
# The covolume of the lattice of integral points of a rational subspace

For a subspace `V` of `ℚ^ι`, the covolume of the lattice `V ∩ ℤ^ι` in the real span of `V`
(`Submodule.intLattice`) is the absolute Euclidean height of `V`:
`covolume (V ∩ ℤ^ι) = subspaceHeight V`.
This is the identity through which theorems of the geometry of numbers about the lattice
`V ∩ ℤ^ι`, such as Minkowski's theorems, become statements about the height of `V`. It is the
case `K = ℚ` of Schmidt's identity between the covolume of the lattice `V ∩ 𝓞_K^ι` and the height
of a subspace `V` of `K^ι`, which over a general number field also involves the discriminant and
the complex places of `K`.

The lattice is the whole intersection `V ∩ ℤ^ι`, which is saturated in `ℤ^ι`. The covolume of a
sublattice of finite index is larger by the index, while the height of `V` does not change.

## Main results

* `Submodule.covolume_intLattice`: the covolume of `V.intLattice` is `V.subspaceHeight`.

## Implementation notes

`Submodule.covolume_intLattice` is obtained by specializing the general number-field Schmidt
covolume identity (`Submodule.covolume_integerLattice`) to `K = ℚ` via the measure-preserving
linear isometry `Submodule.euclideanSpanEquivRealSpan`
(`Submodule.covolume_intLattice_eq_covolume_integerLattice`), using `nrComplexPlaces ℚ = 0`,
`discr ℚ = 1`, and `[ℚ : ℚ] = 1`.

## References

* W. M. Schmidt, *On heights of algebraic subspaces and diophantine approximations*, Ann. of
  Math. **85** (1967), 430–472, §3, Theorem 1.
* E. Bombieri and J. Vaaler, *On Siegel's lemma*, Invent. Math. **73** (1983), 11–32.

The statement is adapted from Ralf Stephan's `ArithmeticHeights/RationalLattice.lean` in
[`rwst/Subspace-Theorems`](https://github.com/rwst/Subspace-Theorems/blob/9894a1c4baf805296b249e95575f0e16e8e1afa3/ArithmeticHeights/RationalLattice.lean),
commit `9894a1c4baf805296b249e95575f0e16e8e1afa3` (Apache 2.0).
-/

public section

noncomputable section

open Module NumberField NumberField.InfinitePlace

namespace Submodule

variable {ι : Type*}

/-- **The covolume of the lattice of integral points of a rational subspace is its absolute
Euclidean height.** For a subspace `V` of `ℚ^ι`, the lattice `V ∩ ℤ^ι` in the real span of `V`
has covolume `V.subspaceHeight`. -/
theorem covolume_intLattice [Fintype ι] [LinearOrder ι] (V : Submodule ℚ (ι → ℚ)) :
    ZLattice.covolume V.intLattice = V.subspaceHeight := by
  classical
  rw [V.covolume_intLattice_eq_covolume_integerLattice, V.covolume_integerLattice,
    IsTotallyReal.nrComplexPlaces_eq_zero, discr_rat, finrank_self]
  norm_num

/-- The line through `(1, 2)` in `ℚ²` cuts out a lattice of covolume `√5` in its real span. -/
example : ZLattice.covolume (ℚ ∙ ![(1 : ℚ), 2]).intLattice = √5 := by
  have h : ![(1 : ℚ), 2] = ((↑) : ℤ → ℚ) ∘ ![1, 2] := by
    ext i
    fin_cases i <;> simp
  rw [covolume_intLattice, subspaceHeight_span_singleton (by simp), h,
    TauCeti.height2_intCast_eq_sqrt_of_gcd_eq_one (by decide)]
  norm_num [Fin.sum_univ_two]

end Submodule

end
