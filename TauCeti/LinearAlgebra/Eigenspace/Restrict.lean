/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Eigenspace.Basic

/-!
# Eigenvectors of restrictions to invariant submodules

Let `f` be an endomorphism preserving a submodule `L`. Eigen-data of `f` carried by vectors of `L`
pass to the restriction `f.restrict` of `f` to `L`.

## Main results

* `Module.End.hasEigenvalue_restrict`: an eigenvector of `f` in `L` makes its eigenvalue an
  eigenvalue of the restriction of `f` to `L`. Together with `Module.End.pow_restrict` this
  applies to powers of `f`.
* `Module.End.exists_restrict_apply_eq`: if `f v = a v - b w` and `f w = b v + a w` with `b ≠ 0`
  (over the reals: `v + iw` is an eigenvector of `f` for `a + bi`), and `v` lies in `L`, then so
  does `w`, and the restriction of `f` to `L` satisfies the same relations.
-/

public section

namespace Module.End

/-- An eigenvector of `f` in a submodule `L` preserved by `f` makes its eigenvalue an eigenvalue of
the restriction of `f` to `L`. -/
theorem hasEigenvalue_restrict {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    {f : End R M} {L : Submodule R M} (hL : ∀ v ∈ L, f v ∈ L) {μ : R} {v : M} (hvL : v ∈ L)
    (hv : f.HasEigenvector μ v) : HasEigenvalue (f.restrict hL) μ :=
  hasEigenvalue_of_hasEigenvector (x := ⟨v, hvL⟩)
    ⟨mem_eigenspace_iff.2 (Subtype.ext (by simpa using hv.apply_eq_smul)), by simpa using hv.2⟩

/-- If `f v = a v - b w` and `f w = b v + a w` with `b ≠ 0`, and `v` lies in a submodule `L`
preserved by `f`, then so does `w`, and the restriction of `f` to `L` satisfies the same
relations. -/
theorem exists_restrict_apply_eq {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    {f : End K V} {L : Submodule K V} (hL : ∀ v ∈ L, f v ∈ L) {a b : K} (hb : b ≠ 0) {v w : V}
    (hvL : v ∈ L) (hv0 : v ≠ 0) (hfv : f v = a • v - b • w) (hfw : f w = b • v + a • w) :
    ∃ v' w' : L, v' ≠ 0 ∧ f.restrict hL v' = a • v' - b • w' ∧
      f.restrict hL w' = b • v' + a • w' := by
  have hwL : w ∈ L := by
    have hw : w = b⁻¹ • (a • v - f v) := by
      rw [hfv, sub_sub_cancel, smul_smul, inv_mul_cancel₀ hb, one_smul]
    rw [hw]
    exact L.smul_mem _ (L.sub_mem (L.smul_mem _ hvL) (hL v hvL))
  exact ⟨⟨v, hvL⟩, ⟨w, hwL⟩, by simpa using hv0, Subtype.ext (by simpa using hfv),
    Subtype.ext (by simpa using hfw)⟩

end Module.End
