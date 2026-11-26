/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.Sl2.EigenspaceMap
public import TauCeti.Algebra.Lie.Sl2.TripleOrZero.Basic
public import TauCeti.LinearAlgebra.Eigenspace.ZeroEndomorphism

/-!
# The raising and lowering operators of a zero-inclusive triple between eigenspaces

Let `t : TauCeti.IsSl2TripleOrZero h e f` be a zero-inclusive `sl₂` triple in a Lie algebra `L`
over a field `K` of characteristic zero, and let `M` be a finite-dimensional `L`-module, with
`M_μ` the `μ`-eigenspace of `h`. For an `sl₂` triple, `TauCeti/Algebra/Lie/Sl2/EigenspaceMap.lean`
shows that `e` maps `M_μ` onto `M_(μ + 2)` unless `μ + 2 = -n` with `n : ℕ`, and injectively
unless `μ = n`; dually for `f`. This file extends these statements, and the uniqueness of the third
element of a triple given the other two, to zero-inclusive triples. For the zero triple they hold
because `h = e = f = 0`: then `M = M_0`, every other eigenspace vanishes, and `e` and `f` act by
zero.

Specialised to integer weights `j`, `e` maps `M_j` onto `M_(j + 2)` for `j ≥ -1` and injectively
for `j ≤ -1`, dually `f` maps `M_j` onto `M_(j - 2)` for `j ≤ 1` and injectively for `j ≥ 1`,
and in the adjoint grading `⁅e, L(0)⁆ = L(2)`. These are the statements about the
grading of a triple used in comparing two triples with the same neutral element: the lowering
element is determined by the other two, and the raising element is reached from any other choice
by the centraliser of `h`, whose orbit map at `e` has differential `x ↦ ⁅x, e⁆` from `L(0)` onto
`L(2)`.

## Main results

* `TauCeti.IsSl2TripleOrZero.disjoint_ker_toEnd_e_eigenspace` and
  `TauCeti.IsSl2TripleOrZero.disjoint_ker_toEnd_f_eigenspace`: injectivity of `e` and `f` on the
  eigenspaces of `h`.
* `TauCeti.IsSl2TripleOrZero.f_eq_of_isSl2TripleOrZero` and
  `TauCeti.IsSl2TripleOrZero.e_eq_of_isSl2TripleOrZero`: two elements of a zero-inclusive triple,
  one of them the neutral element, determine the third.
* `TauCeti.IsSl2TripleOrZero.map_toEnd_e_eigenspace` and
  `TauCeti.IsSl2TripleOrZero.map_toEnd_f_eigenspace`: surjectivity of `e` and `f` between
  eigenspaces.
* `TauCeti.IsSl2TripleOrZero.map_toEnd_e_eigenspace_intCast` and
  `TauCeti.IsSl2TripleOrZero.disjoint_ker_toEnd_e_eigenspace_intCast`: at integer weights, `e`
  maps `M_j` onto `M_(j + 2)` for `j ≥ -1`, and injectively for `j ≤ -1`.
* `TauCeti.IsSl2TripleOrZero.map_toEnd_f_eigenspace_intCast` and
  `TauCeti.IsSl2TripleOrZero.disjoint_ker_toEnd_f_eigenspace_intCast`: dually, `f` maps `M_j`
  onto `M_(j - 2)` for `j ≤ 1`, and injectively for `j ≥ 1`.
* `TauCeti.IsSl2TripleOrZero.map_ad_e_eigenspace_zero`: `⁅e, L(0)⁆ = L(2)` in the adjoint
  grading.

## References

* D. Ciubotaru and M. Harris, *On the generalized Ramanujan and Arthur conjectures over function
  fields*, arXiv:2311.15300, §2.1, for the zero-inclusive convention.
* W. A. de Graaf, *Computing with nilpotent orbits in simple Lie algebras of exceptional type*,
  LMS J. Comput. Math. 11 (2008), §3, Lemmas 2–3.
-/

public section

open LieModule LieAlgebra Module

namespace TauCeti

namespace IsSl2TripleOrZero

/-! ### Injectivity -/

section Domain

variable {K L M : Type*} [CommRing K] [IsDomain K] [CharZero K] [LieRing L] [LieAlgebra K L]
  [AddCommGroup M] [Module K M] [LieRingModule L M] [LieModule K L M]
  [IsNoetherian K M] [IsTorsionFree K M] {h e f : L} {μ : K}

/-- **The raising operator is injective on the eigenspaces at weights outside `ℕ`.** For the zero
triple these eigenspaces vanish. -/
theorem disjoint_ker_toEnd_e_eigenspace (t : IsSl2TripleOrZero h e f) (hμ : ∀ n : ℕ, μ ≠ n) :
    Disjoint (LinearMap.ker (toEnd K L M e)) ((toEnd K L M h).eigenspace μ) := by
  rcases eq_or_ne h 0 with rfl | hh
  · rw [map_zero, End.zero_eigenspace_eq_bot (by simpa using hμ 0)]
    exact disjoint_bot_right
  · exact (t.isSl2Triple hh).disjoint_ker_toEnd_e_eigenspace hμ

/-- **The lowering operator is injective on the eigenspaces at weights outside `-ℕ`.** For the
zero triple these eigenspaces vanish. -/
theorem disjoint_ker_toEnd_f_eigenspace (t : IsSl2TripleOrZero h e f) (hμ : ∀ n : ℕ, μ ≠ -n) :
    Disjoint (LinearMap.ker (toEnd K L M f)) ((toEnd K L M h).eigenspace μ) := by
  rcases eq_or_ne h 0 with rfl | hh
  · rw [map_zero, End.zero_eigenspace_eq_bot (by simpa using hμ 0)]
    exact disjoint_bot_right
  · exact (t.isSl2Triple hh).disjoint_ker_toEnd_f_eigenspace hμ

/-- **Injectivity of the raising operator at negative integer weights.** For `j ≤ -1`, `e` is
injective on the eigenspace of `h` at `j`. -/
theorem disjoint_ker_toEnd_e_eigenspace_intCast (t : IsSl2TripleOrZero h e f) {j : ℤ}
    (hj : j ≤ -1) : Disjoint (LinearMap.ker (toEnd K L M e)) ((toEnd K L M h).eigenspace (j : K)) :=
  t.disjoint_ker_toEnd_e_eigenspace fun n hn ↦ by
    have : j = n := by exact_mod_cast hn
    omega

/-- **Injectivity of the lowering operator at positive integer weights.** For `1 ≤ j`, `f` is
injective on the eigenspace of `h` at `j`. -/
theorem disjoint_ker_toEnd_f_eigenspace_intCast (t : IsSl2TripleOrZero h e f) {j : ℤ}
    (hj : 1 ≤ j) : Disjoint (LinearMap.ker (toEnd K L M f)) ((toEnd K L M h).eigenspace (j : K)) :=
  t.disjoint_ker_toEnd_f_eigenspace fun n hn ↦ by
    rw [← Int.cast_natCast, ← Int.cast_neg, Int.cast_inj] at hn
    omega

end Domain

section Uniqueness

variable (K : Type*) [CommRing K] [IsDomain K] [CharZero K] {L : Type*} [LieRing L]
  [LieAlgebra K L] [IsNoetherian K L] [IsTorsionFree K L]

include K in
/-- **The neutral and raising elements of a zero-inclusive triple determine the lowering
element.** In a Noetherian torsion-free Lie algebra over a domain `K` of characteristic zero, any
two zero-inclusive triples `(h, e, f)` and `(h, e, f')` satisfy `f = f'`. -/
theorem f_eq_of_isSl2TripleOrZero {h e f f' : L} (t : IsSl2TripleOrZero h e f)
    (t' : IsSl2TripleOrZero h e f') : f = f' := by
  have := HasUniqueDiv.of_isTorsionFree K L
  rcases eq_or_ne h 0 with rfl | hh
  · rw [t.f_eq_zero_iff.mpr rfl, t'.f_eq_zero_iff.mpr rfl]
  · exact (t.isSl2Triple hh).f_eq_of_isSl2Triple K (t'.isSl2Triple hh)

include K in
/-- **The neutral and lowering elements of a zero-inclusive triple determine the raising
element.** In a Noetherian torsion-free Lie algebra over a domain `K` of characteristic zero, any
two zero-inclusive triples `(h, e, f)` and `(h, e', f)` satisfy `e = e'`. -/
theorem e_eq_of_isSl2TripleOrZero {h e e' f : L} (t : IsSl2TripleOrZero h e f)
    (t' : IsSl2TripleOrZero h e' f) : e = e' :=
  f_eq_of_isSl2TripleOrZero K t.symm t'.symm

end Uniqueness

/-! ### Surjectivity -/

section Field

variable {K L M : Type*} [Field K] [CharZero K] [LieRing L] [LieAlgebra K L]
  [AddCommGroup M] [Module K M] [LieRingModule L M] [LieModule K L M] [FiniteDimensional K M]
  {h e f : L} {μ : K}

/-- **The raising operator maps `M_μ` onto `M_(μ + 2)`** unless `μ + 2` is of the form `-n` with
`n : ℕ`. For the zero triple both sides vanish, as `μ + 2 ≠ 0` and `e = 0`. -/
theorem map_toEnd_e_eigenspace (t : IsSl2TripleOrZero h e f) (hμ : ∀ n : ℕ, μ + 2 ≠ -n) :
    ((toEnd K L M h).eigenspace μ).map (toEnd K L M e) = (toEnd K L M h).eigenspace (μ + 2) := by
  have := HasUniqueDiv.of_isTorsionFree K L
  rcases eq_or_ne h 0 with rfl | hh
  · rw [map_zero, End.zero_eigenspace_eq_bot (μ := μ + 2) (by simpa using hμ 0),
      t.e_eq_zero_iff.mpr rfl, map_zero, Submodule.map_zero]
  · exact (t.isSl2Triple hh).map_toEnd_e_eigenspace hμ

/-- **The lowering operator maps `M_μ` onto `M_(μ - 2)`** unless `μ - 2` is a natural number. For
the zero triple both sides vanish, as `μ - 2 ≠ 0` and `f = 0`. -/
theorem map_toEnd_f_eigenspace (t : IsSl2TripleOrZero h e f) (hμ : ∀ n : ℕ, μ - 2 ≠ n) :
    ((toEnd K L M h).eigenspace μ).map (toEnd K L M f) = (toEnd K L M h).eigenspace (μ - 2) := by
  have := HasUniqueDiv.of_isTorsionFree K L
  rcases eq_or_ne h 0 with rfl | hh
  · rw [map_zero, End.zero_eigenspace_eq_bot (μ := μ - 2) (by simpa using hμ 0),
      t.f_eq_zero_iff.mpr rfl, map_zero, Submodule.map_zero]
  · exact (t.isSl2Triple hh).map_toEnd_f_eigenspace hμ

/-- **Surjectivity of the raising operator at integer weights `j ≥ -1`.** For `j ≥ -1`, `e` maps
the eigenspace of `h` at `j` onto the eigenspace at `j + 2`. -/
theorem map_toEnd_e_eigenspace_intCast (t : IsSl2TripleOrZero h e f) {j : ℤ} (hj : -1 ≤ j) :
    ((toEnd K L M h).eigenspace (j : K)).map (toEnd K L M e) =
      (toEnd K L M h).eigenspace ((j + 2 : ℤ) : K) := by
  rw [Int.cast_add, Int.cast_ofNat]
  refine t.map_toEnd_e_eigenspace fun n hn ↦ ?_
  have : j + 2 = -n := by exact_mod_cast hn
  omega

/-- **Surjectivity of the lowering operator at integer weights `j ≤ 1`.** For `j ≤ 1`, `f` maps
the eigenspace of `h` at `j` onto the eigenspace at `j - 2`. -/
theorem map_toEnd_f_eigenspace_intCast (t : IsSl2TripleOrZero h e f) {j : ℤ} (hj : j ≤ 1) :
    ((toEnd K L M h).eigenspace (j : K)).map (toEnd K L M f) =
      (toEnd K L M h).eigenspace ((j - 2 : ℤ) : K) := by
  rw [Int.cast_sub, Int.cast_ofNat]
  refine t.map_toEnd_f_eigenspace fun n hn ↦ ?_
  have : j - 2 = n := by exact_mod_cast hn
  omega

variable [FiniteDimensional K L]

/-- **`⁅e, L(0)⁆ = L(2)`.** For a zero-inclusive triple `(h, e, f)` in a finite-dimensional Lie
algebra over a field of characteristic zero, `ad e` maps the `0`-eigenspace of `ad h` onto its
`2`-eigenspace. For the zero triple both sides vanish. -/
theorem map_ad_e_eigenspace_zero (t : IsSl2TripleOrZero h e f) :
    ((ad K L h).eigenspace 0).map (ad K L e) = (ad K L h).eigenspace 2 := by
  rw [ad_eq_toEnd]
  simpa using t.map_toEnd_e_eigenspace_intCast (K := K) (M := L) (j := 0) (by norm_num)

end Field

end IsSl2TripleOrZero

end TauCeti
