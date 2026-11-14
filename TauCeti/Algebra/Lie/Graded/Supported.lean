/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Algebra.Lie.Graded.Hom
public import TauCeti.Algebra.DirectSum.Supported
public import TauCeti.Algebra.Lie.Basic

/-!
# Lie subalgebras supported on additive sets of degrees

Summing the homogeneous pieces over an additive subsemigroup of degrees gives a
Lie subalgebra. For an internal grading, its elements are exactly those whose
components outside the chosen degrees vanish. In particular it is homogeneous,
allowing restriction of the grading to this subalgebra.

The construction uses Mathlib's submodule suprema, graded bracket and homogeneous
projections. It commutes with images of the homogeneous pieces under Lie maps;
this applies in particular to degree truncations.

Adapted from `Mei/Algebra/Lie/Graded/Supported.lean` in
[yuma-mizuno-lean/Mei](https://github.com/yuma-mizuno-lean/Mei), commit
`a79c57178cc83666fc244ca6e6eeaa722e9b8bc7` (Apache 2.0).
Original notice: Copyright (c) 2026 Mei contributors. All rights reserved.
Authors: Codex.
-/

public section

namespace TauCeti

variable {N R L L' : Type*} [Add N] [CommRing R]
  [LieRing L] [LieAlgebra R L] [LieRing L'] [LieAlgebra R L']
  (ℒ : N → Submodule R L) [SetLike.GradedBracket ℒ ℒ]

/-- The Lie subalgebra obtained by summing the pieces in an additive set of degrees.
The degree set need not contain zero. -/
def supportedLieSubalgebra (S : AddSubsemigroup N) : LieSubalgebra R L where
  toSubmodule := ⨆ n : S, ℒ n
  lie_mem' {x y} hx hy := by
    refine lie_mem_of_mem_iSup _ _ _ (fun n m x hx y hy => ?_) hx hy
    exact (le_iSup (fun n : S => ℒ n) ⟨n + m, S.add_mem n.property m.property⟩)
      (SetLike.GradedBracket.bracket_mem hx hy)

/-- The underlying submodule is the sum of the selected homogeneous pieces. -/
@[simp]
theorem supportedLieSubalgebra_toSubmodule (S : AddSubsemigroup N) :
    (supportedLieSubalgebra ℒ S).toSubmodule = ⨆ n : S, ℒ n := (rfl)

/-- Every selected homogeneous piece belongs to the supported Lie subalgebra. -/
theorem le_supportedLieSubalgebra {S : AddSubsemigroup N} {n : N} (hn : n ∈ S) :
    ℒ n ≤ (supportedLieSubalgebra ℒ S).toSubmodule :=
  le_iSup (fun n : S => ℒ n) ⟨n, hn⟩

/-- The supported subalgebra is the smallest Lie subalgebra containing its pieces. -/
theorem supportedLieSubalgebra_le_iff (S : AddSubsemigroup N) (K : LieSubalgebra R L) :
    supportedLieSubalgebra ℒ S ≤ K ↔ ∀ n ∈ S, ℒ n ≤ K.toSubmodule := by
  constructor
  · intro h n hn x hx
    exact h (le_supportedLieSubalgebra ℒ hn hx)
  · intro h
    exact iSup_le fun n : S => h n n.property

/-- Enlarging the selected degrees enlarges their Lie subalgebra. -/
theorem supportedLieSubalgebra_mono {S T : AddSubsemigroup N} (h : S ≤ T) :
    supportedLieSubalgebra ℒ S ≤ supportedLieSubalgebra ℒ T :=
  (supportedLieSubalgebra_le_iff ℒ S _).mpr fun _ hn => le_supportedLieSubalgebra ℒ (h hn)

/-- Images of supported subalgebras are the subalgebras of the image pieces. -/
theorem map_supportedLieSubalgebra (S : AddSubsemigroup N) (f : L →ₗ⁅R⁆ L') :
    letI := f.gradedBracket_map ℒ
    (supportedLieSubalgebra ℒ S).map f =
      supportedLieSubalgebra (fun n => (ℒ n).map f.toLinearMap) S := by
  let := f.gradedBracket_map ℒ
  apply LieSubalgebra.toSubmodule_injective
  rw [LieSubalgebra.map_toSubmodule, supportedLieSubalgebra_toSubmodule,
    supportedLieSubalgebra_toSubmodule, Submodule.map_iSup]

/-- Selecting no degrees gives the zero Lie subalgebra. -/
@[simp]
theorem supportedLieSubalgebra_bot : supportedLieSubalgebra ℒ ⊥ = ⊥ := by
  apply le_antisymm _ bot_le
  exact (supportedLieSubalgebra_le_iff ℒ ⊥ ⊥).mpr fun n hn =>
    (AddSubsemigroup.notMem_bot hn).elim

/-- If all other selected pieces vanish, the supported subalgebra is a single piece. -/
theorem supportedLieSubalgebra_toSubmodule_eq_of_forall_ne_eq_bot
    (S : AddSubsemigroup N) (n : N) (hn : n ∈ S)
    (hvan : ∀ m ∈ S, m ≠ n → ℒ m = ⊥) :
    (supportedLieSubalgebra ℒ S).toSubmodule = ℒ n := by
  rw [supportedLieSubalgebra_toSubmodule]
  apply le_antisymm
  · refine iSup_le fun m => ?_
    by_cases hm : (m : N) = n
    · simpa only [hm] using (le_refl (ℒ n))
    · rw [hvan m m.property hm]
      exact bot_le
  · exact le_iSup_of_le ⟨n, hn⟩ le_rfl

/-- A supported Lie subalgebra is abelian exactly when its homogeneous pieces commute. -/
theorem isLieAbelian_supportedLieSubalgebra_iff (S : AddSubsemigroup N) :
    IsLieAbelian (supportedLieSubalgebra ℒ S) ↔
      ∀ n ∈ S, ∀ m ∈ S, ∀ x ∈ ℒ n, ∀ y ∈ ℒ m, ⁅x, y⁆ = 0 := by
  constructor
  · intro h n hn m hm x hx y hy
    exact LieSubalgebra.lie_eq_zero_of_mem
      (le_supportedLieSubalgebra ℒ hn hx) (le_supportedLieSubalgebra ℒ hm hy)
  · intro h
    refine ⟨fun x y => Subtype.ext ?_⟩
    exact lie_eq_zero_of_mem_iSup (fun n : S => ℒ n) (fun n : S => ℒ n)
      (fun n m => h n n.property m m.property) x.property y.property

variable [DecidableEq N] [DirectSum.Decomposition ℒ]

/-- Membership is detected by the vanishing of the excluded homogeneous components. -/
theorem mem_supportedLieSubalgebra_iff (S : AddSubsemigroup N) (x : L) :
    x ∈ supportedLieSubalgebra ℒ S ↔
      ∀ n, n ∉ S → (DirectSum.decompose ℒ x n : L) = 0 := by
  rw [← LieSubalgebra.mem_toSubmodule, supportedLieSubalgebra_toSubmodule]
  exact TauCeti.DirectSum.mem_iSup_iff_decompose_eq_zero ℒ (S : Set N)

/-- Supported Lie subalgebras are stable under all homogeneous projections. -/
theorem isHomogeneous_supportedLieSubalgebra (S : AddSubsemigroup N) :
    DirectSum.SetLike.IsHomogeneous ℒ (supportedLieSubalgebra ℒ S) := by
  simpa only [DirectSum.SetLike.IsHomogeneous, ← LieSubalgebra.mem_toSubmodule,
    supportedLieSubalgebra_toSubmodule, iSup_subtype, SetLike.mem_coe] using
    TauCeti.DirectSum.isHomogeneous_iSup ℒ (S : Set N)

/-- Selecting every degree recovers the entire Lie algebra. -/
@[simp]
theorem supportedLieSubalgebra_top : supportedLieSubalgebra ℒ ⊤ = ⊤ := by
  ext x
  simp [mem_supportedLieSubalgebra_iff]

/-- Intersecting degree sets intersects their supported Lie subalgebras. -/
@[simp]
theorem supportedLieSubalgebra_inf (S T : AddSubsemigroup N) :
    supportedLieSubalgebra ℒ (S ⊓ T) =
      supportedLieSubalgebra ℒ S ⊓ supportedLieSubalgebra ℒ T := by
  ext x
  simp only [LieSubalgebra.mem_inf, mem_supportedLieSubalgebra_iff,
    AddSubsemigroup.mem_inf]
  grind

/-- Disjoint degree sets have disjoint supported Lie subalgebras. -/
theorem disjoint_supportedLieSubalgebra {S T : AddSubsemigroup N} (h : Disjoint S T) :
    Disjoint (supportedLieSubalgebra ℒ S) (supportedLieSubalgebra ℒ T) := by
  rw [disjoint_iff, ← supportedLieSubalgebra_inf, disjoint_iff.mp h,
    supportedLieSubalgebra_bot]

end TauCeti
