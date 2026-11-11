/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Algebra.Lie.Graded.Hom
public import TauCeti.Algebra.DirectSum.Supported
public import Mathlib.Algebra.Module.Submodule.Bilinear

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

variable {N R L L' : Type*} [AddCommMonoid N] [CommRing R]
  [LieRing L] [LieAlgebra R L] [LieRing L'] [LieAlgebra R L']
  (ℒ : N → Submodule R L) [SetLike.GradedBracket ℒ ℒ]

/-- The Lie subalgebra obtained by summing the pieces in an additive set of degrees.
The degree set need not contain zero. -/
def supportedLieSubalgebra (S : AddSubsemigroup N) : LieSubalgebra R L where
  toSubmodule := ⨆ n : S, ℒ n
  lie_mem' {x y} hx hy := by
    let : LieRing (Module.End R L) := LieRing.ofAssociativeRing
    suffices hle : Submodule.map₂ (LieModule.toEnd R L L).toLinearMap
        (⨆ n : S, ℒ n) (⨆ n : S, ℒ n) ≤ ⨆ n : S, ℒ n from
      hle (Submodule.apply_mem_map₂ _ hx hy)
    simp_rw [Submodule.map₂_iSup_left, Submodule.map₂_iSup_right]
    refine iSup_le fun n => iSup_le fun m => Submodule.map₂_le.mpr fun x hx y hy => ?_
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
  exact Submodule.map_iSup _ _

variable [DecidableEq N] [DirectSum.Decomposition ℒ]

/-- Membership is detected by the vanishing of the excluded homogeneous components. -/
@[simp]
theorem mem_supportedLieSubalgebra_iff (S : AddSubsemigroup N) (x : L) :
    x ∈ supportedLieSubalgebra ℒ S ↔
      ∀ n, n ∉ S → (DirectSum.decompose ℒ x n : L) = 0 := by
  rw [← LieSubalgebra.mem_toSubmodule, supportedLieSubalgebra_toSubmodule]
  exact TauCeti.DirectSum.mem_iSup_iff_decompose_eq_zero ℒ (S : Set N)

/-- Supported Lie subalgebras are stable under all homogeneous projections. -/
theorem supportedLieSubalgebra_isHomogeneous (S : AddSubsemigroup N) :
    DirectSum.SetLike.IsHomogeneous ℒ (supportedLieSubalgebra ℒ S) := by
  simpa only [DirectSum.SetLike.IsHomogeneous, ← LieSubalgebra.mem_toSubmodule,
    supportedLieSubalgebra_toSubmodule, iSup_subtype, SetLike.mem_coe] using
    TauCeti.DirectSum.iSup_isHomogeneous ℒ (S : Set N)

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

end TauCeti
