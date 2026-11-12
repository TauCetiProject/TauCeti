/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Algebra.Lie.Graded.Supported
public import TauCeti.Algebra.Lie.Graded.Truncation
public import TauCeti.Algebra.PositiveDegrees.Ray.Basic
public import Mathlib.Algebra.Lie.Abelian

/-!
# Lie subalgebras on supported rays

The ray Lie algebra sums the homogeneous pieces on the actual allowed positive
multiples of a supported primitive vector. The vector itself need not be allowed.
Its elements are characterized by vanishing of all components off the ray.
The construction commutes with homogeneous images and degree truncations.

`IsAbelianRays` says that each such Lie algebra is abelian. It can be checked on
pairs of homogeneous elements, and is inherited by degree-preserving surjective
maps on homogeneous pieces. This is the condition that permits independent labels
on one primitive ray to be combined without choosing their order.

The construction specializes `TauCeti.supportedLieSubalgebra`; the abelian criterion
uses Mathlib's bilinear submodule images and `IsLieAbelian`.

Adapted from `Mei/Algebra/Lie/Graded/Ray.lean` in
[yuma-mizuno-lean/Mei](https://github.com/yuma-mizuno-lean/Mei), commit
`a79c57178cc83666fc244ca6e6eeaa722e9b8bc7` (Apache 2.0).
Original notice: Copyright (c) 2026 Mei contributors. All rights reserved.
Authors: Codex.
-/

public section

namespace TauCeti

variable {N R L L' : Type*} [AddCommGroup N] [CommRing R]
  [LieRing L] [LieAlgebra R L] [LieRing L'] [LieAlgebra R L']
  {d : PositiveDegrees N} (ℒ : N → Submodule R L) [SetLike.GradedBracket ℒ ℒ]

/-- The Lie subalgebra on the actual allowed positive multiples of a supported ray. -/
def rayLieSubalgebra (w : SupportedRay d) : LieSubalgebra R L :=
  supportedLieSubalgebra ℒ w.degreeSemigroup

/-- The underlying module is the sum of the pieces at actual ray degrees. -/
@[simp]
theorem rayLieSubalgebra_toSubmodule (w : SupportedRay d) :
    (rayLieSubalgebra ℒ w).toSubmodule = ⨆ n : w.rayDegrees, ℒ n := by
  rw [rayLieSubalgebra, supportedLieSubalgebra_toSubmodule]
  simp only [iSup_subtype, SupportedRay.mem_degreeSemigroup]

/-- Every homogeneous piece on the ray embeds in its Lie subalgebra. -/
theorem le_rayLieSubalgebra {w : SupportedRay d} {n : N} (hn : n ∈ w.rayDegrees) :
    ℒ n ≤ (rayLieSubalgebra ℒ w).toSubmodule :=
  le_supportedLieSubalgebra ℒ (by simpa using hn)

/-- The ray subalgebra is the smallest Lie subalgebra containing its pieces. -/
theorem rayLieSubalgebra_le_iff (w : SupportedRay d) (K : LieSubalgebra R L) :
    rayLieSubalgebra ℒ w ≤ K ↔ ∀ n ∈ w.rayDegrees, ℒ n ≤ K.toSubmodule := by
  simpa only [rayLieSubalgebra, SupportedRay.mem_degreeSemigroup] using
    supportedLieSubalgebra_le_iff ℒ w.degreeSemigroup K

/-- If only one homogeneous piece on a ray can be nonzero, that piece is the entire ray
Lie algebra. The distinguished degree need not be primitive. -/
theorem rayLieSubalgebra_toSubmodule_eq_of_single_degree (w : SupportedRay d) (n : N)
    (hn : n ∈ w.rayDegrees)
    (hvan : ∀ m ∈ w.rayDegrees, m ≠ n → ℒ m = ⊥) :
    (rayLieSubalgebra ℒ w).toSubmodule = ℒ n := by
  rw [rayLieSubalgebra_toSubmodule]
  apply le_antisymm
  · refine iSup_le fun m => ?_
    by_cases hm : (m : N) = n
    · simpa only [hm] using (le_refl (ℒ n))
    · rw [hvan m m.property hm]
      exact bot_le
  · exact le_iSup_of_le ⟨n, hn⟩ le_rfl

/-- Abelian rays require commutation within each supported ray, not between distinct rays. -/
class IsAbelianRays (d : PositiveDegrees N) (ℒ : N → Submodule R L)
    [SetLike.GradedBracket ℒ ℒ] : Prop where
  /-- Each supported ray Lie algebra is abelian. -/
  isLieAbelian : ∀ w : SupportedRay d, IsLieAbelian (rayLieSubalgebra ℒ w)

attribute [instance] IsAbelianRays.isLieAbelian

/-- Two elements of one ray Lie algebra have zero bracket when rays are abelian. -/
theorem lie_eq_zero_of_mem_rayLieSubalgebra [IsAbelianRays d ℒ]
    {w : SupportedRay d} {x y : L}
    (hx : x ∈ rayLieSubalgebra ℒ w) (hy : y ∈ rayLieSubalgebra ℒ w) : ⁅x, y⁆ = 0 :=
  congrArg Subtype.val (trivial_lie_zero (rayLieSubalgebra ℒ w)
    (rayLieSubalgebra ℒ w) ⟨x, hx⟩ ⟨y, hy⟩)

/-- Abelian rays can be checked on homogeneous pairs at actual allowed ray degrees. -/
theorem isAbelianRays_iff : IsAbelianRays d ℒ ↔
    ∀ (w : SupportedRay d) (n m : N), n ∈ w.rayDegrees → m ∈ w.rayDegrees →
      ∀ x ∈ ℒ n, ∀ y ∈ ℒ m, ⁅x, y⁆ = 0 := by
  constructor
  · intro h w n m hn hm x hx y hy
    exact lie_eq_zero_of_mem_rayLieSubalgebra ℒ
      (le_rayLieSubalgebra ℒ hn hx) (le_rayLieSubalgebra ℒ hm hy)
  · intro h
    refine ⟨fun w => ⟨fun x y => Subtype.ext ?_⟩⟩
    have hx : (x : L) ∈ ⨆ n : w.rayDegrees, ℒ n := by
      rw [← rayLieSubalgebra_toSubmodule]; exact x.property
    have hy : (y : L) ∈ ⨆ n : w.rayDegrees, ℒ n := by
      rw [← rayLieSubalgebra_toSubmodule]; exact y.property
    let : LieRing (Module.End R L) := LieRing.ofAssociativeRing
    suffices hle : Submodule.map₂ (LieModule.toEnd R L L).toLinearMap
        (⨆ n : w.rayDegrees, ℒ n) (⨆ n : w.rayDegrees, ℒ n) ≤ ⊥ from
      (Submodule.mem_bot R).mp (hle (Submodule.apply_mem_map₂ _ hx hy))
    simp_rw [Submodule.map₂_iSup_left, Submodule.map₂_iSup_right]
    exact iSup_le fun n => iSup_le fun m => Submodule.map₂_le.mpr
      (fun x hx y hy => (Submodule.mem_bot R).mpr (h w n m n.property m.property x hx y hy))

/-- Every grading of an abelian ambient Lie algebra has abelian rays. -/
instance [IsLieAbelian L] : IsAbelianRays d ℒ :=
  (isAbelianRays_iff ℒ).mpr fun _ _ _ _ _ _ _ _ _ => trivial_lie_zero L L _ _

variable (ℳ : N → Submodule R L') [SetLike.GradedBracket ℳ ℳ]

/-- Images of homogeneous pieces under a Lie map give the image ray algebra. -/
theorem map_rayLieSubalgebra (w : SupportedRay d) (f : L →ₗ⁅R⁆ L') :
    letI := f.gradedBracket_map ℒ
    (rayLieSubalgebra ℒ w).map f =
      rayLieSubalgebra (fun n => (ℒ n).map f.toLinearMap) w :=
  map_supportedLieSubalgebra ℒ w.degreeSemigroup f

/-- Surjectivity on homogeneous pieces preserves abelian rays, without injectivity. -/
theorem isAbelianRays_of_le_map [IsAbelianRays d ℒ]
    (f : L →ₗ⁅R⁆ L') (hf : ∀ n, ℳ n ≤ (ℒ n).map f.toLinearMap) :
    IsAbelianRays d ℳ := by
  apply (isAbelianRays_iff ℳ).mpr
  intro w n m hn hm x hx y hy
  obtain ⟨a, ha, rfl⟩ := Submodule.mem_map.mp (hf n hx)
  obtain ⟨b, hb, rfl⟩ := Submodule.mem_map.mp (hf m hy)
  exact (f.map_lie a b).symm.trans (by
    rw [(isAbelianRays_iff ℒ).mp ‹IsAbelianRays d ℒ› w n m hn hm a ha b hb, map_zero])

variable [DecidableEq N] [DirectSum.Decomposition ℒ]

/-- A ray element has zero homogeneous components away from its actual allowed degrees. -/
@[simp]
theorem mem_rayLieSubalgebra_iff (w : SupportedRay d) (x : L) :
    x ∈ rayLieSubalgebra ℒ w ↔
      ∀ n, n ∉ w.rayDegrees → (DirectSum.decompose ℒ x n : L) = 0 := by
  simpa only [rayLieSubalgebra, SupportedRay.mem_degreeSemigroup] using
    mem_supportedLieSubalgebra_iff ℒ w.degreeSemigroup x

/-- Ray Lie algebras are preserved by homogeneous projection. -/
theorem rayLieSubalgebra_isHomogeneous (w : SupportedRay d) :
    DirectSum.SetLike.IsHomogeneous ℒ (rayLieSubalgebra ℒ w) :=
  supportedLieSubalgebra_isHomogeneous ℒ w.degreeSemigroup

/-- Lie algebras on distinct supported rays have zero intersection. -/
theorem disjoint_rayLieSubalgebra [HasUniqueDiv N] {v w : SupportedRay d} (h : v ≠ w) :
    Disjoint (rayLieSubalgebra ℒ v) (rayLieSubalgebra ℒ w) := by
  classical
  rw [disjoint_iff]
  apply le_antisymm _ bot_le
  intro x hx
  rw [LieSubalgebra.mem_bot, ← DirectSum.sum_support_decompose ℒ x]
  apply Finset.sum_eq_zero
  intro n _
  by_cases hn : n ∈ v.rayDegrees
  · exact (mem_rayLieSubalgebra_iff ℒ w x).mp hx.2 n
      (fun hw => h (SupportedRay.eq_of_mem_rayDegrees hn hw))
  · exact (mem_rayLieSubalgebra_iff ℒ v x).mp hx.1 n hn

end TauCeti

namespace TauCeti.PositiveDegrees

variable {N : Type} {R L : Type*} [AddCommGroup N] [CommRing R]
  [LieRing L] [LieAlgebra R L] [DecidableEq N]
  (d : PositiveDegrees N) (ℒ : N → Submodule R L)
  [GradedLieAlgebra ℒ] [IsPositiveGrading d ℒ]

/-- Taking the finite degree quotient commutes with forming a ray Lie algebra. -/
@[simp]
theorem map_rayLieSubalgebra_mkQ (w : SupportedRay d) (k : ℕ) :
    (rayLieSubalgebra ℒ w).map (d.degreeIdeal ℒ k).mkQ =
      rayLieSubalgebra (d.truncatedGrading ℒ k) w := by
  apply LieSubalgebra.toSubmodule_injective
  refine (congrArg LieSubalgebra.toSubmodule
    (map_rayLieSubalgebra ℒ w (d.degreeIdeal ℒ k).mkQ)).trans ?_
  simp only [rayLieSubalgebra_toSubmodule]
  exact iSup_congr fun n => (d.truncatedGrading_eq ℒ k n).symm

/-- Degree truncation maps a ray Lie algebra onto its lower-order counterpart. -/
@[simp]
theorem map_rayLieSubalgebra_truncationMap (w : SupportedRay d)
    {k l : ℕ} (h : k ≤ l) :
    (rayLieSubalgebra (d.truncatedGrading ℒ l) w).map (d.truncationMap ℒ h) =
      rayLieSubalgebra (d.truncatedGrading ℒ k) w := by
  simpa only [d.map_truncationMap_truncatedGrading ℒ h] using
    map_rayLieSubalgebra (d.truncatedGrading ℒ l) w (d.truncationMap ℒ h)

/-- Finite degree quotients inherit abelian rays. -/
instance isAbelianRays_truncatedGrading [IsAbelianRays d ℒ] (k : ℕ) :
    IsAbelianRays d (d.truncatedGrading ℒ k) :=
  isAbelianRays_of_le_map ℒ (d.truncatedGrading ℒ k) (d.degreeIdeal ℒ k).mkQ
    (fun n => (d.truncatedGrading_eq ℒ k n).le)

end TauCeti.PositiveDegrees
