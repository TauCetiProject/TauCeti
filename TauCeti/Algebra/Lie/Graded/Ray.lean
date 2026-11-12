/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Algebra.Lie.Graded.Supported
public import TauCeti.Algebra.Lie.Graded.Truncation
public import TauCeti.Algebra.PositiveDegrees.Ray.Basic

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
theorem rayLieSubalgebra_toSubmodule_eq_of_forall_ne_eq_bot (w : SupportedRay d) (n : N)
    (hn : n ∈ w.rayDegrees)
    (hvan : ∀ m ∈ w.rayDegrees, m ≠ n → ℒ m = ⊥) :
    (rayLieSubalgebra ℒ w).toSubmodule = ℒ n := by
  simpa only [rayLieSubalgebra, SupportedRay.mem_degreeSemigroup] using
    supportedLieSubalgebra_toSubmodule_eq_of_forall_ne_eq_bot ℒ w.degreeSemigroup n
      ((SupportedRay.mem_degreeSemigroup w n).mpr hn)
      (fun m hm => hvan m ((SupportedRay.mem_degreeSemigroup w m).mp hm))

/-- Abelian rays require commutation within each supported ray, not between distinct rays. -/
class IsAbelianRays (d : PositiveDegrees N) (ℒ : N → Submodule R L)
    [SetLike.GradedBracket ℒ ℒ] : Prop where
  /-- Each supported ray Lie algebra is abelian. -/
  isLieAbelian : ∀ w : SupportedRay d, IsLieAbelian (rayLieSubalgebra ℒ w)

attribute [instance] IsAbelianRays.isLieAbelian

/-- A single ray algebra is abelian exactly when its homogeneous pieces commute. -/
theorem isLieAbelian_rayLieSubalgebra_iff (w : SupportedRay d) :
    IsLieAbelian (rayLieSubalgebra ℒ w) ↔
      ∀ n ∈ w.rayDegrees, ∀ m ∈ w.rayDegrees, ∀ x ∈ ℒ n, ∀ y ∈ ℒ m, ⁅x, y⁆ = 0 := by
  unfold rayLieSubalgebra
  simpa only [SupportedRay.mem_degreeSemigroup] using
    isLieAbelian_supportedLieSubalgebra_iff ℒ w.degreeSemigroup

/-- Abelian rays can be checked on homogeneous pairs at actual allowed ray degrees. -/
theorem isAbelianRays_iff : IsAbelianRays d ℒ ↔
    ∀ (w : SupportedRay d) (n m : N), n ∈ w.rayDegrees → m ∈ w.rayDegrees →
      ∀ x ∈ ℒ n, ∀ y ∈ ℒ m, ⁅x, y⁆ = 0 := by
  constructor
  · intro h w n m hn hm
    exact (isLieAbelian_rayLieSubalgebra_iff ℒ w).mp (h.isLieAbelian w) n hn m hm
  · intro h
    exact ⟨fun w => (isLieAbelian_rayLieSubalgebra_iff ℒ w).mpr
      (fun n hn m hm => h w n m hn hm)⟩

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
    (f : L →ₗ⁅R⁆ L')
    (hf : ∀ w : SupportedRay d, ∀ n ∈ w.rayDegrees, ℳ n ≤ (ℒ n).map f.toLinearMap) :
    IsAbelianRays d ℳ := by
  apply (isAbelianRays_iff ℳ).mpr
  intro w n m hn hm x hx y hy
  obtain ⟨a, ha, rfl⟩ := Submodule.mem_map.mp (hf w n hn hx)
  obtain ⟨b, hb, rfl⟩ := Submodule.mem_map.mp (hf w m hm hy)
  exact (f.map_lie a b).symm.trans (by
    rw [(isAbelianRays_iff ℒ).mp ‹IsAbelianRays d ℒ› w n m hn hm a ha b hb, map_zero])

variable [DecidableEq N] [DirectSum.Decomposition ℒ]

/-- A ray element has zero homogeneous components away from its actual allowed degrees. -/
theorem mem_rayLieSubalgebra_iff (w : SupportedRay d) (x : L) :
    x ∈ rayLieSubalgebra ℒ w ↔
      ∀ n, n ∉ w.rayDegrees → (DirectSum.decompose ℒ x n : L) = 0 := by
  simpa only [rayLieSubalgebra, SupportedRay.mem_degreeSemigroup] using
    mem_supportedLieSubalgebra_iff ℒ w.degreeSemigroup x

/-- Ray Lie algebras are preserved by homogeneous projection. -/
theorem isHomogeneous_rayLieSubalgebra (w : SupportedRay d) :
    DirectSum.SetLike.IsHomogeneous ℒ (rayLieSubalgebra ℒ w) :=
  isHomogeneous_supportedLieSubalgebra ℒ w.degreeSemigroup

/-- Lie algebras on distinct supported rays have zero intersection. -/
theorem disjoint_rayLieSubalgebra [HasUniqueDiv N] {v w : SupportedRay d} (h : v ≠ w) :
    Disjoint (rayLieSubalgebra ℒ v) (rayLieSubalgebra ℒ w) := by
  apply disjoint_supportedLieSubalgebra ℒ
  rw [disjoint_iff]
  apply SetLike.coe_injective
  simpa only [Set.ext_iff, AddSubsemigroup.mem_inf, SetLike.mem_coe,
    SupportedRay.mem_degreeSemigroup, AddSubsemigroup.coe_bot, Set.mem_inter_iff,
    Set.mem_empty_iff_false] using
    Set.ext_iff.mp (SupportedRay.disjoint_rayDegrees h).inter_eq

end TauCeti

namespace TauCeti.PositiveDegrees

variable {N : Type} {R L : Type*} [AddCommGroup N] [CommRing R]
  [LieRing L] [LieAlgebra R L] [DecidableEq N]
  (d : PositiveDegrees N) (ℒ : N → Submodule R L)
  [GradedLieAlgebra ℒ] [IsPositiveGrading d ℒ]

/-- Taking the finite degree quotient commutes with forming a ray Lie algebra. -/
@[simp]
theorem map_mkQ_rayLieSubalgebra (w : SupportedRay d) (k : ℕ) :
    (rayLieSubalgebra ℒ w).map (d.degreeIdeal ℒ k).mkQ =
      rayLieSubalgebra (d.truncatedGrading ℒ k) w := by
  simpa only [LieIdeal.coe_mkQ, ← d.truncatedGrading_eq ℒ k] using
    map_rayLieSubalgebra ℒ w (d.degreeIdeal ℒ k).mkQ

/-- Degree truncation maps a ray Lie algebra onto its lower-order counterpart. -/
@[simp]
theorem map_truncationMap_rayLieSubalgebra (w : SupportedRay d)
    {k l : ℕ} (h : k ≤ l) :
    (rayLieSubalgebra (d.truncatedGrading ℒ l) w).map (d.truncationMap ℒ h) =
      rayLieSubalgebra (d.truncatedGrading ℒ k) w := by
  simpa only [d.map_truncationMap_truncatedGrading ℒ h] using
    map_rayLieSubalgebra (d.truncatedGrading ℒ l) w (d.truncationMap ℒ h)

/-- Finite degree quotients inherit abelian rays. -/
instance isAbelianRays_truncatedGrading [IsAbelianRays d ℒ] (k : ℕ) :
    IsAbelianRays d (d.truncatedGrading ℒ k) :=
  isAbelianRays_of_le_map ℒ (d.truncatedGrading ℒ k) (d.degreeIdeal ℒ k).mkQ
    (fun _ n _ => by rw [LieIdeal.coe_mkQ]; exact (d.truncatedGrading_eq ℒ k n).le)

end TauCeti.PositiveDegrees
