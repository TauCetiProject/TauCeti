/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Geometry.ScatteringDiagram.WallSpace.Map
public import TauCeti.Algebra.Lie.Graded.Ray

/-!
# Wall spaces on supported rays

The sum of the homogeneous wall spaces on the actual allowed degrees of a
supported ray is an abelian Lie subalgebra. Distinct rays with proportional
normals commute as well, and so do two rays each of whose normals annihilates the geometric
direction of the other ray. The primitive generator need not be an allowed degree.

For an internal grading, membership in this sum is detected by homogeneous
components: they belong to the prescribed wall spaces, and vanish away from the
ray. The construction uses Mathlib's submodule suprema and
`Submodule.iSup_induction`, with the supported degrees from `TauCeti.SupportedRay`.

Adapted from `Mei/Geometry/ScatteringDiagram/WallSpace/Ray.lean` in
[yuma-mizuno-lean/Mei](https://github.com/yuma-mizuno-lean/Mei), commit
`a79c57178cc83666fc244ca6e6eeaa722e9b8bc7` (Apache 2.0).
Original notice: Copyright (c) 2026 Mei contributors. All rights reserved.
Authors: Codex.
-/

public section

namespace TauCeti.DirectedWallSpaces

variable {Γ Λ R L : Type*} [AddCommGroup Γ] [AddCommMonoid Λ]
  [CommRing R] [LieRing L] [LieAlgebra R L]
  {ρ : Γ →+ Λ} {ℒ : Γ → Submodule R L} {d : PositiveDegrees Γ}
  (H : DirectedWallSpaces ρ ℒ)

/-- The sum of wall spaces on the actual allowed degrees of a supported ray. -/
def raySubmodule (w : SupportedRay d) (m : Λ →+ ℤ) : Submodule R L :=
  ⨆ n : w.rayDegrees, H.wall n m

/-- The ray submodule is the sum over its allowed degrees. -/
theorem raySubmodule_def (w : SupportedRay d) (m : Λ →+ ℤ) :
    H.raySubmodule w m = ⨆ n : w.rayDegrees, H.wall n m := (rfl)

/-- A ray sum lies in a submodule exactly when every selected wall space does. -/
theorem raySubmodule_le_iff (w : SupportedRay d) (m : Λ →+ ℤ) (K : Submodule R L) :
    H.raySubmodule w m ≤ K ↔ ∀ n ∈ w.rayDegrees, H.wall n m ≤ K := by
  simp only [raySubmodule_def, iSup_le_iff, Subtype.forall]

/-- Relabeling tangent directions pulls back the normal of a supported-ray sum. -/
@[simp]
theorem mapTangent_raySubmodule {Λ' : Type*} [AddCommMonoid Λ']
    (T : Λ →+ Λ') (w : SupportedRay d) (m : Λ' →+ ℤ) :
    (H.mapTangent T).raySubmodule w m = H.raySubmodule w (m.comp T) := by
  simp only [raySubmodule_def, mapTangent_wall]

/-- Taking the image of wall spaces commutes with forming their supported-ray sum. -/
@[simp]
theorem map_raySubmodule {L' : Type*} [LieRing L'] [LieAlgebra R L']
    (f : L →ₗ⁅R⁆ L') (ℳ : Γ → Submodule R L')
    (hf : ∀ n, (ℒ n).map f.toLinearMap ≤ ℳ n)
    (w : SupportedRay d) (m : Λ →+ ℤ) :
    (H.map f ℳ hf).raySubmodule w m = (H.raySubmodule w m).map f.toLinearMap := by
  simp only [raySubmodule_def, map_wall, Submodule.map_iSup]

/-- Every ray wall sum lies in the ray Lie subalgebra of the underlying grading. -/
theorem raySubmodule_le_rayLieSubalgebra [SetLike.GradedBracket ℒ ℒ]
    (w : SupportedRay d) (m : Λ →+ ℤ) :
    H.raySubmodule w m ≤ (TauCeti.rayLieSubalgebra ℒ w).toSubmodule := by
  rw [raySubmodule_def]
  exact iSup_le fun n => (H.wall_le_piece n m).trans (le_rayLieSubalgebra ℒ n.property)

/-- A homogeneous wall space embeds into its supported-ray sum. -/
theorem wall_le_raySubmodule (w : SupportedRay d) (m : Λ →+ ℤ)
    {n : Γ} (hn : n ∈ w.rayDegrees) : H.wall n m ≤ H.raySubmodule w m :=
  le_iSup (fun n : w.rayDegrees => H.wall n m) ⟨n, hn⟩

/-- Rescaling the normal by a nonzero integer preserves the ray submodule. -/
@[simp↓]
theorem raySubmodule_rescale (w : SupportedRay d) (m : Λ →+ ℤ)
    (c : ℤ) (hc : c ≠ 0) : H.raySubmodule w (c • m) = H.raySubmodule w m := by
  simp only [raySubmodule_def, H.rescale _ _ c hc]

/-- Normals with the same kernel give the same supported-ray wall sum. -/
theorem raySubmodule_eq_of_ker_eq {Λ : Type*} [AddCommGroup Λ]
    {ρ : Γ →+ Λ} {ℒ : Γ → Submodule R L} (H : DirectedWallSpaces ρ ℒ)
    (w : SupportedRay d) {m m' : Λ →+ ℤ} (hker : m.ker = m'.ker) :
    H.raySubmodule w m = H.raySubmodule w m' := by
  simp only [raySubmodule_def, H.wall_eq_of_ker_eq _ hker]

/-- A zero normal has zero ray submodule. -/
@[simp]
theorem raySubmodule_zero (w : SupportedRay d) : H.raySubmodule w 0 = ⊥ := by
  simp only [raySubmodule_def, H.zero_normal, iSup_bot]

/-- A nonzero wall element at an actual ray degree has normal annihilating the geometric
direction of the generator. -/
theorem normal_apply_generator_eq_zero {w : SupportedRay d} {n : Γ} {m : Λ →+ ℤ}
    {x : L} (hn : n ∈ w.rayDegrees) (hx : x ∈ H.wall n m) (hx0 : x ≠ 0) :
    m (ρ w.generator) = 0 := by
  obtain ⟨-, a, ha, rfl⟩ := SupportedRay.mem_rayDegrees.mp hn
  have h := H.normal_apply_eq_zero hx hx0
  have hmul : a * m (ρ w.generator) = 0 := by
    simpa only [AddMonoidHom.comp_apply, h, zsmul_eq_mul, Int.cast_id] using
      ((m.comp ρ).map_zsmul a w.generator).symm
  exact (mul_eq_zero.mp hmul).resolve_left (ne_of_gt ha)

/-- A normal not annihilating the geometric direction of the generator has zero
supported-ray wall sum. -/
@[simp]
theorem raySubmodule_nontangent (w : SupportedRay d) (m : Λ →+ ℤ)
    (hm : m (ρ w.generator) ≠ 0) : H.raySubmodule w m = ⊥ := by
  apply le_antisymm _ bot_le
  refine (H.raySubmodule_le_iff w m ⊥).mpr fun n hn x hx => ?_
  exact (Submodule.mem_bot R).mpr (by
    by_contra hx0
    exact hm (H.normal_apply_generator_eq_zero hn hx hx0))

/-- Two ray sums commute as soon as their homogeneous wall elements at the allowed degrees of
the two rays commute. -/
theorem lie_eq_zero_of_mem_raySubmodule_of_forall {w v : SupportedRay d} {m m' : Λ →+ ℤ}
    (hwall : ∀ n ∈ w.rayDegrees, ∀ n' ∈ v.rayDegrees, ∀ x ∈ H.wall n m, ∀ y ∈ H.wall n' m',
      ⁅x, y⁆ = 0)
    {x y : L} (hx : x ∈ H.raySubmodule w m) (hy : y ∈ H.raySubmodule v m') : ⁅x, y⁆ = 0 := by
  rw [raySubmodule_def] at hx hy
  exact lie_eq_zero_of_mem_iSup
    (fun n : w.rayDegrees => H.wall n m) (fun n : v.rayDegrees => H.wall n m')
    (fun n n' => hwall n n.property n' n'.property) hx hy

/-- Sums of wall elements with rationally proportional normals commute, even
when their supported rays differ. -/
theorem lie_eq_zero_of_mem_raySubmodule_of_proportional {w v : SupportedRay d} {m m' : Λ →+ ℤ}
    {x y : L} (hx : x ∈ H.raySubmodule w m) (hy : y ∈ H.raySubmodule v m')
    {c e : ℤ} (hc : c ≠ 0) (he : e ≠ 0) (hm : c • m = e • m') : ⁅x, y⁆ = 0 :=
  H.lie_eq_zero_of_mem_raySubmodule_of_forall
    (fun _ _ _ _ _ hx _ hy => H.lie_eq_zero_of_proportional hx hy hc he hm) hx hy

/-- Sums of wall elements on the supported rays `w` and `v`, with normals `m` and `m'`, commute
if `m` annihilates the geometric direction `ρ(v)` of the generator of `v` and `m'` annihilates
`ρ(w)`. The normals need not be proportional. -/
theorem lie_eq_zero_of_mem_raySubmodule_of_apply_eq_zero {w v : SupportedRay d}
    {m m' : Λ →+ ℤ} (hm : m (ρ v.generator) = 0) (hm' : m' (ρ w.generator) = 0)
    {x y : L} (hx : x ∈ H.raySubmodule w m) (hy : y ∈ H.raySubmodule v m') : ⁅x, y⁆ = 0 := by
  refine H.lie_eq_zero_of_mem_raySubmodule_of_forall (fun n hn n' hn' x hx y hy => ?_) hx hy
  obtain ⟨-, a, -, rfl⟩ := SupportedRay.mem_rayDegrees.mp hn
  obtain ⟨-, b, -, rfl⟩ := SupportedRay.mem_rayDegrees.mp hn'
  refine H.lie_eq_zero_of_apply_eq_zero hx hy ?_ ?_
  · simpa only [AddMonoidHom.comp_apply, hm, smul_zero] using (m.comp ρ).map_zsmul b v.generator
  · simpa only [AddMonoidHom.comp_apply, hm', smul_zero] using (m'.comp ρ).map_zsmul a w.generator

/-- The ray sum is an abelian Lie subalgebra of the original Lie algebra. -/
def wallRayLieSubalgebra (w : SupportedRay d) (m : Λ →+ ℤ) : LieSubalgebra R L where
  toSubmodule := H.raySubmodule w m
  lie_mem' hx hy := by
    rw [H.lie_eq_zero_of_mem_raySubmodule_of_proportional hx hy one_ne_zero one_ne_zero rfl]
    exact Submodule.zero_mem _

/-- The underlying module of a wall ray Lie subalgebra is its supported-ray wall sum. -/
@[simp]
theorem wallRayLieSubalgebra_toSubmodule (w : SupportedRay d) (m : Λ →+ ℤ) :
    (H.wallRayLieSubalgebra w m).toSubmodule = H.raySubmodule w m := (rfl)

/-- Membership in the ray Lie subalgebra is membership in the ray sum. -/
@[simp]
theorem mem_wallRayLieSubalgebra (w : SupportedRay d) (m : Λ →+ ℤ) (x : L) :
    x ∈ H.wallRayLieSubalgebra w m ↔ x ∈ H.raySubmodule w m := Iff.rfl

/-- A wall ray Lie subalgebra lies in another exactly when all its wall spaces do. -/
theorem wallRayLieSubalgebra_le_iff (w : SupportedRay d) (m : Λ →+ ℤ)
    (K : LieSubalgebra R L) :
    H.wallRayLieSubalgebra w m ≤ K ↔ ∀ n ∈ w.rayDegrees, H.wall n m ≤ K.toSubmodule := by
  rw [← LieSubalgebra.toSubmodule_le_toSubmodule, wallRayLieSubalgebra_toSubmodule,
    raySubmodule_le_iff]

/-- Relabeling tangent directions pulls back the normal of a wall ray Lie subalgebra. -/
@[simp]
theorem mapTangent_wallRayLieSubalgebra {Λ' : Type*} [AddCommMonoid Λ']
    (T : Λ →+ Λ') (w : SupportedRay d) (m : Λ' →+ ℤ) :
    (H.mapTangent T).wallRayLieSubalgebra w m = H.wallRayLieSubalgebra w (m.comp T) := by
  apply LieSubalgebra.toSubmodule_injective
  simp only [wallRayLieSubalgebra_toSubmodule, mapTangent_raySubmodule]

/-- Rescaling a normal by a nonzero integer preserves the wall ray Lie subalgebra. -/
@[simp↓]
theorem wallRayLieSubalgebra_rescale (w : SupportedRay d) (m : Λ →+ ℤ)
    (c : ℤ) (hc : c ≠ 0) : H.wallRayLieSubalgebra w (c • m) = H.wallRayLieSubalgebra w m := by
  apply LieSubalgebra.toSubmodule_injective
  simp only [wallRayLieSubalgebra_toSubmodule, H.raySubmodule_rescale w m c hc]

/-- Normals with the same kernel give the same wall ray Lie subalgebra. -/
theorem wallRayLieSubalgebra_eq_of_ker_eq {Λ : Type*} [AddCommGroup Λ]
    {ρ : Γ →+ Λ} {ℒ : Γ → Submodule R L} (H : DirectedWallSpaces ρ ℒ)
    (w : SupportedRay d) {m m' : Λ →+ ℤ} (hker : m.ker = m'.ker) :
    H.wallRayLieSubalgebra w m = H.wallRayLieSubalgebra w m' := by
  apply LieSubalgebra.toSubmodule_injective
  simp only [wallRayLieSubalgebra_toSubmodule, H.raySubmodule_eq_of_ker_eq w hker]

/-- A zero normal gives the zero wall ray Lie subalgebra. -/
@[simp]
theorem wallRayLieSubalgebra_zero (w : SupportedRay d) : H.wallRayLieSubalgebra w 0 = ⊥ := by
  apply LieSubalgebra.toSubmodule_injective
  simp only [wallRayLieSubalgebra_toSubmodule, raySubmodule_zero, LieSubalgebra.bot_toSubmodule]

/-- A normal not annihilating the geometric direction of the generator gives the zero
wall ray Lie subalgebra. -/
@[simp]
theorem wallRayLieSubalgebra_nontangent (w : SupportedRay d) (m : Λ →+ ℤ)
    (hm : m (ρ w.generator) ≠ 0) : H.wallRayLieSubalgebra w m = ⊥ := by
  apply LieSubalgebra.toSubmodule_injective
  simp only [wallRayLieSubalgebra_toSubmodule, H.raySubmodule_nontangent w m hm,
    LieSubalgebra.bot_toSubmodule]

/-- A wall ray Lie subalgebra lies in the ambient supported-ray Lie subalgebra. -/
theorem wallRayLieSubalgebra_le_rayLieSubalgebra [SetLike.GradedBracket ℒ ℒ]
    (w : SupportedRay d) (m : Λ →+ ℤ) :
    H.wallRayLieSubalgebra w m ≤ TauCeti.rayLieSubalgebra ℒ w := by
  rw [← LieSubalgebra.toSubmodule_le_toSubmodule, wallRayLieSubalgebra_toSubmodule]
  exact H.raySubmodule_le_rayLieSubalgebra w m

/-- Taking images commutes with forming the wall ray Lie subalgebra. -/
@[simp]
theorem map_wallRayLieSubalgebra {L' : Type*} [LieRing L'] [LieAlgebra R L']
    (f : L →ₗ⁅R⁆ L') (ℳ : Γ → Submodule R L')
    (hf : ∀ n, (ℒ n).map f.toLinearMap ≤ ℳ n)
    (w : SupportedRay d) (m : Λ →+ ℤ) :
    (H.map f ℳ hf).wallRayLieSubalgebra w m = (H.wallRayLieSubalgebra w m).map f := by
  apply LieSubalgebra.toSubmodule_injective
  rw [LieSubalgebra.map_toSubmodule, wallRayLieSubalgebra_toSubmodule,
    wallRayLieSubalgebra_toSubmodule, map_raySubmodule]

/-- Every supported-ray wall Lie algebra is abelian. -/
instance wallRayLieSubalgebra_isLieAbelian (w : SupportedRay d) (m : Λ →+ ℤ) :
    IsLieAbelian (H.wallRayLieSubalgebra w m) where
  trivial x y := Subtype.ext
    (H.lie_eq_zero_of_mem_raySubmodule_of_proportional
      x.property y.property one_ne_zero one_ne_zero rfl)

variable [DecidableEq Γ] [DirectSum.Decomposition ℒ]

/-- Homogeneous components of a ray sum lie in their prescribed wall space. -/
theorem decompose_mem_wall_of_mem_raySubmodule {w : SupportedRay d} {m : Λ →+ ℤ}
    {x : L} (hx : x ∈ H.raySubmodule w m) (n : Γ) :
    (DirectSum.decompose ℒ x n : L) ∈ H.wall n m := by
  rw [raySubmodule_def] at hx
  refine Submodule.iSup_induction _
    (motive := fun x => (DirectSum.decompose ℒ x n : L) ∈ H.wall n m) hx
    (fun i x hx => ?_) (by simp)
    (fun x y hx hy => by simpa using (H.wall n m).add_mem hx hy)
  · by_cases h : (i : Γ) = n
    · subst n
      rwa [DirectSum.decompose_of_mem_same ℒ (H.wall_le_piece _ _ hx)]
    · rw [DirectSum.decompose_of_mem_ne ℒ (H.wall_le_piece _ _ hx) h]
      exact Submodule.zero_mem _

/-- Components outside the actual ray degrees vanish. -/
theorem decompose_eq_zero_of_notMem_rayDegrees {w : SupportedRay d} {m : Λ →+ ℤ}
    {x : L} (hx : x ∈ H.raySubmodule w m) {n : Γ} (hn : n ∉ w.rayDegrees) :
    (DirectSum.decompose ℒ x n : L) = 0 := by
  have hle : H.raySubmodule w m ≤ ⨆ n : w.rayDegrees, ℒ n :=
    iSup_mono fun n => H.wall_le_piece n m
  exact (TauCeti.DirectSum.mem_iSup_iff_decompose_eq_zero ℒ w.rayDegrees).mp (hle hx) n hn

/-- Supported-ray wall sums are stable under homogeneous projections. -/
theorem isHomogeneous_raySubmodule (w : SupportedRay d) (m : Λ →+ ℤ) :
    DirectSum.SetLike.IsHomogeneous ℒ (H.raySubmodule w m) := by
  intro n x hx
  by_cases hn : n ∈ w.rayDegrees
  · exact H.wall_le_raySubmodule w m hn (H.decompose_mem_wall_of_mem_raySubmodule hx n)
  · rw [H.decompose_eq_zero_of_notMem_rayDegrees hx hn]
    exact Submodule.zero_mem _

/-- Wall ray Lie subalgebras are stable under homogeneous projections. -/
theorem isHomogeneous_wallRayLieSubalgebra (w : SupportedRay d) (m : Λ →+ ℤ) :
    DirectSum.SetLike.IsHomogeneous ℒ (H.wallRayLieSubalgebra w m) := by
  simpa only [DirectSum.SetLike.IsHomogeneous, mem_wallRayLieSubalgebra] using
    H.isHomogeneous_raySubmodule w m

/-- Membership in a ray sum is equivalent to the wall-space condition on every
component and vanishing of all components off the actual allowed ray degrees. -/
theorem mem_raySubmodule_iff (w : SupportedRay d) (m : Λ →+ ℤ) (x : L) :
    x ∈ H.raySubmodule w m ↔
      (∀ n, (DirectSum.decompose ℒ x n : L) ∈ H.wall n m) ∧
      ∀ n, n ∉ w.rayDegrees → (DirectSum.decompose ℒ x n : L) = 0 := by
  classical
  refine ⟨fun hx => ⟨H.decompose_mem_wall_of_mem_raySubmodule hx,
    fun _ hn => H.decompose_eq_zero_of_notMem_rayDegrees hx hn⟩, ?_⟩
  rintro ⟨hwall, hzero⟩
  apply (DirectSum.AddSubmonoidClass.IsHomogeneous.mem_iff ℒ _
    (H.isHomogeneous_raySubmodule w m)).mpr
  intro n
  by_cases hn : n ∈ w.rayDegrees
  · exact H.wall_le_raySubmodule w m hn (hwall n)
  · rw [hzero n hn]
    exact Submodule.zero_mem _

end TauCeti.DirectedWallSpaces

namespace TauCeti.DirectedWallSpaces

variable {Γ Γ' Λ Λ' R R' L L' F : Type*}
  [AddCommGroup Γ] [AddCommGroup Γ'] [AddCommMonoid Λ] [AddCommMonoid Λ']
  [CommRing R] [CommRing R'] [LieRing L] [LieAlgebra R L]
  [LieRing L'] [LieAlgebra R' L'] [FunLike F L L'] [AddMonoidHomClass F L L']
  {ρ : Γ →+ Λ} {ρ' : Γ' →+ Λ'}
  {ℒ : Γ → Submodule R L} {ℳ : Γ' → Submodule R' L'}
  {d : PositiveDegrees Γ} {e : PositiveDegrees Γ'}

/-- An additive map preserving the homogeneous wall spaces on a ray preserves their
sum. The target ray condition concerns actual allowed degrees only. -/
theorem map_mem_raySubmodule (H : DirectedWallSpaces ρ ℒ) (H' : DirectedWallSpaces ρ' ℳ)
    (f : F) (T : Γ → Γ') {w : SupportedRay d} {v : SupportedRay e}
    {m : Λ →+ ℤ} {m' : Λ' →+ ℤ}
    (hdegree : ∀ n ∈ w.rayDegrees, T n ∈ v.rayDegrees)
    (hwall : ∀ n ∈ w.rayDegrees, ∀ x ∈ H.wall n m, f x ∈ H'.wall (T n) m')
    {x : L} (hx : x ∈ H.raySubmodule w m) : f x ∈ H'.raySubmodule v m' := by
  rw [raySubmodule_def] at hx
  exact Submodule.iSup_induction _ (motive := fun x => f x ∈ H'.raySubmodule v m') hx
    (fun n x hx => H'.wall_le_raySubmodule v m' (hdegree n n.property)
      (hwall n n.property x hx))
    (by simp) (fun x y hx hy => by simpa using (H'.raySubmodule v m').add_mem hx hy)

end TauCeti.DirectedWallSpaces
