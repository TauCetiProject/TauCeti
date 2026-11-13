/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Geometry.ScatteringDiagram.WallSpace.Ray
import TauCeti.Algebra.DirectSum.Component

/-!
# Brackets between supported-ray wall sums

Bracketing two supported-ray sums produces wall elements at sums of actual
allowed degrees. The output normal contracts each input normal against the
other input's geometric direction; it can vary with both integer multipliers.
For an internal decomposition, the degree-`n` component uses only pairs adding
to `n`. This locates the homogeneous contributions of a wall interaction without
assuming that primitive generators belong to the positive monoid.

The proofs use submodule suprema and `TauCeti.homogeneousComponent`
to select the contributions at each degree.
The contracted-normal rule is the directed-wall law of Leung, Ma and Young,
*Refined scattering diagrams and theta functions from asymptotic analysis of
Maurer-Cartan equations*, Definition 1.2.

Adapted from `Mei/Geometry/ScatteringDiagram/WallSpace/Bracket.lean` in
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

/-- Brackets of ray sums lie in the sum of wall spaces with the contracted
normals of all pairs of actual allowed degrees. -/
theorem lie_mem_iSup_wall_of_mem_raySubmodule
    {w v : SupportedRay d} {m m' : Λ →+ ℤ} {x y : L}
    (hx : x ∈ H.raySubmodule w m) (hy : y ∈ H.raySubmodule v m') :
    ⁅x, y⁆ ∈ ⨆ a : w.rayDegrees, ⨆ b : v.rayDegrees,
      H.wall (a.val + b.val) (wallBracketNormal ρ a.val b.val m m') := by
  rw [raySubmodule_def] at hx hy
  refine lie_mem_of_mem_iSup
    (fun a : w.rayDegrees => H.wall a m) (fun b : v.rayDegrees => H.wall b m') _
    (fun a b x hx y hy => ?_) hx hy
  exact Submodule.mem_iSup_of_mem a (Submodule.mem_iSup_of_mem b (H.bracket_mem hx hy))

/-- The supported-ray bracket formula indexed by positive integer multipliers.
Only multiples belonging to the positive monoid are included. -/
theorem lie_mem_iSup_wall_zsmul_of_mem_raySubmodule
    {w v : SupportedRay d} {m m' : Λ →+ ℤ} {x y : L}
    (hx : x ∈ H.raySubmodule w m) (hy : y ∈ H.raySubmodule v m') :
    ⁅x, y⁆ ∈ ⨆ (a : ℤ) (_ : 0 < a) (_ : a • w.generator ∈ d.monoid),
      ⨆ (b : ℤ) (_ : 0 < b) (_ : b • v.generator ∈ d.monoid),
        H.wall (a • w.generator + b • v.generator)
          ((b * m (ρ v.generator)) • m' - (a * m' (ρ w.generator)) • m) := by
  suffices hle : (⨆ a : w.rayDegrees, ⨆ b : v.rayDegrees,
      H.wall (a.val + b.val) (wallBracketNormal ρ a.val b.val m m')) ≤ _ by
    exact hle (H.lie_mem_iSup_wall_of_mem_raySubmodule hx hy)
  refine iSup_le fun a => iSup_le fun b => ?_
  obtain ⟨hma, a', ha', hea⟩ := SupportedRay.mem_rayDegrees.mp a.property
  obtain ⟨hmb, b', hb', heb⟩ := SupportedRay.mem_rayDegrees.mp b.property
  rw [hea] at hma
  rw [heb] at hmb
  rw [hea, heb, wallBracketNormal_zsmul]
  exact le_iSup_of_le a' (le_iSup_of_le ha' (le_iSup_of_le hma
    (le_iSup_of_le b' (le_iSup_of_le hb' (le_iSup_of_le hmb le_rfl)))))

variable [DecidableEq Γ] [DirectSum.Decomposition ℒ]

/-- The component of an interaction at degree `n` lies in the sum over allowed
ray-degree pairs adding to `n`, with each pair's contracted normal. -/
theorem decompose_lie_mem_iSup_wall_of_mem_raySubmodule
    {w v : SupportedRay d} {m m' : Λ →+ ℤ} {x y : L}
    (hx : x ∈ H.raySubmodule w m) (hy : y ∈ H.raySubmodule v m') (n : Γ) :
    (DirectSum.decompose ℒ ⁅x, y⁆ n : L) ∈
      ⨆ a : w.rayDegrees, ⨆ b : v.rayDegrees, ⨆ (_ : a.val + b.val = n),
        H.wall n (wallBracketNormal ρ a.val b.val m m') := by
  have hxy := H.lie_mem_iSup_wall_of_mem_raySubmodule hx hy
  let S := ⨆ a : w.rayDegrees, ⨆ b : v.rayDegrees, ⨆ (_ : a.val + b.val = n),
    H.wall n (wallBracketNormal ρ a.val b.val m m')
  let p := homogeneousComponent ℒ n
  suffices hle : (⨆ a : w.rayDegrees, ⨆ b : v.rayDegrees,
      H.wall (a.val + b.val) (wallBracketNormal ρ a.val b.val m m')).map p ≤ S from
    by simpa only [p, homogeneousComponent_apply] using
      hle (Submodule.mem_map.mpr ⟨⁅x, y⁆, hxy, rfl⟩)
  simp only [Submodule.map_iSup]
  refine iSup_le fun a => iSup_le fun b => Submodule.map_le_iff_le_comap.mpr ?_
  intro z hz
  simp only [Submodule.mem_comap, p]
  by_cases hab : a.val + b.val = n
  · rw [homogeneousComponent_apply_of_mem ℒ (hab ▸ H.wall_le_piece _ _ hz)]
    exact Submodule.mem_iSup_of_mem a
      (Submodule.mem_iSup_of_mem b (Submodule.mem_iSup_of_mem hab (hab ▸ hz)))
  · rw [homogeneousComponent_apply_of_mem_ne ℒ (H.wall_le_piece _ _ hz) hab]
    exact S.zero_mem

/-- A ray interaction has no component at a degree which is not a sum of an
actual degree on each input ray. -/
theorem decompose_lie_eq_zero_of_mem_raySubmodule_of_forall_add_ne
    {w v : SupportedRay d} {m m' : Λ →+ ℤ} {x y : L}
    (hx : x ∈ H.raySubmodule w m) (hy : y ∈ H.raySubmodule v m')
    {n : Γ} (hn : ∀ a ∈ w.rayDegrees, ∀ b ∈ v.rayDegrees, a + b ≠ n) :
    (DirectSum.decompose ℒ ⁅x, y⁆ n : L) = 0 := by
  have hxy := H.decompose_lie_mem_iSup_wall_of_mem_raySubmodule hx hy n
  simpa only [iSup_of_empty, hn _ (Subtype.property _) _ (Subtype.property _),
    iSup_bot, Submodule.mem_bot] using hxy

end TauCeti.DirectedWallSpaces
