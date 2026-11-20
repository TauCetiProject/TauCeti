/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Geometry.ScatteringDiagram.WallSpace.Basic

/-!
# A common normal for transverse wall spaces

At a degree with geometric direction `v` outside the common kernel of two integral
characters `f` and `g`, the wall spaces with normals annihilating their common kernel
sum to the wall space with normal `f v • g - g v • f`. This contracted normal also
annihilates `v`. The formula includes a zero contracted normal, in which case all
the contributing wall spaces vanish.

This is the wall-space calculation for transverse joint corrections in Mandel,
*Scattering diagrams, theta functions, and refined tropical curve counts*,
proof of Theorem 2.6.

Adapted from `Mei/Geometry/ScatteringDiagram/WallSpace/Normal.lean` in
[yuma-mizuno-lean/Mei](https://github.com/yuma-mizuno-lean/Mei), commit
`bf3986029ff4d3eb4025d4067489511b0724374e` (Apache 2.0).
-/

public section

namespace TauCeti.DirectedWallSpaces

variable {Γ Λ R L : Type*} [AddCommMonoid Γ] [AddCommGroup Λ]
  [CommRing R] [LieRing L] [LieAlgebra R L]
  {ρ : Γ →+ Λ} {ℒ : Γ → Submodule R L} (H : DirectedWallSpaces ρ ℒ)

/-- At a transverse degree, any wall space with normal annihilating the common kernel
is contained in the wall space with the contracted normal. -/
theorem wall_le_wallBracketNormal_of_inf_ker_le (f g m : Λ →+ ℤ) {n : Γ}
    (hn : ρ n ∉ f.ker ⊓ g.ker) (hm : f.ker ⊓ g.ker ≤ m.ker) :
    H.wall n m ≤ H.wall n (wallBracketNormal ρ n n f g) := by
  by_cases hmn : m (ρ n) = 0
  · let μ := wallBracketNormal ρ n n f g
    have hμ : μ = f (ρ n) • g - g (ρ n) • f := by
      ext v
      simp only [μ, wallBracketNormal_apply, AddMonoidHom.sub_apply, AddMonoidHom.zsmul_apply,
        Int.zsmul_eq_mul]
    have hker : μ.ker ≤ m.ker := by
      rw [hμ]
      exact f.ker_zsmul_sub_zsmul_le_of_inf_ker_le g m (ρ n) hn hm hmn
    obtain ⟨a, b, ha, hab⟩ := μ.exists_ne_zero_zsmul_eq_of_ker_le m hker
    by_cases hb : b = 0
    · have hm0 : m = 0 := by
        ext v
        have hprod : a * m v = 0 := by simpa [hb] using DFunLike.congr_fun hab v
        exact (Int.mul_eq_zero.mp hprod).resolve_left ha
      simp [hm0]
    · exact (calc
        H.wall n m = H.wall n (a • m) := (H.rescale n m a ha).symm
        _ = H.wall n (b • μ) := congrArg (H.wall n) hab
        _ = H.wall n μ := H.rescale n μ b hb).le
  · simp [hmn]

/-- At a degree transverse to the common kernel of two normals, the sum of the wall spaces
with normals vanishing on the kernel is the wall space with the contracted normal. -/
theorem iSup_wall_eq_wallBracketNormal_of_notMem_inf_ker (f g : Λ →+ ℤ) {n : Γ}
    (hn : ρ n ∉ f.ker ⊓ g.ker) :
    (⨆ (m : Λ →+ ℤ) (_ : f.ker ⊓ g.ker ≤ m.ker), H.wall n m) =
      H.wall n (wallBracketNormal ρ n n f g) := by
  refine le_antisymm (iSup₂_le fun m hm => H.wall_le_wallBracketNormal_of_inf_ker_le f g m hn hm) ?_
  have hμ : f.ker ⊓ g.ker ≤ (wallBracketNormal ρ n n f g).ker := by
    intro v hv
    have hf : f v = 0 := hv.1
    have hg : g v = 0 := hv.2
    simp [AddMonoidHom.mem_ker, hf, hg]
  exact le_iSup₂_of_le (wallBracketNormal ρ n n f g) hμ le_rfl

end TauCeti.DirectedWallSpaces
