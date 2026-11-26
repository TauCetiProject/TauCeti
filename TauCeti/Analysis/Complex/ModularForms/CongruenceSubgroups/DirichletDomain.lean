/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.Fuchsian.DirichletDomain.Basic
public import TauCeti.Analysis.Complex.ModularForms.CongruenceSubgroups.QuotientMeasure

/-!
# The effective group `PΓ₀(N)` and its Dirichlet domains

The group `Γ₀(N)` contains `-I`, which acts trivially on `ℍ`, so no subset of `ℍ` is a
fundamental domain for `Γ₀(N)` itself. Its image `PΓ₀(N) = gamma0PSL N` in `PSL(2, ℝ)` has the
same orbits and acts faithfully. This file names that image and shows that its Dirichlet domain
centred at any point of the open standard fundamental domain `𝒟ᵒ` is a measurable fundamental
domain of area `[SL(2, ℤ) : Γ₀(N)] · π / 3`. Such a centre has trivial stabilizer in the image of
`PSL(2, ℤ)` (`TauCeti.ModularGroup.mem_freeLocus_of_mem_fdo`), so it works at every level. (At
level `1` the point `i` would not do: `S` fixes it, and the Dirichlet domain centred at `i` has
twice the area of a fundamental domain.)

## Main definitions

* `TauCeti.CongruenceSubgroup.gamma0PSL N`: the image `PΓ₀(N)` of `Γ₀(N)` in `PSL(2, ℝ)`.

## Main results

* `TauCeti.CongruenceSubgroup.isFundamentalDomain_dirichletDomain_gamma0PSL`: the Dirichlet
  domain of `PΓ₀(N)` centred at a point of `𝒟ᵒ` is a measurable fundamental domain.
* `TauCeti.CongruenceSubgroup.volume_dirichletDomain_gamma0PSL`: its area is
  `[SL(2, ℤ) : Γ₀(N)] · π / 3`.

## References

* H. Iwaniec, *Spectral Methods of Automorphic Forms*, 2nd ed., Graduate Studies in Mathematics
  **53**, AMS, 2002, §2.1 (fundamental domains of Fuchsian groups).
-/

public section

open MeasureTheory UpperHalfPlane CongruenceSubgroup
open scoped MatrixGroups

namespace TauCeti.CongruenceSubgroup

variable {N : ℕ}

variable (N) in
/-- **The effective group** `PΓ₀(N)`: the image of `Γ₀(N)` in `PSL(2, ℝ)`. It acts on `ℍ` with
the same orbits as `Γ₀(N)`, and, unlike `Γ₀(N)`, it acts faithfully, so it has fundamental
domains. -/
def gamma0PSL : Subgroup PSL(2, ℝ) :=
  (Gamma0 N).map sl2zToPSL2R

variable (N) in
theorem gamma0PSL_def : gamma0PSL N = (Gamma0 N).map sl2zToPSL2R := (rfl)

theorem mem_gamma0PSL {g : PSL(2, ℝ)} :
    g ∈ gamma0PSL N ↔ ∃ γ ∈ Gamma0 N, sl2zToPSL2R γ = g :=
  Subgroup.mem_map

/-- The image of `γ : SL(2, ℤ)` lies in `PΓ₀(N)` exactly when `γ ∈ Γ₀(N)`, because the kernel
`{±1}` of `sl2zToPSL2R` lies in `Γ₀(N)`. -/
theorem sl2zToPSL2R_mem_gamma0PSL_iff {γ : SL(2, ℤ)} :
    sl2zToPSL2R γ ∈ gamma0PSL N ↔ γ ∈ Gamma0 N := by
  refine (Subgroup.ext_iff.mp (Subgroup.comap_map_eq_self fun δ hδ ↦ ?_) γ)
  rw [sl2zToPSL2R_ker, Matrix.SpecialLinearGroup.mem_center_iff] at hδ
  obtain ⟨r, -, hr⟩ := hδ
  rw [Gamma0_mem, ← hr, Matrix.scalar_apply, Matrix.diagonal_apply_ne _ (by decide),
    Int.cast_zero]

instance : DiscreteTopology (gamma0PSL N) :=
  Subgroup.discreteTopology_map_sl2zToPSL2R _

/-- **The Dirichlet domain of `PΓ₀(N)` centred at a point of `𝒟ᵒ`** is a measurable fundamental
domain. -/
theorem isFundamentalDomain_dirichletDomain_gamma0PSL {z₀ : ℍ}
    (hz₀ : z₀ ∈ _root_.ModularGroup.fdo) :
    IsFundamentalDomain (gamma0PSL N) (dirichletDomain (gamma0PSL N) z₀) :=
  Subgroup.isFundamentalDomain_dirichletDomain _ <| ModularGroup.mem_freeLocus_of_mem_fdo
    (Subgroup.map_sl2zToPSL2R_le_range_psl2zToPSL2R _) hz₀

/-- **The area of a Dirichlet domain of `PΓ₀(N)`** centred at a point of `𝒟ᵒ` is the area
`[SL(2, ℤ) : Γ₀(N)] · π / 3` of `Γ₀(N) \ ℍ`. -/
theorem volume_dirichletDomain_gamma0PSL [NeZero N] {z₀ : ℍ}
    (hz₀ : z₀ ∈ _root_.ModularGroup.fdo) :
    volume (dirichletDomain (gamma0PSL N) z₀) =
      (Gamma0 N).index * ENNReal.ofReal (Real.pi / 3) := by
  rw [← (isFundamentalDomain_dirichletDomain_gamma0PSL hz₀).covolume_eq_volume, gamma0PSL,
    ← Subgroup.quotientVolume_univ, quotientVolume_Gamma0_univ]

end TauCeti.CongruenceSubgroup
