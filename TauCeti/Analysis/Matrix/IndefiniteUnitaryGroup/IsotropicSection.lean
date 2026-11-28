/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.ContDiff.Operations
public import Mathlib.Analysis.Matrix.Normed
public import TauCeti.LinearAlgebra.Matrix.UnitaryGroup.UnitaryTransvection
import TauCeti.Algebra.Star.Pi
import TauCeti.Analysis.Calculus.ContDiff.Star
import TauCeti.LinearAlgebra.Matrix.SesquilinearForm
import TauCeti.Topology.Algebra.Star.RealModule

/-!
# Smooth local sections of the isotropic orbit

Let `𝕜` be `ℝ` or `ℂ` and `J` a Hermitian matrix over `𝕜`, with the form
`⟨x, y⟩ = star x ⬝ᵥ J *ᵥ y` and unitary group `U(J) = Matrix.unitaryGroupOf J`. A vector `x` is
isotropic if `⟨x, x⟩ = 0`. This file shows that `U(J)` carries an isotropic vector to the nearby
isotropic vectors by elements depending real-analytically, in particular smoothly, on the target:
the orbit map `g ↦ g y₀` of an isotropic vector `y₀` has local sections over the isotropic vectors
whose matrix entries are smooth functions of the real coordinates of the target vector.

* If `y₀` is isotropic and `⟨y₀, x₀⟩ ≠ 0`, there are an open neighbourhood `N` of `x₀` and a map
  `g` from `𝕜ⁿ` to `U(J)`, whose matrix entries are real-analytic on `N`, with `g x *ᵥ y₀ = x` for
  every isotropic `x ∈ N`
  (`Matrix.unitaryGroupOf.exists_contDiffOn_mulVec_eq_of_dotProduct_mulVec_ne_zero`).
* If `J *ᵥ x₀ ≠ 0`, that is `x₀` is not in the radical of the form (for instance `J` invertible
  and `x₀ ≠ 0`), the same holds with `g x *ᵥ x₀ = x`
  (`Matrix.unitaryGroupOf.exists_contDiffOn_mulVec_eq_of_mulVec_ne_zero`). This has content
  only for isotropic `x₀`.

Neither statement assumes that `x₀` is isotropic: if it is not, a neighbourhood of `x₀` contains no
isotropic vector and the constant map `1` is a section.

The section is explicit: for isotropic `x₀`, `g x` is the admissible transvection
`Matrix.unitaryGroupOf.orbitSection` along `x - y₀` with parameter `(⟨x, y₀⟩ - ⟨x, x⟩ / 2)⁻¹`.
It lies in `U(J)` for every `x`. Where the denominator `⟨x, y₀⟩ - ⟨x, x⟩ / 2` is nonzero, it is a
quasi-reflection whose entries are rational functions of the coordinates of `x` and their
conjugates; at a zero denominator the section is the identity. It sends `y₀` to every isotropic
`x` at which that denominator does not vanish. For the second statement, a coordinate vector
pairing nontrivially with `x₀`, corrected by a multiple of `x₀`
(`Matrix.exists_comp_add_smul_dotProduct_mulVec_add_smul_eq_zero`), is an isotropic `y₀` with
`⟨y₀, x₀⟩ ≠ 0`; it gives a section `g` carrying `y₀`, and `x ↦ g x * (g x₀)⁻¹` carries `x₀`.

Smoothness uses the entrywise matrix norm (`Matrix.Norms.Elementwise`); entrywise regularity is
also available for the explicit section. The results hold more generally over a normed field
with a normed real algebra structure and a continuous, real-linear involution.

## Main results

* `Matrix.unitaryGroupOf.contDiffOn_orbitSection_apply`: the entries of the orbit section are
  real-analytic where `⟨x, y₀⟩ - ⟨x, x⟩ / 2 ≠ 0`.
* `Matrix.unitaryGroupOf.exists_contDiffOn_mulVec_eq_of_dotProduct_mulVec_ne_zero`: smooth
  local sections of the map `g ↦ g y₀`, for isotropic `y₀`, over the isotropic vectors near a
  vector `x₀` with `⟨y₀, x₀⟩ ≠ 0`.
* `Matrix.unitaryGroupOf.exists_contDiffOn_mulVec_eq_of_mulVec_ne_zero`: smooth local sections
  of the map `g ↦ g x₀` over the isotropic vectors near a vector `x₀` with `J *ᵥ x₀ ≠ 0`.

## Attribution

The statements follow `New.Exchange.exists_contDiff_carrying_isotropic` and
`New.Exchange.exists_contDiff_eventually_mulVec_eq` of grh-lean
(https://github.com/lsernau/grh-lean, Apache 2.0, Copyright 2026 Anthropic, PBC), file
`src/Lib/Adelic/Witt/SmoothWitt.lean`, which construct such sections over `ℂ` from
quasi-reflections and Eichler maps. Here a single admissible transvection, with a parameter adapted
to the target vector, is used over `ℝ` or `ℂ`.

## References

* J. Dieudonné, *La géométrie des groupes classiques*, Ergebnisse der Mathematik 5, Springer (1955),
  for Witt's extension theorem for Hermitian forms, of which these are smooth local forms for one
  isotropic vector.
-/

public section

open scoped ContDiff Matrix.Norms.Elementwise

namespace Matrix.unitaryGroupOf

variable {𝕜 : Type*} [NormedField 𝕜] [NormedAlgebra ℝ 𝕜] [StarRing 𝕜]
  [ContinuousStar 𝕜] {n : Type*} [Fintype n] [DecidableEq n] {J : Matrix n n 𝕜}

local instance : CharZero 𝕜 := Algebra.charZero_of_charZero ℝ 𝕜

local instance : StarModule ℝ 𝕜 := ContinuousStar.starModule_real

omit [DecidableEq n] in
/-- The denominator `x ↦ ⟨x, y⟩ - ⟨x, x⟩ / 2` of the orbit section is a real-analytic function of
`x`. -/
private theorem contDiff_dotProduct_sub_half_dotProduct (y : n → 𝕜) :
    ContDiff ℝ ω fun x : n → 𝕜 => star x ⬝ᵥ J *ᵥ y - star x ⬝ᵥ J *ᵥ x / 2 := by
  simp only [dotProduct, mulVec, Pi.star_apply]
  fun_prop

/-- **The orbit section is real-analytic.** For Hermitian `J` and isotropic `y₀`, the entries of the
orbit section `x ↦ Matrix.unitaryGroupOf.orbitSection hJ hy₀ x` are real-analytic functions of `x`
on the open set where `⟨x, y₀⟩ - ⟨x, x⟩ / 2 ≠ 0`. -/
theorem contDiffOn_orbitSection_apply (hJ : J.IsHermitian) {y₀ : n → 𝕜}
    (hy₀ : star y₀ ⬝ᵥ J *ᵥ y₀ = 0) (i j : n) :
    ContDiffOn ℝ ω (fun x => ((orbitSection hJ hy₀ x : GL n 𝕜) : Matrix n n 𝕜) i j)
      {x | star x ⬝ᵥ J *ᵥ y₀ - star x ⬝ᵥ J *ᵥ x / 2 ≠ 0} := by
  simp only [val_orbitSection, unitaryTransvection_def, Matrix.add_apply, Matrix.smul_apply,
    vecMulVec_apply, smul_eq_mul, TauCeti.starRingEnd_comp_eq_star]
  refine contDiffOn_const.add
    (((contDiff_dotProduct_sub_half_dotProduct y₀).contDiffOn.inv fun x hx => hx).mul ?_)
  simp only [vecMul, dotProduct, Pi.star_apply, Pi.sub_apply]
  fun_prop

/-- The orbit section is real-analytic as a matrix-valued function on its nonvanishing locus. -/
theorem contDiffOn_orbitSection (hJ : J.IsHermitian) {y₀ : n → 𝕜}
    (hy₀ : star y₀ ⬝ᵥ J *ᵥ y₀ = 0) :
    ContDiffOn ℝ ω (fun x => ((orbitSection hJ hy₀ x : GL n 𝕜) : Matrix n n 𝕜))
      {x | star x ⬝ᵥ J *ᵥ y₀ - star x ⬝ᵥ J *ᵥ x / 2 ≠ 0} :=
  contDiffOn_pi.mpr fun i => contDiffOn_pi.mpr fun j => contDiffOn_orbitSection_apply hJ hy₀ i j

/-- Near a non-isotropic vector there are no isotropic vectors, so the constant map `1` satisfies
the section property over the isotropic vectors there, for any vector `y`, vacuously. -/
private theorem exists_contDiffOn_mulVec_eq_of_ne_zero {x₀ : n → 𝕜}
    (hx₀ : star x₀ ⬝ᵥ J *ᵥ x₀ ≠ 0) (y : n → 𝕜) :
    ∃ N, IsOpen N ∧ x₀ ∈ N ∧ ∃ g : (n → 𝕜) → unitaryGroupOf J,
      ContDiffOn ℝ ω (fun x => ((g x : GL n 𝕜) : Matrix n n 𝕜)) N ∧
      ∀ x ∈ N, star x ⬝ᵥ J *ᵥ x = 0 → ((g x : GL n 𝕜) : Matrix n n 𝕜) *ᵥ y = x :=
  ⟨{x | star x ⬝ᵥ J *ᵥ x ≠ 0},
    isOpen_ne_fun (continuous_star.dotProduct (continuous_const.matrix_mulVec continuous_id))
      continuous_const, hx₀,
    fun _ => 1, contDiffOn_const, fun _ hx hx' => absurd hx' hx⟩

/-- **Smooth local sections of the isotropic orbit.** Let `J` be Hermitian and `y₀` isotropic, and
let `x₀` be a vector with `⟨y₀, x₀⟩ ≠ 0`. Then there are an open neighbourhood `N` of `x₀` and a map
`g` to the unitary group of `J`, whose matrix entries are real-analytic (in particular smooth)
functions of the real coordinates on `N`, with `g x *ᵥ y₀ = x` for every isotropic `x ∈ N`. -/
theorem exists_contDiffOn_mulVec_eq_of_dotProduct_mulVec_ne_zero (hJ : J.IsHermitian)
    {x₀ y₀ : n → 𝕜} (hy₀ : star y₀ ⬝ᵥ J *ᵥ y₀ = 0) (hxy : star y₀ ⬝ᵥ J *ᵥ x₀ ≠ 0) :
    ∃ N, IsOpen N ∧ x₀ ∈ N ∧ ∃ g : (n → 𝕜) → unitaryGroupOf J,
      ContDiffOn ℝ ω (fun x => ((g x : GL n 𝕜) : Matrix n n 𝕜)) N ∧
      ∀ x ∈ N, star x ⬝ᵥ J *ᵥ x = 0 → ((g x : GL n 𝕜) : Matrix n n 𝕜) *ᵥ y₀ = x := by
  by_cases hx₀ : star x₀ ⬝ᵥ J *ᵥ x₀ = 0
  swap
  · exact exists_contDiffOn_mulVec_eq_of_ne_zero hx₀ y₀
  -- On isotropic vectors the denominator of the orbit section is `⟨x, y₀⟩`.
  have hden (x : n → 𝕜) (hx : star x ⬝ᵥ J *ᵥ x = 0) :
      star x ⬝ᵥ J *ᵥ y₀ - star x ⬝ᵥ J *ᵥ x / 2 = star x ⬝ᵥ J *ᵥ y₀ := by
    simp [hx]
  refine ⟨_, isOpen_ne_fun (contDiff_dotProduct_sub_half_dotProduct y₀).continuous continuous_const,
    ?_, orbitSection hJ hy₀, contDiffOn_orbitSection hJ hy₀, fun x hx hxx => ?_⟩
  · rw [Set.mem_ofPred_eq, hden x₀ hx₀, ← hJ.star_dotProduct_mulVec_comm]
    exact star_ne_zero.mpr hxy
  · exact orbitSection_mulVec hJ hy₀ hxx (by rwa [← hden x hxx])

/-- **Smooth local sections, over the isotropic vectors, of the orbit map of a vector.** Let `J` be
Hermitian and let `x₀` satisfy `J *ᵥ x₀ ≠ 0`, that is lie outside the radical of the form; this
holds for instance when `J` is invertible and `x₀ ≠ 0`. Then there are an open neighbourhood `N`
of `x₀` and a map `g` to the unitary group of `J`, whose matrix entries are real-analytic (in
particular smooth) functions of the real coordinates on `N`, with `g x *ᵥ x₀ = x` for every
isotropic `x ∈ N`. This has content only when `x₀` is isotropic: otherwise `N` can be chosen to
contain no isotropic vector. -/
theorem exists_contDiffOn_mulVec_eq_of_mulVec_ne_zero (hJ : J.IsHermitian) {x₀ : n → 𝕜}
    (hx₀ : J *ᵥ x₀ ≠ 0) :
    ∃ N, IsOpen N ∧ x₀ ∈ N ∧ ∃ g : (n → 𝕜) → unitaryGroupOf J,
      ContDiffOn ℝ ω (fun x => ((g x : GL n 𝕜) : Matrix n n 𝕜)) N ∧
      ∀ x ∈ N, star x ⬝ᵥ J *ᵥ x = 0 → ((g x : GL n 𝕜) : Matrix n n 𝕜) *ᵥ x₀ = x := by
  by_cases hiso : star x₀ ⬝ᵥ J *ᵥ x₀ = 0
  swap
  · exact exists_contDiffOn_mulVec_eq_of_ne_zero hiso x₀
  -- A coordinate vector pairing nontrivially with `x₀`, corrected to an isotropic partner `y₀`.
  obtain ⟨i, hi⟩ := Function.ne_iff.mp hx₀
  have hux : (starRingEnd 𝕜 ∘ Pi.single i 1) ⬝ᵥ (J *ᵥ x₀) ≠ 0 := by
    simpa [TauCeti.starRingEnd_comp_eq_star, Pi.star_single] using hi
  obtain ⟨c, hy₀⟩ := exists_comp_add_smul_dotProduct_mulVec_add_smul_eq_zero
    (starRingEnd_self_apply (R := 𝕜)) (by rw [one_smul, transpose_map_starRingEnd, hJ.eq])
    (fun s hs => ⟨s / 2, by
      simp only [one_mul] at hs
      simp [hs, map_ofNat]⟩)
    (by rwa [TauCeti.starRingEnd_comp_eq_star]) hux
  set y₀ := Pi.single i 1 + c • x₀
  rw [TauCeti.starRingEnd_comp_eq_star] at hy₀ hux
  have hyx : star y₀ ⬝ᵥ J *ᵥ x₀ ≠ 0 := by
    simpa [y₀, star_add, add_dotProduct, star_smul, smul_dotProduct, hiso] using hux
  obtain ⟨N, hN, hx₀N, g, hg, hgy⟩ :=
    exists_contDiffOn_mulVec_eq_of_dotProduct_mulVec_ne_zero hJ hy₀ hyx
  -- The section `g` carries `y₀` to `x₀`, so `(g x₀)⁻¹` carries `x₀` back to `y₀`.
  have hinv : (((g x₀)⁻¹ : unitaryGroupOf J) : GL n 𝕜) *ᵥ x₀ = y₀ := calc
    _ = ((((g x₀ : GL n 𝕜)⁻¹ : GL n 𝕜) : Matrix n n 𝕜) *
          ((g x₀ : GL n 𝕜) : Matrix n n 𝕜)) *ᵥ y₀ := by
      rw [← mulVec_mulVec, hgy x₀ hx₀N hiso, Subgroup.coe_inv]
    _ = y₀ := by rw [Units.inv_mul, one_mulVec]
  refine ⟨N, hN, hx₀N, fun x => g x * (g x₀)⁻¹, ?_, fun x hx hxx => ?_⟩
  · refine contDiffOn_pi.mpr fun i => contDiffOn_pi.mpr fun j => ?_
    simp only [Subgroup.coe_mul, Units.val_mul, Matrix.mul_apply]
    exact ContDiffOn.sum fun l _ =>
      ((contDiffOn_pi.mp (contDiffOn_pi.mp hg i)) l).mul contDiffOn_const
  · rw [Subgroup.coe_mul, Units.val_mul, ← mulVec_mulVec, hinv, hgy x hx hxx]

end Matrix.unitaryGroupOf
