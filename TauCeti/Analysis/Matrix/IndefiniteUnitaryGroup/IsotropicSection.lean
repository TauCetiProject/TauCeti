/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.Matrix.IndefiniteUnitaryGroup.QuasiReflection
public import Mathlib.Analysis.Calculus.ContDiff.Operations
public import Mathlib.Analysis.RCLike.Basic
import Mathlib.Topology.Instances.Matrix
import TauCeti.Analysis.Calculus.ContDiff.Star
import TauCeti.LinearAlgebra.Matrix.SesquilinearForm

/-!
# Smooth local sections of the isotropic orbit

Let `𝕜` be `ℝ` or `ℂ` and `J` a Hermitian matrix over `𝕜`, with the form
`⟨x, y⟩ = star x ⬝ᵥ J *ᵥ y` and unitary group `U(J) = Matrix.unitaryGroupOf J`. A vector `x` is
isotropic if `⟨x, x⟩ = 0`. This file shows that `U(J)` carries isotropic vectors to nearby isotropic
vectors by elements depending real-analytically, in particular smoothly, on the target: the orbit
map `g ↦ g y₀` of an isotropic vector admits local sections that are smooth functions of the
real coordinates of the target vector.

* If `y₀` is isotropic and `⟨y₀, x₀⟩ ≠ 0`, there are an open neighbourhood `N` of `x₀` and a map
  `g` from `𝕜ⁿ` to `U(J)`, whose matrix entries are real-analytic on `N`, with `g x *ᵥ y₀ = x` for
  every isotropic `x ∈ N` (`Matrix.unitaryGroupOf.exists_contDiffOn_mulVec_eq`).
* If `J` is moreover invertible and `x₀ ≠ 0`, the same holds with `g x *ᵥ x₀ = x`
  (`Matrix.unitaryGroupOf.exists_contDiffOn_mulVec_self_eq`). This has content only for isotropic
  `x₀`, whose orbit consists of isotropic vectors.

Neither statement assumes that `x₀` is isotropic: if it is not, a neighbourhood of `x₀` contains no
isotropic vector and the constant map `1` is a section.

The section is explicit. For `x` near `x₀`, `g x` is the quasi-reflection along `x - y₀` with
parameter `s(x) = ⟨x, x⟩ / 2 - ⟨x, y₀⟩` (`Matrix.unitaryGroupOf.quasiReflection`), the matrix
`1 - s(x)⁻¹ • (x - y₀) (star (x - y₀) ᵥ* J)`. It lies in `U(J)` for every `x`, its entries are
rational functions of the coordinates of `x` and their conjugates with denominator `s(x)`, and it
sends `y₀` to `x` when `x` is isotropic and `s(x) = -⟨x, y₀⟩` is nonzero
(`Matrix.unitaryGroupOf.quasiReflection_sub_mulVec_of_isotropic`). For the second statement, an
isotropic partner `y₀` of `x₀` with `⟨y₀, x₀⟩ = 1`
(`Matrix.exists_comp_dotProduct_mulVec_eq_zero_and_eq_one`) gives a section `g` carrying `y₀`, and
`x ↦ g x * (g x₀)⁻¹` carries `x₀`.

Smoothness is stated for the matrix entries, so that it does not depend on a choice of norm on
matrices; over the finite index type it is equivalent to smoothness for any such norm
(`contDiffOn_pi`).

## Main results

* `Matrix.unitaryGroupOf.exists_contDiffOn_mulVec_eq`: smooth local sections of the map
  `g ↦ g y₀`, for isotropic `y₀`, near a vector `x₀` with `⟨y₀, x₀⟩ ≠ 0`.
* `Matrix.unitaryGroupOf.exists_contDiffOn_mulVec_self_eq`: smooth local sections, over the
  isotropic vectors near a nonzero `x₀`, of the map `g ↦ g x₀`, for invertible `J` (with content
  only when `x₀` is isotropic).

## Attribution

The statements follow `New.Exchange.exists_contDiff_carrying_isotropic` and
`New.Exchange.exists_contDiff_eventually_mulVec_eq` of grh-lean
(https://github.com/lsernau/grh-lean, Apache 2.0, Copyright 2026 Anthropic, PBC), file
`src/Lib/Adelic/Witt/SmoothWitt.lean`, which construct such sections from quasi-reflections and
Eichler maps over `ℂ`. Here a single quasi-reflection with a parameter adapted to `x` is used, over
`ℝ` or `ℂ`, without assuming that `x₀` is isotropic, and with real-analytic entries.

## References

* J. Dieudonné, *La géométrie des groupes classiques*, Ergebnisse der Mathematik 5, Springer (1955),
  for Witt's extension theorem for Hermitian forms, of which these are smooth local forms for one
  isotropic vector.
-/

public section

open scoped ContDiff

namespace Matrix.unitaryGroupOf

variable {𝕜 : Type*} [RCLike 𝕜] {n : Type*} [Fintype n] [DecidableEq n] {J : Matrix n n 𝕜}

omit [DecidableEq n] in
/-- The parameter `x ↦ ⟨x, x⟩ / 2 - ⟨x, y⟩` of the section is a real-analytic function of `x`. -/
private theorem contDiff_half_dotProduct_sub_dotProduct (y : n → 𝕜) :
    ContDiff ℝ ω fun x : n → 𝕜 => star x ⬝ᵥ J *ᵥ x / 2 - star x ⬝ᵥ J *ᵥ y := by
  simp only [dotProduct, mulVec, Pi.star_apply]
  fun_prop

/-- The entries of the quasi-reflection along `x - y₀` with parameter `⟨x, x⟩ / 2 - ⟨x, y₀⟩` are
real-analytic functions of `x` where the parameter does not vanish. -/
private theorem contDiffOn_quasiReflection_sub_apply (hJ : J.IsHermitian) {y₀ : n → 𝕜}
    (hy₀ : star y₀ ⬝ᵥ J *ᵥ y₀ = 0) (i j : n) :
    ContDiffOn ℝ ω (fun x => ((quasiReflection hJ (x - y₀) _
        (add_star_half_dotProduct_sub_dotProduct hJ hy₀ x) : GL n 𝕜) : Matrix n n 𝕜) i j)
      {x | star x ⬝ᵥ J *ᵥ x / 2 - star x ⬝ᵥ J *ᵥ y₀ ≠ 0} := by
  simp only [val_quasiReflection, unitaryTransvection_def, Matrix.add_apply, Matrix.smul_apply,
    vecMulVec_apply, smul_eq_mul]
  refine contDiffOn_const.add
    (((contDiff_half_dotProduct_sub_dotProduct y₀).contDiffOn.inv fun x hx => hx).neg.mul ?_)
  simp only [vecMul, dotProduct, Function.comp_apply, Pi.sub_apply, map_sub, starRingEnd_apply]
  fun_prop

/-- Near a non-isotropic vector there are no isotropic vectors, so the constant map `1` satisfies
the section property over the isotropic vectors there for any vector `y`, vacuously. -/
private theorem exists_contDiffOn_mulVec_eq_of_ne_zero {x₀ : n → 𝕜}
    (hx₀ : star x₀ ⬝ᵥ J *ᵥ x₀ ≠ 0) (y : n → 𝕜) :
    ∃ N, IsOpen N ∧ x₀ ∈ N ∧ ∃ g : (n → 𝕜) → unitaryGroupOf J,
      (∀ i j, ContDiffOn ℝ ω (fun x => ((g x : GL n 𝕜) : Matrix n n 𝕜) i j) N) ∧
      ∀ x ∈ N, star x ⬝ᵥ J *ᵥ x = 0 → ((g x : GL n 𝕜) : Matrix n n 𝕜) *ᵥ y = x :=
  ⟨{x | star x ⬝ᵥ J *ᵥ x ≠ 0},
    isOpen_ne_fun (continuous_star.dotProduct (continuous_const.matrix_mulVec continuous_id))
      continuous_const, hx₀,
    fun _ => 1, fun _ _ => contDiffOn_const, fun _ hx hx' => absurd hx' hx⟩

/-- **Smooth local sections of the isotropic orbit.** Let `J` be Hermitian and `y₀` isotropic, and
let `x₀` be a vector with `⟨y₀, x₀⟩ ≠ 0`. Then there are an open neighbourhood `N` of `x₀` and a map
`g` to the unitary group of `J`, whose matrix entries are real-analytic (in particular smooth)
functions of the real coordinates on `N`, with `g x *ᵥ y₀ = x` for every isotropic `x ∈ N`. -/
theorem exists_contDiffOn_mulVec_eq (hJ : J.IsHermitian) {x₀ y₀ : n → 𝕜}
    (hy₀ : star y₀ ⬝ᵥ J *ᵥ y₀ = 0) (hxy : star y₀ ⬝ᵥ J *ᵥ x₀ ≠ 0) :
    ∃ N, IsOpen N ∧ x₀ ∈ N ∧ ∃ g : (n → 𝕜) → unitaryGroupOf J,
      (∀ i j, ContDiffOn ℝ ω (fun x => ((g x : GL n 𝕜) : Matrix n n 𝕜) i j) N) ∧
      ∀ x ∈ N, star x ⬝ᵥ J *ᵥ x = 0 → ((g x : GL n 𝕜) : Matrix n n 𝕜) *ᵥ y₀ = x := by
  by_cases hx₀ : star x₀ ⬝ᵥ J *ᵥ x₀ = 0
  swap
  · exact exists_contDiffOn_mulVec_eq_of_ne_zero hx₀ y₀
  have hs (x : n → 𝕜) (hx : star x ⬝ᵥ J *ᵥ x = 0) :
      star x ⬝ᵥ J *ᵥ x / 2 - star x ⬝ᵥ J *ᵥ y₀ = -(star x ⬝ᵥ J *ᵥ y₀) := by
    rw [hx, zero_div, zero_sub]
  refine ⟨{x | star x ⬝ᵥ J *ᵥ x / 2 - star x ⬝ᵥ J *ᵥ y₀ ≠ 0},
    isOpen_ne_fun (contDiff_half_dotProduct_sub_dotProduct y₀).continuous continuous_const, ?_,
    fun x => quasiReflection hJ (x - y₀) _ (add_star_half_dotProduct_sub_dotProduct hJ hy₀ x),
    contDiffOn_quasiReflection_sub_apply hJ hy₀, fun x hx hxx => ?_⟩
  · simpa [hs x₀ hx₀, hJ.star_dotProduct_mulVec_comm] using star_ne_zero.mpr hxy
  · exact quasiReflection_sub_mulVec_of_isotropic hJ hxx hy₀ (by simpa [hs x hxx] using hx)

/-- **Smooth local sections, over the isotropic vectors, of the orbit map of a nonzero vector.**
Let `J` be Hermitian and invertible and `x₀ ≠ 0`. Then there are an open neighbourhood `N` of `x₀`
and a map `g` to the unitary group of `J`, whose matrix entries are real-analytic (in particular
smooth) functions of the real coordinates on `N`, with `g x *ᵥ x₀ = x` for every isotropic
`x ∈ N`. This has content only when `x₀` is isotropic: otherwise `N` can be chosen to contain no
isotropic vector. -/
theorem exists_contDiffOn_mulVec_self_eq (hJ : J.IsHermitian) (hJ' : IsUnit J) {x₀ : n → 𝕜}
    (hx₀ : x₀ ≠ 0) :
    ∃ N, IsOpen N ∧ x₀ ∈ N ∧ ∃ g : (n → 𝕜) → unitaryGroupOf J,
      (∀ i j, ContDiffOn ℝ ω (fun x => ((g x : GL n 𝕜) : Matrix n n 𝕜) i j) N) ∧
      ∀ x ∈ N, star x ⬝ᵥ J *ᵥ x = 0 → ((g x : GL n 𝕜) : Matrix n n 𝕜) *ᵥ x₀ = x := by
  by_cases hiso : star x₀ ⬝ᵥ J *ᵥ x₀ = 0
  swap
  · exact exists_contDiffOn_mulVec_eq_of_ne_zero hiso x₀
  -- an isotropic partner `y₀` of `x₀`, from the hyperbolic pairs of a sesquilinear form
  obtain ⟨y₀, -, hy₀, -, hyx⟩ := exists_comp_dotProduct_mulVec_eq_zero_and_eq_one
    (starRingEnd_self_apply (R := 𝕜)) (by rw [one_smul, transpose_map_starRingEnd, hJ.eq])
    ((isUnit_iff_isUnit_det J).mp hJ').ne_zero
    (fun s hs => ⟨s / 2, by
      rw [one_mul] at hs
      rw [one_mul, map_div₀, hs, map_ofNat, add_halves]⟩) hx₀
    (by rwa [TauCeti.starRingEnd_comp_eq_star])
  rw [TauCeti.starRingEnd_comp_eq_star] at hy₀ hyx
  obtain ⟨N, hN, hx₀N, g, hg, hgy⟩ :=
    exists_contDiffOn_mulVec_eq hJ hy₀ (hyx ▸ one_ne_zero : star y₀ ⬝ᵥ J *ᵥ x₀ ≠ 0)
  have hinv : (((g x₀)⁻¹ : unitaryGroupOf J) : GL n 𝕜) *ᵥ x₀ = y₀ := calc
    _ = ((((g x₀ : GL n 𝕜)⁻¹ : GL n 𝕜) : Matrix n n 𝕜) *
          ((g x₀ : GL n 𝕜) : Matrix n n 𝕜)) *ᵥ y₀ := by
      rw [← mulVec_mulVec, hgy x₀ hx₀N hiso, Subgroup.coe_inv]
    _ = y₀ := by rw [Units.inv_mul, one_mulVec]
  refine ⟨N, hN, hx₀N, fun x => g x * (g x₀)⁻¹, fun i j => ?_, fun x hx hxx => ?_⟩
  · simp only [Subgroup.coe_mul, Units.val_mul, Matrix.mul_apply]
    exact ContDiffOn.sum fun l _ => (hg i l).mul contDiffOn_const
  · rw [Subgroup.coe_mul, Units.val_mul, ← mulVec_mulVec, hinv, hgy x hx hxx]

end Matrix.unitaryGroupOf
