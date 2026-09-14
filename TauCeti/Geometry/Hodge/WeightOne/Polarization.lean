/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Hodge.HodgeForm

/-!
# The Riemann bilinear relations in weight one

An effective Hodge structure of weight one has only the two Hodge components `H^{1,0}` and
`H^{0,1}`, and its Weil operator `C` restricts to a complex structure on the real form of its
lattice. For such a structure the Hodge–Riemann relations become the two classical **Riemann
bilinear relations**, which speak only about real vectors: an alternating integral form `Q`
polarizes the structure as soon as

* `Q (C x) (C y) = Q x y` for all real `x` and `y`, and
* `0 < Q (C x) x` for every nonzero real `x`.

Both relations are also necessary — the first is
`TauCeti.Hodge.IsPolarization.isOrthogonal_weilOperator` read on real vectors, and the second is
`TauCeti.Hodge.IsPolarization.integralFormBaseChange_weilOperator_self_pos`, which holds in
arbitrary weight — so together they characterize the polarizing forms. This is the shape in which a
Riemann form on a lattice with a complex structure polarizes the weight-one Hodge structure it
carries, as for the first cohomology of a complex torus.

Effectivity is what makes the two relations sufficient, and it is not decoration. Invariance of `Q`
under `C` forces two Hodge components to be orthogonal only when their degrees differ by an odd
number; in weight one those are exactly the pairs of degrees taken from `{0, 1}`, so a
non-effective weight-one structure, which also has components `H^{p,1-p}` with `p ∉ {0, 1}`, is not
covered.

## Main declarations

* `TauCeti.Hodge.isPolarization_of_isOrthogonal_weilOperator_of_pos`: the Riemann bilinear
  relations polarize an effective weight-one Hodge structure.

The conventions are those pinned in `TauCeti.Hodge.IsPolarization`; the relations follow Voisin,
*Hodge Theory and Complex Algebraic Geometry I*, §7.1.2, and Peters–Steenbrink, *Mixed Hodge
Structures*, §2.
-/

public section

namespace TauCeti.Hodge

open scoped ComplexOrder

universe u v

variable {V : Type u} {Vℂ : Type v}
variable [AddCommGroup V] [AddCommGroup Vℂ] [Module ℂ Vℂ]
variable {ιℂ : V →ₗ[ℤ] Vℂ} {hℂ : IsBaseChange ℂ ιℂ} {Q : LinearMap.BilinForm ℤ V}

section WeightOne

variable {hs : HodgeStructure hℂ 1}

/-- The second Hodge–Riemann relation on `H^{1,0}`, from positivity on the real form. For `z` in
`H^{1,0}` the vector `v = z + conj z` is a nonzero real vector, and `Q (C v) v = 2 i Q z (conj z)`,
because `C` acts by `i` on `z` and by `-i` on `conj z` while `Q` kills both diagonal terms. -/
private theorem pos_I_mul_of_mem_piece_one
    (hskewℂ : ∀ x y : Vℂ, integralFormBaseChange hℂ Q y x = -integralFormBaseChange hℂ Q x y)
    (hpos : ∀ x ∈ realPoints (latticeConj hℂ), x ≠ 0 →
      0 < integralFormBaseChange hℂ Q (hs.weilOperator x) x)
    {z : Vℂ} (hz : z ∈ hs.piece 1) (hz0 : z ≠ 0) :
    0 < Complex.I * integralFormBaseChange hℂ Q z (latticeConj hℂ z) := by
  have hself : ∀ x : Vℂ, integralFormBaseChange hℂ Q x x = 0 := fun x ↦ by
    have h : (2 : ℂ) * integralFormBaseChange hℂ Q x x = 0 := by
      linear_combination hskewℂ x x
    simpa using h
  have hconj : latticeConj hℂ z ∈ hs.piece 0 := by simpa using hs.conj_mem_piece hz
  have hvmem : z + latticeConj hℂ z ∈ realPoints (latticeConj hℂ) := by
    rw [mem_realPoints, map_add, latticeConj_apply_apply, add_comm]
  have hvne : z + latticeConj hℂ z ≠ 0 := by
    intro hzero
    -- If `conj z = -z` then `C` acts on `z` by `i` and by `-i` at once, so `z = 0`.
    have hneg : latticeConj hℂ z = -z := by
      rw [add_comm] at hzero
      exact eq_neg_of_add_eq_zero_left hzero
    have h1 := hs.weilOperator_apply_of_mem_piece_zero hconj
    rw [hneg, map_neg, hs.weilOperator_apply_of_mem_piece_one hz, smul_neg, neg_neg] at h1
    have h3 : ((2 : ℂ) * Complex.I) • z = 0 := by
      rw [mul_smul, two_smul]
      nth_rewrite 1 [← h1]
      exact neg_add_cancel _
    have h4 := congrArg (fun w ↦ ((2 : ℂ) * Complex.I)⁻¹ • w) h3
    simp only [smul_smul, inv_mul_cancel₀ (by simp : (2 : ℂ) * Complex.I ≠ 0), one_smul,
      smul_zero] at h4
    exact hz0 h4
  have hCv : hs.weilOperator (z + latticeConj hℂ z) =
      Complex.I • z - Complex.I • latticeConj hℂ z := by
    rw [map_add, hs.weilOperator_apply_of_mem_piece_one hz,
      hs.weilOperator_apply_of_mem_piece_zero hconj, sub_eq_add_neg]
  have hval : integralFormBaseChange hℂ Q (hs.weilOperator (z + latticeConj hℂ z))
      (z + latticeConj hℂ z) =
      2 * (Complex.I * integralFormBaseChange hℂ Q z (latticeConj hℂ z)) := by
    rw [hCv]
    simp only [map_sub, map_add, LinearMap.sub_apply, map_smul,
      LinearMap.smul_apply, smul_eq_mul]
    rw [hself z, hself (latticeConj hℂ z), hskewℂ z (latticeConj hℂ z)]
    ring
  have hhalf : (0 : ℂ) < 2⁻¹ := by norm_num [Complex.pos_iff]
  have hfull := hpos _ hvmem hvne
  rw [hval] at hfull
  simpa [← mul_assoc] using mul_pos hhalf hfull

/-- **The Riemann bilinear relations polarize an effective weight-one Hodge structure.** Let `Q` be
a nondegenerate antisymmetric form on the lattice of an effective Hodge structure of weight one,
and let `C` be its Weil operator, a complex structure on the real form. If the complexification of
`Q` is invariant under `C` on real vectors, and is positive on the pair `(C x, x)` for every
nonzero real vector `x`, then `Q` polarizes the structure.

Invariance under `C` gives the first Hodge–Riemann relation: on `H^{1,0}` the operator `C` acts by
`i`, so invariance forces the form to vanish there, and in weight one that is the only relation to
check. Positivity on the real form gives the second: a nonzero class of `H^{1,0}` and its conjugate
add up to a nonzero real vector on which the hypothesis applies. -/
theorem isPolarization_of_isOrthogonal_weilOperator_of_pos (heff : hs.IsEffective)
    (hskew : ∀ x y, Q y x = -Q x y) (hnd : Q.Nondegenerate)
    (hinv : ∀ x ∈ realPoints (latticeConj hℂ), ∀ y ∈ realPoints (latticeConj hℂ),
      integralFormBaseChange hℂ Q (hs.weilOperator x) (hs.weilOperator y) =
        integralFormBaseChange hℂ Q x y)
    (hpos : ∀ x ∈ realPoints (latticeConj hℂ), x ≠ 0 →
      0 < integralFormBaseChange hℂ Q (hs.weilOperator x) x) :
    IsPolarization hℂ hs Q := by
  have hskewℂ : ∀ x y : Vℂ, integralFormBaseChange hℂ Q y x =
      -integralFormBaseChange hℂ Q x y := fun x y ↦ by
    simpa using integralFormBaseChange_apply_symm hℂ Q (k := -1) (by simpa using hskew) x y
  -- The real vectors span the complexification, so invariance under `C` holds everywhere.
  have hiso : ∀ x y : Vℂ,
      integralFormBaseChange hℂ Q (hs.weilOperator x) (hs.weilOperator y) =
        integralFormBaseChange hℂ Q x y := by
    have hspan : Submodule.span ℂ (realPoints (latticeConj hℂ) : Set Vℂ) = ⊤ :=
      span_realPoints_eq_top (latticeConj_involutive hℂ)
    have key : ((integralFormBaseChange hℂ Q ∘ₗ hs.weilOperator).compl₂ hs.weilOperator) =
        integralFormBaseChange hℂ Q :=
      LinearMap.ext_on hspan fun x hx ↦ LinearMap.ext_on hspan fun y hy ↦ by
        simpa using hinv x hx y hy
    intro x y
    simpa using DFunLike.congr_fun (DFunLike.congr_fun key x) y
  refine ⟨fun x y ↦ ?_, hnd, fun p x hx y hy ↦ ?_, fun p x hx hx0 ↦ ?_⟩
  · rw [hskew x y, Int.negOnePow_one]
    simp
  · rcases lt_trichotomy p 1 with hp | rfl | hp
    · have hbot : hs.F (1 + 1 - p) = ⊥ := heff.F_eq_bot_of_weight_lt (by omega)
      rw [hbot, Submodule.mem_bot] at hy
      simp [hy]
    · have hx1 : x ∈ hs.piece 1 := by rwa [heff.piece_weight_eq_F]
      have hy1 : y ∈ hs.piece 1 := by
        rw [heff.piece_weight_eq_F]
        norm_num at hy
        exact hy
      have h := hiso x y
      rw [hs.weilOperator_apply_of_mem_piece_one hx1,
        hs.weilOperator_apply_of_mem_piece_one hy1] at h
      simp only [map_smul, LinearMap.smul_apply, smul_eq_mul, ← mul_assoc,
        Complex.I_mul_I] at h
      have h2 : (2 : ℂ) * integralFormBaseChange hℂ Q x y = 0 := by linear_combination -h
      simpa using h2
    · have hbot : hs.F p = ⊥ := heff.F_eq_bot_of_weight_lt (by omega)
      rw [hbot, Submodule.mem_bot] at hx
      simp [hx]
  · rcases eq_or_ne p 1 with rfl | hp1
    · norm_num
      exact pos_I_mul_of_mem_piece_one hskewℂ hpos hx hx0
    rcases eq_or_ne p 0 with rfl | hp0
    · have hconj : latticeConj hℂ x ∈ hs.piece 1 := by simpa using hs.conj_mem_piece hx
      have hne : latticeConj hℂ x ≠ 0 := fun h0 ↦ hx0 (by
        have h := congrArg (latticeConj hℂ) h0
        simpa using h)
      have h := pos_I_mul_of_mem_piece_one hskewℂ hpos hconj hne
      rw [latticeConj_apply_apply, hskewℂ x (latticeConj hℂ x)] at h
      -- The scalar in the target is `i ^ (2 * 0 - 1) = i⁻¹ = -i`.
      have hI : (Complex.I : ℂ) ^ (2 * (0 : ℤ) - 1) = -Complex.I := by
        norm_num [Complex.inv_I]
      rw [hI]
      convert h using 1
      ring
    · have hbot : hs.piece p = ⊥ := by
        rcases lt_or_ge p 0 with hneg | hnonneg
        · exact heff.piece_eq_bot_of_neg hneg
        · exact heff.piece_eq_bot_of_weight_lt (by omega)
      rw [hbot, Submodule.mem_bot] at hx
      exact absurd hx hx0

end WeightOne

end TauCeti.Hodge
