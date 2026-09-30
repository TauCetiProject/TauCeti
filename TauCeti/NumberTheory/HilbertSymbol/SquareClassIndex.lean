/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.FieldTheory.SquareClassGroup.Multiplicative
public import TauCeti.NumberTheory.HilbertSymbol.NormSubgroup

import TauCeti.Algebra.Group.PowMonoidHom
import TauCeti.Algebra.Group.Units.Basic

/-!
# The quadratic norm index through square classes

Let `K` be a field with `2 ≠ 0`, let `a : Kˣ` be a nonsquare, and let `L = K(√a)` be the quadratic
algebra `QuadraticAlgebra K a 0`, which is then a field. The inclusion `Kˣ → Lˣ` and the norm
`Lˣ → Kˣ` induce homomorphisms of square-class groups

`Kˣ/(Kˣ)² → Lˣ/(Lˣ)² → Kˣ/(Kˣ)²`.

The first has kernel `{1, [a]}`, because an element of `K` that is a square in `L` has the form
`x²` or `a y²` with `x, y ∈ K`. Its image is the kernel of the second, which is the quadratic case
of Hilbert's Theorem 90: an element `w` of norm one is either `-1`, which lies in `K`, or
`u / ū = u² / N(u)` with `u = 1 + w`. The image of the second map is the image of the norm
subgroup `N = N_{L/K}(Lˣ)`, which contains the squares. Counting the three groups gives

`2 · (Kˣ : N) · #(Lˣ/(Lˣ)²) = #(Kˣ/(Kˣ)²)²`.

No finiteness is assumed: indices and cardinalities are `Subgroup.index` and `Nat.card`, which
are `0` for infinite groups. Over a field whose two square-class groups are finite and known, such
as a nonarchimedean local field in which `2 ≠ 0`, the identity determines the index of the norm
subgroup.

## Main results

* `TauCeti.two_mul_index_quadraticNormSubgroup_mul_card_squareClass`: the identity above.

## References

* T. Y. Lam, *Introduction to Quadratic Forms over Fields*, Chapter VII, §3, for the exact
  sequence of square-class groups of a quadratic extension.
-/

public section

namespace TauCeti

variable {K : Type*} [Field K]

/-- The map `K(√a)ˣ/(K(√a)ˣ)² → Kˣ/(Kˣ)²` induced by the norm. -/
private noncomputable def squareClassNorm (a : K) :
    (QuadraticAlgebra K a 0)ˣ ⧸ Subgroup.square (QuadraticAlgebra K a 0)ˣ →*
      MultiplicativeSquareClassGroup K :=
  QuotientGroup.map _ _ (quadraticNormHom a) (MonoidHom.square_le_comap _)

/-- The image of the norm map on square classes is the image of the norm subgroup, so its index
is the index of the norm subgroup. -/
private theorem index_range_squareClassNorm (a : K) :
    (squareClassNorm a).range.index = (quadraticNormSubgroup a).index := by
  have hrange : (squareClassNorm a).range =
      (quadraticNormSubgroup a).map (QuotientGroup.mk' (Subgroup.square Kˣ)) := by
    rw [quadraticNormSubgroup_def]
    ext y
    constructor
    · rintro ⟨x, rfl⟩
      obtain ⟨z, rfl⟩ := QuotientGroup.mk_surjective x
      exact ⟨quadraticNormHom a z, ⟨z, rfl⟩, (QuotientGroup.map_mk _ _ _ _ z).symm⟩
    · rintro ⟨_, ⟨z, rfl⟩, rfl⟩
      exact ⟨z, QuotientGroup.map_mk _ _ _ _ z⟩
  rw [hrange, Subgroup.index_map_eq _ (QuotientGroup.mk'_surjective _)]
  rw [QuotientGroup.ker_mk']
  exact square_le_quadraticNormSubgroup a

variable (a : Kˣ)

private theorem quadraticNormHom_units_map_algebraMap (c : Kˣ) :
    quadraticNormHom (a : K)
        (Units.map (algebraMap K (QuadraticAlgebra K (a : K) 0)).toMonoidHom c) = c ^ 2 := by
  ext
  simp [QuadraticAlgebra.norm_algebraMap]

variable {a}

/-- An element of `Kˣ` that becomes a square in `K(√a)` is a square or `a` times a square. -/
private theorem isSquare_or_isSquare_inv_mul_of_isSquare_units_map (h2 : (2 : K) ≠ 0) {c : Kˣ}
    (hc : IsSquare (Units.map (algebraMap K (QuadraticAlgebra K (a : K) 0)).toMonoidHom c)) :
    IsSquare c ∨ IsSquare (a⁻¹ * c) := by
  obtain ⟨z, hz⟩ := hc
  have hre := congrArg QuadraticAlgebra.re (congrArg Units.val hz)
  have him := congrArg QuadraticAlgebra.im (congrArg Units.val hz)
  simp only [Units.coe_map, RingHom.toMonoidHom_eq_coe, MonoidHom.coe_ofClass,
    Units.val_mul, QuadraticAlgebra.re_mul, QuadraticAlgebra.im_mul,
    QuadraticAlgebra.algebraMap_re, QuadraticAlgebra.algebraMap_im, zero_mul, add_zero] at hre him
  -- The coefficient of `√a` in `z²` is `2 z.re z.im`, so one of the two coordinates vanishes.
  have hzero : (z : QuadraticAlgebra K a 0).re = 0 ∨ (z : QuadraticAlgebra K a 0).im = 0 := by
    have : 2 * ((z : QuadraticAlgebra K a 0).re * (z : QuadraticAlgebra K a 0).im) = 0 := by
      linear_combination -him
    simpa [h2] using this
  rcases hzero with hre0 | him0
  · right
    refine isSquare_units_val_iff.mp ⟨(z : QuadraticAlgebra K a 0).im, ?_⟩
    rw [hre0] at hre
    simp only [Units.val_mul, Units.val_inv_eq_inv_val, hre]
    field_simp
    ring
  · left
    exact isSquare_units_val_iff.mp ⟨(z : QuadraticAlgebra K a 0).re, by simpa [him0] using hre⟩

variable [Fact (¬IsSquare (a : K))]

/-- The kernel of `Kˣ/(Kˣ)² → K(√a)ˣ/(K(√a)ˣ)²` has two elements, `1` and the class of `a`. -/
private theorem natCard_ker_multiplicativeSquareClassMap (h2 : (2 : K) ≠ 0) :
    Nat.card (algebraMap K (QuadraticAlgebra K (a : K) 0)).multiplicativeSquareClassMap.ker =
      2 := by
  have ha : ¬IsSquare a := isSquare_units_val_iff.not.mp Fact.out
  let x : MultiplicativeSquareClassGroup K := a
  have hx : x ≠ 1 := fun h ↦ ha ((QuotientGroup.eq_one_iff (N := Subgroup.square Kˣ) a).mp h)
  have hx2 : x ^ 2 = 1 := (QuotientGroup.eq_one_iff (N := Subgroup.square Kˣ) (a ^ 2)).mpr
    ⟨a, sq a⟩
  have hker : (algebraMap K (QuadraticAlgebra K (a : K) 0)).multiplicativeSquareClassMap.ker =
      Subgroup.zpowers x := by
    apply le_antisymm
    · intro y hy
      obtain ⟨c, rfl⟩ := QuotientGroup.mk_surjective y
      rw [MonoidHom.mem_ker, RingHom.multiplicativeSquareClassMap_mk] at hy
      rcases isSquare_or_isSquare_inv_mul_of_isSquare_units_map h2
          ((QuotientGroup.eq_one_iff _).mp hy) with hc | hc
      · rw [(QuotientGroup.eq_one_iff (N := Subgroup.square Kˣ) c).mpr hc]
        exact one_mem _
      · rw [show (c : MultiplicativeSquareClassGroup K) = x from
          ((QuotientGroup.eq (s := Subgroup.square Kˣ)).mpr hc).symm]
        exact Subgroup.mem_zpowers x
    · rw [Subgroup.zpowers_le, MonoidHom.mem_ker, RingHom.multiplicativeSquareClassMap_mk]
      -- `a` is the square of the square-root generator `√a = ⟨0, 1⟩` of `K(√a)`.
      refine (QuotientGroup.eq_one_iff (N := Subgroup.square _) _).mpr
        ⟨Units.mk0 ⟨0, 1⟩ fun h ↦ one_ne_zero (congrArg QuadraticAlgebra.im h), ?_⟩
      ext <;> simp
  rw [hker, Nat.card_zpowers, orderOf_eq_prime hx2 hx]

/-- The image of `Kˣ/(Kˣ)² → K(√a)ˣ/(K(√a)ˣ)²` is the kernel of the norm map on square classes.
This is the quadratic case of Hilbert's Theorem 90. -/
private theorem range_multiplicativeSquareClassMap :
    (algebraMap K (QuadraticAlgebra K (a : K) 0)).multiplicativeSquareClassMap.range =
      (squareClassNorm (a : K)).ker := by
  apply le_antisymm
  · rintro _ ⟨y, rfl⟩
    obtain ⟨c, rfl⟩ := QuotientGroup.mk_surjective y
    rw [MonoidHom.mem_ker, RingHom.multiplicativeSquareClassMap_mk, squareClassNorm,
      QuotientGroup.map_mk, quadraticNormHom_units_map_algebraMap]
    exact (QuotientGroup.eq_one_iff _).mpr ⟨c, sq c⟩
  · intro y hy
    obtain ⟨z, rfl⟩ := QuotientGroup.mk_surjective y
    rw [MonoidHom.mem_ker, squareClassNorm, QuotientGroup.map_mk] at hy
    obtain ⟨d, hd⟩ := (QuotientGroup.eq_one_iff _).mp hy
    -- `w = z / d` has norm one. Hilbert 90 is proved by hand here: Mathlib's
    -- `groupCohomology.exists_div_of_norm_eq_one` needs `K(√a)/K` as a Galois extension with a
    -- chosen generator of its Galois group, while the quadratic computation is two lines.
    set w : (QuadraticAlgebra K a 0)ˣ :=
      z * (Units.map (algebraMap K (QuadraticAlgebra K (a : K) 0)).toMonoidHom d)⁻¹ with hw_def
    have hzw : (z : QuadraticAlgebra K a 0) = w * algebraMap K _ (d : K) := by
      simp [hw_def]
    have hw : (w : QuadraticAlgebra K a 0) * star (w : QuadraticAlgebra K a 0) = 1 := by
      have hnorm : quadraticNormHom (a : K) w = 1 := by
        rw [hw_def, map_mul, map_inv, quadraticNormHom_units_map_algebraMap, hd, sq,
          mul_inv_cancel]
      rw [← QuadraticAlgebra.algebraMap_norm_eq_mul_star, ← quadraticNormHom_apply, hnorm,
        Units.val_one, map_one]
    by_cases hw1 : (w : QuadraticAlgebra K a 0) = -1
    · -- `z = -d` already lies in `K`.
      refine ⟨QuotientGroup.mk (-d), ?_⟩
      rw [RingHom.multiplicativeSquareClassMap_mk]
      congr 1
      ext : 1
      simp [hzw, hw1]
    · -- Otherwise `u = 1 + w` satisfies `w ū = u`, so `z = (d / N(u)) · u²`.
      have hu : (1 + w : QuadraticAlgebra K a 0) ≠ 0 := by
        intro h
        exact hw1 (eq_neg_of_add_eq_zero_right h)
      set u : QuadraticAlgebra K a 0 := 1 + w with hu_def
      have hstar : star u ≠ 0 := fun h ↦ hu (by simpa using congrArg star h)
      have hkey : (z : QuadraticAlgebra K a 0) * star u = algebraMap K _ (d : K) * u := by
        rw [hzw, hu_def, star_add, star_one]
        linear_combination (algebraMap K (QuadraticAlgebra K a 0) (d : K)) * hw
      let U : (QuadraticAlgebra K a 0)ˣ := Units.mk0 u hu
      refine ⟨QuotientGroup.mk (d * (quadraticNormHom (a : K) U)⁻¹), ?_⟩
      rw [RingHom.multiplicativeSquareClassMap_mk, QuotientGroup.eq]
      refine ⟨U, (inv_mul_eq_iff_eq_mul.mpr ?_)⟩
      ext : 1
      simp only [Units.val_mul, Units.coe_map, RingHom.toMonoidHom_eq_coe, MonoidHom.coe_ofClass,
        map_mul, map_inv₀, Units.val_inv_eq_inv_val, quadraticNormHom_apply,
        Units.val_mk0, U, QuadraticAlgebra.algebraMap_norm_eq_mul_star]
      field_simp
      exact hkey

variable (a) in
/-- **The norm index of a quadratic extension through square classes.** If `2 ≠ 0` in `K` and
`a : Kˣ` is not a square, then `2 · (Kˣ : N) · #(Lˣ/(Lˣ)²) = #(Kˣ/(Kˣ)²)²`, where `L = K(√a)` and
`N` is the subgroup of norms from `L`. -/
theorem two_mul_index_quadraticNormSubgroup_mul_card_squareClass (h2 : (2 : K) ≠ 0) :
    2 * (quadraticNormSubgroup (a : K)).index *
        Nat.card (MultiplicativeSquareClassGroup (QuadraticAlgebra K (a : K) 0)) =
      Nat.card (MultiplicativeSquareClassGroup K) ^ 2 := by
  have hK :=
    (algebraMap K (QuadraticAlgebra K (a : K) 0)).multiplicativeSquareClassMap.ker.card_mul_index
  have hL := (squareClassNorm (a : K)).ker.card_mul_index
  have hN := (squareClassNorm (a : K)).range.card_mul_index
  rw [Subgroup.index_ker, natCard_ker_multiplicativeSquareClassMap h2,
    range_multiplicativeSquareClassMap] at hK
  rw [Subgroup.index_ker] at hL
  rw [index_range_squareClassNorm] at hN
  rw [← hL, ← hK]
  rw [← hK] at hN
  calc _ = 2 * Nat.card (squareClassNorm (a : K)).ker *
        (Nat.card (squareClassNorm (a : K)).range * (quadraticNormSubgroup (a : K)).index) := by
        ring
    _ = _ := by rw [hN, sq]

end TauCeti
