/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Matrix.Order
public import Mathlib.GroupTheory.GroupAction.Quotient
public import Mathlib.Topology.Instances.Matrix
public import TauCeti.Order.Filter.Cofinite.Basic
import TauCeti.Analysis.Matrix.PosSemidef.Basic
import TauCeti.Analysis.PositiveDefinite.Kernel.Kolmogorov

/-!
# Restriction, limits, zero extension and induction of positive-definite functions

A function `φ : G → 𝕜` on a group, valued in an `RCLike` field `𝕜`, is positive definite when
`∑ᵢ ∑ⱼ conj (cᵢ) cⱼ φ (gᵢ⁻¹ gⱼ) ≥ 0` for all finite families, that is, when the kernel
`(g, h) ↦ φ (g⁻¹ * h)` is positive semidefinite in the sense of Mathlib's `Matrix.PosSemidef`.
This file records basic norm and real-part bounds for normalized (`φ 1 = 1`) positive-definite
functions and proves that positive-definite functions on discrete groups are stable under the
operations used to pass between a group and its subgroups:

* restriction along a group homomorphism, in particular to a subgroup;
* pointwise limits along any nontrivial filter;
* extension by zero from a subgroup `H` to `G`;
* induction from a subgroup `H` of finite index: for a section `s` of `G → G ⧸ H`, the function
  `g ↦ [G : H]⁻¹ ∑_{x ∈ G ⧸ H} φ₀ ((s (g • x))⁻¹ * g * s x)`, with `φ₀` the extension of `φ`
  by zero. Its arguments `(s (g • x))⁻¹ * g * s x` lie in `H`; it agrees with `φ` at `1`, vanishes
  at infinity when `φ` does, and is uniformly close to `1` on `g` when `φ` is close to `1` at
  the finitely many points `(s (g • x))⁻¹ * g * s x`. When `s` fixes the identity coset and `φ` is
  normalized positive definite, `[G : H] * (1 - re (inducedFun s φ h))` dominates `1 - re (φ h)`
  for every `h ∈ H`.

Pointwise products are covered by Mathlib's Schur product theorem
`Matrix.PosSemidef.hadamard`, since the kernel of `φ * ψ` is the Hadamard product of the kernels.

Extension by zero and induction are the two ways a positive-definite function on a subgroup
yields one on the whole group, and they carry vanishing at infinity along. They give the
permanence of the Haagerup property under increasing unions and finite-index overgroups.

## Main declarations

* `Matrix.IsHermitian.apply_inv_eq_star`: conjugate symmetry `φ g⁻¹ = star (φ g)` for functions
  with Hermitian kernel `(g, h) ↦ φ (g⁻¹ * h)`.
* `Matrix.PosSemidef.norm_apply_le_one`, `Matrix.PosSemidef.one_sub_re_nonneg`,
  `Matrix.PosSemidef.norm_sub_one_sq_le`: norm and real-part bounds for normalized positive-definite
  functions.
* `Matrix.PosSemidef.sqrt_re_one_sub_re_mul_le`: subadditivity (triangle inequality) of
  `g ↦ √(re (φ 1) - re (φ g))` for positive-definite functions on a group.
* `Matrix.PosSemidef.comp_monoidHom`: restriction along a group homomorphism.
* `TauCeti.posSemidef_inv_mul_of_tendsto`: pointwise limits.
* `Matrix.PosSemidef.extend_subtype`: extension by zero from a subgroup.
* `TauCeti.inducedFun`: the function induced from a subgroup of finite index along a section,
  with `TauCeti.posSemidef_inducedFun`, `TauCeti.inducedFun_one`,
  `TauCeti.tendsto_inducedFun_cofinite`, `TauCeti.norm_inducedFun_sub_one_lt`,
  `TauCeti.card_mul_one_sub_re_inducedFun` and
  `TauCeti.one_sub_re_le_card_mul_one_sub_re_inducedFun`.

## References

* C. Anantharaman and S. Popa, *An Introduction to II₁ Factors*, §16.1.
* P.-A. Cherix, M. Cowling, P. Jolissaint, P. Julg and A. Valette, *Groups with the Haagerup
  property*, Progress in Mathematics 197, Birkhäuser (2001).
* B. Bekka, P. de la Harpe and A. Valette, *Kazhdan's Property (T)*, Appendix C.
-/

public section

noncomputable section

open Filter Matrix Topology
open scoped ComplexOrder

namespace Matrix.IsHermitian

/-- For a function `φ : G → R` whose kernel `(g, h) ↦ φ (g⁻¹ * h)` is Hermitian,
`φ g⁻¹ = star (φ g)`. -/
theorem apply_inv_eq_star {R G : Type*} [Star R] [DivInvOneMonoid G] {φ : G → R}
    (h : (of fun g h : G ↦ φ (g⁻¹ * h)).IsHermitian) (g : G) :
    φ g⁻¹ = star (φ g) := by
  simpa using (h.apply g 1).symm

end Matrix.IsHermitian

namespace Matrix.PosSemidef

variable {𝕜 G K : Type*} [RCLike 𝕜] [Group G] [Group K]

/-- A normalized positive-definite function on a group is bounded by `1` in norm. -/
theorem norm_apply_le_one {φ : G → 𝕜} (hφ : (of fun g h : G ↦ φ (g⁻¹ * h)).PosSemidef)
    (h1 : φ 1 = 1) (g : G) : ‖φ g‖ ≤ 1 := by
  simpa using hφ.norm_le_one_of_apply_self_eq_one (a := 1) (b := g) (by simp [h1]) (by simp [h1])

/-- For a normalized positive-definite function `φ` on a group, `0 ≤ 1 - re (φ g)`. -/
theorem one_sub_re_nonneg {φ : G → 𝕜} (hφ : (of fun g h : G ↦ φ (g⁻¹ * h)).PosSemidef)
    (h1 : φ 1 = 1) (g : G) : 0 ≤ 1 - RCLike.re (φ g) := by
  linarith [RCLike.re_le_norm (φ g), hφ.norm_apply_le_one h1 g]

/-- For a normalized positive-definite function `φ` on a group,
`‖φ g - 1‖ ^ 2 ≤ 2 * (1 - re (φ g))`. -/
theorem norm_sub_one_sq_le {φ : G → 𝕜} (hφ : (of fun g h : G ↦ φ (g⁻¹ * h)).PosSemidef)
    (h1 : φ 1 = 1) (g : G) : ‖φ g - 1‖ ^ 2 ≤ 2 * (1 - RCLike.re (φ g)) := by
  have hnorm : RCLike.re (φ g) ^ 2 + RCLike.im (φ g) ^ 2 ≤ 1 := by
    have h := pow_le_pow_left₀ (norm_nonneg (φ g)) (hφ.norm_apply_le_one h1 g) 2
    rwa [← RCLike.normSq_eq_def', RCLike.normSq_apply, ← sq, ← sq, one_pow] at h
  rw [← RCLike.normSq_eq_def', RCLike.normSq_apply]
  simp only [map_sub, RCLike.one_re, RCLike.one_im, sub_zero]
  nlinarith

/-- **Triangle inequality for positive-definite functions.** For any positive-definite function
`φ : G → 𝕜`, `g ↦ √(re (φ 1) - re (φ g))` is subadditive:
`√(re (φ 1) - re (φ (g * h))) ≤ √(re (φ 1) - re (φ g)) + √(re (φ 1) - re (φ h))`. -/
theorem sqrt_re_one_sub_re_mul_le {φ : G → 𝕜}
    (hφ : (of fun x y : G ↦ φ (x⁻¹ * y)).PosSemidef) (g h : G) :
    Real.sqrt (RCLike.re (φ 1) - RCLike.re (φ (g * h))) ≤
      Real.sqrt (RCLike.re (φ 1) - RCLike.re (φ g)) +
        Real.sqrt (RCLike.re (φ 1) - RCLike.re (φ h)) := by
  have hdist (a b : G) :
      dist (hφ.kolmogorovFeature a) (hφ.kolmogorovFeature b) =
        Real.sqrt 2 * Real.sqrt (RCLike.re (φ 1) - RCLike.re (φ (a⁻¹ * b))) := by
    rw [dist_eq_norm, ← Real.sqrt_sq (norm_nonneg _), hφ.norm_kolmogorovFeature_sub_sq a b]
    simp only [of_apply, inv_mul_cancel]
    have hmul :
        RCLike.re (φ 1) - 2 * RCLike.re (φ (a⁻¹ * b)) + RCLike.re (φ 1) =
          2 * (RCLike.re (φ 1) - RCLike.re (φ (a⁻¹ * b))) := by ring
    rw [hmul, Real.sqrt_mul (by norm_num)]
  have htri := dist_triangle (hφ.kolmogorovFeature 1) (hφ.kolmogorovFeature g)
    (hφ.kolmogorovFeature (g * h))
  rw [hdist 1 (g * h), hdist 1 g, hdist g (g * h)] at htri
  simp only [inv_one, one_mul, inv_mul_cancel_left] at htri
  rw [← mul_add] at htri
  exact le_of_mul_le_mul_left htri (by positivity)

/-- The restriction of a positive-definite function on `G` along a group homomorphism `f : K →* G`
is positive definite. In particular, the restriction to a subgroup is positive definite. -/
theorem comp_monoidHom {φ : G → 𝕜} (hφ : (of fun g h : G ↦ φ (g⁻¹ * h)).PosSemidef)
    (f : K →* G) : (of fun a b : K ↦ φ (f (a⁻¹ * b))).PosSemidef := by
  convert hφ.submatrix f using 1
  ext a b
  simp

/-- **Extension by zero.** The extension by zero of a positive-definite function on a subgroup
`H` is a positive-definite function on `G`. -/
theorem extend_subtype {H : Subgroup G} {φ : H → 𝕜}
    (hφ : (of fun a b : H ↦ φ (a⁻¹ * b)).PosSemidef) :
    (of fun g h : G ↦ Function.extend Subtype.val φ 0 (g⁻¹ * h)).PosSemidef := by
  classical
  -- The `H`-coordinate of `g` relative to the chosen representative of the coset `gH`.
  let c : G → H := fun g ↦
    ⟨(g : G ⧸ H).out⁻¹ * g, QuotientGroup.eq.mp (QuotientGroup.out_eq' (g : G ⧸ H))⟩
  -- The kernel is the Hadamard product of the indicator of `gH = hH` with `φ (c g⁻¹ * c h)`.
  convert ((PosSemidef.diagonal (d := fun _ : G ⧸ H ↦ (1 : 𝕜)) fun _ ↦ zero_le_one).submatrix
    ((↑) : G → G ⧸ H)).hadamard (hφ.submatrix c) using 1
  ext g h
  simp only [of_apply, hadamard_apply, submatrix_apply, diagonal_apply]
  by_cases hgh : (g : G ⧸ H) = h
  · have hmem : g⁻¹ * h ∈ H := QuotientGroup.eq.mp hgh
    have hc : (c g)⁻¹ * c h = ⟨g⁻¹ * h, hmem⟩ := by
      ext
      simp [c, hgh, mul_assoc]
    rw [ite_eq_left hgh, one_mul, hc]
    exact Subtype.val_injective.extend_apply φ 0 ⟨g⁻¹ * h, hmem⟩
  · rw [ite_eq_right hgh, zero_mul, Function.extend_apply' _ _ _ fun ⟨a, ha⟩ ↦
      hgh (QuotientGroup.eq.mpr (ha ▸ a.property)), Pi.zero_apply]

end Matrix.PosSemidef

namespace TauCeti

variable {𝕜 G : Type*} [RCLike 𝕜] [Group G]

/-- A pointwise limit, along a nontrivial filter, of positive-definite functions on a group is
positive definite. -/
theorem posSemidef_inv_mul_of_tendsto {ι : Type*} {l : Filter ι} [l.NeBot] {φ : ι → G → 𝕜}
    {ψ : G → 𝕜} (hφ : ∀ i, (of fun g h : G ↦ φ i (g⁻¹ * h)).PosSemidef)
    (hψ : ∀ g, Tendsto (fun i ↦ φ i g) l (𝓝 (ψ g))) :
    (of fun g h : G ↦ ψ (g⁻¹ * h)).PosSemidef :=
  isClosed_setOfPred_posSemidef.mem_of_tendsto
    (tendsto_pi_nhds.mpr fun g ↦ tendsto_pi_nhds.mpr fun h ↦ hψ (g⁻¹ * h))
    (Eventually.of_forall hφ)

variable {H : Subgroup G}

/-- For a section `s` of the projection `G → G ⧸ H`, the element `(s (g • x))⁻¹ * g * s x` lies in
`H`: both `s (g • x)` and `g * s x` represent the coset `g • x`. -/
theorem inv_mul_mul_mem_of_section {s : G ⧸ H → G} (hs : ∀ x, (s x : G ⧸ H) = x) (g : G)
    (x : G ⧸ H) : (s (g • x))⁻¹ * g * s x ∈ H := by
  rw [mul_assoc, ← QuotientGroup.eq, hs]
  nth_rewrite 1 [← hs x]
  exact MulAction.Quotient.smul_mk (H := H) g (s x)

variable [Fintype (G ⧸ H)]

/-- The function induced from a function `φ` on a subgroup `H` of finite index along a map
`s : G ⧸ H → G`, normally a section of the projection `G → G ⧸ H`: its value at `g` is the average
over the cosets `x` of the extension by zero of `φ` at `(s (g • x))⁻¹ * g * s x`. When `s` is a
section and `φ` is positive definite with `φ 1 = 1`, this is the coefficient of the induced unitary
representation at a unit vector spread evenly over the cosets. -/
def inducedFun (s : G ⧸ H → G) (φ : H → 𝕜) (g : G) : 𝕜 :=
  (Fintype.card (G ⧸ H) : 𝕜)⁻¹ * ∑ x, Function.extend Subtype.val φ 0 ((s (g • x))⁻¹ * g * s x)

/-- The defining formula of `TauCeti.inducedFun`. -/
theorem inducedFun_apply (s : G ⧸ H → G) (φ : H → 𝕜) (g : G) :
    inducedFun s φ g = (Fintype.card (G ⧸ H) : 𝕜)⁻¹ *
      ∑ x, Function.extend Subtype.val φ 0 ((s (g • x))⁻¹ * g * s x) :=
  (rfl)

/-- The induced function agrees with `φ` at the identity. -/
@[simp]
theorem inducedFun_one (s : G ⧸ H → G) (φ : H → 𝕜) : inducedFun s φ 1 = φ 1 := by
  have h1 : Function.extend Subtype.val φ 0 (1 : G) = φ 1 :=
    Subtype.val_injective.extend_apply φ 0 (1 : H)
  simp [inducedFun_apply, h1]

/-- **Induction.** The function induced from a positive-definite function on a subgroup of finite
index is positive definite, along any map `s : G ⧸ H → G`. -/
theorem posSemidef_inducedFun (s : G ⧸ H → G) {φ : H → 𝕜}
    (hφ : (of fun a b : H ↦ φ (a⁻¹ * b)).PosSemidef) :
    (of fun g h : G ↦ inducedFun s φ (g⁻¹ * h)).PosSemidef := by
  -- After the substitution `x = h⁻¹ • y`, the term of the coset `y` is the kernel of the
  -- extension by zero of `φ` evaluated at `g * s (g⁻¹ • y)` and `h * s (h⁻¹ • y)`.
  convert (posSemidef_sum Finset.univ fun y _ ↦
    hφ.extend_subtype.submatrix fun g ↦ g * s (g⁻¹ • y)).smul
      (by simp : (0 : 𝕜) ≤ (Fintype.card (G ⧸ H) : 𝕜)⁻¹) using 1
  refine Matrix.ext fun g h ↦ ?_
  simp only [Matrix.smul_apply, Matrix.sum_apply, of_apply, submatrix_apply, inducedFun_apply,
    smul_eq_mul]
  congr 1
  refine Fintype.sum_equiv (MulAction.toPerm h : Equiv.Perm (G ⧸ H)) _ _ fun x ↦ ?_
  simp [smul_smul, mul_assoc]

/-- The function induced from a function vanishing at infinity on a subgroup of finite index
vanishes at infinity. -/
theorem tendsto_inducedFun_cofinite (s : G ⧸ H → G) {φ : H → 𝕜}
    (hφ : Tendsto φ cofinite (𝓝 0)) : Tendsto (inducedFun s φ) cofinite (𝓝 0) := by
  -- Each `g ↦ (s (g • x))⁻¹ * g * s x` has finite fibres, since `g` is recovered from its value
  -- `k` as `s (g • x) * k * (s x)⁻¹` and `s` has finite range.
  have hfib (x : G ⧸ H) : Tendsto (fun g ↦ (s (g • x))⁻¹ * g * s x) cofinite cofinite := by
    refine Tendsto.cofinite_of_finite_preimage_singleton fun k ↦ Set.Finite.to_subtype <|
      ((Set.finite_range s).image fun r ↦ r * k * (s x)⁻¹).subset fun g hg ↦ ?_
    refine ⟨s (g • x), Set.mem_range_self _, ?_⟩
    rw [← Set.mem_singleton_iff.mp hg]
    group
  have hext : Tendsto (Function.extend Subtype.val φ 0) cofinite (𝓝 0) :=
    hφ.extend_cofinite Subtype.val (pure_le_nhds 0)
  have h := (tendsto_finsetSum Finset.univ fun x _ ↦ hext.comp (hfib x)).const_mul
    (Fintype.card (G ⧸ H) : 𝕜)⁻¹
  rw [Finset.sum_const_zero, mul_zero] at h
  exact h.congr fun g ↦ (inducedFun_apply s φ g).symm

/-- If `φ` is within `ε` of `1` at the finitely many elements `(s (g • x))⁻¹ * g * s x` of `H`, then
the induced function is within `ε` of `1` at `g`. -/
theorem norm_inducedFun_sub_one_lt {s : G ⧸ H → G} (hs : ∀ x, (s x : G ⧸ H) = x) {φ : H → 𝕜}
    {g : G} {ε : ℝ}
    (hφ : ∀ x, ‖φ ⟨(s (g • x))⁻¹ * g * s x, inv_mul_mul_mem_of_section hs g x⟩ - 1‖ < ε) :
    ‖inducedFun s φ g - 1‖ < ε := by
  have hcard : (Fintype.card (G ⧸ H) : 𝕜) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  have hext (x : G ⧸ H) : Function.extend Subtype.val φ 0 ((s (g • x))⁻¹ * g * s x) =
      φ ⟨_, inv_mul_mul_mem_of_section hs g x⟩ :=
    Subtype.val_injective.extend_apply φ 0 ⟨_, inv_mul_mul_mem_of_section hs g x⟩
  -- `inducedFun s φ g - 1` is the average of the differences `φ (…) - 1`.
  have heq : inducedFun s φ g - 1 = (Fintype.card (G ⧸ H) : 𝕜)⁻¹ *
      ∑ x, (φ ⟨_, inv_mul_mul_mem_of_section hs g x⟩ - 1) := by
    simp only [inducedFun_apply, hext, Finset.sum_sub_distrib, Finset.sum_const,
      Finset.card_univ, nsmul_eq_mul, mul_one, mul_sub, inv_mul_cancel₀ hcard]
  rw [heq, norm_mul, norm_inv, RCLike.norm_natCast]
  have hpos : (0 : ℝ) < Fintype.card (G ⧸ H) := Nat.cast_pos.mpr Fintype.card_pos
  rw [inv_mul_lt_iff₀ hpos]
  calc ‖∑ x, (φ ⟨_, inv_mul_mul_mem_of_section hs g x⟩ - 1)‖
      ≤ ∑ x, ‖φ ⟨_, inv_mul_mul_mem_of_section hs g x⟩ - 1‖ := norm_sum_le _ _
    _ < ∑ _x : G ⧸ H, ε := Finset.sum_lt_sum_of_nonempty Finset.univ_nonempty fun x _ ↦ hφ x
    _ = Fintype.card (G ⧸ H) * ε := by simp

/-- For a section `s` of `G → G ⧸ H`, `[G : H] * (1 - re (inducedFun s φ g))` equals the sum of
`1 - re (φ ((s (g • x))⁻¹ * g * s x))` over all cosets `x : G ⧸ H`. -/
theorem card_mul_one_sub_re_inducedFun {s : G ⧸ H → G} (hs : ∀ x, (s x : G ⧸ H) = x)
    (φ : H → 𝕜) (g : G) :
    (Fintype.card (G ⧸ H) : ℝ) * (1 - RCLike.re (inducedFun s φ g)) =
      ∑ x : G ⧸ H, (1 - RCLike.re (φ ⟨(s (g • x))⁻¹ * g * s x,
        inv_mul_mul_mem_of_section hs g x⟩)) := by
  have hpos : (0 : ℝ) < Fintype.card (G ⧸ H) := Nat.cast_pos.mpr Fintype.card_pos
  have hext (x : G ⧸ H) :
      Function.extend Subtype.val φ 0 ((s (g • x))⁻¹ * g * s x) =
        φ ⟨_, inv_mul_mul_mem_of_section hs g x⟩ :=
    Subtype.val_injective.extend_apply φ 0 ⟨_, inv_mul_mul_mem_of_section hs g x⟩
  have hre : RCLike.re (inducedFun s φ g) = (Fintype.card (G ⧸ H) : ℝ)⁻¹ *
      ∑ x : G ⧸ H, RCLike.re (φ ⟨_, inv_mul_mul_mem_of_section hs g x⟩) := by
    rw [inducedFun_apply]
    simp_rw [hext]
    rw [← RCLike.ofReal_natCast, ← RCLike.ofReal_inv, RCLike.re_ofReal_mul, map_sum]
  rw [hre, mul_sub, mul_one, mul_inv_cancel_left₀ hpos.ne', Finset.sum_sub_distrib]
  simp

/-- For a normalized positive-definite function `φ` on a finite-index subgroup `H` and a section
`s` fixing the identity coset, `1 - re (φ h)` is bounded above by
`[G : H] * (1 - re (inducedFun s φ h))` for every `h : H`. -/
theorem one_sub_re_le_card_mul_one_sub_re_inducedFun {s : G ⧸ H → G}
    (hs : ∀ x, (s x : G ⧸ H) = x) (hs1 : s ((1 : G) : G ⧸ H) = 1) {φ : H → 𝕜}
    (hφ : (of fun a b : H ↦ φ (a⁻¹ * b)).PosSemidef) (h1 : φ 1 = 1) (h : H) :
    1 - RCLike.re (φ h) ≤ (Fintype.card (G ⧸ H) : ℝ) * (1 - RCLike.re (inducedFun s φ h)) := by
  let x₀ : G ⧸ H := ((1 : G) : G ⧸ H)
  have hsmul : (h : G) • x₀ = x₀ := by
    dsimp only [x₀]
    rw [MulAction.Quotient.smul_mk, smul_eq_mul, mul_one]
    exact QuotientGroup.eq.mpr (by simp)
  have hx₀ : (⟨(s ((h : G) • x₀))⁻¹ * (h : G) * s x₀,
      inv_mul_mul_mem_of_section hs h x₀⟩ : H) = h := by
    ext
    dsimp only
    rw [hsmul, show s x₀ = 1 from hs1]
    simp
  rw [card_mul_one_sub_re_inducedFun hs φ h]
  simpa only [hx₀] using Finset.single_le_sum (f := fun x : G ⧸ H ↦
      1 - RCLike.re (φ ⟨(s ((h : G) • x))⁻¹ * (h : G) * s x,
        inv_mul_mul_mem_of_section hs h x⟩))
    (fun x _ ↦ hφ.one_sub_re_nonneg h1 _) (Finset.mem_univ x₀)

end TauCeti
