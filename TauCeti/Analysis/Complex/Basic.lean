/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Ring.Semireal.Defs
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Complex.Trigonometric
public import TauCeti.Analysis.RCLike.Basic

/-!
# Complex conjugation: invariant discs, symmetric norms and unit-norm quotients

Complex conjugation is an isometry fixing the real axis (Mathlib's `Complex.dist_conj_conj`), so
it maps every open or closed disc centred on the real axis to itself. Such discs are the natural
domains for reflection across the real axis, for instance the even reflection
`TauCeti.evenReflection`. A disc centred in the closed upper half-plane is not invariant, but
its mirror image meets the closed upper half-plane inside the disc itself, since a point of the
closed upper half-plane is at least as close to such a centre as to its mirror image
(`TauCeti.dist_le_dist_conj_of_im_nonneg`, `TauCeti.mem_ball_of_conj_mem_ball_of_im_nonneg`).
Any set becomes invariant under conjugation once its mirror image is added
(`TauCeti.conj_mem_union_preimage_conj`).
Conjugation maps the real axis into itself
(`TauCeti.mapsTo_conj_setOf_im_eq_zero`), whereas the rotation `z ↦ I z` does not
(`TauCeti.not_mapsTo_I_mul_setOf_im_eq_zero`). A function `f : ℂ → ℂ` that commutes with
conjugation is real on the real line (`TauCeti.ofReal_re_apply_of_forall_conj`).

Conjugation also preserves norms (Mathlib's `Complex.norm_conj`), so the norm of
`1 - conj w * z` is symmetric in `z` and `w` (`Complex.norm_one_sub_conj_mul_comm`). This
expression is the denominator of the Möbius automorphisms of the unit disc and of the
pseudo-hyperbolic expression. For `w` on the unit circle it has the norm of `z - w`
(`Complex.norm_one_sub_conj_mul`), and for `z` in the closed unit disc it lies in the closed right
half-plane (`Complex.re_one_sub_conj_mul_nonneg`; strictly inside it for `z` in the open disc,
`Complex.re_one_sub_conj_mul_pos`), by the bound `re (conj u * e) ≤ ‖u‖ ‖e‖`
(`Complex.re_conj_mul_le`).

As a continuous real-linear equivalence, conjugation is its own inverse (`Complex.conjCLE_symm`,
the counterpart of Mathlib's `Complex.conjLIE_symm`).

The real part of `exp (θ * I) ^ j` is `cos (j θ)` (`Complex.re_exp_ofReal_mul_I_pow`), the real
part of de Moivre's formula.

Inversion preserves both the open and closed right half-planes: `z⁻¹` has positive
(respectively nonnegative) real part exactly when `z` does (`Complex.inv_re_pos`,
`Complex.inv_re_nonneg`). Under a reflection symmetry `f (a - z) = c * conj (f (conj z))`, a
one-sided upper bound `Re ρ ≤ B` on all zeros of `f` confines every zero to the bounded vertical
strip `|Re ρ| ≤ max B |Re a - B|` (`TauCeti.abs_re_le_max_of_re_le_of_sub_conj`).

The map `y ↦ r² / y` (inversion in the circle of radius `r` followed by conjugation) satisfies
`‖conj x - r² / y‖ ≤ 3 ‖x - y‖` for `‖x‖ ≤ r ≤ ‖y‖` (`Complex.norm_conj_sub_sq_div_le`).

The scalar Cayley expression `1 + (z - conj z) / (r - z)` has unit norm for real `r`.
When `z ≠ r`, it is the quotient `(r - conj z) / (r - z)` of a complex number's conjugate
by itself; at `z = r`, Lean's totalized inverse gives value one.

Two integers whose images in `ℂ` are at distance less than `1` are equal, and on any compact
subset of `ℂ` avoiding the nonpositive integers `-ℕ`, the shifted norms `‖(n : ℂ) + c‖` have a
positive uniform lower bound (`IsCompact.exists_pos_le_norm_natCast_add`).

A shift `s + μ` stays off the real axis when `|Im μ| < |Im s|`
(`Complex.add_im_ne_zero_of_abs_im_lt`).

The canonical embedding of an `RCLike` field into `ℂ` is bundled as
`TauCeti.toComplexStarAlgHom`, so real star-algebra constructions can be transported to `ℂ`.

Dividing by a natural number does not increase the norm, so `‖(a z + b) / M‖ ≤ ‖a‖ C + ‖b‖`
whenever `‖z‖ ≤ C` (`Complex.norm_mul_add_div_natCast_le`). If `s + β` vanishes for no natural
number `s ≥ 1`, then `‖s + β‖ ≥ c s` for some `c > 0` and all `s ≥ 1`
(`Complex.exists_pos_mul_le_norm_natCast_add`).

The real coordinates `equivRealProdCLM : ℂ ≃L[ℝ] ℝ × ℝ` do not increase distances, so they map the
disc of radius `r` about `equivRealProdCLM.symm z₀` into the square `B_r(z₀)` of `ℝ × ℝ`
(`Complex.dist_equivRealProdCLM_le`).

A point of the closed disc of centre `c` and radius `ρ` has real part in `[c.re - ρ, c.re + ρ]`
(`Complex.re_mem_Icc_of_norm_sub_le`, and `Complex.re_mem_Icc_of_normSq_sub_le` for the disc
written as `normSq (w - c) ≤ ρ ^ 2` with `0 ≤ ρ`). Two complex numbers whose real parts have the
same absolute value compare in norm as their imaginary parts compare in absolute value
(`Complex.norm_le_norm_iff_abs_im_le_abs_im_of_abs_re_eq`). Hence moving up the vertical ray from a
point `z` of the closed upper half-plane does not decrease the norm
(`Complex.norm_le_norm_add_ofReal_mul_I`), and every point `z + s * I` of the vertical line
through such a `z` has norm at least `(‖z‖ + s) / 2`
(`Complex.norm_add_div_two_le_norm_add_ofReal_mul_I`).

The difference of the real parts of two points is at most their distance
(`Complex.re_sub_re_le_dist`), their squared distance is the sum of the squares of the differences
of their real and imaginary parts (`Complex.sq_dist_eq_re_im`), and if the distance is at most the
difference of the real parts then the imaginary parts agree
(`Complex.im_eq_im_of_dist_le_re_sub_re`). A closed disc `closedBall c R` with `θ + R < c.re`,
and an open disc `ball c R` with `θ + R ≤ c.re`, lie in the open half-plane `{z | θ < z.re}`
(`Complex.closedBall_subset_setOfPred_lt_re`, `Complex.ball_subset_setOfPred_lt_re`).

On the closed right half-plane `0 ≤ z.re`, `1 + z` has real part and norm at least `1`
(`Complex.one_le_re_one_add`, `Complex.one_le_norm_one_add`).

At height `1 ≤ |Im s|`, a point `s` is at distance at least `1` from `1`
(`Complex.one_le_norm_sub_one`), so `s ≠ 1` (`Complex.ne_one_of_one_le_abs_im`) and
`‖(s - 1)⁻¹‖ ≤ 1` (`Complex.norm_inv_sub_one_le_one`). For real `1 ≤ r`,
`‖(r : ℂ) - 1‖ = r - 1` (`Complex.norm_ofReal_sub_one`).

A real linear isometry from the plane maps `i` to a unit vector (`LinearIsometry.norm_map_I`).

There is no ring homomorphism from `ℂ` to a semireal semiring, such as `ℝ` or any linearly
ordered ring (`Complex.instIsEmptyRingHom`).

An `n`-th root (`n ≠ 0`) of a complex number `w` with `w * conj w = 1` has its inverse as
conjugate (`Complex.conj_eq_inv_of_pow_eq`).

For a finite set on one side of a vertical line, the distances from a point `⟨σ, t⟩` of the line
separate the points of the set for all but finitely many heights `t`
(`Set.Finite.finite_setOf_not_injOn_dist_complex_mk`).
-/

public section

open scoped ComplexConjugate

/-- A complex number and its inverse lie in the open right half-plane together. -/
theorem Complex.inv_re_pos {z : ℂ} : 0 < z⁻¹.re ↔ 0 < z.re := by
  rcases eq_or_ne z 0 with rfl | hz
  · simp
  · rw [inv_re, div_pos_iff_of_pos_right (normSq_pos.mpr hz)]

/-- A complex number and its inverse lie in the closed right half-plane together. -/
theorem Complex.inv_re_nonneg {z : ℂ} : 0 ≤ z⁻¹.re ↔ 0 ≤ z.re := by
  have hzero : z⁻¹.re = 0 ↔ z.re = 0 := by
    rcases eq_or_ne z 0 with rfl | hz
    · simp
    · simp [inv_re, hz]
  simpa only [le_iff_eq_or_lt, eq_comm (a := (0 : ℝ))] using or_congr hzero Complex.inv_re_pos

/-- The scalar Cayley expression has unit norm at real `r`, including when `z = r`
under the totalized inverse convention. -/
theorem Complex.norm_one_add_sub_conj_mul_inv_ofReal_sub (z : ℂ) (r : ℝ) :
    ‖1 + (z - conj z) * ((r : ℂ) - z)⁻¹‖ = 1 := by
  by_cases hne : (r : ℂ) - z = 0
  · simp [hne]
  have heq : 1 + (z - conj z) * ((r : ℂ) - z)⁻¹ =
      ((r : ℂ) - conj z) / ((r : ℂ) - z) := by
    field_simp
    ring
  have hnorm : ‖(r : ℂ) - conj z‖ = ‖(r : ℂ) - z‖ := by
    simpa using Complex.norm_conj ((r : ℂ) - z)
  rw [heq, norm_div, hnorm, div_self (norm_ne_zero_iff.mpr hne)]

open Complex Set in
/-- For a finite set on one side of a vertical line, distances to a point on the line distinguish
all members of the set except at finitely many heights. -/
theorem Set.Finite.finite_setOf_not_injOn_dist_complex_mk {T : Set ℂ} (hT : T.Finite) {σ : ℝ}
    (hleft : ∀ p ∈ T, p.re ≤ σ) :
    {t : ℝ | ¬ InjOn (fun p : ℂ ↦ dist (⟨σ, t⟩ : ℂ) p) T}.Finite := by
  -- Equate squared distances and solve for the height of the centre.
  let height (p q : ℂ) := ((σ - p.re) ^ 2 + p.im ^ 2 - ((σ - q.re) ^ 2 + q.im ^ 2)) /
    (2 * (p.im - q.im))
  refine ((hT.prod hT).image fun pq : ℂ × ℂ ↦ height pq.1 pq.2).subset ?_
  intro t ht
  simp only [mem_ofPred_eq, InjOn, not_forall] at ht
  obtain ⟨p, hp, q, hq, heq, hne⟩ := ht
  have hs := congrArg (fun d : ℝ ↦ d ^ 2) heq
  simp only [Complex.dist_eq, Complex.sq_norm, normSq_apply, sub_re, sub_im] at hs
  have him : p.im ≠ q.im := by
    intro hi
    have hre : (σ - p.re) ^ 2 = (σ - q.re) ^ 2 := by rw [hi] at hs; linarith
    have hr := (sq_eq_sq₀ (sub_nonneg.mpr (hleft p hp)) (sub_nonneg.mpr (hleft q hq))).mp hre
    exact hne (Complex.ext (by linarith) hi)
  refine ⟨(p, q), ⟨hp, hq⟩, ?_⟩
  exact (div_eq_iff (mul_ne_zero two_ne_zero (sub_ne_zero.mpr him))).2 (by nlinarith only [hs])

namespace TauCeti

/-- The canonical real star-algebra embedding of an `RCLike` field into `ℂ`. -/
noncomputable def toComplexStarAlgHom (𝕜 : Type*) [RCLike 𝕜] : 𝕜 →⋆ₐ[ℝ] ℂ where
  toFun x := (RCLike.re x : ℂ) + (RCLike.im x : ℂ) * Complex.I
  map_zero' := by simp
  map_one' := by simp
  map_add' := by intros; simp only [map_add, Complex.ofReal_add]; ring
  map_mul' := by
    intro x y
    simp only [RCLike.mul_re, RCLike.mul_im, Complex.ofReal_sub, Complex.ofReal_mul,
      Complex.ofReal_add]
    ring_nf
    rw [Complex.I_sq]
    ring
  commutes' := by intro r; simp
  map_star' := by intro x; simp [RCLike.star_def, mul_comm]

/-- The canonical complex embedding sends a scalar to its real and imaginary components. -/
@[simp]
theorem toComplexStarAlgHom_apply {𝕜 : Type*} [RCLike 𝕜] (x : 𝕜) :
    toComplexStarAlgHom 𝕜 x = (RCLike.re x : ℂ) + (RCLike.im x : ℂ) * Complex.I :=
  (rfl)

/-- The canonical complex embedding is the identity on `ℂ`. -/
@[simp]
theorem toComplexStarAlgHom_complex : toComplexStarAlgHom ℂ = .id ℝ ℂ := by
  ext z
  simp

/-- The canonical complex embedding of `ℝ` is the real scalar inclusion. -/
@[simp]
theorem toComplexStarAlgHom_real : toComplexStarAlgHom ℝ = RCLike.ofRealStarAlgHom ℂ := by
  ext r
  simp

/-- The canonical complex embedding preserves the real scalar inclusion. -/
@[simp]
theorem toComplexStarAlgHom_comp_ofRealStarAlgHom (𝕜 : Type*) [RCLike 𝕜] :
    (toComplexStarAlgHom 𝕜).comp (RCLike.ofRealStarAlgHom 𝕜) =
      RCLike.ofRealStarAlgHom ℂ := by
  ext r
  simp

/-- The canonical complex embedding has the same underlying function as `RCLike.map`. -/
theorem coe_toComplexStarAlgHom_eq_map (𝕜 : Type*) [RCLike 𝕜] :
    (toComplexStarAlgHom 𝕜 : 𝕜 → ℂ) = RCLike.map 𝕜 ℂ :=
  (rfl)

/-- The canonical complex embedding preserves distances. -/
theorem isometry_toComplexStarAlgHom (𝕜 : Type*) [RCLike 𝕜] :
    Isometry (toComplexStarAlgHom 𝕜) := by
  apply Isometry.of_dist_eq
  intro x y
  rw [dist_eq_norm, ← map_sub, toComplexStarAlgHom_apply, RCLike.norm_to_complex,
    dist_eq_norm]

/-- The canonical complex embedding is continuous. -/
@[continuity, fun_prop]
theorem continuous_toComplexStarAlgHom (𝕜 : Type*) [RCLike 𝕜] :
    Continuous (toComplexStarAlgHom 𝕜) :=
  (isometry_toComplexStarAlgHom 𝕜).continuous

open ComplexConjugate Metric

variable {x₀ z : ℂ} {r : ℝ}

/-- Conjugation maps an open disc centred on the real axis to itself. -/
theorem conj_mem_ball_of_im_eq_zero (hx₀ : x₀.im = 0) (hz : z ∈ ball x₀ r) :
    conj z ∈ ball x₀ r := by
  rwa [mem_ball, ← Complex.conj_eq_iff_im.2 hx₀, Complex.dist_conj_conj]

/-- Conjugation maps a closed disc centred on the real axis to itself. -/
theorem conj_mem_closedBall_of_im_eq_zero (hx₀ : x₀.im = 0) (hz : z ∈ closedBall x₀ r) :
    conj z ∈ closedBall x₀ r := by
  rwa [mem_closedBall, ← Complex.conj_eq_iff_im.2 hx₀, Complex.dist_conj_conj]

/-- A point `w` of the closed upper half-plane is at least as close to a point `z` of the closed
upper half-plane as to its mirror image `conj z`. -/
theorem dist_le_dist_conj_of_im_nonneg {w : ℂ} (hw : 0 ≤ w.im) (hz : 0 ≤ z.im) :
    dist w z ≤ dist w (conj z) := by
  rw [Complex.dist_eq_re_im, Complex.dist_eq_re_im]
  refine Real.sqrt_le_sqrt ?_
  simp only [Complex.conj_re, Complex.conj_im]
  nlinarith [mul_nonneg hw hz]

/-- If the mirror image of a point `z` of the closed upper half-plane lies in an open disc centred
in the closed upper half-plane, then so does `z`. -/
theorem mem_ball_of_conj_mem_ball_of_im_nonneg (hx₀ : 0 ≤ x₀.im) (hz : 0 ≤ z.im)
    (h : conj z ∈ ball x₀ r) : z ∈ ball x₀ r :=
  (dist_le_dist_conj_of_im_nonneg hz hx₀).trans_lt (by rwa [← Complex.dist_conj_comm])

/-- If the mirror image of a point `z` of the closed upper half-plane lies in a closed disc centred
in the closed upper half-plane, then so does `z`. -/
theorem mem_closedBall_of_conj_mem_closedBall_of_im_nonneg (hx₀ : 0 ≤ x₀.im) (hz : 0 ≤ z.im)
    (h : conj z ∈ closedBall x₀ r) : z ∈ closedBall x₀ r :=
  (dist_le_dist_conj_of_im_nonneg hz hx₀).trans (by rwa [← Complex.dist_conj_comm])

/-- The union of a set `s` with its preimage under conjugation is invariant under conjugation. -/
theorem conj_mem_union_preimage_conj {s : Set ℂ} (hz : z ∈ s ∪ conj ⁻¹' s) :
    conj z ∈ s ∪ conj ⁻¹' s := by
  simp only [Set.mem_union, Set.mem_preimage, Complex.conj_conj] at hz ⊢
  exact hz.symm

/-- A set `s` and its preimage under conjugation meet the closed upper half-plane in the same set,
provided every point of the closed upper half-plane whose mirror image lies in `s` lies in `s`,
as for discs centred in the closed upper half-plane
(`TauCeti.mem_ball_of_conj_mem_ball_of_im_nonneg`). -/
theorem setOfPred_le_im_inter_union_preimage_conj {s : Set ℂ}
    (hs : ∀ z, 0 ≤ z.im → conj z ∈ s → z ∈ s) :
    {z : ℂ | 0 ≤ z.im} ∩ (s ∪ conj ⁻¹' s) = {z : ℂ | 0 ≤ z.im} ∩ s :=
  subset_antisymm (fun z ⟨hz, hzs⟩ ↦ ⟨hz, hzs.elim id (hs z hz)⟩)
    (Set.inter_subset_inter_right _ Set.subset_union_left)

/-- Complex conjugation maps the real axis into itself. -/
theorem mapsTo_conj_setOf_im_eq_zero :
    Set.MapsTo (conj ·) {z : ℂ | z.im = 0} {z : ℂ | z.im = 0} := fun z hz => by
  simpa using hz

/-- A function that commutes with complex conjugation is real on the real line:
`f x` is the cast of its real part. -/
theorem ofReal_re_apply_of_forall_conj {f : ℂ → ℂ} (hf : ∀ w, f (conj w) = conj (f w))
    (x : ℝ) : ((f x).re : ℂ) = f x :=
  Complex.conj_eq_iff_re.1 (by rw [← hf, Complex.conj_ofReal])

/-- The rotation `z ↦ I z` does not preserve the real axis, so it is not admissible on
half-discs. -/
theorem not_mapsTo_I_mul_setOf_im_eq_zero :
    ¬ Set.MapsTo (fun z : ℂ => Complex.I * z) {z | z.im = 0} {z | z.im = 0} := fun h => by
  simpa using h (show (1 : ℂ) ∈ {z : ℂ | z.im = 0} by simp)

/-- Under a reflection symmetry `f (a - z) = c * conj (f (conj z))`, a one-sided upper bound
`ρ.re ≤ B` on all zeros of `f` also gives `a.re - ρ.re ≤ B`, hence confines every zero to the
bounded vertical strip `|ρ.re| ≤ max B |a.re - B|`. -/
theorem abs_re_le_max_of_re_le_of_sub_conj {f : ℂ → ℂ} {B : ℝ}
    (hre : ∀ ρ : ℂ, f ρ = 0 → ρ.re ≤ B)
    {a c : ℂ} (hfe : ∀ z : ℂ, f (a - z) = c * conj (f (conj z)))
    {ρ : ℂ} (hρ : f ρ = 0) : |ρ.re| ≤ max B |a.re - B| := by
  have hsym : f (a - conj ρ) = 0 := by
    have := hfe (conj ρ)
    simpa [hρ] using this
  have h1 := hre (a - conj ρ) hsym
  simp only [Complex.sub_re, Complex.conj_re] at h1
  have hlow : -max B |a.re - B| ≤ a.re - B := by
    have := neg_abs_le (a.re - B)
    linarith [le_max_right B |a.re - B|]
  exact abs_le.mpr ⟨by linarith, (hre ρ hρ).trans (le_max_left _ _)⟩

variable {E : Type*} [TopologicalSpace E] {τ : E → E} {U : Set E} {ρ : ℝ}

/-- The parameter map `τ` composed with conjugation of the disc coordinate is continuous on the
product of `U` with a disc centred at zero, and maps this product and its punctured version to
themselves. -/
theorem continuousOn_mapsTo_prodMap_conj (hτ : ContinuousOn τ U) (hτU : Set.MapsTo τ U U) :
    ContinuousOn (fun b : E × ℂ ↦ (τ b.1, conj b.2)) (U ×ˢ ball 0 ρ) ∧
      Set.MapsTo (fun b : E × ℂ ↦ (τ b.1, conj b.2)) (U ×ˢ ball 0 ρ) (U ×ˢ ball 0 ρ) ∧
      Set.MapsTo (fun b : E × ℂ ↦ (τ b.1, conj b.2)) (U ×ˢ (ball 0 ρ \ {0}))
        (U ×ˢ (ball 0 ρ \ {0})) := by
  have hconjBall : Set.MapsTo conj (ball (0 : ℂ) ρ) (ball 0 ρ) := fun _ hz ↦
    conj_mem_ball_of_im_eq_zero (by simp) hz
  exact ⟨hτ.prodMap Complex.continuous_conj.continuousOn, hτU.prodMap hconjBall,
    hτU.prodMap fun z hz ↦ ⟨hconjBall hz.1, by simpa using hz.2⟩⟩

/-- **Two integers whose complex images are closer than `1` are equal.** -/
theorem eq_of_dist_intCast_lt_one {m n : ℤ} (h : dist (m : ℂ) (n : ℂ) < 1) : m = n := by
  by_contra hne
  have : (1 : ℝ) ≤ dist (m : ℂ) (n : ℂ) := by
    rw [Complex.isometry_intCast.dist_eq]; exact Int.pairwise_one_le_dist hne
  linarith

/-- Reverse triangle lower bound for a natural-number shift: `(n : ℝ) - ‖c‖ ≤ ‖(n : ℂ) + c‖`. -/
theorem _root_.Complex.sub_norm_le_norm_natCast_add (n : ℕ) (c : ℂ) :
    (n : ℝ) - ‖c‖ ≤ ‖(n : ℂ) + c‖ := by
  simpa [Complex.norm_natCast] using norm_sub_norm_le (n : ℂ) (-c)

/-- Shifting a complex number in the open right half-plane by a natural number stays in the open
right half-plane. -/
theorem _root_.Complex.natCast_add_re_pos (n : ℕ) {c : ℂ} (hc : 0 < c.re) :
    0 < ((n : ℂ) + c).re := by
  simp only [Complex.add_re, Complex.natCast_re]
  linarith [Nat.cast_nonneg (α := ℝ) n]

/-- On any compact subset `K ⊆ ℂ` disjoint from `-ℕ`, the shifted norms `‖(n : ℂ) + c‖` are
uniformly bounded below by a positive constant `δ ≤ 1`. -/
theorem _root_.IsCompact.exists_pos_le_norm_natCast_add {K : Set ℂ} (hK : IsCompact K)
    (hKc : ∀ c ∈ K, ∀ n : ℕ, (n : ℂ) + c ≠ 0) :
    ∃ δ > 0, δ ≤ 1 ∧ ∀ c ∈ K, ∀ n : ℕ, δ ≤ ‖(n : ℂ) + c‖ := by
  obtain ⟨C, hC⟩ := hK.isBounded.exists_norm_le
  set C' : ℝ := max C 0
  set N : ℕ := Nat.ceil (C' + 1)
  have hlarge : ∀ c ∈ K, ∀ n : ℕ, N ≤ n → 1 ≤ ‖(n : ℂ) + c‖ := fun c hc n hn => by
    have hc' : ‖c‖ ≤ C' := (hC c hc).trans (le_max_left C 0)
    have hn' : C' + 1 ≤ (n : ℝ) := (Nat.le_ceil _).trans (Nat.cast_le.mpr hn)
    linarith [Complex.sub_norm_le_norm_natCast_add n c]
  have hcont : Continuous (fun p : ℕ × ℂ => ‖(p.1 : ℂ) + p.2‖) :=
    continuous_norm.comp ((continuous_of_discreteTopology.comp continuous_fst).add continuous_snd)
  obtain ⟨δ₀, hδ₀, hmin⟩ := ((Finset.finite_toSet (Finset.range N)).isCompact.prod hK)
    |>.exists_forall_le' hcont.continuousOn (fun p hp => norm_pos_iff.mpr (hKc p.2 hp.2 p.1))
  refine ⟨min δ₀ 1, lt_min hδ₀ one_pos, min_le_right _ _, fun c hc n => ?_⟩
  rcases lt_or_ge n N with hn | hn
  · exact (min_le_left _ _).trans (hmin (n, c) ⟨Finset.mem_range.mpr hn, hc⟩)
  · exact (min_le_right _ _).trans (hlarge c hc n hn)

end TauCeti

namespace Complex

open ComplexConjugate

/-- The real part of `exp (θ * I) ^ j` is `cos (j θ)`: the real part of de Moivre's formula. -/
@[simp]
theorem re_exp_ofReal_mul_I_pow (θ : ℝ) (j : ℕ) : (exp (θ * I) ^ j).re = Real.cos (j * θ) := by
  rw [← exp_natCast_mul, ← mul_assoc, ← ofReal_natCast, ← ofReal_mul, exp_ofReal_mul_I_re]

/-- Complex conjugation, as a continuous real-linear equivalence, is its own inverse. -/
@[simp]
theorem conjCLE_symm : conjCLE.symm = conjCLE := by
  rw [← conjLIE_toCLE, ← LinearIsometryEquiv.toContinuousLinearEquiv_symm, conjLIE_symm]

/-- The imaginary part of a conjugate product is bounded by the product of the norms. -/
theorem abs_im_conj_mul_le (u e : ℂ) : |(conj u * e).im| ≤ ‖u‖ * ‖e‖ := by
  simpa [norm_mul] using abs_im_le_norm (conj u * e)

/-- The real part of a conjugate product is bounded by the product of the norms. -/
theorem re_conj_mul_le (u e : ℂ) : (conj u * e).re ≤ ‖u‖ * ‖e‖ := by
  simpa [norm_mul] using re_le_norm (conj u * e)

/-- The norm of `1 - conj w * z` is symmetric in `z` and `w`: conjugation swaps the two
expressions and preserves norms. -/
theorem norm_one_sub_conj_mul_comm (z w : ℂ) : ‖1 - conj w * z‖ = ‖1 - conj z * w‖ := by
  rw [← norm_conj]
  simp [mul_comm]

/-- For `‖w‖ = 1`, `1 - conj w * z` has the norm of `z - w`. -/
theorem norm_one_sub_conj_mul {w z : ℂ} (hw : ‖w‖ = 1) : ‖1 - conj w * z‖ = ‖z - w‖ := by
  have h : w * (1 - conj w * z) = w - z := by
    rw [mul_sub, mul_one, ← mul_assoc, mul_conj, normSq_eq_norm_sq, hw]
    simp
  rw [norm_sub_rev z w, ← h, norm_mul, hw, one_mul]

/-- For `‖w‖ = 1` and `‖z‖ ≤ 1`, `1 - conj w * z` has nonnegative real part. -/
theorem re_one_sub_conj_mul_nonneg {w z : ℂ} (hw : ‖w‖ = 1) (hz : ‖z‖ ≤ 1) :
    0 ≤ (1 - conj w * z).re := by
  simpa [hw] using (re_conj_mul_le w z).trans (by simpa [hw] using hz)

/-- For `‖w‖ = 1` and `‖z‖ < 1`, `1 - conj w * z` has positive real part. -/
theorem re_one_sub_conj_mul_pos {w z : ℂ} (hw : ‖w‖ = 1) (hz : ‖z‖ < 1) :
    0 < (1 - conj w * z).re := by
  simpa [hw] using (re_conj_mul_le w z).trans_lt (by simpa [hw] using hz)

/-- For a point `x` of the closed disc of radius `r` and a point `y` outside the open disc, the
conjugate `conj x` is within `3 ‖x - y‖` of the point `r² / y`, the inversion of `y` in the circle
of radius `r` followed by conjugation. -/
theorem norm_conj_sub_sq_div_le {r : ℝ} (x y : ℂ)
    (hx : ‖x‖ ≤ r) (hy : r ≤ ‖y‖) :
    ‖conj x - (r : ℂ)^2/y‖ ≤ 3*‖x - y‖ := by
  have hr : 0 ≤ r := (norm_nonneg x).trans hx
  rcases eq_or_ne y 0 with rfl | hyne
  · have hr0 : r = 0 := le_antisymm (by simpa using hy) hr
    have hx0 : x = 0 := norm_le_zero_iff.mp (hr0 ▸ hx)
    simp [hr0, hx0]
  have hy0 : 0 < ‖y‖ := norm_pos_iff.mpr hyne
  have heq : conj y - (r : ℂ)^2/y = (((‖y‖^2 - r^2 : ℝ) : ℂ))/y := by
    apply (eq_div_iff hyne).mpr
    rw [sub_mul, div_mul_cancel₀ _ hyne, conj_mul', ofReal_sub, ofReal_pow, ofReal_pow]
  have hgap : ‖y‖-r ≤ ‖x - y‖ := by
    have h := norm_le_norm_add_norm_sub x y
    linarith
  have htail : ‖conj y - (r : ℂ)^2/y‖ ≤ 2 * (‖y‖-r) := by
    rw [heq, norm_div, norm_real, Real.norm_eq_abs,
      abs_of_nonneg (by nlinarith : 0 ≤ ‖y‖^2 - r^2)]
    apply (div_le_iff₀ hy0).mpr
    nlinarith
  calc
    _ ≤ ‖conj x - conj y‖ + ‖conj y - (r : ℂ)^2/y‖ := by
      simpa only [dist_eq_norm] using dist_triangle (conj x) (conj y) ((r : ℂ)^2/y)
    _ ≤ ‖x - y‖ + 2 * (‖y‖-r) := by
      rw [← map_sub, norm_conj]
      exact add_le_add le_rfl htail
    _ ≤ _ := by linarith

/-- Dividing by a natural number does not increase the norm, so the point `(a z + b) / M` has
norm at most `‖a‖ C + ‖b‖` when `‖z‖ ≤ C`. For `M = 0` the quotient is `0` by Lean's convention
`x / 0 = 0`. -/
theorem norm_mul_add_div_natCast_le (M : ℕ) (a b : ℂ) {z : ℂ} {C : ℝ} (hz : ‖z‖ ≤ C) :
    ‖(a * z + b) / M‖ ≤ ‖a‖ * C + ‖b‖ := by
  rw [norm_div, Complex.norm_natCast]
  exact (div_nat_le_self_of_nonneg (norm_nonneg _) M).trans
    (norm_add_le_of_le (norm_mul_le_of_le le_rfl hz) le_rfl)

/-- If `s + β` never vanishes for natural numbers `s ≥ 1`, then `‖s + β‖` is bounded below by a
positive multiple of `s` for all `s ≥ 1`. -/
theorem exists_pos_mul_le_norm_natCast_add {β : ℂ} (hβ : ∀ s : ℕ, 1 ≤ s → (s : ℂ) + β ≠ 0) :
    ∃ c > 0, ∀ s : ℕ, 1 ≤ s → c * s ≤ ‖(s : ℂ) + β‖ := by
  -- beyond `N` the bound `c = 1/2` holds; below it, take the least ratio `‖s + β‖ / s`
  set N := ⌈2 * ‖β‖⌉₊ + 1
  obtain ⟨s₀, hs₀, hmin⟩ := (Finset.Icc 1 N).exists_min_image (fun s : ℕ ↦ ‖(s : ℂ) + β‖ / s)
    ⟨1, Finset.mem_Icc.2 ⟨le_rfl, by omega⟩⟩
  have hs₀1 : (0 : ℝ) < s₀ := by exact_mod_cast (Finset.mem_Icc.1 hs₀).1
  have hpos : 0 < ‖(s₀ : ℂ) + β‖ / s₀ :=
    div_pos (norm_pos_iff.2 (hβ s₀ (Finset.mem_Icc.1 hs₀).1)) hs₀1
  refine ⟨min (1 / 2) (‖(s₀ : ℂ) + β‖ / s₀), lt_min (by norm_num) hpos, fun s hs ↦ ?_⟩
  have hs' : (0 : ℝ) < s := by exact_mod_cast hs
  by_cases hsN : s ≤ N
  · calc min (1 / 2) (‖(s₀ : ℂ) + β‖ / s₀) * s ≤ (‖(s : ℂ) + β‖ / s) * s := by
          gcongr
          exact (min_le_right _ _).trans (hmin s (Finset.mem_Icc.2 ⟨hs, hsN⟩))
      _ = ‖(s : ℂ) + β‖ := div_mul_cancel₀ _ hs'.ne'
  · have hceil : 2 * ‖β‖ ≤ s := (Nat.le_ceil _).trans (by exact_mod_cast (by omega : _ ≤ s))
    have htri : (s : ℝ) ≤ ‖(s : ℂ) + β‖ + ‖β‖ := by
      simpa using norm_sub_le ((s : ℂ) + β) β
    calc min (1 / 2) (‖(s₀ : ℂ) + β‖ / s₀) * s ≤ 1 / 2 * s := by
          gcongr
          exact min_le_left _ _
      _ ≤ ‖(s : ℂ) + β‖ := by linarith

/-- The real coordinates `equivRealProdCLM` do not increase distances, so they map the disc of
radius `r` about `equivRealProdCLM.symm z₀` into the square `B_r(z₀)` of `ℝ × ℝ`. -/
theorem dist_equivRealProdCLM_le (y : ℂ) (z₀ : ℝ × ℝ) :
    dist (equivRealProdCLM y) z₀ ≤ dist y (equivRealProdCLM.symm z₀) := by
  conv_lhs => rw [← equivRealProdCLM.apply_symm_apply z₀]
  exact (lipschitz_equivRealProd.dist_le_mul y _).trans (by simp)

/-- A point of the closed disc of centre `c` and radius `ρ` has real part in
`[c.re - ρ, c.re + ρ]`. -/
theorem re_mem_Icc_of_norm_sub_le (w : ℂ) {c : ℂ} {ρ : ℝ} (h : ‖w - c‖ ≤ ρ) :
    w.re ∈ Set.Icc (c.re - ρ) (c.re + ρ) := by
  -- the real part is `1`-Lipschitz, so it maps `closedBall c ρ` into `closedBall c.re ρ`
  rw [← Real.closedBall_eq_Icc]
  simpa only [RCLike.re_to_complex, NNReal.coe_one, one_mul] using
    (RCLike.lipschitzWith_re (K := ℂ)).mapsTo_closedBall c ρ
      (by rwa [Metric.mem_closedBall, dist_eq])

/-- A point `w` with `normSq (w - c) ≤ ρ ^ 2`, for `0 ≤ ρ`, has real part in
`[c.re - ρ, c.re + ρ]`. -/
theorem re_mem_Icc_of_normSq_sub_le (w : ℂ) {c : ℂ} {ρ : ℝ} (hρ : 0 ≤ ρ)
    (h : normSq (w - c) ≤ ρ ^ 2) : w.re ∈ Set.Icc (c.re - ρ) (c.re + ρ) :=
  re_mem_Icc_of_norm_sub_le w <| by
    rw [norm_def, ← Real.sqrt_sq hρ]
    exact Real.sqrt_le_sqrt h

/-- The difference of the real parts of two complex numbers is at most their distance. -/
theorem re_sub_re_le_dist (z w : ℂ) : z.re - w.re ≤ dist z w := by
  rw [dist_eq, ← sub_re]
  exact re_le_norm _

/-- The square of the distance between two complex numbers is the sum of the squares of the
differences of their real and imaginary parts. -/
theorem sq_dist_eq_re_im (z w : ℂ) : dist z w ^ 2 = (z.re - w.re) ^ 2 + (z.im - w.im) ^ 2 := by
  rw [dist_eq_re_im, Real.sq_sqrt (by positivity)]

/-- If the distance between two complex numbers is at most the difference of their real parts,
then they have the same imaginary part. -/
theorem im_eq_im_of_dist_le_re_sub_re {z w : ℂ} (h : dist z w ≤ z.re - w.re) : z.im = w.im := by
  rw [dist_eq, ← sub_re] at h
  rw [← sub_eq_zero, ← sub_im]
  simpa only [RCLike.im_to_complex] using
    RCLike.im_eq_zero_of_le (K := ℂ) (a := z - w) (by simpa only [RCLike.re_to_complex] using h)

/-- A closed disc `closedBall c R` with `θ + R < c.re` lies in the open half-plane
`{z | θ < z.re}`. -/
theorem closedBall_subset_setOfPred_lt_re {c : ℂ} {R θ : ℝ} (h : θ + R < c.re) :
    Metric.closedBall c R ⊆ {z | θ < z.re} := fun w hw ↦
  Set.mem_ofPred.2 <| by
    have : |w.re - c.re| ≤ R := by
      simpa only [RCLike.re_to_complex] using RCLike.abs_re_sub_le_of_mem_closedBall hw
    linarith [(abs_le.1 this).1]

/-- An open disc `ball c R` with `θ + R ≤ c.re` lies in the open half-plane `{z | θ < z.re}`. -/
theorem ball_subset_setOfPred_lt_re {c : ℂ} {R θ : ℝ} (h : θ + R ≤ c.re) :
    Metric.ball c R ⊆ {z | θ < z.re} := fun w hw ↦
  Set.mem_ofPred.2 <| by
    have : c.re - R < w.re := by
      simpa only [RCLike.re_to_complex] using (RCLike.re_mem_Ioo_of_mem_ball hw).1
    linarith

/-- Two complex numbers whose real parts have the same absolute value compare in norm as their
imaginary parts compare in absolute value. -/
theorem norm_le_norm_iff_abs_im_le_abs_im_of_abs_re_eq (z : ℂ) {w : ℂ} (h : |z.re| = |w.re|) :
    ‖z‖ ≤ ‖w‖ ↔ |z.im| ≤ |w.im| := by
  rw [← sq_le_sq₀ (norm_nonneg z) (norm_nonneg w), ← sq_le_sq]
  -- `‖·‖ ^ 2 = re ^ 2 + im ^ 2`, and the squares of the real parts agree
  have hz := sq_norm_sub_sq_re z
  have hw := sq_norm_sub_sq_re w
  rw [← sq_abs z.re, h, sq_abs] at hz
  constructor <;> intro <;> linarith

/-- For `z` in the closed upper half-plane, every point `z + s * I` (`s ≥ 0`) of the vertical ray
going upward from `z` is at least as far from the origin as `z`. -/
theorem norm_le_norm_add_ofReal_mul_I (z : ℂ) (hz : 0 ≤ z.im) {s : ℝ} (hs : 0 ≤ s) :
    ‖z‖ ≤ ‖z + (s : ℂ) * I‖ := by
  have him : (z + (s : ℂ) * I).im = z.im + s := by simp
  exact (norm_le_norm_iff_abs_im_le_abs_im_of_abs_re_eq z (by simp)).2
    (abs_le_abs (by linarith) (by linarith))

/-- For `z` in the closed upper half-plane and every real `s`, the point `z + s * I` of the
vertical line through `z` is at distance at least `(‖z‖ + s) / 2` from the origin. -/
theorem norm_add_div_two_le_norm_add_ofReal_mul_I (z : ℂ) (hz : 0 ≤ z.im) (s : ℝ) :
    (‖z‖ + s) / 2 ≤ ‖z + (s : ℂ) * I‖ := by
  rcases le_total 0 s with hs | hs
  · -- `s` is at most the imaginary part `z.im + s` of `z + s * I`, hence at most its norm
    have h : s ≤ ‖z + (s : ℂ) * I‖ := le_trans (by simpa using hz) (im_le_norm _)
    linarith [norm_le_norm_add_ofReal_mul_I z hz hs]
  · -- for `s ≤ 0`, the triangle inequality gives `‖z‖ ≤ ‖z + s * I‖ - s`
    have h := norm_le_norm_add_norm_sub' z (z + (s : ℂ) * I)
    have hsI : ‖z - (z + (s : ℂ) * I)‖ = -s := by simp [abs_of_nonpos hs]
    linarith [norm_nonneg (z + (s : ℂ) * I)]

/-- For `z` in the closed right half-plane (`0 ≤ z.re`), `1 + z` has real part at least `1`. -/
theorem one_le_re_one_add {z : ℂ} (hz : 0 ≤ z.re) : 1 ≤ (1 + z).re := by
  simp [hz]

/-- For `z` in the closed right half-plane (`0 ≤ z.re`), `1 + z` has norm at least `1`. -/
theorem one_le_norm_one_add {z : ℂ} (hz : 0 ≤ z.re) : 1 ≤ ‖1 + z‖ :=
  (one_le_re_one_add hz).trans (re_le_norm _)

/-- A point at height `1 ≤ |Im s|` is at distance at least `1` from `1`. -/
theorem one_le_norm_sub_one {s : ℂ} (ht : 1 ≤ |s.im|) : 1 ≤ ‖s - 1‖ := by
  have h := abs_im_le_norm (s - 1)
  rw [sub_im, one_im, sub_zero] at h
  exact ht.trans h

/-- A point at height `1 ≤ |Im s|` is not `1`. -/
theorem ne_one_of_one_le_abs_im {s : ℂ} (ht : 1 ≤ |s.im|) : s ≠ 1 := by
  rintro rfl
  norm_num at ht

/-- At height `1 ≤ |Im s|`, `‖(s - 1)⁻¹‖ ≤ 1`. -/
theorem norm_inv_sub_one_le_one {s : ℂ} (ht : 1 ≤ |s.im|) : ‖(s - 1)⁻¹‖ ≤ 1 := by
  rw [norm_inv]
  exact inv_le_one_of_one_le₀ (one_le_norm_sub_one ht)

/-- For real `1 ≤ r`, the norm of `(r : ℂ) - 1` is `r - 1`. -/
theorem norm_ofReal_sub_one {r : ℝ} (h : 1 ≤ r) : ‖(r : ℂ) - 1‖ = r - 1 := by
  rw [← ofReal_one, ← ofReal_sub, norm_real, Real.norm_of_nonneg (sub_nonneg.mpr h)]

/-- A shift `s + μ` stays off the real axis when `|Im μ| < |Im s|`. -/
theorem add_im_ne_zero_of_abs_im_lt {s μ : ℂ} (h : |μ.im| < |s.im|) : (s + μ).im ≠ 0 :=
  fun h0 ↦ by
    rw [add_im, ← eq_neg_iff_add_eq_zero] at h0
    rw [h0, abs_neg] at h
    exact h.false

/-- There is no ring homomorphism from `ℂ` to a semireal semiring `R` (one in which `1 + s ≠ 0`
for every sum of squares `s`), such as `ℝ` or any linearly ordered ring: it would send
`1 + I * I = 0` to `1 + f I * f I = 0`. -/
instance instIsEmptyRingHom {R : Type*} [NonAssocSemiring R] [IsSemireal R] :
    IsEmpty (ℂ →+* R) :=
  ⟨fun f => IsSemireal.one_add_ne_zero (IsSumSq.mul_self (f I)) <| by
    rw [← map_one f, ← map_mul, ← map_add, I_mul_I, add_neg_cancel, map_zero]⟩

/-- An `n`-th root `z`, `n ≠ 0`, of a complex number `w` with `w * conj w = 1` lies on the unit
circle, so its conjugate is its inverse. -/
theorem conj_eq_inv_of_pow_eq {z w : ℂ} {n : ℕ} (hn : n ≠ 0) (hz : z ^ n = w)
    (hw : w * conj w = 1) : conj z = z⁻¹ := by
  have hw' : ‖w‖ = 1 := TauCeti.RCLike.mul_conj_eq_one_iff.1 hw
  have hz' : ‖z‖ = 1 :=
    (pow_eq_one_iff_of_nonneg (norm_nonneg z) hn).mp (by rw [← norm_pow, hz, hw'])
  exact (inv_eq_conj hz').symm

end Complex

/-- A linear isometry from the plane maps `i` to a unit vector. -/
theorem LinearIsometry.norm_map_I {E : Type*} [SeminormedAddCommGroup E] [Module ℝ E]
    (ι : ℂ →ₗᵢ[ℝ] E) : ‖ι Complex.I‖ = 1 :=
  (ι.norm_map _).trans Complex.norm_I
