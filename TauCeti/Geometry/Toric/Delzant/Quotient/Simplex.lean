/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Toric.Delzant.Quotient.Basic
public import TauCeti.Geometry.Toric.Delzant.Simplex
public import TauCeti.Topology.Algebra.Projectivization
import Mathlib.Analysis.SpecialFunctions.Complex.Arg
import TauCeti.Algebra.Group.Pi.Lemmas

/-!
# The Delzant quotient of the standard simplex is complex projective space

Let `Δ_a` be the standard simplex `{y | 0 ≤ y (e k) for every k, and ∑ k, y (e k) ≤ a}` of size
`a > 0` in `(ℝ^κ)*`, presented by the normals `e k` and `-1` of `ℤ^κ` with support constants `0`
and `-a` (`TauCeti.Toric.simplexNormal`, `TauCeti.Toric.simplexSupport`). Its facets are indexed
by `Option κ`, so Delzant's construction (`TauCeti.Toric.DelzantQuotient`) takes place in
`ℂ^(Option κ)`, with real coordinates `z_o = q_o + i p_o`. This file identifies the result with
the complex projective space `ℙ ℂ (Option κ → ℂ) = ℂPⁿ`, `n = #κ`, the basic example of a
symplectic toric manifold.

* **The level is a sphere.** The zero level of the moment map of the kernel torus is the sphere
  `‖q‖² + ‖p‖² = 2a` of `ℂ^(Option κ)` (`TauCeti.Toric.mem_delzantLevel_simplex_iff`). Indeed the
  real normals satisfy the single relation `-1 + ∑ k, e k = 0`, and the moment map component along
  it is `∑ o, |z_o|² / 2 - a`.
* **The kernel torus is the diagonal circle.** An angle `θ ∈ (ℝ / 2πℤ)^(Option κ)` lies in the
  kernel of `(ℝ / 2πℤ)^(Option κ) → ℝ^κ / 2πℤ^κ` exactly when all its coordinates agree
  (`TauCeti.Toric.mem_ker_facetTorusHom_simplex_iff`), so it acts on `ℂ^(Option κ)` by a scalar
  `e^(-iφ)`.
* **The quotient is `ℂPⁿ`.** Hence `z ↦ [z]` descends to a continuous bijection from the Delzant
  quotient to `ℙ ℂ (Option κ → ℂ)`: two points of the sphere span the same complex line exactly
  when they differ by a unit scalar, and every line meets the sphere. As the Delzant quotient is
  compact and projective space is Hausdorff, this is a homeomorphism
  (`TauCeti.Toric.DelzantQuotient.simplexHomeomorph`). The argument is the one identifying the
  sphere model `TauCeti.ComplexProjectiveSpace` with `ℙ ℂ (Fin (n + 1) → ℂ)`
  (`TauCeti.ComplexProjectiveSpace.homeomorphProjectivization`), carried out on the Delzant level,
  a sphere of radius `√(2a)` in real coordinates, with the kernel torus in place of the circle.
* **The moment map.** Under this homeomorphism the reduced moment map of the residual torus is
  `[v] ↦ (a |v_(some k)|² / ∑ o, |v_o|²)_k`, the diagonal of `a` times the orthogonal projector
  onto the line `[v]`, with the entry of the homogeneous coordinate `none` dropped
  (`TauCeti.Toric.DelzantQuotient.reducedMomentMap_simplexHomeomorph_symm_mk`). Its image is the
  simplex `Δ_a` (`TauCeti.Toric.DelzantQuotient.range_reducedMomentMap`).

The convention is the one of `TauCeti.Toric.DelzantQuotient`: the torus acts by
`z_o ↦ e^(-iθ_o) z_o` and the moment map is `⟨μ(z), t⟩ = ∑ o, t_o (|z_o|² / 2 + c_o)`.

## Main results

* `TauCeti.Toric.mem_delzantLevel_simplex_iff`: the level of `Δ_a` is the sphere of radius
  `√(2a)`.
* `TauCeti.Toric.mem_ker_facetTorusHom_simplex_iff`: the kernel torus of `Δ_a` is the diagonal
  circle.
* `TauCeti.Toric.DelzantQuotient.simplexHomeomorph`: the Delzant quotient of `Δ_a` is homeomorphic
  to `ℂPⁿ`, by `[z] ↦ [z]`.
* `TauCeti.Toric.DelzantQuotient.reducedMomentMap_simplexHomeomorph_symm_mk`: the moment map of
  `ℂPⁿ` is `[v] ↦ (a |v_(some k)|² / ∑ o, |v_o|²)_k`.

## References

* A. Cannas da Silva, *Lectures on Symplectic Geometry*, Lecture Notes in Mathematics 1764,
  Springer, 2001, Section 29 (Delzant's construction).
* V. Guillemin, *Moment Maps and Combinatorial Invariants of Hamiltonian `T^n`-spaces*,
  Birkhäuser, 1994, Chapter 1.
-/

public section

noncomputable section

open Complex (I)
open Real Set
open scoped LinearAlgebra.Projectivization

namespace TauCeti.Toric

variable {κ : Type*} [Fintype κ] [DecidableEq κ] {a : ℝ}

/-! ### The level and the kernel torus of the simplex -/

/-- **The level of the standard simplex is a sphere.** A point `z = q + i p` of `ℂ^(Option κ)`
lies on the zero level of the moment map of the kernel torus of the simplex of size `a` exactly
when `‖q‖² + ‖p‖² = 2a`. -/
theorem mem_delzantLevel_simplex_iff
    {x : EuclideanSpace ℝ (Option κ) × EuclideanSpace ℝ (Option κ)} :
    x ∈ delzantLevel ((Int.castAddHom ℝ).compLeft κ) (simplexNormal κ) (simplexSupport a) ↔
      ‖x.1‖ ^ 2 + ‖x.2‖ ^ 2 = 2 * a := by
  rw [EuclideanSpace.real_norm_sq_eq, EuclideanSpace.real_norm_sq_eq, ← Finset.sum_add_distrib]
  constructor
  · -- The constant vector `1` spans the relation `-1 + ∑ k, e k = 0` between the real normals.
    intro h
    have h1 : (1 : Option κ → ℝ) ∈
        LinearMap.ker (Fintype.linearCombination ℝ
          fun o ↦ (Int.castAddHom ℝ).compLeft κ (simplexNormal κ o)) := by
      rw [LinearMap.mem_ker, linearCombination_simplexNormal]
      exact funext fun _ ↦ sub_self 1
    have := mem_delzantLevel.1 h 1 h1
    simp only [delzantMomentMap_apply, Pi.one_apply, one_mul, Fintype.sum_option,
      simplexSupport_none, simplexSupport_some, add_zero] at this
    rw [Fintype.sum_option]
    rw [← Finset.sum_div] at this
    linarith
  · -- The moment value is `y = ∑ k, (|z_k|² / 2) e k*`.
    intro h
    refine mem_delzantLevel_of_forall_eq (y := ∑ k, ((x.1 (some k) ^ 2 + x.2 (some k) ^ 2) / 2) •
      ContinuousLinearMap.proj k) fun o ↦ ?_
    rw [Fintype.sum_option] at h
    cases o with
    | none =>
      have h1 : (Int.castAddHom ℝ).compLeft κ (1 : κ → ℤ) = 1 := by
        ext
        simp
      simp only [simplexSupport_none, simplexNormal_none, map_neg, h1]
      simp only [FunLike.coe_sum, FunLike.coe_smul, Finset.sum_apply, Pi.smul_apply,
        ContinuousLinearMap.proj_apply, Pi.one_apply, smul_eq_mul, mul_one]
      rw [← Finset.sum_div]
      linarith
    | some k =>
      simp [Pi.single_apply]

/-- **The kernel torus of the standard simplex is the diagonal circle.** An angle
`θ ∈ (ℝ / 2πℤ)^(Option κ)` lies in the kernel of `facetTorusHom` for the standard simplex exactly
when all its coordinates agree. -/
theorem mem_ker_facetTorusHom_simplex_iff {θ : Option κ → AddCircle (2 * π)} :
    θ ∈ (facetTorusHom ((Int.castAddHom ℝ).compLeft κ) (simplexNormal κ) (2 * π)).ker ↔
      ∀ o, θ o = θ none := by
  choose t ht using fun o ↦ QuotientAddGroup.mk_surjective (θ o)
  obtain rfl : (fun o ↦ (t o : AddCircle (2 * π))) = θ := funext ht
  rw [AddMonoidHom.mem_ker, facetTorusHom_coe, QuotientAddGroup.eq_zero_iff, AddMonoidHom.mem_range]
  -- The class of `t` is in the kernel when `t_(some k) - t_none ∈ 2πℤ` for every `k`.
  rw [linearCombination_simplexNormal]
  have hcoe (k : κ) : ((t (some k) : AddCircle (2 * π)) = t none) ↔
      ∃ n : ℤ, (2 * π) * n = t (some k) - t none := by
    rw [← sub_eq_zero, ← QuotientAddGroup.mk_sub, AddCircle.coe_eq_zero_iff]
    exact exists_congr fun n ↦ by rw [zsmul_eq_mul, mul_comm]
  constructor
  · rintro ⟨n, hn⟩ o
    cases o with
    | none => rfl
    | some k =>
      refine (hcoe k).2 ⟨n k, ?_⟩
      have := congrFun hn k
      simpa using this
  · intro h
    choose n hn using fun k ↦ (hcoe k).1 (h (some k))
    refine ⟨n, funext fun k ↦ ?_⟩
    simpa using hn k

/-! ### Complex coordinates -/

/-- On the level of the simplex of size `a > 0`, the complex coordinates `q_o + i p_o`
(`TauCeti.complexEuclideanEquivRealProd`) do not all vanish. -/
theorem complexEuclideanEquivRealProd_symm_ne_zero_of_mem_delzantLevel_simplex (ha : 0 < a)
    {x : EuclideanSpace ℝ (Option κ) × EuclideanSpace ℝ (Option κ)}
    (hx : x ∈ delzantLevel ((Int.castAddHom ℝ).compLeft κ) (simplexNormal κ) (simplexSupport a)) :
    ⇑((complexEuclideanEquivRealProd (Option κ)).symm x) ≠ 0 := by
  intro h
  rw [mem_delzantLevel_simplex_iff, ← norm_complexEuclideanEquivRealProd_symm_sq,
    EuclideanSpace.norm_sq_eq, h] at hx
  simp only [Pi.zero_apply, norm_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow,
    Finset.sum_const_zero] at hx
  linarith

/-- If the complex coordinates of a point of the level of the simplex of size `a` are `c • v`, then
`‖c‖² ∑ o, |v_o|² = 2a`. -/
private theorem norm_sq_mul_sum_norm_sq_eq_of_smul_eq
    {x : EuclideanSpace ℝ (Option κ) × EuclideanSpace ℝ (Option κ)}
    (hx : x ∈ delzantLevel ((Int.castAddHom ℝ).compLeft κ) (simplexNormal κ) (simplexSupport a))
    {c : ℂ} {v : Option κ → ℂ} (hc : c • v = ⇑((complexEuclideanEquivRealProd (Option κ)).symm x)) :
    ‖c‖ ^ 2 * ∑ o, ‖v o‖ ^ 2 = 2 * a := by
  rw [← mem_delzantLevel_simplex_iff.1 hx, ← norm_complexEuclideanEquivRealProd_symm_sq,
    EuclideanSpace.norm_sq_eq, ← hc, Finset.mul_sum]
  simp only [Pi.smul_apply, smul_eq_mul, norm_mul, mul_pow]

namespace DelzantQuotient

/-- Two points of the level of the simplex span the same complex line exactly when they lie in
the same orbit of the diagonal circle. -/
private theorem mk_eq_mk_iff_mk_complexEuclideanEquivRealProd_symm_eq (ha : 0 < a)
    {x y : delzantLevel ((Int.castAddHom ℝ).compLeft κ) (simplexNormal κ) (simplexSupport a)} :
    mk x = mk y ↔
      Projectivization.mk ℂ _
          (complexEuclideanEquivRealProd_symm_ne_zero_of_mem_delzantLevel_simplex ha x.property) =
        Projectivization.mk ℂ _
          (complexEuclideanEquivRealProd_symm_ne_zero_of_mem_delzantLevel_simplex ha
            y.property) := by
  rw [mk_eq_mk_iff, Projectivization.mk_eq_mk_iff']
  constructor
  · -- The diagonal circle multiplies the complex coordinates by a unit scalar.
    rintro ⟨θ, hθ, rfl⟩
    choose t ht using fun o ↦ QuotientAddGroup.mk_surjective (θ o)
    obtain rfl : (fun o ↦ (t o : AddCircle (2 * π))) = θ := funext ht
    refine ⟨Real.cos (-t none) + Real.sin (-t none) * I, funext fun o ↦ ?_⟩
    have hrot : torusRotation (fun o ↦ (t o : AddCircle (2 * π))) =
        weightRotation (fun _ ↦ -t none) := by
      rw [show (fun o ↦ (t o : AddCircle (2 * π))) = fun _ ↦ (t none : AddCircle (2 * π)) from
        funext (mem_ker_facetTorusHom_simplex_iff.1 hθ), torusRotation_coe, Pi.neg_def]
    rw [coe_vadd_delzantLevel, hrot, complexEuclideanEquivRealProd_symm_weightRotation_apply,
      Pi.smul_apply, smul_eq_mul]
  · -- A scalar relating two points of the same sphere has modulus one, so it is `e^(iφ)`.
    rintro ⟨c, hc⟩
    have hnorm : ‖c‖ = 1 := by
      have h := norm_sq_mul_sum_norm_sq_eq_of_smul_eq x.property hc
      rw [← EuclideanSpace.norm_sq_eq, norm_complexEuclideanEquivRealProd_symm_sq,
        mem_delzantLevel_simplex_iff.1 y.property] at h
      have h1 : ‖c‖ ^ 2 = 1 := by
        have : (‖c‖ ^ 2 - 1) * (2 * a) = 0 := by linarith
        exact sub_eq_zero.1 ((mul_eq_zero.1 this).resolve_right (by positivity))
      nlinarith [norm_nonneg c]
    refine ⟨fun _ ↦ ((-Complex.arg c : ℝ) : AddCircle (2 * π)),
      mem_ker_facetTorusHom_simplex_iff.2 fun _ ↦ rfl,
      Subtype.ext ((complexEuclideanEquivRealProd _).symm.injective (PiLp.ext fun o ↦ ?_))⟩
    rw [coe_vadd_delzantLevel, torusRotation_coe]
    simp only [Pi.neg_def, neg_neg]
    rw [complexEuclideanEquivRealProd_symm_weightRotation_apply]
    have hcexp : (Real.cos (Complex.arg c) + Real.sin (Complex.arg c) * I : ℂ) = c := by
      simpa [hnorm] using Complex.norm_mul_cos_add_sin_mul_I c
    rw [hcexp, ← congrFun hc o, Pi.smul_apply, smul_eq_mul]

/-- Every complex line of `ℂ^(Option κ)` meets the level of the simplex of size `a > 0`, the sphere
`‖z‖² = 2a`. -/
private theorem exists_mk_complexEuclideanEquivRealProd_symm_eq (ha : 0 < a)
    (p : ℙ ℂ (Option κ → ℂ)) :
    ∃ x : delzantLevel ((Int.castAddHom ℝ).compLeft κ) (simplexNormal κ) (simplexSupport a),
      Projectivization.mk ℂ _
          (complexEuclideanEquivRealProd_symm_ne_zero_of_mem_delzantLevel_simplex ha
            x.property) = p := by
  -- Rescale a representative `v` of the line `p` to the sphere `‖z‖² = 2a`.
  set v := p.rep
  have hv : v ≠ 0 := p.rep_ne_zero
  have hs : 0 < ∑ o, ‖v o‖ ^ 2 := by
    obtain ⟨o, ho⟩ := Function.ne_iff.1 hv
    exact lt_of_lt_of_le (pow_pos (norm_pos_iff.2 ho) 2) (Finset.single_le_sum
      (fun o _ ↦ sq_nonneg ‖v o‖) (Finset.mem_univ o))
  set r : ℝ := √(2 * a / ∑ o, ‖v o‖ ^ 2)
  set x : EuclideanSpace ℝ (Option κ) × EuclideanSpace ℝ (Option κ) :=
    (WithLp.toLp 2 fun o ↦ ((r : ℂ) * v o).re, WithLp.toLp 2 fun o ↦ ((r : ℂ) * v o).im)
  have hxv : ⇑((complexEuclideanEquivRealProd (Option κ)).symm x) = (r : ℂ) • v :=
    funext fun _ ↦ (complexEuclideanEquivRealProd_symm_apply _ _).trans (Complex.re_add_im _)
  have hx : x ∈ delzantLevel ((Int.castAddHom ℝ).compLeft κ) (simplexNormal κ)
      (simplexSupport a) := by
    rw [mem_delzantLevel_simplex_iff, ← norm_complexEuclideanEquivRealProd_symm_sq,
      EuclideanSpace.norm_sq_eq, hxv]
    simp only [Pi.smul_apply, smul_eq_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs, mul_pow,
      sq_abs, ← Finset.mul_sum]
    rw [Real.sq_sqrt (by positivity), div_mul_cancel₀ _ hs.ne']
  refine ⟨⟨x, hx⟩, ?_⟩
  conv_rhs => rw [← p.mk_rep]
  exact (Projectivization.mk_eq_mk_iff' ℂ _ _ _ hv).2 ⟨r, hxv.symm⟩

/-- **The Delzant quotient of the standard simplex is complex projective space.** For `a > 0`,
the map `[z] ↦ [z]` from the Delzant quotient of the simplex of size `a`, the quotient of the
sphere `‖z‖² = 2a` of `ℂ^(Option κ)` by the diagonal circle, to `ℙ ℂ (Option κ → ℂ) = ℂPⁿ` is a
homeomorphism. -/
def simplexHomeomorph (ha : 0 < a) :
    DelzantQuotient ((Int.castAddHom ℝ).compLeft κ) (simplexNormal κ) (simplexSupport a) ≃ₜ
      ℙ ℂ (Option κ → ℂ) :=
  haveI := compactSpace_delzantQuotient (isBounded_facetPolyhedron_simplex (κ := κ) a)
  have hf : ∀ θ ∈ (facetTorusHom ((Int.castAddHom ℝ).compLeft κ) (simplexNormal κ) (2 * π)).ker,
      ∀ x : delzantLevel ((Int.castAddHom ℝ).compLeft κ) (simplexNormal κ) (simplexSupport a),
        Projectivization.mk ℂ _
            (complexEuclideanEquivRealProd_symm_ne_zero_of_mem_delzantLevel_simplex ha
              (θ +ᵥ x).property) =
          Projectivization.mk ℂ _
            (complexEuclideanEquivRealProd_symm_ne_zero_of_mem_delzantLevel_simplex ha
              x.property) :=
    fun θ hθ x ↦
      (mk_eq_mk_iff_mk_complexEuclideanEquivRealProd_symm_eq ha).1 (mk_vadd_of_mem_ker hθ x)
  Continuous.homeoOfEquivCompactToT2 (f := Equiv.ofBijective (lift _ hf)
    ⟨fun q q' h ↦ by
      induction q using DelzantQuotient.inductionOn with | h x =>
      induction q' using DelzantQuotient.inductionOn with | h y =>
      rw [lift_mk, lift_mk] at h
      exact (mk_eq_mk_iff_mk_complexEuclideanEquivRealProd_symm_eq ha).2 h,
    fun p ↦ by
      obtain ⟨x, hx⟩ := exists_mk_complexEuclideanEquivRealProd_symm_eq ha p
      exact ⟨mk x, (lift_mk _ _ x).trans hx⟩⟩)
    (continuous_lift hf (Projectivization.continuous_mk (by fun_prop) _))

/-- The homeomorphism `simplexHomeomorph` sends the class of `z = q + i p` to the line `[z]`. -/
@[simp]
theorem simplexHomeomorph_mk (ha : 0 < a)
    (x : delzantLevel ((Int.castAddHom ℝ).compLeft κ) (simplexNormal κ) (simplexSupport a)) :
    simplexHomeomorph ha (mk x) =
      Projectivization.mk ℂ ⇑((complexEuclideanEquivRealProd (Option κ)).symm x)
        (complexEuclideanEquivRealProd_symm_ne_zero_of_mem_delzantLevel_simplex ha x.property) :=
  lift_mk _ _ x

/-- **The moment map of `ℂPⁿ`.** Under `simplexHomeomorph`, the reduced moment map of the residual
torus sends the line `[v]` of `ℂ^(Option κ)` to the covector with coordinates
`a |v_(some k)|² / ∑ o, |v_o|²`, the diagonal entries of `a` times the orthogonal projector onto
`[v]`, with the entry of the coordinate `none` dropped. -/
theorem reducedMomentMap_simplexHomeomorph_symm_mk (ha : 0 < a) {v : Option κ → ℂ} (hv : v ≠ 0)
    (k : κ) :
    reducedMomentMap (i := (Int.castAddHom ℝ).compLeft κ) (u := simplexNormal κ)
        (c := simplexSupport a) surjective_linearCombination_simplexNormal
        ((simplexHomeomorph ha).symm (Projectivization.mk ℂ v hv)) (Pi.single k 1 : κ → ℝ) =
      a * ‖v (some k)‖ ^ 2 / ∑ o, ‖v o‖ ^ 2 := by
  obtain ⟨x, hx⟩ := mk_surjective ((simplexHomeomorph ha).symm (Projectivization.mk ℂ v hv))
  rw [← hx]
  have h := congrArg (simplexHomeomorph ha) hx
  rw [Homeomorph.apply_symm_apply, simplexHomeomorph_mk,
    Projectivization.mk_eq_mk_iff' ℂ _ _ _ hv] at h
  obtain ⟨c, hc⟩ := h
  -- The complex coordinates of `x` are `c • v`, and `‖x‖² = 2a`.
  have hsum := norm_sq_mul_sum_norm_sq_eq_of_smul_eq x.property hc
  have hk := reducedMomentMap_mk_apply (i := (Int.castAddHom ℝ).compLeft κ) (u := simplexNormal κ)
    surjective_linearCombination_simplexNormal x (some k)
  simp only [simplexNormal_some, AddMonoidHom.compLeft_single, Int.coe_castAddHom, Int.cast_one,
    simplexSupport_some, add_zero] at hk
  rw [hk]
  have hxk : (x : EuclideanSpace ℝ (Option κ) × EuclideanSpace ℝ (Option κ)).1 (some k) ^ 2 +
      (x : EuclideanSpace ℝ (Option κ) × EuclideanSpace ℝ (Option κ)).2 (some k) ^ 2 =
        ‖c‖ ^ 2 * ‖v (some k)‖ ^ 2 := by
    have h := congrArg (‖·‖ ^ 2) (congrFun hc (some k))
    simpa [complexEuclideanEquivRealProd_symm_apply, Complex.sq_norm, Complex.normSq_add_mul_I,
      norm_mul, mul_pow] using h.symm
  have hs : ∑ o, ‖v o‖ ^ 2 ≠ 0 := fun h0 ↦ by
    rw [h0, mul_zero] at hsum
    linarith
  rw [hxk, eq_div_iff hs]
  linear_combination (‖v (some k)‖ ^ 2 / 2) * hsum

end DelzantQuotient

end TauCeti.Toric
