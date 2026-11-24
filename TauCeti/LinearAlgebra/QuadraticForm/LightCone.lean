/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Basic.Sign.Basic
public import Mathlib.LinearAlgebra.QuadraticForm.Signature
public import TauCeti.LinearAlgebra.QuadraticForm.Radical
import Mathlib.Algebra.QuadraticDiscriminant
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import TauCeti.LinearAlgebra.QuadraticForm.PosDef

/-!
# Vectors orthogonal to a maximal positive-definite subspace, and the light cone

Let `Q` be a quadratic form on a finite-dimensional vector space over a linearly ordered field,
and let `P` be a subspace on which `Q` is positive definite and whose dimension is the positive
index of inertia `sigPos Q`. Then `Q` is negative semidefinite on the polar-orthogonal complement
of `P`: a vector `x` orthogonal to `P` with `Q x > 0` would enlarge `P` to a positive-definite
subspace of larger dimension (`QuadraticForm.apply_nonpos_of_mem_orthogonal`). If moreover `Q` is
nondegenerate, so is its restriction to that complement, and a vector of the complement with
`Q x ≥ 0` vanishes (`QuadraticForm.eq_zero_of_mem_orthogonal_of_nonneg`).

For the intersection form of a closed oriented four-manifold `X` and a metric `g`, `P` is the
space of self-dual harmonic forms, of dimension `b₂⁺(X)`, and the complement is the space of
anti-self-dual harmonic forms. The second statement says that a nonzero class `l` with `l² ≥ 0`
has a nonzero self-dual part `l⁺`, whatever the metric. This is how a Seiberg–Witten label with
`l² ≥ 0` is kept off the wall `l⁺ = 0`.

When `Q` is nondegenerate and `sigPos Q ≤ 1`, every vector `y` with `Q y > 0` spans such a subspace,
so a vector `x` with `Q x ≥ 0` and `polar Q x y = 0` vanishes
(`QuadraticForm.eq_zero_of_polar_eq_zero_of_nonneg`). This is the light-cone lemma of Lorentzian
geometry: a timelike vector is orthogonal to no nonzero causal vector. It implies that the sign of
`polar Q x y`, for a fixed nonzero `x` with `Q x ≥ 0`, is the same for all `y` in one component of
the cone `{y | Q y > 0}`: if `Q y > 0`, `Q z > 0` and `polar Q y z > 0`, then `polar Q x y` and
`polar Q x z` have the same sign (`QuadraticForm.sign_polar_eq_sign_polar`). For a four-manifold
with `b₂⁺ = 1`, the class `[ω_g]` of a self-dual harmonic form lies in the cone of positive classes.
So for a nonzero class `l` with `l² ≥ 0`, the sign of `l · [ω_g]`, which places `l` in a
Seiberg–Witten chamber, is the same for all metrics whose classes `[ω_g]` are normalized to pair
positively with a fixed positive class, for instance the class of a symplectic form.

## Main results

* `QuadraticForm.apply_nonpos_of_mem_orthogonal`: `Q ≤ 0` on the orthogonal complement of a
  positive-definite subspace of dimension `sigPos Q`.
* `QuadraticForm.eq_zero_of_mem_orthogonal_of_nonneg`: for nondegenerate `Q`, a vector of that
  complement with `Q x ≥ 0` vanishes.
* `QuadraticForm.eq_zero_of_polar_eq_zero_of_nonneg`: for nondegenerate `Q` with `sigPos Q ≤ 1`, a
  vector with `Q x ≥ 0` orthogonal to a vector `y` with `Q y > 0` vanishes.
* `QuadraticForm.sign_polar_eq_sign_polar`: for nondegenerate `Q` with `sigPos Q ≤ 1` and a
  nonzero `x` with `Q x ≥ 0`, the sign of `polar Q x y` is constant on each component of the
  positive cone.

## References

* B. O'Neill, *Semi-Riemannian Geometry with Applications to Relativity*, Academic Press, 1983,
  Chapter 5, Lemmas 26 and 29.
* R. E. Gompf and A. I. Stipsicz, *4-Manifolds and Kirby Calculus*, Graduate Studies in
  Mathematics 20, AMS, 1999, Section 2.4.
-/

public section

open Module QuadraticMap

namespace QuadraticForm

variable {K M : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K] [AddCommGroup M]
  [Module K M] [FiniteDimensional K M] {Q : QuadraticForm K M}

/-- **Negativity off a maximal positive-definite subspace.** If `Q` is positive definite on a
subspace `P` of dimension at least the positive index of inertia, then `Q` is negative
semidefinite on the polar-orthogonal complement of `P`. -/
theorem apply_nonpos_of_mem_orthogonal {P : Submodule K M} (hP : (Q.restrict P).PosDef)
    (hsig : sigPos Q ≤ finrank K P) {x : M}
    (hx : x ∈ LinearMap.BilinForm.orthogonal Q.polarBilin P) : Q x ≤ 0 := by
  by_contra! hpos
  have horth (p : M) (hp : p ∈ P) : polar Q p x = 0 := by
    simpa using LinearMap.BilinForm.mem_orthogonal_iff.mp hx p hp
  have hx0 : x ≠ 0 := by
    rintro rfl
    simp at hpos
  have hxP : x ∉ P := fun h ↦ by
    have h2 := horth x h
    rw [polar_self, two_nsmul] at h2
    linarith
  -- `P ⊔ K ∙ x` is positive definite, of dimension `finrank P + 1`.
  have hW : (Q.restrict (P ⊔ K ∙ x)).PosDef := by
    rintro ⟨w, hw⟩ hw0
    obtain ⟨p, hp, y, hy, rfl⟩ := Submodule.mem_sup.mp hw
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hy
    rw [restrict_apply, QuadraticMap.map_add Q, QuadraticMap.map_smul, polar_smul_right,
      horth p hp, smul_zero, add_zero, smul_eq_mul]
    by_cases hp0 : p = 0
    · subst hp0
      simpa [QuadraticMap.map_smul] using
        posDef_restrict_span_singleton hpos ⟨c • x, hy⟩ (by simpa using hw0)
    · exact add_pos_of_pos_of_nonneg (hP ⟨p, hp⟩ (by simpa using hp0))
        (mul_nonneg (mul_self_nonneg c) hpos.le)
  have hdim := Submodule.finrank_sup_add_finrank_inf_eq P (K ∙ x)
  rw [disjoint_iff.mp ((Submodule.disjoint_span_singleton' hx0).mpr hxP), finrank_bot,
    finrank_span_singleton hx0] at hdim
  have := le_sigPos_of_posDef Q hW
  omega

/-- **The orthogonal complement of a maximal positive-definite subspace is negative definite.**
If `Q` is nondegenerate and positive definite on a subspace `P` of dimension at least the
positive index of inertia, then a vector `x` polar-orthogonal to `P` with `Q x ≥ 0` vanishes. -/
theorem eq_zero_of_mem_orthogonal_of_nonneg (hQ : Q.Nondegenerate) {P : Submodule K M}
    (hP : (Q.restrict P).PosDef) (hsig : sigPos Q ≤ finrank K P) {x : M}
    (hx : x ∈ LinearMap.BilinForm.orthogonal Q.polarBilin P) (hx0 : 0 ≤ Q x) : x = 0 := by
  let _ : Invertible (2 : K) := invertibleOfNonzero two_ne_zero
  have hQx : Q x = 0 := le_antisymm (apply_nonpos_of_mem_orthogonal hP hsig hx) hx0
  have hcompl := Nondegenerate.isCompl_orthogonal hP.anisotropic.nondegenerate
  -- The polar functional of `x` vanishes on `P` by assumption, and on its complement because
  -- `s ↦ Q (x + s • n) = s * polar Q x n + s ^ 2 * Q n` is nowhere positive.
  have hpolar (z : M) : polar Q x z = 0 := by
    obtain ⟨p, hp, n, hn, rfl⟩ :=
      Submodule.mem_sup.mp (show z ∈ P ⊔ _ from hcompl.sup_eq_top ▸ Submodule.mem_top)
    have hpx : polar Q p x = 0 := by
      simpa using LinearMap.BilinForm.mem_orthogonal_iff.mp hx p hp
    rw [polar_add_right, polar_comm, hpx, zero_add]
    have hle (s : K) : Q n * (s * s) + polar Q x n * s + 0 ≤ 0 := by
      have h := apply_nonpos_of_mem_orthogonal hP hsig
        (Submodule.add_mem _ hx (Submodule.smul_mem _ s hn))
      rw [QuadraticMap.map_add Q, QuadraticMap.map_smul, polar_smul_right, hQx, smul_eq_mul,
        smul_eq_mul] at h
      linarith
    have h := discrim_le_zero_of_nonpos hle
    rw [discrim, mul_zero, sub_zero] at h
    exact pow_eq_zero_iff two_ne_zero |>.mp (le_antisymm h (sq_nonneg _))
  by_contra hx0'
  exact hQ.polarBilin_ne_zero hx0' (LinearMap.ext fun z ↦ hpolar z)

/-- **The light-cone lemma.** If `Q` is nondegenerate with positive index of inertia at most one,
then a vector `x` with `Q x ≥ 0` which is polar-orthogonal to a vector `y` with `Q y > 0`
vanishes. -/
theorem eq_zero_of_polar_eq_zero_of_nonneg (hQ : Q.Nondegenerate) (hsig : sigPos Q ≤ 1)
    {x y : M} (hy : 0 < Q y) (hxy : polar Q x y = 0) (hx : 0 ≤ Q x) : x = 0 := by
  have hy0 : y ≠ 0 := by
    rintro rfl
    simp at hy
  refine eq_zero_of_mem_orthogonal_of_nonneg hQ (P := K ∙ y)
    (posDef_restrict_span_singleton hy) ?_ ?_ hx
  · rwa [finrank_span_singleton hy0]
  · refine LinearMap.BilinForm.mem_orthogonal_iff.mpr fun w hw ↦ ?_
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hw
    rw [polarBilin_apply_apply, polar_smul_left, polar_comm, hxy, smul_zero]

/-- **The sign of a pairing with a causal vector is constant on each half of the positive cone.**
Let `Q` be nondegenerate with positive index of inertia at most one, and let `x ≠ 0` satisfy
`Q x ≥ 0`. If `Q y > 0`, `Q z > 0` and `polar Q y z > 0`, so that `y` and `z` lie in the same
component of the cone `{y | Q y > 0}`, then `polar Q x y` and `polar Q x z` have the same sign. -/
theorem sign_polar_eq_sign_polar (hQ : Q.Nondegenerate) (hsig : sigPos Q ≤ 1) {x y z : M}
    (hx : 0 ≤ Q x) (hx0 : x ≠ 0) (hy : 0 < Q y) (hz : 0 < Q z) (hyz : 0 < polar Q y z) :
    SignType.sign (polar Q x y) = SignType.sign (polar Q x z) := by
  set a := polar Q x y
  set b := polar Q x z
  have ha : a ≠ 0 := fun h ↦ hx0 (eq_zero_of_polar_eq_zero_of_nonneg hQ hsig hy h hx)
  have hb : b ≠ 0 := fun h ↦ hx0 (eq_zero_of_polar_eq_zero_of_nonneg hQ hsig hz h hx)
  -- If the signs differed, `w = -b • y + a • z` would satisfy `Q w > 0` and `polar Q x w = 0`.
  have hab : 0 < a * b := by
    by_contra! hab
    have hab' : a * b < 0 := lt_of_le_of_ne hab (mul_ne_zero ha hb)
    refine hx0 (eq_zero_of_polar_eq_zero_of_nonneg hQ hsig (y := -b • y + a • z) ?_ ?_ hx)
    · rw [QuadraticMap.map_add Q, QuadraticMap.map_smul, QuadraticMap.map_smul, polar_smul_left,
        polar_smul_right, smul_eq_mul, smul_eq_mul, smul_eq_mul, smul_eq_mul]
      have := mul_pos (mul_self_pos.mpr (neg_ne_zero.mpr hb)) hy
      have := mul_pos (mul_self_pos.mpr ha) hz
      nlinarith [hab']
    · rw [polar_add_right, polar_smul_right, polar_smul_right, smul_eq_mul, smul_eq_mul]
      ring
  rcases ha.lt_or_gt with ha' | ha'
  · rw [sign_neg ha', sign_neg (by nlinarith)]
  · rw [sign_pos ha', sign_pos (by nlinarith)]

end QuadraticForm
