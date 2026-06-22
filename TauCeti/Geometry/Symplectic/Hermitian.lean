/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.InnerProductSpace.Defs
import TauCeti.Geometry.Symplectic.CompatibleMetric
import TauCeti.Geometry.Symplectic.ComplexModule

/-!
# The Hermitian inner product of a compatible pair

A symplectic form `ω` compatible with an almost complex structure `J` packages the real metric
`g(v, w) = ω(v, J w)` and the symplectic form into a single complex Hermitian inner product
```
h(v, w) = g(v, w) + i ω(v, w) = ω(v, J w) + i ω(v, w)
```
on the complex vector space `(V, J)` (the complex structure of `ComplexModule.lean`, where
multiplication by `i` is `J`). This is the classical statement that a compatible triple
`(ω, J, g)` is the same data as a Hermitian structure (McDuff--Salamon, *J-holomorphic Curves and
Symplectic Topology*, Section 2.1, Remark 2.6.4): the real and imaginary parts of `h` recover the
metric and the symplectic form, `h` is conjugate-symmetric, it is complex linear in the second
argument over the `J`-induced complex structure, and it is positive definite.

This is the complex companion of `TauCeti.SymplecticForm.Compatible.innerProductCore`, which
records the real metric `g` of the same pair as an `InnerProductSpace.Core ℝ V`. Here the form is
built once, as `SymplecticForm.hermitianForm`, with the compatibility hypotheses entering only in
the Hermitian-structure facts, and the capstone `Compatible.hermitianCore` exhibits it as an
`InnerProductSpace.Core ℂ V` for the complex structure `J.complexModule`.

## Main declarations

* `TauCeti.SymplecticForm.hermitianForm`: the complex form `h(v, w) = ω(v, J w) + i ω(v, w)`.
* `TauCeti.SymplecticForm.hermitianForm_re` / `hermitianForm_im`: the real and imaginary parts of
  `h` are the metric `g(v, w) = ω(v, J w)` and the symplectic form `ω(v, w)`.
* `TauCeti.SymplecticForm.Compatible.hermitianForm_conj_symm`: `h` is conjugate-symmetric,
  `conj (h(w, v)) = h(v, w)`.
* `TauCeti.SymplecticForm.hermitianForm_smul_right`: `h` is complex linear in its second argument,
  `h(v, z • w) = z · h(v, w)`, for the complex structure `J.complexModule` (no compatibility
  needed).
* `TauCeti.SymplecticForm.Compatible.hermitianForm_self`: `h(v, v) = ω(v, J v)` is real and
  positive on nonzero vectors.
* `TauCeti.SymplecticForm.Compatible.hermitianCore`: the Hermitian inner product of a compatible
  pair as an `InnerProductSpace.Core ℂ V`.

The conventions follow McDuff--Salamon, *J-holomorphic Curves and Symplectic Topology*,
Section 2.1: a compatible pair `(ω, J)` gives the Hermitian form `⟨v, w⟩ = g(v, w) + i ω(v, w)`.
-/

namespace TauCeti

namespace SymplecticForm

variable {V : Type*} [AddCommGroup V] [Module ℝ V]

/-- The Hermitian form of a pair `(ω, J)`: `h(v, w) = ω(v, J w) + i ω(v, w)`.

Its real part is the metric `ω(·, J ·)` and its imaginary part is the symplectic form `ω`. The
Hermitian-structure facts (conjugate symmetry, complex linearity in the second argument, positive
definiteness) need `J² = -1` and compatibility; the bare definition does not. -/
noncomputable def hermitianForm (ω : SymplecticForm V) (J : AlmostComplexStructure V)
    (v w : V) : ℂ :=
  (ω v (J w) : ℂ) + Complex.I * (ω v w : ℂ)

lemma hermitianForm_apply (ω : SymplecticForm V) (J : AlmostComplexStructure V) (v w : V) :
    ω.hermitianForm J v w = (ω v (J w) : ℂ) + Complex.I * (ω v w : ℂ) := rfl

/-- The real part of the Hermitian form is the metric `g(v, w) = ω(v, J w)`. -/
@[simp]
lemma hermitianForm_re (ω : SymplecticForm V) (J : AlmostComplexStructure V) (v w : V) :
    (ω.hermitianForm J v w).re = ω v (J w) := by
  simp [hermitianForm]

/-- The imaginary part of the Hermitian form is the symplectic form `ω(v, w)`. -/
@[simp]
lemma hermitianForm_im (ω : SymplecticForm V) (J : AlmostComplexStructure V) (v w : V) :
    (ω.hermitianForm J v w).im = ω v w := by
  simp [hermitianForm]

/-- The Hermitian form is additive in its first argument. -/
lemma hermitianForm_add_left (ω : SymplecticForm V) (J : AlmostComplexStructure V)
    (v₁ v₂ w : V) :
    ω.hermitianForm J (v₁ + v₂) w = ω.hermitianForm J v₁ w + ω.hermitianForm J v₂ w := by
  simp only [hermitianForm, map_add, LinearMap.add_apply]
  push_cast
  ring

/-- The Hermitian form is additive in its second argument. -/
lemma hermitianForm_add_right (ω : SymplecticForm V) (J : AlmostComplexStructure V)
    (v w₁ w₂ : V) :
    ω.hermitianForm J v (w₁ + w₂) = ω.hermitianForm J v w₁ + ω.hermitianForm J v w₂ := by
  simp only [hermitianForm, map_add]
  push_cast
  ring

/-- Auxiliary real-scalar form of complex linearity in the second argument: feeding the real
decomposition `r.re • w + r.im • J w` of `r • w` to the second slot multiplies by `r`. This needs
only `J² = -1`, not compatibility. -/
lemma hermitianForm_smul_right_aux (ω : SymplecticForm V) (J : AlmostComplexStructure V)
    (r : ℂ) (v w : V) :
    ω.hermitianForm J v (r.re • w + r.im • J w) = r * ω.hermitianForm J v w := by
  have key1 : ω v (J (r.re • w + r.im • J w)) = r.re * ω v (J w) + r.im * -(ω v w) := by
    simp only [map_add, map_smul, smul_eq_mul, AlmostComplexStructure.apply_apply, map_neg]
  have key2 : ω v (r.re • w + r.im • J w) = r.re * ω v w + r.im * ω v (J w) := by
    simp only [map_add, map_smul, smul_eq_mul]
  simp only [hermitianForm, key1, key2]
  apply Complex.ext <;>
    simp only [Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im, Complex.ofReal_re,
      Complex.ofReal_im, Complex.I_re, Complex.I_im, Complex.neg_re, Complex.neg_im,
      Complex.ofReal_add, Complex.ofReal_mul, Complex.ofReal_neg] <;>
    ring

/-- The Hermitian form is complex linear in its second argument over the complex structure
`J.complexModule`: `h(v, z • w) = z · h(v, w)`. This is the defining property of a Hermitian inner
product on the complex vector space `(V, J)`, and needs only `J² = -1`, not compatibility. -/
lemma hermitianForm_smul_right (ω : SymplecticForm V) (J : AlmostComplexStructure V)
    (z : ℂ) (v w : V) :
    letI := J.complexModule
    ω.hermitianForm J v (z • w) = z * ω.hermitianForm J v w := by
  letI := J.complexModule
  rw [J.complexModule_smul_def]
  exact ω.hermitianForm_smul_right_aux J z v w

/-- The diagonal of the Hermitian form is real and equals the metric diagonal `ω(v, J v)`. -/
@[simp]
lemma hermitianForm_self (ω : SymplecticForm V) (J : AlmostComplexStructure V) (v : V) :
    ω.hermitianForm J v v = (ω v (J v) : ℂ) := by
  simp [hermitianForm]

namespace Compatible

variable {ω : SymplecticForm V} {J : AlmostComplexStructure V}

/-- The diagonal of the Hermitian form is positive on nonzero vectors. -/
lemma hermitianForm_self_re_pos (h : ω.Compatible J) {v : V} (hv : v ≠ 0) :
    0 < (ω.hermitianForm J v v).re := by
  rw [hermitianForm_re]
  exact h.associated_pos hv

/-- The real part of the diagonal of the Hermitian form is nonnegative, in the `RCLike.re` form
the inner-product-space core expects. -/
lemma hermitianForm_re_self_nonneg (h : ω.Compatible J) (v : V) :
    0 ≤ RCLike.re (ω.hermitianForm J v v) := by
  rw [ω.hermitianForm_self]
  simpa using h.symplecticForm_apply_apply_self_nonneg v

/-- The diagonal of the Hermitian form vanishes only at zero. -/
lemma hermitianForm_self_eq_zero (h : ω.Compatible J) {v : V}
    (hv : ω.hermitianForm J v v = 0) : v = 0 := by
  rw [ω.hermitianForm_self] at hv
  have hz : ω v (J v) = 0 := by exact_mod_cast hv
  rw [← associatedBilinForm_apply] at hz
  exact h.associatedBilinForm_self_eq_zero.mp hz

/-- The Hermitian form is conjugate-symmetric: `conj (h(w, v)) = h(v, w)`. -/
lemma hermitianForm_conj_symm (h : ω.Compatible J) (v w : V) :
    (starRingEnd ℂ) (ω.hermitianForm J w v) = ω.hermitianForm J v w := by
  have hg : ω w (J v) = ω v (J w) := (h.associatedBilinForm_apply_swap v w).symm
  have hω : ω w v = -(ω v w) := (ω.neg_eq v w).symm
  simp only [hermitianForm, map_add, map_mul, Complex.conj_ofReal, Complex.conj_I, hg, hω]
  push_cast
  ring

/-- Auxiliary real-scalar form of conjugate linearity in the first argument: feeding the real
decomposition `r.re • v + r.im • J v` of `r • v` to the first slot multiplies by `conj r`. -/
lemma hermitianForm_smul_left_aux (h : ω.Compatible J) (r : ℂ) (v w : V) :
    ω.hermitianForm J (r.re • v + r.im • J v) w
      = (starRingEnd ℂ) r * ω.hermitianForm J v w := by
  have hJvw : ω (J v) (J w) = ω v w := h.invariant_apply v w
  have hJv : ω (J v) w = -(ω v (J w)) := by
    have h1 : -ω (J v) w = ω w (J v) := ω.neg_eq (J v) w
    have h2 : ω v (J w) = ω w (J v) := h.associatedBilinForm_apply_swap v w
    linarith
  have key1 : ω (r.re • v + r.im • J v) (J w) = r.re * ω v (J w) + r.im * ω v w := by
    simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul, hJvw]
  have key2 : ω (r.re • v + r.im • J v) w = r.re * ω v w + r.im * -(ω v (J w)) := by
    simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul, hJv]
  simp only [hermitianForm, key1, key2]
  apply Complex.ext <;>
    simp only [Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im, Complex.ofReal_re,
      Complex.ofReal_im, Complex.I_re, Complex.I_im, Complex.conj_re, Complex.conj_im,
      Complex.neg_re, Complex.neg_im, Complex.ofReal_add, Complex.ofReal_mul,
      Complex.ofReal_neg] <;>
    ring

/-- The Hermitian form is conjugate linear in its first argument over the complex structure
`J.complexModule`: `h(z • v, w) = conj z · h(v, w)`. -/
lemma hermitianForm_smul_left (h : ω.Compatible J) (z : ℂ) (v w : V) :
    letI := J.complexModule
    ω.hermitianForm J (z • v) w = (starRingEnd ℂ) z * ω.hermitianForm J v w := by
  letI := J.complexModule
  rw [J.complexModule_smul_def]
  exact h.hermitianForm_smul_left_aux z v w

/-- The Hermitian inner product of a compatible pair, packaged as an `InnerProductSpace.Core ℂ V`
for the complex structure `J.complexModule`.

The inner product is `⟨v, w⟩ = ω(v, J w) + i ω(v, w)`, conjugate linear in the first argument and
complex linear in the second, with `⟨v, v⟩ = ω(v, J v) > 0` for `v ≠ 0`. -/
@[implicit_reducible]
noncomputable def hermitianCore (h : ω.Compatible J) :
    letI := J.complexModule
    InnerProductSpace.Core ℂ V :=
  letI := J.complexModule
  { inner := ω.hermitianForm J
    conj_inner_symm := h.hermitianForm_conj_symm
    re_inner_nonneg := h.hermitianForm_re_self_nonneg
    add_left := ω.hermitianForm_add_left J
    smul_left := fun v w z => h.hermitianForm_smul_left z v w
    definite := fun _ hv => h.hermitianForm_self_eq_zero hv }

/-- The inner product from `hermitianCore` is the Hermitian form `ω(v, J w) + i ω(v, w)`. -/
@[simp]
lemma hermitianCore_inner (h : ω.Compatible J) (v w : V) :
    letI := J.complexModule
    @inner ℂ V h.hermitianCore.toInner v w = (ω v (J w) : ℂ) + Complex.I * (ω v w : ℂ) :=
  rfl

end Compatible

end SymplecticForm

end TauCeti
