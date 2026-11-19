/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Transvection.Basic
public import TauCeti.Algebra.Homology.SquareZero

/-!
# Handle slides of a differential on a free module

Let `d` be a linear endomorphism of the free module `ι →₀ R` on a set `ι` of generators, over
a ring `R`, and let `a ≠ b` be two generators and `c ∈ R`. Changing the basis by the elementary
transvection `τ` that replaces the generator `a` by `a + c b` and fixes the others
(`Finsupp.transvection`) turns `d` into the conjugate `d' = τ ∘ d ∘ τ⁻¹`, the **handle slide**
of `d` (`LinearMap.handleSlide`). In Morse theory this is the algebraic form of a handle slide:
when a one-parameter family of Morse–Smale pairs passes a time at which a trajectory joins two
critical points `a` and `b` of the same index, the Morse complexes on the two sides of that time
differ by such a change of basis, with `c = ±1` (Milnor's basis theorem). Together with Gaussian
elimination at births and deaths of critical points, these are the elementary chain changes of a
generic one-parameter family of Morse functions. The identification of the Morse complexes on
the two sides of a handle slide is a geometric theorem, not proved here.

The handle slide of `d` is characterized by `d' ∘ τ = τ ∘ d` (`LinearMap.eq_handleSlide_iff`),
so `τ` is an isomorphism from the complex `d` to the complex `d'`. Consequently:

* `d'` squares to zero when `d` does (`LinearMap.handleSlide_comp_self`), and `τ` induces an
  isomorphism of homologies (`LinearMap.handleSlideHomologyEquiv`);
* on the generators, `d'` sends `i ≠ a` to `τ (d i)` (`LinearMap.handleSlide_single_of_ne`)
  and `a` to `τ (d a - c d b)` (`LinearMap.handleSlide_single_self`). When `a` occurs neither
  in `d a` nor in `d b`, as happens when `d` lowers a grading in which `a` and `b` have the same
  degree, this is `d a - c d b` (`LinearMap.handleSlide_single_self_of_apply_eq_zero`). In
  coefficients, for a generator `i ≠ a` the coefficient of `b` in `d' i` is that in `d i` plus
  the coefficient of `a` in `d i` times `c`, and the other coefficients of `d' i` are those of
  `d i`;
* if `d` lowers a grading `deg : ι → G` by one, that is `⟨d i, j⟩ ≠ 0` only when
  `deg i = deg j + 1`, and `deg a = deg b`, then `d'` lowers it by one as well
  (`LinearMap.eq_add_of_handleSlide_single_apply_ne_zero`);
* handle slides along the same pair compose by adding the coefficients
  (`LinearMap.handleSlide_handleSlide`), the slide with coefficient `0` is the identity
  (`LinearMap.handleSlide_zero`), and so the slide with coefficient `-c` undoes the slide with
  coefficient `c` (`LinearMap.handleSlide_handleSlide_neg`);
* handle slides commute with changes of coefficients along a ring homomorphism
  (`LinearMap.mapRange_handleSlide`), which relates integral and mod-two handle slides.

The transvection is Mathlib's `LinearEquiv.transvection` for the coordinate form at `a` and the
vector `c b`, which that form kills since `a ≠ b`, and the handle slide is the image of `d` under
Mathlib's conjugation `LinearEquiv.conjRingEquiv` of endomorphism rings, which also gives
`d' ∘ d' = τ ∘ (d ∘ d) ∘ τ⁻¹`.

## Main definitions

* `Finsupp.transvection`: the transvection `x ↦ x + (x a * c) b` of `ι →₀ R`.
* `LinearMap.handleSlide`: the handle slide `τ ∘ d ∘ τ⁻¹` of an endomorphism `d` of `ι →₀ R`.
* `LinearMap.handleSlideHomologyEquiv`: the isomorphism of homologies induced by `τ`.

## References

* J. Milnor, *Lectures on the h-cobordism theorem*, Princeton University Press, 1965, the basis
  theorem, by which sliding one handle over another changes a basis of the Morse chain complex
  by such an elementary operation.
* J. Cerf, *La stratification naturelle des espaces de fonctions différentiables réelles et le
  théorème de la pseudo-isotopie*, Publ. Math. IHÉS 39 (1970), for the generic one-parameter
  families of functions.
-/

public section

open Finsupp

namespace Finsupp

variable {R ι : Type*} [Ring R] {a b : ι}

/-- The elementary transvection of the free module `ι →₀ R` adding `c` times the generator `b` to
the generator `a`: it sends `x` to `x + single b (x a * c)`, so `single a r` to
`single a r + single b (r * c)`, and fixes the other generators. It is Mathlib's
`LinearEquiv.transvection` for the coordinate form at `a` and the vector `single b c`, which this
form kills because `a ≠ b`. -/
noncomputable def transvection (hab : a ≠ b) (c : R) : (ι →₀ R) ≃ₗ[R] (ι →₀ R) :=
  LinearEquiv.transvection (f := lapply a) (v := single b c) (by simp [hab])

variable (hab : a ≠ b) (c : R)

theorem transvection_apply (x : ι →₀ R) : transvection hab c x = x + single b (x a * c) := by
  simp [transvection, LinearMap.transvection.apply, smul_single]

/-- The transvection only changes the coefficient of `b`. -/
@[simp]
theorem transvection_apply_of_ne (x : ι →₀ R) {j : ι} (hj : j ≠ b) :
    transvection hab c x j = x j := by
  simp [transvection_apply, single_eq_of_ne hj]

/-- The transvection adds `c` times the coefficient of `a` to the coefficient of `b`. -/
@[simp]
theorem transvection_apply_right (x : ι →₀ R) : transvection hab c x b = x b + x a * c := by
  simp [transvection_apply]

@[simp]
theorem transvection_single_self (r : R) :
    transvection hab c (single a r) = single a r + single b (r * c) := by
  simp [transvection_apply]

@[simp]
theorem transvection_single_of_ne {i : ι} (hi : i ≠ a) (r : R) :
    transvection hab c (single i r) = single i r := by
  simp [transvection_apply, single_eq_of_ne hi.symm]

@[simp]
theorem transvection_zero : transvection hab (0 : R) = LinearEquiv.refl R (ι →₀ R) := by
  ext x : 1
  simp [transvection_apply]

/-- Transvections along the same pair of generators compose by adding their coefficients. -/
theorem transvection_trans (c' : R) :
    (transvection hab c).trans (transvection hab c') = transvection hab (c + c') := by
  ext x : 1
  simp [transvection_apply, single_eq_of_ne hab, mul_add, add_assoc]

@[simp]
theorem transvection_symm : (transvection hab c).symm = transvection hab (-c) := by
  ext x : 1
  rw [LinearEquiv.symm_apply_eq, ← LinearEquiv.trans_apply, transvection_trans, neg_add_cancel,
    transvection_zero, LinearEquiv.refl_apply]

/-- Transvections commute with changes of coefficients along a ring homomorphism. -/
theorem mapRange_transvection {R' : Type*} [Ring R'] (g : R →+* R') (x : ι →₀ R) :
    mapRange g (map_zero g) (transvection hab c x) =
      transvection hab (g c) (mapRange g (map_zero g) x) := by
  ext j
  by_cases hj : j = b
  · subst hj
    simp
  · simp [hj]

end Finsupp

namespace LinearMap

variable {R ι : Type*} [Ring R] (d : (ι →₀ R) →ₗ[R] (ι →₀ R)) {a b : ι} (hab : a ≠ b) (c : R)

/-- The **handle slide** of an endomorphism `d` of the free module `ι →₀ R`: its conjugate
`τ ∘ d ∘ τ⁻¹` by the transvection `τ = Finsupp.transvection hab c`, which replaces the generator
`a` by `a + c b`. This is the change of basis of a Morse complex at a slide of the handle of `a`
over the handle of `b`, with `c = ±1`. -/
noncomputable def handleSlide : (ι →₀ R) →ₗ[R] (ι →₀ R) :=
  (Finsupp.transvection hab c).conjRingEquiv d

theorem handleSlide_apply (x : ι →₀ R) :
    d.handleSlide hab c x =
      Finsupp.transvection hab c (d (Finsupp.transvection hab (-c) x)) := by
  simp [handleSlide]

/-- The transvection is a chain map from `d` to its handle slide. -/
theorem handleSlide_comp_transvection :
    d.handleSlide hab c ∘ₗ (Finsupp.transvection hab c).toLinearMap =
      (Finsupp.transvection hab c).toLinearMap ∘ₗ d := by
  refine LinearMap.ext fun x ↦ ?_
  simp only [handleSlide, coe_comp, LinearEquiv.coe_coe, Function.comp_apply,
    LinearEquiv.conjRingEquiv_apply_apply, LinearEquiv.symm_apply_apply]

/-- The handle slide is the unique endomorphism `e` for which the transvection is a chain map from
`d` to `e`. -/
theorem eq_handleSlide_iff {e : (ι →₀ R) →ₗ[R] (ι →₀ R)} :
    e = d.handleSlide hab c ↔
      e ∘ₗ (Finsupp.transvection hab c).toLinearMap =
        (Finsupp.transvection hab c).toLinearMap ∘ₗ d := by
  refine ⟨fun h ↦ h ▸ d.handleSlide_comp_transvection hab c, fun h ↦ LinearMap.ext fun x ↦ ?_⟩
  have hx := congr($h ((Finsupp.transvection hab c).symm x))
  simp only [coe_comp, LinearEquiv.coe_coe, Function.comp_apply,
    LinearEquiv.apply_symm_apply] at hx
  rw [hx, handleSlide, LinearEquiv.conjRingEquiv_apply_apply]

theorem handleSlide_comp_self (hd : d ∘ₗ d = 0) :
    d.handleSlide hab c ∘ₗ d.handleSlide hab c = 0 := by
  rw [handleSlide, ← Module.End.mul_eq_comp, ← map_mul, Module.End.mul_eq_comp, hd, map_zero]

@[simp]
theorem handleSlide_zero : d.handleSlide hab 0 = d :=
  LinearMap.ext fun x ↦ by simp [handleSlide]

/-- Handle slides along the same pair of generators compose by adding their coefficients. -/
theorem handleSlide_handleSlide (c' : R) :
    (d.handleSlide hab c).handleSlide hab c' = d.handleSlide hab (c + c') := by
  refine LinearMap.ext fun x ↦ ?_
  simp only [handleSlide, LinearEquiv.conjRingEquiv_apply_apply]
  rw [← Finsupp.transvection_trans hab c c', LinearEquiv.trans_apply,
    LinearEquiv.symm_trans_apply]

/-- The handle slide with coefficient `-c` undoes the handle slide with coefficient `c`. -/
@[simp]
theorem handleSlide_handleSlide_neg : (d.handleSlide hab c).handleSlide hab (-c) = d := by
  rw [handleSlide_handleSlide, add_neg_cancel, handleSlide_zero]

/-- The coefficient of `j` in the image of `r` times a generator `i` is `r` times the coefficient
of `j` in the image of `i`. -/
private theorem apply_single_apply (i j : ι) (r : R) :
    d (Finsupp.single i r) j = r * d (Finsupp.single i 1) j := by
  rw [← Finsupp.smul_single_one, map_smul, Finsupp.smul_apply, smul_eq_mul]

/-- On a generator `i ≠ a`, the handle slide is `τ (d i)`: the coefficient of `b` gains `c` times
the coefficient of `a`. -/
theorem handleSlide_single_of_ne {i : ι} (hi : i ≠ a) (r : R) :
    d.handleSlide hab c (Finsupp.single i r) =
      Finsupp.transvection hab c (d (Finsupp.single i r)) := by
  rw [handleSlide_apply, Finsupp.transvection_single_of_ne hab _ hi]

/-- On the generator `a`, the handle slide is `τ (d a - c d b)`. -/
theorem handleSlide_single_self (r : R) :
    d.handleSlide hab c (Finsupp.single a r) =
      Finsupp.transvection hab c (d (Finsupp.single a r) - d (Finsupp.single b (r * c))) := by
  rw [handleSlide_apply, transvection_single_self, ← map_sub, mul_neg, Finsupp.single_neg,
    sub_eq_add_neg]

/-- If `a` occurs neither in `d a` nor in `d b`, the handle slide sends `a` to `d a - c d b`. -/
theorem handleSlide_single_self_of_apply_eq_zero (ha : d (Finsupp.single a 1) a = 0)
    (hb : d (Finsupp.single b 1) a = 0) (r : R) :
    d.handleSlide hab c (Finsupp.single a r) =
      d (Finsupp.single a r) - d (Finsupp.single b (r * c)) := by
  rw [handleSlide_single_self, transvection_apply, add_eq_left, Finsupp.single_eq_zero,
    Finsupp.sub_apply, apply_single_apply, apply_single_apply d b, ha, hb]
  simp

/-- **Handle slides preserve the grading.** If `d` lowers a grading `deg` of the generators by one
and the generators `a` and `b` have the same degree, then the handle slide of `d` lowers `deg` by
one as well. -/
theorem eq_add_of_handleSlide_single_apply_ne_zero {G : Type*} [Add G] [One G] (deg : ι → G)
    (hdeg : deg a = deg b) (hd : ∀ i j, d (Finsupp.single i 1) j ≠ 0 → deg i = deg j + 1)
    {i j : ι} (hij : d.handleSlide hab c (Finsupp.single i 1) j ≠ 0) : deg i = deg j + 1 := by
  contrapose! hij
  have hd' : ∀ i' j', deg i' ≠ deg j' + 1 → d (Finsupp.single i' 1) j' = 0 :=
    fun i' j' h ↦ by_contra fun h' ↦ h (hd i' j' h')
  by_cases hi : i = a
  · subst i
    have hbj : d (Finsupp.single b c) j = 0 := by
      rw [apply_single_apply, hd' b j (hdeg ▸ hij), mul_zero]
    rw [handleSlide_single_self, one_mul]
    by_cases hj : j = b
    · subst j
      have hbb : deg b ≠ deg b + 1 := hdeg ▸ hij
      have hba : d (Finsupp.single b c) a = 0 := by
        rw [apply_single_apply, hd' b a (by rwa [hdeg]), mul_zero]
      simp [hd' a a (by rwa [hdeg]), hd' a b hij, hba, hbj]
    · simp [hj, hd' a j hij, hbj]
  · rw [handleSlide_single_of_ne d hab c hi]
    by_cases hj : j = b
    · subst j
      simp [hd' i b hij, hd' i a (by rwa [hdeg])]
    · simp [hj, hd' i j hij]

/-- The isomorphism of homologies from a square-zero endomorphism to its handle slide, induced by
the transvection. -/
noncomputable def handleSlideHomologyEquiv (hd : d ∘ₗ d = 0) :
    d.homology hd ≃ₗ[R] (d.handleSlide hab c).homology (d.handleSlide_comp_self hab c hd) :=
  (Finsupp.transvection hab c).homologyEquiv hd _ (d.handleSlide_comp_transvection hab c).symm

@[simp]
theorem handleSlideHomologyEquiv_mk (hd : d ∘ₗ d = 0) (z : ker d) :
    d.handleSlideHomologyEquiv hab c hd (Submodule.Quotient.mk z) =
      Submodule.Quotient.mk ⟨Finsupp.transvection hab c z,
        map_mem_ker_of_comp_eq (Finsupp.transvection hab c).toLinearMap
          (d.handleSlide_comp_transvection hab c).symm z.2⟩ :=
  LinearEquiv.homologyEquiv_mk _ _ _ _ z

/-- Handle slides commute with changes of coefficients along a ring homomorphism `g`: if `d'`
corresponds to `d` under `g`, then the handle slide of `d'` with coefficient `g c` corresponds to
the handle slide of `d` with coefficient `c`. -/
theorem mapRange_handleSlide {R' : Type*} [Ring R'] (g : R →+* R')
    {d' : (ι →₀ R') →ₗ[R'] (ι →₀ R')}
    (hg : ∀ x, mapRange g (map_zero g) (d x) = d' (mapRange g (map_zero g) x)) (x : ι →₀ R) :
    mapRange g (map_zero g) (d.handleSlide hab c x) =
      d'.handleSlide hab (g c) (mapRange g (map_zero g) x) := by
  rw [handleSlide_apply, handleSlide_apply, mapRange_transvection, hg, mapRange_transvection,
    map_neg]

end LinearMap
