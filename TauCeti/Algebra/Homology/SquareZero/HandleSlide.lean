/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.SquareZero
public import TauCeti.LinearAlgebra.Finsupp.LSum
public import TauCeti.LinearAlgebra.Finsupp.Transvection

/-!
# Handle slides of a differential on a free module

Let `d` be a linear endomorphism of the free module `ι →₀ R` on a set `ι` of generators, over
a ring `R`, and let `a ≠ b` be two generators and `c ∈ R`. Let `τ` be the elementary
transvection that sends the generator `a` to `a + c b` and fixes the others
(`Finsupp.transvection`). The conjugate `d' = τ ∘ d ∘ τ⁻¹`, the **handle slide** of `d`
(`LinearMap.handleSlide`), is the matrix of `d` in the basis obtained by replacing the generator
`a` by `τ⁻¹ a = a - c b`, `τ` being the corresponding change of coordinates. In Morse theory
this is the algebraic form of a handle slide: when a one-parameter family of Morse–Smale pairs
passes a time at which a trajectory joins two critical points `a` and `b` of the same index, the
Morse complexes on the two sides of that time differ by such a change of basis, with `c = ±1`
(Milnor's basis theorem). Together with Gaussian elimination at births and deaths of critical
points, these are the elementary chain changes of a generic one-parameter family of Morse
functions. The identification of the Morse complexes on the two sides of a handle slide is a
geometric theorem, not proved here.

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

The handle slide is the image of `d` under Mathlib's conjugation `LinearEquiv.conjRingEquiv` of
endomorphism rings, so its chain-map, square-zero and homology statements are the cases
`f = τ` of those for conjugation by any semilinear equivalence `f`
(`LinearEquiv.eq_conjRingEquiv_apply_iff`, `LinearEquiv.conjRingEquiv_apply_comp_self`,
`LinearEquiv.conjHomologyEquiv`).

## Main definitions

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

namespace LinearMap

variable {R ι : Type*} [Ring R] (d : (ι →₀ R) →ₗ[R] (ι →₀ R)) {a b : ι} (hab : a ≠ b) (c : R)

/-- The **handle slide** of an endomorphism `d` of the free module `ι →₀ R`: its conjugate
`τ ∘ d ∘ τ⁻¹` by the transvection `τ = Finsupp.transvection hab c`, which sends the generator `a`
to `a + c b`. It is the matrix of `d` in the basis obtained by replacing the generator `a` by
`a - c b`. This is the change of basis of a Morse complex at a slide of the handle of `a` over the
handle of `b`, with `c = ±1`. -/
noncomputable def handleSlide : (ι →₀ R) →ₗ[R] (ι →₀ R) :=
  (Finsupp.transvection hab c).conjRingEquiv d

theorem handleSlide_apply (x : ι →₀ R) :
    d.handleSlide hab c x =
      Finsupp.transvection hab c (d (Finsupp.transvection hab (-c) x)) := by
  simp [handleSlide]

/-- The transvection is a chain map from `d` to its handle slide. -/
theorem handleSlide_comp_transvection :
    d.handleSlide hab c ∘ₗ (Finsupp.transvection hab c).toLinearMap =
      (Finsupp.transvection hab c).toLinearMap ∘ₗ d :=
  (Finsupp.transvection hab c).conjRingEquiv_apply_comp d

/-- The handle slide is the unique endomorphism `e` for which the transvection is a chain map from
`d` to `e`. -/
theorem eq_handleSlide_iff {e : (ι →₀ R) →ₗ[R] (ι →₀ R)} :
    e = d.handleSlide hab c ↔
      e ∘ₗ (Finsupp.transvection hab c).toLinearMap =
        (Finsupp.transvection hab c).toLinearMap ∘ₗ d :=
  (Finsupp.transvection hab c).eq_conjRingEquiv_apply_iff d

/-- The handle slide of a square-zero endomorphism squares to zero. -/
theorem handleSlide_comp_self (hd : d ∘ₗ d = 0) :
    d.handleSlide hab c ∘ₗ d.handleSlide hab c = 0 :=
  (Finsupp.transvection hab c).conjRingEquiv_apply_comp_self hd

@[simp]
theorem handleSlide_zero : d.handleSlide hab 0 = d :=
  LinearMap.ext fun x ↦ by simp [handleSlide]

/-- Handle slides along the same pair of generators compose by adding their coefficients. -/
@[simp]
theorem handleSlide_handleSlide (c' : R) :
    (d.handleSlide hab c).handleSlide hab c' = d.handleSlide hab (c + c') := by
  refine LinearMap.ext fun x ↦ ?_
  simp only [handleSlide, LinearEquiv.conjRingEquiv_apply_apply]
  rw [← Finsupp.transvection_trans hab c c', LinearEquiv.trans_apply,
    LinearEquiv.symm_trans_apply]

/-- The handle slide with coefficient `-c` undoes the handle slide with coefficient `c`. -/
theorem handleSlide_handleSlide_neg : (d.handleSlide hab c).handleSlide hab (-c) = d := by
  rw [handleSlide_handleSlide, add_neg_cancel, handleSlide_zero]

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
  rw [handleSlide_apply]
  simp [sub_eq_add_neg]

/-- If `a` occurs neither in `d a` nor in `d b`, the handle slide sends `a` to `d a - c d b`. -/
theorem handleSlide_single_self_of_apply_eq_zero (ha : d (Finsupp.single a 1) a = 0)
    (hb : d (Finsupp.single b 1) a = 0) (r : R) :
    d.handleSlide hab c (Finsupp.single a r) =
      d (Finsupp.single a r) - d (Finsupp.single b (r * c)) := by
  rw [handleSlide_single_self, Finsupp.transvection_apply]
  simp [d.apply_single_apply_eq_mul a r a, d.apply_single_apply_eq_mul b (r * c) a, ha, hb]

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
      rw [d.apply_single_apply_eq_mul, hd' b j (hdeg ▸ hij), mul_zero]
    rw [handleSlide_single_self, one_mul]
    by_cases hj : j = b
    · subst j
      have hbb : deg b ≠ deg b + 1 := hdeg ▸ hij
      have hba : d (Finsupp.single b c) a = 0 := by
        rw [d.apply_single_apply_eq_mul, hd' b a (hdeg ▸ hbb), mul_zero]
      simp [hd' a a (hdeg ▸ hbb), hd' a b hij, hba, hbj]
    · simp [hj, hd' a j hij, hbj]
  · rw [handleSlide_single_of_ne d hab c hi]
    by_cases hj : j = b
    · subst j
      simp [hd' i b hij, hd' i a (hdeg ▸ hij)]
    · simp [hj, hd' i j hij]

/-- The isomorphism of homologies from a square-zero endomorphism to its handle slide, induced by
the transvection. -/
noncomputable def handleSlideHomologyEquiv (hd : d ∘ₗ d = 0) :
    d.homology hd ≃ₗ[R] (d.handleSlide hab c).homology (d.handleSlide_comp_self hab c hd) :=
  (Finsupp.transvection hab c).conjHomologyEquiv hd

@[simp]
theorem handleSlideHomologyEquiv_mk (hd : d ∘ₗ d = 0) (z : ker d) :
    d.handleSlideHomologyEquiv hab c hd (Submodule.Quotient.mk z) =
      Submodule.Quotient.mk ⟨Finsupp.transvection hab c z,
        map_mem_ker_of_comp_eq (Finsupp.transvection hab c).toLinearMap
          (d.handleSlide_comp_transvection hab c).symm z.property⟩ :=
  (Finsupp.transvection hab c).conjHomologyEquiv_mk hd z

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
