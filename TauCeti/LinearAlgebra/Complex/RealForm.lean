/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.IsTensorProduct
public import TauCeti.LinearAlgebra.Complex.Conjugation
import TauCeti.RingTheory.TensorProduct.IsBaseChange

/-!
# Recognising a complex vector space as a complexification

Let `V` be a complex vector space that is also a real vector space, the two structures being
compatible (`IsScalarTower ℝ ℂ V`), and let `f : W →ₗ[ℝ] V` be a real-linear map.  This file
characterises when `f` exhibits `V` as the complexification `ℂ ⊗[ℝ] W` of `W`, in the sense of
Mathlib's `IsBaseChange ℂ f`: exactly when every vector of `V` is **uniquely** of the form
`f x + I • f y` (`LinearMap.isBaseChange_complex_iff`).  The two halves of this criterion are
separately the description of the image and the injectivity of the induced map
`f.liftBaseChange ℂ : ℂ ⊗[ℝ] W →ₗ[ℂ] V`.  Both rest on the splitting of every element of
`ℂ ⊗[ℝ] W` as `1 ⊗ₜ x + I ⊗ₜ y` (`TauCeti.exists_one_tmul_add_I_tmul`).

The real structure on `V` is an independent instance rather than the one Mathlib derives from the
complex structure (`Module.complexToReal`), so that the criterion applies to spaces such as
`Matrix n n ℂ` that carry their own real structure.

The criterion is then specialised to skew-adjoint vectors.  In a complex star module the
skew-adjoint vectors `v⋆ = -v` form a real form: every vector is `x + I • y` with `x, y`
skew-adjoint, namely `x = I • ℑ v` and `y = -I • ℜ v`, and `x + I • y = 0` forces `x = y = 0`
because applying the star turns it into `-x + I • y = 0`.  So a real-linear isomorphism onto the
skew-adjoint vectors exhibits `V` as their complexification
(`LinearMap.isBaseChange_complex_of_star_eq_neg`).  The leading example is the Lie algebra
`𝔲(n)` of skew-Hermitian matrices inside `𝔤𝔩(n, ℂ)`.

## Main results

* `LinearMap.mem_range_liftBaseChange_complex_iff`: the image of `ℂ ⊗[ℝ] W → V` consists of the
  vectors `f x + I • f y`.
* `LinearMap.liftBaseChange_complex_injective_iff`: the map `ℂ ⊗[ℝ] W → V` is injective exactly
  when `f x + I • f y = 0` forces `x = y = 0`.
* `LinearMap.isBaseChange_complex_iff`: **`f` is a complexification exactly when every vector is
  uniquely `f x + I • f y`.**
* `LinearMap.liftBaseChange_complex_injective_of_star_eq_neg`: an injective map with
  skew-adjoint values induces an injective map on the complexification.
* `LinearMap.isBaseChange_complex_of_star_eq_neg`: a real-linear isomorphism onto the
  skew-adjoint vectors of a complex star module is a complexification.

## References

* A. W. Knapp, *Lie Groups Beyond an Introduction*, second edition, Birkhäuser, 2002, Section I.3
  (complexifications and real forms).
-/

public section

open Complex TensorProduct
open scoped ComplexStarModule

namespace LinearMap

variable {V W : Type*} [AddCommGroup V] [Module ℂ V] [Module ℝ V] [IsScalarTower ℝ ℂ V]
  [AddCommGroup W] [Module ℝ W] (f : W →ₗ[ℝ] V)

/-- The image of the complexified map `ℂ ⊗[ℝ] W → V`, `c ⊗ₜ w ↦ c • f w`, consists of the
vectors `f x + I • f y`. -/
theorem mem_range_liftBaseChange_complex_iff {v : V} :
    v ∈ range (f.liftBaseChange ℂ) ↔ ∃ x y : W, f x + I • f y = v := by
  constructor
  · rintro ⟨u, rfl⟩
    obtain ⟨x, y, rfl⟩ := TauCeti.exists_one_tmul_add_I_tmul u
    exact ⟨x, y, by simp⟩
  · rintro ⟨x, y, rfl⟩
    exact ⟨1 ⊗ₜ[ℝ] x + I ⊗ₜ[ℝ] y, by simp⟩

/-- The complexified map `ℂ ⊗[ℝ] W → V` is injective exactly when the only relation
`f x + I • f y = 0` is the trivial one. -/
theorem liftBaseChange_complex_injective_iff :
    Function.Injective (f.liftBaseChange ℂ) ↔ ∀ x y : W, f x + I • f y = 0 → x = 0 ∧ y = 0 := by
  rw [injective_iff_map_eq_zero]
  constructor
  · intro h x y hxy
    have h0 : (1 : ℂ) ⊗ₜ[ℝ] x + I ⊗ₜ[ℝ] y = 0 := h _ (by simpa using hxy)
    -- The real-part retraction reads off `x`, and after multiplying by `-I` it reads off `y`.
    refine ⟨by simpa using congrArg (TauCeti.realPart W) h0, ?_⟩
    simpa [smul_add, smul_tmul'] using congrArg (fun u ↦ TauCeti.realPart W ((-I) • u)) h0
  · intro h u hu
    obtain ⟨x, y, rfl⟩ := TauCeti.exists_one_tmul_add_I_tmul u
    obtain ⟨rfl, rfl⟩ := h x y (by simpa using hu)
    simp

/-- **Recognising a complexification.**  A real-linear map `f : W →ₗ[ℝ] V` into a complex vector
space exhibits `V` as the complexification of `W` exactly when every vector of `V` is uniquely of
the form `f x + I • f y`. -/
theorem isBaseChange_complex_iff :
    IsBaseChange ℂ f ↔ ∀ v : V, ∃! p : W × W, f p.1 + I • f p.2 = v := by
  rw [IsBaseChange.iff_liftBaseChange_bijective, Function.Bijective,
    liftBaseChange_complex_injective_iff]
  constructor
  · rintro ⟨hinj, hsurj⟩ v
    obtain ⟨x, y, hxy⟩ := f.mem_range_liftBaseChange_complex_iff.1 (mem_range.2 (hsurj v))
    refine ⟨(x, y), hxy, fun p hp ↦ ?_⟩
    obtain ⟨h₁, h₂⟩ := hinj (p.1 - x) (p.2 - y) (by
      rw [map_sub, map_sub, smul_sub, sub_add_sub_comm, hp, hxy, sub_self])
    exact Prod.ext (sub_eq_zero.1 h₁) (sub_eq_zero.1 h₂)
  · intro h
    refine ⟨fun x y hxy ↦ ?_, fun v ↦ ?_⟩
    · have h0 := (h 0).unique (y₁ := (x, y)) (y₂ := (0, 0)) hxy (by simp)
      exact ⟨congrArg Prod.fst h0, congrArg Prod.snd h0⟩
    · obtain ⟨p, hp, -⟩ := h v
      exact mem_range.1 (f.mem_range_liftBaseChange_complex_iff.2 ⟨p.1, p.2, hp⟩)

variable [StarAddMonoid V] [StarModule ℂ V]

/-- An injective real-linear map whose values are skew-adjoint induces an injective map
`ℂ ⊗[ℝ] W → V`: applying the star to a relation `f x + I • f y = 0` gives `-f x + I • f y = 0`,
so both terms vanish. -/
theorem liftBaseChange_complex_injective_of_star_eq_neg (hf : Function.Injective f)
    (hskew : ∀ x, star (f x) = -f x) : Function.Injective (f.liftBaseChange ℂ) := by
  refine f.liftBaseChange_complex_injective_iff.2 fun x y hxy ↦ ?_
  have hstar : -f x + I • f y = 0 := by
    simpa [star_smul, hskew] using congrArg star hxy
  have hx : f x = 0 := by
    have h2 : (2 : ℂ) • f x = 0 := by
      rw [two_smul, ← sub_neg_eq_add, ← add_sub_add_right_eq_sub _ _ (I • f y), hxy, hstar,
        sub_zero]
    simpa using h2
  have hy : f y = 0 := by simpa [hx] using hxy
  exact ⟨hf (hx.trans (map_zero f).symm), hf (hy.trans (map_zero f).symm)⟩

/-- **The skew-adjoint vectors of a complex star module are a real form of it.**  A real-linear
map that is injective and maps onto the skew-adjoint vectors exhibits `V` as the complexification
of its source: every vector is `I • ℑ v + I • (-I • ℜ v)`, a combination of two skew-adjoint
vectors. -/
theorem isBaseChange_complex_of_star_eq_neg (hf : Function.Injective f)
    (hskew : ∀ x, star (f x) = -f x) (hsurj : ∀ v : V, star v = -v → ∃ x, f x = v) :
    IsBaseChange ℂ f := by
  have hinj := f.liftBaseChange_complex_injective_of_star_eq_neg hf hskew
  have hsurj' : Function.Surjective (f.liftBaseChange ℂ) := fun v ↦ by
    obtain ⟨x, hx⟩ := hsurj (I • (ℑ v : V)) (by simp [star_smul])
    obtain ⟨y, hy⟩ := hsurj ((-I) • (ℜ v : V)) (by simp [star_smul])
    refine (f.mem_range_liftBaseChange_complex_iff).2 ⟨x, y, ?_⟩
    rw [hx, hy, smul_smul, mul_neg, I_mul_I, neg_neg, one_smul, add_comm]
    exact realPart_add_I_smul_imaginaryPart v
  exact IsBaseChange.iff_liftBaseChange_bijective.2 ⟨hinj, hsurj'⟩

end LinearMap
