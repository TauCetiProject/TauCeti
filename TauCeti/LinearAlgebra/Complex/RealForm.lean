/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.IsTensorProduct
public import TauCeti.LinearAlgebra.Complex.Conjugation
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Module
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

The criterion is then specialised to real points.  If a conjugate-linear involution `K` of `V`
fixes exactly the values of an injective map `f`, then `f` is a complexification
(`LinearMap.isBaseChange_complex_of_conj`): injectivity is
`LinearMap.liftBaseChange_complex_injective_of_conj`, and every vector is the sum of its real part
and `I` times its imaginary part relative to `K`
(`TauCeti.conjRealPart_add_I_smul_conjImaginaryPart`).
In a complex star module the skew-adjoint vectors `v⋆ = -v` are the vectors fixed by `v ↦ -v⋆`, so
a real-linear isomorphism onto them exhibits `V` as their complexification
(`LinearMap.isBaseChange_complex_of_star_eq_neg`), and likewise for the skew-adjoint vectors of a
star-closed complex subspace (`LinearMap.isBaseChange_complex_codRestrict_of_star_eq_neg`).  The
leading examples are the Lie algebras `𝔲(n)` and `𝔰𝔲(n)` of skew-Hermitian matrices inside
`𝔤𝔩(n, ℂ)` and of trace-free skew-Hermitian matrices inside `𝔰𝔩(n, ℂ)`.

## Main results

* `LinearMap.mem_range_liftBaseChange_complex_iff`: the image of `ℂ ⊗[ℝ] W → V` consists of the
  vectors `f x + I • f y`.
* `LinearMap.liftBaseChange_complex_injective_iff`: the map `ℂ ⊗[ℝ] W → V` is injective exactly
  when `f x + I • f y = 0` forces `x = y = 0`.
* `LinearMap.isBaseChange_complex_iff`: **`f` is a complexification exactly when every vector is
  uniquely `f x + I • f y`.**
* `LinearMap.isBaseChange_complex_of_conj`: a real-linear isomorphism onto the real points of a
  conjugation is a complexification.
* `LinearMap.isBaseChange_complex_of_star_eq_neg`: a real-linear isomorphism onto the
  skew-adjoint vectors of a complex star module is a complexification.
* `LinearMap.isBaseChange_complex_codRestrict_of_star_eq_neg`: the same for the skew-adjoint
  vectors of a star-closed complex subspace.

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
      simp only [map_sub]
      linear_combination (norm := module) hp - hxy)
    exact Prod.ext (sub_eq_zero.1 h₁) (sub_eq_zero.1 h₂)
  · intro h
    refine ⟨fun x y hxy ↦ ?_, fun v ↦ ?_⟩
    · have h0 := (h 0).unique (y₁ := (x, y)) (y₂ := (0, 0)) hxy (by simp)
      exact ⟨congrArg Prod.fst h0, congrArg Prod.snd h0⟩
    · obtain ⟨p, hp, -⟩ := h v
      exact mem_range.1 (f.mem_range_liftBaseChange_complex_iff.2 ⟨p.1, p.2, hp⟩)

/-- **The real points of a conjugation are a real form.**  A real-linear map that is injective and
maps onto the vectors fixed by a conjugate-linear involution `K` exhibits `V` as the
complexification of its source.  Injectivity of the complexified map is
`LinearMap.liftBaseChange_complex_injective_of_conj`, and surjectivity is the decomposition
`v = TauCeti.conjRealPart K v + I • TauCeti.conjImaginaryPart K v` into two fixed vectors. -/
theorem isBaseChange_complex_of_conj {K : V →ₛₗ[starRingEnd ℂ] V} (hK : Function.Involutive K)
    (hf : Function.Injective f) (hfix : ∀ x, K (f x) = f x)
    (hsurj : ∀ v, K v = v → ∃ x, f x = v) : IsBaseChange ℂ f := by
  refine IsBaseChange.iff_liftBaseChange_bijective.2
    ⟨f.liftBaseChange_complex_injective_of_conj hf hfix, fun v ↦ ?_⟩
  obtain ⟨x, hx⟩ := hsurj _ (TauCeti.mem_realPoints.1 (TauCeti.conjRealPart_mem hK v))
  obtain ⟨y, hy⟩ := hsurj _ (TauCeti.mem_realPoints.1 (TauCeti.conjImaginaryPart_mem hK v))
  refine mem_range.1 (f.mem_range_liftBaseChange_complex_iff.2 ⟨x, y, ?_⟩)
  rw [hx, hy]
  exact TauCeti.conjRealPart_add_I_smul_conjImaginaryPart v

variable [StarAddMonoid V] [StarModule ℂ V]

/-- **The skew-adjoint vectors of a complex star module are a real form of it.**  A real-linear
map that is injective and maps onto the skew-adjoint vectors exhibits `V` as the complexification
of its source: the skew-adjoint vectors are the vectors fixed by the conjugation `v ↦ -v⋆`
(`LinearMap.isBaseChange_complex_of_conj`). -/
theorem isBaseChange_complex_of_star_eq_neg (hf : Function.Injective f)
    (hskew : ∀ x, star (f x) = -f x) (hsurj : ∀ v : V, star v = -v → ∃ x, f x = v) :
    IsBaseChange ℂ f :=
  f.isBaseChange_complex_of_conj (K := -(starLinearEquiv ℂ (A := V)).toLinearMap)
    (fun v ↦ by simp) hf (fun x ↦ by simp [hskew])
    fun v hv ↦ hsurj v (by simpa [neg_eq_iff_eq_neg] using hv)

/-- **The skew-adjoint vectors of a star-closed subspace are a real form of it.**  Let `P` be a
complex subspace of a complex star module closed under the star.  A real-linear map into `P` that
is injective and maps onto the skew-adjoint vectors of `P` exhibits `P` as the complexification
of its source.  The leading example is the Lie algebra `𝔰𝔲(n)` of trace-free skew-Hermitian
matrices inside `𝔰𝔩(n, ℂ)`. -/
theorem isBaseChange_complex_codRestrict_of_star_eq_neg {P : Submodule ℂ V}
    (hP : ∀ v ∈ P, star v ∈ P) (hfP : ∀ x, f x ∈ P) (hf : Function.Injective f)
    (hskew : ∀ x, star (f x) = -f x) (hsurj : ∀ v ∈ P, star v = -v → ∃ x, f x = v) :
    IsBaseChange ℂ (f.codRestrict (P.restrictScalars ℝ) hfP) := by
  -- The conjugation `v ↦ -v⋆` of `V`, restricted to `P`.
  let K : P.restrictScalars ℝ →ₛₗ[starRingEnd ℂ] P.restrictScalars ℝ :=
    { toFun v := ⟨-star (v : V), P.neg_mem (hP _ v.2)⟩
      map_add' v w := Subtype.ext (by simp [add_comm])
      map_smul' c v := Subtype.ext (show -star (c • (v : V)) = (starRingEnd ℂ c) • -star (v : V)
        by simp) }
  refine isBaseChange_complex_of_conj _ (K := K) (fun v ↦ Subtype.ext (by simp [K]))
    (fun x y h ↦ hf (congrArg Subtype.val h))
    (fun x ↦ Subtype.ext (show -star (f x) = f x by simp [hskew])) fun v hv ↦ ?_
  obtain ⟨x, hx⟩ := hsurj v v.2 (by
    simpa [K, neg_eq_iff_eq_neg] using congrArg Subtype.val hv)
  exact ⟨x, Subtype.ext hx⟩

end LinearMap
