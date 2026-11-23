/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Instances.AddCircle
public import TauCeti.Geometry.Manifold.LocalDiffeomorph.Cotangent

/-!
# The cotangent relation of the covering `ℝ → ℝ / pℤ`

For a positive period `p`, such as `p = 2π`, the quotient map `π : ℝ → AddCircle p` is a smooth
covering map with derivative the identity of `ℝ` in the charts of `AddCircle p`
(`AddCircle.mfderiv_coe`). Its cotangent relation (`TauCeti.CotangentBundle.cotangentRel`)
relates a covector `(t, a)` of `ℝ` to a covector `(θ, b)` of the circle exactly when `θ = [t]` and
`a = b` (`AddCircle.cotangentRel_coe_iff`).

Since `π` is a local diffeomorphism, this relation is the graph of its cotangent map
`(t, a) ↦ ([t], a)` (`AddCircle.cotangent_coe_apply`), which is a surjective local
diffeomorphism and a local symplectomorphism for the canonical forms
(`IsLocalDiffeomorph.isLocalDiffeomorph_cotangent`,
`IsLocalDiffeomorph.mpullback_cotangent_symplecticForm`). It has no global inverse: it is not
injective (`AddCircle.not_injective_cotangent_coe`), and the transposed relation is the graph of
no map, since a covector of the circle is related to the covectors at all the lifts `t + kp` of
its base point (`AddCircle.not_exists_forall_cotangentRel_coe_iff`). Thus the cotangent relation
of a covering is locally, but not globally, invertible.

## Main results

* `AddCircle.cotangentRel_coe_iff`: the cotangent relation of `ℝ → AddCircle p`.
* `AddCircle.cotangent_coe_apply`: its cotangent map is `(t, a) ↦ ([t], a)`.
* `AddCircle.cotangent_coe_surjective`, `AddCircle.not_injective_cotangent_coe`: the cotangent map
  is surjective and not injective.
* `AddCircle.not_exists_forall_cotangentRel_coe_iff`: the transposed relation is not the graph of
  a map.

## References

* A. Cannas da Silva, *Lectures on Symplectic Geometry*, Lecture Notes in Mathematics 1764,
  Springer, 2001, Section 2.
* J. M. Lee, *Introduction to Smooth Manifolds*, 2nd ed., Graduate Texts in Mathematics 218,
  Springer, 2013, Chapters 4 and 11.
-/

public section

open Bundle Function TauCeti TauCeti.CotangentBundle
open scoped Manifold ContDiff

namespace AddCircle

variable {p : ℝ} [Fact (0 < p)]

/-- **The cotangent relation of `ℝ → ℝ / pℤ`.** A covector `a` at `t ∈ ℝ` is related to a
covector `b` at `θ ∈ AddCircle p` exactly when `θ` is the class of `t` and `a = b`, both read as
linear forms on `ℝ`. -/
theorem cotangentRel_coe_iff (z : CotangentBundle 𝓘(ℝ) ℝ)
    (w : CotangentBundle 𝓘(ℝ) (AddCircle p)) :
    cotangentRel 𝓘(ℝ) 𝓘(ℝ) ((↑) : ℝ → AddCircle p) z w ↔
      (z.proj : AddCircle p) = w.proj ∧ z.snd = w.snd := by
  rw [cotangentRel_iff, mfderiv_coe]
  -- Composing with the identity of `ℝ` does not change the covector `w.2`, whose domain is the
  -- tangent line of the circle, only definitionally `ℝ`.
  exact and_congr_right fun _ ↦
    ⟨fun h ↦ ContinuousLinearMap.ext fun v ↦ DFunLike.congr_fun h v,
      fun h ↦ ContinuousLinearMap.ext fun v ↦ DFunLike.congr_fun h v⟩

/-- The cotangent map of `ℝ → ℝ / pℤ` sends a covector `a` at `t` to the same linear form `a` at
the class of `t`. -/
@[simp]
theorem cotangent_coe_apply (z : CotangentBundle 𝓘(ℝ) ℝ) :
    (isLocalDiffeomorph_coe p ∞).cotangent z = TotalSpace.mk' (ℝ →L[ℝ] ℝ)
      (E := fun θ : AddCircle p ↦ TangentSpace 𝓘(ℝ) θ →L[ℝ] ℝ) (z.proj : AddCircle p) z.snd :=
  ((cotangentRel_iff_of_isLocalDiffeomorph _ z _).1 ((cotangentRel_coe_iff z _).2 ⟨rfl, rfl⟩))

/-- The cotangent map of `ℝ → ℝ / pℤ` is surjective. -/
theorem cotangent_coe_surjective : Surjective (isLocalDiffeomorph_coe p ∞).cotangent :=
  (isLocalDiffeomorph_coe p ∞).cotangent_surjective_iff.2
    (QuotientAddGroup.mk_surjective (s := AddSubgroup.zmultiples p))

/-- The cotangent map of `ℝ → ℝ / pℤ` is not injective: it identifies a covector at `t` with the
same covector at `t + p`. -/
theorem not_injective_cotangent_coe : ¬ Injective (isLocalDiffeomorph_coe p ∞).cotangent :=
  fun h ↦ (Fact.out : 0 < p).ne'
    ((isLocalDiffeomorph_coe p ∞).cotangent_injective_iff.1 h (by simp))

/-- **The transposed cotangent relation of `ℝ → ℝ / pℤ` is not the graph of a map.** No map `g`
from covectors of the circle to covectors of `ℝ` has the cotangent relation as its transposed
graph: the zero covector at `0` of the circle is related to the zero covectors at `0` and at `p`. -/
theorem not_exists_forall_cotangentRel_coe_iff :
    ¬ ∃ g : CotangentBundle 𝓘(ℝ) (AddCircle p) → CotangentBundle 𝓘(ℝ) ℝ,
      ∀ z w, cotangentRel 𝓘(ℝ) 𝓘(ℝ) ((↑) : ℝ → AddCircle p) z w ↔ z = g w := by
  rintro ⟨g, hg⟩
  let w := zeroSection (ℝ →L[ℝ] ℝ) (fun θ : AddCircle p ↦ TangentSpace 𝓘(ℝ) θ →L[ℝ] ℝ) 0
  have h (t : ℝ) (ht : (t : AddCircle p) = 0) :
      zeroSection (ℝ →L[ℝ] ℝ) (fun t : ℝ ↦ TangentSpace 𝓘(ℝ) t →L[ℝ] ℝ) t = g w :=
    (hg _ w).1 ((cotangentRel_coe_iff _ w).2 ⟨ht, rfl⟩)
  have h0 := congrArg TotalSpace.proj ((h 0 (by simp)).trans (h p (by simp)).symm)
  simp only [zeroSection_proj] at h0
  exact (Fact.out : 0 < p).ne h0

end AddCircle
