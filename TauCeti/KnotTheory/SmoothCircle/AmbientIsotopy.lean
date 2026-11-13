/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.KnotTheory.SmoothCircle
public import TauCeti.Geometry.Manifold.SmoothEmbedding.SmoothAmbientIsotopy.Diffeomorph
public import TauCeti.Geometry.Manifold.SmoothEmbedding.SmoothAmbientIsotopy.Reparametrization
import Mathlib.Analysis.Complex.Isometry
import Mathlib.LinearAlgebra.Complex.FiniteDimensional
import TauCeti.Analysis.InnerProductSpace.Reflection
import TauCeti.Geometry.Diffeomorphism.Diffeotopy.Rotation

/-!
# Ambient isotopy of knots and the parametrization of the circle

A knot in a manifold `M` is a smooth circle embedding `K : S¹ → M`, and two knots are equivalent
when they are smoothly ambient isotopic, `TauCeti.SmoothEmbedding.SmoothAmbientIsotopic`: the final
diffeomorphism of a diffeotopy of `M` carries `K` to `J` as parametrized maps. This file shows that
the marked parametrization of a knot is irrelevant up to orientation, and that ambient isotopy is
compatible with the two orientation-sensitive operations on knots.

* **Rotation.** Every rotation of the circle is the final map of a diffeotopy of the circle
  (`TauCeti.exists_diffeotopy_final_eq_circleRotationHom`), so rotating the parameter of a knot is
  realized by an ambient isotopy (`TauCeti.SmoothCircleEmbedding.smoothAmbientIsotopic_rotate`),
  by isotopy extension. Hence two knots are ambient isotopic exactly when some diffeotopy carries
  one onto the other up to a rotation of the parameter
  (`TauCeti.SmoothCircleEmbedding.smoothAmbientIsotopic_iff_exists_diffeotopy_rotate`): the
  relation does not depend on where the parametrization starts. For this the ambient manifold is
  boundaryless, finite-dimensional, Hausdorff and σ-compact, the setting of isotopy extension.
* **Reversal.** Reversing the orientation of both knots preserves and reflects ambient isotopy
  (`TauCeti.SmoothEmbedding.SmoothAmbientIsotopic.reverse`).
* **Invertibility of great circles.** In a sphere `Sⁿ` with `n ≥ 2`, a great circle is ambient
  isotopic to its reverse
  (`TauCeti.SmoothCircleEmbedding.smoothAmbientIsotopic_greatCircle_reverse`): the reflection in
  the hyperplane orthogonal to `ι i` reverses the great circle `ι S¹`, and
  composing it with the reflection in a hyperplane containing `ι ℂ` gives a rotation of the sphere,
  which is the final map of a diffeotopy. In particular the unknot of `S³` is invertible
  (`TauCeti.smoothAmbientIsotopic_unknot_reverse`). For `n = 1` the great circle is a
  diffeomorphism onto `S¹` and its reverse has the opposite degree, so the dimension hypothesis is
  needed.

## References

* W. B. R. Lickorish, *An Introduction to Knot Theory*, Springer GTM 175 (1997), Chapter 1
  (equivalence, orientation and reversal of knots).
* M. W. Hirsch, *Differential Topology*, Springer GTM 33 (1976), Chapter 8, §1 (isotopy
  extension).
-/

public section

noncomputable section

open Metric Module Set
open scoped Manifold ContDiff RealInnerProductSpace

namespace TauCeti

attribute [local instance] finrank_real_complex_fact' finrank_euclideanSpace_fin_succ_fact

/-- **Rotations of the circle are diffeotopic to the identity.** The rotation `z ↦ a * z` of the
circle is the final map of a diffeotopy of the circle. -/
theorem exists_diffeotopy_final_eq_circleRotationHom (a : Circle) :
    ∃ Ψ : Diffeotopy (𝓡 1) ∞ Circle, Ψ.final = circleRotationHom a := by
  -- `Circle` is by definition the unit sphere of `ℂ`, with the charted-space structure of that
  -- sphere, so a diffeotopy of that sphere is a diffeotopy of `Circle`.
  obtain ⟨Ψ, hΨ⟩ : ∃ Ψ : Diffeotopy (𝓡 1) ∞ Circle, ∀ z : Circle, (Ψ.final z : ℂ) = rotation a z :=
    exists_diffeotopy_final_apply_eq_of_det_eq_one (E := ℂ) (n := 1) (m := ∞)
      (by simp [linearEquiv_det_rotation])
  exact ⟨Ψ, _root_.Diffeomorph.ext fun z => Subtype.ext (by rw [hΨ z]; simp)⟩

namespace SmoothCircleEmbedding

section Rotation

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
  [SigmaCompactSpace M] {K J : SmoothCircleEmbedding I M}

/-- **Rotating the parameter of a knot is an ambient isotopy.** A smooth circle embedding is
smoothly ambient isotopic to its reparametrization by any rotation of the circle. -/
theorem smoothAmbientIsotopic_rotate (K : SmoothCircleEmbedding I M) (a : Circle) :
    K.SmoothAmbientIsotopic (K.rotate a) := by
  obtain ⟨Ψ, hΨ⟩ := exists_diffeotopy_final_eq_circleRotationHom a
  have hK : K.rotate a = K.compDiffeomorph Ψ.final := SmoothEmbedding.ext fun x => by simp [hΨ]
  rw [hK]
  exact K.smoothAmbientIsotopic_compDiffeomorph_final Ψ

/-- Rotating the parameter of the first knot does not change smooth ambient isotopy. -/
@[simp]
theorem rotate_smoothAmbientIsotopic_iff (a : Circle) :
    (K.rotate a).SmoothAmbientIsotopic J ↔ K.SmoothAmbientIsotopic J :=
  ⟨(K.smoothAmbientIsotopic_rotate a).trans, (K.smoothAmbientIsotopic_rotate a).symm.trans⟩

/-- Rotating the parameter of the second knot does not change smooth ambient isotopy. -/
@[simp]
theorem smoothAmbientIsotopic_rotate_iff (a : Circle) :
    K.SmoothAmbientIsotopic (J.rotate a) ↔ K.SmoothAmbientIsotopic J :=
  ⟨fun h => h.trans (J.smoothAmbientIsotopic_rotate a).symm,
    fun h => h.trans (J.smoothAmbientIsotopic_rotate a)⟩

/-- **Ambient isotopy of knots up to rotation of the parameter.** Two knots are smoothly ambient
isotopic exactly when the final map of some diffeotopy carries the first onto the second up to a
rotation of the parameter circle. -/
theorem smoothAmbientIsotopic_iff_exists_diffeotopy_rotate :
    K.SmoothAmbientIsotopic J ↔
      ∃ Φ : Diffeotopy I ∞ M, ∃ a : Circle, ∀ x, Φ.final (K x) = J (a * x) := by
  refine ⟨fun h => ?_, fun ⟨Φ, a, hΦ⟩ => ?_⟩
  · obtain ⟨Φ, hΦ⟩ := SmoothEmbedding.smoothAmbientIsotopic_def.1 h
    exact ⟨Φ, 1, by simpa using hΦ⟩
  · rw [← smoothAmbientIsotopic_rotate_iff a]
    exact SmoothEmbedding.SmoothAmbientIsotopic.of_diffeotopy Φ (by simpa using hΦ)

end Rotation

end SmoothCircleEmbedding

section Reverse

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] {K J : SmoothCircleEmbedding I M}

/-- Reversing the orientation of two smoothly ambient-isotopic knots keeps them smoothly ambient
isotopic: the same diffeotopy carries one reverse onto the other. -/
theorem SmoothEmbedding.SmoothAmbientIsotopic.reverse (h : K.SmoothAmbientIsotopic J) :
    K.reverse.SmoothAmbientIsotopic J.reverse := by
  have hrev (L : SmoothCircleEmbedding I M) : L.reverse = L.compDiffeomorph circleReflection :=
    SmoothEmbedding.ext fun x => by simp
  rw [hrev, hrev]
  exact h.compDiffeomorph circleReflection

/-- Reversing the orientation of both knots preserves and reflects smooth ambient isotopy. -/
@[simp]
theorem SmoothEmbedding.smoothAmbientIsotopic_reverse_iff :
    K.reverse.SmoothAmbientIsotopic J.reverse ↔ K.SmoothAmbientIsotopic J :=
  ⟨fun h => by simpa using h.reverse, SmoothEmbedding.SmoothAmbientIsotopic.reverse⟩

end Reverse

namespace SmoothCircleEmbedding

section GreatCircle

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {n : ℕ}
  [Fact (finrank ℝ E = n + 1)]

/-- **Great circles are invertible.** In a sphere `Sⁿ` of dimension `n ≥ 2`, the great circle cut
out by a linear isometric copy `ι` of the complex plane is smoothly ambient isotopic to its
reverse. The reflection in the hyperplane orthogonal to `ι i` reverses the great circle, and
composed with the reflection in a hyperplane containing `ι ℂ` it is a rotation of the sphere. -/
theorem smoothAmbientIsotopic_greatCircle_reverse (hn : 2 ≤ n) (ι : ℂ →ₗᵢ[ℝ] E) :
    (greatCircle (n := n) ι).reverse.SmoothAmbientIsotopic (greatCircle ι) := by
  have : FiniteDimensional ℝ E := .of_fact_finrank_eq_succ n
  -- A nonzero vector `v` orthogonal to the plane `ι ℂ`, which has codimension `n - 1 ≥ 1`.
  obtain ⟨v, hv, hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot
    (p := (LinearMap.range ι.toLinearMap)ᗮ) fun h => by
      have h1 := Submodule.finrank_add_finrank_orthogonal (LinearMap.range ι.toLinearMap)
      rw [h, finrank_bot, LinearMap.finrank_range_of_inj ι.injective,
        Complex.finrank_real_complex, Fact.out (p := finrank ℝ E = n + 1)] at h1
      omega
  have hvι (w : ℂ) : ⟪v, ι w⟫ = 0 := by
    rw [real_inner_comm]
    exact Submodule.inner_right_of_mem_orthogonal (LinearMap.mem_range_self _ w) hv
  have hI0 : ι Complex.I ≠ 0 := fun h => Complex.I_ne_zero (ι.injective (h.trans (map_zero ι).symm))
  obtain ⟨Φ, hΦ⟩ := exists_diffeotopy_final_apply_eq_of_det_eq_one (n := n) (m := ∞)
    (e := (ℝ ∙ ι Complex.I)ᗮ.reflection.trans (ℝ ∙ v)ᗮ.reflection) (by
      rw [LinearIsometryEquiv.toLinearEquiv_trans, LinearEquiv.det_trans, Units.val_mul,
        linearEquiv_det_reflection_orthogonal_singleton hI0,
        linearEquiv_det_reflection_orthogonal_singleton hv0]
      norm_num)
  refine SmoothEmbedding.SmoothAmbientIsotopic.of_diffeotopy Φ fun z => Subtype.ext ?_
  rw [hΦ, reverse_apply, coe_greatCircle_apply, coe_greatCircle_apply,
    LinearIsometryEquiv.trans_apply, Circle.coe_inv_eq_conj,
    ι.reflection_orthogonal_singleton_map_I, Complex.conj_conj,
    reflection_orthogonal_singleton_eq_self_of_inner_eq_zero (hvι _)]

end GreatCircle

end SmoothCircleEmbedding

/-- **The unknot is invertible**: the unknot of `S³` is smoothly ambient isotopic to its
reverse. -/
theorem smoothAmbientIsotopic_unknot_reverse : unknot.reverse.SmoothAmbientIsotopic unknot := by
  rw [unknot_eq_greatCircle]
  exact SmoothCircleEmbedding.smoothAmbientIsotopic_greatCircle_reverse (by norm_num) _

end TauCeti
