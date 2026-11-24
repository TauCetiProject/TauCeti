/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.InnerProductSpace.HodgeStar.Kahler.Basic
-- Private: adapted orthonormal bases of an orthogonal complex structure are used only in proofs.
import TauCeti.Geometry.Symplectic.Complex.OrthonormalBasis

/-!
# The compatible complex structure of a self-dual two-form in dimension four

Let `V` be a finite-dimensional real inner product space with inner product `g`, and let
`F ∈ ⋀² V` represent the two-form `ω(u, w) = ⟪F, u ∧ w⟫`. The operator `A` with
`g(A u, w) = ω(u, w)` is the contraction `u ↦ u ⌟ F`
(`TauCeti.twoVectorContraction`); it is skew-adjoint. For an almost complex structure `J`, the
identity `g(u, v) = ω(u, J v)` says that `J` is compatible with `ω` and that `g` is the metric
`ω(·, J ·)` of the compatible pair. It holds exactly when `J = A` and `A² = -1`; in particular
such a `J` is unique (`TauCeti.AlmostComplexStructure.toLinearMap_eq_twoVectorContraction`, in
`HodgeStar/Kahler/Basic.lean`). It is then orthogonal, and `F` is the Kähler two-vector of `J`.

In dimension four, for an orientation `o` with Hodge star `⋆`, a self-dual or anti-self-dual
two-vector, `⋆F = ±F`, satisfies `‖u ⌟ F‖² = (‖F‖² / 2) ‖u‖²`, hence
`A² = -(‖F‖² / 2)` (`TauCeti.twoVectorContraction_comp_self`). For instance, in an oriented
orthonormal coframe a self-dual form is `a (e¹² + e³⁴) + b (e¹³ - e²⁴) + c (e¹⁴ + e²³)`, with
`‖F‖² = 2 (a² + b² + c²)` and `A² = -(a² + b² + c²)`. The argument is coordinate free: for a
unit vector `s`, the pointwise energy identity `⟪s ∧ a, F + ⋆F⟫ = ‖a‖² + vol (F ∧ F) / 2` with
`a = s ⌟ F` (`Orientation.inner_ιMulti_twoVectorContraction_add_hodgeStar`) reduces, for
`⋆F = ±F`, to `‖a‖² = ‖F‖² / 2`.

Conversely, a `J` with `g(u, v) = ω(u, J v)` is orthogonal and `F` is its Kähler two-vector,
which has `‖F‖² = 2` and is self-dual for the orientation of a unitary frame
(`TauCeti.AlmostComplexStructure.hodgeStar_kahlerForm`), so `⋆F = ±F`. The orientation is
the symplectic orientation of `ω` exactly when `vol (F ∧ F) = ⟪⋆F, F⟫` is positive. Together,
for the symplectic orientation, a `J` with `g(u, v) = ω(u, J v)` exists if and only if `⋆F = F`
and `‖F‖ = √2` (`TauCeti.exists_almostComplexStructure_inner_eq_iff_of_pos`). This is the
pointwise statement of the characterization of the metrics compatible with a symplectic form on
a four-manifold.

## Main definitions

* `TauCeti.AlmostComplexStructure.ofSelfDual`: for `⋆F = ±F` and `‖F‖² = 2`, the almost complex
  structure `u ↦ u ⌟ F`.

## Main results

* `TauCeti.AlmostComplexStructure.norm_sq_eq_two_of_inner_eq` and
  `TauCeti.AlmostComplexStructure.hodgeStar_eq_or_eq_neg_of_inner_eq`: in dimension four, a
  `J` with `⟪u, v⟫ = ⟪F, u ∧ J v⟫` forces `‖F‖² = 2` and `⋆F = ±F`.
* `TauCeti.norm_twoVectorContraction_apply_sq`: for `⋆F = ±F` in dimension four,
  `‖u ⌟ F‖² = (‖F‖² / 2) ‖u‖²`.
* `TauCeti.twoVectorContraction_comp_self`: for `⋆F = ±F`, `A² = -(‖F‖² / 2)`.
* `TauCeti.exists_almostComplexStructure_inner_eq_iff`: in dimension four, a `J` with
  `⟪u, v⟫ = ⟪F, u ∧ J v⟫` exists if and only if `⋆F = ±F` and `‖F‖² = 2`.
* `TauCeti.exists_almostComplexStructure_inner_eq_iff_of_pos`: for the symplectic orientation,
  `0 < vol (F ∧ F)`, it exists if and only if `⋆F = F` and `‖F‖² = 2`.
* `TauCeti.AlmostComplexStructure.existsUnique_inner_eq_inner_ιMulti_apply`: for `⋆F = ±F` and
  `‖F‖² = 2`, `ofSelfDual` is the unique `J` with `⟪u, v⟫ = ⟪F, u ∧ J v⟫`, and `F` is its Kähler
  two-vector (`TauCeti.AlmostComplexStructure.kahlerForm_ofSelfDual`).
* `TauCeti.AlmostComplexStructure.exists_orthonormalBasis_of_inner_eq`: for the symplectic
  orientation, a `J` with `⟪u, v⟫ = ⟪F, u ∧ J v⟫` has a positively oriented unitary frame.

## References

* D. McDuff and D. Salamon, *Introduction to Symplectic Topology*, 3rd ed., Oxford (2017).
* S. K. Donaldson and P. B. Kronheimer, *The Geometry of Four-Manifolds*, Oxford (1990).
-/

public section

noncomputable section

open Module exteriorPower
open scoped RealInnerProductSpace

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]

namespace TauCeti

/-! ### Compatible complex structures in dimension four -/

namespace AlmostComplexStructure

variable {F : ⋀[ℝ]^2 V} {J : AlmostComplexStructure V}
  (hJ : ∀ u v, ⟪u, v⟫ = ⟪F, ιMulti ℝ 2 ![u, J v]⟫)
include hJ

variable [Fact (finrank ℝ V = 4)]

/-- In dimension four, a two-vector `F` with `g(u, v) = ω(u, J v)` has `‖F‖² = 2`. -/
theorem norm_sq_eq_two_of_inner_eq : ‖F‖ ^ 2 = 2 := by
  rw [← kahlerForm_eq_of_inner_eq hJ, norm_kahlerForm_sq (inner_apply_apply_of_inner_eq hJ),
    (Fact.out : finrank ℝ V = 4)]
  norm_num

/-- In dimension four, a two-vector `F` with `g(u, v) = ω(u, J v)` is self-dual or anti-self-dual
for every orientation: it is self-dual for the orientation of a unitary frame of `J`. -/
theorem hodgeStar_eq_or_eq_neg_of_inner_eq (o : Orientation ℝ V (Fin 4))
    (hkl : 2 + 2 = finrank ℝ V) : o.hodgeStar hkl F = F ∨ o.hodgeStar hkl F = -F := by
  have hJn (v : V) : ‖J v‖ = ‖v‖ := by
    rw [norm_eq_sqrt_real_inner, inner_apply_apply_of_inner_eq hJ, ← norm_eq_sqrt_real_inner]
  obtain ⟨b, hb⟩ := J.exists_adapted_orthonormalBasis hJn 2 (by rw [(Fact.out : finrank ℝ V = 4)])
  -- A unitary frame `e₀, e₁ = J e₀, e₂, e₃ = J e₂`.
  have h₀ : J (b 0) = b 1 := (hb 0).symm
  have h₂ : J (b 2) = b 3 := (hb 1).symm
  rw [← kahlerForm_eq_of_inner_eq hJ]
  have hω := hodgeStar_kahlerForm h₀ h₂ hkl rfl
  rcases b.toBasis.orientation_eq_or_eq_neg o with rfl | rfl
  · exact Or.inl hω
  · exact Or.inr (by rw [Orientation.hodgeStar_neg_orientation, hω])

end AlmostComplexStructure

/-! ### Self-dual two-vectors in dimension four -/

section Four

variable [Fact (finrank ℝ V = 4)] (o : Orientation ℝ V (Fin 4)) (hkl : 2 + 2 = finrank ℝ V)
  {F : ⋀[ℝ]^2 V}

/-- For a unit vector `s` and `⋆F = ±F`, the energy identity
`⟪s ∧ a, F + ⋆F⟫ = ‖a‖² + vol (F ∧ F) / 2`, `a = s ⌟ F`, reduces to `‖a‖² = ‖F‖² / 2`. -/
private theorem norm_twoVectorContraction_apply_sq_of_norm_eq_one
    (hF : o.hodgeStar hkl F = F ∨ o.hodgeStar hkl F = -F) {s : V} (hs : ‖s‖ = 1) :
    ‖twoVectorContraction F s‖ ^ 2 = ‖F‖ ^ 2 / 2 := by
  have h := o.inner_ιMulti_twoVectorContraction_add_hodgeStar hkl hs F
  rw [← o.inner_hodgeStar_apply hkl] at h
  have h₁ : ⟪ιMulti ℝ 2 ![s, twoVectorContraction F s], F⟫ =
      ‖twoVectorContraction F s‖ ^ 2 := by
    rw [real_inner_comm, ← inner_twoVectorContraction_apply, real_inner_self_eq_norm_sq]
  rcases hF with hF | hF
  · rw [hF, inner_add_right, h₁, real_inner_self_eq_norm_sq] at h
    linarith
  · rw [hF, add_neg_cancel, inner_zero_right, inner_neg_left, real_inner_self_eq_norm_sq] at h
    linarith

/-- **The contraction by a self-dual or anti-self-dual two-vector is conformal**: in dimension
four, if `⋆F = ±F` then `‖u ⌟ F‖² = (‖F‖² / 2) ‖u‖²`. -/
theorem norm_twoVectorContraction_apply_sq
    (hF : o.hodgeStar hkl F = F ∨ o.hodgeStar hkl F = -F) (u : V) :
    ‖twoVectorContraction F u‖ ^ 2 = ‖F‖ ^ 2 / 2 * ‖u‖ ^ 2 := by
  rcases eq_or_ne u 0 with rfl | hu
  · simp
  have hu' : ‖u‖ ≠ 0 := norm_ne_zero_iff.2 hu
  have hs : ‖‖u‖⁻¹ • u‖ = 1 := by rw [norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hu']
  have h := norm_twoVectorContraction_apply_sq_of_norm_eq_one o hkl hF hs
  rw [map_smul, norm_smul, mul_pow, Real.norm_eq_abs, abs_inv, abs_norm, inv_pow] at h
  field_simp at h ⊢
  linarith

/-- In dimension four, for `⋆F = ±F`, the contraction by `F` scales inner products by
`‖F‖² / 2`: `⟪u ⌟ F, v ⌟ F⟫ = (‖F‖² / 2) ⟪u, v⟫`. -/
theorem inner_twoVectorContraction_apply_twoVectorContraction_apply
    (hF : o.hodgeStar hkl F = F ∨ o.hodgeStar hkl F = -F) (u v : V) :
    ⟪twoVectorContraction F u, twoVectorContraction F v⟫ = ‖F‖ ^ 2 / 2 * ⟪u, v⟫ := by
  rw [real_inner_eq_norm_add_mul_self_sub_norm_mul_self_sub_norm_mul_self_div_two,
    real_inner_eq_norm_add_mul_self_sub_norm_mul_self_sub_norm_mul_self_div_two u v, ← map_add]
  simp only [← sq, norm_twoVectorContraction_apply_sq o hkl hF]
  ring

/-- **The square of the contraction by a self-dual two-vector**: in dimension four, if
`⋆F = ±F` then `A² = -(‖F‖² / 2)` for `A u = u ⌟ F`. In an oriented orthonormal coframe, with
`F = a (e¹² + e³⁴) + b (e¹³ - e²⁴) + c (e¹⁴ + e²³)`, this is `A² = -(a² + b² + c²)`. -/
theorem twoVectorContraction_comp_self
    (hF : o.hodgeStar hkl F = F ∨ o.hodgeStar hkl F = -F) :
    twoVectorContraction F ∘ₗ twoVectorContraction F = -(‖F‖ ^ 2 / 2) • LinearMap.id := by
  refine LinearMap.ext fun u ↦ ext_inner_right ℝ fun w ↦ ?_
  rw [LinearMap.comp_apply, inner_twoVectorContraction_apply_left,
    inner_twoVectorContraction_apply_twoVectorContraction_apply o hkl hF]
  simp [real_inner_smul_left]

/-- **The compatible complex structure of a self-dual two-vector.** In dimension four, if
`⋆F = ±F` and `‖F‖² = 2`, the contraction `J u = u ⌟ F` squares to `-1` and satisfies
`g(u, v) = ω(u, J v)`, where `ω(u, w) = ⟪F, u ∧ w⟫`. -/
theorem inner_eq_inner_ιMulti_twoVectorContraction
    (hF : o.hodgeStar hkl F = F ∨ o.hodgeStar hkl F = -F) (hF₂ : ‖F‖ ^ 2 = 2) (u v : V) :
    ⟪u, v⟫ = ⟪F, ιMulti ℝ 2 ![u, twoVectorContraction F v]⟫ := by
  rw [← inner_twoVectorContraction_apply,
    inner_twoVectorContraction_apply_twoVectorContraction_apply o hkl hF, hF₂]
  ring

end Four

/-! ### The compatible complex structure of a self-dual two-vector -/

namespace AlmostComplexStructure

variable [Fact (finrank ℝ V = 4)] {o : Orientation ℝ V (Fin 4)} (hkl : 2 + 2 = finrank ℝ V)
  {F : ⋀[ℝ]^2 V}

/-- The **almost complex structure of a self-dual two-vector** `F` with `‖F‖² = 2` in an oriented
four-dimensional inner product space: the contraction `u ↦ u ⌟ F`, which squares to `-1` by
`TauCeti.twoVectorContraction_comp_self`. An anti-self-dual `F`, with `⋆F = -F`, is self-dual for
the opposite orientation, and is allowed too. It is the unique almost complex structure with
`⟪u, v⟫ = ⟪F, u ∧ J v⟫` (`TauCeti.inner_eq_inner_ιMulti_twoVectorContraction`,
`TauCeti.AlmostComplexStructure.eq_ofSelfDual`). -/
def ofSelfDual (hF : o.hodgeStar hkl F = F ∨ o.hodgeStar hkl F = -F) (hF₂ : ‖F‖ ^ 2 = 2) :
    AlmostComplexStructure V where
  toLinearMap := twoVectorContraction F
  square_neg := by
    rw [twoVectorContraction_comp_self o hkl hF, hF₂]
    ext u
    simp

variable {hkl}

/-- `ofSelfDual` is the contraction by `F`. -/
theorem ofSelfDual_apply (hF : o.hodgeStar hkl F = F ∨ o.hodgeStar hkl F = -F) (hF₂ : ‖F‖ ^ 2 = 2)
    (u : V) : ofSelfDual hkl hF hF₂ u = twoVectorContraction F u :=
  (rfl)

/-- The underlying linear map of `ofSelfDual` is the contraction by `F`. -/
@[simp]
theorem toLinearMap_ofSelfDual (hF : o.hodgeStar hkl F = F ∨ o.hodgeStar hkl F = -F)
    (hF₂ : ‖F‖ ^ 2 = 2) : (ofSelfDual hkl hF hF₂).toLinearMap = twoVectorContraction F :=
  (rfl)

/-- **`ofSelfDual` is compatible with `F`**: `⟪u, v⟫ = ⟪F, u ∧ J v⟫`. -/
theorem inner_eq_inner_ιMulti_ofSelfDual_apply
    (hF : o.hodgeStar hkl F = F ∨ o.hodgeStar hkl F = -F) (hF₂ : ‖F‖ ^ 2 = 2) (u v : V) :
    ⟪u, v⟫ = ⟪F, ιMulti ℝ 2 ![u, ofSelfDual hkl hF hF₂ v]⟫ :=
  inner_eq_inner_ιMulti_twoVectorContraction o hkl hF hF₂ u v

/-- `ofSelfDual` is orthogonal. -/
theorem inner_ofSelfDual_apply_ofSelfDual_apply
    (hF : o.hodgeStar hkl F = F ∨ o.hodgeStar hkl F = -F) (hF₂ : ‖F‖ ^ 2 = 2) (u v : V) :
    ⟪ofSelfDual hkl hF hF₂ u, ofSelfDual hkl hF hF₂ v⟫ = ⟪u, v⟫ :=
  inner_apply_apply_of_inner_eq (inner_eq_inner_ιMulti_ofSelfDual_apply hF hF₂) u v

/-- `F` is the Kähler two-vector of `ofSelfDual`. -/
@[simp]
theorem kahlerForm_ofSelfDual (hF : o.hodgeStar hkl F = F ∨ o.hodgeStar hkl F = -F)
    (hF₂ : ‖F‖ ^ 2 = 2) : (ofSelfDual hkl hF hF₂).kahlerForm = F :=
  kahlerForm_eq_of_inner_eq (inner_eq_inner_ιMulti_ofSelfDual_apply hF hF₂)

/-- **Uniqueness of the compatible complex structure**: an almost complex structure `J` with
`⟪u, v⟫ = ⟪F, u ∧ J v⟫` is `ofSelfDual`. -/
theorem eq_ofSelfDual (hF : o.hodgeStar hkl F = F ∨ o.hodgeStar hkl F = -F) (hF₂ : ‖F‖ ^ 2 = 2)
    {J : AlmostComplexStructure V} (hJ : ∀ u v, ⟪u, v⟫ = ⟪F, ιMulti ℝ 2 ![u, J v]⟫) :
    J = ofSelfDual hkl hF hF₂ :=
  toLinearMap_injective (toLinearMap_eq_twoVectorContraction hJ)

/-- **The compatible complex structure of a self-dual two-vector of norm `√2` is unique.** -/
theorem existsUnique_inner_eq_inner_ιMulti_apply
    (hF : o.hodgeStar hkl F = F ∨ o.hodgeStar hkl F = -F) (hF₂ : ‖F‖ ^ 2 = 2) :
    ∃! J : AlmostComplexStructure V, ∀ u v, ⟪u, v⟫ = ⟪F, ιMulti ℝ 2 ![u, J v]⟫ :=
  ⟨ofSelfDual hkl hF hF₂, inner_eq_inner_ιMulti_ofSelfDual_apply hF hF₂,
    fun _ hJ ↦ eq_ofSelfDual hF hF₂ hJ⟩

end AlmostComplexStructure

/-! ### Existence of compatible complex structures in dimension four -/

section Four

variable [Fact (finrank ℝ V = 4)] (o : Orientation ℝ V (Fin 4)) (hkl : 2 + 2 = finrank ℝ V)
  {F : ⋀[ℝ]^2 V}

/-- **Two-vectors with a compatible complex structure.** In dimension four, there is an almost
complex structure `J` with `g(u, v) = ω(u, J v)`, where `ω(u, w) = ⟪F, u ∧ w⟫`, if and only if
`F` is self-dual or anti-self-dual and `‖F‖² = 2`. Such a `J` is unique
(`TauCeti.AlmostComplexStructure.toLinearMap_eq_twoVectorContraction`). -/
theorem exists_almostComplexStructure_inner_eq_iff :
    (∃ J : AlmostComplexStructure V, ∀ u v, ⟪u, v⟫ = ⟪F, ιMulti ℝ 2 ![u, J v]⟫) ↔
      (o.hodgeStar hkl F = F ∨ o.hodgeStar hkl F = -F) ∧ ‖F‖ ^ 2 = 2 :=
  ⟨fun ⟨_, hJ⟩ ↦ ⟨AlmostComplexStructure.hodgeStar_eq_or_eq_neg_of_inner_eq hJ o hkl,
    AlmostComplexStructure.norm_sq_eq_two_of_inner_eq hJ⟩, fun ⟨hF, hF₂⟩ ↦ ⟨.ofSelfDual hkl hF hF₂,
      AlmostComplexStructure.inner_eq_inner_ιMulti_ofSelfDual_apply hF hF₂⟩⟩

/-- **Compatible complex structures for the symplectic orientation.** In dimension four, let the
orientation be that of the two-form `ω(u, w) = ⟪F, u ∧ w⟫`, in the sense that
`vol (F ∧ F) = ⟪⋆F, F⟫` is positive. Then there is an almost complex structure `J` with
`g(u, v) = ω(u, J v)` if and only if `⋆F = F` and `‖F‖ = √2`, that is `‖F‖² = 2`. -/
theorem exists_almostComplexStructure_inner_eq_iff_of_pos (ho : 0 < ⟪o.hodgeStar hkl F, F⟫) :
    (∃ J : AlmostComplexStructure V, ∀ u v, ⟪u, v⟫ = ⟪F, ιMulti ℝ 2 ![u, J v]⟫) ↔
      o.hodgeStar hkl F = F ∧ ‖F‖ ^ 2 = 2 := by
  rw [exists_almostComplexStructure_inner_eq_iff o hkl]
  refine ⟨fun ⟨hF, hF₂⟩ ↦ ⟨hF.resolve_right fun h ↦ ?_, hF₂⟩, fun ⟨hF, hF₂⟩ ↦ ⟨Or.inl hF, hF₂⟩⟩
  rw [h, inner_neg_left, real_inner_self_eq_norm_sq] at ho
  have := sq_nonneg ‖F‖
  linarith

end Four

namespace AlmostComplexStructure

variable [Fact (finrank ℝ V = 4)] {o : Orientation ℝ V (Fin 4)} {hkl : 2 + 2 = finrank ℝ V}
  {F : ⋀[ℝ]^2 V}

/-- **A two-vector with a compatible complex structure is self-dual** for its symplectic
orientation: if `⟪u, v⟫ = ⟪F, u ∧ J v⟫` and `⟪⋆F, F⟫ > 0`, then `⋆F = F`. -/
theorem hodgeStar_eq_self_of_inner_eq {J : AlmostComplexStructure V}
    (hJ : ∀ u v, ⟪u, v⟫ = ⟪F, ιMulti ℝ 2 ![u, J v]⟫) (hpos : 0 < ⟪o.hodgeStar hkl F, F⟫) :
    o.hodgeStar hkl F = F :=
  ((exists_almostComplexStructure_inner_eq_iff_of_pos o hkl hpos).1 ⟨J, hJ⟩).1

/-- **A compatible complex structure has a positively oriented unitary frame** for the symplectic
orientation: if `⟪u, v⟫ = ⟪F, u ∧ J v⟫` and `⟪⋆F, F⟫ > 0`, then some positively oriented
orthonormal basis `e` has `J e₀ = e₁` and `J e₂ = e₃`. So the complex orientation of `J` is the
symplectic orientation of `F`. -/
theorem exists_orthonormalBasis_of_inner_eq {J : AlmostComplexStructure V}
    (hJ : ∀ u v, ⟪u, v⟫ = ⟪F, ιMulti ℝ 2 ![u, J v]⟫) (hpos : 0 < ⟪o.hodgeStar hkl F, F⟫) :
    ∃ e : OrthonormalBasis (Fin 4) ℝ V,
      e.toBasis.orientation = o ∧ J (e 0) = e 1 ∧ J (e 2) = e 3 := by
  set b := o.finOrthonormalBasis (by norm_num) (Fact.out : finrank ℝ V = 4)
  obtain ⟨e, -, h₀, h₂⟩ :=
    exists_unitary_orthonormalBasis_of_norm_eq_one (inner_apply_apply_of_inner_eq hJ)
      (b.orthonormal.1 0)
  refine ⟨e, ?_, h₀, h₂⟩
  -- For the opposite orientation `F` would be both self-dual and anti-self-dual, so `F = 0`.
  rcases Orientation.eq_or_eq_neg e.toBasis.orientation o
      ((Nat.card_fin 4).trans (Fact.out : finrank ℝ V = 4).symm) with he | he
  · exact he
  · have h := hodgeStar_kahlerForm h₀ h₂ hkl he
    rw [kahlerForm_eq_of_inner_eq hJ, Orientation.hodgeStar_neg_orientation,
      hodgeStar_eq_self_of_inner_eq hJ hpos] at h
    have hF : F = 0 := by linear_combination (norm := module) (-2⁻¹ : ℝ) • h
    have := norm_sq_eq_two_of_inner_eq hJ
    simp [hF] at this

/-- `ofSelfDual` has a positively oriented unitary frame: its complex orientation is the given
one. -/
theorem exists_orthonormalBasis_ofSelfDual (hF : o.hodgeStar hkl F = F) (hF₂ : ‖F‖ ^ 2 = 2) :
    ∃ e : OrthonormalBasis (Fin 4) ℝ V, e.toBasis.orientation = o ∧
      ofSelfDual hkl (.inl hF) hF₂ (e 0) = e 1 ∧ ofSelfDual hkl (.inl hF) hF₂ (e 2) = e 3 :=
  exists_orthonormalBasis_of_inner_eq (inner_eq_inner_ιMulti_ofSelfDual_apply (.inl hF) hF₂)
    (by rw [hF, real_inner_self_eq_norm_sq, hF₂]; norm_num)

end AlmostComplexStructure

end TauCeti
