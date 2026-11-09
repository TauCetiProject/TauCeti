/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.TotallyReal.Basic
public import Mathlib.LinearAlgebra.BilinearForm.Orthogonal
public import Mathlib.LinearAlgebra.Complex.Module

/-!
# Bilinear forms compatible with a maximal totally real subspace

Let `J` be a linear endomorphism with `J ∘ J = -1` and `L` a maximal totally real subspace, so
that every vector is uniquely `a + J b` with `a, b ∈ L`. Write `P` for the projection onto `L`
along `J L`. For a bilinear form `g`, the form

`g'(v, w) = g(P v, P w) + g(P J v, P J w)`

is `J`-invariant, agrees with `g` on `L`, and makes `L` and `J L` orthogonal. It is the only
bilinear form with these three properties, and it is positive definite when `g` is positive on
`L`; then `J L` is exactly the orthogonal complement of `L`. This is the pointwise step in the
construction of a Hermitian metric with `J F = F^⊥` along a totally real subbundle `F`.

## Main declarations

* `TauCeti.IsMaximalTotallyReal.projection`: the projection onto `L` along `J L`.
* `TauCeti.IsMaximalTotallyReal.compatibleForm`: the form `g'` above.
* `TauCeti.IsMaximalTotallyReal.compatibleForm_map_map`: `g'` is `J`-invariant.
* `TauCeti.IsMaximalTotallyReal.eq_compatibleForm`: a `J`-invariant form agreeing with `g` on
  `L` and making `L` orthogonal to `J L` is `g'`.
* `TauCeti.IsMaximalTotallyReal.orthogonal_compatibleForm`: `J L` is the `g'`-orthogonal
  complement of `L` when `g` is positive on `L`.
* `TauCeti.IsMaximalTotallyReal.projection_sum_smul`: for `J` multiplication by `i` on a complex
  module, `P` takes real parts of complex coordinates in a real frame of `L`.

## References

* D. McDuff and D. Salamon, *J-holomorphic Curves and Symplectic Topology*, 2nd ed.,
  AMS (2012), Section C.1.
-/

public section

noncomputable section

namespace TauCeti.IsMaximalTotallyReal

open LinearMap (BilinForm)

variable {R E : Type*} [CommRing R] [AddCommGroup E] [Module R E]
  {J : E →ₗ[R] E} {L : Submodule R E}

/-- The projection onto a maximal totally real subspace `L` along its `J`-image. -/
def projection (hL : IsMaximalTotallyReal J L) : E →ₗ[R] E :=
  L.projection (L.map J) hL.isCompl

/-- The projection takes values in `L`. -/
theorem projection_apply_mem (hL : IsMaximalTotallyReal J L) (v : E) : hL.projection v ∈ L :=
  L.projection_apply_mem _ v

/-- The projection fixes `L`. -/
theorem projection_apply_of_mem (hL : IsMaximalTotallyReal J L) {v : E} (hv : v ∈ L) :
    hL.projection v = v :=
  Submodule.projection_apply_of_mem_left _ hv

/-- The projection kills `J L`. -/
theorem projection_map (hL : IsMaximalTotallyReal J L) {v : E} (hv : v ∈ L) :
    hL.projection (J v) = 0 :=
  (Submodule.projection_apply_eq_zero_iff hL.isCompl).2 ⟨v, hv, rfl⟩

variable (hJ : J ∘ₗ J = -LinearMap.id)
include hJ

/-- Writing `v = P v + J b` with `b ∈ L`, the projection of `J v` is `-b`, so every vector is
recovered from the projections of itself and of its `J`-image. -/
theorem sub_map_projection_map (hL : IsMaximalTotallyReal J L) (v : E) :
    hL.projection v - J (hL.projection (J v)) = v := by
  have hJJ (v : E) : J (J v) = -v := LinearMap.congr_fun hJ v
  obtain ⟨b, hb, hbv⟩ := Submodule.sub_projection_mem hL.isCompl v
  have hbv : J b = v - hL.projection v := hbv
  have hv : v = hL.projection v + J b := by rw [hbv, add_sub_cancel]
  have hJv : J v = J (hL.projection v) - b := by
    conv_lhs => rw [hv]
    rw [map_add, hJJ, sub_eq_add_neg]
  rw [hJv, map_sub, hL.projection_map (hL.projection_apply_mem v),
    hL.projection_apply_of_mem hb, zero_sub, map_neg, sub_neg_eq_add, hbv, add_sub_cancel]

/-- The projection of `J (J v)` is minus the projection of `v`. -/
theorem projection_map_map (hL : IsMaximalTotallyReal J L) (v : E) :
    hL.projection (J (J v)) = -hL.projection v := by
  rw [show J (J v) = -v from LinearMap.congr_fun hJ v, map_neg]

omit hJ

/-- The bilinear form `g'(v, w) = g(P v, P w) + g(P J v, P J w)` built from `g` and the
projection `P` onto `L` along `J L`. -/
def compatibleForm (hL : IsMaximalTotallyReal J L) (g : BilinForm R E) : BilinForm R E :=
  g.compl₁₂ hL.projection hL.projection +
    g.compl₁₂ (hL.projection ∘ₗ J) (hL.projection ∘ₗ J)

/-- Evaluation of the compatible form. -/
@[simp]
theorem compatibleForm_apply (hL : IsMaximalTotallyReal J L) (g : BilinForm R E) (v w : E) :
    hL.compatibleForm g v w =
      g (hL.projection v) (hL.projection w) +
        g (hL.projection (J v)) (hL.projection (J w)) := by
  simp [compatibleForm]

/-- The compatible form of a symmetric form is symmetric. -/
theorem isSymm_compatibleForm (hL : IsMaximalTotallyReal J L) {g : BilinForm R E}
    (hg : g.IsSymm) : (hL.compatibleForm g).IsSymm :=
  LinearMap.BilinForm.isSymm_def.2 fun v w ↦ by
    simp only [compatibleForm_apply, LinearMap.BilinForm.isSymm_def.1 hg (hL.projection v),
      LinearMap.BilinForm.isSymm_def.1 hg (hL.projection (J v))]

/-- On `L`, the compatible form pairs a vector of `L` with `w` through the projection of `w`. -/
theorem compatibleForm_apply_of_mem (hL : IsMaximalTotallyReal J L) (g : BilinForm R E)
    {a : E} (ha : a ∈ L) (w : E) :
    hL.compatibleForm g a w = g a (hL.projection w) := by
  simp [hL.projection_apply_of_mem ha, hL.projection_map ha]

/-- The compatible form agrees with `g` on `L`. -/
theorem compatibleForm_apply_of_mem_of_mem (hL : IsMaximalTotallyReal J L) (g : BilinForm R E)
    {a b : E} (ha : a ∈ L) (hb : b ∈ L) : hL.compatibleForm g a b = g a b := by
  rw [hL.compatibleForm_apply_of_mem g ha, hL.projection_apply_of_mem hb]

/-- The compatible form makes `L` orthogonal to `J L`. -/
theorem compatibleForm_apply_map (hL : IsMaximalTotallyReal J L) (g : BilinForm R E)
    {a b : E} (ha : a ∈ L) (hb : b ∈ L) : hL.compatibleForm g a (J b) = 0 := by
  rw [hL.compatibleForm_apply_of_mem g ha, hL.projection_map hb, map_zero]

include hJ in
/-- The compatible form is invariant under `J`. -/
theorem compatibleForm_map_map (hL : IsMaximalTotallyReal J L) (g : BilinForm R E) (v w : E) :
    hL.compatibleForm g (J v) (J w) = hL.compatibleForm g v w := by
  simp only [compatibleForm_apply, hL.projection_map_map hJ, map_neg, LinearMap.neg_apply,
    neg_neg]
  exact add_comm _ _

include hJ in
/-- **Uniqueness of the compatible form.** A `J`-invariant bilinear form which agrees with `g`
on `L` and makes `L` orthogonal to `J L` is the compatible form of `g`. -/
theorem eq_compatibleForm (hL : IsMaximalTotallyReal J L) {g h : BilinForm R E}
    (hJh : ∀ v w, h (J v) (J w) = h v w) (hLg : ∀ a ∈ L, ∀ b ∈ L, h a b = g a b)
    (hLJ : ∀ a ∈ L, ∀ b ∈ L, h a (J b) = 0) : h = hL.compatibleForm g := by
  have hJL (a b : E) (ha : a ∈ L) (hb : b ∈ L) : h (J a) b = 0 := by
    rw [← hJh, show J (J a) = -a from LinearMap.congr_fun hJ a,
      map_neg, LinearMap.neg_apply, hLJ a ha b hb, neg_zero]
  refine LinearMap.ext₂ fun v w ↦ ?_
  have ha := hL.projection_apply_mem v
  have hb := hL.projection_apply_mem (J v)
  have ha' := hL.projection_apply_mem w
  have hb' := hL.projection_apply_mem (J w)
  rw [compatibleForm_apply]
  conv_lhs => rw [← hL.sub_map_projection_map hJ v, ← hL.sub_map_projection_map hJ w]
  simp only [map_sub, LinearMap.sub_apply, hJh, hLg _ ha _ ha', hLg _ hb _ hb', hLJ _ ha _ hb',
    hJL _ _ hb ha']
  ring

/-- The compatible form is characterized by `J`-invariance, agreement with `g` on `L`, and
orthogonality of `L` and `J L`. -/
theorem eq_compatibleForm_iff (hL : IsMaximalTotallyReal J L) (hJ : J ∘ₗ J = -LinearMap.id)
    {g h : BilinForm R E} :
    h = hL.compatibleForm g ↔ (∀ v w, h (J v) (J w) = h v w) ∧
      (∀ a ∈ L, ∀ b ∈ L, h a b = g a b) ∧ ∀ a ∈ L, ∀ b ∈ L, h a (J b) = 0 := by
  refine ⟨?_, fun ⟨h₁, h₂, h₃⟩ ↦ hL.eq_compatibleForm hJ h₁ h₂ h₃⟩
  rintro rfl
  exact ⟨hL.compatibleForm_map_map hJ g, fun a ha b hb ↦
    hL.compatibleForm_apply_of_mem_of_mem g ha hb, fun a ha b hb ↦
    hL.compatibleForm_apply_map g ha hb⟩

section Ordered

variable [PartialOrder R]

include hJ in
/-- The compatible form is positive definite when `g` is positive on `L`. -/
theorem compatibleForm_pos [IsOrderedAddMonoid R] (hL : IsMaximalTotallyReal J L)
    {g : BilinForm R E} (hg : ∀ a ∈ L, a ≠ 0 → 0 < g a a) {v : E} (hv : v ≠ 0) :
    0 < hL.compatibleForm g v v := by
  have hnn (a : E) (ha : a ∈ L) : 0 ≤ g a a := by
    rcases eq_or_ne a 0 with rfl | ha0
    · simp
    · exact (hg a ha ha0).le
  rw [compatibleForm_apply]
  by_cases hP : hL.projection v = 0
  · have hPJ : hL.projection (J v) ≠ 0 := by
      intro hPJ
      apply hv
      rw [← hL.sub_map_projection_map hJ v, hP, hPJ, map_zero, sub_zero]
    simp only [hP, map_zero, zero_add]
    exact hg _ (hL.projection_apply_mem _) hPJ
  · exact add_pos_of_pos_of_nonneg (hg _ (hL.projection_apply_mem v) hP)
      (hnn _ (hL.projection_apply_mem _))

include hJ in
/-- **`J L = L^⊥`.** When `g` is positive on `L`, the `J`-image of `L` is the orthogonal
complement of `L` for the compatible form. -/
theorem orthogonal_compatibleForm (hL : IsMaximalTotallyReal J L) {g : BilinForm R E}
    (hg : ∀ a ∈ L, a ≠ 0 → 0 < g a a) :
    (hL.compatibleForm g).orthogonal L = L.map J := by
  apply le_antisymm
  · intro v hv
    have hPv : hL.projection v = 0 := by
      by_contra h
      have h0 := LinearMap.BilinForm.mem_orthogonal_iff.1 hv _ (hL.projection_apply_mem v)
      rw [hL.compatibleForm_apply_of_mem g
        (hL.projection_apply_mem v)] at h0
      exact (hg _ (hL.projection_apply_mem v) h).ne' h0
    rw [← hL.sub_map_projection_map hJ v, hPv, zero_sub, ← map_neg]
    exact ⟨_, L.neg_mem (hL.projection_apply_mem _), rfl⟩
  · rintro _ ⟨b, hb, rfl⟩ a ha
    exact hL.compatibleForm_apply_map g ha hb

end Ordered

end TauCeti.IsMaximalTotallyReal

namespace TauCeti

/-- Multiplication by `i` on a complex module squares to `-1`. -/
theorem lsmul_I_comp_lsmul_I (E : Type*) [AddCommGroup E] [Module ℂ E] [Module ℝ E]
    [IsScalarTower ℝ ℂ E] :
    (LinearMap.lsmul ℂ E Complex.I).restrictScalars ℝ ∘ₗ
        (LinearMap.lsmul ℂ E Complex.I).restrictScalars ℝ = -LinearMap.id := by
  ext v
  simp [smul_smul]

/-- The projection onto a maximal totally real subspace along its `i`-image takes the real part
of complex coordinates in a real frame of the subspace. -/
theorem IsMaximalTotallyReal.projection_sum_smul {E ι : Type*} [AddCommGroup E] [Module ℂ E]
    [Module ℝ E] [IsScalarTower ℝ ℂ E] [Fintype ι] {L : Submodule ℝ E}
    (hL : IsMaximalTotallyReal ((LinearMap.lsmul ℂ E Complex.I).restrictScalars ℝ) L)
    {v : ι → E} (hv : ∀ i, v i ∈ L) (c : ι → ℂ) :
    hL.projection (∑ i, c i • v i) = ∑ i, (c i).re • v i := by
  have hsplit : ∑ i, c i • v i = ∑ i, (c i).re • v i +
      (LinearMap.lsmul ℂ E Complex.I).restrictScalars ℝ (∑ i, (c i).im • v i) := by
    simp only [map_sum, map_smul, LinearMap.restrictScalars_apply, LinearMap.lsmul_apply,
      ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    have hr (r : ℝ) (y : E) : (r : ℂ) • y = r • y := by
      rw [← smul_one_smul ℂ r y, Complex.real_smul, mul_one]
    conv_lhs => rw [← Complex.re_add_im (c i)]
    rw [add_smul, mul_smul, hr, hr]
  rw [hsplit, map_add, hL.projection_map (L.sum_mem fun i _ ↦ L.smul_mem _ (hv i)), add_zero,
    hL.projection_apply_of_mem (L.sum_mem fun i _ ↦ L.smul_mem _ (hv i))]

end TauCeti
