/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.TotallyReal.Basic
public import Mathlib.LinearAlgebra.BilinearForm.Orthogonal

/-!
# Bilinear forms compatible with a maximal totally real subspace

Let `J` be a linear endomorphism with `J ∘ J = -1` and `L` a maximal totally real subspace, so
that every vector is uniquely `a + J b` with `a, b ∈ L`. Write `P` for the projection onto `L`
along `J L`, that is `L.projection (L.map J) hL.isCompl`. For a bilinear form `g`, the form

`g'(v, w) = g(P v, P w) + g(P J v, P J w)`

is `J`-invariant, agrees with `g` on `L`, and makes `L` and `J L` orthogonal. It is the only
bilinear form with these three properties, and it is positive definite when `g` is positive on
`L`; then `J L` is exactly the orthogonal complement of `L`. This is the pointwise step in the
construction of a Hermitian metric with `J F = F^⊥` along a totally real subbundle `F`.

## Main declarations

* `TauCeti.IsMaximalTotallyReal.compatibleForm`: the form `g'` above.
* `TauCeti.IsMaximalTotallyReal.compatibleForm_map_map`: `g'` is `J`-invariant.
* `TauCeti.IsMaximalTotallyReal.eq_compatibleForm`: a `J`-invariant form agreeing with `g` on
  `L` and making `L` orthogonal to `J L` is `g'`.
* `TauCeti.IsMaximalTotallyReal.orthogonal_compatibleForm`: `J L` is the `g'`-orthogonal
  complement of `L` when `g` is positive on `L`.

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

/-- The bilinear form `g'(v, w) = g(P v, P w) + g(P J v, P J w)` built from `g` and the
projection `P` onto `L` along `J L`. -/
def compatibleForm (hL : IsMaximalTotallyReal J L) (g : BilinForm R E) : BilinForm R E :=
  g.compl₁₂ (L.projection (L.map J) hL.isCompl) (L.projection (L.map J) hL.isCompl) +
    g.compl₁₂ (L.projection (L.map J) hL.isCompl ∘ₗ J) (L.projection (L.map J) hL.isCompl ∘ₗ J)

/-- Evaluation of the compatible form. -/
@[simp]
theorem compatibleForm_apply (hL : IsMaximalTotallyReal J L) (g : BilinForm R E) (v w : E) :
    hL.compatibleForm g v w =
      g (L.projection (L.map J) hL.isCompl v) (L.projection (L.map J) hL.isCompl w) +
        g (L.projection (L.map J) hL.isCompl (J v)) (L.projection (L.map J) hL.isCompl (J w)) := by
  simp [compatibleForm]

/-- The compatible form of a form symmetric on `L` is symmetric. -/
theorem isSymm_compatibleForm (hL : IsMaximalTotallyReal J L) {g : BilinForm R E}
    (hg : ∀ a ∈ L, ∀ b ∈ L, g a b = g b a) : (hL.compatibleForm g).IsSymm :=
  LinearMap.BilinForm.isSymm_def.2 fun v w ↦ by
    simp only [compatibleForm_apply]
    rw [hg _ (L.projection_apply_mem hL.isCompl v) _ (L.projection_apply_mem hL.isCompl w),
      hg _ (L.projection_apply_mem hL.isCompl (J v)) _ (L.projection_apply_mem hL.isCompl (J w))]

/-- On `L`, the compatible form pairs a vector of `L` with `w` through the projection of `w`. -/
theorem compatibleForm_apply_of_mem (hL : IsMaximalTotallyReal J L) (g : BilinForm R E)
    {a : E} (ha : a ∈ L) (w : E) :
    hL.compatibleForm g a w = g a (L.projection (L.map J) hL.isCompl w) := by
  simp [Submodule.projection_apply_of_mem_left hL.isCompl ha, hL.projection_map_of_mem ha]

/-- The compatible form agrees with `g` on `L`. -/
theorem compatibleForm_apply_of_mem_of_mem (hL : IsMaximalTotallyReal J L) (g : BilinForm R E)
    {a b : E} (ha : a ∈ L) (hb : b ∈ L) : hL.compatibleForm g a b = g a b := by
  rw [hL.compatibleForm_apply_of_mem g ha, Submodule.projection_apply_of_mem_left hL.isCompl hb]

/-- The compatible form makes `L` orthogonal to `J L`. -/
theorem compatibleForm_apply_map (hL : IsMaximalTotallyReal J L) (g : BilinForm R E)
    {a b : E} (ha : a ∈ L) (hb : b ∈ L) : hL.compatibleForm g a (J b) = 0 := by
  rw [hL.compatibleForm_apply_of_mem g ha, hL.projection_map_of_mem hb, map_zero]

variable (hJ : J ∘ₗ J = -LinearMap.id)

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
  have ha := L.projection_apply_mem hL.isCompl v
  have hb := L.projection_apply_mem hL.isCompl (J v)
  have ha' := L.projection_apply_mem hL.isCompl w
  have hb' := L.projection_apply_mem hL.isCompl (J w)
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
  by_cases hP : L.projection (L.map J) hL.isCompl v = 0
  · have hPJ : L.projection (L.map J) hL.isCompl (J v) ≠ 0 := by
      intro hPJ
      apply hv
      rw [← hL.sub_map_projection_map hJ v, hP, hPJ, map_zero, sub_zero]
    simp only [hP, map_zero, zero_add]
    exact hg _ (L.projection_apply_mem hL.isCompl _) hPJ
  · exact add_pos_of_pos_of_nonneg (hg _ (L.projection_apply_mem hL.isCompl v) hP)
      (hnn _ (L.projection_apply_mem hL.isCompl _))

/-- **`J L = L^⊥`.** When `g` is positive on `L`, the `J`-image of `L` is the orthogonal
complement of `L` for the compatible form. -/
theorem orthogonal_compatibleForm (hL : IsMaximalTotallyReal J L) {g : BilinForm R E}
    (hg : ∀ a ∈ L, a ≠ 0 → 0 < g a a) :
    (hL.compatibleForm g).orthogonal L = L.map J := by
  apply le_antisymm
  · intro v hv
    refine (Submodule.projection_apply_eq_zero_iff hL.isCompl).1 ?_
    by_contra h
    have hPv := L.projection_apply_mem hL.isCompl v
    have h0 := LinearMap.BilinForm.mem_orthogonal_iff.1 hv _ hPv
    rw [hL.compatibleForm_apply_of_mem g hPv] at h0
    exact (hg _ hPv h).ne' h0
  · rintro _ ⟨b, hb, rfl⟩ a ha
    exact hL.compatibleForm_apply_map g ha hb

end Ordered

end TauCeti.IsMaximalTotallyReal
