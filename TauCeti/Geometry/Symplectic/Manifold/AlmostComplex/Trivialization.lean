/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Manifold.AlmostComplex.ContMDiff
public import Mathlib.Geometry.Manifold.Diffeomorph
public import TauCeti.Geometry.Manifold.VectorBundle.Section.Coordinates
import TauCeti.Topology.VectorBundle.Hom

/-!
# Finite almost complex structures in a tangent trivialization

Reading a native finite-regularity almost complex structure in an atlas trivialization gives a
field of model endomorphisms of the same order. When the trivialization covers the base, the
construction is reversible. Both directions use the existing Hom-bundle trivialization and
its native section-regularity equivalence.

The ambient manifold is smooth, as required by the canonical carrier; the field order includes
zero and infinity. No finite-dimensionality or completeness assumption is required.
-/

public noncomputable section

open Bundle Set
open scoped ContDiff Manifold

namespace Bundle.Trivialization

open TauCeti

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] {n m : ℕ∞}
  (e : Trivialization E (TotalSpace.proj : TangentBundle I M → M))
  [MemTrivializationAtlas e]

/-- Read an almost complex structure in a specified tangent-bundle trivialization. -/
def almostComplexCoordinates (J : ContMDiffAlmostComplexStructure I n M) (x : M) : E →L[ℝ] E :=
  (e.continuousLinearMapAt ℝ x).comp ((J.toEndomorphism x).comp (e.symmL ℝ x))

/-- The coordinate field evaluates by conjugating through the chosen tangent frame. -/
theorem almostComplexCoordinates_apply (J : ContMDiffAlmostComplexStructure I n M) (x : M) (v : E) :
    almostComplexCoordinates e J x v =
      e.continuousLinearMapAt ℝ x (J x (e.symmL ℝ x v)) := by
  simp [almostComplexCoordinates]

/-- The coordinate field retains the specified finite order on the full trivialization domain. -/
theorem contMDiffOn_almostComplexCoordinates (J : ContMDiffAlmostComplexStructure I n M) :
    ContMDiffOn I 𝓘(ℝ, E →L[ℝ] E) n (almostComplexCoordinates e J) e.baseSet := by
  have h := (e.continuousLinearMap (RingHom.id ℝ) e).contMDiffOn_section_iff
    (IB := I) (n := (n : ℕ∞ω))
    (s := fun x ↦ J.toEndomorphism x)
    e.open_baseSet (fun _ hx ↦ ⟨hx, hx⟩)
  exact h.1 J.toEndomorphism.contMDiff.contMDiffOn

/-- Coordinates preserve the square identity at every point of the trivialization domain. -/
theorem almostComplexCoordinates_apply_apply (J : ContMDiffAlmostComplexStructure I n M)
    {x : M} (hx : x ∈ e.baseSet) (v : E) :
    almostComplexCoordinates e J x (almostComplexCoordinates e J x v) = -v := by
  rw [almostComplexCoordinates_apply, almostComplexCoordinates_apply,
    e.symmL_continuousLinearMapAt hx, J.apply_apply, map_neg,
    e.continuousLinearMapAt_symmL hx]

@[simp]
theorem almostComplexCoordinates_ofLE (J : ContMDiffAlmostComplexStructure I n M) (h : m ≤ n) :
    almostComplexCoordinates e (J.ofLE h) = almostComplexCoordinates e J := by
  funext x
  simp [almostComplexCoordinates]

@[simp]
theorem almostComplexCoordinates_neg (J : ContMDiffAlmostComplexStructure I n M) :
    almostComplexCoordinates e (-J) = -almostComplexCoordinates e J := by
  funext x
  ext v
  simp [almostComplexCoordinates_apply]

/-- Construct a native almost complex structure from a finite-regularity coordinate field in a
tangent trivialization covering the whole base. -/
def almostComplexStructure (he : e.baseSet = univ) (A : M → E →L[ℝ] E)
    (hA : ContMDiff I 𝓘(ℝ, E →L[ℝ] E) n A) (hAA : ∀ x v, A x (A x v) = -v) :
    ContMDiffAlmostComplexStructure I n M where
  toEndomorphism :=
    ⟨(e.continuousLinearMap (RingHom.id ℝ) e).sectionFromCoordinates (𝕜 := ℝ) A,
      (e.continuousLinearMap (RingHom.id ℝ) e).contMDiff_sectionFromCoordinates
        (by simp [he]) A hA⟩
  square_neg x := by
    have hx : x ∈ e.baseSet := he.symm ▸ mem_univ x
    ext v
    simp only [ContMDiffSection.coeFn_mk, sectionFromCoordinates_apply,
      Trivialization.continuousLinearMap_symmL e e x,
      ContinuousLinearMap.comp_apply, neg_apply, ContinuousLinearMap.id_apply]
    rw [e.continuousLinearMapAt_symmL hx, hAA, map_neg,
      e.symmL_continuousLinearMapAt hx]

/-- Reconstruction evaluates by the inverse coordinate conjugation. -/
theorem almostComplexStructure_apply (he : e.baseSet = univ) (A : M → E →L[ℝ] E)
    (hA : ContMDiff I 𝓘(ℝ, E →L[ℝ] E) n A) (hAA : ∀ x v, A x (A x v) = -v)
    (x : M) (v : TangentSpace I x) :
    almostComplexStructure e he A hA hAA x v =
      e.symmL ℝ x (A x (e.continuousLinearMapAt ℝ x v)) := by
  simp only [almostComplexStructure, ContMDiffSection.coeFn_mk, sectionFromCoordinates_apply,
    Trivialization.continuousLinearMap_symmL e e x, ContinuousLinearMap.comp_apply]

/-- Reading a reconstructed structure recovers the entire coordinate field. -/
@[simp]
theorem almostComplexCoordinates_almostComplexStructure (he : e.baseSet = univ) (A : M → E →L[ℝ] E)
    (hA : ContMDiff I 𝓘(ℝ, E →L[ℝ] E) n A) (hAA : ∀ x v, A x (A x v) = -v) :
    almostComplexCoordinates e (almostComplexStructure e he A hA hAA) = A := by
  funext x
  ext v
  have hx : x ∈ e.baseSet := he.symm ▸ mem_univ x
  rw [almostComplexCoordinates_apply, almostComplexStructure_apply,
    e.continuousLinearMapAt_symmL hx, e.continuousLinearMapAt_symmL hx]

/-- Reconstruction commutes with forgetting regularity. -/
@[simp]
theorem almostComplexStructure_ofLE (he : e.baseSet = univ) (A : M → E →L[ℝ] E)
    (hA : ContMDiff I 𝓘(ℝ, E →L[ℝ] E) n A) (hAA : ∀ x v, A x (A x v) = -v)
    (h : m ≤ n) :
    (almostComplexStructure e he A hA hAA).ofLE h =
      almostComplexStructure e he A (hA.of_le (by exact_mod_cast h)) hAA := by
  ext x v
  rw [TauCeti.ContMDiffAlmostComplexStructure.ofLE_apply, almostComplexStructure_apply,
    almostComplexStructure_apply]

/-- Reconstruction commutes with negating the coordinate field. -/
theorem almostComplexStructure_neg (he : e.baseSet = univ) (A : M → E →L[ℝ] E)
    (hA : ContMDiff I 𝓘(ℝ, E →L[ℝ] E) n A) (hAA : ∀ x v, A x (A x v) = -v) :
    almostComplexStructure e he (-A) hA.neg
      (fun x v ↦ calc
        (-A) x ((-A) x v) = A x (A x v) := by simp
        _ = -v := hAA x v) =
      -(almostComplexStructure e he A hA hAA) := by
  ext x v
  simp only [TauCeti.ContMDiffAlmostComplexStructure.neg_toEndomorphism,
    ContMDiffSection.coe_neg, Pi.neg_apply, neg_apply]
  simp only [almostComplexStructure_apply, Pi.neg_apply, neg_apply, map_neg]

/-- Coordinate readings in two tangent frames are conjugate by the native frame transition.
The hypotheses are precisely membership in the two frame domains. -/
theorem almostComplexCoordinates_eq_conj
    (e' : Trivialization E (TotalSpace.proj : TangentBundle I M → M))
    [MemTrivializationAtlas e'] (J : ContMDiffAlmostComplexStructure I n M)
    {x : M} (hx : x ∈ e.baseSet) (hx' : x ∈ e'.baseSet) :
    almostComplexCoordinates e' J x =
      (e.coordChangeL ℝ e' x).toContinuousLinearMap.comp
        ((almostComplexCoordinates e J x).comp (e'.coordChangeL ℝ e x).toContinuousLinearMap) := by
  rw [← e.comp_continuousLinearEquivAt_eq_coord_change e' ⟨hx, hx'⟩,
    ← e'.comp_continuousLinearEquivAt_eq_coord_change e ⟨hx', hx⟩]
  ext v
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe,
    ContinuousLinearEquiv.trans_apply, almostComplexCoordinates_apply,
    e.coe_continuousLinearEquivAt_eq hx, e'.coe_continuousLinearEquivAt_eq hx',
    e.symm_continuousLinearEquivAt_eq hx, e'.symm_continuousLinearEquivAt_eq hx']
  rw [e.symmL_continuousLinearMapAt hx, e.symmL_continuousLinearMapAt hx]


section BaseCoordinates

variable {E' H' N : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E']
  [TopologicalSpace H'] {I' : ModelWithCorners ℝ E' H'}
  [TopologicalSpace N] [ChartedSpace H' N]

/-- In a globally covering tangent frame and any Cⁿ base coordinates, native structures
correspond exactly to finite-regularity endomorphism fields squaring to minus the identity. -/
def almostComplexEquiv (he : e.baseSet = univ) (h : M ≃ₘ^n⟮I, I'⟯ N) :
    ContMDiffAlmostComplexStructure I n M ≃
      {A : ContMDiffMap I' 𝓘(ℝ, E →L[ℝ] E) N (E →L[ℝ] E) n //
        ∀ x v, A x (A x v) = -v} where
  toFun J := ⟨⟨fun y ↦ almostComplexCoordinates e J (h.symm y),
      ((contMDiffOn_univ.1 (he ▸ contMDiffOn_almostComplexCoordinates e J))).comp
        h.symm.contMDiff⟩,
    fun y v ↦ almostComplexCoordinates_apply_apply e J (he.symm ▸ mem_univ (h.symm y)) v⟩
  invFun A := almostComplexStructure e he (fun x ↦ A.val (h x))
    (A.val.contMDiff.comp h.contMDiff) (fun x v ↦ A.property (h x) v)
  left_inv J := by
    ext x v
    rw [almostComplexStructure_apply]
    -- Unbundle the coordinate field and cancel the inverse base coordinates.
    change e.symmL ℝ x (almostComplexCoordinates e J (h.symm (h x))
      (e.continuousLinearMapAt ℝ x v)) = J x v
    rw [h.symm_apply_apply, almostComplexCoordinates_apply]
    have hx : x ∈ e.baseSet := he.symm ▸ mem_univ x
    rw [e.symmL_continuousLinearMapAt hx, e.symmL_continuousLinearMapAt hx]
  right_inv A := by
    apply Subtype.ext
    apply Subtype.ext
    funext y
    have hcoord := congrFun
      (almostComplexCoordinates_almostComplexStructure e he (fun x ↦ A.val (h x))
        (A.val.contMDiff.comp h.contMDiff) (fun x v ↦ A.property (h x) v))
      (h.symm y)
    exact hcoord.trans (congrArg A.val (h.apply_symm_apply y))

/-- The coordinate equivalence reads the field at the inverse base coordinate. -/
theorem almostComplexEquiv_apply (he : e.baseSet = univ) (h : M ≃ₘ^n⟮I, I'⟯ N)
    (J : ContMDiffAlmostComplexStructure I n M) (y : N) :
    (almostComplexEquiv e he h J).val y = almostComplexCoordinates e J (h.symm y) := by
  unfold almostComplexEquiv
  rfl

/-- The inverse equivalence conjugates through the tangent frame at the forward base coordinate. -/
theorem almostComplexEquiv_symm_apply (he : e.baseSet = univ) (h : M ≃ₘ^n⟮I, I'⟯ N)
    (A : {A : ContMDiffMap I' 𝓘(ℝ, E →L[ℝ] E) N (E →L[ℝ] E) n //
      ∀ x v, A x (A x v) = -v}) (x : M) (v : TangentSpace I x) :
    (almostComplexEquiv e he h).symm A x v =
      e.symmL ℝ x (A.val (h x) (e.continuousLinearMapAt ℝ x v)) := by
  unfold almostComplexEquiv
  exact almostComplexStructure_apply e he (fun x ↦ A.val (h x))
    (A.val.contMDiff.comp h.contMDiff) (fun x v ↦ A.property (h x) v) x v

end BaseCoordinates

end Bundle.Trivialization
