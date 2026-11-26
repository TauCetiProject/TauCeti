/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Hamiltonian.SingularPoint
public import TauCeti.Geometry.Symplectic.Hamiltonian.Williamson.Classification
import TauCeti.Analysis.Calculus.FDeriv.Comp

/-!
# The Williamson type of a nondegenerate singular point

Let `F : E → G` be a `C²` map on a finite-dimensional symplectic vector space `(E, ω)`, the local
model of an integrable system near a point `x`, and write `U = ker dF_x`. The point `x` is
nondegenerate (`TauCeti.SymplecticForm.IsNondegeneratePoint`) when the Hessians at `x` of the
critical functions `ℓ ∘ F` descend to the transversal space `U ⧸ (U ∩ U^ω)` and form a
nondegenerate family there. By Williamson's classification, this family has a **Williamson type**
`(k_e, k_h, k_f)` (`TauCeti.SymplecticForm.HasWilliamsonType`): in suitable linear symplectic
coordinates on the transversal space its span is spanned by `k_e` elliptic blocks
`(xₖ² + yₖ²) / 2`, `k_h` hyperbolic blocks `xₖ yₖ` and `k_f` focus-focus pairs. This file defines
the type of the point as the type of this family
(`TauCeti.SymplecticForm.HasWilliamsonTypeAt ω F x k_e k_h k_f`), and proves:

* every nondegenerate point has a Williamson type
  (`TauCeti.SymplecticForm.IsNondegeneratePoint.exists_hasWilliamsonTypeAt`), and a point with a
  type is nondegenerate (`TauCeti.SymplecticForm.HasWilliamsonTypeAt.isNondegeneratePoint`);
* the type is unique (`TauCeti.SymplecticForm.HasWilliamsonTypeAt.unique`);
* if the functions `ℓ ∘ F` Poisson-commute at `x`, `dim E = 2 n` and `dF_x` has rank `r`, then
  `k_e + k_h + 2 k_f = n - r`
  (`TauCeti.SymplecticForm.HasWilliamsonTypeAt.two_mul_add_add_add_finrank_range_eq_finrank`);
* the type does not depend on the choice of coordinates on the target: it is unchanged when `F`
  is composed with a `C²` map `g` whose differential at `F x` has a continuous linear left inverse
  (`TauCeti.SymplecticForm.hasWilliamsonTypeAt_comp_iff`), and in particular with a continuous
  linear equivalence `A`
  (`TauCeti.SymplecticForm.hasWilliamsonTypeAt_continuousLinearEquiv_comp_iff`), for instance the
  matrix `A ∈ GL(n, ℝ)` that makes the first `r` components of `A ∘ F` independent at `x` and the
  others critical;
* at a critical point the transversal space is `E` itself, and the type of the point is the type
  of the family of Hessians of the functions `ℓ ∘ F` on `E`
  (`TauCeti.SymplecticForm.hasWilliamsonTypeAt_iff_of_fderiv_eq_zero`), with
  `k_e + k_h + 2 k_f = n`
  (`TauCeti.SymplecticForm.HasWilliamsonTypeAt.two_mul_add_add_eq_finrank_of_fderiv_eq_zero`).

## Main definitions

* `TauCeti.SymplecticForm.HasWilliamsonTypeAt ω F x k_e k_h k_f`: `x` is a nondegenerate point of
  `F` with `k_e` elliptic, `k_h` hyperbolic and `k_f` focus-focus components.

## References

* E. Miranda and N. T. Zung, *Equivariant normal form for nondegenerate singular orbits of
  integrable Hamiltonian systems*, Annales scientifiques de l'École Normale Supérieure 37 (2004),
  819–839, Sections 2.1–2.3.
* A. V. Bolsinov and A. T. Fomenko, *Integrable Hamiltonian Systems: Geometry, Topology,
  Classification*, Chapman & Hall/CRC, 2004, Chapter 1.
-/

public section

noncomputable section

open Module

namespace TauCeti.SymplecticForm

variable {E G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup G] [NormedSpace ℝ G] {ι : Type*} {kₑ kₕ k_f : ℕ}

variable (ω : SymplecticForm E) in
/-- A point `x` has **Williamson type** `(kₑ, kₕ, k_f)` for a `C²` map `F : E → G` on a symplectic
vector space `(E, ω)` when it is a nondegenerate point of `F` and the family of transversal
Hessians, the Hessians at `x` of the critical functions `ℓ ∘ F` descended to the transversal space
`U ⧸ (U ∩ U^ω)`, `U = ker dF_x`, has Williamson type `(kₑ, kₕ, k_f)`: in suitable Darboux
coordinates of the transversal space it spans the same space as `kₑ` elliptic blocks, `kₕ`
hyperbolic blocks and `k_f` focus-focus pairs. -/
def HasWilliamsonTypeAt (F : E → G) (x : E) (kₑ kₕ k_f : ℕ) : Prop :=
  ∃ h : ω.IsNondegeneratePoint F x,
    (ω.reduction (fderiv ℝ F x).ker).HasWilliamsonType
      (fun ℓ : {ℓ : G →L[ℝ] ℝ // ℓ.comp (fderiv ℝ F x) = 0} ↦
        ω.reducedQuadraticForm _ (hessianQuadraticForm (ℓ.val ∘ F) x)
          (h.polar_hessianQuadraticForm_eq_zero ℓ.val ℓ.property)) kₑ kₕ k_f

variable {ω : SymplecticForm E} {F : E → G} {x : E}

/-- Unfolding `HasWilliamsonTypeAt`. -/
theorem hasWilliamsonTypeAt_iff :
    ω.HasWilliamsonTypeAt F x kₑ kₕ k_f ↔ ∃ h : ω.IsNondegeneratePoint F x,
      (ω.reduction (fderiv ℝ F x).ker).HasWilliamsonType
        (fun ℓ : {ℓ : G →L[ℝ] ℝ // ℓ.comp (fderiv ℝ F x) = 0} ↦
          ω.reducedQuadraticForm _ (hessianQuadraticForm (ℓ.val ∘ F) x)
            (h.polar_hessianQuadraticForm_eq_zero ℓ.val ℓ.property)) kₑ kₕ k_f :=
  Iff.rfl

/-- A point with a Williamson type is a nondegenerate point. -/
theorem HasWilliamsonTypeAt.isNondegeneratePoint (h : ω.HasWilliamsonTypeAt F x kₑ kₕ k_f) :
    ω.IsNondegeneratePoint F x :=
  h.1

/-- **Existence of the Williamson type of a nondegenerate point.** Every nondegenerate point of `F`
has a Williamson type: by Williamson's classification on the transversal space, its transversal
Hessians span the same space as elliptic, hyperbolic and focus-focus blocks. -/
theorem IsNondegeneratePoint.exists_hasWilliamsonTypeAt (h : ω.IsNondegeneratePoint F x) :
    ∃ kₑ kₕ k_f, ω.HasWilliamsonTypeAt F x kₑ kₕ k_f :=
  let ⟨kₑ, kₕ, k_f, ht⟩ := h.isNondegenerateQuadraticFamily.exists_hasWilliamsonType
  ⟨kₑ, kₕ, k_f, h, ht⟩

/-- A point is nondegenerate exactly when it has a Williamson type. -/
theorem isNondegeneratePoint_iff_exists_hasWilliamsonTypeAt :
    ω.IsNondegeneratePoint F x ↔ ∃ kₑ kₕ k_f, ω.HasWilliamsonTypeAt F x kₑ kₕ k_f :=
  ⟨IsNondegeneratePoint.exists_hasWilliamsonTypeAt,
    fun ⟨_, _, _, h⟩ ↦ h.isNondegeneratePoint⟩

/-- **Uniqueness of the Williamson type of a point.** The numbers of elliptic, hyperbolic and
focus-focus components of a nondegenerate point are well defined. -/
theorem HasWilliamsonTypeAt.unique {kₑ' kₕ' k_f' : ℕ} (h : ω.HasWilliamsonTypeAt F x kₑ kₕ k_f)
    (h' : ω.HasWilliamsonTypeAt F x kₑ' kₕ' k_f') : kₑ = kₑ' ∧ kₕ = kₕ' ∧ k_f = k_f' :=
  h.2.unique h'.2

/-- **The Williamson type and the rank.** If the functions `ℓ ∘ F` Poisson-commute at `x`, a
point of Williamson type `(kₑ, kₕ, k_f)` at which `dF_x` has rank `r` on a space of dimension
`2 n` satisfies `kₑ + kₕ + 2 k_f = n - r`: the transversal space has dimension `2 (n - r)`. -/
theorem HasWilliamsonTypeAt.two_mul_add_add_add_finrank_range_eq_finrank
    (h : ω.HasWilliamsonTypeAt F x kₑ kₕ k_f)
    (hcomm : ∀ ℓ ℓ' : G →L[ℝ] ℝ, ω.poissonBracket (ℓ ∘ F) (ℓ' ∘ F) x = 0) :
    2 * (kₑ + kₕ + 2 * k_f + finrank ℝ (fderiv ℝ F x).range) = finrank ℝ E := by
  have hd := ω.finrank_reducedSpace_ker_fderiv
    (h.isNondegeneratePoint.contDiffAt.differentiableAt two_ne_zero) hcomm
  have ht := h.2.two_mul_add_add_eq_finrank
  omega

/-- **Williamson types of critical points.** At a critical point of `F`, `x` has Williamson type
`(kₑ, kₕ, k_f)` exactly when it is a nondegenerate rank-zero point and the Hessians of the
functions `ℓ ∘ F`, on the whole space `E`, form a family of Williamson type `(kₑ, kₕ, k_f)`. -/
theorem hasWilliamsonTypeAt_iff_of_fderiv_eq_zero (h0 : fderiv ℝ F x = 0) :
    ω.HasWilliamsonTypeAt F x kₑ kₕ k_f ↔ ω.IsNondegenerateRankZeroPoint F x ∧
      ω.HasWilliamsonType (fun ℓ : G →L[ℝ] ℝ ↦ hessianQuadraticForm (ℓ ∘ F) x) kₑ kₕ k_f := by
  have hker : (fderiv ℝ F x).ker = ⊤ := by
    rw [h0]
    exact LinearMap.ker_zero
  have key (hx : ω.IsNondegeneratePoint F x) :=
    (hasWilliamsonType_reduction_iff_of_eq_top (kₑ := kₑ) (kₕ := kₕ) (k_f := k_f) hker _
      fun ℓ : {ℓ : G →L[ℝ] ℝ // ℓ.comp (fderiv ℝ F x) = 0} ↦
        hx.polar_hessianQuadraticForm_eq_zero ℓ.val ℓ.property).trans
      (hasWilliamsonType_iff_of_span_eq (span_range_hessianQuadraticForm_of_fderiv_eq_zero h0))
  have hnd := isNondegeneratePoint_iff_isNondegenerateRankZeroPoint (ω := ω) h0
  exact ⟨fun ⟨hx, ht⟩ ↦ ⟨hnd.1 hx, (key hx).1 ht⟩,
    fun ⟨hx, ht⟩ ↦ ⟨hnd.2 hx, (key (hnd.2 hx)).2 ht⟩⟩

/-- **The Williamson type of a critical point fills the dimension.** At a critical point of
Williamson type `(kₑ, kₕ, k_f)` on a space of dimension `2 n`, `kₑ + kₕ + 2 k_f = n`. -/
theorem HasWilliamsonTypeAt.two_mul_add_add_eq_finrank_of_fderiv_eq_zero
    (h : ω.HasWilliamsonTypeAt F x kₑ kₕ k_f) (h0 : fderiv ℝ F x = 0) :
    2 * (kₑ + kₕ + 2 * k_f) = finrank ℝ E :=
  ((hasWilliamsonTypeAt_iff_of_fderiv_eq_zero h0).1 h).2.two_mul_add_add_eq_finrank

/-- Unbundled form of `HasWilliamsonTypeAt`, with the kernel of `dF_x` replaced by any `U` equal
to it. -/
private theorem hasWilliamsonTypeAt_iff_of_ker_eq {U : Submodule ℝ E}
    (hU : (fderiv ℝ F x).ker = U) :
    ω.HasWilliamsonTypeAt F x kₑ kₕ k_f ↔ ω.IsNondegeneratePoint F x ∧
      ∃ hQ : ∀ ℓ : G →L[ℝ] ℝ, ℓ.comp (fderiv ℝ F x) = 0 → ∀ w ∈ U ⊓ ω.orthogonal U, ∀ u ∈ U,
          QuadraticMap.polar (hessianQuadraticForm (ℓ ∘ F) x) w u = 0,
        (ω.reduction U).HasWilliamsonType
          (fun ℓ : {ℓ : G →L[ℝ] ℝ // ℓ.comp (fderiv ℝ F x) = 0} ↦
            ω.reducedQuadraticForm U _ (hQ ℓ.val ℓ.property)) kₑ kₕ k_f := by
  subst hU
  exact ⟨fun ⟨h, ht⟩ ↦ ⟨h, h.polar_hessianQuadraticForm_eq_zero, ht⟩, fun ⟨h, _, ht⟩ ↦ ⟨h, ht⟩⟩

/-- **Invariance of the Williamson type under reparametrization of the values.** Composing `F` with
a `C²` map `g` whose differential `Dg` at `F x` has a continuous linear left inverse does not change
the Williamson type of a point: the kernel of the differential, and hence the transversal space, is
the same, and the transversal Hessians of `g ∘ F` span the same space as those of `F`
(`TauCeti.SymplecticForm.span_range_reducedQuadraticForm_hessianQuadraticForm_comp_eq`). -/
theorem hasWilliamsonTypeAt_comp_iff {G' : Type*} [NormedAddCommGroup G'] [NormedSpace ℝ G']
    {g : G → G'} (hg : ContDiffAt ℝ 2 g (F x)) (hD : (fderiv ℝ g (F x)).HasLeftInverse)
    (hF : ContDiffAt ℝ 2 F x) :
    ω.HasWilliamsonTypeAt (g ∘ F) x kₑ kₕ k_f ↔ ω.HasWilliamsonTypeAt F x kₑ kₕ k_f := by
  rw [hasWilliamsonTypeAt_iff_of_ker_eq (ker_fderiv_comp_of_injective
      (hg.differentiableAt two_ne_zero) hD.injective (hF.differentiableAt two_ne_zero)),
    hasWilliamsonTypeAt_iff_of_ker_eq rfl]
  exact and_congr (isNondegeneratePoint_comp_iff hg hD hF)
    ((Equiv.ofIff (forall_polar_hessianQuadraticForm_comp_eq_zero_iff hg hD hF)).exists_congr
      fun hQ' ↦ hasWilliamsonType_iff_of_span_eq
        (span_range_reducedQuadraticForm_hessianQuadraticForm_comp_eq hg hD hF hQ' _))

/-- **Invariance of the Williamson type under linear changes of the values.** Composing `F` with a
continuous linear equivalence `A : G ≃ G'` does not change the Williamson type of a point. Unlike
`hasWilliamsonTypeAt_comp_iff`, no regularity of `F` is assumed: `F` is `C²` at `x` exactly when
`A ∘ F` is. -/
@[simp]
theorem hasWilliamsonTypeAt_continuousLinearEquiv_comp_iff {G' : Type*} [NormedAddCommGroup G']
    [NormedSpace ℝ G'] (A : G ≃L[ℝ] G') :
    ω.HasWilliamsonTypeAt (A ∘ F) x kₑ kₕ k_f ↔ ω.HasWilliamsonTypeAt F x kₑ kₕ k_f := by
  by_cases hF : ContDiffAt ℝ 2 F x
  · exact hasWilliamsonTypeAt_comp_iff (A : G →L[ℝ] G').contDiff.contDiffAt
      ⟨(A.symm : G' →L[ℝ] G), fun v ↦ by simp [A.fderiv]⟩ hF
  refine iff_of_false (fun h ↦ hF ?_) fun h ↦ hF h.isNondegeneratePoint.contDiffAt
  have := ((A.symm : G' →L[ℝ] G).contDiff.contDiffAt (x := A (F x))).comp x
    h.isNondegeneratePoint.contDiffAt
  simpa [Function.comp_def] using this

end TauCeti.SymplecticForm
