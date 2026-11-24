/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Fredholm.Adjoint
public import TauCeti.Analysis.InnerProductSpace.HodgeLaplacian
public import TauCeti.Analysis.InnerProductSpace.Projection.Completeness

/-!
# The folded operator of a two-periodic complex

Let `a : V → W` and `b : W → V` be bounded operators between Hilbert spaces with `b a = 0` and
`a b = 0`, so that `V → W → V → W → ⋯` is a *two-periodic complex*. Every finite complex of
Hilbert spaces `V₀ → V₁ → ⋯ → V_N` folds into one: `V` is the sum of the terms of even degree,
`W` the sum of the terms of odd degree, `a` is the differential on even terms and `b` the
differential on odd terms. For the de Rham complex this is `d : Ω^even → Ω^odd` together with
`d : Ω^odd → Ω^even`. The two cohomology groups of the folded complex, `ker a / range b` at `V` and
`ker b / range a` at `W`, are the even and the odd part of the cohomology of the original complex.

The *folded operator* of the complex is `a + b† : V → W`; for the de Rham complex it is
`d + d* : Ω^even → Ω^odd`, whose index is the Euler characteristic. This file proves the Hilbert
space facts behind that statement, by the Hodge theory of the complex.

* `ContinuousLinearMap.ker_add_adjoint`: the kernel of `a + b†` is the space `ker a ⊓ ker b†` of
  harmonic elements of `V`, because it is the kernel of `(a + b†)† (a + b†)`, the Laplacian of
  the complex at `V` (`ContinuousLinearMap.ker_add_adjoint_eq_ker_hodgeLaplacian`).
* `ContinuousLinearMap.adjoint_add_adjoint`: the adjoint of `a + b†` is the folded operator `b + a†`
  of the complex `W → V → W`, so its kernel is the space `ker b ⊓ ker a†` of harmonic elements of
  `W`.
* `ContinuousLinearMap.adjoint_add_adjoint_comp_add_adjoint`,
  `ContinuousLinearMap.add_adjoint_comp_adjoint_add_adjoint`: `(a + b†)† (a + b†)` and
  `(a + b†) (a + b†)†` are the Laplacians `b b† + a† a` and `a a† + b† b`
  (`ContinuousLinearMap.hodgeLaplacian`) of the complex at `V` and at `W`.
* `ContinuousLinearMap.range_add_adjoint`: the range of `a + b†` is the orthogonal sum
  `range a ⊔ range b†`, which is closed when `a` and `b` have closed range
  (`ContinuousLinearMap.isClosed_range_add_adjoint`).
* `ContinuousLinearMap.range_sup_ker_inf_ker_adjoint` and
  `ContinuousLinearMap.kerInfKerAdjointEquiv`: when `b` has closed range, `ker a` is the
  orthogonal sum of `range b` and the harmonic elements (the Hodge decomposition), so every class
  of `ker a / range b` has exactly one harmonic representative.
* `ContinuousLinearMap.index_add_adjoint` and
  `ContinuousLinearMap.index_add_adjoint_eq_finrank_quotient_sub_finrank_quotient`: when `a` and
  `b` have closed range, the index of `a + b†` is `dim (ker a ⊓ ker b†) - dim (ker b ⊓ ker a†)`,
  which is the Euler characteristic `dim (ker a / range b) - dim (ker b / range a)` of the
  complex.
* `ContinuousLinearMap.injective_add_adjoint_iff`, `ContinuousLinearMap.surjective_add_adjoint_iff`
  and `ContinuousLinearMap.bijective_add_adjoint_iff`: when `a` and `b` have closed range, `a + b†`
  is injective exactly when the complex is exact at `V`, surjective exactly when it is exact at
  `W`, and bijective exactly when it is exact at `V` and at `W`. Applied fibrewise to principal
  symbols, where all spaces are finite-dimensional, this says that the folded symbol of an
  elliptic complex is elliptic.

## References

* M. F. Atiyah, I. M. Singer, *The index of elliptic operators: I*, Ann. of Math. 87 (1968),
  §7, pp. 520–522.
* J. Brüning, M. Lesch, *Hilbert complexes*, J. Funct. Anal. 108 (1992), 88–132, §2.
-/

public section

open Module Function
open scoped InnerProductSpace

namespace ContinuousLinearMap

variable {𝕜 V W : Type*} [RCLike 𝕜]
  [NormedAddCommGroup V] [InnerProductSpace 𝕜 V] [CompleteSpace V]
  [NormedAddCommGroup W] [InnerProductSpace 𝕜 W] [CompleteSpace W]
  {a : V →L[𝕜] W} {b : W →L[𝕜] V}

/-! ### Kernel, adjoint and Laplacians -/

/-- The adjoint of the folded operator `a + b†` is the folded operator `b + a†` of the complex
`W → V → W`. -/
theorem adjoint_add_adjoint (a : V →L[𝕜] W) (b : W →L[𝕜] V) :
    adjoint (a + adjoint b) = b + adjoint a := by
  rw [map_add, adjoint_adjoint, add_comm]

/-- If `b a = 0`, the ranges of `a` and `b†` are orthogonal: `⟪a v, b† w⟫ = ⟪b a v, w⟫ = 0`. -/
theorem isOrtho_range_range_adjoint (hba : b ∘L a = 0) : a.range ⟂ (adjoint b).range := by
  rw [Submodule.isOrtho_iff_inner_eq]
  rintro _ ⟨v, rfl⟩ _ ⟨w, rfl⟩
  rw [coe_coe, coe_coe, adjoint_inner_right, ← comp_apply, hba, zero_apply, inner_zero_left]

/-- If `b a = 0`, then `(a + b†)† (a + b†)` is the Laplacian `b b† + a† a` of the complex at
`V`. -/
theorem adjoint_add_adjoint_comp_add_adjoint (hba : b ∘L a = 0) :
    adjoint (a + adjoint b) ∘L (a + adjoint b) = b.hodgeLaplacian a := by
  rw [adjoint_add_adjoint, add_comp, comp_add, comp_add, hba, ← adjoint_comp, hba, map_zero,
    hodgeLaplacian_def]
  abel

/-- If `b a = 0`, the kernel of the folded operator `a + b†` is the kernel of the Laplacian
`b b† + a† a` of the complex at `V`. -/
theorem ker_add_adjoint_eq_ker_hodgeLaplacian (hba : b ∘L a = 0) :
    (a + adjoint b).ker = (b.hodgeLaplacian a).ker := by
  rw [← adjoint_add_adjoint_comp_add_adjoint hba, ker_adjoint_comp_self]

/-- **The kernel of the folded operator.** If `b a = 0`, the kernel of `a + b†` is the space
`ker a ⊓ ker b†` of harmonic elements of `V`. -/
theorem ker_add_adjoint (hba : b ∘L a = 0) : (a + adjoint b).ker = a.ker ⊓ (adjoint b).ker := by
  rw [ker_add_adjoint_eq_ker_hodgeLaplacian hba, ker_hodgeLaplacian, inf_comm]

/-- If `a b = 0`, then `(a + b†) (a + b†)†` is the Laplacian `a a† + b† b` of the complex at
`W`. -/
theorem add_adjoint_comp_adjoint_add_adjoint (hab : a ∘L b = 0) :
    (a + adjoint b) ∘L adjoint (a + adjoint b) = a.hodgeLaplacian b := by
  rw [adjoint_add_adjoint, add_comp, comp_add, comp_add, hab, ← adjoint_comp, hab, map_zero,
    hodgeLaplacian_def]
  abel

/-! ### The range -/

/-- If `a b = 0`, the range of `a` lies in the range of the folded operator `a + b†`: on the
orthogonal complement of `ker a`, the closure of `range a†`, the operator `b†` vanishes. -/
theorem range_le_range_add_adjoint (hab : a ∘L b = 0) : a.range ≤ (a + adjoint b).range := by
  rintro _ ⟨v, rfl⟩
  have : a.ker.HasOrthogonalProjection :=
    Submodule.hasOrthogonalProjection_iff_isClosed.2 a.isClosed_ker
  -- `b†` kills `range a†`, hence its closure `(ker a)ᗮ`.
  have hle : (adjoint a).range.topologicalClosure ≤ (adjoint b).ker := by
    refine (adjoint a).range.topologicalClosure_minimal ?_ (adjoint b).isClosed_ker
    rintro _ ⟨w, rfl⟩
    rw [LinearMap.mem_ker, coe_coe, coe_coe, ← comp_apply, ← adjoint_comp, hab, map_zero,
      zero_apply]
  have hb : adjoint b (v - a.ker.starProjection v) = 0 :=
    LinearMap.mem_ker.1 (hle (orthogonal_ker a ▸ a.ker.sub_starProjection_mem_orthogonal v))
  have ha : a (a.ker.starProjection v) = 0 := LinearMap.mem_ker.1 (a.ker.starProjection_apply_mem v)
  refine ⟨v - a.ker.starProjection v, ?_⟩
  rw [coe_coe, coe_coe, add_apply, hb, add_zero, map_sub, ha, sub_zero]

/-- **The range of the folded operator.** If `a b = 0`, the range of `a + b†` is
`range a ⊔ range b†`. -/
theorem range_add_adjoint (hab : a ∘L b = 0) :
    (a + adjoint b).range = a.range ⊔ (adjoint b).range := by
  refine le_antisymm (by simpa using LinearMap.range_add_le (a : V →ₗ[𝕜] W) (adjoint b))
    (sup_le (range_le_range_add_adjoint hab) ?_)
  -- `b†` is the first operator of the complex `V → W → V` formed by `b†` and `a†`.
  have h := range_le_range_add_adjoint (a := adjoint b) (b := adjoint a)
    (by rw [← adjoint_comp, hab, map_zero])
  rwa [adjoint_adjoint, add_comm] at h

/-- If `a b = 0`, `b a = 0` and `a` and `b` have closed range, the folded operator `a + b†` has
closed range: its range is the sum of the orthogonal closed subspaces `range a` and `range b†`. -/
theorem isClosed_range_add_adjoint (hab : a ∘L b = 0) (hba : b ∘L a = 0)
    (ha : IsClosed (a.range : Set W)) (hb : IsClosed (b.range : Set V)) :
    IsClosed ((a + adjoint b).range : Set W) := by
  have : a.range.HasOrthogonalProjection := Submodule.hasOrthogonalProjection_iff_isClosed.2 ha
  have : (adjoint b).range.HasOrthogonalProjection :=
    Submodule.hasOrthogonalProjection_iff_isClosed.2 (b.isClosed_range_adjoint_of_isClosed_range hb)
  rw [range_add_adjoint hab]
  exact (isOrtho_range_range_adjoint hba).isClosed_sup

/-! ### Hodge decomposition and harmonic representatives -/

/-- **The Hodge decomposition of the cycles.** If `a b = 0` and `b` has closed range, then `ker a`
is the sum of the boundaries `range b` and the harmonic elements `ker a ⊓ ker b†`, which are
orthogonal since `ker b† = (range b)ᗮ`. -/
theorem range_sup_ker_inf_ker_adjoint (hab : a ∘L b = 0) (hb : IsClosed (b.range : Set V)) :
    b.range ⊔ a.ker ⊓ (adjoint b).ker = a.ker := by
  have : b.range.HasOrthogonalProjection := Submodule.hasOrthogonalProjection_iff_isClosed.2 hb
  rw [← orthogonal_range, inf_comm]
  -- The boundaries `range b` are cycles.
  exact Submodule.sup_orthogonal_inf_of_hasOrthogonalProjection
    (LinearMap.range_le_ker_iff.2 (by simpa using congrArg toLinearMap hab))

/-- The harmonic part `v - P v` of a cycle `v`, where `P` is the orthogonal projection onto
`range b`, is a harmonic element in the class of `v`. -/
private theorem sub_starProjection_mem_ker_inf_ker_adjoint (hab : a ∘L b = 0)
    [b.range.HasOrthogonalProjection] (v : a.ker) :
    (v : V) - b.range.starProjection v ∈ a.ker ⊓ (adjoint b).ker :=
  ⟨sub_mem v.property
      ((range_sup_ker_inf_ker_adjoint hab b.range.isClosed_of_hasOrthogonalProjection).le
        (Submodule.mem_sup_left (b.range.starProjection_apply_mem v))),
    orthogonal_range b ▸ b.range.sub_starProjection_mem_orthogonal v⟩

/-- A cycle `v` and its harmonic part `v - P v` have the same cohomology class. -/
private theorem mk_eq_mk_sub_starProjection (hab : a ∘L b = 0) [b.range.HasOrthogonalProjection]
    (v : a.ker) :
    (Submodule.Quotient.mk v : a.ker ⧸ b.range.submoduleOf a.ker) =
      Submodule.Quotient.mk ⟨(v : V) - b.range.starProjection v,
        (sub_starProjection_mem_ker_inf_ker_adjoint hab v).1⟩ := by
  rw [Submodule.Quotient.eq]
  simp [Submodule.submoduleOf]

private theorem bijective_mkQ_comp_inclusion (hab : a ∘L b = 0) (hb : IsClosed (b.range : Set V)) :
    Bijective ((b.range.submoduleOf a.ker).mkQ ∘ₗ
      Submodule.inclusion (inf_le_left : a.ker ⊓ (adjoint b).ker ≤ a.ker)) := by
  have : b.range.HasOrthogonalProjection := Submodule.hasOrthogonalProjection_iff_isClosed.2 hb
  refine ⟨(injective_iff_map_eq_zero _).2 fun h hh ↦ ?_, fun q ↦ ?_⟩
  · -- A harmonic boundary lies in `range b ⊓ (range b)ᗮ = ⊥`.
    rw [LinearMap.comp_apply, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero] at hh
    have h₁ : (h : V) ∈ b.range := by simpa [Submodule.submoduleOf] using hh
    have h₂ : (h : V) ∈ b.rangeᗮ := by rw [orthogonal_range]; exact h.property.2
    exact Subtype.ext (inner_self_eq_zero.1 (Submodule.inner_right_of_mem_orthogonal h₁ h₂))
  · induction q using Submodule.Quotient.induction_on with | _ v => ?_
    exact ⟨⟨_, sub_starProjection_mem_ker_inf_ker_adjoint hab v⟩,
      (mk_eq_mk_sub_starProjection hab v).symm⟩

/-- **Harmonic representatives.** If `a b = 0` and `b` has closed range, every class of the
cohomology `ker a / range b` has exactly one harmonic representative: the harmonic elements
`ker a ⊓ ker b†` map isomorphically onto the cohomology. -/
noncomputable def kerInfKerAdjointEquiv (hab : a ∘L b = 0) (hb : IsClosed (b.range : Set V)) :
    (a.ker ⊓ (adjoint b).ker : Submodule 𝕜 V) ≃ₗ[𝕜] a.ker ⧸ b.range.submoduleOf a.ker :=
  .ofBijective _ (bijective_mkQ_comp_inclusion hab hb)

/-- `ContinuousLinearMap.kerInfKerAdjointEquiv` sends a harmonic element to its cohomology
class. -/
@[simp]
theorem kerInfKerAdjointEquiv_apply (hab : a ∘L b = 0) (hb : IsClosed (b.range : Set V))
    (h : (a.ker ⊓ (adjoint b).ker : Submodule 𝕜 V)) :
    kerInfKerAdjointEquiv hab hb h = Submodule.Quotient.mk (Submodule.inclusion inf_le_left h) := by
  rw [kerInfKerAdjointEquiv, LinearEquiv.ofBijective_apply, LinearMap.comp_apply,
    Submodule.mkQ_apply]

/-- The harmonic representative of the class of a cycle `v` is `v - P v`, where `P` is the
orthogonal projection onto `range b`. -/
@[simp]
theorem coe_kerInfKerAdjointEquiv_symm_mk (hab : a ∘L b = 0) [b.range.HasOrthogonalProjection]
    (v : a.ker) :
    ((kerInfKerAdjointEquiv hab b.range.isClosed_of_hasOrthogonalProjection).symm
      (Submodule.Quotient.mk v) : V) = v - b.range.starProjection v := by
  have h : (kerInfKerAdjointEquiv hab b.range.isClosed_of_hasOrthogonalProjection).symm
      (Submodule.Quotient.mk v) =
      ⟨_, sub_starProjection_mem_ker_inf_ker_adjoint hab v⟩ := by
    rw [LinearEquiv.symm_apply_eq, kerInfKerAdjointEquiv_apply, mk_eq_mk_sub_starProjection hab,
      Submodule.inclusion_apply]
  rw [h]

/-! ### The index -/

/-- **The index of the folded operator.** If `a b = 0`, `b a = 0` and `a` and `b` have closed
range, the index of `a + b† : V → W` is `dim (ker a ⊓ ker b†) - dim (ker b ⊓ ker a†)`, the
difference of the dimensions of the harmonic elements of `V` and of `W`. -/
theorem index_add_adjoint (hab : a ∘L b = 0) (hba : b ∘L a = 0)
    (ha : IsClosed (a.range : Set W)) (hb : IsClosed (b.range : Set V)) :
    (a + adjoint b).index =
      finrank 𝕜 (a.ker ⊓ (adjoint b).ker : Submodule 𝕜 V) -
        finrank 𝕜 (b.ker ⊓ (adjoint a).ker : Submodule 𝕜 W) := by
  rw [index_eq_finrank_sub, (cokerEquivKerAdjoint _
    (isClosed_range_add_adjoint hab hba ha hb)).toLinearEquiv.finrank_eq]
  -- The cokernel is the kernel of the adjoint `b + a†`, the folded operator of `W → V → W`.
  have h₁ : LinearMap.ker ((a + adjoint b : V →L[𝕜] W) : V →ₗ[𝕜] W) =
      a.ker ⊓ (adjoint b).ker := ker_add_adjoint hba
  have h₂ : LinearMap.ker ((adjoint (a + adjoint b) : W →L[𝕜] V) : W →ₗ[𝕜] V) =
      b.ker ⊓ (adjoint a).ker := by
    rw [adjoint_add_adjoint]
    exact ker_add_adjoint hab
  rw [h₁, h₂]

/-- **The index of the folded operator is the Euler characteristic.** If `a b = 0`, `b a = 0` and
`a` and `b` have closed range, the index of `a + b†` is
`dim (ker a / range b) - dim (ker b / range a)`. -/
theorem index_add_adjoint_eq_finrank_quotient_sub_finrank_quotient (hab : a ∘L b = 0)
    (hba : b ∘L a = 0)
    (ha : IsClosed (a.range : Set W)) (hb : IsClosed (b.range : Set V)) :
    (a + adjoint b).index =
      finrank 𝕜 (a.ker ⧸ b.range.submoduleOf a.ker) -
        finrank 𝕜 (b.ker ⧸ a.range.submoduleOf b.ker) := by
  rw [index_add_adjoint hab hba ha hb, (kerInfKerAdjointEquiv hab hb).finrank_eq,
    (kerInfKerAdjointEquiv hba ha).finrank_eq]

/-! ### Exactness -/

/-- If `a b = 0`, `b a = 0` and `b` has closed range, the folded operator `a + b†` is injective
exactly when the complex is exact at `V`. -/
theorem injective_add_adjoint_iff (hab : a ∘L b = 0) (hba : b ∘L a = 0)
    (hb : IsClosed (b.range : Set V)) : Injective (a + adjoint b) ↔ Exact b a := by
  rw [b.exact_iff_injective_hodgeLaplacian a hab hb]
  simp only [← coe_coe, ← LinearMap.ker_eq_bot]
  rw [ker_add_adjoint_eq_ker_hodgeLaplacian hba]

/-- If `a b = 0`, `b a = 0` and `a` and `b` have closed range, the folded operator `a + b†` is
surjective exactly when the complex is exact at `W`. -/
theorem surjective_add_adjoint_iff (hab : a ∘L b = 0) (hba : b ∘L a = 0)
    (ha : IsClosed (a.range : Set W)) (hb : IsClosed (b.range : Set V)) :
    Surjective (a + adjoint b) ↔ Exact a b := by
  rw [← injective_add_adjoint_iff hba hab ha, ← adjoint_add_adjoint a b]
  -- `a + b†` is onto exactly when the orthogonal complement `ker (a + b†)†` of its range is zero.
  have : (a + adjoint b).range.HasOrthogonalProjection :=
    Submodule.hasOrthogonalProjection_iff_isClosed.2 (isClosed_range_add_adjoint hab hba ha hb)
  simp only [← coe_coe, ← LinearMap.range_eq_top, ← LinearMap.ker_eq_bot]
  rw [← orthogonal_range, Submodule.orthogonal_eq_bot_iff]

/-- **Exactness and the folded operator.** If `a b = 0`, `b a = 0` and `a` and `b` have closed
range, the folded operator `a + b†` is bijective exactly when the complex is exact at `V` and at
`W`. -/
theorem bijective_add_adjoint_iff (hab : a ∘L b = 0) (hba : b ∘L a = 0)
    (ha : IsClosed (a.range : Set W)) (hb : IsClosed (b.range : Set V)) :
    Bijective (a + adjoint b) ↔ Exact b a ∧ Exact a b := by
  rw [Bijective, injective_add_adjoint_iff hab hba hb, surjective_add_adjoint_iff hab hba ha hb]

end ContinuousLinearMap
