/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Fredholm.Prod
public import TauCeti.Analysis.Normed.Lp.ProdLp
public import TauCeti.Topology.Algebra.Module.ContinuousLinearMap.IdempotentRange

/-!
# Range compressions and their Fredholm indices

Given continuous endomorphisms `p : E →L[𝕜] E` and `q : F →L[𝕜] F` and a continuous linear map
`T : E →L[𝕜] F`, the operator `ContinuousLinearMap.rangeCompression p q T : p.range →L[𝕜] q.range`
sends `w ∈ p.range` to `q (T w)`. Its integer index `ContinuousLinearMap.compressionIndex p q T`
is invariant under conjugation by continuous linear equivalences (`compressionIndex_conj`),
invariant under extension along continuous linear retracts (`compressionIndex_retract`), and
additive under `WithLp` block sums of Fredholm compressions (`compressionIndex_withLpProdMap`).
-/

public section

open scoped ENNReal

namespace ContinuousLinearMap

section Ring

variable {𝕜 E E' F F' : Type*} [Ring 𝕜]
  [TopologicalSpace E] [AddCommGroup E] [Module 𝕜 E]
  [TopologicalSpace E'] [AddCommGroup E'] [Module 𝕜 E']
  [TopologicalSpace F] [AddCommGroup F] [Module 𝕜 F]
  [TopologicalSpace F'] [AddCommGroup F'] [Module 𝕜 F']

/-- Compression `q ∘ T ∘ ι : p.range →L[𝕜] q.range` of `T : E →L[𝕜] F` between the ranges of
endomorphisms `p : E →L[𝕜] E` and `q : F →L[𝕜] F`. -/
def rangeCompression (p : E →L[𝕜] E) (q : F →L[𝕜] F) (T : E →L[𝕜] F) :
    p.range →L[𝕜] q.range :=
  q.rangeRestrict ∘L T ∘L p.range.subtypeL

theorem rangeCompression_def (p : E →L[𝕜] E) (q : F →L[𝕜] F) (T : E →L[𝕜] F) :
    rangeCompression p q T = q.rangeRestrict ∘L T ∘L p.range.subtypeL :=
  (rfl)

@[simp]
theorem coe_rangeCompression_apply (p : E →L[𝕜] E) (q : F →L[𝕜] F) (T : E →L[𝕜] F)
    (w : p.range) : (rangeCompression p q T w : F) = q (T w) :=
  (rfl)

/-- The integer index of `rangeCompression p q T : p.range →L[𝕜] q.range`. -/
noncomputable def compressionIndex (p : E →L[𝕜] E) (q : F →L[𝕜] F) (T : E →L[𝕜] F) : ℤ :=
  (rangeCompression p q T).index

theorem compressionIndex_def (p : E →L[𝕜] E) (q : F →L[𝕜] F) (T : E →L[𝕜] F) :
    compressionIndex p q T = (rangeCompression p q T).index :=
  (rfl)

/-- Extending `p` and `q` along continuous linear retracts `r₁ ∘L i₁ = id` and `r₂ ∘L i₂ = id`
identifies `compressionIndex (i₁ ∘L p ∘L r₁) (i₂ ∘L q ∘L r₂) T` with
`compressionIndex p q (r₂ ∘L T ∘L i₁)`. -/
theorem compressionIndex_retract {i₁ : E →L[𝕜] E'} {r₁ : E' →L[𝕜] E}
    {i₂ : F →L[𝕜] F'} {r₂ : F' →L[𝕜] F}
    (hri₁ : r₁.comp i₁ = .id 𝕜 E) (hri₂ : r₂.comp i₂ = .id 𝕜 F)
    (p : E →L[𝕜] E) (q : F →L[𝕜] F) (T : E' →L[𝕜] F') :
    compressionIndex (i₁ ∘L p ∘L r₁) (i₂ ∘L q ∘L r₂) T =
      compressionIndex p q (r₂ ∘L T ∘L i₁) := by
  let p' := i₁ ∘L p ∘L r₁
  let q' := i₂ ∘L q ∘L r₂
  let ep := rangeRetractEquiv p hri₁
  let eq_ := rangeRetractEquiv q hri₂
  have intertwine :
      (rangeCompression p' q' T).comp (ep : p.range →L[𝕜] p'.range) =
        (eq_ : q.range →L[𝕜] q'.range).comp (rangeCompression p q (r₂ ∘L T ∘L i₁)) := by
    ext w
    simp only [comp_apply, ContinuousLinearEquiv.coe_coe, coe_rangeCompression_apply,
      coe_rangeRetractEquiv_apply, ep, eq_, p', q']
  rw [compressionIndex_def, compressionIndex_def]
  calc
    (rangeCompression p' q' T).index
      = ((rangeCompression p' q' T).comp (ep : p.range →L[𝕜] p'.range)).index :=
          ((rangeCompression p' q' T).index_comp_equiv ep).symm
    _ = ((eq_ : q.range →L[𝕜] q'.range).comp (rangeCompression p q (r₂ ∘L T ∘L i₁))).index := by
          rw [intertwine]
    _ = (rangeCompression p q (r₂ ∘L T ∘L i₁)).index :=
          (rangeCompression p q (r₂ ∘L T ∘L i₁)).index_equiv_comp eq_

/-- Conjugating `p`, `q`, and `T` by continuous linear equivalences `e₁ : E ≃L[𝕜] E'` and
`e₂ : F ≃L[𝕜] F'` leaves `compressionIndex p q T` unchanged. -/
theorem compressionIndex_conj (e₁ : E ≃L[𝕜] E') (e₂ : F ≃L[𝕜] F')
    (p : E →L[𝕜] E) (q : F →L[𝕜] F) (T : E →L[𝕜] F) :
    compressionIndex ((e₁ : E →L[𝕜] E') ∘L p ∘L (e₁.symm : E' →L[𝕜] E))
      ((e₂ : F →L[𝕜] F') ∘L q ∘L (e₂.symm : F' →L[𝕜] F))
      ((e₂ : F →L[𝕜] F') ∘L T ∘L (e₁.symm : E' →L[𝕜] E)) =
      compressionIndex p q T := by
  have h₁ : (e₁.symm : E' →L[𝕜] E).comp (e₁ : E →L[𝕜] E') = .id 𝕜 E := by
    ext x
    simp
  have h₂ : (e₂.symm : F' →L[𝕜] F).comp (e₂ : F →L[𝕜] F') = .id 𝕜 F := by
    ext y
    simp
  rw [compressionIndex_retract h₁ h₂]
  congr 1
  ext x
  simp

end Ring

section BlockSum

variable {p : ℝ≥0∞} {𝕜 E₁ E₂ F₁ F₂ : Type*} [NontriviallyNormedField 𝕜]
  [TopologicalSpace E₁] [AddCommGroup E₁] [Module 𝕜 E₁]
  [TopologicalSpace E₂] [AddCommGroup E₂] [Module 𝕜 E₂]
  [TopologicalSpace F₁] [AddCommGroup F₁] [Module 𝕜 F₁]
  [TopologicalSpace F₂] [AddCommGroup F₂] [Module 𝕜 F₂]

/-- `compressionIndex` is additive under `WithLp` block sums of Fredholm range compressions. -/
theorem compressionIndex_withLpProdMap
    (p₁ : E₁ →L[𝕜] E₁) (q₁ : F₁ →L[𝕜] F₁) (T₁ : E₁ →L[𝕜] F₁)
    (p₂ : E₂ →L[𝕜] E₂) (q₂ : F₂ →L[𝕜] F₂) (T₂ : E₂ →L[𝕜] F₂)
    (h₁ : (rangeCompression p₁ q₁ T₁).IsFredholm)
    (h₂ : (rangeCompression p₂ q₂ T₂).IsFredholm) :
    compressionIndex (p₁.withLpProdMap p p₂) (q₁.withLpProdMap p q₂)
        (T₁.withLpProdMap p T₂) =
      compressionIndex p₁ q₁ T₁ + compressionIndex p₂ q₂ T₂ := by
  let P := p₁.withLpProdMap p p₂
  let Q := q₁.withLpProdMap p q₂
  let ep := p₁.rangeWithLpProdMapEquiv p p₂
  let eq_ := q₁.rangeWithLpProdMapEquiv p q₂
  let S₁ := rangeCompression p₁ q₁ T₁
  let S₂ := rangeCompression p₂ q₂ T₂
  let S := rangeCompression P Q (T₁.withLpProdMap p T₂)
  have intertwine :
      S.comp (ep : (p₁.range × p₂.range) →L[𝕜] P.range) =
        (eq_ : (q₁.range × q₂.range) →L[𝕜] Q.range).comp (S₁.prodMap S₂) := by
    refine ContinuousLinearMap.ext fun ⟨w₁, w₂⟩ ↦ Subtype.ext ?_
    apply (WithLp.prodContinuousLinearEquiv p 𝕜 F₁ F₂).injective
    ext <;> simp [S, S₁, S₂, P, Q, ep, eq_]
  have := h₁.finite_ker
  have := h₂.finite_ker
  have := h₁.finite_coker
  have := h₂.finite_coker
  rw [compressionIndex_def, compressionIndex_def, compressionIndex_def]
  calc
    S.index = (S.comp (ep : (p₁.range × p₂.range) →L[𝕜] P.range)).index :=
      (S.index_comp_equiv ep).symm
    _ = ((eq_ : (q₁.range × q₂.range) →L[𝕜] Q.range).comp (S₁.prodMap S₂)).index := by
      rw [intertwine]
    _ = (S₁.prodMap S₂).index := (S₁.prodMap S₂).index_equiv_comp eq_
    _ = S₁.index + S₂.index := S₁.index_prodMap S₂

end BlockSum

end ContinuousLinearMap
