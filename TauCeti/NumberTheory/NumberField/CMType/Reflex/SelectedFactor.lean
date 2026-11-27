/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Etale.Field
public import TauCeti.NumberTheory.NumberField.CMType.Reflex.Basic
import TauCeti.RingTheory.Etale.Reduced
import TauCeti.RingTheory.Etale.Trace
import TauCeti.RingTheory.FiniteType.PointSeparation

/-!
# The tensor factor selected by a CM type

A CM type `Φ` on a finite étale rational algebra `E` selects a factor of `k ⊗[ℚ] E` whenever
the subfield `k ⊆ ℂ` contains its reflex field. The factor is the image of simultaneous
evaluation at the embeddings in `Φ` (`TauCeti.CMType.typeFactor`). The two evaluation
projections give the product decomposition `TauCeti.CMType.typeFactorProdEquiv`.

The construction uses `TauCeti.ratTensorProductAlgHomEquiv` to extend the embeddings,
`TauCeti.CMType.typeTrace_mem_reflexField` to descend the partial trace,
and `TauCeti.Algebra.Etale.exists_isIdempotentElem_algHom_apply_eq_indicator` to separate the two
sets of embeddings. Over the reflex field, the selected factor is the rational algebra in
which the reflex order is defined. See Yuan and Zhang, *On the averaged Colmez conjecture*,
§2.2, p. 546.
-/

public section

open scoped TensorProduct

namespace TauCeti.CMType

variable {E : Type*} [CommRing E] [Algebra ℚ E]

/-- Simultaneous evaluation of `k ⊗[ℚ] E` at the complex embeddings selected by `Φ`. -/
noncomputable def typeEvaluation (Φ : CMType E) (k : IntermediateField ℚ ℂ) :
    k ⊗[ℚ] E →ₐ[k] (Φ → ℂ) :=
  AlgHom.pi fun φ ↦ ratTensorProductAlgHomEquiv k E ℂ φ.val

/-- Compute a coordinate using the extended embedding. Keep arbitrary tensors in evaluation
form in simp, with `typeEvaluation_tmul` handling pure tensors. -/
theorem typeEvaluation_apply (Φ : CMType E) (k : IntermediateField ℚ ℂ)
    (x : k ⊗[ℚ] E) (φ : Φ) :
    Φ.typeEvaluation k x φ = ratTensorProductAlgHomEquiv k E ℂ φ.val x :=
  (rfl)

/-- The simp rule for evaluating a pure tensor at a selected embedding. -/
@[simp]
theorem typeEvaluation_tmul (Φ : CMType E) (k : IntermediateField ℚ ℂ)
    (r : k) (a : E) (φ : Φ) :
    Φ.typeEvaluation k (r ⊗ₜ a) φ = (r : ℂ) * (φ : E →+* ℂ) a := by
  simp only [typeEvaluation_apply, ratTensorProductAlgHomEquiv_tmul,
    IntermediateField.algebraMap_apply]

/-- The algebra selected by `Φ`, realized as the image of simultaneous evaluation. The map
onto it is `(Φ.typeEvaluation k).rangeRestrict`. -/
noncomputable abbrev typeFactor (Φ : CMType E) (k : IntermediateField ℚ ℂ) :
    Subalgebra k (Φ → ℂ) :=
  (Φ.typeEvaluation k).range

section FiniteEmbeddings

variable [Finite (E →+* ℂ)]

/-- The partial trace on the base-changed algebra takes values in every field containing the
reflex field. Here the embeddings of the tensor product are indexed by the embeddings of
`E` via the tensor product universal property. -/
theorem finsum_ratTensorProductAlgHomEquiv_image_mem_range (Φ : CMType E)
    {k : IntermediateField ℚ ℂ} (hk : Φ.reflexField ≤ k) (x : k ⊗[ℚ] E) :
    ∑ᶠ ψ ∈ ratTensorProductAlgHomEquiv k E ℂ '' (Φ : Set (E →+* ℂ)), ψ x
      ∈ Set.range (algebraMap k ℂ) := by
  rw [finsum_mem_image (ratTensorProductAlgHomEquiv k E ℂ).injective.injOn]
  induction x using TensorProduct.inductionOn with
  | tmul r a =>
    refine ⟨r * ⟨Φ.typeTrace a, hk (Φ.typeTrace_mem_reflexField a)⟩, ?_⟩
    simp only [ratTensorProductAlgHomEquiv_tmul, map_mul, typeTrace_apply,
      IntermediateField.algebraMap_apply]
    exact mul_finsum_mem' _ _ (Set.toFinite _)
  | add x y hx hy =>
    obtain ⟨r, hr⟩ := hx
    obtain ⟨s, hs⟩ := hy
    refine ⟨r + s, ?_⟩
    simp only [map_add, hr, hs, finsum_mem_add_distrib (Set.toFinite _)]

end FiniteEmbeddings

/-- The pair of range projections selected by a CM type and its complement. -/
noncomputable def typeFactorProd (Φ : CMType E) (k : IntermediateField ℚ ℂ) :
    k ⊗[ℚ] E →ₐ[k] Φ.typeFactor k × (star Φ).typeFactor k :=
  (Φ.typeEvaluation k).rangeRestrict.prod ((star Φ).typeEvaluation k).rangeRestrict

/-- Compute the joint projection using the canonical range projections. -/
@[simp]
theorem typeFactorProd_apply (Φ : CMType E) (k : IntermediateField ℚ ℂ) (x : k ⊗[ℚ] E) :
    Φ.typeFactorProd k x =
      ((Φ.typeEvaluation k).rangeRestrict x, ((star Φ).typeEvaluation k).rangeRestrict x) :=
  (rfl)

/-- The two types exhaust the complex embeddings. Their evaluation projections jointly
separate points of a reduced tensor algebra of finite type. -/
theorem typeFactorProd_injective (Φ : CMType E) (k : IntermediateField ℚ ℂ)
    [Algebra.FiniteType k (k ⊗[ℚ] E)] [IsReduced (k ⊗[ℚ] E)] :
    Function.Injective (Φ.typeFactorProd k) := by
  classical
  intro x y h
  refine eq_of_forall_algHom_apply_eq (k := k) (K := ℂ) fun ψ ↦ ?_
  obtain ⟨φ, rfl⟩ := (ratTensorProductAlgHomEquiv k E ℂ).surjective ψ
  by_cases hφ : φ ∈ Φ
  · have hxy : Φ.typeEvaluation k x ⟨φ, hφ⟩ = Φ.typeEvaluation k y ⟨φ, hφ⟩ :=
      congrArg (fun p : Φ.typeFactor k × (star Φ).typeFactor k ↦ p.1.val ⟨φ, hφ⟩) h
    simpa only [typeEvaluation_apply] using hxy
  · have hφ' : φ ∈ star Φ := mem_star.mpr hφ
    have hxy : (star Φ).typeEvaluation k x ⟨φ, hφ'⟩ = (star Φ).typeEvaluation k y ⟨φ, hφ'⟩ :=
      congrArg (fun p : Φ.typeFactor k × (star Φ).typeFactor k ↦ p.2.val ⟨φ, hφ'⟩) h
    simpa only [typeEvaluation_apply] using hxy

section Finite

variable [Module.Finite ℚ E]

/-- The evaluation image of a finite rational algebra is finite étale over `k`. -/
instance etale_typeFactor (Φ : CMType E) (k : IntermediateField ℚ ℂ) :
    Algebra.Etale k (Φ.typeFactor k) := by
  refine algebraEtale_iff_finite_and_isReduced.mpr ⟨?_, ?_⟩
  · exact Module.Finite.of_surjective (Φ.typeEvaluation k).rangeRestrict.toLinearMap
      (Φ.typeEvaluation k).rangeRestrict_surjective
  · exact isReduced_of_injective (Φ.typeFactor k).val Subtype.val_injective

variable [IsReduced E]

/-- The two evaluation projections together are bijective over any field containing the
reflex field. -/
theorem typeFactorProd_bijective (Φ : CMType E)
    {k : IntermediateField ℚ ℂ} (hk : Φ.reflexField ≤ k) :
    Function.Bijective (Φ.typeFactorProd k) := by
  classical
  have : Algebra.Etale ℚ E :=
    algebraEtale_iff_finite_and_isReduced.mpr ⟨inferInstance, inferInstance⟩
  have : IsReduced (k ⊗[ℚ] E) := Algebra.FormallyUnramified.isReduced_of_field k (k ⊗[ℚ] E)
  refine ⟨Φ.typeFactorProd_injective k, ?_⟩
  rintro ⟨u, v⟩
  obtain ⟨x, rfl⟩ := (Φ.typeEvaluation k).rangeRestrict_surjective u
  obtain ⟨y, rfl⟩ := ((star Φ).typeEvaluation k).rangeRestrict_surjective v
  -- The descended idempotent is one on the selected embeddings and zero on the others.
  obtain ⟨c, -, hc⟩ := TauCeti.Algebra.Etale.exists_isIdempotentElem_algHom_apply_eq_indicator
    (K := k) (A := k ⊗[ℚ] E) (Ω := ℂ)
    (ratTensorProductAlgHomEquiv k E ℂ '' (Φ : Set (E →+* ℂ)))
    (Φ.finsum_ratTensorProductAlgHomEquiv_image_mem_range hk)
  have hmem (φ : E →+* ℂ) :
      ratTensorProductAlgHomEquiv k E ℂ φ ∈ ratTensorProductAlgHomEquiv k E ℂ '' (Φ : Set _) ↔
        φ ∈ Φ :=
    Set.ext_iff.mp (Set.preimage_image_eq _ (ratTensorProductAlgHomEquiv k E ℂ).injective) φ
  have h₁ : Φ.typeEvaluation k c = 1 := funext fun φ ↦ by
    rw [typeEvaluation_apply, hc (ratTensorProductAlgHomEquiv k E ℂ φ.val)]
    exact Set.indicator_of_mem ((hmem _).mpr φ.property) _
  have h₀ : (star Φ).typeEvaluation k c = 0 := funext fun φ ↦ by
    rw [typeEvaluation_apply, hc (ratTensorProductAlgHomEquiv k E ℂ φ.val)]
    exact Set.indicator_of_notMem (fun h ↦ mem_star.mp φ.property ((hmem _).mp h)) _
  refine ⟨c * x + (1 - c) * y, Prod.ext (Subtype.ext ?_) (Subtype.ext ?_)⟩
  · simp [h₁]
  · simp [h₀]

/-- The decomposition of the tensor product into the factors selected by `Φ` and its
complementary CM type. -/
noncomputable def typeFactorProdEquiv (Φ : CMType E)
    {k : IntermediateField ℚ ℂ} (hk : Φ.reflexField ≤ k) :
    k ⊗[ℚ] E ≃ₐ[k] Φ.typeFactor k × (star Φ).typeFactor k :=
  AlgEquiv.ofBijective (Φ.typeFactorProd k) (Φ.typeFactorProd_bijective hk)

/-- Compute the two components of the splitting using the canonical range projections. -/
@[simp]
theorem typeFactorProdEquiv_apply (Φ : CMType E)
    {k : IntermediateField ℚ ℂ} (hk : Φ.reflexField ≤ k) (x : k ⊗[ℚ] E) :
    Φ.typeFactorProdEquiv hk x =
      ((Φ.typeEvaluation k).rangeRestrict x, ((star Φ).typeEvaluation k).rangeRestrict x) :=
  typeFactorProd_apply Φ k x

end Finite

end TauCeti.CMType
