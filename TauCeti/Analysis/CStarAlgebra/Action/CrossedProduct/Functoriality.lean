/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.CStarAlgebra.Action.CrossedProduct.Full
public import TauCeti.Analysis.CStarAlgebra.Action.Covariant.Comap
public import TauCeti.Analysis.CStarAlgebra.Action.Equivariant

/-!
# Functoriality of full crossed products

An equivariant nonunital coefficient homomorphism induces a nonunital star-algebra
homomorphism of full crossed products. On compactly supported coefficients it acts pointwise.
The induced maps preserve identities and composition, and pulling back a covariant pair
commutes with its extended integrated form; in particular, an extended integrated form vanishes
on the range of the induced map precisely when the coefficient representation vanishes on the
range of the coefficient map.

We use the full-seminorm estimate `Hom.fullSeminorm_convolutionMap_le` to extend the
compact-support map by continuity. Both coefficient algebras lie in the same universe, so the
source and target full seminorms use the same indexing universe for covariant representations.
No nondegeneracy, unitality, separability or global σ-finiteness is assumed.

## Main definitions and results

* `TauCeti.CStarAction.Hom.fullCrossedProductMap`: the induced homomorphism.
* `TauCeti.CStarAction.Hom.fullCrossedProductMap_of`: its compact-support formula.
* `TauCeti.CStarAction.Hom.fullCrossedProductMap_id` and
  `TauCeti.CStarAction.Hom.fullCrossedProductMap_comp`: the functor laws.
* `TauCeti.CStarAction.CovariantRepresentation.integratedFull_fullCrossedProductMap_apply`:
  compatibility with integration of covariant pairs.
* `StarAlgEquiv.fullCrossedProductEquiv`, `TauCeti.CStarAction.Hom.fullCrossedProductEquiv`, and
  `TauCeti.CStarAction.Hom.bijective_fullCrossedProductMap`: isometric `⋆`-isomorphisms of full
  crossed products induced by equivariant coefficient `⋆`-isomorphisms.

## References

Dana Williams, *Crossed Products of C*-Algebras*, Chapter 2, for functoriality of full
crossed products. The constructions extend Tau Ceti's `Hom.convolutionMap` and use
`CovariantRepresentation.comap` for the universal-seminorm estimate.
-/

public section

noncomputable section

open MeasureTheory UniformSpace

namespace TauCeti.CStarAction

universe u v

variable {G : Type u} {A B C : Type v} [Group G] [TopologicalSpace G]
  [IsTopologicalGroup G] [LocallyCompactSpace G] [MeasurableSpace G] [BorelSpace G]
  [NonUnitalCStarAlgebra A] [NonUnitalCStarAlgebra B] [NonUnitalCStarAlgebra C]
  {α : CStarAction G A} {β : CStarAction G B} {γ : CStarAction G C}
  (μ : Measure G) [μ.IsHaarMeasure]

namespace Hom

open FullCrossedProduct

variable (φ : Hom α β)

/-- The nonunital star-algebra homomorphism of full crossed products induced by an equivariant
coefficient homomorphism. Its value on compact-support coefficients is given by
`fullCrossedProductMap_of`. -/
def fullCrossedProductMap : FullCrossedProduct α μ →⋆ₙₐ[ℂ] FullCrossedProduct β μ :=
  lift ((of β μ).comp (φ.convolutionMap μ))
    (fun f => by simpa using φ.fullSeminorm_convolutionMap_le μ f)

/-- The induced full crossed-product map acts pointwise on compact-support coefficients. -/
@[simp]
theorem fullCrossedProductMap_of (f : ConvolutionAlgebra α μ) :
    φ.fullCrossedProductMap μ (of α μ f) = of β μ (φ.convolutionMap μ f) :=
  lift_of _ _ f

/-- The compact-support inclusion is natural under equivariant coefficient maps. -/
@[simp]
theorem fullCrossedProductMap_comp_of :
    (φ.fullCrossedProductMap μ).comp (of α μ) = (of β μ).comp (φ.convolutionMap μ) :=
  NonUnitalStarAlgHom.ext (φ.fullCrossedProductMap_of μ)

/-- The identity coefficient map induces the identity on the full crossed product. -/
@[simp]
theorem fullCrossedProductMap_id :
    (Hom.id α).fullCrossedProductMap μ = NonUnitalStarAlgHom.id ℂ (FullCrossedProduct α μ) := by
  apply FullCrossedProduct.starAlgHom_ext
  ext f
  simp

/-- Induced full crossed-product maps preserve composition. -/
@[simp]
theorem fullCrossedProductMap_comp (ψ : Hom β γ) :
    (ψ.comp φ).fullCrossedProductMap μ =
      (ψ.fullCrossedProductMap μ).comp (φ.fullCrossedProductMap μ) := by
  apply FullCrossedProduct.starAlgHom_ext
  ext f
  simp

open scoped CStarAlgebra in
/-- A closed nonunital star subalgebra of `FullCrossedProduct β μ` contains the range of
`φ.fullCrossedProductMap μ` precisely when it contains the image of every compactly supported
element under `φ.convolutionMap μ`. -/
theorem range_fullCrossedProductMap_le_iff
    {J : NonUnitalStarSubalgebra ℂ (FullCrossedProduct β μ)}
    (hJ : IsClosed (J : Set (FullCrossedProduct β μ))) :
    (φ.fullCrossedProductMap μ).range ≤ J ↔
      ∀ f : ConvolutionAlgebra α μ, of β μ (φ.convolutionMap μ f) ∈ J := by
  refine ⟨fun h f => h ((φ.fullCrossedProductMap μ).mem_range.2
      ⟨of α μ f, φ.fullCrossedProductMap_of μ f⟩),
    fun h y hy => ?_⟩
  obtain ⟨x, rfl⟩ := (φ.fullCrossedProductMap μ).mem_range.1 hy
  clear hy
  induction x using FullCrossedProduct.induction_on with
  | hp => exact hJ.preimage (map_continuous (φ.fullCrossedProductMap μ))
  | ih f => simpa only [Set.mem_preimage, SetLike.mem_coe, fullCrossedProductMap_of] using h f

/-- The range of `φ.fullCrossedProductMap μ` is contained in the topological closure of the
compactly supported elements coming from `φ.convolutionMap μ`. -/
theorem range_fullCrossedProductMap_le_topologicalClosure :
    (φ.fullCrossedProductMap μ).range ≤
      ((of β μ).comp (φ.convolutionMap μ)).range.topologicalClosure :=
  (φ.range_fullCrossedProductMap_le_iff μ
    ((of β μ).comp (φ.convolutionMap μ)).range.isClosed_topologicalClosure).2 fun f =>
    NonUnitalStarSubalgebra.le_topologicalClosure _
      (((of β μ).comp (φ.convolutionMap μ)).mem_range.2 ⟨f, rfl⟩)

end Hom

namespace CovariantRepresentation

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H] (P : CovariantRepresentation β H) (φ : Hom α β)

/-- Pulling back a covariant pair commutes with integrating it on the full crossed product. -/
@[simp]
theorem integratedFull_comp_fullCrossedProductMap :
    (P.integratedFull μ).comp (φ.fullCrossedProductMap μ) = (P.comap φ).integratedFull μ := by
  apply FullCrossedProduct.starAlgHom_ext
  apply NonUnitalStarAlgHom.ext
  intro f
  simpa only [NonUnitalStarAlgHom.comp_apply, Hom.fullCrossedProductMap_of,
    integratedFull_of, integratedStarAlgHom_apply] using
    (P.integratedOperator_comap φ μ f).symm

/-- The value of an integrated form after applying the induced full crossed-product map is
the integrated form of the pulled-back pair. -/
@[simp]
theorem integratedFull_fullCrossedProductMap_apply (x : FullCrossedProduct α μ) :
    P.integratedFull μ (φ.fullCrossedProductMap μ x) = (P.comap φ).integratedFull μ x :=
  DFunLike.congr_fun (P.integratedFull_comp_fullCrossedProductMap μ φ) x

/-- An extended integrated form vanishes after `φ.fullCrossedProductMap μ` precisely when the
coefficient representation vanishes on the range of `φ`. -/
theorem integratedFull_comp_fullCrossedProductMap_eq_zero_iff :
    (P.integratedFull μ).comp (φ.fullCrossedProductMap μ) = 0 ↔
      ∀ a, P.coefficient (φ a) = 0 := by
  rw [P.integratedFull_comp_fullCrossedProductMap μ φ, integratedFull_eq_zero_iff,
    NonUnitalStarAlgHom.ext_iff]
  simp only [comap_coefficient, NonUnitalStarAlgHom.comp_apply, Hom.coe_toNonUnitalStarAlgHom,
    NonUnitalStarAlgHom.zero_apply]

/-- An extended integrated form vanishes on the range of `φ.fullCrossedProductMap μ` precisely
when the coefficient representation vanishes on the range of `φ`. -/
theorem forall_mem_range_fullCrossedProductMap_integratedFull_eq_zero_iff :
    (∀ y ∈ (φ.fullCrossedProductMap μ).range, P.integratedFull μ y = 0) ↔
      ∀ a, P.coefficient (φ a) = 0 := by
  rw [← P.integratedFull_comp_fullCrossedProductMap_eq_zero_iff μ φ, NonUnitalStarAlgHom.ext_iff]
  simp only [NonUnitalStarAlgHom.mem_range, forall_exists_index, forall_apply_eq_imp_iff,
    NonUnitalStarAlgHom.comp_apply, NonUnitalStarAlgHom.zero_apply]

end CovariantRepresentation

end TauCeti.CStarAction

namespace StarAlgEquiv

open TauCeti TauCeti.CStarAction TauCeti.CStarAction.FullCrossedProduct

universe u v

variable {G : Type u} {A B C : Type v} [Group G] [TopologicalSpace G]
  [IsTopologicalGroup G] [LocallyCompactSpace G] [MeasurableSpace G] [BorelSpace G]
  [NonUnitalCStarAlgebra A] [NonUnitalCStarAlgebra B] [NonUnitalCStarAlgebra C]
  {α : CStarAction G A} {β : CStarAction G B} {γ : CStarAction G C}

/-- An equivariant `⋆`-isomorphism of coefficient C⋆-algebras induces an isometric `⋆`-isomorphism
of full crossed products. -/
def fullCrossedProductEquiv (e : A ≃⋆ₐ[ℂ] B) (he : α.IsEquivariant β e.toNonUnitalStarAlgHom)
    (μ : Measure G) [μ.IsHaarMeasure] :
    FullCrossedProduct α μ ≃⋆ₐ[ℂ] FullCrossedProduct β μ :=
  let φ : Hom α β := ⟨e.toNonUnitalStarAlgHom, he.apply⟩
  let ψ : Hom β α := ⟨e.symm.toNonUnitalStarAlgHom, (e.isEquivariant_symm he).apply⟩
  StarAlgEquiv.ofNonUnitalStarAlgHom (φ.fullCrossedProductMap μ) (ψ.fullCrossedProductMap μ)
    (by
      rw [← Hom.fullCrossedProductMap_comp, ← Hom.fullCrossedProductMap_id]
      congr 1
      ext a
      simp [φ, ψ])
    (by
      rw [← Hom.fullCrossedProductMap_comp, ← Hom.fullCrossedProductMap_id]
      congr 1
      ext b
      simp [φ, ψ])

@[simp]
theorem toNonUnitalStarAlgHom_fullCrossedProductEquiv (e : A ≃⋆ₐ[ℂ] B)
    (he : α.IsEquivariant β e.toNonUnitalStarAlgHom) (μ : Measure G) [μ.IsHaarMeasure] :
    (e.fullCrossedProductEquiv he μ).toNonUnitalStarAlgHom =
      (⟨e.toNonUnitalStarAlgHom, he.apply⟩ : Hom α β).fullCrossedProductMap μ :=
  (rfl)

theorem fullCrossedProductEquiv_apply (e : A ≃⋆ₐ[ℂ] B)
    (he : α.IsEquivariant β e.toNonUnitalStarAlgHom) (μ : Measure G) [μ.IsHaarMeasure]
    (x : FullCrossedProduct α μ) :
    e.fullCrossedProductEquiv he μ x =
      (⟨e.toNonUnitalStarAlgHom, he.apply⟩ : Hom α β).fullCrossedProductMap μ x :=
  (rfl)

@[simp]
theorem fullCrossedProductEquiv_of (e : A ≃⋆ₐ[ℂ] B)
    (he : α.IsEquivariant β e.toNonUnitalStarAlgHom) (μ : Measure G) [μ.IsHaarMeasure]
    (f : ConvolutionAlgebra α μ) :
    e.fullCrossedProductEquiv he μ (of α μ f) =
      of β μ ((⟨e.toNonUnitalStarAlgHom, he.apply⟩ : Hom α β).convolutionMap μ f) :=
  Hom.fullCrossedProductMap_of μ _ f

@[simp]
theorem fullCrossedProductEquiv_symm (e : A ≃⋆ₐ[ℂ] B)
    (he : α.IsEquivariant β e.toNonUnitalStarAlgHom) (μ : Measure G) [μ.IsHaarMeasure] :
    (e.fullCrossedProductEquiv he μ).symm =
      e.symm.fullCrossedProductEquiv (e.isEquivariant_symm he) μ :=
  (rfl)

@[simp]
theorem fullCrossedProductEquiv_refl
    (he : α.IsEquivariant α (StarAlgEquiv.refl ℂ A).toNonUnitalStarAlgHom)
    (μ : Measure G) [μ.IsHaarMeasure] :
    (StarAlgEquiv.refl ℂ A).fullCrossedProductEquiv he μ =
      StarAlgEquiv.refl ℂ (FullCrossedProduct α μ) := by
  have hid : (⟨(StarAlgEquiv.refl ℂ A).toNonUnitalStarAlgHom, he.apply⟩ : Hom α α) = Hom.id α := by
    ext a
    simp
  ext x
  rw [fullCrossedProductEquiv_apply, hid, Hom.fullCrossedProductMap_id]
  rfl

theorem fullCrossedProductEquiv_trans (e₁ : A ≃⋆ₐ[ℂ] B) (e₂ : B ≃⋆ₐ[ℂ] C)
    (he₁ : α.IsEquivariant β e₁.toNonUnitalStarAlgHom)
    (he₂ : β.IsEquivariant γ e₂.toNonUnitalStarAlgHom)
    (he₁₂ : α.IsEquivariant γ (e₁.trans e₂).toNonUnitalStarAlgHom)
    (μ : Measure G) [μ.IsHaarMeasure] :
    (e₁.trans e₂).fullCrossedProductEquiv he₁₂ μ =
      (e₁.fullCrossedProductEquiv he₁ μ).trans (e₂.fullCrossedProductEquiv he₂ μ) := by
  let φ₁ : Hom α β := ⟨e₁.toNonUnitalStarAlgHom, he₁.apply⟩
  let φ₂ : Hom β γ := ⟨e₂.toNonUnitalStarAlgHom, he₂.apply⟩
  have hcomp : (⟨(e₁.trans e₂).toNonUnitalStarAlgHom, he₁₂.apply⟩ : Hom α γ) =
      φ₂.comp φ₁ := by
    ext a
    rw [← Hom.coe_toNonUnitalStarAlgHom, Hom.comp_apply]
    rfl
  ext x
  rw [fullCrossedProductEquiv_apply, hcomp, Hom.fullCrossedProductMap_comp]
  rfl

end StarAlgEquiv

namespace TauCeti.CStarAction.Hom

universe u v

variable {G : Type u} {A B : Type v} [Group G] [TopologicalSpace G]
  [IsTopologicalGroup G] [LocallyCompactSpace G] [MeasurableSpace G] [BorelSpace G]
  [NonUnitalCStarAlgebra A] [NonUnitalCStarAlgebra B]
  {α : CStarAction G A} {β : CStarAction G B}
  (μ : Measure G) [μ.IsHaarMeasure] (φ : Hom α β)

/-- A bijective equivariant coefficient homomorphism induces an isometric `⋆`-isomorphism of full
crossed products, without assuming `T2Space G`. -/
def fullCrossedProductEquiv (hφ : Function.Bijective φ) :
    FullCrossedProduct α μ ≃⋆ₐ[ℂ] FullCrossedProduct β μ :=
  (StarAlgEquiv.ofBijective φ.toNonUnitalStarAlgHom hφ).fullCrossedProductEquiv
    (CStarAction.isEquivariant_iff.mpr fun g a => φ.map_action g a) μ

@[simp]
theorem toNonUnitalStarAlgHom_fullCrossedProductEquiv (hφ : Function.Bijective φ) :
    (φ.fullCrossedProductEquiv μ hφ).toNonUnitalStarAlgHom = φ.fullCrossedProductMap μ := by
  rw [fullCrossedProductEquiv, StarAlgEquiv.toNonUnitalStarAlgHom_fullCrossedProductEquiv]
  congr 1

@[simp]
theorem fullCrossedProductEquiv_apply (hφ : Function.Bijective φ) (x : FullCrossedProduct α μ) :
    φ.fullCrossedProductEquiv μ hφ x = φ.fullCrossedProductMap μ x :=
  DFunLike.congr_fun (φ.toNonUnitalStarAlgHom_fullCrossedProductEquiv μ hφ) x

/-- A bijective equivariant coefficient homomorphism induces a bijective homomorphism of full
crossed products. -/
theorem bijective_fullCrossedProductMap (hφ : Function.Bijective φ) :
    Function.Bijective (φ.fullCrossedProductMap μ) := by
  have hfn : ⇑(φ.fullCrossedProductMap μ) = ⇑(φ.fullCrossedProductEquiv μ hφ) :=
    funext fun x => (φ.fullCrossedProductEquiv_apply μ hφ x).symm
  rw [hfn]
  exact (φ.fullCrossedProductEquiv μ hφ).bijective

end TauCeti.CStarAction.Hom
