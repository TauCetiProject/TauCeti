/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Continuous.Subrepresentation
public import TauCeti.RepresentationTheory.Continuous.Basic
public import TauCeti.Topology.Algebra.Module.Submodule
public import TauCeti.Topology.Algebra.Module.Quotient
public import Mathlib.Topology.Algebra.Module.Equiv.Prod
import TauCeti.Topology.Algebra.Module.ContinuousLinearMap.Precomp

/-!
# Products of continuous representations and intertwining maps

`ContRepresentation.prod` gives the componentwise action on the native topological product.
`ContIntertwiningMap.prodMap` is the corresponding product intertwining map. Its kernel and
quotient cokernel are continuously equivariantly equivalent to the products of the original defects.
These comparisons retain the actual actions and impose no finite-dimensionality condition.
Product continuity is provided both for strong continuity and for the topology of bounded
convergence on continuous linear maps, which agrees with the operator norm in normed spaces.

The constructions adapt the direct-sum proof in
[AtiyahSinger/Analysis/EquivariantIndexOperations.lean][source] from Lean-Atiyah-Singer,
using the native product and quotient equivalences.

[source]: https://github.com/alpha-squared-labs/Lean-Atiyah-Singer/blob/09fc7bab3f9ff606901bde4b5a5580470da63a70/AtiyahSinger/Analysis/EquivariantIndexOperations.lean
-/

public section

open ContRepresentation

variable {R G E₁ E₂ F₁ F₂ : Type*} [Ring R] [Monoid G]
  [AddCommGroup E₁] [TopologicalSpace E₁] [IsTopologicalAddGroup E₁] [Module R E₁]
  [AddCommGroup E₂] [TopologicalSpace E₂] [IsTopologicalAddGroup E₂] [Module R E₂]
  [AddCommGroup F₁] [TopologicalSpace F₁] [IsTopologicalAddGroup F₁] [Module R F₁]
  [AddCommGroup F₂] [TopologicalSpace F₂] [IsTopologicalAddGroup F₂] [Module R F₂]

namespace ContRepresentation

/-- The componentwise action of a monoid on a product of topological modules. -/
def prod (π : ContRepresentation R G E₁) (ρ : ContRepresentation R G E₂) :
    ContRepresentation R G (E₁ × E₂) :=
  .ofMonoidHom
    { toFun := fun g ↦ (π g).prodMap (ρ g)
      map_one' := by ext x <;> simp
      map_mul' := by intro g h; ext x <;> simp [map_mul] }

/-- The product action operator is the product of the component action operators. -/
@[simp]
theorem prod_apply (π : ContRepresentation R G E₁) (ρ : ContRepresentation R G E₂) (g : G) :
    π.prod ρ g = (π g).prodMap (ρ g) := (rfl)

/-- Forgetting continuity of a product action gives the product of the forgotten actions. -/
@[simp]
theorem toRepresentation_prod (π : ContRepresentation R G E₁)
    (ρ : ContRepresentation R G E₂) :
    (π.prod ρ).toRepresentation = π.toRepresentation.prod ρ.toRepresentation := by
  ext g v <;> rfl

variable [TopologicalSpace G] in
/-- The product of strongly continuous representations is strongly continuous. -/
theorem continuous_prod_apply {π : ContRepresentation R G E₁}
    {ρ : ContRepresentation R G E₂}
    (hπ : ∀ v, Continuous fun g ↦ π g v) (hρ : ∀ w, Continuous fun g ↦ ρ g w)
    (v : E₁ × E₂) : Continuous fun g ↦ π.prod ρ g v :=
  (hπ v.1).prodMk (hρ v.2)

variable [TopologicalSpace G] in
/-- Strong continuity of a product action implies strong continuity of its first factor. -/
theorem continuous_of_continuous_prod_apply_left {π : ContRepresentation R G E₁}
    {ρ : ContRepresentation R G E₂}
    (h : ∀ v, Continuous fun g ↦ π.prod ρ g v) (v : E₁) :
    Continuous fun g ↦ π g v := by
  simpa only [prod_apply, ContinuousLinearMap.coe_prodMap', Prod.map_apply] using
    (h (v, 0)).fst

variable [TopologicalSpace G] in
/-- Strong continuity of a product action implies strong continuity of its second factor. -/
theorem continuous_of_continuous_prod_apply_right {π : ContRepresentation R G E₁}
    {ρ : ContRepresentation R G E₂}
    (h : ∀ v, Continuous fun g ↦ π.prod ρ g v) (v : E₂) :
    Continuous fun g ↦ ρ g v := by
  simpa only [prod_apply, ContinuousLinearMap.coe_prodMap', Prod.map_apply] using
    (h (0, v)).snd

section OperatorContinuity

variable {𝕜 V W : Type*} [NormedField 𝕜] [TopologicalSpace G]
  [AddCommGroup V] [TopologicalSpace V] [IsTopologicalAddGroup V] [Module 𝕜 V]
  [AddCommGroup W] [TopologicalSpace W] [IsTopologicalAddGroup W] [Module 𝕜 W]

/-- Products preserve continuity into the continuous endomorphisms with the topology of
bounded convergence. In normed spaces this is operator-norm continuity. -/
theorem continuous_prod (π : ContRepresentation 𝕜 G V) (ρ : ContRepresentation 𝕜 G W)
    (hπ : Continuous π) (hρ : Continuous ρ) : Continuous (π.prod ρ) := by
  have hl := (ContinuousLinearMap.isInducing_postcomp (ContinuousLinearMap.inl 𝕜 V W)
    (isInducing_prodMkLeft (0 : W))).continuous.comp
      ((ContinuousLinearMap.continuous_precomp (ContinuousLinearMap.fst 𝕜 V W)).comp hπ)
  have hr := (ContinuousLinearMap.isInducing_postcomp (ContinuousLinearMap.inr 𝕜 V W)
    (isInducing_prodMkRight (0 : V))).continuous.comp
      ((ContinuousLinearMap.continuous_precomp (ContinuousLinearMap.snd 𝕜 V W)).comp hρ)
  exact (hl.add hr).congr fun g ↦ by ext v <;> simp

/-- Continuity of a product in the topology of bounded convergence implies continuity of
its first factor. -/
theorem continuous_of_continuous_prod_left {π : ContRepresentation 𝕜 G V}
    {ρ : ContRepresentation 𝕜 G W} (h : Continuous (π.prod ρ)) : Continuous π := by
  rw [(ContinuousLinearMap.isInducing_postcomp (ContinuousLinearMap.inl 𝕜 V W)
    (isInducing_prodMkLeft (0 : W))).continuous_iff]
  exact ((ContinuousLinearMap.continuous_precomp (ContinuousLinearMap.inl 𝕜 V W)).comp h).congr
    fun g ↦ by ext v <;> simp

/-- Continuity of a product in the topology of bounded convergence implies continuity of
its second factor. -/
theorem continuous_of_continuous_prod_right {π : ContRepresentation 𝕜 G V}
    {ρ : ContRepresentation 𝕜 G W} (h : Continuous (π.prod ρ)) : Continuous ρ := by
  rw [(ContinuousLinearMap.isInducing_postcomp (ContinuousLinearMap.inr 𝕜 V W)
    (isInducing_prodMkRight (0 : V))).continuous_iff]
  exact ((ContinuousLinearMap.continuous_precomp (ContinuousLinearMap.inr 𝕜 V W)).comp h).congr
    fun g ↦ by ext v <;> simp

/-- A product action is continuous for bounded convergence exactly when both factors are. -/
@[simp]
theorem continuous_prod_iff (π : ContRepresentation 𝕜 G V) (ρ : ContRepresentation 𝕜 G W) :
    Continuous (π.prod ρ) ↔ Continuous π ∧ Continuous ρ :=
  ⟨fun h ↦ ⟨continuous_of_continuous_prod_left h, continuous_of_continuous_prod_right h⟩,
    fun h ↦ π.continuous_prod ρ h.1 h.2⟩

end OperatorContinuity

namespace Equiv

/-- The product of two continuous equivariant equivalences, acting componentwise. -/
def prodCongr {π₁ : ContRepresentation R G E₁} {π₂ : ContRepresentation R G E₂}
    {ρ₁ : ContRepresentation R G F₁} {ρ₂ : ContRepresentation R G F₂}
    (e : π₁.Equiv ρ₁) (e' : π₂.Equiv ρ₂) : (π₁.prod π₂).Equiv (ρ₁.prod ρ₂) :=
  .mk (e.toContinuousLinearEquiv.prodCongr e'.toContinuousLinearEquiv) fun g ↦
    ContinuousLinearMap.ext fun v ↦ Prod.ext
      (e.toContIntertwiningMap.isIntertwining g v.1)
      (e'.toContIntertwiningMap.isIntertwining g v.2)

/-- A continuous product equivalence acts on each coordinate separately. -/
@[simp]
theorem prodCongr_apply {π₁ : ContRepresentation R G E₁} {π₂ : ContRepresentation R G E₂}
    {ρ₁ : ContRepresentation R G F₁} {ρ₂ : ContRepresentation R G F₂}
    (e : π₁.Equiv ρ₁) (e' : π₂.Equiv ρ₂) (v : E₁ × E₂) :
    e.prodCongr e' v = (e v.1, e' v.2) := (rfl)

/-- Inverting a continuous product equivalence inverts both factors. -/
@[simp]
theorem prodCongr_symm {π₁ : ContRepresentation R G E₁} {π₂ : ContRepresentation R G E₂}
    {ρ₁ : ContRepresentation R G F₁} {ρ₂ : ContRepresentation R G F₂}
    (e : π₁.Equiv ρ₁) (e' : π₂.Equiv ρ₂) :
    (e.prodCongr e').symm = e.symm.prodCongr e'.symm := by
  ext v <;> rfl

end Equiv

end ContRepresentation

namespace ContIntertwiningMap

variable {π₁ : ContRepresentation R G E₁} {π₂ : ContRepresentation R G E₂}
  {ρ₁ : ContRepresentation R G F₁} {ρ₂ : ContRepresentation R G F₂}

/-- The product intertwining map formed from two continuous intertwining maps. -/
def prodMap (T : π₁ →ⁱL ρ₁) (S : π₂ →ⁱL ρ₂) : π₁.prod π₂ →ⁱL ρ₁.prod ρ₂ where
  __ := T.toContinuousLinearMap.prodMap S.toContinuousLinearMap
  isIntertwining' g := by
    apply ContinuousLinearMap.ext
    intro v
    exact Prod.ext (T.isIntertwining g v.1) (S.isIntertwining g v.2)

/-- Forgetting equivariance of a product intertwining map gives the native product operator. -/
@[simp]
theorem toContinuousLinearMap_prodMap (T : π₁ →ⁱL ρ₁) (S : π₂ →ⁱL ρ₂) :
    (T.prodMap S).toContinuousLinearMap =
      T.toContinuousLinearMap.prodMap S.toContinuousLinearMap := (rfl)

/-- A product of intertwining maps acts componentwise. -/
@[simp]
theorem prodMap_apply (T : π₁ →ⁱL ρ₁) (S : π₂ →ⁱL ρ₂) (v : E₁ × E₂) :
    T.prodMap S v = (T v.1, S v.2) := by
  rw [← toContinuousLinearMap_apply, toContinuousLinearMap_prodMap]
  rfl

/-- The product of identity intertwining maps is the identity on the product action. -/
@[simp]
theorem prodMap_id : (id : π₁ →ⁱL π₁).prodMap (id : π₂ →ⁱL π₂) = id := by
  ext v <;> rfl

/-- The product of zero intertwining maps is zero. -/
@[simp]
theorem prodMap_zero : (0 : π₁ →ⁱL ρ₁).prodMap (0 : π₂ →ⁱL ρ₂) = 0 := by
  ext v <;> rfl

/-- Forming product intertwining maps commutes with composition. -/
theorem prodMap_comp {H₁ H₂ : Type*}
    [AddCommGroup H₁] [TopologicalSpace H₁] [IsTopologicalAddGroup H₁] [Module R H₁]
    [AddCommGroup H₂] [TopologicalSpace H₂] [IsTopologicalAddGroup H₂] [Module R H₂]
    {σ₁ : ContRepresentation R G H₁} {σ₂ : ContRepresentation R G H₂}
    (T : π₁ →ⁱL ρ₁) (S : π₂ →ⁱL ρ₂) (U : ρ₁ →ⁱL σ₁) (V : ρ₂ →ⁱL σ₂) :
    (U.comp T).prodMap (V.comp S) = (U.prodMap V).comp (T.prodMap S) := by
  ext v <;> rfl

/-- The kernel of a product intertwining map is continuously equivariantly equivalent to the
product of its kernels, via the identity on the underlying pair of vectors. -/
def kerProdEquiv (T : π₁ →ⁱL ρ₁) (S : π₂ →ⁱL ρ₂) :
    (T.prodMap S).kerRepresentation.Equiv (T.kerRepresentation.prod S.kerRepresentation) := by
  let e : (T.prodMap S).toContinuousLinearMap.ker ≃L[R]
      T.toContinuousLinearMap.ker × S.toContinuousLinearMap.ker :=
    (ContinuousLinearEquiv.ofEq _ _ (by
    rw [toContinuousLinearMap_prodMap, ContinuousLinearMap.coe_prodMap,
      LinearMap.ker_prodMap])).trans
    (Submodule.prodContEquiv T.toContinuousLinearMap.ker S.toContinuousLinearMap.ker)
  refine ContRepresentation.Equiv.mk e ?_
  intro g
  apply ContinuousLinearMap.ext
  intro v
  apply Prod.ext <;> apply Subtype.ext <;>
    simp [e, ContinuousLinearEquiv.ofEq]

/-- The first coordinate of the kernel comparison preserves the underlying vector. -/
@[simp]
theorem coe_kerProdEquiv_apply_fst (T : π₁ →ⁱL ρ₁) (S : π₂ →ⁱL ρ₂)
    (v : (T.prodMap S).toContinuousLinearMap.ker) :
    ((T.kerProdEquiv S v).1 : E₁) = (v : E₁ × E₂).1 := by
  simp [kerProdEquiv, ContinuousLinearEquiv.ofEq]

/-- The second coordinate of the kernel comparison preserves the underlying vector. -/
@[simp]
theorem coe_kerProdEquiv_apply_snd (T : π₁ →ⁱL ρ₁) (S : π₂ →ⁱL ρ₂)
    (v : (T.prodMap S).toContinuousLinearMap.ker) :
    ((T.kerProdEquiv S v).2 : E₂) = (v : E₁ × E₂).2 := by
  simp [kerProdEquiv, ContinuousLinearEquiv.ofEq]

/-- The inverse kernel comparison preserves the underlying pair of vectors. -/
@[simp]
theorem coe_kerProdEquiv_symm_apply (T : π₁ →ⁱL ρ₁) (S : π₂ →ⁱL ρ₂)
    (v : T.toContinuousLinearMap.ker × S.toContinuousLinearMap.ker) :
    ((T.kerProdEquiv S).symm v : E₁ × E₂) = ((v.1 : E₁), (v.2 : E₂)) := by
  apply Prod.ext
  · simpa only [ContRepresentation.Equiv.apply_symm_apply] using
      (coe_kerProdEquiv_apply_fst T S ((T.kerProdEquiv S).symm v)).symm
  · simpa only [ContRepresentation.Equiv.apply_symm_apply] using
      (coe_kerProdEquiv_apply_snd T S ((T.kerProdEquiv S).symm v)).symm

/-- The quotient cokernel of a product intertwining map is continuously equivariantly equivalent
to the product of its quotient cokernels. It sends a pair's class to the pair of its classes. -/
def cokerProdEquiv (T : π₁ →ⁱL ρ₁) (S : π₂ →ⁱL ρ₂) :
    (T.prodMap S).cokerRepresentation.Equiv (T.cokerRepresentation.prod S.cokerRepresentation) := by
  let e : ((F₁ × F₂) ⧸ (T.prodMap S).toContinuousLinearMap.range) ≃L[R]
      (F₁ ⧸ T.toContinuousLinearMap.range) × (F₂ ⧸ S.toContinuousLinearMap.range) :=
    ((ContinuousLinearEquiv.refl R (F₁ × F₂)).quotientEquiv _ _ (by
      simp [ContinuousLinearEquiv.refl, toContinuousLinearMap_prodMap,
        ContinuousLinearMap.coe_prodMap, LinearMap.range_prodMap])).trans
      (Submodule.quotientProdContEquiv T.toContinuousLinearMap.range S.toContinuousLinearMap.range)
  refine ContRepresentation.Equiv.mk e ?_
  intro g
  apply ContinuousLinearMap.ext
  intro v
  induction v using Submodule.Quotient.induction_on with
  | H v => simp [e]

/-- The cokernel product comparison sends a quotient representative to its component classes. -/
@[simp]
theorem cokerProdEquiv_apply_mk (T : π₁ →ⁱL ρ₁) (S : π₂ →ⁱL ρ₂) (v : F₁ × F₂) :
    T.cokerProdEquiv S (Submodule.Quotient.mk v) =
      (Submodule.Quotient.mk v.1, Submodule.Quotient.mk v.2) := by
  simp [cokerProdEquiv]

/-- The inverse cokernel comparison sends component classes to the class of their pair. -/
@[simp]
theorem cokerProdEquiv_symm_apply_mk (T : π₁ →ⁱL ρ₁) (S : π₂ →ⁱL ρ₂) (x : F₁) (y : F₂) :
    (T.cokerProdEquiv S).symm (Submodule.Quotient.mk x, Submodule.Quotient.mk y) =
      Submodule.Quotient.mk (x, y) := by
  simp [cokerProdEquiv]

end ContIntertwiningMap
