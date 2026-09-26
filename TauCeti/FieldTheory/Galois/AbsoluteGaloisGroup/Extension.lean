/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.FieldTheory.Galois.AbsoluteGaloisGroup.Basic
public import TauCeti.FieldTheory.IsSepClosed

/-!
# The absolute Galois group of an embedded extension as a fixing subgroup

Let `L/K` be a field extension and `σ : L →ₐ[K] Kˢ` a `K`-embedding of `L` into a separable
closure `Kˢ` of `K`. Through `σ`, the field `Kˢ` is a separable closure of `L` as well, so a chosen
identification `Lˢ ≃ Kˢ` over `L` carries the automorphisms of `Lˢ` over `L` onto the automorphisms
of `Kˢ` fixing `σ(L)` pointwise. This file constructs that identification and proves that it is an
isomorphism of **topological** groups

```text
G_L ≃ₜ* σ.fieldRange.fixingSubgroup ≤ G_K = AbsoluteGaloisGroup K
```

for the Krull topologies, for any extension `L/K` embedded in `Kˢ`; no finiteness is assumed.
Separability of `L/K` is a consequence of the existence of `σ` and is not assumed either.

The embedding is genuine data. Without one there is no homomorphism `G_L → G_K` induced by the
extension `L/K`, hence no realization of `G_L` as a subgroup of `G_K`, and two embeddings cut out
conjugate subgroups. When `L/K` is finite the fixing subgroup is open, and
`TauCeti.FieldTheory.Galois.AbsoluteGaloisGroup.FiniteExtension` packages it as the open subgroup
`galoisSubgroup K L σ` with the isomorphism read there, since the open subgroup is the object the
cohomological operations along `L/K` are indexed by.

## Main definitions

* `TauCeti.separableClosureRingEquiv K L σ`: a chosen ring isomorphism `Lˢ ≃+* Kˢ` extending `σ`.
* `TauCeti.absoluteGaloisGroupEquivFixingSubgroup K L σ`: the isomorphism of topological groups
  `G_L ≃ₜ* σ.fieldRange.fixingSubgroup` obtained by transport along that identification.

## Main results

* `TauCeti.absoluteGaloisGroupEquivFixingSubgroup_apply`: the isomorphism conjugates by
  `separableClosureRingEquiv K L σ`, so it intertwines the actions of `G_L` on `Lˢ` and of `G_K`
  on `Kˢ`.

## References

* J. Neukirch, A. Schmidt, K. Wingberg, *Cohomology of Number Fields*, 2nd ed., Ch. VI §1 for the
  absolute Galois group at the separable closure.
-/

public section

noncomputable section

namespace TauCeti

open IntermediateField

variable (K : Type*) [Field K] (L : Type*) [Field L] [Algebra K L]
  (σ : L →ₐ[K] SeparableClosure K)

/-! ### The identification of separable closures -/

/-- **A chosen identification `Lˢ ≃+* Kˢ` extending `σ`.** Any two separable closures of `L` are
`L`-isomorphic, and `Kˢ` is one of them through `σ`; the `L`-linearity of the chosen isomorphism is
recorded by `separableClosureRingEquiv_algebraMap`. It is a ring isomorphism rather than an
`L`-algebra isomorphism because the `L`-algebra structure of `Kˢ` is not an instance. -/
def separableClosureRingEquiv : SeparableClosure L ≃+* SeparableClosure K :=
  letI : Algebra L (SeparableClosure K) := σ.toRingHom.toAlgebra
  haveI : IsScalarTower K L (SeparableClosure K) :=
    IsScalarTower.of_algebraMap_eq fun x ↦ (σ.commutes x).symm
  haveI : IsSepClosure L (SeparableClosure K) := isSepClosure_tower_top K L _
  (IsSepClosure.equiv L (SeparableClosure L) (SeparableClosure K)).toRingEquiv

/-- The identification of separable closures restricts to `σ` on `L`. -/
@[simp]
theorem separableClosureRingEquiv_algebraMap (x : L) :
    separableClosureRingEquiv K L σ (algebraMap L (SeparableClosure L) x) = σ x :=
  letI : Algebra L (SeparableClosure K) := σ.toRingHom.toAlgebra
  haveI : IsScalarTower K L (SeparableClosure K) :=
    IsScalarTower.of_algebraMap_eq fun x ↦ (σ.commutes x).symm
  haveI : IsSepClosure L (SeparableClosure K) := isSepClosure_tower_top K L _
  (IsSepClosure.equiv L (SeparableClosure L) (SeparableClosure K)).commutes x

/-- The inverse identification sends `σ x` back to `x`. -/
@[simp]
theorem separableClosureRingEquiv_symm_apply_eq_algebraMap (x : L) :
    (separableClosureRingEquiv K L σ).symm (σ x) = algebraMap L (SeparableClosure L) x := by
  rw [← separableClosureRingEquiv_algebraMap K L σ x, RingEquiv.symm_apply_apply]

/-- The identification of separable closures fixes the image of `K`. -/
@[simp]
theorem separableClosureRingEquiv_algebraMap_base (c : K) :
    separableClosureRingEquiv K L σ (algebraMap K (SeparableClosure L) c) =
      algebraMap K (SeparableClosure K) c := by
  rw [IsScalarTower.algebraMap_apply K L (SeparableClosure L), separableClosureRingEquiv_algebraMap,
    σ.commutes]

/-- The inverse identification fixes the image of `K`. -/
@[simp]
theorem separableClosureRingEquiv_symm_algebraMap_base (c : K) :
    (separableClosureRingEquiv K L σ).symm (algebraMap K (SeparableClosure K) c) =
      algebraMap K (SeparableClosure L) c := by
  rw [← separableClosureRingEquiv_algebraMap_base K L σ c, RingEquiv.symm_apply_apply]

/-! ### The isomorphism with the fixing subgroup of the image of `L` -/

/-- The underlying group isomorphism of `absoluteGaloisGroupEquivFixingSubgroup`: conjugate an
automorphism of `Lˢ` by the identification `separableClosureRingEquiv K L σ`.

It is named so that the structure field and the continuity proofs below refer to one and the same
term rather than to separately built copies identified by definitional unfolding. -/
private def fixingSubgroupMulEquiv : AbsoluteGaloisGroup L ≃* ↥σ.fieldRange.fixingSubgroup where
  toFun g :=
    ⟨AlgEquiv.ofRingEquiv (R := K)
      (f := (separableClosureRingEquiv K L σ).symm.trans
        (g.toRingEquiv.trans (separableClosureRingEquiv K L σ)))
      fun c ↦ by
        simp only [RingEquiv.trans_apply, AlgEquiv.coe_ringEquiv,
          separableClosureRingEquiv_symm_algebraMap_base]
        rw [IsScalarTower.algebraMap_apply K L (SeparableClosure L), AlgEquiv.commutes,
          ← IsScalarTower.algebraMap_apply, separableClosureRingEquiv_algebraMap_base], by
        rw [IntermediateField.mem_fixingSubgroup_iff]
        rintro _ ⟨x, rfl⟩
        simp⟩
  invFun h :=
    AlgEquiv.ofRingEquiv (R := L)
      (f := (separableClosureRingEquiv K L σ).trans
        ((h : AbsoluteGaloisGroup K).toRingEquiv.trans (separableClosureRingEquiv K L σ).symm))
      fun x ↦ by
        have hx : (h : AbsoluteGaloisGroup K) (σ x) = σ x :=
          (IntermediateField.mem_fixingSubgroup_iff _ _).mp h.2 (σ x) ⟨x, rfl⟩
        simp [hx]
  left_inv g := by ext x; simp
  right_inv h := by ext x; simp
  map_mul' g g' := by ext x; simp

private theorem fixingSubgroupMulEquiv_apply (g : AbsoluteGaloisGroup L) (y : SeparableClosure K) :
    (fixingSubgroupMulEquiv K L σ g : AbsoluteGaloisGroup K) y =
      separableClosureRingEquiv K L σ (g ((separableClosureRingEquiv K L σ).symm y)) :=
  (rfl)

/-- The forward map of `fixingSubgroupMulEquiv` is continuous for the Krull topologies: an
automorphism of `Kˢ` fixing a finite subextension `M = K(t)` of `Kˢ` is the image of every
automorphism of `Lˢ` fixing the finite subextension `L(e⁻¹ t)`, where `e` is the identification of
separable closures. -/
private theorem continuous_fixingSubgroupMulEquiv : Continuous (fixingSubgroupMulEquiv K L σ) := by
  refine Continuous.subtype_mk (continuous_of_continuousAt_one
    (σ.fieldRange.fixingSubgroup.subtype.comp (fixingSubgroupMulEquiv K L σ).toMonoidHom)
    (continuousAt_def.mpr fun N hN ↦ ?_)) _
  rw [map_one, krullTopology_mem_nhds_one_iff] at hN
  obtain ⟨M, hM, hMN⟩ := hN
  -- `M` is generated over `K` by a finite set `t`.
  have hfg : Algebra.EssFiniteType K M := inferInstance
  rw [essFiniteType_iff, fg_def] at hfg
  obtain ⟨t, ht, rfl⟩ := hfg
  rw [krullTopology_mem_nhds_one_iff]
  have := (ht.image (separableClosureRingEquiv K L σ).symm).to_subtype
  refine ⟨adjoin L ((separableClosureRingEquiv K L σ).symm '' t),
    finiteDimensional_adjoin fun y _ ↦ Algebra.IsIntegral.isIntegral y, fun g hg ↦ hMN ?_⟩
  -- The image of `g` fixes `t`, hence all of `K(t)`.
  have hfix : ∀ y ∈ t, (fixingSubgroupMulEquiv K L σ g : AbsoluteGaloisGroup K) y = y := by
    intro y hy
    have hgy : g ((separableClosureRingEquiv K L σ).symm y) =
        (separableClosureRingEquiv K L σ).symm y :=
      (IntermediateField.mem_fixingSubgroup_iff _ _).mp hg _ (subset_adjoin L _ ⟨y, hy, rfl⟩)
    rw [fixingSubgroupMulEquiv_apply, hgy, RingEquiv.apply_symm_apply]
  refine (le_iff_le (K := adjoin K t)
    (H := fixingSubgroup (AbsoluteGaloisGroup K) t)).mp ?_ fun y ↦ ?_
  · exact adjoin_le_iff.mpr fun y hy ↦ (mem_fixedField_iff
      (H := fixingSubgroup (AbsoluteGaloisGroup K) t) y).mpr fun f hf ↦ hf ⟨y, hy⟩
  · exact hfix y y.2

/-- **The absolute Galois group of `L` is the subgroup of `G_K` fixing `σ(L)` pointwise**, as
topological groups: conjugation by the identification `separableClosureRingEquiv K L σ` of separable
closures is an isomorphism `G_L ≃ₜ* σ.fieldRange.fixingSubgroup` for the Krull topologies, for any
extension `L/K` embedded in `Kˢ`. For a finite `L/K` this subgroup is open, and the isomorphism is
`galoisSubgroupEquiv K L σ`. -/
def absoluteGaloisGroupEquivFixingSubgroup :
    AbsoluteGaloisGroup L ≃ₜ* ↥σ.fieldRange.fixingSubgroup where
  __ := fixingSubgroupMulEquiv K L σ
  continuous_toFun := continuous_fixingSubgroupMulEquiv K L σ
  -- Continuity of the inverse comes for free: `G_L` is compact and the subgroup is Hausdorff.
  continuous_invFun :=
    (Continuous.homeoOfEquivCompactToT2 (f := (fixingSubgroupMulEquiv K L σ).toEquiv)
      (continuous_fixingSubgroupMulEquiv K L σ)).symm.continuous

/-- `absoluteGaloisGroupEquivFixingSubgroup K L σ` conjugates by the identification of separable
closures. -/
@[simp]
theorem absoluteGaloisGroupEquivFixingSubgroup_apply (g : AbsoluteGaloisGroup L)
    (y : SeparableClosure K) :
    (absoluteGaloisGroupEquivFixingSubgroup K L σ g : AbsoluteGaloisGroup K) y =
      separableClosureRingEquiv K L σ (g ((separableClosureRingEquiv K L σ).symm y)) :=
  fixingSubgroupMulEquiv_apply K L σ g y

/-- The inverse of `absoluteGaloisGroupEquivFixingSubgroup K L σ` conjugates back by the
identification of separable closures. -/
@[simp]
theorem absoluteGaloisGroupEquivFixingSubgroup_symm_apply (h : ↥σ.fieldRange.fixingSubgroup)
    (x : SeparableClosure L) :
    (absoluteGaloisGroupEquivFixingSubgroup K L σ).symm h x =
      (separableClosureRingEquiv K L σ).symm
        ((h : AbsoluteGaloisGroup K) (separableClosureRingEquiv K L σ x)) := by
  conv_rhs => rw [← (absoluteGaloisGroupEquivFixingSubgroup K L σ).apply_symm_apply h]
  rw [absoluteGaloisGroupEquivFixingSubgroup_apply, RingEquiv.symm_apply_apply,
    RingEquiv.symm_apply_apply]

end TauCeti
