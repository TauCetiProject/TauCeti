/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.NumberField.Global.Adeles.GaloisAction
public import TauCeti.NumberTheory.NumberField.Global.Places.Semilocal

/-!
# The semi-local component of an infinite adele

Let `L/K` be an extension of number fields and `v` an infinite place of `K`. An infinite adele
`a` of `L` has a component `a_w ∈ L_w` at each of the places `w` of `L` above `v`. Read through
the semi-local decomposition `K_v ⊗[K] L ≃ ∏_{w ∣ v} L_w`
(`TauCeti.GlobalNumberFields.infiniteSemilocalEquiv`), this family is an element of the scalar
extension `K_v ⊗[K] L`, and

```text
infiniteAdeleSemilocalHom L v : L_∞ → K_v ⊗[K] L
```

is a ring homomorphism. It sends a diagonal field element `x ∈ L` to `1 ⊗ x`, and it is natural:
it carries the extension map of infinite adeles along a tower `L ⊆ M` to `id ⊗ (L → M)`, and the
transport of infinite adeles along a `K`-isomorphism `e` to `id ⊗ e`. This is the archimedean
counterpart of `TauCeti.finiteAdeleSemilocalHom`: it is how the components above `v` of adeles
are mapped into extensions of `K_v`, for instance into a separable closure of `K_v`.

## Main definitions

* `TauCeti.GlobalNumberFields.infiniteAdeleSemilocalHom L v`: the components above `v` of an
  infinite adele of `L`, as an element of `K_v ⊗[K] L`.

## Main results

* `TauCeti.GlobalNumberFields.infiniteSemilocalEquiv_infiniteAdeleSemilocalHom`: under the
  semi-local decomposition it is the family of components above `v`.
* `TauCeti.GlobalNumberFields.infiniteAdeleSemilocalHom_algebraMap`: it sends `x ∈ L` to `1 ⊗ x`.
* `TauCeti.GlobalNumberFields.infiniteAdeleSemilocalHom_infiniteAdeleExtension`: naturality along
  a tower `L ⊆ M`.
* `TauCeti.GlobalNumberFields.infiniteAdeleSemilocalHom_infiniteAdeleEquiv`: naturality under
  `K`-isomorphisms.

## References

* [J. Neukirch, *Algebraic Number Theory*][Neukirch1992], Chapter II, Proposition (8.3), and
  Chapter VI, §2.
-/

public section
noncomputable section

open NumberField
open scoped TensorProduct NumberField.LiesOver

namespace TauCeti.GlobalNumberFields

variable {K : Type*} [Field K] [NumberField K] (L : Type*) [Field L] [NumberField L] [Algebra K L]
  (v : InfinitePlace K)

/-- **The semi-local component of an infinite adele.** The components `a_w` of an infinite adele
`a` of `L` at the places `w` of `L` above the infinite place `v` of `K`, read in `K_v ⊗[K] L`
through the semi-local decomposition `K_v ⊗[K] L ≃ ∏_{w ∣ v} L_w`. -/
def infiniteAdeleSemilocalHom : InfiniteAdeleRing L →+* v.Completion ⊗[K] L :=
  (infiniteSemilocalEquiv L v).symm.toRingHom.comp
    (RingHom.pi fun w : {w : InfinitePlace L // w.LiesOver v} ↦ Pi.evalRingHom _ w.1)

variable {L v}

/-- The semi-local component of an infinite adele is the inverse semi-local decomposition of its
family of components at the places above `v`. -/
theorem infiniteAdeleSemilocalHom_apply (a : InfiniteAdeleRing L) :
    infiniteAdeleSemilocalHom L v a =
      (infiniteSemilocalEquiv L v).symm fun w : {w : InfinitePlace L // w.LiesOver v} ↦ a w.1 :=
  (rfl)

/-- Under the semi-local decomposition, the semi-local component of an infinite adele is its
family of components at the places above `v`. -/
@[simp]
theorem infiniteSemilocalEquiv_infiniteAdeleSemilocalHom (a : InfiniteAdeleRing L) :
    infiniteSemilocalEquiv L v (infiniteAdeleSemilocalHom L v a) =
      fun w : {w : InfinitePlace L // w.LiesOver v} ↦ a w.1 := by
  rw [infiniteAdeleSemilocalHom_apply, AlgEquiv.apply_symm_apply]

/-- The semi-local component of a diagonal field element `x` is `1 ⊗ x`. -/
@[simp]
theorem infiniteAdeleSemilocalHom_algebraMap (x : L) :
    infiniteAdeleSemilocalHom L v (algebraMap L _ x) = 1 ⊗ₜ[K] x := by
  rw [infiniteAdeleSemilocalHom_apply, ← infiniteSemilocalEquiv_symm_algebraMap L v x]
  exact congrArg (infiniteSemilocalEquiv L v).symm
    (funext fun w ↦ InfiniteAdeleRing.algebraMap_apply L x w.1)

/-! ### Naturality -/

section Naturality

variable {M : Type*} [Field M] [NumberField M] [Algebra K M]

/-- A `K_v`-linear map `K_v ⊗[K] L → K_v ⊗[K] M` applied to semi-local components is continuous
on the infinite adeles of `L`, after the semi-local decomposition of `K_v ⊗[K] M`: both tensor
products are finite-dimensional over `K_v`. -/
private theorem continuous_infiniteSemilocalEquiv_linearMap_infiniteAdeleSemilocalHom
    (φ : v.Completion ⊗[K] L →ₗ[v.Completion] v.Completion ⊗[K] M) :
    Continuous fun a : InfiniteAdeleRing L ↦
      infiniteSemilocalEquiv M v (φ (infiniteAdeleSemilocalHom L v a)) := by
  let := moduleTopology v.Completion (v.Completion ⊗[K] L)
  have : IsModuleTopology v.Completion (v.Completion ⊗[K] L) := ⟨rfl⟩
  let := moduleTopology v.Completion (v.Completion ⊗[K] M)
  have : IsModuleTopology v.Completion (v.Completion ⊗[K] M) := ⟨rfl⟩
  have := IsModuleTopology.toContinuousAdd v.Completion (v.Completion ⊗[K] M)
  have hproj : Continuous fun a : InfiniteAdeleRing L ↦
      fun w : {w : InfinitePlace L // w.LiesOver v} ↦ a w.1 :=
    continuous_pi fun w ↦ continuous_apply w.1
  refine ((infiniteSemilocalContinuousEquiv M v).continuous.comp
    ((IsModuleTopology.continuous_of_linearMap φ).comp
      ((infiniteSemilocalContinuousEquiv L v).symm.continuous.comp hproj))).congr fun a ↦ ?_
  simp only [Function.comp_apply, ← ContinuousAlgEquiv.coe_toAlgEquiv,
    ContinuousAlgEquiv.symm_toAlgEquiv, infiniteSemilocalContinuousEquiv_toAlgEquiv,
    infiniteAdeleSemilocalHom_apply]

omit [Algebra K L] in
/-- Two ring homomorphisms from the infinite adeles of `L` to `K_v ⊗[K] M` agree once they agree
on `L` and are continuous after the semi-local decomposition, because `L` is dense in `L_∞`. -/
private theorem infiniteAdeleSemilocal_ringHom_ext
    {f g : InfiniteAdeleRing L →+* v.Completion ⊗[K] M}
    (hf : Continuous fun a ↦ infiniteSemilocalEquiv M v (f a))
    (hg : Continuous fun a ↦ infiniteSemilocalEquiv M v (g a))
    (h : ∀ x : L, f (algebraMap L _ x) = g (algebraMap L _ x)) : f = g :=
  RingHom.ext fun a ↦ (infiniteSemilocalEquiv M v).injective <| congrFun
    ((InfiniteAdeleRing.denseRange_algebraMap L).equalizer hf hg
      (funext fun x ↦ congrArg (infiniteSemilocalEquiv M v) (h x))) a

variable (v) in
/-- **Naturality under isomorphisms**: transporting an infinite adele of `L` along a `K`-algebra
isomorphism `e : L ≃ M`, for instance a `K`-automorphism of `L`, applies `id ⊗ e` to its
semi-local component. -/
theorem infiniteAdeleSemilocalHom_infiniteAdeleEquiv (e : L ≃ₐ[K] M) (a : InfiniteAdeleRing L) :
    infiniteAdeleSemilocalHom M v (infiniteAdeleEquiv L M e.toRingEquiv a) =
      Algebra.TensorProduct.map (AlgHom.id v.Completion v.Completion) (e : L →ₐ[K] M)
        (infiniteAdeleSemilocalHom L v a) := by
  refine RingHom.congr_fun (infiniteAdeleSemilocal_ringHom_ext (v := v)
    (f := (infiniteAdeleSemilocalHom M v).comp (infiniteAdeleEquiv L M e.toRingEquiv : _ →+* _))
    (g := (Algebra.TensorProduct.map (AlgHom.id v.Completion v.Completion)
        (e : L →ₐ[K] M)).toRingHom.comp (infiniteAdeleSemilocalHom L v))
    ?_ ?_ fun x ↦ ?_) a
  · simp only [RingHom.comp_apply, RingHom.coe_coe,
      infiniteSemilocalEquiv_infiniteAdeleSemilocalHom]
    exact continuous_pi fun w ↦ (continuous_apply w.1).comp
      (continuous_infiniteAdeleEquiv L M e.toRingEquiv)
  · simpa only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe,
      AlgHom.coe_toLinearMap] using
      continuous_infiniteSemilocalEquiv_linearMap_infiniteAdeleSemilocalHom
        (Algebra.TensorProduct.map (AlgHom.id v.Completion v.Completion)
          (e : L →ₐ[K] M)).toLinearMap
  · simp only [RingHom.comp_apply, RingHom.coe_coe, infiniteAdeleEquiv_algebraMap,
      infiniteAdeleSemilocalHom_algebraMap, AlgHom.toRingHom_eq_coe,
      Algebra.TensorProduct.map_tmul, map_one, AlgEquiv.coe_toRingEquiv, AlgEquiv.coe_toAlgHom]

variable [Algebra L M] [IsScalarTower K L M]

variable (v) in
/-- **Naturality along a tower `L ⊆ M`**: the semi-local component of the extension to `M` of an
infinite adele of `L` is the image of its semi-local component under `id ⊗ (L → M)`. -/
theorem infiniteAdeleSemilocalHom_infiniteAdeleExtension (a : InfiniteAdeleRing L) :
    infiniteAdeleSemilocalHom M v (infiniteAdeleExtension L M a) =
      Algebra.TensorProduct.map (AlgHom.id v.Completion v.Completion)
        (IsScalarTower.toAlgHom K L M) (infiniteAdeleSemilocalHom L v a) := by
  refine RingHom.congr_fun (infiniteAdeleSemilocal_ringHom_ext (v := v)
    (f := (infiniteAdeleSemilocalHom M v).comp (infiniteAdeleExtension L M))
    (g := (Algebra.TensorProduct.map (AlgHom.id v.Completion v.Completion)
        (IsScalarTower.toAlgHom K L M)).toRingHom.comp (infiniteAdeleSemilocalHom L v))
    ?_ ?_ fun x ↦ ?_) a
  · simp only [RingHom.comp_apply, infiniteSemilocalEquiv_infiniteAdeleSemilocalHom]
    exact continuous_pi fun w ↦ (continuous_apply w.1).comp (continuous_infiniteAdeleExtension L M)
  · simpa only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe,
      AlgHom.coe_toLinearMap] using
      continuous_infiniteSemilocalEquiv_linearMap_infiniteAdeleSemilocalHom
        (Algebra.TensorProduct.map (AlgHom.id v.Completion v.Completion)
          (IsScalarTower.toAlgHom K L M)).toLinearMap
  · simp only [RingHom.comp_apply, infiniteAdeleExtension_algebraMap,
      infiniteAdeleSemilocalHom_algebraMap, AlgHom.toRingHom_eq_coe, RingHom.coe_coe,
      Algebra.TensorProduct.map_tmul, map_one, IsScalarTower.coe_toAlgHom']

end Naturality

end TauCeti.GlobalNumberFields
