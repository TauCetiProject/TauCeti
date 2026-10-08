/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.NumberField.Global.Adeles.GaloisAction
public import TauCeti.NumberTheory.NumberField.LocalGlobal.Semilocal.Basic
import TauCeti.RingTheory.DedekindDomain.FiniteAdeleRing.Basic

/-!
# The semi-local component of a finite adele

Let `L/K` be an extension of number fields and `v` a finite place of `K`. A finite adele `a` of
`L` has a component `a_w ∈ L_w` at each of the finitely many places `w` of `L` above `v`. Read
through the semi-local decomposition `K_v ⊗[K] L ≃ ∏_{w ∣ v} L_w` (`TauCeti.semilocalEquiv`),
this family is an element of the scalar extension `K_v ⊗[K] L`, and

```text
finiteAdeleSemilocalHom L v : 𝔸_L^f → K_v ⊗[K] L
```

is a ring homomorphism. It sends a diagonal field element `x ∈ L` to `1 ⊗ x`, and it is natural:
it carries the extension map of finite adeles along a tower `L ⊆ M` to `id ⊗ (L → M)`, and the
transport of finite adeles along a `K`-automorphism `σ` of `L` to `id ⊗ σ`. The ring `K_v ⊗[K] L`
receives `K`-algebra maps out of `L` more easily than the product of completions does, so this
is how the components above `v` of adeles are mapped into extensions of `K_v`, for instance into
a separable closure of `K_v`.

## Main definitions

* `TauCeti.finiteAdeleSemilocalHom L v`: the components above `v` of a finite adele of `L`, as an
  element of `K_v ⊗[K] L`.

## Main results

* `TauCeti.semilocalEquiv_finiteAdeleSemilocalHom`: under the semi-local decomposition it is the
  family of components above `v`.
* `TauCeti.finiteAdeleSemilocalHom_algebraMap`: it sends `x ∈ L` to `1 ⊗ x`.
* `TauCeti.finiteAdeleSemilocalHom_finiteAdeleExtension`: naturality along a tower `L ⊆ M`.
* `TauCeti.finiteAdeleSemilocalHom_finiteAdeleEquiv`: naturality under `K`-automorphisms of `L`.

## References

* [J. Neukirch, *Algebraic Number Theory*][Neukirch1992], Chapter II, Proposition (8.3), and
  Chapter VI, §2.
-/

public section
noncomputable section

open IsDedekindDomain NumberField
open scoped TensorProduct AdicCompletionExtension

namespace TauCeti

open IsDedekindDomain.HeightOneSpectrum

local notation "𝒪" => _root_.NumberField.RingOfIntegers

variable {K : Type*} [Field K] [NumberField K] (L : Type*) [Field L] [NumberField L] [Algebra K L]
  (v : HeightOneSpectrum (𝒪 K))

/-- **The semi-local component of a finite adele.** The components `a_w` of a finite adele `a` of
`L` at the places `w` of `L` above the finite place `v` of `K`, read in `K_v ⊗[K] L` through the
semi-local decomposition `K_v ⊗[K] L ≃ ∏_{w ∣ v} L_w`. -/
def finiteAdeleSemilocalHom : FiniteAdeleRing (𝒪 L) L →+* v.adicCompletion K ⊗[K] L :=
  (semilocalEquiv L v).symm.toRingHom.comp
    (RingHom.pi fun w : {w : HeightOneSpectrum (𝒪 L) // w.asIdeal.LiesOver v.asIdeal} ↦
      RestrictedProduct.evalRingHom _ w.1)

variable {L v}

/-- The semi-local component of a finite adele is the inverse semi-local decomposition of its
family of components at the places above `v`. -/
theorem finiteAdeleSemilocalHom_apply (a : FiniteAdeleRing (𝒪 L) L) :
    finiteAdeleSemilocalHom L v a =
      (semilocalEquiv L v).symm
        fun w : {w : HeightOneSpectrum (𝒪 L) // w.asIdeal.LiesOver v.asIdeal} ↦ a w.1 :=
  (rfl)

/-- Under the semi-local decomposition, the semi-local component of a finite adele is its family
of components at the places above `v`. -/
@[simp]
theorem semilocalEquiv_finiteAdeleSemilocalHom (a : FiniteAdeleRing (𝒪 L) L) :
    semilocalEquiv L v (finiteAdeleSemilocalHom L v a) =
      fun w : {w : HeightOneSpectrum (𝒪 L) // w.asIdeal.LiesOver v.asIdeal} ↦ a w.1 := by
  rw [finiteAdeleSemilocalHom_apply, AlgEquiv.apply_symm_apply]

/-- The semi-local component of a diagonal field element `x` is `1 ⊗ x`. -/
@[simp]
theorem finiteAdeleSemilocalHom_algebraMap (x : L) :
    finiteAdeleSemilocalHom L v (algebraMap L _ x) = 1 ⊗ₜ[K] x := by
  rw [finiteAdeleSemilocalHom_apply, ← semilocalEquiv_symm_algebraMap L v x]
  exact congrArg (semilocalEquiv L v).symm
    (funext fun w ↦ FiniteAdeleRing.algebraMap_apply (𝒪 L) L x w.1)

/-! ### Naturality -/

section Naturality

variable {M : Type*} [Field M] [NumberField M] [Algebra K M]

/-- A `K_v`-linear map `K_v ⊗[K] L → K_v ⊗[K] M` applied to semi-local components is continuous
on the finite adeles of `L`, after the semi-local decomposition of `K_v ⊗[K] M`: both tensor
products are finite-dimensional over `K_v`. -/
private theorem continuous_semilocalEquiv_linearMap_finiteAdeleSemilocalHom
    (φ : v.adicCompletion K ⊗[K] L →ₗ[v.adicCompletion K] v.adicCompletion K ⊗[K] M) :
    Continuous fun a : FiniteAdeleRing (𝒪 L) L ↦
      semilocalEquiv M v (φ (finiteAdeleSemilocalHom L v a)) := by
  let := moduleTopology (v.adicCompletion K) (v.adicCompletion K ⊗[K] L)
  have : IsModuleTopology (v.adicCompletion K) (v.adicCompletion K ⊗[K] L) := ⟨rfl⟩
  let := moduleTopology (v.adicCompletion K) (v.adicCompletion K ⊗[K] M)
  have : IsModuleTopology (v.adicCompletion K) (v.adicCompletion K ⊗[K] M) := ⟨rfl⟩
  have := IsModuleTopology.toContinuousAdd (v.adicCompletion K) (v.adicCompletion K ⊗[K] M)
  have hproj : Continuous fun a : FiniteAdeleRing (𝒪 L) L ↦
      fun w : {w : HeightOneSpectrum (𝒪 L) // w.asIdeal.LiesOver v.asIdeal} ↦ a w.1 :=
    continuous_pi fun w ↦ RestrictedProduct.continuous_eval w.1
  refine ((semilocalContinuousEquiv M v).continuous.comp
    ((IsModuleTopology.continuous_of_linearMap φ).comp
      ((semilocalContinuousEquiv L v).symm.continuous.comp hproj))).congr fun a ↦ ?_
  simp only [Function.comp_apply, ← ContinuousAlgEquiv.coe_toAlgEquiv,
    ContinuousAlgEquiv.symm_toAlgEquiv, semilocalContinuousEquiv_toAlgEquiv,
    finiteAdeleSemilocalHom_apply]

omit [Algebra K L] in
/-- Two ring homomorphisms from the finite adeles of `L` to `K_v ⊗[K] M` agree once they agree
on `L` and are continuous after the semi-local decomposition, by strong approximation. -/
private theorem finiteAdeleSemilocal_ringHom_ext
    {f g : FiniteAdeleRing (𝒪 L) L →+* v.adicCompletion K ⊗[K] M}
    (hf : Continuous fun a ↦ semilocalEquiv M v (f a))
    (hg : Continuous fun a ↦ semilocalEquiv M v (g a))
    (h : ∀ x : L, f (algebraMap L _ x) = g (algebraMap L _ x)) : f = g :=
  RingHom.ext fun a ↦ (semilocalEquiv M v).injective <| congrFun
    ((FiniteAdeleRing.denseRange_algebraMap (𝒪 L) L).equalizer hf hg
      (funext fun x ↦ congrArg (semilocalEquiv M v) (h x))) a

variable (v) in
/-- **Naturality under isomorphisms**: transporting a finite adele of `L` along a `K`-algebra
isomorphism `e : L ≃ M`, for instance a `K`-automorphism of `L`, applies `id ⊗ e` to its
semi-local component. -/
theorem finiteAdeleSemilocalHom_finiteAdeleEquiv (e : L ≃ₐ[K] M) (a : FiniteAdeleRing (𝒪 L) L) :
    finiteAdeleSemilocalHom M v (GlobalNumberFields.finiteAdeleEquiv L M e.toRingEquiv a) =
      Algebra.TensorProduct.map (AlgHom.id (v.adicCompletion K) (v.adicCompletion K))
        (e : L →ₐ[K] M) (finiteAdeleSemilocalHom L v a) := by
  refine RingHom.congr_fun (finiteAdeleSemilocal_ringHom_ext (v := v)
    (f := (finiteAdeleSemilocalHom M v).comp
      (GlobalNumberFields.finiteAdeleEquiv L M e.toRingEquiv : _ →+* _))
    (g := (Algebra.TensorProduct.map (AlgHom.id (v.adicCompletion K) (v.adicCompletion K))
        (e : L →ₐ[K] M)).toRingHom.comp (finiteAdeleSemilocalHom L v))
    ?_ ?_ fun x ↦ ?_) a
  · simp only [RingHom.comp_apply, RingHom.coe_coe, semilocalEquiv_finiteAdeleSemilocalHom]
    exact continuous_pi fun w ↦ (RestrictedProduct.continuous_eval w.1).comp
      (GlobalNumberFields.continuous_finiteAdeleEquiv L M e.toRingEquiv)
  · simpa only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe,
      AlgHom.coe_toLinearMap] using
      continuous_semilocalEquiv_linearMap_finiteAdeleSemilocalHom
        (Algebra.TensorProduct.map (AlgHom.id (v.adicCompletion K) (v.adicCompletion K))
          (e : L →ₐ[K] M)).toLinearMap
  · simp only [RingHom.comp_apply, RingHom.coe_coe, GlobalNumberFields.finiteAdeleEquiv_algebraMap,
      finiteAdeleSemilocalHom_algebraMap, AlgHom.toRingHom_eq_coe,
      Algebra.TensorProduct.map_tmul, map_one, AlgEquiv.coe_toRingEquiv, AlgEquiv.coe_toAlgHom]

variable [Algebra L M] [IsScalarTower K L M]

variable (v) in
/-- **Naturality along a tower `L ⊆ M`**: the semi-local component of the extension to `M` of a
finite adele of `L` is the image of its semi-local component under `id ⊗ (L → M)`. -/
theorem finiteAdeleSemilocalHom_finiteAdeleExtension (a : FiniteAdeleRing (𝒪 L) L) :
    finiteAdeleSemilocalHom M v (finiteAdeleExtension (𝒪 L) L (𝒪 M) M a) =
      Algebra.TensorProduct.map (AlgHom.id (v.adicCompletion K) (v.adicCompletion K))
        (IsScalarTower.toAlgHom K L M) (finiteAdeleSemilocalHom L v a) := by
  refine RingHom.congr_fun (finiteAdeleSemilocal_ringHom_ext (v := v)
    (f := (finiteAdeleSemilocalHom M v).comp (finiteAdeleExtension (𝒪 L) L (𝒪 M) M))
    (g := (Algebra.TensorProduct.map (AlgHom.id (v.adicCompletion K) (v.adicCompletion K))
        (IsScalarTower.toAlgHom K L M)).toRingHom.comp (finiteAdeleSemilocalHom L v))
    ?_ ?_ fun x ↦ ?_) a
  · simp only [RingHom.comp_apply, semilocalEquiv_finiteAdeleSemilocalHom]
    exact continuous_pi fun w ↦ (RestrictedProduct.continuous_eval w.1).comp
      (continuous_finiteAdeleExtension (𝒪 L) L (𝒪 M) M)
  · simpa only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe,
      AlgHom.coe_toLinearMap] using
      continuous_semilocalEquiv_linearMap_finiteAdeleSemilocalHom
        (Algebra.TensorProduct.map (AlgHom.id (v.adicCompletion K) (v.adicCompletion K))
          (IsScalarTower.toAlgHom K L M)).toLinearMap
  · simp only [RingHom.comp_apply, finiteAdeleExtension_algebraMap,
      finiteAdeleSemilocalHom_algebraMap, AlgHom.toRingHom_eq_coe, RingHom.coe_coe,
      Algebra.TensorProduct.map_tmul, map_one, IsScalarTower.coe_toAlgHom']

end Naturality

end TauCeti
