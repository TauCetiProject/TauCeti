/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.NumberField.Global.Adeles.Extension

/-!
# Galois action on adeles

A field isomorphism transports finite and infinite adeles by restriction of places and the
induced maps of completions. The resulting ring equivalences are continuous in both directions
and commute with the diagonal embeddings. Their composition laws give the Galois action on the
full adele ring, with the discrete topology on the finite automorphism group.

The construction uses `finiteAdeleExtension` and `infiniteAdeleExtension` with the algebra
structure induced by the field isomorphism. In particular, it preserves the restricted-product
condition, rather than merely permuting the ambient unrestricted product.

## References

* Neukirch, *Algebraic Number Theory*, Chapter VI, §1.
-/

public section

open NumberField IsDedekindDomain

namespace TauCeti.GlobalNumberFields

variable (K L : Type*) [Field K] [Field L]

private noncomputable def infiniteMap (e : K ≃+* L) :
    InfiniteAdeleRing K →+* InfiniteAdeleRing L :=
  letI := e.toRingHom.toAlgebra
  infiniteAdeleExtension K L

private theorem continuous_infiniteMap (e : K ≃+* L) : Continuous (infiniteMap K L e) := by
  let := e.toRingHom.toAlgebra
  exact continuous_infiniteAdeleExtension K L

private theorem infiniteMap_algebraMap (e : K ≃+* L) (x : K) :
    infiniteMap K L e (algebraMap K _ x) = algebraMap L _ (e x) := by
  let := e.toRingHom.toAlgebra
  exact infiniteAdeleExtension_algebraMap K L x

private theorem infiniteMap_comp (M : Type*) [Field M]
    (e : K ≃+* L) (f : L ≃+* M) :
    (infiniteMap L M f).comp (infiniteMap K L e) = infiniteMap K M (e.trans f) := by
  let := e.toRingHom.toAlgebra
  let := f.toRingHom.toAlgebra
  let := (e.trans f).toRingHom.toAlgebra
  let : IsScalarTower K L M := IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  exact infiniteAdeleExtension_comp K L M

private theorem infiniteMap_refl : infiniteMap K K (RingEquiv.refl K) = RingHom.id _ :=
  infiniteAdeleExtension_self K

/-- The transport of infinite adeles along a field isomorphism. The component at `w` uses the
completion map from the place obtained by pulling `w` back along the isomorphism. -/
noncomputable def infiniteAdeleEquiv (e : K ≃+* L) :
    InfiniteAdeleRing K ≃+* InfiniteAdeleRing L :=
  RingEquiv.ofRingHom (infiniteMap K L e) (infiniteMap L K e.symm)
    (by rw [infiniteMap_comp, RingEquiv.symm_trans_self, infiniteMap_refl])
    (by rw [infiniteMap_comp, RingEquiv.self_trans_symm, infiniteMap_refl])

/-- Transport of infinite adeles is continuous. -/
@[continuity, fun_prop]
theorem continuous_infiniteAdeleEquiv (e : K ≃+* L) : Continuous (infiniteAdeleEquiv K L e) :=
  continuous_infiniteMap K L e

/-- Transport of infinite adeles commutes with the diagonal field embeddings. -/
@[simp]
theorem infiniteAdeleEquiv_algebraMap (e : K ≃+* L) (x : K) :
    infiniteAdeleEquiv K L e (algebraMap K _ x) = algebraMap L _ (e x) :=
  infiniteMap_algebraMap K L e x

/-- The inverse transport of infinite adeles is transport along the inverse field isomorphism. -/
@[simp]
theorem infiniteAdeleEquiv_symm (e : K ≃+* L) :
    (infiniteAdeleEquiv K L e).symm = infiniteAdeleEquiv L K e.symm :=
  (rfl)

/-- The placewise formula for transport of infinite adeles. The local map uses the algebra
structure induced by `e`, not any pre-existing algebra structure on `L` over `K`. -/
@[simp]
theorem infiniteAdeleEquiv_apply (e : K ≃+* L) (a : InfiniteAdeleRing K)
    (w : InfinitePlace L) :
    letI := e.toRingHom.toAlgebra
    infiniteAdeleEquiv K L e a w =
      LiesOver.completionMap (v := w.comap (algebraMap K L)) (w := w)
        (a (w.comap (algebraMap K L))) := by
  let := e.toRingHom.toAlgebra
  exact infiniteAdeleExtension_apply a w

/-- Transport of infinite adeles along the identity field isomorphism is the identity. -/
@[simp]
theorem infiniteAdeleEquiv_refl :
    infiniteAdeleEquiv K K (RingEquiv.refl K) = RingEquiv.refl _ := by
  ext a : 1
  exact RingHom.congr_fun (infiniteMap_refl K) a

/-- Transport of infinite adeles respects composition of field isomorphisms. -/
@[simp]
theorem infiniteAdeleEquiv_trans (M : Type*) [Field M]
    (e : K ≃+* L) (f : L ≃+* M) :
    (infiniteAdeleEquiv K L e).trans (infiniteAdeleEquiv L M f) =
      infiniteAdeleEquiv K M (e.trans f) := by
  ext a : 1
  exact RingHom.congr_fun (infiniteMap_comp K L M e f) a

variable [NumberField K] [NumberField L]

private noncomputable def finiteMap (e : K ≃+* L) :
    FiniteAdeleRing (𝓞 K) K →+* FiniteAdeleRing (𝓞 L) L := by
  letI := e.toRingHom.toAlgebra
  exact finiteAdeleExtension (𝓞 K) K (𝓞 L) L

private theorem continuous_finiteMap (e : K ≃+* L) : Continuous (finiteMap K L e) := by
  let := e.toRingHom.toAlgebra
  exact continuous_finiteAdeleExtension (𝓞 K) K (𝓞 L) L

private theorem finiteMap_algebraMap (e : K ≃+* L) (x : K) :
    finiteMap K L e (algebraMap K _ x) = algebraMap L _ (e x) := by
  let := e.toRingHom.toAlgebra
  exact finiteAdeleExtension_algebraMap (𝓞 K) K (𝓞 L) L x

private theorem finiteMap_comp (M : Type*) [Field M] [NumberField M]
    (e : K ≃+* L) (f : L ≃+* M) :
    (finiteMap L M f).comp (finiteMap K L e) = finiteMap K M (e.trans f) := by
  let := (e.trans f).toRingHom.toAlgebra
  apply eq_finiteAdeleExtension_of_continuous (𝓞 K) K (𝓞 M) M
    ((continuous_finiteMap L M f).comp (continuous_finiteMap K L e))
  intro x
  simp only [RingHom.comp_apply, finiteMap_algebraMap]
  rfl

private theorem finiteMap_refl : finiteMap K K (RingEquiv.refl K) = RingHom.id _ :=
  finiteAdeleExtension_self (𝓞 K) K

/-- The transport of finite adeles along a field isomorphism, including preservation of
integrality at all but finitely many places. -/
noncomputable def finiteAdeleEquiv (e : K ≃+* L) :
    FiniteAdeleRing (𝓞 K) K ≃+* FiniteAdeleRing (𝓞 L) L :=
  RingEquiv.ofRingHom (finiteMap K L e) (finiteMap L K e.symm)
    (by rw [finiteMap_comp, RingEquiv.symm_trans_self, finiteMap_refl])
    (by rw [finiteMap_comp, RingEquiv.self_trans_symm, finiteMap_refl])

/-- Transport of finite adeles is continuous. -/
@[continuity, fun_prop]
theorem continuous_finiteAdeleEquiv (e : K ≃+* L) : Continuous (finiteAdeleEquiv K L e) :=
  continuous_finiteMap K L e

/-- Transport of finite adeles commutes with the diagonal field embeddings. -/
@[simp]
theorem finiteAdeleEquiv_algebraMap (e : K ≃+* L) (x : K) :
    finiteAdeleEquiv K L e (algebraMap K _ x) = algebraMap L _ (e x) :=
  finiteMap_algebraMap K L e x

/-- The inverse transport of finite adeles is transport along the inverse field isomorphism. -/
@[simp]
theorem finiteAdeleEquiv_symm (e : K ≃+* L) :
    (finiteAdeleEquiv K L e).symm = finiteAdeleEquiv L K e.symm :=
  (rfl)

/-- The placewise formula for transport of finite adeles. The prime below `w` is its comap
under the induced isomorphism of rings of integers. -/
@[simp]
theorem finiteAdeleEquiv_apply (e : K ≃+* L) (a : FiniteAdeleRing (𝓞 K) K)
    (w : HeightOneSpectrum (𝓞 L)) :
    letI := e.toRingHom.toAlgebra
    finiteAdeleEquiv K L e a w =
      HeightOneSpectrum.adicCompletionExtension K L (w.under (𝓞 K)) w (a (w.under (𝓞 K))) := by
  let := e.toRingHom.toAlgebra
  exact finiteAdeleExtension_apply a w

/-- Transport of finite adeles along the identity field isomorphism is the identity. -/
@[simp]
theorem finiteAdeleEquiv_refl :
    finiteAdeleEquiv K K (RingEquiv.refl K) = RingEquiv.refl _ := by
  ext a : 1
  exact RingHom.congr_fun (finiteMap_refl K) a

/-- Transport of finite adeles respects composition of field isomorphisms. -/
@[simp]
theorem finiteAdeleEquiv_trans (M : Type*) [Field M] [NumberField M]
    (e : K ≃+* L) (f : L ≃+* M) :
    (finiteAdeleEquiv K L e).trans (finiteAdeleEquiv L M f) =
      finiteAdeleEquiv K M (e.trans f) := by
  ext a : 1
  exact RingHom.congr_fun (finiteMap_comp K L M e f) a

/-- The ring equivalence of full adele rings induced by a field isomorphism. -/
noncomputable def adeleEquiv (e : K ≃+* L) : AdeleRing (𝓞 K) K ≃+* AdeleRing (𝓞 L) L :=
  RingEquiv.prodCongr (infiniteAdeleEquiv K L e) (finiteAdeleEquiv K L e)

@[simp]
theorem adeleEquiv_fst (e : K ≃+* L) (a : AdeleRing (𝓞 K) K) :
    (adeleEquiv K L e a).1 = infiniteAdeleEquiv K L e a.1 :=
  (rfl)

@[simp]
theorem adeleEquiv_snd (e : K ≃+* L) (a : AdeleRing (𝓞 K) K) :
    (adeleEquiv K L e a).2 = finiteAdeleEquiv K L e a.2 :=
  (rfl)

/-- Transport of full adeles is continuous. Its inverse is the transport along `e.symm`. -/
@[continuity, fun_prop]
theorem continuous_adeleEquiv (e : K ≃+* L) : Continuous (adeleEquiv K L e) :=
  (continuous_infiniteAdeleEquiv K L e).prodMap (continuous_finiteAdeleEquiv K L e)

/-- The inverse transport of full adeles is transport along the inverse field isomorphism. -/
@[simp]
theorem adeleEquiv_symm (e : K ≃+* L) :
    (adeleEquiv K L e).symm = adeleEquiv L K e.symm := by
  ext a : 1
  exact Prod.ext (RingEquiv.congr_fun (infiniteAdeleEquiv_symm K L e) a.1)
    (RingEquiv.congr_fun (finiteAdeleEquiv_symm K L e) a.2)

/-- Field isomorphisms commute with the diagonal embeddings into the full adele rings. -/
@[simp]
theorem adeleEquiv_algebraMap (e : K ≃+* L) (x : K) :
    adeleEquiv K L e (algebraMap K _ x) = algebraMap L _ (e x) := by
  apply Prod.ext <;> simp

/-- Transport of full adeles along the identity field isomorphism is the identity. -/
@[simp]
theorem adeleEquiv_refl : adeleEquiv K K (RingEquiv.refl K) = RingEquiv.refl _ := by
  ext a : 1
  apply Prod.ext <;> simp

/-- Transport of full adeles respects composition of field isomorphisms. -/
@[simp]
theorem adeleEquiv_trans (M : Type*) [Field M] [NumberField M]
    (e : K ≃+* L) (f : L ≃+* M) :
    (adeleEquiv K L e).trans (adeleEquiv L M f) = adeleEquiv K M (e.trans f) := by
  ext a : 1
  apply Prod.ext
  · exact RingEquiv.congr_fun (infiniteAdeleEquiv_trans K L M e f) a.1
  · exact RingEquiv.congr_fun (finiteAdeleEquiv_trans K L M e f) a.2

section Galois

omit [NumberField K]

variable [Algebra K L]

/-- The action of the field automorphism group on full adeles, by continuous ring automorphisms.
No normality hypothesis is needed to act; for a Galois extension this is the Galois action. -/
noncomputable def adeleGaloisAction :
    (L ≃ₐ[K] L) →* (AdeleRing (𝓞 L) L ≃+* AdeleRing (𝓞 L) L) where
  toFun σ := adeleEquiv L L σ.toRingEquiv
  map_one' := adeleEquiv_refl L
  map_mul' σ τ := by
    ext a : 1
    exact (RingEquiv.congr_fun
      (adeleEquiv_trans L L L τ.toRingEquiv σ.toRingEquiv) a).symm

/-- Evaluation of the Galois action uses transport along the underlying field automorphism. -/
theorem adeleGaloisAction_apply (σ : L ≃ₐ[K] L) (a : AdeleRing (𝓞 L) L) :
    adeleGaloisAction K L σ a = adeleEquiv L L σ.toRingEquiv a :=
  (rfl)

/-- The Galois action extends the action on the diagonally embedded number field. -/
@[simp]
theorem adeleGaloisAction_algebraMap (σ : L ≃ₐ[K] L) (x : L) :
    adeleGaloisAction K L σ (algebraMap L _ x) = algebraMap L _ (σ x) :=
  adeleEquiv_algebraMap L L σ.toRingEquiv x

/-- The Galois action fixes every adele extended from the base field, not only principal adeles. -/
@[simp]
theorem adeleGaloisAction_adeleExtension [NumberField K] (σ : L ≃ₐ[K] L) (a : AdeleRing (𝓞 K) K) :
    adeleGaloisAction K L σ (adeleExtension (𝓞 K) K (𝓞 L) L a) =
      adeleExtension (𝓞 K) K (𝓞 L) L a := by
  have hi := eq_infiniteAdeleExtension_of_continuous K L
    (f := (infiniteAdeleEquiv L L σ.toRingEquiv).toRingHom.comp (infiniteAdeleExtension K L))
    ((continuous_infiniteAdeleEquiv L L σ.toRingEquiv).comp
      (continuous_infiniteAdeleExtension K L))
    (fun x ↦ by simp)
  have hf := eq_finiteAdeleExtension_of_continuous (𝓞 K) K (𝓞 L) L
    (f := (finiteAdeleEquiv L L σ.toRingEquiv).toRingHom.comp
      (finiteAdeleExtension (𝓞 K) K (𝓞 L) L))
    ((continuous_finiteAdeleEquiv L L σ.toRingEquiv).comp
      (continuous_finiteAdeleExtension (𝓞 K) K (𝓞 L) L))
    (fun x ↦ by simp)
  apply Prod.ext
  · simp only [adeleGaloisAction_apply, adeleEquiv_fst, adeleExtension_fst]
    exact RingHom.congr_fun hi a.1
  · simp only [adeleGaloisAction_apply, adeleEquiv_snd, adeleExtension_snd]
    exact RingHom.congr_fun hf a.2

/-- Every automorphism acts continuously on full adeles. -/
@[continuity, fun_prop]
theorem continuous_adeleGaloisAction (σ : L ≃ₐ[K] L) :
    Continuous (adeleGaloisAction K L σ) :=
  continuous_adeleEquiv L L σ.toRingEquiv

/-- The action is jointly continuous when the automorphism group has its discrete topology,
as is appropriate for a finite extension. -/
theorem continuous_adeleGaloisAction_uncurry [TopologicalSpace (L ≃ₐ[K] L)]
    [DiscreteTopology (L ≃ₐ[K] L)] :
    Continuous (fun p : (L ≃ₐ[K] L) × AdeleRing (𝓞 L) L ↦ adeleGaloisAction K L p.1 p.2) :=
  continuous_prod_of_discrete_left.mpr (continuous_adeleGaloisAction K L)

/-- The Galois action as a semiring action, available in the `AdeleGaloisAction` scope.
It is not a global instance, so competing actions on an adele ring remain available. -/
@[reducible]
noncomputable def adeleMulSemiringAction : MulSemiringAction (L ≃ₐ[K] L) (AdeleRing (𝓞 L) L) :=
  MulSemiringAction.compHom _ (adeleGaloisAction K L)

scoped[AdeleGaloisAction] attribute [instance]
  TauCeti.GlobalNumberFields.adeleMulSemiringAction

open scoped AdeleGaloisAction

/-- The scoped Galois action is evaluation of `adeleGaloisAction`. -/
@[simp]
theorem adele_smul_def (σ : L ≃ₐ[K] L) (a : AdeleRing (𝓞 L) L) :
    σ • a = adeleGaloisAction K L σ a :=
  (rfl)

/-- With the discrete topology on field automorphisms, the scoped Galois action is continuous. -/
instance [TopologicalSpace (L ≃ₐ[K] L)] [DiscreteTopology (L ≃ₐ[K] L)] :
    ContinuousSMul (L ≃ₐ[K] L) (AdeleRing (𝓞 L) L) :=
  ⟨continuous_adeleGaloisAction_uncurry K L⟩

end Galois

end TauCeti.GlobalNumberFields
