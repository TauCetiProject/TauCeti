/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.FieldTheory.LinearDisjoint
import Mathlib.RingTheory.Localization.BaseChange
import TauCeti.RingTheory.Localization.Defs
import TauCeti.RingTheory.Localization.FractionRing

/-!
# The fraction field of a tensor product of fields

If `F ⊗[k] K` is a domain, its fraction field is a compositum of the two factors,
with linearly disjoint images. Unlike the existential construction
`IntermediateField.LinearDisjoint.exists_field_of_isDomain`, these statements retain
an arbitrary specified fraction field and its scalar maps. This is useful when the
same fraction field must also be compared with localizations or geometric base change.

When `K` is flat over `k` (in particular over a field `k`), an injective `k`-algebra
homomorphism `f : A →ₐ[k] B` induces an injective `K`-algebra homomorphism
`f.fractionRingTensorMap hf K Q₁ Q₂ : Q₁ →ₐ[K] Q₂` between specified total rings of fractions
of `A ⊗[k] K` and `B ⊗[k] K` (when `Q₂` has no zero divisors, for instance a fraction field),
uniquely determined by its action `algebraMap A Q₁ a ↦ algebraMap B Q₂ (f a)` on the left factor
and functorial with respect to identity and composition. When `A` is a division ring and `Q₂` is
nontrivial, injectivity of `f` is automatic (`TauCeti.injective_of_isFractionRing_tensorProduct`).
An isomorphism `e : A ≃ₐ[k] B` induces `e.fractionRingTensorCongr K Q₁ Q₂ : Q₁ ≃ₐ[K] Q₂`, and
swapping the factors induces `TauCeti.fractionRingTensorCommAlgEquiv`, both without flatness or
domain hypotheses.
Moreover, if `F` is a total ring of fractions of a `k`-algebra `A`, then along compatible
algebra maps into `Q`, a total ring of fractions `Q` (without zero divisors) of a
nontrivial `F ⊗[k] K` is also a total ring of fractions of `A ⊗[k] K` when `K` is flat
over `k`, and conversely a fraction ring `Q` of a domain `A ⊗[k] K` is a fraction ring of
`F ⊗[k] K`.

The right-factor algebra is Mathlib's `Algebra.TensorProduct.rightAlgebra`, installed
locally together with `right_isScalarTower`; all maps to the fraction field are the
usual scalar-tower maps. The linear-disjointness argument follows Jz Pan's
`Subalgebra.LinearDisjoint.exists_field_of_isDomain_of_injective` in Mathlib,
using `Subalgebra.LinearDisjoint.include_range` and transport along the fraction map.

## Main declarations

* `TauCeti.adjoin_range_right_eq_top_of_isFractionRing_tensorProduct`: the two factors generate
  the fraction field of `F ⊗[k] K`.
* `TauCeti.linearDisjoint_of_isFractionRing_tensorProduct`: the images of `F` and `K` in a
  fraction field of `F ⊗[k] K` are linearly disjoint over `k`.
* `TauCeti.ringHom_ext_of_isFractionRing_tensorProduct`,
  `TauCeti.algHom_ext_of_isFractionRing_tensorProduct`: maps out of a fraction ring of `A ⊗[k] K`
  are determined by their restrictions to `A` and `K` (or to `A` for `K`-algebra maps).
* `AlgHom.fractionRingTensorMap`: the `K`-algebra map `Q₁ →ₐ[K] Q₂` induced on specified total
  rings of fractions by an injective `f : A →ₐ[k] B`, with its values on `A ⊗[k] K`, `A`, and pure
  tensors, injectivity (`AlgHom.fractionRingTensorMap_injective`), uniqueness
  (`AlgHom.eq_fractionRingTensorMap_iff`, `AlgHom.eq_coe_fractionRingTensorMap_of_algebraMap`),
  identity (`AlgHom.fractionRingTensorMap_id`), and composition
  (`AlgHom.fractionRingTensorMap_comp`).
* `AlgEquiv.fractionRingTensorCongr`: the `K`-algebra equivalence `Q₁ ≃ₐ[K] Q₂` induced by
  `e : A ≃ₐ[k] B`, with `refl`, `symm`, `trans`, and compatibility with
  `AlgHom.fractionRingTensorMap`.
* `TauCeti.fractionRingTensorCommAlgEquiv`: the `K`-algebra equivalence between total rings of
  fractions of `A ⊗[k] K` and `K ⊗[k] A`.
* `TauCeti.injective_of_isFractionRing_tensorProduct`: algebra maps out of a division ring into `B`
  are injective as soon as `B ⊗[k] K` has a nontrivial total ring of fractions.
* `TauCeti.isFractionRing_base_tensorProduct_of_isFractionRing_tensorProduct`,
  `TauCeti.isFractionRing_tensorProduct_of_isFractionRing_base_tensorProduct`: comparison of
  fraction rings of `A ⊗[k] K` and `F ⊗[k] K` when `F` is a fraction ring of `A`.

## References

* S. Lang, *Algebra*, the construction of linearly disjoint composita by tensor products.
-/

public section

open scoped TensorProduct

namespace TauCeti

attribute [local instance] Algebra.TensorProduct.rightAlgebra
  Algebra.TensorProduct.right_isScalarTower

section Generation

variable {k F K Q : Type*} [CommRing k] [Field F] [CommRing K] [Field Q]
  [Algebra k F] [Algebra k K] [Algebra (F ⊗[k] K) Q]
  [Algebra F Q] [Algebra K Q]
  [IsScalarTower F (F ⊗[k] K) Q] [IsScalarTower K (F ⊗[k] K) Q]
  [IsFractionRing (F ⊗[k] K) Q]

include k in
/-- The two factors generate the fraction field of their tensor product as a field.
No algebraicity assumption on either factor is needed. -/
theorem adjoin_range_right_eq_top_of_isFractionRing_tensorProduct :
    IntermediateField.adjoin F (Set.range (algebraMap K Q)) = ⊤ := by
  have hleft : (algebraMap (F ⊗[k] K) Q) ∘
      (Algebra.TensorProduct.includeLeft : F →ₐ[k] F ⊗[k] K) = algebraMap F Q := by
    exact congrArg DFunLike.coe (IsScalarTower.algebraMap_eq F (F ⊗[k] K) Q).symm
  have hright : (algebraMap (F ⊗[k] K) Q) ∘
      (Algebra.TensorProduct.includeRight : K →ₐ[k] F ⊗[k] K) = algebraMap K Q := by
    exact congrArg DFunLike.coe (IsScalarTower.algebraMap_eq K (F ⊗[k] K) Q).symm
  have hs : (algebraMap (F ⊗[k] K) Q).range =
      Subring.closure (Set.range (algebraMap F Q) ∪ Set.range (algebraMap K Q)) := by
    rw [RingHom.range_eq_map,
      ← Algebra.TensorProduct.closure_range_union_range_eq_top k F K,
      RingHom.map_closure, Set.image_union, ← Set.range_comp, ← Set.range_comp,
      hleft, hright]
  have h := IsFractionRing.ringHom_fieldRange_eq_of_comp_eq_of_range_eq
    (f := RingHom.id Q) (g := algebraMap (F ⊗[k] K) Q) rfl hs
  apply IntermediateField.toSubfield_injective
  rw [IntermediateField.adjoin_toSubfield, ← h]
  exact RingHom.fieldRange_eq_top_iff.mpr Function.surjective_id

end Generation

section LinearDisjoint

variable {k F K Q : Type*} [Field k] [Field F] [Field K] [Field Q]
  [Algebra k F] [Algebra k K] [Algebra (F ⊗[k] K) Q]
  [Algebra k Q] [Algebra F Q] [Algebra K Q]
  [IsScalarTower F (F ⊗[k] K) Q] [IsScalarTower K (F ⊗[k] K) Q]
  [IsScalarTower k F Q] [IsScalarTower k K Q]
  [IsFractionRing (F ⊗[k] K) Q]

/-- The images of the two factors in a fraction field of their tensor product are
linearly disjoint. This is the concrete fraction-field form of Mathlib's
`Subalgebra.LinearDisjoint.exists_field_of_isDomain_of_injective`. -/
theorem linearDisjoint_of_isFractionRing_tensorProduct :
    (IsScalarTower.toAlgHom k K Q).fieldRange.LinearDisjoint F := by
  have : IsScalarTower k (F ⊗[k] K) Q := .to₁₃₄ k F (F ⊗[k] K) Q
  let i := IsScalarTower.toAlgHom k (F ⊗[k] K) Q
  have hi : Function.Injective i := IsFractionRing.injective (F ⊗[k] K) Q
  have H := (Subalgebra.LinearDisjoint.include_range k F K).map i hi
  rw [IntermediateField.linearDisjoint_iff, AlgHom.fieldRange_toSubalgebra]
  have hleft : i.comp Algebra.TensorProduct.includeLeft = IsScalarTower.toAlgHom k F Q := by
    apply AlgHom.toRingHom_injective
    exact (IsScalarTower.algebraMap_eq F (F ⊗[k] K) Q).symm
  have hright : i.comp Algebra.TensorProduct.includeRight = IsScalarTower.toAlgHom k K Q := by
    apply AlgHom.toRingHom_injective
    exact (IsScalarTower.algebraMap_eq K (F ⊗[k] K) Q).symm
  simpa only [← AlgHom.range_comp, hleft, hright] using H.symm

end LinearDisjoint

section Ext

variable (k : Type*) {A K Q R : Type*} [CommSemiring k] [CommRing A] [CommRing K] [CommRing Q]
  [CommRing R] [Algebra k A] [Algebra k K] [Algebra (A ⊗[k] K) Q] [Algebra A Q] [Algebra K Q]
  [IsScalarTower A (A ⊗[k] K) Q] [IsScalarTower K (A ⊗[k] K) Q]
  [IsFractionRing (A ⊗[k] K) Q]

include k in
/-- Two ring homomorphisms out of a total ring of fractions of `A ⊗[k] K` are equal as soon as
they agree on the images of `A` and `K`. -/
theorem ringHom_ext_of_isFractionRing_tensorProduct {φ₁ φ₂ : Q →+* R}
    (hA : ∀ a : A, φ₁ (algebraMap A Q a) = φ₂ (algebraMap A Q a))
    (hK : ∀ c : K, φ₁ (algebraMap K Q c) = φ₂ (algebraMap K Q c)) : φ₁ = φ₂ := by
  refine IsLocalization.ringHom_ext (nonZeroDivisors (A ⊗[k] K)) ?_
  refine Algebra.TensorProduct.ringHom_ext ?_ ?_
  · ext a
    have ha : algebraMap (A ⊗[k] K) Q (a ⊗ₜ[k] (1 : K)) = algebraMap A Q a :=
      (IsScalarTower.algebraMap_apply A (A ⊗[k] K) Q a).symm
    simpa [ha] using hA a
  · ext c
    have hc : algebraMap (A ⊗[k] K) Q ((1 : A) ⊗ₜ[k] c) = algebraMap K Q c :=
      (IsScalarTower.algebraMap_apply K (A ⊗[k] K) Q c).symm
    simpa [hc] using hK c

include k in
/-- Two `K`-algebra homomorphisms out of a total ring of fractions of `A ⊗[k] K` are equal as soon
as they agree on the image of `A`. -/
theorem algHom_ext_of_isFractionRing_tensorProduct [Algebra K R] {φ₁ φ₂ : Q →ₐ[K] R}
    (hA : ∀ a : A, φ₁ (algebraMap A Q a) = φ₂ (algebraMap A Q a)) : φ₁ = φ₂ :=
  AlgHom.toRingHom_injective <|
    ringHom_ext_of_isFractionRing_tensorProduct k hA fun c : K ↦ by simp

end Ext

end TauCeti

namespace AlgHom

attribute [local instance] Algebra.TensorProduct.rightAlgebra
  Algebra.TensorProduct.right_isScalarTower

section FractionRingTensorMap

variable {k A B C : Type*} [CommSemiring k] [CommRing A] [CommRing B] [CommRing C]
  [Algebra k A] [Algebra k B] [Algebra k C]

/-- When `K` is flat over `k` and `Q₂` has no zero divisors, the base change
`f ⊗ id : A ⊗[k] K → B ⊗[k] K` of an injective `f : A →ₐ[k] B` carries non-zero-divisors
to non-zero-divisors. -/
private theorem nonZeroDivisors_le_comap_map_tensorProduct {f : A →ₐ[k] B}
    (hf : Function.Injective f) (K Q₂ : Type*) [CommRing K] [Algebra k K] [Module.Flat k K]
    [CommRing Q₂] [NoZeroDivisors Q₂] [Algebra (B ⊗[k] K) Q₂] [IsFractionRing (B ⊗[k] K) Q₂] :
    nonZeroDivisors (A ⊗[k] K) ≤ (nonZeroDivisors (B ⊗[k] K)).comap
      (Algebra.TensorProduct.map f (AlgHom.id k K) : A ⊗[k] K →+* B ⊗[k] K) := by
  have : NoZeroDivisors (B ⊗[k] K) :=
    (IsFractionRing.injective (B ⊗[k] K) Q₂).noZeroDivisors _ (map_zero _) (map_mul _)
  exact nonZeroDivisors_le_comap_nonZeroDivisors_of_injective _
    (Module.Flat.rTensor_preserves_injective_linearMap f.toLinearMap hf)

/-- The `K`-algebra homomorphism `Q₁ →ₐ[K] Q₂` between specified total rings of fractions of
`A ⊗[k] K` and `B ⊗[k] K` induced by an injective `k`-algebra map `f : A →ₐ[k] B`, when `K` is flat
over `k` (in particular, whenever `k` is a field) and `Q₂` has no zero divisors (for instance, a
fraction field). -/
noncomputable def fractionRingTensorMap (f : A →ₐ[k] B) (hf : Function.Injective f)
    (K Q₁ Q₂ : Type*) [CommRing K] [Algebra k K] [Module.Flat k K] [CommRing Q₁] [CommRing Q₂]
    [NoZeroDivisors Q₂] [Algebra (A ⊗[k] K) Q₁] [Algebra K Q₁]
    [IsScalarTower K (A ⊗[k] K) Q₁] [IsFractionRing (A ⊗[k] K) Q₁]
    [Algebra (B ⊗[k] K) Q₂] [Algebra K Q₂]
    [IsScalarTower K (B ⊗[k] K) Q₂] [IsFractionRing (B ⊗[k] K) Q₂] : Q₁ →ₐ[K] Q₂ where
  toRingHom := IsLocalization.map Q₂
    (Algebra.TensorProduct.map f (AlgHom.id k K) : A ⊗[k] K →+* B ⊗[k] K)
    (nonZeroDivisors_le_comap_map_tensorProduct hf K Q₂)
  commutes' c := by
    simp [IsScalarTower.algebraMap_apply K (A ⊗[k] K) Q₁,
      IsScalarTower.algebraMap_apply K (B ⊗[k] K) Q₂, Algebra.TensorProduct.right_algebraMap_apply]

section Basic

variable (f : A →ₐ[k] B) (hf : Function.Injective f) (K Q₁ Q₂ : Type*)
  [CommRing K] [Algebra k K] [Module.Flat k K] [CommRing Q₁] [CommRing Q₂] [NoZeroDivisors Q₂]
  [Algebra (A ⊗[k] K) Q₁] [Algebra K Q₁]
  [IsScalarTower K (A ⊗[k] K) Q₁] [IsFractionRing (A ⊗[k] K) Q₁]
  [Algebra (B ⊗[k] K) Q₂] [Algebra K Q₂]
  [IsScalarTower K (B ⊗[k] K) Q₂] [IsFractionRing (B ⊗[k] K) Q₂]

/-- On the tensor product `A ⊗[k] K`, the induced fraction-field map agrees with `f ⊗ id`. -/
@[simp]
theorem fractionRingTensorMap_algebraMap_tensorProduct (z : A ⊗[k] K) :
    f.fractionRingTensorMap hf K Q₁ Q₂ (algebraMap (A ⊗[k] K) Q₁ z) =
      algebraMap (B ⊗[k] K) Q₂ (Algebra.TensorProduct.map f (AlgHom.id k K) z) :=
  IsLocalization.map_eq (nonZeroDivisors_le_comap_map_tensorProduct hf K Q₂) z

/-- The induced map on total rings of fractions of tensor products is injective. -/
theorem fractionRingTensorMap_injective :
    Function.Injective (f.fractionRingTensorMap hf K Q₁ Q₂) :=
  IsLocalization.map_injective_of_injective_of_le_nonZeroDivisors Q₁ Q₂
    (Module.Flat.rTensor_preserves_injective_linearMap f.toLinearMap hf)
    (nonZeroDivisors_le_comap_map_tensorProduct hf K Q₂) le_rfl

section LeftFactor

variable [Algebra A Q₁] [Algebra B Q₂]
  [IsScalarTower A (A ⊗[k] K) Q₁] [IsScalarTower B (B ⊗[k] K) Q₂]

/-- On the left factor `A`, the induced fraction-field map restricts to `f`. -/
@[simp]
theorem fractionRingTensorMap_algebraMap_left (a : A) :
    f.fractionRingTensorMap hf K Q₁ Q₂ (algebraMap A Q₁ a) = algebraMap B Q₂ (f a) := by
  rw [IsScalarTower.algebraMap_apply A (A ⊗[k] K) Q₁,
    fractionRingTensorMap_algebraMap_tensorProduct]
  exact (IsScalarTower.algebraMap_apply B (B ⊗[k] K) Q₂ (f a)).symm

omit [Algebra A Q₁] [IsScalarTower A (A ⊗[k] K) Q₁] in
/-- On the image of a pure tensor `a ⊗ c`, the induced fraction-field map gives `f a * c`. -/
theorem fractionRingTensorMap_algebraMap_tmul (a : A) (c : K) :
    f.fractionRingTensorMap hf K Q₁ Q₂ (algebraMap (A ⊗[k] K) Q₁ (a ⊗ₜ[k] c)) =
      algebraMap B Q₂ (f a) * algebraMap K Q₂ c := by
  rw [fractionRingTensorMap_algebraMap_tensorProduct, Algebra.TensorProduct.map_tmul,
    AlgHom.id_apply, IsScalarTower.algebraMap_apply B (B ⊗[k] K) Q₂,
    IsScalarTower.algebraMap_apply K (B ⊗[k] K) Q₂, ← map_mul]
  simp [Algebra.TensorProduct.right_algebraMap_apply]

/-- The induced fraction-field map forms a commuting square with the `k`-algebra scalar maps from
`A` and `B`. -/
theorem fractionRingTensorMap_comp_toAlgHom_left [Algebra k Q₁] [Algebra k Q₂]
    [IsScalarTower k A Q₁] [IsScalarTower k K Q₁] [IsScalarTower k B Q₂] [IsScalarTower k K Q₂] :
    ((f.fractionRingTensorMap hf K Q₁ Q₂).restrictScalars k).comp (IsScalarTower.toAlgHom k A Q₁) =
      (IsScalarTower.toAlgHom k B Q₂).comp f := by
  ext a
  exact f.fractionRingTensorMap_algebraMap_left hf K Q₁ Q₂ a

/-- **Uniqueness of the induced fraction-field map (`K`-algebra form)**: a `K`-algebra map
`φ : Q₁ →ₐ[K] Q₂` equals `f.fractionRingTensorMap hf K Q₁ Q₂` if and only if it extends `f` along
the specified embeddings of `A` and `B`. -/
theorem eq_fractionRingTensorMap_iff {φ : Q₁ →ₐ[K] Q₂} :
    φ = f.fractionRingTensorMap hf K Q₁ Q₂ ↔
      ∀ a : A, φ (algebraMap A Q₁ a) = algebraMap B Q₂ (f a) :=
  ⟨fun h a ↦ h ▸ f.fractionRingTensorMap_algebraMap_left hf K Q₁ Q₂ a, fun h ↦
    TauCeti.algHom_ext_of_isFractionRing_tensorProduct k fun a ↦
      (h a).trans (f.fractionRingTensorMap_algebraMap_left hf K Q₁ Q₂ a).symm⟩

/-- **Uniqueness of the induced fraction-field map (ring-homomorphism form)**: a ring homomorphism
`φ : Q₁ →+* Q₂` extending `f` on `A` and fixing `K` is `f.fractionRingTensorMap hf K Q₁ Q₂`. -/
theorem eq_coe_fractionRingTensorMap_of_algebraMap {φ : Q₁ →+* Q₂}
    (hA : ∀ a : A, φ (algebraMap A Q₁ a) = algebraMap B Q₂ (f a))
    (hK : ∀ c : K, φ (algebraMap K Q₁ c) = algebraMap K Q₂ c) :
    φ = (f.fractionRingTensorMap hf K Q₁ Q₂ : Q₁ →+* Q₂) :=
  TauCeti.ringHom_ext_of_isFractionRing_tensorProduct k
    (fun a ↦ (hA a).trans (f.fractionRingTensorMap_algebraMap_left hf K Q₁ Q₂ a).symm)
    (fun c ↦ (hK c).trans ((f.fractionRingTensorMap hf K Q₁ Q₂).commutes c).symm)

end LeftFactor

end Basic

/-- The fraction-field map induced by the identity `AlgHom.id k A` is `AlgHom.id K Q₁`. -/
@[simp]
theorem fractionRingTensorMap_id (k A K Q₁ : Type*) [CommSemiring k] [CommRing A] [CommRing K]
    [CommRing Q₁] [NoZeroDivisors Q₁] [Algebra k A] [Algebra k K] [Module.Flat k K]
    [Algebra (A ⊗[k] K) Q₁] [Algebra K Q₁]
    [IsScalarTower K (A ⊗[k] K) Q₁] [IsFractionRing (A ⊗[k] K) Q₁]
    (hid : Function.Injective (AlgHom.id k A) := fun _ _ h ↦ h) :
    (AlgHom.id k A).fractionRingTensorMap hid K Q₁ Q₁ = AlgHom.id K Q₁ := by
  refine AlgHom.toRingHom_injective <|
    IsLocalization.ringHom_ext (nonZeroDivisors (A ⊗[k] K)) <| RingHom.ext fun z ↦ ?_
  simp

/-- Functoriality of `AlgHom.fractionRingTensorMap` with respect to composition. -/
theorem fractionRingTensorMap_comp (f : A →ₐ[k] B) (hf : Function.Injective f)
    (g : B →ₐ[k] C) (hg : Function.Injective g) (K Q₁ Q₂ Q₃ : Type*)
    [CommRing K] [Algebra k K] [Module.Flat k K] [CommRing Q₁] [CommRing Q₂] [NoZeroDivisors Q₂]
    [CommRing Q₃] [NoZeroDivisors Q₃]
    [Algebra (A ⊗[k] K) Q₁] [Algebra K Q₁]
    [IsScalarTower K (A ⊗[k] K) Q₁] [IsFractionRing (A ⊗[k] K) Q₁]
    [Algebra (B ⊗[k] K) Q₂] [Algebra K Q₂]
    [IsScalarTower K (B ⊗[k] K) Q₂] [IsFractionRing (B ⊗[k] K) Q₂]
    [Algebra (C ⊗[k] K) Q₃] [Algebra K Q₃]
    [IsScalarTower K (C ⊗[k] K) Q₃] [IsFractionRing (C ⊗[k] K) Q₃]
    (hcomp : Function.Injective (g.comp f) := fun _ _ h ↦ hf (hg h)) :
    (g.comp f).fractionRingTensorMap hcomp K Q₁ Q₃ =
      (g.fractionRingTensorMap hg K Q₂ Q₃).comp (f.fractionRingTensorMap hf K Q₁ Q₂) := by
  refine AlgHom.toRingHom_injective <|
    IsLocalization.ringHom_ext (nonZeroDivisors (A ⊗[k] K)) <| RingHom.ext fun z ↦ ?_
  refine TensorProduct.inductionOn z (fun a c ↦ by simp) fun x y hx hy ↦ ?_
  simp only [RingHom.comp_apply, map_add] at hx hy ⊢
  rw [hx, hy]

/-- Elementwise composition law for `AlgHom.fractionRingTensorMap`. -/
theorem fractionRingTensorMap_comp_apply (f : A →ₐ[k] B) (hf : Function.Injective f)
    (g : B →ₐ[k] C) (hg : Function.Injective g) (K Q₁ Q₂ Q₃ : Type*)
    [CommRing K] [Algebra k K] [Module.Flat k K] [CommRing Q₁] [CommRing Q₂] [NoZeroDivisors Q₂]
    [CommRing Q₃] [NoZeroDivisors Q₃]
    [Algebra (A ⊗[k] K) Q₁] [Algebra K Q₁]
    [IsScalarTower K (A ⊗[k] K) Q₁] [IsFractionRing (A ⊗[k] K) Q₁]
    [Algebra (B ⊗[k] K) Q₂] [Algebra K Q₂]
    [IsScalarTower K (B ⊗[k] K) Q₂] [IsFractionRing (B ⊗[k] K) Q₂]
    [Algebra (C ⊗[k] K) Q₃] [Algebra K Q₃]
    [IsScalarTower K (C ⊗[k] K) Q₃] [IsFractionRing (C ⊗[k] K) Q₃]
    (hcomp : Function.Injective (g.comp f) := fun _ _ h ↦ hf (hg h)) (x : Q₁) :
    (g.comp f).fractionRingTensorMap hcomp K Q₁ Q₃ x =
      g.fractionRingTensorMap hg K Q₂ Q₃ (f.fractionRingTensorMap hf K Q₁ Q₂ x) := by
  rw [fractionRingTensorMap_comp f hf g hg K Q₁ Q₂ Q₃ hcomp, AlgHom.comp_apply]

end FractionRingTensorMap

end AlgHom

namespace AlgEquiv

attribute [local instance] Algebra.TensorProduct.rightAlgebra
  Algebra.TensorProduct.right_isScalarTower

variable {k A B C : Type*} [CommSemiring k] [CommRing A] [CommRing B] [CommRing C]
  [Algebra k A] [Algebra k B] [Algebra k C]

/-- The `K`-algebra equivalence `Q₁ ≃ₐ[K] Q₂` between specified total rings of fractions of
`A ⊗[k] K` and `B ⊗[k] K` induced by a `k`-algebra equivalence `e : A ≃ₐ[k] B`. -/
noncomputable def fractionRingTensorCongr (e : A ≃ₐ[k] B) (K Q₁ Q₂ : Type*)
    [CommRing K] [Algebra k K] [CommRing Q₁] [CommRing Q₂]
    [Algebra (A ⊗[k] K) Q₁] [Algebra K Q₁]
    [IsScalarTower K (A ⊗[k] K) Q₁] [IsFractionRing (A ⊗[k] K) Q₁]
    [Algebra (B ⊗[k] K) Q₂] [Algebra K Q₂]
    [IsScalarTower K (B ⊗[k] K) Q₂] [IsFractionRing (B ⊗[k] K) Q₂] : Q₁ ≃ₐ[K] Q₂ :=
  let congrK : A ⊗[k] K ≃ₐ[K] B ⊗[k] K :=
    { Algebra.TensorProduct.congr e (AlgEquiv.refl : K ≃ₐ[k] K) with
      commutes' := fun c ↦ by simp [Algebra.TensorProduct.right_algebraMap_apply] }
  IsFractionRing.algEquivOfAlgEquiv congrK

section Basic

variable (e : A ≃ₐ[k] B) (K Q₁ Q₂ : Type*)
  [CommRing K] [Algebra k K] [CommRing Q₁] [CommRing Q₂]
  [Algebra (A ⊗[k] K) Q₁] [Algebra K Q₁]
  [IsScalarTower K (A ⊗[k] K) Q₁] [IsFractionRing (A ⊗[k] K) Q₁]
  [Algebra (B ⊗[k] K) Q₂] [Algebra K Q₂]
  [IsScalarTower K (B ⊗[k] K) Q₂] [IsFractionRing (B ⊗[k] K) Q₂]

/-- On `A ⊗[k] K`, `AlgEquiv.fractionRingTensorCongr` agrees with `e ⊗ id`. -/
@[simp]
theorem fractionRingTensorCongr_algebraMap_tensorProduct (z : A ⊗[k] K) :
    e.fractionRingTensorCongr K Q₁ Q₂ (algebraMap (A ⊗[k] K) Q₁ z) =
      algebraMap (B ⊗[k] K) Q₂ (Algebra.TensorProduct.congr e (AlgEquiv.refl : K ≃ₐ[k] K) z) := by
  simp [fractionRingTensorCongr]

/-- On the left factor `A`, `AlgEquiv.fractionRingTensorCongr` restricts to `e`. -/
@[simp]
theorem fractionRingTensorCongr_algebraMap_left [Algebra A Q₁] [Algebra B Q₂]
    [IsScalarTower A (A ⊗[k] K) Q₁] [IsScalarTower B (B ⊗[k] K) Q₂] (a : A) :
    e.fractionRingTensorCongr K Q₁ Q₂ (algebraMap A Q₁ a) = algebraMap B Q₂ (e a) := by
  rw [IsScalarTower.algebraMap_apply A (A ⊗[k] K) Q₁,
    fractionRingTensorCongr_algebraMap_tensorProduct]
  exact (IsScalarTower.algebraMap_apply B (B ⊗[k] K) Q₂ (e a)).symm

/-- When `K` is flat over `k` and `Q₂` is a field, `AlgEquiv.fractionRingTensorCongr` has the same
underlying `K`-algebra homomorphism as `AlgHom.fractionRingTensorMap`. -/
theorem toAlgHom_fractionRingTensorCongr {Q₂ : Type*} [CommRing Q₂] [NoZeroDivisors Q₂]
    [Module.Flat k K]
    [Algebra (B ⊗[k] K) Q₂] [Algebra K Q₂]
    [IsScalarTower K (B ⊗[k] K) Q₂] [IsFractionRing (B ⊗[k] K) Q₂]
    (he : Function.Injective (e : A →ₐ[k] B) := fun _ _ h ↦ e.injective h) :
    (e.fractionRingTensorCongr K Q₁ Q₂).toAlgHom =
      (e : A →ₐ[k] B).fractionRingTensorMap he K Q₁ Q₂ := by
  refine AlgHom.toRingHom_injective <|
    IsLocalization.ringHom_ext (nonZeroDivisors (A ⊗[k] K)) <| RingHom.ext fun z ↦ ?_
  simp

end Basic

/-- `AlgEquiv.fractionRingTensorCongr` sends the identity equivalence to `AlgEquiv.refl`. -/
@[simp]
theorem fractionRingTensorCongr_refl (k A K Q₁ : Type*) [CommSemiring k] [CommRing A] [CommRing K]
    [CommRing Q₁] [Algebra k A] [Algebra k K] [Algebra (A ⊗[k] K) Q₁] [Algebra K Q₁]
    [IsScalarTower K (A ⊗[k] K) Q₁] [IsFractionRing (A ⊗[k] K) Q₁] :
    (AlgEquiv.refl : A ≃ₐ[k] A).fractionRingTensorCongr K Q₁ Q₁ = AlgEquiv.refl := by
  refine AlgEquiv.coe_toAlgHom_injective <| AlgHom.toRingHom_injective <|
    IsLocalization.ringHom_ext (nonZeroDivisors (A ⊗[k] K)) ?_
  refine Algebra.TensorProduct.ringHom_ext (by ext; simp) (by ext; simp)

/-- `AlgEquiv.fractionRingTensorCongr` commutes with composition of equivalences. -/
theorem fractionRingTensorCongr_trans (e₁ : A ≃ₐ[k] B) (e₂ : B ≃ₐ[k] C) (K Q₁ Q₂ Q₃ : Type*)
    [CommRing K] [Algebra k K] [CommRing Q₁] [CommRing Q₂] [CommRing Q₃]
    [Algebra (A ⊗[k] K) Q₁] [Algebra K Q₁]
    [IsScalarTower K (A ⊗[k] K) Q₁] [IsFractionRing (A ⊗[k] K) Q₁]
    [Algebra (B ⊗[k] K) Q₂] [Algebra K Q₂]
    [IsScalarTower K (B ⊗[k] K) Q₂] [IsFractionRing (B ⊗[k] K) Q₂]
    [Algebra (C ⊗[k] K) Q₃] [Algebra K Q₃]
    [IsScalarTower K (C ⊗[k] K) Q₃] [IsFractionRing (C ⊗[k] K) Q₃] :
    (e₁.trans e₂).fractionRingTensorCongr K Q₁ Q₃ =
      (e₁.fractionRingTensorCongr K Q₁ Q₂).trans (e₂.fractionRingTensorCongr K Q₂ Q₃) := by
  refine AlgEquiv.coe_toAlgHom_injective <| AlgHom.toRingHom_injective <|
    IsLocalization.ringHom_ext (nonZeroDivisors (A ⊗[k] K)) ?_
  refine Algebra.TensorProduct.ringHom_ext (by ext; simp) (by ext; simp)

/-- The inverse of `e.fractionRingTensorCongr` is `e.symm.fractionRingTensorCongr`. -/
@[simp]
theorem fractionRingTensorCongr_symm (e : A ≃ₐ[k] B) (K Q₁ Q₂ : Type*)
    [CommRing K] [Algebra k K] [CommRing Q₁] [CommRing Q₂]
    [Algebra (A ⊗[k] K) Q₁] [Algebra K Q₁]
    [IsScalarTower K (A ⊗[k] K) Q₁] [IsFractionRing (A ⊗[k] K) Q₁]
    [Algebra (B ⊗[k] K) Q₂] [Algebra K Q₂]
    [IsScalarTower K (B ⊗[k] K) Q₂] [IsFractionRing (B ⊗[k] K) Q₂] :
    (e.fractionRingTensorCongr K Q₁ Q₂).symm = e.symm.fractionRingTensorCongr K Q₂ Q₁ := by
  ext x
  rw [AlgEquiv.symm_apply_eq, ← AlgEquiv.trans_apply,
    ← fractionRingTensorCongr_trans e.symm e K Q₂ Q₁ Q₂, AlgEquiv.symm_trans_self,
    fractionRingTensorCongr_refl]
  rfl

end AlgEquiv

namespace TauCeti

section FieldSource

variable {k E B : Type*} (K : Type*) [CommSemiring k] [DivisionRing E] [CommRing B] [CommRing K]
  [Algebra k E] [Algebra k B] [Algebra k K]

/-- When `E` is a division ring (in particular a field) and a total ring of fractions `Q` of
`B ⊗[k] K` is nontrivial, `B` is nontrivial and every `k`-algebra map `E →ₐ[k] B` is injective, so
it induces `AlgHom.fractionRingTensorMap` without a separate injectivity hypothesis. -/
theorem injective_of_isFractionRing_tensorProduct (Q : Type*) [CommRing Q] [Nontrivial Q]
    [Algebra (B ⊗[k] K) Q] [IsFractionRing (B ⊗[k] K) Q] (f : E →ₐ[k] B) :
    Function.Injective f := by
  have : Nontrivial (B ⊗[k] K) :=
    (IsFractionRing.nontrivial_iff_nontrivial (B ⊗[k] K) Q).mpr inferInstance
  have : Nontrivial B :=
    (Algebra.TensorProduct.includeLeftRingHom : B →+* B ⊗[k] K).domain_nontrivial
  rw [← AlgHom.coe_toRingHom]
  exact (f : E →+* B).injective

end FieldSource

section Comm

attribute [local instance] Algebra.TensorProduct.rightAlgebra
  Algebra.TensorProduct.right_isScalarTower

variable (k A K : Type*) [CommSemiring k] [CommRing A] [CommRing K] [Algebra k A] [Algebra k K]
  (Q₁ Q₂ : Type*) [CommRing Q₁] [Algebra (A ⊗[k] K) Q₁] [Algebra K Q₁]
  [IsScalarTower K (A ⊗[k] K) Q₁] [IsFractionRing (A ⊗[k] K) Q₁]
  [CommRing Q₂] [Algebra (K ⊗[k] A) Q₂] [Algebra K Q₂]
  [IsScalarTower K (K ⊗[k] A) Q₂] [IsFractionRing (K ⊗[k] A) Q₂]

/-- **Commutativity of tensor factors on total rings of fractions.** Any specified total ring of
fractions `Q₁` of `A ⊗[k] K` (with the right `K`-algebra structure) is canonically isomorphic as a
`K`-algebra to any specified total ring of fractions `Q₂` of `K ⊗[k] A` (with the left `K`-algebra
structure), compatibly with the scalar maps from `A` and `K`. -/
noncomputable def fractionRingTensorCommAlgEquiv : Q₁ ≃ₐ[K] Q₂ :=
  IsFractionRing.algEquivOfAlgEquiv (Algebra.TensorProduct.commRight k K A).symm

/-- `TauCeti.fractionRingTensorCommAlgEquiv` swaps pure tensors on the image of `A ⊗[k] K`. -/
@[simp]
theorem fractionRingTensorCommAlgEquiv_algebraMap_tensorProduct (x : A ⊗[k] K) :
    fractionRingTensorCommAlgEquiv k A K Q₁ Q₂ (algebraMap (A ⊗[k] K) Q₁ x) =
      algebraMap (K ⊗[k] A) Q₂ ((Algebra.TensorProduct.comm k K A).symm x) := by
  rw [fractionRingTensorCommAlgEquiv, IsFractionRing.algEquivOfAlgEquiv_algebraMap]
  apply congrArg (algebraMap (K ⊗[k] A) Q₂)
  exact TensorProduct.inductionOn x (fun _ _ ↦ by simp) (fun _ _ hx hy ↦ by simp [map_add, hx, hy])

/-- The inverse of `TauCeti.fractionRingTensorCommAlgEquiv` swaps pure tensors on `K ⊗[k] A`. -/
@[simp]
theorem fractionRingTensorCommAlgEquiv_symm_algebraMap_tensorProduct (x : K ⊗[k] A) :
    (fractionRingTensorCommAlgEquiv k A K Q₁ Q₂).symm (algebraMap (K ⊗[k] A) Q₂ x) =
      algebraMap (A ⊗[k] K) Q₁ (Algebra.TensorProduct.comm k K A x) :=
  (fractionRingTensorCommAlgEquiv k A K Q₁ Q₂).injective (by simp)

variable [Algebra A Q₁] [IsScalarTower A (A ⊗[k] K) Q₁] [Algebra A Q₂]
  [IsScalarTower A (K ⊗[k] A) Q₂]

/-- `TauCeti.fractionRingTensorCommAlgEquiv` commutes with the canonical maps from `A`. -/
@[simp]
theorem fractionRingTensorCommAlgEquiv_algebraMap_left (a : A) :
    fractionRingTensorCommAlgEquiv k A K Q₁ Q₂ (algebraMap A Q₁ a) = algebraMap A Q₂ a := by
  simp [IsScalarTower.algebraMap_apply A (A ⊗[k] K) Q₁,
    IsScalarTower.algebraMap_apply A (K ⊗[k] A) Q₂, Algebra.TensorProduct.right_algebraMap_apply]

/-- The inverse of `TauCeti.fractionRingTensorCommAlgEquiv` commutes with the canonical maps from
`A`. -/
@[simp]
theorem fractionRingTensorCommAlgEquiv_symm_algebraMap_right (a : A) :
    (fractionRingTensorCommAlgEquiv k A K Q₁ Q₂).symm (algebraMap A Q₂ a) = algebraMap A Q₁ a :=
  (fractionRingTensorCommAlgEquiv k A K Q₁ Q₂).injective (by simp)

end Comm

section BaseLocalization

variable {k A F K : Type*} [CommRing k] [CommRing A] [CommRing F] [CommRing K]
  [Algebra k A] [Algebra k F] [Algebra A F] [IsScalarTower k A F] [Algebra k K]

/-- The `A ⊗[k] K`-algebra structure on `F ⊗[k] K` induced by `algebraMap A F ⊗ id`. -/
@[instance_reducible]
private noncomputable def baseTensorAlgebra : Algebra (A ⊗[k] K) (F ⊗[k] K) :=
  (Algebra.TensorProduct.map (IsScalarTower.toAlgHom k A F) (AlgHom.id k K)).toRingHom.toAlgebra

attribute [local instance] baseTensorAlgebra

private theorem algebraMap_baseTensorAlgebra_eq :
    algebraMap (A ⊗[k] K) (F ⊗[k] K) =
      (Algebra.TensorProduct.map (IsScalarTower.toAlgHom k A F) (AlgHom.id k K)).toRingHom :=
  rfl

/-- `F ⊗[k] K` is the localization of `A ⊗[k] K` at the image of `nonZeroDivisors A`. -/
private theorem isLocalization_baseTensorAlgebra [IsFractionRing A F] :
    IsLocalization (Algebra.algebraMapSubmonoid (A ⊗[k] K) (nonZeroDivisors A)) (F ⊗[k] K) := by
  have : IsScalarTower A (A ⊗[k] K) (F ⊗[k] K) := .of_algebraMap_eq fun a ↦ by
    simp [algebraMap_baseTensorAlgebra_eq]
  exact _root_.IsLocalization.tensorProduct_tensorProduct k K (nonZeroDivisors A) F
    (by ext; simp [algebraMap_baseTensorAlgebra_eq])

variable {Q : Type*} [CommRing Q] [Algebra (A ⊗[k] K) Q] [Algebra (F ⊗[k] K) Q]

/-- Elementwise compatibility on pure tensors implies `algebraMap (A ⊗[k] K) Q` factors through
`F ⊗[k] K`. -/
private theorem algebraMap_eq_comp_baseTensorAlgebra
    (hmap : ∀ (a : A) (c : K),
      algebraMap (A ⊗[k] K) Q (a ⊗ₜ c) = algebraMap (F ⊗[k] K) Q (algebraMap A F a ⊗ₜ c)) :
    algebraMap (A ⊗[k] K) Q =
      (algebraMap (F ⊗[k] K) Q).comp (algebraMap (A ⊗[k] K) (F ⊗[k] K)) :=
  Algebra.TensorProduct.ringHom_ext
    (RingHom.ext fun a ↦ by simpa [algebraMap_baseTensorAlgebra_eq] using hmap a 1)
    (RingHom.ext fun c ↦ by simpa [algebraMap_baseTensorAlgebra_eq] using hmap 1 c)

variable [IsFractionRing A F]

/-- **A fraction ring of `F ⊗[k] K` is a fraction ring of `A ⊗[k] K`.** If `F` is a total ring of
fractions of a `k`-algebra `A`, `K` is flat over `k`, and `Q` (without zero divisors, for instance
a field) is a total ring of fractions of a nontrivial `F ⊗[k] K`, then `Q` is also a total ring of
fractions of `A ⊗[k] K` along the composite map `A ⊗[k] K → F ⊗[k] K → Q`. Unlike
`TauCeti.isFractionRing_tensorProduct_of_constantCompositum_eq_top`, `K / k` need not be
algebraic. -/
theorem isFractionRing_base_tensorProduct_of_isFractionRing_tensorProduct
    [Module.Flat k K] [Nontrivial (F ⊗[k] K)] [NoZeroDivisors Q] [IsFractionRing (F ⊗[k] K) Q]
    (hmap : ∀ (a : A) (c : K),
      algebraMap (A ⊗[k] K) Q (a ⊗ₜ c) = algebraMap (F ⊗[k] K) Q (algebraMap A F a ⊗ₜ c)) :
    IsFractionRing (A ⊗[k] K) Q := by
  have hcomp := algebraMap_eq_comp_baseTensorAlgebra hmap
  -- `A ⊗[k] K → F ⊗[k] K` is injective by flatness of `K`, so `A ⊗[k] K` embeds into `Q`.
  have hρ : Function.Injective (algebraMap (A ⊗[k] K) (F ⊗[k] K)) :=
    Module.Flat.rTensor_preserves_injective_linearMap (IsScalarTower.toAlgHom k A F).toLinearMap
      (_root_.IsFractionRing.injective A F)
  have hinj : Function.Injective (algebraMap (A ⊗[k] K) Q) :=
    hcomp ▸ (_root_.IsFractionRing.injective (F ⊗[k] K) Q).comp hρ
  have : NoZeroDivisors (A ⊗[k] K) := hinj.noZeroDivisors _ (map_zero _) (map_mul _)
  have := isLocalization_baseTensorAlgebra (k := k) (A := A) (F := F) (K := K)
  have : IsScalarTower (A ⊗[k] K) (F ⊗[k] K) Q := .of_algebraMap_eq fun x ↦ congr($hcomp x)
  exact IsFractionRing.of_isLocalization_of_isFractionRing
    (Algebra.algebraMapSubmonoid (A ⊗[k] K) (nonZeroDivisors A)) (F ⊗[k] K) Q
    (IsLocalization.le_nonZeroDivisors_of_nontrivial _ (F ⊗[k] K))

/-- **A fraction ring of a domain `A ⊗[k] K` is a fraction ring of `F ⊗[k] K`.** Converse to
`TauCeti.isFractionRing_base_tensorProduct_of_isFractionRing_tensorProduct`, if `F` is a total
ring of fractions of `A` and `Q` is a fraction ring of a domain `A ⊗[k] K` compatibly with an
`F ⊗[k] K`-algebra structure on `Q`, then `Q` is a fraction ring of `F ⊗[k] K`. -/
theorem isFractionRing_tensorProduct_of_isFractionRing_base_tensorProduct
    [IsDomain (A ⊗[k] K)] [IsFractionRing (A ⊗[k] K) Q]
    (hmap : ∀ (a : A) (c : K),
      algebraMap (A ⊗[k] K) Q (a ⊗ₜ c) = algebraMap (F ⊗[k] K) Q (algebraMap A F a ⊗ₜ c)) :
    IsFractionRing (F ⊗[k] K) Q := by
  have hcomp := algebraMap_eq_comp_baseTensorAlgebra hmap
  have := isLocalization_baseTensorAlgebra (k := k) (A := A) (F := F) (K := K)
  have : IsScalarTower (A ⊗[k] K) (F ⊗[k] K) Q := .of_algebraMap_eq fun x ↦ congr($hcomp x)
  exact _root_.IsFractionRing.isFractionRing_of_isDomain_of_isLocalization
    (Algebra.algebraMapSubmonoid (A ⊗[k] K) (nonZeroDivisors A)) (F ⊗[k] K) Q

end BaseLocalization

end TauCeti
