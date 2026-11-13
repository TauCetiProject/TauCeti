/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.FieldTheory.LinearDisjoint
public import TauCeti.RingTheory.Localization.FractionRing
import Mathlib.RingTheory.Flat.Basic

/-!
# The fraction field of a tensor product of fields

If `F ⊗[k] K` is a domain, its fraction field is a compositum of the two factors,
with linearly disjoint images. Unlike the existential construction
`IntermediateField.LinearDisjoint.exists_field_of_isDomain`, these statements retain
an arbitrary specified fraction field and its scalar maps. This is useful when the
same fraction field must also be compared with localizations or geometric base change.

When `K` is flat over `k` (in particular when `k` is a field), an injective `k`-algebra map
`f : A →ₐ[k] B` induces an injective `K`-algebra map between any specified total quotient rings
`QA` of `A ⊗[k] K` and `QB` of `B ⊗[k] K` once `QB` has no zero divisors, characterized uniquely
by its restriction to `A` and `K`. When the source `E` is a field and `QB` is a domain, injectivity
of `f : E →ₐ[k] B` is automatic. Isomorphisms of the left factor and permutation of the two
tensor factors (`A ⊗[k] K` versus `K ⊗[k] A`) induce `K`-algebra isomorphisms of arbitrary total
quotient rings with no flatness or domain assumption.

The right-factor algebra is Mathlib's `Algebra.TensorProduct.rightAlgebra`, installed
locally together with `right_isScalarTower`; all maps to the fraction field are the
usual scalar-tower maps. The linear-disjointness argument follows Jz Pan's
`Subalgebra.LinearDisjoint.exists_field_of_isDomain_of_injective` in Mathlib,
using `Subalgebra.LinearDisjoint.include_range` and transport along the fraction map.

## Main definitions and results

* `TauCeti.adjoin_range_right_eq_top_of_isFractionRing_tensorProduct` and
  `TauCeti.linearDisjoint_of_isFractionRing_tensorProduct`: a fraction field of `F ⊗[k] K` is a
  linearly disjoint compositum of `F` and `K`.
* `TauCeti.fractionRingTensorMapAlgHom` and `TauCeti.fractionRingTensorFieldMapAlgHom`: the
  `K`-algebra homomorphism on fraction rings induced by an injective `k`-algebra map on the left
  factor (automatic when the source is a field), together with its injectivity, functoriality, and
  uniqueness (`TauCeti.eq_fractionRingTensorMapAlgHom_of_apply_algebraMap`).
* `TauCeti.fractionRingTensorCongrAlgEquiv` and `TauCeti.fractionRingTensorCommAlgEquiv`: the
  `K`-algebra equivalences on fraction rings induced by an isomorphism `A ≃ₐ[k] B` and by
  swapping `A ⊗[k] K` with `K ⊗[k] A`.

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
  [IsScalarTower k (F ⊗[k] K) Q] [IsScalarTower F (F ⊗[k] K) Q]
  [IsScalarTower K (F ⊗[k] K) Q] [IsScalarTower k F Q] [IsScalarTower k K Q]
  [IsFractionRing (F ⊗[k] K) Q]

/-- The images of the two factors in a fraction field of their tensor product are
linearly disjoint. This is the concrete fraction-field form of Mathlib's
`Subalgebra.LinearDisjoint.exists_field_of_isDomain_of_injective`. -/
theorem linearDisjoint_of_isFractionRing_tensorProduct :
    (IsScalarTower.toAlgHom k K Q).fieldRange.LinearDisjoint F := by
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

/-! ### Functoriality and uniqueness on fraction rings of tensor products -/

section Functoriality

variable {k A B C : Type*} (K : Type*) [CommRing k] [CommRing A] [CommRing B] [CommRing C]
  [CommRing K] [Algebra k A] [Algebra k B] [Algebra k C] [Algebra k K] [Module.Flat k K]

/-- When `K` is flat over `k` and `QB` has no zero divisors, the base change
`f ⊗ id : A ⊗[k] K → B ⊗[k] K` of an injective `f : A →ₐ[k] B` carries non-zero-divisors
to non-zero-divisors. -/
private theorem nonZeroDivisors_le_comap_map_tensorProduct (QB : Type*) [CommRing QB]
    [NoZeroDivisors QB] [Algebra (B ⊗[k] K) QB] [IsFractionRing (B ⊗[k] K) QB]
    {f : A →ₐ[k] B} (hf : Function.Injective f) :
    nonZeroDivisors (A ⊗[k] K) ≤ (nonZeroDivisors (B ⊗[k] K)).comap
      (Algebra.TensorProduct.map f (AlgHom.id k K) : A ⊗[k] K →+* B ⊗[k] K) := by
  have : NoZeroDivisors (B ⊗[k] K) :=
    (IsFractionRing.injective (B ⊗[k] K) QB).noZeroDivisors _ (map_zero _) (map_mul _)
  have hinj : Function.Injective (Algebra.TensorProduct.map f (AlgHom.id k K)) :=
    Module.Flat.rTensor_preserves_injective_linearMap f.toLinearMap hf
  exact nonZeroDivisors_le_comap_nonZeroDivisors_of_injective _ hinj

/-- **Functoriality of the fraction ring of a tensor product.** Let `K` be a flat `k`-algebra
(in particular, any `k`-algebra when `k` is a field) and let `f : A →ₐ[k] B` be injective.
Between any specified total quotient rings `QA` of `A ⊗[k] K` and `QB` of `B ⊗[k] K` with
`NoZeroDivisors QB` (for instance, a fraction field), `f ⊗ id` induces a `K`-algebra
homomorphism `QA →ₐ[K] QB`. -/
noncomputable def fractionRingTensorMapAlgHom (QA QB : Type*)
    [CommRing QA] [Algebra (A ⊗[k] K) QA] [Algebra K QA]
    [IsScalarTower K (A ⊗[k] K) QA] [IsFractionRing (A ⊗[k] K) QA]
    [CommRing QB] [NoZeroDivisors QB] [Algebra (B ⊗[k] K) QB] [Algebra K QB]
    [IsScalarTower K (B ⊗[k] K) QB] [IsFractionRing (B ⊗[k] K) QB]
    {f : A →ₐ[k] B} (hf : Function.Injective f) : QA →ₐ[K] QB where
  toRingHom := IsLocalization.map QB
    (Algebra.TensorProduct.map f (AlgHom.id k K) : A ⊗[k] K →+* B ⊗[k] K)
    (nonZeroDivisors_le_comap_map_tensorProduct K QB hf)
  commutes' c := by
    simp [IsScalarTower.algebraMap_apply K (A ⊗[k] K) QA,
      IsScalarTower.algebraMap_apply K (B ⊗[k] K) QB, Algebra.TensorProduct.right_algebraMap_apply]

section Apply

variable (QA QB : Type*)
  [CommRing QA] [Algebra (A ⊗[k] K) QA] [Algebra K QA]
  [IsScalarTower K (A ⊗[k] K) QA] [IsFractionRing (A ⊗[k] K) QA]
  [CommRing QB] [NoZeroDivisors QB] [Algebra (B ⊗[k] K) QB] [Algebra K QB]
  [IsScalarTower K (B ⊗[k] K) QB] [IsFractionRing (B ⊗[k] K) QB]
  {f : A →ₐ[k] B} (hf : Function.Injective f)

/-- On the image of `A ⊗[k] K`, `fractionRingTensorMapAlgHom` acts as `f ⊗ id`. -/
@[simp]
theorem fractionRingTensorMapAlgHom_algebraMap_tensorProduct (x : A ⊗[k] K) :
    fractionRingTensorMapAlgHom K QA QB hf (algebraMap (A ⊗[k] K) QA x) =
      algebraMap (B ⊗[k] K) QB (Algebra.TensorProduct.map f (AlgHom.id k K) x) :=
  IsLocalization.map_eq (nonZeroDivisors_le_comap_map_tensorProduct K QB hf) x

/-- On the image of the left factor `A`, `fractionRingTensorMapAlgHom` acts via `f`. -/
@[simp]
theorem fractionRingTensorMapAlgHom_algebraMap_left [Algebra A QA]
    [IsScalarTower A (A ⊗[k] K) QA] [Algebra B QB] [IsScalarTower B (B ⊗[k] K) QB] (a : A) :
    fractionRingTensorMapAlgHom K QA QB hf (algebraMap A QA a) = algebraMap B QB (f a) := by
  simp [IsScalarTower.algebraMap_apply A (A ⊗[k] K) QA,
    IsScalarTower.algebraMap_apply B (B ⊗[k] K) QB]

/-- On the image of a pure tensor `a ⊗ c`, `fractionRingTensorMapAlgHom` sends it to `f a * c`. -/
theorem fractionRingTensorMapAlgHom_algebraMap_tmul [Algebra B QB]
    [IsScalarTower B (B ⊗[k] K) QB] (a : A) (c : K) :
    fractionRingTensorMapAlgHom K QA QB hf (algebraMap (A ⊗[k] K) QA (a ⊗ₜ[k] c)) =
      algebraMap B QB (f a) * algebraMap K QB c := by
  have hmul : (f a ⊗ₜ[k] c : B ⊗[k] K) =
      algebraMap B (B ⊗[k] K) (f a) * algebraMap K (B ⊗[k] K) c := by
    simp [Algebra.TensorProduct.right_algebraMap_apply]
  rw [fractionRingTensorMapAlgHom_algebraMap_tensorProduct, Algebra.TensorProduct.map_tmul,
    AlgHom.id_apply, hmul, map_mul, ← IsScalarTower.algebraMap_apply,
    ← IsScalarTower.algebraMap_apply]

/-- The induced map on fraction rings of tensor products is injective. -/
theorem fractionRingTensorMapAlgHom_injective :
    Function.Injective (fractionRingTensorMapAlgHom K QA QB hf) := by
  have hinj : Function.Injective (Algebra.TensorProduct.map f (AlgHom.id k K)) :=
    Module.Flat.rTensor_preserves_injective_linearMap f.toLinearMap hf
  exact IsLocalization.map_injective_of_injective_of_le_nonZeroDivisors QA QB hinj
    (nonZeroDivisors_le_comap_map_tensorProduct K QB hf) le_rfl

/-- **Uniqueness of the induced `RingHom` on fraction rings of tensor products.** Any ring
homomorphism `ψ : QA →+* QB` extending `f` on `A` and the canonical map on `K` agrees with
`fractionRingTensorMapAlgHom K QA QB hf`. -/
theorem apply_eq_fractionRingTensorMapAlgHom_of_apply_algebraMap [Algebra A QA]
    [IsScalarTower A (A ⊗[k] K) QA] [Algebra B QB] [IsScalarTower B (B ⊗[k] K) QB]
    {ψ : QA →+* QB} (hA : ∀ a : A, ψ (algebraMap A QA a) = algebraMap B QB (f a))
    (hK : ∀ c : K, ψ (algebraMap K QA c) = algebraMap K QB c) (z : QA) :
    ψ z = fractionRingTensorMapAlgHom K QA QB hf z := by
  -- Two ring homomorphisms out of `QA` agree once they agree on `A` and `K` inside `A ⊗[k] K`.
  have heq : ψ = (fractionRingTensorMapAlgHom K QA QB hf).toRingHom := by
    refine IsLocalization.ringHom_ext (nonZeroDivisors (A ⊗[k] K)) ?_
    refine Algebra.TensorProduct.ringHom_ext ?_ ?_
    · refine RingHom.ext fun a ↦ ?_
      have hA' := hA a
      simp [IsScalarTower.algebraMap_apply A (A ⊗[k] K) QA,
        IsScalarTower.algebraMap_apply B (B ⊗[k] K) QB] at hA'
      simp [hA']
    · refine RingHom.ext fun c ↦ ?_
      simp [← Algebra.TensorProduct.right_algebraMap_apply,
        ← IsScalarTower.algebraMap_apply K (A ⊗[k] K) QA, hK]
  exact congr($heq z)

/-- **Uniqueness of the induced `K`-algebra map on fraction rings of tensor products.** Any
`K`-algebra map `ψ : QA →ₐ[K] QB` extending `f` on `A` equals
`fractionRingTensorMapAlgHom K QA QB hf`. -/
theorem eq_fractionRingTensorMapAlgHom_of_apply_algebraMap [Algebra A QA]
    [IsScalarTower A (A ⊗[k] K) QA] [Algebra B QB] [IsScalarTower B (B ⊗[k] K) QB]
    {ψ : QA →ₐ[K] QB} (hA : ∀ a : A, ψ (algebraMap A QA a) = algebraMap B QB (f a)) :
    ψ = fractionRingTensorMapAlgHom K QA QB hf :=
  AlgHom.ext fun z ↦
    apply_eq_fractionRingTensorMapAlgHom_of_apply_algebraMap K QA QB hf hA ψ.commutes z

end Apply

/-- `fractionRingTensorMapAlgHom` sends the identity algebra map to the identity. -/
@[simp]
theorem fractionRingTensorMapAlgHom_id (QA : Type*) [CommRing QA] [NoZeroDivisors QA]
    [Algebra (A ⊗[k] K) QA] [Algebra K QA] [IsScalarTower K (A ⊗[k] K) QA]
    [IsFractionRing (A ⊗[k] K) QA] (hid : Function.Injective (AlgHom.id k A)) :
    fractionRingTensorMapAlgHom K QA QA hid = AlgHom.id K QA := by
  apply AlgHom.toRingHom_injective
  refine IsLocalization.ringHom_ext (nonZeroDivisors (A ⊗[k] K)) (RingHom.ext fun x ↦ ?_)
  simp

/-- `fractionRingTensorMapAlgHom` respects composition of injective `k`-algebra maps. -/
theorem fractionRingTensorMapAlgHom_comp (QA QB QC : Type*)
    [CommRing QA] [Algebra (A ⊗[k] K) QA] [Algebra K QA]
    [IsScalarTower K (A ⊗[k] K) QA] [IsFractionRing (A ⊗[k] K) QA]
    [CommRing QB] [NoZeroDivisors QB] [Algebra (B ⊗[k] K) QB] [Algebra K QB]
    [IsScalarTower K (B ⊗[k] K) QB] [IsFractionRing (B ⊗[k] K) QB]
    [CommRing QC] [NoZeroDivisors QC] [Algebra (C ⊗[k] K) QC] [Algebra K QC]
    [IsScalarTower K (C ⊗[k] K) QC] [IsFractionRing (C ⊗[k] K) QC]
    {f : A →ₐ[k] B} (hf : Function.Injective f)
    {g : B →ₐ[k] C} (hg : Function.Injective g)
    (hfg : Function.Injective (g.comp f) := (AlgHom.coe_comp g f).symm ▸ hg.comp hf) :
    (fractionRingTensorMapAlgHom K QB QC hg).comp (fractionRingTensorMapAlgHom K QA QB hf) =
      fractionRingTensorMapAlgHom K QA QC hfg := by
  apply AlgHom.toRingHom_injective
  refine IsLocalization.ringHom_ext (nonZeroDivisors (A ⊗[k] K)) (RingHom.ext fun x ↦ ?_)
  simp only [AlgHom.comp_toRingHom, RingHom.comp_apply, AlgHom.coe_toRingHom,
    fractionRingTensorMapAlgHom_algebraMap_tensorProduct]
  exact congrArg (algebraMap (C ⊗[k] K) QC)
    (DFunLike.congr_fun
      (Algebra.TensorProduct.map_comp g f (AlgHom.id k K) (AlgHom.id k K)).symm x)

end Functoriality

section FieldSource

variable {k E B : Type*} (K : Type*) [CommRing k] [Field E] [CommRing B] [CommRing K]
  [Algebra k E] [Algebra k B] [Algebra k K] [Module.Flat k K]

omit [Module.Flat k K] in
/-- When `E` is a field and a total quotient ring `QB` of `B ⊗[k] K` is nontrivial, `B` is
nontrivial and every `k`-algebra map `E →ₐ[k] B` is injective. -/
private theorem injective_of_isFractionRing_tensorProduct (QB : Type*) [CommRing QB]
    [Nontrivial QB] [Algebra (B ⊗[k] K) QB] [IsFractionRing (B ⊗[k] K) QB] (f : E →ₐ[k] B) :
    Function.Injective f := by
  have : Nontrivial (B ⊗[k] K) :=
    (IsFractionRing.nontrivial_iff_nontrivial (B ⊗[k] K) QB).mpr inferInstance
  have : Nontrivial B :=
    (Algebra.TensorProduct.includeLeftRingHom : B →+* B ⊗[k] K).domain_nontrivial
  exact f.toRingHom.injective

/-- When `K` is flat over `k`, the source `E` is a field, and the target fraction ring `QB` is a
domain, any `k`-algebra map `f : E →ₐ[k] B` is automatically injective (`B ⊗[k] K` is nontrivial
since `QB` is) and induces an injective `K`-algebra map `QA →ₐ[K] QB` between fraction rings of
`E ⊗[k] K` and `B ⊗[k] K`. -/
noncomputable def fractionRingTensorFieldMapAlgHom (QA QB : Type*)
    [CommRing QA] [Algebra (E ⊗[k] K) QA] [Algebra K QA]
    [IsScalarTower K (E ⊗[k] K) QA] [IsFractionRing (E ⊗[k] K) QA]
    [CommRing QB] [IsDomain QB] [Algebra (B ⊗[k] K) QB] [Algebra K QB]
    [IsScalarTower K (B ⊗[k] K) QB] [IsFractionRing (B ⊗[k] K) QB]
    (f : E →ₐ[k] B) : QA →ₐ[K] QB :=
  fractionRingTensorMapAlgHom K QA QB (injective_of_isFractionRing_tensorProduct K QB f)

section FieldApply

variable (QA QB : Type*)
  [CommRing QA] [Algebra (E ⊗[k] K) QA] [Algebra K QA]
  [IsScalarTower K (E ⊗[k] K) QA] [IsFractionRing (E ⊗[k] K) QA]
  [CommRing QB] [IsDomain QB] [Algebra (B ⊗[k] K) QB] [Algebra K QB]
  [IsScalarTower K (B ⊗[k] K) QB] [IsFractionRing (B ⊗[k] K) QB]
  (f : E →ₐ[k] B)

/-- `fractionRingTensorFieldMapAlgHom` agrees with `fractionRingTensorMapAlgHom` for the
automatic injectivity of `f : E →ₐ[k] B`. -/
theorem fractionRingTensorFieldMapAlgHom_eq_fractionRingTensorMapAlgHom
    (hf : Function.Injective f) :
    fractionRingTensorFieldMapAlgHom K QA QB f = fractionRingTensorMapAlgHom K QA QB hf := by
  rfl

/-- On the image of `E ⊗[k] K`, `fractionRingTensorFieldMapAlgHom` acts as `f ⊗ id`. -/
@[simp]
theorem fractionRingTensorFieldMapAlgHom_algebraMap_tensorProduct (x : E ⊗[k] K) :
    fractionRingTensorFieldMapAlgHom K QA QB f (algebraMap (E ⊗[k] K) QA x) =
      algebraMap (B ⊗[k] K) QB (Algebra.TensorProduct.map f (AlgHom.id k K) x) :=
  fractionRingTensorMapAlgHom_algebraMap_tensorProduct K QA QB _ x

/-- On the image of the field `E`, `fractionRingTensorFieldMapAlgHom` acts via `f`. -/
@[simp]
theorem fractionRingTensorFieldMapAlgHom_algebraMap_left [Algebra E QA]
    [IsScalarTower E (E ⊗[k] K) QA] [Algebra B QB] [IsScalarTower B (B ⊗[k] K) QB] (a : E) :
    fractionRingTensorFieldMapAlgHom K QA QB f (algebraMap E QA a) = algebraMap B QB (f a) :=
  fractionRingTensorMapAlgHom_algebraMap_left K QA QB _ a

/-- The `K`-algebra map induced from a field source `E` is injective. -/
theorem fractionRingTensorFieldMapAlgHom_injective :
    Function.Injective (fractionRingTensorFieldMapAlgHom K QA QB f) :=
  fractionRingTensorMapAlgHom_injective K QA QB _

/-- Any `K`-algebra map `QA →ₐ[K] QB` extending `f` on `E` equals
`fractionRingTensorFieldMapAlgHom K QA QB f`. -/
theorem eq_fractionRingTensorFieldMapAlgHom_of_apply_algebraMap [Algebra E QA]
    [IsScalarTower E (E ⊗[k] K) QA] [Algebra B QB] [IsScalarTower B (B ⊗[k] K) QB]
    {ψ : QA →ₐ[K] QB} (hE : ∀ a : E, ψ (algebraMap E QA a) = algebraMap B QB (f a)) :
    ψ = fractionRingTensorFieldMapAlgHom K QA QB f :=
  eq_fractionRingTensorMapAlgHom_of_apply_algebraMap K QA QB _ hE

end FieldApply

/-- `fractionRingTensorFieldMapAlgHom` sends the identity on `E` to the identity on `QA`. -/
@[simp]
theorem fractionRingTensorFieldMapAlgHom_id (QA : Type*) [CommRing QA] [IsDomain QA]
    [Algebra (E ⊗[k] K) QA] [Algebra K QA] [IsScalarTower K (E ⊗[k] K) QA]
    [IsFractionRing (E ⊗[k] K) QA] :
    fractionRingTensorFieldMapAlgHom K QA QA (AlgHom.id k E) = AlgHom.id K QA :=
  fractionRingTensorMapAlgHom_id K QA _

/-- `fractionRingTensorFieldMapAlgHom` respects composition across field sources. -/
theorem fractionRingTensorFieldMapAlgHom_comp {F C : Type*} [Field F] [CommRing C]
    [Algebra k F] [Algebra k C] (QA QB QC : Type*)
    [CommRing QA] [Algebra (E ⊗[k] K) QA] [Algebra K QA]
    [IsScalarTower K (E ⊗[k] K) QA] [IsFractionRing (E ⊗[k] K) QA]
    [CommRing QB] [IsDomain QB] [Algebra (F ⊗[k] K) QB] [Algebra K QB]
    [IsScalarTower K (F ⊗[k] K) QB] [IsFractionRing (F ⊗[k] K) QB]
    [CommRing QC] [IsDomain QC] [Algebra (C ⊗[k] K) QC] [Algebra K QC]
    [IsScalarTower K (C ⊗[k] K) QC] [IsFractionRing (C ⊗[k] K) QC]
    (f : E →ₐ[k] F) (g : F →ₐ[k] C) :
    (fractionRingTensorFieldMapAlgHom K QB QC g).comp
        (fractionRingTensorFieldMapAlgHom K QA QB f) =
      fractionRingTensorFieldMapAlgHom K QA QC (g.comp f) :=
  fractionRingTensorMapAlgHom_comp K QA QB QC _ _ _

end FieldSource

section Equiv

section Congr

variable {k A B : Type*} (K : Type*) [CommSemiring k] [CommRing A] [CommRing B] [CommRing K]
  [Algebra k A] [Algebra k B] [Algebra k K]

/-- A `k`-algebra isomorphism `e : A ≃ₐ[k] B` induces a `K`-algebra isomorphism between any
specified total quotient rings of `A ⊗[k] K` and `B ⊗[k] K`, with no flatness or domain
assumption. -/
noncomputable def fractionRingTensorCongrAlgEquiv (QA QB : Type*)
    [CommRing QA] [Algebra (A ⊗[k] K) QA] [Algebra K QA]
    [IsScalarTower K (A ⊗[k] K) QA] [IsFractionRing (A ⊗[k] K) QA]
    [CommRing QB] [Algebra (B ⊗[k] K) QB] [Algebra K QB]
    [IsScalarTower K (B ⊗[k] K) QB] [IsFractionRing (B ⊗[k] K) QB]
    (e : A ≃ₐ[k] B) : QA ≃ₐ[K] QB :=
  IsFractionRing.algEquivOfAlgEquiv <| AlgEquiv.ofRingEquiv
    (f := (Algebra.TensorProduct.congr e (AlgEquiv.refl : K ≃ₐ[k] K)).toRingEquiv)
    fun c ↦ by simp [Algebra.TensorProduct.right_algebraMap_apply]

/-- On the image of `A ⊗[k] K`, `fractionRingTensorCongrAlgEquiv` acts via `e ⊗ id`. -/
@[simp]
theorem fractionRingTensorCongrAlgEquiv_algebraMap_tensorProduct (QA QB : Type*)
    [CommRing QA] [Algebra (A ⊗[k] K) QA] [Algebra K QA]
    [IsScalarTower K (A ⊗[k] K) QA] [IsFractionRing (A ⊗[k] K) QA]
    [CommRing QB] [Algebra (B ⊗[k] K) QB] [Algebra K QB]
    [IsScalarTower K (B ⊗[k] K) QB] [IsFractionRing (B ⊗[k] K) QB]
    (e : A ≃ₐ[k] B) (x : A ⊗[k] K) :
    fractionRingTensorCongrAlgEquiv K QA QB e (algebraMap (A ⊗[k] K) QA x) =
      algebraMap (B ⊗[k] K) QB
        (Algebra.TensorProduct.congr e (AlgEquiv.refl : K ≃ₐ[k] K) x) :=
  IsFractionRing.algEquivOfAlgEquiv_algebraMap _ x

/-- On the image of the left factor `A`, `fractionRingTensorCongrAlgEquiv` acts via `e`. -/
@[simp]
theorem fractionRingTensorCongrAlgEquiv_algebraMap_left (QA QB : Type*)
    [CommRing QA] [Algebra (A ⊗[k] K) QA] [Algebra K QA] [Algebra A QA]
    [IsScalarTower K (A ⊗[k] K) QA] [IsScalarTower A (A ⊗[k] K) QA]
    [IsFractionRing (A ⊗[k] K) QA]
    [CommRing QB] [Algebra (B ⊗[k] K) QB] [Algebra K QB] [Algebra B QB]
    [IsScalarTower K (B ⊗[k] K) QB] [IsScalarTower B (B ⊗[k] K) QB]
    [IsFractionRing (B ⊗[k] K) QB]
    (e : A ≃ₐ[k] B) (a : A) :
    fractionRingTensorCongrAlgEquiv K QA QB e (algebraMap A QA a) = algebraMap B QB (e a) := by
  simp [IsScalarTower.algebraMap_apply A (A ⊗[k] K) QA,
    IsScalarTower.algebraMap_apply B (B ⊗[k] K) QB]

/-- `fractionRingTensorCongrAlgEquiv` sends the identity equivalence on `A` to the identity on
`QA`. -/
@[simp]
theorem fractionRingTensorCongrAlgEquiv_refl (QA : Type*)
    [CommRing QA] [Algebra (A ⊗[k] K) QA] [Algebra K QA]
    [IsScalarTower K (A ⊗[k] K) QA] [IsFractionRing (A ⊗[k] K) QA] :
    fractionRingTensorCongrAlgEquiv K QA QA (AlgEquiv.refl : A ≃ₐ[k] A) = AlgEquiv.refl := by
  apply AlgEquiv.coe_toAlgHom_injective
  apply AlgHom.toRingHom_injective
  refine IsLocalization.ringHom_ext (nonZeroDivisors (A ⊗[k] K)) (RingHom.ext fun x ↦ ?_)
  simp

/-- Inverting `fractionRingTensorCongrAlgEquiv` corresponds to inverting `e`. -/
@[simp]
theorem fractionRingTensorCongrAlgEquiv_symm (QA QB : Type*)
    [CommRing QA] [Algebra (A ⊗[k] K) QA] [Algebra K QA]
    [IsScalarTower K (A ⊗[k] K) QA] [IsFractionRing (A ⊗[k] K) QA]
    [CommRing QB] [Algebra (B ⊗[k] K) QB] [Algebra K QB]
    [IsScalarTower K (B ⊗[k] K) QB] [IsFractionRing (B ⊗[k] K) QB]
    (e : A ≃ₐ[k] B) :
    (fractionRingTensorCongrAlgEquiv K QA QB e).symm =
      fractionRingTensorCongrAlgEquiv K QB QA e.symm := by
  apply AlgEquiv.coe_toAlgHom_injective
  apply AlgHom.toRingHom_injective
  refine IsLocalization.ringHom_ext (nonZeroDivisors (B ⊗[k] K)) (RingHom.ext fun x ↦ ?_)
  apply (fractionRingTensorCongrAlgEquiv K QA QB e).injective
  simp [← AlgHom.comp_apply, ← Algebra.TensorProduct.map_comp]

/-- `fractionRingTensorCongrAlgEquiv` respects composition of `k`-algebra equivalences. -/
@[simp]
theorem fractionRingTensorCongrAlgEquiv_trans {C : Type*} [CommRing C] [Algebra k C]
    (QA QB QC : Type*)
    [CommRing QA] [Algebra (A ⊗[k] K) QA] [Algebra K QA]
    [IsScalarTower K (A ⊗[k] K) QA] [IsFractionRing (A ⊗[k] K) QA]
    [CommRing QB] [Algebra (B ⊗[k] K) QB] [Algebra K QB]
    [IsScalarTower K (B ⊗[k] K) QB] [IsFractionRing (B ⊗[k] K) QB]
    [CommRing QC] [Algebra (C ⊗[k] K) QC] [Algebra K QC]
    [IsScalarTower K (C ⊗[k] K) QC] [IsFractionRing (C ⊗[k] K) QC]
    (e₁ : A ≃ₐ[k] B) (e₂ : B ≃ₐ[k] C) :
    (fractionRingTensorCongrAlgEquiv K QA QB e₁).trans
        (fractionRingTensorCongrAlgEquiv K QB QC e₂) =
      fractionRingTensorCongrAlgEquiv K QA QC (e₁.trans e₂) := by
  apply AlgEquiv.coe_toAlgHom_injective
  apply AlgHom.toRingHom_injective
  refine IsLocalization.ringHom_ext (nonZeroDivisors (A ⊗[k] K)) (RingHom.ext fun x ↦ ?_)
  have he : (e₂ : B →ₐ[k] C).comp (e₁ : A →ₐ[k] B) = (e₁.trans e₂ : A →ₐ[k] C) := by
    ext
    simp
  simp [← AlgHom.comp_apply, ← Algebra.TensorProduct.map_comp, he]

end Congr

/-- As a `K`-algebra homomorphism, `fractionRingTensorCongrAlgEquiv` agrees with
`fractionRingTensorMapAlgHom` when `K` is flat over a commutative ring `k` and `QB` has no zero
divisors. -/
@[simp]
theorem fractionRingTensorCongrAlgEquiv_toAlgHom {k A B : Type*} (K QA QB : Type*)
    [CommRing k] [CommRing A] [CommRing B] [CommRing K]
    [Algebra k A] [Algebra k B] [Algebra k K] [Module.Flat k K]
    [CommRing QA] [Algebra (A ⊗[k] K) QA] [Algebra K QA]
    [IsScalarTower K (A ⊗[k] K) QA] [IsFractionRing (A ⊗[k] K) QA]
    [CommRing QB] [NoZeroDivisors QB] [Algebra (B ⊗[k] K) QB] [Algebra K QB]
    [IsScalarTower K (B ⊗[k] K) QB] [IsFractionRing (B ⊗[k] K) QB]
    (e : A ≃ₐ[k] B) :
    (fractionRingTensorCongrAlgEquiv K QA QB e).toAlgHom =
      fractionRingTensorMapAlgHom K QA QB
        (show Function.Injective (e : A →ₐ[k] B) from e.injective) := by
  apply AlgHom.toRingHom_injective
  refine IsLocalization.ringHom_ext (nonZeroDivisors (A ⊗[k] K)) (RingHom.ext fun x ↦ ?_)
  simp

section Comm

variable (k A K : Type*) [CommSemiring k] [CommRing A] [CommRing K]
  [Algebra k A] [Algebra k K]

/-- **Commutativity of tensor factors on total quotient rings.** Any specified total quotient
ring `Q₁` of `A ⊗[k] K` (with the right `K`-algebra structure) is canonically isomorphic as a
`K`-algebra to any specified total quotient ring `Q₂` of `K ⊗[k] A` (with the left `K`-algebra
structure), compatibly with the scalar maps from `A` and `K`. -/
noncomputable def fractionRingTensorCommAlgEquiv (Q₁ Q₂ : Type*)
    [CommRing Q₁] [Algebra (A ⊗[k] K) Q₁] [Algebra K Q₁]
    [IsScalarTower K (A ⊗[k] K) Q₁] [IsFractionRing (A ⊗[k] K) Q₁]
    [CommRing Q₂] [Algebra (K ⊗[k] A) Q₂] [Algebra K Q₂]
    [IsScalarTower K (K ⊗[k] A) Q₂] [IsFractionRing (K ⊗[k] A) Q₂] :
    Q₁ ≃ₐ[K] Q₂ :=
  IsFractionRing.algEquivOfAlgEquiv (Algebra.TensorProduct.commRight k K A).symm

/-- `fractionRingTensorCommAlgEquiv` swaps pure tensors on the image of `A ⊗[k] K`. -/
@[simp]
theorem fractionRingTensorCommAlgEquiv_algebraMap_tensorProduct (Q₁ Q₂ : Type*)
    [CommRing Q₁] [Algebra (A ⊗[k] K) Q₁] [Algebra K Q₁]
    [IsScalarTower K (A ⊗[k] K) Q₁] [IsFractionRing (A ⊗[k] K) Q₁]
    [CommRing Q₂] [Algebra (K ⊗[k] A) Q₂] [Algebra K Q₂]
    [IsScalarTower K (K ⊗[k] A) Q₂] [IsFractionRing (K ⊗[k] A) Q₂] (x : A ⊗[k] K) :
    fractionRingTensorCommAlgEquiv k A K Q₁ Q₂ (algebraMap (A ⊗[k] K) Q₁ x) =
      algebraMap (K ⊗[k] A) Q₂ ((Algebra.TensorProduct.comm k K A).symm x) := by
  rw [fractionRingTensorCommAlgEquiv, IsFractionRing.algEquivOfAlgEquiv_algebraMap]
  rfl

/-- The inverse of `fractionRingTensorCommAlgEquiv` swaps pure tensors on `K ⊗[k] A`. -/
@[simp]
theorem fractionRingTensorCommAlgEquiv_symm_algebraMap_tensorProduct (Q₁ Q₂ : Type*)
    [CommRing Q₁] [Algebra (A ⊗[k] K) Q₁] [Algebra K Q₁]
    [IsScalarTower K (A ⊗[k] K) Q₁] [IsFractionRing (A ⊗[k] K) Q₁]
    [CommRing Q₂] [Algebra (K ⊗[k] A) Q₂] [Algebra K Q₂]
    [IsScalarTower K (K ⊗[k] A) Q₂] [IsFractionRing (K ⊗[k] A) Q₂] (x : K ⊗[k] A) :
    (fractionRingTensorCommAlgEquiv k A K Q₁ Q₂).symm (algebraMap (K ⊗[k] A) Q₂ x) =
      algebraMap (A ⊗[k] K) Q₁ (Algebra.TensorProduct.comm k K A x) := by
  rw [fractionRingTensorCommAlgEquiv, IsFractionRing.algEquivOfAlgEquiv_symm,
    AlgEquiv.symm_symm, IsFractionRing.algEquivOfAlgEquiv_algebraMap]
  rfl

/-- `fractionRingTensorCommAlgEquiv` commutes with the canonical maps from `A`. -/
@[simp]
theorem fractionRingTensorCommAlgEquiv_algebraMap_left (Q₁ Q₂ : Type*)
    [CommRing Q₁] [Algebra (A ⊗[k] K) Q₁] [Algebra K Q₁] [Algebra A Q₁]
    [IsScalarTower K (A ⊗[k] K) Q₁] [IsScalarTower A (A ⊗[k] K) Q₁]
    [IsFractionRing (A ⊗[k] K) Q₁]
    [CommRing Q₂] [Algebra (K ⊗[k] A) Q₂] [Algebra K Q₂] [Algebra A Q₂]
    [IsScalarTower K (K ⊗[k] A) Q₂] [IsScalarTower A (K ⊗[k] A) Q₂]
    [IsFractionRing (K ⊗[k] A) Q₂]
    (a : A) :
    fractionRingTensorCommAlgEquiv k A K Q₁ Q₂ (algebraMap A Q₁ a) = algebraMap A Q₂ a := by
  simp [IsScalarTower.algebraMap_apply A (A ⊗[k] K) Q₁,
    IsScalarTower.algebraMap_apply A (K ⊗[k] A) Q₂, Algebra.TensorProduct.right_algebraMap_apply]

/-- The inverse of `fractionRingTensorCommAlgEquiv` commutes with the canonical maps from `A`. -/
@[simp]
theorem fractionRingTensorCommAlgEquiv_symm_algebraMap_right (Q₁ Q₂ : Type*)
    [CommRing Q₁] [Algebra (A ⊗[k] K) Q₁] [Algebra K Q₁] [Algebra A Q₁]
    [IsScalarTower K (A ⊗[k] K) Q₁] [IsScalarTower A (A ⊗[k] K) Q₁]
    [IsFractionRing (A ⊗[k] K) Q₁]
    [CommRing Q₂] [Algebra (K ⊗[k] A) Q₂] [Algebra K Q₂] [Algebra A Q₂]
    [IsScalarTower K (K ⊗[k] A) Q₂] [IsScalarTower A (K ⊗[k] A) Q₂]
    [IsFractionRing (K ⊗[k] A) Q₂]
    (a : A) :
    (fractionRingTensorCommAlgEquiv k A K Q₁ Q₂).symm (algebraMap A Q₂ a) = algebraMap A Q₁ a :=
  (fractionRingTensorCommAlgEquiv k A K Q₁ Q₂).injective (by simp)

end Comm

end Equiv

end TauCeti
