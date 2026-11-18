/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Dimension.OrzechProperty
public import Mathlib.RingTheory.Nakayama
public import TauCeti.FieldTheory.FunctionField.Place.Completion.Approximation
public import TauCeti.FieldTheory.FunctionField.Place.Completion.LocalDegree
public import TauCeti.FieldTheory.FunctionField.Place.Extension.Fundamental
public import TauCeti.RingTheory.NormTrace.Pi
import Mathlib.RingTheory.Etale.Field
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.Localization.BaseChange
import TauCeti.LinearAlgebra.Span.Basic
import TauCeti.RingTheory.Localization.Separable
import TauCeti.RingTheory.NormTrace.BaseChange

/-!
# The completions above a place and the semilocal decomposition

Let `F' / F` be a finite extension, `P` a place of `F / k`, and `P'` run over the finitely many
places of `F' / k'` lying over `P`. Each completion `F̂'_{P'}` is a finite extension of the
completion `F̂_P` (`TauCeti.Place.finrank_completion`), and the diagonal map
`F' → ∏_{P' ∣ P} F̂'_{P'}` is compared here with the scalar extension of `F'` to `F̂_P`.

First, without installing an `F`-algebra structure on `F̂_P`, the decomposition is established on
families of vectors:

* **Spanning.** The functions of `F'` regular at every place over `P` span
  `∏_{P' ∣ P} 𝒪̂_{P'}` over `𝒪̂_P`. By weak approximation, every family of completed functions
  agrees with a single function of `F'` to order `e(P' ∣ P)` at each `P'`, that is, modulo a
  uniformizer of `P`; since `∏_{P' ∣ P} 𝒪̂_{P'}` is a finite `𝒪̂_P`-module, Nakayama's lemma
  turns this into an exact expansion. Approximating to order `0` reduces the completed fields
  to the completed valuation rings, so `F'`, and so any family spanning `F'` over `F`, spans
  `∏_{P' ∣ P} F̂'_{P'}` over `F̂_P`. Spanning needs only `F' / F` finite.
* **Dimension.** The local degrees are `e(P' ∣ P) f(P' ∣ P)`, so their sum over `P' ∣ P` is
  `[F' : F]` by the fundamental identity. This is where integrality of `k' / k` enters, together
  with separability of `F' / F` or, without separability, the hypothesis that `F / k` is an
  algebraic function field. A spanning family of `[F' : F]` vectors is a basis, so a family of
  `F'` is linearly independent over `F` exactly when its diagonal image is linearly independent
  over `F̂_P`. Reading the matrix of multiplication by `x ∈ F'` in such a basis gives **the trace
  formula** `Tr_{F'/F} x = ∑_{P' ∣ P} Tr_{F̂'_{P'}/F̂_P} x`.

Second, in the `PlaceCompletionExtension` scope, `P.Completion` and `P.completionPlace.integers`
carry their canonical `F`- and `P.integers`-algebra structures alongside the fibre extension
algebras on `w.1.Completion` and `w.1.completionPlace.integers`. For a finite extension `F' / F`
with `k' / k` integral — assuming either `F' / F` separable or `F / k` an algebraic function field
— combining the spanning and dimension results above with the identification of
`integralClosure P.integers F'` as the intersection of the valuation rings above `P`
(`TauCeti.Place.isIntegral_iff_forall_restrict_eq_mem_integers_of_finiteDimensional`) upgrades the
diagonal maps to the bundled field and integral **semilocal decompositions**

```text
P.Completion ⊗[F] F' ≃ₐ[P.Completion] ∏_{w ∣ P} w.1.Completion,
P.completionPlace.integers ⊗[P.integers] integralClosure P.integers F'
  ≃ₐ[P.completionPlace.integers] ∏_{w ∣ P} w.1.completionPlace.integers,
```

together with componentwise splitting of `Algebra.norm` and `Algebra.trace` on the tensor product.
Restricting constants from `k'` to `k` via `TauCeti.Place.restrictScalars` and transferring formal
étaleness across `completionSemilocalEquiv` shows that each completed extension
`P.Completion → P'.Completion` of a finite separable extension is separable
(`TauCeti.Place.isSeparable_completion`), with no hypothesis on the constant fields or residue
fields.

## Main definitions

* `TauCeti.Place.completionSemilocalHom`, `TauCeti.Place.completionSemilocalEquiv`, and
  `TauCeti.Place.completionSemilocalEquivOfIsFunctionField`: the semilocal `P.Completion`-algebra
  homomorphism and isomorphisms `P.Completion ⊗[F] F' ≃ₐ[P.Completion] ∏_{w ∣ P} w.1.Completion`
  (when `k' / k` is integral and either `F' / F` is finite separable or `F / k` is a function
  field).
* `TauCeti.Place.completionIntegersSemilocalHom`, `TauCeti.Place.completionIntegersSemilocalEquiv`,
  and `TauCeti.Place.completionIntegersSemilocalEquivOfIsFunctionField`: the integral semilocal
  homomorphism and isomorphisms
  `P.completionPlace.integers ⊗[P.integers] integralClosure P.integers F'
  ≃ₐ[P.completionPlace.integers] ∏_{w ∣ P} w.1.completionPlace.integers`.
* `TauCeti.Place.completionIntegersSemilocalToField`: the canonical injective map from the
  integral tensor product to the field tensor product.

## Main results

* `TauCeti.Place.span_completionIntegers_pi_eq_top`: the functions regular above `P` span
  `∏_{P' ∣ P} 𝒪̂_{P'}` over `𝒪̂_P`.
* `TauCeti.Place.span_completion_pi_eq_top` and
  `TauCeti.Place.span_completionEmbedding_pi_eq_top`: `F'`, and so any family spanning `F'` over
  `F`, spans `∏_{P' ∣ P} F̂'_{P'}` over `F̂_P`.
* `TauCeti.Place.finsum_finrank_completion_eq_finrank` and
  `TauCeti.Place.finsum_finrank_completion_eq_finrank_of_isSeparable`: for `F' / F` finite and
  `k' / k` integral (with `F / k` a function field or `F' / F` separable), the local degrees above
  `P` add up to `[F' : F]`.
* `TauCeti.Place.linearIndependent_completionEmbedding_pi_iff` and
  `TauCeti.Place.linearIndependent_completionEmbedding_pi_iff_of_isSeparable`: a family of `F'`
  is linearly independent over `F` if and only if its diagonal image in `∏_{P' ∣ P} F̂'_{P'}` is
  linearly independent over `F̂_P`.
* `TauCeti.Place.completionEmbedding_trace` and
  `TauCeti.Place.completionEmbedding_trace_of_isSeparable`: **the trace formula**
  `Tr_{F'/F} x = ∑_{P' ∣ P} Tr_{F̂'_{P'}/F̂_P} x`.
* `TauCeti.Place.completionEmbedding_norm`,
  `TauCeti.Place.completionEmbedding_norm_of_isSeparable`,
  `TauCeti.Place.norm_eq_finprod_norm_completionSemilocalEquiv`,
  `TauCeti.Place.trace_eq_finsum_trace_completionSemilocalEquiv`, and
  `TauCeti.Place.trace_completionSemilocalEquiv_symm_single_mul`: local-global norm product
  formulas and componentwise norm/trace identities across the semilocal decomposition.
* `TauCeti.Place.isSeparable_completion` and
  `TauCeti.Place.isSeparable_fractionRing_completionIntegers`: completion preserves separability
  of a finite separable field extension, with no assumption on the constant fields or residue
  fields.

## Implementation notes

The `PlaceCompletionExtension` scope is modeled on `AdicCompletionExtension` in
`TauCeti/NumberTheory/NumberField/LocalGlobal/Completion.lean`. Both the family-level and bundled
semilocal decompositions and norm/trace formulas closely adapt the number-field development in
`TauCeti/NumberTheory/NumberField/LocalGlobal/Semilocal/` (`TauCeti.semilocalEquiv`,
`TauCeti.integralSemilocalEquiv`, `TauCeti.algebraMap_trace_eq_sum_trace`, and
`TauCeti.trace_semilocalEquiv_symm_single_mul`), replacing density of `L` in `∏_{w ∣ v} L_w` with
weak approximation and Nakayama's lemma over the completed valuation ring.

## References

* N. Bourbaki, *Commutative Algebra*, Chapter VI, §8, nos. 2 and 5.
* H. Stichtenoth, *Algebraic Function Fields and Codes*, 2nd ed., GTM 254, Springer, 2009,
  Sections I.3, III.1, and IV.2.
* J.-P. Serre, *Local Fields*, GTM 67, Springer, 1979, Chapter II, §3.
* J. Neukirch, *Algebraic Number Theory*, Chapter II, Proposition (8.3).
-/

public section

open IsDedekindDomain IsLocalRing Module UniformSpace
open scoped TensorProduct nonZeroDivisors

namespace TauCeti.Place

section FamilySemilocal

variable {k k' F F' : Type*} [Field k] [Field k'] [Field F] [Field F']
  [Algebra k F] [Algebra k k'] [Algebra k' F'] [Algebra k F'] [Algebra F F']
  [IsScalarTower k k' F'] [IsScalarTower k F F'] [FiniteDimensional F F'] (P : Place k F)

variable (k')

section Spanning

/-- The diagonal embedding `F' → ∏_{P' ∣ P} F̂'_{P'}`, semilinear over the embedding of `F` in
`F̂_P`. -/
private noncomputable def completionEmbeddingPi :
    letI := fun P' : {P' : Place k' F' // P'.restrict k F = P} ↦
      P.completionExtensionAlgebra P'.1 P'.2
    F' →ₛₗ[(P.completionEmbedding : F →+* P.Completion)]
      ∀ P' : {P' : Place k' F' // P'.restrict k F = P}, P'.1.Completion :=
  letI := fun P' : {P' : Place k' F' // P'.restrict k F = P} ↦
    P.completionExtensionAlgebra P'.1 P'.2
  { toFun y P' := P'.1.completionEmbedding y
    map_add' _ _ := funext fun _ ↦ map_add _ _ _
    map_smul' c y := funext fun P' ↦ completionEmbedding_smul P P'.1 P'.2 c y }

/-- `TauCeti.Place.completionEmbeddingPi` is the coordinatewise completion embedding. -/
private theorem completionEmbeddingPi_apply (y : F') :
    completionEmbeddingPi k' P y = fun P' ↦ P'.1.completionEmbedding y :=
  rfl

variable (F') in
/-- **The completed valuation rings above `P` are spanned by the functions regular above `P`**:
the diagonal images of the functions of `F'` regular at every place over `P` span
`∏_{P' ∣ P} 𝒪̂_{P'}` over `𝒪̂_P`. -/
theorem span_completionIntegers_pi_eq_top :
    letI := fun P' : {P' : Place k' F' // P'.restrict k F = P} ↦
      P.completionIntegersExtensionAlgebra P'.1 P'.2
    Submodule.span P.completionPlace.integers
      (Set.range fun y : {y : F' // ∀ P' : {P' : Place k' F' // P'.restrict k F = P},
          y ∈ P'.1.integers} ↦
        fun P' : {P' : Place k' F' // P'.restrict k F = P} ↦
          P'.1.completionIntegersEmbedding ⟨y.1, y.2 P'⟩) = ⊤ := by
  classical
  let ι := {P' : Place k' F' // P'.restrict k F = P}
  let _ := fun P' : ι ↦ P.completionIntegersExtensionAlgebra P'.1 P'.2
  have _ := fun P' : ι ↦ moduleFinite_completionIntegers P P'.1 P'.2
  have := Fintype.ofFinite ι
  -- By Nakayama's lemma it suffices to span modulo `𝔪̂_P`.
  refine top_unique (Submodule.le_of_le_smul_of_le_jacobson (I := maximalIdeal _)
    Module.Finite.fg_top (ringJacobson_eq_maximalIdeal _).ge fun m _ ↦ ?_)
  -- Approximate `m` to order `e(P' ∣ P)` at every `P'` by a single function `y`.
  obtain ⟨y, hy⟩ := exists_forall_sub_completionEmbedding_mem_filtration
    (P := fun P' : ι ↦ P'.1) Subtype.val_injective (fun P' ↦ (m P' : P'.1.Completion))
    (fun P' ↦ ramificationIdx F P'.1)
  have hyint (P' : ι) : y ∈ P'.1.integers := by
    have hm := P'.1.completionPlace.mem_filtration_zero_iff.mpr (m P').2
    have h := sub_mem hm (P'.1.completionPlace.filtration_antitone (by simp) (hy P'))
    rw [sub_sub_cancel, completionEmbedding_mem_filtration_iff] at h
    exact P'.1.mem_filtration_zero_iff.mp h
  -- The error is a multiple of a uniformizer of `P` at every coordinate.
  set my := fun P' : ι ↦ P'.1.completionIntegersEmbedding ⟨y, hyint P'⟩
  rw [← add_sub_cancel my m, ← Finset.univ_sum_single (m - my)]
  refine Submodule.add_mem_sup (Submodule.subset_span ⟨⟨y, hyint⟩, rfl⟩)
    (Submodule.sum_mem _ fun P' _ ↦ Submodule.smul_top_le_comap_smul_top _
      (LinearMap.single P.completionPlace.integers (fun P' : ι ↦ P'.1.completionPlace.integers) P')
      (mem_maximalIdeal_smul_top_of_mem_filtration P P'.1 P'.2 ?_))
  simpa [my, completionIntegersEmbedding_apply] using hy P'

variable (F') in
/-- **`F'` spans the completions above `P`**: the diagonal image of `F'` spans
`∏_{P' ∣ P} F̂'_{P'}` over `F̂_P`. -/
theorem span_completion_pi_eq_top :
    letI := fun P' : {P' : Place k' F' // P'.restrict k F = P} ↦
      P.completionExtensionAlgebra P'.1 P'.2
    Submodule.span P.Completion
      (Set.range fun (y : F') (P' : {P' : Place k' F' // P'.restrict k F = P}) ↦
        P'.1.completionEmbedding y) = ⊤ := by
  let ι := {P' : Place k' F' // P'.restrict k F = P}
  let _ := fun P' : ι ↦ P.completionExtensionAlgebra P'.1 P'.2
  let _ := fun P' : ι ↦ P.completionIntegersExtensionAlgebra P'.1 P'.2
  set W := Submodule.span P.Completion
    (Set.range fun (y : F') (P' : ι) ↦ P'.1.completionEmbedding y)
  -- Families of completed integers lie in `W`, since they are spanned by functions of `F'`.
  let toV : (∀ P' : ι, P'.1.completionPlace.integers) →+* ∀ P' : ι, P'.1.Completion :=
    RingHom.pi fun P' ↦ P'.1.completionPlace.integers.subtype.comp (Pi.evalRingHom _ P')
  have hint (m : ∀ P' : ι, P'.1.completionPlace.integers) : toV m ∈ W := by
    refine Submodule.map_mem_span_of_forall_exists (A := P.completionPlace.integers) toV _ _
      (fun a ↦ ⟨(a : P.Completion), funext fun P' ↦ ?_⟩) ?_
      ((span_completionIntegers_pi_eq_top k' F' P).symm ▸ Submodule.mem_top)
    · simp only [toV, RingHom.pi_apply, RingHom.comp_apply, Pi.evalRingHom_apply,
        Pi.algebraMap_apply, ValuationSubring.coe_subtype]
      rw [coe_algebraMap_completionIntegersExtensionAlgebra, algebraMap_completionExtensionAlgebra]
    · rintro _ ⟨y, rfl⟩
      exact Submodule.subset_span ⟨y.1, funext fun P' ↦ by simp [toV]⟩
  refine eq_top_iff.mpr fun z _ ↦ ?_
  -- Subtracting a function of `F'` leaves a family of completed integers.
  obtain ⟨y, hy⟩ := exists_forall_sub_completionEmbedding_mem_filtration
    (P := fun P' : ι ↦ P'.1) Subtype.val_injective z (fun _ ↦ 0)
  have h := W.add_mem (Submodule.subset_span ⟨y, rfl⟩)
    (hint fun P' ↦ ⟨_, P'.1.completionPlace.mem_filtration_zero_iff.mp (hy P')⟩)
  convert h using 1
  funext P'
  simp [toV]

/-- **A spanning family of `F'` spans the completions above `P`**: if `v` spans `F'` over `F`,
its diagonal image spans `∏_{P' ∣ P} F̂'_{P'}` over `F̂_P`. -/
theorem span_completionEmbedding_pi_eq_top {ι' : Type*} {v : ι' → F'}
    (hv : Submodule.span F (Set.range v) = ⊤) :
    letI := fun P' : {P' : Place k' F' // P'.restrict k F = P} ↦
      P.completionExtensionAlgebra P'.1 P'.2
    Submodule.span P.Completion
      (Set.range fun (i : ι') (P' : {P' : Place k' F' // P'.restrict k F = P}) ↦
        P'.1.completionEmbedding (v i)) = ⊤ := by
  let _ := fun P' : {P' : Place k' F' // P'.restrict k F = P} ↦
    P.completionExtensionAlgebra P'.1 P'.2
  exact (Submodule.span_range_eq_span_range_comp_of_span_eq_top (S := P.Completion) hv
    (completionEmbeddingPi k' P)).symm.trans (span_completion_pi_eq_top k' F' P)

end Spanning

section Dimension

/-! The dimension count and the trace formula are first proved from the sum of the local degrees,
and then specialized through the two forms of the fundamental identity. -/

/-- The local degrees above `P` add up to `[F' : F]` whenever the fundamental identity holds
at `P`. -/
private theorem finsum_finrank_completion_eq_finrank_of_sum_eq
    (hfund : ∀ {s : Finset (Place k' F')}, (∀ P' : Place k' F', P' ∈ s ↔ P'.restrict k F = P) →
      ∑ P' ∈ s, ramificationIdx F P' * relativeDegree k F P' = finrank F F') :
    ∑ᶠ P' : {P' : Place k' F' // P'.restrict k F = P},
        (letI := P.completionExtensionAlgebra P'.1 P'.2
        finrank P.Completion P'.1.Completion) = finrank F F' := by
  have hfin := finite_setOf_restrict_eq (k' := k') (F' := F') k F P
  have := Fintype.ofFinite {P' : Place k' F' // P'.restrict k F = P}
  rw [finsum_eq_sum_of_fintype, ← hfund (s := hfin.toFinset) fun _ ↦ hfin.mem_toFinset,
    Finset.sum_subtype hfin.toFinset fun _ ↦ hfin.mem_toFinset]
  exact Finset.sum_congr rfl fun P' _ ↦ finrank_completion P P'.1 P'.2

/-- The diagonal image of an `F`-basis of `F'` is linearly independent over `F̂_P` whenever the
local degrees above `P` add up to `[F' : F]`. -/
private theorem linearIndependent_completionEmbedding_basis_of_finsum
    (hdeg : ∑ᶠ P' : {P' : Place k' F' // P'.restrict k F = P},
        (letI := P.completionExtensionAlgebra P'.1 P'.2
        finrank P.Completion P'.1.Completion) = finrank F F')
    {ι' : Type*} (b : Basis ι' F F') :
    letI := fun P' : {P' : Place k' F' // P'.restrict k F = P} ↦
      P.completionExtensionAlgebra P'.1 P'.2
    LinearIndependent P.Completion
      fun (i : ι') (P' : {P' : Place k' F' // P'.restrict k F = P}) ↦
        P'.1.completionEmbedding (b i) := by
  let ι := {P' : Place k' F' // P'.restrict k F = P}
  let _ := fun P' : ι ↦ P.completionExtensionAlgebra P'.1 P'.2
  have _ := fun P' : ι ↦ finiteDimensional_completion P P'.1 P'.2
  have := Fintype.ofFinite ι
  have := Module.Finite.finite_basis b
  have := Fintype.ofFinite ι'
  refine linearIndependent_of_top_le_span_of_card_eq_finrank
    (span_completionEmbedding_pi_eq_top k' P b.span_eq).ge ?_
  rw [← finrank_eq_card_basis b, finrank_pi_fintype, ← hdeg, finsum_eq_sum_of_fintype]

/-- A family of `F'` is linearly independent over `F` if and only if its diagonal image is
linearly independent over `F̂_P`, whenever the local degrees above `P` add up to `[F' : F]`. -/
private theorem linearIndependent_completionEmbedding_pi_iff_of_finsum
    (hdeg : ∑ᶠ P' : {P' : Place k' F' // P'.restrict k F = P},
        (letI := P.completionExtensionAlgebra P'.1 P'.2
        finrank P.Completion P'.1.Completion) = finrank F F')
    {ι' : Type*} {v : ι' → F'} :
    letI := fun P' : {P' : Place k' F' // P'.restrict k F = P} ↦
      P.completionExtensionAlgebra P'.1 P'.2
    LinearIndependent P.Completion
        (fun (i : ι') (P' : {P' : Place k' F' // P'.restrict k F = P}) ↦
          P'.1.completionEmbedding (v i)) ↔
      LinearIndependent F v := by
  let ι := {P' : Place k' F' // P'.restrict k F = P}
  let _ := fun P' : ι ↦ P.completionExtensionAlgebra P'.1 P'.2
  refine ⟨fun h ↦ ?_, fun hv ↦ ?_⟩
  · -- A vanishing `F`-combination of `v` maps to a vanishing `F̂_P`-combination.
    rw [linearIndependent_iff'] at h ⊢
    intro s g hg i hi
    refine P.completionEmbedding.injective ?_
    rw [map_zero]
    refine h s (fun i ↦ P.completionEmbedding (g i)) ?_ i hi
    simpa only [map_sum, map_zero, LinearMap.map_smulₛₗ, AlgHom.coe_toRingHom,
      completionEmbeddingPi_apply] using
      congrArg (completionEmbeddingPi k' P) hg
  · -- Extend `v` to a basis of `F'`.
    have h := (linearIndependent_completionEmbedding_basis_of_finsum k' P hdeg
      (Basis.extend hv.linearIndepOn_id)).comp
        (fun i ↦ ⟨v i, Basis.subset_extend _ (Set.mem_range_self i)⟩)
        fun _ _ hij ↦ hv.injective (congrArg Subtype.val hij)
    simpa only [Function.comp_def, Basis.coe_extend] using h

/-- The trace formula at `P`, whenever the local degrees above `P` add up to `[F' : F]`. -/
private theorem completionEmbedding_trace_of_finsum
    (hdeg : ∑ᶠ P' : {P' : Place k' F' // P'.restrict k F = P},
        (letI := P.completionExtensionAlgebra P'.1 P'.2
        finrank P.Completion P'.1.Completion) = finrank F F')
    (x : F') :
    P.completionEmbedding (Algebra.trace F F' x) =
      ∑ᶠ P' : {P' : Place k' F' // P'.restrict k F = P},
        (letI := P.completionExtensionAlgebra P'.1 P'.2
        Algebra.trace P.Completion P'.1.Completion (P'.1.completionEmbedding x)) := by
  classical
  let ι := {P' : Place k' F' // P'.restrict k F = P}
  let _ := fun P' : ι ↦ P.completionExtensionAlgebra P'.1 P'.2
  have _ := fun P' : ι ↦ finiteDimensional_completion P P'.1 P'.2
  have := Fintype.ofFinite ι
  let b := Module.finBasis F F'
  -- The diagonal image `B` of `b` is a basis, in which `x` acts by the matrix it has in `b`.
  let B : Basis (Fin (finrank F F')) P.Completion (∀ P' : ι, P'.1.Completion) :=
    .mk (linearIndependent_completionEmbedding_basis_of_finsum k' P hdeg b)
      (span_completionEmbedding_pi_eq_top k' P b.span_eq).ge
  have hrepr (y : F') (i) :
      B.repr (fun P' : ι ↦ P'.1.completionEmbedding y) i = P.completionEmbedding (b.repr y i) := by
    have hy : (fun P' : ι ↦ P'.1.completionEmbedding y) =
        ∑ j, P.completionEmbedding (b.repr y j) • B j := by
      rw [← completionEmbeddingPi_apply]
      conv_lhs => rw [← b.sum_repr y]
      simp only [B, Basis.coe_mk, map_sum, LinearMap.map_smulₛₗ, AlgHom.coe_toRingHom,
        completionEmbeddingPi_apply]
    rw [hy, B.repr_sum_self]
  have hmat : Algebra.leftMulMatrix B (fun P' : ι ↦ P'.1.completionEmbedding x) =
      (P.completionEmbedding : F →+* P.Completion).mapMatrix (Algebra.leftMulMatrix b x) := by
    ext i j
    have hmul : (fun P' : ι ↦ P'.1.completionEmbedding x) * B j =
        fun P' : ι ↦ P'.1.completionEmbedding (x * b j) := by
      funext P'
      simp [B]
    rw [Algebra.leftMulMatrix_eq_repr_mul, RingHom.mapMatrix_apply, Matrix.map_apply,
      Algebra.leftMulMatrix_eq_repr_mul, hmul, hrepr, AlgHom.coe_toRingHom]
  rw [finsum_eq_sum_of_fintype, ← TauCeti.Algebra.trace_pi, Algebra.trace_eq_matrix_trace B, hmat,
    Algebra.trace_eq_matrix_trace b]
  exact AddMonoidHom.map_trace (P.completionEmbedding : F →+* P.Completion).toAddMonoidHom _

variable [Algebra.IsIntegral k k']

variable (F') in
/-- **The local degrees above `P` add up to the global degree**:
`∑_{P' ∣ P} [F̂'_{P'} : F̂_P] = [F' : F]` for a finite separable extension `F' / F` whose constant
field extension `k' / k` is integral. For an algebraic function field `F / k` separability is not
needed; that is `TauCeti.Place.finsum_finrank_completion_eq_finrank`. -/
theorem finsum_finrank_completion_eq_finrank_of_isSeparable [Algebra.IsSeparable F F'] :
    ∑ᶠ P' : {P' : Place k' F' // P'.restrict k F = P},
        (letI := P.completionExtensionAlgebra P'.1 P'.2
        finrank P.Completion P'.1.Completion) = finrank F F' :=
  finsum_finrank_completion_eq_finrank_of_sum_eq k' P
    (sum_ramificationIdx_mul_relativeDegree_eq_finrank_of_isSeparable k F P)

variable (F') in
/-- **The local degrees above `P` add up to the global degree**:
`∑_{P' ∣ P} [F̂'_{P'} : F̂_P] = [F' : F]` for an algebraic function field `F / k` and a finite
extension `F' / F` whose constant field extension `k' / k` is integral, with no separability
hypothesis. For a separable `F' / F` this holds without assuming that `F / k` is a function field;
that is `TauCeti.Place.finsum_finrank_completion_eq_finrank_of_isSeparable`. -/
theorem finsum_finrank_completion_eq_finrank (hF : IsFunctionField k F) :
    ∑ᶠ P' : {P' : Place k' F' // P'.restrict k F = P},
        (letI := P.completionExtensionAlgebra P'.1 P'.2
        finrank P.Completion P'.1.Completion) = finrank F F' :=
  finsum_finrank_completion_eq_finrank_of_sum_eq k' P
    (sum_ramificationIdx_mul_relativeDegree_eq_finrank_of_isFunctionField k F hF P)

/-- **Linear independence survives completion at `P`**: for a finite separable extension `F' / F`
whose constant field extension `k' / k` is integral, a family of `F'` is linearly independent over
`F` if and only if its diagonal image in `∏_{P' ∣ P} F̂'_{P'}` is linearly independent over `F̂_P`.
Together with `TauCeti.Place.span_completionEmbedding_pi_eq_top`, the diagonal image of an
`F`-basis of `F'` is an `F̂_P`-basis: this is the semilocal decomposition
`F̂_P ⊗_F F' ≅ ∏_{P' ∣ P} F̂'_{P'}`. For an algebraic function field `F / k` separability is not
needed; that is `TauCeti.Place.linearIndependent_completionEmbedding_pi_iff`. -/
theorem linearIndependent_completionEmbedding_pi_iff_of_isSeparable [Algebra.IsSeparable F F']
    {ι' : Type*} {v : ι' → F'} :
    letI := fun P' : {P' : Place k' F' // P'.restrict k F = P} ↦
      P.completionExtensionAlgebra P'.1 P'.2
    LinearIndependent P.Completion
        (fun (i : ι') (P' : {P' : Place k' F' // P'.restrict k F = P}) ↦
          P'.1.completionEmbedding (v i)) ↔
      LinearIndependent F v :=
  linearIndependent_completionEmbedding_pi_iff_of_finsum k' P
    (finsum_finrank_completion_eq_finrank_of_isSeparable k' F' P)

/-- **Linear independence survives completion at `P`**: for an algebraic function field `F / k`
and a finite extension `F' / F` whose constant field extension `k' / k` is integral, a family of
`F'` is linearly independent over `F` if and only if its diagonal image in
`∏_{P' ∣ P} F̂'_{P'}` is linearly independent over `F̂_P`. Together with
`TauCeti.Place.span_completionEmbedding_pi_eq_top`, the diagonal image of an `F`-basis of `F'` is
an `F̂_P`-basis: this is the semilocal decomposition `F̂_P ⊗_F F' ≅ ∏_{P' ∣ P} F̂'_{P'}`. For a
separable `F' / F` this holds without assuming that `F / k` is a function field; that is
`TauCeti.Place.linearIndependent_completionEmbedding_pi_iff_of_isSeparable`. -/
theorem linearIndependent_completionEmbedding_pi_iff (hF : IsFunctionField k F)
    {ι' : Type*} {v : ι' → F'} :
    letI := fun P' : {P' : Place k' F' // P'.restrict k F = P} ↦
      P.completionExtensionAlgebra P'.1 P'.2
    LinearIndependent P.Completion
        (fun (i : ι') (P' : {P' : Place k' F' // P'.restrict k F = P}) ↦
          P'.1.completionEmbedding (v i)) ↔
      LinearIndependent F v :=
  linearIndependent_completionEmbedding_pi_iff_of_finsum k' P
    (finsum_finrank_completion_eq_finrank k' F' P hF)

/-- **The trace formula**: for a finite separable extension `F' / F` whose constant field
extension `k' / k` is integral and a place `P` of `F`, the trace of `x ∈ F'` over `F` is, in the
completion at `P`, the sum of the traces of `x` over the completions `F̂'_{P'} / F̂_P` at the places
`P'` above `P`. For an algebraic function field `F / k` separability is not needed; that is
`TauCeti.Place.completionEmbedding_trace`. -/
theorem completionEmbedding_trace_of_isSeparable [Algebra.IsSeparable F F'] (x : F') :
    P.completionEmbedding (Algebra.trace F F' x) =
      ∑ᶠ P' : {P' : Place k' F' // P'.restrict k F = P},
        (letI := P.completionExtensionAlgebra P'.1 P'.2
        Algebra.trace P.Completion P'.1.Completion (P'.1.completionEmbedding x)) :=
  completionEmbedding_trace_of_finsum k' P
    (finsum_finrank_completion_eq_finrank_of_isSeparable k' F' P) x

/-- **The trace formula**: for an algebraic function field `F / k`, a finite extension `F' / F`
whose constant field extension `k' / k` is integral and a place `P` of `F`, the trace of `x ∈ F'`
over `F` is, in the completion at `P`, the sum of the traces of `x` over the completions
`F̂'_{P'} / F̂_P` at the places `P'` above `P`. No separability hypothesis is needed. For a
separable `F' / F` this holds without assuming that `F / k` is a function field; that is
`TauCeti.Place.completionEmbedding_trace_of_isSeparable`. -/
theorem completionEmbedding_trace (hF : IsFunctionField k F) (x : F') :
    P.completionEmbedding (Algebra.trace F F' x) =
      ∑ᶠ P' : {P' : Place k' F' // P'.restrict k F = P},
        (letI := P.completionExtensionAlgebra P'.1 P'.2
        Algebra.trace P.Completion P'.1.Completion (P'.1.completionEmbedding x)) :=
  completionEmbedding_trace_of_finsum k' P (finsum_finrank_completion_eq_finrank k' F' P hF) x

end Dimension

end FamilySemilocal

noncomputable section BundledSemilocal

section FibreInstances

variable {k k' F F' : Type*} [Field k] [Field k'] [Field F] [Field F']
  [Algebra k F] [Algebra k k'] [Algebra k' F'] [Algebra k F'] [Algebra F F']
  [IsScalarTower k k' F'] [IsScalarTower k F F'] [Algebra.IsIntegral F F']
  {P : Place k F} (w : {Q' : Place k' F' // Q'.restrict k F = P})

/-- For a place `w` in the fibre over `P`, `w.1.Completion` is a `P.Completion`-algebra in the
`PlaceCompletionExtension` scope. -/
@[expose, instance_reducible]
def instCompletionExtensionAlgebraSubtype : Algebra P.Completion w.1.Completion :=
  P.completionExtensionAlgebra w.1 w.2

scoped[PlaceCompletionExtension] attribute [instance]
  TauCeti.Place.instCompletionExtensionAlgebraSubtype

/-- For a place `w` in the fibre over `P`, `w.1.completionPlace.integers` is a
`P.completionPlace.integers`-algebra in the `PlaceCompletionExtension` scope. -/
@[expose, instance_reducible]
def instCompletionIntegersExtensionAlgebraSubtype :
    Algebra P.completionPlace.integers w.1.completionPlace.integers :=
  P.completionIntegersExtensionAlgebra w.1 w.2

scoped[PlaceCompletionExtension] attribute [instance]
  TauCeti.Place.instCompletionIntegersExtensionAlgebraSubtype

open scoped PlaceCompletionExtension in
theorem algebraMap_completionExtensionAlgebra_subtype :
    algebraMap P.Completion w.1.Completion = P.completionExtension w.1 w.2 :=
  P.algebraMap_completionExtensionAlgebra w.1 w.2

open scoped PlaceCompletionExtension in
theorem algebraMap_completionIntegersExtensionAlgebra_subtype :
    algebraMap P.completionPlace.integers w.1.completionPlace.integers =
      P.completionIntegersExtension w.1 w.2 :=
  P.algebraMap_completionIntegersExtensionAlgebra w.1 w.2

open scoped PlaceCompletionExtension in
theorem isTorsionFree_completionIntegers_subtype :
    Module.IsTorsionFree P.completionPlace.integers w.1.completionPlace.integers :=
  P.isTorsionFree_completionIntegersExtensionAlgebra w.1 w.2

scoped[PlaceCompletionExtension] attribute [instance]
  TauCeti.Place.isTorsionFree_completionIntegers_subtype

open scoped PlaceCompletionExtension in
theorem isScalarTower_completionIntegers_subtype :
    IsScalarTower P.completionPlace.integers w.1.completionPlace.integers w.1.Completion :=
  P.isScalarTower_completionIntegersExtensionAlgebra w.1 w.2

scoped[PlaceCompletionExtension] attribute [instance]
  TauCeti.Place.isScalarTower_completionIntegers_subtype

variable [FiniteDimensional F F']

open scoped PlaceCompletionExtension in
theorem finiteDimensional_completion_subtype :
    FiniteDimensional P.Completion w.1.Completion :=
  P.finiteDimensional_completion w.1 w.2

scoped[PlaceCompletionExtension] attribute [instance]
  TauCeti.Place.finiteDimensional_completion_subtype

open scoped PlaceCompletionExtension in
theorem moduleFinite_completionIntegers_subtype :
    Module.Finite P.completionPlace.integers w.1.completionPlace.integers :=
  P.moduleFinite_completionIntegers w.1 w.2

scoped[PlaceCompletionExtension] attribute [instance]
  TauCeti.Place.moduleFinite_completionIntegers_subtype

open scoped PlaceCompletionExtension in
theorem moduleFree_completionIntegers_subtype :
    Module.Free P.completionPlace.integers w.1.completionPlace.integers :=
  P.moduleFree_completionIntegers w.1 w.2

scoped[PlaceCompletionExtension] attribute [instance]
  TauCeti.Place.moduleFree_completionIntegers_subtype

end FibreInstances

open scoped PlaceCompletionExtension

attribute [local instance 10] algebraIntegersExtension isScalarTowerIntegersExtension

section ToField

variable {k : Type*} {F : Type*} (F' : Type*)
  [Field k] [Field F] [Field F'] [Algebra k F] [Algebra F F']
  (P : Place k F)

/-- The canonical `P.integers`-algebra homomorphism from the integral tensor product
`P.completionPlace.integers ⊗[P.integers] integralClosure P.integers F'` to the field tensor
product `P.Completion ⊗[F] F'`. -/
def completionIntegersSemilocalToField :
    P.completionPlace.integers ⊗[P.integers] integralClosure P.integers F' →ₐ[P.integers]
      P.Completion ⊗[F] F' :=
  Algebra.TensorProduct.lift
    ((Algebra.TensorProduct.includeLeft : P.Completion →ₐ[F] P.Completion ⊗[F] F').restrictScalars
      P.integers |>.comp (IsScalarTower.toAlgHom P.integers P.completionPlace.integers
        P.Completion))
    ((Algebra.TensorProduct.includeRight : F' →ₐ[F] P.Completion ⊗[F] F').restrictScalars
      P.integers |>.comp (IsScalarTower.toAlgHom P.integers (integralClosure P.integers F') F'))
    fun _ _ ↦ .all _ _

variable {F' P} in
/-- The map to the field tensor product on a pure tensor. -/
@[simp]
theorem completionIntegersSemilocalToField_tmul (a : P.completionPlace.integers)
    (x : integralClosure P.integers F') :
    completionIntegersSemilocalToField F' P (a ⊗ₜ x) = (a : P.Completion) ⊗ₜ[F] (x : F') := by
  simp [completionIntegersSemilocalToField]

/-- The canonical map from the integral tensor product to the field tensor product is injective. -/
theorem completionIntegersSemilocalToField_injective :
    Function.Injective (completionIntegersSemilocalToField F' P) := by
  -- `F` is the fraction field of `P.integers`, so tensoring over `F` agrees with tensoring over
  -- `P.integers`, and both `P.Completion` and `F'` are torsion-free hence flat over the Dedekind
  -- domain `P.integers`.
  have := IsLocalization.tensorProduct_compatibleSMul P.integers⁰ F P.Completion F'
  let e : (P.Completion ⊗[F] F') →ₗ[P.integers] (P.Completion ⊗[P.integers] F') :=
    TensorProduct.mapOfCompatibleSMul P.integers F P.integers P.Completion F'
  let f₁ : P.completionPlace.integers →ₗ[P.integers] P.Completion :=
    (IsScalarTower.toAlgHom P.integers P.completionPlace.integers P.Completion).toLinearMap
  let f₂ : integralClosure P.integers F' →ₗ[P.integers] F' :=
    (IsScalarTower.toAlgHom P.integers (integralClosure P.integers F') F').toLinearMap
  have hcomp : e.comp (completionIntegersSemilocalToField F' P).toLinearMap =
      TensorProduct.map f₁ f₂ :=
    TensorProduct.ext' fun a x ↦ by simp [e, f₁, f₂]
  have hinj : Function.Injective (TensorProduct.map f₁ f₂) :=
    TensorProduct.map_injective_of_flat_flat f₁ f₂ Subtype.val_injective Subtype.val_injective
  intro x y hxy
  exact hinj <| DFunLike.congr_fun hcomp x ▸ DFunLike.congr_fun hcomp y ▸ congrArg e hxy

/-- The trace of a pure integral tensor paired with a global element is a scalar extension of the
global trace pairing. -/
theorem trace_completionIntegersSemilocalToField_tmul_mul
    (a : P.completionPlace.integers) (x : integralClosure P.integers F') (d : F') :
    Algebra.trace P.Completion (P.Completion ⊗[F] F')
        (completionIntegersSemilocalToField F' P (a ⊗ₜ x) * (1 ⊗ₜ d)) =
      (a : P.Completion) * P.completionEmbedding (Algebra.trace F F' ((x : F') * d)) := by
  simpa only [ValuationSubring.algebraMap_apply, Subalgebra.algebraMap_apply,
    algebraMap_completionFieldAlgebra] using
    Algebra.trace_map_tmul_mul (K := F) (A := P.Completion) (B := F')
      (completionIntegersSemilocalToField F' P)
      (fun b y ↦ completionIntegersSemilocalToField_tmul b y) a x d

end ToField

section Semilocal

variable {k : Type*} (k' : Type*) {F : Type*} (F' : Type*)
  [Field k] [Field k'] [Field F] [Field F']
  [Algebra k F] [Algebra k k'] [Algebra k' F'] [Algebra k F'] [Algebra F F']
  [IsScalarTower k k' F'] [IsScalarTower k F F']
  (P : Place k F)

section Maps

variable [Algebra.IsIntegral F F']

/-- The canonical semilocal map `P.Completion ⊗[F] F' →ₐ[P.Completion] ∏_{w ∣ P} w.1.Completion`
sending `a ⊗ x` to `(a · x)_w`. -/
def completionSemilocalHom :
    P.Completion ⊗[F] F' →ₐ[P.Completion]
      ((w : {Q' : Place k' F' // Q'.restrict k F = P}) → w.1.Completion) :=
  letI (w : {Q' : Place k' F' // Q'.restrict k F = P}) : Algebra F w.1.Completion :=
    letI := WithVal.uniformContinuousConstSMul (S := F) w.1.valuation
    UniformSpace.Completion.algebra (WithVal w.1.valuation) F
  letI (w : {Q' : Place k' F' // Q'.restrict k F = P}) :
      IsScalarTower F F' w.1.Completion :=
    IsScalarTower.of_algebraMap_eq fun x ↦
      congrArg (UniformSpace.Completion.coeRingHom (α := WithVal w.1.valuation))
        (IsScalarTower.algebraMap_apply F F' (WithVal w.1.valuation) x)
  letI (w : {Q' : Place k' F' // Q'.restrict k F = P}) :
      IsScalarTower F P.Completion w.1.Completion :=
    IsScalarTower.of_algebraMap_eq fun x ↦ by
      rw [IsScalarTower.algebraMap_apply F F' w.1.Completion, algebraMap_completionFieldAlgebra,
        algebraMap_completionExtensionAlgebra_subtype, algebraMap_completionFieldAlgebra,
        P.completionExtension_completionEmbedding w.1 w.2]
  Algebra.TensorProduct.lift (Algebra.ofId _ _)
    (AlgHom.pi fun w ↦ IsScalarTower.toAlgHom F F' w.1.Completion)
    fun _ _ ↦ .all _ _

variable {k' F' P} in
/-- The semilocal map on a pure tensor. -/
@[simp]
theorem completionSemilocalHom_tmul (a : P.Completion) (x : F')
    (w : {Q' : Place k' F' // Q'.restrict k F = P}) :
    completionSemilocalHom k' F' P (a ⊗ₜ x) w =
      P.completionExtension w.1 w.2 a * w.1.completionEmbedding x := by
  simp [completionSemilocalHom, algebraMap_completionExtensionAlgebra_subtype]

/-- The canonical integral semilocal map from
`P.completionPlace.integers ⊗[P.integers] integralClosure P.integers F'` to
`∏_{w ∣ P} w.1.completionPlace.integers`. -/
def completionIntegersSemilocalHom :
    P.completionPlace.integers ⊗[P.integers] integralClosure P.integers F'
      →ₐ[P.completionPlace.integers]
        ((w : {Q' : Place k' F' // Q'.restrict k F = P}) → w.1.completionPlace.integers) :=
  letI (w : {Q' : Place k' F' // Q'.restrict k F = P}) :
      Algebra P.integers w.1.completionPlace.integers :=
    ((algebraMap P.completionPlace.integers w.1.completionPlace.integers).comp
      (algebraMap P.integers P.completionPlace.integers)).toAlgebra
  letI (w : {Q' : Place k' F' // Q'.restrict k F = P}) :
      IsScalarTower P.integers P.completionPlace.integers w.1.completionPlace.integers :=
    IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  Algebra.TensorProduct.lift (Algebra.ofId _ _)
    (AlgHom.pi fun w ↦
      { P.integralClosureToCompletionIntegers w.1 w.2 with
        commutes' := fun r ↦ by
          rw [RingHom.toFun_eq_coe, IsScalarTower.algebraMap_apply P.integers
              P.completionPlace.integers w.1.completionPlace.integers,
            algebraMap_completionIntegersExtensionAlgebra_subtype,
            algebraMap_completionIntegersAlgebra]
          exact P.integralClosureToCompletionIntegers_algebraMap w.1 w.2 r })
    fun _ _ ↦ .all _ _

variable {k' F' P} in
/-- The integral semilocal map on a pure tensor. -/
@[simp]
theorem completionIntegersSemilocalHom_tmul (a : P.completionPlace.integers)
    (x : integralClosure P.integers F')
    (w : {Q' : Place k' F' // Q'.restrict k F = P}) :
    completionIntegersSemilocalHom k' F' P (a ⊗ₜ x) w =
      P.completionIntegersExtension w.1 w.2 a *
        P.integralClosureToCompletionIntegers w.1 w.2 x := by
  simp [completionIntegersSemilocalHom, algebraMap_completionIntegersExtensionAlgebra_subtype]

variable {k' F' P} in
/-- After inclusion into the completions, the integral and field semilocal maps agree. -/
theorem completionIntegersSemilocalHom_fieldCompatibility
    (z : P.completionPlace.integers ⊗[P.integers] integralClosure P.integers F') :
    completionSemilocalHom k' F' P (completionIntegersSemilocalToField F' P z) =
      fun w ↦ (completionIntegersSemilocalHom k' F' P z w : w.1.Completion) := by
  induction z using TensorProduct.inductionOn with
  | add x y hx hy =>
    funext w
    simp [congrFun hx w, congrFun hy w]
  | tmul a x =>
    funext w
    simp

end Maps

section Surjective

variable [FiniteDimensional F F']

/-- **The field semilocal map is surjective** for any finite extension `F' / F`: every family of
elements in the completions above `P` lies in the image of `P.Completion ⊗[F] F'`. -/
theorem completionSemilocalHom_surjective :
    Function.Surjective (completionSemilocalHom k' F' P) := by
  rw [← AlgHom.coe_toLinearMap, ← LinearMap.range_eq_top, eq_top_iff,
    ← span_completion_pi_eq_top k' F' P, Submodule.span_le]
  rintro _ ⟨y, rfl⟩
  exact ⟨1 ⊗ₜ y, funext fun w ↦ by simp⟩

/-- **The integral semilocal map is surjective** for any finite extension `F' / F` over an
integral constant extension `k' / k` (requiring neither separability of `F' / F` nor a
function-field hypothesis). -/
theorem completionIntegersSemilocalHom_surjective [Algebra.IsIntegral k k'] :
    Function.Surjective (completionIntegersSemilocalHom k' F' P) := by
  -- Functions regular above `P` span the product of completed valuation rings over `𝒪̂_P`, and
  -- every such function belongs to `integralClosure P.integers F'`.
  rw [← AlgHom.coe_toLinearMap, ← LinearMap.range_eq_top, eq_top_iff,
    ← span_completionIntegers_pi_eq_top k' F' P, Submodule.span_le]
  rintro _ ⟨y, rfl⟩
  have hy : IsIntegral P.integers y.1 :=
    (isIntegral_iff_forall_restrict_eq_mem_integers_of_finiteDimensional (k' := k') P).mpr
      fun P' hP' ↦ y.2 ⟨P', hP'⟩
  refine ⟨1 ⊗ₜ ⟨y.1, hy⟩, funext fun w ↦ Subtype.ext ?_⟩
  simp

end Surjective

section BijectiveHelpers

variable [FiniteDimensional F F']

private theorem completionSemilocalHom_injective_of_finsum
    (hdeg : ∑ᶠ w : {Q' : Place k' F' // Q'.restrict k F = P},
      finrank P.Completion w.1.Completion = finrank F F') :
    Function.Injective (completionSemilocalHom k' F' P) := by
  -- Domain and codomain have the same finite dimension over `P.Completion`, and the map is
  -- surjective.
  have := Fintype.ofFinite {Q' : Place k' F' // Q'.restrict k F = P}
  have hdim : finrank P.Completion (P.Completion ⊗[F] F') =
      finrank P.Completion ((w : {Q' : Place k' F' // Q'.restrict k F = P}) → w.1.Completion) := by
    rw [Module.finrank_pi_fintype, Module.finrank_baseChange, ← hdeg, finsum_eq_sum_of_fintype]
  exact (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hdim
    (f := (completionSemilocalHom k' F' P).toLinearMap)).mpr
    (completionSemilocalHom_surjective k' F' P)

private theorem completionIntegersSemilocalHom_injective_of_fieldInjective
    (hinj : Function.Injective (completionSemilocalHom k' F' P)) :
    Function.Injective (completionIntegersSemilocalHom k' F' P) := fun x y hxy ↦ by
  -- The integral tensor product embeds into the field tensor product, where
  -- `completionSemilocalHom` is injective.
  apply completionIntegersSemilocalToField_injective F' P
  apply hinj
  rw [completionIntegersSemilocalHom_fieldCompatibility,
    completionIntegersSemilocalHom_fieldCompatibility, hxy]

private theorem norm_eq_finprod_norm_of_algEquiv
    (e : P.Completion ⊗[F] F' ≃ₐ[P.Completion]
      ((w : {Q' : Place k' F' // Q'.restrict k F = P}) → w.1.Completion))
    (ξ : P.Completion ⊗[F] F') :
    Algebra.norm P.Completion ξ =
      ∏ᶠ w : {Q' : Place k' F' // Q'.restrict k F = P},
        Algebra.norm P.Completion (e ξ w) := by
  have := Fintype.ofFinite {Q' : Place k' F' // Q'.restrict k F = P}
  rw [finprod_eq_prod_of_fintype, ← Algebra.norm_eq_of_algEquiv e]
  exact Algebra.norm_pi _

private theorem completionEmbedding_norm_of_algEquiv
    (e : P.Completion ⊗[F] F' ≃ₐ[P.Completion]
      ((w : {Q' : Place k' F' // Q'.restrict k F = P}) → w.1.Completion))
    (he : ∀ (x : F') (w : {Q' : Place k' F' // Q'.restrict k F = P}),
      e (1 ⊗ₜ x) w = w.1.completionEmbedding x)
    (x : F') :
    P.completionEmbedding (Algebra.norm F x) =
      ∏ᶠ w : {Q' : Place k' F' // Q'.restrict k F = P},
        Algebra.norm P.Completion (w.1.completionEmbedding x) := by
  rw [← algebraMap_completionFieldAlgebra,
    ← Algebra.norm_baseChange_tmul (A := P.Completion) (B := F') x,
    norm_eq_finprod_norm_of_algEquiv k' F' P e]
  exact finprod_congr fun w ↦ by rw [he]

end BijectiveHelpers

section EquivFunctionField

variable [FiniteDimensional F F'] [Algebra.IsIntegral k k']

/-- **The field semilocal map is injective** for an algebraic function field `F / k` and a finite
extension `F' / F` whose constant extension `k' / k` is integral, with no separability
hypothesis. For `F' / F` separable without assuming `IsFunctionField k F`, see
`TauCeti.Place.completionSemilocalHom_injective_of_isSeparable`. -/
theorem completionSemilocalHom_injective (hF : IsFunctionField k F) :
    Function.Injective (completionSemilocalHom k' F' P) :=
  completionSemilocalHom_injective_of_finsum k' F' P
    (finsum_finrank_completion_eq_finrank k' F' P hF)

/-- **The field semilocal map is bijective** for an algebraic function field `F / k` and a finite
extension `F' / F` whose constant extension `k' / k` is integral. -/
theorem completionSemilocalHom_bijective (hF : IsFunctionField k F) :
    Function.Bijective (completionSemilocalHom k' F' P) :=
  ⟨completionSemilocalHom_injective k' F' P hF, completionSemilocalHom_surjective k' F' P⟩

/-- **The semilocal decomposition at a place of an algebraic function field**, with no separability
hypothesis on the finite extension `F' / F` (over an integral constant extension `k' / k`). -/
def completionSemilocalEquivOfIsFunctionField (hF : IsFunctionField k F) :
    P.Completion ⊗[F] F' ≃ₐ[P.Completion]
      ((w : {Q' : Place k' F' // Q'.restrict k F = P}) → w.1.Completion) :=
  AlgEquiv.ofBijective (completionSemilocalHom k' F' P)
    (completionSemilocalHom_bijective k' F' P hF)

theorem coe_completionSemilocalEquivOfIsFunctionField (hF : IsFunctionField k F) :
    ⇑(completionSemilocalEquivOfIsFunctionField k' F' P hF) = completionSemilocalHom k' F' P := by
  rw [completionSemilocalEquivOfIsFunctionField, AlgEquiv.coe_ofBijective]

variable {k' F' P} in
/-- `completionSemilocalEquivOfIsFunctionField` on a pure tensor. -/
@[simp]
theorem completionSemilocalEquivOfIsFunctionField_tmul (hF : IsFunctionField k F)
    (a : P.Completion) (x : F') (w : {Q' : Place k' F' // Q'.restrict k F = P}) :
    completionSemilocalEquivOfIsFunctionField k' F' P hF (a ⊗ₜ x) w =
      P.completionExtension w.1 w.2 a * w.1.completionEmbedding x := by
  rw [completionSemilocalEquivOfIsFunctionField, AlgEquiv.ofBijective_apply]
  exact completionSemilocalHom_tmul a x w

/-- The inverse of `completionSemilocalEquivOfIsFunctionField` sends a diagonal field element to
`1 ⊗ x`. -/
@[simp]
theorem completionSemilocalEquivOfIsFunctionField_symm_completionEmbedding
    (hF : IsFunctionField k F) (x : F') :
    (completionSemilocalEquivOfIsFunctionField k' F' P hF).symm
      (fun w : {Q' : Place k' F' // Q'.restrict k F = P} ↦ w.1.completionEmbedding x) =
        1 ⊗ₜ[F] x := by
  apply (completionSemilocalEquivOfIsFunctionField k' F' P hF).symm_apply_eq.mpr
  funext w
  simp

/-- **The integral semilocal map is injective** for an algebraic function field `F / k` and a
finite extension `F' / F` whose constant extension `k' / k` is integral, with no separability
hypothesis. For `F' / F` separable without assuming `IsFunctionField k F`, see
`TauCeti.Place.completionIntegersSemilocalHom_injective_of_isSeparable`. -/
theorem completionIntegersSemilocalHom_injective (hF : IsFunctionField k F) :
    Function.Injective (completionIntegersSemilocalHom k' F' P) :=
  completionIntegersSemilocalHom_injective_of_fieldInjective k' F' P
    (completionSemilocalHom_injective k' F' P hF)

/-- **The integral semilocal map is bijective** for an algebraic function field `F / k` and a
finite extension `F' / F` whose constant extension `k' / k` is integral. -/
theorem completionIntegersSemilocalHom_bijective (hF : IsFunctionField k F) :
    Function.Bijective (completionIntegersSemilocalHom k' F' P) :=
  ⟨completionIntegersSemilocalHom_injective k' F' P hF,
    completionIntegersSemilocalHom_surjective k' F' P⟩

/-- **The integral semilocal decomposition at a place of an algebraic function field**, with no
separability hypothesis on the finite extension `F' / F` (over an integral constant extension
`k' / k`). -/
def completionIntegersSemilocalEquivOfIsFunctionField (hF : IsFunctionField k F) :
    P.completionPlace.integers ⊗[P.integers] integralClosure P.integers F'
      ≃ₐ[P.completionPlace.integers]
        ((w : {Q' : Place k' F' // Q'.restrict k F = P}) → w.1.completionPlace.integers) :=
  AlgEquiv.ofBijective (completionIntegersSemilocalHom k' F' P)
    (completionIntegersSemilocalHom_bijective k' F' P hF)

theorem coe_completionIntegersSemilocalEquivOfIsFunctionField (hF : IsFunctionField k F) :
    ⇑(completionIntegersSemilocalEquivOfIsFunctionField k' F' P hF) =
      completionIntegersSemilocalHom k' F' P := by
  rw [completionIntegersSemilocalEquivOfIsFunctionField, AlgEquiv.coe_ofBijective]

variable {k' F' P} in
/-- `completionIntegersSemilocalEquivOfIsFunctionField` on a pure tensor. -/
@[simp]
theorem completionIntegersSemilocalEquivOfIsFunctionField_tmul (hF : IsFunctionField k F)
    (a : P.completionPlace.integers) (x : integralClosure P.integers F')
    (w : {Q' : Place k' F' // Q'.restrict k F = P}) :
    completionIntegersSemilocalEquivOfIsFunctionField k' F' P hF (a ⊗ₜ x) w =
      P.completionIntegersExtension w.1 w.2 a *
        P.integralClosureToCompletionIntegers w.1 w.2 x := by
  rw [completionIntegersSemilocalEquivOfIsFunctionField, AlgEquiv.ofBijective_apply]
  exact completionIntegersSemilocalHom_tmul a x w

/-- The inverse of `completionIntegersSemilocalEquivOfIsFunctionField` sends a diagonal integral
element to `1 ⊗ x`. -/
@[simp]
theorem completionIntegersSemilocalEquivOfIsFunctionField_symm_integralClosureToCompletionIntegers
    (hF : IsFunctionField k F) (x : integralClosure P.integers F') :
    (completionIntegersSemilocalEquivOfIsFunctionField k' F' P hF).symm
      (fun w : {Q' : Place k' F' // Q'.restrict k F = P} ↦
        P.integralClosureToCompletionIntegers w.1 w.2 x) = 1 ⊗ₜ[P.integers] x := by
  apply (completionIntegersSemilocalEquivOfIsFunctionField k' F' P hF).symm_apply_eq.mpr
  funext w
  simp

/-- **Global norm equals the product of local norms** above `P` for an algebraic function field
`F / k` and a finite extension `F' / F` whose constant extension `k' / k` is integral, with no
separability hypothesis. For `F' / F` separable without assuming `IsFunctionField k F`, see
`TauCeti.Place.completionEmbedding_norm_of_isSeparable`. -/
theorem completionEmbedding_norm (hF : IsFunctionField k F) (x : F') :
    P.completionEmbedding (Algebra.norm F x) =
      ∏ᶠ w : {Q' : Place k' F' // Q'.restrict k F = P},
        Algebra.norm P.Completion (w.1.completionEmbedding x) :=
  completionEmbedding_norm_of_algEquiv k' F' P
    (completionSemilocalEquivOfIsFunctionField k' F' P hF) (fun y w ↦ by simp) x

end EquivFunctionField

section Equiv

variable [FiniteDimensional F F'] [Algebra.IsSeparable F F'] [Algebra.IsIntegral k k']

/-- **The field semilocal map is injective** for a finite separable extension `F' / F` whose
constant extension `k' / k` is integral. For an algebraic function field `F / k`, separability is
not needed (`TauCeti.Place.completionSemilocalHom_injective`). -/
theorem completionSemilocalHom_injective_of_isSeparable :
    Function.Injective (completionSemilocalHom k' F' P) :=
  completionSemilocalHom_injective_of_finsum k' F' P
    (finsum_finrank_completion_eq_finrank_of_isSeparable k' F' P)

/-- **The field semilocal map is bijective** for a finite separable extension `F' / F` whose
constant extension `k' / k` is integral. -/
theorem completionSemilocalHom_bijective_of_isSeparable :
    Function.Bijective (completionSemilocalHom k' F' P) :=
  ⟨completionSemilocalHom_injective_of_isSeparable k' F' P,
    completionSemilocalHom_surjective k' F' P⟩

/-- **The semilocal decomposition at a place**: `P.Completion ⊗[F] F' ≃ₐ[P.Completion]
∏_{w ∣ P} w.1.Completion` for a finite separable extension `F' / F` over an integral constant
extension `k' / k`. -/
def completionSemilocalEquiv :
    P.Completion ⊗[F] F' ≃ₐ[P.Completion]
      ((w : {Q' : Place k' F' // Q'.restrict k F = P}) → w.1.Completion) :=
  AlgEquiv.ofBijective (completionSemilocalHom k' F' P)
    (completionSemilocalHom_bijective_of_isSeparable k' F' P)

theorem coe_completionSemilocalEquiv :
    ⇑(completionSemilocalEquiv k' F' P) = completionSemilocalHom k' F' P := by
  rw [completionSemilocalEquiv, AlgEquiv.coe_ofBijective]

variable {k' F' P} in
/-- The semilocal equivalence on a pure tensor. -/
@[simp]
theorem completionSemilocalEquiv_tmul (a : P.Completion) (x : F')
    (w : {Q' : Place k' F' // Q'.restrict k F = P}) :
    completionSemilocalEquiv k' F' P (a ⊗ₜ x) w =
      P.completionExtension w.1 w.2 a * w.1.completionEmbedding x := by
  rw [completionSemilocalEquiv, AlgEquiv.ofBijective_apply]
  exact completionSemilocalHom_tmul a x w

/-- The inverse semilocal equivalence sends a diagonal field element to `1 ⊗ x`. -/
@[simp]
theorem completionSemilocalEquiv_symm_completionEmbedding (x : F') :
    (completionSemilocalEquiv k' F' P).symm
      (fun w : {Q' : Place k' F' // Q'.restrict k F = P} ↦ w.1.completionEmbedding x) =
        1 ⊗ₜ[F] x := by
  apply (completionSemilocalEquiv k' F' P).symm_apply_eq.mpr
  funext w
  simp

/-- **The integral semilocal map is injective** for a finite separable extension `F' / F` whose
constant extension `k' / k` is integral. For an algebraic function field `F / k`, separability is
not needed (`TauCeti.Place.completionIntegersSemilocalHom_injective`). -/
theorem completionIntegersSemilocalHom_injective_of_isSeparable :
    Function.Injective (completionIntegersSemilocalHom k' F' P) :=
  completionIntegersSemilocalHom_injective_of_fieldInjective k' F' P
    (completionSemilocalHom_injective_of_isSeparable k' F' P)

/-- **The integral semilocal map is bijective** for a finite separable extension `F' / F` whose
constant extension `k' / k` is integral. -/
theorem completionIntegersSemilocalHom_bijective_of_isSeparable :
    Function.Bijective (completionIntegersSemilocalHom k' F' P) :=
  ⟨completionIntegersSemilocalHom_injective_of_isSeparable k' F' P,
    completionIntegersSemilocalHom_surjective k' F' P⟩

/-- **The integral semilocal decomposition at a place**:
`P.completionPlace.integers ⊗[P.integers] integralClosure P.integers F'
≃ₐ[P.completionPlace.integers] ∏_{w ∣ P} w.1.completionPlace.integers` for a finite separable
extension `F' / F` over an integral constant extension `k' / k`. -/
def completionIntegersSemilocalEquiv :
    P.completionPlace.integers ⊗[P.integers] integralClosure P.integers F'
      ≃ₐ[P.completionPlace.integers]
        ((w : {Q' : Place k' F' // Q'.restrict k F = P}) → w.1.completionPlace.integers) :=
  AlgEquiv.ofBijective (completionIntegersSemilocalHom k' F' P)
    (completionIntegersSemilocalHom_bijective_of_isSeparable k' F' P)

theorem coe_completionIntegersSemilocalEquiv :
    ⇑(completionIntegersSemilocalEquiv k' F' P) = completionIntegersSemilocalHom k' F' P := by
  rw [completionIntegersSemilocalEquiv, AlgEquiv.coe_ofBijective]

variable {k' F' P} in
/-- The integral semilocal equivalence on a pure tensor. -/
@[simp]
theorem completionIntegersSemilocalEquiv_tmul (a : P.completionPlace.integers)
    (x : integralClosure P.integers F')
    (w : {Q' : Place k' F' // Q'.restrict k F = P}) :
    completionIntegersSemilocalEquiv k' F' P (a ⊗ₜ x) w =
      P.completionIntegersExtension w.1 w.2 a *
        P.integralClosureToCompletionIntegers w.1 w.2 x := by
  rw [completionIntegersSemilocalEquiv, AlgEquiv.ofBijective_apply]
  exact completionIntegersSemilocalHom_tmul a x w

/-- The inverse integral semilocal equivalence sends a diagonal integral element to `1 ⊗ x`. -/
@[simp]
theorem completionIntegersSemilocalEquiv_symm_integralClosureToCompletionIntegers
    (x : integralClosure P.integers F') :
    (completionIntegersSemilocalEquiv k' F' P).symm
      (fun w : {Q' : Place k' F' // Q'.restrict k F = P} ↦
        P.integralClosureToCompletionIntegers w.1 w.2 x) = 1 ⊗ₜ[P.integers] x := by
  apply (completionIntegersSemilocalEquiv k' F' P).symm_apply_eq.mpr
  funext w
  simp

variable {k' F' P} in
/-- After inclusion into the completions, the integral semilocal equivalence agrees with the field
semilocal equivalence. -/
theorem completionIntegersSemilocalEquiv_fieldCompatibility
    (z : P.completionPlace.integers ⊗[P.integers] integralClosure P.integers F') :
    completionSemilocalEquiv k' F' P (completionIntegersSemilocalToField F' P z) =
      fun w ↦ (completionIntegersSemilocalEquiv k' F' P z w : w.1.Completion) := by
  rw [coe_completionSemilocalEquiv, coe_completionIntegersSemilocalEquiv]
  exact completionIntegersSemilocalHom_fieldCompatibility z

/-! ### Norm and trace in the semilocal decomposition -/

/-- The norm of `P.Completion ⊗[F] F'` over `P.Completion` is the product of the norms of its
semilocal components. -/
theorem norm_eq_finprod_norm_completionSemilocalEquiv (ξ : P.Completion ⊗[F] F') :
    Algebra.norm P.Completion ξ =
      ∏ᶠ w : {Q' : Place k' F' // Q'.restrict k F = P},
        Algebra.norm P.Completion (completionSemilocalEquiv k' F' P ξ w) :=
  norm_eq_finprod_norm_of_algEquiv k' F' P (completionSemilocalEquiv k' F' P) ξ

/-- **Global norm equals the product of local norms** above `P` for a finite separable extension
`F' / F` whose constant field extension `k' / k` is integral. For an algebraic function field
`F / k`, separability is not needed (`TauCeti.Place.completionEmbedding_norm`). -/
theorem completionEmbedding_norm_of_isSeparable (x : F') :
    P.completionEmbedding (Algebra.norm F x) =
      ∏ᶠ w : {Q' : Place k' F' // Q'.restrict k F = P},
        Algebra.norm P.Completion (w.1.completionEmbedding x) :=
  completionEmbedding_norm_of_algEquiv k' F' P
    (completionSemilocalEquiv k' F' P) (fun y w ↦ by simp) x

/-- The trace of `P.Completion ⊗[F] F'` over `P.Completion` is the sum of the traces of its
semilocal components. -/
theorem trace_eq_finsum_trace_completionSemilocalEquiv (ξ : P.Completion ⊗[F] F') :
    Algebra.trace P.Completion (P.Completion ⊗[F] F') ξ =
      ∑ᶠ w : {Q' : Place k' F' // Q'.restrict k F = P},
        Algebra.trace P.Completion w.1.Completion (completionSemilocalEquiv k' F' P ξ w) := by
  have := Fintype.ofFinite {Q' : Place k' F' // Q'.restrict k F = P}
  rw [finsum_eq_sum_of_fintype, ← Algebra.trace_eq_of_algEquiv (completionSemilocalEquiv k' F' P)]
  exact Algebra.trace_pi _

open scoped Classical in
/-- An element of `w.1.Completion`, placed in the `w`-component of `P.Completion ⊗[F] F'`, has the
same trace pairing with a global element as in `w.1.Completion`. -/
theorem trace_completionSemilocalEquiv_symm_single_mul
    (w : {Q' : Place k' F' // Q'.restrict k F = P}) (z : w.1.Completion) (x : F') :
    Algebra.trace P.Completion (P.Completion ⊗[F] F')
        ((completionSemilocalEquiv k' F' P).symm (Pi.single w z) * (1 ⊗ₜ x)) =
      Algebra.trace P.Completion w.1.Completion (z * w.1.completionEmbedding x) := by
  simpa using (completionSemilocalEquiv k' F' P).trace_symm_single_mul w z (1 ⊗ₜ x)

variable {k' F' P} in
/-- Each completed factor in the semilocal decomposition of a finite separable extension is
separable over `P.Completion`. -/
theorem isSeparable_completion_subtype
    (w : {Q' : Place k' F' // Q'.restrict k F = P}) :
    Algebra.IsSeparable P.Completion w.1.Completion := by
  have := Fintype.ofFinite {Q' : Place k' F' // Q'.restrict k F = P}
  have : Algebra.FormallyEtale F F' := Algebra.FormallyEtale.of_isSeparable F F'
  have hpi : Algebra.FormallyEtale P.Completion
      ((u : {Q' : Place k' F' // Q'.restrict k F = P}) → u.1.Completion) :=
    Algebra.FormallyEtale.of_equiv (completionSemilocalEquiv k' F' P)
  exact (Algebra.FormallyEtale.iff_isSeparable P.Completion w.1.Completion).mp
    ((Algebra.FormallyEtale.pi_iff (R := P.Completion)
      (A := fun u : {Q' : Place k' F' // Q'.restrict k F = P} ↦ u.1.Completion)).mp hpi w)

scoped[PlaceCompletionExtension] attribute [instance]
  TauCeti.Place.isSeparable_completion_subtype

end Equiv

end Semilocal

section SeparableCompletion

variable {k k' F F' : Type*} [Field k] [Field k'] [Field F] [Field F']
  [Algebra k F] [Algebra k k'] [Algebra k' F'] [Algebra k F'] [Algebra F F']
  [IsScalarTower k k' F'] [IsScalarTower k F F']
  [FiniteDimensional F F'] [Algebra.IsSeparable F F']
  (P : Place k F) (P' : Place k' F') (hP : P'.restrict k F = P)

/-- **Completion preserves separability of the field extension.** If `F' / F` is finite and
separable and `P'` lies over `P`, then `P'.Completion` is separable over `P.Completion` — with no
integrality hypothesis on `k' / k` and no separability hypothesis on the residue extension. -/
theorem isSeparable_completion :
    letI := P.completionExtensionAlgebra P' hP
    Algebra.IsSeparable P.Completion P'.Completion := by
  -- Restricting constants of `P'` to `k` via `TauCeti.Place.restrictScalars` places
  -- `(P'.restrictScalars k).Completion` as a factor of the formally étale `P.Completion`-algebra
  -- `P.Completion ⊗[F] F'`, and `completionExtensionRestrictScalarsEquiv` transports separability
  -- to `P'.Completion`.
  let P₀' : Place k F' := P'.restrictScalars k
  have hP₀ : P₀'.restrict k F = P := (P'.restrict_restrictScalars (k := k) (F := F)).trans hP
  let _ := P.completionExtensionAlgebra P' hP
  let _ := P.completionExtensionAlgebra P₀' hP₀
  have : Algebra.IsSeparable P.Completion P₀'.Completion :=
    isSeparable_completion_subtype ⟨P₀', hP₀⟩
  let e := P.completionExtensionRestrictScalarsEquiv P' hP
  exact Algebra.IsSeparable.of_equiv_equiv (.refl P.Completion) e.toRingEquiv
    (RingHom.ext fun z ↦ (e.commutes z).symm)

attribute [local instance] FractionRing.liftAlgebra FractionRing.isScalarTower_liftAlgebra in
/-- Separability of `P'.Completion / P.Completion`, transported to the canonical fraction fields
`FractionRing P.completionPlace.integers` and `FractionRing P'.completionPlace.integers` consumed
by Mathlib's `differentIdeal` API. -/
theorem isSeparable_fractionRing_completionIntegers :
    letI := P.completionIntegersExtensionAlgebra P' hP
    Algebra.IsSeparable (FractionRing P.completionPlace.integers)
      (FractionRing P'.completionPlace.integers) := by
  let _ := P.completionExtensionAlgebra P' hP
  let _ := P.completionIntegersExtensionAlgebra P' hP
  have : Algebra.IsSeparable P.Completion P'.Completion := isSeparable_completion P P' hP
  have : IsScalarTower P.completionPlace.integers P'.completionPlace.integers P'.Completion :=
    P.isScalarTower_completionIntegersExtensionAlgebra P' hP
  exact IsFractionRing.isSeparable_fractionRing P.completionPlace.integers
    P'.completionPlace.integers P.Completion P'.Completion

end SeparableCompletion

end BundledSemilocal

end TauCeti.Place

end
