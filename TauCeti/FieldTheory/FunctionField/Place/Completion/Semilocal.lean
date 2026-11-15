/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Dimension.OrzechProperty
public import Mathlib.RingTheory.Nakayama
public import TauCeti.FieldTheory.FunctionField.Place.Completion.Approximation
public import TauCeti.FieldTheory.FunctionField.Place.Completion.IntegralClosure
public import TauCeti.FieldTheory.FunctionField.Place.Extension.Fundamental
public import TauCeti.RingTheory.NormTrace.BaseChange
public import TauCeti.RingTheory.NormTrace.Pi
import Mathlib.LinearAlgebra.Dimension.Free
import TauCeti.FieldTheory.FunctionField.AffineModel.IntegralClosure
import TauCeti.FieldTheory.FunctionField.Place.Extension.IntegralBasis.Basic
import TauCeti.LinearAlgebra.Span.Basic
import TauCeti.RingTheory.DedekindDomain.IntegralClosure
import TauCeti.RingTheory.IntegralClosure.MvPolynomial
import TauCeti.RingTheory.Localization.Integral

/-!
# Semilocal decomposition, norm, and trace at a completed place

Let `F' / F` be a finite extension, `P` a place of `F / k`, and `P'` run over the finitely many
places of `F' / k'` lying over `P`. Each completion `F̂'_{P'}` is a finite extension of the
completion `F̂_P` (`TauCeti.Place.finrank_completion`), and the diagonal map
`F' → ∏_{P' ∣ P} F̂'_{P'}` compares the scalar extension of `F'` to `F̂_P` with the product of
completed extensions above `P`. No finiteness, compactness, or separability hypothesis on the
residue fields is needed.

This module develops the semilocal decomposition in both its unbundled family-of-vectors form and
its bundled tensor-product `AlgEquiv` form (over the valuation rings as well as over the fields):

* **Spanning and linear independence.** By weak approximation in the completions and Nakayama's
  lemma over `𝒪̂_P`, the functions of `F'` regular at every place over `P` span `∏_{P' ∣ P} 𝒪̂_{P'}`
  over `𝒪̂_P` (`TauCeti.Place.span_completionIntegers_pi_eq_top`), and `F'` spans
  `∏_{P' ∣ P} F̂'_{P'}` over `F̂_P` (`TauCeti.Place.span_completion_pi_eq_top`) assuming only
  `[FiniteDimensional F F']`. When `k' / k` is integral and either `F' / F` is separable or `F / k`
  is an algebraic function field, the fundamental identity gives `∑_{P' ∣ P} [F̂'_{P'} : F̂_P] =
  [F' : F]`, so linear independence over `F` is preserved in `∏_{P' ∣ P} F̂'_{P'}` and the trace
  formula `Tr_{F'/F} x = ∑_{P' ∣ P} Tr_{F̂'_{P'}/F̂_P} x` holds.
* **Bundled integral and field semilocal equivalences.** In the `PlaceCompletionExtension` scope,
  we register the algebra structures `F → F̂_P`, `𝒪_P → 𝒪̂_P`, and the factorwise extension algebras
  over `{P' : Place k' F' // P'.restrict k F = P}`. Whenever the local integral closure
  `𝒪'_P = integralClosure P.integers F'` is module-finite over `𝒪_P` — which holds automatically
  when `F' / F` is separable (`TauCeti.Place.moduleFinite_integralClosure`) and for every finite
  extension of an algebraic function field
  (`TauCeti.Place.moduleFinite_integralClosure_of_isFunctionField`) — completing along `P` gives
  isomorphisms
  ```text
  𝒪̂_P ⊗[𝒪_P] 𝒪'_P ≃ₐ[𝒪̂_P] ∏_{Q ∣ P} 𝒪̂_Q,
  F̂_P ⊗[F] F'     ≃ₐ[F̂_P] ∏_{Q ∣ P} F̂_Q,
  ```
  compatible with inclusion into the completions, together with the local–global norm formula and
  componentwise trace-pairing identities used to localize the complementary module and different at
  a completion.

## Main definitions

* `TauCeti.Place.integralCompletionSemilocalHom` and
  `TauCeti.Place.integralCompletionSemilocalEquiv`: the integral semilocal map and isomorphism
  `𝒪̂_P ⊗[𝒪_P] 𝒪'_P ≃ₐ[𝒪̂_P] ∀ Q : {P' // P'.restrict k F = P}, 𝒪̂_Q`.
* `TauCeti.Place.completionSemilocalHom` and `TauCeti.Place.completionSemilocalEquiv`: the field
  semilocal map and isomorphism `F̂_P ⊗[F] F' ≃ₐ[F̂_P] ∀ Q : {P' // P'.restrict k F = P}, F̂_Q`.
* `TauCeti.Place.integralCompletionSemilocalToField`: the canonical injection
  `𝒪̂_P ⊗[𝒪_P] 𝒪'_P →ₐ[𝒪_P] F̂_P ⊗[F] F'`.

## Main results

* `TauCeti.Place.span_completionIntegers_pi_eq_top`, `TauCeti.Place.span_completion_pi_eq_top`,
  and `TauCeti.Place.span_completionEmbedding_pi_eq_top`: spanning of `∏_{P' ∣ P} 𝒪̂_{P'}` and
  `∏_{P' ∣ P} F̂'_{P'}` by diagonal images from `F'`.
* `TauCeti.Place.finsum_finrank_completion_eq_finrank`,
  `TauCeti.Place.finsum_finrank_completion_eq_finrank_of_isSeparable`, and
  `TauCeti.Place.finsum_finrank_completion_eq_finrank_of_moduleFinite`: the local degrees above `P`
  add up to `[F' : F]`.
* `TauCeti.Place.linearIndependent_completionEmbedding_pi_iff` and
  `TauCeti.Place.linearIndependent_completionEmbedding_pi_iff_of_isSeparable`: linear independence
  survives completion at `P`.
* `TauCeti.Place.completionEmbedding_trace` and
  `TauCeti.Place.completionEmbedding_trace_of_isSeparable`: **the trace formula**
  `Tr_{F'/F} x = ∑_{P' ∣ P} Tr_{F̂'_{P'}/F̂_P} x`.
* `TauCeti.Place.moduleFinite_integralClosure_of_isFunctionField`: `𝒪'_P` is module-finite over
  `𝒪_P` for any finite extension of a function field, without separability.
* `TauCeti.Place.mem_integralClosure_iff_forall_restrict_eq_mem_integers`: for any finite extension
  `F' / F` over an integral constant extension, `𝒪'_P` is the intersection of `𝒪_{P'}` over
  `P' ∣ P`.
* `TauCeti.Place.integralCompletionSemilocalEquiv_fieldCompatibility` and
  `TauCeti.Place.integralCompletionSemilocalToField_injective`: compatibility of the integral and
  field semilocal equivalences.
* `TauCeti.Place.completionEmbedding_norm`,
  `TauCeti.Place.completionEmbedding_norm_of_isSeparable`, and
  `TauCeti.Place.completionEmbedding_norm_of_moduleFinite`: **the norm formula**
  `N_{F'/F} x = ∏_{P' ∣ P} N_{F̂'_{P'}/F̂_P} x`.
* `TauCeti.Place.trace_completionSemilocalEquiv_symm_single_mul` and
  `TauCeti.Place.trace_integralCompletionSemilocalToField_tmul_mul`: componentwise and integral
  trace-pairing formulas.

## References

* H. Stichtenoth, *Algebraic Function Fields and Codes*, 2nd ed., GTM 254, Springer, 2009,
  Sections III.1, III.4, and IV.2.
* [J.-P. Serre, *Local Fields*][serre1968], Chapter II, §3, Theorem 1 and Corollary 4.
* [J. Neukirch, *Algebraic Number Theory*][Neukirch1992], Chapter II, Proposition (8.3).
* Adapted in part from `TauCeti/NumberTheory/NumberField/LocalGlobal/Semilocal/`.
-/

public section

open IsDedekindDomain IsLocalRing Module
open scoped TensorProduct

namespace TauCeti.Place

section Unbundled

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
and then specialized through the forms of the fundamental identity. -/

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

attribute [local instance 10] algebraIntegersExtension isScalarTowerIntegersExtension in
variable (F') in
/-- **The local degrees above `P` add up to the global degree** whenever the local integral closure
`𝒪'_P` is module-finite over `𝒪_P`. -/
theorem finsum_finrank_completion_eq_finrank_of_moduleFinite
    [Module.Finite P.integers (integralClosure P.integers F')] :
    ∑ᶠ P' : {P' : Place k' F' // P'.restrict k F = P},
        (letI := P.completionExtensionAlgebra P'.1 P'.2
        finrank P.Completion P'.1.Completion) = finrank F F' := by
  have : IsDedekindDomain (integralClosure P.integers F') :=
    TauCeti.integralClosure.isDedekindDomain P.integers F F'
  have hR : ∀ r : P.integers, algebraMap P.integers F r ∈ P.integers := fun r ↦ r.2
  have : IsScalarTower k P.integers F' := .of_algebraMap_eq fun c ↦ by
    rw [IsScalarTower.algebraMap_apply P.integers F F',
      ← IsScalarTower.algebraMap_apply k P.integers F, ← IsScalarTower.algebraMap_apply k F F']
  have hk' : ∀ c : k', algebraMap k' F' c ∈ integralClosure P.integers F' := fun c ↦
    (IsIntegral.algebraMap (Algebra.IsIntegral.isIntegral (R := k) c)).tower_top
  let _ : Algebra k' (integralClosure P.integers F') :=
    ((algebraMap k' F').codRestrict (integralClosure P.integers F') hk').toAlgebra
  have : IsScalarTower k' (integralClosure P.integers F') F' := .of_algebraMap_eq fun _ ↦ rfl
  refine finsum_finrank_completion_eq_finrank_of_sum_eq k' P fun hs ↦
    sum_ramificationIdx_mul_relativeDegree_eq_finrank (S := integralClosure P.integers F')
      k F (P.center hR) fun P' ↦ ?_
  rw [hs P', ofPrime_center]

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

end Unbundled

noncomputable section

attribute [local instance 10] algebraIntegersExtension isScalarTowerIntegersExtension

section ScopedInstances

section Base

variable {k F : Type*} [Field k] [Field F] [Algebra k F]

/-- Scalar multiplication on `WithVal P.valuation` by any `F`-algebra base `S` is uniformly
continuous. Kept as an explicit theorem rather than a global instance so it cannot compete with
`TauCeti.Place.instAlgebraCompletion` at `S = k`. -/
theorem uniformContinuousConstSMul_withVal (P : Place k F) {S : Type*} [CommSemiring S]
    [Algebra S F] :
    UniformContinuousConstSMul S (WithVal P.valuation) := ⟨fun s ↦ by
  simp_rw [WithVal.smul_right_def, Algebra.smul_def]
  exact (Ring.uniformContinuousConstSMul (WithVal P.valuation)).uniformContinuous_const_smul _⟩

/-- The `F`-algebra structure on `F̂_P` whose scalar multiplication matches
`UniformSpace.Completion.instSMul`. Installed in the `PlaceCompletionExtension` scope. -/
@[instance_reducible]
def completionAlgebra (P : Place k F) : Algebra F P.Completion :=
  haveI := P.uniformContinuousConstSMul_withVal (S := F)
  UniformSpace.Completion.algebra (WithVal P.valuation) F

/-- The `𝒪_P`-algebra structure on `F̂_P` whose scalar multiplication matches
`UniformSpace.Completion.instSMul`. Installed in the `PlaceCompletionExtension` scope. -/
@[instance_reducible]
def completionIntegersFieldAlgebra (P : Place k F) : Algebra P.integers P.Completion :=
  haveI := P.uniformContinuousConstSMul_withVal (S := P.integers)
  UniformSpace.Completion.algebra (WithVal P.valuation) P.integers

/-- The valuation ring `𝒪_P` acts on its completion `𝒪̂_P` through
`TauCeti.Place.completionIntegersEmbedding`. Installed in the `PlaceCompletionExtension` scope. -/
@[instance_reducible]
def completionIntegersAlgebra (P : Place k F) :
    Algebra P.integers P.completionPlace.integers :=
  P.completionIntegersEmbedding.toRingHom.toAlgebra

scoped[PlaceCompletionExtension] attribute [instance]
  TauCeti.Place.completionAlgebra
  TauCeti.Place.completionIntegersFieldAlgebra
  TauCeti.Place.completionIntegersAlgebra

open scoped PlaceCompletionExtension

/-- The scoped `F`-algebra structure on `F̂_P` acts via `TauCeti.Place.completionEmbedding`. -/
@[simp]
theorem algebraMap_completion (P : Place k F) (x : F) :
    algebraMap F P.Completion x = P.completionEmbedding x := by
  rw [UniformSpace.Completion.algebraMap_def, WithVal.algebraMap_right_apply,
    Algebra.algebraMap_self_apply, P.completionEmbedding_apply]

/-- The scoped `𝒪_P`-algebra structure on `F̂_P` acts via `TauCeti.Place.completionEmbedding`. -/
@[simp]
theorem algebraMap_completionIntegersFieldAlgebra (P : Place k F) (r : P.integers) :
    algebraMap P.integers P.Completion r = P.completionEmbedding r := by
  rw [UniformSpace.Completion.algebraMap_def, WithVal.algebraMap_right_apply,
    P.completionEmbedding_apply]
  rfl

/-- The scoped `𝒪_P`-algebra structure on `𝒪̂_P` acts via
`TauCeti.Place.completionIntegersEmbedding`. -/
@[simp]
theorem algebraMap_completionIntegersAlgebra (P : Place k F) (x : P.integers) :
    algebraMap P.integers P.completionPlace.integers x = P.completionIntegersEmbedding x :=
  (rfl)

/-- The scalar tower `𝒪_P → F → F̂_P`. Installed in the `PlaceCompletionExtension` scope. -/
theorem completionIntegersFieldIsScalarTower (P : Place k F) :
    IsScalarTower P.integers F P.Completion :=
  IsScalarTower.of_algebraMap_eq fun r ↦ by
    rw [algebraMap_completionIntegersFieldAlgebra, algebraMap_completion]
    rfl

/-- The scalar tower `𝒪_P → 𝒪̂_P → F̂_P`. Installed in the `PlaceCompletionExtension` scope. -/
theorem completionIntegersIsScalarTower (P : Place k F) :
    IsScalarTower P.integers P.completionPlace.integers P.Completion :=
  IsScalarTower.of_algebraMap_eq fun r ↦ by
    rw [algebraMap_completionIntegersFieldAlgebra, ValuationSubring.algebraMap_apply,
      algebraMap_completionIntegersAlgebra, P.completionIntegersEmbedding_apply]

scoped[PlaceCompletionExtension] attribute [instance]
  TauCeti.Place.completionIntegersFieldIsScalarTower
  TauCeti.Place.completionIntegersIsScalarTower

end Base

open scoped PlaceCompletionExtension

variable {k k' F F' : Type*} [Field k] [Field k'] [Field F] [Field F']
  [Algebra k F] [Algebra k k'] [Algebra k' F'] [Algebra k F'] [Algebra F F']
  [IsScalarTower k k' F'] [IsScalarTower k F F']

/-- For each place `Q` in the fibre above `P`, the `F`-algebra structure on `F̂_Q` whose scalar
multiplication matches `UniformSpace.Completion.instSMul`. Installed in the
`PlaceCompletionExtension` scope. -/
@[instance_reducible]
def completionFibreBaseAlgebra [Algebra.IsIntegral F F'] (P : Place k F)
    (Q : {P' : Place k' F' // P'.restrict k F = P}) :
    Algebra F Q.1.Completion :=
  haveI := Q.1.uniformContinuousConstSMul_withVal (S := F)
  UniformSpace.Completion.algebra (WithVal Q.1.valuation) F

/-- For each place `Q` in the fibre above `P`, the local field extension algebra `F̂_P → F̂_Q`.
Installed in the `PlaceCompletionExtension` scope so dependent products over the fibre inherit the
factorwise `F̂_P`-algebra structure without introducing a global self-algebra diamond. -/
@[expose, instance_reducible]
def completionFibreAlgebra [Algebra.IsIntegral F F'] (P : Place k F)
    (Q : {P' : Place k' F' // P'.restrict k F = P}) :
    Algebra P.Completion Q.1.Completion :=
  P.completionExtensionAlgebra Q.1 Q.2

/-- For each place `Q` in the fibre above `P`, the local valuation-ring algebra `𝒪̂_P → 𝒪̂_Q`.
Installed in the `PlaceCompletionExtension` scope. -/
@[expose, instance_reducible]
def completionIntegersFibreAlgebra [Algebra.IsIntegral F F'] (P : Place k F)
    (Q : {P' : Place k' F' // P'.restrict k F = P}) :
    Algebra P.completionPlace.integers Q.1.completionPlace.integers :=
  P.completionIntegersExtensionAlgebra Q.1 Q.2

scoped[PlaceCompletionExtension] attribute [instance]
  TauCeti.Place.completionFibreBaseAlgebra
  TauCeti.Place.completionFibreAlgebra
  TauCeti.Place.completionIntegersFibreAlgebra

/-- The scoped `F`-algebra map into `F̂_Q` embeds `F` into `F'` and then into `F̂_Q`. -/
theorem algebraMap_completionFibreBaseAlgebra [Algebra.IsIntegral F F'] (P : Place k F)
    (Q : {P' : Place k' F' // P'.restrict k F = P}) (x : F) :
    algebraMap F Q.1.Completion x = Q.1.completionEmbedding (algebraMap F F' x) := by
  rw [UniformSpace.Completion.algebraMap_def, WithVal.algebraMap_right_apply,
    Q.1.completionEmbedding_apply]

/-- For each place `Q` in the fibre above `P`, `F → F̂_P → F̂_Q` is a scalar tower. Installed in the
`PlaceCompletionExtension` scope. -/
theorem completionFibreIsScalarTower [Algebra.IsIntegral F F'] (P : Place k F)
    (Q : {P' : Place k' F' // P'.restrict k F = P}) :
    IsScalarTower F P.Completion Q.1.Completion :=
  IsScalarTower.of_algebraMap_eq fun x ↦ by
    rw [algebraMap_completionFibreBaseAlgebra, algebraMap_completion,
      algebraMap_completionExtensionAlgebra P Q.1 Q.2,
      P.completionExtension_completionEmbedding Q.1 Q.2 x]

/-- For each place `Q` in the fibre above `P`, `𝒪̂_Q` is torsion-free over `𝒪̂_P`. Installed in the
`PlaceCompletionExtension` scope. -/
theorem completionFibreIsTorsionFree [Algebra.IsIntegral F F'] (P : Place k F)
    (Q : {P' : Place k' F' // P'.restrict k F = P}) :
    Module.IsTorsionFree P.completionPlace.integers Q.1.completionPlace.integers :=
  P.isTorsionFree_completionIntegers Q.1 Q.2

scoped[PlaceCompletionExtension] attribute [instance]
  TauCeti.Place.completionFibreIsScalarTower
  TauCeti.Place.completionFibreIsTorsionFree

end ScopedInstances

open scoped PlaceCompletionExtension

section FunctionFieldFinite

open _root_.IntermediateField _root_.IntermediateField.algebraAdjoinAdjoin

/-- Over an algebraic function field `F / k`, the integral closure `𝒪'_P` of `𝒪_P` in any finite
extension `F' / F` is a finite `𝒪_P`-module, with no separability hypothesis on `F' / F`: it is the
localization at the centre of `P` of the integral closure of `k[t]` in `F'` for a uniformizer `t` at
`P`. -/
theorem moduleFinite_integralClosure_of_isFunctionField {k F : Type*} [Field k] [Field F]
    [Algebra k F] (F' : Type*) [Field F'] [Algebra F F'] [FiniteDimensional F F'] (P : Place k F)
    (hF : IsFunctionField k F) :
    Module.Finite P.integers (integralClosure P.integers F') := by
  let _ : Algebra k F' := Algebra.compHom F' (algebraMap k F)
  have : IsScalarTower k F F' := .of_compHom k F F'
  obtain ⟨t, ht⟩ := P.exists_isUniformizer
  have htP : P.ord t = 1 := P.isUniformizer_iff_ord_eq_one.mp ht
  have htr : Transcendental k t := P.transcendental_of_ord_ne_zero (by omega)
  have hti : t ∈ P.integers := P.mem_integers_iff_ord_nonneg.mpr (by omega)
  have : FiniteDimensional k⟮t⟯ F := hF.finiteDimensional_adjoin htr
  have : FiniteDimensional k⟮t⟯ F' := Module.Finite.trans F F'
  let R := integralClosure (Algebra.adjoin k {t}) F
  have : IsDedekindDomain R := isDedekindDomain_integralClosure_adjoin hF t
  have : IsFractionRing R F := isFractionRing_integralClosure_adjoin hF htr
  have : Module.Finite R (integralClosure R F') :=
    IsIntegralClosure.finite_integralClosure_integralClosure_adjoin k t F'
  have hR : ∀ r : R, algebraMap R F r ∈ P.integers := fun r ↦
    P.mem_integers_iff.mpr
      (P.forall_algebraMap_mem_integers_integralClosure_adjoin_iff.mpr hti r r.2)
  let p : HeightOneSpectrum R := P.center hR
  let _ : Algebra R P.integers := ((algebraMap R F).codRestrict P.integers hR).toAlgebra
  have : IsScalarTower R P.integers F := .of_algebraMap_eq fun _ ↦ rfl
  have : IsScalarTower R P.integers F' := .of_algebraMap_eq fun x ↦
    IsScalarTower.algebraMap_apply R F F' x
  let eR : HeightOneSpectrum.valuationSubringAtPrime F p ≃ₐ[R] P.integers :=
    AlgEquiv.ofRingEquiv
      (f := RingEquiv.subringCongr
        (congrArg ValuationSubring.toSubring (P.valuationSubringAtPrime_eq_integers hR)))
      fun _ ↦ rfl
  have : IsLocalization p.asIdeal.primeCompl P.integers :=
    IsLocalization.isLocalization_of_algEquiv p.asIdeal.primeCompl eR
  exact TauCeti.finite_integralClosure_of_isLocalization p.asIdeal.primeCompl P.integers F'

end FunctionFieldFinite

section ToField

variable {k F : Type*} [Field k] [Field F] [Algebra k F]

/-- The canonical `𝒪_P`-algebra homomorphism `𝒪̂_P ⊗[𝒪_P] 𝒪'_P →ₐ[𝒪_P] F̂_P ⊗[F] F'`. -/
def integralCompletionSemilocalToField (F' : Type*) [Field F'] [Algebra F F'] (P : Place k F) :
    P.completionPlace.integers ⊗[P.integers] integralClosure P.integers F' →ₐ[P.integers]
      P.Completion ⊗[F] F' :=
  Algebra.TensorProduct.lift
    { (Algebra.TensorProduct.includeLeftRingHom : P.Completion →+* P.Completion ⊗[F] F').comp
        (algebraMap P.completionPlace.integers P.Completion) with
      commutes' := fun r ↦ by
        rw [RingHom.toFun_eq_coe, RingHom.comp_apply,
          Algebra.TensorProduct.includeLeftRingHom_apply,
          ← IsScalarTower.algebraMap_apply P.integers P.completionPlace.integers P.Completion,
          Algebra.TensorProduct.algebraMap_apply] }
    { (Algebra.TensorProduct.includeRight : F' →ₐ[F] P.Completion ⊗[F] F').toRingHom.comp
        (algebraMap (integralClosure P.integers F') F') with
      commutes' := fun r ↦ by
        simp only [RingHom.toFun_eq_coe, RingHom.comp_apply, AlgHom.toRingHom_eq_coe,
          RingHom.coe_coe, Algebra.TensorProduct.includeRight_apply]
        rw [← IsScalarTower.algebraMap_apply P.integers (integralClosure P.integers F') F',
          IsScalarTower.algebraMap_apply P.integers F F',
          ← Algebra.TensorProduct.algebraMap_apply',
          Algebra.TensorProduct.algebraMap_apply, Algebra.TensorProduct.algebraMap_apply,
          ← IsScalarTower.algebraMap_apply P.integers F P.Completion] }
    fun _ _ ↦ .all _ _

variable {F' : Type*} [Field F'] [Algebra F F']

/-- `integralCompletionSemilocalToField` acts on pure tensors by coercion in both factors. -/
@[simp]
theorem integralCompletionSemilocalToField_tmul {P : Place k F} (a : P.completionPlace.integers)
    (b : integralClosure P.integers F') :
    integralCompletionSemilocalToField F' P (a ⊗ₜ[P.integers] b) =
      (a : P.Completion) ⊗ₜ[F] (b : F') := by
  simp [integralCompletionSemilocalToField]

/-- The trace of a pure integral tensor paired with `d ∈ F'` is the scalar extension of the global
trace pairing. -/
theorem trace_integralCompletionSemilocalToField_tmul_mul {P : Place k F}
    (a : P.completionPlace.integers) (b : integralClosure P.integers F') (d : F') :
    Algebra.trace P.Completion (P.Completion ⊗[F] F')
        (integralCompletionSemilocalToField F' P (a ⊗ₜ[P.integers] b) * (1 ⊗ₜ[F] d)) =
      (a : P.Completion) * P.completionEmbedding (Algebra.trace F F' ((b : F') * d)) := by
  have ha : (a : P.Completion) ⊗ₜ[F] ((b : F') * d) =
      (a : P.Completion) • ((1 : P.Completion) ⊗ₜ[F] ((b : F') * d)) := by
    rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
  rw [integralCompletionSemilocalToField_tmul, Algebra.TensorProduct.tmul_mul_tmul, mul_one, ha,
    map_smul, TauCeti.Algebra.trace_baseChange_tmul, smul_eq_mul, algebraMap_completion]

end ToField

section Semilocal

variable {k k' F F' : Type*} [Field k] [Field k'] [Field F] [Field F']
  [Algebra k F] [Algebra k k'] [Algebra k' F'] [Algebra k F'] [Algebra F F']
  [IsScalarTower k k' F'] [IsScalarTower k F F']

section Hom

variable [Algebra.IsIntegral F F'] (k' F') (P : Place k F)

/-- The integral semilocal algebra map `𝒪̂_P ⊗[𝒪_P] 𝒪'_P →ₐ[𝒪̂_P] ∏_{Q ∣ P} 𝒪̂_Q` sending `a ⊗ b`
to `(a · b)_Q`. -/
def integralCompletionSemilocalHom :
    P.completionPlace.integers ⊗[P.integers] integralClosure P.integers F' →ₐ[
        P.completionPlace.integers]
      ∀ Q : {P' : Place k' F' // P'.restrict k F = P}, Q.1.completionPlace.integers :=
  letI (Q : {P' : Place k' F' // P'.restrict k F = P}) :
      Algebra P.integers Q.1.completionPlace.integers :=
    ((algebraMap P.completionPlace.integers Q.1.completionPlace.integers).comp
      (algebraMap P.integers P.completionPlace.integers)).toAlgebra
  letI (Q : {P' : Place k' F' // P'.restrict k F = P}) :
      IsScalarTower P.integers P.completionPlace.integers Q.1.completionPlace.integers :=
    .of_algebraMap_eq fun _ ↦ rfl
  Algebra.TensorProduct.lift (Algebra.ofId _ _)
    (AlgHom.pi fun Q ↦
      { P.completionIntegersIntegralClosureHom Q.1 Q.2 with
        commutes' := fun r ↦ by
          -- Expose the composite `P.integers`-algebra installed above so the compatibility lemma
          -- for `completionIntegersIntegralClosureHom` applies.
          change P.completionIntegersIntegralClosureHom Q.1 Q.2
              (algebraMap P.integers (integralClosure P.integers F') r) =
            algebraMap P.completionPlace.integers Q.1.completionPlace.integers
              (algebraMap P.integers P.completionPlace.integers r)
          rw [completionIntegersIntegralClosureHom_algebraMap,
            algebraMap_completionIntegersAlgebra,
            algebraMap_completionIntegersExtensionAlgebra] })
    fun _ _ ↦ .all _ _

/-- The field semilocal algebra map `F̂_P ⊗[F] F' →ₐ[F̂_P] ∏_{Q ∣ P} F̂_Q` sending `a ⊗ x` to
`(a · x)_Q`. -/
def completionSemilocalHom :
    P.Completion ⊗[F] F' →ₐ[P.Completion]
      ∀ Q : {P' : Place k' F' // P'.restrict k F = P}, Q.1.Completion :=
  Algebra.TensorProduct.lift (Algebra.ofId _ _)
    (AlgHom.pi fun Q ↦
      { Q.1.completionEmbedding.toRingHom with
        commutes' := fun x ↦ (algebraMap_completionFibreBaseAlgebra P Q x).symm })
    fun _ _ ↦ .all _ _

variable {k' F' P}

/-- `integralCompletionSemilocalHom` acts componentwise on pure tensors. -/
@[simp]
theorem integralCompletionSemilocalHom_tmul (a : P.completionPlace.integers)
    (b : integralClosure P.integers F') (Q : {P' : Place k' F' // P'.restrict k F = P}) :
    integralCompletionSemilocalHom k' F' P (a ⊗ₜ b) Q =
      algebraMap P.completionPlace.integers Q.1.completionPlace.integers a *
        P.completionIntegersIntegralClosureHom Q.1 Q.2 b := by
  simp [integralCompletionSemilocalHom]

/-- `completionSemilocalHom` acts componentwise on pure tensors. -/
@[simp]
theorem completionSemilocalHom_tmul (a : P.Completion) (x : F')
    (Q : {P' : Place k' F' // P'.restrict k F = P}) :
    completionSemilocalHom k' F' P (a ⊗ₜ x) Q =
      algebraMap P.Completion Q.1.Completion a * Q.1.completionEmbedding x := by
  simp [completionSemilocalHom]

end Hom

section Surjective

variable [FiniteDimensional F F'] (k' F') (P : Place k F)

/-- **The field semilocal map is surjective** for any finite extension `F' / F`: its `F̂_P`-linear
range contains the diagonal image of `F'`, which spans `∏_{Q ∣ P} F̂_Q` over `F̂_P` by
`TauCeti.Place.span_completion_pi_eq_top`. -/
theorem completionSemilocalHom_surjective :
    Function.Surjective (completionSemilocalHom k' F' P) := by
  rw [← AlgHom.coe_toLinearMap, ← LinearMap.range_eq_top, eq_top_iff,
    ← span_completion_pi_eq_top k' F' P, Submodule.span_le]
  rintro _ ⟨y, rfl⟩
  refine ⟨1 ⊗ₜ y, funext fun Q ↦ ?_⟩
  simp

variable [Algebra.IsIntegral k k']

variable {F'} in
/-- For any finite extension `F' / F` over an integral constant-field extension `k' / k`, an
element of `F'` lies in `𝒪'_P` if and only if it is regular at every place of `F' / k'` lying over
`P`. This removes the `IsFunctionField` hypothesis of
`TauCeti.Place.isIntegral_iff_forall_restrict_eq_mem_integers` when `F' / F` is finite. -/
theorem mem_integralClosure_iff_forall_restrict_eq_mem_integers {y : F'} :
    y ∈ integralClosure P.integers F' ↔
      ∀ P' : Place k' F', P'.restrict k F = P → y ∈ P'.integers := by
  refine ⟨fun hy P' hP' ↦ ?_, fun hy ↦ ?_⟩
  · subst hP'
    exact algebraMap_mem_integers_of_mem_integralClosure k F P' ⟨y, hy⟩
  · let B := integralClosure P.integers F'
    have : IsDedekindDomain B := TauCeti.integralClosure.isDedekindDomain P.integers F F'
    have : IsFractionRing B F' :=
      IsIntegralClosure.isFractionRing_of_finite_extension P.integers F F' B
    have hR : ∀ r : P.integers, algebraMap P.integers F r ∈ P.integers := fun r ↦ r.2
    have : IsScalarTower k P.integers F' := .of_algebraMap_eq fun c ↦ by
      rw [IsScalarTower.algebraMap_apply P.integers F F',
        ← IsScalarTower.algebraMap_apply k P.integers F, ← IsScalarTower.algebraMap_apply k F F']
    have hk' : ∀ c : k', algebraMap k' F' c ∈ B := fun c ↦
      (IsIntegral.algebraMap (Algebra.IsIntegral.isIntegral (R := k) c)).tower_top
    let _ : Algebra k' B := ((algebraMap k' F').codRestrict B hk').toAlgebra
    have : IsScalarTower k' B F' := .of_algebraMap_eq fun _ ↦ rfl
    obtain ⟨b, hb⟩ := HeightOneSpectrum.mem_integers_of_valuation_le_one (R := B) F' y fun 𝔓 ↦ by
      have : 𝔓.asIdeal.LiesOver (P.center hR).asIdeal :=
        ⟨(IsLocalRing.eq_maximalIdeal (P.center hR).isMaximal).trans
          (IsLocalRing.eq_maximalIdeal
            (𝔓.asIdeal.isMaximal_under_of_isIntegral_of_isMaximal (R := P.integers)
              (hI := 𝔓.isMaximal))).symm⟩
      have hP' : (ofPrime k' F' 𝔓).restrict k F = P :=
        (restrict_ofPrime k F (P.center hR) 𝔓).trans (ofPrime_center k F P hR)
      simpa only [mem_integers_iff, valuation_ofPrime] using hy (ofPrime k' F' 𝔓) hP'
    exact hb ▸ b.2

/-- **The integral semilocal map is surjective** for arbitrary residue fields: functions regular at
every place over `P` lie in `𝒪'_P` and span `∏_{Q ∣ P} 𝒪̂_Q` over `𝒪̂_P` by
`TauCeti.Place.span_completionIntegers_pi_eq_top`. -/
theorem integralCompletionSemilocalHom_surjective :
    Function.Surjective (integralCompletionSemilocalHom k' F' P) := by
  rw [← AlgHom.coe_toLinearMap, ← LinearMap.range_eq_top, eq_top_iff,
    ← span_completionIntegers_pi_eq_top k' F' P, Submodule.span_le]
  rintro _ ⟨y, rfl⟩
  have hy : y.1 ∈ integralClosure P.integers F' :=
    (mem_integralClosure_iff_forall_restrict_eq_mem_integers k' P).mpr fun P' hP' ↦
      y.2 ⟨P', hP'⟩
  refine ⟨1 ⊗ₜ ⟨y.1, hy⟩, funext fun Q ↦ Subtype.ext ?_⟩
  simp

end Surjective

section Equiv

variable [FiniteDimensional F F'] [Algebra.IsIntegral k k']
variable (k' F') (P : Place k F) [Module.Finite P.integers (integralClosure P.integers F')]

attribute [local instance] Fintype.ofFinite in
/-- Under `[Module.Finite P.integers (integralClosure P.integers F')]`, the local degrees above `P`
sum to `[F' : F]`. -/
theorem sum_finrank_completion_eq_finrank :
    ∑ Q : {P' : Place k' F' // P'.restrict k F = P},
      Module.finrank P.Completion Q.1.Completion = Module.finrank F F' := by
  rw [← finsum_eq_sum_of_fintype]
  exact finsum_finrank_completion_eq_finrank_of_moduleFinite k' F' P

attribute [local instance] Fintype.ofFinite in
/-- The integral semilocal map is bijective. -/
theorem integralCompletionSemilocalHom_bijective :
    Function.Bijective (integralCompletionSemilocalHom k' F' P) := by
  have : Module.Free P.integers (integralClosure P.integers F') :=
    Module.free_of_finite_type_torsion_free'
  have (Q : {P' : Place k' F' // P'.restrict k F = P}) :
      Module.Finite P.completionPlace.integers Q.1.completionPlace.integers :=
    moduleFinite_completionIntegers P Q.1 Q.2
  have (Q : {P' : Place k' F' // P'.restrict k F = P}) :
      Module.Free P.completionPlace.integers Q.1.completionPlace.integers :=
    moduleFree_completionIntegers P Q.1 Q.2
  refine OrzechProperty.bijective_of_surjective_of_finrank_le
    (integralCompletionSemilocalHom k' F' P).toLinearMap
    (integralCompletionSemilocalHom_surjective k' F' P) ?_
  rw [Module.finrank_baseChange, finrank_integralClosure F' P,
    Module.finrank_pi_fintype, ← sum_finrank_completion_eq_finrank k' F' P]
  refine le_of_eq (Finset.sum_congr rfl fun Q _ ↦ ?_)
  rw [finrank_completion P Q.1 Q.2, finrank_completionIntegers P Q.1 Q.2]

/-- **The integral semilocal decomposition**
`𝒪̂_P ⊗[𝒪_P] 𝒪'_P ≃ₐ[𝒪̂_P] ∏_{Q ∣ P} 𝒪̂_Q`, valid for arbitrary residue fields. -/
def integralCompletionSemilocalEquiv :
    P.completionPlace.integers ⊗[P.integers] integralClosure P.integers F' ≃ₐ[
        P.completionPlace.integers]
      ∀ Q : {P' : Place k' F' // P'.restrict k F = P}, Q.1.completionPlace.integers :=
  AlgEquiv.ofBijective (integralCompletionSemilocalHom k' F' P)
    (integralCompletionSemilocalHom_bijective k' F' P)

variable {k' F' P} in
/-- `integralCompletionSemilocalEquiv` acts componentwise on pure tensors. -/
@[simp]
theorem integralCompletionSemilocalEquiv_tmul (a : P.completionPlace.integers)
    (b : integralClosure P.integers F') (Q : {P' : Place k' F' // P'.restrict k F = P}) :
    integralCompletionSemilocalEquiv k' F' P (a ⊗ₜ b) Q =
      algebraMap P.completionPlace.integers Q.1.completionPlace.integers a *
        P.completionIntegersIntegralClosureHom Q.1 Q.2 b :=
  integralCompletionSemilocalHom_tmul a b Q

/-- Compatibility of the integral and field semilocal homomorphisms. -/
theorem integralCompletionSemilocalHom_fieldCompatibility
    (z : P.completionPlace.integers ⊗[P.integers] integralClosure P.integers F') :
    completionSemilocalHom k' F' P (integralCompletionSemilocalToField F' P z) =
      fun Q ↦ (integralCompletionSemilocalEquiv k' F' P z Q : Q.1.Completion) := by
  induction z using TensorProduct.inductionOn with
  | add x y hx hy =>
    funext Q
    rw [map_add, map_add, Pi.add_apply, hx, hy, map_add, Pi.add_apply, AddMemClass.coe_add]
  | tmul a b =>
    funext Q
    rw [integralCompletionSemilocalToField_tmul, completionSemilocalHom_tmul,
      integralCompletionSemilocalEquiv_tmul, MulMemClass.coe_mul,
      coe_algebraMap_completionIntegersExtensionAlgebra, algebraMap_completionExtensionAlgebra,
      coe_completionIntegersIntegralClosureHom]

attribute [local instance] Fintype.ofFinite in
/-- The field semilocal map is bijective. -/
theorem completionSemilocalHom_bijective :
    Function.Bijective (completionSemilocalHom k' F' P) := by
  have (Q : {P' : Place k' F' // P'.restrict k F = P}) :
      FiniteDimensional P.Completion Q.1.Completion :=
    finiteDimensional_completion P Q.1 Q.2
  have hdim : Module.finrank P.Completion (P.Completion ⊗[F] F') =
      Module.finrank P.Completion
        (∀ Q : {P' : Place k' F' // P'.restrict k F = P}, Q.1.Completion) := by
    rw [Module.finrank_baseChange, Module.finrank_pi_fintype,
      ← sum_finrank_completion_eq_finrank k' F' P]
  exact ⟨(LinearMap.injective_iff_surjective_of_finrank_eq_finrank hdim
      (f := (completionSemilocalHom k' F' P).toLinearMap)).mpr
        (completionSemilocalHom_surjective k' F' P),
    completionSemilocalHom_surjective k' F' P⟩

/-- **The field semilocal decomposition**
`F̂_P ⊗[F] F' ≃ₐ[F̂_P] ∏_{Q ∣ P} F̂_Q`, valid for arbitrary residue fields. -/
def completionSemilocalEquiv :
    P.Completion ⊗[F] F' ≃ₐ[P.Completion]
      ∀ Q : {P' : Place k' F' // P'.restrict k F = P}, Q.1.Completion :=
  AlgEquiv.ofBijective (completionSemilocalHom k' F' P) (completionSemilocalHom_bijective k' F' P)

variable {k' F' P} in
/-- `completionSemilocalEquiv` acts componentwise on pure tensors. -/
@[simp]
theorem completionSemilocalEquiv_tmul (a : P.Completion) (x : F')
    (Q : {P' : Place k' F' // P'.restrict k F = P}) :
    completionSemilocalEquiv k' F' P (a ⊗ₜ x) Q =
      algebraMap P.Completion Q.1.Completion a * Q.1.completionEmbedding x :=
  completionSemilocalHom_tmul a x Q

/-- After inclusion into the completions, `integralCompletionSemilocalEquiv` agrees with
`completionSemilocalEquiv`. -/
theorem integralCompletionSemilocalEquiv_fieldCompatibility
    (z : P.completionPlace.integers ⊗[P.integers] integralClosure P.integers F') :
    completionSemilocalEquiv k' F' P (integralCompletionSemilocalToField F' P z) =
      fun Q ↦ (integralCompletionSemilocalEquiv k' F' P z Q : Q.1.Completion) :=
  integralCompletionSemilocalHom_fieldCompatibility k' F' P z

/-! ### Norm and trace in the semilocal decomposition -/

attribute [local instance] Fintype.ofFinite in
/-- The norm of `F̂_P ⊗[F] F'` over `F̂_P` is the product of the norms of its semilocal
components. -/
theorem norm_eq_prod_norm_completionSemilocalEquiv (ξ : P.Completion ⊗[F] F') :
    Algebra.norm P.Completion ξ =
      ∏ Q : {P' : Place k' F' // P'.restrict k F = P},
        Algebra.norm P.Completion (completionSemilocalEquiv k' F' P ξ Q) := by
  have (Q : {P' : Place k' F' // P'.restrict k F = P}) :
      FiniteDimensional P.Completion Q.1.Completion :=
    finiteDimensional_completion P Q.1 Q.2
  rw [← Algebra.norm_eq_of_algEquiv (completionSemilocalEquiv k' F' P)]
  exact TauCeti.Algebra.norm_pi _

variable {F'} in
/-- **Local–global norm decomposition** under `[Module.Finite P.integers (integralClosure
P.integers F')]`: the norm of `x ∈ F'` in `F̂_P` is the product of its local norms across the
places `P'` of `F' / k'` lying over `P`. -/
theorem completionEmbedding_norm_of_moduleFinite (x : F') :
    P.completionEmbedding (Algebra.norm F x) =
      ∏ᶠ P' : {P' : Place k' F' // P'.restrict k F = P},
        (letI := P.completionExtensionAlgebra P'.1 P'.2
        Algebra.norm P.Completion (P'.1.completionEmbedding x)) := by
  have := Fintype.ofFinite {P' : Place k' F' // P'.restrict k F = P}
  have (Q : {P' : Place k' F' // P'.restrict k F = P}) :
      FiniteDimensional P.Completion Q.1.Completion :=
    finiteDimensional_completion P Q.1 Q.2
  rw [finprod_eq_prod_of_fintype, ← algebraMap_completion,
    ← TauCeti.Algebra.norm_baseChange_tmul (A := P.Completion) (B := F') x,
    ← Algebra.norm_eq_of_algEquiv (completionSemilocalEquiv k' F' P), TauCeti.Algebra.norm_pi]
  exact Finset.prod_congr rfl fun Q _ ↦ by simp

attribute [local instance] Fintype.ofFinite in
/-- The trace of `F̂_P ⊗[F] F'` over `F̂_P` is the sum of the traces of its semilocal components. -/
theorem trace_eq_sum_trace_completionSemilocalEquiv (ξ : P.Completion ⊗[F] F') :
    Algebra.trace P.Completion (P.Completion ⊗[F] F') ξ =
      ∑ Q : {P' : Place k' F' // P'.restrict k F = P},
        Algebra.trace P.Completion Q.1.Completion (completionSemilocalEquiv k' F' P ξ Q) := by
  have (Q : {P' : Place k' F' // P'.restrict k F = P}) :
      FiniteDimensional P.Completion Q.1.Completion :=
    finiteDimensional_completion P Q.1 Q.2
  rw [← Algebra.trace_eq_of_algEquiv (completionSemilocalEquiv k' F' P)]
  exact TauCeti.Algebra.trace_pi _

variable {k' F' P} in
attribute [local instance] Fintype.ofFinite in
/-- An element of `F̂_{P'}`, placed in the `P'`-component of `F̂_P ⊗[F] F'`, has the same trace
pairing with `x ∈ F'` as in `F̂_{P'}`. -/
theorem trace_completionSemilocalEquiv_symm_single_mul
    [DecidableEq {Q : Place k' F' // Q.restrict k F = P}]
    (P' : Place k' F') (hP : P'.restrict k F = P) (z : P'.Completion) (x : F') :
    letI := P.completionExtensionAlgebra P' hP
    Algebra.trace P.Completion (P.Completion ⊗[F] F')
        ((completionSemilocalEquiv k' F' P).symm
          (Pi.single (⟨P', hP⟩ : {Q : Place k' F' // Q.restrict k F = P}) z) * (1 ⊗ₜ x)) =
      Algebra.trace P.Completion P'.Completion (z * P'.completionEmbedding x) := by
  rw [trace_eq_sum_trace_completionSemilocalEquiv k' F' P, Finset.sum_eq_single
    (⟨P', hP⟩ : {Q : Place k' F' // Q.restrict k F = P})]
  · simp
  · intro Q _ hQ
    rw [map_mul, AlgEquiv.apply_symm_apply, Pi.mul_apply, Pi.single_eq_of_ne hQ, zero_mul,
      map_zero]
  · simp

end Equiv

section NormSpecializations

variable [FiniteDimensional F F'] [Algebra.IsIntegral k k'] (k') (P : Place k F)

/-- **The norm formula**: for a finite separable extension `F' / F` whose constant field extension
`k' / k` is integral and a place `P` of `F`, the norm of `x ∈ F'` over `F` is, in the completion at
`P`, the product of the norms of `x` over the completions `F̂'_{P'} / F̂_P` at the places `P'` above
`P`. For an algebraic function field `F / k` separability is not needed; that is
`TauCeti.Place.completionEmbedding_norm`. -/
theorem completionEmbedding_norm_of_isSeparable [Algebra.IsSeparable F F'] (x : F') :
    P.completionEmbedding (Algebra.norm F x) =
      ∏ᶠ P' : {P' : Place k' F' // P'.restrict k F = P},
        (letI := P.completionExtensionAlgebra P'.1 P'.2
        Algebra.norm P.Completion (P'.1.completionEmbedding x)) :=
  completionEmbedding_norm_of_moduleFinite k' P x

/-- **The norm formula**: for an algebraic function field `F / k`, a finite extension `F' / F`
whose constant field extension `k' / k` is integral and a place `P` of `F`, the norm of `x ∈ F'`
over `F` is, in the completion at `P`, the product of the norms of `x` over the completions
`F̂'_{P'} / F̂_P` at the places `P'` above `P`, with no separability hypothesis. -/
theorem completionEmbedding_norm (hF : IsFunctionField k F) (x : F') :
    P.completionEmbedding (Algebra.norm F x) =
      ∏ᶠ P' : {P' : Place k' F' // P'.restrict k F = P},
        (letI := P.completionExtensionAlgebra P'.1 P'.2
        Algebra.norm P.Completion (P'.1.completionEmbedding x)) := by
  have := moduleFinite_integralClosure_of_isFunctionField F' P hF
  exact completionEmbedding_norm_of_moduleFinite k' P x

end NormSpecializations

end Semilocal

section ToFieldInjective

/-- The canonical map `𝒪̂_P ⊗[𝒪_P] 𝒪'_P → F̂_P ⊗[F] F'` is injective. -/
theorem integralCompletionSemilocalToField_injective {k F F' : Type*} [Field k] [Field F]
    [Field F'] [Algebra k F] [Algebra F F'] [FiniteDimensional F F'] (P : Place k F)
    [Module.Finite P.integers (integralClosure P.integers F')] :
    Function.Injective (integralCompletionSemilocalToField F' P) := fun x y h ↦ by
  let _ : Algebra k F' := Algebra.compHom F' (algebraMap k F)
  have : IsScalarTower k F F' := .of_compHom k F F'
  apply (integralCompletionSemilocalEquiv k F' P).injective
  funext Q
  apply Subtype.ext
  exact congrFun ((integralCompletionSemilocalEquiv_fieldCompatibility k F' P x).symm.trans
    ((congrArg (completionSemilocalEquiv k F' P) h).trans
      (integralCompletionSemilocalEquiv_fieldCompatibility k F' P y))) Q

end ToFieldInjective

end

end TauCeti.Place
