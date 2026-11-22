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
public import TauCeti.RingTheory.NormTrace.BaseChange
public import TauCeti.RingTheory.NormTrace.Pi
import Mathlib.LinearAlgebra.Dimension.Free
import TauCeti.FieldTheory.FunctionField.Place.Extension.IntegralBasis.Basic
import TauCeti.LinearAlgebra.Span.Basic

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
  `[FiniteDimensional F F']`. When `k' / k` is integral and `𝒪'_P` is finite over `𝒪_P` (in
  particular, when `F' / F` is separable or `F / k` is an algebraic function field), the
  fundamental identity gives `∑_{P' ∣ P} [F̂'_{P'} : F̂_P] = [F' : F]`, so linear independence over
  `F` is preserved in `∏_{P' ∣ P} F̂'_{P'}` and the trace formula
  `Tr_{F'/F} x = ∑_{P' ∣ P} Tr_{F̂'_{P'}/F̂_P} x` holds.
* **Bundled integral and field semilocal equivalences.** In the `PlaceCompletionExtension` scope
  (extending the single-place completion algebras from `Place/Completion/Basic.lean`), we register
  the factorwise extension algebras over `{P' : Place k' F' // P'.restrict k F = P}`. Whenever the
  local integral closure `𝒪'_P = integralClosure P.integers F'` is module-finite over `𝒪_P` — which
  holds automatically when `F' / F` is separable (`TauCeti.Place.moduleFinite_integralClosure`) and
  for every finite extension of an algebraic function field
  (`TauCeti.Place.moduleFinite_integralClosure_of_isFunctionField`) — completing along `P` gives
  isomorphisms
  ```text
  𝒪̂_P ⊗[𝒪_P] 𝒪'_P ≃ₐ[𝒪̂_P] ∏_{Q ∣ P} 𝒪̂_Q,
  F̂_P ⊗[F] F'     ≃ₐ[F̂_P] ∏_{Q ∣ P} F̂_Q,
  ```
  compatible with inclusion into the completions, together with the local–global norm and trace
  formulas and componentwise trace-pairing identities used to localize the complementary module and
  different at a completion.

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
* `TauCeti.Place.finsum_finrank_completion_eq_finrank_of_moduleFinite`,
  `TauCeti.Place.finsum_finrank_completion_eq_finrank_of_isSeparable`, and
  `TauCeti.Place.finsum_finrank_completion_eq_finrank`: the local degrees above `P` add up to
  `[F' : F]`.
* `TauCeti.Place.linearIndependent_completionEmbedding_pi_iff` and
  `TauCeti.Place.linearIndependent_completionEmbedding_pi_iff_of_isSeparable`: linear independence
  survives completion at `P`.
* `TauCeti.Place.completionSemilocalHom_integralCompletionSemilocalToField`,
  `TauCeti.Place.completionSemilocalEquiv_integralCompletionSemilocalToField`, and
  `TauCeti.Place.integralCompletionSemilocalToField_injective`: compatibility of the integral and
  field semilocal equivalences.
* `TauCeti.Place.completionEmbedding_norm_of_moduleFinite` and
  `TauCeti.Place.completionEmbedding_norm`: **the norm formula**
  `N_{F'/F} x = ∏_{P' ∣ P} N_{F̂'_{P'}/F̂_P} x`.
* `TauCeti.Place.completionEmbedding_trace_of_moduleFinite`,
  `TauCeti.Place.completionEmbedding_trace_of_isSeparable`, and
  `TauCeti.Place.completionEmbedding_trace`: **the trace formula**
  `Tr_{F'/F} x = ∑_{P' ∣ P} Tr_{F̂'_{P'}/F̂_P} x`.
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

open IsLocalRing Module
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
      P.completionExtensionAlgebra P'.val P'.property
    F' →ₛₗ[(P.completionEmbedding : F →+* P.Completion)]
      ∀ P' : {P' : Place k' F' // P'.restrict k F = P}, P'.val.Completion :=
  letI := fun P' : {P' : Place k' F' // P'.restrict k F = P} ↦
    P.completionExtensionAlgebra P'.val P'.property
  { toFun y P' := P'.val.completionEmbedding y
    map_add' _ _ := funext fun _ ↦ map_add _ _ _
    map_smul' c y := funext fun P' ↦ completionEmbedding_smul P P'.val P'.property c y }

/-- `TauCeti.Place.completionEmbeddingPi` is the coordinatewise completion embedding. -/
private theorem completionEmbeddingPi_apply (y : F') :
    completionEmbeddingPi k' P y = fun P' ↦ P'.val.completionEmbedding y :=
  rfl

variable (F') in
/-- **The completed valuation rings above `P` are spanned by the functions regular above `P`**:
the diagonal images of the functions of `F'` regular at every place over `P` span
`∏_{P' ∣ P} 𝒪̂_{P'}` over `𝒪̂_P`. -/
theorem span_completionIntegers_pi_eq_top :
    letI := fun P' : {P' : Place k' F' // P'.restrict k F = P} ↦
      P.completionIntegersExtensionAlgebra P'.val P'.property
    Submodule.span P.completionPlace.integers
      (Set.range fun y : {y : F' // ∀ P' : {P' : Place k' F' // P'.restrict k F = P},
          y ∈ P'.val.integers} ↦
        fun P' : {P' : Place k' F' // P'.restrict k F = P} ↦
          P'.val.completionIntegersEmbedding ⟨y.val, y.property P'⟩) = ⊤ := by
  classical
  let ι := {P' : Place k' F' // P'.restrict k F = P}
  let _ := fun P' : ι ↦ P.completionIntegersExtensionAlgebra P'.val P'.property
  have _ := fun P' : ι ↦ moduleFinite_completionIntegers P P'.val P'.property
  have := Fintype.ofFinite ι
  -- By Nakayama's lemma it suffices to span modulo `𝔪̂_P`.
  refine top_unique (Submodule.le_of_le_smul_of_le_jacobson (I := maximalIdeal _)
    Module.Finite.fg_top (ringJacobson_eq_maximalIdeal _).ge fun m _ ↦ ?_)
  -- Approximate `m` to order `e(P' ∣ P)` at every `P'` by a single function `y`.
  obtain ⟨y, hy⟩ := exists_forall_sub_completionEmbedding_mem_filtration
    (P := fun P' : ι ↦ P'.val) Subtype.val_injective (fun P' ↦ (m P' : P'.val.Completion))
    (fun P' ↦ ramificationIdx F P'.val)
  have hyint (P' : ι) : y ∈ P'.val.integers := by
    have hm := P'.val.completionPlace.mem_filtration_zero_iff.mpr (m P').property
    have h := sub_mem hm (P'.val.completionPlace.filtration_antitone (by simp) (hy P'))
    rw [sub_sub_cancel, completionEmbedding_mem_filtration_iff] at h
    exact P'.val.mem_filtration_zero_iff.mp h
  -- The error is a multiple of a uniformizer of `P` at every coordinate.
  set my := fun P' : ι ↦ P'.val.completionIntegersEmbedding ⟨y, hyint P'⟩
  rw [← add_sub_cancel my m, ← Finset.univ_sum_single (m - my)]
  refine Submodule.add_mem_sup (Submodule.subset_span ⟨⟨y, hyint⟩, rfl⟩)
    (Submodule.sum_mem _ fun P' _ ↦ Submodule.smul_top_le_comap_smul_top _
      (LinearMap.single P.completionPlace.integers (fun P' : ι ↦ P'.val.completionPlace.integers)
          P')
      (mem_maximalIdeal_smul_top_of_mem_filtration P P'.val P'.property ?_))
  simpa [my, completionIntegersEmbedding_apply] using hy P'

variable (F') in
/-- **`F'` spans the completions above `P`**: the diagonal image of `F'` spans
`∏_{P' ∣ P} F̂'_{P'}` over `F̂_P`. -/
theorem span_completion_pi_eq_top :
    letI := fun P' : {P' : Place k' F' // P'.restrict k F = P} ↦
      P.completionExtensionAlgebra P'.val P'.property
    Submodule.span P.Completion
      (Set.range fun (y : F') (P' : {P' : Place k' F' // P'.restrict k F = P}) ↦
        P'.val.completionEmbedding y) = ⊤ := by
  let ι := {P' : Place k' F' // P'.restrict k F = P}
  let _ := fun P' : ι ↦ P.completionExtensionAlgebra P'.val P'.property
  let _ := fun P' : ι ↦ P.completionIntegersExtensionAlgebra P'.val P'.property
  set W := Submodule.span P.Completion
    (Set.range fun (y : F') (P' : ι) ↦ P'.val.completionEmbedding y)
  -- Families of completed integers lie in `W`, since they are spanned by functions of `F'`.
  let toV : (∀ P' : ι, P'.val.completionPlace.integers) →+* ∀ P' : ι, P'.val.Completion :=
    RingHom.pi fun P' ↦ P'.val.completionPlace.integers.subtype.comp (Pi.evalRingHom _ P')
  have hint (m : ∀ P' : ι, P'.val.completionPlace.integers) : toV m ∈ W := by
    refine Submodule.map_mem_span_of_forall_exists (A := P.completionPlace.integers) toV _ _
      (fun a ↦ ⟨(a : P.Completion), funext fun P' ↦ ?_⟩) ?_
      ((span_completionIntegers_pi_eq_top k' F' P).symm ▸ Submodule.mem_top)
    · simp only [toV, RingHom.pi_apply, RingHom.comp_apply, Pi.evalRingHom_apply,
        Pi.algebraMap_apply, ValuationSubring.coe_subtype]
      rw [coe_algebraMap_completionIntegersExtensionAlgebra, algebraMap_completionExtensionAlgebra]
    · rintro _ ⟨y, rfl⟩
      exact Submodule.subset_span ⟨y.val, funext fun P' ↦ by simp [toV]⟩
  refine eq_top_iff.mpr fun z _ ↦ ?_
  -- Subtracting a function of `F'` leaves a family of completed integers.
  obtain ⟨y, hy⟩ := exists_forall_sub_completionEmbedding_mem_filtration
    (P := fun P' : ι ↦ P'.val) Subtype.val_injective z (fun _ ↦ 0)
  have h := W.add_mem (Submodule.subset_span ⟨y, rfl⟩)
    (hint fun P' ↦ ⟨_, P'.val.completionPlace.mem_filtration_zero_iff.mp (hy P')⟩)
  convert h using 1
  funext P'
  simp [toV]

/-- **A spanning family of `F'` spans the completions above `P`**: if `v` spans `F'` over `F`,
its diagonal image spans `∏_{P' ∣ P} F̂'_{P'}` over `F̂_P`. -/
theorem span_completionEmbedding_pi_eq_top {ι' : Type*} {v : ι' → F'}
    (hv : Submodule.span F (Set.range v) = ⊤) :
    letI := fun P' : {P' : Place k' F' // P'.restrict k F = P} ↦
      P.completionExtensionAlgebra P'.val P'.property
    Submodule.span P.Completion
      (Set.range fun (i : ι') (P' : {P' : Place k' F' // P'.restrict k F = P}) ↦
        P'.val.completionEmbedding (v i)) = ⊤ := by
  let _ := fun P' : {P' : Place k' F' // P'.restrict k F = P} ↦
    P.completionExtensionAlgebra P'.val P'.property
  exact (Submodule.span_range_eq_span_range_comp_of_span_eq_top (S := P.Completion) hv
    (completionEmbeddingPi k' P)).symm.trans (span_completion_pi_eq_top k' F' P)

end Spanning

section Dimension

/-! The local-degree sum and preservation of linear independence follow from the fundamental
identity. -/

/-- The diagonal image of an `F`-basis of `F'` is linearly independent over `F̂_P` whenever the
local degrees above `P` add up to `[F' : F]`. -/
private theorem linearIndependent_completionEmbedding_basis_of_finsum
    (hdeg : ∑ᶠ P' : {P' : Place k' F' // P'.restrict k F = P},
        (letI := P.completionExtensionAlgebra P'.val P'.property
        finrank P.Completion P'.val.Completion) = finrank F F')
    {ι' : Type*} (b : Basis ι' F F') :
    letI := fun P' : {P' : Place k' F' // P'.restrict k F = P} ↦
      P.completionExtensionAlgebra P'.val P'.property
    LinearIndependent P.Completion
      fun (i : ι') (P' : {P' : Place k' F' // P'.restrict k F = P}) ↦
        P'.val.completionEmbedding (b i) := by
  let ι := {P' : Place k' F' // P'.restrict k F = P}
  let _ := fun P' : ι ↦ P.completionExtensionAlgebra P'.val P'.property
  have _ := fun P' : ι ↦ finiteDimensional_completion P P'.val P'.property
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
        (letI := P.completionExtensionAlgebra P'.val P'.property
        finrank P.Completion P'.val.Completion) = finrank F F')
    {ι' : Type*} {v : ι' → F'} :
    letI := fun P' : {P' : Place k' F' // P'.restrict k F = P} ↦
      P.completionExtensionAlgebra P'.val P'.property
    LinearIndependent P.Completion
        (fun (i : ι') (P' : {P' : Place k' F' // P'.restrict k F = P}) ↦
          P'.val.completionEmbedding (v i)) ↔
      LinearIndependent F v := by
  let ι := {P' : Place k' F' // P'.restrict k F = P}
  let _ := fun P' : ι ↦ P.completionExtensionAlgebra P'.val P'.property
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

variable [Algebra.IsIntegral k k']

attribute [local instance 10] algebraIntegersExtension isScalarTowerIntegersExtension in
variable (F') in
/-- **The local degrees above `P` add up to the global degree** whenever the local integral closure
`𝒪'_P` is module-finite over `𝒪_P`. -/
theorem finsum_finrank_completion_eq_finrank_of_moduleFinite
    [Module.Finite P.integers (integralClosure P.integers F')] :
    ∑ᶠ P' : {P' : Place k' F' // P'.restrict k F = P},
        (letI := P.completionExtensionAlgebra P'.val P'.property
        finrank P.Completion P'.val.Completion) = finrank F F' := by
  have hfin := finite_setOf_restrict_eq (k' := k') (F' := F') k F P
  have := Fintype.ofFinite {P' : Place k' F' // P'.restrict k F = P}
  rw [finsum_eq_sum_of_fintype,
    ← sum_ramificationIdx_mul_relativeDegree_eq_finrank_of_moduleFinite k F P
      (s := hfin.toFinset) fun _ ↦ hfin.mem_toFinset,
    Finset.sum_subtype hfin.toFinset fun _ ↦ hfin.mem_toFinset]
  exact Finset.sum_congr rfl fun P' _ ↦ finrank_completion P P'.val P'.property

variable (F') in
/-- **The local degrees above `P` add up to the global degree**:
`∑_{P' ∣ P} [F̂'_{P'} : F̂_P] = [F' : F]` for a finite separable extension `F' / F` whose constant
field extension `k' / k` is integral. For an algebraic function field `F / k` separability is not
needed; that is `TauCeti.Place.finsum_finrank_completion_eq_finrank`. -/
theorem finsum_finrank_completion_eq_finrank_of_isSeparable [Algebra.IsSeparable F F'] :
    ∑ᶠ P' : {P' : Place k' F' // P'.restrict k F = P},
        (letI := P.completionExtensionAlgebra P'.val P'.property
        finrank P.Completion P'.val.Completion) = finrank F F' :=
  finsum_finrank_completion_eq_finrank_of_moduleFinite k' F' P

variable (F') in
/-- **The local degrees above `P` add up to the global degree**:
`∑_{P' ∣ P} [F̂'_{P'} : F̂_P] = [F' : F]` for an algebraic function field `F / k` and a finite
extension `F' / F` whose constant field extension `k' / k` is integral, with no separability
hypothesis. For a separable `F' / F` this holds without assuming that `F / k` is a function field;
that is `TauCeti.Place.finsum_finrank_completion_eq_finrank_of_isSeparable`. -/
theorem finsum_finrank_completion_eq_finrank (hF : IsFunctionField k F) :
    ∑ᶠ P' : {P' : Place k' F' // P'.restrict k F = P},
        (letI := P.completionExtensionAlgebra P'.val P'.property
        finrank P.Completion P'.val.Completion) = finrank F F' := by
  have := moduleFinite_integralClosure_of_isFunctionField F' P hF
  exact finsum_finrank_completion_eq_finrank_of_moduleFinite k' F' P

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
      P.completionExtensionAlgebra P'.val P'.property
    LinearIndependent P.Completion
        (fun (i : ι') (P' : {P' : Place k' F' // P'.restrict k F = P}) ↦
          P'.val.completionEmbedding (v i)) ↔
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
      P.completionExtensionAlgebra P'.val P'.property
    LinearIndependent P.Completion
        (fun (i : ι') (P' : {P' : Place k' F' // P'.restrict k F = P}) ↦
          P'.val.completionEmbedding (v i)) ↔
      LinearIndependent F v :=
  linearIndependent_completionEmbedding_pi_iff_of_finsum k' P
    (finsum_finrank_completion_eq_finrank k' F' P hF)

end Dimension

end Unbundled

noncomputable section

attribute [local instance 10] algebraIntegersExtension isScalarTowerIntegersExtension

section ScopedInstances

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
    Algebra F Q.val.Completion :=
  haveI := WithVal.uniformContinuousConstSMul_of_isScalarTower F Q.val.valuation
  UniformSpace.Completion.algebra (WithVal Q.val.valuation) F

/-- For each place `Q` in the fibre above `P`, the local field extension algebra `F̂_P → F̂_Q`.
Installed in the `PlaceCompletionExtension` scope so dependent products over the fibre inherit the
factorwise `F̂_P`-algebra structure without introducing a global self-algebra diamond. Marked
`@[expose]` so downstream modules retain definitional equality with
`TauCeti.Place.completionExtensionAlgebra` across `Algebra`-indexed expressions. -/
@[expose, instance_reducible]
def completionFibreAlgebra [Algebra.IsIntegral F F'] (P : Place k F)
    (Q : {P' : Place k' F' // P'.restrict k F = P}) :
    Algebra P.Completion Q.val.Completion :=
  P.completionExtensionAlgebra Q.val Q.property

/-- For each place `Q` in the fibre above `P`, the local valuation-ring algebra `𝒪̂_P → 𝒪̂_Q`.
Installed in the `PlaceCompletionExtension` scope. Marked `@[expose]` so downstream modules retain
definitional equality with `TauCeti.Place.completionIntegersExtensionAlgebra` across
`Algebra`-indexed expressions such as `differentIdeal`. -/
@[expose, instance_reducible]
def completionIntegersFibreAlgebra [Algebra.IsIntegral F F'] (P : Place k F)
    (Q : {P' : Place k' F' // P'.restrict k F = P}) :
    Algebra P.completionPlace.integers Q.val.completionPlace.integers :=
  P.completionIntegersExtensionAlgebra Q.val Q.property

scoped[PlaceCompletionExtension] attribute [instance]
  TauCeti.Place.completionFibreBaseAlgebra
  TauCeti.Place.completionFibreAlgebra
  TauCeti.Place.completionIntegersFibreAlgebra

/-- The scoped `F`-algebra map into `F̂_Q` embeds `F` into `F'` and then into `F̂_Q`. -/
@[simp]
theorem algebraMap_completionFibreBaseAlgebra [Algebra.IsIntegral F F'] (P : Place k F)
    (Q : {P' : Place k' F' // P'.restrict k F = P}) (x : F) :
    algebraMap F Q.val.Completion x = Q.val.completionEmbedding (algebraMap F F' x) := by
  rw [UniformSpace.Completion.algebraMap_def, WithVal.algebraMap_right_apply,
    Q.val.completionEmbedding_apply]

/-- The scoped `F̂_P`-algebra map into `F̂_Q` acts via `TauCeti.Place.completionExtension`. -/
@[simp]
theorem algebraMap_completionFibreAlgebra [Algebra.IsIntegral F F'] (P : Place k F)
    (Q : {P' : Place k' F' // P'.restrict k F = P}) (x : P.Completion) :
    algebraMap P.Completion Q.val.Completion x = P.completionExtension Q.val Q.property x :=
  congrArg (fun f ↦ f x) (P.algebraMap_completionExtensionAlgebra Q.val Q.property)

/-- The scoped `𝒪̂_P`-algebra map into `𝒪̂_Q` acts via
`TauCeti.Place.completionIntegersExtension`. -/
@[simp]
theorem algebraMap_completionIntegersFibreAlgebra [Algebra.IsIntegral F F'] (P : Place k F)
    (Q : {P' : Place k' F' // P'.restrict k F = P}) (x : P.completionPlace.integers) :
    algebraMap P.completionPlace.integers Q.val.completionPlace.integers x =
      P.completionIntegersExtension Q.val Q.property x :=
  congrArg (fun f ↦ f x) (P.algebraMap_completionIntegersExtensionAlgebra Q.val Q.property)

/-- For each place `Q` in the fibre above `P`, `F → F̂_P → F̂_Q` is a scalar tower. Installed in the
`PlaceCompletionExtension` scope. -/
theorem completionFibreIsScalarTower [Algebra.IsIntegral F F'] (P : Place k F)
    (Q : {P' : Place k' F' // P'.restrict k F = P}) :
    IsScalarTower F P.Completion Q.val.Completion :=
  IsScalarTower.of_algebraMap_eq fun x ↦ by
    rw [algebraMap_completionFibreBaseAlgebra, algebraMap_completion,
      algebraMap_completionFibreAlgebra,
      P.completionExtension_completionEmbedding Q.val Q.property x]

/-- For each place `Q` in the fibre above `P`, `𝒪̂_Q` is torsion-free over `𝒪̂_P`. Installed in the
`PlaceCompletionExtension` scope. -/
theorem completionFibreIsTorsionFree [Algebra.IsIntegral F F'] (P : Place k F)
    (Q : {P' : Place k' F' // P'.restrict k F = P}) :
    Module.IsTorsionFree P.completionPlace.integers Q.val.completionPlace.integers :=
  P.isTorsionFree_completionIntegers Q.val Q.property

scoped[PlaceCompletionExtension] attribute [instance]
  TauCeti.Place.completionFibreIsScalarTower
  TauCeti.Place.completionFibreIsTorsionFree

end ScopedInstances

open scoped PlaceCompletionExtension

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
  rw [integralCompletionSemilocalToField_tmul, Algebra.TensorProduct.tmul_mul_tmul, mul_one,
    TauCeti.Algebra.trace_tmul, algebraMap_completion]

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
      ∀ Q : {P' : Place k' F' // P'.restrict k F = P}, Q.val.completionPlace.integers :=
  letI (Q : {P' : Place k' F' // P'.restrict k F = P}) :
      Algebra P.integers Q.val.completionPlace.integers :=
    ((algebraMap P.completionPlace.integers Q.val.completionPlace.integers).comp
      (algebraMap P.integers P.completionPlace.integers)).toAlgebra
  letI (Q : {P' : Place k' F' // P'.restrict k F = P}) :
      IsScalarTower P.integers P.completionPlace.integers Q.val.completionPlace.integers :=
    .of_algebraMap_eq fun _ ↦ by rw [RingHom.algebraMap_toAlgebra, RingHom.comp_apply]
  Algebra.TensorProduct.lift (Algebra.ofId _ _)
    (AlgHom.pi fun Q ↦
      { P.completionIntegersIntegralClosureHom Q.val Q.property with
        commutes' := fun r ↦ by
          rw [RingHom.toFun_eq_coe,
            IsScalarTower.algebraMap_apply P.integers P.completionPlace.integers
              Q.val.completionPlace.integers,
            completionIntegersIntegralClosureHom_algebraMap,
            algebraMap_completionIntegersAlgebra,
            algebraMap_completionIntegersFibreAlgebra] })
    fun _ _ ↦ .all _ _

/-- The field semilocal algebra map `F̂_P ⊗[F] F' →ₐ[F̂_P] ∏_{Q ∣ P} F̂_Q` sending `a ⊗ x` to
`(a · x)_Q`. -/
def completionSemilocalHom :
    P.Completion ⊗[F] F' →ₐ[P.Completion]
      ∀ Q : {P' : Place k' F' // P'.restrict k F = P}, Q.val.Completion :=
  Algebra.TensorProduct.lift (Algebra.ofId _ _)
    (AlgHom.pi fun Q ↦
      { Q.val.completionEmbedding.toRingHom with
        commutes' := fun x ↦ (algebraMap_completionFibreBaseAlgebra P Q x).symm })
    fun _ _ ↦ .all _ _

variable {k' F' P}

/-- `integralCompletionSemilocalHom` acts componentwise on pure tensors. -/
@[simp]
theorem integralCompletionSemilocalHom_tmul (a : P.completionPlace.integers)
    (b : integralClosure P.integers F') (Q : {P' : Place k' F' // P'.restrict k F = P}) :
    integralCompletionSemilocalHom k' F' P (a ⊗ₜ b) Q =
      algebraMap P.completionPlace.integers Q.val.completionPlace.integers a *
        P.completionIntegersIntegralClosureHom Q.val Q.property b := by
  simp [integralCompletionSemilocalHom]

/-- `completionSemilocalHom` acts componentwise on pure tensors. -/
@[simp]
theorem completionSemilocalHom_tmul (a : P.Completion) (x : F')
    (Q : {P' : Place k' F' // P'.restrict k F = P}) :
    completionSemilocalHom k' F' P (a ⊗ₜ x) Q =
      algebraMap P.Completion Q.val.Completion a * Q.val.completionEmbedding x := by
  simp [completionSemilocalHom]

variable (k' F' P) in
/-- Compatibility of the integral and field semilocal homomorphisms. -/
theorem completionSemilocalHom_integralCompletionSemilocalToField
    (z : P.completionPlace.integers ⊗[P.integers] integralClosure P.integers F') :
    completionSemilocalHom k' F' P (integralCompletionSemilocalToField F' P z) =
      fun Q ↦ (integralCompletionSemilocalHom k' F' P z Q : Q.val.Completion) := by
  induction z using TensorProduct.inductionOn with
  | add x y hx hy =>
    funext Q
    rw [map_add, map_add, Pi.add_apply, hx, hy, map_add, Pi.add_apply, AddMemClass.coe_add]
  | tmul a b =>
    funext Q
    rw [integralCompletionSemilocalToField_tmul, completionSemilocalHom_tmul,
      integralCompletionSemilocalHom_tmul, MulMemClass.coe_mul,
      algebraMap_completionIntegersFibreAlgebra, coe_completionIntegersExtension,
      algebraMap_completionFibreAlgebra, coe_completionIntegersIntegralClosureHom]

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

/-- **The integral semilocal map is surjective** for arbitrary residue fields: functions regular at
every place over `P` lie in `𝒪'_P` and span `∏_{Q ∣ P} 𝒪̂_Q` over `𝒪̂_P` by
`TauCeti.Place.span_completionIntegers_pi_eq_top`. -/
theorem integralCompletionSemilocalHom_surjective :
    Function.Surjective (integralCompletionSemilocalHom k' F' P) := by
  rw [← AlgHom.coe_toLinearMap, ← LinearMap.range_eq_top, eq_top_iff,
    ← span_completionIntegers_pi_eq_top k' F' P, Submodule.span_le]
  rintro _ ⟨y, rfl⟩
  have hy : y.val ∈ integralClosure P.integers F' :=
    (mem_integralClosure_iff_forall_restrict_eq_mem_integers k' P).mpr fun P' hP' ↦
      y.property ⟨P', hP'⟩
  refine ⟨1 ⊗ₜ ⟨y.val, hy⟩, funext fun Q ↦ Subtype.ext ?_⟩
  simp

end Surjective

section Equiv

variable [FiniteDimensional F F'] [Algebra.IsIntegral k k']
variable (k' F') (P : Place k F) [Module.Finite P.integers (integralClosure P.integers F')]

/-- Under `[Module.Finite P.integers (integralClosure P.integers F')]`, the local degrees above `P`
sum to `[F' : F]`. -/
theorem sum_finrank_completion_eq_finrank [Fintype {P' : Place k' F' // P'.restrict k F = P}] :
    ∑ Q : {P' : Place k' F' // P'.restrict k F = P},
      Module.finrank P.Completion Q.val.Completion = Module.finrank F F' := by
  rw [← finsum_eq_sum_of_fintype]
  exact finsum_finrank_completion_eq_finrank_of_moduleFinite k' F' P

/-- The integral semilocal map is bijective. -/
theorem integralCompletionSemilocalHom_bijective :
    Function.Bijective (integralCompletionSemilocalHom k' F' P) := by
  have := Fintype.ofFinite {P' : Place k' F' // P'.restrict k F = P}
  have : Module.Free P.integers (integralClosure P.integers F') :=
    Module.free_of_finite_type_torsion_free'
  have (Q : {P' : Place k' F' // P'.restrict k F = P}) :
      Module.Finite P.completionPlace.integers Q.val.completionPlace.integers :=
    moduleFinite_completionIntegers P Q.val Q.property
  have (Q : {P' : Place k' F' // P'.restrict k F = P}) :
      Module.Free P.completionPlace.integers Q.val.completionPlace.integers :=
    moduleFree_completionIntegers P Q.val Q.property
  refine OrzechProperty.bijective_of_surjective_of_finrank_le
    (integralCompletionSemilocalHom k' F' P).toLinearMap
    (integralCompletionSemilocalHom_surjective k' F' P) ?_
  rw [Module.finrank_baseChange, finrank_integralClosure F' P,
    Module.finrank_pi_fintype, ← sum_finrank_completion_eq_finrank k' F' P]
  refine le_of_eq (Finset.sum_congr rfl fun Q _ ↦ ?_)
  rw [finrank_completion P Q.val Q.property, finrank_completionIntegers P Q.val Q.property]

/-- **The integral semilocal decomposition**
`𝒪̂_P ⊗[𝒪_P] 𝒪'_P ≃ₐ[𝒪̂_P] ∏_{Q ∣ P} 𝒪̂_Q`, valid for arbitrary residue fields. -/
def integralCompletionSemilocalEquiv :
    P.completionPlace.integers ⊗[P.integers] integralClosure P.integers F' ≃ₐ[
        P.completionPlace.integers]
      ∀ Q : {P' : Place k' F' // P'.restrict k F = P}, Q.val.completionPlace.integers :=
  AlgEquiv.ofBijective (integralCompletionSemilocalHom k' F' P)
    (integralCompletionSemilocalHom_bijective k' F' P)

variable {k' F' P} in
/-- `integralCompletionSemilocalEquiv` acts componentwise on pure tensors. -/
@[simp]
theorem integralCompletionSemilocalEquiv_tmul (a : P.completionPlace.integers)
    (b : integralClosure P.integers F') (Q : {P' : Place k' F' // P'.restrict k F = P}) :
    integralCompletionSemilocalEquiv k' F' P (a ⊗ₜ b) Q =
      algebraMap P.completionPlace.integers Q.val.completionPlace.integers a *
        P.completionIntegersIntegralClosureHom Q.val Q.property b :=
  integralCompletionSemilocalHom_tmul a b Q

/-- The field semilocal map is bijective. -/
theorem completionSemilocalHom_bijective :
    Function.Bijective (completionSemilocalHom k' F' P) := by
  have := Fintype.ofFinite {P' : Place k' F' // P'.restrict k F = P}
  have (Q : {P' : Place k' F' // P'.restrict k F = P}) :
      FiniteDimensional P.Completion Q.val.Completion :=
    finiteDimensional_completion P Q.val Q.property
  have hdim : Module.finrank P.Completion (P.Completion ⊗[F] F') =
      Module.finrank P.Completion
        (∀ Q : {P' : Place k' F' // P'.restrict k F = P}, Q.val.Completion) := by
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
      ∀ Q : {P' : Place k' F' // P'.restrict k F = P}, Q.val.Completion :=
  AlgEquiv.ofBijective (completionSemilocalHom k' F' P) (completionSemilocalHom_bijective k' F' P)

variable {k' F' P} in
/-- `completionSemilocalEquiv` acts componentwise on pure tensors. -/
@[simp]
theorem completionSemilocalEquiv_tmul (a : P.Completion) (x : F')
    (Q : {P' : Place k' F' // P'.restrict k F = P}) :
    completionSemilocalEquiv k' F' P (a ⊗ₜ x) Q =
      algebraMap P.Completion Q.val.Completion a * Q.val.completionEmbedding x :=
  completionSemilocalHom_tmul a x Q

/-- After inclusion into the completions, `integralCompletionSemilocalEquiv` agrees with
`completionSemilocalEquiv`. -/
theorem completionSemilocalEquiv_integralCompletionSemilocalToField
    (z : P.completionPlace.integers ⊗[P.integers] integralClosure P.integers F') :
    completionSemilocalEquiv k' F' P (integralCompletionSemilocalToField F' P z) =
      fun Q ↦ (integralCompletionSemilocalEquiv k' F' P z Q : Q.val.Completion) :=
  completionSemilocalHom_integralCompletionSemilocalToField k' F' P z

/-! ### Norm and trace in the semilocal decomposition -/

/-- The norm of `F̂_P ⊗[F] F'` over `F̂_P` is the product of the norms of its semilocal
components. -/
theorem norm_eq_prod_norm_completionSemilocalEquiv
    [Fintype {P' : Place k' F' // P'.restrict k F = P}] (ξ : P.Completion ⊗[F] F') :
    Algebra.norm P.Completion ξ =
      ∏ Q : {P' : Place k' F' // P'.restrict k F = P},
        Algebra.norm P.Completion (completionSemilocalEquiv k' F' P ξ Q) := by
  have (Q : {P' : Place k' F' // P'.restrict k F = P}) :
      FiniteDimensional P.Completion Q.val.Completion :=
    finiteDimensional_completion P Q.val Q.property
  rw [← Algebra.norm_eq_of_algEquiv (completionSemilocalEquiv k' F' P)]
  exact TauCeti.Algebra.norm_pi _

variable {F'} in
/-- **Local–global norm decomposition** under `[Module.Finite P.integers (integralClosure
P.integers F')]`: the norm of `x ∈ F'` in `F̂_P` is the product of its local norms across the
places `P'` of `F' / k'` lying over `P`. When `F' / F` is separable, the finiteness hypothesis is
supplied automatically by `TauCeti.Place.moduleFinite_integralClosure`. -/
theorem completionEmbedding_norm_of_moduleFinite (x : F') :
    P.completionEmbedding (Algebra.norm F x) =
      ∏ᶠ P' : {P' : Place k' F' // P'.restrict k F = P},
        (letI := P.completionExtensionAlgebra P'.val P'.property
        Algebra.norm P.Completion (P'.val.completionEmbedding x)) := by
  have := Fintype.ofFinite {P' : Place k' F' // P'.restrict k F = P}
  rw [finprod_eq_prod_of_fintype, ← algebraMap_completion,
    ← TauCeti.Algebra.norm_baseChange_tmul (A := P.Completion) (B := F') x,
    norm_eq_prod_norm_completionSemilocalEquiv k' F' P]
  exact Finset.prod_congr rfl fun Q _ ↦ by simp

/-- The trace of `F̂_P ⊗[F] F'` over `F̂_P` is the sum of the traces of its semilocal components. -/
theorem trace_eq_sum_trace_completionSemilocalEquiv
    [Fintype {P' : Place k' F' // P'.restrict k F = P}] (ξ : P.Completion ⊗[F] F') :
    Algebra.trace P.Completion (P.Completion ⊗[F] F') ξ =
      ∑ Q : {P' : Place k' F' // P'.restrict k F = P},
        Algebra.trace P.Completion Q.val.Completion (completionSemilocalEquiv k' F' P ξ Q) := by
  have (Q : {P' : Place k' F' // P'.restrict k F = P}) :
      FiniteDimensional P.Completion Q.val.Completion :=
    finiteDimensional_completion P Q.val Q.property
  rw [← Algebra.trace_eq_of_algEquiv (completionSemilocalEquiv k' F' P)]
  exact TauCeti.Algebra.trace_pi _

variable {F'} in
/-- **Local–global trace decomposition** under `[Module.Finite P.integers (integralClosure
P.integers F')]`: the trace of `x ∈ F'` in `F̂_P` is the sum of its local traces across the
places `P'` of `F' / k'` lying over `P`. -/
theorem completionEmbedding_trace_of_moduleFinite (x : F') :
    P.completionEmbedding (Algebra.trace F F' x) =
      ∑ᶠ P' : {P' : Place k' F' // P'.restrict k F = P},
        (letI := P.completionExtensionAlgebra P'.val P'.property
        Algebra.trace P.Completion P'.val.Completion (P'.val.completionEmbedding x)) := by
  have := Fintype.ofFinite {P' : Place k' F' // P'.restrict k F = P}
  rw [finsum_eq_sum_of_fintype, ← algebraMap_completion,
    ← TauCeti.Algebra.trace_baseChange_tmul (A := P.Completion) (B := F') x,
    trace_eq_sum_trace_completionSemilocalEquiv k' F' P]
  exact Finset.sum_congr rfl fun Q _ ↦ by simp

variable {k' F' P} in
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
  have := Fintype.ofFinite {Q : Place k' F' // Q.restrict k F = P}
  rw [trace_eq_sum_trace_completionSemilocalEquiv k' F' P, Finset.sum_eq_single
    (⟨P', hP⟩ : {Q : Place k' F' // Q.restrict k F = P})]
  · simp
  · intro Q _ hQ
    rw [map_mul, AlgEquiv.apply_symm_apply, Pi.mul_apply, Pi.single_eq_of_ne hQ, zero_mul,
      map_zero]
  · simp

end Equiv

section NormTraceSpecializations

variable [FiniteDimensional F F'] [Algebra.IsIntegral k k'] (k') (P : Place k F)

/-- **The norm formula**: for an algebraic function field `F / k`, a finite extension `F' / F`
whose constant field extension `k' / k` is integral and a place `P` of `F`, the norm of `x ∈ F'`
over `F` is, in the completion at `P`, the product of the norms of `x` over the completions
`F̂'_{P'} / F̂_P` at the places `P'` above `P`, with no separability hypothesis. For a separable
`F' / F` over an arbitrary base field, use `TauCeti.Place.completionEmbedding_norm_of_moduleFinite`
directly. -/
theorem completionEmbedding_norm (hF : IsFunctionField k F) (x : F') :
    P.completionEmbedding (Algebra.norm F x) =
      ∏ᶠ P' : {P' : Place k' F' // P'.restrict k F = P},
        (letI := P.completionExtensionAlgebra P'.val P'.property
        Algebra.norm P.Completion (P'.val.completionEmbedding x)) := by
  have := moduleFinite_integralClosure_of_isFunctionField F' P hF
  exact completionEmbedding_norm_of_moduleFinite k' P x

/-- **The trace formula**: for a finite separable extension `F' / F` whose constant field
extension `k' / k` is integral and a place `P` of `F`, the trace of `x ∈ F'` over `F` is, in the
completion at `P`, the sum of the traces of `x` over the completions `F̂'_{P'} / F̂_P` at the places
`P'` above `P`. For an algebraic function field `F / k` separability is not needed; that is
`TauCeti.Place.completionEmbedding_trace`. -/
theorem completionEmbedding_trace_of_isSeparable [Algebra.IsSeparable F F'] (x : F') :
    P.completionEmbedding (Algebra.trace F F' x) =
      ∑ᶠ P' : {P' : Place k' F' // P'.restrict k F = P},
        (letI := P.completionExtensionAlgebra P'.val P'.property
        Algebra.trace P.Completion P'.val.Completion (P'.val.completionEmbedding x)) :=
  completionEmbedding_trace_of_moduleFinite k' P x

/-- **The trace formula**: for an algebraic function field `F / k`, a finite extension `F' / F`
whose constant field extension `k' / k` is integral and a place `P` of `F`, the trace of `x ∈ F'`
over `F` is, in the completion at `P`, the sum of the traces of `x` over the completions
`F̂'_{P'} / F̂_P` at the places `P'` above `P`. No separability hypothesis is needed. For a
separable `F' / F` this holds without assuming that `F / k` is a function field; that is
`TauCeti.Place.completionEmbedding_trace_of_isSeparable`. -/
theorem completionEmbedding_trace (hF : IsFunctionField k F) (x : F') :
    P.completionEmbedding (Algebra.trace F F' x) =
      ∑ᶠ P' : {P' : Place k' F' // P'.restrict k F = P},
        (letI := P.completionExtensionAlgebra P'.val P'.property
        Algebra.trace P.Completion P'.val.Completion (P'.val.completionEmbedding x)) := by
  have := moduleFinite_integralClosure_of_isFunctionField F' P hF
  exact completionEmbedding_trace_of_moduleFinite k' P x

end NormTraceSpecializations

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
  exact congrFun
    ((completionSemilocalEquiv_integralCompletionSemilocalToField k F' P x).symm.trans
      ((congrArg (completionSemilocalEquiv k F' P) h).trans
        (completionSemilocalEquiv_integralCompletionSemilocalToField k F' P y))) Q

end ToFieldInjective

end

end TauCeti.Place
