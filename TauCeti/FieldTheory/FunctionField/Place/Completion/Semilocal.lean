/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Dimension.OrzechProperty
public import Mathlib.RingTheory.Flat.TorsionFree
public import Mathlib.RingTheory.Nakayama
public import TauCeti.FieldTheory.FunctionField.Place.Completion.Approximation
public import TauCeti.FieldTheory.FunctionField.Place.Completion.Separable
public import TauCeti.FieldTheory.FunctionField.Place.Extension.Fundamental
public import TauCeti.RingTheory.NormTrace.BaseChange
public import TauCeti.RingTheory.NormTrace.Pi
import TauCeti.LinearAlgebra.Span.Basic

/-!
# The semilocal decomposition of an extension of function fields at a place

Let `F' / F` be a finite extension of fields with constant fields `k' / k`, `P` a place of `F / k`,
and `P'` run over the finitely many places of `F' / k'` lying over `P`. Each completion `F̂'_{P'}`
is a finite extension of `F̂_P` (`TauCeti.Place.finrank_completion`), and this file compares the
diagonal map from `F'` into `∏_{P' ∣ P} F̂'_{P'}` with scalar extension to `F̂_P` and `𝒪̂_P` both on
families of vectors and as bundled tensor-product algebra equivalences:

* **Spanning** (for any finite extension `F' / F`, with no hypothesis on `k' / k` or separability):
  the functions of `F'` regular at every place over `P` span `∏_{P' ∣ P} 𝒪̂_{P'}` over `𝒪̂_P` by
  weak approximation (`TauCeti.Place.exists_forall_sub_completionEmbedding_mem_filtration`) and
  Nakayama's lemma, and `F'` spans `∏_{P' ∣ P} F̂'_{P'}` over `F̂_P`. Consequently
  `semilocalHom` is surjective without assuming `k' / k` integral, and `integralSemilocalHom` is
  surjective whenever `k' / k` is integral.
* **Dimension and basis comparison** (when `k' / k` is integral and either `F' / F` is separable or
  `F / k` is an algebraic function field): the local degrees `e(P' ∣ P) f(P' ∣ P)` sum to
  `[F' : F]`, linear independence over `F` is preserved and reflected in `∏_{P' ∣ P} F̂'_{P'}`, and
  `Tr_{F'/F} x = ∑_{P' ∣ P} Tr_{F̂'_{P'}/F̂_P} x`.
* **Bundled semilocal equivalences** (when `F' / F` is finite separable and `k' / k` is integral,
  with no `IsFunctionField`, characteristic, or residue-field assumptions):
  `F̂_P ⊗[F] F' ≃ₐ[F̂_P] ∏_{P' ∣ P} F̂'_{P'}` (`TauCeti.Place.semilocalEquiv`) and
  `𝒪̂_P ⊗[𝒪_P] 𝒪'_P ≃ₐ[𝒪̂_P] ∏_{P' ∣ P} 𝒪̂_{P'}` (`TauCeti.Place.integralSemilocalEquiv`), where
  `𝒪'_P` is the integral closure of `𝒪_P` in `F'`, together with tensor-level trace and norm
  decompositions and single-place transfer of trace-dual expansions.

Single-place and unbundled statements bind `TauCeti.Place.completionExtensionAlgebra` and
`TauCeti.Place.completionIntegersExtensionAlgebra` locally via `letI`; bundled fiber-indexed
declarations use `open scoped PlaceCompletion` (`fiberCompletionAlgebra`,
`fiberCompletionIntegersAlgebra`, and companion `Prop` instances) so they never compete with
`Algebra.id`. The bundled interface parallels `TauCeti.semilocalEquiv` and
`TauCeti.integralSemilocalEquiv` in `TauCeti/NumberTheory/NumberField/LocalGlobal/Semilocal/`.

## Main definitions

* `TauCeti.Place.fiberCompletionAlgebra`, `TauCeti.Place.fiberCompletionIntegersAlgebra`: scoped
  `PlaceCompletion` algebra structures on `Q.1.Completion` and `Q.1.completionPlace.integers`.
* `TauCeti.Place.semilocalHom`, `TauCeti.Place.integralSemilocalHom`,
  `TauCeti.Place.semilocalEquiv`, `TauCeti.Place.integralSemilocalEquiv`: field and integral
  semilocal algebra homomorphisms and isomorphisms above `P`.
* `TauCeti.Place.integralSemilocalToField`: injective `𝒪_P`-algebra map
  `𝒪̂_P ⊗[𝒪_P] 𝒪'_P →ₐ[𝒪_P] F̂_P ⊗[F] F'`.

## Main results

* `TauCeti.Place.span_completionIntegers_pi_eq_top`, `TauCeti.Place.span_completion_pi_eq_top`,
  `TauCeti.Place.span_completionEmbedding_pi_eq_top`: spanning of `∏_{P' ∣ P} 𝒪̂_{P'}` and
  `∏_{P' ∣ P} F̂'_{P'}` for any finite `F' / F`.
* `TauCeti.Place.finsum_finrank_completion_eq_finrank`,
  `TauCeti.Place.finsum_finrank_completion_eq_finrank_of_isSeparable`,
  `TauCeti.Place.linearIndependent_completionEmbedding_pi_iff`,
  `TauCeti.Place.linearIndependent_completionEmbedding_pi_iff_of_isSeparable`,
  `TauCeti.Place.completionEmbedding_trace`,
  `TauCeti.Place.completionEmbedding_trace_of_isSeparable`: local degree sum, linear-independence
  transfer, and trace formula under `IsFunctionField k F` or `[Algebra.IsSeparable F F']`.
* `TauCeti.Place.semilocalHom_surjective` (without `[Algebra.IsIntegral k k']` or separability) and
  `TauCeti.Place.integralSemilocalHom_surjective` (for finite `F' / F` and integral `k' / k`).
* `TauCeti.Place.trace_eq_sum_trace_semilocalEquiv`,
  `TauCeti.Place.trace_semilocalEquiv_symm_single_mul`,
  `TauCeti.Place.norm_eq_prod_norm_semilocalEquiv`,
  `TauCeti.Place.completionEmbedding_norm_eq_prod_norm`: tensor-product trace and norm
  decompositions (when `F' / F` is finite separable and `k' / k` is integral).
* `TauCeti.Place.trace_integralSemilocalToField_tmul_mul`,
  `TauCeti.Place.sum_trace_mul_smul_completionEmbedding_eq`: integral-tensor trace pairing and
  transfer of trace-dual expansions to completions (without `[Algebra.IsIntegral k k']`).

## References

* H. Stichtenoth, *Algebraic Function Fields and Codes*, 2nd ed., GTM 254, Springer, 2009,
  Sections I.3, III.1–III.2, and IV.2.
* J.-P. Serre, *Local Fields*, GTM 67, Springer, 1979, Chapter II, §3.
* J. Neukirch, *Algebraic Number Theory*, Chapter II, Proposition (8.3).
-/

public section

open IsLocalRing Module
open scoped TensorProduct BigOperators

namespace TauCeti.Place

section SpanningAndDimension

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

end SpanningAndDimension

open IsDedekindDomain

attribute [local instance 10] algebraIntegersExtension isScalarTowerIntegersExtension

section FiberInstances

variable {k k' F F' : Type*} [Field k] [Field k'] [Field F] [Field F']
  [Algebra k F] [Algebra k k'] [Algebra k' F'] [Algebra k F'] [Algebra F F']
  [IsScalarTower k k' F'] [IsScalarTower k F F']

section Integral

variable [Algebra.IsIntegral F F'] {P : Place k F}

/-- For a place `Q` in the fiber over `P`, the completed field `F̂'_Q` as an `F̂_P`-algebra.
Registered as a scoped instance in `PlaceCompletion`. -/
@[expose, instance_reducible]
noncomputable def fiberCompletionAlgebra (Q : {P' : Place k' F' // P'.restrict k F = P}) :
    Algebra P.Completion Q.1.Completion :=
  P.completionExtensionAlgebra Q.1 Q.2

/-- For a place `Q` in the fiber over `P`, the completed valuation ring `𝒪̂_Q` as an
`𝒪̂_P`-algebra. Registered as a scoped instance in `PlaceCompletion`. -/
@[expose, instance_reducible]
noncomputable def fiberCompletionIntegersAlgebra (Q : {P' : Place k' F' // P'.restrict k F = P}) :
    Algebra P.completionPlace.integers Q.1.completionPlace.integers :=
  P.completionIntegersExtensionAlgebra Q.1 Q.2

scoped[PlaceCompletion] attribute [instance]
  TauCeti.Place.fiberCompletionAlgebra TauCeti.Place.fiberCompletionIntegersAlgebra

open scoped PlaceCompletion

/-- On a place `Q` in the fiber over `P`, `algebraMap P.Completion Q.1.Completion` is
`P.completionExtension Q.1 Q.2`. -/
theorem algebraMap_fiberCompletionAlgebra (Q : {P' : Place k' F' // P'.restrict k F = P}) :
    algebraMap P.Completion Q.1.Completion = P.completionExtension Q.1 Q.2 :=
  P.algebraMap_completionExtensionAlgebra Q.1 Q.2

/-- On a place `Q` in the fiber over `P`,
`algebraMap P.completionPlace.integers Q.1.completionPlace.integers` is
`P.completionIntegersExtension Q.1 Q.2`. -/
theorem algebraMap_fiberCompletionIntegersAlgebra (Q : {P' : Place k' F' // P'.restrict k F = P}) :
    algebraMap P.completionPlace.integers Q.1.completionPlace.integers =
      P.completionIntegersExtension Q.1 Q.2 :=
  P.algebraMap_completionIntegersExtensionAlgebra Q.1 Q.2

@[simp]
theorem coe_algebraMap_fiberCompletionIntegersAlgebra
    (Q : {P' : Place k' F' // P'.restrict k F = P}) (x : P.completionPlace.integers) :
    (algebraMap P.completionPlace.integers Q.1.completionPlace.integers x : Q.1.Completion) =
      P.completionExtension Q.1 Q.2 x :=
  P.coe_algebraMap_completionIntegersExtensionAlgebra Q.1 Q.2 x

/-- Scalar-tower compatibility `𝒪̂_P → 𝒪̂_Q → F̂'_Q` on a place `Q` in the fiber over `P`. -/
theorem isScalarTower_fiberCompletionIntegers (Q : {P' : Place k' F' // P'.restrict k F = P}) :
    IsScalarTower P.completionPlace.integers Q.1.completionPlace.integers Q.1.Completion :=
  P.isScalarTower_completionIntegersExtension Q.1 Q.2

/-- Torsion-freeness of `𝒪̂_Q` over `𝒪̂_P` for a place `Q` in the fiber over `P`. -/
theorem isTorsionFree_fiberCompletionIntegers (Q : {P' : Place k' F' // P'.restrict k F = P}) :
    Module.IsTorsionFree P.completionPlace.integers Q.1.completionPlace.integers :=
  P.isTorsionFree_completionIntegersExtension Q.1 Q.2

/-- Locality of `𝒪̂_P →+* 𝒪̂_Q` for a place `Q` in the fiber over `P`. -/
theorem isLocalHom_algebraMap_fiberCompletionIntegers
    (Q : {P' : Place k' F' // P'.restrict k F = P}) :
    IsLocalHom (algebraMap P.completionPlace.integers Q.1.completionPlace.integers) :=
  P.isLocalHom_algebraMap_completionIntegersExtensionAlgebra Q.1 Q.2

scoped[PlaceCompletion] attribute [instance]
  TauCeti.Place.isScalarTower_fiberCompletionIntegers
  TauCeti.Place.isTorsionFree_fiberCompletionIntegers
  TauCeti.Place.isLocalHom_algebraMap_fiberCompletionIntegers

end Integral

section Finite

open scoped PlaceCompletion

variable [FiniteDimensional F F'] {P : Place k F}

/-- Finite-dimensionality of `F̂'_Q` over `F̂_P` for a place `Q` in the fiber over `P`. -/
theorem finiteDimensional_fiberCompletion (Q : {P' : Place k' F' // P'.restrict k F = P}) :
    FiniteDimensional P.Completion Q.1.Completion :=
  P.finiteDimensional_completion Q.1 Q.2

/-- Module-finiteness of `𝒪̂_Q` over `𝒪̂_P` for a place `Q` in the fiber over `P`. -/
theorem moduleFinite_fiberCompletionIntegers (Q : {P' : Place k' F' // P'.restrict k F = P}) :
    Module.Finite P.completionPlace.integers Q.1.completionPlace.integers :=
  P.moduleFinite_completionIntegers Q.1 Q.2

/-- Module-freeness of `𝒪̂_Q` over `𝒪̂_P` for a place `Q` in the fiber over `P`. -/
theorem moduleFree_fiberCompletionIntegers (Q : {P' : Place k' F' // P'.restrict k F = P}) :
    Module.Free P.completionPlace.integers Q.1.completionPlace.integers :=
  P.moduleFree_completionIntegers Q.1 Q.2

/-- Integral-closure property of `𝒪̂_Q` over `𝒪̂_P` in `F̂'_Q` for `Q` in the fiber over `P`. -/
theorem isIntegralClosure_fiberCompletionIntegers (Q : {P' : Place k' F' // P'.restrict k F = P}) :
    IsIntegralClosure Q.1.completionPlace.integers P.completionPlace.integers Q.1.Completion :=
  P.isIntegralClosure_completionIntegers Q.1 Q.2

scoped[PlaceCompletion] attribute [instance]
  TauCeti.Place.finiteDimensional_fiberCompletion
  TauCeti.Place.moduleFinite_fiberCompletionIntegers
  TauCeti.Place.moduleFree_fiberCompletionIntegers
  TauCeti.Place.isIntegralClosure_fiberCompletionIntegers

end Finite

section Separable

open scoped PlaceCompletion

variable [FiniteDimensional F F'] [Algebra.IsSeparable F F'] {P : Place k F}

/-- Separability of `F̂'_Q` over `F̂_P` for a place `Q` in the fiber over `P`. -/
theorem isSeparable_fiberCompletion (Q : {P' : Place k' F' // P'.restrict k F = P}) :
    Algebra.IsSeparable P.Completion Q.1.Completion :=
  P.isSeparable_completion Q.1 Q.2

scoped[PlaceCompletion] attribute [instance] TauCeti.Place.isSeparable_fiberCompletion

end Separable

end FiberInstances

open scoped PlaceCompletion

section IntegralToField

variable {k F F' : Type*} [Field k] [Field F] [Field F'] [Algebra k F] [Algebra F F']

variable (F') in
/-- The canonical `𝒪_P`-algebra homomorphism from `𝒪̂_P ⊗[𝒪_P] 𝒪'_P` to `F̂_P ⊗[F] F'`. -/
noncomputable def integralSemilocalToField (P : Place k F) :
    P.completionPlace.integers ⊗[P.integers] integralClosure P.integers F' →ₐ[P.integers]
      P.Completion ⊗[F] F' :=
  TauCeti.baseChangeOfTower P.integers F P.completionPlace.integers
    P.Completion (integralClosure P.integers F') F'

/-- `integralSemilocalToField` is `TauCeti.baseChangeOfTower` for the local completion square
`(𝒪_P, F, 𝒪̂_P, F̂_P, 𝒪'_P, F')`. -/
theorem integralSemilocalToField_eq_baseChangeOfTower (P : Place k F) :
    integralSemilocalToField F' P =
      TauCeti.baseChangeOfTower P.integers F P.completionPlace.integers
        P.Completion (integralClosure P.integers F') F' :=
  (rfl)

@[simp]
theorem integralSemilocalToField_tmul (P : Place k F) (a : P.completionPlace.integers)
    (x : integralClosure P.integers F') :
    integralSemilocalToField F' P (a ⊗ₜ x) = (a : P.Completion) ⊗ₜ (x : F') := by
  simp [integralSemilocalToField]

variable (F') in
/-- The canonical map `𝒪̂_P ⊗[𝒪_P] 𝒪'_P → F̂_P ⊗[F] F'` is injective. -/
theorem integralSemilocalToField_injective [Algebra.IsIntegral F F'] (P : Place k F) :
    Function.Injective (integralSemilocalToField F' P) := by
  have : Module.IsTorsionFree P.integers (integralClosure P.integers F') :=
    IsIntegralClosure.isTorsionFree P.integers F'
  have : Module.IsTorsionFree P.integers F' := .trans_faithfulSMul P.integers F F'
  have : Algebra.IsAlgebraic P.integers F' :=
    IsFractionRing.comap_isAlgebraic_iff (K := F).mpr inferInstance
  have : IsFractionRing (integralClosure P.integers F') F' :=
    integralClosure.isFractionRing_of_algebraic fun _ ↦
      (injective_iff_map_eq_zero _).mp (FaithfulSMul.algebraMap_injective P.integers F') _
  exact TauCeti.baseChangeOfTower_injective P.integers F
    P.completionPlace.integers P.Completion (integralClosure P.integers F') F'

/-- The trace of a pure integral tensor paired with an element of `F'` is the scalar extension of
the trace pairing of `F' / F`. -/
theorem trace_integralSemilocalToField_tmul_mul (P : Place k F)
    (a : P.completionPlace.integers) (x : integralClosure P.integers F') (d : F') :
    Algebra.trace P.Completion (P.Completion ⊗[F] F')
        (integralSemilocalToField F' P (a ⊗ₜ x) * (1 ⊗ₜ d)) =
      (a : P.Completion) * P.completionEmbedding (Algebra.trace F F' ((x : F') * d)) := by
  simpa [integralSemilocalToField] using
    TauCeti.Algebra.trace_baseChangeOfTower_tmul_mul (R := P.integers) (K := F)
      (A := P.Completion) a x d

end IntegralToField

section Semilocal

variable {k k' F F' : Type*} [Field k] [Field k'] [Field F] [Field F']
  [Algebra k F] [Algebra k k'] [Algebra k' F'] [Algebra k F'] [Algebra F F']
  [IsScalarTower k k' F'] [IsScalarTower k F F']

section Maps

variable [Algebra.IsIntegral F F'] (k' F') (P : Place k F)

/-- The canonical `𝒪̂_P`-algebra homomorphism from `𝒪̂_P ⊗[𝒪_P] 𝒪'_P` to the product of the
completed valuation rings above `P`. -/
noncomputable def integralSemilocalHom :
    P.completionPlace.integers ⊗[P.integers] integralClosure P.integers F' →ₐ[
      P.completionPlace.integers]
      (∀ Q : {P' : Place k' F' // P'.restrict k F = P}, Q.1.completionPlace.integers) :=
  letI (Q : {P' : Place k' F' // P'.restrict k F = P}) :
      Algebra P.integers Q.1.completionPlace.integers :=
    ((algebraMap P.completionPlace.integers Q.1.completionPlace.integers).comp
      (algebraMap P.integers P.completionPlace.integers)).toAlgebra
  letI (Q : {P' : Place k' F' // P'.restrict k F = P}) :
      IsScalarTower P.integers P.completionPlace.integers Q.1.completionPlace.integers :=
    IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  Algebra.TensorProduct.lift (Algebra.ofId _ _)
    (AlgHom.pi fun Q ↦
      { P.integralClosureToCompletionIntegers Q.1 Q.2 with
        commutes' := fun r ↦ by
          rw [RingHom.toFun_eq_coe, RingHom.algebraMap_toAlgebra, RingHom.comp_apply,
            algebraMap_fiberCompletionIntegersAlgebra, P.algebraMap_completionIntegers,
            AlgHom.toRingHom_eq_coe, RingHom.coe_coe,
            P.integralClosureToCompletionIntegers_algebraMap Q.1 Q.2 r] })
    fun _ _ ↦ .all _ _

variable {k' F' P} in
@[simp]
theorem integralSemilocalHom_tmul (a : P.completionPlace.integers)
    (x : integralClosure P.integers F') (Q : {P' : Place k' F' // P'.restrict k F = P}) :
    integralSemilocalHom k' F' P (a ⊗ₜ x) Q =
      P.completionIntegersExtension Q.1 Q.2 a *
        P.integralClosureToCompletionIntegers Q.1 Q.2 x := by
  simp [integralSemilocalHom, algebraMap_fiberCompletionIntegersAlgebra]

/-- The canonical `F̂_P`-algebra homomorphism from `F̂_P ⊗[F] F'` to the product of the completed
fields above `P`. -/
noncomputable def semilocalHom :
    P.Completion ⊗[F] F' →ₐ[P.Completion]
      (∀ Q : {P' : Place k' F' // P'.restrict k F = P}, Q.1.Completion) :=
  letI (Q : {P' : Place k' F' // P'.restrict k F = P}) :
      UniformContinuousConstSMul F (WithVal Q.1.valuation) :=
    WithVal.uniformContinuousConstSMul_of_isScalarTower F Q.1.valuation
  have (Q : {P' : Place k' F' // P'.restrict k F = P}) :
      IsScalarTower F P.Completion Q.1.Completion :=
    IsScalarTower.of_algebraMap_eq fun x ↦ by
      rw [UniformSpace.Completion.algebraMap_def, WithVal.algebraMap_right_apply,
        ← Q.1.completionEmbedding_apply, algebraMap_fiberCompletionAlgebra,
        P.algebraMap_completion_eq_completionEmbedding,
        P.completionExtension_completionEmbedding Q.1 Q.2]
  Algebra.TensorProduct.lift (Algebra.ofId _ _)
    (AlgHom.pi fun Q ↦
      { Q.1.completionEmbedding.toRingHom with
        commutes' := fun x ↦ by
          rw [RingHom.toFun_eq_coe, AlgHom.toRingHom_eq_coe, RingHom.coe_coe,
            UniformSpace.Completion.algebraMap_def, WithVal.algebraMap_right_apply,
            ← Q.1.completionEmbedding_apply] })
    fun _ _ ↦ .all _ _

variable {k' F' P} in
@[simp]
theorem semilocalHom_tmul (a : P.Completion) (x : F')
    (Q : {P' : Place k' F' // P'.restrict k F = P}) :
    semilocalHom k' F' P (a ⊗ₜ x) Q =
      P.completionExtension Q.1 Q.2 a * Q.1.completionEmbedding x := by
  simp [semilocalHom, algebraMap_fiberCompletionAlgebra]

end Maps

/-- After inclusion into the completions, `integralSemilocalHom` agrees with `semilocalHom`. -/
theorem integralSemilocalHom_fieldCompatibility [Algebra.IsIntegral F F'] (P : Place k F)
    (z : P.completionPlace.integers ⊗[P.integers] integralClosure P.integers F') :
    semilocalHom k' F' P (integralSemilocalToField F' P z) =
      fun Q ↦ (integralSemilocalHom k' F' P z Q : Q.1.Completion) := by
  induction z using TensorProduct.inductionOn with
  | tmul a x => funext Q; simp [coe_completionIntegersExtension]
  | add x y hx hy => funext Q; simp [congrFun hx Q, congrFun hy Q]

section Surjective

variable [FiniteDimensional F F'] (k' F')

/-- **Surjectivity of the field semilocal map**: for any finite extension `F' / F`,
`semilocalHom k' F' P` is surjective (with no assumption on `k' / k` or separability). -/
theorem semilocalHom_surjective (P : Place k F) :
    Function.Surjective (semilocalHom k' F' P) := by
  rw [← AlgHom.coe_toLinearMap, ← LinearMap.range_eq_top, eq_top_iff,
    ← span_completion_pi_eq_top k' F' P, Submodule.span_le]
  rintro _ ⟨y, rfl⟩
  exact ⟨1 ⊗ₜ y, funext fun Q ↦ by simp⟩

/-- **Surjectivity of the integral semilocal map**: for a finite extension `F' / F` and an integral
constant extension `k' / k`, `integralSemilocalHom k' F' P` is surjective. -/
theorem integralSemilocalHom_surjective [Algebra.IsIntegral k k'] (P : Place k F) :
    Function.Surjective (integralSemilocalHom k' F' P) := by
  rw [← AlgHom.coe_toLinearMap, ← LinearMap.range_eq_top, eq_top_iff,
    ← span_completionIntegers_pi_eq_top k' F' P, Submodule.span_le]
  rintro _ ⟨y, rfl⟩
  have hy : y.1 ∈ integralClosure P.integers F' := by
    rw [mem_integralClosure_iff,
      isIntegral_iff_forall_restrict_eq_mem_integers_of_finiteDimensional (k' := k') P]
    exact fun P' hP' ↦ y.2 ⟨P', hP'⟩
  exact ⟨1 ⊗ₜ ⟨y.1, hy⟩, funext fun Q ↦ Subtype.ext (by simp)⟩

end Surjective

section Equivalence

variable [FiniteDimensional F F'] [Algebra.IsSeparable F F'] [Algebra.IsIntegral k k'] (k' F')

attribute [local instance] Fintype.ofFinite in
/-- For a finite separable extension `F' / F` and an integral constant extension `k' / k`,
`semilocalHom k' F' P` is injective. -/
theorem semilocalHom_injective (P : Place k F) :
    Function.Injective (semilocalHom k' F' P) := by
  -- A surjective `F̂_P`-linear map between vector spaces of equal finite dimension `[F' : F]` is
  -- injective.
  have hdim : finrank P.Completion (P.Completion ⊗[F] F') =
      finrank P.Completion
        (∀ Q : {P' : Place k' F' // P'.restrict k F = P}, Q.1.Completion) := by
    rw [Module.finrank_baseChange, Module.finrank_pi_fintype, ← finsum_eq_sum_of_fintype]
    exact (finsum_finrank_completion_eq_finrank_of_isSeparable k' F' P).symm
  exact (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
    (f := (semilocalHom k' F' P).toLinearMap) hdim).mpr (semilocalHom_surjective k' F' P)

/-- **The field semilocal decomposition**: `F̂_P ⊗[F] F' ≃ₐ[F̂_P] ∏_{P' ∣ P} F̂'_{P'}`. -/
noncomputable def semilocalEquiv (P : Place k F) :
    P.Completion ⊗[F] F' ≃ₐ[P.Completion]
      (∀ Q : {P' : Place k' F' // P'.restrict k F = P}, Q.1.Completion) :=
  AlgEquiv.ofBijective (semilocalHom k' F' P)
    -- `Function.Bijective` is semireducible; `show` keeps the proof typed at `Function.Bijective`
    -- rather than its unfolded conjunction so `AlgEquiv.ofBijective_apply` rewrites cleanly.
    (show Function.Bijective (semilocalHom k' F' P) from
      ⟨semilocalHom_injective k' F' P, semilocalHom_surjective k' F' P⟩)

/-- As a function, `semilocalEquiv` agrees with `semilocalHom`. -/
theorem coe_semilocalEquiv (P : Place k F) :
    ⇑(semilocalEquiv k' F' P) = ⇑(semilocalHom k' F' P) :=
  funext fun _ ↦ by rw [semilocalEquiv, AlgEquiv.ofBijective_apply]

variable {k' F'} in
@[simp]
theorem semilocalEquiv_tmul (P : Place k F) (a : P.Completion) (x : F')
    (Q : {P' : Place k' F' // P'.restrict k F = P}) :
    semilocalEquiv k' F' P (a ⊗ₜ x) Q =
      P.completionExtension Q.1 Q.2 a * Q.1.completionEmbedding x := by
  rw [semilocalEquiv, AlgEquiv.ofBijective_apply, semilocalHom_tmul]

variable {k' F'} in
@[simp]
theorem semilocalEquiv_symm_completionEmbedding (P : Place k F) (x : F') :
    (semilocalEquiv k' F' P).symm (fun Q ↦ Q.1.completionEmbedding x) = 1 ⊗ₜ x := by
  rw [AlgEquiv.symm_apply_eq]; funext Q; simp

/-- For a finite separable extension `F' / F` and an integral constant extension `k' / k`,
`integralSemilocalHom k' F' P` is injective. -/
theorem integralSemilocalHom_injective (P : Place k F) :
    Function.Injective (integralSemilocalHom k' F' P) := by
  intro x y hxy
  apply integralSemilocalToField_injective F' P
  apply (semilocalEquiv k' F' P).injective
  rw [semilocalEquiv, AlgEquiv.ofBijective_apply, AlgEquiv.ofBijective_apply,
    integralSemilocalHom_fieldCompatibility, integralSemilocalHom_fieldCompatibility, hxy]

/-- **The integral semilocal decomposition**: `𝒪̂_P ⊗[𝒪_P] 𝒪'_P ≃ₐ[𝒪̂_P] ∏_{P' ∣ P} 𝒪̂_{P'}`. -/
noncomputable def integralSemilocalEquiv (P : Place k F) :
    P.completionPlace.integers ⊗[P.integers] integralClosure P.integers F' ≃ₐ[
      P.completionPlace.integers]
      (∀ Q : {P' : Place k' F' // P'.restrict k F = P}, Q.1.completionPlace.integers) :=
  AlgEquiv.ofBijective (integralSemilocalHom k' F' P)
    -- Keep the proof typed at `Function.Bijective` so `AlgEquiv.ofBijective_apply` rewrites it.
    (show Function.Bijective (integralSemilocalHom k' F' P) from
      ⟨integralSemilocalHom_injective k' F' P, integralSemilocalHom_surjective k' F' P⟩)

/-- As a function, `integralSemilocalEquiv` agrees with `integralSemilocalHom`. -/
theorem coe_integralSemilocalEquiv (P : Place k F) :
    ⇑(integralSemilocalEquiv k' F' P) = ⇑(integralSemilocalHom k' F' P) :=
  funext fun _ ↦ by rw [integralSemilocalEquiv, AlgEquiv.ofBijective_apply]

variable {k' F'} in
@[simp]
theorem integralSemilocalEquiv_tmul (P : Place k F) (a : P.completionPlace.integers)
    (x : integralClosure P.integers F') (Q : {P' : Place k' F' // P'.restrict k F = P}) :
    integralSemilocalEquiv k' F' P (a ⊗ₜ x) Q =
      P.completionIntegersExtension Q.1 Q.2 a *
        P.integralClosureToCompletionIntegers Q.1 Q.2 x := by
  rw [integralSemilocalEquiv, AlgEquiv.ofBijective_apply, integralSemilocalHom_tmul]

variable {k' F'} in
@[simp]
theorem integralSemilocalEquiv_symm_integralClosureToCompletionIntegers
    (P : Place k F) (x : integralClosure P.integers F') :
    (integralSemilocalEquiv k' F' P).symm
        (fun Q ↦ P.integralClosureToCompletionIntegers Q.1 Q.2 x) = 1 ⊗ₜ x := by
  rw [AlgEquiv.symm_apply_eq]; funext Q; simp

variable {k' F'} in
/-- After inclusion into the completions, `integralSemilocalEquiv` agrees with `semilocalEquiv`. -/
theorem integralSemilocalEquiv_fieldCompatibility (P : Place k F)
    (z : P.completionPlace.integers ⊗[P.integers] integralClosure P.integers F') :
    semilocalEquiv k' F' P (integralSemilocalToField F' P z) =
      fun Q ↦ (integralSemilocalEquiv k' F' P z Q : Q.1.Completion) := by
  rw [coe_semilocalEquiv, coe_integralSemilocalEquiv, integralSemilocalHom_fieldCompatibility]

variable {k' F'} in
/-- Transporting an integral tuple along `(integralSemilocalEquiv k' F' P).symm` and including into
`F̂_P ⊗[F] F'` agrees with `(semilocalEquiv k' F' P).symm` of the coerced tuple. -/
@[simp]
theorem integralSemilocalToField_integralSemilocalEquiv_symm (P : Place k F)
    (y : ∀ Q : {P' : Place k' F' // P'.restrict k F = P}, Q.1.completionPlace.integers) :
    integralSemilocalToField F' P ((integralSemilocalEquiv k' F' P).symm y) =
      (semilocalEquiv k' F' P).symm (fun Q ↦ (y Q : Q.1.Completion)) := by
  rw [AlgEquiv.eq_symm_apply, integralSemilocalEquiv_fieldCompatibility, AlgEquiv.apply_symm_apply]

/-! ### Norm and trace in the semilocal decomposition -/

attribute [local instance] Fintype.ofFinite in
/-- The trace of `F̂_P ⊗[F] F'` over `F̂_P` is the sum of the traces of its completed components. -/
theorem trace_eq_sum_trace_semilocalEquiv (P : Place k F) (ξ : P.Completion ⊗[F] F') :
    Algebra.trace P.Completion (P.Completion ⊗[F] F') ξ =
      ∑ Q : {P' : Place k' F' // P'.restrict k F = P},
        Algebra.trace P.Completion Q.1.Completion (semilocalEquiv k' F' P ξ Q) := by
  rw [← Algebra.trace_eq_of_algEquiv (semilocalEquiv k' F' P)]
  exact Algebra.trace_pi _

variable {k' F'} in
attribute [local instance] Fintype.ofFinite in
/-- An element of `F̂'_Q`, placed in the `Q`-component of `F̂_P ⊗[F] F'`, has the same trace
pairing with an element of `F'` as inside `F̂'_Q`. -/
theorem trace_semilocalEquiv_symm_single_mul (P : Place k F)
    [DecidableEq {P' : Place k' F' // P'.restrict k F = P}]
    (Q : {P' : Place k' F' // P'.restrict k F = P}) (z : Q.1.Completion) (x : F') :
    Algebra.trace P.Completion (P.Completion ⊗[F] F')
        ((semilocalEquiv k' F' P).symm (Pi.single Q z) * (1 ⊗ₜ x)) =
      Algebra.trace P.Completion Q.1.Completion (z * Q.1.completionEmbedding x) := by
  rw [trace_eq_sum_trace_semilocalEquiv k' F' P, Finset.sum_eq_single Q]
  · simp [semilocalEquiv_tmul]
  · exact fun Q' _ hQ' ↦ by simp [Pi.single_eq_of_ne hQ']
  · simp

attribute [local instance] Fintype.ofFinite in
/-- The norm of `F̂_P ⊗[F] F'` over `F̂_P` is the product of the norms of its completed
components. -/
theorem norm_eq_prod_norm_semilocalEquiv (P : Place k F) (ξ : P.Completion ⊗[F] F') :
    Algebra.norm P.Completion ξ =
      ∏ Q : {P' : Place k' F' // P'.restrict k F = P},
        Algebra.norm P.Completion (semilocalEquiv k' F' P ξ Q) := by
  rw [← Algebra.norm_eq_of_algEquiv (semilocalEquiv k' F' P)]
  exact Algebra.norm_pi _

variable {F'} in
attribute [local instance] Fintype.ofFinite in
/-- **Local-global norm formula**: the norm of an element of `F'` is the product of its completed
local norms at the places above `P`. -/
theorem completionEmbedding_norm_eq_prod_norm (P : Place k F) (x : F') :
    P.completionEmbedding (Algebra.norm F x) =
      ∏ Q : {P' : Place k' F' // P'.restrict k F = P},
        Algebra.norm P.Completion (Q.1.completionEmbedding x) := by
  rw [← algebraMap_completion_eq_completionEmbedding,
    ← Algebra.norm_baseChange_tmul (A := P.Completion) (B := F') x,
    norm_eq_prod_norm_semilocalEquiv k' F' P]
  exact Finset.prod_congr rfl fun Q _ ↦ by simp [semilocalEquiv_tmul]

end Equivalence

section SinglePlaceTrace

variable [FiniteDimensional F F'] [Algebra.IsSeparable F F']

/-- **Trace-dual expansions pass to completions.** If `x = ∑ᵢ Tr_{F'/F}(x bᵢ) • yᵢ` for every
`x ∈ F'`, then the same expansion holds in `F̂'_{P'}` over `F̂_P` after applying
`P'.completionEmbedding`, without assuming `k' / k` is integral. -/
theorem sum_trace_mul_smul_completionEmbedding_eq
    (P : Place k F) (P' : Place k' F') (hP : P'.restrict k F = P)
    {ι : Type*} [Fintype ι] (b y : ι → F')
    (h : ∀ x : F', ∑ i, Algebra.trace F F' (x * b i) • y i = x) (z : P'.Completion) :
    letI := P.completionExtensionAlgebra P' hP
    ∑ i, Algebra.trace P.Completion P'.Completion (z * P'.completionEmbedding (b i)) •
        P'.completionEmbedding (y i) = z := by
  classical
  set Q₀ : {Q : Place k F' // Q.restrict k F = P} :=
    ⟨P'.restrictConstants k, (restrict_restrictConstants k F P').trans hP⟩
  have h' := congrArg (fun ξ ↦ semilocalEquiv k F' P ξ Q₀)
    (TauCeti.Algebra.sum_trace_mul_smul_baseChange_eq (A := P.Completion) b y h
      ((semilocalEquiv k F' P).symm (Pi.single Q₀ z)))
  simp only [AlgEquiv.apply_symm_apply, Pi.single_eq_same, map_sum, map_smul,
    Finset.sum_apply, Pi.smul_apply, semilocalEquiv_tmul, map_one, one_mul,
    trace_semilocalEquiv_symm_single_mul] at h'
  rw [← P.completionExtensionAlgebra_restrictConstants P' hP]
  simpa only [Q₀, fiberCompletionAlgebra, completionEmbedding_restrictConstants] using h'

end SinglePlaceTrace

end Semilocal

end TauCeti.Place
