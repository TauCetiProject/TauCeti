/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Dimension.OrzechProperty
public import Mathlib.RingTheory.Nakayama
public import TauCeti.FieldTheory.FunctionField.Place.Approximation
public import TauCeti.FieldTheory.FunctionField.Place.Completion.LocalDegree
public import TauCeti.FieldTheory.FunctionField.Place.Extension.Fundamental
public import TauCeti.RingTheory.NormTrace.Pi

/-!
# The completions above a place

Let `F' / F` be a finite extension, `P` a place of `F / k`, and `P'` run over the finitely many
places of `F' / k'` lying over `P`. Each completion `F̂'_{P'}` is a finite extension of the
completion `F̂_P` (`TauCeti.Place.finrank_completion`), and the diagonal map
`F' → ∏_{P' ∣ P} F̂'_{P'}` identifies the scalar extension of `F'` to `F̂_P` with this product:
an `F`-basis of `F'` stays an `F̂_P`-basis of `∏_{P' ∣ P} F̂'_{P'}`. This is the semilocal
decomposition `F̂_P ⊗_F F' ≅ ∏_{P' ∣ P} F̂'_{P'}`, stated here through bases, since `F̂_P` is not
given an `F`-algebra structure. Its two halves are:

* **Spanning.** The functions of `F'` regular at every place over `P` span
  `∏_{P' ∣ P} 𝒪̂_{P'}` over `𝒪̂_P`. By weak approximation, every family of completed functions
  agrees with a single function of `F'` to order `e(P' ∣ P)` at each `P'`, that is, modulo a
  uniformizer of `P`; since `∏_{P' ∣ P} 𝒪̂_{P'}` is a finite `𝒪̂_P`-module, Nakayama's lemma
  turns this into an exact expansion. Approximating to order `0` reduces the completed fields
  to the completed valuation rings, so `F'` spans `∏_{P' ∣ P} F̂'_{P'}` over `F̂_P`. Neither
  statement needs separability.
* **Dimension.** The local degrees are `e(P' ∣ P) f(P' ∣ P)`, so their sum over `P' ∣ P` is
  `[F' : F]` by the fundamental identity, which is where separability of `F' / F` enters. A
  spanning family of `[F' : F]` vectors is a basis.

Reading the matrix of multiplication by `x ∈ F'` in such a basis gives the **trace formula**
`Tr_{F'/F} x = ∑_{P' ∣ P} Tr_{F̂'_{P'}/F̂_P} x`, which relates the global trace pairing, and so the
complementary module of `F' / F` at `P`, to the trace pairings of the completed extensions. No
hypothesis on the residue fields is needed.

The product `∏_{P' ∣ P} F̂'_{P'}` is indexed by the subtype of places over `P`, each carrying its
proof that it lies over `P`, and is an `F̂_P`-algebra through the family of explicit algebra
structures `TauCeti.Place.completionExtensionAlgebra`, installed locally in each statement.

This follows the number-field semilocal decomposition `TauCeti.semilocalEquiv` and its trace
formula `TauCeti.algebraMap_trace_eq_sum_trace`, with weak approximation and Nakayama's lemma
over the completed valuation ring in place of density of `L` in `∏_{w ∣ v} L_w`.

## Main results

* `TauCeti.Place.exists_forall_sub_completionEmbedding_mem_filtration`: weak approximation in
  the completions at finitely many distinct places.
* `TauCeti.Place.span_completionIntegers_pi_eq_top`: the functions regular above `P` span
  `∏_{P' ∣ P} 𝒪̂_{P'}` over `𝒪̂_P`.
* `TauCeti.Place.span_completion_pi_eq_top` and
  `TauCeti.Place.span_completionEmbedding_basis_eq_top`: `F'`, and so any `F`-basis of `F'`, spans
  `∏_{P' ∣ P} F̂'_{P'}` over `F̂_P`.
* `TauCeti.Place.finsum_finrank_completion_eq_finrank`: the local degrees above `P` add up to
  `[F' : F]`.
* `TauCeti.Place.linearIndependent_completionEmbedding_pi`: an `F`-basis of `F'` is linearly
  independent over `F̂_P` in `∏_{P' ∣ P} F̂'_{P'}`.
* `TauCeti.Place.completionEmbedding_trace`: **the trace formula**
  `Tr_{F'/F} x = ∑_{P' ∣ P} Tr_{F̂'_{P'}/F̂_P} x`.

## References

* H. Stichtenoth, *Algebraic Function Fields and Codes*, 2nd ed., GTM 254, Springer, 2009,
  Section IV.2.
* J.-P. Serre, *Local Fields*, GTM 67, Springer, 1979, Chapter II, §3.
* J. Neukirch, *Algebraic Number Theory*, Chapter II, Proposition (8.3).
-/

public section

open IsLocalRing Module

namespace TauCeti.Place

section Approximation

variable {k F : Type*} [Field k] [Field F] [Algebra k F]

/-- **Weak approximation in the completions.** Given finitely many distinct places `P i`,
completed functions `x i` at them and prescribed orders `b i`, a single function `y` of `F`
agrees with every `x i` to order `b i` at `P i`. -/
theorem exists_forall_sub_completionEmbedding_mem_filtration {ι : Type*} [Finite ι]
    {P : ι → Place k F} (hP : Function.Injective P) (x : ∀ i, (P i).Completion) (b : ι → ℤ) :
    ∃ y : F, ∀ i, x i - (P i).completionEmbedding y ∈ (P i).completionPlace.filtration (b i) := by
  choose z hz using fun i ↦ (P i).exists_sub_completionEmbedding_mem_filtration (x i) (b i)
  obtain ⟨y, hy⟩ := exists_forall_ord_sub_eq hP z b
  refine ⟨y, fun i ↦ ?_⟩
  have h : (P i).completionEmbedding (y - z i) ∈ (P i).completionPlace.filtration (b i) := by
    rw [completionEmbedding_mem_filtration_iff]
    rcases eq_or_ne (y - z i) 0 with h | h
    · rw [h]
      exact zero_mem _
    · exact ((P i).mem_filtration_iff_le_ord h).mpr (hy i).ge
  have := sub_mem (hz i) h
  rwa [map_sub, sub_sub_sub_cancel_right] at this

end Approximation

section Semilocal

variable {k k' F F' : Type*} [Field k] [Field k'] [Field F] [Field F']
  [Algebra k F] [Algebra k k'] [Algebra k' F'] [Algebra k F'] [Algebra F F']
  [IsScalarTower k k' F'] [IsScalarTower k F F'] [FiniteDimensional F F'] (P : Place k F)

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
  let ι := {P' : Place k' F' // P'.restrict k F = P}
  let _ := fun P' : ι ↦ P.completionIntegersExtensionAlgebra P'.1 P'.2
  have _ := fun P' : ι ↦ moduleFinite_completionIntegers P P'.1 P'.2
  -- A uniformizer `πc` of the completed valuation ring of `P`.
  obtain ⟨π, hπ0, hπ⟩ := P.exists_ne_zero_ord_eq 1
  have hπint : π ∈ P.integers := by rw [mem_integers_iff_ord_nonneg, hπ]; norm_num
  set πc := P.completionIntegersEmbedding ⟨π, hπint⟩
  have hπc0 : (πc : P.Completion) ≠ 0 := by simpa [πc] using hπ0
  have hπm : πc ∈ maximalIdeal P.completionPlace.integers := by
    rw [P.completionPlace.mem_maximalIdeal_iff_ord_pos hπc0]
    simp [πc, hπ]
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
  -- The error is `πc` times a family of completed integers.
  have hE0 (P' : ι) : P.completionExtension P'.1 P'.2 πc ≠ 0 := (map_ne_zero _).mpr hπc0
  have hw (P' : ι) : ((m P' : P'.1.Completion) - P'.1.completionEmbedding y) /
      P.completionExtension P'.1 P'.2 πc ∈ P'.1.completionPlace.integers := by
    rcases eq_or_ne ((m P' : P'.1.Completion) - P'.1.completionEmbedding y) 0 with h | h
    · simp [h]
    have hord : P'.1.completionPlace.ord (P.completionExtension P'.1 P'.2 πc) =
        ramificationIdx F P'.1 := by
      simp only [πc, completionIntegersEmbedding_apply, ord_completionExtension,
        ord_completionEmbedding, hπ, mul_one]
    rw [mem_integers_iff_ord_nonneg, P'.1.completionPlace.ord_div h (hE0 P'), hord]
    have := (P'.1.completionPlace.mem_filtration_iff_le_ord h).mp (hy P')
    linarith
  have hm : m = (fun P' : ι ↦ P'.1.completionIntegersEmbedding ⟨y, hyint P'⟩) +
      πc • fun P' : ι ↦ (⟨_, hw P'⟩ : P'.1.completionPlace.integers) := by
    funext P'
    apply Subtype.ext
    rw [Pi.add_apply, Pi.smul_apply, Algebra.smul_def, Subring.coe_add, Subring.coe_mul,
      coe_algebraMap_completionIntegersExtensionAlgebra, mul_div_cancel₀ _ (hE0 P'),
      completionIntegersEmbedding_apply, add_sub_cancel]
  rw [hm]
  exact Submodule.add_mem_sup (Submodule.subset_span ⟨⟨y, hyint⟩, rfl⟩)
    (Submodule.smul_mem_smul hπm Submodule.mem_top)

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
  let toV : (∀ P' : ι, P'.1.completionPlace.integers) → ∀ P' : ι, P'.1.Completion :=
    fun m P' ↦ m P'
  have hint (m : ∀ P' : ι, P'.1.completionPlace.integers) : toV m ∈ W := by
    have hm : m ∈ Submodule.span P.completionPlace.integers _ :=
      (span_completionIntegers_pi_eq_top (k' := k') (F' := F') P).symm ▸ Submodule.mem_top
    induction hm using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨y, rfl⟩ := hx
      exact Submodule.subset_span ⟨y.1, funext fun P' ↦ by simp [toV]⟩
    | zero => exact W.zero_mem
    | add x z _ _ hx hz => exact W.add_mem hx hz
    | smul a x _ hx =>
      convert W.smul_mem (a : P.Completion) hx using 1
      funext P'
      simp only [toV, Pi.smul_apply]
      rw [Algebra.smul_def, Algebra.smul_def, Subring.coe_mul,
        coe_algebraMap_completionIntegersExtensionAlgebra, algebraMap_completionExtensionAlgebra]
  refine eq_top_iff.mpr fun z _ ↦ ?_
  -- Subtracting a function of `F'` leaves a family of completed integers.
  obtain ⟨y, hy⟩ := exists_forall_sub_completionEmbedding_mem_filtration
    (P := fun P' : ι ↦ P'.1) Subtype.val_injective z (fun _ ↦ 0)
  have h := W.add_mem (Submodule.subset_span ⟨y, rfl⟩)
    (hint fun P' ↦ ⟨_, P'.1.completionPlace.mem_filtration_zero_iff.mp (hy P')⟩)
  convert h using 1
  funext P'
  simp [toV]

/-- The diagonal image of an `F`-basis of `F'` spans `∏_{P' ∣ P} F̂'_{P'}` over `F̂_P`. -/
theorem span_completionEmbedding_basis_eq_top {ι' : Type*} (b : Basis ι' F F') :
    letI := fun P' : {P' : Place k' F' // P'.restrict k F = P} ↦
      P.completionExtensionAlgebra P'.1 P'.2
    Submodule.span P.Completion
      (Set.range fun (i : ι') (P' : {P' : Place k' F' // P'.restrict k F = P}) ↦
        P'.1.completionEmbedding (b i)) = ⊤ := by
  let ι := {P' : Place k' F' // P'.restrict k F = P}
  let _ := fun P' : ι ↦ P.completionExtensionAlgebra P'.1 P'.2
  refine eq_top_iff.mpr ((span_completion_pi_eq_top P).symm.le.trans (Submodule.span_le.mpr ?_))
  rintro _ ⟨y, rfl⟩
  have hy : (fun P' : {P' : Place k' F' // P'.restrict k F = P} ↦ P'.1.completionEmbedding y) =
      (b.repr y).sum fun i c ↦ P.completionEmbedding c • fun P' : ι ↦
        P'.1.completionEmbedding (b i) := by
    funext P'
    conv_lhs => rw [← b.linearCombination_repr y, Finsupp.linearCombination_apply]
    simp only [Finsupp.sum, map_sum, Finset.sum_apply, Pi.smul_apply,
      completionEmbedding_smul P P'.1 P'.2]
  rw [SetLike.mem_coe]
  beta_reduce
  rw [hy]
  exact Submodule.finsuppSum_mem _ _ _ _ fun i _ ↦
    Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)

/-- **The local degrees above `P` add up to the global degree**:
`∑_{P' ∣ P} [F̂'_{P'} : F̂_P] = [F' : F]` for a finite separable extension `F' / F`. Each local
degree is `e(P' ∣ P) f(P' ∣ P)`, and those add up to `[F' : F]` by the fundamental identity. -/
theorem finsum_finrank_completion_eq_finrank [Algebra.IsIntegral k k']
    [Algebra.IsSeparable F F'] :
    ∑ᶠ P' : {P' : Place k' F' // P'.restrict k F = P},
        (letI := P.completionExtensionAlgebra P'.1 P'.2
        finrank P.Completion P'.1.Completion) = finrank F F' := by
  have hfin := finite_setOf_restrict_eq (k' := k') (F' := F') k F P
  have := Fintype.ofFinite {P' : Place k' F' // P'.restrict k F = P}
  rw [finsum_eq_sum_of_fintype,
    ← sum_ramificationIdx_mul_relativeDegree_eq_finrank_of_isSeparable k F P
      (s := hfin.toFinset) fun _ ↦ hfin.mem_toFinset,
    Finset.sum_subtype hfin.toFinset fun _ ↦ hfin.mem_toFinset]
  exact Finset.sum_congr rfl fun P' _ ↦ finrank_completion P P'.1 P'.2

/-- **An `F`-basis of `F'` stays linearly independent over the completion at `P`** in
`∏_{P' ∣ P} F̂'_{P'}`, for a finite separable extension `F' / F`. Together with
`TauCeti.Place.span_completion_pi_eq_top`, its diagonal image is an `F̂_P`-basis: this is the
semilocal decomposition `F̂_P ⊗_F F' ≅ ∏_{P' ∣ P} F̂'_{P'}`. -/
theorem linearIndependent_completionEmbedding_pi [Algebra.IsIntegral k k']
    [Algebra.IsSeparable F F'] {ι' : Type*} (b : Basis ι' F F') :
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
    (span_completionEmbedding_basis_eq_top P b).ge ?_
  rw [← finrank_eq_card_basis b, finrank_pi_fintype,
    ← finsum_finrank_completion_eq_finrank (k' := k') P, finsum_eq_sum_of_fintype]

/-- **The trace formula**: for a finite separable extension `F' / F` and a place `P` of `F`, the
trace of `x ∈ F'` over `F` is, in the completion at `P`, the sum of the traces of `x` over the
completions `F̂'_{P'} / F̂_P` at the places `P'` above `P`. -/
theorem completionEmbedding_trace [Algebra.IsIntegral k k'] [Algebra.IsSeparable F F']
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
    .mk (linearIndependent_completionEmbedding_pi (k' := k') P b)
      (span_completionEmbedding_basis_eq_top P b).ge
  have hrepr (y : F') (i) :
      B.repr (fun P' : ι ↦ P'.1.completionEmbedding y) i = P.completionEmbedding (b.repr y i) := by
    have hy : (fun P' : ι ↦ P'.1.completionEmbedding y) =
        ∑ j, P.completionEmbedding (b.repr y j) • B j := by
      funext P'
      conv_lhs => rw [← b.sum_repr y]
      simp only [B, Basis.coe_mk, map_sum, Finset.sum_apply, Pi.smul_apply,
        completionEmbedding_smul P P'.1 P'.2]
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

end Semilocal

end TauCeti.Place
