/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.SetTheory.Cardinal.Continuum
public import TauCeti.Analysis.InnerProductSpace.HilbertBasis.Basic
public import TauCeti.Analysis.InnerProductSpace.HilbertBasis.Reindex
public import TauCeti.Analysis.InnerProductSpace.Orthonormal.Countable
import Mathlib.Analysis.Real.Cardinality
import TauCeti.Analysis.Normed.Lp.Support

/-!
# Hilbert dimension and the unitary classification of Hilbert spaces

Any two Hilbert bases `b : HilbertBasis ι 𝕜 H` and `c : HilbertBasis κ 𝕜 H` of the same
inner-product space `H` over `𝕜` (`ℝ` or `ℂ`) have equinumerous index types
(`HilbertBasis.mk_eq`, `HilbertBasis.lift_mk_eq`):

* If `κ` is finite, `H` is finite-dimensional (`HilbertBasis.finite_iff_finiteDimensional`) and
  both index types have cardinality `Module.finrank 𝕜 H` (`HilbertBasis.card_eq_finrank`).
* If `κ` is infinite, so is `ι`. For each `j : κ`, the coordinate sequence `b.repr (c j)` lies in
  `ℓ²(ι, 𝕜)` and therefore has countable support `S j = {i | ⟪b i, c j⟫ ≠ 0}`
  (`lp.countable_dsupport`). Every `i : ι` lies in some `S j`, since a unit vector `b i` cannot be
  orthogonal to all of `c`; hence `#ι ≤ ∑ j, #(S j) ≤ #κ * ℵ₀ = #κ`, and symmetry gives `#ι = #κ`.

Combining basis-cardinality invariance with `HilbertBasis.equiv` and `HilbertBasis.mapₗᵢ` yields
the **unitary classification of Hilbert spaces**
(`HilbertBasis.nonempty_linearIsometryEquiv_iff_lift_mk_eq`,
`TauCeti.nonempty_linearIsometryEquiv_iff_lift_hilbertDimension_eq`): two Hilbert spaces over `𝕜`
are linearly isometrically equivalent if and only if they have the same Hilbert dimension
`TauCeti.hilbertDimension 𝕜 H`, defined as the cardinality of any Hilbert basis of `H`.

Separability corresponds to countable Hilbert dimension, `hilbertDimension 𝕜 H ≤ ℵ₀`
(`TauCeti.separableSpace_iff_hilbertDimension_le_aleph0`), and separable infinite-dimensional
Hilbert spaces are precisely those unitarily equivalent to `ℓ²(ℕ, 𝕜)`
(`TauCeti.nonempty_linearIsometryEquiv_lp_nat_iff`). Separability alone does not classify finite
dimensions (`𝕜` and `𝕜²` have Hilbert dimensions `1` and `2`), whereas `ℓ²(ℕ, 𝕜)` and `ℓ²(ℤ, 𝕜)`
both have Hilbert dimension `ℵ₀` and are unitarily equivalent, while `ℓ²(ℕ, 𝕜)` and `ℓ²(ℝ, 𝕜)`
have Hilbert dimensions `ℵ₀` and `𝔠` and are not.

## References

* J. B. Conway, *A Course in Functional Analysis*, 2nd ed., Theorems I.4.17 and I.4.19.
* M. Reed and B. Simon, *Methods of Modern Mathematical Physics I: Functional Analysis*, §II.2.
* P. R. Halmos, *A Hilbert Space Problem Book*, 2nd ed., Problem 9.
-/

public section

universe u v w

open scoped Cardinal InnerProductSpace lp

namespace HilbertBasis

variable {𝕜 : Type*} [RCLike 𝕜]
  {H : Type*} [NormedAddCommGroup H] [InnerProductSpace 𝕜 H]
  {K : Type*} [NormedAddCommGroup K] [InnerProductSpace 𝕜 K]

/-- A finite Hilbert basis has cardinality equal to `Module.finrank 𝕜 H`. -/
theorem card_eq_finrank {ι : Type*} [Fintype ι] (b : HilbertBasis ι 𝕜 H) :
    Fintype.card ι = Module.finrank 𝕜 H :=
  (Module.finrank_eq_card_basis b.toOrthonormalBasis.toBasis).symm

/-- An inner-product space admitting a Hilbert basis over a finite index type is
finite-dimensional. -/
theorem finiteDimensional_of_finite {ι : Type*} [Finite ι] (b : HilbertBasis ι 𝕜 H) :
    FiniteDimensional 𝕜 H := by
  cases nonempty_fintype ι
  exact Module.Finite.of_basis b.toOrthonormalBasis.toBasis

/-- The index type of a Hilbert basis of `H` is finite if and only if `H` is finite-dimensional. -/
theorem finite_iff_finiteDimensional {ι : Type*} (b : HilbertBasis ι 𝕜 H) :
    Finite ι ↔ FiniteDimensional 𝕜 H :=
  ⟨fun _ ↦ b.finiteDimensional_of_finite, fun _ ↦ b.orthonormal.linearIndependent.finite⟩

/-- The index type of a Hilbert basis of `H` is infinite if and only if `H` is
infinite-dimensional. -/
theorem infinite_iff {ι : Type*} (b : HilbertBasis ι 𝕜 H) :
    Infinite ι ↔ ¬ FiniteDimensional 𝕜 H := by
  rw [← not_finite_iff_infinite, b.finite_iff_finiteDimensional]

/-- `H` is trivial if and only if the index type of a Hilbert basis of `H` is empty. -/
theorem subsingleton_iff_isEmpty {ι : Type*} (b : HilbertBasis ι 𝕜 H) :
    Subsingleton H ↔ IsEmpty ι :=
  ⟨fun _ ↦ ⟨fun i ↦ b.orthonormal.ne_zero i (Subsingleton.elim _ _)⟩,
    fun _ ↦ b.repr.injective.subsingleton⟩

/-- `H` is nontrivial if and only if the index type of a Hilbert basis of `H` is nonempty. -/
theorem nontrivial_iff_nonempty {ι : Type*} (b : HilbertBasis ι 𝕜 H) :
    Nontrivial H ↔ Nonempty ι := by
  rw [← not_subsingleton_iff_nontrivial, b.subsingleton_iff_isEmpty, not_isEmpty_iff]

/-- Auxiliary bound for `HilbertBasis.mk_eq`: if `κ` is infinite in the same universe as `ι`, then
`#ι ≤ #κ`, because each `c j` has countable `b`-support and these supports cover `ι`. -/
private theorem mk_le_of_infinite {ι κ : Type w} [Infinite κ] (b : HilbertBasis ι 𝕜 H)
    (c : HilbertBasis κ 𝕜 H) : #ι ≤ #κ := by
  let S : κ → Set ι := fun j ↦ {i : ι | b.repr (c j) i ≠ 0}
  have hcover : (Set.univ : Set ι) ⊆ ⋃ j : κ, S j := by
    intro i _
    by_contra hi
    simp only [Set.mem_iUnion, S, Set.mem_ofPred_eq, not_exists, not_not] at hi
    have hzero : c.repr (b i) = 0 := by
      ext j
      rw [lp.coeFn_zero, Pi.zero_apply, c.repr_apply_apply, ← inner_conj_symm,
        ← b.repr_apply_apply, hi j, map_zero]
    exact b.orthonormal.ne_zero i (c.repr.map_eq_zero_iff.1 hzero)
  calc #ι = #(Set.univ : Set ι) := Cardinal.mk_univ.symm
    _ ≤ #(⋃ j : κ, S j) := Cardinal.mk_le_mk_of_subset hcover
    _ ≤ Cardinal.sum fun j : κ ↦ #(S j) := Cardinal.mk_iUnion_le_sum_mk
    _ ≤ Cardinal.sum fun _ : κ ↦ ℵ₀ := Cardinal.sum_le_sum _ _ fun j ↦ by
          have := (lp.countable_dsupport (b.repr (c j)) (by simp)).to_subtype
          exact Cardinal.mk_le_aleph0
    _ = #κ * ℵ₀ := by simp
    _ = #κ := Cardinal.mul_aleph0_eq (Cardinal.aleph0_le_mk κ)

/-- **Basis-cardinality invariance (same universe).** Any two Hilbert bases of `H` indexed by types
in the same universe have equal cardinalities. -/
theorem mk_eq {ι κ : Type w} (b : HilbertBasis ι 𝕜 H) (c : HilbertBasis κ 𝕜 H) :
    #ι = #κ := by
  rcases finite_or_infinite κ with hfin | hinf
  · have : FiniteDimensional 𝕜 H := c.finiteDimensional_of_finite
    have : Finite ι := b.finite_iff_finiteDimensional.2 ‹_›
    cases nonempty_fintype ι
    cases nonempty_fintype κ
    simp [Cardinal.mk_fintype, b.card_eq_finrank, c.card_eq_finrank]
  · have : Infinite ι := b.infinite_iff.2 (c.infinite_iff.1 hinf)
    exact le_antisymm (b.mk_le_of_infinite c) (c.mk_le_of_infinite b)

/-- **Basis-cardinality invariance.** Any two Hilbert bases of `H`, across arbitrary index
universes, have equal lifted cardinalities. -/
theorem lift_mk_eq {ι : Type u} {κ : Type v} (b : HilbertBasis ι 𝕜 H) (c : HilbertBasis κ 𝕜 H) :
    Cardinal.lift.{v} #ι = Cardinal.lift.{u} #κ := by
  simpa only [Cardinal.mk_uLift] using
    (b.reindex Equiv.ulift.{v, u}.symm).mk_eq (c.reindex Equiv.ulift.{u, v}.symm)

/-- Any two Hilbert bases of `H` have equinumerous index types. -/
theorem nonempty_equiv {ι : Type u} {κ : Type v} (b : HilbertBasis ι 𝕜 H)
    (c : HilbertBasis κ 𝕜 H) : Nonempty (ι ≃ κ) :=
  Cardinal.lift_mk_eq'.1 (b.lift_mk_eq c)

/-- **Unitary classification of Hilbert spaces via Hilbert bases.** Two spaces carrying Hilbert
bases `b : HilbertBasis ι 𝕜 H` and `c : HilbertBasis κ 𝕜 K` are linearly isometrically equivalent
if and only if `ι` and `κ` have the same lifted cardinality. -/
theorem nonempty_linearIsometryEquiv_iff_lift_mk_eq {ι : Type u} {κ : Type v}
    (b : HilbertBasis ι 𝕜 H) (c : HilbertBasis κ 𝕜 K) :
    Nonempty (H ≃ₗᵢ[𝕜] K) ↔ Cardinal.lift.{v} #ι = Cardinal.lift.{u} #κ :=
  ⟨fun ⟨U⟩ ↦ (b.mapₗᵢ U).lift_mk_eq c,
    fun h ↦ let ⟨e⟩ := Cardinal.lift_mk_eq'.1 h; ⟨b.equiv c e⟩⟩

/-- Same-universe specialization of `HilbertBasis.nonempty_linearIsometryEquiv_iff_lift_mk_eq`. -/
theorem nonempty_linearIsometryEquiv_iff_mk_eq {ι κ : Type w}
    (b : HilbertBasis ι 𝕜 H) (c : HilbertBasis κ 𝕜 K) :
    Nonempty (H ≃ₗᵢ[𝕜] K) ↔ #ι = #κ := by
  simpa using b.nonempty_linearIsometryEquiv_iff_lift_mk_eq c

/-- A space carrying a Hilbert basis `b : HilbertBasis ι 𝕜 H` is separable if and only if the
index type `ι` is countable. -/
theorem separableSpace_iff_countable {ι : Type*} (b : HilbertBasis ι 𝕜 H) :
    TopologicalSpace.SeparableSpace H ↔ Countable ι := by
  refine ⟨fun _ ↦ b.orthonormal.countable_of_separableSpace, fun _ ↦ ?_⟩
  have : TopologicalSpace.SeparableSpace ℓ²(ι, 𝕜) :=
    (lp.separableSpace_iff_countable (G := 𝕜) (p := 2) (by simp)).2 ‹_›
  exact b.repr.symm.surjective.denseRange.separableSpace b.repr.symm.continuous

end HilbertBasis

namespace TauCeti

/-- **Hilbert dimension** of a Hilbert space `H` over `𝕜` (`ℝ` or `ℂ`): the cardinality of any
Hilbert basis of `H`. Unlike the algebraic Hamel rank `Module.rank`, this uses complete orthonormal
bases, so `hilbertDimension 𝕜 ℓ²(ℕ, 𝕜) = ℵ₀`. -/
noncomputable def hilbertDimension (𝕜 : Type*) [RCLike 𝕜] (H : Type u)
    [NormedAddCommGroup H] [InnerProductSpace 𝕜 H] [CompleteSpace H] : Cardinal.{u} :=
  #(exists_hilbertBasis 𝕜 H).choose

end TauCeti

/-- Every Hilbert basis of `H` has lifted cardinality equal to `TauCeti.hilbertDimension 𝕜 H`. -/
theorem HilbertBasis.lift_mk_eq_hilbertDimension {𝕜 : Type*} [RCLike 𝕜] {H : Type u}
    [NormedAddCommGroup H] [InnerProductSpace 𝕜 H] [CompleteSpace H] {ι : Type w}
    (b : HilbertBasis ι 𝕜 H) :
    Cardinal.lift.{u} #ι = Cardinal.lift.{w} (TauCeti.hilbertDimension 𝕜 H) :=
  b.lift_mk_eq (exists_hilbertBasis 𝕜 H).choose_spec.choose

/-- Every Hilbert basis of `H` indexed in the same universe as `H` has cardinality equal to
`TauCeti.hilbertDimension 𝕜 H`. -/
theorem HilbertBasis.mk_eq_hilbertDimension {𝕜 : Type*} [RCLike 𝕜] {H : Type u}
    [NormedAddCommGroup H] [InnerProductSpace 𝕜 H] [CompleteSpace H] {ι : Type u}
    (b : HilbertBasis ι 𝕜 H) :
    #ι = TauCeti.hilbertDimension 𝕜 H :=
  b.mk_eq (exists_hilbertBasis 𝕜 H).choose_spec.choose

/-- A linear isometric equivalence between Hilbert spaces preserves lifted Hilbert dimension. -/
theorem LinearIsometryEquiv.lift_hilbertDimension_eq {𝕜 : Type*} [RCLike 𝕜]
    {H : Type u} {K : Type v}
    [NormedAddCommGroup H] [InnerProductSpace 𝕜 H] [CompleteSpace H]
    [NormedAddCommGroup K] [InnerProductSpace 𝕜 K] [CompleteSpace K]
    (U : H ≃ₗᵢ[𝕜] K) :
    Cardinal.lift.{v} (TauCeti.hilbertDimension 𝕜 H) =
      Cardinal.lift.{u} (TauCeti.hilbertDimension 𝕜 K) := by
  obtain ⟨s, b, -⟩ := exists_hilbertBasis 𝕜 H
  rw [← b.mk_eq_hilbertDimension]
  exact (b.mapₗᵢ U).lift_mk_eq_hilbertDimension

/-- Same-universe specialization of `LinearIsometryEquiv.lift_hilbertDimension_eq`. -/
theorem LinearIsometryEquiv.hilbertDimension_eq {𝕜 : Type*} [RCLike 𝕜] {H K : Type u}
    [NormedAddCommGroup H] [InnerProductSpace 𝕜 H] [CompleteSpace H]
    [NormedAddCommGroup K] [InnerProductSpace 𝕜 K] [CompleteSpace K]
    (U : H ≃ₗᵢ[𝕜] K) :
    TauCeti.hilbertDimension 𝕜 H = TauCeti.hilbertDimension 𝕜 K := by
  simpa using U.lift_hilbertDimension_eq

namespace TauCeti

section Classification

variable (𝕜 : Type*) [RCLike 𝕜]

/-- **Unitary classification of Hilbert spaces.** Two Hilbert spaces over `𝕜` (`ℝ` or `ℂ`) are
linearly isometrically equivalent if and only if their Hilbert dimensions agree up to universe
lift. -/
theorem nonempty_linearIsometryEquiv_iff_lift_hilbertDimension_eq
    (H : Type u) (K : Type v)
    [NormedAddCommGroup H] [InnerProductSpace 𝕜 H] [CompleteSpace H]
    [NormedAddCommGroup K] [InnerProductSpace 𝕜 K] [CompleteSpace K] :
    Nonempty (H ≃ₗᵢ[𝕜] K) ↔
      Cardinal.lift.{v} (hilbertDimension 𝕜 H) = Cardinal.lift.{u} (hilbertDimension 𝕜 K) := by
  obtain ⟨_, bH, -⟩ := exists_hilbertBasis 𝕜 H
  obtain ⟨_, bK, -⟩ := exists_hilbertBasis 𝕜 K
  rw [← bH.mk_eq_hilbertDimension, ← bK.mk_eq_hilbertDimension]
  exact bH.nonempty_linearIsometryEquiv_iff_lift_mk_eq bK

/-- **Unitary classification of Hilbert spaces (same universe).** Two Hilbert spaces in the same
universe over `𝕜` are linearly isometrically equivalent if and only if they have equal Hilbert
dimension. -/
theorem nonempty_linearIsometryEquiv_iff_hilbertDimension_eq
    (H K : Type u)
    [NormedAddCommGroup H] [InnerProductSpace 𝕜 H] [CompleteSpace H]
    [NormedAddCommGroup K] [InnerProductSpace 𝕜 K] [CompleteSpace K] :
    Nonempty (H ≃ₗᵢ[𝕜] K) ↔ hilbertDimension 𝕜 H = hilbertDimension 𝕜 K := by
  simpa using nonempty_linearIsometryEquiv_iff_lift_hilbertDimension_eq 𝕜 H K

/-- The Hilbert dimension of `ℓ²(ι, 𝕜)` is the cardinality of `ι` (lifted to `max v w`). -/
@[simp]
theorem hilbertDimension_lp {𝕜 : Type w} [RCLike 𝕜] (ι : Type v) :
    hilbertDimension 𝕜 ℓ²(ι, 𝕜) = Cardinal.lift.{w} #ι := by
  have h := (lp.hilbertBasisFun ι 𝕜).lift_mk_eq_hilbertDimension
  rwa [Cardinal.lift_umax.{v, w}, Cardinal.lift_id'.{v, w}, eq_comm] at h

/-- On a finite-dimensional Hilbert space, Hilbert dimension agrees with `Module.finrank`. -/
theorem hilbertDimension_eq_finrank (H : Type u) [NormedAddCommGroup H]
    [InnerProductSpace 𝕜 H] [CompleteSpace H] [FiniteDimensional 𝕜 H] :
    hilbertDimension 𝕜 H = Module.finrank 𝕜 H := by
  obtain ⟨s, b, -⟩ := exists_hilbertBasis 𝕜 H
  have : Finite s := b.finite_iff_finiteDimensional.2 inferInstance
  cases nonempty_fintype s
  rw [← b.mk_eq_hilbertDimension, Cardinal.mk_fintype, b.card_eq_finrank]

/-- The Hilbert dimension of `EuclideanSpace 𝕜 ι` over a finite index type is `Fintype.card ι`. -/
@[simp]
theorem hilbertDimension_euclideanSpace (ι : Type*) [Fintype ι] :
    hilbertDimension 𝕜 (EuclideanSpace 𝕜 ι) = Fintype.card ι := by
  rw [hilbertDimension_eq_finrank, finrank_euclideanSpace]

/-- The scalar field `𝕜` viewed as a one-dimensional Hilbert space over itself has Hilbert
dimension `1`. -/
@[simp]
theorem hilbertDimension_self : hilbertDimension 𝕜 𝕜 = 1 := by
  rw [hilbertDimension_eq_finrank, Module.finrank_self, Nat.cast_one]

end Classification

section Properties

variable {𝕜 : Type*} [RCLike 𝕜] {H : Type u}
  [NormedAddCommGroup H] [InnerProductSpace 𝕜 H] [CompleteSpace H]

/-- A Hilbert space has Hilbert dimension `0` if and only if it is trivial. -/
@[simp]
theorem hilbertDimension_eq_zero_iff : hilbertDimension 𝕜 H = 0 ↔ Subsingleton H := by
  obtain ⟨s, b, -⟩ := exists_hilbertBasis 𝕜 H
  rw [← b.mk_eq_hilbertDimension, Cardinal.mk_eq_zero_iff, b.subsingleton_iff_isEmpty]

/-- A Hilbert space has positive Hilbert dimension if and only if it is nontrivial. -/
theorem hilbertDimension_pos_iff : 0 < hilbertDimension 𝕜 H ↔ Nontrivial H := by
  rw [pos_iff_ne_zero, ne_eq, hilbertDimension_eq_zero_iff, not_subsingleton_iff_nontrivial]

/-- A Hilbert space has finite Hilbert dimension (`< ℵ₀`) if and only if it is
finite-dimensional. -/
theorem hilbertDimension_lt_aleph0_iff :
    hilbertDimension 𝕜 H < ℵ₀ ↔ FiniteDimensional 𝕜 H := by
  obtain ⟨s, b, -⟩ := exists_hilbertBasis 𝕜 H
  rw [← b.mk_eq_hilbertDimension, Cardinal.lt_aleph0_iff_finite, b.finite_iff_finiteDimensional]

/-- A Hilbert space has infinite Hilbert dimension (`ℵ₀ ≤ hilbertDimension 𝕜 H`) if and only if it
is infinite-dimensional. -/
theorem aleph0_le_hilbertDimension_iff :
    ℵ₀ ≤ hilbertDimension 𝕜 H ↔ ¬ FiniteDimensional 𝕜 H := by
  rw [← not_lt, hilbertDimension_lt_aleph0_iff]

variable (𝕜 H) in
/-- **Separability via Hilbert dimension.** A Hilbert space is separable if and only if its Hilbert
dimension is at most `ℵ₀`. -/
theorem separableSpace_iff_hilbertDimension_le_aleph0 :
    TopologicalSpace.SeparableSpace H ↔ hilbertDimension 𝕜 H ≤ ℵ₀ := by
  obtain ⟨s, b, -⟩ := exists_hilbertBasis 𝕜 H
  rw [b.separableSpace_iff_countable, ← b.mk_eq_hilbertDimension, Cardinal.mk_le_aleph0_iff]

/-- A Hilbert space has Hilbert dimension `ℵ₀` if and only if it is separable and
infinite-dimensional. -/
theorem hilbertDimension_eq_aleph0_iff :
    hilbertDimension 𝕜 H = ℵ₀ ↔
      TopologicalSpace.SeparableSpace H ∧ ¬ FiniteDimensional 𝕜 H := by
  rw [le_antisymm_iff, separableSpace_iff_hilbertDimension_le_aleph0 𝕜 H,
    aleph0_le_hilbertDimension_iff]

/-- A Hilbert space admits a `ℕ`-indexed Hilbert basis if and only if it is separable and
infinite-dimensional. -/
theorem nonempty_hilbertBasis_nat_iff :
    Nonempty (HilbertBasis ℕ 𝕜 H) ↔
      TopologicalSpace.SeparableSpace H ∧ ¬ FiniteDimensional 𝕜 H := by
  refine ⟨fun ⟨b⟩ ↦ ⟨b.separableSpace_iff_countable.2 inferInstance,
      b.infinite_iff.1 inferInstance⟩, fun h ↦ ?_⟩
  obtain ⟨s, b, -⟩ := exists_hilbertBasis 𝕜 H
  have hs : #s = ℵ₀ := by
    rw [b.mk_eq_hilbertDimension, hilbertDimension_eq_aleph0_iff]
    exact h
  have hl : Cardinal.lift.{0} #s = Cardinal.lift.{u} #ℕ := by simp [hs]
  obtain ⟨e⟩ := Cardinal.lift_mk_eq'.1 hl
  exact ⟨b.reindex e⟩

/-- **Classification of separable infinite-dimensional Hilbert spaces.** A Hilbert space `H` over
`𝕜` is linearly isometrically equivalent to `ℓ²(ℕ, 𝕜)` if and only if `H` is separable and
infinite-dimensional. -/
theorem nonempty_linearIsometryEquiv_lp_nat_iff :
    Nonempty (H ≃ₗᵢ[𝕜] ℓ²(ℕ, 𝕜)) ↔
      TopologicalSpace.SeparableSpace H ∧ ¬ FiniteDimensional 𝕜 H := by
  rw [← nonempty_hilbertBasis_nat_iff (𝕜 := 𝕜) (H := H)]
  exact ⟨fun ⟨U⟩ ↦ ⟨(lp.hilbertBasisFun ℕ 𝕜).mapₗᵢ U.symm⟩, fun ⟨b⟩ ↦ ⟨b.repr⟩⟩

end Properties

section Examples

variable (𝕜 : Type*) [RCLike 𝕜]

/-- `𝕜` and `𝕜²` are both separable Hilbert spaces, yet have distinct Hilbert dimensions `1` and `2`
and therefore admit no linear isometric equivalence. -/
theorem isEmpty_linearIsometryEquiv_self_euclideanSpace_fin_two :
    IsEmpty (𝕜 ≃ₗᵢ[𝕜] EuclideanSpace 𝕜 (Fin 2)) := by
  rw [← not_nonempty_iff, nonempty_linearIsometryEquiv_iff_lift_hilbertDimension_eq]
  simp

/-- `ℓ²(ℕ, 𝕜)` and `ℓ²(ℤ, 𝕜)` both have Hilbert dimension `ℵ₀` and are linearly isometrically
equivalent. -/
theorem nonempty_linearIsometryEquiv_lp_nat_int :
    Nonempty (ℓ²(ℕ, 𝕜) ≃ₗᵢ[𝕜] ℓ²(ℤ, 𝕜)) := by
  rw [nonempty_linearIsometryEquiv_iff_hilbertDimension_eq]
  simp

/-- `ℓ²(ℕ, 𝕜)` (Hilbert dimension `ℵ₀`) and `ℓ²(ℝ, 𝕜)` (Hilbert dimension `𝔠`) admit no linear
isometric equivalence. -/
theorem isEmpty_linearIsometryEquiv_lp_nat_real :
    IsEmpty (ℓ²(ℕ, 𝕜) ≃ₗᵢ[𝕜] ℓ²(ℝ, 𝕜)) := by
  rw [← not_nonempty_iff, nonempty_linearIsometryEquiv_iff_hilbertDimension_eq]
  simp [Cardinal.mk_real, Cardinal.aleph0_lt_continuum.ne]

end Examples

end TauCeti
