/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.RCLike.Lemmas
public import Mathlib.SetTheory.Cardinal.Arithmetic
public import TauCeti.Analysis.InnerProductSpace.HilbertBasis.Prod
public import TauCeti.Analysis.InnerProductSpace.HilbertBasis.Reindex
public import TauCeti.Analysis.InnerProductSpace.Orthonormal.Basic
public import TauCeti.Analysis.Normed.Lp.Basic

/-!
# Hilbert dimension and unitary classification of Hilbert spaces

In an inner product space `E` over `𝕜` (`ℝ` or `ℂ`), any orthonormal family `v : ι → E` has index
cardinality at most that of any Hilbert basis `c : HilbertBasis κ 𝕜 E` (`Orthonormal.lift_mk_le`,
`Orthonormal.mk_le`), so any two Hilbert bases of `E` have index types of equal cardinality
(`HilbertBasis.lift_mk_eq`, `HilbertBasis.mk_eq`):

* When `κ` is finite, `c.toOrthonormalBasis` identifies `E` as finite-dimensional of dimension
  `Module.finrank 𝕜 E = Fintype.card κ`, bounding `Fintype.card ι` by linear independence
  (`HilbertBasis.finiteDimensional_iff_finite`, `HilbertBasis.finrank_eq_card`).
* When `κ` is infinite, each basis vector `c j` has countable Fourier support in `v`
  (`Orthonormal.countable_support_inner_left`), and the union of those supports over `j : κ` covers
  `ι` (`Orthonormal.iUnion_support_inner_eq_univ`) because any omitted `v i` would be orthogonal to
  every `c j` and hence zero. Thus `#ι ≤ #κ * ℵ₀ = #κ`.

Consequently, two spaces carrying Hilbert bases `b : HilbertBasis ι 𝕜 E` and
`c : HilbertBasis κ 𝕜 F` admit a linear isometric equivalence `E ≃ₗᵢ[𝕜] F` if and only if their
basis index types have the same lifted cardinality
(`HilbertBasis.nonempty_linearIsometryEquiv_iff_lift_mk_eq`): a unitary equivalence transports `b`
to a Hilbert basis of `F` via `HilbertBasis.mapₗᵢ`, and an index equivalence `e : ι ≃ κ` produces a
basis-preserving unitary `b.equiv c e : E ≃ₗᵢ[𝕜] F`.

For any complete inner product space `E`, `TauCeti.hilbertDim 𝕜 E : Cardinal.{u}` is the common
cardinality of all Hilbert bases of `E` (defined from `exists_hilbertBasis 𝕜 E`). Unlike the
algebraic Hamel rank `Module.rank 𝕜 E` — which strictly exceeds `hilbertDim 𝕜 E = ℵ₀` on separable
infinite-dimensional spaces such as `ℓ²(ℕ, 𝕜)`, though always `hilbertDim 𝕜 E ≤ Module.rank 𝕜 E` —
the Hilbert dimension of `ℓ²(ι, 𝕜)` is `#ι` (up to universe lift), bounds every orthonormal family
(`Orthonormal.cardinal_lift_le_hilbertDim`), is monotone along linear isometries and complete
subspaces (`LinearIsometry.lift_hilbertDim_le`, `Submodule.hilbertDim_le`), agrees with
`Module.finrank 𝕜 E` in finite dimension, is invariant under continuous linear equivalences
(`ContinuousLinearEquiv.lift_hilbertDim_eq`, `ContinuousLinearEquiv.hilbertDim_eq`) via a
density-character bound (`HilbertBasis.lift_mk_le_max_aleph0_of_denseRange`), is at most `ℵ₀` if
and only if `E` is separable (`TauCeti.hilbertDim_le_aleph0_iff`), equals `ℵ₀` if and only if `E`
is separable and infinite-dimensional (`TauCeti.hilbertDim_eq_aleph0_iff`), and classifies Hilbert
spaces over `𝕜` up to linear isometric equivalence
(`TauCeti.nonempty_linearIsometryEquiv_iff_lift_hilbertDim_eq`, and
`TauCeti.nonempty_linearIsometryEquiv_iff_finrank_eq` in finite dimension). In particular, separable
Hilbert spaces have Hilbert dimension `0`, a positive natural number, or `ℵ₀`, and every separable
infinite-dimensional Hilbert space is unitarily isomorphic to `ℓ²(ℕ, 𝕜)`. The file also establishes
basis-existence characterizations (`TauCeti.nonempty_hilbertBasis_iff_lift_mk_eq`,
`TauCeti.nonempty_hilbertBasis_nat_iff`) and cardinal addition laws for `L²` products, orthogonal
decompositions, and quotients by closed submodules (`TauCeti.hilbertDim_prodLp`,
`TauCeti.hilbertDim_add_hilbertDim_orthogonal`, `TauCeti.hilbertDim_add_hilbertDim_quotient`,
`TauCeti.hilbertDim_orthogonal_eq_of_finiteDimensional`).

## Main declarations

* `HilbertBasis.separableSpace_iff_countable`: a space with a Hilbert basis `b` is separable iff
  its index type is countable.
* `HilbertBasis.finiteDimensional_iff_finite`, `HilbertBasis.finrank_eq_card`: `E` is
  finite-dimensional iff the index type is finite, with `finrank 𝕜 E = Fintype.card ι`.
* `Orthonormal.lift_mk_le`, `HilbertBasis.lift_mk_eq`: orthonormal cardinality bound and
  basis-cardinality invariance for `HilbertBasis`.
* `HilbertBasis.lift_mk_le_max_aleph0_of_denseRange`: density-character bound for continuous maps
  with dense range.
* `HilbertBasis.nonempty_linearIsometryEquiv_iff_lift_mk_eq`: unitary classification in terms of
  given Hilbert bases.
* `TauCeti.hilbertDim`: the Hilbert dimension of a complete inner product space.
* `Orthonormal.cardinal_lift_le_hilbertDim`, `LinearIsometry.lift_hilbertDim_le`,
  `Submodule.hilbertDim_le`: orthonormal upper bound and monotonicity of `hilbertDim`.
* `ContinuousLinearEquiv.lift_hilbertDim_eq`, `ContinuousLinearEquiv.hilbertDim_eq`: invariance
  of `hilbertDim` under continuous linear equivalences.
* `TauCeti.nonempty_linearIsometryEquiv_iff_lift_hilbertDim_eq`,
  `TauCeti.nonempty_linearIsometryEquiv_iff_finrank_eq`: unitary classification of general and
  finite-dimensional Hilbert spaces.
* `TauCeti.hilbertDim_le_aleph0_iff`, `TauCeti.hilbertDim_eq_aleph0_iff`: separability and
  countably infinite Hilbert dimension.
* `TauCeti.hilbertDim_prodLp`, `TauCeti.hilbertDim_add_hilbertDim_orthogonal`,
  `TauCeti.hilbertDim_add_hilbertDim_quotient`: cardinal addition laws.

## References

* J. B. Conway, *A Course in Functional Analysis*, 2nd ed., Chapter I, §§4–5.
* M. Reed and B. Simon, *Methods of Modern Mathematical Physics I: Functional Analysis*, §II.3.
-/

public section

open scoped Cardinal InnerProductSpace lp

universe u v w

namespace HilbertBasis

section Structure

variable {ι : Type*} {𝕜 : Type*} {E : Type*} [RCLike 𝕜]
  [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]

/-- An inner product space carrying a Hilbert basis indexed by `ι` is trivial if and only if `ι` is
empty. -/
theorem subsingleton_iff_isEmpty (b : HilbertBasis ι 𝕜 E) : Subsingleton E ↔ IsEmpty ι :=
  ⟨fun _ ↦ ⟨fun i ↦ b.orthonormal.ne_zero i (Subsingleton.elim _ _)⟩,
   fun _ ↦ b.repr.toEquiv.subsingleton⟩

/-- An inner product space carrying a Hilbert basis indexed by `ι` is nontrivial if and only if `ι`
is nonempty. -/
theorem nontrivial_iff_nonempty (b : HilbertBasis ι 𝕜 E) : Nontrivial E ↔ Nonempty ι := by
  rw [← not_subsingleton_iff_nontrivial, b.subsingleton_iff_isEmpty, not_isEmpty_iff]

/-- An inner product space carrying a Hilbert basis indexed by `ι` is finite-dimensional if and
only if `ι` is finite. -/
theorem finiteDimensional_iff_finite (b : HilbertBasis ι 𝕜 E) :
    FiniteDimensional 𝕜 E ↔ Finite ι := by
  refine ⟨fun _ ↦ b.orthonormal.linearIndependent.finite, fun _ ↦ ?_⟩
  cases nonempty_fintype ι
  exact b.toOrthonormalBasis.toBasis.finiteDimensional_of_finite

/-- The index type of a Hilbert basis of `E` is infinite if and only if `E` is not
finite-dimensional. -/
theorem infinite_iff_not_finiteDimensional (b : HilbertBasis ι 𝕜 E) :
    Infinite ι ↔ ¬ FiniteDimensional 𝕜 E := by
  rw [← not_finite_iff_infinite, b.finiteDimensional_iff_finite]

/-- For a finite Hilbert basis, `Module.finrank 𝕜 E` equals `Fintype.card ι`. -/
theorem finrank_eq_card [Fintype ι] (b : HilbertBasis ι 𝕜 E) :
    Module.finrank 𝕜 E = Fintype.card ι :=
  Module.finrank_eq_card_basis b.toOrthonormalBasis.toBasis

/-- For any Hilbert basis `b : HilbertBasis ι 𝕜 E`, `Module.finrank 𝕜 E` equals `Nat.card ι`
(both sides being `0` in infinite dimension). -/
theorem finrank_eq_nat_card (b : HilbertBasis ι 𝕜 E) :
    Module.finrank 𝕜 E = Nat.card ι := by
  by_cases h : Finite ι
  · cases nonempty_fintype ι
    rw [b.finrank_eq_card, Nat.card_eq_fintype_card]
  · have : Infinite ι := not_finite_iff_infinite.1 h
    rw [Module.finrank_of_not_finite (mt b.finiteDimensional_iff_finite.1 h),
      Nat.card_eq_zero_of_infinite]

/-- **Separability in terms of a Hilbert basis.** An inner product space carrying a Hilbert basis
`b : HilbertBasis ι 𝕜 E` is separable if and only if the index type `ι` is countable. -/
theorem separableSpace_iff_countable (b : HilbertBasis ι 𝕜 E) :
    TopologicalSpace.SeparableSpace E ↔ Countable ι := by
  refine ⟨fun _ ↦ b.orthonormal.countable_of_separableSpace, fun _ ↦ ?_⟩
  have : TopologicalSpace.SeparableSpace ℓ²(ι, 𝕜) := lp.separableSpace (by norm_num)
  exact b.repr.symm.surjective.denseRange.separableSpace b.repr.symm.continuous

/-- The index type of a Hilbert basis of a separable infinite-dimensional Hilbert space is
countably infinite, hence equivalent to `ℕ`. -/
theorem nonempty_equiv_nat (b : HilbertBasis ι 𝕜 E) [TopologicalSpace.SeparableSpace E]
    (hE : ¬ FiniteDimensional 𝕜 E) : Nonempty (ι ≃ ℕ) := by
  have : Countable ι := b.separableSpace_iff_countable.1 ‹_›
  have : Infinite ι := b.infinite_iff_not_finiteDimensional.2 hE
  exact nonempty_equiv_of_countable

end Structure

end HilbertBasis

namespace Orthonormal

variable {𝕜 : Type*} {E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]

/-- Every member `v i` of an orthonormal family pairs nontrivially with at least one member `c j` of
any Hilbert basis of `E`, so the supports of `i ↦ ⟪v i, c j⟫_𝕜` cover `ι`. -/
theorem iUnion_support_inner_eq_univ {ι : Type*} {κ : Type*} {v : ι → E}
    (hv : Orthonormal 𝕜 v) (c : HilbertBasis κ 𝕜 E) :
    (⋃ j : κ, Function.support fun i : ι ↦ ⟪v i, c j⟫_𝕜) = Set.univ := by
  refine Set.eq_univ_of_forall fun i ↦ Set.mem_iUnion.2 ?_
  by_contra! h
  have hrepr : c.repr (v i) = 0 := by
    ext j
    have hj : ⟪v i, c j⟫_𝕜 = 0 := Function.notMem_support.1 (h j)
    rw [c.repr_apply_apply, ← inner_conj_symm, hj, map_zero, lp.coeFn_zero, Pi.zero_apply]
  exact hv.ne_zero i (c.repr.map_eq_zero_iff.1 hrepr)

/-- Any orthonormal family in `E` has index cardinality at most that of any Hilbert basis of `E` in
the same universe. -/
theorem mk_le {ι κ : Type u} {v : ι → E} (hv : Orthonormal 𝕜 v) (c : HilbertBasis κ 𝕜 E) :
    #ι ≤ #κ := by
  by_cases hκ : Finite κ
  · have : FiniteDimensional 𝕜 E := c.finiteDimensional_iff_finite.2 hκ
    have : Finite ι := hv.linearIndependent.finite
    cases nonempty_fintype ι
    cases nonempty_fintype κ
    rw [Cardinal.mk_fintype, Cardinal.mk_fintype, ← c.finrank_eq_card]
    exact mod_cast hv.linearIndependent.fintype_card_le_finrank
  · have : Infinite κ := not_finite_iff_infinite.1 hκ
    set s : κ → Set ι := fun j ↦ Function.support fun i : ι ↦ ⟪v i, c j⟫_𝕜
    calc #ι = #(Set.univ : Set ι) := Cardinal.mk_univ.symm
      _ = #(⋃ j : κ, s j) := by rw [hv.iUnion_support_inner_eq_univ c]
      _ ≤ #κ * ⨆ j : κ, #(s j) := Cardinal.mk_iUnion_le s
      _ ≤ #κ * ℵ₀ := mul_le_mul_of_nonneg_left (ciSup_le fun j ↦
          Cardinal.le_aleph0_iff_set_countable.2
            (hv.countable_support_inner_left (c j))) zero_le
      _ = #κ := Cardinal.mul_eq_left (Cardinal.aleph0_le_mk κ) (Cardinal.aleph0_le_mk κ)
          Cardinal.aleph0_ne_zero

/-- Any orthonormal family `v : ι → E` has lifted index cardinality at most that of any Hilbert
basis `c : HilbertBasis κ 𝕜 E`. -/
theorem lift_mk_le {ι : Type u} {κ : Type v} {v : ι → E} (hv : Orthonormal 𝕜 v)
    (c : HilbertBasis κ 𝕜 E) :
    Cardinal.lift.{v} #ι ≤ Cardinal.lift.{u} #κ := by
  have h := (hv.comp (Equiv.ulift : ULift.{v} ι ≃ ι) Equiv.ulift.injective).mk_le
    (c.reindexOfRepr (Equiv.ulift.symm : κ ≃ ULift.{u} κ))
  rwa [Cardinal.mk_uLift, Cardinal.mk_uLift] at h

end Orthonormal

namespace HilbertBasis

section Cardinality

variable {𝕜 : Type*} {E : Type*} {F : Type*} [RCLike 𝕜]
  [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [NormedAddCommGroup F] [InnerProductSpace 𝕜 F]

/-- **Invariance of Hilbert basis cardinality (same universe).** Any two Hilbert bases of `E`
indexed by types in the same universe have equal index cardinalities. -/
theorem mk_eq {ι κ : Type u} (b : HilbertBasis ι 𝕜 E) (c : HilbertBasis κ 𝕜 E) :
    #ι = #κ :=
  le_antisymm (b.orthonormal.mk_le c) (c.orthonormal.mk_le b)

/-- **Invariance of Hilbert basis cardinality.** Any two Hilbert bases `b : HilbertBasis ι 𝕜 E` and
`c : HilbertBasis κ 𝕜 E` of the same inner product space have index types of equal lifted
cardinality. -/
theorem lift_mk_eq {ι : Type u} {κ : Type v} (b : HilbertBasis ι 𝕜 E) (c : HilbertBasis κ 𝕜 E) :
    Cardinal.lift.{v} #ι = Cardinal.lift.{u} #κ :=
  le_antisymm (b.orthonormal.lift_mk_le c) (c.orthonormal.lift_mk_le b)

/-- Any two Hilbert bases of the same space have equivalent index types. -/
theorem nonempty_equiv {ι : Type u} {κ : Type v} (b : HilbertBasis ι 𝕜 E)
    (c : HilbertBasis κ 𝕜 E) : Nonempty (ι ≃ κ) :=
  Cardinal.lift_mk_eq'.1 (b.lift_mk_eq c)

/-- **Unitary classification of Hilbert spaces via Hilbert bases.** Two spaces carrying Hilbert
bases `b : HilbertBasis ι 𝕜 E` and `c : HilbertBasis κ 𝕜 F` are linearly isometric if and only if
their basis index types have the same lifted cardinality. -/
theorem nonempty_linearIsometryEquiv_iff_lift_mk_eq {ι : Type u} {κ : Type v}
    (b : HilbertBasis ι 𝕜 E) (c : HilbertBasis κ 𝕜 F) :
    Nonempty (E ≃ₗᵢ[𝕜] F) ↔ Cardinal.lift.{v} #ι = Cardinal.lift.{u} #κ :=
  ⟨fun ⟨U⟩ ↦ (b.mapₗᵢ U).lift_mk_eq c,
   fun h ↦ let ⟨e⟩ := Cardinal.lift_mk_eq'.1 h; ⟨b.equiv c e⟩⟩

/-- Same-universe form of `HilbertBasis.nonempty_linearIsometryEquiv_iff_lift_mk_eq`. -/
theorem nonempty_linearIsometryEquiv_iff_mk_eq {ι κ : Type u}
    (b : HilbertBasis ι 𝕜 E) (c : HilbertBasis κ 𝕜 F) :
    Nonempty (E ≃ₗᵢ[𝕜] F) ↔ #ι = #κ := by
  simpa using b.nonempty_linearIsometryEquiv_iff_lift_mk_eq c

/-- Two spaces carrying Hilbert bases `b` and `c` are linearly isometric if and only if the index
types of `b` and `c` are equivalent. -/
theorem nonempty_linearIsometryEquiv_iff_nonempty_equiv {ι : Type u} {κ : Type v}
    (b : HilbertBasis ι 𝕜 E) (c : HilbertBasis κ 𝕜 F) :
    Nonempty (E ≃ₗᵢ[𝕜] F) ↔ Nonempty (ι ≃ κ) := by
  rw [b.nonempty_linearIsometryEquiv_iff_lift_mk_eq c, Cardinal.lift_mk_eq']

private theorem denseRange_finset_sum_smul {ι : Type u} {α : Type v}
    (b : HilbertBasis ι 𝕜 E) {g : α → 𝕜} (hg : DenseRange g) :
    DenseRange (fun t : Finset (ι × α) ↦ ∑ p ∈ t, g p.2 • b p.1) := by
  classical
  rw [Metric.denseRange_iff]
  intro x ε hε
  obtain ⟨t, ht⟩ := Metric.tendsto_atTop.1 (b.hasSum_repr x) (ε / 2) (half_pos hε)
  have ht' : dist (∑ i ∈ t, b.repr x i • b i) x < ε / 2 := ht t le_rfl
  have hδ : 0 < ε / (2 * (t.card + 1)) := by positivity
  choose n hn using fun i : ι ↦
    Metric.denseRange_iff.1 hg (b.repr x i) (ε / (2 * (t.card + 1))) hδ
  refine ⟨t.image fun i ↦ (i, n i), ?_⟩
  have hsum_eq : ∑ p ∈ t.image (fun i ↦ (i, n i)), g p.2 • b p.1 = ∑ i ∈ t, g (n i) • b i :=
    Finset.sum_image fun _ _ _ _ h ↦ (Prod.mk.inj h).1
  have hdist1 : dist (∑ i ∈ t, b.repr x i • b i) (∑ i ∈ t, g (n i) • b i) < ε / 2 := by
    rw [dist_eq_norm, ← Finset.sum_sub_distrib]
    calc ‖∑ i ∈ t, (b.repr x i • b i - g (n i) • b i)‖
        ≤ ∑ i ∈ t, ‖(b.repr x i - g (n i)) • b i‖ := by
          simpa only [sub_smul] using norm_sum_le t _
      _ = ∑ i ∈ t, dist (b.repr x i) (g (n i)) := Finset.sum_congr rfl fun i _ ↦ by
          rw [norm_smul, b.orthonormal.1 i, mul_one, dist_eq_norm]
      _ ≤ ∑ _i ∈ t, ε / (2 * (t.card + 1)) := Finset.sum_le_sum fun i _ ↦ (hn i).le
      _ = t.card * (ε / (2 * (t.card + 1))) := by rw [Finset.sum_const, nsmul_eq_mul]
      _ < ε / 2 := by
          rw [mul_div_assoc', div_lt_div_iff₀ (by positivity) (by norm_num)]
          nlinarith
  rw [hsum_eq]
  calc dist x (∑ i ∈ t, g (n i) • b i)
      ≤ dist x (∑ i ∈ t, b.repr x i • b i) +
          dist (∑ i ∈ t, b.repr x i • b i) (∑ i ∈ t, g (n i) • b i) := dist_triangle _ _ _
    _ < ε / 2 + ε / 2 := add_lt_add (by rwa [dist_comm]) hdist1
    _ = ε := add_halves ε

private theorem lift_mk_le_of_orthonormal_denseRange {ι : Type u} {α : Type v}
    {v : ι → F} (hv : Orthonormal 𝕜 v) {ψ : α → F} (hψ : DenseRange ψ) :
    Cardinal.lift.{v} #ι ≤ Cardinal.lift.{u} #α := by
  choose q hq using fun i ↦ Metric.denseRange_iff.1 hψ (v i) (1 / 2) (by norm_num)
  refine Cardinal.lift_mk_le'.2 ⟨⟨q, fun i₁ i₂ heq ↦ by_contra fun hne ↦ ?_⟩⟩
  have hdist : dist (v i₁) (v i₂) < 1 := calc
    dist (v i₁) (v i₂) ≤ dist (v i₁) (ψ (q i₁)) + dist (ψ (q i₁)) (v i₂) := dist_triangle _ _ _
    _ = dist (v i₁) (ψ (q i₁)) + dist (v i₂) (ψ (q i₂)) := by
        rw [heq, dist_comm (ψ (q i₂)) (v i₂)]
    _ < 1 / 2 + 1 / 2 := add_lt_add (hq i₁) (hq i₂)
    _ = 1 := by norm_num
  have hsq : ‖v i₁ - v i₂‖ ^ 2 = 2 := by
    rw [norm_sub_sq (𝕜 := 𝕜), hv.1 i₁, hv.1 i₂, hv.2 hne]
    norm_num
  rw [dist_eq_norm] at hdist
  nlinarith [norm_nonneg (v i₁ - v i₂)]

/-- **Density-character bound.** If `f : E → F` is continuous with dense range, then the index
cardinality of any Hilbert basis of `F` is at most `max (#ι) ℵ₀` for any Hilbert basis `b` of
`E`. -/
theorem lift_mk_le_max_aleph0_of_denseRange {ι : Type u} {κ : Type v}
    (b : HilbertBasis ι 𝕜 E) (c : HilbertBasis κ 𝕜 F) {f : E → F}
    (hf : Continuous f) (hd : DenseRange f) :
    Cardinal.lift.{u} #κ ≤ max (Cardinal.lift.{v} #ι) ℵ₀ := by
  have : ProperSpace 𝕜 := FiniteDimensional.proper_rclike 𝕜 𝕜
  obtain ⟨s, hs_count, hs_dense⟩ := TopologicalSpace.exists_countable_dense 𝕜
  obtain ⟨g, hg⟩ := hs_count.exists_eq_range hs_dense.nonempty
  have hg_dense : DenseRange g := by simpa only [DenseRange, hg] using hs_dense
  have hφ_dense := b.denseRange_finset_sum_smul hg_dense
  have hfφ_dense : DenseRange (f ∘ fun t : Finset (ι × ℕ) ↦ ∑ p ∈ t, g p.2 • b p.1) := by
    rw [DenseRange, Set.range_comp]
    exact hd.dense_image hf hφ_dense
  refine (lift_mk_le_of_orthonormal_denseRange c.orthonormal hfφ_dense).trans ?_
  by_cases hι : Finite ι
  · have : Countable (Finset (ι × ℕ)) := inferInstance
    have hct : Cardinal.lift.{v} #(Finset (ι × ℕ)) ≤ ℵ₀ := by
      simpa only [Cardinal.lift_aleph0] using
        Cardinal.lift_le.2 (Cardinal.mk_le_aleph0 (α := Finset (ι × ℕ)))
    exact hct.trans (le_max_right _ _)
  · have : Infinite ι := not_finite_iff_infinite.1 hι
    have : Infinite (ι × ℕ) := inferInstance
    have hcard : #(Finset (ι × ℕ)) = #ι := by
      rw [Cardinal.mk_finset_of_infinite, Cardinal.mk_prod, Cardinal.lift_uzero,
        Cardinal.mk_nat, Cardinal.lift_aleph0, Cardinal.mk_mul_aleph0_eq]
    rw [hcard]
    exact le_max_left _ _

end Cardinality

end HilbertBasis

namespace TauCeti

/-- The **Hilbert dimension** (or orthogonal dimension) of a complete inner product space `E` over
`𝕜`: the cardinality of any Hilbert basis of `E`. Unlike the algebraic Hamel rank
`Module.rank 𝕜 E`, `hilbertDim 𝕜 E` is `ℵ₀` on `ℓ²(ℕ, 𝕜)` and classifies Hilbert spaces up to
linear isometric equivalence (`TauCeti.nonempty_linearIsometryEquiv_iff_lift_hilbertDim_eq`). -/
noncomputable def hilbertDim (𝕜 : Type*) (E : Type u) [RCLike 𝕜] [NormedAddCommGroup E]
    [InnerProductSpace 𝕜 E] [CompleteSpace E] : Cardinal.{u} :=
  #(exists_hilbertBasis 𝕜 E).choose

end TauCeti

namespace HilbertBasis

/-- Every Hilbert basis `b : HilbertBasis ι 𝕜 E` has lifted index cardinality equal to
`TauCeti.hilbertDim 𝕜 E`. -/
theorem lift_hilbertDim_eq {𝕜 : Type*} {E : Type u} {ι : Type v} [RCLike 𝕜]
    [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
    (b : HilbertBasis ι 𝕜 E) :
    Cardinal.lift.{v} (TauCeti.hilbertDim 𝕜 E) = Cardinal.lift.{u} #ι := by
  rw [TauCeti.hilbertDim]
  exact (exists_hilbertBasis 𝕜 E).choose_spec.choose.lift_mk_eq b

/-- Same-universe form of `HilbertBasis.lift_hilbertDim_eq`. -/
theorem hilbertDim_eq {𝕜 : Type*} {E ι : Type u} [RCLike 𝕜]
    [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
    (b : HilbertBasis ι 𝕜 E) :
    TauCeti.hilbertDim 𝕜 E = #ι := by
  simpa using b.lift_hilbertDim_eq

end HilbertBasis

namespace Orthonormal

/-- Every orthonormal family in a Hilbert space `E` has lifted index cardinality at most
`TauCeti.hilbertDim 𝕜 E`. -/
theorem cardinal_lift_le_hilbertDim {𝕜 : Type*} {E : Type u} {ι : Type v} [RCLike 𝕜]
    [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
    {v : ι → E} (hv : Orthonormal 𝕜 v) :
    Cardinal.lift.{u} #ι ≤ Cardinal.lift.{v} (TauCeti.hilbertDim 𝕜 E) := by
  obtain ⟨_, b, -⟩ := exists_hilbertBasis 𝕜 E
  simpa only [← b.hilbertDim_eq] using hv.lift_mk_le b

/-- Same-universe form of `Orthonormal.cardinal_lift_le_hilbertDim`. -/
theorem cardinal_le_hilbertDim {𝕜 : Type*} {E ι : Type u} [RCLike 𝕜]
    [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
    {v : ι → E} (hv : Orthonormal 𝕜 v) :
    #ι ≤ TauCeti.hilbertDim 𝕜 E := by
  simpa using hv.cardinal_lift_le_hilbertDim

end Orthonormal

namespace LinearIsometry

/-- A linear isometry between Hilbert spaces does not increase the lifted Hilbert dimension. -/
theorem lift_hilbertDim_le {𝕜 : Type*} {E : Type u} {F : Type v} [RCLike 𝕜]
    [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
    [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F]
    (f : E →ₗᵢ[𝕜] F) :
    Cardinal.lift.{v} (TauCeti.hilbertDim 𝕜 E) ≤ Cardinal.lift.{u} (TauCeti.hilbertDim 𝕜 F) := by
  obtain ⟨_, b, -⟩ := exists_hilbertBasis 𝕜 E
  rw [b.hilbertDim_eq]
  exact (b.orthonormal.comp_linearIsometry f).cardinal_lift_le_hilbertDim

/-- Same-universe form of `LinearIsometry.lift_hilbertDim_le`. -/
theorem hilbertDim_le {𝕜 : Type*} {E F : Type u} [RCLike 𝕜]
    [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
    [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F]
    (f : E →ₗᵢ[𝕜] F) :
    TauCeti.hilbertDim 𝕜 E ≤ TauCeti.hilbertDim 𝕜 F := by
  simpa using f.lift_hilbertDim_le

end LinearIsometry

namespace Submodule

/-- A complete subspace of a Hilbert space has Hilbert dimension at most that of the ambient
space. -/
theorem hilbertDim_le {𝕜 : Type*} {E : Type u} [RCLike 𝕜]
    [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
    (K : Submodule 𝕜 E) [CompleteSpace K] :
    TauCeti.hilbertDim 𝕜 K ≤ TauCeti.hilbertDim 𝕜 E :=
  K.subtypeₗᵢ.hilbertDim_le

end Submodule

namespace LinearIsometryEquiv

/-- Linearly isometric Hilbert spaces have equal lifted Hilbert dimensions. -/
theorem lift_hilbertDim_eq {𝕜 : Type*} {E : Type u} {F : Type v} [RCLike 𝕜]
    [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
    [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F]
    (e : E ≃ₗᵢ[𝕜] F) :
    Cardinal.lift.{v} (TauCeti.hilbertDim 𝕜 E) = Cardinal.lift.{u} (TauCeti.hilbertDim 𝕜 F) := by
  obtain ⟨_, b, -⟩ := exists_hilbertBasis 𝕜 E
  rw [b.hilbertDim_eq, (b.mapₗᵢ e).lift_hilbertDim_eq]

/-- Linearly isometric Hilbert spaces in the same universe have equal Hilbert dimensions. -/
theorem hilbertDim_eq {𝕜 : Type*} {E F : Type u} [RCLike 𝕜]
    [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
    [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F]
    (e : E ≃ₗᵢ[𝕜] F) :
    TauCeti.hilbertDim 𝕜 E = TauCeti.hilbertDim 𝕜 F := by
  simpa using e.lift_hilbertDim_eq

end LinearIsometryEquiv

namespace TauCeti

section Classification

variable {𝕜 : Type*} [RCLike 𝕜]

/-- A Hilbert space `E` admits a Hilbert basis indexed by `ι` if and only if `#ι` equals
`hilbertDim 𝕜 E` (up to universe lift). -/
theorem nonempty_hilbertBasis_iff_lift_mk_eq {E : Type u} {ι : Type v}
    [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E] :
    Nonempty (HilbertBasis ι 𝕜 E) ↔ Cardinal.lift.{u} #ι = Cardinal.lift.{v} (hilbertDim 𝕜 E) := by
  refine ⟨fun ⟨b⟩ ↦ b.lift_hilbertDim_eq.symm, fun h ↦ ?_⟩
  obtain ⟨w, b, -⟩ := exists_hilbertBasis 𝕜 E
  rw [b.hilbertDim_eq] at h
  obtain ⟨e⟩ := Cardinal.lift_mk_eq'.1 h
  exact ⟨b.reindexOfRepr e.symm⟩

/-- Same-universe specialization of `TauCeti.nonempty_hilbertBasis_iff_lift_mk_eq`. -/
theorem nonempty_hilbertBasis_iff_mk_eq {E ι : Type u}
    [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E] :
    Nonempty (HilbertBasis ι 𝕜 E) ↔ #ι = hilbertDim 𝕜 E := by
  simpa using nonempty_hilbertBasis_iff_lift_mk_eq (𝕜 := 𝕜) (E := E) (ι := ι)

/-- **Unitary classification of Hilbert spaces.** Two Hilbert spaces `E` and `F` over `𝕜` admit a
linear isometric equivalence if and only if their lifted Hilbert dimensions are equal. -/
theorem nonempty_linearIsometryEquiv_iff_lift_hilbertDim_eq {E : Type u} {F : Type v}
    [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
    [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F] :
    Nonempty (E ≃ₗᵢ[𝕜] F) ↔
      Cardinal.lift.{v} (hilbertDim 𝕜 E) = Cardinal.lift.{u} (hilbertDim 𝕜 F) := by
  obtain ⟨_, bE, -⟩ := exists_hilbertBasis 𝕜 E
  obtain ⟨_, bF, -⟩ := exists_hilbertBasis 𝕜 F
  rw [bE.hilbertDim_eq, bF.hilbertDim_eq]
  exact bE.nonempty_linearIsometryEquiv_iff_lift_mk_eq bF

/-- Two Hilbert spaces in the same universe are linearly isometric if and only if they have the
same Hilbert dimension. -/
theorem nonempty_linearIsometryEquiv_iff_hilbertDim_eq {E F : Type u}
    [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
    [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F] :
    Nonempty (E ≃ₗᵢ[𝕜] F) ↔ hilbertDim 𝕜 E = hilbertDim 𝕜 F := by
  simpa using nonempty_linearIsometryEquiv_iff_lift_hilbertDim_eq (𝕜 := 𝕜) (E := E) (F := F)

/-- Two Hilbert spaces with distinct lifted Hilbert dimensions admit no linear isometric
equivalence. -/
theorem isEmpty_linearIsometryEquiv_of_lift_hilbertDim_ne {E : Type u} {F : Type v}
    [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
    [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F]
    (h : Cardinal.lift.{v} (hilbertDim 𝕜 E) ≠ Cardinal.lift.{u} (hilbertDim 𝕜 F)) :
    IsEmpty (E ≃ₗᵢ[𝕜] F) :=
  ⟨fun e ↦ h e.lift_hilbertDim_eq⟩

/-- Two Hilbert spaces in the same universe with distinct Hilbert dimensions admit no linear
isometric equivalence. -/
theorem isEmpty_linearIsometryEquiv_of_hilbertDim_ne {E F : Type u}
    [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
    [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F]
    (h : hilbertDim 𝕜 E ≠ hilbertDim 𝕜 F) :
    IsEmpty (E ≃ₗᵢ[𝕜] F) :=
  ⟨fun e ↦ h e.hilbertDim_eq⟩

/-- The Hilbert dimension of `ℓ²(ι, 𝕜)` is the lifted cardinality of `ι`. -/
@[simp]
theorem hilbertDim_lp (𝕜 : Type w) (ι : Type v) [RCLike 𝕜] :
    hilbertDim 𝕜 ℓ²(ι, 𝕜) = Cardinal.lift.{w} #ι := by
  have h := (default : HilbertBasis ι 𝕜 ℓ²(ι, 𝕜)).lift_hilbertDim_eq
  rw [Cardinal.lift_id'.{v, w}, Cardinal.lift_umax.{v, w}] at h
  exact h

/-- When `ι` and `𝕜` lie in the same universe, `hilbertDim 𝕜 ℓ²(ι, 𝕜) = #ι`. -/
theorem hilbertDim_lp' (𝕜 ι : Type u) [RCLike 𝕜] :
    hilbertDim 𝕜 ℓ²(ι, 𝕜) = #ι := by
  simp

/-- The Hilbert dimension of `EuclideanSpace 𝕜 ι` is `Fintype.card ι`. -/
@[simp]
theorem hilbertDim_euclideanSpace (𝕜 : Type w) (ι : Type v) [RCLike 𝕜] [Fintype ι] :
    hilbertDim 𝕜 (EuclideanSpace 𝕜 ι) = Fintype.card ι := by
  simpa using (EuclideanSpace.basisFun ι 𝕜).toHilbertBasis.lift_hilbertDim_eq

end Classification

section Properties

variable {𝕜 : Type*} {E : Type u} [RCLike 𝕜]
  [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]

/-- A trivial Hilbert space has Hilbert dimension `0`. -/
@[simp]
theorem hilbertDim_of_subsingleton [Subsingleton E] : hilbertDim 𝕜 E = 0 := by
  obtain ⟨w, b, -⟩ := exists_hilbertBasis 𝕜 E
  have : IsEmpty w := b.subsingleton_iff_isEmpty.1 ‹_›
  rw [b.hilbertDim_eq, Cardinal.mk_eq_zero]

/-- The Hilbert dimension of `E` vanishes if and only if `E` is trivial. -/
theorem hilbertDim_eq_zero_iff : hilbertDim 𝕜 E = 0 ↔ Subsingleton E := by
  obtain ⟨w, b, -⟩ := exists_hilbertBasis 𝕜 E
  rw [b.hilbertDim_eq, Cardinal.mk_eq_zero_iff, b.subsingleton_iff_isEmpty]

/-- The Hilbert dimension of `E` is positive if and only if `E` is nontrivial. -/
theorem hilbertDim_pos_iff : 0 < hilbertDim 𝕜 E ↔ Nontrivial E := by
  rw [pos_iff_ne_zero, ne_eq, hilbertDim_eq_zero_iff, not_subsingleton_iff_nontrivial]

/-- In finite dimension, `hilbertDim 𝕜 E` agrees with `Module.finrank 𝕜 E`. -/
theorem hilbertDim_eq_finrank [FiniteDimensional 𝕜 E] :
    hilbertDim 𝕜 E = Module.finrank 𝕜 E := by
  obtain ⟨w, b, -⟩ := exists_hilbertBasis 𝕜 E
  have : Finite w := b.finiteDimensional_iff_finite.1 ‹_›
  cases nonempty_fintype w
  rw [b.hilbertDim_eq, b.finrank_eq_card, Cardinal.mk_fintype]

/-- Every Hilbert basis is linearly independent, so the Hilbert dimension never exceeds the
algebraic Hamel rank `Module.rank 𝕜 E`. -/
theorem hilbertDim_le_rank : hilbertDim 𝕜 E ≤ Module.rank 𝕜 E := by
  obtain ⟨w, b, -⟩ := exists_hilbertBasis 𝕜 E
  rw [b.hilbertDim_eq]
  exact b.orthonormal.linearIndependent.cardinal_le_rank

/-- In finite dimension, the Hilbert dimension agrees with the algebraic rank `Module.rank 𝕜 E`. -/
theorem hilbertDim_eq_rank_of_finiteDimensional [FiniteDimensional 𝕜 E] :
    hilbertDim 𝕜 E = Module.rank 𝕜 E := by
  rw [hilbertDim_eq_finrank, Module.finrank_eq_rank]

/-- Viewing a scalar field `𝕜` (`ℝ` or `ℂ`) as a one-dimensional Hilbert space over itself gives
`hilbertDim 𝕜 𝕜 = 1`. -/
@[simp]
theorem hilbertDim_self (𝕜 : Type u) [RCLike 𝕜] : hilbertDim 𝕜 𝕜 = 1 := by
  rw [hilbertDim_eq_finrank, Module.finrank_self, Nat.cast_one]

/-- A Hilbert space is finite-dimensional if and only if its Hilbert dimension is strictly less
than `ℵ₀`. -/
theorem hilbertDim_lt_aleph0_iff : hilbertDim 𝕜 E < ℵ₀ ↔ FiniteDimensional 𝕜 E := by
  obtain ⟨w, b, -⟩ := exists_hilbertBasis 𝕜 E
  rw [b.hilbertDim_eq, Cardinal.lt_aleph0_iff_finite, b.finiteDimensional_iff_finite]

/-- A Hilbert space is infinite-dimensional if and only if its Hilbert dimension is at least `ℵ₀`.
-/
theorem aleph0_le_hilbertDim_iff : ℵ₀ ≤ hilbertDim 𝕜 E ↔ ¬ FiniteDimensional 𝕜 E := by
  rw [← not_lt, hilbertDim_lt_aleph0_iff]

/-- **Hilbert-dimension characterization of separability.** A Hilbert space `E` is separable if and
only if `hilbertDim 𝕜 E ≤ ℵ₀`. -/
theorem hilbertDim_le_aleph0_iff :
    hilbertDim 𝕜 E ≤ ℵ₀ ↔ TopologicalSpace.SeparableSpace E := by
  obtain ⟨w, b, -⟩ := exists_hilbertBasis 𝕜 E
  rw [b.hilbertDim_eq, Cardinal.mk_le_aleph0_iff, b.separableSpace_iff_countable]

/-- A Hilbert space has Hilbert dimension `ℵ₀` if and only if it is separable and
infinite-dimensional. -/
theorem hilbertDim_eq_aleph0_iff :
    hilbertDim 𝕜 E = ℵ₀ ↔ TopologicalSpace.SeparableSpace E ∧ ¬ FiniteDimensional 𝕜 E := by
  rw [le_antisymm_iff, hilbertDim_le_aleph0_iff, aleph0_le_hilbertDim_iff]

/-- **Classification of separable Hilbert spaces by Hilbert dimension.** Every separable Hilbert
space has Hilbert dimension `0` (the trivial space), a positive natural number `n` (finite
dimension `n`), or `ℵ₀` (separable infinite-dimensional). -/
theorem hilbertDim_eq_zero_or_pos_natCast_or_aleph0 [TopologicalSpace.SeparableSpace E] :
    hilbertDim 𝕜 E = 0 ∨ (∃ n : ℕ, 0 < n ∧ hilbertDim 𝕜 E = n) ∨ hilbertDim 𝕜 E = ℵ₀ := by
  by_cases hfin : FiniteDimensional 𝕜 E
  · by_cases hsub : Subsingleton E
    · exact Or.inl hilbertDim_of_subsingleton
    · have : Nontrivial E := not_subsingleton_iff_nontrivial.1 hsub
      exact Or.inr (Or.inl ⟨Module.finrank 𝕜 E, Module.finrank_pos, hilbertDim_eq_finrank⟩)
  · exact Or.inr (Or.inr (hilbertDim_eq_aleph0_iff.2 ⟨‹_›, hfin⟩))

end Properties

/-- If `f : E → F` is continuous with dense range, then `hilbertDim 𝕜 F ≤ max (hilbertDim 𝕜 E) ℵ₀`
(up to universe lift). -/
theorem lift_hilbertDim_le_max_aleph0_of_denseRange {𝕜 : Type*} {E : Type u} {F : Type v}
    [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
    [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F]
    {f : E → F} (hf : Continuous f) (hd : DenseRange f) :
    Cardinal.lift.{u} (hilbertDim 𝕜 F) ≤ max (Cardinal.lift.{v} (hilbertDim 𝕜 E)) ℵ₀ := by
  obtain ⟨_, bE, -⟩ := exists_hilbertBasis 𝕜 E
  obtain ⟨_, bF, -⟩ := exists_hilbertBasis 𝕜 F
  rw [bE.hilbertDim_eq, bF.hilbertDim_eq]
  exact bE.lift_mk_le_max_aleph0_of_denseRange bF hf hd

end TauCeti

namespace ContinuousLinearEquiv

variable {𝕜 : Type*} [RCLike 𝕜]

/-- **Invariance under continuous linear equivalence.** Any continuous linear equivalence between
Hilbert spaces preserves Hilbert dimension (up to universe lift). -/
theorem lift_hilbertDim_eq {E : Type u} {F : Type v}
    [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
    [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F]
    (e : E ≃L[𝕜] F) :
    Cardinal.lift.{v} (TauCeti.hilbertDim 𝕜 E) = Cardinal.lift.{u} (TauCeti.hilbertDim 𝕜 F) := by
  by_cases hE : FiniteDimensional 𝕜 E
  · have : FiniteDimensional 𝕜 F := e.toLinearEquiv.finiteDimensional
    rw [TauCeti.hilbertDim_eq_finrank, TauCeti.hilbertDim_eq_finrank,
      Cardinal.lift_natCast, Cardinal.lift_natCast, e.toLinearEquiv.finrank_eq]
  · have hF : ¬ FiniteDimensional 𝕜 F := fun h ↦ hE e.symm.toLinearEquiv.finiteDimensional
    have hE_inf : ℵ₀ ≤ Cardinal.lift.{v} (TauCeti.hilbertDim 𝕜 E) := by
      simpa only [Cardinal.lift_aleph0] using
        Cardinal.lift_le.2 (TauCeti.aleph0_le_hilbertDim_iff.2 hE)
    have hF_inf : ℵ₀ ≤ Cardinal.lift.{u} (TauCeti.hilbertDim 𝕜 F) := by
      simpa only [Cardinal.lift_aleph0] using
        Cardinal.lift_le.2 (TauCeti.aleph0_le_hilbertDim_iff.2 hF)
    refine le_antisymm ?_ ?_
    · simpa only [max_eq_left hF_inf] using
        TauCeti.lift_hilbertDim_le_max_aleph0_of_denseRange (𝕜 := 𝕜) (f := e.symm)
          e.symm.continuous e.symm.surjective.denseRange
    · simpa only [max_eq_left hE_inf] using
        TauCeti.lift_hilbertDim_le_max_aleph0_of_denseRange (𝕜 := 𝕜) (f := e)
          e.continuous e.surjective.denseRange

/-- Same-universe continuous linear equivalences preserve Hilbert dimension. -/
theorem hilbertDim_eq {E F : Type u}
    [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
    [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F]
    (e : E ≃L[𝕜] F) :
    TauCeti.hilbertDim 𝕜 E = TauCeti.hilbertDim 𝕜 F := by
  simpa using e.lift_hilbertDim_eq

end ContinuousLinearEquiv

namespace Submodule

/-- A complete subspace of an inner product space has Hilbert dimension `0` if and only if it is
`⊥`. -/
@[simp]
theorem hilbertDim_eq_zero {𝕜 : Type*} {E : Type*} [RCLike 𝕜]
    [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
    {K : Submodule 𝕜 E} [CompleteSpace K] :
    TauCeti.hilbertDim 𝕜 K = 0 ↔ K = ⊥ := by
  rw [TauCeti.hilbertDim_eq_zero_iff, Submodule.subsingleton_iff_eq_bot]

end Submodule

namespace TauCeti

section Separable

/-- Two finite-dimensional inner product spaces over `𝕜` admit a linear isometric equivalence if and
only if they have the same `Module.finrank`. -/
theorem nonempty_linearIsometryEquiv_iff_finrank_eq {𝕜 : Type*} {E : Type u} {F : Type v}
    [RCLike 𝕜]
    [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [FiniteDimensional 𝕜 E]
    [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [FiniteDimensional 𝕜 F] :
    Nonempty (E ≃ₗᵢ[𝕜] F) ↔ Module.finrank 𝕜 E = Module.finrank 𝕜 F :=
  ⟨fun ⟨e⟩ ↦ e.toLinearEquiv.finrank_eq,
   fun h ↦ ⟨(stdOrthonormalBasis 𝕜 E).equiv (stdOrthonormalBasis 𝕜 F) (finCongr h)⟩⟩

/-- Two finite-dimensional inner product spaces over `𝕜` admit no linear isometric equivalence if
and only if their `Module.finrank`s differ. -/
theorem isEmpty_linearIsometryEquiv_iff_finrank_ne {𝕜 : Type*} {E : Type u} {F : Type v}
    [RCLike 𝕜]
    [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [FiniteDimensional 𝕜 E]
    [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [FiniteDimensional 𝕜 F] :
    IsEmpty (E ≃ₗᵢ[𝕜] F) ↔ Module.finrank 𝕜 E ≠ Module.finrank 𝕜 F := by
  rw [← not_nonempty_iff, nonempty_linearIsometryEquiv_iff_finrank_eq]

example (𝕜 : Type u) (ι : Type v) [RCLike 𝕜] [Fintype ι] (hι : Fintype.card ι ≠ 1) :
    IsEmpty (𝕜 ≃ₗᵢ[𝕜] EuclideanSpace 𝕜 ι) :=
  isEmpty_linearIsometryEquiv_iff_finrank_ne.2 (by simpa using hι.symm)

/-- Every separable infinite-dimensional Hilbert space admits a Hilbert basis indexed by `ℕ`. -/
theorem nonempty_hilbertBasis_nat (𝕜 : Type*) (E : Type*) [RCLike 𝕜] [NormedAddCommGroup E]
    [InnerProductSpace 𝕜 E] [CompleteSpace E] [TopologicalSpace.SeparableSpace E]
    (hE : ¬ FiniteDimensional 𝕜 E) : Nonempty (HilbertBasis ℕ 𝕜 E) := by
  obtain ⟨w, b, -⟩ := exists_hilbertBasis 𝕜 E
  obtain ⟨e⟩ := b.nonempty_equiv_nat hE
  exact ⟨b.reindex e⟩

/-- Every separable infinite-dimensional Hilbert space over `𝕜` is linearly isometric to
`ℓ²(ℕ, 𝕜)`. -/
theorem nonempty_linearIsometryEquiv_lp_nat (𝕜 : Type*) (E : Type*) [RCLike 𝕜]
    [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
    [TopologicalSpace.SeparableSpace E] (hE : ¬ FiniteDimensional 𝕜 E) :
    Nonempty (E ≃ₗᵢ[𝕜] ℓ²(ℕ, 𝕜)) :=
  let ⟨b⟩ := nonempty_hilbertBasis_nat 𝕜 E hE
  ⟨b.repr⟩

/-- Any two separable infinite-dimensional Hilbert spaces over the same scalar field `𝕜` are
linearly isometric. -/
theorem nonempty_linearIsometryEquiv_of_separableSpace_of_not_finiteDimensional
    {𝕜 : Type*} {E : Type*} {F : Type*} [RCLike 𝕜]
    [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
    [TopologicalSpace.SeparableSpace E]
    [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F]
    [TopologicalSpace.SeparableSpace F]
    (hE : ¬ FiniteDimensional 𝕜 E) (hF : ¬ FiniteDimensional 𝕜 F) :
    Nonempty (E ≃ₗᵢ[𝕜] F) := by
  obtain ⟨eE⟩ := nonempty_linearIsometryEquiv_lp_nat 𝕜 E hE
  obtain ⟨eF⟩ := nonempty_linearIsometryEquiv_lp_nat 𝕜 F hF
  exact ⟨eE.trans eF.symm⟩

/-- A Hilbert space admits a Hilbert basis indexed by `ℕ` if and only if it is separable and
infinite-dimensional. -/
theorem nonempty_hilbertBasis_nat_iff {𝕜 : Type*} {E : Type u} [RCLike 𝕜]
    [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E] :
    Nonempty (HilbertBasis ℕ 𝕜 E) ↔
      TopologicalSpace.SeparableSpace E ∧ ¬ FiniteDimensional 𝕜 E := by
  rw [nonempty_hilbertBasis_iff_lift_mk_eq, Cardinal.mk_nat, Cardinal.lift_aleph0,
    Cardinal.lift_uzero, eq_comm, hilbertDim_eq_aleph0_iff]

/-- A Hilbert space over `𝕜` is linearly isometrically equivalent to `ℓ²(ℕ, 𝕜)` if and only if
it is separable and infinite-dimensional. -/
theorem nonempty_linearIsometryEquiv_lp_nat_iff {𝕜 : Type w} {E : Type u} [RCLike 𝕜]
    [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E] :
    Nonempty (E ≃ₗᵢ[𝕜] ℓ²(ℕ, 𝕜)) ↔
      TopologicalSpace.SeparableSpace E ∧ ¬ FiniteDimensional 𝕜 E := by
  rw [nonempty_linearIsometryEquiv_iff_lift_hilbertDim_eq, hilbertDim_lp, Cardinal.mk_nat,
    Cardinal.lift_aleph0, Cardinal.lift_aleph0, ← Cardinal.lift_aleph0.{w, u},
    Cardinal.lift_inj, hilbertDim_eq_aleph0_iff]

end Separable

section DirectSums

variable {𝕜 : Type*} [RCLike 𝕜]

/-- The Hilbert dimension of the `L²` product `WithLp 2 (E × F)` is the sum of the lifted Hilbert
dimensions of `E` and `F`. -/
@[simp]
theorem hilbertDim_prodLp {E : Type u} {F : Type v}
    [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
    [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F] :
    hilbertDim 𝕜 (WithLp 2 (E × F)) =
      Cardinal.lift.{v} (hilbertDim 𝕜 E) + Cardinal.lift.{u} (hilbertDim 𝕜 F) := by
  obtain ⟨_, bE, -⟩ := exists_hilbertBasis 𝕜 E
  obtain ⟨_, bF, -⟩ := exists_hilbertBasis 𝕜 F
  rw [(bE.prodLp bF).hilbertDim_eq, Cardinal.mk_sum, bE.hilbertDim_eq, bF.hilbertDim_eq]

/-- Same-universe specialization of `TauCeti.hilbertDim_prodLp`. -/
theorem hilbertDim_prodLp' {E F : Type u}
    [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
    [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F] :
    hilbertDim 𝕜 (WithLp 2 (E × F)) = hilbertDim 𝕜 E + hilbertDim 𝕜 F := by
  simp

/-- **Orthogonal-direct-sum cardinal law.** For a complete submodule `K` of a Hilbert space `E`,
the Hilbert dimensions of `K` and `Kᗮ` sum to the Hilbert dimension of `E`. -/
theorem hilbertDim_add_hilbertDim_orthogonal {E : Type u}
    [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
    (K : Submodule 𝕜 E) [CompleteSpace K] :
    hilbertDim 𝕜 K + hilbertDim 𝕜 Kᗮ = hilbertDim 𝕜 E := by
  rw [← hilbertDim_prodLp', ← K.orthogonalDecomposition.hilbertDim_eq]

/-- The quotient `E ⧸ K` by a closed submodule `K` of a Hilbert space `E` has the same Hilbert
dimension as `Kᗮ`. -/
theorem hilbertDim_quotient_eq_orthogonal {E : Type u}
    [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
    (K : Submodule 𝕜 E) [IsClosed (K : Set E)] :
    hilbertDim 𝕜 (E ⧸ K) = hilbertDim 𝕜 Kᗮ :=
  K.quotientEquivOrthogonal.hilbertDim_eq

/-- For a closed submodule `K` of a Hilbert space `E`, the Hilbert dimensions of `K` and `E ⧸ K`
sum to the Hilbert dimension of `E`. -/
theorem hilbertDim_add_hilbertDim_quotient {E : Type u}
    [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
    (K : Submodule 𝕜 E) [IsClosed (K : Set E)] :
    hilbertDim 𝕜 K + hilbertDim 𝕜 (E ⧸ K) = hilbertDim 𝕜 E := by
  rw [hilbertDim_quotient_eq_orthogonal, hilbertDim_add_hilbertDim_orthogonal]

/-- Taking the orthogonal complement of a finite-dimensional subspace in an infinite-dimensional
Hilbert space does not change the Hilbert dimension. -/
theorem hilbertDim_orthogonal_eq_of_finiteDimensional {E : Type u}
    [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
    (K : Submodule 𝕜 E) [FiniteDimensional 𝕜 K] (hE : ¬ FiniteDimensional 𝕜 E) :
    hilbertDim 𝕜 Kᗮ = hilbertDim 𝕜 E := by
  have hK : hilbertDim 𝕜 K < ℵ₀ := hilbertDim_lt_aleph0_iff.2 inferInstance
  have hsum : hilbertDim 𝕜 K + hilbertDim 𝕜 Kᗮ = hilbertDim 𝕜 E :=
    hilbertDim_add_hilbertDim_orthogonal K
  have hKperp : ℵ₀ ≤ hilbertDim 𝕜 Kᗮ := by
    by_contra h
    push Not at h
    exact hE (hilbertDim_lt_aleph0_iff.1 (hsum ▸ Cardinal.add_lt_aleph0 hK h))
  rw [← hsum, Cardinal.add_eq_right hKperp (hK.le.trans hKperp)]

/-- A complete subspace of finite codimension (meaning finite-dimensional orthogonal complement) in
an infinite-dimensional Hilbert space has the same Hilbert dimension as the ambient space. -/
theorem hilbertDim_eq_of_finiteDimensional_orthogonal {E : Type u}
    [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
    (K : Submodule 𝕜 E) [CompleteSpace K] [FiniteDimensional 𝕜 Kᗮ]
    (hE : ¬ FiniteDimensional 𝕜 E) :
    hilbertDim 𝕜 K = hilbertDim 𝕜 E := by
  rw [← (LinearIsometryEquiv.ofEq _ _ K.orthogonal_orthogonal).hilbertDim_eq]
  exact hilbertDim_orthogonal_eq_of_finiteDimensional Kᗮ hE

end DirectSums

end TauCeti
