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
public import TauCeti.Analysis.Normed.Lp.Basic

/-!
# Hilbert dimension and unitary classification of Hilbert spaces

Any two Hilbert bases of a Hilbert space over `ℝ` or `ℂ` have index types of the same cardinality
(`HilbertBasis.lift_mk_eq`, `HilbertBasis.mk_eq`). For finite bases this reduces to equality of
`Module.finrank` via `HilbertBasis.toOrthonormalBasis`; for infinite bases each vector of one basis
has countable support in the other (`HilbertBasis.countable_support_inner`), and the union of these
supports covers the index type, yielding `#ι ≤ #κ * ℵ₀ = #κ` and hence equality by antisymmetry.

This justifies defining the basis-independent Hilbert dimension `TauCeti.hilbertDim 𝕜 E : Cardinal`
of a complete inner product space `E`, distinct from the algebraic Hamel dimension `Module.rank`
in infinite dimensions (`TauCeti.hilbertDim_le_rank`). Two Hilbert spaces over the same field `𝕜`
are linearly isometrically equivalent if and only if their Hilbert dimensions agree
(`HilbertBasis.nonempty_linearIsometryEquiv_iff_lift_mk_eq`,
`TauCeti.nonempty_linearIsometryEquiv_iff_lift_hilbertDim_eq`,
`TauCeti.nonempty_linearIsometryEquiv_iff_hilbertDim_eq`).

In addition, this file records:
* basis existence at a prescribed index cardinality (`TauCeti.nonempty_hilbertBasis_iff_lift_mk_eq`,
  `TauCeti.nonempty_hilbertBasis_iff_mk_eq`, `TauCeti.nonempty_hilbertBasis_nat_iff`);
* separability characterizations (`HilbertBasis.separableSpace_iff_countable`,
  `TauCeti.hilbertDim_le_aleph0_iff`, `TauCeti.hilbertDim_eq_aleph0_iff`,
  `TauCeti.nonempty_linearIsometryEquiv_lp_nat_iff`);
* invariance of Hilbert dimension under continuous linear equivalences
  (`ContinuousLinearEquiv.lift_hilbertDim_eq`, `ContinuousLinearEquiv.hilbertDim_eq`), via a
  density-character bound for continuous maps with dense range
  (`HilbertBasis.lift_mk_le_max_aleph0_of_denseRange`);
* the cardinal addition laws for `L²` products, orthogonal decompositions, and quotients by
  complete submodules (`TauCeti.hilbertDim_prodLp`, `TauCeti.hilbertDim_add_hilbertDim_orthogonal`,
  `TauCeti.hilbertDim_add_hilbertDim_quotient`,
  `TauCeti.hilbertDim_orthogonal_eq_of_finiteDimensional`).

## References

* J. B. Conway, *A Course in Functional Analysis*, 2nd ed., Springer, 1990, §I.4–I.5.
* M. Reed and B. Simon, *Methods of Modern Mathematical Physics, Vol. I: Functional Analysis*,
  Academic Press, 1980, §II.3.
-/

public section

open scoped Cardinal ENNReal InnerProductSpace lp

universe u v w w'

/-! ### Cardinality invariance and separability for Hilbert bases -/

namespace HilbertBasis

variable {𝕜 : Type*} [RCLike 𝕜]
  {E : Type w} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  {F : Type w'} [NormedAddCommGroup F] [InnerProductSpace 𝕜 F]

/-- The representation of a vector in a Hilbert basis has countable support. -/
theorem countable_support_repr {ι : Type u} (b : HilbertBasis ι 𝕜 E) (x : E) :
    {i | b.repr x i ≠ 0}.Countable :=
  lp.countable_dsupport (b.repr x) (by simp)

/-- Every vector in a Hilbert space has nonzero inner product with at most countably many elements
of a Hilbert basis. -/
theorem countable_support_inner {ι : Type u} (b : HilbertBasis ι 𝕜 E) (x : E) :
    {i | ⟪b i, x⟫_𝕜 ≠ 0}.Countable := by
  simpa only [b.repr_apply_apply] using b.countable_support_repr x

/-- A Hilbert space with a Hilbert basis is subsingleton if and only if the index type is empty. -/
theorem subsingleton_iff_isEmpty {ι : Type u} (b : HilbertBasis ι 𝕜 E) :
    Subsingleton E ↔ IsEmpty ι := by
  refine ⟨fun h ↦ ⟨fun i ↦ b.orthonormal.ne_zero i (Subsingleton.elim _ 0)⟩, fun h ↦ ?_⟩
  refine ⟨fun x y ↦ b.repr.injective (lp.ext <| funext fun i ↦ h.elim i)⟩

/-- A Hilbert space with a Hilbert basis is nontrivial if and only if the index type is nonempty. -/
theorem nontrivial_iff_nonempty {ι : Type u} (b : HilbertBasis ι 𝕜 E) :
    Nontrivial E ↔ Nonempty ι := by
  rw [← not_subsingleton_iff_nontrivial, b.subsingleton_iff_isEmpty, not_isEmpty_iff]

/-- A Hilbert space with a finite Hilbert basis is finite-dimensional. -/
theorem finiteDimensional {ι : Type u} [Finite ι] (b : HilbertBasis ι 𝕜 E) :
    FiniteDimensional 𝕜 E := by
  cases nonempty_fintype ι
  exact b.toOrthonormalBasis.toBasis.finiteDimensional_of_finite

/-- A Hilbert basis of a finite-dimensional space has finite index type. -/
theorem finite_of_finiteDimensional {ι : Type u} [FiniteDimensional 𝕜 E]
    (b : HilbertBasis ι 𝕜 E) : Finite ι := by
  have hlt : Cardinal.lift.{w} #ι < ℵ₀ := by
    refine b.orthonormal.linearIndependent.cardinal_lift_le_rank.trans_lt ?_
    simpa only [Cardinal.lift_aleph0] using
      Cardinal.lift_lt.2 (Module.rank_lt_aleph0 𝕜 E)
  rw [← Cardinal.lift_aleph0.{w, u}, Cardinal.lift_lt, Cardinal.lt_aleph0_iff_finite] at hlt
  exact hlt

/-- A Hilbert space with a Hilbert basis is finite-dimensional if and only if the basis index type
is finite. -/
theorem finite_iff_finiteDimensional {ι : Type u} (b : HilbertBasis ι 𝕜 E) :
    Finite ι ↔ FiniteDimensional 𝕜 E :=
  ⟨fun _ ↦ b.finiteDimensional, fun _ ↦ b.finite_of_finiteDimensional⟩

/-- For a Hilbert basis with a `Fintype` index, `Module.finrank 𝕜 E` equals `Fintype.card ι`. -/
theorem finrank_eq_card {ι : Type u} [Fintype ι] (b : HilbertBasis ι 𝕜 E) :
    Module.finrank 𝕜 E = Fintype.card ι :=
  Module.finrank_eq_card_basis b.toOrthonormalBasis.toBasis

/-- For any Hilbert basis `b : HilbertBasis ι 𝕜 E`, `Module.finrank 𝕜 E = Nat.card ι` (both are `0`
in the infinite-dimensional case). -/
theorem finrank_eq_natCard {ι : Type u} (b : HilbertBasis ι 𝕜 E) :
    Module.finrank 𝕜 E = Nat.card ι := by
  by_cases hι : Finite ι
  · have := Fintype.ofFinite ι
    rw [b.finrank_eq_card, Nat.card_eq_fintype_card]
  · have : Infinite ι := not_finite_iff_infinite.1 hι
    rw [Module.finrank_of_infinite_dimensional (mt b.finite_iff_finiteDimensional.2 hι),
      Nat.card_eq_zero_of_infinite]

private theorem lift_mk_le_of_infinite {ι : Type u} {κ : Type v}
    (b : HilbertBasis ι 𝕜 E) (c : HilbertBasis κ 𝕜 E) [Infinite κ] :
    Cardinal.lift.{v} #ι ≤ Cardinal.lift.{u} #κ := by
  have hcov : (Set.univ : Set ι) = ⋃ j : κ, {i : ι | ⟪b i, c j⟫_𝕜 ≠ 0} := by
    ext i
    simp only [Set.mem_univ, Set.mem_iUnion, Set.mem_ofPred_eq, true_iff]
    by_contra h
    push Not at h
    have hzero : b i = 0 := c.repr.injective (lp.ext <| funext fun j ↦ by
      rw [c.repr_apply_apply, map_zero, lp.coeFn_zero, Pi.zero_apply,
        inner_eq_zero_symm.2 (h j)])
    exact b.orthonormal.ne_zero i hzero
  have hcard : Cardinal.lift.{v} #ι ≤
      Cardinal.lift.{u} #κ * ⨆ j : κ, Cardinal.lift.{v} #({i : ι | ⟪b i, c j⟫_𝕜 ≠ 0}) := by
    simpa only [← hcov, Cardinal.mk_univ] using
      Cardinal.mk_iUnion_le_lift (fun j : κ ↦ {i : ι | ⟪b i, c j⟫_𝕜 ≠ 0})
  have hsup : (⨆ j : κ, Cardinal.lift.{v} #({i : ι | ⟪b i, c j⟫_𝕜 ≠ 0})) ≤ ℵ₀ := by
    refine ciSup_le' fun j ↦ ?_
    have hct : #({i : ι | ⟪b i, c j⟫_𝕜 ≠ 0}) ≤ ℵ₀ :=
      Cardinal.le_aleph0_iff_set_countable.2 (b.countable_support_inner (c j))
    simpa only [Cardinal.lift_aleph0] using Cardinal.lift_le.2 hct
  calc Cardinal.lift.{v} #ι
      ≤ Cardinal.lift.{u} #κ * ⨆ j : κ, Cardinal.lift.{v} #({i : ι | ⟪b i, c j⟫_𝕜 ≠ 0}) := hcard
    _ ≤ Cardinal.lift.{u} #κ * ℵ₀ := by gcongr
    _ = Cardinal.lift.{u} #κ := Cardinal.mul_aleph0_eq (by
        simpa only [Cardinal.lift_aleph0] using Cardinal.lift_le.2 (Cardinal.aleph0_le_mk κ))

/-- **Basis-cardinality invariance.** Any two Hilbert bases of the same inner product space have
index types of the same cardinality (up to universe lift). -/
theorem lift_mk_eq {ι : Type u} {κ : Type v}
    (b : HilbertBasis ι 𝕜 E) (c : HilbertBasis κ 𝕜 E) :
    Cardinal.lift.{v} #ι = Cardinal.lift.{u} #κ := by
  by_cases hι : Finite ι
  · have : FiniteDimensional 𝕜 E := b.finite_iff_finiteDimensional.1 hι
    have : Finite κ := c.finite_iff_finiteDimensional.2 inferInstance
    have := Fintype.ofFinite ι
    have := Fintype.ofFinite κ
    rw [Cardinal.mk_fintype, Cardinal.mk_fintype, Cardinal.lift_natCast, Cardinal.lift_natCast,
      ← b.finrank_eq_card, ← c.finrank_eq_card]
  · have : Infinite ι := not_finite_iff_infinite.1 hι
    have hκ : ¬ Finite κ := fun h ↦ hι
      (b.finite_iff_finiteDimensional.2 (c.finite_iff_finiteDimensional.1 h))
    have : Infinite κ := not_finite_iff_infinite.1 hκ
    exact le_antisymm (b.lift_mk_le_of_infinite c) (c.lift_mk_le_of_infinite b)

/-- Same-universe specialization of `HilbertBasis.lift_mk_eq`: any two Hilbert bases of `E` indexed
by types in the same universe have equal cardinality. -/
theorem mk_eq {ι κ : Type u} (b : HilbertBasis ι 𝕜 E) (c : HilbertBasis κ 𝕜 E) : #ι = #κ := by
  simpa only [Cardinal.lift_id] using b.lift_mk_eq c

/-- A linear isometric equivalence between spaces with Hilbert bases implies their index types have
the same cardinality. -/
theorem lift_mk_eq_of_linearIsometryEquiv {ι : Type u} {κ : Type v}
    (b : HilbertBasis ι 𝕜 E) (c : HilbertBasis κ 𝕜 F) (U : E ≃ₗᵢ[𝕜] F) :
    Cardinal.lift.{v} #ι = Cardinal.lift.{u} #κ :=
  (b.mapₗᵢ U).lift_mk_eq c

/-- **Unitary classification in terms of Hilbert bases.** Two Hilbert spaces equipped with Hilbert
bases are linearly isometrically equivalent if and only if their basis index types have the same
cardinality. -/
theorem nonempty_linearIsometryEquiv_iff_lift_mk_eq {ι : Type u} {κ : Type v}
    (b : HilbertBasis ι 𝕜 E) (c : HilbertBasis κ 𝕜 F) :
    Nonempty (E ≃ₗᵢ[𝕜] F) ↔ Cardinal.lift.{v} #ι = Cardinal.lift.{u} #κ :=
  ⟨fun ⟨U⟩ ↦ b.lift_mk_eq_of_linearIsometryEquiv c U, fun h ↦
    let ⟨e⟩ := Cardinal.lift_mk_eq'.1 h
    ⟨b.equiv c e⟩⟩

/-- Same-universe specialization of `HilbertBasis.nonempty_linearIsometryEquiv_iff_lift_mk_eq`. -/
theorem nonempty_linearIsometryEquiv_iff_mk_eq {ι κ : Type u}
    (b : HilbertBasis ι 𝕜 E) (c : HilbertBasis κ 𝕜 F) :
    Nonempty (E ≃ₗᵢ[𝕜] F) ↔ #ι = #κ := by
  simpa only [Cardinal.lift_id] using b.nonempty_linearIsometryEquiv_iff_lift_mk_eq c

/-- A Hilbert space with a Hilbert basis is separable if and only if the index type is countable. -/
theorem separableSpace_iff_countable {ι : Type u} (b : HilbertBasis ι 𝕜 E) :
    TopologicalSpace.SeparableSpace E ↔ Countable ι := by
  have : ProperSpace 𝕜 := FiniteDimensional.proper_rclike 𝕜 𝕜
  have hhomeo : TopologicalSpace.SeparableSpace E ↔ TopologicalSpace.SeparableSpace ℓ²(ι, 𝕜) :=
    ⟨fun _ ↦ b.repr.surjective.denseRange.separableSpace b.repr.continuous,
      fun _ ↦ b.repr.symm.surjective.denseRange.separableSpace b.repr.symm.continuous⟩
  rw [hhomeo, lp.separableSpace_iff_countable (by simp)]

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

end HilbertBasis

/-! ### Hilbert dimension -/

namespace TauCeti

variable (𝕜 : Type*) [RCLike 𝕜]

/-- The **Hilbert dimension** of a Hilbert space `E` over `𝕜`: the cardinality of any Hilbert basis
of `E`. This is independent of the choice of Hilbert basis (`HilbertBasis.lift_mk_eq_hilbertDim`),
agrees with `Module.finrank 𝕜 E` in finite dimensions (`hilbertDim_eq_finrank`), and is strictly
smaller than the algebraic Hamel dimension `Module.rank 𝕜 E` in infinite dimensions (for example,
`hilbertDim 𝕜 ℓ²(ℕ, 𝕜) = ℵ₀`). -/
noncomputable def hilbertDim (E : Type u) [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
    [CompleteSpace E] : Cardinal.{u} :=
  #(exists_hilbertBasis 𝕜 E).choose

section Basic

variable {𝕜} {E : Type u} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
  {F : Type v} [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F]

/-- Every Hilbert basis of `E` has index cardinality equal to `hilbertDim 𝕜 E` (up to universe
lift). -/
theorem _root_.HilbertBasis.lift_mk_eq_hilbertDim {ι : Type v} (b : HilbertBasis ι 𝕜 E) :
    Cardinal.lift.{u} #ι = Cardinal.lift.{v} (hilbertDim 𝕜 E) :=
  b.lift_mk_eq (exists_hilbertBasis 𝕜 E).choose_spec.choose

/-- Same-universe specialization of `HilbertBasis.lift_mk_eq_hilbertDim`. -/
theorem _root_.HilbertBasis.mk_eq_hilbertDim {ι : Type u} (b : HilbertBasis ι 𝕜 E) :
    #ι = hilbertDim 𝕜 E := by
  simpa only [Cardinal.lift_id] using b.lift_mk_eq_hilbertDim

/-- A Hilbert space `E` admits a Hilbert basis indexed by `ι` if and only if `#ι` equals
`hilbertDim 𝕜 E` (up to universe lift). -/
theorem nonempty_hilbertBasis_iff_lift_mk_eq {ι : Type v} :
    Nonempty (HilbertBasis ι 𝕜 E) ↔ Cardinal.lift.{u} #ι = Cardinal.lift.{v} (hilbertDim 𝕜 E) := by
  refine ⟨fun ⟨b⟩ ↦ b.lift_mk_eq_hilbertDim, fun h ↦ ?_⟩
  obtain ⟨w, b, -⟩ := exists_hilbertBasis 𝕜 E
  rw [← b.mk_eq_hilbertDim] at h
  obtain ⟨e⟩ := Cardinal.lift_mk_eq'.1 h
  exact ⟨b.reindex e.symm⟩

/-- Same-universe specialization of `nonempty_hilbertBasis_iff_lift_mk_eq`. -/
theorem nonempty_hilbertBasis_iff_mk_eq {ι : Type u} :
    Nonempty (HilbertBasis ι 𝕜 E) ↔ #ι = hilbertDim 𝕜 E := by
  simpa only [Cardinal.lift_id] using
    nonempty_hilbertBasis_iff_lift_mk_eq (𝕜 := 𝕜) (E := E) (ι := ι)

/-- The Hilbert dimension of `ℓ²(S, 𝕜)` is `#S` (lifted to the universe of `ℓ²(S, 𝕜)`). -/
@[simp]
theorem hilbertDim_lp (𝕜 : Type v) (S : Type u) [RCLike 𝕜] :
    hilbertDim 𝕜 ℓ²(S, 𝕜) = Cardinal.lift.{v} #S := by
  have h := (default : HilbertBasis S 𝕜 ℓ²(S, 𝕜)).lift_mk_eq_hilbertDim
  rw [Cardinal.lift_id'.{u, max u v}] at h
  rw [← h, ← Cardinal.lift_lift.{u, v, u}, Cardinal.lift_id]

/-- Linear isometric equivalences preserve Hilbert dimension (up to universe lift). -/
theorem _root_.LinearIsometryEquiv.lift_hilbertDim_eq (U : E ≃ₗᵢ[𝕜] F) :
    Cardinal.lift.{v} (hilbertDim 𝕜 E) = Cardinal.lift.{u} (hilbertDim 𝕜 F) := by
  obtain ⟨wE, bE, -⟩ := exists_hilbertBasis 𝕜 E
  obtain ⟨wF, bF, -⟩ := exists_hilbertBasis 𝕜 F
  rw [← bE.mk_eq_hilbertDim, ← bF.mk_eq_hilbertDim]
  exact bE.lift_mk_eq_of_linearIsometryEquiv bF U

/-- Same-universe linear isometric equivalences preserve Hilbert dimension. -/
theorem _root_.LinearIsometryEquiv.hilbertDim_eq {F : Type u} [NormedAddCommGroup F]
    [InnerProductSpace 𝕜 F] [CompleteSpace F] (U : E ≃ₗᵢ[𝕜] F) :
    hilbertDim 𝕜 E = hilbertDim 𝕜 F := by
  simpa only [Cardinal.lift_id] using U.lift_hilbertDim_eq

/-- **Unitary classification of Hilbert spaces.** Two Hilbert spaces over `𝕜` are linearly
isometrically equivalent if and only if their Hilbert dimensions agree (up to universe lift). -/
theorem nonempty_linearIsometryEquiv_iff_lift_hilbertDim_eq :
    Nonempty (E ≃ₗᵢ[𝕜] F) ↔
      Cardinal.lift.{v} (hilbertDim 𝕜 E) = Cardinal.lift.{u} (hilbertDim 𝕜 F) := by
  obtain ⟨wE, bE, -⟩ := exists_hilbertBasis 𝕜 E
  obtain ⟨wF, bF, -⟩ := exists_hilbertBasis 𝕜 F
  rw [← bE.mk_eq_hilbertDim, ← bF.mk_eq_hilbertDim]
  exact bE.nonempty_linearIsometryEquiv_iff_lift_mk_eq bF

/-- Same-universe specialization of `nonempty_linearIsometryEquiv_iff_lift_hilbertDim_eq`. -/
theorem nonempty_linearIsometryEquiv_iff_hilbertDim_eq {F : Type u} [NormedAddCommGroup F]
    [InnerProductSpace 𝕜 F] [CompleteSpace F] :
    Nonempty (E ≃ₗᵢ[𝕜] F) ↔ hilbertDim 𝕜 E = hilbertDim 𝕜 F := by
  simpa only [Cardinal.lift_id] using
    nonempty_linearIsometryEquiv_iff_lift_hilbertDim_eq (𝕜 := 𝕜) (E := E) (F := F)

/-- In finite dimensions, `hilbertDim 𝕜 E` equals `Module.finrank 𝕜 E`. -/
theorem hilbertDim_eq_finrank [FiniteDimensional 𝕜 E] :
    hilbertDim 𝕜 E = Module.finrank 𝕜 E := by
  obtain ⟨w, b, -⟩ := exists_hilbertBasis 𝕜 E
  have : Finite w := b.finite_of_finiteDimensional
  have := Fintype.ofFinite w
  rw [← b.mk_eq_hilbertDim, Cardinal.mk_fintype, b.finrank_eq_card]

/-- The Hilbert dimension of the base field `𝕜` over itself is `1`. -/
@[simp]
theorem hilbertDim_self (𝕜 : Type u) [RCLike 𝕜] : hilbertDim 𝕜 𝕜 = 1 := by
  rw [hilbertDim_eq_finrank, Module.finrank_self, Nat.cast_one]

/-- A Hilbert space is finite-dimensional if and only if its Hilbert dimension is strictly less
than `ℵ₀`. -/
theorem hilbertDim_lt_aleph0_iff : hilbertDim 𝕜 E < ℵ₀ ↔ FiniteDimensional 𝕜 E := by
  obtain ⟨w, b, -⟩ := exists_hilbertBasis 𝕜 E
  rw [← b.mk_eq_hilbertDim, Cardinal.lt_aleph0_iff_finite, b.finite_iff_finiteDimensional]

/-- A Hilbert space is infinite-dimensional if and only if its Hilbert dimension is at least `ℵ₀`.
-/
theorem aleph0_le_hilbertDim_iff : ℵ₀ ≤ hilbertDim 𝕜 E ↔ ¬ FiniteDimensional 𝕜 E := by
  rw [← not_lt, hilbertDim_lt_aleph0_iff]

/-- A Hilbert space has Hilbert dimension `0` if and only if it is subsingleton. -/
@[simp]
theorem hilbertDim_eq_zero_iff : hilbertDim 𝕜 E = 0 ↔ Subsingleton E := by
  obtain ⟨w, b, -⟩ := exists_hilbertBasis 𝕜 E
  rw [← b.mk_eq_hilbertDim, Cardinal.mk_eq_zero_iff, b.subsingleton_iff_isEmpty]

/-- A Hilbert space has positive Hilbert dimension if and only if it is nontrivial. -/
@[simp]
theorem hilbertDim_pos_iff : 0 < hilbertDim 𝕜 E ↔ Nontrivial E := by
  rw [pos_iff_ne_zero, ne_eq, hilbertDim_eq_zero_iff, not_subsingleton_iff_nontrivial]

/-- A Hilbert space is separable if and only if its Hilbert dimension is at most `ℵ₀`. -/
theorem hilbertDim_le_aleph0_iff :
    hilbertDim 𝕜 E ≤ ℵ₀ ↔ TopologicalSpace.SeparableSpace E := by
  obtain ⟨w, b, -⟩ := exists_hilbertBasis 𝕜 E
  rw [← b.mk_eq_hilbertDim, Cardinal.mk_le_aleph0_iff, b.separableSpace_iff_countable]

/-- A Hilbert space has Hilbert dimension `ℵ₀` if and only if it is separable and
infinite-dimensional. -/
theorem hilbertDim_eq_aleph0_iff :
    hilbertDim 𝕜 E = ℵ₀ ↔ TopologicalSpace.SeparableSpace E ∧ ¬ FiniteDimensional 𝕜 E := by
  rw [le_antisymm_iff, hilbertDim_le_aleph0_iff, aleph0_le_hilbertDim_iff]

/-- A Hilbert space admits a Hilbert basis indexed by `ℕ` if and only if it is separable and
infinite-dimensional. -/
theorem nonempty_hilbertBasis_nat_iff :
    Nonempty (HilbertBasis ℕ 𝕜 E) ↔
      TopologicalSpace.SeparableSpace E ∧ ¬ FiniteDimensional 𝕜 E := by
  rw [nonempty_hilbertBasis_iff_lift_mk_eq, Cardinal.mk_nat, Cardinal.lift_aleph0,
    Cardinal.lift_uzero, eq_comm, hilbertDim_eq_aleph0_iff]

/-- Every separable infinite-dimensional Hilbert space over `𝕜` is linearly isometrically
equivalent to `ℓ²(ℕ, 𝕜)`, and conversely. -/
theorem nonempty_linearIsometryEquiv_lp_nat_iff :
    Nonempty (E ≃ₗᵢ[𝕜] ℓ²(ℕ, 𝕜)) ↔
      TopologicalSpace.SeparableSpace E ∧ ¬ FiniteDimensional 𝕜 E := by
  rw [nonempty_linearIsometryEquiv_iff_lift_hilbertDim_eq, hilbertDim_lp, Cardinal.mk_nat,
    Cardinal.lift_aleph0, Cardinal.lift_aleph0, ← Cardinal.lift_aleph0.{_, u},
    Cardinal.lift_inj, hilbertDim_eq_aleph0_iff]

/-- The Hilbert dimension of a Hilbert space never exceeds its algebraic Hamel dimension. -/
theorem hilbertDim_le_rank : hilbertDim 𝕜 E ≤ Module.rank 𝕜 E := by
  obtain ⟨w, b, -⟩ := exists_hilbertBasis 𝕜 E
  rw [← b.mk_eq_hilbertDim]
  exact b.orthonormal.linearIndependent.cardinal_le_rank

/-- If `f : E → F` is continuous with dense range, then `hilbertDim 𝕜 F ≤ max (hilbertDim 𝕜 E) ℵ₀`
(up to universe lift). -/
theorem lift_hilbertDim_le_max_aleph0_of_denseRange {f : E → F}
    (hf : Continuous f) (hd : DenseRange f) :
    Cardinal.lift.{u} (hilbertDim 𝕜 F) ≤ max (Cardinal.lift.{v} (hilbertDim 𝕜 E)) ℵ₀ := by
  obtain ⟨wE, bE, -⟩ := exists_hilbertBasis 𝕜 E
  obtain ⟨wF, bF, -⟩ := exists_hilbertBasis 𝕜 F
  rw [← bE.mk_eq_hilbertDim, ← bF.mk_eq_hilbertDim]
  exact bE.lift_mk_le_max_aleph0_of_denseRange bF hf hd

/-- **Invariance under continuous linear equivalence.** Any continuous linear equivalence between
Hilbert spaces preserves Hilbert dimension (up to universe lift). -/
theorem _root_.ContinuousLinearEquiv.lift_hilbertDim_eq (e : E ≃L[𝕜] F) :
    Cardinal.lift.{v} (hilbertDim 𝕜 E) = Cardinal.lift.{u} (hilbertDim 𝕜 F) := by
  by_cases hE : FiniteDimensional 𝕜 E
  · have : FiniteDimensional 𝕜 F := e.toLinearEquiv.finiteDimensional
    rw [hilbertDim_eq_finrank, hilbertDim_eq_finrank, Cardinal.lift_natCast, Cardinal.lift_natCast,
      e.toLinearEquiv.finrank_eq]
  · have hF : ¬ FiniteDimensional 𝕜 F := fun h ↦ hE e.symm.toLinearEquiv.finiteDimensional
    have hE_inf : ℵ₀ ≤ Cardinal.lift.{v} (hilbertDim 𝕜 E) := by
      simpa only [Cardinal.lift_aleph0] using
        Cardinal.lift_le.2 (aleph0_le_hilbertDim_iff.2 hE)
    have hF_inf : ℵ₀ ≤ Cardinal.lift.{u} (hilbertDim 𝕜 F) := by
      simpa only [Cardinal.lift_aleph0] using
        Cardinal.lift_le.2 (aleph0_le_hilbertDim_iff.2 hF)
    refine le_antisymm ?_ ?_
    · simpa only [max_eq_left hF_inf] using
        lift_hilbertDim_le_max_aleph0_of_denseRange (𝕜 := 𝕜) (f := e.symm)
          e.symm.continuous e.symm.surjective.denseRange
    · simpa only [max_eq_left hE_inf] using
        lift_hilbertDim_le_max_aleph0_of_denseRange (𝕜 := 𝕜) (f := e)
          e.continuous e.surjective.denseRange

/-- Same-universe continuous linear equivalences preserve Hilbert dimension. -/
theorem _root_.ContinuousLinearEquiv.hilbertDim_eq {F : Type u} [NormedAddCommGroup F]
    [InnerProductSpace 𝕜 F] [CompleteSpace F] (e : E ≃L[𝕜] F) :
    hilbertDim 𝕜 E = hilbertDim 𝕜 F := by
  simpa only [Cardinal.lift_id] using e.lift_hilbertDim_eq

/-! ### Direct sums, orthogonal complements, and quotients -/

/-- The Hilbert dimension of the `L²` product `WithLp 2 (E × F)` is the sum of the lifted Hilbert
dimensions of `E` and `F`. -/
@[simp]
theorem hilbertDim_prodLp :
    hilbertDim 𝕜 (WithLp 2 (E × F)) =
      Cardinal.lift.{v} (hilbertDim 𝕜 E) + Cardinal.lift.{u} (hilbertDim 𝕜 F) := by
  obtain ⟨wE, bE, -⟩ := exists_hilbertBasis 𝕜 E
  obtain ⟨wF, bF, -⟩ := exists_hilbertBasis 𝕜 F
  rw [← (bE.prod bF).mk_eq_hilbertDim, ← bE.mk_eq_hilbertDim, ← bF.mk_eq_hilbertDim,
    Cardinal.mk_sum]

/-- Same-universe specialization of `hilbertDim_prodLp`. -/
theorem hilbertDim_prodLp' {F : Type u} [NormedAddCommGroup F] [InnerProductSpace 𝕜 F]
    [CompleteSpace F] :
    hilbertDim 𝕜 (WithLp 2 (E × F)) = hilbertDim 𝕜 E + hilbertDim 𝕜 F := by
  simp

/-- **Orthogonal-direct-sum cardinal law.** For a complete submodule `K` of a Hilbert space `E`,
the Hilbert dimensions of `K` and `Kᗮ` sum to the Hilbert dimension of `E`. -/
theorem hilbertDim_add_hilbertDim_orthogonal (K : Submodule 𝕜 E) [CompleteSpace K] :
    hilbertDim 𝕜 K + hilbertDim 𝕜 Kᗮ = hilbertDim 𝕜 E := by
  rw [← hilbertDim_prodLp', ← K.orthogonalDecomposition.hilbertDim_eq]

/-- The Hilbert dimension of a complete submodule is at most the Hilbert dimension of the ambient
Hilbert space. -/
theorem hilbertDim_le_of_submodule (K : Submodule 𝕜 E) [CompleteSpace K] :
    hilbertDim 𝕜 K ≤ hilbertDim 𝕜 E := by
  rw [← hilbertDim_add_hilbertDim_orthogonal K]
  exact le_self_add

/-- The quotient `E ⧸ K` by a closed submodule `K` with orthogonal projection has the same Hilbert
dimension as `Kᗮ`. -/
theorem hilbertDim_quotient_eq_orthogonal (K : Submodule 𝕜 E) [K.HasOrthogonalProjection]
    [IsClosed (K : Set E)] :
    hilbertDim 𝕜 (E ⧸ K) = hilbertDim 𝕜 Kᗮ :=
  K.quotientEquivOrthogonal.hilbertDim_eq

/-- For a complete closed submodule `K` of a Hilbert space `E`, the Hilbert dimensions of `K` and
`E ⧸ K` sum to the Hilbert dimension of `E`. -/
theorem hilbertDim_add_hilbertDim_quotient (K : Submodule 𝕜 E) [CompleteSpace K]
    [IsClosed (K : Set E)] :
    hilbertDim 𝕜 K + hilbertDim 𝕜 (E ⧸ K) = hilbertDim 𝕜 E := by
  rw [hilbertDim_quotient_eq_orthogonal, hilbertDim_add_hilbertDim_orthogonal]

/-- Taking the orthogonal complement of a finite-dimensional subspace in an infinite-dimensional
Hilbert space does not change the Hilbert dimension. -/
theorem hilbertDim_orthogonal_eq_of_finiteDimensional (K : Submodule 𝕜 E) [FiniteDimensional 𝕜 K]
    (hE : ¬ FiniteDimensional 𝕜 E) :
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
theorem hilbertDim_eq_of_finiteDimensional_orthogonal (K : Submodule 𝕜 E) [CompleteSpace K]
    [FiniteDimensional 𝕜 Kᗮ] (hE : ¬ FiniteDimensional 𝕜 E) :
    hilbertDim 𝕜 K = hilbertDim 𝕜 E := by
  rw [← (LinearIsometryEquiv.ofEq _ _ K.orthogonal_orthogonal).hilbertDim_eq]
  exact hilbertDim_orthogonal_eq_of_finiteDimensional Kᗮ hE

end Basic

end TauCeti
