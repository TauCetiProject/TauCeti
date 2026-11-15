/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.LinearAlgebra.Dimension.StrongRankCondition
public import Mathlib.SetTheory.Cardinal.Arithmetic
public import TauCeti.Analysis.InnerProductSpace.HilbertBasis.Reindex
public import TauCeti.Analysis.InnerProductSpace.Orthonormal.Basic
public import TauCeti.Analysis.Normed.Lp.Basic
import TauCeti.Analysis.InnerProductSpace.HilbertBasis.Basic

/-!
# Hilbert dimension and unitary classification of Hilbert spaces

Any two Hilbert bases `b : HilbertBasis ι 𝕜 E` and `c : HilbertBasis κ 𝕜 E` of a Hilbert space
have equal lifted index cardinalities, `Cardinal.lift #ι = Cardinal.lift #κ`
(`HilbertBasis.lift_mk_eq`). Indeed, any orthonormal family in `E` has lifted index cardinality at
most that of any Hilbert basis (`Orthonormal.cardinal_lift_le_hilbertBasis`): when `κ` is finite
this reduces to linear algebra via `HilbertBasis.toOrthonormalBasis`, while when `κ` is infinite
each `c j` has countably many nonzero inner products with the family and completeness of `c` forces
their union over `j` to cover the index type.

We define `TauCeti.hilbertDim 𝕜 E : Cardinal` as the basis-independent cardinal of any Hilbert
basis of a complete `𝕜`-inner product space `E` (`HilbertBasis.mk_eq_hilbertDim`). Unlike the
algebraic Hamel dimension `Module.rank` (which equals the continuum on `ℓ²(ℕ, 𝕜)`), `hilbertDim`
agrees with `Module.finrank` in finite dimension (`TauCeti.hilbertDim_eq_finrank`), equals `#ι`
(up to universe lift) on `ℓ²(ι, 𝕜)` (`TauCeti.hilbertDim_lp`), and equals the supremum of
cardinalities of orthonormal subsets of `E` (`TauCeti.hilbertDim_eq_ciSup_orthonormal`).

Hilbert dimension increases along linear isometries (`LinearIsometry.lift_hilbertDim_le`), decreases
along continuous linear maps with dense range (`TauCeti.lift_hilbertDim_le_of_denseRange`), and is
therefore invariant under both linear isometric equivalences and continuous linear equivalences
(`LinearIsometryEquiv.lift_hilbertDim_eq`, `ContinuousLinearEquiv.lift_hilbertDim_eq`). Two Hilbert
spaces over `𝕜` admit a linear isometric equivalence (equivalently, a continuous linear equivalence)
if and only if their Hilbert dimensions agree
(`HilbertBasis.nonempty_linearIsometryEquiv_iff_lift_mk_eq`,
`TauCeti.nonempty_linearIsometryEquiv_iff_lift_hilbertDim_eq`,
`TauCeti.nonempty_continuousLinearEquiv_iff_nonempty_linearIsometryEquiv`). A Hilbert space is
separable if and only if any Hilbert basis is countable (`HilbertBasis.separableSpace_iff`),
equivalently `hilbertDim 𝕜 E ≤ ℵ₀` (`TauCeti.separableSpace_iff_hilbertDim_le_aleph0`), and every
separable infinite-dimensional Hilbert space is unitarily equivalent to `ℓ²(ℕ, 𝕜)`
(`TauCeti.nonempty_linearIsometryEquiv_lp_nat`).

## References

* P. R. Halmos, *A Hilbert Space Problem Book*, 2nd ed., Springer, 1982, Chapter 1.
* J. B. Conway, *A Course in Functional Analysis*, 2nd ed., Springer, 1990, §I.4.
-/

public section

open scoped Cardinal InnerProductSpace lp

universe u u' v w

section OrthonormalBound

variable {𝕜 : Type*} {E : Type u} {F : Type u'} [RCLike 𝕜]
  [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [NormedAddCommGroup F] [InnerProductSpace 𝕜 F]

/-- If `f : E →L[𝕜] F` has dense range and `c : HilbertBasis κ 𝕜 E`, any orthonormal family in `F`
indexed by `ι` satisfies `Cardinal.lift #ι ≤ Cardinal.lift #κ`. -/
theorem Orthonormal.cardinal_lift_le_hilbertBasis_of_denseRange {ι : Type v} {κ : Type w}
    {v : ι → F} (hv : Orthonormal 𝕜 v) (c : HilbertBasis κ 𝕜 E) (f : E →L[𝕜] F)
    (hf : DenseRange f) :
    Cardinal.lift.{w} #ι ≤ Cardinal.lift.{v} #κ := by
  by_cases hκ : Finite κ
  · cases nonempty_fintype κ
    have : FiniteDimensional 𝕜 E := Module.Finite.of_basis c.toOrthonormalBasis.toBasis
    have hclosed : IsClosed (Set.range f) := by
      simpa only [LinearMap.coe_range, ContinuousLinearMap.coe_coe] using
        (LinearMap.range (f : E →ₗ[𝕜] F)).isClosed_of_finiteDimensional
    have hsurj : Function.Surjective f := Set.range_eq_univ.1 (hclosed.closure_eq ▸ hf.closure_eq)
    rw [← Cardinal.lift_le.{max u u'}, Cardinal.lift_lift, Cardinal.lift_lift]
    calc
      Cardinal.lift.{max w (max u u')} #ι
        = Cardinal.lift.{max w u} (Cardinal.lift.{u'} #ι) := (Cardinal.lift_lift #ι).symm
      _ ≤ Cardinal.lift.{max w u} (Cardinal.lift.{v} (Module.rank 𝕜 F)) :=
          Cardinal.lift_le.2 hv.linearIndependent.cardinal_lift_le_rank
      _ = Cardinal.lift.{max v w} (Cardinal.lift.{u} (Module.rank 𝕜 F)) := by
          simp only [Cardinal.lift_lift]
      _ ≤ Cardinal.lift.{max v w} (Cardinal.lift.{u'} (Module.rank 𝕜 E)) :=
          Cardinal.lift_le.2 (LinearMap.lift_rank_le_of_surjective (f : E →ₗ[𝕜] F) hsurj)
      _ = Cardinal.lift.{max v u'} (Cardinal.lift.{w} (Module.rank 𝕜 E)) := by
          simp only [Cardinal.lift_lift]
      _ = Cardinal.lift.{max v u'} (Cardinal.lift.{u} #κ) := by
          rw [← c.toOrthonormalBasis.toBasis.mk_eq_rank]
      _ = Cardinal.lift.{max v (max u u')} #κ := Cardinal.lift_lift #κ
  · have : Infinite κ := not_finite_iff_infinite.1 hκ
    let S : κ → Set ι := fun j ↦ {i : ι | ⟪v i, f (c j)⟫_𝕜 ≠ 0}
    have hS_univ : ⋃ j : κ, S j = Set.univ := by
      refine Set.eq_univ_of_forall fun i ↦ ?_
      by_contra hi
      let φ : F →L[𝕜] 𝕜 := innerSL 𝕜 (v i)
      have hφf : φ.comp f = 0 := c.ext_continuousLinearMap fun j ↦
        not_ne_iff.1 fun hne ↦ hi (Set.mem_iUnion.2 ⟨j, hne⟩)
      have hφ : ⇑φ = 0 :=
        hf.equalizer φ.continuous continuous_zero (congrArg DFunLike.coe hφf)
      have hvi : ⟪v i, v i⟫_𝕜 = 0 := congrFun hφ (v i)
      exact hv.ne_zero i (inner_self_eq_zero.1 hvi)
    calc
      Cardinal.lift.{w} #ι
        = Cardinal.lift.{w} #(Set.univ : Set ι) := by rw [Cardinal.mk_univ]
      _ = Cardinal.lift.{w} #(⋃ j : κ, S j) := by rw [← hS_univ]
      _ ≤ Cardinal.lift.{v} #κ * ⨆ j : κ, Cardinal.lift.{w} #(S j) :=
          Cardinal.mk_iUnion_le_lift S
      _ ≤ Cardinal.lift.{v} #κ * ℵ₀ := by
          gcongr
          refine ciSup_le fun j ↦ ?_
          exact Cardinal.lift_le_aleph0.2 (hv.countable_support_inner (f (c j))).le_aleph0
      _ = Cardinal.lift.{v} #κ :=
          Cardinal.mul_eq_left (Cardinal.aleph0_le_lift.2 (Cardinal.aleph0_le_mk κ))
            (Cardinal.aleph0_le_lift.2 (Cardinal.aleph0_le_mk κ)) Cardinal.aleph0_ne_zero

/-- Any orthonormal family in `E` has lifted index cardinality at most that of any Hilbert basis
of `E`. -/
theorem Orthonormal.cardinal_lift_le_hilbertBasis {ι : Type v} {κ : Type w} {v : ι → E}
    (hv : Orthonormal 𝕜 v) (c : HilbertBasis κ 𝕜 E) :
    Cardinal.lift.{w} #ι ≤ Cardinal.lift.{v} #κ :=
  hv.cardinal_lift_le_hilbertBasis_of_denseRange c (ContinuousLinearMap.id 𝕜 E) denseRange_id

end OrthonormalBound

namespace HilbertBasis

variable {𝕜 : Type*} {E : Type u} {F : Type u'} [RCLike 𝕜]
  [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [NormedAddCommGroup F] [InnerProductSpace 𝕜 F]

/-- **Invariance of Hilbert-basis cardinality.** Any two Hilbert bases of `E` have equal lifted
index cardinalities. -/
theorem lift_mk_eq {ι : Type v} {κ : Type w} (b : HilbertBasis ι 𝕜 E) (c : HilbertBasis κ 𝕜 E) :
    Cardinal.lift.{w} #ι = Cardinal.lift.{v} #κ :=
  le_antisymm (b.orthonormal.cardinal_lift_le_hilbertBasis c)
    (c.orthonormal.cardinal_lift_le_hilbertBasis b)

/-- Same-universe specialization of `HilbertBasis.lift_mk_eq`. -/
theorem mk_eq {ι κ : Type v} (b : HilbertBasis ι 𝕜 E) (c : HilbertBasis κ 𝕜 E) :
    #ι = #κ :=
  Cardinal.lift_inj.1 (b.lift_mk_eq c)

/-- Any two Hilbert bases of `E` have equivalent index types. -/
noncomputable def indexEquiv {ι : Type v} {κ : Type w} (b : HilbertBasis ι 𝕜 E)
    (c : HilbertBasis κ 𝕜 E) : ι ≃ κ :=
  (Cardinal.lift_mk_eq'.1 (b.lift_mk_eq c)).some

/-- A space with a Hilbert basis `b` is a subsingleton if and only if the index type of `b` is
empty. -/
theorem subsingleton_iff_isEmpty {ι : Type v} (b : HilbertBasis ι 𝕜 E) :
    Subsingleton E ↔ IsEmpty ι :=
  ⟨fun _ ↦ b.orthonormal.isEmpty_of_subsingleton, fun _ ↦ b.repr.toEquiv.subsingleton⟩

/-- A space with a Hilbert basis `b` is nontrivial if and only if the index type of `b` is
nonempty. -/
theorem nontrivial_iff_nonempty {ι : Type v} (b : HilbertBasis ι 𝕜 E) :
    Nontrivial E ↔ Nonempty ι := by
  rw [← not_subsingleton_iff_nontrivial, ← not_isEmpty_iff, b.subsingleton_iff_isEmpty]

/-- The index type of a Hilbert basis of `E` is finite if and only if `E` is finite-dimensional. -/
theorem finite_iff_finiteDimensional {ι : Type v} (b : HilbertBasis ι 𝕜 E) :
    Finite ι ↔ FiniteDimensional 𝕜 E := by
  refine ⟨fun _ ↦ ?_, fun _ ↦ ?_⟩
  · cases nonempty_fintype ι
    exact Module.Finite.of_basis b.toOrthonormalBasis.toBasis
  · have : CompleteSpace E := b.completeSpace
    exact Finite.of_equiv _ (b.indexEquiv (stdOrthonormalBasis 𝕜 E).toHilbertBasis).symm

/-- The index type of a Hilbert basis of `E` is infinite if and only if `E` is
infinite-dimensional. -/
theorem infinite_iff {ι : Type v} (b : HilbertBasis ι 𝕜 E) :
    Infinite ι ↔ ¬ FiniteDimensional 𝕜 E := by
  rw [← not_finite_iff_infinite, b.finite_iff_finiteDimensional]

/-- The cardinality of a finite Hilbert basis equals `Module.finrank 𝕜 E`. -/
theorem card_eq_finrank {ι : Type v} [Fintype ι] (b : HilbertBasis ι 𝕜 E) :
    Fintype.card ι = Module.finrank 𝕜 E :=
  (Module.finrank_eq_card_basis b.toOrthonormalBasis.toBasis).symm

/-- On a finite-dimensional space, `Nat.card` of any Hilbert-basis index type equals
`Module.finrank 𝕜 E`. -/
theorem natCard_eq_finrank {ι : Type v} [FiniteDimensional 𝕜 E] (b : HilbertBasis ι 𝕜 E) :
    Nat.card ι = Module.finrank 𝕜 E := by
  have : Finite ι := b.finite_iff_finiteDimensional.2 ‹_›
  cases nonempty_fintype ι
  rw [Nat.card_eq_fintype_card, b.card_eq_finrank]

/-- A space with a Hilbert basis `b` is separable if and only if the index type of `b` is
countable. -/
theorem separableSpace_iff {ι : Type v} (b : HilbertBasis ι 𝕜 E) :
    TopologicalSpace.SeparableSpace E ↔ Countable ι := by
  refine ⟨fun _ ↦ b.orthonormal.countable, fun _ ↦ ?_⟩
  have : ProperSpace 𝕜 := FiniteDimensional.proper_rclike 𝕜 𝕜
  have : TopologicalSpace.SeparableSpace ℓ²(ι, 𝕜) :=
    lp.separableSpace (E := fun _ : ι ↦ 𝕜) (by simp)
  exact b.repr.symm.surjective.denseRange.separableSpace b.repr.symm.continuous

/-- Hilbert bases of continuously linearly equivalent inner product spaces have equal lifted index
cardinalities. -/
theorem lift_mk_eq_of_continuousLinearEquiv {ι : Type v} {κ : Type w}
    (b : HilbertBasis ι 𝕜 E) (c : HilbertBasis κ 𝕜 F) (e : E ≃L[𝕜] F) :
    Cardinal.lift.{w} #ι = Cardinal.lift.{v} #κ :=
  le_antisymm
    (b.orthonormal.cardinal_lift_le_hilbertBasis_of_denseRange c e.symm.toContinuousLinearMap
      e.symm.surjective.denseRange)
    (c.orthonormal.cardinal_lift_le_hilbertBasis_of_denseRange b e.toContinuousLinearMap
      e.surjective.denseRange)

/-- Same-universe specialization of `HilbertBasis.lift_mk_eq_of_continuousLinearEquiv`. -/
theorem mk_eq_of_continuousLinearEquiv {ι κ : Type v}
    (b : HilbertBasis ι 𝕜 E) (c : HilbertBasis κ 𝕜 F) (e : E ≃L[𝕜] F) :
    #ι = #κ :=
  Cardinal.lift_inj.1 (b.lift_mk_eq_of_continuousLinearEquiv c e)

/-- **Unitary classification of Hilbert spaces (basis form).** Given Hilbert bases `b` of `E` and
`c` of `F`, `E` and `F` are linearly isometrically equivalent if and only if `#ι` and `#κ` agree up
to universe lift. -/
theorem nonempty_linearIsometryEquiv_iff_lift_mk_eq {ι : Type v} {κ : Type w}
    (b : HilbertBasis ι 𝕜 E) (c : HilbertBasis κ 𝕜 F) :
    Nonempty (E ≃ₗᵢ[𝕜] F) ↔ Cardinal.lift.{w} #ι = Cardinal.lift.{v} #κ :=
  ⟨fun ⟨U⟩ ↦ (b.mapₗᵢ U).lift_mk_eq c,
    fun h ↦ let ⟨e⟩ := Cardinal.lift_mk_eq'.1 h; ⟨b.equiv c e⟩⟩

end HilbertBasis

namespace TauCeti

/-- **Hilbert dimension** of a complete inner product space `E` over `𝕜`, defined as the
basis-independent cardinality of any Hilbert basis of `E`. Unlike `Module.rank 𝕜 E`, this is the
complete orthonormal dimension (`ℵ₀` on `ℓ²(ℕ, 𝕜)`, whereas `Module.rank` is the continuum). -/
noncomputable def hilbertDim (𝕜 : Type*) (E : Type u) [RCLike 𝕜] [NormedAddCommGroup E]
    [InnerProductSpace 𝕜 E] [CompleteSpace E] : Cardinal.{u} :=
  #(exists_hilbertBasis 𝕜 E).choose

end TauCeti

section HilbertDimAPI

variable {𝕜 : Type*} {E : Type u} {F : Type u'} [RCLike 𝕜]
  [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F]

/-- Every Hilbert basis of `E` has lifted index cardinality equal to the lifted Hilbert dimension
of `E`. -/
theorem HilbertBasis.mk_eq_hilbertDim {ι : Type v} (b : HilbertBasis ι 𝕜 E) :
    Cardinal.lift.{u} #ι = Cardinal.lift.{v} (TauCeti.hilbertDim 𝕜 E) :=
  b.lift_mk_eq (exists_hilbertBasis 𝕜 E).choose_spec.choose

/-- Every Hilbert basis of `E` indexed in the same universe as `E` has index cardinality
`TauCeti.hilbertDim 𝕜 E`. -/
theorem HilbertBasis.mk_eq_hilbertDim' {ι : Type u} (b : HilbertBasis ι 𝕜 E) :
    #ι = TauCeti.hilbertDim 𝕜 E :=
  Cardinal.lift_inj.1 b.mk_eq_hilbertDim

/-- The range of any Hilbert basis of `E` has cardinality `TauCeti.hilbertDim 𝕜 E`. -/
theorem HilbertBasis.mk_range_eq_hilbertDim {ι : Type v} (b : HilbertBasis ι 𝕜 E) :
    #(Set.range b) = TauCeti.hilbertDim 𝕜 E := by
  rw [← Cardinal.lift_inj.{u, v}, Cardinal.mk_range_eq_of_injective
    b.orthonormal.linearIndependent.injective, b.mk_eq_hilbertDim]

/-- Any orthonormal family in a Hilbert space `E` has lifted index cardinality at most the lifted
Hilbert dimension of `E`. -/
theorem Orthonormal.cardinal_lift_le_hilbertDim {ι : Type v} {v : ι → E}
    (hv : Orthonormal 𝕜 v) :
    Cardinal.lift.{u} #ι ≤ Cardinal.lift.{v} (TauCeti.hilbertDim 𝕜 E) :=
  hv.cardinal_lift_le_hilbertBasis (exists_hilbertBasis 𝕜 E).choose_spec.choose

/-- Linear isometric equivalences preserve Hilbert dimension up to universe lift. -/
theorem LinearIsometryEquiv.lift_hilbertDim_eq (e : E ≃ₗᵢ[𝕜] F) :
    Cardinal.lift.{u'} (TauCeti.hilbertDim 𝕜 E) = Cardinal.lift.{u} (TauCeti.hilbertDim 𝕜 F) := by
  let b := (exists_hilbertBasis 𝕜 E).choose_spec.choose
  simpa only [b.mk_eq_hilbertDim'] using (b.mapₗᵢ e).mk_eq_hilbertDim

/-- Linear isometric equivalences between Hilbert spaces in the same universe preserve Hilbert
dimension. -/
theorem LinearIsometryEquiv.hilbertDim_eq {F : Type u} [NormedAddCommGroup F]
    [InnerProductSpace 𝕜 F] [CompleteSpace F] (e : E ≃ₗᵢ[𝕜] F) :
    TauCeti.hilbertDim 𝕜 E = TauCeti.hilbertDim 𝕜 F :=
  Cardinal.lift_inj.1 e.lift_hilbertDim_eq

/-- A linear isometry between Hilbert spaces does not decrease Hilbert dimension (up to lift). -/
theorem LinearIsometry.lift_hilbertDim_le (f : E →ₗᵢ[𝕜] F) :
    Cardinal.lift.{u'} (TauCeti.hilbertDim 𝕜 E) ≤ Cardinal.lift.{u} (TauCeti.hilbertDim 𝕜 F) := by
  let b := (exists_hilbertBasis 𝕜 E).choose_spec.choose
  simpa only [b.mk_eq_hilbertDim'] using
    (b.orthonormal.comp_linearIsometry f).cardinal_lift_le_hilbertDim

/-- Same-universe specialization of `LinearIsometry.lift_hilbertDim_le`. -/
theorem LinearIsometry.hilbertDim_le {F : Type u} [NormedAddCommGroup F]
    [InnerProductSpace 𝕜 F] [CompleteSpace F] (f : E →ₗᵢ[𝕜] F) :
    TauCeti.hilbertDim 𝕜 E ≤ TauCeti.hilbertDim 𝕜 F :=
  Cardinal.lift_le.1 f.lift_hilbertDim_le

/-- Continuous linear equivalences between Hilbert spaces preserve Hilbert dimension up to universe
lift. -/
theorem ContinuousLinearEquiv.lift_hilbertDim_eq (e : E ≃L[𝕜] F) :
    Cardinal.lift.{u'} (TauCeti.hilbertDim 𝕜 E) = Cardinal.lift.{u} (TauCeti.hilbertDim 𝕜 F) := by
  let b := (exists_hilbertBasis 𝕜 E).choose_spec.choose
  let c := (exists_hilbertBasis 𝕜 F).choose_spec.choose
  simpa only [b.mk_eq_hilbertDim', c.mk_eq_hilbertDim'] using
    b.lift_mk_eq_of_continuousLinearEquiv c e

/-- Continuous linear equivalences between Hilbert spaces in the same universe preserve Hilbert
dimension. -/
theorem ContinuousLinearEquiv.hilbertDim_eq {F : Type u} [NormedAddCommGroup F]
    [InnerProductSpace 𝕜 F] [CompleteSpace F] (e : E ≃L[𝕜] F) :
    TauCeti.hilbertDim 𝕜 E = TauCeti.hilbertDim 𝕜 F :=
  Cardinal.lift_inj.1 e.lift_hilbertDim_eq

namespace TauCeti

/-- A continuous linear map `f : E →L[𝕜] F` with dense range satisfies
`Cardinal.lift (hilbertDim 𝕜 F) ≤ Cardinal.lift (hilbertDim 𝕜 E)`. -/
theorem lift_hilbertDim_le_of_denseRange (f : E →L[𝕜] F) (hf : DenseRange f) :
    Cardinal.lift.{u} (hilbertDim 𝕜 F) ≤ Cardinal.lift.{u'} (hilbertDim 𝕜 E) := by
  let b := (exists_hilbertBasis 𝕜 E).choose_spec.choose
  let c := (exists_hilbertBasis 𝕜 F).choose_spec.choose
  simpa only [b.mk_eq_hilbertDim', c.mk_eq_hilbertDim'] using
    c.orthonormal.cardinal_lift_le_hilbertBasis_of_denseRange b f hf

/-- A type `ι` indexes a Hilbert basis of `E` if and only if its lifted cardinality equals the
lifted Hilbert dimension of `E`. -/
theorem nonempty_hilbertBasis_iff_lift_mk_eq_hilbertDim {ι : Type v} :
    Nonempty (HilbertBasis ι 𝕜 E) ↔ Cardinal.lift.{u} #ι = Cardinal.lift.{v} (hilbertDim 𝕜 E) := by
  refine ⟨fun ⟨b⟩ ↦ b.mk_eq_hilbertDim, fun h ↦ ?_⟩
  let b₀ := (exists_hilbertBasis 𝕜 E).choose_spec.choose
  have hb₀ : Cardinal.lift.{v} #(exists_hilbertBasis 𝕜 E).choose = Cardinal.lift.{u} #ι := by
    rw [b₀.mk_eq_hilbertDim', h]
  obtain ⟨e⟩ := Cardinal.lift_mk_eq'.1 hb₀
  exact ⟨b₀.reindex e⟩

/-- The Hilbert dimension of a complete inner product space equals the supremum of cardinalities of
its orthonormal subsets. -/
theorem hilbertDim_eq_ciSup_orthonormal (𝕜 : Type*) (E : Type u) [RCLike 𝕜]
    [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E] :
    hilbertDim 𝕜 E = ⨆ s : {s : Set E // Orthonormal 𝕜 ((↑) : s → E)}, #(s : Set E) := by
  have : Nonempty {s : Set E // Orthonormal 𝕜 ((↑) : s → E)} := ⟨⟨∅, orthonormal_empty 𝕜 E⟩⟩
  refine le_antisymm ?_ (ciSup_le fun s ↦ Cardinal.lift_le.{u}.1 <| by
    simpa using s.2.cardinal_lift_le_hilbertDim)
  obtain ⟨w, b, hbw⟩ := exists_hilbertBasis 𝕜 E
  have hw : Orthonormal 𝕜 ((↑) : w → E) := hbw ▸ b.orthonormal
  rw [← b.mk_eq_hilbertDim']
  exact le_ciSup (f := fun s : {s : Set E // Orthonormal 𝕜 ((↑) : s → E)} ↦ #(s : Set E))
    Cardinal.bddAbove_of_small ⟨w, hw⟩

/-- A subsingleton Hilbert space has Hilbert dimension `0`. -/
@[simp]
theorem hilbertDim_of_subsingleton [Subsingleton E] :
    hilbertDim 𝕜 E = 0 := by
  let b := (exists_hilbertBasis 𝕜 E).choose_spec.choose
  have : IsEmpty (exists_hilbertBasis 𝕜 E).choose := b.subsingleton_iff_isEmpty.1 ‹_›
  rw [← b.mk_eq_hilbertDim', Cardinal.mk_eq_zero]

/-- The Hilbert dimension of `E` is `0` if and only if `E` is a subsingleton. -/
@[simp]
theorem hilbertDim_eq_zero_iff :
    hilbertDim 𝕜 E = 0 ↔ Subsingleton E := by
  let b := (exists_hilbertBasis 𝕜 E).choose_spec.choose
  rw [← b.mk_eq_hilbertDim', Cardinal.mk_eq_zero_iff, b.subsingleton_iff_isEmpty]

/-- The Hilbert dimension of `E` is positive if and only if `E` is nontrivial. -/
@[simp]
theorem hilbertDim_pos_iff :
    0 < hilbertDim 𝕜 E ↔ Nontrivial E := by
  rw [pos_iff_ne_zero, ne_eq, hilbertDim_eq_zero_iff, not_subsingleton_iff_nontrivial]

/-- On a finite-dimensional inner product space, `hilbertDim 𝕜 E` agrees with `Module.finrank 𝕜 E`.
-/
theorem hilbertDim_eq_finrank [FiniteDimensional 𝕜 E] :
    hilbertDim 𝕜 E = Module.finrank 𝕜 E := by
  have h := (stdOrthonormalBasis 𝕜 E).toHilbertBasis.mk_eq_hilbertDim
  simpa using h.symm

/-- The Hilbert dimension of `E` is finite (`< ℵ₀`) if and only if `E` is finite-dimensional. -/
@[simp]
theorem hilbertDim_lt_aleph0_iff :
    hilbertDim 𝕜 E < ℵ₀ ↔ FiniteDimensional 𝕜 E := by
  let b := (exists_hilbertBasis 𝕜 E).choose_spec.choose
  rw [← b.mk_eq_hilbertDim', Cardinal.lt_aleph0_iff_finite, b.finite_iff_finiteDimensional]

/-- The Hilbert dimension of `E` is at least `ℵ₀` if and only if `E` is infinite-dimensional. -/
@[simp]
theorem aleph0_le_hilbertDim_iff :
    ℵ₀ ≤ hilbertDim 𝕜 E ↔ ¬ FiniteDimensional 𝕜 E := by
  rw [← not_lt, hilbertDim_lt_aleph0_iff]

/-- The Hilbert dimension of `ℓ²(ι, 𝕜)` is `#ι` lifted to the universe of `𝕜` (in particular `#ι`
when `𝕜 = ℝ` or `𝕜 = ℂ`). -/
@[simp]
theorem hilbertDim_lp (ι : Type v) (𝕜 : Type w) [RCLike 𝕜] :
    hilbertDim 𝕜 ℓ²(ι, 𝕜) = Cardinal.lift.{w} #ι := by
  have h := (lp.hilbertBasisFun ι 𝕜).mk_eq_hilbertDim
  rw [Cardinal.lift_id'.{v, max v w}, Cardinal.lift_umax.{v, w}] at h
  exact h.symm

/-- The Hilbert dimension of `ℓ²(ℕ, 𝕜)` is `ℵ₀`. -/
theorem hilbertDim_lp_nat (𝕜 : Type w) [RCLike 𝕜] :
    hilbertDim 𝕜 ℓ²(ℕ, 𝕜) = ℵ₀ := by
  simp

/-- The Hilbert dimension of `EuclideanSpace 𝕜 ι` is `Fintype.card ι`. -/
@[simp]
theorem hilbertDim_euclideanSpace (ι : Type v) (𝕜 : Type w) [RCLike 𝕜] [Fintype ι] :
    hilbertDim 𝕜 (EuclideanSpace 𝕜 ι) = Fintype.card ι := by
  rw [hilbertDim_eq_finrank, finrank_euclideanSpace]

/-- The Hilbert dimension of the scalar field `𝕜` over itself is `1`. -/
@[simp]
theorem hilbertDim_self (𝕜 : Type u) [RCLike 𝕜] :
    hilbertDim 𝕜 𝕜 = 1 := by
  rw [hilbertDim_eq_finrank, Module.finrank_self, Nat.cast_one]

/-- **Unitary classification of Hilbert spaces.** Two Hilbert spaces over `𝕜` are linearly
isometrically equivalent if and only if their Hilbert dimensions agree up to universe lift. -/
theorem nonempty_linearIsometryEquiv_iff_lift_hilbertDim_eq :
    Nonempty (E ≃ₗᵢ[𝕜] F) ↔
      Cardinal.lift.{u'} (hilbertDim 𝕜 E) = Cardinal.lift.{u} (hilbertDim 𝕜 F) := by
  let b := (exists_hilbertBasis 𝕜 E).choose_spec.choose
  let c := (exists_hilbertBasis 𝕜 F).choose_spec.choose
  rw [b.nonempty_linearIsometryEquiv_iff_lift_mk_eq c, b.mk_eq_hilbertDim', c.mk_eq_hilbertDim']

/-- Same-universe specialization of `TauCeti.nonempty_linearIsometryEquiv_iff_lift_hilbertDim_eq`.
-/
theorem nonempty_linearIsometryEquiv_iff_hilbertDim_eq {F : Type u} [NormedAddCommGroup F]
    [InnerProductSpace 𝕜 F] [CompleteSpace F] :
    Nonempty (E ≃ₗᵢ[𝕜] F) ↔ hilbertDim 𝕜 E = hilbertDim 𝕜 F := by
  rw [nonempty_linearIsometryEquiv_iff_lift_hilbertDim_eq, Cardinal.lift_inj]

/-- Two Hilbert spaces over `𝕜` admit a continuous linear equivalence if and only if their Hilbert
dimensions agree up to universe lift. -/
theorem nonempty_continuousLinearEquiv_iff_lift_hilbertDim_eq :
    Nonempty (E ≃L[𝕜] F) ↔
      Cardinal.lift.{u'} (hilbertDim 𝕜 E) = Cardinal.lift.{u} (hilbertDim 𝕜 F) :=
  ⟨fun ⟨e⟩ ↦ e.lift_hilbertDim_eq,
    fun h ↦ let ⟨U⟩ := nonempty_linearIsometryEquiv_iff_lift_hilbertDim_eq.2 h
      ⟨U.toContinuousLinearEquiv⟩⟩

/-- Two Hilbert spaces over `𝕜` are continuously linearly equivalent if and only if they are
linearly isometrically equivalent. -/
theorem nonempty_continuousLinearEquiv_iff_nonempty_linearIsometryEquiv :
    Nonempty (E ≃L[𝕜] F) ↔ Nonempty (E ≃ₗᵢ[𝕜] F) := by
  rw [nonempty_continuousLinearEquiv_iff_lift_hilbertDim_eq,
    nonempty_linearIsometryEquiv_iff_lift_hilbertDim_eq]

/-- A Hilbert space `E` is separable if and only if `hilbertDim 𝕜 E ≤ ℵ₀`. -/
theorem separableSpace_iff_hilbertDim_le_aleph0 :
    TopologicalSpace.SeparableSpace E ↔ hilbertDim 𝕜 E ≤ ℵ₀ := by
  let b := (exists_hilbertBasis 𝕜 E).choose_spec.choose
  rw [b.separableSpace_iff, ← b.mk_eq_hilbertDim', Cardinal.mk_le_aleph0_iff]

/-- A Hilbert space `E` is separable if and only if its Hilbert dimension is a natural number or
`ℵ₀`. -/
theorem separableSpace_iff_exists_nat_or_eq_aleph0 :
    TopologicalSpace.SeparableSpace E ↔
      (∃ n : ℕ, hilbertDim 𝕜 E = n) ∨ hilbertDim 𝕜 E = ℵ₀ := by
  rw [separableSpace_iff_hilbertDim_le_aleph0 (𝕜 := 𝕜), le_iff_lt_or_eq, Cardinal.lt_aleph0]

/-- Every separable infinite-dimensional Hilbert space has Hilbert dimension `ℵ₀`. -/
theorem hilbertDim_eq_aleph0_of_separableSpace [TopologicalSpace.SeparableSpace E]
    (hE : ¬ FiniteDimensional 𝕜 E) :
    hilbertDim 𝕜 E = ℵ₀ :=
  le_antisymm (separableSpace_iff_hilbertDim_le_aleph0.1 ‹_›) (aleph0_le_hilbertDim_iff.2 hE)

/-- Every separable infinite-dimensional Hilbert space admits a `ℕ`-indexed Hilbert basis. -/
theorem nonempty_hilbertBasis_nat [TopologicalSpace.SeparableSpace E]
    (hE : ¬ FiniteDimensional 𝕜 E) :
    Nonempty (HilbertBasis ℕ 𝕜 E) := by
  rw [nonempty_hilbertBasis_iff_lift_mk_eq_hilbertDim,
    hilbertDim_eq_aleph0_of_separableSpace (𝕜 := 𝕜) hE]
  simp

/-- **Riesz–Fischer model theorem.** Every separable infinite-dimensional Hilbert space over `𝕜`
is linearly isometrically equivalent to `ℓ²(ℕ, 𝕜)`. -/
theorem nonempty_linearIsometryEquiv_lp_nat [TopologicalSpace.SeparableSpace E]
    (hE : ¬ FiniteDimensional 𝕜 E) :
    Nonempty (E ≃ₗᵢ[𝕜] ℓ²(ℕ, 𝕜)) := by
  obtain ⟨b⟩ := nonempty_hilbertBasis_nat (𝕜 := 𝕜) hE
  exact ⟨b.repr⟩

/-- Any two separable infinite-dimensional Hilbert spaces over `𝕜` are linearly isometrically
equivalent. -/
theorem nonempty_linearIsometryEquiv_of_separableSpace [TopologicalSpace.SeparableSpace E]
    [TopologicalSpace.SeparableSpace F] (hE : ¬ FiniteDimensional 𝕜 E)
    (hF : ¬ FiniteDimensional 𝕜 F) :
    Nonempty (E ≃ₗᵢ[𝕜] F) := by
  rw [nonempty_linearIsometryEquiv_iff_lift_hilbertDim_eq,
    hilbertDim_eq_aleph0_of_separableSpace (𝕜 := 𝕜) hE,
    hilbertDim_eq_aleph0_of_separableSpace (𝕜 := 𝕜) hF]
  simp

end TauCeti

end HilbertDimAPI
