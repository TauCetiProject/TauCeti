/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.SetTheory.Cardinal.Arithmetic
public import TauCeti.Analysis.InnerProductSpace.HilbertBasis.Reindex
public import TauCeti.Analysis.InnerProductSpace.Orthonormal.Basic
public import TauCeti.Analysis.Normed.Lp.Basic
import Mathlib.Analysis.RCLike.Lemmas

/-!
# Hilbert dimension and unitary classification of Hilbert spaces

Any two Hilbert bases `b : HilbertBasis ι 𝕜 E` and `c : HilbertBasis κ 𝕜 E` of an inner product
space `E` over `𝕜` (`ℝ` or `ℂ`) have index types of equal cardinality (`HilbertBasis.lift_mk_eq`,
`HilbertBasis.mk_eq`):

* When either index type is finite, `b.toOrthonormalBasis` identifies `E` as finite-dimensional of
  dimension `Module.finrank 𝕜 E = Fintype.card ι = Fintype.card κ`
  (`HilbertBasis.finiteDimensional_iff_finite`, `HilbertBasis.finrank_eq_card`).
* When both index types are infinite, each basis vector `c j` has countable Fourier support in `b`
  (`Orthonormal.countable_support_inner_left`), and the union of those supports over `j : κ` covers
  `ι` (`HilbertBasis.iUnion_support_inner_eq_univ`) because any omitted `b i` would be orthogonal
  to every `c j` and hence zero. Thus `#ι ≤ #κ * ℵ₀ = #κ`, and symmetry gives equality.

Consequently, two spaces carrying Hilbert bases `b : HilbertBasis ι 𝕜 E` and
`c : HilbertBasis κ 𝕜 F` admit a linear isometric equivalence `E ≃ₗᵢ[𝕜] F` if and only if their
basis index types have the same lifted cardinality
(`HilbertBasis.nonempty_linearIsometryEquiv_iff_lift_mk_eq`): a unitary equivalence transports `b`
to a Hilbert basis of `F` via `HilbertBasis.mapₗᵢ`, and an index equivalence `e : ι ≃ κ` produces a
basis-preserving unitary `b.equiv c e : E ≃ₗᵢ[𝕜] F`.

For any complete inner product space `E`, `TauCeti.hilbertDim 𝕜 E : Cardinal.{u}` is the common
cardinality of all Hilbert bases of `E` (defined from `exists_hilbertBasis 𝕜 E`). Unlike the
algebraic Hamel rank `Module.rank 𝕜 E` — which equals `2 ^ ℵ₀` on `ℓ²(ℕ, 𝕜)` — the Hilbert
dimension of `ℓ²(ι, 𝕜)` is `#ι` (up to universe lift), agrees with `Module.finrank 𝕜 E` in finite
dimension, is at most `ℵ₀` if and only if `E` is separable (`TauCeti.hilbertDim_le_aleph0_iff`),
equals `ℵ₀` if and only if `E` is separable and infinite-dimensional
(`TauCeti.hilbertDim_eq_aleph0_iff`), and classifies Hilbert spaces over `𝕜` up to linear isometric
equivalence (`TauCeti.nonempty_linearIsometryEquiv_iff_lift_hilbertDim_eq`). In particular,
separable Hilbert spaces have Hilbert dimension `0`, a positive natural number, or `ℵ₀`, and every
separable infinite-dimensional Hilbert space is unitarily isomorphic to `ℓ²(ℕ, 𝕜)`.

## Main declarations

* `HilbertBasis.separableSpace_iff_countable`: a space with a Hilbert basis `b` is separable iff
  its index type is countable.
* `HilbertBasis.finiteDimensional_iff_finite`, `HilbertBasis.finrank_eq_card`: `E` is
  finite-dimensional iff the index type is finite, with `finrank 𝕜 E = Fintype.card ι`.
* `HilbertBasis.lift_mk_eq`, `HilbertBasis.mk_eq`: basis-cardinality invariance for `HilbertBasis`.
* `HilbertBasis.nonempty_linearIsometryEquiv_iff_lift_mk_eq`: unitary classification in terms of
  given Hilbert bases.
* `TauCeti.hilbertDim`: the Hilbert dimension of a complete inner product space.
* `TauCeti.nonempty_linearIsometryEquiv_iff_lift_hilbertDim_eq`: two Hilbert spaces over `𝕜` are
  linearly isometric iff they have the same lifted Hilbert dimension.
* `TauCeti.hilbertDim_le_aleph0_iff`, `TauCeti.hilbertDim_eq_aleph0_iff`: separability and
  countably infinite Hilbert dimension.

## References

* J. B. Conway, *A Course in Functional Analysis*, 2nd ed., Chapter I, §4.
* M. Reed and B. Simon, *Methods of Modern Mathematical Physics I: Functional Analysis*, §II.2.
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
theorem subsingleton_iff_isEmpty (b : HilbertBasis ι 𝕜 E) : Subsingleton E ↔ IsEmpty ι := by
  refine ⟨fun _ ↦ ⟨fun i ↦ b.orthonormal.ne_zero i (Subsingleton.elim _ _)⟩, fun _ ↦ ?_⟩
  have : Subsingleton ℓ²(ι, 𝕜) := ⟨fun x y ↦ lp.ext (funext isEmptyElim)⟩
  exact b.repr.toEquiv.subsingleton

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
  have hcard : #ι = ℵ₀ :=
    le_antisymm (Cardinal.mk_le_aleph0_iff.2 ‹_›) (Cardinal.aleph0_le_mk ι)
  refine Cardinal.lift_mk_eq'.1 ?_
  rw [hcard]
  simp

end Structure

section Cardinality

variable {𝕜 : Type*} {E : Type*} {F : Type*} [RCLike 𝕜]
  [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [NormedAddCommGroup F] [InnerProductSpace 𝕜 F]

/-- Every member `b i` of a Hilbert basis pairs nontrivially with at least one member `c j` of any
other Hilbert basis of the same space, so the supports of `i ↦ ⟪b i, c j⟫_𝕜` cover `ι`. -/
theorem iUnion_support_inner_eq_univ {ι : Type*} {κ : Type*} (b : HilbertBasis ι 𝕜 E)
    (c : HilbertBasis κ 𝕜 E) :
    (⋃ j : κ, Function.support fun i : ι ↦ ⟪b i, c j⟫_𝕜) = Set.univ := by
  refine Set.eq_univ_of_forall fun i ↦ Set.mem_iUnion.2 ?_
  by_contra! h
  have hrepr : c.repr (b i) = 0 := by
    ext j
    have hj : ⟪b i, c j⟫_𝕜 = 0 := Function.notMem_support.1 (h j)
    rw [c.repr_apply_apply, ← inner_conj_symm, hj, map_zero, lp.coeFn_zero, Pi.zero_apply]
  exact b.orthonormal.ne_zero i (c.repr.map_eq_zero_iff.1 hrepr)

private theorem mk_le_same {ι κ : Type u} (b : HilbertBasis ι 𝕜 E) (c : HilbertBasis κ 𝕜 E) :
    #ι ≤ #κ := by
  by_cases hκ : Finite κ
  · have hE : FiniteDimensional 𝕜 E := c.finiteDimensional_iff_finite.2 hκ
    have : Finite ι := b.finiteDimensional_iff_finite.1 hE
    cases nonempty_fintype ι
    cases nonempty_fintype κ
    rw [Cardinal.mk_fintype, Cardinal.mk_fintype, ← b.finrank_eq_card, ← c.finrank_eq_card]
  · have : Infinite κ := not_finite_iff_infinite.1 hκ
    set s : κ → Set ι := fun j ↦ Function.support fun i : ι ↦ ⟪b i, c j⟫_𝕜
    calc #ι = #(Set.univ : Set ι) := Cardinal.mk_univ.symm
      _ = #(⋃ j : κ, s j) := by rw [b.iUnion_support_inner_eq_univ c]
      _ ≤ #κ * ⨆ j : κ, #(s j) := Cardinal.mk_iUnion_le s
      _ ≤ #κ * ℵ₀ := mul_le_mul_of_nonneg_left (ciSup_le fun j ↦
          Cardinal.le_aleph0_iff_set_countable.2
            (b.orthonormal.countable_support_inner_left (c j))) zero_le
      _ = #κ := Cardinal.mul_eq_left (Cardinal.aleph0_le_mk κ) (Cardinal.aleph0_le_mk κ)
          Cardinal.aleph0_ne_zero

/-- **Invariance of Hilbert basis cardinality (same universe).** Any two Hilbert bases of `E`
indexed by types in the same universe have equal index cardinalities. -/
theorem mk_eq {ι κ : Type u} (b : HilbertBasis ι 𝕜 E) (c : HilbertBasis κ 𝕜 E) :
    #ι = #κ :=
  le_antisymm (mk_le_same b c) (mk_le_same c b)

/-- **Invariance of Hilbert basis cardinality.** Any two Hilbert bases `b : HilbertBasis ι 𝕜 E` and
`c : HilbertBasis κ 𝕜 E` of the same inner product space have index types of equal lifted
cardinality. -/
theorem lift_mk_eq {ι : Type u} {κ : Type v} (b : HilbertBasis ι 𝕜 E) (c : HilbertBasis κ 𝕜 E) :
    Cardinal.lift.{v} #ι = Cardinal.lift.{u} #κ := by
  have h := (b.reindex (Equiv.ulift.symm : ι ≃ ULift.{v} ι)).mk_eq
    (c.reindex (Equiv.ulift.symm : κ ≃ ULift.{u} κ))
  rwa [Cardinal.mk_uLift, Cardinal.mk_uLift] at h

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
    Cardinal.lift.{v} (TauCeti.hilbertDim 𝕜 E) = Cardinal.lift.{u} #ι :=
  (exists_hilbertBasis 𝕜 E).choose_spec.choose.lift_mk_eq b

/-- Same-universe form of `HilbertBasis.lift_hilbertDim_eq`. -/
theorem hilbertDim_eq {𝕜 : Type*} {E ι : Type u} [RCLike 𝕜]
    [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
    (b : HilbertBasis ι 𝕜 E) :
    TauCeti.hilbertDim 𝕜 E = #ι := by
  simpa using b.lift_hilbertDim_eq

end HilbertBasis

namespace LinearIsometryEquiv

/-- Linearly isometric Hilbert spaces have equal lifted Hilbert dimensions. -/
theorem lift_hilbertDim_eq {𝕜 : Type*} {E : Type u} {F : Type v} [RCLike 𝕜]
    [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
    [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F]
    (e : E ≃ₗᵢ[𝕜] F) :
    Cardinal.lift.{v} (TauCeti.hilbertDim 𝕜 E) = Cardinal.lift.{u} (TauCeti.hilbertDim 𝕜 F) :=
  ((exists_hilbertBasis 𝕜 E).choose_spec.choose.nonempty_linearIsometryEquiv_iff_lift_mk_eq
    (exists_hilbertBasis 𝕜 F).choose_spec.choose).1 ⟨e⟩

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

/-- **Unitary classification of Hilbert spaces.** Two Hilbert spaces `E` and `F` over `𝕜` admit a
linear isometric equivalence if and only if their lifted Hilbert dimensions are equal. -/
theorem nonempty_linearIsometryEquiv_iff_lift_hilbertDim_eq {E : Type u} {F : Type v}
    [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
    [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F] :
    Nonempty (E ≃ₗᵢ[𝕜] F) ↔
      Cardinal.lift.{v} (hilbertDim 𝕜 E) = Cardinal.lift.{u} (hilbertDim 𝕜 F) :=
  (exists_hilbertBasis 𝕜 E).choose_spec.choose.nonempty_linearIsometryEquiv_iff_lift_mk_eq
    (exists_hilbertBasis 𝕜 F).choose_spec.choose

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
  have : ProperSpace (EuclideanSpace 𝕜 ι) :=
    FiniteDimensional.proper_rclike 𝕜 (EuclideanSpace 𝕜 ι)
  have h := (EuclideanSpace.basisFun ι 𝕜).toHilbertBasis.lift_hilbertDim_eq
  simpa using h

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
@[simp]
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

section Separable

/-- Every separable infinite-dimensional Hilbert space admits a Hilbert basis indexed by `ℕ`. -/
theorem exists_hilbertBasis_nat (𝕜 : Type*) (E : Type*) [RCLike 𝕜] [NormedAddCommGroup E]
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
  let ⟨b⟩ := exists_hilbertBasis_nat 𝕜 E hE
  ⟨b.repr⟩

/-- Any two separable infinite-dimensional Hilbert spaces over the same scalar field `𝕜` are
linearly isometric. -/
theorem nonempty_linearIsometryEquiv_of_separableSpace {𝕜 : Type*} {E : Type*} {F : Type*}
    [RCLike 𝕜]
    [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
    [TopologicalSpace.SeparableSpace E]
    [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F]
    [TopologicalSpace.SeparableSpace F]
    (hE : ¬ FiniteDimensional 𝕜 E) (hF : ¬ FiniteDimensional 𝕜 F) :
    Nonempty (E ≃ₗᵢ[𝕜] F) := by
  obtain ⟨eE⟩ := nonempty_linearIsometryEquiv_lp_nat 𝕜 E hE
  obtain ⟨eF⟩ := nonempty_linearIsometryEquiv_lp_nat 𝕜 F hF
  exact ⟨eE.trans eF.symm⟩

/-- A scalar field `𝕜` and `EuclideanSpace 𝕜 ι` (`Fintype.card ι ≠ 1`) have Hilbert dimensions `1`
and `Fintype.card ι`, hence admit no linear isometric equivalence (for instance `ι = Fin 2`, showing
that separability alone does not classify Hilbert spaces). -/
theorem isEmpty_linearIsometryEquiv_self_euclideanSpace (𝕜 : Type u) (ι : Type v) [RCLike 𝕜]
    [Fintype ι] (hι : Fintype.card ι ≠ 1) :
    IsEmpty (𝕜 ≃ₗᵢ[𝕜] EuclideanSpace 𝕜 ι) :=
  isEmpty_linearIsometryEquiv_of_lift_hilbertDim_ne
    (by simpa using (mod_cast hι.symm : (1 : Cardinal) ≠ Fintype.card ι))

end Separable

end TauCeti
