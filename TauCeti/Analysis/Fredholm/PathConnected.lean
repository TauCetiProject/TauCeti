/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Fredholm.CompactPerturbation
public import TauCeti.Analysis.Fredholm.IndexRange
public import TauCeti.Analysis.InnerProductSpace.UnitaryPath
import Mathlib.Tactic.Abel

/-!
# Norm-path classification of Fredholm operators

Two Fredholm operators between complete complex inner-product spaces are joined by a
continuous path through Fredholm operators exactly when their indices agree. All paths
use the native operator-norm topology, and the two spaces may differ. No separability,
dimension or nontriviality assumption is imposed.

A fixed parametrix reduces the converse to completing the finite-dimensional defect of
an index-zero Fredholm operator. An affine compact perturbation followed by composition
with an invertible path connects the original endpoints. Index invariance along the path
is supplied by `Path.index_eq`.

Consequently, the Fredholm index descends to the set of path components
`ZerothHomotopy {T : E →L[𝕜] F // T.IsFredholm}` (`ZerothHomotopy.fredholmIndex`). Between
finite-dimensional spaces over a complete nontrivially normed field with real-linear operator
segments, every operator is Fredholm and affine segments make the Fredholm locus path connected.
Between complex Hilbert spaces, `ZerothHomotopy.fredholmIndex` is always injective; when the domain
is infinite-dimensional and continuously linearly equivalent (in particular unitarily equivalent) to
the codomain, combining injectivity with `ContinuousLinearEquiv.exists_isFredholm_and_index_eq`
identifies the norm-path components of the Fredholm locus bijectively with `ℤ`
(`ContinuousLinearEquiv.zerothHomotopyFredholmEquivInt`,
`LinearIsometryEquiv.zerothHomotopyFredholmEquivInt`).

The path construction is adapted from
[AtiyahSinger/Analysis/FredholmPaths.lean][fredholm-paths] in Lean-Atiyah-Singer.
Its finite-defect and parametrix argument is supplementary to Lawson--Michelsohn,
*Spin Geometry*, Chapter III, §7, Lemmas 7.6--7.7 and Theorem 7.8, pp. 203--204, which prove the
same path-component classification by first making the Fredholm endpoints surjective.

## Main declarations

* `ContinuousLinearMap.IsFredholm.exists_path_of_index_eq`,
  `ContinuousLinearMap.nonempty_path_iff_index_eq`: two Fredholm operators between complex Hilbert
  spaces are joined by a norm-continuous Fredholm path if and only if their indices agree.
* `ContinuousLinearMap.instPathConnectedSpaceFredholmOfFiniteDimensional`: in finite dimensions,
  the Fredholm locus is path connected.
* `ZerothHomotopy.fredholmIndex`, `ZerothHomotopy.fredholmIndex_injective`: the Fredholm index on
  path components and its injectivity for complex Hilbert spaces.
* `ContinuousLinearMap.zerothHomotopyFredholmSelfEquivInt`,
  `ContinuousLinearEquiv.zerothHomotopyFredholmEquivInt`,
  `LinearIsometryEquiv.zerothHomotopyFredholmEquivInt`: the bijection
  `ZerothHomotopy {T : E →L[ℂ] F // T.IsFredholm} ≃ ℤ` for infinite-dimensional isomorphic complex
  Hilbert spaces.

## References

* D. S. Freed, *The Atiyah--Singer index theorem*, Bull. Amer. Math. Soc. **58** (2021), 517--566,
  arXiv:2107.03557, display (3.13).
* H. B. Lawson, Jr., and M.-L. Michelsohn, *Spin Geometry*, Princeton Mathematical Series 38,
  Princeton University Press, 1989, Chapter III, §7, Lemmas 7.6--7.7 and Theorem 7.8, pp. 203--204,
  [DOI](https://doi.org/10.1515/9781400883912).

[fredholm-paths]: https://github.com/alpha-squared-labs/Lean-Atiyah-Singer/blob/09fc7bab3f9ff606901bde4b5a5580470da63a70/AtiyahSinger/Analysis/FredholmPaths.lean
-/

public section

noncomputable section

open ContinuousLinearMap
open scoped unitInterval

section FiniteDimensional

/-- Between finite-dimensional topological vector spaces over a complete nontrivially normed field
(with Hausdorff target and continuous real scalar multiplication on operators), every continuous
linear map is Fredholm and affine segments make the Fredholm locus path connected. -/
instance ContinuousLinearMap.instPathConnectedSpaceFredholmOfFiniteDimensional
    {𝕜 E F : Type*} [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜]
    [AddCommGroup E] [TopologicalSpace E] [IsTopologicalAddGroup E]
    [Module 𝕜 E] [ContinuousSMul 𝕜 E] [FiniteDimensional 𝕜 E]
    [AddCommGroup F] [TopologicalSpace F] [IsTopologicalAddGroup F] [T2Space F]
    [Module 𝕜 F] [ContinuousSMul 𝕜 F] [FiniteDimensional 𝕜 F]
    [Module ℝ (E →L[𝕜] F)] [ContinuousSMul ℝ (E →L[𝕜] F)] :
    PathConnectedSpace {T : E →L[𝕜] F // T.IsFredholm} :=
  PathConnectedSpace.mk ⟨⟨0, isFredholm_of_finiteDimensional 0⟩⟩ fun S T ↦
    (joinedIn_iff_joined (F := {U : E →L[𝕜] F | U.IsFredholm}) S.property T.property).mp
      ⟨Path.segment S.val T.val, fun _ ↦ isFredholm_of_finiteDimensional _⟩

end FiniteDimensional

section ZerothHomotopy

variable {𝕜 E F : Type*} [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E] [CompleteSpace E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F]

/-- The Fredholm index descended to the path components of the Fredholm locus. -/
def ZerothHomotopy.fredholmIndex :
    ZerothHomotopy {T : E →L[𝕜] F // T.IsFredholm} → ℤ :=
  ZerothHomotopy.lift (fun T ↦ T.val.index) fun _ _ γ ↦
    (γ.map continuous_subtype_val).index_eq fun t ↦ (γ t).property

/-- On the path component of a Fredholm operator `T`, `ZerothHomotopy.fredholmIndex` evaluates to
`T.val.index`. -/
@[simp]
theorem ZerothHomotopy.fredholmIndex_mk (T : {T : E →L[𝕜] F // T.IsFredholm}) :
    ZerothHomotopy.fredholmIndex (.mk T) = T.val.index := (rfl)

end ZerothHomotopy

section Hilbert

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

/-- Equal-index Fredholm operators between complex Hilbert spaces are joined by an
operator-norm continuous path consisting entirely of Fredholm operators. -/
theorem ContinuousLinearMap.IsFredholm.exists_path_of_index_eq {T₀ T₁ : E →L[ℂ] F}
    (hT₀ : T₀.IsFredholm) (hT₁ : T₁.IsFredholm) (hind : T₀.index = T₁.index) :
    ∃ γ : Path T₀ T₁, ∀ t, (γ t).IsFredholm := by
  -- A parametrix for T₁ reduces equality of indices to an index-zero operator on E.
  obtain ⟨Q, hQT, hTQ⟩ := hT₁.exists_isCompactOperator_comp_sub_one
  have hQ : Q.IsFredholm := .of_isCompactOperator_comp_sub_one hTQ hQT
  have hQindex : Q.index = -T₁.index :=
    ContinuousLinearMap.index_eq_neg_of_isCompactOperator_comp_sub_one hQT hTQ
  have hindex : (Q.comp T₀).index = 0 := by
    have hcomp := hQ.index_comp hT₀
    rw [← ContinuousLinearMap.index_def, ← ContinuousLinearMap.index_def,
      ← ContinuousLinearMap.index_def, hQindex, hind] at hcomp
    simpa only [neg_add_cancel] using hcomp
  obtain ⟨C, hC, hK⟩ :=
    (hQ.comp hT₀).exists_isInvertible_sub_isCompactOperator_of_index_eq_zero hindex
  -- Both terms in T₁(C - QT₀) + (T₁Q - 1)T₀ are compact.
  have hdiff : IsCompactOperator (T₁.comp C - T₀) := by
    have hleft := hK.clm_comp T₁
    have hright := hTQ.comp_clm T₀
    convert hleft.add hright using 1
    ext x
    simp only [Pi.add_apply, sub_apply,
      ContinuousLinearMap.coe_comp, Function.comp_apply, one_apply_eq_self,
      map_sub]
    abel
  have hpath₀ := hT₀.joinedIn_of_isCompactOperator_sub hdiff
  obtain ⟨γC, hγC⟩ := hC.exists_path_to_id
  let γ₁ : Path (T₁.comp C) T₁ :=
    (γC.map (f := fun A ↦ T₁.comp A)
      (continuous_const.clm_comp continuous_id)).cast rfl T₁.comp_id.symm
  have hγ₁ : ∀ t, (γ₁ t).IsFredholm := by
    intro t
    simpa only [γ₁, Path.cast_coe, Path.map_coe, Function.comp_apply] using
      hT₁.comp (hγC t).isFredholm
  exact hpath₀.trans ⟨γ₁, hγ₁⟩

/-- Two elements of the Fredholm locus are connected by a norm-continuous path precisely
when their indices agree. The topology is the subtype topology of `E →L[ℂ] F`. -/
@[simp]
theorem ContinuousLinearMap.nonempty_path_iff_index_eq
    (S T : {T : E →L[ℂ] F // T.IsFredholm}) :
    Nonempty (Path S T) ↔ S.val.index = T.val.index := by
  constructor
  · rintro ⟨γ⟩
    exact (γ.map continuous_subtype_val).index_eq fun t ↦ (γ t).property
  · intro hind
    exact (joinedIn_iff_joined (F := {U : E →L[ℂ] F | U.IsFredholm})
      (x := S.val) (y := T.val) S.property T.property).mp
      (S.property.exists_path_of_index_eq T.property hind)

/-- Two Fredholm operators between complex Hilbert spaces define the same path component in
`ZerothHomotopy` if and only if they have the same Fredholm index. -/
@[simp]
theorem ZerothHomotopy.mk_eq_mk_iff_index_eq
    (S T : {T : E →L[ℂ] F // T.IsFredholm}) :
    ZerothHomotopy.mk S = ZerothHomotopy.mk T ↔ S.val.index = T.val.index :=
  ⟨fun h ↦ (ContinuousLinearMap.nonempty_path_iff_index_eq S T).mp (Quotient.exact h),
    fun h ↦ let ⟨γ⟩ := (ContinuousLinearMap.nonempty_path_iff_index_eq S T).mpr h
      ZerothHomotopy.sound γ⟩

/-- For complex Hilbert spaces `E` and `F`, the Fredholm index is injective on the path components
of the Fredholm locus. -/
theorem ZerothHomotopy.fredholmIndex_injective :
    Function.Injective (ZerothHomotopy.fredholmIndex (𝕜 := ℂ) (E := E) (F := F)) :=
  ZerothHomotopy.rec fun S ↦ ZerothHomotopy.rec fun T h ↦
    (ZerothHomotopy.mk_eq_mk_iff_index_eq S T).mpr h

/-- If `E` and `F` are continuously linearly equivalent infinite-dimensional complex Hilbert spaces,
the Fredholm index identifies the norm-path components of the Fredholm locus `{T : E →L[ℂ] F //
T.IsFredholm}` bijectively with `ℤ`. -/
def ContinuousLinearEquiv.zerothHomotopyFredholmEquivInt (e : E ≃L[ℂ] F)
    (hE : ¬ FiniteDimensional ℂ E) :
    ZerothHomotopy {T : E →L[ℂ] F // T.IsFredholm} ≃ ℤ :=
  Equiv.ofBijective ZerothHomotopy.fredholmIndex
    ⟨ZerothHomotopy.fredholmIndex_injective, fun n ↦ by
      obtain ⟨T, hT⟩ := e.exists_index_eq hE n
      exact ⟨.mk T, hT⟩⟩

/-- Forward application of `ContinuousLinearEquiv.zerothHomotopyFredholmEquivInt` is the Fredholm
index on path components. -/
@[simp]
theorem ContinuousLinearEquiv.zerothHomotopyFredholmEquivInt_apply (e : E ≃L[ℂ] F)
    (hE : ¬ FiniteDimensional ℂ E) (c : ZerothHomotopy {T : E →L[ℂ] F // T.IsFredholm}) :
    e.zerothHomotopyFredholmEquivInt hE c = c.fredholmIndex := (rfl)

/-- The inverse of `ContinuousLinearEquiv.zerothHomotopyFredholmEquivInt` sends `n : ℤ` to the path
component of Fredholm index `n`. -/
@[simp]
theorem ContinuousLinearEquiv.fredholmIndex_zerothHomotopyFredholmEquivInt_symm (e : E ≃L[ℂ] F)
    (hE : ¬ FiniteDimensional ℂ E) (n : ℤ) :
    ((e.zerothHomotopyFredholmEquivInt hE).symm n).fredholmIndex = n :=
  (e.zerothHomotopyFredholmEquivInt hE).apply_symm_apply n

/-- If `E` and `F` are unitarily equivalent infinite-dimensional complex Hilbert spaces, the
Fredholm index identifies the norm-path components of `{T : E →L[ℂ] F // T.IsFredholm}` bijectively
with `ℤ`. -/
def LinearIsometryEquiv.zerothHomotopyFredholmEquivInt (e : E ≃ₗᵢ[ℂ] F)
    (hE : ¬ FiniteDimensional ℂ E) :
    ZerothHomotopy {T : E →L[ℂ] F // T.IsFredholm} ≃ ℤ :=
  e.toContinuousLinearEquiv.zerothHomotopyFredholmEquivInt hE

/-- Forward application of `LinearIsometryEquiv.zerothHomotopyFredholmEquivInt` is the Fredholm
index on path components. -/
@[simp]
theorem LinearIsometryEquiv.zerothHomotopyFredholmEquivInt_apply (e : E ≃ₗᵢ[ℂ] F)
    (hE : ¬ FiniteDimensional ℂ E) (c : ZerothHomotopy {T : E →L[ℂ] F // T.IsFredholm}) :
    e.zerothHomotopyFredholmEquivInt hE c = c.fredholmIndex := (rfl)

/-- The inverse of `LinearIsometryEquiv.zerothHomotopyFredholmEquivInt` sends `n : ℤ` to the path
component of Fredholm index `n`. -/
@[simp]
theorem LinearIsometryEquiv.fredholmIndex_zerothHomotopyFredholmEquivInt_symm (e : E ≃ₗᵢ[ℂ] F)
    (hE : ¬ FiniteDimensional ℂ E) (n : ℤ) :
    ((e.zerothHomotopyFredholmEquivInt hE).symm n).fredholmIndex = n :=
  (e.zerothHomotopyFredholmEquivInt hE).apply_symm_apply n

/-- On an infinite-dimensional complex Hilbert space `E`, the Fredholm index identifies the
norm-path components of `{T : E →L[ℂ] E // T.IsFredholm}` bijectively with `ℤ`. -/
def ContinuousLinearMap.zerothHomotopyFredholmSelfEquivInt (hE : ¬ FiniteDimensional ℂ E) :
    ZerothHomotopy {T : E →L[ℂ] E // T.IsFredholm} ≃ ℤ :=
  (ContinuousLinearEquiv.refl ℂ E).zerothHomotopyFredholmEquivInt hE

/-- Forward application of `ContinuousLinearMap.zerothHomotopyFredholmSelfEquivInt` is the Fredholm
index on path components. -/
@[simp]
theorem ContinuousLinearMap.zerothHomotopyFredholmSelfEquivInt_apply
    (hE : ¬ FiniteDimensional ℂ E) (c : ZerothHomotopy {T : E →L[ℂ] E // T.IsFredholm}) :
    zerothHomotopyFredholmSelfEquivInt hE c = c.fredholmIndex := (rfl)

/-- The inverse of `ContinuousLinearMap.zerothHomotopyFredholmSelfEquivInt` sends `n : ℤ` to the
path component of Fredholm index `n`. -/
@[simp]
theorem ContinuousLinearMap.fredholmIndex_zerothHomotopyFredholmSelfEquivInt_symm
    (hE : ¬ FiniteDimensional ℂ E) (n : ℤ) :
    ((zerothHomotopyFredholmSelfEquivInt hE).symm n).fredholmIndex = n :=
  (zerothHomotopyFredholmSelfEquivInt hE).apply_symm_apply n

end Hilbert
