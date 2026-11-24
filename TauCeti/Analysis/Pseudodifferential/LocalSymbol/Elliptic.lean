/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Pseudodifferential.LocalSymbol.Principal
import TauCeti.Analysis.Calculus.ContinuousLinearMapInverse

/-!
# Elliptic classical symbols on an open set

For an open set `U ⊆ ℝⁿ` of positions, a homogeneous symbol `a` on `U`
(`TauCeti.LocalHomogeneousSymbol`) is *elliptic* when its value `a (x, ξ)` is invertible at every
position `x ∈ U` and every nonzero frequency `ξ`; a classical symbol on `U`
(`TauCeti.LocalClassicalSymbol`) is elliptic when its principal symbol is. This is the ellipticity
of a classical pseudodifferential operator read in a chart of a manifold, and the pointwise inverse
of its principal symbol is the leading term of a local parametrix. Nothing is asked of positions
outside `U`, so the restriction to `U` of a symbol on `ℝⁿ` can be elliptic on `U` without being
elliptic on `ℝⁿ`.

* `TauCeti.LocalHomogeneousSymbol.IsElliptic` and `TauCeti.LocalClassicalSymbol.IsElliptic`:
  ellipticity on `U`; it passes to smaller open sets (`IsElliptic.restrict`), the restriction of a
  classical symbol on `ℝⁿ` to `U` is elliptic exactly when its principal symbol is invertible over
  `U` (`TauCeti.ClassicalSymbol.isElliptic_restrict_iff`), and over `U = ℝⁿ` it is the
  ellipticity of `TauCeti.ClassicalSymbol`.
* `TauCeti.LocalClassicalSymbol.isElliptic_add_iff`: ellipticity does not see terms of order
  `m - 1`.
* `TauCeti.LocalHomogeneousSymbol.inverse`: for an elliptic `a` of degree `m` on `U` with a
  complete source space, the homogeneous symbol `(x, ξ) ↦ a (x, ξ)⁻¹` of degree `-m` on `U`. It is
  the unique left or right inverse of `a` over `U` (`eq_inverse_of_comp_eq_id_left`,
  `eq_inverse_of_comp_eq_id_right`), and it commutes with restriction to smaller open sets and with
  the restriction of homogeneous symbols on `ℝⁿ`.
* `TauCeti.LocalClassicalSymbol.existsUnique_inversePrincipalSymbol`: the principal symbol of an
  elliptic classical symbol on `U` has a unique two-sided inverse over `U` at nonzero frequencies
  that is a homogeneous symbol of degree `-m` on `U`.
* `TauCeti.LocalClassicalSymbol.IsElliptic.finrank_eq`: in positive dimension, ellipticity on a
  nonempty open set forces the two fibres to have the same dimension.

## References

* M. E. Taylor, *Pseudodifferential Operators: Four Lectures at MSRI*, September 2008,
  Lecture I, (4.1)–(4.6).
* L. Hörmander, *The Analysis of Linear Partial Differential Operators III*, §18.1.
-/

public section

noncomputable section

open Set

namespace TauCeti

variable {n : ℕ}

namespace LocalHomogeneousSymbol

variable {U U' : TopologicalSpace.Opens (CoordinateSpace n)} {V W : Type*}
  [NormedAddCommGroup V] [NormedSpace ℂ V] [NormedAddCommGroup W] [NormedSpace ℂ W] {m : ℝ}

/-! ### Elliptic homogeneous symbols on `U` -/

section IsElliptic

/-- A homogeneous symbol on `U` is *elliptic* if its value at every position of `U` and every
nonzero frequency is an invertible continuous linear map. -/
def IsElliptic (a : LocalHomogeneousSymbol U V W m) : Prop :=
  ∀ x ∈ U, ∀ ξ, ξ ≠ 0 → (a.coefficient (x, ξ)).IsInvertible

theorem isElliptic_iff {a : LocalHomogeneousSymbol U V W m} :
    a.IsElliptic ↔ ∀ x ∈ U, ∀ ξ, ξ ≠ 0 → (a.coefficient (x, ξ)).IsInvertible :=
  Iff.rfl

/-- Transport along an equality of degrees does not change ellipticity. -/
@[simp]
theorem isElliptic_castDegree_iff {m' : ℝ} (h : m = m') {a : LocalHomogeneousSymbol U V W m} :
    (a.castDegree h).IsElliptic ↔ a.IsElliptic := by
  simp only [isElliptic_iff, coefficient_castDegree]

/-- Multiplying by a nonzero complex number does not change ellipticity. -/
@[simp]
theorem isElliptic_smul_iff {c : ℂ} (hc : c ≠ 0) {a : LocalHomogeneousSymbol U V W m} :
    (c • a).IsElliptic ↔ a.IsElliptic := by
  simp only [isElliptic_iff, coefficient_smul, Pi.smul_apply,
    ContinuousLinearMap.isInvertible_smul_iff hc]

/-- An elliptic homogeneous symbol on `U` restricts to an elliptic homogeneous symbol on every
smaller open set. -/
theorem IsElliptic.restrict {a : LocalHomogeneousSymbol U V W m} (ha : a.IsElliptic)
    (h : U' ≤ U) : (restrict h a).IsElliptic := fun x hx ξ hξ => by
  rw [coefficient_restrict_of_mem h a hx]
  exact ha x (h hx) ξ hξ

/-- Over a nontrivial frequency space, a homogeneous symbol that is elliptic on a nonempty open set
identifies its two fibres by a continuous linear equivalence. -/
theorem IsElliptic.nonempty_continuousLinearEquiv [Nontrivial (CoordinateSpace n)]
    {a : LocalHomogeneousSymbol U V W m} (ha : a.IsElliptic)
    (hU : (U : Set (CoordinateSpace n)).Nonempty) : Nonempty (V ≃L[ℂ] W) := by
  obtain ⟨x, hx⟩ := hU
  obtain ⟨ξ, hξ⟩ := exists_ne (0 : CoordinateSpace n)
  obtain ⟨e, -⟩ := ha x hx ξ hξ
  exact ⟨e⟩

/-- **Ellipticity forces equal ranks.** Over a nontrivial frequency space, the fibres of a
homogeneous symbol that is elliptic on a nonempty open set have the same dimension. Both
hypotheses are needed: every symbol is elliptic on the empty set, and over the zero frequency
space every symbol is elliptic. -/
theorem IsElliptic.finrank_eq [Nontrivial (CoordinateSpace n)]
    {a : LocalHomogeneousSymbol U V W m} (ha : a.IsElliptic)
    (hU : (U : Set (CoordinateSpace n)).Nonempty) :
    Module.finrank ℂ V = Module.finrank ℂ W :=
  (ha.nonempty_continuousLinearEquiv hU).some.toLinearEquiv.finrank_eq

end IsElliptic

/-! ### The inverse of an elliptic homogeneous symbol on `U` -/

section Inverse

variable [CompleteSpace V] (a : LocalHomogeneousSymbol U V W m) (ha : a.IsElliptic)

/-- The inverse `(x, ξ) ↦ a (x, ξ)⁻¹` of an elliptic homogeneous symbol `a` of degree `m` on `U`,
a homogeneous symbol of degree `-m` on `U`. -/
def inverse (a : LocalHomogeneousSymbol U V W m) (ha : a.IsElliptic) :
    LocalHomogeneousSymbol U W V (-m) where
  coefficient p := (a.coefficient p).inverse
  coefficient_of_notMem x hx ξ := by simp [a.coefficient_of_notMem x hx ξ]
  zero_covector x := by simp
  contDiffOn_coefficient := a.contDiffOn_coefficient.clm_inverse fun p hp => ha p.1 hp.1 p.2 hp.2
  homogeneous x ξ t ht := by
    rw [a.homogeneous x ξ t ht, ContinuousLinearMap.inverse_smul_of_isScalarTower,
      Real.rpow_neg ht.le]

@[simp]
theorem coefficient_inverse (p : CoordinateSpace n × CoordinateSpace n) :
    (a.inverse ha).coefficient p = (a.coefficient p).inverse :=
  (rfl)

/-- At a position of `U` and a nonzero frequency, the inverse is a left inverse. -/
theorem coefficient_inverse_comp_coefficient {x : CoordinateSpace n} (hx : x ∈ U)
    {ξ : CoordinateSpace n} (hξ : ξ ≠ 0) :
    (a.inverse ha).coefficient (x, ξ) ∘L a.coefficient (x, ξ) = ContinuousLinearMap.id ℂ V :=
  (ha x hx ξ hξ).inverse_comp_self

/-- At a position of `U` and a nonzero frequency, the inverse is a right inverse. -/
theorem coefficient_comp_coefficient_inverse {x : CoordinateSpace n} (hx : x ∈ U)
    {ξ : CoordinateSpace n} (hξ : ξ ≠ 0) :
    a.coefficient (x, ξ) ∘L (a.inverse ha).coefficient (x, ξ) = ContinuousLinearMap.id ℂ W :=
  (ha x hx ξ hξ).self_comp_inverse

/-- The inverse of an elliptic homogeneous symbol on `U` is elliptic. -/
theorem isElliptic_inverse : (a.inverse ha).IsElliptic :=
  fun x hx ξ hξ => (ha x hx ξ hξ).inverse

/-- A homogeneous symbol of degree `-m` on `U` that is a left inverse of `a` at every position of
`U` and every nonzero frequency is the inverse of `a`. -/
theorem eq_inverse_of_comp_eq_id_left {b : LocalHomogeneousSymbol U W V (-m)}
    (h : ∀ x ∈ U, ∀ ξ, ξ ≠ 0 →
      b.coefficient (x, ξ) ∘L a.coefficient (x, ξ) = ContinuousLinearMap.id ℂ V) :
    b = a.inverse ha :=
  ext_of_mem fun x hx ξ hξ => (ha x hx ξ hξ).eq_inverse_of_comp_eq_id_left (h x hx ξ hξ)

/-- A homogeneous symbol of degree `-m` on `U` that is a right inverse of `a` at every position of
`U` and every nonzero frequency is the inverse of `a`. -/
theorem eq_inverse_of_comp_eq_id_right {b : LocalHomogeneousSymbol U W V (-m)}
    (h : ∀ x ∈ U, ∀ ξ, ξ ≠ 0 →
      a.coefficient (x, ξ) ∘L b.coefficient (x, ξ) = ContinuousLinearMap.id ℂ W) :
    b = a.inverse ha :=
  ext_of_mem fun x hx ξ hξ => (ha x hx ξ hξ).eq_inverse_of_comp_eq_id_right (h x hx ξ hξ)

/-- The inverse of the inverse is the original symbol. -/
@[simp]
theorem inverse_inverse [CompleteSpace W] :
    (a.inverse ha).inverse (a.isElliptic_inverse ha) = a.castDegree (neg_neg m).symm :=
  ext_of_mem fun x hx ξ hξ => by simp [(ha x hx ξ hξ).inverse_inverse]

/-- The inverse commutes with restriction to a smaller open set. -/
theorem restrict_inverse (h : U' ≤ U) :
    restrict h (a.inverse ha) = (restrict h a).inverse (ha.restrict h) :=
  ext_of_mem fun x hx ξ _ => by simp [coefficient_restrict_of_mem h _ hx]

end Inverse

end LocalHomogeneousSymbol

namespace HomogeneousSymbol

variable {U : TopologicalSpace.Opens (CoordinateSpace n)} {V W : Type*}
  [NormedAddCommGroup V] [NormedSpace ℂ V] [NormedAddCommGroup W] [NormedSpace ℂ W] {m : ℝ}

/-- The restriction of a homogeneous symbol on `ℝⁿ` to `U` is elliptic exactly when the symbol is
invertible at every position of `U` and every nonzero frequency. -/
theorem isElliptic_restrict_iff
    {a : HomogeneousSymbol (CoordinateSpace n) (CoordinateSpace n) V W m} :
    (restrict U a).IsElliptic ↔ ∀ x ∈ U, ∀ ξ, ξ ≠ 0 → (a.coefficient (x, ξ)).IsInvertible := by
  refine forall₂_congr fun x hx => ?_
  simp only [coefficient_restrict_of_mem a hx]

/-- The restriction of an elliptic homogeneous symbol on `ℝⁿ` to an open set is elliptic. -/
theorem IsElliptic.restrict {a : HomogeneousSymbol (CoordinateSpace n) (CoordinateSpace n) V W m}
    (ha : a.IsElliptic) : (restrict U a).IsElliptic :=
  isElliptic_restrict_iff.2 fun x _ ξ hξ => isElliptic_iff.1 ha x ξ hξ

/-- The inverse commutes with the restriction of homogeneous symbols on `ℝⁿ` to an open set. -/
theorem restrict_inverse [CompleteSpace V]
    (a : HomogeneousSymbol (CoordinateSpace n) (CoordinateSpace n) V W m) (ha : a.IsElliptic) :
    restrict U (a.inverse ha) = (restrict U a).inverse ha.restrict :=
  LocalHomogeneousSymbol.ext_of_mem fun x hx ξ _ => by simp [hx]

end HomogeneousSymbol

namespace LocalClassicalSymbol

variable {U U' : TopologicalSpace.Opens (CoordinateSpace n)} {V W : Type*}
  [NormedAddCommGroup V] [NormedSpace ℂ V] [NormedAddCommGroup W] [NormedSpace ℂ W] {m : ℝ}

/-! ### Elliptic classical symbols on `U` -/

/-- A classical symbol on `U` is *elliptic* if its principal symbol is: its value at every position
of `U` and every nonzero frequency is an invertible continuous linear map. -/
def IsElliptic (a : LocalClassicalSymbol U V W m) : Prop :=
  a.principal.IsElliptic

/-- Ellipticity of a classical symbol on `U` is ellipticity of its principal symbol, whose
pointwise inverse is then `TauCeti.LocalHomogeneousSymbol.inverse`. -/
theorem isElliptic_def {a : LocalClassicalSymbol U V W m} :
    a.IsElliptic ↔ a.principal.IsElliptic :=
  Iff.rfl

/-- A classical symbol on `U` is elliptic when its principal symbol is invertible at every position
of `U` and every nonzero frequency. -/
theorem isElliptic_iff {a : LocalClassicalSymbol U V W m} :
    a.IsElliptic ↔ ∀ x ∈ U, ∀ ξ, ξ ≠ 0 → (a.principal.coefficient (x, ξ)).IsInvertible :=
  Iff.rfl

/-- The classical symbol `χ(ξ) a(x, ξ)` of a single homogeneous term on `U` is elliptic exactly
when the term is. -/
@[simp]
theorem isElliptic_ofHomogeneous_iff (χ : FrequencyCutoff (CoordinateSpace n))
    {a : LocalHomogeneousSymbol U V W m} : (ofHomogeneous χ a).IsElliptic ↔ a.IsElliptic := by
  rw [isElliptic_def, principal_ofHomogeneous]

/-- Multiplying by a nonzero complex number does not change ellipticity. -/
@[simp]
theorem isElliptic_smul_iff {c : ℂ} (hc : c ≠ 0) {a : LocalClassicalSymbol U V W m} :
    (c • a).IsElliptic ↔ a.IsElliptic := by
  rw [isElliptic_def, principal_smul, LocalHomogeneousSymbol.isElliptic_smul_iff hc,
    isElliptic_def]

/-- Adding a classical symbol with vanishing principal symbol, that is, of order `m - 1` on `U`
(`TauCeti.LocalClassicalSymbol.principal_eq_zero_iff`), does not change ellipticity. -/
theorem isElliptic_add_iff {a b : LocalClassicalSymbol U V W m} (hb : b.principal = 0) :
    (a + b).IsElliptic ↔ a.IsElliptic := by
  rw [isElliptic_def, principal_add, hb, add_zero, isElliptic_def]

/-- An elliptic classical symbol on `U` restricts to an elliptic classical symbol on every smaller
open set. -/
theorem IsElliptic.restrict {a : LocalClassicalSymbol U V W m} (ha : a.IsElliptic) (h : U' ≤ U) :
    (restrict h a).IsElliptic := by
  rw [isElliptic_def, principal_restrict]
  exact LocalHomogeneousSymbol.IsElliptic.restrict ha h

/-- **Ellipticity forces equal ranks.** Over a nontrivial frequency space, the fibres of a
classical symbol that is elliptic on a nonempty open set have the same dimension. -/
theorem IsElliptic.finrank_eq [Nontrivial (CoordinateSpace n)] {a : LocalClassicalSymbol U V W m}
    (ha : a.IsElliptic) (hU : (U : Set (CoordinateSpace n)).Nonempty) :
    Module.finrank ℂ V = Module.finrank ℂ W :=
  LocalHomogeneousSymbol.IsElliptic.finrank_eq ha hU

/-- **The inverse principal symbol.** The principal symbol `a_m` of an elliptic classical symbol of
order `m` on `U` has a unique two-sided inverse at every position of `U` and every nonzero
frequency that is a homogeneous symbol of degree `-m` on `U`, namely
`TauCeti.LocalHomogeneousSymbol.inverse`. -/
theorem existsUnique_inversePrincipalSymbol [CompleteSpace V] {a : LocalClassicalSymbol U V W m}
    (ha : a.IsElliptic) :
    ∃! b : LocalHomogeneousSymbol U W V (-m), ∀ x ∈ U, ∀ ξ, ξ ≠ 0 →
      b.coefficient (x, ξ) ∘L a.principal.coefficient (x, ξ) = ContinuousLinearMap.id ℂ V ∧
        a.principal.coefficient (x, ξ) ∘L b.coefficient (x, ξ) = ContinuousLinearMap.id ℂ W :=
  ⟨a.principal.inverse ha, fun _ hx _ hξ =>
    ⟨LocalHomogeneousSymbol.coefficient_inverse_comp_coefficient _ ha hx hξ,
      LocalHomogeneousSymbol.coefficient_comp_coefficient_inverse _ ha hx hξ⟩,
    fun _ hb => LocalHomogeneousSymbol.eq_inverse_of_comp_eq_id_left _ ha fun x hx ξ hξ =>
      (hb x hx ξ hξ).1⟩

end LocalClassicalSymbol

namespace ClassicalSymbol

variable {U : TopologicalSpace.Opens (CoordinateSpace n)} {V W : Type*}
  [NormedAddCommGroup V] [NormedSpace ℂ V] [NormedAddCommGroup W] [NormedSpace ℂ W] {m : ℝ}

/-- The restriction of a classical symbol on `ℝⁿ` to `U` is elliptic exactly when its principal
symbol is invertible at every position of `U` and every nonzero frequency. -/
theorem isElliptic_restrict_iff {a : ClassicalSymbol n V W m} :
    (restrict U a).IsElliptic ↔
      ∀ x ∈ U, ∀ ξ, ξ ≠ 0 → (a.principal.coefficient (x, ξ)).IsInvertible := by
  rw [LocalClassicalSymbol.isElliptic_def, principal_restrict,
    HomogeneousSymbol.isElliptic_restrict_iff]

/-- The restriction of an elliptic classical symbol on `ℝⁿ` to an open set is elliptic. -/
theorem IsElliptic.restrict {a : ClassicalSymbol n V W m} (ha : a.IsElliptic) :
    (restrict U a).IsElliptic :=
  isElliptic_restrict_iff.2 fun x _ ξ hξ => isElliptic_iff.1 ha x ξ hξ

/-- Over `U = ℝⁿ`, ellipticity of classical symbols on an open set is ellipticity of classical
symbols on `ℝⁿ`. -/
@[simp]
theorem isElliptic_restrictTopEquiv_iff {a : ClassicalSymbol n V W m} :
    (restrictTopEquiv a).IsElliptic ↔ a.IsElliptic := by
  rw [← restrict_top, isElliptic_restrict_iff, isElliptic_iff]
  simp

end ClassicalSymbol

end TauCeti
