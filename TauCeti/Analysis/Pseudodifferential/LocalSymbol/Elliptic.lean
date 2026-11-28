/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Pseudodifferential.LocalSymbol.Principal
public import TauCeti.Analysis.Pseudodifferential.Symbol.Elliptic
import TauCeti.Analysis.Calculus.BumpFunction.Cutoff
import TauCeti.Analysis.Calculus.ContinuousLinearMapInverse
import TauCeti.Topology.Algebra.Module.ContinuousLinearMap.Invertible

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
* `TauCeti.HomogeneousSymbol.eventually_forall_isInvertible_coefficient`: invertibility of a
  homogeneous symbol on `ℝⁿ` at every nonzero frequency is an open condition on the position.
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
* `TauCeti.LocalClassicalSymbol.IsElliptic.exists_isInvertible_and_norm_inverse_le`: on every
  compact set `K ⊆ U` the full symbol `a(x, ξ)` is invertible at large frequencies, with
  `‖a(x, ξ)⁻¹‖ ≤ C ⟨ξ⟩^(-m)`, so a symbol on `ℝⁿ` that agrees with `a` on `K` is elliptic there in
  the sense of `TauCeti.Symbol.IsEllipticOn`
  (`TauCeti.LocalClassicalSymbol.IsElliptic.exists_isEllipticOn`).
* `TauCeti.LocalClassicalSymbol.IsElliptic.exists_eventually_comp_eq_id`: a symbol on `ℝⁿ` that
  agrees with `a` near a position `x ∈ U` has an inverse symbol of order `-m` at large frequencies
  near `x`. A cut-off extension of `a` is elliptic only where the cutoff is `1`, so this is the
  form in which the elliptic regularity of an operator read in a chart is proved
  (`TauCeti.LocalClassicalSymbol.IsElliptic.isLocallySobolevAt_of_quantizeDistribution`).
* `TauCeti.ClassicalSymbol.exists_isEllipticOn_of_isElliptic_restrict`,
  `TauCeti.ClassicalSymbol.exists_comp_eq_id_of_isElliptic_restrict`: if the restriction of a
  classical symbol on `ℝⁿ` to `U` is elliptic, the symbol is elliptic at large frequencies over
  each compact `K ⊆ U` and has an inverse symbol of order `-m` there near `K`.

## References

* M. E. Taylor, *Pseudodifferential Operators: Four Lectures at MSRI*, September 2008,
  Lecture I, (4.1)–(4.6).
* L. Hörmander, *The Analysis of Linear Partial Differential Operators III*, §18.1.
-/

public section

noncomputable section

open Set
open scoped Topology

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

/-- **Invertibility is an open condition in the position.** If a homogeneous symbol on `ℝⁿ` is
invertible at a position `x` at every nonzero frequency, then so it is at every position near `x`:
by homogeneity it suffices to look at the compact unit sphere of frequencies. -/
theorem eventually_forall_isInvertible_coefficient [CompleteSpace V]
    (a : HomogeneousSymbol (CoordinateSpace n) (CoordinateSpace n) V W m) {x : CoordinateSpace n}
    (ha : ∀ ξ, ξ ≠ 0 → (a.coefficient (x, ξ)).IsInvertible) :
    ∀ᶠ y in 𝓝 x, ∀ ξ, ξ ≠ 0 → (a.coefficient (y, ξ)).IsInvertible := by
  -- `a` is invertible at `(y, ξ)` for `y` near `x` and `‖ξ‖ = 1`.
  have hS : ∀ᶠ y in 𝓝 x, ∀ ξ ∈ Metric.sphere (0 : CoordinateSpace n) 1,
      (a.coefficient (y, ξ)).IsInvertible := by
    refine (isCompact_sphere _ _).eventually_forall_of_forall_eventually fun ξ hξ ↦ ?_
    have hξ0 : ξ ≠ 0 := Metric.ne_of_mem_sphere hξ one_ne_zero
    have hcont : ContinuousAt a.coefficient (x, ξ) :=
      a.continuousOn_coefficient.continuousAt
        ((isOpen_ne_fun continuous_snd continuous_const).mem_nhds hξ0)
    exact hcont.eventually (ha ξ hξ0).eventually_nhds
  -- By homogeneity it is invertible at every nonzero frequency.
  filter_upwards [hS] with y hy ξ hξ
  have hn : 0 < ‖ξ‖ := norm_pos_iff.2 hξ
  have hscal : a.coefficient (y, ξ) = ((‖ξ‖ ^ m : ℝ) : ℂ) • a.coefficient (y, ‖ξ‖⁻¹ • ξ) := by
    rw [Complex.coe_smul, ← a.homogeneous y _ _ hn, smul_inv_smul₀ hn.ne']
  rw [hscal, ContinuousLinearMap.isInvertible_smul_iff
    (Complex.ofReal_ne_zero.2 (Real.rpow_pos_of_pos hn m).ne')]
  exact hy _ (by simp [norm_smul, hn.ne'])

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

/-- **Invertibility of an elliptic symbol at large frequencies.** On every compact set `K ⊆ U` of
positions, the full symbol `a(x, ξ)` of an elliptic classical symbol of order `m` on `U` is
invertible at all frequencies of norm at least some radius `R`, with `‖a(x, ξ)⁻¹‖ ≤ C ⟨ξ⟩^(-m)`. -/
theorem IsElliptic.exists_isInvertible_and_norm_inverse_le [CompleteSpace V]
    {a : LocalClassicalSymbol U V W m} (ha : a.IsElliptic) {K : Set (CoordinateSpace n)}
    (hKU : K ⊆ U) (hK : IsCompact K) :
    ∃ R C : ℝ, ∀ x ∈ K, ∀ ξ, R ≤ ‖ξ‖ → (a.toLocalSymbol.coefficient (x, ξ)).IsInvertible ∧
      ‖(a.toLocalSymbol.coefficient (x, ξ)).inverse‖ ≤ C * (1 + ‖ξ‖ ^ 2) ^ (-m / 2) := by
  -- Near `K`, `a` agrees with its cut-off extension `ψ a` to `ℝⁿ`, for a cutoff `ψ = 1` on `K`.
  obtain ⟨ψ, hψ, -, hψ1, -, hψU⟩ := hK.exists_contDiff_cutoff_eventuallyEq_one U.isOpen hKU
  have hψK (x : CoordinateSpace n) (hx : x ∈ K) : ψ x = 1 := (hψ1 x hx).self_of_nhds
  -- On `K`, the inverse of the principal symbol is the cut-off extension of the local inverse
  -- for `‖ξ‖ ≥ 2`, which is bounded by `C₀ ⟨ξ⟩^(-m)`.
  obtain ⟨C₀, hC₀⟩ := (HomogeneousSymbol.cutoffSymbol default (LocalHomogeneousSymbol.extend ψ
    hψ hψU (a.principal.inverse ha))).exists_norm_coefficient_le K hK
  obtain ⟨R, C, h⟩ := (extend ψ hψ hψU a).exists_isInvertible_and_norm_inverse_le_of_principal hK
    (Γ := Set.univ) (C₀ := C₀) fun x hx ξ _ h2 ↦ by
      have hM := hC₀ x hx ξ
      rw [HomogeneousSymbol.coefficient_cutoffSymbol_of_two_le_norm _ _ h2] at hM
      simp only [principal_extend, LocalHomogeneousSymbol.coefficient_extend, hψK x hx,
        one_smul] at hM ⊢
      exact ⟨isElliptic_iff.1 ha x (hKU hx) ξ (norm_pos_iff.1 (by linarith)), hM⟩
  refine ⟨R, C, fun x hx ξ hξ ↦ ?_⟩
  simpa [LocalSymbol.coefficient_extend, hψK x hx] using h x hx ξ (Set.mem_univ ξ) hξ

/-- **Ellipticity on compact sets of positions.** If a symbol `p` on `ℝⁿ` agrees with an elliptic
classical symbol `a` on `U` at the positions of a compact set `K ⊆ U`, for instance a cut-off
extension of `a` by a cutoff equal to `1` on `K`, then `p` is elliptic on `K` at the frequencies of
norm at least some radius `R`, in the sense of `TauCeti.Symbol.IsEllipticOn`. -/
theorem IsElliptic.exists_isEllipticOn [CompleteSpace V] {a : LocalClassicalSymbol U V W m}
    (ha : a.IsElliptic) {K : Set (CoordinateSpace n)} (hKU : K ⊆ U) (hK : IsCompact K)
    {p : Symbol n V W m}
    (hpa : ∀ x ∈ K, ∀ ξ, p.coefficient (x, ξ) = a.toLocalSymbol.coefficient (x, ξ)) :
    ∃ R, p.IsEllipticOn {q | q.1 ∈ K ∧ R ≤ ‖q.2‖} := by
  obtain ⟨R, C, hC⟩ := ha.exists_isInvertible_and_norm_inverse_le hKU hK
  refine ⟨R, Symbol.isEllipticOn_iff.2 fun _ _ ↦ ⟨C, fun ⟨x, ξ⟩ hq _ ↦ ?_⟩⟩
  rw [hpa x hq.1 ξ]
  exact hC x hq.1 ξ hq.2

/-- **Local inverse symbols.** If a symbol `p` on `ℝⁿ` agrees near a position `x ∈ U` with an
elliptic classical symbol `a` on `U`, then a symbol of order `-m` on `ℝⁿ` inverts `p` on both
sides at all large frequencies and all positions near `x`. This inverts an operator on a manifold,
read in a chart through a cut-off extension of its symbol, near the points where the cutoff is
`1`. -/
theorem IsElliptic.exists_eventually_comp_eq_id [CompleteSpace V]
    {a : LocalClassicalSymbol U V W m} (ha : a.IsElliptic) {p : Symbol n V W m}
    {x : CoordinateSpace n} (hx : x ∈ U)
    (hpa : ∀ᶠ y in 𝓝 x, ∀ ξ, p.coefficient (y, ξ) = a.toLocalSymbol.coefficient (y, ξ)) :
    ∃ (e : Symbol n W V (-m)) (R : ℝ), ∀ᶠ y in 𝓝 x, ∀ ξ, R ≤ ‖ξ‖ →
      e.coefficient (y, ξ) ∘L p.coefficient (y, ξ) = .id ℂ V ∧
        p.coefficient (y, ξ) ∘L e.coefficient (y, ξ) = .id ℂ W := by
  -- A closed ball `K` around `x`, inside `U`, on which `p = a`; `p` is elliptic on `K`.
  obtain ⟨δ, hδ, hδU⟩ := Metric.mem_nhds_iff.1 (Filter.inter_mem (U.isOpen.mem_nhds hx) hpa)
  have hK : Metric.closedBall x (δ / 2) ⊆ _ :=
    (Metric.closedBall_subset_ball (half_lt_self hδ)).trans hδU
  obtain ⟨R, hR⟩ := ha.exists_isEllipticOn (fun y hy ↦ (hK hy).1) (isCompact_closedBall x _)
    fun y hy ↦ (hK hy).2
  have hKx : Metric.closedBall x (δ / 2) ∈ 𝓝ˢ {x} := by
    rw [nhdsSet_singleton]
    exact Metric.closedBall_mem_nhds x (half_pos hδ)
  simpa [nhdsSet_singleton] using
    (Symbol.exists_mem_nhdsSet_isEllipticOn_iff isCompact_singleton).1 ⟨_, hKx, R, hR⟩

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

/-- **Ellipticity on compact sets of positions.** If the restriction of a classical symbol `a` on
`ℝⁿ` to `U` is elliptic, then `a` is elliptic on every compact set `K ⊆ U` of positions at the
frequencies of norm at least some radius `R`, in the sense of `TauCeti.Symbol.IsEllipticOn`. -/
theorem exists_isEllipticOn_of_isElliptic_restrict [CompleteSpace V] {a : ClassicalSymbol n V W m}
    (ha : (restrict U a).IsElliptic) {K : Set (CoordinateSpace n)} (hKU : K ⊆ U)
    (hK : IsCompact K) : ∃ R, a.toSymbol.IsEllipticOn {p | p.1 ∈ K ∧ R ≤ ‖p.2‖} :=
  ha.exists_isEllipticOn hKU hK fun _ hx _ ↦ by
    rw [toLocalSymbol_restrict, Symbol.coefficient_restrict_of_mem _ (hKU hx)]

/-- **Local inverse symbols.** If the restriction of a classical symbol `a` on `ℝⁿ` to `U` is
elliptic and `K ⊆ U` is compact, then a symbol of order `-m` on `ℝⁿ` inverts `a` on both sides at
all large frequencies and all positions near `K`. -/
theorem exists_comp_eq_id_of_isElliptic_restrict [CompleteSpace V] {a : ClassicalSymbol n V W m}
    (ha : (restrict U a).IsElliptic) {K : Set (CoordinateSpace n)} (hKU : K ⊆ U)
    (hK : IsCompact K) :
    ∃ (b : Symbol n W V (-m)) (R : ℝ), ∀ᶠ y in 𝓝ˢ K, ∀ ξ, R ≤ ‖ξ‖ →
      b.coefficient (y, ξ) ∘L a.toSymbol.coefficient (y, ξ) = .id ℂ V ∧
        a.toSymbol.coefficient (y, ξ) ∘L b.coefficient (y, ξ) = .id ℂ W := by
  -- `a` is elliptic on a compact neighbourhood `L ⊆ U` of `K`.
  obtain ⟨L, hL, hKL, hLU⟩ := exists_compact_between hK U.isOpen hKU
  obtain ⟨R, hR⟩ := exists_isEllipticOn_of_isElliptic_restrict ha hLU hL
  exact (Symbol.exists_mem_nhdsSet_isEllipticOn_iff hK).1
    ⟨L, subset_interior_iff_mem_nhdsSet.1 hKL, R, hR⟩

end ClassicalSymbol

end TauCeti
