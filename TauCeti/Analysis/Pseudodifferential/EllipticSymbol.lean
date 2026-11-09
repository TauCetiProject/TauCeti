/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Operator.Banach
public import TauCeti.Analysis.Pseudodifferential.CutoffSymbol
public import TauCeti.Topology.Algebra.Module.ContinuousLinearMap.Invertible

/-!
# Elliptic homogeneous symbols and their inverses

A homogeneous symbol `a` of degree `m` is *elliptic* (`TauCeti.HomogeneousSymbol.IsElliptic`) if
its value `a(x, ξ) : V →L[ℂ] W` is an invertible continuous linear map at every position `x` and
every nonzero frequency `ξ`. Ellipticity of a pseudodifferential operator is ellipticity of its
principal symbol, and the inverse of the principal symbol is the leading term of a parametrix.

This file constructs that inverse and proves its basic properties:

* `TauCeti.HomogeneousSymbol.inverse`: for `V` complete, the pointwise inverse
  `a(x, ξ)⁻¹` of an elliptic homogeneous symbol of degree `m` is a homogeneous symbol of
  degree `-m`, smooth off `ξ = 0` because inversion is smooth on invertible maps. It is a
  two-sided inverse of `a` at every nonzero frequency
  (`TauCeti.HomogeneousSymbol.coefficient_inverse_comp_coefficient`,
  `TauCeti.HomogeneousSymbol.coefficient_comp_coefficient_inverse`), and it is the only
  homogeneous symbol that is a one-sided inverse of `a`
  (`TauCeti.HomogeneousSymbol.eq_inverse_of_comp_eq_id_left`,
  `TauCeti.HomogeneousSymbol.eq_inverse_of_comp_eq_id_right`);
* ellipticity and the inverse are compatible with the operations on homogeneous symbols:
  composition (where the inverse reverses the order), pullback of positions, change of degree,
  multiplication by a nonzero scalar, and inversion itself; the powers `‖ξ‖ ^ m` of the
  frequency norm are elliptic with inverse `‖ξ‖ ^ (-m)`;
* `TauCeti.HomogeneousSymbol.IsElliptic.exists_mul_norm_le_norm_coefficient_apply`: the elliptic
  estimate `‖ξ‖ ^ m ‖v‖ ≤ C ‖a(x, ξ) v‖` for positions in a compact set and a proper frequency
  space;
* `TauCeti.HomogeneousSymbol.IsElliptic.finrank_eq`: when there is a nonzero frequency, an
  elliptic symbol identifies `V` with `W`, so the fibres have the same rank. With
  no nonzero frequency, as on a zero-dimensional base, every symbol is elliptic
  (`TauCeti.HomogeneousSymbol.isElliptic_of_subsingleton`), and no rank condition follows;
* on `ℝⁿ`, the cut-off inverse is a two-sided inverse of the cut-off symbol modulo smoothing
  symbols: `χ(ξ) a(x, ξ)⁻¹ ∘ χ(ξ) a(x, ξ) - 1` vanishes for `‖ξ‖ ≥ 2`
  (`TauCeti.HomogeneousSymbol.isSmoothing_toSymbol_inverse_comp_toSymbol_sub`,
  `TauCeti.HomogeneousSymbol.isSmoothing_toSymbol_comp_toSymbol_inverse_sub`). This is the
  first step of the construction of a parametrix from the principal symbol.

## References

* M. Taylor, *Pseudodifferential Operators: Four Lectures at MSRI* (2008), Lecture I,
  (4.1)–(4.6).
* L. Hörmander, *The Analysis of Linear Partial Differential Operators III*, §18.1.
-/

public section

noncomputable section

open scoped ContDiff

namespace TauCeti

namespace HomogeneousSymbol

variable {X E : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [NormedAddCommGroup E]
  [NormedSpace ℝ E] {V W U : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]
  [NormedAddCommGroup W] [NormedSpace ℂ W] [NormedAddCommGroup U] [NormedSpace ℂ U] {m m' : ℝ}

/-! ### Ellipticity -/

/-- A homogeneous symbol is *elliptic* if its value at every position and every nonzero frequency
is an invertible continuous linear map. -/
def IsElliptic (a : HomogeneousSymbol X E V W m) : Prop :=
  ∀ x ξ, ξ ≠ 0 → (a.coefficient (x, ξ)).IsInvertible

theorem isElliptic_iff {a : HomogeneousSymbol X E V W m} :
    a.IsElliptic ↔ ∀ x ξ, ξ ≠ 0 → (a.coefficient (x, ξ)).IsInvertible :=
  Iff.rfl

/-- Between Banach spaces, ellipticity is bijectivity of the symbol at every nonzero frequency,
by the open mapping theorem. -/
theorem isElliptic_iff_bijective [CompleteSpace V] [CompleteSpace W]
    {a : HomogeneousSymbol X E V W m} :
    a.IsElliptic ↔ ∀ x ξ, ξ ≠ 0 → Function.Bijective (a.coefficient (x, ξ)) := by
  refine forall₂_congr fun x ξ ↦ imp_congr_right fun _ ↦ ⟨fun h ↦ h.bijective, fun h ↦ ?_⟩
  exact ⟨.ofBijective _ (LinearMap.ker_eq_bot.2 h.1) (LinearMap.range_eq_top.2 h.2), rfl⟩

/-- Without nonzero frequencies, as over a zero-dimensional base, ellipticity is vacuous. -/
theorem isElliptic_of_subsingleton [Subsingleton E] (a : HomogeneousSymbol X E V W m) :
    a.IsElliptic :=
  fun _ ξ hξ ↦ (hξ (Subsingleton.elim ξ 0)).elim

/-- In the presence of a nonzero frequency, an elliptic symbol identifies the fibres `V` and `W`. -/
theorem IsElliptic.nonempty_continuousLinearEquiv [Nontrivial E]
    {a : HomogeneousSymbol X E V W m} (ha : a.IsElliptic) : Nonempty (V ≃L[ℂ] W) := by
  obtain ⟨ξ, hξ⟩ := exists_ne (0 : E)
  obtain ⟨e, -⟩ := ha 0 ξ hξ
  exact ⟨e⟩

/-- In the presence of a nonzero frequency, an elliptic symbol forces the fibres to have the same
rank. -/
theorem IsElliptic.finrank_eq [Nontrivial E] {a : HomogeneousSymbol X E V W m}
    (ha : a.IsElliptic) : Module.finrank ℂ V = Module.finrank ℂ W :=
  let ⟨e⟩ := ha.nonempty_continuousLinearEquiv
  e.toLinearEquiv.finrank_eq

/-- In the presence of a nonzero frequency, the zero symbol on a nonzero fibre is not elliptic. -/
theorem not_isElliptic_zero [Nontrivial E] [Nontrivial V] :
    ¬(0 : HomogeneousSymbol X E V W m).IsElliptic := fun h ↦ by
  obtain ⟨ξ, hξ⟩ := exists_ne (0 : E)
  have := h 0 ξ hξ
  rw [coefficient_zero, Pi.zero_apply, ContinuousLinearMap.isInvertible_zero_iff] at this
  exact not_subsingleton V this.1

@[simp]
theorem isElliptic_castDegree (h : m = m') {a : HomogeneousSymbol X E V W m} :
    (a.castDegree h).IsElliptic ↔ a.IsElliptic := by
  simp only [isElliptic_iff, coefficient_castDegree]

alias ⟨_, IsElliptic.castDegree⟩ := isElliptic_castDegree

/-- The composition of elliptic symbols is elliptic. -/
theorem IsElliptic.comp {b : HomogeneousSymbol X E W U m'} {a : HomogeneousSymbol X E V W m}
    (hb : b.IsElliptic) (ha : a.IsElliptic) : (b.comp a).IsElliptic :=
  fun x ξ hξ ↦ by rw [coefficient_comp]; exact (hb x ξ hξ).comp (ha x ξ hξ)

/-- Pulling back the positions of an elliptic symbol along a smooth map keeps it elliptic. -/
theorem IsElliptic.compPosition {Y : Type*} [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    {a : HomogeneousSymbol X E V W m} (ha : a.IsElliptic) (g : Y → X) (hg : ContDiff ℝ ∞ g) :
    (a.compPosition g hg).IsElliptic :=
  fun y ξ hξ ↦ by rw [coefficient_compPosition]; exact ha (g y) ξ hξ

/-- A nonzero scalar multiple of an elliptic symbol is elliptic. -/
theorem IsElliptic.smul {a : HomogeneousSymbol X E V W m} (ha : a.IsElliptic) {c : ℂ}
    (hc : c ≠ 0) : (c • a).IsElliptic :=
  fun x ξ hξ ↦ by rw [coefficient_smul, Pi.smul_apply]; exact (ha x ξ hξ).smul hc

/-! ### The inverse symbol -/

section Inverse

/-- The pointwise inverse of a homogeneous symbol of degree `m` is homogeneous of degree `-m`. -/
private theorem inverse_coefficient_smul (a : HomogeneousSymbol X E V W m) (x : X) (ξ : E)
    {t : ℝ} (ht : 0 < t) :
    (a.coefficient (x, t • ξ)).inverse = t ^ (-m) • (a.coefficient (x, ξ)).inverse := by
  have hm : ((t ^ m : ℝ) : ℂ) ≠ 0 := by exact_mod_cast (Real.rpow_pos_of_pos ht m).ne'
  rw [a.homogeneous x ξ t ht, ← Complex.coe_smul, ContinuousLinearMap.inverse_smul _ hm,
    ← Complex.ofReal_inv, Complex.coe_smul, Real.rpow_neg ht.le]

variable [CompleteSpace V]

/-- The inverse of an elliptic homogeneous symbol `a` of degree `m`: the homogeneous symbol
`a(x, ξ)⁻¹` of degree `-m`. -/
def inverse (a : HomogeneousSymbol X E V W m) (ha : a.IsElliptic) :
    HomogeneousSymbol X E W V (-m) :=
  mk' (fun p ↦ (a.coefficient p).inverse)
    (fun p hp ↦ ((ha p.1 p.2 hp).contDiffAt_map_inverse.restrict_scalars ℝ).comp p
      (a.contDiffAt_coefficient hp) |>.contDiffWithinAt)
    fun x ξ _ _ ht ↦ inverse_coefficient_smul a x ξ ht

variable (a : HomogeneousSymbol X E V W m) (ha : a.IsElliptic)

@[simp]
theorem coefficient_inverse (p : X × E) :
    (a.inverse ha).coefficient p = (a.coefficient p).inverse := by
  obtain ⟨x, ξ⟩ := p
  rcases eq_or_ne ξ 0 with rfl | hξ
  · simp
  · exact coefficient_mk'_of_ne_zero _ _ _ hξ

/-- The inverse symbol is a left inverse of the symbol at every nonzero frequency. -/
theorem coefficient_inverse_comp_coefficient (x : X) {ξ : E} (hξ : ξ ≠ 0) :
    (a.inverse ha).coefficient (x, ξ) ∘L a.coefficient (x, ξ) = .id ℂ V := by
  rw [coefficient_inverse, (ha x ξ hξ).inverse_comp_self]

/-- The inverse symbol is a right inverse of the symbol at every nonzero frequency. -/
theorem coefficient_comp_coefficient_inverse (x : X) {ξ : E} (hξ : ξ ≠ 0) :
    a.coefficient (x, ξ) ∘L (a.inverse ha).coefficient (x, ξ) = .id ℂ W := by
  rw [coefficient_inverse, (ha x ξ hξ).self_comp_inverse]

/-- The inverse of an elliptic symbol is elliptic. -/
theorem isElliptic_inverse : (a.inverse ha).IsElliptic :=
  fun x ξ hξ ↦ by rw [coefficient_inverse]; exact (ha x ξ hξ).inverse

/-- A homogeneous symbol of degree `-m` that is a left inverse of `a` at every nonzero frequency
is the inverse of `a`. -/
theorem eq_inverse_of_comp_eq_id_left {b : HomogeneousSymbol X E W V (-m)}
    (h : ∀ x ξ, ξ ≠ 0 → b.coefficient (x, ξ) ∘L a.coefficient (x, ξ) = .id ℂ V) :
    b = a.inverse ha :=
  ext_of_ne_zero fun x ξ hξ ↦ by
    have hb : b.coefficient (x, ξ) = (b.coefficient (x, ξ) ∘L a.coefficient (x, ξ)) ∘L
        (a.coefficient (x, ξ)).inverse := by
      rw [ContinuousLinearMap.comp_assoc, (ha x ξ hξ).self_comp_inverse,
        ContinuousLinearMap.comp_id]
    rw [hb, h x ξ hξ, ContinuousLinearMap.id_comp, coefficient_inverse]

/-- A homogeneous symbol of degree `-m` that is a right inverse of `a` at every nonzero frequency
is the inverse of `a`. -/
theorem eq_inverse_of_comp_eq_id_right {b : HomogeneousSymbol X E W V (-m)}
    (h : ∀ x ξ, ξ ≠ 0 → a.coefficient (x, ξ) ∘L b.coefficient (x, ξ) = .id ℂ W) :
    b = a.inverse ha :=
  ext_of_ne_zero fun x ξ hξ ↦ by
    have hb : b.coefficient (x, ξ) = (a.coefficient (x, ξ)).inverse ∘L
        (a.coefficient (x, ξ) ∘L b.coefficient (x, ξ)) := by
      rw [← ContinuousLinearMap.comp_assoc, (ha x ξ hξ).inverse_comp_self,
        ContinuousLinearMap.id_comp]
    rw [hb, h x ξ hξ, ContinuousLinearMap.comp_id, coefficient_inverse]

/-- Inverting twice gives back the symbol, up to the identification of the degrees `-(-m)` and
`m`. -/
@[simp]
theorem inverse_inverse [CompleteSpace W] :
    (a.inverse ha).inverse (a.isElliptic_inverse ha) = a.castDegree (neg_neg m).symm :=
  ext_of_ne_zero fun x ξ hξ ↦ by simp [(ha x ξ hξ).inverse_inverse]

@[simp]
theorem inverse_castDegree (h : m = m') :
    (a.castDegree h).inverse (ha.castDegree h) = (a.inverse ha).castDegree (neg_inj.2 h) :=
  ext_of_ne_zero fun x ξ _ ↦ by simp

/-- The inverse of a composition is the composition of the inverses in the reverse order. -/
theorem inverse_comp [CompleteSpace W] {b : HomogeneousSymbol X E W U m'} (hb : b.IsElliptic) :
    (b.comp a).inverse (hb.comp ha) =
      ((a.inverse ha).comp (b.inverse hb)).castDegree (neg_add_rev m' m).symm :=
  ext_of_ne_zero fun x ξ hξ ↦ by simp [(ha x ξ hξ).inverse_comp_of_right]

@[simp]
theorem inverse_compPosition {Y : Type*} [NormedAddCommGroup Y] [NormedSpace ℝ Y] (g : Y → X)
    (hg : ContDiff ℝ ∞ g) :
    (a.compPosition g hg).inverse (ha.compPosition g hg) = (a.inverse ha).compPosition g hg :=
  ext_of_ne_zero fun _ _ _ ↦ by simp

/-- The inverse of `c • a` is `c⁻¹` times the inverse of `a`. -/
@[simp]
theorem inverse_smul {c : ℂ} (hc : c ≠ 0) :
    (c • a).inverse (ha.smul hc) = c⁻¹ • a.inverse ha :=
  ext_of_ne_zero fun _ _ _ ↦ by simp [ContinuousLinearMap.inverse_smul _ hc]

/-- The elliptic estimate: for positions in a compact set, `‖ξ‖ ^ m ‖v‖ ≤ C ‖a(x, ξ) v‖` at every
nonzero frequency `ξ`. -/
theorem IsElliptic.exists_mul_norm_le_norm_coefficient_apply [ProperSpace E]
    {a : HomogeneousSymbol X E V W m} (ha : a.IsElliptic) {K : Set X} (hK : IsCompact K) :
    ∃ C, 0 ≤ C ∧ ∀ x ∈ K, ∀ ξ, ξ ≠ 0 → ∀ v,
      ‖ξ‖ ^ m * ‖v‖ ≤ C * ‖a.coefficient (x, ξ) v‖ := by
  obtain ⟨C, hC, hCK⟩ := (a.inverse ha).exists_norm_coefficient_le hK
  refine ⟨C, hC, fun x hx ξ hξ v ↦ ?_⟩
  have hpos : 0 < ‖ξ‖ ^ m := Real.rpow_pos_of_pos (norm_pos_iff.2 hξ) m
  -- `v = a(x, ξ)⁻¹ (a(x, ξ) v)`, and `‖a(x, ξ)⁻¹‖ ≤ C ‖ξ‖ ^ (-m)`.
  have hv : ‖v‖ ≤ C * ‖ξ‖ ^ (-m) * ‖a.coefficient (x, ξ) v‖ := by
    calc ‖v‖ = ‖(a.inverse ha).coefficient (x, ξ) (a.coefficient (x, ξ) v)‖ := by
          rw [← ContinuousLinearMap.comp_apply, coefficient_inverse_comp_coefficient a ha x hξ,
            ContinuousLinearMap.id_apply]
      _ ≤ _ := ((a.inverse ha).coefficient (x, ξ)).le_of_opNorm_le (hCK x hx ξ) _
  rw [Real.rpow_neg (norm_nonneg ξ)] at hv
  calc ‖ξ‖ ^ m * ‖v‖ ≤ ‖ξ‖ ^ m * (C * (‖ξ‖ ^ m)⁻¹ * ‖a.coefficient (x, ξ) v‖) :=
        mul_le_mul_of_nonneg_left hv hpos.le
    _ = C * ‖a.coefficient (x, ξ) v‖ := by field_simp

end Inverse

/-! ### Powers of the frequency norm -/

section NormRpow

variable (X) {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F] (V)

/-- The power `‖ξ‖ ^ m` of the frequency norm, times the identity, is elliptic. -/
theorem isElliptic_normRpow (m : ℝ) : (normRpow X F V m).IsElliptic := fun x ξ hξ ↦ by
  have hm : ((‖ξ‖ ^ m : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast (Real.rpow_pos_of_pos (norm_pos_iff.2 hξ) m).ne'
  rw [coefficient_normRpow_of_ne_zero _ _ _ hξ, ← Complex.coe_smul,
    ContinuousLinearMap.isInvertible_smul_iff hm]
  exact ⟨.refl ℂ V, rfl⟩

/-- The inverse of `‖ξ‖ ^ m` is `‖ξ‖ ^ (-m)`. -/
@[simp]
theorem inverse_normRpow [CompleteSpace V] (m : ℝ) :
    (normRpow X F V m).inverse (isElliptic_normRpow X V m) = normRpow X F V (-m) := by
  refine (eq_inverse_of_comp_eq_id_left (normRpow X F V m) (isElliptic_normRpow X V m)
    fun x ξ hξ ↦ ?_).symm
  have hξ' : (0 : ℝ) < ‖ξ‖ := norm_pos_iff.2 hξ
  ext v
  simp [hξ, smul_smul, ← Real.rpow_add hξ']

end NormRpow

/-! ### The cut-off inverse on `ℝⁿ` -/

section CutOff

variable {n : ℕ} [CompleteSpace V] (χ : FrequencyCutoff (CoordinateSpace n))
  (a : HomogeneousSymbol (CoordinateSpace n) (CoordinateSpace n) V W m) (ha : a.IsElliptic)

/-- The cut-off inverse symbol is a left inverse of the cut-off symbol modulo smoothing symbols:
`χ(ξ) a(x, ξ)⁻¹ ∘ χ(ξ) a(x, ξ) - 1` is smoothing. -/
theorem isSmoothing_toSymbol_inverse_comp_toSymbol_sub :
    ((toSymbol χ (a.inverse ha)).comp (toSymbol χ a) -
      Symbol.inclusion (neg_add_cancel m).ge (Symbol.const (.id ℂ V))).IsSmoothing :=
  -- The difference vanishes for `‖ξ‖ ≥ 2`, where the cutoff is `1`.
  Symbol.isSmoothing_of_coefficient_eq_zero 2 fun x ξ hξ ↦ by
    have hξ0 : ξ ≠ 0 := norm_pos_iff.1 (by linarith)
    simp [coefficient_toSymbol_of_two_le_norm _ _ _ hξ, (ha x ξ hξ0).inverse_comp_self]

/-- The cut-off inverse symbol is a right inverse of the cut-off symbol modulo smoothing symbols:
`χ(ξ) a(x, ξ) ∘ χ(ξ) a(x, ξ)⁻¹ - 1` is smoothing. -/
theorem isSmoothing_toSymbol_comp_toSymbol_inverse_sub :
    ((toSymbol χ a).comp (toSymbol χ (a.inverse ha)) -
      Symbol.inclusion (add_neg_cancel m).ge (Symbol.const (.id ℂ W))).IsSmoothing :=
  -- The difference vanishes for `‖ξ‖ ≥ 2`, where the cutoff is `1`.
  Symbol.isSmoothing_of_coefficient_eq_zero 2 fun x ξ hξ ↦ by
    have hξ0 : ξ ≠ 0 := norm_pos_iff.1 (by linarith)
    simp [coefficient_toSymbol_of_two_le_norm _ _ _ hξ, (ha x ξ hξ0).self_comp_inverse]

end CutOff

end HomogeneousSymbol

end TauCeti
