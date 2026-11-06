/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Normed.Operator.Banach
public import TauCeti.Analysis.Pseudodifferential.HomogeneousSymbol
public import TauCeti.Topology.Algebra.Module.ContinuousLinearMap.Invertible
public import Mathlib.Analysis.Calculus.ContDiff.Operations

/-!
# Elliptic homogeneous symbols and their inverses

A homogeneous symbol `a` of degree `m` is *elliptic* when its value `a (x, ξ)` is an invertible
continuous linear map at every position `x` and every nonzero frequency `ξ`. Applied to the
principal term of a classical symbol, this is the ellipticity of a pseudodifferential operator,
and the pointwise inverse of the principal term is the leading term of a parametrix.

The file proves that this pointwise inverse is again a homogeneous symbol, of the opposite
degree:

* `TauCeti.HomogeneousSymbol.IsElliptic`: invertibility at every nonzero frequency; between
  Banach spaces it is the same as bijectivity (`HomogeneousSymbol.isElliptic_iff_bijective`).
* `TauCeti.HomogeneousSymbol.inverse`: for an elliptic `a` of degree `m` and a complete `V`, the
  homogeneous symbol `(x, ξ) ↦ a (x, ξ)⁻¹` of degree `-m`. It is a two-sided inverse of `a` for
  `HomogeneousSymbol.comp` (`inverse_comp`, `comp_inverse`) and the only one-sided inverse
  (`eq_inverse_of_comp_eq_id_left`, `eq_inverse_of_comp_eq_id_right`).
* `HomogeneousSymbol.spatialDeriv_inverse` and `HomogeneousSymbol.frequencyDeriv_inverse`: the
  derivatives of the inverse are `-(a⁻¹ ∘ ∂a ∘ a⁻¹)`, the formula behind the derivative
  estimates of inverse symbols.
* `HomogeneousSymbol.IsElliptic.finrank_eq`: when the frequency space is nontrivial, an elliptic
  symbol identifies the two fibres, so they have the same dimension. On a trivial frequency space
  every symbol is elliptic (`HomogeneousSymbol.isElliptic_of_subsingleton`), and no such
  conclusion holds.

## References

* M. E. Taylor, *Pseudodifferential Operators: Four Lectures at MSRI*, September 2008,
  Lecture I, (4.1)–(4.6).
* L. Hörmander, *The Analysis of Linear Partial Differential Operators III*, §18.1.
-/

public section

open Set Filter
open scoped ContDiff Topology

namespace TauCeti

namespace HomogeneousSymbol

variable {X E : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [NormedAddCommGroup E]
  [NormedSpace ℝ E] {V W U : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]
  [NormedAddCommGroup W] [NormedSpace ℂ W] [NormedAddCommGroup U] [NormedSpace ℂ U] {m m' : ℝ}

/-! ### Elliptic homogeneous symbols -/

/-- A homogeneous symbol is elliptic if its value at every position and every nonzero frequency
is an invertible continuous linear map. -/
def IsElliptic (a : HomogeneousSymbol X E V W m) : Prop :=
  ∀ x ξ, ξ ≠ 0 → (a.coefficient (x, ξ)).IsInvertible

theorem isElliptic_iff {a : HomogeneousSymbol X E V W m} :
    a.IsElliptic ↔ ∀ x ξ, ξ ≠ 0 → (a.coefficient (x, ξ)).IsInvertible :=
  Iff.rfl

/-- Between Banach spaces, a homogeneous symbol is elliptic exactly when its value at every
nonzero frequency is bijective. -/
theorem isElliptic_iff_bijective [CompleteSpace V] [CompleteSpace W]
    {a : HomogeneousSymbol X E V W m} :
    a.IsElliptic ↔ ∀ x ξ, ξ ≠ 0 → Function.Bijective (a.coefficient (x, ξ)) := by
  simp only [isElliptic_iff, ContinuousLinearMap.isInvertible_iff_bijective]

/-- On a trivial frequency space there is no nonzero frequency, so every homogeneous symbol is
elliptic. -/
theorem isElliptic_of_subsingleton [Subsingleton E] (a : HomogeneousSymbol X E V W m) :
    a.IsElliptic :=
  fun _ ξ hξ ↦ (hξ (Subsingleton.elim ξ 0)).elim

variable (X E V) in
/-- The identity symbol is elliptic. -/
theorem isElliptic_id : (id X E V).IsElliptic :=
  fun _ _ hξ ↦ by simpa [hξ] using ContinuousLinearMap.isInvertible_equiv (f := .refl ℂ V)

/-- The composition of elliptic symbols is elliptic. -/
theorem IsElliptic.comp {b : HomogeneousSymbol X E W U m'} {a : HomogeneousSymbol X E V W m}
    (hb : b.IsElliptic) (ha : a.IsElliptic) : (b.comp a).IsElliptic :=
  fun x ξ hξ ↦ by simpa using (hb x ξ hξ).comp (ha x ξ hξ)

/-- Multiplying by a nonzero complex number does not change ellipticity. -/
@[simp]
theorem isElliptic_smul_iff {c : ℂ} (hc : c ≠ 0) {a : HomogeneousSymbol X E V W m} :
    (c • a).IsElliptic ↔ a.IsElliptic := by
  simp only [isElliptic_iff, coefficient_smul, Pi.smul_apply,
    ContinuousLinearMap.isInvertible_smul_iff hc]

/-- Transport along an equality of degrees does not change ellipticity. -/
@[simp]
theorem isElliptic_castDegree_iff (h : m = m') {a : HomogeneousSymbol X E V W m} :
    (a.castDegree h).IsElliptic ↔ a.IsElliptic := by
  simp only [isElliptic_iff, coefficient_castDegree]

/-- The zero symbol is not elliptic as soon as there is a nonzero frequency and a nonzero
vector. -/
theorem not_isElliptic_zero [Nonempty X] [Nontrivial E] [Nontrivial V] :
    ¬(0 : HomogeneousSymbol X E V W m).IsElliptic := fun h ↦ by
  obtain ⟨ξ, hξ⟩ := exists_ne (0 : E)
  have := (ContinuousLinearMap.isInvertible_zero_iff.1 (h (Classical.arbitrary X) ξ hξ)).1
  exact not_subsingleton V this

/-- Over a nontrivial frequency space, an elliptic homogeneous symbol identifies its two fibres
by a continuous linear equivalence. -/
theorem IsElliptic.nonempty_continuousLinearEquiv [Nonempty X] [Nontrivial E]
    {a : HomogeneousSymbol X E V W m} (ha : a.IsElliptic) : Nonempty (V ≃L[ℂ] W) := by
  obtain ⟨ξ, hξ⟩ := exists_ne (0 : E)
  obtain ⟨e, -⟩ := ha (Classical.arbitrary X) ξ hξ
  exact ⟨e⟩

/-- **Ellipticity forces equal ranks.** Over a nontrivial frequency space, the fibres of an
elliptic homogeneous symbol have the same dimension. The hypothesis `Nontrivial E` is needed:
over the zero frequency space every symbol is elliptic
(`HomogeneousSymbol.isElliptic_of_subsingleton`). -/
theorem IsElliptic.finrank_eq [Nonempty X] [Nontrivial E] {a : HomogeneousSymbol X E V W m}
    (ha : a.IsElliptic) : Module.finrank ℂ V = Module.finrank ℂ W :=
  ha.nonempty_continuousLinearEquiv.some.toLinearEquiv.finrank_eq

/-! ### The inverse of an elliptic symbol -/

section Inverse

variable [CompleteSpace V] (a : HomogeneousSymbol X E V W m) (ha : a.IsElliptic)

include ha in
/-- The pointwise inverse of an invertible continuous linear map is smooth along a smooth family,
as a map of real variables. -/
private theorem contDiffAt_inverse_coefficient {p : X × E} (hp : p.2 ≠ 0) :
    ContDiffAt ℝ ∞ (fun q ↦ (a.coefficient q).inverse) p :=
  (((ha p.1 p.2 hp).contDiffAt_map_inverse (𝕜 := ℂ)).restrict_scalars ℝ).comp p
    (a.contDiffAt_coefficient hp)

/-- The inverse `(x, ξ) ↦ a (x, ξ)⁻¹` of an elliptic homogeneous symbol `a` of degree `m`, a
homogeneous symbol of degree `-m`. -/
noncomputable def inverse (a : HomogeneousSymbol X E V W m) (ha : a.IsElliptic) :
    HomogeneousSymbol X E W V (-m) where
  coefficient p := (a.coefficient p).inverse
  zero_covector x := by simp
  contDiffOn_coefficient _ hp := (contDiffAt_inverse_coefficient a ha hp).contDiffWithinAt
  homogeneous x ξ t ht := by
    rw [a.homogeneous x ξ t ht, ← Complex.coe_smul, ContinuousLinearMap.inverse_smul,
      ← Complex.ofReal_inv, Complex.coe_smul, Real.rpow_neg ht.le]

@[simp]
theorem coefficient_inverse (p : X × E) :
    (a.inverse ha).coefficient p = (a.coefficient p).inverse :=
  (rfl)

/-- At a nonzero frequency, the inverse is a left inverse. -/
theorem coefficient_inverse_comp_coefficient {x : X} {ξ : E} (hξ : ξ ≠ 0) :
    (a.inverse ha).coefficient (x, ξ) ∘L a.coefficient (x, ξ) = ContinuousLinearMap.id ℂ V :=
  (ha x ξ hξ).inverse_comp_self

/-- At a nonzero frequency, the inverse is a right inverse. -/
theorem coefficient_comp_coefficient_inverse {x : X} {ξ : E} (hξ : ξ ≠ 0) :
    a.coefficient (x, ξ) ∘L (a.inverse ha).coefficient (x, ξ) = ContinuousLinearMap.id ℂ W :=
  (ha x ξ hξ).self_comp_inverse

/-- The inverse is a left inverse for `HomogeneousSymbol.comp`. -/
@[simp]
theorem inverse_comp : (a.inverse ha).comp a = (id X E V).castDegree (neg_add_cancel m).symm :=
  ext_of_ne_zero fun x ξ hξ ↦ by simp [(ha x ξ hξ).inverse_comp_self, hξ]

/-- The inverse is a right inverse for `HomogeneousSymbol.comp`. -/
@[simp]
theorem comp_inverse : a.comp (a.inverse ha) = (id X E W).castDegree (add_neg_cancel m).symm :=
  ext_of_ne_zero fun x ξ hξ ↦ by simp [(ha x ξ hξ).self_comp_inverse, hξ]

/-- The inverse of an elliptic symbol is elliptic. -/
theorem isElliptic_inverse : (a.inverse ha).IsElliptic :=
  fun x ξ hξ ↦ (ha x ξ hξ).inverse

/-- A left inverse of an elliptic symbol is its inverse. -/
theorem eq_inverse_of_comp_eq_id_left {b : HomogeneousSymbol X E W V (-m)}
    (h : b.comp a = (id X E V).castDegree (neg_add_cancel m).symm) : b = a.inverse ha := by
  refine ext_of_ne_zero fun x ξ hξ ↦ ?_
  have hb := congrArg (fun c ↦ c.coefficient (x, ξ)) h
  simp only [coefficient_comp, coefficient_castDegree, coefficient_id hξ] at hb
  calc b.coefficient (x, ξ)
      = (b.coefficient (x, ξ) ∘L a.coefficient (x, ξ)) ∘L (a.inverse ha).coefficient (x, ξ) := by
        rw [ContinuousLinearMap.comp_assoc, coefficient_comp_coefficient_inverse a ha hξ,
          ContinuousLinearMap.comp_id]
    _ = (a.inverse ha).coefficient (x, ξ) := by rw [hb, ContinuousLinearMap.id_comp]

/-- A right inverse of an elliptic symbol is its inverse. -/
theorem eq_inverse_of_comp_eq_id_right {b : HomogeneousSymbol X E W V (-m)}
    (h : a.comp b = (id X E W).castDegree (add_neg_cancel m).symm) : b = a.inverse ha := by
  refine ext_of_ne_zero fun x ξ hξ ↦ ?_
  have hb := congrArg (fun c ↦ c.coefficient (x, ξ)) h
  simp only [coefficient_comp, coefficient_castDegree, coefficient_id hξ] at hb
  calc b.coefficient (x, ξ)
      = (a.inverse ha).coefficient (x, ξ) ∘L (a.coefficient (x, ξ) ∘L b.coefficient (x, ξ)) := by
        rw [← ContinuousLinearMap.comp_assoc, coefficient_inverse_comp_coefficient a ha hξ,
          ContinuousLinearMap.id_comp]
    _ = (a.inverse ha).coefficient (x, ξ) := by rw [hb, ContinuousLinearMap.comp_id]

/-- The inverse of the inverse is the original symbol. -/
@[simp]
theorem inverse_inverse [CompleteSpace W] :
    (a.inverse ha).inverse (a.isElliptic_inverse ha) = a.castDegree (neg_neg m).symm :=
  ext_of_ne_zero fun x ξ hξ ↦ by simp [(ha x ξ hξ).inverse_inverse]

/-! ### Derivatives of the inverse -/

/-- The derivative of the inverse of an elliptic symbol: away from the zero frequency, the
derivative of `a⁻¹` in the direction `q` is `-(a⁻¹ ∘ a' q ∘ a⁻¹)`. -/
theorem fderiv_coefficient_inverse {p : X × E} (hp : p.2 ≠ 0) (q : X × E) :
    fderiv ℝ (a.inverse ha).coefficient p q =
      -((a.inverse ha).coefficient p ∘L (fderiv ℝ a.coefficient p q ∘L
        (a.inverse ha).coefficient p)) := by
  obtain ⟨x, ξ⟩ := p
  -- Near `p`, `a⁻¹ ∘ a` is the constant identity, so the product rule for it vanishes.
  have hloc : ((a.inverse ha).comp a).coefficient =ᶠ[𝓝 (x, ξ)]
      fun _ ↦ ContinuousLinearMap.id ℂ V := by
    filter_upwards [(isOpen_compl_singleton.preimage continuous_snd).mem_nhds hp] with q hq
    rw [coefficient_comp]
    exact coefficient_inverse_comp_coefficient a ha (x := q.1) (ξ := q.2) hq
  have hzero := fderiv_coefficient_comp (a.inverse ha) a hp q
  rw [hloc.fderiv_eq, fderiv_const_apply, zero_apply] at hzero
  -- Compose `0 = (a⁻¹)' q ∘ a + a⁻¹ ∘ a' q` on the right with `a⁻¹`.
  have h := congrArg (· ∘L (a.inverse ha).coefficient (x, ξ)) hzero
  simp only [ContinuousLinearMap.zero_comp, ContinuousLinearMap.add_comp,
    ContinuousLinearMap.comp_assoc, coefficient_comp_coefficient_inverse a ha hp,
    ContinuousLinearMap.comp_id] at h
  exact eq_neg_of_add_eq_zero_left h.symm

/-- The spatial derivative of the inverse of an elliptic symbol is `-(a⁻¹ ∘ ∂ₓa ∘ a⁻¹)`. -/
theorem spatialDeriv_inverse (v : X) :
    (a.inverse ha).spatialDeriv v =
      -((a.inverse ha).comp ((a.spatialDeriv v).comp (a.inverse ha))).castDegree (by ring) :=
  ext_of_ne_zero fun x ξ hξ ↦ by
    simp [coefficient_spatialDeriv_eq_fderiv _ _ hξ,
      fderiv_coefficient_inverse a ha (p := (x, ξ)) hξ]

/-- The frequency derivative of the inverse of an elliptic symbol is `-(a⁻¹ ∘ ∂_ξa ∘ a⁻¹)`; its
degree `-m + ((m - 1) + -m)` is transported to the degree `-m - 1` of the left side. -/
theorem frequencyDeriv_inverse (w : E) :
    (a.inverse ha).frequencyDeriv w =
      -((a.inverse ha).comp ((a.frequencyDeriv w).comp (a.inverse ha))).castDegree (by ring) :=
  ext_of_ne_zero fun x ξ hξ ↦ by
    simp [coefficient_frequencyDeriv_eq_fderiv _ _ hξ,
      fderiv_coefficient_inverse a ha (p := (x, ξ)) hξ]

end Inverse

end HomogeneousSymbol

end TauCeti
