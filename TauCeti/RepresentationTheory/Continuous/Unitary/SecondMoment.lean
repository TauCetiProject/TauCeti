/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Continuous.Unitary.Basic
public import TauCeti.MeasureTheory.Integral.RankOne
public import Mathlib.RepresentationTheory.Irreducible
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.Analysis.InnerProductSpace.Trace
import Mathlib.Analysis.Complex.Polynomial.Basic
import TauCeti.Topology.Algebra.Module.Trace
import TauCeti.RepresentationTheory.Continuous.Schur

/-!
# Second moments of equivariant functions

A square-integrable function with values in a finite-dimensional irreducible unitary
representation has a scalar second moment if it is equivariant up to unit-modulus factors
under measure-preserving transformations. The scalar is its integrated squared norm divided
by the dimension. This gives the coordinate normalization and the coefficient bound used for
Bessel functions and their cutoffs. Unit-modulus factors are allowed because they disappear
from the rank-one integrand, as happens when taking representatives on a quotient.

The Bessel normalization is the one in `New.IsCutPair.exists_integral_cut_mul_conj_eq` and
`New.BesselSystem.orthonormal` in lsernau/grh-lean (`72fead1`,
`grh/src/New/Spanning/Bessel/Orthonormality.lean`).
-/

public section

open MeasureTheory Module InnerProductSpace

namespace ContRepresentation

variable {G V X : Type*} [Monoid G] [NormedAddCommGroup V] [InnerProductSpace ℂ V]
  [FiniteDimensional ℂ V] [MeasurableSpace X] {μ : Measure X}

/-- The integrated rank-one operator of a square-integrable function equivariant up to phase
under measure-preserving maps is scalar in an irreducible unitary representation. -/
theorem integral_rankOne_eq_smul_id_of_equivariant (ρ : ContRepresentation ℂ G V)
    (hρ : ρ.IsUnitary) (hirr : Representation.IsIrreducible ρ.toRepresentation)
    {τ : G → X → X} (hτ : ∀ g, MeasurePreserving (τ g) μ μ)
    {F : X → V} (hF : MemLp F 2 μ)
    (heq : ∀ g, ∀ᵐ x ∂μ, ∃ c : ℂ, ‖c‖ = 1 ∧ F (τ g x) = c • ρ g (F x)) :
    (∫ x, rankOne ℂ (F x) (F x) ∂μ) =
      (((∫ x, ‖F x‖ ^ 2 ∂μ) / finrank ℂ V : ℝ) : ℂ) • ContinuousLinearMap.id ℂ V := by
  have : CompleteSpace V := FiniteDimensional.completeSpace ℂ V
  let R : X → V →L[ℂ] V := fun x ↦ rankOne ℂ (F x) (F x)
  have hR : Integrable R μ := hF.integrable_rankOne_self
  let T : V →L[ℂ] V := ∫ x, R x ∂μ
  have hcomm (g : G) (v : V) : T (ρ g v) = ρ g (T v) := by
    simp only [T, ContinuousLinearMap.integral_apply hR]
    rw [← (ρ g).integral_comp_comm (hR.apply_continuousLinearMap v)]
    rw [← (hτ g).map_eq, integral_map (hτ g).measurable.aemeasurable
      (by simpa only [(hτ g).map_eq] using
        (hR.apply_continuousLinearMap (ρ g v)).aestronglyMeasurable), (hτ g).map_eq]
    apply integral_congr_ae
    filter_upwards [heq g] with x hx
    obtain ⟨c, hc, hcx⟩ := hx
    have hc' : (starRingEnd ℂ) c * c = 1 := by
      rw [← Complex.normSq_eq_conj_mul_self, Complex.normSq_eq_norm_sq, hc, one_pow]
      norm_num
    dsimp only [R]
    rw [hcx, rankOne_apply, rankOne_apply, inner_smul_left, hρ.inner_map_map, map_smul,
      smul_smul, mul_right_comm, hc', one_mul]
  let S : ContIntertwiningMap ρ ρ := ⟨T, fun g ↦ ContinuousLinearMap.ext (hcomm g)⟩
  have hdim : (finrank ℂ V : ℂ) ≠ 0 := by
    have := (Representation.irreducible_iff_isSimpleModule_asModule _).mp hirr
    have : Nontrivial V := IsSimpleModule.nontrivial (MonoidAlgebra ℂ G) ρ.toRepresentation.asModule
    exact_mod_cast (ne_of_gt (finrank_pos : 0 < finrank ℂ V))
  have htrace : TauCeti.traceCLM ℂ V T = (↑(∫ x, ‖F x‖ ^ 2 ∂μ : ℝ) : ℂ) := by
    rw [← (TauCeti.traceCLM ℂ V).integral_comp_comm hR]
    simp only [R, TauCeti.traceCLM_apply, trace_rankOne, inner_self_eq_norm_sq_to_K]
    rw [← integral_complex_ofReal (μ := μ) (f := fun x ↦ ‖F x‖ ^ 2)]
    exact integral_congr_ae (Filter.Eventually.of_forall fun x ↦
      (map_pow Complex.ofRealHom ‖F x‖ 2).symm)
  have hS := ρ.eq_finrank_inv_mul_trace_smul_id_of_isIrreducible hdim hirr S
  simpa only [S, ← TauCeti.traceCLM_apply, htrace, Complex.ofReal_natCast, Complex.ofReal_mul,
    Complex.ofReal_inv, div_eq_inv_mul, T, R] using hS

/-- The products of two vector coefficients integrate to the corresponding inner product,
scaled by the mean energy per dimension. In an orthonormal basis this is the Gram identity
for the coordinate functions. -/
theorem integral_mul_inner_eq_of_equivariant (ρ : ContRepresentation ℂ G V)
    (hρ : ρ.IsUnitary) (hirr : Representation.IsIrreducible ρ.toRepresentation)
    {τ : G → X → X} (hτ : ∀ g, MeasurePreserving (τ g) μ μ)
    {F : X → V} (hF : MemLp F 2 μ)
    (heq : ∀ g, ∀ᵐ x ∂μ, ∃ c : ℂ, ‖c‖ = 1 ∧ F (τ g x) = c • ρ g (F x)) (v w : V) :
    (∫ x, ⟪v, F x⟫_ℂ * ⟪F x, w⟫_ℂ ∂μ) =
      (((∫ x, ‖F x‖ ^ 2 ∂μ) / finrank ℂ V : ℝ) : ℂ) * ⟪v, w⟫_ℂ := by
  have : CompleteSpace V := FiniteDimensional.completeSpace ℂ V
  rw [← hF.inner_integral_rankOne_self v w,
    ρ.integral_rankOne_eq_smul_id_of_equivariant hρ hirr hτ hF heq]
  simp only [smul_apply, ContinuousLinearMap.id_apply, inner_smul_right]

/-- An equivariant function with total squared norm at most the dimension has each integrated
squared coefficient bounded by the squared norm of the probing vector. -/
theorem integral_norm_inner_sq_le_of_equivariant (ρ : ContRepresentation ℂ G V)
    (hρ : ρ.IsUnitary) (hirr : Representation.IsIrreducible ρ.toRepresentation)
    {τ : G → X → X} (hτ : ∀ g, MeasurePreserving (τ g) μ μ)
    {F : X → V} (hF : MemLp F 2 μ)
    (heq : ∀ g, ∀ᵐ x ∂μ, ∃ c : ℂ, ‖c‖ = 1 ∧ F (τ g x) = c • ρ g (F x))
    (henergy : (∫ x, ‖F x‖ ^ 2 ∂μ) ≤ finrank ℂ V) (v : V) :
    (∫ x, ‖⟪v, F x⟫_ℂ‖ ^ 2 ∂μ) ≤ ‖v‖ ^ 2 := by
  have h := ρ.integral_mul_inner_eq_of_equivariant hρ hirr hτ hF heq v v
  have hprod (x : X) : ⟪v, F x⟫_ℂ * ⟪F x, v⟫_ℂ = (↑(‖⟪v, F x⟫_ℂ‖ ^ 2) : ℂ) := by
    rw [← inner_conj_symm (F x) v, Complex.mul_conj, Complex.normSq_eq_norm_sq]
  simp only [hprod, integral_complex_ofReal, inner_self_eq_norm_sq_to_K] at h
  have hs : (∫ x, ‖⟪v, F x⟫_ℂ‖ ^ 2 ∂μ) =
      (∫ x, ‖F x‖ ^ 2 ∂μ) / finrank ℂ V * ‖v‖ ^ 2 := by
    apply Complex.ofReal_injective
    rw [Complex.ofReal_mul]
    exact h.trans (congrArg (_ * ·) (map_pow Complex.ofRealHom ‖v‖ 2).symm)
  rcases Nat.eq_zero_or_pos (finrank ℂ V) with hd | hd
  · simp [hs, hd]
  have hd' : (0 : ℝ) < finrank ℂ V := Nat.cast_pos.mpr hd
  exact hs.le.trans (mul_le_of_le_one_left (sq_nonneg _) ((div_le_one hd').2 henergy))

end ContRepresentation
