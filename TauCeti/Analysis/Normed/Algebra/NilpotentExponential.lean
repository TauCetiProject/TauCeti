/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Analytic.Constructions
public import Mathlib.Analysis.Convex.Contractible
public import Mathlib.Analysis.Normed.Algebra.Exponential
public import Mathlib.Analysis.Normed.Algebra.Logarithm
public import Mathlib.Topology.Algebra.Group.Units
public import Mathlib.AlgebraicTopology.FundamentalGroupoid.SimplyConnected
public import TauCeti.RingTheory.Nilpotent.Log
import TauCeti.RingTheory.Nilpotent.Exp

/-!
# Finite exponentials and logarithms as continuous and analytic maps

Let `A` be a topological ring which is a `ℚ`-algebra. The finite exponential `IsNilpotent.exp`
and the finite logarithm `IsNilpotent.log` are purely algebraic: they are the truncations
`∑ i < n, a ^ i / i!` and `∑ i < n, (-1) ^ (i + 1) / i • (u - 1) ^ i` of the exponential and
logarithm series, valid when `a ^ n = 0`, respectively `(u - 1) ^ n = 0`. This file compares
them with the analytic maps of the topological algebra and records their topological properties.

* On nilpotent elements the exponential series of `NormedSpace.exp` terminates, so the finite
  exponential is the exponential of the topological algebra; for a matrix algebra over `ℝ` or
  `ℂ` this is the matrix exponential of Lie theory. Likewise the logarithm series
  `NormedSpace.log` terminates on unipotent elements and equals the finite logarithm.
* For a fixed bound `n`, the finite exponential is continuous on `{a | a ^ n = 0}` and the
  finite logarithm is continuous on `{u | (u - 1) ^ n = 0}`, because there they agree with the
  degree-`n` truncations, which are polynomial maps. In a normed algebra over a nontrivially
  normed field they are analytic there for the same reason.
* Consequently, on any set `s` of elements killed by a common power, the exponential is a
  homeomorphism `s ≃ₜ exp '' s` with inverse the logarithm. Taking `s = {a | a ^ n = 0}`, whose
  image is `{u | (u - 1) ^ n = 0}` by `IsNilpotent.image_exp_setOf_pow_eq_zero`, the nilpotent
  and unipotent elements with a common bound are homeomorphic. If `s` is star-convex and
  nonempty, for instance a real or complex linear subspace, then `exp '' s` is contractible,
  hence simply connected.

The last statement is aimed at unipotent groups over `ℂ`. Every element `X` of a complex
subspace `𝔲` of strictly upper triangular `n × n` matrices satisfies `X ^ n = 0`, so `exp '' 𝔲`
is contractible and simply connected. The complex points of a unipotent group realized inside the
upper unitriangular matrices are of this form, with `𝔲` its Lie algebra.

## Main results

* `IsNilpotent.normedSpace_exp_eq_exp`: on a nilpotent element, `NormedSpace.exp` is the finite
  exponential.
* `IsNilpotent.normedSpace_log_eq_log`: on a unipotent element, `NormedSpace.log` is the finite
  logarithm.
* `IsNilpotent.continuousOn_exp`, `IsNilpotent.continuousOn_log`: continuity on the elements
  satisfying a fixed nilpotency bound.
* `IsNilpotent.analyticOn_exp`, `IsNilpotent.analyticOn_log`: analyticity there, in a normed
  algebra.
* `IsNilpotent.expImageHomeomorph`: the exponential is a homeomorphism from a set with a common
  nilpotency bound onto its image, with inverse the logarithm.
* `IsNilpotent.contractibleSpace_image_exp`, `IsNilpotent.simplyConnectedSpace_image_exp`: the
  exponential image of a nonempty star-convex set with a common nilpotency bound is contractible
  and simply connected.
* `Subgroup.contractibleSpace_of_expSMulHom_log_mem`: a subgroup of unipotent units with
  a common nilpotency bound is contractible if it contains all real scalar exponentials
  of its logarithms.

## References

* B. C. Hall, *Lie Groups, Lie Algebras, and Representations*, 2nd ed., Springer GTM 222
  (2015), §§2.1 and 2.3, for the matrix exponential and logarithm.
* J. E. Humphreys, *Linear Algebraic Groups*, Springer GTM 21 (1975), for the polynomial
  exponential and logarithm of nilpotent and unipotent matrices in characteristic zero.
-/

public section

open Finset Set

namespace IsNilpotent

section TopologicalAlgebra

variable {A : Type*} [Ring A] [Algebra ℚ A] [TopologicalSpace A] [IsTopologicalRing A]

/-- On a nilpotent element the exponential series terminates: `NormedSpace.exp` agrees with the
finite exponential. -/
theorem normedSpace_exp_eq_exp {a : A} (ha : IsNilpotent a) : NormedSpace.exp a = exp a := by
  obtain ⟨n, hn⟩ := ha
  rw [NormedSpace.exp_eq_tsum_rat, exp_eq_sum hn]
  exact tsum_eq_sum fun i hi => by rw [pow_eq_zero_of_le (by simpa using hi) hn, smul_zero]

/-- On a unipotent element the logarithm series terminates: `NormedSpace.log` agrees with the
finite logarithm. -/
theorem normedSpace_log_eq_log {a : A} (ha : IsNilpotent (a - 1)) : NormedSpace.log a = log a := by
  obtain ⟨n, hn⟩ := ha
  rw [NormedSpace.log_eq_tsum ℚ, log_eq_sum hn]
  exact tsum_eq_sum fun i hi => by rw [pow_eq_zero_of_le (by simpa using hi) hn, smul_zero]

/-- The finite exponential is continuous on the elements killed by a fixed power. -/
theorem continuousOn_exp (n : ℕ) : ContinuousOn (exp : A → A) {a | a ^ n = 0} := by
  have h : Continuous fun a : A => ∑ i ∈ range n, (i.factorial : ℚ)⁻¹ • a ^ i := by
    simp_rw [Algebra.smul_def]
    fun_prop
  exact h.continuousOn.congr fun _ ha => exp_eq_sum ha

/-- The finite logarithm is continuous on the elements `u` with `(u - 1) ^ n = 0` for a fixed
`n`. -/
theorem continuousOn_log (n : ℕ) : ContinuousOn (log : A → A) {u | (u - 1) ^ n = 0} := by
  have h : Continuous fun u : A => ∑ i ∈ range n, ((-1 : ℚ) ^ (i + 1) / i) • (u - 1) ^ i := by
    simp_rw [Algebra.smul_def]
    fun_prop
  exact h.continuousOn.congr fun _ hu => log_eq_sum hu

/-- On a set of elements killed by a common power, the finite exponential is a homeomorphism
onto its image. The inverse is the finite logarithm. -/
noncomputable def expImageHomeomorph {s : Set A} {n : ℕ} (hs : ∀ a ∈ s, a ^ n = 0) :
    s ≃ₜ exp '' s where
  toFun := MapsTo.restrict exp s _ (mapsTo_image exp s)
  invFun := MapsTo.restrict log _ s <| by
    rintro _ ⟨a, ha, rfl⟩
    rwa [log_exp ⟨n, hs a ha⟩]
  left_inv a := Subtype.ext (log_exp ⟨n, hs a a.2⟩)
  right_inv := by
    rintro ⟨_, a, ha, rfl⟩
    exact Subtype.ext (congrArg exp (log_exp ⟨n, hs a ha⟩))
  continuous_toFun := ((continuousOn_exp n).mono hs).mapsToRestrict _
  continuous_invFun := ((continuousOn_log n).mono <| by
    rintro _ ⟨a, ha, rfl⟩
    exact pow_exp_sub_one_eq_zero (hs a ha)).mapsToRestrict _

/-- The homeomorphism `expImageHomeomorph` is the finite exponential. -/
@[simp]
theorem coe_expImageHomeomorph_apply {s : Set A} {n : ℕ} (hs : ∀ a ∈ s, a ^ n = 0) (a : s) :
    (expImageHomeomorph hs a : A) = exp (a : A) :=
  (rfl)

/-- The inverse of `expImageHomeomorph` is the finite logarithm. -/
@[simp]
theorem coe_expImageHomeomorph_symm_apply {s : Set A} {n : ℕ} (hs : ∀ a ∈ s, a ^ n = 0)
    (u : exp '' s) : ((expImageHomeomorph hs).symm u : A) = log (u : A) :=
  (rfl)

variable [Module ℝ A] [ContinuousSMul ℝ A]

/-- The exponential image of a nonempty star-convex set of elements killed by a common power is
contractible. -/
theorem contractibleSpace_image_exp {s : Set A} {x : A} (hs : StarConvex ℝ x s)
    (hne : s.Nonempty) {n : ℕ} (hn : ∀ a ∈ s, a ^ n = 0) : ContractibleSpace (exp '' s) :=
  have := hs.contractibleSpace hne
  (expImageHomeomorph hn).symm.contractibleSpace

/-- The exponential image of a nonempty star-convex set of elements killed by a common power is
simply connected. -/
theorem simplyConnectedSpace_image_exp {s : Set A} {x : A} (hs : StarConvex ℝ x s)
    (hne : s.Nonempty) {n : ℕ} (hn : ∀ a ∈ s, a ^ n = 0) : SimplyConnectedSpace (exp '' s) :=
  have := contractibleSpace_image_exp hs hne hn
  inferInstance

end TopologicalAlgebra

section Normed

variable {𝕜 A : Type*} [NontriviallyNormedField 𝕜] [NormedRing A] [NormedAlgebra 𝕜 A]
  [Algebra ℚ A]

/-- In a normed algebra, the finite exponential is analytic on the elements killed by a fixed
power. -/
theorem analyticOn_exp (n : ℕ) : AnalyticOn 𝕜 (exp : A → A) {a | a ^ n = 0} := by
  have h : AnalyticOnNhd 𝕜 (fun a : A => ∑ i ∈ range n, (i.factorial : ℚ)⁻¹ • a ^ i) univ := by
    intro _ _
    simp_rw [Algebra.smul_def]
    fun_prop
  exact (h.analyticOn.mono (subset_univ _)).congr fun _ ha => exp_eq_sum ha

/-- In a normed algebra, the finite logarithm is analytic on the elements `u` with
`(u - 1) ^ n = 0` for a fixed `n`. -/
theorem analyticOn_log (n : ℕ) : AnalyticOn 𝕜 (log : A → A) {u | (u - 1) ^ n = 0} := by
  have h : AnalyticOnNhd 𝕜
      (fun u : A => ∑ i ∈ range n, ((-1 : ℚ) ^ (i + 1) / i) • (u - 1) ^ i) univ := by
    intro _ _
    simp_rw [Algebra.smul_def]
    fun_prop
  exact (h.analyticOn.mono (subset_univ _)).congr fun _ hu => log_eq_sum hu

end Normed

end IsNilpotent

namespace Subgroup

open IsNilpotent TauCeti

variable {A : Type*} [Ring A] [Algebra ℚ A] [Algebra ℝ A]
  [TopologicalSpace A] [IsTopologicalRing A] [ContinuousSMul ℝ A]

/-- A subgroup of unipotent units is contractible if the differences from one have a
uniform nilpotency bound and every real scalar exponential of a logarithm stays in the
group. The contraction is `g ↦ exp ((1 - t) • log g)` and fixes the identity. -/
theorem contractibleSpace_of_expSMulHom_log_mem (G : Subgroup Aˣ) {n : ℕ}
    (hn : ∀ g ∈ G, ((g : A) - 1) ^ n = 0)
    (hcurve : ∀ (g : G) (t : ℝ),
      expSMulHom ℝ (isNilpotent_log ⟨n, hn g g.property⟩) (Multiplicative.ofAdd t) ∈ G) :
    ContractibleSpace G := by
  have hlog : Continuous (fun g : G ↦ log ((g : Aˣ) : A)) :=
    (continuousOn_log n).comp_continuous
      (Units.continuous_val.comp continuous_subtype_val) (fun g ↦ hn g g.property)
  have hscale : Continuous (fun p : unitInterval × G ↦
      (1 - (p.1 : ℝ)) • log ((p.2 : Aˣ) : A)) :=
    (continuous_const.sub (continuous_subtype_val.comp continuous_fst)).smul
      (hlog.comp continuous_snd)
  have hpow (t : ℝ) (g : G) : (t • log ((g : Aˣ) : A)) ^ n = 0 := by
    rw [smul_pow, pow_log_eq_zero (hn g g.property), smul_zero]
  -- The topology on units records both the value and the inverse. Their polynomial
  -- formulas use the same nilpotency bound, with opposite scalar parameters.
  let H : (ContinuousMap.id G).Homotopy (ContinuousMap.const G (1 : G)) :=
    { toFun := fun p ↦ ⟨expSMulHom ℝ
        (isNilpotent_log ⟨n, hn p.2 p.2.property⟩)
        (Multiplicative.ofAdd (1 - (p.1 : ℝ))), hcurve p.2 _⟩
      continuous_toFun := by
        apply Continuous.subtype_mk
        apply Units.continuous_iff.mpr
        constructor
        · simpa only [expSMulHom_apply, coe_nilpotentExpUnit, toAdd_ofAdd, Function.comp_def] using
            (continuousOn_exp n).comp_continuous hscale (fun p ↦ hpow _ p.2)
        · simpa only [expSMulHom_apply, coe_inv_nilpotentExpUnit, Pi.neg_apply,
            toAdd_ofAdd, Function.comp_def] using
            (continuousOn_exp n).comp_continuous hscale.neg
              (fun p ↦ by
                simpa only [Pi.neg_apply, Set.mem_ofPred_eq, neg_smul] using
                  hpow (-(1 - (p.1 : ℝ))) p.2)
      map_zero_left := by
        intro g
        apply Subtype.ext
        apply Units.ext
        simp [expSMulHom_apply, exp_log ⟨n, hn g g.property⟩]
      map_one_left := by
        intro g
        apply Subtype.ext
        apply Units.ext
        simp [expSMulHom_apply] }
  exact (contractible_iff_id_nullhomotopic G).mpr ⟨1, ⟨H⟩⟩

end Subgroup
