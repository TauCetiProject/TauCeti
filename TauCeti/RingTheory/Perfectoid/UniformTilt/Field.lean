/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Field.WithAbs
public import TauCeti.RingTheory.Perfectoid.Field
public import TauCeti.RingTheory.Perfectoid.PseudoUniformizerRoots.Existence
public import TauCeti.RingTheory.Perfectoid.UniformTilt.Basic
import Mathlib.Algebra.CharP.Algebra

/-!
# The tilt of a perfectoid field

Let `K` be a complete nontrivially normed field with an ultrametric norm in which `p` is
topologically nilpotent, and let `K♭ = uniformTilt p K` be its tilt. Then `K♭` is a field: an
element `x` vanishes as soon as its zeroth coordinate `x♯ = x⁽⁰⁾` does, and it is a unit as soon
as `x♯` is. Moreover `|x|♭ := ‖x♯‖` is an absolute value on `K♭`. It is multiplicative because
the coordinates are, and it is ultrametric by the limit formula
`(x + y)♯ = lim_{m → ∞} (x⁽ᵐ⁾ + y⁽ᵐ⁾) ^ p ^ m`, since `‖x⁽ᵐ⁾‖ ^ p ^ m = ‖x♯‖`.

The normed field `tiltField p K` is `K♭` with this absolute value, Mathlib's `WithAbs` construction.
Its norm topology is the inverse-limit topology of `K♭`, because `‖x⁽ⁿ⁾‖ = ‖x♯‖ ^ (1 / p ^ n)`, so
it is complete. When `K` is a perfectoid field, a pseudouniformiser `ϖ♭` with compatible roots
gives an element of `tiltField p K` of norm `‖ϖ‖ ∈ (0, 1)`, so `tiltField p K` is a nontrivially
normed field. It is perfect of characteristic `p`, hence a perfectoid field.

## Main definitions

* `TauCeti.Perfectoid.uniformTilt.instField`: the tilt of a field is a field.
* `TauCeti.Perfectoid.uniformTilt.sharpAbsoluteValue p K`: the absolute value `x ↦ ‖x♯‖`.
* `TauCeti.Perfectoid.tiltField p K`: the tilt `K♭` as a normed field.

## Main results

* `TauCeti.Perfectoid.uniformTilt.norm_coeff_zero_add_le`: `‖(x + y)♯‖ ≤ max ‖x♯‖ ‖y♯‖`.
* `TauCeti.Perfectoid.tiltField.isHomeomorph_equiv`: the norm topology of `tiltField p K` is the
  inverse-limit topology of `uniformTilt p K`.
* `TauCeti.Perfectoid.tiltField.instIsPerfectoidField`: the tilt of a perfectoid field is a
  perfectoid field.

## References

* P. Scholze, *Perfectoid spaces*, Lemma 3.4.
* K. S. Kedlaya, *Nonarchimedean geometry of Witt vectors and the tilting equivalence*, in
  *Perfectoid Spaces: Lectures from the 2017 Arizona Winter School*, Lemma 2.7.1.
-/

public section

open Filter Topology TauCeti.Huber

namespace TauCeti.Perfectoid

namespace uniformTilt

variable {p : ℕ} [hp : Fact p.Prime]

section Field

variable {K : Type*} [Field K] [UniformSpace K] [IsUniformAddGroup K] [IsTopologicalRing K]
  [IsTateRing K] [CompleteSpace K] [T2Space K] [IsUniform K]
  [Fact (IsTopologicallyNilpotent (p : K))]

variable (p K) in
/-- **The tilt of a field is a field**: a nonzero `x` has `x♯ ≠ 0`, hence is a unit. -/
theorem isField : IsField (uniformTilt p K) where
  exists_pair_ne := exists_pair_ne _
  mul_comm := mul_comm
  mul_inv_cancel hx := isUnit_iff_exists_inv.mp <| isUnit_iff_coeff_zero.mpr <|
    isUnit_iff_ne_zero.mpr (coeff_zero_eq_zero_iff.not.mpr hx)

/-- The field structure of the tilt of a field, with the ring structure of the tilt. -/
noncomputable instance instField : Field (uniformTilt p K) :=
  (isField p K).toField

end Field

section Normed

variable {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
  [Fact (IsTopologicallyNilpotent (p : K))]

/-- The norm of the `n`-th coordinate is the `p ^ n`-th root of the norm of the zeroth. -/
theorem norm_coeff_pow (x : uniformTilt p K) (n : ℕ) :
    ‖coeff p K n x‖ ^ p ^ n = ‖coeff p K 0 x‖ := by
  rw [← norm_pow, ← coeff_pow_p_pow x 0 n, zero_add]

/-- **The norm of the zeroth coordinate is ultrametric**: `‖(x + y)♯‖ ≤ max ‖x♯‖ ‖y♯‖`. The
zeroth coordinate is the limit of `(x⁽ᵐ⁾ + y⁽ᵐ⁾) ^ p ^ m`, whose norm is at most
`max ‖x⁽ᵐ⁾‖ ‖y⁽ᵐ⁾‖ ^ p ^ m = max ‖x♯‖ ‖y♯‖`. -/
theorem norm_coeff_zero_add_le (x y : uniformTilt p K) :
    ‖coeff p K 0 (x + y)‖ ≤ max ‖coeff p K 0 x‖ ‖coeff p K 0 y‖ := by
  refine le_of_tendsto' ((continuous_norm.tendsto _).comp (coeff_add x y 0)) fun m ↦ ?_
  simp only [Function.comp_apply, zero_add, norm_pow]
  calc ‖coeff p K m x + coeff p K m y‖ ^ p ^ m
      ≤ max ‖coeff p K m x‖ ‖coeff p K m y‖ ^ p ^ m := by
        gcongr; exact IsUltrametricDist.norm_add_le_max _ _
    _ = max ‖coeff p K 0 x‖ ‖coeff p K 0 y‖ := by
        rw [max_pow_of_nonneg (norm_nonneg _) (norm_nonneg _), norm_coeff_pow, norm_coeff_pow]

variable (p K) in
/-- The absolute value `|x|♭ = ‖x♯‖` on the tilt of a complete ultrametric field. -/
noncomputable def sharpAbsoluteValue : AbsoluteValue (uniformTilt p K) ℝ where
  toFun x := ‖coeff p K 0 x‖
  map_mul' x y := by rw [map_mul, norm_mul]
  nonneg' _ := norm_nonneg _
  eq_zero' _ := by rw [norm_eq_zero, coeff_zero_eq_zero_iff]
  add_le' x y := (norm_coeff_zero_add_le x y).trans
    (max_le_add_of_nonneg (norm_nonneg _) (norm_nonneg _))

/-- The absolute value `sharpAbsoluteValue p K` is the norm of the zeroth coordinate. -/
@[simp]
theorem sharpAbsoluteValue_apply (x : uniformTilt p K) :
    sharpAbsoluteValue p K x = ‖coeff p K 0 x‖ := (rfl)

end Normed

end uniformTilt

open uniformTilt

section General

variable (p : ℕ) [Fact p.Prime] (K : Type*) [NontriviallyNormedField K] [IsUltrametricDist K]
  [CompleteSpace K] [Fact (IsTopologicallyNilpotent (p : K))]

/-- The tilt `K♭ = uniformTilt p K` of a complete ultrametric field `K`, as the normed field with
norm `‖x‖ = ‖x♯‖`. Mathlib's `WithAbs.equiv` identifies it with `uniformTilt p K` as a ring, and
`tiltField.isHomeomorph_equiv` as a topological space. -/
abbrev tiltField : Type _ := WithAbs (sharpAbsoluteValue p K)

namespace tiltField

variable {p K}

/-- The norm of the tilt is the norm of the zeroth coordinate. -/
theorem norm_def (x : tiltField p K) : ‖x‖ = ‖coeff p K 0 (WithAbs.equiv _ x)‖ := (rfl)

/-- The norm of an element of the tilt, viewed in `tiltField p K`, is the norm of its zeroth
coordinate. -/
@[simp]
theorem norm_toAbs (x : uniformTilt p K) :
    ‖WithAbs.toAbs (sharpAbsoluteValue p K) x‖ = ‖coeff p K 0 x‖ := (rfl)

variable (p K) in
/-- **The norm of the tilt is ultrametric.** -/
instance instIsUltrametricDist : IsUltrametricDist (tiltField p K) :=
  IsUltrametricDist.isUltrametricDist_of_forall_norm_add_le_max_norm (S' := tiltField p K)
    fun x y ↦ norm_coeff_zero_add_le (WithAbs.equiv _ x) (WithAbs.equiv _ y)

variable (p K) in
/-- **The norm topology of the tilt is its inverse-limit topology**: a sequence tends to zero in
norm exactly when its zeroth coordinates do, and then all coordinates do since
`‖x⁽ⁿ⁾‖ ^ p ^ n = ‖x♯‖`. -/
theorem isHomeomorph_equiv : IsHomeomorph (WithAbs.equiv (sharpAbsoluteValue p K)) := by
  set e := WithAbs.equiv (sharpAbsoluteValue p K)
  -- both maps are additive, so continuity at zero suffices
  have h₁ : Continuous e := by
    refine continuous_of_continuousAt_zero e ?_
    rw [ContinuousAt, map_zero, tendsto_nhds_iff]
    intro n
    rw [coeff_zero, Metric.tendsto_nhds_nhds]
    intro ε hε
    refine ⟨ε ^ p ^ n, pow_pos hε _, fun x hx ↦ ?_⟩
    rw [dist_zero_right] at hx ⊢
    rw [norm_def, ← norm_coeff_pow] at hx
    exact lt_of_pow_lt_pow_left₀ _ hε.le hx
  have h₂ : Continuous e.symm := by
    refine continuous_of_continuousAt_zero e.symm ?_
    rw [ContinuousAt, map_zero, tendsto_zero_iff_norm_tendsto_zero]
    have h := (continuous_coeff (p := p) (B := K) 0).norm.tendsto 0
    rw [coeff_zero, norm_zero] at h
    simpa only [e, WithAbs.equiv_symm_apply, norm_toAbs] using h
  exact (Homeomorph.mk e.toEquiv h₁ h₂).isHomeomorph

variable (p K) in
/-- **The tilt is complete**, its norm topology being the complete inverse-limit topology. -/
instance instCompleteSpace : CompleteSpace (tiltField p K) :=
  (completeSpace_congr (e := (WithAbs.equiv (sharpAbsoluteValue p K)).toEquiv)
    (AddMonoidHom.isUniformEmbedding_of_isEmbedding (f := WithAbs.equiv (sharpAbsoluteValue p K))
      (isHomeomorph_equiv p K).isEmbedding)).mpr inferInstance

/-- **The tilt has characteristic `p`.** -/
instance instCharP : CharP (tiltField p K) p :=
  charP_of_injective_ringHom (f := (WithAbs.equiv (sharpAbsoluteValue p K)).symm.toRingHom)
    (WithAbs.equiv _).symm.injective p

/-- **The tilt is perfect.** -/
instance instPerfectRing : PerfectRing (tiltField p K) p :=
  PerfectRing.ofSurjective _ p fun y ↦
    ⟨WithAbs.toAbs _ ((frobeniusEquiv (uniformTilt p K) p).symm (WithAbs.ofAbs y)), by
      simp [frobenius_def, ← WithAbs.toAbs_pow]⟩

end tiltField

end General

namespace tiltField

variable {p : ℕ} [Fact p.Prime] {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K]
  [CompleteSpace K] [IsPerfectoidField p K]

/-- **The tilt of a perfectoid field is nontrivially normed**: a pseudouniformiser `ϖ♭` with
compatible roots has norm `‖ϖ‖ ∈ (0, 1)`. -/
noncomputable instance instNontriviallyNormedField : NontriviallyNormedField (tiltField p K) :=
  NontriviallyNormedField.ofNormNeOne <| by
    obtain ⟨ϖ⟩ := PseudoUniformizerRoots.nonempty (p := p) (R := K)
    obtain ⟨hϖ0, hϖ1⟩ := isPseudoUniformizer_iff_norm_lt_one.mp ϖ.isPseudoUniformizer_root_zero
    refine ⟨WithAbs.toAbs _ (mk ϖ.root ϖ.root_succ_pow), ?_, ?_⟩
    · rw [ne_eq, ← norm_eq_zero, norm_toAbs, coeff_mk, norm_eq_zero]
      exact hϖ0
    · rw [norm_toAbs, coeff_mk]
      exact hϖ1.ne

/-- **The tilt of a perfectoid field is a perfectoid field** of characteristic `p`, with norm
`‖x‖ = ‖x♯‖` (Scholze, *Perfectoid spaces*, Lemma 3.4(iii)). -/
instance instIsPerfectoidField : IsPerfectoidField p (tiltField p K) :=
  isPerfectoidField_iff_perfectRing.mpr inferInstance

end tiltField

end TauCeti.Perfectoid
