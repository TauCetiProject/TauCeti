/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.MFDeriv.SpecificFunctions
public import TauCeti.RepresentationTheory.SU2.Adjoint
public import TauCeti.RepresentationTheory.SU2.ConjugacyClasses
import TauCeti.Algebra.Quaternion.ComplexMatrix
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

/-!
# Normal subgroups of `SU(2)` and the simplicity of `SO(3)`

The center of `SU(2)` is `{1, -1}` (`TauCeti.SU2.mem_center_iff`, proved alongside the double
cover), and it is the only source of
proper normal subgroups: **every normal subgroup of `SU(2)` lies in the center or is the whole
group** (`TauCeti.SU2.le_center_or_eq_top`). No topology enters the statement; it is a fact about
the abstract group. Since the only subgroups of `{1, -1}` are `⊥` and the center, the normal
subgroups of `SU(2)` are exactly `⊥`, the center and `⊤`
(`TauCeti.SU2.eq_bot_or_eq_center_or_eq_top_of_normal`).

Consequently a homomorphism out of `SU(2)` is either trivial or has kernel contained in `{1, -1}`
(`TauCeti.SU2.ker_le_center`). For instance, a homomorphism `φ : SU(2) → G` of Lie groups whose
differential sends `diag (i, -i)` to a nonzero vector, such as a coroot `α∨` with `α(α∨) = 2`, is
not trivial, so its kernel lies in `{1, -1}`; conversely the trivial homomorphism has kernel all
of the noncommutative `SU(2)` (`TauCeti.SU2.ker_le_center_iff`). The derivative condition needs no
smoothness of `φ` and no Lie group structure on `G`: if `G` is a manifold and the curve
`t ↦ φ (diag (e^{it}, e^{-it}))` has a nonzero derivative at `0`, then `ker φ ⊆ {1, -1}`
(`TauCeti.SU2.ker_le_center_of_mfderiv_ne_zero`). The bound is attained by the double cover
`SU(2) → SO(3)`, whose kernel is the whole center (`TauCeti.SU2.ker_toSO3`). Pushed through that
double cover, the classification says that **`SO(3)` is a simple group**
(`TauCeti.isSimpleGroup_specialOrthogonalGroup_fin_three`).

## Implementation notes

Let `N` be a normal subgroup containing a noncentral element `g`. The trace classifies conjugacy
classes in `SU(2)` (`TauCeti.SU2.isConj_iff_trace_eq`), so `N` contains the torus element
`t = diag (e^{iθ}, e^{-iθ})` conjugate to `g`, and `sin θ ≠ 0` because `g ≠ ±1`. For the real
rotation `k_φ = !![cos φ, sin φ; -sin φ, cos φ]` the commutator `t k_φ t⁻¹ k_φ⁻¹` lies in `N`, and
its trace is `2 - 4 sin² φ sin² θ`. As `φ` varies these traces fill the interval
`[2 - 4 sin² θ, 2]`, so `N` contains every torus element `diag (e^{iψ}, e^{-iψ})` with
`|ψ| ≤ 2 |sin θ|`. Products of such elements give every torus element, and every element of
`SU(2)` is conjugate into the torus, so `N = SU(2)`.

## Main results

* `TauCeti.SU2.le_center_or_eq_top`: a normal subgroup of `SU(2)` lies in the center or is
  everything.
* `TauCeti.SU2.eq_bot_or_eq_center_or_eq_top_of_normal`: the normal subgroups of `SU(2)` are `⊥`,
  the center and `⊤`.
* `TauCeti.SU2.ker_le_center`: a nontrivial homomorphism out of `SU(2)` has kernel in `{1, -1}`.
* `TauCeti.SU2.ker_le_center_iff`: a homomorphism out of `SU(2)` has kernel in `{1, -1}` exactly
  when it is nontrivial.
* `TauCeti.SU2.ker_le_center_of_mfderiv_ne_zero`: the kernel bound from a nonzero derivative along
  the maximal torus.
* `TauCeti.isSimpleGroup_specialOrthogonalGroup_fin_three`: `SO(3)` is a simple group.

## References

* John Stillwell, *Naive Lie Theory*, Undergraduate Texts in Mathematics, Springer, 2008,
  Section 2.3 (the simplicity of `SO(3)`, from the conjugacy classes of rotations).
* Brian Conrad and Aaron Landesman, *Compact Lie Groups*, lecture notes, Stanford, Section 18
  (the kernel of a rank-one homomorphism out of `SU(2)` is central).
-/

public section

noncomputable section

open Matrix
open scoped Quaternion

namespace TauCeti

namespace SU2

/-! ### Commutators of torus elements with real rotations -/

/-- The real rotation matrix `!![cos φ, sin φ; -sin φ, cos φ]`, viewed as a complex matrix. -/
private def rotationMatrix (φ : ℝ) : Matrix (Fin 2) (Fin 2) ℂ :=
  !![(Real.cos φ : ℂ), Real.sin φ; -Real.sin φ, Real.cos φ]

/-- The real rotation by `φ` is the matrix of the unit quaternion `cos φ + sin φ j`. -/
private theorem rotationMatrix_mem (φ : ℝ) :
    rotationMatrix φ ∈ specialUnitaryGroup (Fin 2) ℂ := by
  have hq : (⟨Real.cos φ, 0, Real.sin φ, 0⟩ : ℍ[ℝ]) ∈ unitary ℍ[ℝ] := by
    rw [Quaternion.mem_unitary_iff_normSq_eq_one, Quaternion.normSq_def']
    linear_combination Real.cos_sq_add_sin_sq φ
  convert Quaternion.mem_specialUnitaryGroup_toComplexMatrix hq using 1
  rw [Quaternion.toComplexMatrix_apply, rotationMatrix]
  simp

/-- The real rotation `!![cos φ, sin φ; -sin φ, cos φ]` as an element of `SU(2)`. -/
private def rotation (φ : ℝ) : SU2 := ⟨rotationMatrix φ, rotationMatrix_mem φ⟩

/-- The commutator of the torus element `diag (e^{iθ}, e^{-iθ})` with the real rotation by `φ`
has trace `2 - 4 sin² φ sin² θ`. -/
private theorem trace_torusExp_mul_rotation_mul_inv_mul_inv (θ φ : ℝ) :
    Matrix.trace ((torusExp θ * rotation φ * (torusExp θ)⁻¹ * (rotation φ)⁻¹ : SU2) :
        Matrix (Fin 2) (Fin 2) ℂ) =
      ((2 - 4 * Real.sin φ ^ 2 * Real.sin θ ^ 2 : ℝ) : ℂ) := by
  rw [← torusExp_neg, ← Matrix.star_eq_inv]
  simp only [Submonoid.coe_mul, Matrix.specialUnitaryGroup.coe_star, coe_torusExp, rotation,
    rotationMatrix, Matrix.trace_fin_two]
  simp only [Complex.ofReal_neg, neg_mul, neg_neg, star_eq_conjTranspose, Fin.isValue,
    Matrix.mul_apply, of_apply, cons_val', cons_val_fin_one, Fin.sum_univ_two, diagonal_apply_eq,
    cons_val_zero, ne_eq, zero_ne_one, not_false_eq_true, diagonal_apply_ne, cons_val_one, zero_mul,
    add_zero, conjTranspose_apply, RCLike.star_def, one_ne_zero, mul_zero, Complex.conj_ofReal,
    zero_add, mul_neg, map_neg, neg_zero, Complex.ofReal_sub, Complex.ofReal_ofNat,
    Complex.ofReal_mul, Complex.ofReal_pow]
  -- With `e = e^{iθ}`, the trace is `2 cos² φ e e⁻¹ + sin² φ (e² + e⁻²)`.
  have h₁ : Complex.exp (θ * Complex.I) * Complex.exp (-(θ * Complex.I)) = 1 := by
    rw [← Complex.exp_add, add_neg_cancel, Complex.exp_zero]
  have h₂ : Complex.exp (θ * Complex.I) + Complex.exp (-(θ * Complex.I)) = 2 * Real.cos θ := by
    rw [Complex.ofReal_cos, Complex.two_cos, neg_mul]
  have h₃ : (Real.cos θ : ℂ) ^ 2 + (Real.sin θ : ℂ) ^ 2 = 1 := by
    exact_mod_cast Real.cos_sq_add_sin_sq θ
  have h₄ : (Real.cos φ : ℂ) ^ 2 + (Real.sin φ : ℂ) ^ 2 = 1 := by
    exact_mod_cast Real.cos_sq_add_sin_sq φ
  linear_combination (2 * (Real.cos φ : ℂ) ^ 2 - 2 * (Real.sin φ : ℂ) ^ 2) * h₁ +
    (Real.sin φ : ℂ) ^ 2 *
      (Complex.exp (θ * Complex.I) + Complex.exp (-(θ * Complex.I)) + 2 * Real.cos θ) * h₂ +
    4 * (Real.sin φ : ℂ) ^ 2 * h₃ + 2 * h₄

/-! ### Normal subgroups -/

/-- A normal subgroup of `SU(2)` containing `diag (e^{iθ}, e^{-iθ})` with `sin θ ≠ 0` contains
every torus element `diag (e^{iψ}, e^{-iψ})` with `|ψ| ≤ 2 |sin θ|`. -/
private theorem torusExp_mem_of_abs_le {N : Subgroup SU2} [N.Normal] {θ ψ : ℝ}
    (hθ : torusExp θ ∈ N) (hsin : Real.sin θ ≠ 0) (hψ : |ψ| ≤ 2 * |Real.sin θ|) :
    torusExp ψ ∈ N := by
  -- Choose `φ` with `sin φ = sin (ψ / 2) / sin θ`, possible since `|sin (ψ / 2)| ≤ |ψ| / 2`.
  have hs : |Real.sin (ψ / 2) / Real.sin θ| ≤ 1 := by
    rw [abs_div, div_le_one (abs_pos.mpr hsin)]
    calc |Real.sin (ψ / 2)| ≤ |ψ / 2| := Real.abs_sin_le_abs
      _ ≤ |Real.sin θ| := by rw [abs_div, abs_two]; linarith
  obtain ⟨hs₁, hs₂⟩ := abs_le.mp hs
  have hφ := Real.sin_arcsin hs₁ hs₂
  set φ := Real.arcsin (Real.sin (ψ / 2) / Real.sin θ)
  -- The commutator of `diag (e^{iθ}, e^{-iθ})` with the rotation by `φ` lies in `N`.
  have hmem : torusExp θ * rotation φ * (torusExp θ)⁻¹ * (rotation φ)⁻¹ ∈ N := by
    rw [mul_assoc, mul_assoc]
    refine N.mul_mem hθ ?_
    rw [← mul_assoc]
    exact ‹N.Normal›.conj_mem _ (N.inv_mem hθ) _
  -- Its trace `2 - 4 sin² φ sin² θ = 2 - 4 sin² (ψ / 2)` is `2 cos ψ`, the trace of the target.
  have htr : Matrix.trace ((torusExp θ * rotation φ * (torusExp θ)⁻¹ * (rotation φ)⁻¹ : SU2) :
      Matrix (Fin 2) (Fin 2) ℂ) = Matrix.trace ((torusExp ψ : SU2) : Matrix (Fin 2) (Fin 2) ℂ) := by
    have hcos : Real.cos ψ = 1 - 2 * Real.sin (ψ / 2) ^ 2 := by
      rw [← Real.cos_two_mul_eq_one_sub, mul_div_cancel₀ ψ two_ne_zero]
    have key : 2 - 4 * (Real.sin (ψ / 2) / Real.sin θ) ^ 2 * Real.sin θ ^ 2 = 2 * Real.cos ψ := by
      rw [hcos]
      field_simp
      ring
    rw [trace_torusExp_mul_rotation_mul_inv_mul_inv, trace_torusExp, hφ, key, Complex.ofReal_mul,
      Complex.ofReal_ofNat]
  obtain ⟨c, hc⟩ := isConj_iff.mp (isConj_iff_trace_eq.mpr htr)
  rw [← hc]
  exact ‹N.Normal›.conj_mem _ hmem c

/-- A normal subgroup of `SU(2)` containing `diag (e^{iθ}, e^{-iθ})` with `sin θ ≠ 0` contains
the whole maximal torus. -/
private theorem torusExp_mem_of_sin_ne_zero {N : Subgroup SU2} [N.Normal] {θ : ℝ}
    (hθ : torusExp θ ∈ N) (hsin : Real.sin θ ≠ 0) (ψ : ℝ) : torusExp ψ ∈ N := by
  -- Write `ψ = n (ψ / n)` with `|ψ / n| ≤ 2 |sin θ|`.
  have hpos : 0 < 2 * |Real.sin θ| := by positivity
  obtain ⟨n, hn⟩ := exists_nat_gt (|ψ| / (2 * |Real.sin θ|))
  have hn₀ : (0 : ℝ) < n := (div_nonneg (abs_nonneg ψ) hpos.le).trans_lt hn
  rw [← mul_div_cancel₀ ψ hn₀.ne', torusExp_def, Circle.exp_natCast_mul, map_pow, ← torusExp_def]
  refine N.pow_mem (torusExp_mem_of_abs_le hθ hsin ?_) n
  rw [abs_div, Nat.abs_cast, div_le_iff₀ hn₀]
  rw [div_lt_iff₀ hpos] at hn
  linarith

/-- **The normal subgroups of `SU(2)`.** A normal subgroup of `SU(2)` lies in the center
`{1, -1}` or is the whole group. -/
theorem le_center_or_eq_top (N : Subgroup SU2) [N.Normal] :
    N ≤ Subgroup.center SU2 ∨ N = ⊤ := by
  refine or_iff_not_imp_left.mpr fun hN ↦ ?_
  obtain ⟨g, hgN, hgc⟩ := Set.not_subset.mp hN
  -- `N` contains the torus element `diag (e^{iθ}, e^{-iθ})` conjugate to the noncentral `g`.
  obtain ⟨θ, hθ⟩ := exists_isConj_torusExp g
  have hθN : torusExp θ ∈ N := by
    obtain ⟨c, hc⟩ := isConj_iff.mp hθ
    rw [← hc]
    exact ‹N.Normal›.conj_mem _ hgN c
  -- That torus element is not central, so `sin θ ≠ 0`.
  have hsin : Real.sin θ ≠ 0 := fun h ↦ by
    obtain ⟨n, hn⟩ := Real.sin_eq_zero_iff.mp h
    have hz : torusExp θ ∈ Subgroup.center SU2 := by
      rw [← ker_toSO3, MonoidHom.mem_ker, toSO3_torusExp_eq_one_iff]
      exact ⟨n, hn.symm⟩
    exact hgc ((hθ.eq_of_right_mem_center hz).symm ▸ hz)
  -- So `N` contains the whole torus, which meets every conjugacy class.
  refine eq_top_iff.mpr fun h _ ↦ ?_
  obtain ⟨ψ, hψ⟩ := exists_isConj_torusExp h
  obtain ⟨c, hc⟩ := isConj_iff.mp hψ.symm
  rw [← hc]
  exact ‹N.Normal›.conj_mem _ (torusExp_mem_of_sin_ne_zero hθN hsin ψ) c

/-- **The kernel of a nontrivial homomorphism out of `SU(2)` lies in the center `{1, -1}`.** -/
theorem ker_le_center {M : Type*} [MulOneClass M] {φ : SU2 →* M} (hφ : φ ≠ 1) :
    φ.ker ≤ Subgroup.center SU2 :=
  (le_center_or_eq_top φ.ker).resolve_right fun h ↦ hφ (MonoidHom.ker_eq_top_iff.mp h)

/-- **A subgroup of the center `{1, -1}` of `SU(2)` is `⊥` or the center.** -/
theorem eq_bot_or_eq_center_of_le_center {K : Subgroup SU2} (hK : K ≤ Subgroup.center SU2) :
    K = ⊥ ∨ K = Subgroup.center SU2 := by
  refine K.bot_or_exists_ne_one.imp_right fun ⟨k, hkK, hk⟩ ↦ le_antisymm hK fun z hz ↦ ?_
  rcases mem_center_iff.mp hz with hz | hz
  · rw [show z = 1 from Subtype.ext hz]
    exact K.one_mem
  · rcases mem_center_iff.mp (hK hkK) with hk' | hk'
    · exact absurd (Subtype.ext hk') hk
    · rwa [show z = k from Subtype.ext (hz.trans hk'.symm)]

/-- **The normal subgroups of `SU(2)` are `⊥`, the center `{1, -1}` and `⊤`.** -/
theorem eq_bot_or_eq_center_or_eq_top_of_normal (N : Subgroup SU2) [N.Normal] :
    N = ⊥ ∨ N = Subgroup.center SU2 ∨ N = ⊤ :=
  (le_center_or_eq_top N).elim
    (fun h ↦ (eq_bot_or_eq_center_of_le_center h).elim Or.inl (Or.inr ∘ Or.inl))
    (Or.inr ∘ Or.inr)

/-- **A homomorphism out of `SU(2)` has kernel in the center `{1, -1}` exactly when it is
nontrivial.** -/
theorem ker_le_center_iff {M : Type*} [MulOneClass M] {φ : SU2 →* M} :
    φ.ker ≤ Subgroup.center SU2 ↔ φ ≠ 1 := by
  refine ⟨fun h hφ ↦ center_ne_top (top_le_iff.mp ?_), ker_le_center⟩
  rwa [hφ, MonoidHom.ker_one] at h

/-- **The kernel of a nontrivial homomorphism out of `SU(2)` is `⊥` or the center `{1, -1}`.** -/
theorem ker_eq_bot_or_eq_center {M : Type*} [MulOneClass M] {φ : SU2 →* M} (hφ : φ ≠ 1) :
    φ.ker = ⊥ ∨ φ.ker = Subgroup.center SU2 :=
  eq_bot_or_eq_center_of_le_center (ker_le_center hφ)

open scoped Manifold in
/-- **Kernel bound for rank-one maps.** Let `φ : SU(2) →* G` be a homomorphism into a manifold
`G` such that the curve `t ↦ φ (diag (e^{it}, e^{-it}))` has a nonzero derivative at `t = 0`,
as it does when `φ` is smooth with differential at the identity nonzero on `diag (i, -i)`. Then
the kernel of `φ` is contained in the center `{1, -1}` of `SU(2)`. -/
theorem ker_le_center_of_mfderiv_ne_zero {E H G : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [TopologicalSpace G]
    [ChartedSpace H G] [MulOneClass G] {φ : SU2 →* G}
    (h : mfderiv 𝓘(ℝ) I (fun t : ℝ ↦ φ (torusExp t)) 0 ≠ 0) :
    φ.ker ≤ Subgroup.center SU2 := by
  refine ker_le_center fun hφ ↦ h ?_
  subst hφ
  simp only [MonoidHom.one_apply]
  exact mfderiv_const

end SU2

/-- **`SO(3)` is a simple group.** Its normal subgroups pull back along the double cover
`SU(2) → SO(3)` to normal subgroups of `SU(2)` containing the center, the kernel of the cover. -/
instance isSimpleGroup_specialOrthogonalGroup_fin_three :
    IsSimpleGroup (specialOrthogonalGroup (Fin 3) ℝ) where
  exists_pair_ne := by
    obtain ⟨g, -, hg⟩ := IsConcreteLE.exists_of_lt SU2.center_ne_top.lt_top
    refine ⟨SU2.toSO3 g, 1, fun h ↦ hg ?_⟩
    rwa [← SU2.ker_toSO3, MonoidHom.mem_ker]
  eq_bot_or_eq_top_of_normal N hN := by
    have hsurj := SU2.toSO3_surjective
    rcases SU2.le_center_or_eq_top (N.comap SU2.toSO3) with h | h
    · refine Or.inl (eq_bot_iff.mpr fun x hx ↦ ?_)
      obtain ⟨g, rfl⟩ := hsurj x
      rw [Subgroup.mem_bot, ← MonoidHom.mem_ker, SU2.ker_toSO3]
      exact h hx
    · refine Or.inr (eq_top_iff.mpr fun x _ ↦ ?_)
      obtain ⟨g, rfl⟩ := hsurj x
      exact Subgroup.mem_comap.mp (h ▸ Subgroup.mem_top g)

end TauCeti
