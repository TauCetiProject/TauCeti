/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.DifferentialForm.Wedge.Smooth.Pow
public import TauCeti.Geometry.Manifold.Orientation.TopForm
public import TauCeti.Geometry.Symplectic.Manifold.TwoForm
public import TauCeti.Geometry.Symplectic.Orientation

/-!
# The symplectic volume form and orientation of a symplectic manifold

Let `σ` be a smooth two-form on a manifold `M` modelled on a space of dimension `2 * n`. Its
**symplectic volume form** is the top-degree form

`σⁿ / n!`

(`TauCeti.SmoothTwoForm.volumeForm σ n`), built from the smooth wedge power
`TauCeti.SmoothForm.wedgePow`. At a point where `σ` is nondegenerate it takes the value `1` on
every Darboux basis `(q₁, p₁, …, qₙ, pₙ)` of the tangent space, listed in this interleaved order
(`TauCeti.SmoothTwoForm.IsNondegenerate.volumeForm_apply_reindex`). This is the classical
normalization: `σⁿ` takes the value `n!` on such a basis.

Hence a fiberwise nondegenerate two-form has a nowhere-vanishing volume form, and `M` carries the
orientation on which it is positive, the **symplectic orientation**
(`TauCeti.SmoothTwoForm.IsNondegenerate.volumeOrientation`). It is the manifold version of the
linear symplectic orientation: its orientation of each tangent space is the symplectic orientation
`TauCeti.SymplecticForm.orientation` of the value of `σ` there
(`TauCeti.SmoothTwoForm.IsNondegenerate.orientationAt_volumeOrientation`), so every Darboux basis
of a tangent space is positively oriented. Closedness of `σ` is not used.

## Main definitions

* `TauCeti.SmoothTwoForm.volumeForm σ n`: the form `σⁿ / n!`.
* `TauCeti.SmoothTwoForm.IsNondegenerate.volumeOrientation`: the symplectic orientation of a
  manifold with a fiberwise nondegenerate two-form.

## Main results

* `TauCeti.SmoothTwoForm.IsNondegenerate.volumeForm_apply_reindex`: the volume form takes the
  value `1` on Darboux bases.
* `TauCeti.SmoothTwoForm.IsNondegenerate.volumeForm_apply_ne_zero`: the volume form of a
  nondegenerate two-form vanishes nowhere.
* `TauCeti.SmoothTwoForm.IsNondegenerate.orientation_eq_orientationAt_volumeOrientation_iff`: a
  tangent basis is positive for the symplectic orientation exactly when the volume form is positive
  on it.
* `TauCeti.SmoothTwoForm.IsNondegenerate.orientationAt_volumeOrientation`: the symplectic
  orientation of each tangent space is the linear symplectic orientation of the value of the form.

## References

* D. McDuff and D. Salamon, *Introduction to Symplectic Topology*, 3rd ed., Oxford University
  Press, 2017, Section 2.1 (the linear symplectic orientation) and Chapter 3 (the volume form
  `ωⁿ / n!` of a symplectic manifold).
* A. Cannas da Silva, *Lectures on Symplectic Geometry*, Lecture Notes in Mathematics 1764,
  Springer, 2001, Chapter 1 (the symplectic volume and orientation).
-/

public section

noncomputable section

open Module
open scoped ContDiff Manifold

namespace TauCeti

namespace SmoothTwoForm

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  {σ : SmoothTwoForm I M} {n : ℕ}

/-- The **symplectic volume form** `σⁿ / n!` of a smooth two-form `σ`, a smooth form of degree
`2 * n`. When `2 * n` is the dimension and `σ` is nondegenerate, it is a volume form taking the
value `1` on Darboux bases. -/
def volumeForm (σ : SmoothTwoForm I M) (n : ℕ) : SmoothForm I M ℝ (2 * n) :=
  ((n.factorial : ℝ)⁻¹) • SmoothForm.wedgePow σ n

/-- The symplectic volume form at a point is `σⁿ / n!` for the value of `σ` there. -/
@[simp]
theorem volumeForm_apply (σ : SmoothTwoForm I M) (n : ℕ) (x : M) :
    (σ.volumeForm n).1 x = ((n.factorial : ℝ)⁻¹) • (σ.1 x).wedgePow n := by
  rw [volumeForm, Submodule.coe_smul, Pi.smul_apply, SmoothForm.wedgePow_apply]

/-- **The symplectic volume form takes the value `1` on Darboux bases.** For a Darboux basis
`(q₁, p₁, …, qₙ, pₙ)` of the tangent space at `x`, listed in this interleaved order,
`(σⁿ / n!)(q₁, p₁, …, qₙ, pₙ) = 1`. -/
theorem IsNondegenerate.volumeForm_apply_reindex (h : σ.IsNondegenerate) {x : M}
    {b : Basis (Fin n × Fin 2) ℝ (TangentSpace I x)}
    (hb : (h.symplecticFormAt x).IsDarbouxBasis b) :
    (σ.volumeForm n).1 x (b.reindex (finProdFinEquiv.trans (finCongr (Nat.mul_comm n 2)))) =
      1 := by
  have hσ (v w : TangentSpace I x) : σ.1 x ![v, w] = h.symplecticFormAt x v w := by
    rw [IsNondegenerate.symplecticFormAt_apply, SmoothBundleForm.eval₂_apply]
  have hval := ContinuousAlternatingMap.wedgePow_apply_finProdFinEquiv (σ.1 x) (m := n) b
    (fun i j ↦ by rw [hσ, hb.apply_fst_fst])
    (fun i j ↦ by rw [hσ, hb.apply_fst_snd])
  have hb' : ⇑b ∘ (finProdFinEquiv.trans (finCongr (Nat.mul_comm n 2))).symm =
      fun r ↦ b (finProdFinEquiv.symm (Fin.cast (Nat.mul_comm 2 n) r)) := by
    funext r
    simp only [Function.comp_apply, Equiv.symm_trans_apply, finCongr_symm, finCongr_apply]
  rw [volumeForm_apply, ContinuousAlternatingMap.smul_apply, Basis.coe_reindex, hb', hval,
    smul_eq_mul, inv_mul_cancel₀ (by positivity)]

/-- **The symplectic volume form of a nondegenerate two-form vanishes nowhere**, on a manifold
modelled on a space of dimension `2 * n`. -/
theorem IsNondegenerate.volumeForm_apply_ne_zero [FiniteDimensional ℝ E]
    (h : σ.IsNondegenerate) (hn : finrank ℝ E = 2 * n) (x : M) :
    (σ.volumeForm n).1 x ≠ 0 := by
  obtain ⟨b, hb⟩ := (h.symplecticFormAt x).exists_isDarbouxBasis_of_finrank_eq
    (n := n) (hn.trans (Nat.mul_comm 2 n))
  rw [← ContinuousAlternatingMap.map_basis_ne_zero_iff _
    (b.reindex (finProdFinEquiv.trans (finCongr (Nat.mul_comm n 2)))),
    h.volumeForm_apply_reindex hb]
  exact one_ne_zero

/-- The **symplectic orientation** of a manifold modelled on a space of dimension `2 * n` with a
fiberwise nondegenerate two-form `σ`: the orientation on which the volume form `σⁿ / n!` is
positive. -/
def IsNondegenerate.volumeOrientation [FiniteDimensional ℝ E] (h : σ.IsNondegenerate)
    (hn : finrank ℝ E = 2 * n) : Manifold.Orientation I M (Fin (2 * n)) :=
  Manifold.Orientation.ofTopForm hn (σ.volumeForm n).1
    ((σ.volumeForm n).isSmoothForm.of_le bot_le) (h.volumeForm_apply_ne_zero hn)

/-- A tangent basis is positive for the symplectic orientation exactly when the symplectic volume
form is positive on it. -/
theorem IsNondegenerate.orientation_eq_orientationAt_volumeOrientation_iff [FiniteDimensional ℝ E]
    (h : σ.IsNondegenerate) (hn : finrank ℝ E = 2 * n) {x : M}
    (b : Basis (Fin (2 * n)) ℝ (TangentSpace I x)) :
    b.orientation = Manifold.Orientation.orientationAt (h.volumeOrientation hn) x ↔
      0 < (σ.volumeForm n).1 x b :=
  Manifold.Orientation.orientation_eq_orientationAt_ofTopForm_iff hn _ _ b

/-- **The symplectic orientation is the linear symplectic orientation on each tangent space**:
at every point it is the orientation `TauCeti.SymplecticForm.orientation` of the symplectic
vector space formed by the tangent space and the value of `σ`, the orientation of its Darboux
bases. -/
@[simp]
theorem IsNondegenerate.orientationAt_volumeOrientation [FiniteDimensional ℝ E]
    (h : σ.IsNondegenerate) (hn : finrank ℝ E = 2 * n) (x : M) :
    Manifold.Orientation.orientationAt (h.volumeOrientation hn) x =
      (h.symplecticFormAt x).orientation (k := 2 * n) hn := by
  obtain ⟨b, hb⟩ := (h.symplecticFormAt x).exists_isDarbouxBasis_of_finrank_eq
    (n := n) (hn.trans (Nat.mul_comm 2 n))
  rw [← hb.orientation_reindex hn (Nat.mul_comm n 2), eq_comm,
    h.orientation_eq_orientationAt_volumeOrientation_iff hn, h.volumeForm_apply_reindex hb]
  exact one_pos

end SmoothTwoForm

end TauCeti
