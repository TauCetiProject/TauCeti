/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.InnerProductSpace.HodgeStar.Kahler.Mass
public import TauCeti.Analysis.InnerProductSpace.Orthonormal.CalibratedFrame
public import TauCeti.Analysis.InnerProductSpace.Orthonormal.Wedge
import TauCeti.Geometry.Symplectic.CompatibleMetric
import TauCeti.Geometry.Symplectic.ExistsCompatible
import TauCeti.Topology.Algebra.Module.Alternating.TopDegree

/-!
# Normalized powers of the Kähler form and the Wirtinger inequality

Let `J` be an orthogonal almost complex structure on a finite-dimensional real inner product space
`V`, with Kähler form `ω(u, w) = ⟪J u, w⟫`, the form of the Kähler two-vector
`TauCeti.AlmostComplexStructure.kahlerForm J`. The **normalized Kähler power**
`TauCeti.AlmostComplexStructure.kahlerPowerForm J r` is the real `2r`-form `ω ^ r / r!`, for the
wedge powers `ContinuousAlternatingMap.wedgePow` in the determinant normalization.

For a family `u` of `r` vectors, `TauCeti.AlmostComplexStructure.complexRealFrame J u` is the real
frame `(u₀, J u₀, u₁, J u₁, …)`. It is orthonormal exactly when `u` is orthonormal for the
Hermitian metric of `J`: `u` is orthonormal and `⟪J uᵢ, uⱼ⟫ = 0` for all `i` and `j`. Such frames
are positively oriented orthonormal frames of complex `r`-planes with their complex orientation
(every complex `r`-plane has one), and `ω ^ r / r!` takes the value `1` on each of them.

The **Wirtinger inequality** says that `ω ^ r / r!` has comass at most one. It follows from the
comass bound `‖ω ^ r‖ ≤ r! ‖ω‖ ^ r` for wedge powers of real two-forms
(`ContinuousAlternatingMap.norm_wedgePow_le`) and the bound `‖ω‖ ≤ 1` on the Kähler form. So
the complex frames are calibrated by `ω ^ r / r!`, and its comass is exactly one whenever
`2r ≤ dim V`; for `2r > dim V` the form vanishes. The normalized powers are natural under
complex-linear isometries, and in particular invariant under the unitary group of `J`.

## Main definitions

* `TauCeti.AlmostComplexStructure.kahlerPowerForm J r`: the normalized Kähler power `ω ^ r / r!`.
* `TauCeti.AlmostComplexStructure.complexRealFrame J u`: the real frame `(u₀, J u₀, u₁, J u₁, …)`.

## Main results

* `TauCeti.AlmostComplexStructure.orthonormal_complexRealFrame_iff`: the frame of `u` is
  orthonormal exactly when `u` is orthonormal for the Hermitian metric of `J`.
* `TauCeti.AlmostComplexStructure.kahlerPowerForm_apply_complexRealFrame`: `ω ^ r / r!` takes the
  value one on the frame of a Hermitian-orthonormal family.
* `TauCeti.AlmostComplexStructure.norm_kahlerPowerForm_le`: the Wirtinger inequality
  `‖ω ^ r / r!‖ ≤ 1`.
* `TauCeti.AlmostComplexStructure.norm_kahlerPowerForm`: `‖ω ^ r / r!‖ = 1` when `2r ≤ dim V`.
* `TauCeti.AlmostComplexStructure.isCalibratedFrame_kahlerPowerForm_complexRealFrame`: the frames
  of Hermitian-orthonormal families are calibrated by `ω ^ r / r!`.
* `TauCeti.AlmostComplexStructure.kahlerPowerForm_compContinuousLinearMap`: naturality under
  complex-linear isometries.

## References

* R. Harvey and H. B. Lawson, *Calibrated geometries*, Acta Math. **148** (1982), 47–157,
  Theorem II.6.11.
* H. Federer, *Geometric Measure Theory*, §1.8.2.
-/

public section

noncomputable section

open Module ContinuousAlternatingMap
open scoped RealInnerProductSpace

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

namespace TauCeti.AlmostComplexStructure

/-! ### Complex frames -/

section ComplexRealFrame

variable (J : AlmostComplexStructure V) {r : ℕ}

/-- The real frame `(u₀, J u₀, u₁, J u₁, …)` of `2r` vectors attached to a family `u` of `r`
vectors. -/
def complexRealFrame (u : Fin r → V) : Fin (2 * r) → V :=
  fun k ↦ (fun p : Fin r × Fin 2 ↦ ![u p.1, J (u p.1)] p.2)
    (finProdFinEquiv.symm (Fin.cast (Nat.mul_comm 2 r) k))

/-- The frame of `u` is the family `(i, 0) ↦ u i`, `(i, 1) ↦ J (u i)` on `Fin r × Fin 2`,
reindexed by `Fin (2 * r)` through `finProdFinEquiv`. -/
theorem complexRealFrame_eq_comp (u : Fin r → V) :
    J.complexRealFrame u = (fun p : Fin r × Fin 2 ↦ ![u p.1, J (u p.1)] p.2) ∘
      (finCongr (Nat.mul_comm 2 r)).trans finProdFinEquiv.symm :=
  (rfl)

/-- The even-indexed vectors of the frame of `u` are the vectors of `u`. -/
@[simp]
theorem complexRealFrame_apply_two_mul (u : Fin r → V) (i : Fin r) :
    J.complexRealFrame u ⟨2 * i, by omega⟩ = u i := by
  have h : finProdFinEquiv.symm (Fin.cast (Nat.mul_comm 2 r) ⟨2 * i, by omega⟩) = (i, 0) := by
    rw [Equiv.symm_apply_eq]
    ext
    simp [mul_comm]
  simp only [complexRealFrame, h, Matrix.cons_val_zero]

/-- The odd-indexed vectors of the frame of `u` are their images under `J`. -/
@[simp]
theorem complexRealFrame_apply_two_mul_add_one (u : Fin r → V) (i : Fin r) :
    J.complexRealFrame u ⟨2 * i + 1, by omega⟩ = J (u i) := by
  have h : finProdFinEquiv.symm (Fin.cast (Nat.mul_comm 2 r) ⟨2 * i + 1, by omega⟩) = (i, 1) := by
    rw [Equiv.symm_apply_eq]
    ext
    simp [mul_comm, add_comm]
  simp only [complexRealFrame, h, Matrix.cons_val_one, Matrix.cons_val_zero]

variable {J} (hJ : ∀ v w, ⟪J v, J w⟫ = ⟪v, w⟫)
include hJ

/-- **Complex frames are orthonormal**: the frame `(u₀, J u₀, u₁, J u₁, …)` is orthonormal exactly
when `u` is orthonormal for the Hermitian metric of `J`, that is, `u` is orthonormal and
`⟪J uᵢ, uⱼ⟫ = 0` for all `i` and `j`. -/
theorem orthonormal_complexRealFrame_iff {u : Fin r → V} :
    Orthonormal ℝ (J.complexRealFrame u) ↔ Orthonormal ℝ u ∧ ∀ i j, ⟪J (u i), u j⟫ = 0 := by
  set b : Fin r × Fin 2 → V := fun p ↦ ![u p.1, J (u p.1)] p.2
  set e : Fin (2 * r) ≃ Fin r × Fin 2 :=
    (finCongr (Nat.mul_comm 2 r)).trans finProdFinEquiv.symm
  have hframe : J.complexRealFrame u = b ∘ e := J.complexRealFrame_eq_comp u
  have hb : Orthonormal ℝ (J.complexRealFrame u) ↔ Orthonormal ℝ b := by
    rw [hframe]
    refine ⟨fun h ↦ ?_, fun h ↦ h.comp e e.injective⟩
    simpa [Function.comp_def] using h.comp e.symm e.symm.injective
  rw [hb, orthonormal_iff_ite, orthonormal_iff_ite]
  constructor
  · intro h
    exact ⟨fun i j ↦ by simpa [b] using h (i, 0) (j, 0),
      fun i j ↦ by simpa [b] using h (i, 1) (j, 0)⟩
  · rintro ⟨hu, hJu⟩ ⟨i, a⟩ ⟨j, c⟩
    fin_cases a <;> fin_cases c
    · simpa [b] using hu i j
    · simpa [b, hJu] using inner_apply_left hJ (u i) (u j)
    · simp [b, hJu]
    · simpa [b, hJ] using hu i j

end ComplexRealFrame

/-! ### Normalized Kähler powers -/

variable [FiniteDimensional ℝ V] (J : AlmostComplexStructure V)

/-- The **normalized Kähler power** `ω ^ r / r!`, the real `2r`-form given by the `r`-th wedge
power of the Kähler form `ω(u, w) = ⟪J u, w⟫` divided by `r!`. -/
def kahlerPowerForm (r : ℕ) : V [⋀^Fin (2 * r)]→L[ℝ] ℝ :=
  (r.factorial : ℝ)⁻¹ • (alternatingFormEquiv V 2 J.kahlerForm).wedgePow r

/-- The normalized Kähler power is the wedge power of the Kähler form divided by `r!`. -/
theorem kahlerPowerForm_def (r : ℕ) :
    J.kahlerPowerForm r =
      (r.factorial : ℝ)⁻¹ • (alternatingFormEquiv V 2 J.kahlerForm).wedgePow r :=
  (rfl)

/-- The zeroth normalized Kähler power is the constant `1`. -/
@[simp]
theorem kahlerPowerForm_zero_apply (v : Fin (2 * 0) → V) : J.kahlerPowerForm 0 v = 1 := by
  simp [kahlerPowerForm_def]

/-- The first normalized Kähler power is the Kähler form. -/
@[simp]
theorem kahlerPowerForm_one : J.kahlerPowerForm 1 = alternatingFormEquiv V 2 J.kahlerForm := by
  ext v
  rw [kahlerPowerForm_def, ContinuousAlternatingMap.smul_apply, wedgePow_succ,
    pairedWedge_apply_zero_left]
  simp

/-- The normalized Kähler powers of degree above the dimension vanish. -/
theorem kahlerPowerForm_eq_zero {r : ℕ} (h : finrank ℝ V < 2 * r) : J.kahlerPowerForm r = 0 :=
  eq_zero_of_finrank_lt _ (by simpa using h)

variable {J} (hJ : ∀ v w, ⟪J v, J w⟫ = ⟪v, w⟫)
include hJ

/-- `ω ^ r / r!` takes the value `1` on the frame `(u₀, J u₀, u₁, J u₁, …)` of a family `u` that
is orthonormal for the Hermitian metric of `J`. -/
theorem kahlerPowerForm_apply_complexRealFrame {r : ℕ} {u : Fin r → V} (hu : Orthonormal ℝ u)
    (hJu : ∀ i j, ⟪J (u i), u j⟫ = 0) : J.kahlerPowerForm r (J.complexRealFrame u) = 1 := by
  have hω (a b : V) : alternatingFormEquiv V 2 J.kahlerForm ![a, b] = ⟪J a, b⟫ := by
    rw [alternatingFormEquiv_apply, inner_kahlerForm_ιMulti hJ]
  have h := wedgePow_apply_finProdFinEquiv (alternatingFormEquiv V 2 J.kahlerForm)
    (fun p : Fin r × Fin 2 ↦ ![u p.1, J (u p.1)] p.2) (fun i j ↦ by simpa [hω] using hJu i j)
    (fun i j ↦ by simpa [hω, hJ] using (orthonormal_iff_ite.1 hu) i j)
  -- `h` evaluates the wedge power on the frame `(u₀, J u₀, …)`.
  have h' : (alternatingFormEquiv V 2 J.kahlerForm).wedgePow r (J.complexRealFrame u) =
      r.factorial := by
    rw [complexRealFrame_eq_comp, Equiv.coe_trans, Function.comp_def]
    exact h
  rw [kahlerPowerForm_def, ContinuousAlternatingMap.smul_apply, smul_eq_mul, h',
    inv_mul_cancel₀ (by positivity)]

/-- The frame `(u₀, J u₀, u₁, J u₁, …)` of a family `u` that is orthonormal for the Hermitian
metric of `J` is calibrated by `ω ^ r / r!`. -/
theorem isCalibratedFrame_kahlerPowerForm_complexRealFrame {r : ℕ} {u : Fin r → V}
    (hu : Orthonormal ℝ u) (hJu : ∀ i j, ⟪J (u i), u j⟫ = 0) :
    (J.kahlerPowerForm r).IsCalibratedFrame (J.complexRealFrame u) :=
  ⟨(orthonormal_complexRealFrame_iff hJ).2 ⟨hu, hJu⟩,
    kahlerPowerForm_apply_complexRealFrame hJ hu hJu⟩

/-- **The Wirtinger inequality**: `ω ^ r / r!` has comass at most one. -/
theorem norm_kahlerPowerForm_le (r : ℕ) : ‖J.kahlerPowerForm r‖ ≤ 1 := by
  have hr : (0 : ℝ) < r.factorial := by positivity
  rw [kahlerPowerForm_def, norm_smul, norm_inv, Real.norm_natCast, inv_mul_le_iff₀ hr, mul_one]
  refine (norm_wedgePow_le _ r).trans ?_
  calc (r.factorial : ℝ) * ‖alternatingFormEquiv V 2 J.kahlerForm‖ ^ r ≤ r.factorial * 1 ^ r := by
        gcongr
        exact norm_alternatingFormEquiv_kahlerForm_le hJ
    _ = r.factorial := by simp

/-- Up to half the dimension, there are families of `r` vectors that are orthonormal for the
Hermitian metric of `J`. -/
theorem exists_orthonormal_forall_inner_apply_eq_zero {r : ℕ} (hr : 2 * r ≤ finrank ℝ V) :
    ∃ u : Fin r → V, Orthonormal ℝ u ∧ ∀ i j, ⟪J (u i), u j⟫ = 0 := by
  obtain ⟨n, hn⟩ := (J.symplecticForm hJ).even_finrank
  obtain ⟨b, hb⟩ := exists_adapted_orthonormalBasis J (norm_apply hJ) n (by omega)
  refine ⟨fun i ↦ b ⟨2 * i, by omega⟩, ?_, fun i j ↦ ?_⟩
  · exact b.orthonormal.comp _ fun i j h ↦ Fin.ext (by simpa using congrArg Fin.val h)
  · rw [← hb ⟨i, by omega⟩]
    exact b.orthonormal.2 (by simp [Fin.ext_iff]; omega)

/-- `ω ^ r / r!` has comass exactly one when `2r` is at most the dimension. -/
theorem norm_kahlerPowerForm {r : ℕ} (hr : 2 * r ≤ finrank ℝ V) : ‖J.kahlerPowerForm r‖ = 1 := by
  obtain ⟨u, hu, hJu⟩ := exists_orthonormal_forall_inner_apply_eq_zero hJ hr
  exact (norm_kahlerPowerForm_le hJ r).antisymm
    (isCalibratedFrame_kahlerPowerForm_complexRealFrame hJ hu hJu).one_le_norm

/-- **Naturality of the normalized Kähler powers**: a complex-linear isometric equivalence pulls
the normalized Kähler powers back to the normalized Kähler powers. In particular they are
invariant under the unitary group of `J`. -/
theorem kahlerPowerForm_compContinuousLinearMap {V' : Type*} [NormedAddCommGroup V']
    [InnerProductSpace ℝ V'] [FiniteDimensional ℝ V'] {J' : AlmostComplexStructure V'}
    {f : V ≃ₗᵢ[ℝ] V'} (hfJ : IsComplexLinearMap J J' f.toLinearMap) (r : ℕ) :
    (J'.kahlerPowerForm r).compContinuousLinearMap f.toLinearIsometry.toContinuousLinearMap =
      J.kahlerPowerForm r := by
  have hω : (alternatingFormEquiv V' 2 J'.kahlerForm).compContinuousLinearMap
      f.toLinearIsometry.toContinuousLinearMap = alternatingFormEquiv V 2 J.kahlerForm := by
    rw [← map_kahlerForm_of_isComplexLinearMap hJ hfJ]
    exact LinearIsometry.alternatingFormEquiv_map f.toLinearIsometry J.kahlerForm
  ext v
  simp only [kahlerPowerForm_def, compContinuousLinearMap_apply,
    ContinuousAlternatingMap.smul_apply, ← hω, ← wedgePow_compContinuousLinearMap]

end TauCeti.AlmostComplexStructure
