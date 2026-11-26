/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.InnerProductSpace.HodgeStar.Kahler.Mass
public import TauCeti.Analysis.InnerProductSpace.Orthonormal.CalibratedFrame
public import TauCeti.Analysis.InnerProductSpace.Orthonormal.Wedge
import TauCeti.Analysis.InnerProductSpace.Orthonormal.Extension
import TauCeti.Geometry.Symplectic.CompatibleMetric
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

Conversely, every frame calibrated by `ω ^ r / r!` is of this kind: it is orthonormal and has the
same wedge `v₀ ∧ ⋯ ∧ v₂ᵣ₋₁` as the frame `(u₀, J u₀, …)` of a Hermitian-orthonormal family `u`,
so it is a positively oriented orthonormal frame of a complex `r`-plane with its complex
orientation, and its span is invariant under `J`. The proof splits off one complex line at a time.
For an orthonormal frame `v` with span `P` and first vector `x`, the projection of `J x` to `P` is
a multiple of a unit vector `y ⊥ x` of `P`; completing `(x, y)` to an orthonormal frame
`(x, y, q)` of `P`, the value of `ω ^ (r + 1) / (r + 1)!` on it is `⟪J x, y⟫` times the value of
`ω ^ r / r!` on `q` (`TauCeti.AlmostComplexStructure.kahlerPowerForm_succ_apply_vecCons`). Both
factors have absolute value at most one, so on a calibrated frame `|⟪J x, y⟫| = 1`, that is
`J x = ±y ∈ P`, and `q` is calibrated up to sign, inside the orthogonal complement of the complex
line `span {x, J x}`.

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
* `TauCeti.AlmostComplexStructure.kahlerPowerForm_succ_apply_vecCons`: splitting off a complex
  line, `(ω ^ (r + 1) / (r + 1)!)(x, y, q) = ⟪J x, y⟫ (ω ^ r / r!)(q)` when `⟪J x, qᵢ⟫ = 0`.
* `TauCeti.AlmostComplexStructure.isCalibratedFrame_kahlerPowerForm_iff`: the frames calibrated by
  `ω ^ r / r!` are the orthonormal frames with the wedge of the frame of a Hermitian-orthonormal
  family.
* `TauCeti.AlmostComplexStructure.apply_mem_span_range_of_isCalibratedFrame_kahlerPowerForm`: the
  span of a calibrated frame is a complex subspace.
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
evaluated at `finProdFinEquiv.symm` of the index cast to `Fin (r * 2)`. -/
theorem complexRealFrame_def (u : Fin r → V) :
    J.complexRealFrame u = fun k ↦ (fun p : Fin r × Fin 2 ↦ ![u p.1, J (u p.1)] p.2)
      (finProdFinEquiv.symm (Fin.cast (Nat.mul_comm 2 r) k)) :=
  (rfl)

/-- The frame of `u` is the family `(i, 0) ↦ u i`, `(i, 1) ↦ J (u i)` on `Fin r × Fin 2`,
reindexed by `Fin (2 * r)` through `finProdFinEquiv`. -/
theorem complexRealFrame_eq_comp (u : Fin r → V) :
    J.complexRealFrame u = (fun p : Fin r × Fin 2 ↦ ![u p.1, J (u p.1)] p.2) ∘
      (finCongr (Nat.mul_comm 2 r)).trans finProdFinEquiv.symm := by
  funext k
  simp [complexRealFrame, finCongr_apply]

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
power of the alternating form of the Kähler two-vector `J.kahlerForm`, divided by `r!`. When `J`
is orthogonal, `ω` is the two-form `ω(u, w) = ⟪J u, w⟫`. -/
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

/-! The frame `(u₀, J u₀, u₁, J u₁, …)` of a family `u` that is orthonormal for the Hermitian
metric of `J` is a symplectic basis for the Kähler form `ω(a, b) = ⟪J a, b⟫`: `ω(uᵢ, uⱼ) = 0`,
`ω(uᵢ, J uⱼ) = δᵢⱼ` and `ω(J uᵢ, J uⱼ) = 0`. -/

/-- The Kähler form vanishes on two vectors of a family `u` with `⟪J uᵢ, uⱼ⟫ = 0`. -/
theorem alternatingFormEquiv_kahlerForm_vecCons_eq_zero {ι : Type*} {u : ι → V}
    (hJu : ∀ i j, ⟪J (u i), u j⟫ = 0) (i j : ι) :
    alternatingFormEquiv V 2 J.kahlerForm ![u i, u j] = 0 := by
  simpa [alternatingFormEquiv_kahlerForm_apply hJ] using hJu i j

/-- The Kähler form pairs an orthonormal family `u` with `J u` by the Kronecker delta. -/
theorem alternatingFormEquiv_kahlerForm_vecCons_apply {ι : Type*} [DecidableEq ι] {u : ι → V}
    (hu : Orthonormal ℝ u) (i j : ι) :
    alternatingFormEquiv V 2 J.kahlerForm ![u i, J (u j)] = if i = j then 1 else 0 := by
  simpa [alternatingFormEquiv_kahlerForm_apply hJ, hJ] using (orthonormal_iff_ite.1 hu) i j

/-- The Kähler form vanishes on the images under `J` of two vectors of a family `u` with
`⟪J uᵢ, uⱼ⟫ = 0`. -/
theorem alternatingFormEquiv_kahlerForm_vecCons_apply_apply_eq_zero {ι : Type*} {u : ι → V}
    (hJu : ∀ i j, ⟪J (u i), u j⟫ = 0) (i j : ι) :
    alternatingFormEquiv V 2 J.kahlerForm ![J (u i), J (u j)] = 0 := by
  simpa [alternatingFormEquiv_kahlerForm_apply hJ, hJ, real_inner_comm] using hJu j i

/-- `ω ^ r / r!` takes the value `1` on the frame `(u₀, J u₀, u₁, J u₁, …)` of a family `u` that
is orthonormal for the Hermitian metric of `J`. -/
theorem kahlerPowerForm_apply_complexRealFrame {r : ℕ} {u : Fin r → V} (hu : Orthonormal ℝ u)
    (hJu : ∀ i j, ⟪J (u i), u j⟫ = 0) : J.kahlerPowerForm r (J.complexRealFrame u) = 1 := by
  -- The frame vectors `b (i, 0)` and `b (i, 1)` reduce to `u i` and `J (u i)`.
  have h := wedgePow_apply_finProdFinEquiv (alternatingFormEquiv V 2 J.kahlerForm)
    (fun p : Fin r × Fin 2 ↦ ![u p.1, J (u p.1)] p.2)
    (alternatingFormEquiv_kahlerForm_vecCons_eq_zero hJ hJu)
    (alternatingFormEquiv_kahlerForm_vecCons_apply hJ hu)
  rw [kahlerPowerForm_def, ContinuousAlternatingMap.smul_apply, smul_eq_mul, complexRealFrame_def,
    h, inv_mul_cancel₀ (by positivity)]

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

/-- `ω ^ r / r!` has comass exactly one when `2r` is at most the dimension. -/
theorem norm_kahlerPowerForm {r : ℕ} (hr : 2 * r ≤ finrank ℝ V) : ‖J.kahlerPowerForm r‖ = 1 := by
  obtain ⟨u, hu, hJu⟩ := exists_orthonormal_forall_inner_apply_eq_zero hJ hr
  exact (norm_kahlerPowerForm_le hJ r).antisymm
    (isCalibratedFrame_kahlerPowerForm_complexRealFrame hJ hu hJu).one_le_norm

/-! ### Calibrated frames of the normalized Kähler powers -/

/-- **Splitting off a complex line.** If `⟪J x, qᵢ⟫ = 0` for every `i`, then the value of
`ω ^ (r + 1) / (r + 1)!` on the frame `(x, y, q₀, q₁, …)` is `⟪J x, y⟫` times the value of
`ω ^ r / r!` on `q`. -/
theorem kahlerPowerForm_succ_apply_vecCons {r : ℕ} {x : V} (y : V) {q : Fin (2 * r) → V}
    (hq : ∀ i, ⟪J x, q i⟫ = 0) :
    J.kahlerPowerForm (r + 1) (Matrix.vecCons x (Matrix.vecCons y q)) =
      ⟪J x, y⟫ * J.kahlerPowerForm r q := by
  have hω (w w' : V) : alternatingFormEquiv V 2 J.kahlerForm ![w, w'] = ⟪J w, w'⟫ := by
    simp [alternatingFormEquiv_kahlerForm_apply hJ]
  rw [kahlerPowerForm_def, kahlerPowerForm_def, ContinuousAlternatingMap.smul_apply,
    ContinuousAlternatingMap.smul_apply, wedgePow_succ_apply_vecCons_vecCons _ _ y
      fun i ↦ (hω _ _).trans (hq i), hω, smul_eq_mul, smul_eq_mul, Nat.factorial_succ]
  push_cast
  field_simp

/-- For an orthonormal frame `v` of `2(r + 1)` vectors, there is a unit vector `y` in the span of
`v`, orthogonal to `x = v 0`, such that `⟪J x, w⟫ = ⟪J x, y⟫ ⟪y, w⟫` for every `w` in the span:
the orthogonal projection of `J x` to the span is a multiple of `y`. -/
private theorem exists_norm_eq_one_inner_apply_eq_mul_inner {r : ℕ} {v : Fin (2 * (r + 1)) → V}
    (hv : Orthonormal ℝ v) :
    ∃ y ∈ Submodule.span ℝ (Set.range v), ‖y‖ = 1 ∧ ⟪v 0, y⟫ = 0 ∧
      ∀ w ∈ Submodule.span ℝ (Set.range v), ⟪J (v 0), w⟫ = ⟪J (v 0), y⟫ * ⟪y, w⟫ := by
  set P := Submodule.span ℝ (Set.range v)
  have hvP (j) : v j ∈ P := Submodule.subset_span ⟨j, rfl⟩
  set z := J (v 0)
  have hz : ⟪v 0, z⟫ = 0 := inner_self_apply hJ (v 0)
  set a := P.starProjection z
  have hza (w) (hw : w ∈ P) : ⟪z, w⟫ = ⟪a, w⟫ := by
    rw [← sub_eq_zero, ← inner_sub_left]
    exact P.starProjection_inner_eq_zero _ _ hw
  by_cases ha : a = 0
  · refine ⟨v 1, hvP 1, hv.1 1, hv.inner_eq_zero (by simp), fun w hw ↦ ?_⟩
    simp [hza w hw, hza _ (hvP 1), ha]
  · have ha' : ‖a‖ ≠ 0 := norm_ne_zero_iff.2 ha
    refine ⟨‖a‖⁻¹ • a, P.smul_mem _ (P.starProjection_apply_mem z), by simp [norm_smul, ha'], ?_,
      fun w hw ↦ ?_⟩
    · rw [real_inner_smul_right, real_inner_comm, ← hza _ (hvP 0), real_inner_comm, hz, mul_zero]
    · rw [hza w hw, hza _ (P.smul_mem _ (P.starProjection_apply_mem z)), real_inner_smul_right,
        real_inner_smul_left, real_inner_self_eq_norm_sq]
      field_simp

/-- **Splitting off a complex line from a calibrated frame.** Let `v` be an orthonormal frame of
`2(r + 1)` vectors on which `ω ^ (r + 1) / (r + 1)!` takes the value `±1`, with span `P`, and let
`x = v 0`. Then `J x ∈ P`, and the orthogonal complement of `span {x, J x}` in `P` has an
orthonormal frame `q` on which `ω ^ r / r!` takes the value `±1`. -/
private theorem exists_orthonormal_abs_kahlerPowerForm_apply_eq_one {r : ℕ}
    {v : Fin (2 * (r + 1)) → V} (hv : Orthonormal ℝ v) (h1 : |J.kahlerPowerForm (r + 1) v| = 1) :
    J (v 0) ∈ Submodule.span ℝ (Set.range v) ∧ ∃ q : Fin (2 * r) → V, Orthonormal ℝ q ∧
      |J.kahlerPowerForm r q| = 1 ∧ ∀ i, q i ∈ Submodule.span ℝ (Set.range v) ∧
        ⟪v 0, q i⟫ = 0 ∧ ⟪J (v 0), q i⟫ = 0 := by
  set P := Submodule.span ℝ (Set.range v)
  have hvP (j) : v j ∈ P := Submodule.subset_span ⟨j, rfl⟩
  -- The projection of `J x` to `P` is a multiple of a unit vector `y ⊥ x`; extend `(x, y)` to an
  -- orthonormal frame `τ = (x, y, q)` of `P`.
  obtain ⟨y, hyP, hy, hxy, hJy⟩ := exists_norm_eq_one_inner_apply_eq_mul_inner hJ hv
  set x := v 0
  have hx : ‖x‖ = 1 := hv.1 0
  have hxy' : Orthonormal ℝ ![x, y] := by
    rw [orthonormal_iff_ite]
    simp [Fin.forall_fin_two, hx, hy, hxy, real_inner_comm x y]
  have h2 : 2 ≤ 2 * (r + 1) := by omega
  obtain ⟨τ, hτ, hspan, hτxy⟩ := hv.exists_orthonormal_span_eq_apply_castLE_eq h2 hxy'
    (Fin.forall_fin_two.2 ⟨hvP 0, hyP⟩)
  set q : Fin (2 * r) → V := fun i ↦ τ i.succ.succ
  have hτq : τ = Matrix.vecCons x (Matrix.vecCons y q) := by
    ext i
    refine Fin.cases ?_ (Fin.cases ?_ fun _ ↦ rfl) i
    · simpa using hτxy 0
    · simpa [show Fin.castLE h2 1 = Fin.succ 0 from Fin.ext rfl] using hτxy 1
  have hq : Orthonormal ℝ q := hτ.comp _ (Fin.succ_injective _ |>.comp (Fin.succ_injective _))
  have hqP (i) : q i ∈ P := hspan.le (Submodule.subset_span ⟨_, rfl⟩)
  have hτ₀ (i) : ⟪x, q i⟫ = 0 ∧ ⟪y, q i⟫ = 0 := by
    simpa [hτq] using And.intro (hτ.inner_eq_zero (Fin.succ_ne_zero (Fin.succ i)).symm)
      (hτ.inner_eq_zero (Fin.succ_injective _ |>.ne (Fin.succ_ne_zero i).symm))
  have hJxq (i) : ⟪J x, q i⟫ = 0 := by rw [hJy _ (hqP i), (hτ₀ i).2, mul_zero]
  -- Compare the values of the form on `v` and on `τ`: `±1 = ⟪J x, y⟫ (ω ^ r / r!)(q)`, where both
  -- factors have absolute value at most one.
  have hval := (J.kahlerPowerForm (r + 1)).toAlternatingMap.map_eq_frameSign_smul_of_mem_span hτ hv
    fun j ↦ hspan.ge (hvP j)
  simp only [coe_toAlternatingMap, hτq, kahlerPowerForm_succ_apply_vecCons hJ y hJxq] at hval
  have habs : |⟪J x, y⟫| * |J.kahlerPowerForm r q| = 1 := by
    rw [← h1, hval, zsmul_eq_mul, abs_mul, abs_mul, ← Int.cast_abs, abs_frameSign, Int.cast_one,
      one_mul]
  have hxy1 : |⟪J x, y⟫| ≤ 1 :=
    (abs_real_inner_le_norm _ _).trans (by rw [norm_apply hJ, hx, hy, one_mul])
  have hq1 : |J.kahlerPowerForm r q| ≤ 1 := by
    simpa using (opNorm_le_iff_le_orthonormal zero_le_one).1 (norm_kahlerPowerForm_le hJ r) q hq
  have hxy_eq : |⟪J x, y⟫| = 1 := by
    nlinarith [abs_nonneg ⟪J x, y⟫, abs_nonneg (J.kahlerPowerForm r q)]
  -- Hence `J x = ±y` lies in `P`.
  have hJx : J x ∈ P := by
    obtain ⟨-, c, -, hc⟩ := (abs_real_inner_div_norm_mul_norm_eq_one_iff y (J x)).1 <| by
      rw [real_inner_comm, hy, norm_apply hJ, hx, mul_one, div_one, hxy_eq]
    exact hc ▸ P.smul_mem c hyP
  refine ⟨hJx, q, hq, ?_, fun i ↦ ⟨hqP i, (hτ₀ i).1, hJxq i⟩⟩
  rwa [hxy_eq, one_mul] at habs

/-- An orthonormal frame `v` of `2r` vectors on which `ω ^ r / r!` takes the value `±1` contains a
family `u` that is orthonormal for the Hermitian metric of `J`, with `u` and `J u` in the span of
`v`. -/
private theorem exists_forall_mem_span_of_abs_kahlerPowerForm_apply_eq_one :
    ∀ (r : ℕ) {v : Fin (2 * r) → V}, Orthonormal ℝ v → |J.kahlerPowerForm r v| = 1 →
      ∃ u : Fin r → V, Orthonormal ℝ u ∧ (∀ i j, ⟪J (u i), u j⟫ = 0) ∧
        ∀ i, u i ∈ Submodule.span ℝ (Set.range v) ∧ J (u i) ∈ Submodule.span ℝ (Set.range v)
  | 0, _, _, _ => ⟨Fin.elim0, ⟨fun i ↦ i.elim0, fun i ↦ i.elim0⟩, fun i ↦ i.elim0, fun i ↦ i.elim0⟩
  | r + 1, v, hv, h1 => by
    obtain ⟨hJx, q, hq, hq1, hqx⟩ := exists_orthonormal_abs_kahlerPowerForm_apply_eq_one hJ hv h1
    obtain ⟨u, hu, hJu, hmem⟩ := exists_forall_mem_span_of_abs_kahlerPowerForm_apply_eq_one r hq hq1
    -- The span of `q` lies in the span of `v` and is orthogonal to `v 0` and `J (v 0)`.
    have hsub : Submodule.span ℝ (Set.range q) ≤ Submodule.span ℝ (Set.range v) ⊓
        LinearMap.ker (innerₛₗ ℝ (v 0)) ⊓ LinearMap.ker (innerₛₗ ℝ (J (v 0))) :=
      Submodule.span_le.2 <| Set.range_subset_iff.2 fun i ↦
        ⟨⟨(hqx i).1, (hqx i).2.1⟩, (hqx i).2.2⟩
    have hu₀ (i) : ⟪v 0, u i⟫ = 0 ∧ ⟪J (v 0), u i⟫ = 0 ∧ ⟪v 0, J (u i)⟫ = 0 ∧
        u i ∈ Submodule.span ℝ (Set.range v) ∧ J (u i) ∈ Submodule.span ℝ (Set.range v) :=
      ⟨(hsub (hmem i).1).1.2, (hsub (hmem i).1).2, (hsub (hmem i).2).1.2, (hsub (hmem i).1).1.1,
        (hsub (hmem i).2).1.1⟩
    refine ⟨Fin.cons (v 0) u, ?_, fun i j ↦ ?_, fun i ↦ ?_⟩
    · rw [orthonormal_iff_ite]
      intro i j
      cases i using Fin.cases with
      | zero => cases j using Fin.cases with
        | zero => simp [hv.1 0]
        | succ j => simp [(hu₀ j).1, (Fin.succ_ne_zero j).symm]
      | succ i => cases j using Fin.cases with
        | zero => simpa [real_inner_comm] using (hu₀ i).1
        | succ j => simp [orthonormal_iff_ite.1 hu]
    · cases i using Fin.cases with
      | zero => cases j using Fin.cases with
        | zero => exact inner_apply_self hJ _
        | succ j => simpa using (hu₀ j).2.1
      | succ i => cases j using Fin.cases with
        | zero => simpa [real_inner_comm] using (hu₀ i).2.2.1
        | succ j => simpa using hJu i j
    · refine Fin.cases ⟨Submodule.subset_span ⟨0, rfl⟩, hJx⟩ (fun i ↦ ?_) i
      simpa using (hu₀ i).2.2.2

/-- **Calibrated frames of the normalized Kähler powers.** A frame `v` of `2r` vectors is
calibrated by `ω ^ r / r!` exactly when it is orthonormal and has the same wedge
`v₀ ∧ ⋯ ∧ v₂ᵣ₋₁` as the frame `(u₀, J u₀, u₁, J u₁, …)` of a family `u` that is orthonormal for
the Hermitian metric of `J`: `v` is a positively oriented orthonormal frame of a complex `r`-plane,
with its complex orientation. -/
theorem isCalibratedFrame_kahlerPowerForm_iff {r : ℕ} {v : Fin (2 * r) → V} :
    (J.kahlerPowerForm r).IsCalibratedFrame v ↔ Orthonormal ℝ v ∧
      ∃ u : Fin r → V, Orthonormal ℝ u ∧ (∀ i j, ⟪J (u i), u j⟫ = 0) ∧
        exteriorPower.ιMulti ℝ (2 * r) v =
          exteriorPower.ιMulti ℝ (2 * r) (J.complexRealFrame u) := by
  refine ⟨fun h ↦ ⟨h.orthonormal, ?_⟩, fun ⟨hv, u, hu, hJu, h⟩ ↦
    (isCalibratedFrame_kahlerPowerForm_complexRealFrame hJ hu hJu).of_ιMulti_eq hv h⟩
  obtain ⟨u, hu, hJu, hmem⟩ := exists_forall_mem_span_of_abs_kahlerPowerForm_apply_eq_one hJ r
    h.orthonormal (by rw [h.apply_eq_one, abs_one])
  have hw := (orthonormal_complexRealFrame_iff hJ).2 ⟨hu, hJu⟩
  -- The frame of `u` is an orthonormal frame of the span of `v`, so the two frames differ by a
  -- sign, which is `1` since the form takes the value `1` on both.
  have hspan (k) : J.complexRealFrame u k ∈ Submodule.span ℝ (Set.range v) := by
    simp only [complexRealFrame_def]
    obtain ⟨i, j⟩ := finProdFinEquiv.symm (Fin.cast (Nat.mul_comm 2 r) k)
    fin_cases j
    exacts [(hmem i).1, (hmem i).2]
  have hs := (J.kahlerPowerForm r).toAlternatingMap.map_eq_frameSign_smul_of_mem_span
    h.orthonormal hw hspan
  rw [coe_toAlternatingMap, kahlerPowerForm_apply_complexRealFrame hJ hu hJu, h.apply_eq_one,
    zsmul_eq_mul, mul_one, eq_comm, Int.cast_eq_one] at hs
  refine ⟨u, hu, hJu, ?_⟩
  rw [(exteriorPower.ιMulti ℝ (2 * r)).map_eq_frameSign_smul_of_mem_span h.orthonormal hw hspan,
    hs, one_smul]

/-- The span of a frame calibrated by `ω ^ r / r!` is invariant under `J`: it is a complex
`r`-plane. -/
theorem apply_mem_span_range_of_isCalibratedFrame_kahlerPowerForm {r : ℕ} {v : Fin (2 * r) → V}
    (h : (J.kahlerPowerForm r).IsCalibratedFrame v) (i : Fin (2 * r)) :
    J (v i) ∈ Submodule.span ℝ (Set.range v) := by
  obtain ⟨hv, u, hu, hJu, hvu⟩ := (isCalibratedFrame_kahlerPowerForm_iff hJ).1 h
  have hw := (orthonormal_complexRealFrame_iff hJ).2 ⟨hu, hJu⟩
  -- Frames with the same wedge are orthogonal changes of each other, so they span the same plane.
  obtain ⟨A, -, hA⟩ := (hw.ιMulti_eq_ιMulti_iff hv).1 hvu
  obtain ⟨B, -, hB⟩ := (hv.ιMulti_eq_ιMulti_iff hw).1 hvu.symm
  have hmem (k) : J.complexRealFrame u k ∈ Submodule.span ℝ (Set.range v) := by
    rw [hB]
    exact Submodule.sum_mem _ fun l _ ↦ Submodule.smul_mem _ _ (Submodule.subset_span ⟨l, rfl⟩)
  have hJmem (l : Fin r) : J (u l) ∈ Submodule.span ℝ (Set.range v) ∧
      J (J (u l)) ∈ Submodule.span ℝ (Set.range v) :=
    ⟨by simpa using hmem ⟨2 * l + 1, by omega⟩,
      by simpa [J.apply_apply] using neg_mem (hmem ⟨2 * l, by omega⟩)⟩
  simp only [congrFun hA i, _root_.map_sum, _root_.map_smul]
  refine Submodule.sum_mem _ fun k _ ↦ Submodule.smul_mem _ _ ?_
  simp only [complexRealFrame_def]
  obtain ⟨l, j⟩ := finProdFinEquiv.symm (Fin.cast (Nat.mul_comm 2 r) k)
  fin_cases j
  exacts [(hJmem l).1, (hJmem l).2]

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
