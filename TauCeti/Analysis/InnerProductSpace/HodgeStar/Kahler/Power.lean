/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.InnerProductSpace.HodgeStar.Kahler.Mass
public import TauCeti.Analysis.InnerProductSpace.Orthonormal.CalibratedFrame
public import TauCeti.Analysis.InnerProductSpace.Orthonormal.Wedge
import TauCeti.Algebra.BigOperators.Ring.SquareZero
import TauCeti.Analysis.InnerProductSpace.Orthonormal.Extension
import TauCeti.Analysis.Normed.Module.Alternating.Bilinear
import TauCeti.Data.Fin.StrictMono
import TauCeti.Geometry.Symplectic.CompatibleMetric
import TauCeti.Geometry.Symplectic.Finrank
import TauCeti.LinearAlgebra.ExteriorPower.Basis
import TauCeti.Topology.Algebra.Module.Alternating.TopDegree

/-!
# Normalized powers of the Kähler form and the Wirtinger inequality

Let `J` be an almost complex structure on a finite-dimensional real inner product space `V`, and let
`ω := alternatingFormEquiv V 2 J.kahlerForm` be the alternating two-form corresponding to the
Kähler two-vector `TauCeti.AlmostComplexStructure.kahlerForm J`. For general `J` (not necessarily
orthogonal), `ω` has skew-symmetrized evaluation `ω(u, w) = (⟪J u, w⟫ - ⟪J w, u⟫) / 2`, which
reduces to `ω(u, w) = ⟪J u, w⟫` when `J` is orthogonal. The **normalized Kähler power**
`TauCeti.AlmostComplexStructure.kahlerPowerForm J r` is the real `2r`-form `ω ^ r / r!`, for the
wedge powers `ContinuousAlternatingMap.wedgePow` in the determinant normalization; via
`TauCeti.alternatingFormEquiv_pow`, it equals `(r!)⁻¹ • alternatingFormEquiv V (2 * r)
(exteriorPower.pow J.kahlerForm r)`. Specializing `J` to multiplication by `i`
(`AlmostComplexStructure.ofComplexModule E`) defines `TauCeti.kahlerPowerForm E r` on any
finite-dimensional Hermitian vector space `E`, where `ω = TauCeti.kahlerTwoForm E` evaluates as
`Im ⟪u, w⟫_ℂ = ⟪i • u, w⟫_ℝ` (`TauCeti.kahlerPowerForm_eq_wedgePow`).

For a family `u` of `r` vectors, `TauCeti.AlmostComplexStructure.complexRealFrame J u` is the real
frame `(u₀, J u₀, u₁, J u₁, …)`. When `J` is orthogonal, it is orthonormal exactly when `u` is
orthonormal for the Hermitian metric of `J`: `u` is orthonormal and `⟪J uᵢ, uⱼ⟫ = 0` for all `i`
and `j`. Such frames are positively oriented orthonormal frames of complex `r`-planes with their
complex orientation (every complex `r`-plane has one), and `ω ^ r / r!` takes the value `1` on each
of them.

The **Wirtinger inequality** says that for an orthogonal `J`, `ω ^ r / r!` has comass at most one.
It follows from the comass bound `‖ω ^ r‖ ≤ r! ‖ω‖ ^ r` for wedge powers of real two-forms
(`ContinuousAlternatingMap.norm_wedgePow_le`) and the bound `‖ω‖ ≤ 1` on the Kähler form. So
the complex frames are calibrated by `ω ^ r / r!`, and its comass is exactly one whenever
`2r ≤ dim V`; for `2r > dim V` the form vanishes. Its Hilbert norm is `√(dim V / 2 choose r)`.
The normalized powers are natural under complex-linear isometries, and in particular invariant under
the unitary group of `J`.

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

* `TauCeti.AlmostComplexStructure.kahlerPowerForm J r`: the normalized Kähler power `ω ^ r / r!`,
  where `ω := alternatingFormEquiv V 2 J.kahlerForm` evaluates as `(⟪J u, w⟫ - ⟪J w, u⟫) / 2`.
* `TauCeti.AlmostComplexStructure.complexRealFrame J u`: the real frame `(u₀, J u₀, u₁, J u₁, …)`.
* `TauCeti.kahlerPowerForm E r`: the normalized `r`-th Kähler power `(kahlerTwoForm E) ^ r / r!`
  on a finite-dimensional Hermitian vector space (`TauCeti.kahlerPowerForm_eq_wedgePow`).

## Main results

* `TauCeti.AlmostComplexStructure.orthonormal_complexRealFrame_iff`: the frame of `u` is
  orthonormal exactly when `u` is orthonormal for the Hermitian metric of `J`.
* `TauCeti.AlmostComplexStructure.kahlerPowerForm_apply_complexRealFrame` and
  `TauCeti.AlmostComplexStructure.kahlerPowerForm_apply_of_adapted`: `ω ^ r / r!` takes the value
  one on complex / adapted orthonormal frames.
* `TauCeti.AlmostComplexStructure.eq_smul_kahlerPowerForm`: on a space of dimension `2r`, a form
  of top degree is its value on such a frame times `ω ^ r / r!`.
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
* `AlmostComplexStructure.exists_basis_orientation_eq_and_isCalibratedFrame_kahlerPowerForm`:
  a complex-linear injection from a space of dimension `2r` carries some basis positive for the
  complex orientation to a frame calibrated by `ω ^ r / r!`.
* `TauCeti.AlmostComplexStructure.kahlerPowerForm_compContinuousLinearMap_eq`,
  `TauCeti.AlmostComplexStructure.kahlerPowerForm_comp_linearIsometry`, and
  `TauCeti.AlmostComplexStructure.kahlerPowerForm_compContinuousLinearMap`:
  pullback and naturality under complex-linear isometries.
* `TauCeti.AlmostComplexStructure.sqrt_alternatingFormInner_kahlerPowerForm` and
  `TauCeti.sqrt_alternatingFormInner_kahlerPowerForm`: Hilbert norm `√(n choose r)`.

## References

* R. Harvey and H. B. Lawson, *Calibrated geometries*, Acta Math. **148** (1982), 47–157,
  Theorem II.6.11.
* H. Federer, *Geometric Measure Theory*, §1.8.2.
-/

public section

noncomputable section

open Module ContinuousAlternatingMap
open exteriorPower (ιMulti)
open scoped InnerProductSpace RealInnerProductSpace

namespace TauCeti.AlmostComplexStructure

/-! ### Complex frames -/

section ComplexRealFrame

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
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

/-- The frame of `u` lies in a submodule containing every `u i` and every `J (u i)`. -/
theorem complexRealFrame_apply_mem {S : Submodule ℝ V} {u : Fin r → V}
    (h : ∀ i, u i ∈ S ∧ J (u i) ∈ S) (k : Fin (2 * r)) : J.complexRealFrame u k ∈ S := by
  simp only [complexRealFrame_def]
  obtain ⟨i, j⟩ := finProdFinEquiv.symm (Fin.cast (Nat.mul_comm 2 r) k)
  fin_cases j
  exacts [(h i).1, (h i).2]

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

section KahlerPower

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]

/-- The **normalized Kähler power** `ω ^ r / r!`, the real `2r`-form given by the `r`-th wedge
power of `ω := alternatingFormEquiv V 2 J.kahlerForm`, divided by `r!`. For an arbitrary almost
complex structure `J`, `ω` has skew-symmetrized evaluation
`ω(u, w) = (⟪J u, w⟫ - ⟪J w, u⟫) / 2`, reducing to `ω(u, w) = ⟪J u, w⟫` when `J` is orthogonal. -/
def kahlerPowerForm (J : AlmostComplexStructure V) (r : ℕ) : V [⋀^Fin (2 * r)]→L[ℝ] ℝ :=
  (r.factorial : ℝ)⁻¹ • (alternatingFormEquiv V 2 J.kahlerForm).wedgePow r

/-- The normalized Kähler power is the wedge power of the Kähler form divided by `r!`. -/
theorem kahlerPowerForm_def (J : AlmostComplexStructure V) (r : ℕ) :
    J.kahlerPowerForm r =
      (r.factorial : ℝ)⁻¹ • (alternatingFormEquiv V 2 J.kahlerForm).wedgePow r :=
  (rfl)

/-- The normalized Kähler power in terms of `exteriorPower.pow`. -/
theorem kahlerPowerForm_eq_alternatingFormEquiv_pow (J : AlmostComplexStructure V) (r : ℕ) :
    J.kahlerPowerForm r =
      (r.factorial : ℝ)⁻¹ • alternatingFormEquiv V (2 * r) (exteriorPower.pow J.kahlerForm r) := by
  rw [kahlerPowerForm_def, alternatingFormEquiv_pow]

/-- Evaluation formula for `AlmostComplexStructure.kahlerPowerForm` on an arbitrary `2r`-frame. -/
theorem kahlerPowerForm_apply (J : AlmostComplexStructure V) (r : ℕ) (v : Fin (2 * r) → V) :
    J.kahlerPowerForm r v =
      ⟪(r.factorial : ℝ)⁻¹ • exteriorPower.pow J.kahlerForm r, ιMulti ℝ (2 * r) v⟫ := by
  rw [kahlerPowerForm_eq_alternatingFormEquiv_pow, ContinuousAlternatingMap.smul_apply,
    alternatingFormEquiv_apply, real_inner_smul_left, smul_eq_mul]

/-- Under the Riesz identification `alternatingFormEquiv`, the normalized Kähler power
`J.kahlerPowerForm r` corresponds to `(r!)⁻¹ • exteriorPower.pow J.kahlerForm r`. -/
@[simp]
theorem alternatingFormEquiv_symm_kahlerPowerForm (J : AlmostComplexStructure V) (r : ℕ) :
    (alternatingFormEquiv V (2 * r)).symm (J.kahlerPowerForm r) =
      (r.factorial : ℝ)⁻¹ • exteriorPower.pow J.kahlerForm r := by
  rw [kahlerPowerForm_eq_alternatingFormEquiv_pow, map_smul, LinearEquiv.symm_apply_apply]

/-- The zeroth normalized Kähler power is the constant `1`. -/
@[simp]
theorem kahlerPowerForm_zero_apply (J : AlmostComplexStructure V) (v : Fin (2 * 0) → V) :
    J.kahlerPowerForm 0 v = 1 := by
  simp [kahlerPowerForm_def]

/-- For power index `r = 0` (form degree `0`), `ω⁰ / 0!` is the constant form `1`. -/
theorem kahlerPowerForm_zero (J : AlmostComplexStructure V) :
    J.kahlerPowerForm 0 = ContinuousAlternatingMap.constOfIsEmpty ℝ V (Fin 0) 1 := by
  ext v
  exact J.kahlerPowerForm_zero_apply v

/-- The first normalized Kähler power is the Kähler form. -/
@[simp]
theorem kahlerPowerForm_one (J : AlmostComplexStructure V) :
    J.kahlerPowerForm 1 = alternatingFormEquiv V 2 J.kahlerForm := by
  ext v
  rw [kahlerPowerForm_def, ContinuousAlternatingMap.smul_apply, wedgePow_succ,
    pairedWedge_apply_zero_left]
  simp

/-- Wedge recurrence for normalized Kähler powers:
`ω^(r+1) / (r+1)! = (r + 1)⁻¹ • (ωʳ / r!) ∧ ω`. -/
theorem kahlerPowerForm_succ (J : AlmostComplexStructure V) (r : ℕ) :
    J.kahlerPowerForm (r + 1) =
      ((r + 1 : ℕ) : ℝ)⁻¹ •
        (J.kahlerPowerForm r).wedge (alternatingFormEquiv V 2 J.kahlerForm) := by
  rw [kahlerPowerForm_def, ContinuousAlternatingMap.wedgePow_succ,
    ← ContinuousAlternatingMap.wedge_def, kahlerPowerForm_def,
    ContinuousAlternatingMap.wedge_smul_left, smul_smul, Nat.factorial_succ, Nat.cast_mul,
    mul_inv]

/-- The normalized Kähler powers of degree above the dimension vanish. -/
theorem kahlerPowerForm_eq_zero (J : AlmostComplexStructure V) {r : ℕ} (h : finrank ℝ V < 2 * r) :
    J.kahlerPowerForm r = 0 :=
  eq_zero_of_finrank_lt _ (by simpa using h)

/-- Pullback of `J.kahlerPowerForm r` along a continuous linear map `L : W →L[ℝ] V` when the
degree-two form pulls back to `alternatingFormEquiv W 2 B`. -/
theorem kahlerPowerForm_compContinuousLinearMap_eq {W : Type*} [NormedAddCommGroup W]
    [InnerProductSpace ℝ W] [FiniteDimensional ℝ W] (J : AlmostComplexStructure V)
    (L : W →L[ℝ] V) (B : ⋀[ℝ]^2 W)
    (h2 : (alternatingFormEquiv V 2 J.kahlerForm).compContinuousLinearMap L =
      alternatingFormEquiv W 2 B) (r : ℕ) :
    (J.kahlerPowerForm r).compContinuousLinearMap L =
      (r.factorial : ℝ)⁻¹ • alternatingFormEquiv W (2 * r) (exteriorPower.pow B r) := by
  rw [kahlerPowerForm_def, ← ContinuousAlternatingMap.compContinuousLinearMapₗ_apply,
    map_smul, ContinuousAlternatingMap.compContinuousLinearMapₗ_apply,
    ContinuousAlternatingMap.wedgePow_compContinuousLinearMap, h2, ← alternatingFormEquiv_pow]

/-- Naturality of `kahlerPowerForm` under complex-linear isometric embeddings between
finite-dimensional real inner product spaces with almost complex structures. -/
theorem kahlerPowerForm_comp_linearIsometry {W : Type*} [NormedAddCommGroup W]
    [InnerProductSpace ℝ W] [FiniteDimensional ℝ W]
    {J : AlmostComplexStructure V} {J' : AlmostComplexStructure W}
    (f : V →ₗᵢ[ℝ] W) (hf : IsComplexLinearMap J J' f.toLinearMap) (r : ℕ) :
    (J'.kahlerPowerForm r).compContinuousLinearMap f.toContinuousLinearMap =
      J.kahlerPowerForm r := by
  have hf' (v : V) : f (J v) = J' (f v) := LinearMap.congr_fun hf v
  have h2 : (alternatingFormEquiv W 2 J'.kahlerForm).compContinuousLinearMap
      f.toContinuousLinearMap = alternatingFormEquiv V 2 J.kahlerForm := by
    ext v
    rw [show v = ![v 0, v 1] from (FinVec.etaExpand_eq v).symm,
      ContinuousAlternatingMap.compContinuousLinearMap_apply_vecCons_two,
      alternatingFormEquiv_apply, inner_kahlerForm_ιMulti_eq_inv_two_mul_sub,
      LinearIsometry.coe_toContinuousLinearMap, ← hf', ← hf',
      f.inner_map_map, f.inner_map_map, ← inner_kahlerForm_ιMulti_eq_inv_two_mul_sub,
      ← alternatingFormEquiv_apply]
  rw [kahlerPowerForm_compContinuousLinearMap_eq J' f.toContinuousLinearMap J.kahlerForm h2 r,
    kahlerPowerForm_eq_alternatingFormEquiv_pow]

/-- The normalized Kähler power `ωʳ / r!` evaluates to `1` on every `J`-adapted orthonormal
`2r`-frame `(w₀, J w₀, …, w_{2r-2}, J w_{2r-2})`, without requiring `J` to be orthogonal outside
the span of `w`. -/
theorem kahlerPowerForm_apply_of_adapted {J : AlmostComplexStructure V}
    {r : ℕ} {w : Fin (2 * r) → V} (hw : Orthonormal ℝ w)
    (hadapt : ∀ j : Fin r, w ⟨2 * (j : ℕ) + 1, by omega⟩ = J (w ⟨2 * (j : ℕ), by omega⟩)) :
    J.kahlerPowerForm r w = 1 := by
  let ω := alternatingFormEquiv V 2 J.kahlerForm
  let b : Fin r × Fin 2 → V := w ∘ complexRealIndexEquiv r
  have hb0 (i : Fin r) : b (i, 0) = w ⟨2 * (i : ℕ), by omega⟩ := by
    simp [b, complexRealIndexEquiv_zero]
  have hb1 (i : Fin r) : b (i, 1) = w ⟨2 * (i : ℕ) + 1, by omega⟩ := by
    simp [b, complexRealIndexEquiv_one]
  have h00 (i j : Fin r) : ω ![b (i, 0), b (j, 0)] = 0 := by
    rw [hb0, hb0, alternatingFormEquiv_apply, inner_kahlerForm_ιMulti_eq_inv_two_mul_sub,
      ← hadapt i, ← hadapt j, hw.2 (Fin.ne_of_val_ne (by dsimp; omega)),
      hw.2 (Fin.ne_of_val_ne (by dsimp; omega)), sub_self, mul_zero]
  have h01 (i j : Fin r) : ω ![b (i, 0), b (j, 1)] = if i = j then 1 else 0 := by
    rw [hb0, hb1, alternatingFormEquiv_apply, inner_kahlerForm_ιMulti_eq_inv_two_mul_sub,
      ← hadapt i]
    conv_lhs => rhs; rhs; rw [hadapt j, J.apply_apply, inner_neg_left]
    rw [sub_neg_eq_add]
    rcases eq_or_ne i j with rfl | hij
    · simp only [↓reduceIte, real_inner_self_eq_norm_sq, hw.1]
      ring
    · simp only [hij, ↓reduceIte]
      rw [hw.2 (Fin.ne_of_val_ne (by dsimp; omega)),
        hw.2 (Fin.ne_of_val_ne (by dsimp; omega))]
      ring
  have hw_eq : (fun t ↦ b (finProdFinEquiv.symm (Fin.cast (Nat.mul_comm 2 r) t))) = w := by
    ext t
    refine congrArg w (Fin.ext ?_)
    simp [complexRealIndexEquiv_apply_val, Nat.div_add_mod]
  have hpow := ContinuousAlternatingMap.wedgePow_apply_finProdFinEquiv ω b h00 h01
  rw [hw_eq] at hpow
  rw [kahlerPowerForm_def, ContinuousAlternatingMap.smul_apply, smul_eq_mul, hpow,
    inv_mul_cancel₀ (Nat.cast_ne_zero (R := ℝ).mpr (Nat.factorial_ne_zero r))]

section Orthogonal

variable {J : AlmostComplexStructure V} (hJ : ∀ v w, ⟪J v, J w⟫ = ⟪v, w⟫)
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

/-- `ω ^ r` takes the value `r!` on the frame `(u₀, J u₀, u₁, J u₁, …)` of a family `u` that is
orthonormal for the Hermitian metric of `J`. -/
theorem wedgePow_kahlerForm_apply_complexRealFrame {r : ℕ} {u : Fin r → V}
    (hu : Orthonormal ℝ u) (hJu : ∀ i j, ⟪J (u i), u j⟫ = 0) :
    (alternatingFormEquiv V 2 J.kahlerForm).wedgePow r (J.complexRealFrame u) = r.factorial := by
  -- The frame vectors `b (i, 0)` and `b (i, 1)` reduce to `u i` and `J (u i)`.
  rw [complexRealFrame_def]
  exact wedgePow_apply_finProdFinEquiv (alternatingFormEquiv V 2 J.kahlerForm)
    (fun p : Fin r × Fin 2 ↦ ![u p.1, J (u p.1)] p.2)
    (alternatingFormEquiv_kahlerForm_vecCons_eq_zero hJ hJu)
    (alternatingFormEquiv_kahlerForm_vecCons_apply hJ hu)

/-- `ω ^ r / r!` takes the value `1` on the frame `(u₀, J u₀, u₁, J u₁, …)` of a family `u` that
is orthonormal for the Hermitian metric of `J`. -/
theorem kahlerPowerForm_apply_complexRealFrame {r : ℕ} {u : Fin r → V} (hu : Orthonormal ℝ u)
    (hJu : ∀ i j, ⟪J (u i), u j⟫ = 0) : J.kahlerPowerForm r (J.complexRealFrame u) = 1 := by
  rw [kahlerPowerForm_def, ContinuousAlternatingMap.smul_apply, smul_eq_mul,
    wedgePow_kahlerForm_apply_complexRealFrame hJ hu hJu, inv_mul_cancel₀ (by positivity)]

/-- On a space of dimension `2r`, a form `φ` of top degree is `φ(u₀, J u₀, …) ω ^ r / r!` for the
frame of any family `u` of `r` vectors that is orthonormal for the Hermitian metric of `J`. -/
theorem eq_smul_kahlerPowerForm {r : ℕ} (hr : finrank ℝ V = 2 * r) {u : Fin r → V}
    (hu : Orthonormal ℝ u) (hJu : ∀ i j, ⟪J (u i), u j⟫ = 0) (φ : V [⋀^Fin (2 * r)]→L[ℝ] ℝ) :
    φ = φ (J.complexRealFrame u) • J.kahlerPowerForm r := by
  -- Both sides are forms of top degree, compared on the orthonormal basis given by the frame.
  let B : Basis (Fin (2 * r)) ℝ V := basisOfLinearIndependentOfCardEqFinrank' _
    ((orthonormal_complexRealFrame_iff hJ).2 ⟨hu, hJu⟩).linearIndependent (by simp [hr])
  have hB : (B : Fin (2 * r) → V) = J.complexRealFrame u :=
    coe_basisOfLinearIndependentOfCardEqFinrank' _ _ _
  ext v
  rw [ContinuousAlternatingMap.smul_apply, apply_eq_det_mul φ B v,
    apply_eq_det_mul (J.kahlerPowerForm r) B v, hB,
    kahlerPowerForm_apply_complexRealFrame hJ hu hJu, smul_eq_mul]
  ring

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
  have hspan := J.complexRealFrame_apply_mem hmem
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
  exact Submodule.sum_mem _ fun k _ ↦ Submodule.smul_mem _ _
    (J.complexRealFrame_apply_mem (S := (Submodule.span ℝ (Set.range v)).comap J.toLinearMap)
      hJmem k)

/-- **Complex subspaces carry calibrated frames.** Let `L` be an injective linear map, from a real
vector space `U` of dimension `2r` with an almost complex structure `j`, intertwining `j` with `J`.
Some basis of `U` that is positive for the complex orientation of `j` is carried by `L` to a frame
calibrated by `ω ^ r / r!`. -/
theorem exists_basis_orientation_eq_and_isCalibratedFrame_kahlerPowerForm {U : Type*}
    [AddCommGroup U] [Module ℝ U] [FiniteDimensional ℝ U] (j : AlmostComplexStructure U) {r : ℕ}
    (hr : finrank ℝ U = 2 * r) {L : U →ₗ[ℝ] V} (hL : Function.Injective L)
    (hLj : ∀ u, L (j u) = J (L u)) :
    ∃ b : Basis (Fin (2 * r)) ℝ U, b.orientation = j.orientation hr ∧
      (J.kahlerPowerForm r).IsCalibratedFrame (L ∘ b) := by
  -- The image `S` of `L` is a `J`-invariant subspace of dimension `2r`; choose a family `w` in
  -- it that is orthonormal for the Hermitian metric of `J`, and pull it back to `U`.
  set S := LinearMap.range L
  have hS : ∀ x ∈ S, J x ∈ S := by
    rintro _ ⟨u, rfl⟩
    exact ⟨j u, hLj u⟩
  have hJS (v w : S) : ⟪J.restrict S hS v, J.restrict S hS w⟫ = ⟪v, w⟫ := by
    simpa only [Submodule.coe_inner, coe_restrict_apply] using hJ v w
  obtain ⟨w, hw, hJw⟩ := exists_orthonormal_forall_inner_apply_eq_zero hJS
    ((LinearMap.finrank_range_of_inj hL).trans hr).ge
  set e := LinearEquiv.ofInjective L hL
  set u : Fin r → U := fun i ↦ e.symm (w i)
  have hLu (i : Fin r) : L (u i) = w i := congrArg Subtype.val (e.apply_symm_apply (w i))
  -- The frame `(u₀, j u₀, u₁, j u₁, …)` of `U` is carried to the frame of `w`.
  set ε : Fin (2 * r) ≃ Fin r × Fin 2 := (finCongr (Nat.mul_comm 2 r)).trans finProdFinEquiv.symm
  set c : Fin (2 * r) → U := (fun p : Fin r × Fin 2 ↦ ![u p.1, j (u p.1)] p.2) ∘ ε
  have hframe : L ∘ c = J.complexRealFrame fun i ↦ (w i : V) := by
    rw [complexRealFrame_eq_comp]
    funext k
    simp only [Function.comp_apply, c]
    generalize ε k = p
    obtain ⟨i, a⟩ := p
    fin_cases a <;> simp [hLu, hLj]
  have hcal : (J.kahlerPowerForm r).IsCalibratedFrame (J.complexRealFrame fun i ↦ (w i : V)) :=
    isCalibratedFrame_kahlerPowerForm_complexRealFrame hJ (hw.comp_linearIsometry S.subtypeₗᵢ)
      fun i i' ↦ by simpa only [Submodule.coe_inner, coe_restrict_apply] using hJw i i'
  -- This frame is a basis of `U`, positive since it is adapted to `j`.
  have hli : LinearIndependent ℝ c :=
    LinearIndependent.of_comp L (hframe ▸ hcal.orthonormal.linearIndependent)
  set b := basisOfLinearIndependentOfCardEqFinrank' _ hli (by simp [hr])
  have hb : ⇑b = c := coe_basisOfLinearIndependentOfCardEqFinrank' _ _ _
  refine ⟨b, ?_, by rwa [hb, hframe]⟩
  have hB (i : Fin r) : b.reindex ε (i, 1) = j (b.reindex ε (i, 0)) := by
    simp [hb, c]
  have hb' : (b.reindex ε).reindex (finProdFinEquiv.trans (finCongr (Nat.mul_comm r 2))) = b :=
    Basis.eq_of_apply_eq fun k ↦ by
      simp only [Basis.reindex_apply]
      congr 1
      ext
      simp [ε]
      omega
  rw [← j.orientation_reindex hB hr (Nat.mul_comm r 2), hb']

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

end Orthogonal

private theorem kahlerPowerForm_symm_eq_sum_adapted {J : AlmostComplexStructure V} {n : ℕ}
    (b : OrthonormalBasis (Fin (2 * n)) ℝ V)
    (hb : ∀ j : Fin n, b ⟨2 * (j : ℕ) + 1, by omega⟩ = J (b ⟨2 * (j : ℕ), by omega⟩)) (r : ℕ) :
    (alternatingFormEquiv V (2 * r)).symm (J.kahlerPowerForm r) =
      ∑ s : Set.powersetCard (Fin n) r, b.exteriorPower (2 * r)
        (Set.powersetCard.ofFinEmbEquiv
          (doubleOrderEmb (Set.powersetCard.ofFinEmbEquiv.symm s))) := by
  let x : Fin n → _root_.ExteriorAlgebra ℝ V := fun k ↦
    (1 : ℝ) • _root_.ExteriorAlgebra.ιMulti ℝ 2
      ![b ⟨2 * (k : ℕ), by omega⟩, b ⟨2 * (k : ℕ) + 1, by omega⟩]
  have hcoe : (J.kahlerForm : _root_.ExteriorAlgebra ℝ V) = ∑ k : Fin n, x k := by
    rw [kahlerForm_eq_sum_of_adapted b hb]
    simp [x]
  have hcomm : Pairwise (Function.onFun Commute x) := fun _ _ _ ↦
    TauCeti.ExteriorAlgebra.commute_smul_ιMulti_two (1 : ℝ) 1
      (b ⟨2 * _, _⟩) (b ⟨2 * _ + 1, _⟩) (b ⟨2 * _, _⟩) (b ⟨2 * _ + 1, _⟩)
  have hsq : ∀ k ∈ (Finset.univ : Finset (Fin n)), x k * x k = 0 := fun k _ ↦
    TauCeti.ExteriorAlgebra.smul_ιMulti_two_mul_self (1 : ℝ)
      (b ⟨2 * (k : ℕ), by omega⟩) (b ⟨2 * (k : ℕ) + 1, by omega⟩)
  rw [alternatingFormEquiv_symm_kahlerPowerForm]
  apply Subtype.ext
  rw [SetLike.val_smul, Submodule.coe_sum, exteriorPower.coe_pow]
  rw [hcoe, Finset.sum_pow_of_pairwise_commute_of_mul_self_eq_zero Finset.univ x hcomm hsq r,
    ← Nat.cast_smul_eq_nsmul ℝ, smul_smul,
    inv_mul_cancel₀ (Nat.cast_ne_zero (R := ℝ).mpr (Nat.factorial_ne_zero r)), one_smul,
    ← Finset.sum_coe_sort ((Finset.univ : Finset (Fin n)).powersetCard r)]
  refine Fintype.sum_equiv (Set.equivOfEq (Set.powersetCard.coe_finset (Fin n) r).symm) _ _
    fun s ↦ ?_
  have hs : s.val = ((Set.equivOfEq (Set.powersetCard.coe_finset (Fin n) r).symm s :
      Set.powersetCard (Fin n) r) : Finset (Fin n)) := rfl
  rw [Finset.noncommProd_congr hs (fun _ _ ↦ rfl)]
  rw [← OrthonormalBasis.coe_toBasis (b.exteriorPower (2 * r)),
    OrthonormalBasis.toBasis_exteriorPower, exteriorPower.basis_apply,
    exteriorPower.ιMulti_family, exteriorPower.ιMulti_apply_coe, Equiv.symm_apply_apply]
  simpa only [x, Finset.prod_const_one, one_smul, OrthonormalBasis.coe_toBasis] using
    TauCeti.ExteriorAlgebra.noncommProd_powersetCard_smul_ιMulti_two (fun _ ↦ (1 : ℝ)) b.toBasis
      (Set.equivOfEq (Set.powersetCard.coe_finset (Fin n) r).symm s)
      (fun _ _ _ _ _ ↦ TauCeti.ExteriorAlgebra.commute_smul_ιMulti_two _ _ _ _ _ _)

/-- **Hilbert norm of the normalized Kähler power**: for an orthogonal almost complex structure `J`
on a `2n`-dimensional real inner product space, the Hilbert norm `√⟨ωʳ / r!, ωʳ / r!⟩` equals
`√(n choose r)`. -/
theorem sqrt_alternatingFormInner_kahlerPowerForm {J : AlmostComplexStructure V}
    (hJ : ∀ u w, ⟪J u, J w⟫ = ⟪u, w⟫) (r : ℕ) :
    √(alternatingFormInner V (2 * r) (J.kahlerPowerForm r) (J.kahlerPowerForm r)) =
      √((finrank ℝ V / 2).choose r) := by
  obtain ⟨n, hn⟩ := J.even_finrank_real
  have hdim : finrank ℝ V = 2 * n := by omega
  have hn_eq : finrank ℝ V / 2 = n := by omega
  obtain ⟨b, hb⟩ := J.exists_adapted_orthonormalBasis (J.norm_apply hJ) n hdim
  let idx : Set.powersetCard (Fin n) r → Set.powersetCard (Fin (2 * n)) (2 * r) := fun s ↦
    Set.powersetCard.ofFinEmbEquiv (doubleOrderEmb (Set.powersetCard.ofFinEmbEquiv.symm s))
  have hidx_inj : Function.Injective idx :=
    Set.powersetCard.ofFinEmbEquiv.injective.comp
      (doubleOrderEmb_injective.comp Set.powersetCard.ofFinEmbEquiv.symm.injective)
  have hon : Orthonormal ℝ ((b.exteriorPower (2 * r)) ∘ idx) :=
    (b.exteriorPower (2 * r)).orthonormal.comp idx hidx_inj
  rw [ContinuousAlternatingMap.sqrt_alternatingFormInner_self,
    kahlerPowerForm_symm_eq_sum_adapted b hb r, hn_eq, norm_eq_sqrt_real_inner]
  congr 1
  have hinner := hon.inner_sum (fun _ ↦ (1 : ℝ)) (fun _ ↦ (1 : ℝ)) Finset.univ
  simp only [Function.comp_apply, one_smul, mul_one, Finset.sum_const, Finset.card_univ,
    nsmul_eq_mul] at hinner
  rw [hinner, ← Nat.card_eq_fintype_card, Set.powersetCard.card, Nat.card_eq_fintype_card,
    Fintype.card_fin, map_one, mul_one]

end KahlerPower

end TauCeti.AlmostComplexStructure

namespace TauCeti

section HermitianPower

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [InnerProductSpace ℂ E]
  [IsScalarTower ℝ ℂ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [InnerProductSpace ℂ F]
  [IsScalarTower ℝ ℂ F] [FiniteDimensional ℝ F]

variable (E) in
/-- The normalized `r`-th Kähler power `(kahlerTwoForm E) ^ r / r!` (power index `r`, form
degree `2 * r`) on a finite-dimensional Hermitian vector space `E`, as a real continuous
alternating `2r`-form (`TauCeti.kahlerPowerForm_eq_wedgePow`). -/
def kahlerPowerForm (r : ℕ) : E [⋀^Fin (2 * r)]→L[ℝ] ℝ :=
  (AlmostComplexStructure.ofComplexModule E).kahlerPowerForm r

/-- Specialization of `AlmostComplexStructure.kahlerPowerForm` to `ofComplexModule E`. -/
theorem kahlerPowerForm_eq_ofComplexModule (r : ℕ) :
    kahlerPowerForm E r = (AlmostComplexStructure.ofComplexModule E).kahlerPowerForm r :=
  (rfl)

/-- The normalized Kähler power on a Hermitian vector space is the normalized wedge power of
`TauCeti.kahlerTwoForm E`. -/
theorem kahlerPowerForm_eq_wedgePow (r : ℕ) :
    kahlerPowerForm E r = (r.factorial : ℝ)⁻¹ • (kahlerTwoForm E).wedgePow r := by
  rw [kahlerPowerForm_eq_ofComplexModule, AlmostComplexStructure.kahlerPowerForm_def,
    alternatingFormEquiv_ofComplexModule_kahlerForm]

/-- For power index `r = 1` (form degree `2`), `ω¹ / 1!` is `TauCeti.kahlerTwoForm E`. -/
@[simp]
theorem kahlerPowerForm_one : kahlerPowerForm E 1 = kahlerTwoForm E := by
  rw [kahlerPowerForm_eq_ofComplexModule, AlmostComplexStructure.kahlerPowerForm_one,
    alternatingFormEquiv_ofComplexModule_kahlerForm]

/-- Normalized Kähler powers vanish whenever the power index exceeds the complex dimension
(`r > finrank ℂ E`, equivalently form degree `2 * r > finrank ℝ E`). -/
theorem kahlerPowerForm_eq_zero_of_finrank_lt {r : ℕ} (hr : finrank ℂ E < r) :
    kahlerPowerForm E r = 0 := by
  have : FiniteDimensional ℂ E := Module.Finite.of_restrictScalars_finite ℝ ℂ E
  rw [kahlerPowerForm_eq_ofComplexModule]
  refine AlmostComplexStructure.kahlerPowerForm_eq_zero _ ?_
  rw [finrank_real_eq_two_mul_finrank_complex]
  omega

/-- Naturality of `TauCeti.kahlerPowerForm` under every complex linear isometry `f : E →ₗᵢ[ℂ] F`
(in particular, unitary invariance when `f : E ≃ₗᵢ[ℂ] E`). -/
theorem kahlerPowerForm_comp_linearIsometry (f : E →ₗᵢ[ℂ] F) (r : ℕ) :
    (kahlerPowerForm F r).compContinuousLinearMap (f.toContinuousLinearMap.restrictScalars ℝ) =
      kahlerPowerForm E r := by
  let fR : E →ₗᵢ[ℝ] F :=
    { toLinearMap := f.toLinearMap.restrictScalars ℝ
      norm_map' := f.norm_map }
  rw [kahlerPowerForm_eq_ofComplexModule, kahlerPowerForm_eq_ofComplexModule]
  exact AlmostComplexStructure.kahlerPowerForm_comp_linearIsometry fR
    ((isComplexLinearMap_iff_apply _ _ _).2 fun v ↦ by
      rw [AlmostComplexStructure.ofComplexModule_apply,
        AlmostComplexStructure.ofComplexModule_apply]
      exact f.map_smul Complex.I v) r

/-- **Hilbert norm of the normalized Kähler power**:
`√⟨ωʳ / r!, ωʳ / r!⟩ = √((finrank ℂ E).choose r)`. -/
theorem sqrt_alternatingFormInner_kahlerPowerForm (r : ℕ) :
    √(alternatingFormInner E (2 * r) (kahlerPowerForm E r) (kahlerPowerForm E r)) =
      √((finrank ℂ E).choose r) := by
  have : FiniteDimensional ℂ E := Module.Finite.of_restrictScalars_finite ℝ ℂ E
  rw [kahlerPowerForm_eq_ofComplexModule,
    AlmostComplexStructure.sqrt_alternatingFormInner_kahlerPowerForm
      AlmostComplexStructure.real_inner_ofComplexModule_ofComplexModule r,
    finrank_real_eq_two_mul_finrank_complex, Nat.mul_div_right _ (by decide : 0 < 2)]

end HermitianPower

end TauCeti
