/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.InnerProductSpace.HodgeStar.Kahler.Mass
public import TauCeti.Analysis.InnerProductSpace.Orthonormal.Wedge
import TauCeti.Geometry.Symplectic.Finrank

/-!
# The Wirtinger inequality in every degree

Let `J` be an orthogonal almost complex structure on a finite-dimensional real inner product
space `V`, with Kähler two-form `ω(u, w) = ⟪J u, w⟫`. The normalized Kähler power `ωʳ / r!`,
`TauCeti.AlmostComplexStructure.kahlerPowerForm J r`, is a real `2r`-form. The **Wirtinger
inequality** says that it has comass at most one, with value one on every orthonormal frame
`(u₀, J u₀, …, u_{r-1}, J u_{r-1})` (`TauCeti.AlmostComplexStructure.complexRealFrame`); such
frames exist exactly when `2r ≤ dim V`, so in that range the comass is exactly one. Thus the
complex `r`-planes, oriented by such frames, are planes on which `ωʳ / r!` attains its comass.

The inequality follows from two comass bounds of
`TauCeti.Analysis.InnerProductSpace.Orthonormal.Wedge`: inserting a vector `v` into `ω ^ (m + 1)`
gives `(m + 1) • (ι_v ω ∧ ω ^ m)`, and wedging with a one-form does not increase comass, so
`‖ω ^ r‖ ≤ r! ‖ω‖ ^ r`. The Kähler form itself has comass at most one by Cauchy–Schwarz.

For multiplication by `i` on `ℂⁿ` with the real part of the Hermitian inner product, the Kähler
form is `ω(v, w) = ⟪i v, w⟫ = Im ⟪v, w⟫_ℂ`, the standard Kähler form, and the frames above are the
frames `(u₀, i u₀, …)` of unitary families `u`.

## Main definitions

* `TauCeti.AlmostComplexStructure.kahlerPowerForm J r`: the `2r`-form `ωʳ / r!`.
* `TauCeti.AlmostComplexStructure.complexRealFrame J u`: the real frame
  `(u₀, J u₀, u₁, J u₁, …)` of a family `u`.

## Main results

* `TauCeti.AlmostComplexStructure.norm_kahlerPowerForm_le`: `ωʳ / r!` has comass at most one.
* `TauCeti.AlmostComplexStructure.kahlerPowerForm_complexRealFrame`: its value on an orthonormal
  frame `(u₀, J u₀, …)` is one.
* `TauCeti.AlmostComplexStructure.norm_kahlerPowerForm`: for `2r ≤ dim V` its comass is one.

## References

* W. Wirtinger, *Eine Determinantenidentität und ihre Anwendung auf analytische Gebilde in
  euklidischer und Hermitescher Maßbestimmung*, Monatsh. Math. Phys. **44** (1936), 343–365.
* H. Federer, *Geometric Measure Theory*, Springer, 1969, §1.8.2.
* R. Harvey and H. B. Lawson, *Calibrated geometries*, Acta Math. **148** (1982), Theorem II.6.11.
-/

public section

noncomputable section

open Module ContinuousAlternatingMap
open scoped RealInnerProductSpace Nat

namespace TauCeti.AlmostComplexStructure

/-! ### The frame `(u₀, J u₀, u₁, J u₁, …)` -/

section Frame

variable {M : Type*} [AddCommGroup M] [Module ℝ M] {r : ℕ}

/-- The real frame `(u₀, J u₀, u₁, J u₁, …)` of a family `u` of `r` vectors: its vector of index
`2 i` is `u i` and its vector of index `2 i + 1` is `J (u i)`. -/
def complexRealFrame (J : AlmostComplexStructure M) (u : Fin r → M) : Fin (2 * r) → M :=
  fun k ↦ ![u (finProdFinEquiv.symm (Fin.cast (Nat.mul_comm 2 r) k)).1,
    J (u (finProdFinEquiv.symm (Fin.cast (Nat.mul_comm 2 r) k)).1)]
    (finProdFinEquiv.symm (Fin.cast (Nat.mul_comm 2 r) k)).2

/-- The vector of index `k` of `(u₀, J u₀, u₁, J u₁, …)` is `u (k / 2)` for even `k` and
`J (u (k / 2))` for odd `k`. -/
theorem complexRealFrame_apply (J : AlmostComplexStructure M) (u : Fin r → M) (k : Fin (2 * r)) :
    J.complexRealFrame u k =
      if (k : ℕ) % 2 = 0 then u ⟨k / 2, by omega⟩ else J (u ⟨k / 2, by omega⟩) := by
  have hq : finProdFinEquiv.symm (Fin.cast (Nat.mul_comm 2 r) k) =
      (⟨k / 2, by omega⟩, ⟨k % 2, by omega⟩) := by
    ext <;> simp [finProdFinEquiv]
  simp only [complexRealFrame, hq]
  split_ifs with hk
  · simp [hk]
  · have h1 : (⟨k % 2, by omega⟩ : Fin 2) = 1 := by
      ext
      simp only [Fin.val_one]
      omega
    simp [h1]

/-- The vector of index `2 i` of `(u₀, J u₀, u₁, J u₁, …)` is `u i`. -/
@[simp]
theorem complexRealFrame_apply_two_mul (J : AlmostComplexStructure M) (u : Fin r → M)
    (i : Fin r) : J.complexRealFrame u ⟨2 * i, by omega⟩ = u i := by
  rw [complexRealFrame_apply, ite_eq_left_of_eq_true _ _ (by simp)]
  congr 1
  ext
  simp

/-- The vector of index `2 i + 1` of `(u₀, J u₀, u₁, J u₁, …)` is `J (u i)`. -/
@[simp]
theorem complexRealFrame_apply_two_mul_add_one (J : AlmostComplexStructure M) (u : Fin r → M)
    (i : Fin r) : J.complexRealFrame u ⟨2 * i + 1, by omega⟩ = J (u i) := by
  rw [complexRealFrame_apply, ite_eq_right_of_eq_false _ _ (by simp)]
  congr 2
  ext
  simp
  omega

end Frame

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  {J : AlmostComplexStructure V} {r : ℕ}

/-- An orthogonal almost complex structure has orthonormal frames `(u₀, J u₀, …, u_{r-1},
J u_{r-1})` whenever `2 r ≤ dim V`: take the first `2 r` vectors of an adapted orthonormal
basis. -/
theorem exists_orthonormal_complexRealFrame (hJ : ∀ u w, ⟪J u, J w⟫ = ⟪u, w⟫)
    (hr : 2 * r ≤ finrank ℝ V) : ∃ u : Fin r → V, Orthonormal ℝ (J.complexRealFrame u) := by
  obtain ⟨n, hn⟩ := J.even_finrank_real
  obtain ⟨b, hb⟩ := J.exists_adapted_orthonormalBasis (norm_apply hJ) n (by omega)
  refine ⟨fun i : Fin r ↦ b ⟨2 * i, by omega⟩, ?_⟩
  have hframe : J.complexRealFrame (fun i : Fin r ↦ b ⟨2 * i, by omega⟩) =
      b ∘ Fin.castLE (by omega) := by
    funext k
    rw [complexRealFrame_apply, Function.comp_apply]
    split_ifs with hk
    · congr 1
      ext
      simp only [Fin.val_castLE]
      omega
    · rw [← hb ⟨k / 2, by omega⟩]
      congr 1
      ext
      simp only [Fin.val_castLE]
      omega
  rw [hframe]
  exact b.orthonormal.comp _ (Fin.castLE_injective _)

/-! ### Normalized Kähler powers -/

/-- The **normalized Kähler power** `ωʳ / r!`, the `2r`-form of the `r`-th wedge power of the
Kähler two-form `ω(u, w) = ⟪J u, w⟫` divided by `r!`. -/
def kahlerPowerForm (J : AlmostComplexStructure V) (r : ℕ) : V [⋀^Fin (2 * r)]→L[ℝ] ℝ :=
  (r ! : ℝ)⁻¹ • (alternatingFormEquiv V 2 J.kahlerForm).wedgePow r

/-- The normalized Kähler power is `(r!)⁻¹ • ωʳ`. -/
theorem kahlerPowerForm_def (J : AlmostComplexStructure V) (r : ℕ) :
    J.kahlerPowerForm r = (r ! : ℝ)⁻¹ • (alternatingFormEquiv V 2 J.kahlerForm).wedgePow r :=
  (rfl)

/-- **The Wirtinger inequality.** For an orthogonal almost complex structure the normalized
Kähler power `ωʳ / r!` has comass at most one. -/
theorem norm_kahlerPowerForm_le (hJ : ∀ u w, ⟪J u, J w⟫ = ⟪u, w⟫) (r : ℕ) :
    ‖J.kahlerPowerForm r‖ ≤ 1 := by
  rw [kahlerPowerForm_def, norm_smul, norm_inv, Real.norm_natCast,
    inv_mul_le_iff₀ (by positivity), mul_one]
  exact (norm_wedgePow_le _ r).trans (mul_le_of_le_one_right (by positivity)
    (pow_le_one₀ (norm_nonneg _) (norm_alternatingFormEquiv_kahlerForm_le hJ)))

/-- The normalized Kähler power `ωʳ / r!` takes the value one on every orthonormal frame
`(u₀, J u₀, …, u_{r-1}, J u_{r-1})`. -/
theorem kahlerPowerForm_complexRealFrame (hJ : ∀ u w, ⟪J u, J w⟫ = ⟪u, w⟫) {u : Fin r → V}
    (hu : Orthonormal ℝ (J.complexRealFrame u)) :
    J.kahlerPowerForm r (J.complexRealFrame u) = 1 := by
  have hinner (i j : Fin r) : ⟪u i, u j⟫ = if i = j then 1 else 0 := by
    have h := orthonormal_iff_ite.1 hu ⟨2 * i, by omega⟩ ⟨2 * j, by omega⟩
    simp only [complexRealFrame_apply_two_mul, Fin.mk.injEq] at h
    simpa [Fin.ext_iff] using h
  have hJinner (i j : Fin r) : ⟪J (u i), u j⟫ = 0 := by
    have h := hu.inner_eq_zero (i := ⟨2 * i + 1, by omega⟩) (j := ⟨2 * j, by omega⟩)
      (by rw [ne_eq, Fin.mk.injEq]; omega)
    simpa only [complexRealFrame_apply_two_mul, complexRealFrame_apply_two_mul_add_one] using h
  -- The frame is, by definition, the family of pairs `(u i, J (u i))` indexed through
  -- `finProdFinEquiv`, on which `ω ^ r` takes the value `r!`.
  have hpow : (alternatingFormEquiv V 2 J.kahlerForm).wedgePow r (J.complexRealFrame u) = r ! :=
    wedgePow_apply_finProdFinEquiv _ (fun q ↦ ![u q.1, J (u q.1)] q.2)
      (fun i j ↦ by simpa [alternatingFormEquiv_kahlerForm_apply hJ] using hJinner i j)
      (fun i j ↦ by simpa [alternatingFormEquiv_kahlerForm_apply hJ, hJ] using hinner i j)
  rw [kahlerPowerForm_def, ContinuousAlternatingMap.smul_apply, hpow, smul_eq_mul,
    inv_mul_cancel₀ (by positivity)]

/-- **The Wirtinger inequality is sharp**: for `2r ≤ dim V` the normalized Kähler power
`ωʳ / r!` has comass exactly one. -/
theorem norm_kahlerPowerForm (hJ : ∀ u w, ⟪J u, J w⟫ = ⟪u, w⟫) (hr : 2 * r ≤ finrank ℝ V) :
    ‖J.kahlerPowerForm r‖ = 1 := by
  obtain ⟨u, hu⟩ := exists_orthonormal_complexRealFrame hJ hr
  refine le_antisymm (norm_kahlerPowerForm_le hJ r) ?_
  simpa [kahlerPowerForm_complexRealFrame hJ hu, hu.norm_eq_one] using
    (J.kahlerPowerForm r).le_opNorm (J.complexRealFrame u)

end TauCeti.AlmostComplexStructure
