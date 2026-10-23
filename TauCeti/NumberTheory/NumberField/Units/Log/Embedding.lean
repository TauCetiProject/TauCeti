/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.NumberField.InfinitePlace.Ramification
public import Mathlib.NumberTheory.NumberField.Units.DirichletTheorem
public import Mathlib.RepresentationTheory.Subrepresentation
public import TauCeti.Algebra.GroupAction.TypeTags
public import TauCeti.NumberTheory.Height.NumberField
public import TauCeti.RepresentationTheory.RestrictScalars
public import TauCeti.NumberTheory.NumberField.AutomorphismAction
public import TauCeti.NumberTheory.NumberField.Global.Places.Height

/-!
# The logarithmic embedding of the units

Let `L` be a number field. Mathlib's logarithmic embedding sends a unit `x` of `𝓞 L` to the vector
`(mult w * log w(x))_w` indexed by the infinite places `w ≠ w₀` of `L`, for a distinguished
infinite place `w₀`; its image is the unit lattice, a full `ℤ`-lattice in this space
`logSpace L`. The omitted coordinate is recovered from the product formula: the full vector,
indexed by all infinite places, has coordinate sum zero. So `logSpace L` is a coordinate chart
on the sum-zero hyperplane of `ℝ^{InfinitePlace L}` (`TauCeti.NumberField.Units.logSpaceExtend`).

The relative logarithmic height of a unit is half the `ℓ¹` norm of this full vector. Therefore
it is the sum of the absolute values of the kept coordinates together with the absolute value of
their sum, divided by two. This gives two-sided `ℓ¹` comparisons, a sharp supremum-norm bound,
and the corresponding absolute-height estimate. It also records exactly when the omitted
coordinate contributes to the positive-part and absolute-value formulas.

An automorphism `σ` of `L` over a subfield `K` permutes the infinite places of `L`, and so acts
on that hyperplane by permuting coordinates. Read in the chart this is a real representation
`TauCeti.NumberField.Units.logSpaceRep K L` of `Aut(L/K)` on `logSpace L`. The logarithmic
embedding is equivariant for the Galois action on the units
(`TauCeti.NumberField.Units.logEmbedding_smul`), so the unit lattice is a Galois-stable lattice
in this representation (`TauCeti.NumberField.Units.unitLatticeSubrep`). This is the form in
which the unit group enters the computation of Herbrand quotients of units in class field theory.

## Main definitions

* `TauCeti.NumberField.Units.logSpaceExtend`: the extension of a vector of `logSpace L` to the
  infinite place `w₀` by minus the sum of its coordinates.
* `TauCeti.NumberField.Units.logSpaceRep`: the permutation representation of `Aut(L/K)` on
  `logSpace L`.
* `TauCeti.NumberField.Units.unitLatticeSubrep`: the unit lattice as an integral
  subrepresentation.

## Main results

* `TauCeti.NumberField.Units.logSpaceExtend_logSpaceRep`: the extension intertwines
  `logSpaceRep` with the permutation of the infinite places.
* `TauCeti.NumberField.Units.mem_unitLattice_iff`: the unit lattice is the set of logarithmic
  embeddings of units.
* `TauCeti.NumberField.Units.logEmbedding_smul`: the logarithmic embedding is
  `Aut(L/K)`-equivariant.
* `TauCeti.NumberField.Units.two_mul_logHeight₁_eq_sum_mult_mul_abs_log`: twice the height of a
  unit is the sum of its weighted absolute logarithms over all infinite places.
* `TauCeti.NumberField.Units.two_mul_logHeight₁_eq_sum_abs_logEmbedding`: the exact relation
  between logarithmic height and the omitted-coordinate embedding.
* `TauCeti.NumberField.Units.norm_logEmbedding_le_logHeight₁` and
  `TauCeti.NumberField.Units.logHeight₁_le_rank_mul_norm_logEmbedding`: the supremum-norm
  comparisons.
* `TauCeti.NumberField.Units.sum_abs_logEmbedding_le_sum_mult_mul_abs_log`: the `ℓ¹` norm of
  the logarithmic embedding of a unit is at most the sum of its weighted absolute logarithms
  over all infinite places.

## References

* J. S. Milne, *Class Field Theory*, Chapter VII, §3 (the Herbrand quotient of the unit group).
* Y. Bugeaud and K. Győry, *Bounds for the solutions of unit equations*, Acta Arith. **74**
  (1996), 67–80, §3, formula (12).
-/

public noncomputable section

open Finset NumberField NumberField.InfinitePlace NumberField.Units
  NumberField.Units.dirichletUnitTheorem

namespace TauCeti.NumberField.Units

/-! ### The sum-zero hyperplane -/

section Extend

variable (L : Type*) [Field L] [NumberField L]

-- the infinite places have no computable equality, so the case split and the sum over
-- `{w // w ≠ w₀}` are classical, as in Mathlib's `NumberField.Units.dirichletUnitTheorem`
open Classical in
/-- The extension of a vector of `logSpace L`, indexed by the infinite places other than `w₀`,
to all infinite places, with coordinate at `w₀` minus the sum of the others. It identifies
`logSpace L` with the vectors of `ℝ^{InfinitePlace L}` of coordinate sum zero
(`TauCeti.NumberField.Units.sum_logSpaceExtend`,
`TauCeti.NumberField.Units.logSpaceExtend_eq_self`). -/
def logSpaceExtend : logSpace L →ₗ[ℝ] InfinitePlace L → ℝ where
  toFun y w := if h : w = w₀ then -∑ i, y i else y ⟨w, h⟩
  map_add' y z := by
    ext w
    by_cases h : w = w₀ <;> simp [h, sum_add_distrib, add_comm]
  map_smul' c y := by
    ext w
    by_cases h : w = w₀ <;> simp [h, mul_sum]

variable {L}

open Classical in
@[simp]
theorem logSpaceExtend_apply_w₀ (y : logSpace L) : logSpaceExtend L y w₀ = -∑ i, y i := by
  simp [logSpaceExtend]

@[simp]
theorem logSpaceExtend_apply_val (y : logSpace L) (w : {w : InfinitePlace L // w ≠ w₀}) :
    logSpaceExtend L y w.1 = y w := by
  simp [logSpaceExtend, w.2]

/-- The coordinates of `logSpaceExtend L y` sum to zero. -/
@[simp]
theorem sum_logSpaceExtend (y : logSpace L) : ∑ w, logSpaceExtend L y w = 0 := by
  classical
  rw [Fintype.sum_eq_add_sum_subtype_ne _ w₀, logSpaceExtend_apply_w₀, neg_add_eq_zero]
  exact Fintype.sum_congr _ _ fun w ↦ (logSpaceExtend_apply_val y w).symm

/-- The coordinates of `logSpaceExtend L y`, permuted by any permutation of the infinite places,
sum to zero. -/
theorem sum_logSpaceExtend_perm (y : logSpace L) (e : Equiv.Perm (InfinitePlace L)) :
    ∑ w, logSpaceExtend L y (e w) = 0 := by
  rw [Equiv.sum_comp e (logSpaceExtend L y), sum_logSpaceExtend]

/-- A vector of coordinate sum zero is the extension of its coordinates away from `w₀`. -/
theorem logSpaceExtend_eq_self {f : InfinitePlace L → ℝ} (hf : ∑ w, f w = 0) :
    logSpaceExtend L (fun w ↦ f w.1) = f := by
  classical
  ext w
  by_cases hw : w = w₀
  · subst hw
    rw [logSpaceExtend_apply_w₀, eq_comm, ← add_eq_zero_iff_eq_neg,
      ← Fintype.sum_eq_add_sum_subtype_ne f w₀, hf]
  · exact logSpaceExtend_apply_val (fun w ↦ f w.1) ⟨w, hw⟩

/-- The extension of the logarithmic embedding of a unit `x` is the full vector
`(mult w * log w(x))_w` over all infinite places, by the product formula. -/
@[simp]
theorem logSpaceExtend_logEmbedding (x : (𝓞 L)ˣ) :
    logSpaceExtend L (logEmbedding L (Additive.ofMul x)) = fun w ↦ w.mult * Real.log (w x) :=
  logSpaceExtend_eq_self (sum_mult_mul_log x)

end Extend

/-! ### The unit lattice -/

section UnitLattice

variable {L : Type*} [Field L] [NumberField L]

/-- A vector lies in the unit lattice exactly when it is the logarithmic embedding of a unit. -/
theorem mem_unitLattice_iff {y : logSpace L} :
    y ∈ unitLattice L ↔ ∃ u : (𝓞 L)ˣ, logEmbedding L (Additive.ofMul u) = y :=
  ⟨fun ⟨z, _, hz⟩ ↦ ⟨z.toMul, hz⟩, fun ⟨u, hu⟩ ↦ ⟨Additive.ofMul u, Submodule.mem_top, hu⟩⟩

/-- The logarithmic embedding of a unit lies in the unit lattice. -/
@[simp]
theorem logEmbedding_mem_unitLattice (x : Additive (𝓞 L)ˣ) : logEmbedding L x ∈ unitLattice L :=
  ⟨x, Submodule.mem_top, rfl⟩

end UnitLattice

/-! ### The `ℓ¹` norm -/

section Norm

variable {L : Type*} [Field L] [NumberField L]

open Classical in
/-- The `ℓ¹` norm of the logarithmic embedding of a unit, which omits the distinguished infinite
place, is at most the sum of the weighted absolute logarithms over all infinite places. -/
theorem sum_abs_logEmbedding_le_sum_mult_mul_abs_log (u : (𝓞 L)ˣ) :
    ∑ w, |logEmbedding L (Additive.ofMul u) w| ≤
      ∑ w : InfinitePlace L, w.mult * |Real.log (w u)| := by
  simp_rw [logEmbedding_component, abs_mul, Nat.abs_cast]
  rw [← sum_subtype {w | w ≠ w₀} (by simp)
    fun w : InfinitePlace L => (w.mult : ℝ) * |Real.log (w u)|]
  exact sum_le_univ_sum_of_nonneg fun _ => by positivity

end Norm

/-! ### Comparison with the logarithmic height -/

section Height

variable {L : Type*} [Field L] [NumberField L]

/-- Twice the relative logarithmic height of a unit is the sum over all infinite places of its
weighted absolute logarithms: the finite places contribute nothing. -/
theorem two_mul_logHeight₁_eq_sum_mult_mul_abs_log (u : (𝓞 L)ˣ) :
    2 * Height.logHeight₁ (u : L) = ∑ w : InfinitePlace L, w.mult * |Real.log (w u)| := by
  have hfinite : ∀ v ∉ (∅ : Finset (IsDedekindDomain.HeightOneSpectrum (𝓞 L))),
      NumberField.HeightOneSpectrum.adicAbv L v (u : L) = 1 := by
    intro v _
    exact (v.adicAbv_coe_eq_one_iff
      (NumberField.HeightOneSpectrum.one_lt_absNorm_nnreal v) (u : 𝓞 L)).mpr
        (Ideal.notMem_of_isUnit v.asIdeal u.isUnit)
  rw [TauCeti.GlobalNumberFields.two_mul_logHeight₁_eq_sum_abs_log_adicAbv_add_sum_mult_mul_abs_log
    (∅ : Finset (IsDedekindDomain.HeightOneSpectrum (𝓞 L))) hfinite]
  simp only [Finset.sum_empty, zero_add]

open Classical in
/-- Twice the relative logarithmic height of a unit is the `ℓ¹` norm of its logarithmic
embedding, together with the absolute value of the omitted coordinate. -/
theorem two_mul_logHeight₁_eq_sum_abs_logEmbedding (u : (𝓞 L)ˣ) :
    2 * Height.logHeight₁ (u : L) =
      ∑ w, |logEmbedding L (Additive.ofMul u) w| +
        |∑ w, logEmbedding L (Additive.ofMul u) w| := by
  rw [two_mul_logHeight₁_eq_sum_mult_mul_abs_log]
  calc
    ∑ w : InfinitePlace L, w.mult * |Real.log (w u)| =
        ∑ w : InfinitePlace L, |logSpaceExtend L (logEmbedding L (Additive.ofMul u)) w| := by
      congr 1
      funext w
      rw [logSpaceExtend_logEmbedding]
      simp [abs_mul]
    _ = |logSpaceExtend L (logEmbedding L (Additive.ofMul u)) w₀| +
        ∑ w : {w : InfinitePlace L // w ≠ w₀},
          |logSpaceExtend L (logEmbedding L (Additive.ofMul u)) w| :=
      Fintype.sum_eq_add_sum_subtype_ne _ w₀
    _ = |∑ w, logEmbedding L (Additive.ofMul u) w| +
        ∑ w, |logEmbedding L (Additive.ofMul u) w| := by simp
    _ = ∑ w, |logEmbedding L (Additive.ofMul u) w| +
        |∑ w, logEmbedding L (Additive.ofMul u) w| := add_comm _ _

open Classical in
/-- The `ℓ¹` norm of the logarithmic embedding of a unit is at most twice its relative
logarithmic height. -/
theorem sum_abs_logEmbedding_le_two_mul_logHeight₁ (u : (𝓞 L)ˣ) :
    ∑ w, |logEmbedding L (Additive.ofMul u) w| ≤ 2 * Height.logHeight₁ (u : L) := by
  rw [two_mul_logHeight₁_eq_sum_abs_logEmbedding]
  exact le_add_of_nonneg_right (abs_nonneg _)

open Classical in
/-- Twice the relative logarithmic height of a unit is at most twice the `ℓ¹` norm of its
logarithmic embedding. -/
theorem two_mul_logHeight₁_le_two_mul_sum_abs_logEmbedding (u : (𝓞 L)ˣ) :
    2 * Height.logHeight₁ (u : L) ≤
      2 * ∑ w, |logEmbedding L (Additive.ofMul u) w| := by
  rw [two_mul_logHeight₁_eq_sum_abs_logEmbedding]
  nlinarith [Finset.abs_sum_le_sum_abs (fun w ↦ logEmbedding L (Additive.ofMul u) w)
    Finset.univ]

open Classical in
/-- The supremum norm of the logarithmic embedding of a unit is at most its relative
logarithmic height. This improves by a factor of two on the bound obtained from its `ℓ¹` norm. -/
theorem norm_logEmbedding_le_logHeight₁ (u : (𝓞 L)ˣ) :
    ‖logEmbedding L (Additive.ofMul u)‖ ≤ Height.logHeight₁ (u : L) := by
  rw [pi_norm_le_iff_of_nonneg (by positivity)]
  intro w
  rw [Real.norm_eq_abs, logEmbedding_component]
  have h := TauCeti.GlobalNumberFields.abs_log_normalizedAbsValue_le_logHeight₁
    (Sum.inr w.1) (u : L)
  simpa [TauCeti.GlobalNumberFields.normalizedAbsValue_inr, Real.log_pow, abs_mul,
    Nat.abs_cast] using h

open Classical in
/-- The relative logarithmic height of a unit is bounded by the unit rank times the supremum
norm of its logarithmic embedding. -/
theorem logHeight₁_le_rank_mul_norm_logEmbedding (u : (𝓞 L)ˣ) :
    Height.logHeight₁ (u : L) ≤
      NumberField.Units.rank L * ‖logEmbedding L (Additive.ofMul u)‖ := by
  let y := logEmbedding L (Additive.ofMul u)
  have hcard : Fintype.card {w : InfinitePlace L // w ≠ w₀} = NumberField.Units.rank L := by
    simp [NumberField.Units.rank]
  have hsum : ∑ w, |y w| ≤ NumberField.Units.rank L * ‖y‖ := by
    simpa only [Real.norm_eq_abs, hcard, nsmul_eq_mul] using Pi.sum_norm_apply_le_norm y
  have habs : |∑ w, y w| ≤ NumberField.Units.rank L * ‖y‖ :=
    (Finset.abs_sum_le_sum_abs (fun w ↦ y w) Finset.univ).trans hsum
  have hheight := two_mul_logHeight₁_eq_sum_abs_logEmbedding u
  dsimp only [y] at hsum habs
  nlinarith

open Classical in
/-- The absolute logarithmic height of a unit is at most the `ℓ¹` norm of its logarithmic
embedding divided by the degree of the number field. -/
theorem absLogHeight₁_le_sum_abs_logEmbedding_div_finrank (u : (𝓞 L)ˣ) :
    NumberField.absLogHeight₁ (u : L) ≤
      (∑ w, |logEmbedding L (Additive.ofMul u) w|) / Module.finrank ℚ L := by
  rw [NumberField.absLogHeight₁_eq_div]
  refine div_le_div_of_nonneg_right ?_ (by positivity)
  nlinarith [two_mul_logHeight₁_le_two_mul_sum_abs_logEmbedding u]

open Classical in
/-- The relative logarithmic height of a unit equals the sum of the positive parts of the kept
logarithmic coordinates exactly when its absolute value at the omitted place is at most one. -/
theorem logHeight₁_eq_sum_posPart_logEmbedding_iff (u : (𝓞 L)ˣ) :
    Height.logHeight₁ (u : L) =
        ∑ w, (logEmbedding L (Additive.ofMul u) w)⁺ ↔ (w₀ (K := L)) u ≤ 1 := by
  let y := logEmbedding L (Additive.ofMul u)
  have hheight := two_mul_logHeight₁_eq_sum_abs_logEmbedding u
  have hpos : 2 * ∑ w, (y w)⁺ = ∑ w, |y w| + ∑ w, y w := by
    calc
      2 * ∑ w, (y w)⁺ = ∑ w, 2 * (y w)⁺ := by rw [Finset.mul_sum]
      _ = ∑ w, (y w + |y w|) := by
        apply Finset.sum_congr rfl
        intro w _
        simpa [two_nsmul] using (add_abs_eq_two_nsmul_posPart (y w)).symm
      _ = ∑ w, y w + ∑ w, |y w| := Finset.sum_add_distrib
      _ = ∑ w, |y w| + ∑ w, y w := add_comm _ _
  have hsum : ∑ w, y w =
      -(((w₀ (K := L)).mult : ℝ) * Real.log ((w₀ (K := L)) u)) :=
    by simpa only [y, neg_mul] using
      (NumberField.Units.dirichletUnitTheorem.sum_logEmbedding_component u)
  have heq :
      (Height.logHeight₁ (u : L) = ∑ w, (y w)⁺) ↔ 0 ≤ ∑ w, y w := by
    constructor
    · intro h
      have habs : |∑ w, y w| = ∑ w, y w := by
        nlinarith
      exact abs_eq_self.mp habs
    · intro h
      have habs : |∑ w, y w| = ∑ w, y w := abs_eq_self.mpr h
      nlinarith
  rw [heq, hsum]
  constructor
  · intro h
    apply (Real.log_nonpos_iff (by positivity)).mp
    have hmult : (0 : ℝ) < (w₀ (K := L)).mult := by
      exact_mod_cast InfinitePlace.mult_pos
    nlinarith
  · intro h
    have hlog := (Real.log_nonpos_iff (by positivity)).mpr h
    have hmult : (0 : ℝ) < (w₀ (K := L)).mult := by
      exact_mod_cast InfinitePlace.mult_pos
    nlinarith

open Classical in
/-- Twice the relative logarithmic height of a unit equals the `ℓ¹` norm of the kept
logarithmic coordinates exactly when its absolute value at the omitted place is one. -/
theorem two_mul_logHeight₁_eq_sum_abs_logEmbedding_iff (u : (𝓞 L)ˣ) :
    2 * Height.logHeight₁ (u : L) =
        ∑ w, |logEmbedding L (Additive.ofMul u) w| ↔ (w₀ (K := L)) u = 1 := by
  let y := logEmbedding L (Additive.ofMul u)
  have hheight := two_mul_logHeight₁_eq_sum_abs_logEmbedding u
  have hsum : ∑ w, y w =
      -(((w₀ (K := L)).mult : ℝ) * Real.log ((w₀ (K := L)) u)) :=
    by simpa only [y, neg_mul] using
      (NumberField.Units.dirichletUnitTheorem.sum_logEmbedding_component u)
  constructor
  · intro h
    have habs : |∑ w, y w| = 0 := by
      nlinarith
    simpa only [abs_eq_zero, hsum, neg_eq_zero,
      NumberField.Units.dirichletUnitTheorem.mult_log_place_eq_zero] using habs
  · intro h
    have hsum_zero : ∑ w, y w = 0 := by
      rw [hsum, h, Real.log_one, mul_zero, neg_zero]
    calc
      2 * Height.logHeight₁ (u : L) = ∑ w, |y w| + |∑ w, y w| := by
        simpa only [y] using hheight
      _ = ∑ w, |y w| := by rw [hsum_zero, abs_zero, add_zero]

end Height

/-! ### The Galois representation -/

variable (K L : Type*) [Field K] [Field L] [NumberField L] [Algebra K L]

/-- The real representation of `Aut(L/K)` on `logSpace L`: an automorphism `σ` permutes the
coordinates of the sum-zero hyperplane of `ℝ^{InfinitePlace L}` by `w ↦ σ • w`, read in the chart
`logSpaceExtend L` (`TauCeti.NumberField.Units.logSpaceExtend_logSpaceRep`). -/
def logSpaceRep : Representation ℝ (L ≃ₐ[K] L) (logSpace L) where
  toFun σ := LinearMap.funLeft ℝ ℝ (fun w : {w : InfinitePlace L // w ≠ w₀} ↦ σ⁻¹ • w.1) ∘ₗ
    logSpaceExtend L
  map_one' := LinearMap.ext fun y ↦ funext fun w ↦ by simp
  map_mul' σ τ := LinearMap.ext fun y ↦ funext fun w ↦ by
    have hτ : ∑ v, logSpaceExtend L y (τ⁻¹ • v) = 0 :=
      sum_logSpaceExtend_perm y (MulAction.toPerm τ⁻¹)
    have h : (LinearMap.funLeft ℝ ℝ fun w : {w : InfinitePlace L // w ≠ w₀} ↦ τ⁻¹ • w.1)
        (logSpaceExtend L y) = fun w ↦ logSpaceExtend L y (τ⁻¹ • w.1) :=
      funext fun w ↦ LinearMap.funLeft_apply _ _ _ _ w
    simp only [LinearMap.comp_apply, LinearMap.funLeft_apply, Module.End.mul_apply, h,
      logSpaceExtend_eq_self hτ, mul_inv_rev, mul_smul]

variable {K L}

@[simp]
theorem logSpaceRep_apply (σ : L ≃ₐ[K] L) (y : logSpace L)
    (w : {w : InfinitePlace L // w ≠ w₀}) :
    logSpaceRep K L σ y w = logSpaceExtend L y (σ⁻¹ • w.1) :=
  (rfl)

/-- **`logSpaceRep` is the permutation of the infinite places**, read through the identification
`logSpaceExtend L` of `logSpace L` with the sum-zero hyperplane. -/
@[simp]
theorem logSpaceExtend_logSpaceRep (σ : L ≃ₐ[K] L) (y : logSpace L) :
    logSpaceExtend L (logSpaceRep K L σ y) =
      fun w : InfinitePlace L ↦ logSpaceExtend L y (σ⁻¹ • w) := by
  have hrep : logSpaceRep K L σ y =
      fun w : {w : InfinitePlace L // w ≠ w₀} ↦ logSpaceExtend L y (σ⁻¹ • w.1) :=
    funext (logSpaceRep_apply σ y)
  rw [hrep]
  exact logSpaceExtend_eq_self (f := fun w ↦ logSpaceExtend L y (σ⁻¹ • w))
    (sum_logSpaceExtend_perm y (MulAction.toPerm σ⁻¹))

/-- **The logarithmic embedding is Galois-equivariant**: the logarithmic embedding of `σ • x` is
`logSpaceRep K L σ` applied to that of `x`. -/
@[simp]
theorem logEmbedding_smul (σ : L ≃ₐ[K] L) (x : Additive (𝓞 L)ˣ) :
    logEmbedding L (σ • x) = logSpaceRep K L σ (logEmbedding L x) := by
  -- The action on the additive tag is defined through `ofMul (σ • x.toMul)`.
  -- Expose that defining equality so the unit-coordinate lemmas can rewrite before
  -- simplification folds `ofMul` back into the additive action.
  change logEmbedding L (Additive.ofMul (σ • x.toMul)) =
    logSpaceRep K L σ (logEmbedding L (Additive.ofMul x.toMul))
  ext w
  have hmult : (σ.symm • w.1).mult = w.1.mult := by
    unfold mult
    rw [isReal_smul_iff]
  rw [logSpaceRep_apply, logSpaceExtend_logEmbedding x.toMul,
    logEmbedding_component (σ • x.toMul)]
  simp [hmult, AlgEquiv.aut_inv]

variable (K L) in
/-- The unit lattice `logEmbedding L ((𝓞 L)ˣ)` as an integral subrepresentation of `logSpaceRep`:
it is stable under `Aut(L/K)` by `TauCeti.NumberField.Units.logEmbedding_smul`. -/
def unitLatticeSubrep : Subrepresentation (logSpaceRep K L).restrictScalarsInt where
  toSubmodule := unitLattice L
  apply_mem_toSubmodule σ y := by
    rintro ⟨x, -, rfl⟩
    exact ⟨Additive.ofMul (σ • x.toMul), trivial, by
      simp⟩

@[simp]
theorem toSubmodule_unitLatticeSubrep : (unitLatticeSubrep K L).toSubmodule = unitLattice L :=
  (rfl)

end TauCeti.NumberField.Units
