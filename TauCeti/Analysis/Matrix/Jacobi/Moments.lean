/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Matrix.Jacobi.Basic
public import TauCeti.Probability.Distributions.Dirichlet.Density
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Pi
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Analysis.Calculus.FDeriv.Pi
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.MeasureTheory.Constructions.Pi
import TauCeti.Analysis.Matrix.Jacobi.Reconstruction

/-!
# The Jacobi moment map and spectral chart bijection

This file constructs the coordinate equivalences, moment maps, and triangular Jacobian for real
Jacobi matrices with strictly positive subdiagonal entries:

* `TauCeti.jacobiCoordEquiv` and `TauCeti.spectralCoordEquiv` package the tridiagonal entries
  `(a, b)` and the spectral chart coordinates `(lam, q')` into `Fin (2 * n + 1) → ℝ` while
  preserving Lebesgue measure.
* `TauCeti.jacobiMomentMap` sends interleaved tridiagonal coordinates `(a 0, b 0, …, a n)` to
  the moment vector `r ↦ (J ^ (r + 1)) 0 0`. Its `(r, j)` partial derivatives vanish for `r < j`
  and equal `(∏ m < k, b m) ^ 2` at `r = 2 * k` and `2 * (∏ m < k, b m) ^ 2 * b k` at
  `r = 2 * k + 1`, yielding injectivity on `b > 0` (`TauCeti.injOn_jacobiMomentMap`) and the
  lower-triangular Jacobian `TauCeti.det_fderiv_jacobiMomentMap`.
* Combining injectivity of the Jacobi moment map with the spectral reconstruction theorem from
  `TauCeti.Analysis.Matrix.Jacobi.Reconstruction` shows that `TauCeti.jacobiSpectralChart` maps
  `TauCeti.jacobiDomain n` bijectively onto `TauCeti.spectralDomain n`, and that
  `TauCeti.spectralMomentMap` is injective on `spectralDomain n` with the same image.

## References

* I. Dumitriu and A. Edelman, *Matrix models for beta ensembles*, J. Math. Phys. 43 (2002),
  5830–5847.
* G. W. Anderson, A. Guionnet, and O. Zeitouni, *An Introduction to Random Matrices*, Cambridge
  University Press, 2010, §4.5.1.
-/

public section

noncomputable section

open Matrix MeasureTheory Set TauCeti.Probability

namespace TauCeti

/-! ### Coordinate equivalences and domains -/

/-- Interleaving equivalence `Fin (n + 1) ⊕ Fin n ≃ Fin (2 * n + 1)`, placing diagonal index `k`
at `2 * k` and subdiagonal index `k` at `2 * k + 1`. -/
private def interleaveIndexEquiv (n : ℕ) : Fin (n + 1) ⊕ Fin n ≃ Fin (2 * n + 1) where
  toFun
    | .inl k => ⟨2 * k.val, by omega⟩
    | .inr k => ⟨2 * k.val + 1, by omega⟩
  invFun r :=
    if h : r.val % 2 = 0 then .inl ⟨r.val / 2, by omega⟩ else .inr ⟨r.val / 2, by omega⟩
  left_inv x := by
    cases x with
    | inl k => simp
    | inr k =>
        have h : (2 * k.val + 1) % 2 ≠ 0 := by omega
        dsimp only
        rw [dite_eq_right h]
        congr 1; ext; dsimp only; omega
  right_inv r := by
    by_cases h : r.val % 2 = 0
    · dsimp only
      rw [dite_eq_left h]
      ext; simp; omega
    · dsimp only
      rw [dite_eq_right h]
      ext; simp; omega

/-- Index equivalence `Fin (n + 1) ⊕ {i // i ≠ Fin.last n} ≃ Fin (2 * n + 1)`, placing
eigenvalue indices at `0, …, n` and spectral chart weight indices at `n + 1, …, 2 * n`. -/
private def spectralIndexEquiv (n : ℕ) :
    Fin (n + 1) ⊕ {i : Fin (n + 1) // i ≠ Fin.last n} ≃ Fin (2 * n + 1) where
  toFun
    | .inl k => ⟨k.val, by omega⟩
    | .inr j => ⟨n + 1 + j.1.val, by have : j.1.val < n := Fin.lt_last_iff_ne_last.mpr j.2; omega⟩
  invFun r :=
    if h : r.val < n + 1 then .inl ⟨r.val, h⟩
    else .inr ⟨⟨r.val - (n + 1), by omega⟩, fun heq => by
      have hv := congrArg Fin.val heq; simp at hv; omega⟩
  left_inv x := by
    cases x with
    | inl k =>
        have hk : k.val < n + 1 := k.isLt
        dsimp only
        rw [dite_eq_left hk]
    | inr j =>
        have h : ¬(n + 1 + j.1.val < n + 1) := by omega
        dsimp only
        rw [dite_eq_right h]
        congr 1; refine Subtype.ext (Fin.ext ?_); simp
  right_inv r := by
    by_cases h : r.val < n + 1
    · dsimp only
      rw [dite_eq_left h]
    · dsimp only
      rw [dite_eq_right h]
      ext; simp; omega

/-- Volume-preserving measurable equivalence interleaving `(a, b)` into `Fin (2 * n + 1) → ℝ`. -/
def jacobiCoordEquiv (n : ℕ) :
    (Fin (n + 1) → ℝ) × (Fin n → ℝ) ≃ᵐ (Fin (2 * n + 1) → ℝ) :=
  (MeasurableEquiv.sumPiEquivProdPi (fun _ : Fin (n + 1) ⊕ Fin n => ℝ)).symm.trans
    (MeasurableEquiv.piCongrLeft (fun _ : Fin (2 * n + 1) => ℝ) (interleaveIndexEquiv n))

/-- Volume-preserving measurable equivalence concatenating `(lam, q')` into
`Fin (2 * n + 1) → ℝ`. -/
def spectralCoordEquiv (n : ℕ) :
    (Fin (n + 1) → ℝ) × ({i : Fin (n + 1) // i ≠ Fin.last n} → ℝ) ≃ᵐ (Fin (2 * n + 1) → ℝ) :=
  (MeasurableEquiv.sumPiEquivProdPi
    (fun _ : Fin (n + 1) ⊕ {i : Fin (n + 1) // i ≠ Fin.last n} => ℝ)).symm.trans
    (MeasurableEquiv.piCongrLeft (fun _ : Fin (2 * n + 1) => ℝ) (spectralIndexEquiv n))

/-- Even coordinates of `jacobiCoordEquiv n (a, b)` recover the diagonal entries `a`. -/
@[simp]
theorem jacobiCoordEquiv_apply_even (n : ℕ) (a : Fin (n + 1) → ℝ) (b : Fin n → ℝ)
    (k : Fin (n + 1)) :
    jacobiCoordEquiv n (a, b) ⟨2 * k.val, by omega⟩ = a k := by
  change (MeasurableEquiv.piCongrLeft (fun _ => ℝ) (interleaveIndexEquiv n))
    ((MeasurableEquiv.sumPiEquivProdPi (fun _ => ℝ)).symm (a, b))
    (interleaveIndexEquiv n (.inl k)) = a k
  simp [MeasurableEquiv.piCongrLeft, MeasurableEquiv.sumPiEquivProdPi]

/-- Odd coordinates of `jacobiCoordEquiv n (a, b)` recover the subdiagonal entries `b`. -/
@[simp]
theorem jacobiCoordEquiv_apply_odd (n : ℕ) (a : Fin (n + 1) → ℝ) (b : Fin n → ℝ) (k : Fin n) :
    jacobiCoordEquiv n (a, b) ⟨2 * k.val + 1, by omega⟩ = b k := by
  change (MeasurableEquiv.piCongrLeft (fun _ => ℝ) (interleaveIndexEquiv n))
    ((MeasurableEquiv.sumPiEquivProdPi (fun _ => ℝ)).symm (a, b))
    (interleaveIndexEquiv n (.inr k)) = b k
  simp [MeasurableEquiv.piCongrLeft, MeasurableEquiv.sumPiEquivProdPi]

/-- The diagonal component of `(jacobiCoordEquiv n).symm x` reads the even entries of `x`. -/
@[simp]
theorem jacobiCoordEquiv_symm_fst (n : ℕ) (x : Fin (2 * n + 1) → ℝ) (k : Fin (n + 1)) :
    ((jacobiCoordEquiv n).symm x).1 k = x ⟨2 * k.val, by omega⟩ := by
  have hx := congrFun ((jacobiCoordEquiv n).apply_symm_apply x) ⟨2 * k.val, by omega⟩
  rw [← hx]
  exact (jacobiCoordEquiv_apply_even n _ _ k).symm

/-- The subdiagonal component of `(jacobiCoordEquiv n).symm x` reads the odd entries of `x`. -/
@[simp]
theorem jacobiCoordEquiv_symm_snd (n : ℕ) (x : Fin (2 * n + 1) → ℝ) (k : Fin n) :
    ((jacobiCoordEquiv n).symm x).2 k = x ⟨2 * k.val + 1, by omega⟩ := by
  have hx := congrFun ((jacobiCoordEquiv n).apply_symm_apply x) ⟨2 * k.val + 1, by omega⟩
  rw [← hx]
  exact (jacobiCoordEquiv_apply_odd n _ _ k).symm

/-- The first `n + 1` coordinates of `spectralCoordEquiv n (lam, q')` recover `lam`. -/
@[simp]
theorem spectralCoordEquiv_apply_left (n : ℕ) (lam : Fin (n + 1) → ℝ)
    (q' : {i : Fin (n + 1) // i ≠ Fin.last n} → ℝ) (k : Fin (n + 1)) :
    spectralCoordEquiv n (lam, q') ⟨k.val, by omega⟩ = lam k := by
  change (MeasurableEquiv.piCongrLeft (fun _ => ℝ) (spectralIndexEquiv n))
    ((MeasurableEquiv.sumPiEquivProdPi (fun _ => ℝ)).symm (lam, q'))
    (spectralIndexEquiv n (.inl k)) = lam k
  simp [MeasurableEquiv.piCongrLeft, MeasurableEquiv.sumPiEquivProdPi]

/-- The last `n` coordinates of `spectralCoordEquiv n (lam, q')` recover `q'`. -/
@[simp]
theorem spectralCoordEquiv_apply_right (n : ℕ) (lam : Fin (n + 1) → ℝ)
    (q' : {i : Fin (n + 1) // i ≠ Fin.last n} → ℝ) (j : {i : Fin (n + 1) // i ≠ Fin.last n}) :
    spectralCoordEquiv n (lam, q')
      ⟨n + 1 + j.1.val, by have : j.1.val < n := Fin.lt_last_iff_ne_last.mpr j.2; omega⟩ =
        q' j := by
  change (MeasurableEquiv.piCongrLeft (fun _ => ℝ) (spectralIndexEquiv n))
    ((MeasurableEquiv.sumPiEquivProdPi (fun _ => ℝ)).symm (lam, q'))
    (spectralIndexEquiv n (.inr j)) = q' j
  simp [MeasurableEquiv.piCongrLeft, MeasurableEquiv.sumPiEquivProdPi]

/-- The eigenvalue component of `(spectralCoordEquiv n).symm y` reads the first `n + 1` entries. -/
@[simp]
theorem spectralCoordEquiv_symm_fst (n : ℕ) (y : Fin (2 * n + 1) → ℝ) (k : Fin (n + 1)) :
    ((spectralCoordEquiv n).symm y).1 k = y ⟨k.val, by omega⟩ := by
  have hy := congrFun ((spectralCoordEquiv n).apply_symm_apply y) ⟨k.val, by omega⟩
  rw [← hy]
  exact (spectralCoordEquiv_apply_left n _ _ k).symm

/-- The spectral-weight chart component of `(spectralCoordEquiv n).symm y` reads the last `n`
entries. -/
@[simp]
theorem spectralCoordEquiv_symm_snd (n : ℕ) (y : Fin (2 * n + 1) → ℝ)
    (j : {i : Fin (n + 1) // i ≠ Fin.last n}) :
    ((spectralCoordEquiv n).symm y).2 j =
      y ⟨n + 1 + j.1.val, by have : j.1.val < n := Fin.lt_last_iff_ne_last.mpr j.2; omega⟩ := by
  have hy := congrFun ((spectralCoordEquiv n).apply_symm_apply y)
    ⟨n + 1 + j.1.val, by have : j.1.val < n := Fin.lt_last_iff_ne_last.mpr j.2; omega⟩
  rw [← hy]
  exact (spectralCoordEquiv_apply_right n _ _ j).symm

/-- `jacobiCoordEquiv` preserves Lebesgue measure. -/
theorem measurePreserving_jacobiCoordEquiv (n : ℕ) :
    MeasurePreserving (jacobiCoordEquiv n) (volume.prod volume) volume := by
  have h1 := volume_measurePreserving_sumPiEquivProdPi_symm (fun _ : Fin (n + 1) ⊕ Fin n => ℝ)
  have h2 := measurePreserving_piCongrLeft (fun _ : Fin (2 * n + 1) => (volume : Measure ℝ))
    (interleaveIndexEquiv n)
  exact h2.comp h1

/-- `spectralCoordEquiv` preserves Lebesgue measure. -/
theorem measurePreserving_spectralCoordEquiv (n : ℕ) :
    MeasurePreserving (spectralCoordEquiv n) (volume.prod volume) volume := by
  have h1 := volume_measurePreserving_sumPiEquivProdPi_symm
    (fun _ : Fin (n + 1) ⊕ {i : Fin (n + 1) // i ≠ Fin.last n} => ℝ)
  have h2 := measurePreserving_piCongrLeft (fun _ : Fin (2 * n + 1) => (volume : Measure ℝ))
    (spectralIndexEquiv n)
  exact h2.comp h1

/-- The positive-subdiagonal domain of Jacobi matrix parameters `(a, b)`. -/
def jacobiDomain (n : ℕ) : Set ((Fin (n + 1) → ℝ) × (Fin n → ℝ)) :=
  {p | ∀ j, 0 < p.2 j}

/-- Membership in `jacobiDomain n`, unfolded. -/
@[simp]
theorem mem_jacobiDomain_iff {n : ℕ} {p : (Fin (n + 1) → ℝ) × (Fin n → ℝ)} :
    p ∈ jacobiDomain n ↔ ∀ j, 0 < p.2 j := Iff.rfl

/-- The open spectral chart domain: strictly decreasing eigenvalues and spectral weights in the
interior of the standard simplex (represented in `dirichletChartRegion (Fin.last n)`). -/
def spectralDomain (n : ℕ) :
    Set ((Fin (n + 1) → ℝ) × ({i : Fin (n + 1) // i ≠ Fin.last n} → ℝ)) :=
  {p | StrictAnti p.1 ∧ p.2 ∈ dirichletChartRegion (Fin.last n)}

/-- Membership in `spectralDomain n`, unfolded. -/
@[simp]
theorem mem_spectralDomain_iff {n : ℕ}
    {p : (Fin (n + 1) → ℝ) × ({i : Fin (n + 1) // i ≠ Fin.last n} → ℝ)} :
    p ∈ spectralDomain n ↔ StrictAnti p.1 ∧ p.2 ∈ dirichletChartRegion (Fin.last n) := Iff.rfl

/-- `jacobiDomain n` is open. -/
theorem isOpen_jacobiDomain (n : ℕ) : IsOpen (jacobiDomain n) := by
  have h : jacobiDomain n = ⋂ j : Fin n, {p | 0 < p.2 j} := by
    ext p; simp [jacobiDomain]
  rw [h]
  exact isOpen_iInter_of_finite fun j =>
    isOpen_lt continuous_const ((continuous_apply j).comp continuous_snd)

/-- `jacobiDomain n` is measurable. -/
theorem measurableSet_jacobiDomain (n : ℕ) : MeasurableSet (jacobiDomain n) :=
  (isOpen_jacobiDomain n).measurableSet

/-- `spectralDomain n` is open. -/
theorem isOpen_spectralDomain (n : ℕ) : IsOpen (spectralDomain n) := by
  have h1 : IsOpen {lam : Fin (n + 1) → ℝ | StrictAnti lam} := by
    have heq : {lam : Fin (n + 1) → ℝ | StrictAnti lam} =
        ⋂ k : Fin n, {lam | lam k.succ < lam k.castSucc} := by
      ext lam
      simp only [Set.mem_ofPred_eq, Set.mem_iInter, Fin.strictAnti_iff_succ_lt]
    rw [heq]
    exact isOpen_iInter_of_finite fun k =>
      isOpen_lt (continuous_apply k.succ) (continuous_apply k.castSucc)
  exact (h1.preimage continuous_fst).inter
    ((isOpen_dirichletChartRegion (Fin.last n)).preimage continuous_snd)

/-- `spectralDomain n` is measurable. -/
theorem measurableSet_spectralDomain (n : ℕ) : MeasurableSet (spectralDomain n) :=
  (isOpen_spectralDomain n).measurableSet

/-- The spectral chart map sending Jacobi parameters `(a, b)` to the pair of ordered eigenvalues
and the first `n` spectral weights (omitting `Fin.last n`). -/
def jacobiSpectralChart (n : ℕ) (p : (Fin (n + 1) → ℝ) × (Fin n → ℝ)) :
    (Fin (n + 1) → ℝ) × ({i : Fin (n + 1) // i ≠ Fin.last n} → ℝ) :=
  (jacobiEigenvalues p.1 p.2, fun j => jacobiSpectralWeight p.1 p.2 j.1)

/-- The first component of `jacobiSpectralChart` is the ordered eigenvalue vector. -/
@[simp]
theorem jacobiSpectralChart_fst (n : ℕ) (p : (Fin (n + 1) → ℝ) × (Fin n → ℝ)) :
    (jacobiSpectralChart n p).1 = jacobiEigenvalues p.1 p.2 := by rfl

/-- The second component of `jacobiSpectralChart` records the non-last spectral weights. -/
@[simp]
theorem jacobiSpectralChart_snd (n : ℕ) (p : (Fin (n + 1) → ℝ) × (Fin n → ℝ))
    (j : {i : Fin (n + 1) // i ≠ Fin.last n}) :
    (jacobiSpectralChart n p).2 j = jacobiSpectralWeight p.1 p.2 j.1 := by rfl

/-- Reconstructing the full vector of spectral weights from the spectral chart recovers
`jacobiSpectralWeight` on `jacobiDomain n`. -/
theorem dirichletChart_jacobiSpectralChart_snd {n : ℕ} {p : (Fin (n + 1) → ℝ) × (Fin n → ℝ)}
    (hp : p ∈ jacobiDomain n) (k : Fin (n + 1)) :
    dirichletChart (Fin.last n) (jacobiSpectralChart n p).2 k = jacobiSpectralWeight p.1 p.2 k := by
  have hbne : ∀ j, p.2 j ≠ 0 := fun j => (hp j).ne'
  by_cases hk : k = Fin.last n
  · subst hk
    rw [dirichletChart_apply_self]
    have hsum := sum_jacobiSpectralWeight (a := p.1) hbne
    rw [Fintype.sum_eq_add_sum_subtype_ne _ (Fin.last n)] at hsum
    simp_rw [jacobiSpectralChart_snd]
    linarith
  · rw [dirichletChart_apply_of_ne (Fin.last n) _ hk, jacobiSpectralChart_snd]

/-- The spectral chart map is globally measurable. -/
@[fun_prop]
theorem measurable_jacobiSpectralChart (n : ℕ) : Measurable (jacobiSpectralChart n) := by
  refine measurable_jacobiEigenvalues.prodMk (measurable_pi_iff.mpr fun j => ?_)
  exact (measurable_pi_apply j.1).comp measurable_jacobiSpectralWeight

/-- The Jacobi moment map sending interleaved tridiagonal coordinates `x` to the first `2 * n + 1`
moments `r ↦ (J ^ (r + 1)) 0 0`. -/
def jacobiMomentMap (n : ℕ) (x : Fin (2 * n + 1) → ℝ) (r : Fin (2 * n + 1)) : ℝ :=
  let p := (jacobiCoordEquiv n).symm x
  (jacobiMatrix p.1 p.2 ^ (r.val + 1)) 0 0

/-- The spectral moment map sending spectral chart coordinates `y` to the first `2 * n + 1`
moments `r ↦ ∑ k, dirichletChart (Fin.last n) q' k * lam k ^ (r + 1)`. -/
def spectralMomentMap (n : ℕ) (y : Fin (2 * n + 1) → ℝ) (r : Fin (2 * n + 1)) : ℝ :=
  let p := (spectralCoordEquiv n).symm y
  ∑ k : Fin (n + 1), dirichletChart (Fin.last n) p.2 k * p.1 k ^ (r.val + 1)

/-- Coordinate formula for `spectralMomentMap`. -/
theorem spectralMomentMap_apply (n : ℕ) (y : Fin (2 * n + 1) → ℝ) (r : Fin (2 * n + 1)) :
    spectralMomentMap n y r =
      ∑ k : Fin (n + 1), dirichletChart (Fin.last n) ((spectralCoordEquiv n).symm y).2 k *
        ((spectralCoordEquiv n).symm y).1 k ^ (r.val + 1) := by rfl

/-- The Jacobi and spectral moment maps commute with `jacobiSpectralChart` on `jacobiDomain n`. -/
theorem spectralMomentMap_jacobiSpectralChart {n : ℕ} {p : (Fin (n + 1) → ℝ) × (Fin n → ℝ)}
    (hp : p ∈ jacobiDomain n) :
    spectralMomentMap n (spectralCoordEquiv n (jacobiSpectralChart n p)) =
      jacobiMomentMap n (jacobiCoordEquiv n p) := by
  have hbne : ∀ j, p.2 j ≠ 0 := fun j => (hp j).ne'
  funext r
  simp only [spectralMomentMap, jacobiMomentMap, MeasurableEquiv.symm_apply_apply]
  rw [jacobiMatrix_pow_zero_zero hbne (r.val + 1)]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [dirichletChart_jacobiSpectralChart_snd hp k, jacobiSpectralChart_fst]

/-! ### Triangular structure and Jacobian of the Jacobi moment map -/

/-- Entry formula for `jacobiMatrix a b i r` via the public entry lemmas. -/
private theorem jacobiMatrix_apply_eq {n : ℕ} (a : Fin (n + 1) → ℝ) (b : Fin n → ℝ)
    (i r : Fin (n + 1)) :
    jacobiMatrix a b i r =
      if i = r then a i
      else if h : i.val + 1 = r.val then b ⟨i.val, by omega⟩
      else if h : r.val + 1 = i.val then b ⟨r.val, by omega⟩
      else 0 := by
  by_cases h0 : i = r
  · subst h0; rw [ite_eq_left rfl, jacobiMatrix_apply_self]
  · rw [ite_eq_right h0]
    by_cases h1 : i.val + 1 = r.val
    · rw [dite_eq_left h1]
      let k : Fin n := ⟨i.val, by omega⟩
      have hi : i = k.castSucc := Fin.ext rfl
      have hr : r = k.succ := Fin.ext (by simp [k, h1])
      rw [show jacobiMatrix a b i r = jacobiMatrix a b k.castSucc k.succ by rw [hi, hr],
        jacobiMatrix_apply_castSucc_succ]
    · rw [dite_eq_right h1]
      by_cases h2 : r.val + 1 = i.val
      · rw [dite_eq_left h2]
        let k : Fin n := ⟨r.val, by omega⟩
        have hr : r = k.castSucc := Fin.ext rfl
        have hi : i = k.succ := Fin.ext (by simp [k, h2])
        rw [show jacobiMatrix a b i r = jacobiMatrix a b k.succ k.castSucc by rw [hi, hr],
          jacobiMatrix_apply_succ_castSucc]
      · rw [dite_eq_right h2]
        rcases lt_or_gt_of_ne (Fin.val_ne_of_ne h0) with hlt | hgt
        · exact jacobiMatrix_apply_of_add_one_lt_right a b (by omega)
        · exact jacobiMatrix_apply_of_add_one_lt_left a b (by omega)

/-- Entrywise expansion of `(J ^ (m + 1)) i 0` using the tridiagonal structure of `J`. -/
private theorem jacobiMatrix_pow_succ_apply_zero {n : ℕ} (a : Fin (n + 1) → ℝ) (b : Fin n → ℝ)
    (m : ℕ) (i : Fin (n + 1)) :
    (jacobiMatrix a b ^ (m + 1)) i 0 =
      a i * (jacobiMatrix a b ^ m) i 0 +
      (if h : i.val < n then
        b ⟨i.val, h⟩ * (jacobiMatrix a b ^ m) ⟨i.val + 1, by omega⟩ 0 else 0) +
      (if h : 0 < i.val then
        b ⟨i.val - 1, by omega⟩ * (jacobiMatrix a b ^ m) ⟨i.val - 1, by omega⟩ 0 else 0) := by
  rw [pow_succ', Matrix.mul_apply]
  have hterm : ∀ r : Fin (n + 1), jacobiMatrix a b i r * (jacobiMatrix a b ^ m) r 0 =
      (if r = i then a i * (jacobiMatrix a b ^ m) i 0 else 0) +
      (if h : i.val < n then
        if r = ⟨i.val + 1, by omega⟩ then
          b ⟨i.val, h⟩ * (jacobiMatrix a b ^ m) ⟨i.val + 1, by omega⟩ 0 else 0 else 0) +
      (if h : 0 < i.val then
        if r = ⟨i.val - 1, by omega⟩ then
          b ⟨i.val - 1, by omega⟩ *
            (jacobiMatrix a b ^ m) ⟨i.val - 1, by omega⟩ 0 else 0 else 0) := by
    intro r
    rw [jacobiMatrix_apply_eq]
    split_ifs <;>
      simp only [Fin.ext_iff] at * <;>
      first
      | omega
      | (simp only [add_zero]; exact congrArg (a i * ·)
          (congrArg (fun j => (jacobiMatrix a b ^ m) j 0) (Fin.ext (by omega))))
      | (simp only [zero_add, add_zero]; exact congrArg₂ (· * ·)
          (congrArg b (Fin.ext (by omega)))
          (congrArg (fun j => (jacobiMatrix a b ^ m) j 0) (Fin.ext (by omega))))
      | simp
  simp_rw [hterm, Finset.sum_add_distrib]
  congr 1
  · congr 1
    · simp
    · by_cases h : i.val < n
      · rw [dite_eq_left h]; simp_rw [dite_eq_left h]; simp
      · rw [dite_eq_right h]; simp_rw [dite_eq_right h]; simp
  · by_cases h : 0 < i.val
    · rw [dite_eq_left h]; simp_rw [dite_eq_left h]; simp
    · rw [dite_eq_right h]; simp_rw [dite_eq_right h]; simp

/-- `(jacobiMatrix a b ^ m) i 0` depends only on interleaved coordinates `< m + i.val`. -/
private theorem jacobiMatrix_pow_eq_of_eq_lt {n : ℕ} {a a' : Fin (n + 1) → ℝ} {b b' : Fin n → ℝ}
    (m : ℕ) (i : Fin (n + 1))
    (ha : ∀ j : Fin (n + 1), 2 * j.val < m + i.val → a j = a' j)
    (hb : ∀ j : Fin n, 2 * j.val + 1 < m + i.val → b j = b' j) :
    (jacobiMatrix a b ^ m) i 0 = (jacobiMatrix a' b' ^ m) i 0 := by
  induction m generalizing i with
  | zero => simp
  | succ m ih =>
      rw [jacobiMatrix_pow_succ_apply_zero, jacobiMatrix_pow_succ_apply_zero]
      have h1 : a i * (jacobiMatrix a b ^ m) i 0 = a' i * (jacobiMatrix a' b' ^ m) i 0 := by
        by_cases hmi : m < i.val
        · rw [jacobiMatrix_pow_apply_zero_of_lt a b m hmi,
            jacobiMatrix_pow_apply_zero_of_lt a' b' m hmi, mul_zero, mul_zero]
        · rw [ha i (by omega),
            ih i (fun j hj => ha j (by omega)) (fun j hj => hb j (by omega))]
      have h2 : (if h : i.val < n then
          b ⟨i.val, h⟩ * (jacobiMatrix a b ^ m) ⟨i.val + 1, by omega⟩ 0 else 0) =
          (if h : i.val < n then
          b' ⟨i.val, h⟩ * (jacobiMatrix a' b' ^ m) ⟨i.val + 1, by omega⟩ 0 else 0) := by
        by_cases h : i.val < n
        · rw [dite_eq_left h, dite_eq_left h]
          by_cases hmi : m < i.val + 1
          · rw [jacobiMatrix_pow_apply_zero_of_lt a b m (i := ⟨i.val + 1, by omega⟩) hmi,
              jacobiMatrix_pow_apply_zero_of_lt a' b' m (i := ⟨i.val + 1, by omega⟩) hmi,
              mul_zero, mul_zero]
          · rw [hb ⟨i.val, h⟩ (by change 2 * i.val + 1 < _; omega),
              ih ⟨i.val + 1, by omega⟩
                (fun j hj => ha j (by dsimp only at hj; omega))
                (fun j hj => hb j (by dsimp only at hj; omega))]
        · rw [dite_eq_right h, dite_eq_right h]
      have h3 : (if h : 0 < i.val then
          b ⟨i.val - 1, by omega⟩ * (jacobiMatrix a b ^ m) ⟨i.val - 1, by omega⟩ 0 else 0) =
          (if h : 0 < i.val then
          b' ⟨i.val - 1, by omega⟩ * (jacobiMatrix a' b' ^ m) ⟨i.val - 1, by omega⟩ 0 else 0) := by
        by_cases h : 0 < i.val
        · rw [dite_eq_left h, dite_eq_left h]
          by_cases hmi : m < i.val - 1
          · rw [jacobiMatrix_pow_apply_zero_of_lt a b m (i := ⟨i.val - 1, by omega⟩) hmi,
              jacobiMatrix_pow_apply_zero_of_lt a' b' m (i := ⟨i.val - 1, by omega⟩) hmi,
              mul_zero, mul_zero]
          · rw [hb ⟨i.val - 1, by omega⟩ (by change 2 * (i.val - 1) + 1 < _; omega),
              ih ⟨i.val - 1, by omega⟩
                (fun j hj => ha j (by dsimp only at hj; omega))
                (fun j hj => hb j (by dsimp only at hj; omega))]
        · rw [dite_eq_right h, dite_eq_right h]
      rw [h1, h2, h3]

/-- Leading linear dependence of `(J ^ m) i 0` on `a k` when `m + i = 2 * k + 1` and `i ≤ k`. -/
private theorem jacobiMatrix_pow_sub_even {n : ℕ} {a a' : Fin (n + 1) → ℝ} {b b' : Fin n → ℝ}
    (k : Fin (n + 1)) (m : ℕ) (i : Fin (n + 1))
    (hmi : m + i.val = 2 * k.val + 1) (hik : i.val ≤ k.val)
    (ha : ∀ j : Fin (n + 1), j.val < k.val → a j = a' j)
    (hb : ∀ j : Fin n, j.val < k.val → b j = b' j) :
    (jacobiMatrix a' b' ^ m) i 0 - (jacobiMatrix a b ^ m) i 0 =
      (∏ j ∈ Finset.univ.filter (fun j : Fin n => j.val < k.val), b j) *
      (∏ j ∈ Finset.univ.filter (fun j : Fin n => i.val ≤ j.val ∧ j.val < k.val), b j) *
      (a' k - a k) := by
  induction m generalizing i with
  | zero => omega
  | succ m ih =>
      rw [jacobiMatrix_pow_succ_apply_zero a' b', jacobiMatrix_pow_succ_apply_zero a b]
      have hprev : (jacobiMatrix a' b' ^ m) i 0 = (jacobiMatrix a b ^ m) i 0 :=
        (jacobiMatrix_pow_eq_of_eq_lt m i
          (fun j hj => ha j (by omega)) (fun j hj => hb j (by omega))).symm
      have hdn : (if h : 0 < i.val then
          b' ⟨i.val - 1, by omega⟩ * (jacobiMatrix a' b' ^ m) ⟨i.val - 1, by omega⟩ 0 else 0) =
          (if h : 0 < i.val then
          b ⟨i.val - 1, by omega⟩ * (jacobiMatrix a b ^ m) ⟨i.val - 1, by omega⟩ 0 else 0) := by
        by_cases h : 0 < i.val
        · rw [dite_eq_left h, dite_eq_left h,
            (hb ⟨i.val - 1, by omega⟩ (by change i.val - 1 < _; omega)).symm,
            (jacobiMatrix_pow_eq_of_eq_lt m ⟨i.val - 1, by omega⟩
              (fun j hj => ha j (by dsimp only at hj; omega))
              (fun j hj => hb j (by dsimp only at hj; omega))).symm]
        · rw [dite_eq_right h, dite_eq_right h]
      by_cases heq : i.val = k.val
      · have hik_eq : i = k := Fin.ext heq
        subst hik_eq
        have hmk : m = i.val := by omega
        subst hmk
        have hup : (if h : i.val < n then
            b' ⟨i.val, h⟩ * (jacobiMatrix a' b' ^ i.val) ⟨i.val + 1, by omega⟩ 0 else 0) = 0 ∧
            (if h : i.val < n then
            b ⟨i.val, h⟩ * (jacobiMatrix a b ^ i.val) ⟨i.val + 1, by omega⟩ 0 else 0) = 0 := by
          by_cases h : i.val < n
          · rw [dite_eq_left h, dite_eq_left h,
              jacobiMatrix_pow_apply_zero_of_lt a' b' i.val (i := ⟨i.val + 1, by omega⟩) (by simp),
              jacobiMatrix_pow_apply_zero_of_lt a b i.val (i := ⟨i.val + 1, by omega⟩) (by simp),
              mul_zero, mul_zero]
            exact ⟨rfl, rfl⟩
          · rw [dite_eq_right h, dite_eq_right h]; exact ⟨rfl, rfl⟩
        have hemp : Finset.univ.filter (fun j : Fin n => i.val ≤ j.val ∧ j.val < i.val) = ∅ := by
          ext j; simp
        rw [hup.1, hup.2, hprev, hdn, hemp, Finset.prod_empty, mul_one,
          jacobiMatrix_pow_apply_zero_self]
        ring
      · have hilt : i.val < k.val := by omega
        have hin : i.val < n := by omega
        have hai : a' i = a i := (ha i hilt).symm
        have hbi : b' ⟨i.val, hin⟩ = b ⟨i.val, hin⟩ := (hb ⟨i.val, hin⟩ hilt).symm
        have hih := ih ⟨i.val + 1, by omega⟩ (by simp; omega) (by simp; omega)
        have hsplit : ∏ j ∈ Finset.univ.filter (fun j : Fin n => i.val ≤ j.val ∧ j.val < k.val),
            b j = b ⟨i.val, hin⟩ *
              ∏ j ∈ Finset.univ.filter (fun j : Fin n => i.val + 1 ≤ j.val ∧ j.val < k.val),
                b j := by
          rw [← Finset.prod_insert (a := (⟨i.val, hin⟩ : Fin n)) (by simp)]
          refine Finset.prod_congr ?_ fun _ _ => rfl
          ext j
          simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert, Fin.ext_iff]
          omega
        rw [dite_eq_left hin, dite_eq_left hin, hprev, hai, hbi, hdn, hsplit]
        calc _ = b ⟨i.val, hin⟩ * ((jacobiMatrix a' b' ^ m) ⟨i.val + 1, by omega⟩ 0 -
              (jacobiMatrix a b ^ m) ⟨i.val + 1, by omega⟩ 0) := by ring
          _ = _ := by rw [hih]; ring

/-- Leading quadratic dependence of `(J ^ m) i 0` on `b k` when `m + i = 2 * k + 2` and `i ≤ k`. -/
private theorem jacobiMatrix_pow_sub_odd {n : ℕ} {a a' : Fin (n + 1) → ℝ} {b b' : Fin n → ℝ}
    (k : Fin n) (m : ℕ) (i : Fin (n + 1))
    (hmi : m + i.val = 2 * k.val + 2) (hik : i.val ≤ k.val)
    (ha : ∀ j : Fin (n + 1), j.val ≤ k.val → a j = a' j)
    (hb : ∀ j : Fin n, j.val < k.val → b j = b' j) :
    (jacobiMatrix a' b' ^ m) i 0 - (jacobiMatrix a b ^ m) i 0 =
      (∏ j ∈ Finset.univ.filter (fun j : Fin n => j.val < k.val), b j) *
      (∏ j ∈ Finset.univ.filter (fun j : Fin n => i.val ≤ j.val ∧ j.val < k.val), b j) *
      (b' k ^ 2 - b k ^ 2) := by
  induction m generalizing i with
  | zero => omega
  | succ m ih =>
      rw [jacobiMatrix_pow_succ_apply_zero a' b', jacobiMatrix_pow_succ_apply_zero a b]
      have hin : i.val < n := by omega
      have hai : a' i = a i := (ha i hik).symm
      have hprev : (jacobiMatrix a' b' ^ m) i 0 = (jacobiMatrix a b ^ m) i 0 :=
        (jacobiMatrix_pow_eq_of_eq_lt m i
          (fun j hj => ha j (by omega)) (fun j hj => hb j (by omega))).symm
      have hdn : (if h : 0 < i.val then
          b' ⟨i.val - 1, by omega⟩ * (jacobiMatrix a' b' ^ m) ⟨i.val - 1, by omega⟩ 0 else 0) =
          (if h : 0 < i.val then
          b ⟨i.val - 1, by omega⟩ * (jacobiMatrix a b ^ m) ⟨i.val - 1, by omega⟩ 0 else 0) := by
        by_cases h : 0 < i.val
        · rw [dite_eq_left h, dite_eq_left h,
            (hb ⟨i.val - 1, by omega⟩ (by change i.val - 1 < _; omega)).symm,
            (jacobiMatrix_pow_eq_of_eq_lt m ⟨i.val - 1, by omega⟩
              (fun j hj => ha j (by dsimp only at hj; omega))
              (fun j hj => hb j (by dsimp only at hj; omega))).symm]
        · rw [dite_eq_right h, dite_eq_right h]
      by_cases heq : i.val = k.val
      · have hmk : m = k.val + 1 := by omega
        subst hmk
        have hi_eq : (⟨i.val, hin⟩ : Fin n) = k := Fin.ext heq
        have hi1_eq : (⟨i.val + 1, by omega⟩ : Fin (n + 1)) = k.succ := Fin.ext (by simp [heq])
        have hset : Finset.univ.filter (fun j : Fin n => j.val < k.val + 1) =
            insert k (Finset.univ.filter (fun j : Fin n => j.val < k.val)) := by
          ext j
          simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert, Fin.ext_iff]
          omega
        have hself : (jacobiMatrix a b ^ (k.val + 1)) k.succ 0 =
            b k * ∏ j ∈ Finset.univ.filter (fun j : Fin n => j.val < k.val), b j := by
          have h1 := jacobiMatrix_pow_apply_zero_self a b k.succ
          simp only [Fin.val_succ] at h1
          rw [h1, hset, Finset.prod_insert (by simp)]
        have hself' : (jacobiMatrix a' b' ^ (k.val + 1)) k.succ 0 =
            b' k * ∏ j ∈ Finset.univ.filter (fun j : Fin n => j.val < k.val), b j := by
          have h1 := jacobiMatrix_pow_apply_zero_self a' b' k.succ
          simp only [Fin.val_succ] at h1
          rw [h1, hset, Finset.prod_insert (by simp)]
          congr 1
          exact Finset.prod_congr rfl fun j hj => (hb j (Finset.mem_filter.mp hj).2).symm
        have hemp : Finset.univ.filter (fun j : Fin n => i.val ≤ j.val ∧ j.val < k.val) = ∅ := by
          ext j; simp; omega
        rw [dite_eq_left hin, dite_eq_left hin, hi_eq, hi1_eq, hai, hprev, hdn, hself, hself',
          hemp, Finset.prod_empty, mul_one]
        ring
      · have hilt : i.val < k.val := by omega
        have hbi : b' ⟨i.val, hin⟩ = b ⟨i.val, hin⟩ := (hb ⟨i.val, hin⟩ hilt).symm
        have hih := ih ⟨i.val + 1, by omega⟩ (by simp; omega) (by simp; omega)
        have hsplit : ∏ j ∈ Finset.univ.filter (fun j : Fin n => i.val ≤ j.val ∧ j.val < k.val),
            b j = b ⟨i.val, hin⟩ *
              ∏ j ∈ Finset.univ.filter (fun j : Fin n => i.val + 1 ≤ j.val ∧ j.val < k.val),
                b j := by
          rw [← Finset.prod_insert (a := (⟨i.val, hin⟩ : Fin n)) (by simp)]
          refine Finset.prod_congr ?_ fun _ _ => rfl
          ext j
          simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert, Fin.ext_iff]
          omega
        rw [dite_eq_left hin, dite_eq_left hin, hprev, hai, hbi, hdn, hsplit]
        calc _ = b ⟨i.val, hin⟩ * ((jacobiMatrix a' b' ^ m) ⟨i.val + 1, by omega⟩ 0 -
              (jacobiMatrix a b ^ m) ⟨i.val + 1, by omega⟩ 0) := by ring
          _ = _ := by rw [hih]; ring

/-- Specialization of `jacobiMatrix_pow_sub_even` at `i = 0`. -/
private theorem jacobiMomentMap_sub_even {n : ℕ} {x x' : Fin (2 * n + 1) → ℝ} (k : Fin (n + 1))
    (h : ∀ c : Fin (2 * n + 1), c.val < 2 * k.val → x c = x' c) :
    jacobiMomentMap n x' ⟨2 * k.val, by omega⟩ - jacobiMomentMap n x ⟨2 * k.val, by omega⟩ =
      (∏ j ∈ Finset.univ.filter (fun j : Fin n => j.val < k.val),
        ((jacobiCoordEquiv n).symm x).2 j) ^ 2 *
      (x' ⟨2 * k.val, by omega⟩ - x ⟨2 * k.val, by omega⟩) := by
  have h0 := jacobiMatrix_pow_sub_even (a := ((jacobiCoordEquiv n).symm x).1)
    (a' := ((jacobiCoordEquiv n).symm x').1) (b := ((jacobiCoordEquiv n).symm x).2)
    (b' := ((jacobiCoordEquiv n).symm x').2) k (2 * k.val + 1) 0 (by simp) (by simp)
    (fun j hj => by simpa using h ⟨2 * j.val, by omega⟩ (by simp; omega))
    (fun j hj => by simpa using h ⟨2 * j.val + 1, by omega⟩ (by simp; omega))
  simp only [jacobiMomentMap, Fin.val_zero, zero_le, true_and, jacobiCoordEquiv_symm_fst] at h0 ⊢
  rw [h0, ← sq]

/-- Specialization of `jacobiMatrix_pow_sub_odd` at `i = 0`. -/
private theorem jacobiMomentMap_sub_odd {n : ℕ} {x x' : Fin (2 * n + 1) → ℝ} (k : Fin n)
    (h : ∀ c : Fin (2 * n + 1), c.val < 2 * k.val + 1 → x c = x' c) :
    jacobiMomentMap n x' ⟨2 * k.val + 1, by omega⟩ -
        jacobiMomentMap n x ⟨2 * k.val + 1, by omega⟩ =
      (∏ j ∈ Finset.univ.filter (fun j : Fin n => j.val < k.val),
        ((jacobiCoordEquiv n).symm x).2 j) ^ 2 *
      (x' ⟨2 * k.val + 1, by omega⟩ ^ 2 - x ⟨2 * k.val + 1, by omega⟩ ^ 2) := by
  have h0 := jacobiMatrix_pow_sub_odd (a := ((jacobiCoordEquiv n).symm x).1)
    (a' := ((jacobiCoordEquiv n).symm x').1) (b := ((jacobiCoordEquiv n).symm x).2)
    (b' := ((jacobiCoordEquiv n).symm x').2) k (2 * k.val + 2) 0 (by simp) (by simp)
    (fun j hj => by simpa using h ⟨2 * j.val, by omega⟩ (by simp; omega))
    (fun j hj => by simpa using h ⟨2 * j.val + 1, by omega⟩ (by simp; omega))
  simp only [jacobiMomentMap, Fin.val_zero, zero_le, true_and, jacobiCoordEquiv_symm_snd] at h0 ⊢
  rw [h0, ← sq]

/-- The Jacobi moment map is injective on the positive-subdiagonal image
`jacobiCoordEquiv n '' jacobiDomain n`. -/
theorem injOn_jacobiMomentMap (n : ℕ) :
    InjOn (jacobiMomentMap n) (jacobiCoordEquiv n '' jacobiDomain n) := by
  rintro x ⟨p, hp, rfl⟩ x' ⟨p', hp', rfl⟩ hΦ
  have hcoord : ∀ r : ℕ, ∀ hr : r < 2 * n + 1,
      jacobiCoordEquiv n p ⟨r, hr⟩ = jacobiCoordEquiv n p' ⟨r, hr⟩ := by
    intro r
    induction r using Nat.strong_induction_on with
    | ind r ih =>
        intro hr
        have hlt : ∀ c : Fin (2 * n + 1), c.val < r →
            jacobiCoordEquiv n p c = jacobiCoordEquiv n p' c := fun c hc => ih c.val hc c.isLt
        by_cases heven : r % 2 = 0
        · let k : Fin (n + 1) := ⟨r / 2, by omega⟩
          have hrk : (⟨r, hr⟩ : Fin (2 * n + 1)) = ⟨2 * k.val, by omega⟩ :=
            Fin.ext (by simp [k]; omega)
          have hsub := jacobiMomentMap_sub_even (x := jacobiCoordEquiv n p)
            (x' := jacobiCoordEquiv n p') k (fun c hc => hlt c (by simp [k] at hc; omega))
          have hzero : jacobiMomentMap n (jacobiCoordEquiv n p') ⟨2 * k.val, by omega⟩ -
              jacobiMomentMap n (jacobiCoordEquiv n p) ⟨2 * k.val, by omega⟩ = 0 := by
            rw [congrFun hΦ _]; ring
          rw [hzero, MeasurableEquiv.symm_apply_apply] at hsub
          have hprod : (∏ j ∈ Finset.univ.filter (fun j : Fin n => j.val < k.val), p.2 j) ^ 2 ≠ 0 :=
            pow_ne_zero 2 (Finset.prod_ne_zero_iff.mpr fun j _ => (hp j).ne')
          rw [hrk]
          linarith [(mul_eq_zero.mp hsub.symm).resolve_left hprod]
        · let k : Fin n := ⟨r / 2, by omega⟩
          have hrk : (⟨r, hr⟩ : Fin (2 * n + 1)) = ⟨2 * k.val + 1, by omega⟩ :=
            Fin.ext (by simp [k]; omega)
          have hsub := jacobiMomentMap_sub_odd (x := jacobiCoordEquiv n p)
            (x' := jacobiCoordEquiv n p') k (fun c hc => hlt c (by simp [k] at hc; omega))
          have hzero : jacobiMomentMap n (jacobiCoordEquiv n p') ⟨2 * k.val + 1, by omega⟩ -
              jacobiMomentMap n (jacobiCoordEquiv n p) ⟨2 * k.val + 1, by omega⟩ = 0 := by
            rw [congrFun hΦ _]; ring
          rw [hzero, MeasurableEquiv.symm_apply_apply] at hsub
          have hprod : (∏ j ∈ Finset.univ.filter (fun j : Fin n => j.val < k.val), p.2 j) ^ 2 ≠ 0 :=
            pow_ne_zero 2 (Finset.prod_ne_zero_iff.mpr fun j _ => (hp j).ne')
          have hsq : jacobiCoordEquiv n p' ⟨2 * k.val + 1, by omega⟩ ^ 2 =
              jacobiCoordEquiv n p ⟨2 * k.val + 1, by omega⟩ ^ 2 := by
            linarith [(mul_eq_zero.mp hsub.symm).resolve_left hprod]
          rw [jacobiCoordEquiv_apply_odd, jacobiCoordEquiv_apply_odd] at hsq
          rw [hrk, jacobiCoordEquiv_apply_odd, jacobiCoordEquiv_apply_odd]
          exact ((sq_eq_sq₀ (hp' k).le (hp k).le).mp hsq).symm
  funext r
  exact hcoord r.val r.isLt

/-- Every entry of `(jacobiMatrix p.1 p.2 ^ m)` is differentiable in the interleaved coordinates. -/
private theorem differentiable_jacobiMatrix_pow_entry (n : ℕ) (m : ℕ) (i j : Fin (n + 1)) :
    Differentiable ℝ fun x : Fin (2 * n + 1) → ℝ =>
      (jacobiMatrix ((jacobiCoordEquiv n).symm x).1 ((jacobiCoordEquiv n).symm x).2 ^ m) i j := by
  induction m generalizing i j with
  | zero => simp
  | succ m ih =>
      simp_rw [pow_succ', Matrix.mul_apply]
      refine Differentiable.fun_sum fun r _ => ?_
      have hJ : Differentiable ℝ fun x : Fin (2 * n + 1) → ℝ =>
          jacobiMatrix ((jacobiCoordEquiv n).symm x).1 ((jacobiCoordEquiv n).symm x).2 i r := by
        simp_rw [jacobiMatrix_apply_eq]
        split_ifs
        · simpa using differentiable_apply (⟨2 * i.val, by omega⟩ : Fin (2 * n + 1))
        · simpa using differentiable_apply (⟨2 * i.val + 1, by omega⟩ : Fin (2 * n + 1))
        · simpa using differentiable_apply (⟨2 * r.val + 1, by omega⟩ : Fin (2 * n + 1))
        · exact differentiable_const 0
      exact hJ.mul (ih r j)

/-- The Jacobi moment map is globally differentiable. -/
theorem differentiable_jacobiMomentMap (n : ℕ) : Differentiable ℝ (jacobiMomentMap n) := by
  rw [differentiable_pi]
  intro r
  exact differentiable_jacobiMatrix_pow_entry n (r.val + 1) 0 0

/-- The `(r, j)` matrix entry of `fderiv ℝ f x` equals the directional derivative along `update`. -/
private theorem toMatrix'_fderiv_apply {ι : Type*} [Fintype ι] [DecidableEq ι]
    {f : (ι → ℝ) → (ι → ℝ)} {x : ι → ℝ} (hf : DifferentiableAt ℝ f x) (r j : ι) :
    LinearMap.toMatrix' (fderiv ℝ f x : (ι → ℝ) →ₗ[ℝ] (ι → ℝ)) r j =
      deriv (fun t => f (Function.update x j t) r) (x j) := by
  have hfx : HasFDerivAt f (fderiv ℝ f x) (Function.update x j (x j)) := by
    simpa [Function.update_eq_self] using hf.hasFDerivAt
  have hcomp := hfx.comp_hasDerivAt (x j) (hasDerivAt_update x j (x j))
  have hcoord := (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : ι => ℝ) r).hasFDerivAt
    |>.comp_hasDerivAt (x j) hcomp
  simpa [LinearMap.toMatrix'_apply, Function.comp_def] using hcoord.deriv.symm

/-- Product-of-prefixes algebraic identity for the lower-triangular diagonal product of `DΦ`. -/
private theorem prod_jacobi_diagonal (n : ℕ) (b : Fin n → ℝ) :
    (∏ k : Fin (n + 1), (∏ j ∈ Finset.univ.filter (fun j : Fin n => j.val < k.val), b j) ^ 2) *
      (∏ k : Fin n,
        2 * (∏ j ∈ Finset.univ.filter (fun j : Fin n => j.val < k.val), b j) ^ 2 * b k) =
      2 ^ n * ∏ j : Fin n, b j ^ (4 * (n - j.val) - 1) := by
  have h1 : ∏ k : Fin (n + 1),
      (∏ j ∈ Finset.univ.filter (fun j : Fin n => j.val < k.val), b j) ^ 2 =
      ∏ j : Fin n, b j ^ (2 * (n - j.val)) := by
    simp_rw [← Finset.prod_pow, Finset.prod_filter]
    rw [Finset.prod_comm]
    refine Finset.prod_congr rfl fun j _ => ?_
    rw [← Finset.prod_filter, Finset.prod_const, ← pow_mul]
    congr 1
    have hbij : (Finset.univ.filter (fun k : Fin (n + 1) => j.val < k.val)) =
        Finset.Ioi j.castSucc := by
      ext k; simp [Fin.lt_def]
    rw [hbij, Fin.card_Ioi]
    simp [mul_comm]
  have h2 : ∏ k : Fin n,
      (∏ j ∈ Finset.univ.filter (fun j : Fin n => j.val < k.val), b j) ^ 2 =
      ∏ j : Fin n, b j ^ (2 * (n - 1 - j.val)) := by
    simp_rw [← Finset.prod_pow, Finset.prod_filter]
    rw [Finset.prod_comm]
    refine Finset.prod_congr rfl fun j _ => ?_
    rw [← Finset.prod_filter, Finset.prod_const, ← pow_mul]
    congr 1
    have hbij : (Finset.univ.filter (fun k : Fin n => j.val < k.val)) = Finset.Ioi j := by
      ext k; simp
    rw [hbij, Fin.card_Ioi, mul_comm]
  have hsplit : ∏ k : Fin n,
      (2 * (∏ j ∈ Finset.univ.filter (fun j : Fin n => j.val < k.val), b j) ^ 2 * b k) =
      2 ^ n * (∏ k : Fin n, (∏ j ∈ Finset.univ.filter (fun j : Fin n => j.val < k.val), b j) ^ 2) *
        ∏ k : Fin n, b k := by
    simp_rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  rw [hsplit, h1, h2]
  calc (∏ j : Fin n, b j ^ (2 * (n - j.val))) *
        (2 ^ n * (∏ j : Fin n, b j ^ (2 * (n - 1 - j.val))) * ∏ j : Fin n, b j)
      = 2 ^ n * ((∏ j : Fin n, b j ^ (2 * (n - j.val))) *
          (∏ j : Fin n, b j ^ (2 * (n - 1 - j.val))) * ∏ j : Fin n, b j) := by ring
    _ = 2 ^ n * ∏ j : Fin n, b j ^ (4 * (n - j.val) - 1) := by
        congr 1
        rw [← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
        refine Finset.prod_congr rfl fun j _ => ?_
        rw [← pow_add, ← pow_succ]
        congr 1; omega

/-- **Jacobian determinant of the Jacobi moment map**: at `x = jacobiCoordEquiv n (a, b)`, the
Fréchet derivative is lower triangular with determinant `2 ^ n * ∏ j, b j ^ (4 * (n - j) - 1)`. -/
theorem det_fderiv_jacobiMomentMap (n : ℕ) (a : Fin (n + 1) → ℝ) (b : Fin n → ℝ) :
    (fderiv ℝ (jacobiMomentMap n) (jacobiCoordEquiv n (a, b))).det =
      2 ^ n * ∏ j : Fin n, b j ^ (4 * (n - j.val) - 1) := by
  let x := jacobiCoordEquiv n (a, b)
  let M := LinearMap.toMatrix'
    (fderiv ℝ (jacobiMomentMap n) x : (Fin (2 * n + 1) → ℝ) →ₗ[ℝ] (Fin (2 * n + 1) → ℝ))
  have hlt : M.IsLowerTriangular := by
    intro r j hrj
    have hrj' : r.val < j.val := hrj
    dsimp only [M]
    rw [toMatrix'_fderiv_apply (differentiable_jacobiMomentMap n x) r j]
    have hconst : ∀ t, jacobiMomentMap n (Function.update x j t) r = jacobiMomentMap n x r := by
      intro t
      exact (jacobiMatrix_pow_eq_of_eq_lt (r.val + 1) 0
        (fun k hk => by
          simp only [jacobiCoordEquiv_symm_fst]
          have hne : (⟨2 * k.val, by omega⟩ : Fin (2 * n + 1)) ≠ j := by
            intro heq
            have hv : 2 * k.val = j.val := congrArg Fin.val heq
            simp only [Fin.val_zero, add_zero] at hk
            omega
          exact (Function.update_of_ne hne t x).symm)
        (fun k hk => by
          simp only [jacobiCoordEquiv_symm_snd]
          have hne : (⟨2 * k.val + 1, by omega⟩ : Fin (2 * n + 1)) ≠ j := by
            intro heq
            have hv : 2 * k.val + 1 = j.val := congrArg Fin.val heq
            simp only [Fin.val_zero, add_zero] at hk
            omega
          exact (Function.update_of_ne hne t x).symm)).symm
    simp_rw [hconst]
    exact deriv_const (x j) _
  have hdiag_even : ∀ k : Fin (n + 1), M ⟨2 * k.val, by omega⟩ ⟨2 * k.val, by omega⟩ =
      (∏ j ∈ Finset.univ.filter (fun j : Fin n => j.val < k.val), b j) ^ 2 := by
    intro k
    dsimp only [M]
    rw [toMatrix'_fderiv_apply (differentiable_jacobiMomentMap n x) _ _]
    have hfn : (fun t => jacobiMomentMap n (Function.update x ⟨2 * k.val, by omega⟩ t)
        ⟨2 * k.val, by omega⟩) =
        fun t => jacobiMomentMap n x ⟨2 * k.val, by omega⟩ +
          (∏ j ∈ Finset.univ.filter (fun j : Fin n => j.val < k.val), b j) ^ 2 *
            (t - x ⟨2 * k.val, by omega⟩) := by
      funext t
      have hsub := jacobiMomentMap_sub_even (x := x)
        (x' := Function.update x ⟨2 * k.val, by omega⟩ t)
        k fun c hc => (Function.update_of_ne (by intro heq; subst heq; simp at hc) t x).symm
      simp only [x, MeasurableEquiv.symm_apply_apply, Function.update_self] at hsub
      linarith
    rw [hfn]
    have hd := (((hasDerivAt_id' (x ⟨2 * k.val, by omega⟩)).sub_const
      (x ⟨2 * k.val, by omega⟩)).const_mul
      ((∏ j ∈ Finset.univ.filter (fun j : Fin n => j.val < k.val), b j) ^ 2)).const_add
      (jacobiMomentMap n x ⟨2 * k.val, by omega⟩)
    rw [hd.deriv, mul_one]
  have hdiag_odd : ∀ k : Fin n, M ⟨2 * k.val + 1, by omega⟩ ⟨2 * k.val + 1, by omega⟩ =
      2 * (∏ j ∈ Finset.univ.filter (fun j : Fin n => j.val < k.val), b j) ^ 2 * b k := by
    intro k
    dsimp only [M]
    rw [toMatrix'_fderiv_apply (differentiable_jacobiMomentMap n x) _ _]
    have hfn : (fun t => jacobiMomentMap n (Function.update x ⟨2 * k.val + 1, by omega⟩ t)
        ⟨2 * k.val + 1, by omega⟩) =
        fun t => jacobiMomentMap n x ⟨2 * k.val + 1, by omega⟩ +
          (∏ j ∈ Finset.univ.filter (fun j : Fin n => j.val < k.val), b j) ^ 2 *
            (t ^ 2 - x ⟨2 * k.val + 1, by omega⟩ ^ 2) := by
      funext t
      have hsub := jacobiMomentMap_sub_odd (x := x)
        (x' := Function.update x ⟨2 * k.val + 1, by omega⟩ t)
        k fun c hc => (Function.update_of_ne (by intro heq; subst heq; simp at hc) t x).symm
      simp only [x, MeasurableEquiv.symm_apply_apply, Function.update_self] at hsub
      linarith
    rw [hfn]
    have hd := (((hasDerivAt_pow 2 (x ⟨2 * k.val + 1, by omega⟩)).sub_const
      (x ⟨2 * k.val + 1, by omega⟩ ^ 2)).const_mul
      ((∏ j ∈ Finset.univ.filter (fun j : Fin n => j.val < k.val), b j) ^ 2)).const_add
      (jacobiMomentMap n x ⟨2 * k.val + 1, by omega⟩)
    rw [hd.deriv]
    simp only [x, jacobiCoordEquiv_apply_odd]
    ring
  rw [ContinuousLinearMap.det, ← LinearMap.det_toMatrix', Matrix.det_of_isLowerTriangular M hlt]
  rw [← (interleaveIndexEquiv n).prod_comp (fun r => M r r), Fintype.prod_sum_type]
  simp only [interleaveIndexEquiv, Equiv.coe_fn_mk, hdiag_even, hdiag_odd]
  exact prod_jacobi_diagonal n b

/-! ### Bijectivity of the spectral chart and injectivity of the spectral moment map -/

/-- The spectral chart maps `jacobiDomain n` onto `spectralDomain n`. -/
theorem jacobiSpectralChart_image_domain (n : ℕ) :
    jacobiSpectralChart n '' jacobiDomain n = spectralDomain n := by
  ext ⟨lam, q'⟩
  constructor
  · rintro ⟨⟨a, b⟩, hb, h⟩
    have hlam : jacobiEigenvalues a b = lam := congrArg Prod.fst h
    have hq' : (fun j : {i : Fin (n + 1) // i ≠ Fin.last n} => jacobiSpectralWeight a b j.1) = q' :=
      congrArg Prod.snd h
    have hbne : ∀ j, b j ≠ 0 := fun j => (hb j).ne'
    refine ⟨hlam ▸ strictAnti_jacobiEigenvalues hbne, mem_dirichletChartRegion_iff.mpr ⟨?_, ?_⟩⟩
    · intro j
      rw [← hq']
      exact jacobiSpectralWeight_pos hbne j.1
    · rw [← hq']
      have hsum := sum_jacobiSpectralWeight (a := a) hbne
      rw [Fintype.sum_eq_add_sum_subtype_ne _ (Fin.last n)] at hsum
      have hlast : 0 < jacobiSpectralWeight a b (Fin.last n) :=
        jacobiSpectralWeight_pos hbne (Fin.last n)
      linarith
  · rintro ⟨hlam, hq'⟩
    obtain ⟨a, b, hb, hlam_eq, hq_eq⟩ := exists_jacobiMatrix_of_strictAnti_weights hlam
      (dirichletChart_pos hq') (sum_dirichletChart (Fin.last n) q')
    refine ⟨(a, b), hb, Prod.ext hlam_eq (funext fun j => ?_)⟩
    dsimp only [jacobiSpectralChart]
    rw [congrFun hq_eq j.1]
    exact dirichletChart_apply_coe (Fin.last n) q' j

/-- The spectral chart is injective on `jacobiDomain n`. -/
theorem injOn_jacobiSpectralChart (n : ℕ) :
    InjOn (jacobiSpectralChart n) (jacobiDomain n) := by
  intro p₁ hp₁ p₂ hp₂ h
  have hΦ : jacobiMomentMap n (jacobiCoordEquiv n p₁) =
      jacobiMomentMap n (jacobiCoordEquiv n p₂) := by
    rw [← spectralMomentMap_jacobiSpectralChart hp₁,
      ← spectralMomentMap_jacobiSpectralChart hp₂, h]
  exact (jacobiCoordEquiv n).injective
    (injOn_jacobiMomentMap n ⟨p₁, hp₁, rfl⟩ ⟨p₂, hp₂, rfl⟩ hΦ)

/-- The spectral moment map is injective on `spectralCoordEquiv n '' spectralDomain n`. -/
theorem injOn_spectralMomentMap (n : ℕ) :
    InjOn (spectralMomentMap n) (spectralCoordEquiv n '' spectralDomain n) := by
  rintro y₁ ⟨s₁, hs₁, rfl⟩ y₂ ⟨s₂, hs₂, rfl⟩ hG
  rw [← jacobiSpectralChart_image_domain n] at hs₁ hs₂
  obtain ⟨p₁, hp₁, rfl⟩ := hs₁
  obtain ⟨p₂, hp₂, rfl⟩ := hs₂
  rw [spectralMomentMap_jacobiSpectralChart hp₁, spectralMomentMap_jacobiSpectralChart hp₂] at hG
  have hp := (jacobiCoordEquiv n).injective
    (injOn_jacobiMomentMap n ⟨p₁, hp₁, rfl⟩ ⟨p₂, hp₂, rfl⟩ hG)
  rw [hp]

/-- The Jacobi and spectral moment maps have the same image on their respective domains. -/
theorem jacobiMomentMap_image_eq_spectralMomentMap_image (n : ℕ) :
    jacobiMomentMap n '' (jacobiCoordEquiv n '' jacobiDomain n) =
      spectralMomentMap n '' (spectralCoordEquiv n '' spectralDomain n) := by
  rw [← jacobiSpectralChart_image_domain n]
  ext z
  constructor
  · rintro ⟨_, ⟨p, hp, rfl⟩, rfl⟩
    exact ⟨spectralCoordEquiv n (jacobiSpectralChart n p),
      ⟨jacobiSpectralChart n p, ⟨p, hp, rfl⟩, rfl⟩,
      spectralMomentMap_jacobiSpectralChart hp⟩
  · rintro ⟨_, ⟨_, ⟨p, hp, rfl⟩, rfl⟩, rfl⟩
    exact ⟨jacobiCoordEquiv n p, ⟨p, hp, rfl⟩, (spectralMomentMap_jacobiSpectralChart hp).symm⟩

end TauCeti
