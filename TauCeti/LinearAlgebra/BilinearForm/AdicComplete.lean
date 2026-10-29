/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.BilinearForm.IsometryEquiv
public import Mathlib.LinearAlgebra.Matrix.BilinearForm
public import Mathlib.RingTheory.AdicCompletion.Basic
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Module
import TauCeti.LinearAlgebra.BilinearForm.Isometry
import TauCeti.LinearAlgebra.Matrix.Symmetric
import TauCeti.RingTheory.AdicCompletion.Pi

/-!
# Approximate isometries over an adically complete ring

Let `R` be `π`-adically complete, for instance `ℤ_[p]` with `π = p`, and let `C'` be a symmetric
bilinear form on a finite free `R`-module whose Gram matrix `G` admits a symmetric matrix `H` with
even diagonal and `G * H = π ^ j • 1`. Thus `π ^ j • G⁻¹` is integral and *even*: the scales of
`C'` are at most `π ^ j`, and its constituent of scale `π ^ j` is even at its own scale. This
file proves that a linear map `φ` carrying `C'` to a symmetric form `C` modulo `π ^ (j + 1)`, and
the self-pairings modulo `2 π ^ (j + 1)`, is congruent modulo `π` to a linear map carrying `C'`
exactly to `C` (`LinearMap.BilinForm.IsSymm.exists_isometry_of_dvd_sub`). Consequently two such
forms related by approximate isometries in both directions are isometric
(`LinearMap.BilinForm.IsSymm.equivalent_of_dvd_sub`).

When `2` is a unit the parity conditions are automatic, and this is the classical statement that a
lattice whose discriminant group is killed by `π ^ j` is determined by its Gram matrix modulo
`π ^ (j + 1)`. At `π = 2` the hypothesis on `C'` holds for a dyadic lattice whose Jordan
constituents have scale at most `2 ^ j`, the one of scale `2 ^ j` being of type II, and the
precision required is the Gram matrix modulo `2 ^ (j + 1)` together with the self-pairings modulo
`2 ^ (j + 2)` (`LinearMap.BilinForm.IsJordanSplitting.exists_isometry_of_dvd_sub`). For `j = 0` this
is the analogue over complete rings of the reduction theorem for even unimodular forms
`LinearMap.BilinForm.IsSymm.equivalent_of_sub_mem_maximalIdeal_of_even`. Without the parity
condition on `C'` the statement fails: the forms `⟨1⟩` and `⟨5⟩` over `ℤ_[2]` agree modulo `2`,
with self-pairings agreeing modulo `4`, but they are not isometric.

## Main results

* `Matrix.exists_transpose_mul_mul_eq_of_sub_eq`: Newton's method for Gram matrices.
* `LinearMap.BilinForm.IsSymm.exists_isometry_of_dvd_sub`: an approximate isometry is congruent
  modulo `π` to an exact one.
* `LinearMap.BilinForm.IsSymm.equivalent_of_dvd_sub`: two forms satisfying the hypotheses, with
  approximate isometries in both directions, are isometric.

## Implementation notes

If `G - Uᵀ A U = π ^ (j + k) • (D + Dᵀ)` with `k ≥ 1`, where `A` is the Gram matrix of `C` pulled
back along `φ`, then replacing `U` by `U * (1 + π ^ k • (H * D))` cancels the error to first order,
and the new error has the same shape with `k + 1` in place of `k`. The corrections converge
`π`-adically. Recording the error as `D + Dᵀ`, rather than as a symmetric matrix, is what makes the
iteration work when `2` is not a unit.

## References

* J. W. S. Cassels, *Rational Quadratic Forms*, Chapter 8.
* O. T. O'Meara, *Introduction to Quadratic Forms*, §93.
-/

public section

open Module
open LinearMap (BilinForm)
open scoped Matrix

namespace Matrix

variable {R n : Type*} [CommRing R]

/-- Over a `π`-adically complete ring, a sequence of matrices whose consecutive terms are
congruent modulo `π ^ (m + 1)` has a limit, congruent to the `m`-th term modulo `π ^ m`. -/
private theorem exists_forall_pow_dvd_sub [Finite n] (π : R) [IsAdicComplete (Ideal.span {π}) R]
    (U : ℕ → Matrix n n R) (hU : ∀ m i i', π ^ (m + 1) ∣ U (m + 1) i i' - U m i i') :
    ∃ L : Matrix n n R, ∀ m i i', π ^ m ∣ L i i' - U m i i' := by
  let f : ℕ → n × n → R := fun m p ↦ U m p.1 p.2
  have hcauchy {m m' : ℕ} (hm : m ≤ m') (p : n × n) : π ^ m ∣ f m' p - f m p := by
    induction m', hm using Nat.le_induction with
    | base => simp
    | succ m' hm ih =>
      rw [← sub_add_sub_cancel]
      exact dvd_add ((pow_dvd_pow π (by omega)).trans (hU m' p.1 p.2)) ih
  obtain ⟨L, hL⟩ := IsPrecomplete.prec (I := Ideal.span {π}) inferInstance (f := f)
    fun {m m'} hm ↦ by
      rw [SModEq.sub_mem, TauCeti.mem_span_singleton_pow_smul_top_iff]
      exact fun p ↦ dvd_sub_comm.mp (hcauchy hm p)
  refine ⟨Matrix.of fun i i' ↦ L (i, i'), fun m i i' ↦ ?_⟩
  have := (TauCeti.mem_span_singleton_pow_smul_top_iff π _ m).1 (SModEq.sub_mem.1 (hL m)) (i, i')
  exact dvd_sub_comm.mp (by simpa [f] using this)

/-- Over a `π`-adically Hausdorff ring, a matrix whose entries are divisible by every power of `π`
vanishes. -/
private theorem eq_zero_of_forall_pow_dvd (π : R) [IsHausdorff (Ideal.span {π}) R]
    {X : Matrix n n R} (hX : ∀ m i i', π ^ m ∣ X i i') : X = 0 := by
  have : (fun p : n × n ↦ X p.1 p.2) = 0 :=
    IsHausdorff.haus (I := Ideal.span {π}) inferInstance _ fun m ↦ by
      rw [SModEq.zero, TauCeti.mem_span_singleton_pow_smul_top_iff]
      exact fun p ↦ hX m p.1 p.2
  ext i i'
  simpa using congrFun this (i, i')

variable [Fintype n] [DecidableEq n]

/-- **The Newton step.** Let `G` be symmetric with `G * H = π ^ j • 1`, where `H = H₀ + H₀ᵀ`. If a
matrix differs from `G` by `π ^ (j + k) • (D + Dᵀ)`, then its congruence by
`1 + π ^ k • (H * D)` differs from `G` by `π ^ (j + 2 * k) • (P + Pᵀ)` for an explicit `P`. -/
private theorem sub_transpose_one_add_mul_mul_one_add_eq (π : R) (j k : ℕ) {G H₀ D : Matrix n n R}
    (hG : G.IsSymm) (hGH : G * (H₀ + H₀ᵀ) = π ^ j • 1) :
    G - (1 + π ^ k • ((H₀ + H₀ᵀ) * D))ᵀ * (G - π ^ (j + k) • (D + Dᵀ)) *
        (1 + π ^ k • ((H₀ + H₀ᵀ) * D)) =
      π ^ (j + 2 * k) • ((Dᵀ * (H₀ + H₀ᵀ) * (D + Dᵀ) - Dᵀ * H₀ * D +
          π ^ k • (Dᵀ * (H₀ + H₀ᵀ) * D * (H₀ + H₀ᵀ) * D)) +
        (Dᵀ * (H₀ + H₀ᵀ) * (D + Dᵀ) - Dᵀ * H₀ * D +
          π ^ k • (Dᵀ * (H₀ + H₀ᵀ) * D * (H₀ + H₀ᵀ) * D))ᵀ) := by
  set H := H₀ + H₀ᵀ with hHdef
  have hH : Hᵀ = H := by simp [hHdef, add_comm]
  -- The three ways `G` enters the expansion, each rewritten through `G * H = π ^ j • 1`.
  have hGHD : G * (H * D) = π ^ j • D := by rw [← Matrix.mul_assoc, hGH, smul_mul, one_mul]
  have hDHG : Dᵀ * (H * G) = π ^ j • Dᵀ := by
    have : (G * (H * D))ᵀ = Dᵀ * (H * G) := by
      simp [transpose_mul, hH, hG.eq, Matrix.mul_assoc]
    rw [← this, hGHD, transpose_smul]
  have hDHD : Dᵀ * (H * D) = Dᵀ * (H₀ * D) + Dᵀ * (H₀ᵀ * D) := by
    rw [hHdef, Matrix.add_mul, Matrix.mul_add]
  simp only [transpose_add, transpose_sub, transpose_one, transpose_smul, transpose_mul, hH,
    transpose_transpose, Matrix.add_mul, Matrix.mul_add, Matrix.one_mul, Matrix.mul_one,
    Matrix.sub_mul, Matrix.mul_sub, Matrix.smul_mul, Matrix.mul_smul, Matrix.mul_assoc, hGHD,
    hDHG]
  rw [hDHD]
  module

/-- **Newton's method for Gram matrices.** Let `R` be `π`-adically complete, let `G` be symmetric,
and let `H₀` satisfy `G * (H₀ + H₀ᵀ) = π ^ j • 1`. If `G - A = π ^ (j + 1) • (D + Dᵀ)`, then
`Uᵀ * A * U = G` for some `U ≡ 1` modulo `π`. -/
theorem exists_transpose_mul_mul_eq_of_sub_eq (π : R) [IsAdicComplete (Ideal.span {π}) R]
    {j : ℕ} {G A H₀ D : Matrix n n R} (hG : G.IsSymm) (hGH : G * (H₀ + H₀ᵀ) = π ^ j • 1)
    (hA : G - A = π ^ (j + 1) • (D + Dᵀ)) :
    ∃ V : Matrix n n R, (1 + π • V)ᵀ * A * (1 + π • V) = G := by
  set H := H₀ + H₀ᵀ with hHdef
  -- The Newton iterates `(U m, D m)`, with `G - (U m)ᵀ A (U m) = π ^ (j + m + 1) • (D m + (D m)ᵀ)`.
  let s : ℕ → Matrix n n R × Matrix n n R := fun m ↦ Nat.rec (1, D)
    (fun m p ↦ (p.1 * (1 + π ^ (m + 1) • (H * p.2)), π ^ m • (p.2ᵀ * H * (p.2 + p.2ᵀ) -
      p.2ᵀ * H₀ * p.2 + π ^ (m + 1) • (p.2ᵀ * H * p.2 * H * p.2)))) m
  have hs (m : ℕ) : s (m + 1) = ((s m).1 * (1 + π ^ (m + 1) • (H * (s m).2)),
      π ^ m • ((s m).2ᵀ * H * ((s m).2 + (s m).2ᵀ) - (s m).2ᵀ * H₀ * (s m).2 +
        π ^ (m + 1) • ((s m).2ᵀ * H * (s m).2 * H * (s m).2))) := (rfl)
  have hinv (m : ℕ) : G - (s m).1ᵀ * A * (s m).1 = π ^ (j + m + 1) • ((s m).2 + (s m).2ᵀ) := by
    induction m with
    | zero => simpa [s] using hA
    | succ m ih =>
      have hA' : (s m).1ᵀ * A * (s m).1 = G - π ^ (j + (m + 1)) • ((s m).2 + (s m).2ᵀ) := by
        rw [← add_assoc, ← ih, sub_sub_cancel]
      rw [hs, transpose_mul, show ∀ X Y : Matrix n n R, Xᵀ * Yᵀ * A * (Y * X) =
        Xᵀ * (Yᵀ * A * Y) * X from fun _ _ ↦ by simp only [Matrix.mul_assoc], hA',
        sub_transpose_one_add_mul_mul_one_add_eq π j (m + 1) hG hGH, ← hHdef, transpose_smul,
        ← smul_add, smul_smul, ← pow_add]
      ring_nf
  -- Consecutive iterates are congruent modulo `π ^ (m + 1)`, so the iterates converge to `U`.
  obtain ⟨U, hU⟩ := exists_forall_pow_dvd_sub π (fun m ↦ (s m).1) fun m i i' ↦
    ⟨((s m).1 * (H * (s m).2)) i i', by
      simp only [hs, Matrix.mul_add, Matrix.mul_one, Matrix.mul_smul, add_apply, smul_apply,
        smul_eq_mul, add_sub_cancel_left]⟩
  -- `U ≡ 1` modulo `π`, since `U ≡ (s 1).1 = 1 + π • (H * D)`.
  obtain ⟨V, hV⟩ : ∃ V : Matrix n n R, U = 1 + π • V := by
    have hs1 : (s 1).1 = 1 + π • (H * D) := by
      rw [show s 1 = s (0 + 1) from rfl, hs]
      simp [s]
    choose V hV using hU 1
    refine ⟨Matrix.of fun i i' ↦ V i i' + (H * D) i i', ?_⟩
    ext i i'
    have := hV i i'
    rw [hs1] at this
    simp only [add_apply, smul_apply, of_apply, smul_eq_mul, pow_one] at this ⊢
    linear_combination this
  refine ⟨V, ?_⟩
  rw [← hV]
  -- `G - Uᵀ A U` vanishes modulo every power of `π`.
  refine (sub_eq_zero.mp (eq_zero_of_forall_pow_dvd π fun m ↦ ?_)).symm
  choose W hW using hU m
  have hUW : U = (s m).1 + π ^ m • Matrix.of W := by
    ext i i'
    simp [← hW i i']
  have hdiff : G - Uᵀ * A * U = π ^ m • (π ^ (j + 1) • ((s m).2 + (s m).2ᵀ) -
      ((Matrix.of W)ᵀ * A * (s m).1 + (s m).1ᵀ * A * Matrix.of W +
        π ^ m • ((Matrix.of W)ᵀ * A * Matrix.of W))) := by
    rw [hUW, ← sub_add_cancel G ((s m).1ᵀ * A * (s m).1), hinv m]
    simp only [transpose_add, transpose_smul, Matrix.add_mul, Matrix.mul_add, Matrix.smul_mul,
      Matrix.mul_smul]
    rw [show j + m + 1 = m + (j + 1) by omega, pow_add]
    module
  intro i i'
  rw [hdiff]
  exact ⟨_, rfl⟩

end Matrix

namespace LinearMap.BilinForm

variable {R M M' n : Type*} [CommRing R] [AddCommGroup M] [Module R M] [AddCommGroup M']
  [Module R M'] [Fintype n] [DecidableEq n] {C : BilinForm R M} {C' : BilinForm R M'}

/-- **Approximate isometries over an adically complete ring.** Let `R` be `π`-adically complete,
let `C` and `C'` be symmetric, and let `b` be a basis of the domain of `C'`. Suppose that the Gram
matrix of `C'` times some symmetric matrix `H` with even diagonal is `π ^ j • 1`. If a linear map
`φ` carries `C'` to `C` modulo `π ^ (j + 1)`, and the self-pairings modulo `2 * π ^ (j + 1)`, then a
linear map `ψ ≡ φ` modulo `π` carries `C'` exactly to `C`. -/
theorem IsSymm.exists_isometry_of_dvd_sub (π : R) [IsAdicComplete (Ideal.span {π}) R]
    (hC : C.IsSymm) (hC' : C'.IsSymm) (b : Basis n R M') {j : ℕ} {H : Matrix n n R}
    (hH : C'.toMatrix b * H = π ^ j • 1) (hHs : H.IsSymm) (hHd : ∀ i, 2 ∣ H i i)
    (φ : M' →ₗ[R] M) (h₁ : ∀ x y, π ^ (j + 1) ∣ C' x y - C (φ x) (φ y))
    (h₂ : ∀ x, 2 * π ^ (j + 1) ∣ C' x x - C (φ x) (φ x)) :
    ∃ τ : M' →ₗ[R] M', ∀ x y, C (φ (x + π • τ x)) (φ (y + π • τ y)) = C' x y := by
  obtain ⟨H₀, hH₀⟩ := hHs.exists_eq_smul_add_transpose 1 (fun _ _ ↦ one_dvd _)
    (fun i ↦ by simpa using hHd i)
  rw [one_smul] at hH₀
  set G := C'.toMatrix b
  set A := BilinForm.toMatrix b (C.comp φ φ)
  have hG : G.IsSymm := by
    ext i i'
    simp [G, toMatrix_apply, hC'.eq (b i') (b i)]
  have hE : (G - A).IsSymm := by
    ext i i'
    simp [G, A, toMatrix_apply, hC'.eq (b i') (b i), hC.eq (φ (b i')) (φ (b i))]
  obtain ⟨D, hD⟩ := hE.exists_eq_smul_add_transpose (π ^ (j + 1))
    (fun i i' ↦ by simpa [G, A, toMatrix_apply] using h₁ (b i) (b i'))
    (fun i ↦ by simpa [G, A, toMatrix_apply] using h₂ (b i))
  obtain ⟨V, hV⟩ := Matrix.exists_transpose_mul_mul_eq_of_sub_eq π hG (hH₀ ▸ hH) hD
  refine ⟨Matrix.toLin b b V, fun x y ↦ ?_⟩
  have hT : (LinearMap.id + π • Matrix.toLin b b V) = Matrix.toLin b b (1 + π • V) := by
    simp [map_add, map_smul, Matrix.toLin_one]
  have hcomp : BilinForm.toMatrix b ((C.comp φ φ).comp (Matrix.toLin b b (1 + π • V))
      (Matrix.toLin b b (1 + π • V))) = BilinForm.toMatrix b C' := by
    rw [toMatrix_comp b b, LinearMap.toMatrix_toLin]
    exact hV
  have := (BilinForm.toMatrix b).injective hcomp
  rw [← hT] at this
  simpa using LinearMap.congr_fun₂ this x y

/-- A form whose Gram matrix times some matrix is `π ^ j • 1`, with `π ≠ 0` in a domain, is
nondegenerate. -/
private theorem separatingLeft_of_toMatrix_mul_eq [IsDomain R] {π : R} (hπ : π ≠ 0)
    (b : Basis n R M') {j : ℕ} {H : Matrix n n R} (hH : C'.toMatrix b * H = π ^ j • 1) :
    C'.SeparatingLeft := by
  refine ((nondegenerate_iff_det_ne_zero b).mpr fun h ↦ ?_).1
  have := congrArg Matrix.det hH
  rw [Matrix.det_mul, h, zero_mul, Matrix.det_smul, Matrix.det_one, mul_one] at this
  exact pow_ne_zero _ (pow_ne_zero _ hπ) this.symm

/-- **Two-sided approximate isometries.** Over a `π`-adically complete domain with `π ≠ 0`, let `C`
and `C'` be symmetric forms on finite free modules, each satisfying the hypothesis of
`LinearMap.BilinForm.IsSymm.exists_isometry_of_dvd_sub`: its Gram matrix times a symmetric matrix
with even diagonal is `π ^ j • 1`. If linear maps in both directions carry each form to the other
modulo `π ^ (j + 1)`, and the self-pairings modulo `2 * π ^ (j + 1)`, then `C` and `C'` are
isometric. -/
theorem IsSymm.equivalent_of_dvd_sub [IsDomain R] (π : R) [IsAdicComplete (Ideal.span {π}) R]
    (hπ : π ≠ 0) (hC : C.IsSymm) (hC' : C'.IsSymm) {m : Type*} [Fintype m] [DecidableEq m]
    (c : Basis m R M) (b : Basis n R M') {j : ℕ} {H : Matrix m m R} {H' : Matrix n n R}
    (hH : C.toMatrix c * H = π ^ j • 1) (hHs : H.IsSymm) (hHd : ∀ i, 2 ∣ H i i)
    (hH' : C'.toMatrix b * H' = π ^ j • 1) (hH's : H'.IsSymm) (hH'd : ∀ i, 2 ∣ H' i i)
    (φ : M' →ₗ[R] M) (h₁ : ∀ x y, π ^ (j + 1) ∣ C' x y - C (φ x) (φ y))
    (h₂ : ∀ x, 2 * π ^ (j + 1) ∣ C' x x - C (φ x) (φ x))
    (φ' : M →ₗ[R] M') (h₁' : ∀ x y, π ^ (j + 1) ∣ C x y - C' (φ' x) (φ' y))
    (h₂' : ∀ x, 2 * π ^ (j + 1) ∣ C x x - C' (φ' x) (φ' x)) :
    C.Equivalent C' := by
  have : Module.Free R M := .of_basis c
  have : Module.Finite R M := .of_basis c
  have : Module.Free R M' := .of_basis b
  have : Module.Finite R M' := .of_basis b
  obtain ⟨τ, hτ⟩ := hC.exists_isometry_of_dvd_sub π hC' b hH' hH's hH'd φ h₁ h₂
  obtain ⟨τ', hτ'⟩ := hC'.exists_isometry_of_dvd_sub π hC c hH hHs hHd φ' h₁' h₂'
  set ψ : M' →ₗ[R] M := φ ∘ₗ (LinearMap.id + π • τ)
  set ψ' : M →ₗ[R] M' := φ' ∘ₗ (LinearMap.id + π • τ')
  have hψ (x y : M') : C (ψ x) (ψ y) = C' x y := by simpa [ψ] using hτ x y
  have hψ' (x y : M) : C' (ψ' x) (ψ' y) = C x y := by simpa [ψ'] using hτ' x y
  -- The two composites are isometries of nondegenerate forms, hence bijective.
  have hbij : Function.Bijective (ψ ∘ₗ ψ') :=
    TauCeti.BilinForm.IsIsometry.bijective (separatingLeft_of_toMatrix_mul_eq hπ c hH)
      ((TauCeti.BilinForm.isIsometry_iff (B := C)).mpr fun x y ↦ by simp [hψ, hψ'])
  have hbij' : Function.Bijective (ψ' ∘ₗ ψ) :=
    TauCeti.BilinForm.IsIsometry.bijective (separatingLeft_of_toMatrix_mul_eq hπ b hH')
      ((TauCeti.BilinForm.isIsometry_iff (B := C')).mpr fun x y ↦ by simp [hψ, hψ'])
  rw [LinearMap.coe_comp] at hbij hbij'
  have hψbij : Function.Bijective ψ := ⟨.of_comp hbij'.1, .of_comp hbij.2⟩
  exact ⟨{ (LinearEquiv.ofBijective ψ hψbij).symm with
    map_app' x y := by
      obtain ⟨x, rfl⟩ := hψbij.2 x
      obtain ⟨y, rfl⟩ := hψbij.2 y
      simp [hψ] }⟩

end LinearMap.BilinForm
