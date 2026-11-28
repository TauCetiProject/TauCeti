/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.HeisenbergModel.Fock.Tensor
public import TauCeti.NumberTheory.NumberField.CMField.HeisenbergDatum
public import TauCeti.NumberTheory.NumberField.CMField.UnitaryGroup.WeilData
public import TauCeti.NumberTheory.NumberField.Global.Adeles.BorelSpace
public import TauCeti.RingTheory.DedekindDomain.FiniteAdeleRing.Haar

/-!
# The real and finite coordinates of Weil data

Let `E` be a CM field with a CM type `Φ` and Weil data `(j, α, υ)`, and let `n` be a finite set.
The adelic Heisenberg datum `β_s(x, y) = ψ(½ j · y* ε_s x)` of signature `s` lives on
`𝔸^n = E_∞^n × 𝔸_f^n` (`TauCeti.adelicHeisenbergDatum`). Weil data fix coordinates on this group:

* the **real coordinates** `y ∈ ℂ^{Φ × n} ↦ (κ_w y_{w,i})_{i,w} ∈ E_∞^n`, where `κ_w` is the real
  scale `(2π Im Φ_w(j))^{−1/2}` (`TauCeti.WeilData.realScale`) and a complex number is read as a
  component at `w` through the embedding `Φ_w` of `Φ` above `w`
  (`TauCeti.CMType.completionRingEquiv`);
* the **finite coordinates** `z ∈ 𝔸_f^n ↦ α z`.

Together they identify `ℂ^{Φ × n} × 𝔸_f^n` with `𝔸^n` (`TauCeti.WeilData.coordEquiv`). The real
vector of `y` and the finite vector of `z` are `realVec(y) = (κ y, 0)` and `finVec(z) = (0, α z)`;
the finite image of a rational vector `γ ∈ E^n` is `α⁻¹ γ ∈ 𝔸_f^n`, so that
`finVec(α⁻¹ γ) = (0, γ)`.
The measure `μ` on `𝔸^n` is the image under these coordinates of `π^{−|Φ × n|}` times Lebesgue
measure on `ℂ^{Φ × n}` times the Haar measure `λ` on `𝔸_f^n` with `λ(Ô^n) = 1`
(`TauCeti.WeilData.vacuumMeasure`); it is an additive Haar measure.

The coordinates are chosen to split the Heisenberg datum and the adelic vacuum:

* in real coordinates, the infinite part `ψ_∞(½ j · y* ε_s x)` of the datum is the Fock datum
  `exp((y* ε x − x* ε y)/2)` on `ℂ^{Φ × n}` for the signs `ε(w, i) = s_i`
  (`TauCeti.WeilData.infiniteAdeleAddChar_realCoord`), as `Im Φ_w(j) κ_w² = (2π)⁻¹`;
* hence `β_s` in coordinates is the Fock datum of the real coordinates times `ψ_f(½ j · y* x)` at
  the finite coordinates (`TauCeti.WeilData.adelicHeisenbergDatum_coordEquiv`), and on real
  vectors it is the Fock datum (`TauCeti.WeilData.adelicHeisenbergDatum_realVec`);
* the adelic vacuum at `(κ y, α z)` is the Gaussian `exp(−|y|²/2)` times `semi(z)` on `Ô^n` and `0`
  off it (`TauCeti.WeilData.vacuum_realCoord_finCoord`), because
  `ψ_f(−¼ (α z)* (α z)) = semi(z)` for every `z`
  (`TauCeti.WeilData.semichar_eq_finiteAdeleAddChar`).

## Main definitions

* `TauCeti.WeilData.realCoord`, `TauCeti.WeilData.finCoord`, `TauCeti.WeilData.coordEquiv`: the
  real, finite and adelic coordinates.
* `TauCeti.WeilData.realVec`, `TauCeti.WeilData.finVec`, `TauCeti.WeilData.finImage`: real and
  finite vectors and the finite image of a rational vector.
* `TauCeti.WeilData.vacuumMeasure`: the measure `μ` on `𝔸^n`.

## Main results

* `TauCeti.WeilData.infiniteAdeleAddChar_realCoord`,
  `TauCeti.WeilData.adelicHeisenbergDatum_coordEquiv`,
  `TauCeti.WeilData.adelicHeisenbergDatum_realVec`: the Heisenberg datum in coordinates.
* `TauCeti.WeilData.semichar_eq_finiteAdeleAddChar`: `semi(z) = ψ_f(−¼ (α z)* (α z))`.
* `TauCeti.WeilData.vacuum_realCoord_finCoord`: the adelic vacuum in coordinates.
* `TauCeti.WeilData.measurePreserving_coordEquiv`: the coordinates carry the product measure to
  `μ`.

The index set `Φ × n` of the real coordinates is written `InfinitePlace E × n`: a CM type picks
exactly one embedding `Φ_w` above each infinite place `w` (`TauCeti.CMType.embedding`).

## Attribution

The coordinates and the measure correspond to `New.realVec`, `New.finVec` and `New.vacuumMeasure`
in `src/Lib/Weil/Construction/AdelicRepresentation.lean` of grh-lean
(https://github.com/lsernau/grh-lean, Apache 2.0, Copyright 2026 Anthropic, PBC). The statements
and proofs here, through the identification `E_w ≅ ℂ` of a CM type and the Fock datum, were
written independently.

## References

* A. Weil, *Sur certains groupes d'opérateurs unitaires*, Acta Math. 111 (1964), 143–211.
-/

public section
noncomputable section

open IsDedekindDomain IsDedekindDomain.FiniteAdeleRing NumberField NumberField.IsCMField
open NumberField.InfinitePlace.Completion MeasureTheory Measure Matrix
open TauCeti.GlobalNumberFields
open scoped NumberField NumberField.AdeleRing Real ComplexConjugate

variable {E : Type*} [Field E] [NumberField E] [IsCMField E]

namespace TauCeti

namespace CMType

variable (Φ : CMType E)

/-- Read in `ℂ` through the embedding `Φ_w` of `Φ` above `w`, the component at `w` of the conjugate
of an infinite adele is the complex conjugate of its component at `w`. -/
@[simp]
theorem completionEmbedding_star_apply (a : InfiniteAdeleRing E) (w : InfinitePlace E) :
    Φ.completionEmbedding w ((star a) w) = conj (Φ.completionEmbedding w (a w)) := by
  rw [CMType.completionEmbedding_def]
  split_ifs <;> simp [InfiniteAdeleRing.extensionEmbedding_star_apply]

end CMType

namespace WeilData

variable {Φ : CMType E} (W : WeilData Φ) {n : Type*}

/-! ### The real scales -/

/-- `κ_w² = (2π |j|_w)⁻¹`. -/
theorem realScale_sq (w : InfinitePlace E) : W.realScale w ^ 2 = (2 * π * w W.j)⁻¹ := by
  have h : 0 < 2 * π * w W.j := by have := W.apply_j_pos w; positivity
  rw [realScale_eq, ← Real.rpow_natCast, ← Real.rpow_mul h.le]
  norm_num [Real.rpow_neg_one]

/-- `|j|_w κ_w² = (2π)⁻¹`: the real scales normalise the infinite datum. -/
theorem apply_j_mul_realScale_sq (w : InfinitePlace E) :
    w W.j * W.realScale w ^ 2 = (2 * π)⁻¹ := by
  have := (W.apply_j_pos w).ne'
  rw [realScale_sq]
  field_simp

/-- The real scales are nonzero, as complex numbers. -/
theorem realScale_ne_zero (w : InfinitePlace E) : (W.realScale w : ℂ) ≠ 0 :=
  Complex.ofReal_ne_zero.mpr (W.realScale_pos w).ne'

/-- `j / 2` is purely imaginary. -/
theorem half_j_mem_skewAdjoint : W.j / 2 ∈ skewAdjoint E := by
  rw [skewAdjoint.mem_iff, star_div₀, W.star_j, star_ofNat, neg_div]

/-! ### The coordinates -/

/-- The **real coordinates** `ℂ^{Φ × n} ≃ E_∞^n`, `y ↦ (κ_w y_{w,i})_{i,w}`, a complex number
being read as a component at `w` through the embedding `Φ_w` of `Φ` above `w`. -/
def realCoord : (InfinitePlace E × n → ℂ) ≃ₜ+ (n → InfiniteAdeleRing E) where
  toFun y i w := (Φ.completionRingEquiv w).symm (W.realScale w * y (w, i))
  invFun x p := (W.realScale p.1 : ℂ)⁻¹ * Φ.completionEmbedding p.1 (x p.2 p.1)
  left_inv y := funext fun p ↦ by
    simp only [← CMType.completionRingEquiv_apply, RingEquiv.apply_symm_apply]
    exact inv_mul_cancel_left₀ (W.realScale_ne_zero p.1) _
  right_inv x := funext fun i ↦ funext fun w ↦ by
    rw [RingEquiv.symm_apply_eq, CMType.completionRingEquiv_apply]
    exact mul_inv_cancel_left₀ (W.realScale_ne_zero w) _
  map_add' y y' := funext fun i ↦ funext fun w ↦ by simp [mul_add]
  continuous_toFun := by
    refine continuous_pi fun i ↦ continuous_pi fun w ↦ ?_
    exact (Φ.continuous_completionRingEquiv_symm w).comp (by fun_prop)
  continuous_invFun := by
    refine continuous_pi fun p ↦ ?_
    exact continuous_const.mul ((Φ.continuous_completionEmbedding p.1).comp (by fun_prop))

/-- The defining formula of the real coordinates: the component at `w` of the `i`-th coordinate
of `realCoord y` is the complex number `κ_w y_{w,i}` read in `E_w` through `Φ_w`. -/
theorem realCoord_apply (y : InfinitePlace E × n → ℂ) (i : n) (w : InfinitePlace E) :
    W.realCoord y i w = (Φ.completionRingEquiv w).symm (W.realScale w * y (w, i)) :=
  (rfl)

/-- The real coordinates read through `Φ_w`: the component at `w` of the `i`-th coordinate of
`realCoord y` is `κ_w y_{w,i}`. -/
@[simp]
theorem completionEmbedding_realCoord_apply (y : InfinitePlace E × n → ℂ) (i : n)
    (w : InfinitePlace E) :
    Φ.completionEmbedding w (W.realCoord y i w) = W.realScale w * y (w, i) := by
  rw [← CMType.completionRingEquiv_apply, realCoord_apply, RingEquiv.apply_symm_apply]

/-- The inverse of the real coordinates: `x ↦ (κ_w⁻¹ Φ_w(x_{i,w}))_{w,i}`. -/
@[simp]
theorem realCoord_symm_apply (x : n → InfiniteAdeleRing E) (p : InfinitePlace E × n) :
    W.realCoord.symm x p = (W.realScale p.1 : ℂ)⁻¹ * Φ.completionEmbedding p.1 (x p.2 p.1) :=
  (rfl)

/-- The norm of a real coordinate: `‖(κ y)_{i,w}‖ = κ_w ‖y_{w,i}‖`. -/
theorem norm_realCoord_apply (y : InfinitePlace E × n → ℂ) (i : n) (w : InfinitePlace E) :
    ‖W.realCoord y i w‖ = W.realScale w * ‖y (w, i)‖ := by
  rw [← Φ.norm_completionEmbedding, completionEmbedding_realCoord_apply, norm_mul,
    Complex.norm_real, Real.norm_of_nonneg (W.realScale_pos w).le]

/-- The **finite coordinates** `𝔸_f^n ≃ 𝔸_f^n`, `z ↦ α z`. -/
def finCoord : (n → 𝔸ᶠ[E]) ≃ₜ+ (n → 𝔸ᶠ[E]) where
  toFun z := W.α • z
  invFun x := W.α⁻¹ • x
  left_inv z := inv_smul_smul W.α z
  right_inv x := smul_inv_smul W.α x
  map_add' z z' := smul_add W.α z z'
  continuous_toFun := continuous_const_smul _
  continuous_invFun := continuous_const_smul _

@[simp]
theorem finCoord_apply (z : n → 𝔸ᶠ[E]) : W.finCoord z = W.α • z :=
  (rfl)

@[simp]
theorem finCoord_symm_apply (x : n → 𝔸ᶠ[E]) : W.finCoord.symm x = W.α⁻¹ • x :=
  (rfl)

/-- The **coordinates** `ℂ^{Φ × n} × 𝔸_f^n ≃ 𝔸^n = E_∞^n × 𝔸_f^n`, `(y, z) ↦ (κ y, α z)`. -/
def coordEquiv : (InfinitePlace E × n → ℂ) × (n → 𝔸ᶠ[E]) ≃ₜ+
    (n → InfiniteAdeleRing E) × (n → 𝔸ᶠ[E]) where
  toFun x := (W.realCoord x.1, W.finCoord x.2)
  invFun x := (W.realCoord.symm x.1, W.finCoord.symm x.2)
  left_inv x := by simp
  right_inv x := by simp
  map_add' x x' := by simp
  continuous_toFun := by fun_prop
  continuous_invFun := by fun_prop

@[simp]
theorem coordEquiv_apply (x : (InfinitePlace E × n → ℂ) × (n → 𝔸ᶠ[E])) :
    W.coordEquiv x = (W.realCoord x.1, W.finCoord x.2) :=
  (rfl)

@[simp]
theorem coordEquiv_symm_apply (x : (n → InfiniteAdeleRing E) × (n → 𝔸ᶠ[E])) :
    W.coordEquiv.symm x = (W.realCoord.symm x.1, W.finCoord.symm x.2) :=
  (rfl)

/-- The **real vector** `realVec(y) = (κ y, 0)` of `y ∈ ℂ^{Φ × n}`. -/
def realVec (y : InfinitePlace E × n → ℂ) : (n → InfiniteAdeleRing E) × (n → 𝔸ᶠ[E]) :=
  W.coordEquiv (y, 0)

/-- The **finite vector** `finVec(z) = (0, α z)` of `z ∈ 𝔸_f^n`. -/
def finVec (z : n → 𝔸ᶠ[E]) : (n → InfiniteAdeleRing E) × (n → 𝔸ᶠ[E]) :=
  W.coordEquiv (0, z)

@[simp]
theorem realVec_def (y : InfinitePlace E × n → ℂ) : W.realVec y = (W.realCoord y, 0) := by
  simp [realVec]

@[simp]
theorem finVec_def (z : n → 𝔸ᶠ[E]) : W.finVec z = (0, W.α • z) := by
  simp [finVec]

/-- Every point of `𝔸^n` is the sum of a real and a finite vector:
`coordEquiv (y, z) = realVec(y) + finVec(z)`. -/
theorem realVec_add_finVec (y : InfinitePlace E × n → ℂ) (z : n → 𝔸ᶠ[E]) :
    W.realVec y + W.finVec z = W.coordEquiv (y, z) := by
  simp [realVec, finVec]

/-- The **finite image** `α⁻¹ γ ∈ 𝔸_f^n` of a rational vector `γ ∈ E^n`. -/
def finImage (γ : n → E) : n → 𝔸ᶠ[E] := W.α⁻¹ • fun i ↦ algebraMap E 𝔸ᶠ[E] (γ i)

theorem finImage_def (γ : n → E) :
    W.finImage γ = W.α⁻¹ • fun i ↦ algebraMap E 𝔸ᶠ[E] (γ i) :=
  (rfl)

/-- The finite coordinates of the finite image of `γ ∈ E^n` are the finite adele `γ`. -/
@[simp]
theorem smul_finImage (γ : n → E) :
    W.α • W.finImage γ = fun i ↦ algebraMap E 𝔸ᶠ[E] (γ i) :=
  smul_inv_smul W.α _

/-- The finite vector of the finite image of `γ ∈ E^n` is the finite adele `γ`. -/
theorem finVec_finImage (γ : n → E) :
    W.finVec (W.finImage γ) = (0, fun i ↦ algebraMap E 𝔸ᶠ[E] (γ i)) := by
  rw [finVec_def, smul_finImage]

/-! ### The Heisenberg datum in coordinates -/

variable [Fintype n]

/-- The infinite trace of the infinite datum in real coordinates. With
`H = Σ_{w,i} s_i conj(y_{w,i}) x_{w,i}`, the infinite adele `½ j · (κ y)* ε_s (κ x)` has trace
`−Im H / (2π)`. -/
private theorem infiniteAdeleTrace_realCoord [DecidableEq n] (s : n → ℤˣ)
    (x y : InfinitePlace E × n → ℂ) :
    infiniteAdeleTrace E (algebraMap E (InfiniteAdeleRing E) (W.j / 2) *
        (star (W.realCoord y) ⬝ᵥ diagonal (fun i ↦ ((s i : ℤ) : InfiniteAdeleRing E)) *ᵥ
          W.realCoord x)) =
      -(∑ p : InfinitePlace E × n, ((s p.2 : ℤ) : ℂ) * (conj (y p) * x p)).im / (2 * π) := by
  have hc := (CMType.nonempty_iff_isTotallyComplex.mp ⟨Φ⟩)
  rw [infiniteAdeleTrace_apply, Fintype.sum_prod_type, Complex.im_sum, ← Finset.sum_neg_distrib,
    Finset.sum_div]
  refine Finset.sum_congr rfl fun w _ ↦ ?_
  rw [(hc.isComplex w).mult_eq_two, ← Φ.re_completionEmbedding]
  -- read the component at `w` in `ℂ` through `Φ_w`
  have hj : Φ.embedding w W.j = Complex.I * (w W.j : ℂ) := by
    apply Complex.ext <;> simp [W.re_embedding_j, W.im_embedding_j]
  have hκ := W.apply_j_mul_realScale_sq w
  -- evaluation at `w` followed by `Φ_w`, as a ring homomorphism `E_∞ →+* ℂ`
  set φ : InfiniteAdeleRing E →+* ℂ :=
    (Φ.completionEmbedding w).comp (Pi.evalRingHom (fun v : InfinitePlace E ↦ v.Completion) w)
  have hφ (a : InfiniteAdeleRing E) : Φ.completionEmbedding w (a w) = φ a := by
    rw [RingHom.comp_apply, Pi.evalRingHom_apply]
  have hstar (a : InfiniteAdeleRing E) : φ (star a) = conj (φ a) := by
    rw [← hφ, ← hφ, CMType.completionEmbedding_star_apply]
  have hR (v : InfinitePlace E × n → ℂ) (i : n) :
      φ (W.realCoord v i) = W.realScale w * v (w, i) := by
    rw [← hφ, completionEmbedding_realCoord_apply]
  have ht : φ (algebraMap E (InfiniteAdeleRing E) (W.j / 2)) = Complex.I * (w W.j : ℂ) / 2 := by
    rw [← hφ, InfiniteAdeleRing.algebraMap_apply, CMType.completionEmbedding_coe,
      WithAbs.ofAbs_toAbs, map_div₀, hj, map_ofNat]
  rw [hφ]
  simp only [mulVec_diagonal, dotProduct, Pi.star_apply, map_mul, _root_.map_sum, map_intCast,
    hstar, hR, ht, Complex.conj_ofReal]
  simp only [Complex.re_sum, Complex.im_sum, Finset.mul_sum, Finset.sum_div,
    ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  -- collect the real factor `|j|_w κ_w² = (2π)⁻¹`
  have h : Complex.I * (w W.j : ℂ) / 2 * (W.realScale w * conj (y (w, i)) *
      (((s i : ℤ) : ℂ) * (W.realScale w * x (w, i)))) =
      ((w W.j * W.realScale w ^ 2 : ℝ) : ℂ) *
        (Complex.I * (((s i : ℤ) : ℂ) * (conj (y (w, i)) * x (w, i)))) / 2 := by
    push_cast
    ring
  rw [h, hκ, Complex.div_ofNat_re, Complex.re_ofReal_mul, Complex.I_mul_re]
  field_simp
  push_cast
  ring

/-- **The infinite datum in real coordinates is the Fock datum.** For signs `s` on `n`, the
infinite part `ψ_∞(½ j · (κ y)* ε_s (κ x))` of the adelic Heisenberg datum is the Fock datum
`exp((y* ε x − x* ε y)/2)` on `ℂ^{Φ × n}` for the signs `ε(w, i) = s_i`. -/
theorem infiniteAdeleAddChar_realCoord [DecidableEq n] [DecidableEq (InfinitePlace E)]
    (s : n → ℤˣ) (x y : InfinitePlace E × n → ℂ) :
    (infiniteAdeleAddChar E (algebraMap E (InfiniteAdeleRing E) (W.j / 2) *
        (star (W.realCoord y) ⬝ᵥ diagonal (fun i ↦ ((s i : ℤ) : InfiniteAdeleRing E)) *ᵥ
          W.realCoord x)) : ℂ) =
      Fock.heisenbergDatum (Fock.blockSign (InfinitePlace E) s) x y := by
  set H := ∑ p : InfinitePlace E × n, ((s p.2 : ℤ) : ℂ) * (conj (y p) * x p)
  have hconj : ∑ p : InfinitePlace E × n, ((s p.2 : ℤ) : ℂ) * (conj (x p) * y p) = conj H := by
    rw [_root_.map_sum]
    refine Finset.sum_congr rfl fun p _ ↦ ?_
    simp [mul_comm]
  rw [infiniteAdeleAddChar_apply, W.infiniteAdeleTrace_realCoord, Real.fourierChar_apply,
    Fock.heisenbergDatum_apply, Fock.star_dotProduct_signMatrix_mulVec,
    Fock.star_dotProduct_signMatrix_mulVec]
  simp only [Fock.blockSign]
  rw [hconj, Complex.sub_conj]
  congr 1
  push_cast
  field_simp

/-- **The adelic Heisenberg datum in coordinates.** In the coordinates `(y, z) ↦ (κ y, α z)`, the
adelic Heisenberg datum `β_s(x, y) = ψ(½ j · y* ε_s x)` is the Fock datum of the real
coordinates, for the signs `(w, i) ↦ s_i`, times the finite datum `ψ_f(½ j · (α z′)* (α z))` of
the finite coordinates. -/
theorem adelicHeisenbergDatum_coordEquiv [DecidableEq n] [DecidableEq (InfinitePlace E)]
    (s : n → ℤˣ) (x y : (InfinitePlace E × n → ℂ) × (n → 𝔸ᶠ[E])) :
    adelicHeisenbergDatum n (W.j / 2) W.half_j_mem_skewAdjoint s (W.coordEquiv x)
        (W.coordEquiv y) =
      Fock.heisenbergDatum (Fock.blockSign (InfinitePlace E) s) x.1 y.1 *
        finiteAdeleAddChar E (algebraMap E 𝔸ᶠ[E] (W.j / 2) *
          (star (W.finCoord y.2) ⬝ᵥ W.finCoord x.2)) := by
  rw [adelicHeisenbergDatum_apply, coordEquiv_apply, coordEquiv_apply,
    infiniteAdeleAddChar_realCoord]

/-- The adelic Heisenberg datum on real vectors is the Fock datum, for the signs
`(w, i) ↦ s_i`. -/
theorem adelicHeisenbergDatum_realVec [DecidableEq n] [DecidableEq (InfinitePlace E)]
    (s : n → ℤˣ) (x y : InfinitePlace E × n → ℂ) :
    adelicHeisenbergDatum n (W.j / 2) W.half_j_mem_skewAdjoint s (W.realVec x) (W.realVec y) =
      Fock.heisenbergDatum (Fock.blockSign (InfinitePlace E) s) x y := by
  rw [realVec, realVec, adelicHeisenbergDatum_coordEquiv]
  simp

/-! ### The vacuum in coordinates -/

/-- **The semicharacter as a value of `ψ_f`**: `semi(z) = ψ_f(−¼ (α z)* (α z))` for every
`z ∈ 𝔸_f^n`. Indeed `½ j c₀ = (j − 1)/4`, and `ψ_f` is trivial on the skew-adjoint finite adele
`¼ j (α z)* (α z)`. -/
theorem semichar_eq_finiteAdeleAddChar (z : n → 𝔸ᶠ[E]) :
    W.semichar z =
      finiteAdeleAddChar E (algebraMap E 𝔸ᶠ[E] (-4⁻¹) * ∑ i, star (W.α • z i) * (W.α • z i)) := by
  set S := ∑ i, star (z i) * z i
  have hS : star S = S := by simp only [S, star_sum, star_mul, star_star, mul_comm]
  set a : 𝔸ᶠ[E] := (W.α : 𝔸ᶠ[E])
  have hαz : ∑ i, star (W.α • z i) * (W.α • z i) = a * star a * S := by
    simp only [Units.smul_def, smul_eq_mul, star_mul, S, Finset.mul_sum, a]
    exact Finset.sum_congr rfl fun i _ ↦ by ring
  -- `j c₀ / 2 = j / 4 - 1 / 4` in `E`
  have hj : W.j * (W.traceOne / 2) = W.j / 4 + -4⁻¹ := by
    rw [traceOne_def]
    field_simp [W.j_ne_zero]
    ring
  have hsplit : (W.scaleIdele : 𝔸ᶠ[E]) * (algebraMap E 𝔸ᶠ[E] (W.traceOne / 2) * S) =
      algebraMap E 𝔸ᶠ[E] (W.j / 4) * (a * star a * S) +
        algebraMap E 𝔸ᶠ[E] (-4⁻¹) * (a * star a * S) := by
    rw [← add_mul, ← map_add, ← hj, map_mul, coe_scaleIdele]
    ring
  have hskew : algebraMap E 𝔸ᶠ[E] (W.j / 4) * (a * star a * S) ∈ skewAdjoint 𝔸ᶠ[E] := by
    rw [skewAdjoint.mem_iff, star_mul, ← algebraMap_star_comm, star_div₀, W.star_j, star_ofNat,
      star_mul, star_mul, star_star, hS, neg_div, map_neg]
    ring
  rw [semichar_apply, selfDualAddChar_apply, hsplit, AddChar.map_add_eq_mul,
    finiteAdeleAddChar_eq_one_of_mem_skewAdjoint hskew, one_mul, hαz]

/-- The quadratic form `π Σ_{i,w} |j|_w ‖(κ y)_{i,w}‖²` of the infinite vacuum in real
coordinates is `|y|²/2`. -/
private theorem pi_mul_sum_norm_realCoord_sq (y : InfinitePlace E × n → ℂ) :
    π * ∑ i, ∑ w : InfinitePlace E, w W.j * ‖W.realCoord y i w‖ ^ 2 =
      (∑ p : InfinitePlace E × n, ‖y p‖ ^ 2) / 2 := by
  have h (i : n) (w : InfinitePlace E) :
      w W.j * ‖W.realCoord y i w‖ ^ 2 = (2 * π)⁻¹ * ‖y (w, i)‖ ^ 2 := by
    rw [norm_realCoord_apply, mul_pow, ← mul_assoc, apply_j_mul_realScale_sq]
  simp only [h, ← Finset.mul_sum, Fintype.sum_prod_type]
  rw [Finset.sum_comm]
  field_simp

open scoped Classical in
/-- **The adelic vacuum in coordinates**: at `(κ y, α z)` the adelic vacuum is the Gaussian
`exp(−|y|²/2)` of the Fock model (`TauCeti.Fock.gaussian`) times `semi(z)` if `z ∈ Ô^n`, and `0`
otherwise. -/
theorem vacuum_realCoord_finCoord (y : InfinitePlace E × n → ℂ) (z : n → 𝔸ᶠ[E]) :
    W.vacuum (fun i ↦ ((W.realCoord y i, W.finCoord z i) : AdeleRing (𝓞 E) E)) =
      Fock.gaussian (InfinitePlace E × n) y *
        if ∀ i, z i ∈ integralAdeles (𝓞 E) E then (W.semichar z : ℂ) else 0 := by
  set x : n → AdeleRing (𝓞 E) E := fun i ↦ (W.realCoord y i, W.finCoord z i)
  -- `AdeleRing (𝓞 E) E` is by definition the product `E_∞ × 𝔸_f`
  have hx₁ (i : n) : (x i).1 = W.realCoord y i := (rfl)
  have hx₂ (i : n) : (x i).2 = W.α • z i := (rfl)
  have hiff : (∀ i, W.α⁻¹ • (x i).2 ∈ integralAdeles (𝓞 E) E) ↔
      ∀ i, z i ∈ integralAdeles (𝓞 E) E := by
    simp only [hx₂, inv_smul_smul]
  have hexp : (Real.exp (-(π * ∑ i, ∑ w : InfinitePlace E, w W.j * ‖(x i).1 w‖ ^ 2)) : ℂ) =
      Fock.gaussian (InfinitePlace E × n) y := by
    simp only [hx₁]
    rw [W.pi_mul_sum_norm_realCoord_sq, Fock.gaussian_apply, Complex.ofReal_exp]
    push_cast
    rw [neg_div]
  by_cases h : ∀ i, z i ∈ integralAdeles (𝓞 E) E
  · rw [W.vacuum_of_forall_mem (hiff.mpr h), hexp, W.semichar_eq_finiteAdeleAddChar]
    simp only [h, implies_true, ↓reduceIte, hx₂]
  · rw [W.vacuum_of_not_forall_mem (hiff.not.mpr h)]
    simp only [h, ↓reduceIte, mul_zero]

/-! ### The measure -/

variable (n) in
/-- The **measure `μ` of the adelic vacuum** on `𝔸^n = E_∞^n × 𝔸_f^n`: the image under the
coordinates `(y, z) ↦ (κ y, α z)` of `π^{−|Φ × n|}` times Lebesgue measure on `ℂ^{Φ × n}`
(`TauCeti.Fock.measure`) times the Haar measure `λ` on `𝔸_f^n` with `λ(Ô^n) = 1`, the product of
the Haar measures on `𝔸_f` giving `Ô` mass one. -/
def vacuumMeasure : Measure ((n → InfiniteAdeleRing E) × (n → 𝔸ᶠ[E])) :=
  ((Fock.measure (InfinitePlace E × n)).prod
    (Measure.pi fun _ : n ↦ addHaarMeasure (integralAdelesPositiveCompacts (𝓞 E) E))).map
      W.coordEquiv

theorem vacuumMeasure_def :
    W.vacuumMeasure n = ((Fock.measure (InfinitePlace E × n)).prod
      (Measure.pi fun _ : n ↦ addHaarMeasure (integralAdelesPositiveCompacts (𝓞 E) E))).map
        W.coordEquiv :=
  (rfl)

/-- The coordinates carry `π^{−|Φ × n|}` Lebesgue measure times `λ` to `μ`. -/
theorem measurePreserving_coordEquiv :
    MeasurePreserving W.coordEquiv ((Fock.measure (InfinitePlace E × n)).prod
      (Measure.pi fun _ : n ↦ addHaarMeasure (integralAdelesPositiveCompacts (𝓞 E) E)))
      (W.vacuumMeasure n) :=
  ⟨W.coordEquiv.continuous.measurable, W.vacuumMeasure_def.symm⟩

/-- `μ` is an additive Haar measure on `𝔸^n`. -/
instance isAddHaarMeasure_vacuumMeasure : (W.vacuumMeasure n).IsAddHaarMeasure := by
  rw [vacuumMeasure_def]
  exact W.coordEquiv.isAddHaarMeasure_map _

end WeilData

end TauCeti
