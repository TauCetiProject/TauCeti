/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.NumberField.CMField.AdeleStar
public import TauCeti.NumberTheory.NumberField.Global.Adeles.AddChar
public import TauCeti.NumberTheory.NumberField.Global.HeckeCharacter.Splitting
import TauCeti.LinearAlgebra.Matrix.DotProduct
import TauCeti.NumberTheory.NumberField.CMField.AddChar

/-!
# Weil data of a CM field

Let `E` be a CM field with complex conjugation `x ↦ conj x`, a CM type `Φ`, finite adeles `𝔸_f`,
integral finite adeles `Ô`, different `𝔇`, and let `ψ_f` be the standard character of `𝔸_f`
(`TauCeti.GlobalNumberFields.finiteAdeleAddChar`). **Weil data** `(j, α, υ)` for `E` and `Φ`
consist of

* an element `j ∈ E` with `conj j = −j` and `Im φ(j) > 0` for every embedding `φ ∈ Φ`;
* a finite idele `α` such that `ord_w(j α (conj α)) = −ord_w(𝔇)` at every finite place `w`, that
  is, such that `j α (conj α)` generates the inverse different;
* a splitting character `υ` of `E` for `Φ`
  (`TauCeti.GlobalNumberFields.HeckeCharacter.IsSplitting`);

such that `c₀ = (1 − j⁻¹)/2` is an algebraic integer and `υ(ϖ_w) = −1` for every uniformiser `ϖ_w`
at a finite place `w = conj w`.

These data fix the Weil representation of the unitary groups of hermitian spaces over `E`: `j`
turns a hermitian form into the symplectic form of a Heisenberg group, `α` scales the lattice
`α Ô^n` on which the finite part of the vacuum lives, and `υ` splits the metaplectic cover. This
file records the scalars built from them:

* `c₀ = (1 − j⁻¹)/2`, an algebraic integer with `c₀ + conj c₀ = 1` (`TauCeti.WeilData.traceOne`);
* the finite idele `t = j α (conj α)` (`TauCeti.WeilData.scaleIdele`), a generator of `𝔇⁻¹`;
* the character `ψ₀(z) = ψ_f(t z)` of `𝔸_f`, for which `Ô` is self-dual: `z ∈ Ô`
  exactly when `ψ₀(z u) = 1` for every `u ∈ Ô`
  (`TauCeti.WeilData.forall_selfDualAddChar_mul_eq_one_iff`);
* the real scale `κ_w = (2π Im Φ_w(j))^{−1/2}` at an infinite place `w`
  (`TauCeti.WeilData.realScale`), where `Im Φ_w(j) = |j|_w`;
* the Hecke character `χ_𝔸(x) = υ(x) |x|^{−1/2}` (`TauCeti.WeilData.adelicChar`);
* the **adelic vacuum** on `𝔸^n`,
  `vac(x) = exp(−π Σ_{i,w} Im Φ_w(j) |x_{i,w}|²) · ψ_f(−¼ x_f* x_f)` if `x_f ∈ α Ô^n` and `0`
  otherwise (`TauCeti.WeilData.vacuum`);
* the **semicharacter** `semi(z) = ψ₀(½ c₀ z* z)` on `𝔸_f^n` (`TauCeti.WeilData.semichar`).

The definition of Weil data makes sense for every CM field. Splitting characters exist only under
a condition on the roots of unity of `E`: by
`TauCeti.GlobalNumberFields.HeckeCharacter.IsSplitting.prod_embedding_div_norm_eq_one` the phases
of every global unit multiply to one, which fails for `i ∈ ℚ(i)`.

## Main definitions

* `TauCeti.WeilData Φ`: Weil data for `E` and the CM type `Φ`.
* `TauCeti.WeilData.traceOne`, `TauCeti.WeilData.scaleIdele`, `TauCeti.WeilData.selfDualAddChar`,
  `TauCeti.WeilData.realScale`, `TauCeti.WeilData.adelicChar`, `TauCeti.WeilData.vacuum`,
  `TauCeti.WeilData.semichar`: the scalars, characters and functions above.

## Main results

* `TauCeti.WeilData.im_embedding_j`: `Im Φ_w(j) = |j|_w`, so it is positive.
* `TauCeti.WeilData.traceOne_add_star`: `c₀ + conj c₀ = 1`.
* `TauCeti.WeilData.toFractionalIdeal_scaleIdele`: `j α (conj α)` generates `𝔇⁻¹`.
* `TauCeti.WeilData.forall_selfDualAddChar_mul_eq_one_iff`: `Ô` is self-dual for `ψ₀`.
* `TauCeti.WeilData.selfDualAddChar_eq_one_of_mem`, `TauCeti.WeilData.selfDualAddChar_star`,
  `TauCeti.WeilData.selfDualAddChar_sub_star`: `ψ₀` is trivial on `Ô`, `ψ₀(conj z) = ψ₀(−z)`, and
  `ψ₀(w − conj w) = ψ₀(w)²`.
* `TauCeti.WeilData.selfDualAddChar_algebraMap_div_two_mul_sq`: `ψ₀(½ x z)² = ψ₀(x z)` for
  `x ∈ E`.
* `TauCeti.WeilData.semichar_sq_of_forall_mem`, `TauCeti.WeilData.semichar_add_of_forall_mem`: on
  `Ôⁿ` the semicharacter takes the values `±1` and satisfies
  `semi(a + b) = semi(a) semi(b) ψ₀(½ b* a)`.
* `TauCeti.WeilData.vacuum_zero`, `TauCeti.WeilData.norm_vacuum_of_forall_mem`,
  `TauCeti.WeilData.vacuum_of_not_forall_mem`, `TauCeti.WeilData.continuous_vacuum`: the vacuum
  is `1` at `0`, a Gaussian in absolute value on `𝔸_∞^n × α Ô^n`, zero off it, and continuous.

## References

* S. S. Kudla, *Splitting metaplectic covers of dual reductive pairs*, Israel J. Math. 87 (1994).
* M. Harris, S. S. Kudla and W. J. Sweet, *Theta dichotomy for unitary groups*, J. Amer. Math. Soc.
  9 (1996), §1.

## Attribution

The data and the scalars built from them follow `New.WeilData`, `New.WeilData.traceOne`,
`New.vacuumFn` and `New.stdLattice.semichar` in `src/Lib/Weil/Construction/WeilData.lean` and
`src/Lib/Weil/Construction/FiniteMultiplier.lean` of grh-lean
(https://github.com/lsernau/grh-lean, Apache 2.0, Copyright 2026 Anthropic, PBC).
-/

public section
noncomputable section

open IsDedekindDomain IsDedekindDomain.FiniteAdeleRing NumberField NumberField.IsCMField
open TauCeti.GlobalNumberFields
open scoped NumberField nonZeroDivisors Real ComplexConjugate

namespace TauCeti

variable {E : Type*} [Field E] [NumberField E] [IsCMField E]

/-- **Weil data** `(j, α, υ)` for a CM field `E` and a CM type `Φ`: an element `j ∈ E` with
`conj j = −j` and `Im φ(j) > 0` for `φ ∈ Φ`, such that `(1 − j⁻¹)/2` is an algebraic integer; a
finite idele `α` such that `j α (conj α)` generates the inverse different `𝔇⁻¹`, that is,
`ord_w(j α (conj α)) = −ord_w(𝔇)` at every finite place `w`; and a splitting character `υ` of `E`
for `Φ` with `υ(ϖ_w) = −1` at every uniformiser `ϖ_w` of a finite place `w = conj w`. -/
@[ext]
structure WeilData (Φ : CMType E) where
  /-- The element `j` of `E`. -/
  j : E
  /-- `j` is purely imaginary: `conj j = −j`. -/
  star_j : star j = -j
  /-- `j` has positive imaginary part under every embedding of `Φ`. -/
  im_embedding_j_pos (φ : E →+* ℂ) (hφ : φ ∈ Φ) : 0 < (φ j).im
  /-- `(1 − j⁻¹)/2` is an algebraic integer. -/
  isIntegral_one_sub_inv_j_div_two : IsIntegral ℤ ((1 - j⁻¹) / 2)
  /-- The finite idele `α`. -/
  α : (FiniteAdeleRing (𝓞 E) E)ˣ
  /-- The fractional ideal of `j α (conj α)` is the inverse different `𝔇⁻¹`. -/
  spanSingleton_mul_toFractionalIdeal :
    FractionalIdeal.spanSingleton (𝓞 E)⁰ j *
        (toFractionalIdeal (α * star α) : FractionalIdeal (𝓞 E)⁰ E) =
      FractionalIdeal.dual ℤ ℚ 1
  /-- The splitting character `υ`. -/
  υ : HeckeCharacter E
  /-- `υ` is a splitting character of `E` for `Φ`. -/
  isSplitting : υ.IsSplitting Φ
  /-- `υ(ϖ_w) = −1` at every uniformiser `ϖ_w` of a finite place `w` fixed by conjugation. -/
  finiteComponent_eq_neg_one (w : HeightOneSpectrum (𝓞 E)) (hw : w.conjPlace = w)
    (ϖ : (w.adicCompletion E)ˣ) (hϖ : IsUniformizer (w.adicCompletion E) ϖ) :
    HeckeCharacter.finiteComponent υ w ϖ = -1

namespace WeilData

variable {Φ : CMType E} (W : WeilData Φ)

/-! ### The element `j` -/

/-- `j` is purely imaginary under every complex embedding. -/
@[simp]
theorem re_embedding_j (φ : E →+* ℂ) : (φ W.j).re = 0 := by
  have h : conj (φ W.j) = -φ W.j := by
    rw [← complexEmbedding_complexConj, ← star_eq_complexConj, W.star_j, map_neg]
  have := congrArg Complex.re h
  rw [Complex.conj_re, Complex.neg_re] at this
  linarith

/-- **`Im Φ_w(j) = |j|_w`**: `Φ_w(j)` is purely imaginary with positive imaginary part. -/
@[simp]
theorem im_embedding_j (w : InfinitePlace E) : (Φ.embedding w W.j).im = w W.j := by
  have him := W.im_embedding_j_pos _ (Φ.embedding_mem w)
  rw [← Φ.norm_embedding_apply w, Complex.norm_eq_sqrt_sq_add_sq, W.re_embedding_j]
  simp [Real.sqrt_sq him.le]

/-- `j` has positive absolute value at every infinite place. -/
theorem apply_j_pos (w : InfinitePlace E) : 0 < w W.j :=
  W.im_embedding_j w ▸ W.im_embedding_j_pos _ (Φ.embedding_mem w)

/-- `j ≠ 0`. -/
theorem j_ne_zero : W.j ≠ 0 := by
  obtain ⟨w⟩ : Nonempty (InfinitePlace E) := inferInstance
  exact fun h ↦ (W.apply_j_pos w).ne' (by simp [h])

/-! ### The algebraic integer `c₀` -/

/-- The element `c₀ = (1 − j⁻¹)/2` of `E`. -/
def traceOne : E := (1 - W.j⁻¹) / 2

/-- The defining formula of `c₀`. -/
theorem traceOne_def : W.traceOne = (1 - W.j⁻¹) / 2 := (rfl)

/-- `c₀ = (1 − j⁻¹)/2` is an algebraic integer. -/
theorem isIntegral_traceOne : IsIntegral ℤ W.traceOne :=
  W.isIntegral_one_sub_inv_j_div_two

/-- `c₀` is integral at every finite place. -/
theorem algebraMap_traceOne_mem_integralAdeles :
    algebraMap E (FiniteAdeleRing (𝓞 E) E) W.traceOne ∈ integralAdeles (𝓞 E) E :=
  (algebraMap_mem_integralAdeles_iff _).2 ⟨⟨W.traceOne, W.isIntegral_traceOne⟩, rfl⟩

/-- **`c₀ + conj c₀ = 1`**, as `j⁻¹` is purely imaginary. -/
theorem traceOne_add_star : W.traceOne + star W.traceOne = 1 := by
  simp only [traceOne_def, star_div₀, star_sub, star_inv₀, W.star_j, star_one, star_ofNat]
  ring

/-! ### The self-dual character `ψ₀` -/

/-- The finite idele `t = j α (conj α)` that scales `ψ_f` to `ψ₀`; it generates the inverse
different `𝔇⁻¹` (`TauCeti.WeilData.toFractionalIdeal_scaleIdele`). -/
def scaleIdele : (FiniteAdeleRing (𝓞 E) E)ˣ :=
  unitEmbedding (𝓞 E) E (Units.mk0 W.j W.j_ne_zero) * (W.α * star W.α)

/-- The finite adele underlying `t` is `j α (conj α)`. -/
@[simp]
theorem coe_scaleIdele :
    (W.scaleIdele : FiniteAdeleRing (𝓞 E) E) =
      algebraMap E _ W.j * W.α * star (W.α : FiniteAdeleRing (𝓞 E) E) := by
  rw [scaleIdele, Units.val_mul, Units.val_mul, Units.coe_star, unitEmbedding_apply, Units.val_mk0,
    mul_assoc]

/-- **`t = j α (conj α)` generates the inverse different**: its fractional ideal is `𝔇⁻¹`. -/
theorem toFractionalIdeal_scaleIdele :
    toFractionalIdeal W.scaleIdele = Units.mk0 (FractionalIdeal.dual ℤ ℚ 1)
      (FractionalIdeal.dual_ne_zero ℤ ℚ one_ne_zero) := by
  refine Units.ext ?_
  rw [scaleIdele, map_mul, toFractionalIdeal_unitEmbedding, Units.val_mul, coe_toPrincipalIdeal,
    Units.val_mk0, Units.val_mk0, W.spanSingleton_mul_toFractionalIdeal]

/-- The character `ψ₀(z) = ψ_f(t z)` of the finite adeles, where `t = j α (conj α)`. -/
def selfDualAddChar : AddChar (FiniteAdeleRing (𝓞 E) E) Circle :=
  (finiteAdeleAddChar E).mulShift (W.scaleIdele : _)

/-- The defining formula `ψ₀(z) = ψ_f(t z)`, where `t = j α (conj α)`
(`TauCeti.WeilData.coe_scaleIdele`). -/
theorem selfDualAddChar_apply (z : FiniteAdeleRing (𝓞 E) E) :
    W.selfDualAddChar z = finiteAdeleAddChar E (W.scaleIdele * z) :=
  (rfl)

/-- `ψ₀` is continuous. -/
@[fun_prop, continuity]
theorem continuous_selfDualAddChar : Continuous W.selfDualAddChar :=
  continuous_finiteAdeleAddChar.comp (continuous_const.mul continuous_id)

/-- **`Ô` is self-dual for `ψ₀`**: a finite adele `z` is integral exactly when `ψ₀(z u) = 1` for
every `u ∈ Ô`, because `t = j α (conj α)` generates the inverse different. -/
theorem forall_selfDualAddChar_mul_eq_one_iff (z : FiniteAdeleRing (𝓞 E) E) :
    (∀ u ∈ integralAdeles (𝓞 E) E, W.selfDualAddChar (z * u) = 1) ↔
      z ∈ integralAdeles (𝓞 E) E := by
  simp_rw [selfDualAddChar_apply, ← mul_assoc]
  rw [forall_finiteAdeleAddChar_mul_eq_one_iff,
    mem_finiteAdelicIdeal_iff W.scaleIdele W.toFractionalIdeal_scaleIdele,
    Units.inv_mul_cancel_left]

/-- `t = j α (conj α)` is purely imaginary: `conj t = −t`. -/
theorem star_coe_scaleIdele :
    star (W.scaleIdele : FiniteAdeleRing (𝓞 E) E) = -W.scaleIdele := by
  rw [coe_scaleIdele, star_mul, star_mul, star_star, ← algebraMap_star_comm, W.star_j, map_neg]
  ring

/-- `ψ₀` is trivial on `Ô`, which is self-dual for it. -/
theorem selfDualAddChar_eq_one_of_mem {z : FiniteAdeleRing (𝓞 E) E}
    (hz : z ∈ integralAdeles (𝓞 E) E) : W.selfDualAddChar z = 1 := by
  simpa using (W.forall_selfDualAddChar_mul_eq_one_iff 1).2 (one_mem _) z hz

/-- `ψ₀(conj z) = ψ₀(−z)`, since `ψ_f` is invariant under conjugation and `conj t = −t`. -/
theorem selfDualAddChar_star (z : FiniteAdeleRing (𝓞 E) E) :
    W.selfDualAddChar (star z) = W.selfDualAddChar (-z) := by
  rw [selfDualAddChar_apply, selfDualAddChar_apply, ← finiteAdeleAddChar_star, star_mul,
    star_star, star_coe_scaleIdele, mul_neg, mul_neg, mul_comm]

/-- `ψ₀(w − conj w) = ψ₀(w)²`. -/
theorem selfDualAddChar_sub_star (w : FiniteAdeleRing (𝓞 E) E) :
    W.selfDualAddChar (w - star w) = W.selfDualAddChar w ^ 2 := by
  rw [sub_eq_add_neg, AddChar.map_add_eq_mul, ← star_neg, selfDualAddChar_star, neg_neg, sq]

/-- **Halving under `ψ₀`**: `ψ₀(½ x z)² = ψ₀(x z)` for `x ∈ E`. -/
theorem selfDualAddChar_algebraMap_div_two_mul_sq (x : E) (z : FiniteAdeleRing (𝓞 E) E) :
    W.selfDualAddChar (algebraMap E _ (x / 2) * z) ^ 2 =
      W.selfDualAddChar (algebraMap E _ x * z) := by
  rw [← AddChar.map_nsmul_eq_pow, nsmul_eq_mul, Nat.cast_ofNat, ← mul_assoc,
    ← map_ofNat (algebraMap E (FiniteAdeleRing (𝓞 E) E)) 2, ← map_mul,
    mul_div_cancel₀ _ two_ne_zero]

/-! ### The real scales and the Hecke character `χ_𝔸` -/

/-- The real scale `κ_w = (2π Im Φ_w(j))^{−1/2}` at an infinite place `w`. -/
def realScale (w : InfinitePlace E) : ℝ := (2 * π * (Φ.embedding w W.j).im) ^ (-(2⁻¹ : ℝ))

/-- `κ_w = (2π |j|_w)^{−1/2}`. -/
theorem realScale_eq (w : InfinitePlace E) :
    W.realScale w = (2 * π * w W.j) ^ (-(2⁻¹ : ℝ)) := by
  rw [realScale, im_embedding_j]

/-- The real scales are positive. -/
theorem realScale_pos (w : InfinitePlace E) : 0 < W.realScale w := by
  rw [realScale_eq]
  exact Real.rpow_pos_of_pos (by have := W.apply_j_pos w; positivity) _

/-- The Hecke character `χ_𝔸(x) = υ(x) |x|^{−1/2}`. -/
def adelicChar : HeckeCharacter E := W.υ * HeckeCharacter.normPow E (-(2⁻¹ : ℂ))

/-- The defining formula `χ_𝔸(x) = υ(x) |x|^{−1/2}`. -/
@[simp]
theorem adelicChar_apply (c : IdeleClassGroup (𝓞 E) E) :
    (W.adelicChar c : ℂ) = W.υ c * (((ideleClassNorm c : NNReal) : ℝ) : ℂ) ^ (-(2⁻¹ : ℂ)) := by
  simp [adelicChar]

/-- `|χ_𝔸(x)| = |x|^{−1/2}`. -/
theorem norm_adelicChar_apply (c : IdeleClassGroup (𝓞 E) E) :
    ‖(W.adelicChar c : ℂ)‖ = ((ideleClassNorm c : NNReal) : ℝ) ^ (-(2⁻¹ : ℝ)) := by
  rw [adelicChar, ContinuousMonoidHom.mul_apply, Units.val_mul, norm_mul,
    W.isSplitting.norm_apply, one_mul, HeckeCharacter.norm_normPow_apply]
  simp

/-! ### The adelic vacuum and the semicharacter -/

variable {n : Type*} [Fintype n]

open scoped Classical in
/-- The **adelic vacuum** on `𝔸^n`: `exp(−π Σ_{i,w} Im Φ_w(j) |x_{i,w}|²) · ψ_f(−¼ x_f* x_f)` if the
finite part `x_f` lies in `α Ô^n`, and `0` otherwise, where `Im Φ_w(j) = |j|_w`
(`TauCeti.WeilData.im_embedding_j`) and `x_f* x_f = Σ_i conj x_{i,f} x_{i,f}`. -/
def vacuum (x : n → AdeleRing (𝓞 E) E) : ℂ :=
  Real.exp (-(π * ∑ i, ∑ w : InfinitePlace E, w W.j * ‖(x i).1 w‖ ^ 2)) *
    if ∀ i, W.α⁻¹ • (x i).2 ∈ integralAdeles (𝓞 E) E then
      (finiteAdeleAddChar E (algebraMap E _ (-4⁻¹) * ∑ i, star (x i).2 * (x i).2) : ℂ)
    else 0

/-- The vacuum on `𝔸_∞^n × α Ô^n`. -/
theorem vacuum_of_forall_mem {x : n → AdeleRing (𝓞 E) E}
    (hx : ∀ i, W.α⁻¹ • (x i).2 ∈ integralAdeles (𝓞 E) E) :
    W.vacuum x = Real.exp (-(π * ∑ i, ∑ w : InfinitePlace E, w W.j * ‖(x i).1 w‖ ^ 2)) *
      (finiteAdeleAddChar E (algebraMap E _ (-4⁻¹) * ∑ i, star (x i).2 * (x i).2) : ℂ) := by
  simp only [vacuum, hx, implies_true, ↓reduceIte]

/-- The vacuum vanishes off `𝔸_∞^n × α Ô^n`. -/
theorem vacuum_of_not_forall_mem {x : n → AdeleRing (𝓞 E) E}
    (hx : ¬∀ i, W.α⁻¹ • (x i).2 ∈ integralAdeles (𝓞 E) E) :
    W.vacuum x = 0 := by
  simp only [vacuum, hx, ↓reduceIte, mul_zero]

/-- On `𝔸_∞^n × α Ô^n` the vacuum has the absolute value of a Gaussian. -/
theorem norm_vacuum_of_forall_mem {x : n → AdeleRing (𝓞 E) E}
    (hx : ∀ i, W.α⁻¹ • (x i).2 ∈ integralAdeles (𝓞 E) E) :
    ‖W.vacuum x‖ = Real.exp (-(π * ∑ i, ∑ w : InfinitePlace E, w W.j * ‖(x i).1 w‖ ^ 2)) := by
  rw [W.vacuum_of_forall_mem hx, norm_mul, Circle.norm_coe, mul_one, Complex.norm_real,
    Real.norm_of_nonneg (Real.exp_nonneg _)]

/-- The vacuum takes the value `1` at `0`. -/
@[simp]
theorem vacuum_zero : W.vacuum (0 : n → AdeleRing (𝓞 E) E) = 1 := by
  rw [W.vacuum_of_forall_mem fun i ↦ by simp]
  simp

/-- The vacuum is continuous: `α Ô^n` is open and closed. -/
@[fun_prop, continuity]
theorem continuous_vacuum : Continuous (W.vacuum (n := n)) := by
  classical
  -- the set of the `x` with `x_f ∈ α Ô^n` is open and closed, so the cut-off is continuous
  have hS : IsClopen
      {x : n → AdeleRing (𝓞 E) E | ∀ i, W.α⁻¹ • (x i).2 ∈ integralAdeles (𝓞 E) E} := by
    simp only [Set.ofPred_forall]
    refine isClopen_iInter_of_finite fun i ↦ ?_
    have hc : Continuous fun x : n → AdeleRing (𝓞 E) E ↦ W.α⁻¹ • (x i).2 := by fun_prop
    exact ⟨(isClosed_integralAdeles (𝓞 E) E).preimage hc,
      (isOpen_integralAdeles (𝓞 E) E).preimage hc⟩
  unfold vacuum
  refine Continuous.mul (by fun_prop) (Continuous.if (fun a ha ↦ ?_) ?_ continuous_const)
  · rw [hS.frontier_eq] at ha
    exact ha.elim
  exact continuous_subtypeVal.comp (continuous_finiteAdeleAddChar.comp (by fun_prop))

/-- The **semicharacter** `semi(z) = ψ₀(½ c₀ z* z)` on `𝔸_f^n`, where `z* z = Σ_i conj z_i z_i`. -/
def semichar (z : n → FiniteAdeleRing (𝓞 E) E) : Circle :=
  W.selfDualAddChar (algebraMap E _ (W.traceOne / 2) * ∑ i, star (z i) * z i)

/-- The defining formula `semi(z) = ψ₀(½ c₀ z* z)`. -/
theorem semichar_apply (z : n → FiniteAdeleRing (𝓞 E) E) :
    W.semichar z = W.selfDualAddChar (algebraMap E _ (W.traceOne / 2) * ∑ i, star (z i) * z i) :=
  (rfl)

/-- The semicharacter takes the value `1` at `0`. -/
@[simp]
theorem semichar_zero : W.semichar (0 : n → FiniteAdeleRing (𝓞 E) E) = 1 := by
  simp [semichar]

/-- The semicharacter is continuous. -/
@[fun_prop, continuity]
theorem continuous_semichar : Continuous (W.semichar (n := n)) :=
  (W.continuous_selfDualAddChar.comp (by fun_prop)).congr fun z ↦ (W.semichar_apply z).symm

/-- `ψ₀(½ c₀ z)² = ψ₀(c₀ z) = 1` for `z ∈ Ô`, as `c₀` is integral. -/
theorem selfDualAddChar_traceOne_div_two_mul_sq_of_mem {z : FiniteAdeleRing (𝓞 E) E}
    (hz : z ∈ integralAdeles (𝓞 E) E) :
    W.selfDualAddChar (algebraMap E _ (W.traceOne / 2) * z) ^ 2 = 1 := by
  rw [selfDualAddChar_algebraMap_div_two_mul_sq]
  exact W.selfDualAddChar_eq_one_of_mem (mul_mem W.algebraMap_traceOne_mem_integralAdeles hz)

/-- On `Ôⁿ` the semicharacter takes the values `±1`: `semi(z)² = ψ₀(c₀ z* z) = 1`. -/
theorem semichar_sq_of_forall_mem {z : n → FiniteAdeleRing (𝓞 E) E}
    (hz : ∀ i, z i ∈ integralAdeles (𝓞 E) E) : W.semichar z ^ 2 = 1 :=
  W.selfDualAddChar_traceOne_div_two_mul_sq_of_mem
    (dotProduct_mem (forall_star_apply_mem_integralAdeles_iff.2 hz) hz)

/-- **The semicharacter law** on `Ôⁿ`: `semi(a + b) = semi(a) semi(b) ψ₀(½ b* a)` for integral
vectors `a` and `b`. -/
theorem semichar_add_of_forall_mem {a b : n → FiniteAdeleRing (𝓞 E) E}
    (ha : ∀ i, a i ∈ integralAdeles (𝓞 E) E) (hb : ∀ i, b i ∈ integralAdeles (𝓞 E) E) :
    W.semichar (a + b) =
      W.semichar a * W.semichar b * W.selfDualAddChar (algebraMap E _ 2⁻¹ * (star b ⬝ᵥ a)) := by
  -- With `u = b* a`, `(a + b)* (a + b) = a* a + b* b + (u + conj u)`, and for `c = ½ c₀` the
  -- quotient of `ψ₀(c (u + conj u))` by `ψ₀(½ u)` is `ψ₀(w − conj w) = ψ₀(w)²` with
  -- `w = c conj u`, because `c − ½ = −conj c`; it is `1` because `u` is integral.
  set u := star b ⬝ᵥ a
  set c := algebraMap E (FiniteAdeleRing (𝓞 E) E) (W.traceOne / 2)
  have hu : u ∈ integralAdeles (𝓞 E) E :=
    dotProduct_mem (forall_star_apply_mem_integralAdeles_iff.2 hb) ha
  have hstar : star u = ∑ i, star (a i) * b i := by
    simp only [u, dotProduct, Pi.star_apply, star_sum, star_mul, star_star]
  have hsum : ∑ i, star ((a + b) i) * (a + b) i =
      ∑ i, star (a i) * a i + ∑ i, star (b i) * b i + (u + star u) := by
    rw [hstar]
    simp only [u, dotProduct, Pi.add_apply, Pi.star_apply, star_add, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun i _ ↦ by ring
  have hc : c - algebraMap E _ 2⁻¹ = -star c := by
    rw [← algebraMap_star_comm, ← map_sub, ← map_neg, star_div₀, star_ofNat]
    congr 1
    linear_combination (2⁻¹ : E) * W.traceOne_add_star
  have hw : W.selfDualAddChar (c * star u - star (c * star u)) = 1 := by
    rw [selfDualAddChar_sub_star]
    exact W.selfDualAddChar_traceOne_div_two_mul_sq_of_mem (star_mem_integralAdeles_iff.2 hu)
  have hsplit : c * (u + star u) =
      algebraMap E _ 2⁻¹ * u + (c * star u - star (c * star u)) := by
    rw [star_mul, star_star, mul_comm u (star c)]
    linear_combination u * hc
  rw [semichar_apply, semichar_apply, semichar_apply, hsum, mul_add, mul_add, hsplit]
  simp only [AddChar.map_add_eq_mul, hw, mul_one]

end WeilData

end TauCeti
