/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Polynomial.Laurent
public import Mathlib.Analysis.Normed.Algebra.Ultra
public import TauCeti.Analysis.Normed.Ring.UnitBall
public import TauCeti.RingTheory.Robba.Basic
import Mathlib.Topology.Algebra.Algebra
import Mathlib.Topology.Algebra.InfiniteSum.Nonarchimedean
import TauCeti.Analysis.Normed.Group.NullFamily
import TauCeti.Analysis.Normed.Ring.LaurentMaximum

/-!
# Evaluation of Robba series

A Robba series that converges at the norm of a nonzero point in a complete valued extension can
be evaluated there by summing its two-sided Laurent series. Evaluation is an algebra homomorphism
on the subalgebra of series converging at that radius and is bounded by the corresponding Gauss
norm. It commutes with isometric extensions of the target field. On an annular stage, evaluation
at each point of the annulus is compatible with restriction. Over a field with infinite residue
field, a point on each nonempty circle of convergence attains the Gauss norm.

For the specialized integral annulus convention with inner radius `p⁻¹`, see
`TauCeti.AnnularRing.eval`.

## References

* M. Lazard, *Les zéros des fonctions analytiques d'une variable sur un corps valué complet*,
  Publ. Math. IHÉS 14 (1962), §§1–2.
-/

public section

open Filter TauCeti.IsConvolutionRing
open scoped Topology LaurentPolynomial

namespace TauCeti.RobbaRing

section Coefficients

variable (K : Type*) [NormedCommRing K] [IsUltrametricDist K] [CompleteSpace K]

/-- The subalgebra of Robba series converging at the positive radius `ρ`. -/
def atRadius {ρ : ℝ} (hρ : 0 < ρ) : Subalgebra K (RobbaRing K) where
  carrier := {f | LaurentConvergesAt ρ (f : ℤ → K)}
  mul_mem' hf hg := hf.addRingConvolution hρ hg
  add_mem' hf hg := hf.add hg
  algebraMap_mem' c := by
    -- Membership in the carrier is exactly the convergence condition on its coefficients.
    change LaurentConvergesAt ρ (algebraMap K (RobbaRing K) c : ℤ → K)
    rw [coe_algebraMap]
    exact laurentConvergesAt_single ρ 0 c

/-- Membership in the radius subalgebra is convergence of the Laurent coefficient family. -/
@[simp]
theorem mem_atRadius {ρ : ℝ} (hρ : 0 < ρ) {f : RobbaRing K} :
    f ∈ atRadius K hρ ↔ LaurentConvergesAt ρ (f : ℤ → K) :=
  (Iff.rfl)

/-- Every Laurent monomial converges at every positive radius. -/
theorem monomial_mem_atRadius {ρ : ℝ} (hρ : 0 < ρ) (n : ℤ) (c : K) :
    monomial n c ∈ atRadius K hρ := by
  simpa only [mem_atRadius, coe_monomial] using laurentConvergesAt_single ρ n c

/-- Every series on an annular stage converges at each radius in its defining interval. -/
theorem annulus_le_atRadius {r ρ : ℝ} (hρ : 0 < ρ) (hr : r < ρ) (h₁ : ρ < 1) :
    annulus K r ≤ atRadius K hρ := fun _ hf ↦
  (mem_annularCoeff.mp (mem_annulus.mp hf)) ρ hρ hr h₁

private def annulusMonomialOne (r : ℝ) : Multiplicative ℤ →* annulus K r where
  toFun n := ⟨monomial n.toAdd 1, monomial_mem_annulus r n.toAdd 1⟩
  map_one' := Subtype.ext (by simp)
  map_mul' m n := Subtype.ext (by
    rw [Subalgebra.coe_mul, monomial_mul_monomial, one_mul, toAdd_mul])

/-- Regard a Laurent polynomial as a series on the annulus. -/
noncomputable def ofLaurentPolynomial (r : ℝ) : K[T;T⁻¹] →ₐ[K] annulus K r :=
  AddMonoidAlgebra.lift K (annulus K r) ℤ (annulusMonomialOne K r)

/-- A Laurent monomial embeds as the series supported in its degree. -/
@[simp]
theorem ofLaurentPolynomial_C_mul_T (r : ℝ) (n : ℤ) (c : K) :
    ofLaurentPolynomial K r (LaurentPolynomial.C c * LaurentPolynomial.T n) =
      ⟨monomial n c, monomial_mem_annulus r n c⟩ := by
  have hT : ofLaurentPolynomial K r (LaurentPolynomial.T n) = annulusMonomialOne K r (.ofAdd n) :=
    AddMonoidAlgebra.lift_of (annulusMonomialOne K r) (.ofAdd n)
  rw [map_mul, hT, LaurentPolynomial.C_eq_algebraMap, AlgHom.commutes]
  exact Subtype.ext (by
    simp only [Subalgebra.coe_mul, Subalgebra.coe_algebraMap, annulusMonomialOne,
      MonoidHom.coe_mk, OneHom.coe_mk, algebraMap_mul_monomial, mul_one, toAdd_ofAdd])

/-- The annular series of a Laurent polynomial has the same coefficient family. -/
@[simp]
theorem coe_ofLaurentPolynomial (r : ℝ) (P : K[T;T⁻¹]) :
    ((ofLaurentPolynomial K r P).val : ℤ → K) = P.coeff := by
  induction P using LaurentPolynomial.induction_on' with
  | add P Q hP hQ => simp only [map_add, Subalgebra.coe_add, Submodule.coe_add,
      AddMonoidAlgebra.coeff_add, Finsupp.coe_add, hP, hQ]
  | C_mul_T n c =>
    rw [ofLaurentPolynomial_C_mul_T, ← LaurentPolynomial.single_eq_C_mul_T]
    simpa only [coe_monomial, AddMonoidAlgebra.coeff_single] using
      (Finsupp.single_eq_pi_single (a := n) (b := c)).symm

/-- The inclusion of Laurent polynomials into the annular series is injective. -/
theorem ofLaurentPolynomial_injective (r : ℝ) : Function.Injective (ofLaurentPolynomial K r) := by
  intro P Q h
  apply AddMonoidAlgebra.ext
  apply DFunLike.ext
  intro n
  simpa only [coe_ofLaurentPolynomial] using congrArg
    (fun f : annulus K r ↦ (f.val : ℤ → K) n) h

end Coefficients

variable (K : Type*) [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
variable {L : Type*} [NormedField L] [NormedAlgebra K L] [CompleteSpace L]

omit [CompleteSpace K] in
private theorem summable_evalTerms {z : L} {a : ℤ → K}
    (ha : LaurentConvergesAt ‖z‖ a) :
    Summable fun n : ℤ ↦ algebraMap K L (a n) * z ^ n := by
  have : IsUltrametricDist L := IsUltrametricDist.of_normedAlgebra K
  apply NonarchimedeanAddGroup.summable_of_tendsto_cofinite_zero
  rw [tendsto_zero_iff_norm_tendsto_zero]
  simpa only [norm_mul, norm_algebraMap', norm_zpow] using laurentConvergesAt_iff.mp ha

omit [IsUltrametricDist K] [CompleteSpace K] [CompleteSpace L] in
private theorem tsum_eval_single (z : L) (n : ℤ) (c : K) :
    ∑' m, algebraMap K L (Pi.single (M := fun _ ↦ K) n c m) * z ^ m = algebraMap K L c * z ^ n := by
  rw [tsum_eq_single n]
  · simp
  · intro m hm
    simp [Pi.single_eq_of_ne hm]

variable {z : L}

private theorem tsum_eval_mul (hz : 0 < ‖z‖) (f g : atRadius K hz) :
    ∑' n : ℤ, algebraMap K L (((f * g).val : ℤ → K) n) * z ^ n =
      (∑' n : ℤ, algebraMap K L ((f.val : ℤ → K) n) * z ^ n) *
        ∑' n : ℤ, algebraMap K L ((g.val : ℤ → K) n) * z ^ n := by
  let a : ℤ → L := fun n ↦ algebraMap K L ((f.val : ℤ → K) n) * z ^ n
  let b : ℤ → L := fun n ↦ algebraMap K L ((g.val : ℤ → K) n) * z ^ n
  have ha : Summable a := summable_evalTerms K ((mem_atRadius K hz).mp f.property)
  have hb : Summable b := summable_evalTerms K ((mem_atRadius K hz).mp g.property)
  have : IsUltrametricDist L := IsUltrametricDist.of_normedAlgebra K
  -- Reindex the product of the two summable families by total degree and the second index.
  let e : ℤ × ℤ ≃ ℤ × ℤ := Equiv.prodCongrLeft fun j ↦ Equiv.addRight (-j)
  have hab : Summable (fun p : ℤ × ℤ ↦ a p.1 * b p.2) := by
    simp only [NonarchimedeanAddGroup.summable_iff_tendsto_cofinite_zero] at ha hb ⊢
    exact tendsto_mul_cofinite_nhds_zero ha hb
  have h := (e.hasSum_iff (f := fun p : ℤ × ℤ ↦ a p.1 * b p.2)).2
    (ha.hasSum.mul hb.hasSum hab)
  refine Eq.trans ?_ (h.prod_fiberwise fun n ↦ (h.summable.prod_factor n).hasSum).tsum_eq
  refine tsum_congr fun n ↦ ?_
  have hcoeff := (hasSum_coeff_mul f.val g.val n).map (algebraMap K L)
    (continuous_algebraMap K L)
  refine Eq.trans (hcoeff.mul_right (z ^ n)).tsum_eq.symm ?_
  refine tsum_congr fun j ↦ ?_
  have hzpow : z ^ (n - j) * z ^ j = z ^ n := by
    rw [← zpow_add₀ (norm_pos_iff.mp hz), sub_add_cancel]
  have he : e (n, j) = (n - j, j) := rfl
  simp only [a, b, Function.comp_apply, he, map_mul]
  rw [mul_mul_mul_comm, hzpow]

/-- Evaluate a Robba series at a nonzero point in a complete nonarchimedean extension.
The domain consists of the series converging at the norm of the point. -/
noncomputable def evalAt (hz : 0 < ‖z‖) : atRadius K hz →ₐ[K] L where
  toFun f := ∑' n : ℤ, algebraMap K L ((f.val : ℤ → K) n) * z ^ n
  map_one' := by
    simpa only [Subalgebra.coe_one, coe_one, map_one, zpow_zero, mul_one] using
      tsum_eval_single K z 0 1
  map_zero' := by simp
  map_mul' := tsum_eval_mul K hz
  map_add' f g := by
    simp only [Subalgebra.coe_add, Submodule.coe_add, Pi.add_apply, map_add, add_mul]
    exact (summable_evalTerms K ((mem_atRadius K hz).mp f.property)).tsum_add
      (summable_evalTerms K ((mem_atRadius K hz).mp g.property))
  commutes' c := by
    simpa only [Subalgebra.coe_algebraMap, coe_algebraMap, zpow_zero, mul_one] using
      tsum_eval_single K z 0 c

/-- Evaluation is the sum of the two-sided Laurent series at the given point. -/
theorem evalAt_apply (hz : 0 < ‖z‖) (f : atRadius K hz) :
    evalAt K hz f = ∑' n : ℤ, algebraMap K L ((f.val : ℤ → K) n) * z ^ n :=
  (rfl)

/-- A Laurent monomial of degree `n` evaluates to its coefficient times `z ^ n`. -/
@[simp]
theorem evalAt_monomial (hz : 0 < ‖z‖) (n : ℤ) (c : K) :
    evalAt K hz ⟨monomial n c, monomial_mem_atRadius K hz n c⟩ =
      algebraMap K L c * z ^ n := by
  rw [evalAt_apply]
  simpa only [coe_monomial] using tsum_eval_single K z n c

/-- The series of evaluated Laurent monomials converges to the value of the Robba series. -/
theorem hasSum_evalAt (hz : 0 < ‖z‖) (f : atRadius K hz) :
    HasSum (fun n : ℤ ↦ algebraMap K L ((f.val : ℤ → K) n) * z ^ n) (evalAt K hz f) := by
  rw [evalAt_apply]
  exact (summable_evalTerms K ((mem_atRadius K hz).mp f.property)).hasSum

/-- Evaluation at `z` is bounded by the Gauss norm at `‖z‖`. -/
theorem norm_evalAt_le (hz : 0 < ‖z‖) (f : atRadius K hz) :
    ‖evalAt K hz f‖ ≤ laurentGaussNorm ‖z‖ (f.val : ℤ → K) := by
  have : IsUltrametricDist L := IsUltrametricDist.of_normedAlgebra K
  rw [evalAt_apply]
  refine IsUltrametricDist.norm_tsum_le_of_forall_le_of_nonneg (laurentGaussNorm_nonneg _ _) ?_
  intro n
  rw [norm_mul, norm_algebraMap', norm_zpow]
  exact le_laurentGaussNorm ((mem_atRadius K hz).mp f.property).bddAbove n

/-- A net converging in the Gauss norm at the evaluation radius converges after evaluation. -/
theorem tendsto_evalAt_of_tendsto_laurentGaussNorm_sub (hz : 0 < ‖z‖) {ι : Type*}
    {l : Filter ι} {f : ι → atRadius K hz} {g : atRadius K hz}
    (h : Tendsto (fun i ↦ laurentGaussNorm ‖z‖ ((f i - g).val : ℤ → K)) l (𝓝 0)) :
    Tendsto (fun i ↦ evalAt K hz (f i)) l (𝓝 (evalAt K hz g)) := by
  refine tendsto_iff_norm_sub_tendsto_zero.mpr <| squeeze_zero_norm' ?_ h
  exact Eventually.of_forall fun i ↦ by
    simpa only [norm_norm, map_sub] using norm_evalAt_le K hz (f i - g)

/-- Mapping a Robba series value into an isometric extension agrees with evaluating the same
series at the image of the point. -/
theorem comp_evalAt {M : Type*} [NormedField M] [NormedAlgebra K M] [CompleteSpace M]
    (φ : L →ₐ[K] M) (hφ : Isometry φ) (hz : 0 < ‖z‖) (f : atRadius K hz) :
    φ (evalAt K hz f) =
      evalAt K (z := φ z)
        (by simpa only [hφ.norm_map_of_map_zero (map_zero φ)] using hz)
        ⟨f.val, by
          simpa only [mem_atRadius, hφ.norm_map_of_map_zero (map_zero φ)] using f.property⟩ := by
  refine ((hasSum_evalAt K hz f).map φ hφ.continuous |>.congr_fun fun n ↦ ?_).unique
    (hasSum_evalAt K _ _)
  simp only [Function.comp_apply, map_mul, AlgHom.commutes, map_zpow₀]

/-- Evaluate a series on the annulus `r < ‖z‖ < 1` at the nonzero point `z`. -/
noncomputable def annulusEval {r : ℝ} (hz : 0 < ‖z‖) (hr : r < ‖z‖) (h₁ : ‖z‖ < 1) :
    annulus K r →ₐ[K] L :=
  (evalAt K hz).comp (Subalgebra.inclusion (annulus_le_atRadius K hz hr h₁))

/-- Annular evaluation is fixed-radius evaluation restricted to the annular subalgebra. -/
theorem annulusEval_eq_evalAt {r : ℝ} (hz : 0 < ‖z‖) (hr : r < ‖z‖) (h₁ : ‖z‖ < 1) :
    annulusEval K hz hr h₁ =
      (evalAt K hz).comp (Subalgebra.inclusion (annulus_le_atRadius K hz hr h₁)) :=
  (rfl)

/-- The value of a series on an annulus is its convergent Laurent sum at the point. -/
theorem annulusEval_apply {r : ℝ} (hz : 0 < ‖z‖) (hr : r < ‖z‖) (h₁ : ‖z‖ < 1)
    (f : annulus K r) :
    annulusEval K hz hr h₁ f = ∑' n : ℤ, algebraMap K L ((f.val : ℤ → K) n) * z ^ n :=
  (rfl)

/-- Evaluation on an annulus is bounded by the Gauss norm at the norm of the point. -/
theorem norm_annulusEval_le {r : ℝ} (hz : 0 < ‖z‖) (hr : r < ‖z‖) (h₁ : ‖z‖ < 1)
    (f : annulus K r) :
    ‖annulusEval K hz hr h₁ f‖ ≤ laurentGaussNorm ‖z‖ (f.val : ℤ → K) :=
  norm_evalAt_le K hz (Subalgebra.inclusion (annulus_le_atRadius K hz hr h₁) f)

/-- The evaluated annular Laurent series converges as an unordered sum over its degrees. -/
theorem hasSum_annulusEval {r : ℝ} (hz : 0 < ‖z‖) (hr : r < ‖z‖) (h₁ : ‖z‖ < 1)
    (f : annulus K r) :
    HasSum (fun n : ℤ ↦ algebraMap K L ((f.val : ℤ → K) n) * z ^ n)
      (annulusEval K hz hr h₁ f) :=
  hasSum_evalAt K hz (Subalgebra.inclusion (annulus_le_atRadius K hz hr h₁) f)

/-- An annular monomial of degree `n` evaluates to its coefficient times `z ^ n`. -/
@[simp]
theorem annulusEval_monomial {r : ℝ} (hz : 0 < ‖z‖) (hr : r < ‖z‖) (h₁ : ‖z‖ < 1)
    (n : ℤ) (c : K) :
    annulusEval K hz hr h₁ ⟨monomial n c, monomial_mem_annulus r n c⟩ =
      algebraMap K L c * z ^ n := by
  rw [annulusEval_eq_evalAt, AlgHom.comp_apply, Subalgebra.inclusion_mk]
  exact evalAt_monomial K hz n c

/-- On Laurent polynomials, annular evaluation agrees with algebraic evaluation at the same
nonzero point. -/
@[simp]
theorem annulusEval_ofLaurentPolynomial {r : ℝ} (u : Lˣ) (hz : 0 < ‖(u : L)‖)
    (hr : r < ‖(u : L)‖) (h₁ : ‖(u : L)‖ < 1) (P : K[T;T⁻¹]) :
    annulusEval K hz hr h₁ (ofLaurentPolynomial K r P) =
      LaurentPolynomial.eval₂ (algebraMap K L) u P := by
  induction P using LaurentPolynomial.induction_on' with
  | add P Q hP hQ => rw [map_add, map_add, map_add, hP, hQ]
  | C_mul_T n c =>
    rw [ofLaurentPolynomial_C_mul_T, annulusEval_monomial,
      LaurentPolynomial.eval₂_C_mul_T, Units.val_zpow_eq_zpow_val]

/-- At any fixed point of the smaller annulus, restriction leaves the evaluation map unchanged. -/
theorem annulusEval_comp_inclusion {r s : ℝ} (h : r ≤ s) (hz : 0 < ‖z‖)
    (hs : s < ‖z‖) (h₁ : ‖z‖ < 1) :
    (annulusEval K hz hs h₁).comp (Subalgebra.inclusion (annulus_mono h)) =
      annulusEval K hz (h.trans_lt hs) h₁ := by
  ext f
  simp only [AlgHom.comp_apply, annulusEval_apply, Subalgebra.coe_inclusion]

/-- Evaluating an annular series and mapping its value into a further valued extension agrees
with evaluating at the image of the point. -/
theorem comp_annulusEval {M : Type*} [NormedField M] [NormedAlgebra K M] [CompleteSpace M]
    (φ : L →ₐ[K] M) (hφ : Isometry φ) {r : ℝ}
    (hz : 0 < ‖z‖) (hr : r < ‖z‖) (h₁ : ‖z‖ < 1) :
    φ.comp (annulusEval K hz hr h₁) =
      annulusEval K (z := φ z)
        (by simpa only [hφ.norm_map_of_map_zero (map_zero φ)] using hz)
        (by simpa only [hφ.norm_map_of_map_zero (map_zero φ)] using hr)
        (by simpa only [hφ.norm_map_of_map_zero (map_zero φ)] using h₁) := by
  ext ⟨f, hf⟩
  simpa only [annulusEval_eq_evalAt, AlgHom.comp_apply, Subalgebra.inclusion_mk] using
    comp_evalAt K φ hφ hz ⟨f, annulus_le_atRadius K hz hr h₁ hf⟩

open _root_.IsLocalRing

/-- A Robba series converging on a nonempty circle over an extension with infinite residue field
attains its Gauss norm at some point of that circle. -/
theorem exists_norm_evalAt_eq_laurentGaussNorm [IsUltrametricDist L]
    [Infinite (ResidueField (Subring.unitClosedBall L))]
    (hz : 0 < ‖z‖) (f : atRadius K hz) :
    ∃ w : L, ∃ hw : ‖w‖ = ‖z‖,
      ‖evalAt K (z := w) (hw.symm ▸ hz)
        ⟨f.val, by simpa only [mem_atRadius, hw] using f.property⟩‖ =
        laurentGaussNorm ‖z‖ (f.val : ℤ → K) := by
  let a (n : ℤ) := algebraMap K L ((f.val : ℤ → K) n) * z ^ n
  have ha : Summable a := (hasSum_evalAt K hz f).summable
  have hn (n : ℤ) : ‖a n‖ = ‖(f.val : ℤ → K) n‖ * ‖z‖ ^ n := by
    simp only [a, norm_mul, norm_algebraMap', norm_zpow]
  obtain ⟨j, hj⟩ := ha.tendsto_cofinite_zero.exists_norm_eq_ciSup
  have hG : ‖a j‖ = laurentGaussNorm ‖z‖ (f.val : ℤ → K) := by
    simpa only [hn, laurentGaussNorm_def] using hj
  rcases eq_or_ne (a j) 0 with hzero | hj'
  · refine ⟨z, rfl, le_antisymm (norm_evalAt_le K hz f) ?_⟩
    rw [← hG, hzero, norm_zero]
    exact norm_nonneg _
  have hle (n : ℤ) : ‖a n‖ ≤ ‖a j‖ := by
    rw [hn, hG]
    exact le_laurentGaussNorm ((mem_atRadius K hz).mp f.property).bddAbove n
  have hjnorm : ‖a j / a j‖ = 1 := by simp [hj']
  obtain ⟨u, hu, hsum⟩ := exists_norm_tsum_mul_zpow_eq_one (ha.div_const (a j))
    (fun n ↦ by rw [norm_div]; exact div_le_one_of_le₀ (hle n) (norm_nonneg _)) hjnorm
  have hw : ‖z * u‖ = ‖z‖ := by rw [norm_mul, hu, mul_one]
  refine ⟨z * u, hw, ?_⟩
  rw [evalAt_apply, ← hG]
  have hscaled : (∑' n : ℤ, a n / a j * u ^ n) * a j =
      ∑' n : ℤ, algebraMap K L ((f.val : ℤ → K) n) * (z * u) ^ n := by
    rw [← tsum_mul_right]
    refine tsum_congr fun n ↦ ?_
    rw [mul_right_comm, div_mul_cancel₀ _ hj', mul_zpow, ← mul_assoc]
  rw [← hscaled, norm_mul, hsum, one_mul]

/-- A Robba series converging on a nonempty circle over an algebraically closed valued extension
attains its Gauss norm at some point of that circle. -/
theorem exists_norm_evalAt_eq_laurentGaussNorm_of_isAlgClosed [IsAlgClosed L]
    (hz : 0 < ‖z‖) (f : atRadius K hz) :
    ∃ w : L, ∃ hw : ‖w‖ = ‖z‖,
      ‖evalAt K (z := w) (hw.symm ▸ hz)
        ⟨f.val, by simpa only [mem_atRadius, hw] using f.property⟩‖ =
        laurentGaussNorm ‖z‖ (f.val : ℤ → K) := by
  have : IsUltrametricDist L := IsUltrametricDist.of_normedAlgebra K
  have : IsAlgClosed (ResidueField (Subring.unitClosedBall L)) :=
    isAlgClosed_residueField_unitClosedBall L
  exact exists_norm_evalAt_eq_laurentGaussNorm K hz f

/-- On a nonempty circle in an annulus over a valued field with infinite residue field, some
evaluation attains the Gauss norm. -/
theorem exists_norm_annulusEval_eq_laurentGaussNorm [IsUltrametricDist L]
    [Infinite (ResidueField (Subring.unitClosedBall L))] {r : ℝ}
    (hz : 0 < ‖z‖) (hr : r < ‖z‖) (h₁ : ‖z‖ < 1) (f : annulus K r) :
    ∃ w : L, ∃ hw : ‖w‖ = ‖z‖,
      ‖annulusEval K (z := w) (hw.symm ▸ hz) (hw.symm ▸ hr) (hw.symm ▸ h₁) f‖ =
        laurentGaussNorm ‖z‖ (f.val : ℤ → K) := by
  rcases f with ⟨f, hf⟩
  simpa only [annulusEval_eq_evalAt, AlgHom.comp_apply, Subalgebra.inclusion_mk] using
    exists_norm_evalAt_eq_laurentGaussNorm K hz ⟨f, annulus_le_atRadius K hz hr h₁ hf⟩

/-- On a nonempty circle in an annulus over an algebraically closed valued extension, the Gauss
norm is attained by evaluating at a point on that circle. -/
theorem exists_norm_annulusEval_eq_laurentGaussNorm_of_isAlgClosed [IsAlgClosed L] {r : ℝ}
    (hz : 0 < ‖z‖) (hr : r < ‖z‖) (h₁ : ‖z‖ < 1) (f : annulus K r) :
    ∃ w : L, ∃ hw : ‖w‖ = ‖z‖,
      ‖annulusEval K (z := w) (hw.symm ▸ hz) (hw.symm ▸ hr) (hw.symm ▸ h₁) f‖ =
        laurentGaussNorm ‖z‖ (f.val : ℤ → K) := by
  rcases f with ⟨f, hf⟩
  simpa only [annulusEval_eq_evalAt, AlgHom.comp_apply, Subalgebra.inclusion_mk] using
    exists_norm_evalAt_eq_laurentGaussNorm_of_isAlgClosed K hz
      ⟨f, annulus_le_atRadius K hz hr h₁ hf⟩

end TauCeti.RobbaRing
