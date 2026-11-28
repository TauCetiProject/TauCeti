/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Derivation.Basic
public import TauCeti.RingTheory.PowerSeries.MahlerDerivation
public import TauCeti.RingTheory.Robba.Log
public import TauCeti.RingTheory.Robba.Primitive
import Mathlib.RingTheory.PowerSeries.WellKnown

/-!
# The derivations `d/dt` and `(1 + t) d/dt` of the Robba ring

Let `R` be a complete ultrametric normed commutative ring. Termwise differentiation
`∑ aₙ tⁿ ↦ ∑ n aₙ tⁿ⁻¹` (`TauCeti.laurentDerivative`) preserves convergence on every circle
`|t| = ρ`, so it maps the Robba ring `R_R` to itself. It satisfies the Leibniz rule for the
convolution product, because the coefficients `(n + 1 - y) aₙ₊₁₋ᵧ b_y` and `y aₙ₊₁₋ᵧ b_y` of the
two convergent series computing `(a' b)ₙ` and `(a b')ₙ` add up to `(n + 1) aₙ₊₁₋ᵧ b_y`
(`TauCeti.laurentDerivative_addRingConvolution`). This makes it an `R`-derivation
`TauCeti.RobbaRing.derivative R` of the Robba ring. It preserves the annular, bounded and integral
subrings, and on the power series on the open unit disc it is the derivative of power series.

Over a field `K` of characteristic zero, the constants are the only series with derivative zero,
and a series is a derivative exactly when its residue, its coefficient of `t⁻¹`, vanishes: the
termwise primitive of a residue-free series converges on the same open annulus
(`TauCeti.exists_laurentDerivative_eq_iff`). So `t⁻¹` spans the cokernel of `d/dt`.

The element `1 + t` is a unit of the Robba ring, with inverse the geometric series
`∑_{n ≥ 0} (-t)ⁿ`. The derivation `∂ = (1 + t) d/dt` (`TauCeti.RobbaRing.mahlerDerivation`), the
Robba-ring form of `PowerSeries.mahlerDerivation`, is the derivation `Y d/dY` in `Y = 1 + t`. With
the cyclotomic variable `π` in place of `t`, it is the derivation `∂ = (1 + π) d/dπ` of p-adic
Hodge theory, and it sends the period `log (1 + t)` (`TauCeti.RobbaRing.log`) to `1`. Since `1 + t`
is a unit, `∂` has the same kernel as `d/dt`, and its cokernel is spanned by the class of
`(1 + t) t⁻¹`.

## Main definitions

* `TauCeti.RobbaRing.derivative R`: the derivation `d/dt` of the Robba ring.
* `TauCeti.RobbaRing.mahlerDerivation R`: the derivation `∂ = (1 + t) d/dt`.

## Main results

* `TauCeti.laurentDerivative_addRingConvolution`: the Leibniz rule for the termwise derivative of
  a convolution.
* `TauCeti.RobbaRing.derivative_monomial`: `d(c tⁿ) = n c tⁿ⁻¹`.
* `TauCeti.RobbaRing.derivative_ofOnOpenDisc`: on the power series on the open unit disc, `d/dt` is
  the derivative of power series.
* `TauCeti.RobbaRing.derivative_eq_zero_iff`: without additive torsion, the kernel of `d/dt`
  consists of the constants.
* `TauCeti.RobbaRing.exists_derivative_eq_iff`,
  `TauCeti.RobbaRing.existsUnique_eq_smul_add_derivative`: over a field of characteristic zero, a
  series is a derivative exactly when its residue vanishes, and every series is uniquely a multiple
  of `t⁻¹` plus a derivative.
* `TauCeti.RobbaRing.isUnit_one_add_monomial`: `1 + t` is a unit.
* `TauCeti.RobbaRing.mahlerDerivation_ofOnOpenDisc`: on the power series on the open unit disc,
  `∂` is `PowerSeries.mahlerDerivation`.
* `TauCeti.RobbaRing.mahlerDerivation_log`: `∂ log (1 + t) = 1`.
* `TauCeti.RobbaRing.mahlerDerivation_eq_zero_iff`,
  `TauCeti.RobbaRing.existsUnique_eq_smul_add_mahlerDerivation`: `∂` kills exactly the constants,
  and every series is uniquely a multiple of `(1 + t) t⁻¹` plus an element of the image of `∂`.

## References

* L. Berger, *Représentations p-adiques et équations différentielles*, Invent. Math. 148 (2002),
  Lemma 4.2 and Proposition 4.4.
* K. S. Kedlaya, *Local monodromy of p-adic differential equations: an overview*, Int. J. Number
  Theory 1 (2005), Definition 5.1.1.
-/

public section

open scoped DiscreteConvolution PowerSeries

open DiscreteConvolution

namespace TauCeti

/-! ### The Leibniz rule for the termwise derivative -/

section Leibniz

variable {S R : Type*} [Semiring S] [Ring R] [Module S R] [TopologicalSpace R]
  [IsTopologicalAddGroup R] [T2Space R]

/-- **The Leibniz rule for the termwise derivative**: if the three convolutions `a ⋆ b`, `a' ⋆ b`
and `a ⋆ b'` exist, then `(a ⋆ b)' = a' ⋆ b + a ⋆ b'`. -/
theorem laurentDerivative_addRingConvolution {a b : ℤ → R}
    (hab : AddConvolutionExists (.mul ℕ R) a b)
    (ha : AddConvolutionExists (.mul ℕ R) (laurentDerivative S a) b)
    (hb : AddConvolutionExists (.mul ℕ R) a (laurentDerivative S b)) :
    laurentDerivative S (a ⋆ᵣ₊ b) =
      laurentDerivative S a ⋆ᵣ₊ b + a ⋆ᵣ₊ laurentDerivative S b := by
  ext n
  -- Reindex the series for `(a ⋆ b')ₙ` by `y ↦ y - 1`, so that both series have the terms
  -- `aₙ₊₁₋ᵧ b_y` up to an integer factor.
  have h₂ : HasSum (fun y ↦ a (n + 1 - y) * laurentDerivative S b (y - 1))
      ((a ⋆ᵣ₊ laurentDerivative S b) n) := by
    have h := (Equiv.subRight (1 : ℤ)).hasSum_iff.2 (hb n).hasSum_sub
    simp only [Function.comp_def, Equiv.subRight_apply, sub_sub_eq_add_sub] at h
    exact h
  have h₃ := ((hab (n + 1)).hasSum_sub).const_smul (n + 1)
  rw [laurentDerivative_apply, Pi.add_apply]
  refine h₃.unique (((ha n).hasSum_sub.add h₂).congr_fun fun y ↦ ?_)
  simp only [LinearMap.mul_apply', laurentDerivative_apply, sub_add_cancel, smul_mul_assoc,
    mul_smul_comm, ← add_smul, sub_add_eq_add_sub]

end Leibniz

/-! ### Convergence of the derivative -/

section Convergence

variable {S R : Type*} [Semiring S] [SeminormedRing R] [IsUltrametricDist R] [Module S R]

/-- Over an ultrametric ring, the derivative of a series converging on an annulus converges on the
same annulus. -/
theorem laurentDerivative_mem_annularCoeff {r : ℝ} {a : ℤ → R} (ha : a ∈ annularCoeff R r) :
    laurentDerivative S a ∈ annularCoeff R r :=
  mem_annularCoeff.2 fun ρ hρ₀ hr hρ₁ ↦
    (mem_annularCoeff.1 ha ρ hρ₀ hr hρ₁).laurentDerivative hρ₀

/-- Over an ultrametric ring, the derivative of an element of the Robba ring is in the Robba
ring. -/
theorem laurentDerivative_mem_robbaCoeff {a : ℤ → R} (ha : a ∈ robbaCoeff R) :
    laurentDerivative S a ∈ robbaCoeff R :=
  let ⟨r, hr, ha⟩ := mem_robbaCoeff.1 ha
  mem_robbaCoeff.2 ⟨r, hr, laurentDerivative_mem_annularCoeff ha⟩

end Convergence

namespace RobbaRing

open IsConvolutionRing

/-! ### The derivation `d/dt` -/

section Derivative

variable (R : Type*) [NormedCommRing R] [IsUltrametricDist R] [CompleteSpace R]

/-- **The derivation `d/dt` of the Robba ring**: termwise differentiation
`∑ aₙ tⁿ ↦ ∑ n aₙ tⁿ⁻¹`. -/
noncomputable def derivative : Derivation R (RobbaRing R) (RobbaRing R) :=
  Derivation.mk' ((laurentDerivative R).restrict fun _ ha ↦ laurentDerivative_mem_robbaCoeff ha)
    fun f g ↦ by
      ext n
      have h := congrFun (laurentDerivative_addRingConvolution (S := R)
        (addConvolutionExists f.property g.property)
        (addConvolutionExists (laurentDerivative_mem_robbaCoeff f.property) g.property)
        (addConvolutionExists f.property (laurentDerivative_mem_robbaCoeff g.property))) n
      simp only [LinearMap.restrict_apply, coe_mul, Submodule.coe_add, smul_eq_mul,
        Pi.add_apply] at h ⊢
      rw [h, add_comm, addRingConvolution_comm (g : ℤ → R)]

variable {R}

/-- The coefficients of `df/dt` are those of the termwise derivative. -/
@[simp]
theorem coe_derivative (f : RobbaRing R) :
    (derivative R f : ℤ → R) = laurentDerivative R (f : ℤ → R) :=
  (rfl)

/-- `d(c tⁿ)/dt = n c tⁿ⁻¹`. -/
@[simp]
theorem derivative_monomial (n : ℤ) (c : R) :
    derivative R (monomial n c) = monomial (n - 1) (n * c) :=
  Subtype.ext <| by
    rw [coe_derivative, coe_monomial, coe_monomial, laurentDerivative_single, zsmul_eq_mul]

/-- `d/dt` preserves the series converging on the annulus `r < |t| < 1`. -/
theorem derivative_mem_annulus {r : ℝ} {f : RobbaRing R} (hf : f ∈ annulus R r) :
    derivative R f ∈ annulus R r :=
  mem_annulus.2 (laurentDerivative_mem_annularCoeff (mem_annulus.1 hf))

/-- `d/dt` preserves the bounded Robba ring. -/
theorem derivative_mem_bounded {f : RobbaRing R} (hf : f ∈ bounded R) :
    derivative R f ∈ bounded R :=
  let ⟨C, hC⟩ := mem_bounded.1 hf
  mem_bounded.2 ⟨C, Set.forall_mem_range.2 fun n ↦ by
    rw [coe_derivative, laurentDerivative_apply]
    exact (IsUltrametricDist.norm_zsmul_le _ _).trans (hC ⟨n + 1, rfl⟩)⟩

/-- `d/dt` preserves the integral Robba ring. -/
theorem derivative_mem_integral [NormOneClass R] {f : RobbaRing R}
    (hf : f ∈ integral (robbaCoeff R)) : derivative R f ∈ integral (robbaCoeff R) :=
  mem_integral.2 fun n ↦ by
    rw [coe_derivative, laurentDerivative_apply]
    exact (IsUltrametricDist.norm_zsmul_le _ _).trans (mem_integral.1 hf (n + 1))

/-- **On power series, `d/dt` is the derivative of power series**: for a power series `f` on the
open unit disc, `d/dt` of its image in the Robba ring is the image of `d⁄dX f`. -/
theorem derivative_ofOnOpenDisc (f : PowerSeries.OnOpenDisc.subring R 1) :
    derivative R (ofOnOpenDisc R f) = ofOnOpenDisc R ⟨d⁄dX (f : R⟦X⟧),
      PowerSeries.OnOpenDisc.mem_subring.2
        (PowerSeries.OnOpenDisc.mem_subring.1 f.property).derivative⟩ := by
  ext n
  rw [coe_derivative, laurentDerivative_apply]
  rcases lt_or_ge n 0 with hn | hn
  · rw [coe_ofOnOpenDisc_of_neg R _ hn]
    rcases (Int.add_one_le_iff.2 hn).lt_or_eq with hn' | hn'
    · rw [coe_ofOnOpenDisc_of_neg R _ (by omega), smul_zero]
    · rw [hn', zero_smul]
  · lift n to ℕ using hn
    rw [coe_ofOnOpenDisc_natCast, PowerSeries.coeff_derivative, ← Nat.cast_one,
      ← Nat.cast_add, coe_ofOnOpenDisc_natCast, natCast_zsmul, nsmul_eq_mul, mul_comm,
      Nat.cast_succ]

/-- **The kernel of `d/dt`**: without additive torsion, the series with zero derivative are the
constants. -/
theorem derivative_eq_zero_iff [IsAddTorsionFree R] {f : RobbaRing R} :
    derivative R f = 0 ↔ f = algebraMap R (RobbaRing R) ((f : ℤ → R) 0) := by
  rw [Subtype.ext_iff, Subtype.ext_iff, coe_derivative, coe_algebraMap]
  exact laurentDerivative_eq_zero_iff_eq_single

end Derivative

/-! ### The cokernel of `d/dt` -/

section Cokernel

variable {K : Type*} [NormedField K] [IsUltrametricDist K] [CompleteSpace K] [CharZero K]

/-- **The image of `d/dt`**: over a field of characteristic zero, a series in the Robba ring is the
derivative of a series in the Robba ring exactly when its residue, the coefficient of `t⁻¹`,
vanishes. -/
theorem exists_derivative_eq_iff {f : RobbaRing K} :
    (∃ g, derivative K g = f) ↔ (f : ℤ → K) (-1) = 0 := by
  refine ⟨fun ⟨g, hg⟩ ↦ hg ▸ laurentDerivative_apply_neg_one _, fun h ↦ ?_⟩
  obtain ⟨r, hr, hf⟩ := mem_robbaCoeff.1 f.property
  -- The termwise primitive converges on the open annulus `max r 0 < |t| < 1`.
  have hpos (ρ : ℝ) (hρ : ρ ∈ Set.Ioo (max r 0) 1) : 0 < ρ := (le_max_right r 0).trans_lt hρ.1
  obtain ⟨g, hg, hgf⟩ := (exists_laurentDerivative_eq_iff (K := K) isOpen_Ioo hpos
    fun ρ hρ ↦ mem_annularCoeff.1 hf ρ (hpos ρ hρ) ((le_max_left r 0).trans_lt hρ.1) hρ.2).2 h
  exact ⟨⟨g, mem_robbaCoeff.2 ⟨max r 0, max_lt hr zero_lt_one,
    mem_annularCoeff.2 fun ρ _ hρ hρ₁ ↦ hg ρ ⟨hρ, hρ₁⟩⟩⟩, Subtype.ext hgf⟩

/-- **The cokernel of `d/dt` is spanned by `t⁻¹`**: over a field of characteristic zero, every
series in the Robba ring is uniquely a multiple `c t⁻¹` plus a derivative, and `c` is its
residue. -/
theorem existsUnique_eq_smul_add_derivative (f : RobbaRing K) :
    ∃! c : K, ∃ g, f = c • monomial (-1) 1 + derivative K g := by
  refine ⟨(f : ℤ → K) (-1), ?_, ?_⟩
  · obtain ⟨g, hg⟩ := (exists_derivative_eq_iff
      (f := f - (f : ℤ → K) (-1) • monomial (-1) 1)).2 (by simp)
    exact ⟨g, by rw [hg, add_sub_cancel]⟩
  · rintro c ⟨g, rfl⟩
    simp

end Cokernel

/-! ### The derivation `∂ = (1 + t) d/dt` -/

section MahlerDerivation

variable (R : Type*) [NormedCommRing R] [IsUltrametricDist R] [CompleteSpace R]

/-- `1 + t` is the image of the polynomial `1 + X`. -/
private theorem one_add_monomial_eq_ofOnOpenDisc : (1 + monomial 1 1 : RobbaRing R) =
    ofOnOpenDisc R (PowerSeries.OnOpenDisc.polynomialHom (1 + Polynomial.X)) := by
  simp

/-- `1 + t` is a unit of the Robba ring: its inverse is the geometric series `∑_{n ≥ 0} (-t)ⁿ`,
which converges on the open unit disc. -/
theorem isUnit_one_add_monomial : IsUnit (1 + monomial 1 1 : RobbaRing R) := by
  have hg : (PowerSeries.mk fun n ↦ (-1 : R) ^ n).OnOpenDisc 1 :=
    PowerSeries.onOpenDisc_of_bddAbove_norm_coeff ⟨‖(1 : R)‖, Set.forall_mem_range.2 fun n ↦ by
      rcases neg_one_pow_eq_or R n with h | h <;> simp [h]⟩
  refine IsUnit.of_mul_eq_one (ofOnOpenDisc R ⟨_, PowerSeries.OnOpenDisc.mem_subring.2 hg⟩) ?_
  rw [one_add_monomial_eq_ofOnOpenDisc, ← map_one (ofOnOpenDisc R), ← map_mul]
  congr 1
  exact Subtype.ext <| by simpa [mul_comm] using PowerSeries.mk_neg_one_pow_mul_one_add_eq_one R

/-- **The derivation `∂ = (1 + t) d/dt` of the Robba ring**, the analogue of
`PowerSeries.mahlerDerivation`. In the variable `Y = 1 + t` it is `Y d/dY`. With the cyclotomic
variable `π` in place of `t`, it is the derivation `∂ = (1 + π) d/dπ` of p-adic Hodge theory. -/
noncomputable def mahlerDerivation : Derivation R (RobbaRing R) (RobbaRing R) :=
  (1 + monomial 1 1 : RobbaRing R) • derivative R

variable {R}

theorem mahlerDerivation_apply (f : RobbaRing R) :
    mahlerDerivation R f = (1 + monomial 1 1) * derivative R f :=
  (rfl)

/-- **On power series, `∂` is the Mahler derivation**: for a power series `f` on the open unit
disc, `∂` of its image in the Robba ring is the image of `PowerSeries.mahlerDerivation R f`. -/
theorem mahlerDerivation_ofOnOpenDisc (f : PowerSeries.OnOpenDisc.subring R 1) :
    mahlerDerivation R (ofOnOpenDisc R f) =
      ofOnOpenDisc R ⟨PowerSeries.mahlerDerivation R (f : R⟦X⟧), by
        rw [PowerSeries.mahlerDerivation_apply, PowerSeries.OnOpenDisc.mem_subring]
        exact (PowerSeries.onOpenDisc_one.add PowerSeries.onOpenDisc_X).mul
          (PowerSeries.OnOpenDisc.mem_subring.1 f.property).derivative⟩ := by
  rw [mahlerDerivation_apply, derivative_ofOnOpenDisc, one_add_monomial_eq_ofOnOpenDisc, ← map_mul]
  congr 1
  exact Subtype.ext <| by simp [PowerSeries.mahlerDerivation_apply]

/-- `∂(c tⁿ) = n c tⁿ⁻¹ + n c tⁿ`. In particular `∂t = 1 + t`. -/
@[simp]
theorem mahlerDerivation_monomial (n : ℤ) (c : R) :
    mahlerDerivation R (monomial n c) = monomial (n - 1) (n * c) + monomial n (n * c) := by
  rw [mahlerDerivation_apply, derivative_monomial, add_mul, one_mul, monomial_mul_monomial,
    one_mul, add_sub_cancel]

/-- **The kernel of `∂`**: without additive torsion, the series killed by `∂ = (1 + t) d/dt` are
the constants. -/
theorem mahlerDerivation_eq_zero_iff [IsAddTorsionFree R] {f : RobbaRing R} :
    mahlerDerivation R f = 0 ↔ f = algebraMap R (RobbaRing R) ((f : ℤ → R) 0) := by
  rw [mahlerDerivation_apply, (isUnit_one_add_monomial R).mul_right_eq_zero,
    derivative_eq_zero_iff]

end MahlerDerivation

section Field

variable {K : Type*} [NormedField K] [IsUltrametricDist K] [CompleteSpace K] [CharZero K]

/-- **`∂ log (1 + t) = 1`**: the period `log (1 + t)` has derivative `(1 + t)⁻¹`. -/
@[simp]
theorem mahlerDerivation_log : mahlerDerivation K (log K) = 1 := by
  rw [log_def, mahlerDerivation_ofOnOpenDisc, ← map_one (ofOnOpenDisc K)]
  congr 1
  exact Subtype.ext <| by
    simpa [PowerSeries.mahlerDerivation_apply, mul_comm] using
      PowerSeries.derivative_log_mul_one_add_X (A := K)

/-- **The cokernel of `∂` is spanned by `(1 + t) t⁻¹`**: over a field of characteristic zero,
every series in the Robba ring is uniquely a multiple of `(1 + t) t⁻¹` plus an element of the
image of `∂ = (1 + t) d/dt`. -/
theorem existsUnique_eq_smul_add_mahlerDerivation (f : RobbaRing K) :
    ∃! c : K, ∃ g, f = c • ((1 + monomial 1 1) * monomial (-1) 1) + mahlerDerivation K g := by
  obtain ⟨u, hu⟩ := isUnit_one_add_monomial K
  -- Dividing by the unit `1 + t` turns `∂` into `d/dt`.
  have key (c : K) : (∃ g, f = c • ((1 + monomial 1 1) * monomial (-1) 1) +
      mahlerDerivation K g) ↔
        ∃ g, (↑u⁻¹ : RobbaRing K) * f = c • monomial (-1) 1 + derivative K g := by
    refine exists_congr fun g ↦ ?_
    rw [mahlerDerivation_apply, ← hu, ← Algebra.mul_smul_comm, ← mul_add,
      Units.inv_mul_eq_iff_eq_mul]
  simp only [key]
  exact existsUnique_eq_smul_add_derivative _

end Field

end RobbaRing

end TauCeti
