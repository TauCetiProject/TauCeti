/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.MvPowerSeries.PiTopology
public import Mathlib.RingTheory.Polynomial.Quotient
public import TauCeti.Analysis.Normed.Ring.Ultra
public import TauCeti.RingTheory.Dagger.GaussNorm
public import TauCeti.RingTheory.AdicCompletion.AlgHom
public import TauCeti.Analysis.Normed.Ring.PseudoUniformizer

/-!
# The integral Monsky–Washnitzer algebra

Let `R` be an ultrametric normed commutative ring with `‖1‖ = 1` and closed unit ball
`R° = {a | ‖a‖ ≤ 1}`. The *integral Monsky–Washnitzer algebra* is the subring

```text
R°⟨X⟩† = R⟨X⟩† ∩ R°[[X]]  ⊆  R[[X]]
```

of overconvergent power series with coefficients in `R°`. For a complete discretely valued field
`K` with ring of integers `O_K`, the ring `O_K⟨X⟩†` is the basic object of Monsky and Washnitzer's
formal cohomology: weak completions of finitely generated `O_K`-algebras are its quotients, and
inverting a uniformiser recovers the Monsky–Washnitzer algebra `K⟨X⟩†`. Its elements are the
overconvergent series of Gauss norm at most one.

Over an ultrametric normed field `K`, reduction modulo a nonzero `ϖ ∈ K°` turns `K°⟨X⟩†` into a
polynomial ring: `K°⟨X⟩† ⧸ ϖ ≃ (K° ⧸ ϖ)[X]`. Indeed the coefficients of an overconvergent series
tend to zero, so all but finitely many of them lie in `ϖ K°`. Taking `ϖ = πᵐ` gives the
isomorphisms `O_K⟨X⟩† ⧸ πᵐ ≃ (O_K ⧸ πᵐ)[X]` through which weak completions are compared with
`π`-adic completions.

The same reductions identify the `ϖ`-adic completion of `K°⟨X⟩†`, for `0 < ‖ϖ‖ < 1` over a complete
field, with the ring `K°⟨X⟩ = T°` of restricted series with coefficients in `K°`, the closed unit
ball of the Tate algebra `T = K⟨X⟩`. Overconvergent series are dense in `T°`, so `K°⟨X⟩† ⧸ ϖⁿ` and
`T° ⧸ ϖⁿ` agree, and `T°` is `ϖ`-adically complete. For a uniformiser `π` of a discretely valued
`K` this says that the `π`-adic completion of `O_K⟨X⟩†` is `O_K⟨X⟩`.

## Main definitions

* `TauCeti.Dagger.intWashnitzerAlgebra σ R`: the subring `R°⟨X⟩†` of overconvergent series with
  coefficients of norm at most one.
* `TauCeti.Dagger.intWashnitzerAlgebra.toWashnitzerAlgebra`: its inclusion into `R⟨X⟩†`.
* `TauCeti.Dagger.intWashnitzerAlgebra.restrictRingEquiv`: the restriction of a
  Gauss-norm-preserving isomorphism `R⟨X⟩† ≃ R⟨Y⟩†` to an isomorphism `R°⟨X⟩† ≃ R°⟨Y⟩†`.
* `TauCeti.Dagger.intWashnitzerAlgebra.ofMvPolynomial`: the inclusion `R°[X] → R°⟨X⟩†` of the
  polynomials, an `R°`-algebra map for the structure of `R°⟨X⟩†` given by the constant series.
* `TauCeti.Dagger.intWashnitzerAlgebra.quotientSpanEquivMvPolynomial`: the reduction
  `K°⟨X⟩† ⧸ ϖ ≃ₐ[K°] (K° ⧸ ϖ)[X]` for a nonzero `ϖ ∈ K°`.
* `TauCeti.Dagger.intWashnitzerAlgebra.toTate`: the inclusion `R°⟨X⟩† → T°` into the closed unit
  ball of the Tate algebra.
* `TauCeti.Dagger.intWashnitzerAlgebra.adicCompletionEquiv`: the ring isomorphism between the
  `ϖ`-adic completion of `K°⟨X⟩†` and `T° = K°⟨X⟩`.

## Main results

* `TauCeti.Dagger.mem_intWashnitzerAlgebra_iff`: `f ∈ R°⟨X⟩†` iff `f` is overconvergent and all
  its coefficients have norm at most one; equivalently
  (`TauCeti.Dagger.mem_intWashnitzerAlgebra_iff_norm_le_one`), `f` lies in the closed unit
  ball for the Gauss norm. Over a nontrivially normed field this says that `K°⟨X⟩†` is the ring of
  power-bounded elements of `K⟨X⟩†`
  (`TauCeti.Dagger.mem_intWashnitzerAlgebra_iff_isPowerBounded`).
* `TauCeti.Dagger.mem_intWashnitzerAlgebra_iff_exists_norm_coeff_le_pow`: the
  Monsky–Washnitzer degree growth condition in coefficient form. For finitely many variables and
  any `0 < q < 1`, `f ∈ R°⟨X⟩†` iff `‖aᵥ‖ ≤ q ^ ⌊|ν| / c⌋` for some integer `c > 0`.
* `TauCeti.Dagger.mem_intWashnitzerAlgebra_iff_exists_hasSum`: the degree growth condition as
  stated by Monsky and Washnitzer. For finitely many variables, over an ultrametric normed field
  `K` with an element `π` of norm in `(0, 1)`, `f ∈ K°⟨X⟩†` iff `f = ∑ⱼ πʲ Pⱼ` for polynomials
  `Pⱼ` with integral coefficients and `deg Pⱼ ≤ c (j + 1)` for some `c`.
* `TauCeti.Dagger.mem_washnitzerAlgebra_iff_exists_C_pow_mul_mem`: `K⟨X⟩† = K°⟨X⟩†[1/π]`, that
  is, every overconvergent series becomes integral after multiplication by a power of `π`.
* `TauCeti.Dagger.intWashnitzerAlgebra.mem_span_algebraMap_iff_norm_le`: over a field, a series in
  `K°⟨X⟩†` is a multiple of the constant `a ∈ K°` iff its Gauss norm is at most `‖a‖`.
* `TauCeti.Dagger.isUnit_intWashnitzerAlgebra_iff`: over a complete ultrametric normed field, `f`
  is a unit of `K°⟨X⟩†` iff its constant coefficient has norm one and all other coefficients have
  norm less than one.
* `TauCeti.Dagger.mem_jacobson_bot_intWashnitzerAlgebra_iff`: the Jacobson radical of
  `K°⟨X⟩†` consists of the series all of whose coefficients have norm less than one. In
  particular every constant `π` with `‖π‖ < 1` lies in it, so `1 + π f` is a unit for every
  `f ∈ K°⟨X⟩†`.
* `TauCeti.Dagger.intWashnitzerAlgebra.exists_ofMvPolynomial_add_algebraMap_mul_eq`: every
  series in `K°⟨X⟩†` is a polynomial over `K°` plus `ϖ` times a series in `K°⟨X⟩†`, and
  `TauCeti.Dagger.intWashnitzerAlgebra.ker_mkₐ_comp_ofMvPolynomial`: for any `ϖ ∈ R°`, a
  polynomial over `R°` is divisible by `ϖ` in `R°⟨X⟩†` only if it is divisible by `ϖ` in `R°[X]`.
* `TauCeti.Dagger.intWashnitzerAlgebra.mem_span_algebraMap_pow_iff`: a series lies in `ϖⁿ K°⟨X⟩†`
  iff all its coefficients have norm at most `‖ϖ‖ ^ n`.
* `TauCeti.Dagger.intWashnitzerAlgebra.quotientMap_toTate_bijective`: `K°⟨X⟩† ⧸ ϖⁿ ≃ T° ⧸ ϖⁿ`.
* `TauCeti.Dagger.intWashnitzerAlgebra.isAdicComplete_span_toTate_algebraMap`: `T°` is
  `ϖ`-adically complete over a complete field.
* `TauCeti.Dagger.intWashnitzerAlgebra.adicCompletionEquiv_of`: the completion comparison extends
  the inclusion `K°⟨X⟩† → T°`.

## References

* P. Monsky and G. Washnitzer, *Formal cohomology. I*, Ann. of Math. 88 (1968), §2.
* M. van der Put, *The cohomology of Monsky and Washnitzer*, Mém. Soc. Math. France 23 (1986),
  §2.
* K. Kedlaya, *Finiteness of rigid cohomology with coefficients*, Duke Math. J. 134 (2006),
  §2.4.
-/

public section

namespace TauCeti.Dagger

open _root_.MvPowerSeries
open scoped MvPowerSeries.WithPiTopology

section Defs

variable (σ R : Type*) [NormedCommRing R] [IsUltrametricDist R] [NormOneClass R]

/-- The **integral Monsky–Washnitzer algebra** `R°⟨X⟩† = R⟨X⟩† ∩ R°[[X]]`: the overconvergent
power series whose coefficients lie in the closed unit ball `R°` of `R`. -/
noncomputable def intWashnitzerAlgebra : Subring (MvPowerSeries σ R) :=
  (washnitzerAlgebra σ R).toSubring ⊓
    (MvPowerSeries.map (Subring.unitClosedBall R).subtype).range

variable {σ R}

/-- A series lies in `R°⟨X⟩†` iff it is overconvergent and all its coefficients have norm at most
one. -/
theorem mem_intWashnitzerAlgebra_iff {f : MvPowerSeries σ R} :
    f ∈ intWashnitzerAlgebra σ R ↔ f ∈ washnitzerAlgebra σ R ∧ ∀ t, ‖coeff t f‖ ≤ 1 := by
  refine Subring.mem_inf.trans (and_congr Iff.rfl ⟨?_, fun h ↦ ?_⟩)
  · rintro ⟨g, rfl⟩ t
    rw [coeff_map]
    exact Subring.mem_unitClosedBall.1 (coeff t g).2
  · let g : MvPowerSeries σ (Subring.unitClosedBall R) := fun t ↦
      ⟨coeff t f, Subring.mem_unitClosedBall.2 (h t)⟩
    -- `MvPowerSeries` is a function type, and `coeff t` evaluates at `t`.
    have hg (t) : coeff t g = ⟨coeff t f, Subring.mem_unitClosedBall.2 (h t)⟩ := coeff_apply g t
    exact ⟨g, MvPowerSeries.ext fun t ↦ by simp [coeff_map, hg]⟩

/-- The integral Monsky–Washnitzer algebra lies in the Monsky–Washnitzer algebra. -/
theorem intWashnitzerAlgebra_le :
    intWashnitzerAlgebra σ R ≤ (washnitzerAlgebra σ R).toSubring :=
  inf_le_left

namespace intWashnitzerAlgebra

/-- The coefficients of a series in `R°⟨X⟩†` have norm at most one. -/
theorem norm_coeff_le_one (f : intWashnitzerAlgebra σ R) (t : σ →₀ ℕ) :
    ‖coeff t (f : MvPowerSeries σ R)‖ ≤ 1 :=
  (mem_intWashnitzerAlgebra_iff.1 f.2).2 t

/-- The constant coefficient of a series in `R°⟨X⟩†` has norm at most one. -/
theorem norm_constantCoeff_le_one (f : intWashnitzerAlgebra σ R) :
    ‖constantCoeff (f : MvPowerSeries σ R)‖ ≤ 1 := by
  simpa using norm_coeff_le_one f 0

end intWashnitzerAlgebra

/-- A constant series lies in `R°⟨X⟩†` iff it has norm at most one. -/
@[simp]
theorem C_mem_intWashnitzerAlgebra_iff {a : R} :
    C a ∈ intWashnitzerAlgebra σ R ↔ ‖a‖ ≤ 1 := by
  classical
  refine ⟨fun h ↦ by simpa using intWashnitzerAlgebra.norm_constantCoeff_le_one ⟨_, h⟩,
    fun h ↦ mem_intWashnitzerAlgebra_iff.2 ⟨C_mem_washnitzerAlgebra a, fun t ↦ ?_⟩⟩
  rw [coeff_C]
  split_ifs
  · exact h
  · simp

/-- A polynomial lies in `R°⟨X⟩†` iff all its coefficients have norm at most one. -/
@[simp]
theorem coe_mem_intWashnitzerAlgebra_iff {p : MvPolynomial σ R} :
    (p : MvPowerSeries σ R) ∈ intWashnitzerAlgebra σ R ↔ ∀ t, ‖p.coeff t‖ ≤ 1 := by
  simp [mem_intWashnitzerAlgebra_iff, coe_mem_washnitzerAlgebra]

/-- The variables lie in `R°⟨X⟩†`. -/
theorem X_mem_intWashnitzerAlgebra (i : σ) :
    (MvPowerSeries.X i : MvPowerSeries σ R) ∈ intWashnitzerAlgebra σ R := by
  classical
  refine mem_intWashnitzerAlgebra_iff.2 ⟨by simpa using (washnitzerAlgebra.X σ R i).2, fun t ↦ ?_⟩
  rw [coeff_X]
  split_ifs <;> simp

/-- With no variables, `R°⟨⟩†` consists of the constants of norm at most one. -/
theorem mem_intWashnitzerAlgebra_iff_of_isEmpty [IsEmpty σ] {f : MvPowerSeries σ R} :
    f ∈ intWashnitzerAlgebra σ R ↔ ‖constantCoeff f‖ ≤ 1 := by
  refine ⟨fun h ↦ intWashnitzerAlgebra.norm_constantCoeff_le_one ⟨_, h⟩, fun h ↦ ?_⟩
  rw [mem_intWashnitzerAlgebra_iff, washnitzerAlgebra_eq_top]
  refine ⟨trivial, fun t ↦ ?_⟩
  rwa [Subsingleton.elim t 0, coeff_zero_eq_constantCoeff_apply]

/-- **Integrality is the Gauss unit ball.** An overconvergent series lies in `R°⟨X⟩†` iff its
Gauss norm is at most one. -/
theorem mem_intWashnitzerAlgebra_iff_norm_le_one {f : washnitzerAlgebra σ R} :
    (f : MvPowerSeries σ R) ∈ intWashnitzerAlgebra σ R ↔ ‖f‖ ≤ 1 := by
  rw [mem_intWashnitzerAlgebra_iff, washnitzerAlgebra.norm_le_iff zero_le_one]
  exact and_iff_right f.2

namespace intWashnitzerAlgebra

variable (σ R) in
/-- The inclusion of the integral Monsky–Washnitzer algebra into the Monsky–Washnitzer
algebra. -/
noncomputable def toWashnitzerAlgebra : intWashnitzerAlgebra σ R →+* washnitzerAlgebra σ R :=
  (intWashnitzerAlgebra σ R).subtype.codRestrict (washnitzerAlgebra σ R) fun f ↦
    intWashnitzerAlgebra_le f.2

/-- The inclusion into `R⟨X⟩†` does not change the underlying series. -/
@[simp]
theorem coe_toWashnitzerAlgebra (f : intWashnitzerAlgebra σ R) :
    (toWashnitzerAlgebra σ R f : MvPowerSeries σ R) = f :=
  (rfl)

/-- Overconvergent series form an algebra over their integral subring by inclusion. -/
noncomputable instance : Algebra (intWashnitzerAlgebra σ R) (washnitzerAlgebra σ R) :=
  (toWashnitzerAlgebra σ R).toAlgebra

/-- The integral-algebra action is the inclusion of the underlying series. -/
@[simp]
theorem algebraMap_apply (f : intWashnitzerAlgebra σ R) :
    algebraMap (intWashnitzerAlgebra σ R) (washnitzerAlgebra σ R) f =
      toWashnitzerAlgebra σ R f := (rfl)

/-- The inclusion into `R⟨X⟩†` sends an integral overconvergent series to itself. -/
@[simp]
theorem toWashnitzerAlgebra_mk (f : washnitzerAlgebra σ R)
    (hf : (f : MvPowerSeries σ R) ∈ intWashnitzerAlgebra σ R) :
    toWashnitzerAlgebra σ R ⟨f, hf⟩ = f :=
  Subtype.ext (coe_toWashnitzerAlgebra _)

/-- The inclusion `R°⟨X⟩† → R⟨X⟩†` is injective. -/
theorem toWashnitzerAlgebra_injective : Function.Injective (toWashnitzerAlgebra σ R) :=
  fun _ _ h ↦ Subtype.ext (by simpa using congrArg Subtype.val h)

/-- An element of `R°⟨X⟩†` has Gauss norm at most one in `R⟨X⟩†`. -/
theorem norm_toWashnitzerAlgebra_le_one (f : intWashnitzerAlgebra σ R) :
    ‖toWashnitzerAlgebra σ R f‖ ≤ 1 :=
  mem_intWashnitzerAlgebra_iff_norm_le_one.1 (by rw [coe_toWashnitzerAlgebra]; exact f.2)

/-- A Gauss-norm-preserving ring isomorphism of Monsky–Washnitzer algebras restricts to their
integral subrings. -/
noncomputable def restrictRingEquiv {τ : Type*}
    (e : washnitzerAlgebra σ R ≃+* washnitzerAlgebra τ R) (he : ∀ f, ‖e f‖ = ‖f‖) :
    intWashnitzerAlgebra σ R ≃+* intWashnitzerAlgebra τ R where
  toFun f := ⟨e (toWashnitzerAlgebra σ R f),
    mem_intWashnitzerAlgebra_iff_norm_le_one.2
      ((he _).trans_le (norm_toWashnitzerAlgebra_le_one f))⟩
  invFun f := ⟨e.symm (toWashnitzerAlgebra τ R f),
    mem_intWashnitzerAlgebra_iff_norm_le_one.2 <| by
      rw [← he, e.apply_symm_apply]
      exact norm_toWashnitzerAlgebra_le_one f⟩
  left_inv f := Subtype.ext (by simp)
  right_inv f := Subtype.ext (by simp)
  map_mul' f g := Subtype.ext (by simp)
  map_add' f g := Subtype.ext (by simp)

/-- The restricted isomorphism acts as the given one on the underlying overconvergent series. -/
@[simp]
theorem toWashnitzerAlgebra_restrictRingEquiv {τ : Type*}
    (e : washnitzerAlgebra σ R ≃+* washnitzerAlgebra τ R) (he : ∀ f, ‖e f‖ = ‖f‖)
    (f : intWashnitzerAlgebra σ R) :
    toWashnitzerAlgebra τ R (restrictRingEquiv e he f) = e (toWashnitzerAlgebra σ R f) :=
  toWashnitzerAlgebra_mk _ _

/-- `R°⟨X⟩†` is an `R°`-algebra through the constant series. -/
noncomputable instance : Algebra (Subring.unitClosedBall R) (intWashnitzerAlgebra σ R) :=
  RingHom.toAlgebra <| ((C : R →+* MvPowerSeries σ R).comp
    (Subring.unitClosedBall R).subtype).codRestrict _ fun a ↦
      C_mem_intWashnitzerAlgebra_iff.2 (Subring.mem_unitClosedBall.1 a.2)

/-- The structure map `R° → R°⟨X⟩†` sends `a` to the constant series `a`. -/
@[simp]
theorem coe_algebraMap (a : Subring.unitClosedBall R) :
    (algebraMap (Subring.unitClosedBall R) (intWashnitzerAlgebra σ R) a : MvPowerSeries σ R) =
      C (a : R) :=
  (rfl)

/-- Integral coefficients act compatibly through the integral overconvergent algebra. -/
instance : IsScalarTower (Subring.unitClosedBall R) (intWashnitzerAlgebra σ R)
    (washnitzerAlgebra σ R) := .of_algebraMap_eq fun a ↦ by
  apply Subtype.ext
  simp [IsScalarTower.algebraMap_eq (Subring.unitClosedBall R) R (washnitzerAlgebra σ R),
    MvPowerSeries.algebraMap_apply, Algebra.algebraMap_ofSubsemiring_apply]

/-- The inclusion into `R⟨X⟩†` sends the constant `a ∈ R°` to the constant `a`. -/
@[simp]
theorem toWashnitzerAlgebra_algebraMap (a : Subring.unitClosedBall R) :
    toWashnitzerAlgebra σ R (algebraMap (Subring.unitClosedBall R) (intWashnitzerAlgebra σ R) a) =
      algebraMap R (washnitzerAlgebra σ R) a :=
  Subtype.ext (by simp [MvPowerSeries.algebraMap_apply])

/-- A multiple of the constant `a ∈ R°` in `R°⟨X⟩†` has Gauss norm at most `‖a‖`. -/
theorem norm_toWashnitzerAlgebra_le_of_mem_span {a : Subring.unitClosedBall R}
    {f : intWashnitzerAlgebra σ R}
    (hf : f ∈ Ideal.span {algebraMap (Subring.unitClosedBall R) (intWashnitzerAlgebra σ R) a}) :
    ‖toWashnitzerAlgebra σ R f‖ ≤ ‖(a : R)‖ := by
  obtain ⟨b, rfl⟩ := Ideal.mem_span_singleton'.1 hf
  rw [map_mul, toWashnitzerAlgebra_algebraMap]
  refine (norm_mul_le _ _).trans ?_
  rw [washnitzerAlgebra.norm_algebraMap]
  exact mul_le_of_le_one_left (norm_nonneg _) (norm_toWashnitzerAlgebra_le_one b)

variable (σ R) in
/-- The inclusion of the polynomials with coefficients in `R°` into `R°⟨X⟩†`. -/
noncomputable def ofMvPolynomial :
    MvPolynomial σ (Subring.unitClosedBall R) →ₐ[Subring.unitClosedBall R]
      intWashnitzerAlgebra σ R :=
  MvPolynomial.aeval fun i ↦ ⟨MvPowerSeries.X i, X_mem_intWashnitzerAlgebra i⟩

/-- A polynomial over `R°` viewed in `R°⟨X⟩†` is the polynomial viewed as a power series over
`R`. -/
@[simp]
theorem coe_ofMvPolynomial (p : MvPolynomial σ (Subring.unitClosedBall R)) :
    (ofMvPolynomial σ R p : MvPowerSeries σ R) =
      ((p.map (Subring.unitClosedBall R).subtype : MvPolynomial σ R) : MvPowerSeries σ R) := by
  induction p using MvPolynomial.induction_on with
  | C a => simp [ofMvPolynomial]
  | add p q hp hq => simp [hp, hq]
  | mul_X p i hp => simp_all [ofMvPolynomial]

/-- The coefficients of a polynomial over `R°` viewed in `R°⟨X⟩†` are its coefficients. -/
theorem coeff_ofMvPolynomial (p : MvPolynomial σ (Subring.unitClosedBall R)) (t : σ →₀ ℕ) :
    coeff t (ofMvPolynomial σ R p : MvPowerSeries σ R) = p.coeff t := by
  simp [MvPolynomial.coeff_map]

end intWashnitzerAlgebra

/-- **The Monsky–Washnitzer degree growth condition**, in coefficient form. For finitely many
variables and any `0 < q < 1`, a series lies in `R°⟨X⟩†` iff for some integer `c > 0` its
coefficients satisfy `‖aᵥ‖ ≤ q ^ ⌊|ν| / c⌋`. Over a normed field and for `q = ‖π‖`, this says
that `aᵥ ∈ πʲ K°` as soon as `|ν| ≥ c j`. -/
theorem mem_intWashnitzerAlgebra_iff_exists_norm_coeff_le_pow [Finite σ] {q : ℝ} (hq0 : 0 < q)
    (hq1 : q < 1) {f : MvPowerSeries σ R} :
    f ∈ intWashnitzerAlgebra σ R ↔ ∃ c > 0, ∀ t, ‖coeff t f‖ ≤ q ^ (t.degree / c) := by
  rw [mem_intWashnitzerAlgebra_iff, mem_washnitzerAlgebra_iff_norm_coeff_le]
  constructor
  · rintro ⟨⟨ρ, hρ, C, hC⟩, h1⟩
    -- With `M = max C 1` and `M / q < ρ ^ c`, the bound `‖aᵥ‖ ≤ M ρ^{-|ν|}` gives
    -- `‖aᵥ‖ ≤ M (q / M) ^ j ≤ q ^ j` whenever `|ν| ≥ c j` with `j ≥ 1`.
    set M := max C 1
    have hM : 1 ≤ M := le_max_right _ _
    obtain ⟨c, hc⟩ := pow_unbounded_of_one_lt (M / q) hρ
    refine ⟨c + 1, c.succ_pos, fun t ↦ ?_⟩
    set j := t.degree / (c + 1)
    rcases Nat.eq_zero_or_pos j with hj | hj
    · simpa [hj] using h1 t
    have hqM : M / q < ρ ^ (c + 1) :=
      hc.trans_le (pow_le_pow_right₀ hρ.le c.le_succ)
    calc ‖coeff t f‖ ≤ C * (ρ ^ t.degree)⁻¹ := hC t
      _ ≤ M * ((ρ ^ (c + 1)) ^ j)⁻¹ := by
          rw [← pow_mul]
          gcongr
          · exact le_max_left _ _
          · exact hρ.le
          · exact Nat.mul_div_le _ _
      _ ≤ M * ((M / q) ^ j)⁻¹ := by gcongr
      _ = q ^ j * (M / M ^ j) := by
          rw [div_pow]
          field_simp
      _ ≤ q ^ j := mul_le_of_le_one_right (by positivity)
          ((div_le_one (by positivity)).2 (le_self_pow₀ hM hj.ne'))
  · rintro ⟨c, hc, h⟩
    -- At the radius `ρ = q^{-1/c} > 1`, `‖aᵥ‖ ρ^{|ν|} ≤ q ^ j q ^ {-(j+1)} = q⁻¹`.
    have hq : 1 < q⁻¹ := one_lt_inv_iff₀.2 ⟨hq0, hq1⟩
    set ρ := q⁻¹ ^ ((c : ℝ)⁻¹)
    have hρc : ρ ^ c = q⁻¹ := Real.rpow_inv_natCast_pow (inv_nonneg.2 hq0.le) hc.ne'
    have hρ : 1 < ρ := Real.one_lt_rpow hq (by positivity)
    refine ⟨⟨ρ, hρ, q⁻¹, fun t ↦ ?_⟩, fun t ↦ (h t).trans (pow_le_one₀ hq0.le hq1.le)⟩
    rw [le_mul_inv_iff₀ (by positivity)]
    calc ‖coeff t f‖ * ρ ^ t.degree ≤ q ^ (t.degree / c) * (ρ ^ c) ^ (t.degree / c + 1) := by
          rw [← pow_mul]
          gcongr
          · exact h t
          · exact hρ.le
          · exact (Nat.lt_mul_div_succ _ hc).le
      _ = q⁻¹ := by
          rw [hρc, inv_pow, pow_succ]
          field_simp

end Defs

section NormedField

variable {σ K : Type*} [NormedField K] [IsUltrametricDist K]

/-- **The Monsky–Washnitzer degree growth condition.** Let `π ∈ K` with `0 < ‖π‖ < 1`. For
finitely many variables, a series lies in `K°⟨X⟩†` iff it is a sum `∑ⱼ πʲ Pⱼ`, converging
coefficientwise, of polynomials `Pⱼ` with coefficients of norm at most one and total degree at
most `c (j + 1)` for some `c`. -/
theorem mem_intWashnitzerAlgebra_iff_exists_hasSum [Finite σ] {π : K} (hπ0 : π ≠ 0)
    (hπ1 : ‖π‖ < 1) {f : MvPowerSeries σ K} :
    f ∈ intWashnitzerAlgebra σ K ↔ ∃ c : ℕ, ∃ P : ℕ → MvPolynomial σ K,
      (∀ j t, ‖(P j).coeff t‖ ≤ 1) ∧ (∀ j, (P j).totalDegree ≤ c * (j + 1)) ∧
        HasSum (fun j ↦ C (π ^ j) * (P j : MvPowerSeries σ K)) f := by
  classical
  have hπ : 0 < ‖π‖ := norm_pos_iff.2 hπ0
  rw [mem_intWashnitzerAlgebra_iff_exists_norm_coeff_le_pow hπ hπ1]
  constructor
  · rintro ⟨c, hc, h⟩
    -- `Pⱼ` collects the monomials `(aᵥ / πʲ) Xᵛ` with `⌊|ν| / c⌋ = j`, of degree `< c (j + 1)`.
    have hfin (j : ℕ) : {t : σ →₀ ℕ | t.degree / c = j}.Finite :=
      (Finsupp.finite_of_degree_lt (c * (j + 1))).subset fun t (ht : t.degree / c = j) ↦
        (ht ▸ Nat.lt_mul_div_succ t.degree hc : t.degree < c * (j + 1))
    let P (j : ℕ) : MvPolynomial σ K :=
      ∑ t ∈ (hfin j).toFinset, MvPolynomial.monomial t (coeff t f / π ^ j)
    have hcoeff (j : ℕ) (t : σ →₀ ℕ) :
        (P j).coeff t = if t.degree / c = j then coeff t f / π ^ j else 0 := by
      simp [P, MvPolynomial.coeff_monomial]
    refine ⟨c, P, fun j t ↦ ?_, fun j ↦ ?_, ?_⟩
    · rw [hcoeff]
      split_ifs with ht
      · rw [norm_div, norm_pow, div_le_one (by positivity), ← ht]
        exact h t
      · simp
    · refine Finset.sup_le fun t ht ↦ ?_
      have ht' := MvPolynomial.mem_support_iff.1 ht
      rw [hcoeff, ite_ne_right_iff] at ht'
      obtain ⟨rfl, -⟩ := ht'
      exact (Nat.lt_mul_div_succ t.degree hc).le
    · refine MvPowerSeries.WithPiTopology.hasSum_iff_hasSum_coeff.2 fun t ↦ ?_
      simp only [coeff_C_mul, MvPolynomial.coeff_coe, hcoeff, mul_ite, mul_zero]
      convert hasSum_ite_eq (t.degree / c) (coeff t f) using 1
      ext j
      simp only [eq_comm (a := t.degree / c)]
      split_ifs
      · exact mul_div_cancel₀ _ (pow_ne_zero _ hπ0)
      · rfl
  · rintro ⟨c, P, hP1, hPdeg, hsum⟩
    -- Only the terms `πʲ Pⱼ` with `|ν| ≤ c (j + 1)` contribute to the coefficient of `Xᵛ`, and
    -- these have norm at most `‖π‖ ^ j ≤ ‖π‖ ^ ⌊|ν| / (c + 1)⌋`.
    refine ⟨c + 1, c.succ_pos, fun t ↦ ?_⟩
    have ht := MvPowerSeries.WithPiTopology.hasSum_iff_hasSum_coeff.1 hsum t
    simp only [coeff_C_mul, MvPolynomial.coeff_coe] at ht
    refine le_of_tendsto' ht.norm fun s ↦
      IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (by positivity) fun j _ ↦ ?_
    rw [norm_mul, norm_pow]
    by_cases h0 : (P j).coeff t = 0
    · simp [h0, pow_nonneg (norm_nonneg π)]
    have hdeg : t.degree ≤ c * (j + 1) :=
      (MvPolynomial.le_totalDegree (MvPolynomial.mem_support_iff.2 h0)).trans (hPdeg j)
    have hj : t.degree / (c + 1) ≤ j :=
      Nat.lt_succ_iff.1 ((Nat.div_lt_iff_lt_mul c.succ_pos).2 (by nlinarith))
    exact (mul_le_of_le_one_right (by positivity) (hP1 j t)).trans
      (pow_le_pow_of_le_one hπ.le hπ1.le hj)

/-- **`K⟨X⟩† = K°⟨X⟩†[1/π]`.** For `π ∈ K` with `0 < ‖π‖ < 1`, a series is overconvergent iff
some power of `π` multiplies it into the integral Monsky–Washnitzer algebra. -/
theorem mem_washnitzerAlgebra_iff_exists_C_pow_mul_mem {π : K} (hπ0 : π ≠ 0) (hπ1 : ‖π‖ < 1)
    {f : MvPowerSeries σ K} :
    f ∈ washnitzerAlgebra σ K ↔ ∃ k : ℕ, C (π ^ k) * f ∈ intWashnitzerAlgebra σ K := by
  refine ⟨fun hf ↦ ?_, fun ⟨k, hk⟩ ↦ ?_⟩
  · -- The coefficients of an overconvergent series are bounded, by `B` say, and `‖π‖ ^ k B ≤ 1`
    -- for large `k`.
    obtain ⟨ρ, hρ, hfρ⟩ := mem_washnitzerAlgebra.1 hf
    obtain ⟨B, hB⟩ := (isRestricted_const_iff.1 hfρ).bddAbove_range_of_cofinite
    obtain ⟨k, hk⟩ := exists_pow_lt_of_lt_one (inv_pos.2 (zero_lt_one.trans_le
      (le_max_right B 1))) hπ1
    refine ⟨k, mem_intWashnitzerAlgebra_iff.2
      ⟨mul_mem (C_mem_washnitzerAlgebra _) hf, fun t ↦ ?_⟩⟩
    have ht : ‖coeff t f‖ ≤ max B 1 :=
      calc ‖coeff t f‖ ≤ ‖coeff t f‖ * ρ ^ t.degree :=
            le_mul_of_one_le_right (norm_nonneg _) (one_le_pow₀ hρ.le)
        _ ≤ B := hB ⟨t, rfl⟩
        _ ≤ max B 1 := le_max_left _ _
    rw [coeff_C_mul, norm_mul, norm_pow]
    calc ‖π‖ ^ k * ‖coeff t f‖ ≤ (max B 1)⁻¹ * max B 1 := by gcongr
      _ = 1 := inv_mul_cancel₀ (zero_lt_one.trans_le (le_max_right B 1)).ne'
  · have := mul_mem (C_mem_washnitzerAlgebra (π ^ k)⁻¹) (intWashnitzerAlgebra_le hk)
    simpa [← mul_assoc, ← map_mul, ← map_pow, hπ0] using this

namespace intWashnitzerAlgebra

/-- **Divisibility by constants.** Over a field, a series in `K°⟨X⟩†` is a multiple of the
constant `a ∈ K°` iff its Gauss norm is at most `‖a‖`. -/
theorem mem_span_algebraMap_iff_norm_le {a : Subring.unitClosedBall K}
    {f : intWashnitzerAlgebra σ K} :
    f ∈ Ideal.span {algebraMap (Subring.unitClosedBall K) (intWashnitzerAlgebra σ K) a} ↔
      ‖toWashnitzerAlgebra σ K f‖ ≤ ‖(a : K)‖ := by
  refine ⟨norm_toWashnitzerAlgebra_le_of_mem_span, fun hf ↦ ?_⟩
  rcases eq_or_ne (a : K) 0 with ha | ha
  · rw [ha, norm_zero, norm_le_zero_iff, ← map_zero (toWashnitzerAlgebra σ K)] at hf
    rw [toWashnitzerAlgebra_injective hf]
    exact zero_mem _
  refine Ideal.mem_span_singleton'.2
    ⟨⟨((algebraMap K (washnitzerAlgebra σ K) (a : K)⁻¹ * toWashnitzerAlgebra σ K f :
      washnitzerAlgebra σ K) : MvPowerSeries σ K), mem_intWashnitzerAlgebra_iff_norm_le_one.2 ?_⟩,
      toWashnitzerAlgebra_injective ?_⟩
  · rw [norm_mul, washnitzerAlgebra.norm_algebraMap, norm_inv]
    exact inv_mul_le_one_of_le₀ hf (norm_nonneg _)
  · refine Subtype.ext ?_
    simp [MvPowerSeries.algebraMap_apply, mul_right_comm _ (f : MvPowerSeries σ K), ← map_mul, ha]

end intWashnitzerAlgebra

variable [CompleteSpace K]

/-- **Units of the integral Monsky–Washnitzer algebra.** Over a complete ultrametric normed
field, a series in `K°⟨X⟩†` is a unit there iff its constant coefficient has norm one and every
other coefficient has norm less than one. -/
theorem isUnit_intWashnitzerAlgebra_iff {f : intWashnitzerAlgebra σ K} :
    IsUnit f ↔ ‖constantCoeff (f : MvPowerSeries σ K)‖ = 1 ∧
      ∀ t ≠ 0, ‖coeff t (f : MvPowerSeries σ K)‖ < 1 := by
  set F := intWashnitzerAlgebra.toWashnitzerAlgebra σ K f
  have hF1 : ‖F‖ ≤ 1 := mem_intWashnitzerAlgebra_iff_norm_le_one.1 f.2
  refine ⟨fun hf ↦ ?_, fun ⟨h0, hlt⟩ ↦ ?_⟩
  · -- The constant coefficients of `f` and of its inverse have norm at most one and multiply to
    -- one, so both have norm one; the other coefficients are then controlled by the unit
    -- criterion in `K⟨X⟩†`.
    obtain ⟨g, hg⟩ := hf.exists_right_inv
    have hfg : ‖constantCoeff (f : MvPowerSeries σ K)‖ *
        ‖constantCoeff (g : MvPowerSeries σ K)‖ = 1 := by
      simpa using
        congrArg (fun x : intWashnitzerAlgebra σ K ↦ ‖constantCoeff (x : MvPowerSeries σ K)‖) hg
    have hf0 := intWashnitzerAlgebra.norm_constantCoeff_le_one f
    have hg0 := intWashnitzerAlgebra.norm_constantCoeff_le_one g
    have h1 : ‖constantCoeff (f : MvPowerSeries σ K)‖ = 1 := by
      nlinarith [norm_nonneg (constantCoeff (f : MvPowerSeries σ K)),
        norm_nonneg (constantCoeff (g : MvPowerSeries σ K))]
    refine ⟨h1, fun t ht ↦ ?_⟩
    simpa [h1, F] using ((isUnit_washnitzerAlgebra_iff F).1
      (hf.map (intWashnitzerAlgebra.toWashnitzerAlgebra σ K))).2 t ht
  · -- `F` is a unit of `K⟨X⟩†` of Gauss norm one, so its inverse has Gauss norm one as well.
    have hF : IsUnit F := (isUnit_washnitzerAlgebra_iff F).2
      ⟨fun h ↦ by simp only [F, intWashnitzerAlgebra.coe_toWashnitzerAlgebra] at h; simp [h] at h0,
        fun t ht ↦ by simpa [F, h0] using hlt t ht⟩
    obtain ⟨u, hu⟩ := hF
    have hnorm : ‖F‖ = 1 := by
      refine le_antisymm hF1 ?_
      simpa [F, h0, coeff_zero_eq_constantCoeff_apply] using washnitzerAlgebra.norm_coeff_le F 0
    have hinv : ‖(↑u⁻¹ : washnitzerAlgebra σ K)‖ ≤ 1 := by
      have := congrArg norm u.mul_inv
      rw [norm_mul, hu, hnorm, one_mul, norm_one] at this
      exact this.le
    have hmem := mem_intWashnitzerAlgebra_iff_norm_le_one.2 hinv
    refine ⟨⟨f, ⟨_, hmem⟩, Subtype.ext ?_, Subtype.ext ?_⟩, rfl⟩
    · simpa [hu, F] using congrArg Subtype.val u.mul_inv
    · simpa [hu, F] using congrArg Subtype.val u.inv_mul

/-- **The Jacobson radical of the integral Monsky–Washnitzer algebra.** Over a complete
ultrametric normed field, a series in `K°⟨X⟩†` lies in the Jacobson radical iff all its
coefficients have norm less than one. In particular, for every constant `π` with `‖π‖ < 1` and
every `f ∈ K°⟨X⟩†`, the series `1 + π f` is a unit. -/
theorem mem_jacobson_bot_intWashnitzerAlgebra_iff {f : intWashnitzerAlgebra σ K} :
    f ∈ Ideal.jacobson ⊥ ↔ ∀ t, ‖coeff t (f : MvPowerSeries σ K)‖ < 1 := by
  classical
  rw [Ideal.jacobson_bot, Ring.mem_jacobson_iff]
  constructor
  · intro h t
    by_contra! ht
    by_cases h0 : ‖constantCoeff (f : MvPowerSeries σ K)‖ < 1
    · -- A coefficient of norm one in positive degree survives in `f + 1`.
      have ht0 : t ≠ 0 := by
        rintro rfl
        rw [coeff_zero_eq_constantCoeff_apply] at ht
        exact ht.not_gt h0
      have := (isUnit_intWashnitzerAlgebra_iff.1 (h 1)).2 t ht0
      simp [coeff_one, ht0] at this
      exact this.not_ge ht
    · -- A constant coefficient of norm one is cancelled by multiplying by `-f(0)⁻¹`.
      push Not at h0
      set a := constantCoeff (f : MvPowerSeries σ K)
      have ha : a ≠ 0 := norm_pos_iff.1 (zero_lt_one.trans_le h0)
      have hy : C (-a⁻¹) ∈ intWashnitzerAlgebra σ K := by
        rw [C_mem_intWashnitzerAlgebra_iff, norm_neg, norm_inv]
        exact inv_le_one_of_one_le₀ h0
      have := (isUnit_intWashnitzerAlgebra_iff.1 (h ⟨_, hy⟩)).1
      simp [a, ha] at this
  · intro h y
    -- The coefficients of `f y` have norm less than one, so `f y + 1` passes the unit test.
    have hfy : ∀ t, ‖coeff t ((f * y : intWashnitzerAlgebra σ K) : MvPowerSeries σ K)‖ < 1 := by
      have hf : ‖intWashnitzerAlgebra.toWashnitzerAlgebra σ K f‖ < 1 :=
        washnitzerAlgebra.norm_lt_iff.2 h
      have hy : ‖intWashnitzerAlgebra.toWashnitzerAlgebra σ K y‖ ≤ 1 :=
        mem_intWashnitzerAlgebra_iff_norm_le_one.1 y.2
      have hlt := (norm_mul_le _ _).trans_lt
        ((mul_le_of_le_one_right (norm_nonneg _) hy).trans_lt hf)
      rw [← map_mul] at hlt
      exact washnitzerAlgebra.norm_lt_iff.1 hlt
    refine isUnit_intWashnitzerAlgebra_iff.2 ⟨?_, fun t ht ↦ ?_⟩
    · have h0 := hfy 0
      rw [coeff_zero_eq_constantCoeff_apply] at h0
      have hne : ‖constantCoeff (f : MvPowerSeries σ K) * constantCoeff (y : MvPowerSeries σ K)‖ ≠
          ‖(1 : K)‖ := by
        simpa using h0.ne
      simpa [IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm hne] using h0.le
    · simpa [coeff_one, ht] using hfy t

end NormedField

section Reduction

section NormedCommRing

variable {σ R : Type*} [NormedCommRing R] [IsUltrametricDist R] [NormOneClass R]

local notation "R°" => Subring.unitClosedBall R

namespace intWashnitzerAlgebra

/-- **The polynomials divisible by `ϖ` in `R°⟨X⟩†` are those divisible by `ϖ` in `R°[X]`.** The
kernel of `R°[X] → R°⟨X⟩† ⧸ ϖ` is generated by `ϖ`. No hypothesis on `ϖ` is needed. -/
theorem ker_mkₐ_comp_ofMvPolynomial (ϖ : R°) :
    RingHom.ker ((Ideal.Quotient.mkₐ R° (Ideal.span
      {algebraMap R° (intWashnitzerAlgebra σ R) ϖ})).comp (ofMvPolynomial σ R)) =
      Ideal.span {MvPolynomial.C ϖ} := by
  ext p
  simp only [RingHom.mem_ker, AlgHom.comp_apply, Ideal.Quotient.mkₐ_eq_mk,
    Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton]
  refine ⟨fun ⟨g, hg⟩ ↦ (MvPolynomial.C_dvd_iff_dvd_coeff ϖ p).2 fun t ↦ ?_, fun h ↦ ?_⟩
  · -- The coefficients of `p = ϖ g` are `ϖ` times the coefficients of `g`, which lie in `R°`.
    refine ⟨⟨coeff t (g : MvPowerSeries σ R), Subring.mem_unitClosedBall.2
      (norm_coeff_le_one g t)⟩, Subtype.ext ?_⟩
    have := congrArg (fun x : intWashnitzerAlgebra σ R ↦ coeff t (x : MvPowerSeries σ R)) hg
    simp only [coeff_ofMvPolynomial, MulMemClass.coe_mul, coe_algebraMap, coeff_C_mul] at this
    exact this
  · simpa using map_dvd (ofMvPolynomial σ R) h

end intWashnitzerAlgebra

end NormedCommRing

section NormedField

variable {σ K : Type*} [NormedField K] [IsUltrametricDist K]

local notation "K°" => Subring.unitClosedBall K

namespace intWashnitzerAlgebra

/-- **Series in `K°⟨X⟩†` are polynomials modulo `ϖ`.** For every nonzero `ϖ ∈ K°`, a series in
`K°⟨X⟩†` is the sum of a polynomial with coefficients in `K°` and of `ϖ` times a series in
`K°⟨X⟩†`: only finitely many of its coefficients have norm at least `‖ϖ‖`. -/
theorem exists_ofMvPolynomial_add_algebraMap_mul_eq {ϖ : K°} (hϖ : ϖ ≠ 0)
    (f : intWashnitzerAlgebra σ K) : ∃ (p : MvPolynomial σ K°) (g : intWashnitzerAlgebra σ K),
      ofMvPolynomial σ K p + algebraMap K° _ ϖ * g = f := by
  classical
  have hϖ0 : 0 < ‖(ϖ : K)‖ := norm_pos_iff.2 (by simpa using hϖ)
  -- The coefficients of `f` tend to zero, so only finitely many have norm at least `‖ϖ‖`.
  have hf : Filter.Tendsto (fun t ↦ ‖coeff t (f : MvPowerSeries σ K)‖) Filter.cofinite
      (nhds 0) :=
    isRestricted_one_iff.1
      (isRestricted_of_mem_washnitzerAlgebra (intWashnitzerAlgebra_le f.2) zero_le_one le_rfl)
  have hS : {t | ¬ ‖coeff t (f : MvPowerSeries σ K)‖ < ‖(ϖ : K)‖}.Finite :=
    Filter.eventually_cofinite.1 (hf.eventually (gt_mem_nhds hϖ0))
  -- `p` is the part of `f` made of these coefficients.
  let F : MvPowerSeries σ K° := fun t ↦
    ⟨coeff t (f : MvPowerSeries σ K), Subring.mem_unitClosedBall.2 (norm_coeff_le_one f t)⟩
  let p : MvPolynomial σ K° := truncFinset K° hS.toFinset F
  have hp (t : σ →₀ ℕ) : coeff t (ofMvPolynomial σ K p : MvPowerSeries σ K) =
      if ‖coeff t (f : MvPowerSeries σ K)‖ < ‖(ϖ : K)‖ then 0
      else coeff t (f : MvPowerSeries σ K) := by
    -- `MvPowerSeries` is a function type, and `coeff t` evaluates at `t`.
    have hF : coeff t F = ⟨coeff t (f : MvPowerSeries σ K), _⟩ := coeff_apply F t
    simp only [coeff_ofMvPolynomial, p, coeff_truncFinset, Set.Finite.mem_toFinset, hF]
    by_cases ht : ‖coeff t (f : MvPowerSeries σ K)‖ < ‖(ϖ : K)‖
    · simp [ht]
    · simp [ht, not_lt.1 ht]
  -- The remainder `f - p` has coefficients of norm at most `‖ϖ‖`, so it is divisible by `ϖ`.
  set h := f - ofMvPolynomial σ K p
  have hh (t : σ →₀ ℕ) : ‖(ϖ : K)⁻¹ * coeff t (h : MvPowerSeries σ K)‖ ≤ 1 := by
    rw [norm_mul, norm_inv, inv_mul_le_one₀ hϖ0, AddSubgroupClass.coe_sub, map_sub, hp]
    split_ifs with ht
    · simpa using ht.le
    · simp
  refine ⟨p, ⟨C (ϖ : K)⁻¹ * (h : MvPowerSeries σ K), mem_intWashnitzerAlgebra_iff.2
    ⟨mul_mem (C_mem_washnitzerAlgebra _) (intWashnitzerAlgebra_le h.2), fun t ↦ ?_⟩⟩,
    Subtype.ext ?_⟩
  · simpa [coeff_C_mul] using hh t
  · simp [h, ← mul_assoc, ← map_mul, mul_inv_cancel₀ (show (ϖ : K) ≠ 0 by simpa using hϖ)]

/-- **Polynomials surject onto `K°⟨X⟩† ⧸ ϖ`** for every nonzero `ϖ ∈ K°`. -/
theorem surjective_mkₐ_comp_ofMvPolynomial {ϖ : K°} (hϖ : ϖ ≠ 0) :
    Function.Surjective ((Ideal.Quotient.mkₐ K° (Ideal.span
      {algebraMap K° (intWashnitzerAlgebra σ K) ϖ})).comp (ofMvPolynomial σ K)) := by
  intro x
  obtain ⟨f, rfl⟩ := Ideal.Quotient.mk_surjective x
  obtain ⟨p, g, rfl⟩ := exists_ofMvPolynomial_add_algebraMap_mul_eq hϖ f
  refine ⟨p, ?_⟩
  simp only [AlgHom.comp_apply, Ideal.Quotient.mkₐ_eq_mk, map_add, map_mul,
    Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.mem_span_singleton_self _), zero_mul, add_zero]

/-- **Reduction of the integral Monsky–Washnitzer algebra.** For every nonzero `ϖ ∈ K°`,
`K°⟨X⟩† ⧸ ϖ ≃ (K° ⧸ ϖ)[X]`: overconvergent series with integral coefficients reduce modulo `ϖ`
to polynomials. For a uniformiser `π` and `ϖ = πᵐ` this is
`O_K⟨X⟩† ⧸ πᵐ ≃ (O_K ⧸ πᵐ)[X]`. -/
noncomputable def quotientSpanEquivMvPolynomial {ϖ : K°} (hϖ : ϖ ≠ 0) :
    (intWashnitzerAlgebra σ K ⧸ Ideal.span {algebraMap K° (intWashnitzerAlgebra σ K) ϖ}) ≃ₐ[K°]
      MvPolynomial σ (K° ⧸ Ideal.span {ϖ}) :=
  (Ideal.quotientKerAlgEquivOfSurjective (surjective_mkₐ_comp_ofMvPolynomial hϖ)).symm.trans <|
    (Ideal.quotientEquivAlgOfEq K° (J := Ideal.map MvPolynomial.C (Ideal.span {ϖ})) (by
      rw [ker_mkₐ_comp_ofMvPolynomial, Ideal.map_span, Set.image_singleton])).trans
      (MvPolynomial.quotientEquivQuotientMvPolynomial (Ideal.span {ϖ})).symm

/-- The reduction of the class of a polynomial over `K°` is its coefficientwise reduction. -/
@[simp]
theorem quotientSpanEquivMvPolynomial_mk_ofMvPolynomial {ϖ : K°} (hϖ : ϖ ≠ 0)
    (p : MvPolynomial σ K°) :
    quotientSpanEquivMvPolynomial hϖ (Ideal.Quotient.mk _ (ofMvPolynomial σ K p)) =
      p.map (Ideal.Quotient.mk (Ideal.span {ϖ})) := by
  have h : Ideal.Quotient.mk (Ideal.span {algebraMap K° (intWashnitzerAlgebra σ K) ϖ})
      (ofMvPolynomial σ K p) = (Ideal.Quotient.mkₐ K° _).comp (ofMvPolynomial σ K) p := by
    rw [AlgHom.comp_apply, Ideal.Quotient.mkₐ_eq_mk]
  rw [quotientSpanEquivMvPolynomial, AlgEquiv.trans_apply, AlgEquiv.trans_apply, h,
    Ideal.quotientKerAlgEquivOfSurjective_symm_apply, Ideal.quotientEquivAlgOfEq_mk,
    AlgEquiv.symm_apply_eq]
  clear h
  -- It remains to evaluate Mathlib's `(K° ⧸ ϖ)[X] ≃ K°[X] ⧸ ϖ` on a reduced polynomial.
  induction p using MvPolynomial.induction_on with
  | C a => simp [MvPolynomial.quotientEquivQuotientMvPolynomial]
  | add p q hp hq => simp only [map_add, hp, hq]
  | mul_X p i hp => simp [hp, MvPolynomial.quotientEquivQuotientMvPolynomial]

end intWashnitzerAlgebra

end NormedField

end Reduction

section AdicCompletion

/-! ### The `ϖ`-adic completion -/

section NormedCommRing

variable {σ R : Type*} [NormedCommRing R] [IsUltrametricDist R] [NormOneClass R]

local notation "R°" => Subring.unitClosedBall R
local notation "T" => IsRestricted.subring (R := R) (fun _ : σ ↦ (1 : ℝ))

namespace intWashnitzerAlgebra

variable (σ R) in
/-- The inclusion `R°⟨X⟩† → T°` of the integral Monsky–Washnitzer algebra into the closed unit
ball `T°` of the unit-radius Tate algebra `T = R⟨X⟩`. The ring `T°` consists of the restricted
series with coefficients in `R°`. -/
noncomputable def toTate : intWashnitzerAlgebra σ R →+* Subring.unitClosedBall T :=
  ((washnitzerAlgebra.toTate σ R).toRingHom.comp (toWashnitzerAlgebra σ R)).codRestrict _
    fun f ↦ Subring.mem_unitClosedBall.2 (mem_intWashnitzerAlgebra_iff_norm_le_one.1 f.2)

/-- The inclusion into `T°` does not change the underlying series. -/
@[simp]
theorem coe_toTate (f : intWashnitzerAlgebra σ R) :
    ((toTate σ R f : T) : MvPowerSeries σ R) = f :=
  washnitzerAlgebra.coe_toTate (toWashnitzerAlgebra σ R f)

/-- The inclusion into `T°` is injective. -/
theorem toTate_injective : Function.Injective (toTate σ R) :=
  fun f g h ↦ Subtype.ext (by simpa using congrArg (fun x : Subring.unitClosedBall T ↦
    ((x : T) : MvPowerSeries σ R)) h)

/-- The inclusion into `T°` sends a scalar `a ∈ R°` to the scalar `a` of the Tate algebra. -/
@[simp]
theorem coe_toTate_algebraMap (a : R°) :
    (toTate σ R (algebraMap R° _ a) : T) = algebraMap R T a :=
  Subtype.ext (by simp)

end intWashnitzerAlgebra

end NormedCommRing

section NormedField

variable {σ K : Type*} [NormedField K] [IsUltrametricDist K]

local notation "K°" => Subring.unitClosedBall K
local notation "T" => IsRestricted.subring (R := K) (fun _ : σ ↦ (1 : ℝ))

namespace intWashnitzerAlgebra

/-- **The powers of `ϖ K°⟨X⟩†`**: a series in `K°⟨X⟩†` lies in `(ϖ) ^ n` iff all its coefficients
have norm at most `‖ϖ‖ ^ n`. -/
theorem mem_span_algebraMap_pow_iff {ϖ : K°} (n : ℕ)
    {f : intWashnitzerAlgebra σ K} :
    f ∈ Ideal.span {algebraMap K° (intWashnitzerAlgebra σ K) ϖ} ^ n ↔
      ∀ t, ‖coeff t (f : MvPowerSeries σ K)‖ ≤ ‖(ϖ : K)‖ ^ n := by
  rcases eq_or_ne ϖ 0 with rfl | hϖ
  · rcases n with _ | n
    · simpa using norm_coeff_le_one f
    · rw [map_zero, Ideal.span_singleton_zero, Ideal.bot_pow n.succ_ne_zero, Ideal.mem_bot,
        Subtype.ext_iff]
      simp only [ZeroMemClass.coe_zero, MvPowerSeries.ext_iff, map_zero, norm_zero, ne_eq,
        add_eq_zero, one_ne_zero, and_false, not_false_eq_true, zero_pow]
      exact forall_congr' fun t ↦ norm_le_zero_iff.symm
  have hϖ0 : (ϖ : K) ≠ 0 := by simpa using hϖ
  rw [Ideal.span_singleton_pow, ← map_pow, Ideal.mem_span_singleton']
  constructor
  · rintro ⟨g, rfl⟩ t
    simpa [← map_pow, coeff_mul_C, mul_comm] using
      mul_le_mul_of_nonneg_left (norm_coeff_le_one g t) (pow_nonneg (norm_nonneg (ϖ : K)) n)
  · intro h
    -- `ϖ⁻ⁿ f` is overconvergent with coefficients of norm at most one.
    refine ⟨⟨C ((ϖ : K) ^ n)⁻¹ * (f : MvPowerSeries σ K), mem_intWashnitzerAlgebra_iff.2
      ⟨mul_mem (C_mem_washnitzerAlgebra _) (intWashnitzerAlgebra_le f.2), fun t ↦ ?_⟩⟩,
      Subtype.ext ?_⟩
    · rw [coeff_C_mul, norm_mul, norm_inv, norm_pow]
      exact inv_mul_le_one_of_le₀ (h t) (by positivity)
    · simp only [MulMemClass.coe_mul, coe_algebraMap, SubmonoidClass.coe_pow]
      rw [mul_right_comm, ← map_mul, inv_mul_cancel₀ (pow_ne_zero n hϖ0), map_one, one_mul]

/-- The multiplicative pseudo-uniformiser `ϖ` of the Tate algebra. -/
private noncomputable def tatePseudoUniformizer {ϖ : K°} (hϖ : ϖ ≠ 0) (hϖ1 : ‖(ϖ : K)‖ < 1) :
    NormedRing.PseudoUniformizer T :=
  .ofAlgebraMap (c := (ϖ : K)) (by simpa using hϖ) hϖ1

private theorem toUnitClosedBall_tatePseudoUniformizer {ϖ : K°} (hϖ : ϖ ≠ 0) (hϖ1 : ‖(ϖ : K)‖ < 1) :
    (tatePseudoUniformizer (σ := σ) hϖ hϖ1).toUnitClosedBall = toTate σ K (algebraMap K° _ ϖ) :=
  Subtype.ext (by simp [tatePseudoUniformizer])

private theorem mem_span_toTate_algebraMap_pow_iff {ϖ : K°} (hϖ : ϖ ≠ 0) (hϖ1 : ‖(ϖ : K)‖ < 1)
    (n : ℕ) {x : Subring.unitClosedBall T} :
    x ∈ Ideal.span {toTate σ K (algebraMap K° _ ϖ)} ^ n ↔ ‖(x : T)‖ ≤ ‖(ϖ : K)‖ ^ n := by
  rw [← toUnitClosedBall_tatePseudoUniformizer hϖ hϖ1,
    NormedRing.PseudoUniformizer.mem_span_toUnitClosedBall_pow_iff, tatePseudoUniformizer,
    NormedRing.PseudoUniformizer.coe_unit_ofAlgebraMap, norm_algebraMap']

/-- The ideal `ϖ K°⟨X⟩†` is carried into the ideal `ϖ T°`. -/
theorem span_algebraMap_le_comap_toTate {ϖ : K°} :
    Ideal.span {algebraMap K° (intWashnitzerAlgebra σ K) ϖ} ≤
      (Ideal.span {toTate σ K (algebraMap K° _ ϖ)}).comap (toTate σ K) :=
  Ideal.span_le.2 (Set.singleton_subset_iff.2 (Ideal.mem_span_singleton_self _))

/-- **`K°⟨X⟩† ⧸ ϖⁿ ≃ T° ⧸ ϖⁿ`.** Reduction modulo `ϖⁿ` identifies the integral Monsky–Washnitzer
algebra with the closed unit ball `T°` of the Tate algebra: the overconvergent series are dense
in `T°`, and an overconvergent series divisible by `ϖⁿ` in `T°` is divisible by `ϖⁿ` in
`K°⟨X⟩†`. -/
theorem quotientMap_toTate_bijective {ϖ : K°} (hϖ : ϖ ≠ 0) (n : ℕ) :
    Function.Bijective (Ideal.quotientMap (Ideal.span {toTate σ K (algebraMap K° _ ϖ)} ^ n)
      (toTate σ K) ((Ideal.pow_right_mono span_algebraMap_le_comap_toTate n).trans
        (Ideal.le_comap_pow _ n))) := by
  rcases (Subring.mem_unitClosedBall.1 ϖ.2).lt_or_eq with hϖ1 | hϖ1
  · have hr : 0 < ‖(ϖ : K)‖ ^ n := pow_pos (norm_pos_iff.2 (by simpa using hϖ)) n
    refine ⟨Ideal.quotientMap_injective' fun f hf ↦ ?_, fun y ↦ ?_⟩
    · rw [Ideal.mem_comap, mem_span_toTate_algebraMap_pow_iff hϖ hϖ1] at hf
      exact (mem_span_algebraMap_pow_iff n).2 fun t ↦
        (washnitzerAlgebra.norm_coeff_le (toWashnitzerAlgebra σ K f) t).trans hf
    · -- Approximate a representative `s ∈ T°` by an overconvergent series to within `‖ϖ‖ ^ n`.
      obtain ⟨s, rfl⟩ := Ideal.Quotient.mk_surjective y
      obtain ⟨w, hw⟩ := Metric.denseRange_iff.1 washnitzerAlgebra.denseRange_toTate (s : T) _ hr
      rw [dist_eq_norm'] at hw
      have hw1 : ‖w‖ ≤ 1 := by
        have h := IsUltrametricDist.norm_add_le_max (s : T) (washnitzerAlgebra.toTate σ K w - s)
        rw [add_sub_cancel] at h
        exact h.trans (max_le (Subring.mem_unitClosedBall.1 s.2)
          (hw.le.trans (pow_le_one₀ (norm_nonneg _) hϖ1.le)))
      refine ⟨Ideal.Quotient.mk _ ⟨w, mem_intWashnitzerAlgebra_iff_norm_le_one.2 hw1⟩, ?_⟩
      rw [Ideal.quotientMap_mk, Ideal.Quotient.eq, mem_span_toTate_algebraMap_pow_iff hϖ hϖ1]
      exact hw.le
  · -- If `‖ϖ‖ = 1` then `ϖ` is a unit, so both quotients are trivial.
    have hu : IsUnit ϖ := IsUnit.of_mul_eq_one ⟨(ϖ : K)⁻¹, by simp [hϖ1]⟩
      (Subtype.ext (mul_inv_cancel₀ (by simpa using hϖ)))
    have hJ : Ideal.span {algebraMap K° (intWashnitzerAlgebra σ K) ϖ} ^ n = ⊤ := by
      rw [Ideal.span_singleton_pow, Ideal.span_singleton_eq_top]
      exact (hu.map _).pow n
    have hI : Ideal.span {toTate σ K (algebraMap K° _ ϖ)} ^ n = ⊤ := by
      rw [Ideal.span_singleton_pow, Ideal.span_singleton_eq_top]
      exact ((hu.map _).map _).pow n
    have h1 := Ideal.Quotient.subsingleton_iff.2 hJ
    have h2 := Ideal.Quotient.subsingleton_iff.2 hI
    exact ⟨fun a b _ ↦ Subsingleton.elim a b, fun y ↦ ⟨0, Subsingleton.elim _ _⟩⟩

variable [CompleteSpace K]

/-- **`K°⟨X⟩` is `ϖ`-adically complete**: over a complete field, the closed unit ball `T°` of the
Tate algebra is complete for the `ϖ`-adic topology. -/
theorem isAdicComplete_span_toTate_algebraMap {ϖ : K°} (hϖ1 : ‖(ϖ : K)‖ < 1) :
    IsAdicComplete (Ideal.span {toTate σ K (algebraMap K° _ ϖ)}) (Subring.unitClosedBall T) := by
  rcases eq_or_ne ϖ 0 with rfl | hϖ
  · rw [map_zero, map_zero, Ideal.span_singleton_zero]
    infer_instance
  rw [← toUnitClosedBall_tatePseudoUniformizer hϖ hϖ1]
  exact NormedRing.PseudoUniformizer.isAdicComplete_span_toUnitClosedBall _

variable (σ) in
/-- **The `ϖ`-adic completion of `K°⟨X⟩†` is `K°⟨X⟩`.** Over a complete ultrametric normed field,
for `ϖ ∈ K°` with `0 < ‖ϖ‖ < 1`, the `ϖ`-adic completion of the integral Monsky–Washnitzer algebra
is the closed unit ball `T°` of the Tate algebra, the restricted series with coefficients in
`K°`. The isomorphism extends `intWashnitzerAlgebra.toTate` (`adicCompletionEquiv_of`). -/
noncomputable def adicCompletionEquiv {ϖ : K°} (hϖ : ϖ ≠ 0) (hϖ1 : ‖(ϖ : K)‖ < 1) :
    AdicCompletion (Ideal.span {algebraMap K° (intWashnitzerAlgebra σ K) ϖ})
      (intWashnitzerAlgebra σ K) ≃+* Subring.unitClosedBall T :=
  haveI := isAdicComplete_span_toTate_algebraMap (σ := σ) hϖ1
  (RingEquiv.ofBijective _ (AdicCompletion.mapₐ_bijective (toTate σ K).toIntAlgHom
    span_algebraMap_le_comap_toTate (quotientMap_toTate_bijective hϖ))).trans
    (AdicCompletion.ofAlgEquiv _).symm.toRingEquiv

/-- The completion comparison extends the inclusion `K°⟨X⟩† → T°`. -/
@[simp]
theorem adicCompletionEquiv_of {ϖ : K°} (hϖ : ϖ ≠ 0) (hϖ1 : ‖(ϖ : K)‖ < 1)
    (f : intWashnitzerAlgebra σ K) :
    adicCompletionEquiv σ hϖ hϖ1 (AdicCompletion.of _ _ f) = toTate σ K f := by
  have := isAdicComplete_span_toTate_algebraMap (σ := σ) hϖ1
  rw [adicCompletionEquiv, RingEquiv.trans_apply, RingEquiv.ofBijective_apply]
  exact (congrArg (AdicCompletion.ofAlgEquiv _).symm (AdicCompletion.mapₐ_of _ _ f)).trans
    (AdicCompletion.ofAlgEquiv_symm_of _ _)

/-- Reduction of the completion comparison agrees with the map induced by the inclusion
of integral overconvergent series into integral restricted series. -/
theorem mk_adicCompletionEquiv {ϖ : K°} (hϖ : ϖ ≠ 0) (hϖ1 : ‖(ϖ : K)‖ < 1)
    (n : ℕ) (z : AdicCompletion
      (Ideal.span {algebraMap K° (intWashnitzerAlgebra σ K) ϖ}) (intWashnitzerAlgebra σ K)) :
    Ideal.Quotient.mk (Ideal.span {toTate σ K (algebraMap K° _ ϖ)} ^ n)
        (adicCompletionEquiv σ hϖ hϖ1 z) =
      Ideal.quotientMap _ (toTate σ K)
        ((Ideal.pow_right_mono span_algebraMap_le_comap_toTate n).trans
          (Ideal.le_comap_pow _ n)) (AdicCompletion.evalₐ _ n z) := by
  have := isAdicComplete_span_toTate_algebraMap (σ := σ) hϖ1
  simp only [adicCompletionEquiv, RingEquiv.trans_apply, RingEquiv.ofBijective_apply,
    AlgEquiv.coe_toRingEquiv, AdicCompletion.mk_ofAlgEquiv_symm]
  exact AdicCompletion.evalₐ_mapₐ (toTate σ K).toIntAlgHom
    span_algebraMap_le_comap_toTate n z

end intWashnitzerAlgebra

end NormedField

end AdicCompletion

end TauCeti.Dagger

/-! The power-bounded characterisation is stated outside the scope of
`MvPowerSeries.WithPiTopology` opened above, so that power-boundedness refers to the Gauss norm
topology of `K⟨X⟩†` rather than to the coefficientwise topology. -/

namespace TauCeti.Dagger

variable {σ K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K]

/-- **The integral Monsky–Washnitzer algebra is the ring of power-bounded elements**: an
overconvergent series has all its coefficients in `K°` iff it is power-bounded for the Gauss norm
topology. -/
theorem mem_intWashnitzerAlgebra_iff_isPowerBounded {f : washnitzerAlgebra σ K} :
    (f : MvPowerSeries σ K) ∈ intWashnitzerAlgebra σ K ↔ Huber.IsPowerBounded f := by
  rw [mem_intWashnitzerAlgebra_iff_norm_le_one, washnitzerAlgebra.isPowerBounded_iff_norm_le_one]

end TauCeti.Dagger
