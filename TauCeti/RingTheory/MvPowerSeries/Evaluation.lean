/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
module

public import Mathlib.RingTheory.AdicCompletion.Basic
public import Mathlib.RingTheory.MvPowerSeries.Evaluation
public import TauCeti.Topology.Algebra.Nonarchimedean.AdicTopology
import Mathlib.RingTheory.AdicCompletion.Completeness
import Mathlib.RingTheory.AdicCompletion.Functoriality
import Mathlib.RingTheory.AdicCompletion.Topology
import TauCeti.Data.Finsupp.Weight

/-!
# Evaluating a multivariate power series at arguments from an adic ideal

Let `S` carry the `I`-adic topology for an ideal `I`, and let `f` be a multivariate power series
evaluated at a family `a : σ → S` through a continuous coefficient map `φ`. This file bounds the
value `eval₂ φ a f` by a power of `I`, in the three forms the estimate is used in: the value is
confined to `I ^ k` as soon as the arguments are and `φ` sends the constant term there, and the
confinement improves when its coefficient images vanish in low total degree or when `φ` sends every
coefficient into a power of `I`.

Three further results serve the same arguments from either side. Over finitely many variables a
pointwise topologically nilpotent family admits evaluation; arguments drawn from `I` satisfy
`MvPowerSeries.HasEval` in the first place, so that the value is defined at all; and the value is
congruent to the image of the constant term modulo `I`.

They are proved differently. `hasEval_of_finite_of_isTopologicallyNilpotent` does not use the
estimates above at all: over
finitely many variables the decay condition at infinity is vacuous, so topological nilpotence
of each argument is the whole content. `hasEval_of_mem` is its corollary, obtained by supplying
that nilpotence from membership in `I` through `IsAdic.isTopologicallyNilpotent_of_mem`.
`eval₂_sub_constantCoeff_mem` is the one that reduces to them — subtracting the constant term
kills the constant monomial and every surviving monomial carries an argument, so the difference
is the `k = 1` case of `eval₂_mem_pow` applied to `f - C (constantCoeff f)`.

The three bounds have the same one-line mechanism. `MvPowerSeries.hasSum_eval₂` writes the value
as the sum of its monomial values `φ (coeff d f) * ∏ s, a s ^ d s`; each such monomial is checked
to lie in the relevant power of `I`; and the sum of a family inside `I ^ n` stays inside `I ^ n`
because `I ^ n` is closed (`IsAdic.isClosed_pow`) and `tsum_mem` applies. The three statements
differ only in which power the monomial estimate produces.

Three hypotheses of the source turn out to be unnecessary. Nothing asks for `I` to be maximal or
for `S` to be local, only that the topology be `I`-adic, so the results are stated for an
arbitrary ideal; the coefficient map is an arbitrary continuous `φ : R →+* S` rather than the
identity, since `MvPowerSeries.hasSum_eval₂` is already stated at that generality; and the index
type need not be finite, because the summation argument uses only the `Tendsto a cofinite (𝓝 0)`
already carried by `HasEval`. Taking `I` to be `IsLocalRing.maximalIdeal S` and `φ` to be
`RingHom.id S` recovers the source statements.

Finally, evaluation reaches every element of a complete ring once the arguments generate `I` and
the coefficients reach every class modulo `I`. Through the discrete topology on the coefficients and
the `I`-adic topology on the target, this gives surjective ring homomorphisms from power series
rings onto `I`-adically complete rings, stated without any topology. This is how a complete local
ring containing a field becomes a quotient of a power series ring over a coefficient field.

Finiteness of `σ` survives in `hasEval_of_finite_of_isTopologicallyNilpotent`, where it is what
makes the decay condition of
`HasEval` vacuous; that is the one place the hypothesis does work, and `hasEval_of_mem` inherits
it from there.

## Main results

* `MvPowerSeries.eval₂_mem_pow` : arguments in `I ^ k`, and a constant term whose image under
  `φ` lies in `I ^ k`, confine the value to `I ^ k`.
* `MvPowerSeries.eval₂_mem_pow_mul` : if the coefficient images vanish below total degree `c`,
  evaluation at arguments in `I ^ j` takes values in `I ^ (c * j)`.
* `MvPowerSeries.eval₂_mem_pow_add_mul` : if moreover `φ` sends every coefficient into `I ^ k`,
  the value lies in `I ^ (k + c * j)`.
* `MvPowerSeries.hasEval_of_finite_of_isTopologicallyNilpotent` : finitely many topologically
  nilpotent arguments are an
  admissible evaluation point.
* `MvPowerSeries.hasEval_finTwo` : in particular, so is a pair of topologically nilpotent
  arguments.
* `MvPowerSeries.hasEval_of_mem` : a family of finitely many arguments drawn from `I` is an
  admissible evaluation point.
* `MvPowerSeries.eval₂_sub_constantCoeff_mem` : the value and the image of the constant term
  differ by an element of `I`.
* `MvPowerSeries.eval₂_zero` : evaluation sends `0` to `0`, with no hypothesis.
* `MvPowerSeries.isTopologicallyNilpotent_eval₂_iff` : the value is topologically nilpotent
  exactly when the image of the constant term is.
* `MvPowerSeries.eval₂_surjective` : evaluation at finitely many generators of `I` is surjective
  onto a complete ring when the coefficients reach every class modulo `I`.
* `MvPowerSeries.exists_surjective_ringHom_of_isAdicComplete` : the same as a statement about
  `I`-adically complete rings: a ring homomorphism `A →+* R` reaching every class modulo `I` and
  finitely many generators of `I` extend to a surjection `MvPowerSeries σ A →+* R`.

## Provenance

Adapted from Michael Stoll's `EllipticCurves` (`github.com/MichaelStollBayreuth/EllipticCurves`,
Apache-2.0) at commit `66889eada51a74c2f5dfb7fb5909b0b5a0a2d96e`, file
`EllipticCurves/WeierstrassFormalGroup/Eval.lean`, where the three bounds are
`ChabautyColeman.MvPSeries.eval_mem_maximalIdeal_pow`, `..._pow_mul` and `..._pow_add_mul`, and
`EllipticCurves/Mathlib/Chabauty/MvPSeries.lean`, where `hasEval_of_mem` carries the same name and
`eval₂_sub_constantCoeff_mem` is `ChabautyColeman.MvPSeries.eval_sub_constantCoeff_mem`. That
development evaluates through its own `ChabautyColeman.MvPSeries.eval`, which is by definition
`MvPowerSeries.eval₂ (RingHom.id _)`; the wrapper is dropped here and the statements are made
directly about Mathlib's `MvPowerSeries.eval₂`, as are the generalisations noted above. The
monomial estimates and the closed-ideal summation argument are the source's, as is the
`HasEval` construction. The congruence modulo `I` is not: the source proves it from the
`hasSum` expansion directly, whereas here it is the `k = 1` case of `eval₂_mem_pow` applied to
`f - C (constantCoeff f)`, which is shorter and needs no finiteness of `σ`.

The surjectivity results are not from that source. Their proof is the successive approximation
argument of Mathlib's `surjective_of_mk_map_comp_surjective`, applied to the power series ring,
which is complete for the ideal of its variables; compare the proof of the Cohen structure theorem
in [Stacks Project, Tag 032A](https://stacks.math.columbia.edu/tag/032A).
-/

public section

namespace MvPowerSeries

open scoped WithPiTopology

/-- Evaluation sends `0` to `0`, at any family and with no hypothesis: `0` is a polynomial. -/
@[simp]
theorem eval₂_zero {σ R S : Type*} [CommRing R] [UniformSpace R] [CommRing S] [UniformSpace S]
    (φ : R →+* S) (a : σ → S) : eval₂ φ a (0 : MvPowerSeries σ R) = 0 := by
  simpa using eval₂_coe φ a 0

section Eval

variable {σ : Type*}
variable {R : Type*} [CommRing R] [UniformSpace R] [IsTopologicalSemiring R] [IsUniformAddGroup R]
variable {S : Type*} [CommRing S] [UniformSpace S] [IsUniformAddGroup S] [CompleteSpace S]
    [T2Space S] [IsTopologicalRing S] [IsLinearTopology S S]
variable {φ : R →+* S} {a : σ → S} {I : Ideal S}

/-- **The value lies in `I ^ k` when the arguments do and `φ` sends the constant term there.**
Every monomial of positive degree already carries an argument, hence a factor from `I ^ k`; the
constant monomial is covered by the hypothesis on the image of the constant term. -/
theorem eval₂_mem_pow (hφ : Continuous φ) (ha : HasEval a) (hI : IsAdic I) {k : ℕ}
    (hmem : ∀ i, a i ∈ I ^ k) (f : MvPowerSeries σ R)
    (hcc : φ (constantCoeff f) ∈ I ^ k) :
    eval₂ φ a f ∈ I ^ k := by
  classical
  have htot := hasSum_eval₂ hφ ha f
  have hval : ∀ d : σ →₀ ℕ, φ (coeff d f) * d.prod (fun s e ↦ a s ^ e) ∈ I ^ k := by
    intro d
    rcases eq_or_ne d 0 with rfl | hd
    · simpa using hcc
    · obtain ⟨i, hi⟩ := Finsupp.support_nonempty_iff.mpr hd
      rw [Finsupp.prod, ← Finset.prod_erase_mul _ _ hi]
      exact Ideal.mul_mem_left _ _ (Ideal.mul_mem_left _ _
        (Ideal.pow_mem_of_mem _ (hmem i) _
          (Nat.pos_of_ne_zero (Finsupp.mem_support_iff.mp hi))))
  have hsum := tsum_mem (hI.isClosed_pow k) hval
  rwa [htot.tsum_eq] at hsum

/-- **Small coefficient images improve the bound.** If `φ` kills the coefficients below total degree
`c` and sends every coefficient of `f` into `I ^ k`, evaluation at arguments of `I ^ j` lies in
`I ^ (k + c * j)`. -/
theorem eval₂_mem_pow_add_mul (hφ : Continuous φ) (ha : HasEval a) (hI : IsAdic I) {j c k : ℕ}
    (hmem : ∀ i, a i ∈ I ^ j) (f : MvPowerSeries σ R)
    (hcoeff : ∀ d : σ →₀ ℕ, φ (coeff d f) ∈ I ^ k)
    (hlow : ∀ d : σ →₀ ℕ, d.degree < c → φ (coeff d f) = 0) :
    eval₂ φ a f ∈ I ^ (k + c * j) := by
  classical
  have htot := hasSum_eval₂ hφ ha f
  have hval : ∀ d : σ →₀ ℕ, φ (coeff d f) * d.prod (fun s e ↦ a s ^ e) ∈ I ^ (k + c * j) := by
    intro d
    rcases lt_or_ge d.degree c with hlt | hge
    · rw [hlow d hlt, zero_mul]
      exact zero_mem _
    · rw [pow_add]
      apply Ideal.mul_mem_mul (hcoeff d)
      apply Ideal.pow_le_pow_right (Nat.mul_le_mul_right j hge)
      have h : d.prod (fun s e ↦ a s ^ e) ∈ (I ^ j) ^ d.degree := by
        rw [← Finsupp.prod_pow_eq_pow_degree]
        exact Ideal.prod_mem_prod fun s _ ↦ Ideal.pow_mem_pow (hmem s) (d s)
      rwa [← pow_mul, Nat.mul_comm] at h
  have hsum := tsum_mem (hI.isClosed_pow (k + c * j)) hval
  rwa [htot.tsum_eq] at hsum

/-- **If the coefficient images vanish below total degree `c`, evaluation at arguments of
`I ^ j` takes values in `I ^ (c * j)`.** -/
theorem eval₂_mem_pow_mul (hφ : Continuous φ) (ha : HasEval a) (hI : IsAdic I) {j c : ℕ}
    (hmem : ∀ i, a i ∈ I ^ j) (f : MvPowerSeries σ R)
    (hcoeff : ∀ d : σ →₀ ℕ, d.degree < c → φ (coeff d f) = 0) :
    eval₂ φ a f ∈ I ^ (c * j) := by
  simpa using eval₂_mem_pow_add_mul (k := 0) hφ ha hI hmem f (fun _ ↦ by simp) hcoeff

/-- **The value differs from the image of the constant term by an element of `I`.** Equivalently,
for arguments drawn from `I` the value of `f` is congruent to the image of its constant term
modulo `I`. -/
theorem eval₂_sub_constantCoeff_mem (hφ : Continuous φ) (ha : HasEval a)
    (hI : IsAdic I) (hmem : ∀ i, a i ∈ I) (f : MvPowerSeries σ R) :
    eval₂ φ a f - φ (constantCoeff f) ∈ I := by
  have key := eval₂_mem_pow (k := 1) hφ ha hI (by simpa using hmem)
    (f - C (constantCoeff f)) (by simp)
  rw [pow_one] at key
  -- `eval₂ φ a` is not syntactically a bundled hom, so additivity is taken through `eval₂Hom`.
  have hsplit : eval₂ φ a (f - C (constantCoeff f)) = eval₂ φ a f - φ (constantCoeff f) := by
    rw [← coe_eval₂Hom hφ ha, map_sub, coe_eval₂Hom hφ ha, eval₂_C]
  rwa [hsplit] at key

/-- **A value is topologically nilpotent exactly when the image of the constant term is.** Every
monomial of positive degree carries a topologically nilpotent argument, so the value differs from
`φ (constantCoeff f)` by a topologically nilpotent element. In particular a series without
constant term takes topologically nilpotent values. -/
theorem isTopologicallyNilpotent_eval₂_iff (hφ : Continuous φ) (ha : HasEval a)
    (f : MvPowerSeries σ R) :
    IsTopologicallyNilpotent (eval₂ φ a f) ↔ IsTopologicallyNilpotent (φ (constantCoeff f)) := by
  -- The part of `f` without constant term is topologically nilpotent for the product topology,
  -- and evaluation is a continuous ring hom.
  have hg : IsTopologicallyNilpotent (eval₂ φ a (f - C (constantCoeff f))) := by
    rw [← coe_eval₂Hom hφ ha]
    exact IsTopologicallyNilpotent.map (by rw [coe_eval₂Hom]; exact continuous_eval₂ hφ ha)
      (WithPiTopology.isTopologicallyNilpotent_of_constantCoeff_zero (by simp))
  have hsplit : eval₂ φ a f = φ (constantCoeff f) + eval₂ φ a (f - C (constantCoeff f)) := by
    rw [← coe_eval₂Hom hφ ha, map_sub, coe_eval₂Hom hφ ha, eval₂_C, add_sub_cancel]
  simp_rw [← IsTopologicallyNilpotent.mem_topologicalNilradical_iff] at hg ⊢
  rw [hsplit, Ideal.add_mem_iff_left _ hg]

end Eval

section HasEval

-- Neither result below needs the uniform structure the evaluation bounds require: `HasEval` is
-- a condition on a topological ring alone.
variable {σ : Type*} {S : Type*} [CommRing S] [TopologicalSpace S] {a : σ → S} {I : Ideal S}

/-- **Finitely many topologically nilpotent arguments can be substituted into a power series.**
Over finitely many variables the decay condition `HasEval` asks for at infinity is vacuous, so
pointwise topological nilpotence is the whole of it. -/
theorem hasEval_of_finite_of_isTopologicallyNilpotent [Finite σ]
    (h : ∀ i, IsTopologicallyNilpotent (a i)) : HasEval a where
  hpow := h
  tendsto_zero := by simp [Filter.cofinite_eq_bot]

/-- **Two topologically nilpotent arguments can be substituted into a power series in two
variables.** -/
theorem hasEval_finTwo {x y : S} (hx : IsTopologicallyNilpotent x)
    (hy : IsTopologicallyNilpotent y) : HasEval ![x, y] :=
  hasEval_of_finite_of_isTopologicallyNilpotent fun s ↦ by fin_cases s <;> assumption

/-- **A family drawn from an adic ideal can be substituted into a power series.** For an index
type with finitely many variables, lying in `I` is the only condition the arguments need: it
already gives them the `HasEval` property that evaluation requires. -/
theorem hasEval_of_mem [Finite σ] (hI : IsAdic I) (hmem : ∀ i, a i ∈ I) : HasEval a :=
  hasEval_of_finite_of_isTopologicallyNilpotent fun s ↦ hI.isTopologicallyNilpotent_of_mem (hmem s)

end HasEval

section Surjective

variable {σ : Type*}
variable {R : Type*} [CommRing R] [UniformSpace R] [IsTopologicalSemiring R] [IsUniformAddGroup R]
variable {S : Type*} [CommRing S] [UniformSpace S] [IsUniformAddGroup S] [CompleteSpace S]
    [T2Space S] [IsTopologicalRing S] [IsLinearTopology S S]
variable {φ : R →+* S} {a : σ → S} {I : Ideal S}

/-- **Evaluation onto an adically complete ring.** Let `S` carry the `I`-adic topology, for which
it is complete and Hausdorff. If finitely many arguments generate `I` and every class of `S ⧸ I`
is the image of a coefficient, then every element of `S` is the value of a power series. -/
theorem eval₂_surjective [Finite σ] (hφ : Continuous φ) (hI : IsAdic I)
    (hspan : Ideal.span (Set.range a) = I)
    (hres : Function.Surjective ((Ideal.Quotient.mk I).comp φ)) :
    Function.Surjective (eval₂ φ a : MvPowerSeries σ R → S) := by
  have ha : HasEval a := hasEval_of_mem hI fun i ↦ hspan ▸ Ideal.subset_span ⟨i, rfl⟩
  -- The ideal of the variables, for which the power series ring is complete, maps onto `I`.
  have hmap : (Ideal.span (Set.range X)).map (eval₂Hom hφ ha) = I := by
    rw [Ideal.map_span, ← Set.range_comp, ← hspan]
    congr 2
    ext i
    simp [coe_eval₂Hom, eval₂_X]
  have : IsHausdorff ((Ideal.span (Set.range X)).map (eval₂Hom hφ ha)) S :=
    hmap ▸ hI.isHausdorff_iff.mpr ‹_›
  rw [← coe_eval₂Hom hφ ha]
  refine surjective_of_mk_map_comp_surjective (I := Ideal.span (Set.range X)) (eval₂Hom hφ ha) ?_
  rw [hmap]
  intro y
  obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective y
  obtain ⟨r, hr⟩ := hres (Ideal.Quotient.mk I y)
  exact ⟨C r, by simpa [coe_eval₂Hom, eval₂_C] using hr⟩

end Surjective

/-- **Power series rings map onto adically complete rings.** Let `R` be `I`-adically complete, let
`s : A →+* R` reach every class of `R ⧸ I`, and let a finite family `x` generate `I`. Then a
surjective ring homomorphism `MvPowerSeries σ A →+* R` restricts to `s` on constants and sends
each variable `X i` to `x i`. -/
theorem exists_surjective_ringHom_of_isAdicComplete {σ A R : Type*} [Finite σ] [CommRing A]
    [CommRing R] {I : Ideal R} [IsAdicComplete I R] (s : A →+* R)
    (hs : Function.Surjective ((Ideal.Quotient.mk I).comp s)) (x : σ → R)
    (hx : Ideal.span (Set.range x) = I) :
    ∃ φ : MvPowerSeries σ A →+* R, Function.Surjective φ ∧ φ.comp C = s ∧ ∀ i, φ (X i) = x i := by
  -- Evaluate with the `I`-adic topology on `R` and the discrete topology on `A`.
  let : WithIdeal R := ⟨I⟩
  let : UniformSpace A := ⊥
  -- The topology that `WithIdeal` puts on `R` is by definition `I.adicTopology`.
  have hI : IsAdic I := rfl
  obtain ⟨_, _⟩ := hI.isAdicComplete_iff.mp ‹_›
  have hs' : Continuous s := continuous_of_discreteTopology
  have ha : HasEval x := hasEval_of_mem hI fun i ↦ hx ▸ Ideal.subset_span ⟨i, rfl⟩
  refine ⟨eval₂Hom hs' ha, ?_, ?_, fun i ↦ ?_⟩
  · rw [coe_eval₂Hom]
    exact eval₂_surjective hs' hI hx hs
  · ext a
    simp [coe_eval₂Hom, eval₂_C]
  · simp [coe_eval₂Hom, eval₂_X]

end MvPowerSeries
