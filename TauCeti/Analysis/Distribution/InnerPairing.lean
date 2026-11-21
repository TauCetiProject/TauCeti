/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.LinearAlgebra.Complex.FiniteDimensional
public import TauCeti.Analysis.Distribution.ComplexPairing
import Mathlib.MeasureTheory.Function.L2Space
import TauCeti.Analysis.Distribution.Support
import TauCeti.Analysis.Distribution.TestFunction.Basic
import TauCeti.MeasureTheory.Function.LocallyIntegrable

/-!
# Pairing vector-valued distributions with vector-valued test functions

Let `V` be a finite-dimensional complex inner product space. A distribution `T : 𝓓'(Ω, V)` is
defined on *real* test functions. For a `V`-valued test function `g` it has the sesquilinear
pairing

`⟪g, T⟫ = ∫ ⟪g x, T x⟫ dx`

(`Distribution.innerPairing T g`), conjugate-linear in `g` and complex-linear in `T`. In an
orthonormal basis `(eᵢ)` of `V` it is `∑ᵢ ⟪eᵢ, T⟫ (conj ⟪eᵢ, g⟫)`, the sum of the complex-linear
extensions (`Distribution.complexPairing`) of the scalar components `⟪eᵢ, T⟫` applied to the
conjugated components of `g`. The definition uses the basis `stdOrthonormalBasis ℂ V`, but the
pairing does not depend on it: it is additive in `g` and on the test functions `φ • v`, with `φ`
real, it is

`⟪φ • v, T⟫ = ⟪v, T φ⟫`

(`Distribution.innerPairing_postcompCLM_toSpanSingleton`). Every `V`-valued test function is a
finite sum of such test functions, its components in a real basis of `V` times the basis vectors,
so for every real basis `(bᵢ)` of `V` the pairing is `∑ᵢ ⟪bᵢ, T (bᵢ* ∘ g)⟫`
(`Distribution.innerPairing_eq_sum_basis`). For `V = ℂ` it is the complex-linear extension of `T`
applied to `conj g` (`Distribution.innerPairing_eq_complexPairing`), and on the distribution of a
locally integrable function `f` it is `∫ ⟪g x, f x⟫ dx` (`Distribution.innerPairing_ofFun`). It
only depends on the values of `g` near the support of `T`
(`Distribution.innerPairing_eq_zero_of_disjoint`).

This is the pairing through which an operator on vector-valued test functions acts on
vector-valued distributions by transposition, for instance a pseudodifferential operator with a
matrix-valued symbol: `⟪w, Op(a) T (φ)⟫ = ⟪Op(a)* (φ • w), T⟫`. For a continuous real-linear map
`h` into `V`-valued test functions, the pairings `φ ↦ ⟪h φ, T⟫` form a distribution that depends
continuously on `T` (`Distribution.innerPairingCLM`).

## Main declarations

* `Distribution.innerPairing`: the pairing `⟪g, T⟫` of a `V`-valued distribution with a `V`-valued
  test function.
* `Distribution.innerPairingCLM`: for a continuous real-linear map `h` into `V`-valued test
  functions, the distribution `φ ↦ ⟪h φ, T⟫`, as a continuous real-linear function of `T`.
* `Distribution.innerPairing_postcompCLM_toSpanSingleton`: its value on `φ • v`, and
  `Distribution.innerPairing_eq_sum_basis`: its formula in an arbitrary real basis of `V`.
* `Distribution.innerPairing_eq_complexPairing`: for `V = ℂ` it is `T.complexPairing (conj g)`.
* `Distribution.innerPairing_ofFun`: on a locally integrable function it is an integral.
* `Distribution.innerPairing_eq_zero_of_disjoint`: it vanishes on test functions supported away
  from the support of `T`.
-/

public section

noncomputable section

open Complex Filter Set TopologicalSpace TestFunction MeasureTheory
open scoped Distributions Topology InnerProductSpace

namespace Distribution

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {Ω : Opens E} {n : ℕ∞}
  {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V]

/-- The real-linear functional `v ↦ ⟪v, e⟫`, the conjugate of the coordinate `⟪e, v⟫`. -/
private def conjInner (e : V) : V →L[ℝ] ℂ :=
  conjCLE.toContinuousLinearMap ∘L (innerSL ℂ e).restrictScalars ℝ

omit [FiniteDimensional ℂ V] in
private theorem conjInner_apply (e v : V) : conjInner e v = ⟪v, e⟫_ℂ := by
  simp [conjInner, inner_conj_symm]

/-- The component `⟪e, T⟫` of a `V`-valued distribution, a complex-valued distribution. -/
private abbrev innerComponent (e : V) (T : 𝓓'^{n}(Ω, V)) : 𝓓'^{n}(Ω, ℂ) :=
  mapCLM ((innerSL ℂ e).restrictScalars ℝ) T

omit [FiniteDimensional ℂ V] in
private theorem innerComponent_apply (e : V) (T : 𝓓'^{n}(Ω, V)) (φ : 𝓓^{n}(Ω, ℝ)) :
    innerComponent e T φ = ⟪e, T φ⟫_ℂ := by
  simp [innerComponent]

/-- The **pairing** `⟪g, T⟫ = ∫ ⟪g x, T x⟫ dx` of a distribution `T` with values in a
finite-dimensional complex inner product space `V` with a `V`-valued test function `g`. It is
defined as `∑ᵢ ⟪eᵢ, T⟫ (conj ⟪eᵢ, g⟫)` in the orthonormal basis `stdOrthonormalBasis ℂ V`, where
the scalar distributions `⟪eᵢ, T⟫` act on complex test functions by `Distribution.complexPairing`;
it does not depend on the basis, see `Distribution.innerPairing_postcompCLM_toSpanSingleton`. It is
conjugate-linear in `g` and complex-linear in `T`. -/
def innerPairing (T : 𝓓'^{n}(Ω, V)) (g : 𝓓^{n}(Ω, V)) : ℂ :=
  ∑ i, (innerComponent (stdOrthonormalBasis ℂ V i) T).complexPairing
    (postcompCLM (𝕜 := ℝ) (conjInner (stdOrthonormalBasis ℂ V i)) g)

theorem innerPairing_def (T : 𝓓'^{n}(Ω, V)) (g : 𝓓^{n}(Ω, V)) :
    T.innerPairing g = ∑ i, (mapCLM ((innerSL ℂ (stdOrthonormalBasis ℂ V i)).restrictScalars ℝ)
      T).complexPairing (postcompCLM (𝕜 := ℝ) (conjCLE.toContinuousLinearMap ∘L
        (innerSL ℂ (stdOrthonormalBasis ℂ V i)).restrictScalars ℝ) g) :=
  (rfl)

@[simp]
theorem innerPairing_add_right (T : 𝓓'^{n}(Ω, V)) (g h : 𝓓^{n}(Ω, V)) :
    T.innerPairing (g + h) = T.innerPairing g + T.innerPairing h := by
  simp only [innerPairing, map_add, Finset.sum_add_distrib]

/-- The pairing is conjugate-linear in the test function. -/
@[simp]
theorem innerPairing_smul_right (T : 𝓓'^{n}(Ω, V)) (c : ℂ) (g : 𝓓^{n}(Ω, V)) :
    T.innerPairing (c • g) = starRingEnd ℂ c * T.innerPairing g := by
  have h (e : V) : postcompCLM (𝕜 := ℝ) (conjInner e) (c • g) =
      starRingEnd ℂ c • postcompCLM (𝕜 := ℝ) (conjInner e) g := by
    ext x
    simp [conjInner_apply, inner_smul_left]
  simp only [innerPairing, h, map_smul, smul_eq_mul, Finset.mul_sum]

@[simp]
theorem innerPairing_zero_right (T : 𝓓'^{n}(Ω, V)) : T.innerPairing 0 = 0 := by
  simpa using T.innerPairing_smul_right 0 0

@[simp]
theorem innerPairing_neg_right (T : 𝓓'^{n}(Ω, V)) (g : 𝓓^{n}(Ω, V)) :
    T.innerPairing (-g) = -T.innerPairing g := by
  simpa using T.innerPairing_smul_right (-1) g

@[simp]
theorem innerPairing_sub_right (T : 𝓓'^{n}(Ω, V)) (g h : 𝓓^{n}(Ω, V)) :
    T.innerPairing (g - h) = T.innerPairing g - T.innerPairing h := by
  simp [sub_eq_add_neg]

theorem innerPairing_sum_right {ι : Type*} (T : 𝓓'^{n}(Ω, V)) (s : Finset ι)
    (g : ι → 𝓓^{n}(Ω, V)) : T.innerPairing (∑ i ∈ s, g i) = ∑ i ∈ s, T.innerPairing (g i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert i s hi ih => rw [Finset.sum_insert hi, innerPairing_add_right, ih, Finset.sum_insert hi]

@[simp]
theorem innerPairing_add_left (T S : 𝓓'^{n}(Ω, V)) (g : 𝓓^{n}(Ω, V)) :
    (T + S).innerPairing g = T.innerPairing g + S.innerPairing g := by
  simp only [innerPairing, map_add, complexPairing_add, Finset.sum_add_distrib]

/-- The pairing is complex-linear in the distribution. -/
@[simp]
theorem innerPairing_smul_left (c : ℂ) (T : 𝓓'^{n}(Ω, V)) (g : 𝓓^{n}(Ω, V)) :
    (c • T).innerPairing g = c * T.innerPairing g := by
  have h (e : V) : innerComponent e (c • T) = c • innerComponent e T := by
    ext φ
    simp
  simp only [innerPairing, h, complexPairing_smul, Finset.mul_sum]

@[simp]
theorem innerPairing_zero_left (g : 𝓓^{n}(Ω, V)) : (0 : 𝓓'^{n}(Ω, V)).innerPairing g = 0 := by
  simpa using innerPairing_smul_left 0 0 g

@[simp]
theorem innerPairing_neg_left (T : 𝓓'^{n}(Ω, V)) (g : 𝓓^{n}(Ω, V)) :
    (-T).innerPairing g = -T.innerPairing g := by
  simpa using innerPairing_smul_left (-1) T g

@[simp]
theorem innerPairing_sub_left (T S : 𝓓'^{n}(Ω, V)) (g : 𝓓^{n}(Ω, V)) :
    (T - S).innerPairing g = T.innerPairing g - S.innerPairing g := by
  simp [sub_eq_add_neg]

/-- The pairing is continuous in the test function. -/
theorem continuous_innerPairing (T : 𝓓'^{n}(Ω, V)) : Continuous T.innerPairing :=
  continuous_finsetSum _ fun _ _ ↦ (ContinuousLinearMap.continuous _).comp
    (postcompCLM (𝕜 := ℝ) _).continuous

/-- **The pairing on `φ • v`.** For a real test function `φ` and a vector `v`, the pairing of `T`
with the test function `x ↦ φ x • v` is `⟪v, T φ⟫`. Since every `V`-valued test function is a
finite sum of such test functions and of their multiples by `i`, this and the conjugate linearity
determine the pairing; in particular it does not depend on the basis used to define it. -/
@[simp]
theorem innerPairing_postcompCLM_toSpanSingleton (T : 𝓓'^{n}(Ω, V)) (v : V)
    (φ : 𝓓^{n}(Ω, ℝ)) :
    T.innerPairing (postcompCLM (𝕜 := ℝ) (ContinuousLinearMap.toSpanSingleton ℝ v) φ) =
      ⟪v, T φ⟫_ℂ := by
  have h (e : V) : postcompCLM (𝕜 := ℝ) (conjInner e)
      (postcompCLM (𝕜 := ℝ) (ContinuousLinearMap.toSpanSingleton ℝ v) φ) =
        ⟪v, e⟫_ℂ • postcompCLM (𝕜 := ℝ) ofRealCLM φ := by
    ext x
    simp [conjInner_apply, mul_comm]
  simp only [innerPairing, h, map_smul, complexPairing_postcompCLM_ofRealCLM, innerComponent_apply,
    smul_eq_mul]
  exact (stdOrthonormalBasis ℂ V).sum_inner_mul_inner v (T φ)

/-- **The pairing in a basis.** For every real basis `(bᵢ)` of `V`, the pairing of `T` with `g` is
`∑ᵢ ⟪bᵢ, T (bᵢ* ∘ g)⟫`, where `bᵢ* ∘ g` are the real components of `g`. In particular the pairing
does not depend on the orthonormal basis used to define it. -/
theorem innerPairing_eq_sum_basis {ι : Type*} [Fintype ι] (b : Module.Basis ι ℝ V)
    (T : 𝓓'^{n}(Ω, V)) (g : 𝓓^{n}(Ω, V)) :
    T.innerPairing g = ∑ i, ⟪b i, T (postcompCLM (b.coord i).toContinuousLinearMap g)⟫_ℂ := by
  conv_lhs => rw [← sum_postcompCLM_toSpanSingleton_coord b g]
  simp only [innerPairing_sum_right, innerPairing_postcompCLM_toSpanSingleton]

/-- For complex-valued distributions the pairing is the complex-linear extension of `T` applied to
the conjugate of the test function. -/
theorem innerPairing_eq_complexPairing (T : 𝓓'^{n}(Ω, ℂ)) (g : 𝓓^{n}(Ω, ℂ)) :
    T.innerPairing g =
      T.complexPairing (postcompCLM (𝕜 := ℝ) conjCLE.toContinuousLinearMap g) := by
  -- Split `g` into its real and imaginary parts, which are real multiples of `1`.
  have hsplit : g = postcompCLM (𝕜 := ℝ) (ContinuousLinearMap.toSpanSingleton ℝ 1)
      (postcompCLM (𝕜 := ℝ) reCLM g) +
        I • postcompCLM (𝕜 := ℝ) (ContinuousLinearMap.toSpanSingleton ℝ 1)
          (postcompCLM (𝕜 := ℝ) imCLM g) := by
    ext x
    simp only [add_apply, smul_apply, postcompCLM_apply, Function.comp_apply,
      ContinuousLinearMap.toSpanSingleton_apply, reCLM_apply, imCLM_apply, real_smul, mul_one,
      smul_eq_mul]
    exact (re_add_im _).symm.trans (by ring)
  have hconj : postcompCLM (𝕜 := ℝ) conjCLE.toContinuousLinearMap g =
      postcompCLM (𝕜 := ℝ) ofRealCLM (postcompCLM (𝕜 := ℝ) reCLM g) -
        I • postcompCLM (𝕜 := ℝ) ofRealCLM (postcompCLM (𝕜 := ℝ) imCLM g) := by
    ext x
    apply Complex.ext <;> simp
  rw [hconj, map_sub, map_smul, complexPairing_postcompCLM_ofRealCLM,
    complexPairing_postcompCLM_ofRealCLM]
  conv_lhs => rw [hsplit]
  simp only [innerPairing_add_right, innerPairing_smul_right,
    innerPairing_postcompCLM_toSpanSingleton, conj_I, smul_eq_mul]
  simp [RCLike.inner_apply, sub_eq_add_neg]

/-- **The distribution `φ ↦ ⟪h φ, T⟫`.** For a continuous real-linear map `h` from real to
`V`-valued test functions, the pairings `φ ↦ ⟪h φ, T⟫` of `T` form a complex-valued distribution,
which depends continuously and real-linearly on `T` (`Distribution.innerPairingCLM_apply`). This
is how operators defined on distributions by transposition are assembled. -/
def innerPairingCLM (h : 𝓓^{n}(Ω, ℝ) →L[ℝ] 𝓓^{n}(Ω, V)) : 𝓓'^{n}(Ω, V) →L[ℝ] 𝓓'^{n}(Ω, ℂ) :=
  ∑ i, (mapCLM ((innerSL ℂ (stdOrthonormalBasis ℂ V i)).restrictScalars ℝ) ∘L
      (postcompCLM (𝕜 := ℝ) (reCLM ∘L conjInner (stdOrthonormalBasis ℂ V i)) ∘L
        h).precompCompactConvergenceCLM V +
    mapCLM (ContinuousLinearMap.mul ℝ ℂ I) ∘L
      mapCLM ((innerSL ℂ (stdOrthonormalBasis ℂ V i)).restrictScalars ℝ) ∘L
        (postcompCLM (𝕜 := ℝ) (imCLM ∘L conjInner (stdOrthonormalBasis ℂ V i)) ∘L
          h).precompCompactConvergenceCLM V)

@[simp]
theorem innerPairingCLM_apply (h : 𝓓^{n}(Ω, ℝ) →L[ℝ] 𝓓^{n}(Ω, V)) (T : 𝓓'^{n}(Ω, V))
    (φ : 𝓓^{n}(Ω, ℝ)) : innerPairingCLM h T φ = T.innerPairing (h φ) := by
  simp only [innerPairingCLM, innerPairing, complexPairing_apply, sum_apply]
  -- The remaining evaluation is by unfolding: `precompCompactConvergenceCLM_apply` produces a sum
  -- in the type synonym `UniformConvergenceCLM`, whose evaluation the lemma `add_apply` does not
  -- match.
  rfl

/-- **The pairing with a function.** On the distribution of a function `f` locally integrable on
`Ω`, the pairing with a test function `g` is `∫ ⟪g x, f x⟫ dμ(x)`. -/
theorem innerPairing_ofFun [MeasurableSpace E] [OpensMeasurableSpace E] {f : E → V} {μ : Measure E}
    (hf : LocallyIntegrableOn f Ω μ) (g : 𝓓^{n}(Ω, V)) :
    (ofFun Ω f μ n).innerPairing g = ∫ x, ⟪g x, f x⟫_ℂ ∂μ := by
  have := FiniteDimensional.completeSpace ℂ V
  obtain ⟨b, hb⟩ : ∃ b, stdOrthonormalBasis ℂ V = b := ⟨_, rfl⟩
  -- Each component `⟪bᵢ, f⟫` is locally integrable and is the density of `⟪bᵢ, ofFun f⟫`.
  have hfi (i : Fin _) : LocallyIntegrableOn (fun x ↦ ⟪b i, f x⟫_ℂ) Ω μ :=
    ((innerSL ℂ (b i)).restrictScalars ℝ).locallyIntegrableOn_comp hf
  have hcomp (i : Fin _) (φ : 𝓓^{n}(Ω, ℝ)) :
      innerComponent (b i) (ofFun Ω f μ n) φ = ∫ x, φ x • ⟪b i, f x⟫_ℂ ∂μ := by
    rw [innerComponent_apply, ofFun_apply hf, ← integral_inner
      (LocallyIntegrableOn.integrable_smul_left_of_hasCompactSupport hf φ.continuous
        φ.hasCompactSupport φ.tsupport_subset)]
    simp only [← Complex.coe_smul, inner_smul_right, smul_eq_mul]
  -- The integrand of each term is integrable.
  have hint (i : Fin _) : Integrable (fun x ↦ postcompCLM (𝕜 := ℝ) (conjInner (b i)) g x *
      ⟪b i, f x⟫_ℂ) μ := by
    simpa [smul_eq_mul] using LocallyIntegrableOn.integrable_smul_left_of_hasCompactSupport (hfi i)
      (postcompCLM (𝕜 := ℝ) (conjInner (b i)) g).continuous
      (postcompCLM (𝕜 := ℝ) (conjInner (b i)) g).hasCompactSupport
      (postcompCLM (𝕜 := ℝ) (conjInner (b i)) g).tsupport_subset
  rw [innerPairing, hb, Finset.sum_congr rfl fun i _ ↦ complexPairing_eq_integral (hfi i)
    (fun φ _ ↦ hcomp i φ) (postcompCLM (𝕜 := ℝ) (conjInner (b i)) g).tsupport_subset,
    ← integral_finsetSum _ fun i _ ↦ hint i]
  refine integral_congr_ae (.of_forall fun x ↦ ?_)
  simp only [postcompCLM_apply, Function.comp_apply, conjInner_apply]
  exact b.sum_inner_mul_inner (g x) (f x)

/-- **The pairing only sees the support of `T`.** If the support of the test function `g` is
disjoint from the support of `T`, the pairing vanishes. -/
theorem innerPairing_eq_zero_of_disjoint (T : 𝓓'^{n}(Ω, V)) {g : 𝓓^{n}(Ω, V)}
    (h : Disjoint (tsupport g) (dsupport T)) : T.innerPairing g = 0 := by
  refine Finset.sum_eq_zero fun i _ ↦ ?_
  have hsupp : dsupport (innerComponent (stdOrthonormalBasis ℂ V i) T) ⊆ dsupport T :=
    dsupport_comp_subset (g := (innerSL ℂ (stdOrthonormalBasis ℂ V i)).restrictScalars ℝ) T
      (map_zero _)
  rw [complexPairing_eq_of_eventuallyEq _ (ψ := 0), map_zero]
  filter_upwards [(isClosed_tsupport g).isOpen_compl.mem_nhdsSet.2
    ((h.symm.subset_compl_right).trans' hsupp)] with x hx
  simp [postcompCLM_apply, image_eq_zero_of_notMem_tsupport hx]

end Distribution
