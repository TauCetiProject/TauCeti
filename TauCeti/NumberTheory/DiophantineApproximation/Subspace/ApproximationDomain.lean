/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Convex.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.LinearAlgebra.Dual.Defs
public import Mathlib.NumberTheory.NumberField.Completion.FinitePlace
public import TauCeti.NumberTheory.NumberField.CanonicalEmbedding.MixedImage
import TauCeti.LinearAlgebra.Dual.Lemmas
import TauCeti.NumberTheory.NumberField.FinitePlace.Basic

/-!
# Approximation domains

Let `K` be a number field and `S₀` a finite set of finite places of `K`. Fix linear forms
`L v i` on `ι → K`, real exponents `c v i` and a level `Q`. The **approximation domain**
`TauCeti.NumberField.approxDomain S₀ L c Q` is the set of `x : ι → K` with

* `v (L v i x) ≤ Q ^ c v i` for every `i`, at every infinite place `v` and every `v ∈ S₀`;
* `v (x j) ≤ 1` for every `j`, at every finite place `v ∉ S₀`.

Schmidt's proof of the Subspace Theorem applies the geometry of numbers to these domains. The two
kinds of conditions separate. The finite-place conditions cut out an `𝓞 K`-submodule
`TauCeti.NumberField.approxModule S₀ L c Q` of `ι → K`; the infinite-place conditions cut out a
body `TauCeti.NumberField.approxBody L c Q` in `ι → mixedSpace K`, the real space `(K ⊗ ℝ)ⁱ`; and
the domain is the set of points of the module whose coordinatewise mixed embedding lies in the body
(`TauCeti.NumberField.approxDomain_eq`).

The body is convex and symmetric (`TauCeti.NumberField.convex_approxBody`,
`TauCeti.NumberField.neg_mem_approxBody`), compact when the forms at each infinite place are
linearly independent (`TauCeti.NumberField.isCompact_approxBody`), and a neighbourhood of `0` for
`0 < Q` (`TauCeti.NumberField.approxBody_mem_nhds_zero`). It is balanced over every completion at
once: multiplying a point by an element of `mixedSpace K` of norm at most `1` at every infinite
place keeps it in the body (`TauCeti.NumberField.mul_mem_approxBody`). When the forms at the places
of `S₀` are linearly independent the module is finitely generated
(`TauCeti.NumberField.fg_approxModule`), and for `Q ≠ 0` it spans `ι → K`
(`TauCeti.NumberField.span_approxModule_eq_top`). Its mixed image is therefore discrete
(`TauCeti.NumberField.discreteTopology_mixedImage_approxModule`) and, for `Q ≠ 0`, a full lattice
in `ι → mixedSpace K` (`TauCeti.NumberField.isZLattice_mixedImage_approxModule`), so an
approximation domain is the set of points of a lattice in a convex body.

## Conventions

The forms and the exponents are indexed by the underlying absolute value of a place,
`L : AbsoluteValue K ℝ → ι → Module.Dual K (ι → K)`, so that one family serves the infinite places
and the places of `S₀`; their values at other absolute values are irrelevant. On the mixed space a
form `l` acts through its coefficients `l (Pi.basisFun K ι j)`, as
`z ↦ ∑ j, mixedEmbedding K (l (Pi.basisFun K ι j)) * z j`, and at an infinite place `w` the body
reads only the `w`-component through `normAtPlace w`. No statement needs `DecidableEq ι`.

The module is defined with `|Q|` in place of `Q`, so that it is a submodule for every real `Q`.
Real powers of a negative base are not meaningful bounds, and
`TauCeti.NumberField.approxDomain_eq` is stated for `0 ≤ Q`, where `|Q| = Q`.

Every infinite place carries a condition: a domain without a condition at some infinite place is
unbounded there.

## References

* E. Bombieri and W. Gubler, *Heights in Diophantine Geometry*, Cambridge University Press (2006),
  7.5.6 and Lemma 7.5.7.
* The definitions and the structure results follow Ralf Stephan's
  `DiophantineApproximation/ApproximationDomain.lean` and
  `DiophantineApproximation/FinitePlaceValues.lean` in `rwst/Subspace-Theorems`, snapshot
  `c26d909dc48cf7fe` (Apache 2.0).
-/

public section

noncomputable section

open Module NumberField NumberField.mixedEmbedding NumberField.InfinitePlace

namespace TauCeti.NumberField

variable {K : Type*} [Field K] {ι : Type*}

/-- **The approximation domain of level `Q`** (Bombieri–Gubler 7.5.6): the points `x` of `Kⁱ`
with `v (L v i x) ≤ Q ^ c v i` at every infinite place and every place of `S₀`, and with
`v (x j) ≤ 1` at every finite place outside `S₀`. -/
def approxDomain [NumberField K] (S₀ : Finset (FinitePlace K))
    (L : AbsoluteValue K ℝ → ι → Dual K (ι → K)) (c : AbsoluteValue K ℝ → ι → ℝ) (Q : ℝ) :
    Set (ι → K) :=
  {x | (∀ (v : InfinitePlace K) (i : ι), v (L v.1 i x) ≤ Q ^ c v.1 i) ∧
    (∀ v ∈ S₀, ∀ i : ι, v (L v.1 i x) ≤ Q ^ c v.1 i) ∧
    ∀ v : FinitePlace K, v ∉ S₀ → ∀ j : ι, v (x j) ≤ 1}

/-- Membership in an approximation domain, unfolded. -/
@[simp]
theorem mem_approxDomain [NumberField K] {S₀ : Finset (FinitePlace K)}
    {L : AbsoluteValue K ℝ → ι → Dual K (ι → K)} {c : AbsoluteValue K ℝ → ι → ℝ} {Q : ℝ}
    {x : ι → K} :
    x ∈ approxDomain S₀ L c Q ↔
      (∀ (v : InfinitePlace K) (i : ι), v (L v.1 i x) ≤ Q ^ c v.1 i) ∧
      (∀ v ∈ S₀, ∀ i : ι, v (L v.1 i x) ≤ Q ^ c v.1 i) ∧
      ∀ v : FinitePlace K, v ∉ S₀ → ∀ j : ι, v (x j) ≤ 1 := by
  rw [approxDomain, Set.mem_ofPred_eq]

/-- **The finite part of an approximation domain**: the conditions `v (L v i x) ≤ |Q| ^ c v i` at
the places of `S₀` and integrality at the other finite places, an `𝓞 K`-submodule of `Kⁱ`. It is
stated with `|Q|` so that it is a submodule for every real `Q`. -/
def approxModule [NumberField K] (S₀ : Finset (FinitePlace K))
    (L : AbsoluteValue K ℝ → ι → Dual K (ι → K)) (c : AbsoluteValue K ℝ → ι → ℝ) (Q : ℝ) :
    Submodule (𝓞 K) (ι → K) where
  carrier := {x | (∀ v ∈ S₀, ∀ i : ι, v (L v.1 i x) ≤ |Q| ^ c v.1 i) ∧
    ∀ v : FinitePlace K, v ∉ S₀ → ∀ j : ι, v (x j) ≤ 1}
  add_mem' := by
    rintro x y ⟨hx, hx'⟩ ⟨hy, hy'⟩
    refine ⟨fun v hv i ↦ ?_, fun v hv j ↦ ?_⟩
    · rw [map_add]
      exact (v.add_le _ _).trans (max_le (hx v hv i) (hy v hv i))
    · exact (v.add_le _ _).trans (max_le (hx' v hv j) (hy' v hv j))
  zero_mem' := ⟨fun v _ i ↦ by simpa using Real.rpow_nonneg (abs_nonneg Q) _, by simp⟩
  smul_mem' := by
    rintro a x ⟨hx, hx'⟩
    refine ⟨fun v hv i ↦ ?_, fun v hv j ↦ ?_⟩
    · rw [LinearMap.map_smul_of_tower, Algebra.smul_def, map_mul]
      exact (mul_le_of_le_one_left (apply_nonneg _ _) (v.apply_le_one a)).trans (hx v hv i)
    · rw [Pi.smul_apply, Algebra.smul_def, map_mul]
      exact (mul_le_of_le_one_left (apply_nonneg _ _) (v.apply_le_one a)).trans (hx' v hv j)

/-- Membership in the finite part of an approximation domain, unfolded. -/
@[simp]
theorem mem_approxModule [NumberField K] {S₀ : Finset (FinitePlace K)}
    {L : AbsoluteValue K ℝ → ι → Dual K (ι → K)} {c : AbsoluteValue K ℝ → ι → ℝ} {Q : ℝ}
    {x : ι → K} :
    x ∈ approxModule S₀ L c Q ↔ (∀ v ∈ S₀, ∀ i : ι, v (L v.1 i x) ≤ |Q| ^ c v.1 i) ∧
      ∀ v : FinitePlace K, v ∉ S₀ → ∀ j : ι, v (x j) ≤ 1 :=
  Iff.rfl

variable [Fintype ι]

/-- **The infinite part of an approximation domain**: the body in `ι → mixedSpace K` cut out at
every infinite place `w` by the conditions `‖L w i z‖_w ≤ Q ^ c w i`, where a form acts on the
mixed space through its coefficients and `normAtPlace w` reads the `w`-component. -/
def approxBody (L : AbsoluteValue K ℝ → ι → Dual K (ι → K)) (c : AbsoluteValue K ℝ → ι → ℝ)
    (Q : ℝ) : Set (ι → mixedSpace K) :=
  {z | ∀ (w : InfinitePlace K) (i : ι),
    normAtPlace w (∑ j, mixedEmbedding K (L w.1 i (Pi.basisFun K ι j)) * z j) ≤ Q ^ c w.1 i}

/-- Membership in the infinite part of an approximation domain, unfolded. -/
@[simp]
theorem mem_approxBody {L : AbsoluteValue K ℝ → ι → Dual K (ι → K)}
    {c : AbsoluteValue K ℝ → ι → ℝ} {Q : ℝ} {z : ι → mixedSpace K} :
    z ∈ approxBody L c Q ↔ ∀ (w : InfinitePlace K) (i : ι),
      normAtPlace w (∑ j, mixedEmbedding K (L w.1 i (Pi.basisFun K ι j)) * z j) ≤ Q ^ c w.1 i := by
  rw [approxBody, Set.mem_ofPred_eq]

/-- The coordinatewise mixed embedding of a point `x` of `Kⁱ` lies in the infinite part of an
approximation domain exactly when `w (L w i x) ≤ Q ^ c w i` at every infinite place `w`. -/
theorem mixedEmbedding_mem_approxBody_iff {L : AbsoluteValue K ℝ → ι → Dual K (ι → K)}
    {c : AbsoluteValue K ℝ → ι → ℝ} {Q : ℝ} {x : ι → K} :
    (fun j ↦ mixedEmbedding K (x j)) ∈ approxBody L c Q ↔
      ∀ (w : InfinitePlace K) (i : ι), w (L w.1 i x) ≤ Q ^ c w.1 i := by
  simp only [mem_approxBody, sum_mixedEmbedding_mul_mixedEmbedding, normAtPlace_apply]

/-- **An approximation domain is the set of points of a module whose mixed embedding lies in a
body**: `x` lies in it exactly when it lies in the finite part and its coordinatewise mixed
embedding lies in the infinite part. -/
theorem approxDomain_eq [NumberField K] (S₀ : Finset (FinitePlace K))
    (L : AbsoluteValue K ℝ → ι → Dual K (ι → K)) (c : AbsoluteValue K ℝ → ι → ℝ) {Q : ℝ}
    (hQ : 0 ≤ Q) :
    approxDomain S₀ L c Q =
      {x | x ∈ approxModule S₀ L c Q ∧ (fun j ↦ mixedEmbedding K (x j)) ∈ approxBody L c Q} := by
  ext x
  simp only [mem_approxDomain, mem_approxModule, mixedEmbedding_mem_approxBody_iff,
    Set.mem_ofPred_eq, abs_of_nonneg hQ]
  tauto

omit [Fintype ι] in
/-- At a place of `S₀` where the forms are linearly independent, the coordinates of the points of
the finite part of an approximation domain are bounded. -/
private theorem exists_forall_mem_approxModule_apply_le [Finite ι] [NumberField K]
    {S₀ : Finset (FinitePlace K)} {L : AbsoluteValue K ℝ → ι → Dual K (ι → K)}
    {c : AbsoluteValue K ℝ → ι → ℝ} {Q : ℝ} {v : FinitePlace K} (hv : v ∈ S₀)
    (hL : LinearIndependent K (L v.1)) :
    ∃ R : ℝ, 0 ≤ R ∧ ∀ x ∈ approxModule S₀ L c Q, ∀ j, v (x j) ≤ R := by
  have : Fintype ι := Fintype.ofFinite ι
  obtain ⟨a, ha⟩ := hL.exists_sum_smul_eq_proj
  refine ⟨∑ j, ∑ i, v (a j i) * |Q| ^ c v.1 i, by positivity, fun x hx j ↦ ?_⟩
  have hxj : x j = ∑ i, a j i * L v.1 i x := by
    simpa using (LinearMap.congr_fun (ha j) x).symm
  rw [hxj]
  refine (AbsoluteValue.sum_le _ _ _).trans <| le_trans ?_ <| Finset.single_le_sum
    (f := fun j ↦ ∑ i, v (a j i) * |Q| ^ c v.1 i) (fun _ _ ↦ by positivity) (Finset.mem_univ j)
  refine Finset.sum_le_sum fun i _ ↦ ?_
  rw [map_mul]
  exact mul_le_mul_of_nonneg_left ((mem_approxModule.1 hx).1 v hv i) (apply_nonneg _ _)

/-- The body of an approximation domain is convex. -/
theorem convex_approxBody (L : AbsoluteValue K ℝ → ι → Dual K (ι → K))
    (c : AbsoluteValue K ℝ → ι → ℝ) (Q : ℝ) : Convex ℝ (approxBody L c Q) := by
  intro x hx y hy a b ha hb hab
  rw [mem_approxBody] at hx hy ⊢
  intro w i
  have hxy : ∑ j, mixedEmbedding K (L w.1 i (Pi.basisFun K ι j)) * (a • x + b • y) j =
      a • ∑ j, mixedEmbedding K (L w.1 i (Pi.basisFun K ι j)) * x j +
        b • ∑ j, mixedEmbedding K (L w.1 i (Pi.basisFun K ι j)) * y j := by
    simp only [Pi.add_apply, Pi.smul_apply, mul_add, mul_smul_comm, Finset.smul_sum,
      Finset.sum_add_distrib]
  rw [hxy]
  refine (normAtPlace_add_le _ _ _).trans ?_
  rw [normAtPlace_smul, normAtPlace_smul, abs_of_nonneg ha, abs_of_nonneg hb]
  calc _ ≤ a * Q ^ c w.1 i + b * Q ^ c w.1 i := by gcongr <;> [exact hx w i; exact hy w i]
    _ = Q ^ c w.1 i := by rw [← add_mul, hab, one_mul]

/-- The body of an approximation domain is symmetric. -/
theorem neg_mem_approxBody {L : AbsoluteValue K ℝ → ι → Dual K (ι → K)}
    {c : AbsoluteValue K ℝ → ι → ℝ} {Q : ℝ} {z : ι → mixedSpace K} (hz : z ∈ approxBody L c Q) :
    -z ∈ approxBody L c Q := by
  rw [mem_approxBody] at hz ⊢
  intro w i
  simpa [Finset.sum_neg_distrib, normAtPlace_neg] using hz w i

/-- **The body is balanced over every completion at once**: multiplying a point of the body by an
element of the mixed space whose norm at every infinite place is at most `1` keeps it in the body.
For instance, the image of `ω • x` lies in the body with that of `x` whenever every conjugate of
`ω ∈ K` has absolute value at most `1`. -/
theorem mul_mem_approxBody {L : AbsoluteValue K ℝ → ι → Dual K (ι → K)}
    {c : AbsoluteValue K ℝ → ι → ℝ} {Q : ℝ} {z : ι → mixedSpace K} (hz : z ∈ approxBody L c Q)
    {a : mixedSpace K} (ha : ∀ w, normAtPlace w a ≤ 1) :
    (fun j ↦ a * z j) ∈ approxBody L c Q := by
  rw [mem_approxBody] at hz ⊢
  intro w i
  have : ∑ j, mixedEmbedding K (L w.1 i (Pi.basisFun K ι j)) * (a * z j) =
      a * ∑ j, mixedEmbedding K (L w.1 i (Pi.basisFun K ι j)) * z j := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun j _ ↦ by ring
  rw [this, map_mul]
  exact (mul_le_of_le_one_left (normAtPlace_nonneg _ _) (ha w)).trans (hz w i)

/-- The body of an approximation domain is closed. -/
theorem isClosed_approxBody (L : AbsoluteValue K ℝ → ι → Dual K (ι → K))
    (c : AbsoluteValue K ℝ → ι → ℝ) (Q : ℝ) : IsClosed (approxBody L c Q) := by
  have : approxBody L c Q = ⋂ (w : InfinitePlace K) (i : ι),
      {z | normAtPlace w (∑ j, mixedEmbedding K (L w.1 i (Pi.basisFun K ι j)) * z j) ≤
        Q ^ c w.1 i} := by
    ext z
    simp [mem_approxBody]
  rw [this]
  exact isClosed_iInter fun w ↦ isClosed_iInter fun i ↦ isClosed_le (by fun_prop)
    continuous_const

/-- The body of an approximation domain of positive level is a neighbourhood of `0`. -/
theorem approxBody_mem_nhds_zero [NumberField K] (L : AbsoluteValue K ℝ → ι → Dual K (ι → K))
    (c : AbsoluteValue K ℝ → ι → ℝ) {Q : ℝ} (hQ : 0 < Q) : approxBody L c Q ∈ nhds 0 := by
  have h (w : InfinitePlace K) (i : ι) : ∀ᶠ z in nhds (0 : ι → mixedSpace K),
      normAtPlace w (∑ j, mixedEmbedding K (L w.1 i (Pi.basisFun K ι j)) * z j) ≤ Q ^ c w.1 i := by
    have hcont : Continuous fun z : ι → mixedSpace K ↦
        normAtPlace w (∑ j, mixedEmbedding K (L w.1 i (Pi.basisFun K ι j)) * z j) := by
      fun_prop
    refine hcont.continuousAt.eventually (ge_mem_nhds ?_)
    simpa using Real.rpow_pos_of_pos hQ _
  filter_upwards [Filter.eventually_all.2 fun w ↦ Filter.eventually_all.2 (h w)] with z hz
  exact mem_approxBody.2 hz

/-- **The body of an approximation domain is bounded** when the forms are linearly independent at
every infinite place. -/
theorem isBounded_approxBody [NumberField K] {L : AbsoluteValue K ℝ → ι → Dual K (ι → K)}
    (hL : ∀ w : InfinitePlace K, LinearIndependent K (L w.1)) (c : AbsoluteValue K ℝ → ι → ℝ)
    (Q : ℝ) : Bornology.IsBounded (approxBody L c Q) := by
  classical
  -- At each infinite place `w` every coordinate form is a combination `a w j` of the forms at `w`.
  choose a ha using fun w : InfinitePlace K ↦ (hL w).exists_sum_smul_eq_proj
  set R : ℝ := ∑ w : InfinitePlace K, ∑ j, ∑ i, w (a w j i) * |Q ^ c w.1 i|
  have hR (w : InfinitePlace K) (j : ι) : ∑ i, w (a w j i) * |Q ^ c w.1 i| ≤ R :=
    (Finset.single_le_sum (f := fun j ↦ ∑ i, w (a w j i) * |Q ^ c w.1 i|)
      (fun _ _ ↦ by positivity) (Finset.mem_univ j)).trans <|
      Finset.single_le_sum (f := fun w : InfinitePlace K ↦ ∑ j, ∑ i, w (a w j i) * |Q ^ c w.1 i|)
        (fun _ _ ↦ by positivity) (Finset.mem_univ w)
  refine (Metric.isBounded_closedBall (x := (0 : ι → mixedSpace K)) (r := R)).subset
    fun z hz ↦ ?_
  rw [mem_approxBody] at hz
  rw [mem_closedBall_zero_iff, pi_norm_le_iff_of_nonneg (by positivity)]
  intro j
  rw [norm_eq_sup'_normAtPlace]
  refine Finset.sup'_le _ _ fun w _ ↦ le_trans ?_ (hR w j)
  have hzj := sum_mixedEmbedding_sum_smul_mul (a w j) (L w.1) z
  rw [ha w j, sum_mixedEmbedding_proj_mul] at hzj
  rw [hzj]
  refine (Finset.le_sum_of_subadditive (normAtPlace w) (map_zero _).le (normAtPlace_add_le w)
    _ _).trans (Finset.sum_le_sum fun i _ ↦ ?_)
  rw [map_mul, normAtPlace_apply]
  exact mul_le_mul_of_nonneg_left ((hz w i).trans (le_abs_self _)) (apply_nonneg _ _)

/-- **The body of an approximation domain is compact** when the forms are linearly independent at
every infinite place. -/
theorem isCompact_approxBody [NumberField K] {L : AbsoluteValue K ℝ → ι → Dual K (ι → K)}
    (hL : ∀ w : InfinitePlace K, LinearIndependent K (L w.1)) (c : AbsoluteValue K ℝ → ι → ℝ)
    (Q : ℝ) : IsCompact (approxBody L c Q) := by
  -- The metric on the mixed space is built with decidability of `IsReal`.
  classical
  exact Metric.isCompact_of_isClosed_isBounded (isClosed_approxBody L c Q)
    (isBounded_approxBody hL c Q)

omit [Fintype ι]

/-- **The finite part of an approximation domain is finitely generated** when the forms are
linearly independent at the places of `S₀`. -/
theorem fg_approxModule [Finite ι] [NumberField K] {S₀ : Finset (FinitePlace K)}
    {L : AbsoluteValue K ℝ → ι → Dual K (ι → K)} (hL : ∀ v ∈ S₀, LinearIndependent K (L v.1))
    (c : AbsoluteValue K ℝ → ι → ℝ) (Q : ℝ) : (approxModule S₀ L c Q).FG := by
  have : Fintype ι := Fintype.ofFinite ι
  -- At each place of `S₀` the coordinates of a point of the module are at most `R v`.
  have hR (v : FinitePlace K) : ∃ R : ℝ, 0 ≤ R ∧ (v ∈ S₀ → ∀ x ∈ approxModule S₀ L c Q,
      ∀ j, v (x j) ≤ R) := by
    by_cases hv : v ∈ S₀
    · obtain ⟨R, hR0, hR⟩ := exists_forall_mem_approxModule_apply_le (c := c) (Q := Q) hv (hL v hv)
      exact ⟨R, hR0, fun _ ↦ hR⟩
    · exact ⟨0, le_rfl, fun h ↦ (hv h).elim⟩
  choose R hR0 hR using hR
  -- A nonzero algebraic integer `d` clears these denominators.
  obtain ⟨d, hd0, hd⟩ := FinitePlace.exists_ne_zero_forall_mul_apply_le S₀ fun v _ ↦ hR0 v
  have hdK : (d : K) ≠ 0 := RingOfIntegers.coe_ne_zero_iff.2 hd0
  have hle : approxModule S₀ L c Q ≤
      Submodule.span (𝓞 K) (Set.range fun j ↦ (d : K)⁻¹ • Pi.basisFun K ι j) := by
    intro x hx
    have hint (j : ι) : ∃ z : 𝓞 K, algebraMap (𝓞 K) K z = d * x j := by
      refine IsDedekindDomain.HeightOneSpectrum.mem_integers_of_valuation_le_one K _ fun P ↦ ?_
      rw [← FinitePlace.mk_apply_le_one_iff, map_mul]
      set v := FinitePlace.mk P
      by_cases hv : v ∈ S₀
      · exact (mul_le_mul_of_nonneg_left (hR v hv x hx j) (apply_nonneg _ _)).trans (hd v hv)
      · exact (mul_le_mul (v.apply_le_one d) ((mem_approxModule.1 hx).2 v hv j)
          (apply_nonneg _ _) zero_le_one).trans_eq (one_mul 1)
    choose z hz using hint
    have hsum : x = ∑ j, z j • ((d : K)⁻¹ • Pi.basisFun K ι j) := by
      ext k
      classical
      have hk : x k = (d : K)⁻¹ * (d * x k) := (inv_mul_cancel_left₀ hdK (x k)).symm
      simpa [Algebra.smul_def, hz, Pi.single_apply, mul_comm] using hk
    rw [hsum]
    exact Submodule.sum_mem _ fun j _ ↦ Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩)
  have : IsNoetherian (𝓞 K)
      (Submodule.span (𝓞 K) (Set.range fun j ↦ (d : K)⁻¹ • Pi.basisFun K ι j)) :=
    isNoetherian_of_fg_of_noetherian _ (Submodule.fg_span (Set.finite_range _))
  exact Submodule.FG.of_le_of_isNoetherian hle

/-- **The finite part of an approximation domain of nonzero level spans `Kⁱ` over `K`**, for every
`S₀`, `L` and `c`. -/
theorem span_approxModule_eq_top [Finite ι] [NumberField K] (S₀ : Finset (FinitePlace K))
    (L : AbsoluteValue K ℝ → ι → Dual K (ι → K)) (c : AbsoluteValue K ℝ → ι → ℝ) {Q : ℝ}
    (hQ : Q ≠ 0) : Submodule.span K (approxModule S₀ L c Q : Set (ι → K)) = ⊤ := by
  have : Fintype ι := Fintype.ofFinite ι
  classical
  set S : FinitePlace K → ℝ := fun v ↦ ∑ i, ∑ j, v (L v.1 i (Pi.basisFun K ι j)) / |Q| ^ c v.1 i
  have hQc (v : FinitePlace K) (i : ι) : 0 < |Q| ^ c v.1 i :=
    Real.rpow_pos_of_pos (abs_pos.2 hQ) _
  have hS (v : FinitePlace K) (i j : ι) :
      v (L v.1 i (Pi.basisFun K ι j)) ≤ S v * |Q| ^ c v.1 i := by
    rw [← div_le_iff₀ (hQc v i)]
    refine (Finset.single_le_sum (f := fun j ↦ v (L v.1 i (Pi.basisFun K ι j)) / |Q| ^ c v.1 i)
      (fun _ _ ↦ div_nonneg (apply_nonneg _ _) (hQc v i).le) (Finset.mem_univ j)).trans ?_
    exact Finset.single_le_sum
      (f := fun i ↦ ∑ j, v (L v.1 i (Pi.basisFun K ι j)) / |Q| ^ c v.1 i)
      (fun i _ ↦ Finset.sum_nonneg fun j _ ↦ div_nonneg (apply_nonneg _ _) (hQc v i).le)
      (Finset.mem_univ i)
  have hS0 (v : FinitePlace K) : 0 ≤ S v :=
    Finset.sum_nonneg fun i _ ↦ Finset.sum_nonneg fun j _ ↦
      div_nonneg (apply_nonneg _ _) (hQc v i).le
  obtain ⟨d, hd0, hd⟩ := FinitePlace.exists_ne_zero_forall_mul_apply_le S₀ fun v _ ↦ hS0 v
  have hdK : (d : K) ≠ 0 := RingOfIntegers.coe_ne_zero_iff.2 hd0
  have hmem (j : ι) : (d : K) • Pi.basisFun K ι j ∈ approxModule S₀ L c Q := by
    refine mem_approxModule.2 ⟨fun v hv i ↦ ?_, fun v hv k ↦ ?_⟩
    · rw [map_smul, smul_eq_mul, map_mul]
      calc v (d : K) * v (L v.1 i (Pi.basisFun K ι j))
          ≤ v (d : K) * (S v * |Q| ^ c v.1 i) :=
            mul_le_mul_of_nonneg_left (hS v i j) (apply_nonneg _ _)
        _ = v (d : K) * S v * |Q| ^ c v.1 i := (mul_assoc _ _ _).symm
        _ ≤ |Q| ^ c v.1 i := mul_le_of_le_one_left (hQc v i).le (hd v hv)
    · rw [Pi.smul_apply, smul_eq_mul, map_mul, Pi.basisFun_apply, Pi.single_apply]
      split_ifs <;> simp [v.apply_le_one d]
  rw [eq_top_iff, ← (Pi.basisFun K ι).span_eq, Submodule.span_le]
  rintro _ ⟨j, rfl⟩
  rw [SetLike.mem_coe, ← inv_smul_smul₀ hdK (Pi.basisFun K ι j)]
  exact Submodule.smul_mem _ _ (Submodule.subset_span (hmem j))

/-- When the forms at `S₀` are linearly independent, the mixed image of `approxModule S₀ L c Q` is
discrete in `ι → mixedSpace K`. -/
theorem discreteTopology_mixedImage_approxModule [Finite ι] [NumberField K]
    {S₀ : Finset (FinitePlace K)} {L : AbsoluteValue K ℝ → ι → Dual K (ι → K)}
    (hL : ∀ v ∈ S₀, LinearIndependent K (L v.1)) (c : AbsoluteValue K ℝ → ι → ℝ) (Q : ℝ) :
    DiscreteTopology (approxModule S₀ L c Q).mixedImage :=
  Submodule.discreteTopology_mixedImage_iff.mpr (fg_approxModule hL c Q)

open scoped Classical in
/-- When the forms at `S₀` are linearly independent and `Q ≠ 0`, the mixed image of
`approxModule S₀ L c Q` is a full `ℤ`-lattice in `ι → mixedSpace K`. -/
theorem isZLattice_mixedImage_approxModule [Fintype ι] [NumberField K]
    {S₀ : Finset (FinitePlace K)} {L : AbsoluteValue K ℝ → ι → Dual K (ι → K)}
    (hL : ∀ v ∈ S₀, LinearIndependent K (L v.1)) (c : AbsoluteValue K ℝ → ι → ℝ) {Q : ℝ}
    (hQ : Q ≠ 0) :
    haveI := discreteTopology_mixedImage_approxModule hL c Q
    IsZLattice ℝ (approxModule S₀ L c Q).mixedImage :=
  letI := discreteTopology_mixedImage_approxModule hL c Q
  Submodule.isZLattice_mixedImage (span_approxModule_eq_top S₀ L c hQ)

end TauCeti.NumberField
