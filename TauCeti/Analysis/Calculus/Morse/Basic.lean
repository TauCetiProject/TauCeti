/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.DiscreteSubset
public import TauCeti.Analysis.Calculus.Bilinear
public import TauCeti.Analysis.Calculus.SecondDerivative
public import TauCeti.Topology.Algebra.Module.BilinearForm
-- Private: the negation rules for `ContDiffAt` and for the Fréchet derivative are used only
-- inside the proof of `TauCeti.IsNondegenerateCriticalPoint.neg`.
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.FDeriv.Add

/-!
# Nondegenerate critical points

A critical point of a real-valued function `f` on a normed space is *nondegenerate* when the
second derivative `fderiv ℝ (fderiv ℝ f) x`, read as a continuous linear map from `E` to its
dual, is a linear homeomorphism. In finite dimensions this is the classical requirement that the
Hessian be a nondegenerate bilinear form; in infinite dimensions it is the standard strong
nondegeneracy condition of Morse theory on Banach and Hilbert spaces, and it is genuinely stronger
than injectivity of the Hessian. It is unrelated to the Palais--Smale condition, which is not a
condition at a critical point at all but a separate global compactness hypothesis, asking that
every sequence along which `f` is bounded and `fderiv ℝ f` tends to `0` have a convergent
subsequence.

Twice continuous differentiability at the point is part of `IsNondegenerateCriticalPoint`, and so
of `HasNondegenerateCriticalPointsOn` at each critical point: Mathlib totalizes `fderiv` by zero
where a function is not differentiable, so a predicate phrased on `fderiv ℝ f` alone would call a
function nondegenerate at a point where it is not even continuous. No statement below that
hypothesises `IsNondegenerateCriticalPoint` therefore needs a separate regularity hypothesis at
that point. Two statements do ask for more, because what they assume there is not nondegeneracy:
the finiteness statement needs continuity of `fderiv ℝ f` on the compact set, which is what closes
the critical locus, and the change-of-coordinates results need `ContDiffAt ℝ 2` of the chart (and,
for the two-way `isNondegenerateCriticalPoint_comp_iff`, of `f` as well, since there nondegeneracy
is assumed downstairs rather than upstairs).

`HasNondegenerateCriticalPointsOn f s` asks nothing at all of `f` away from its critical points in
`s`, so it is weaker than the textbook notion of a Morse function, which carries global regularity
on `s` as a standing hypothesis. The name `IsMorseOn` is deliberately left free for that stronger
notion; it belongs with the manifold-level material, where smoothness is standing anyway. The
results below are stated for the weak predicate because that is all their proofs use.

The point of the definition is that nondegenerate critical points are *isolated*, so a function
whose critical points in a set are all nondegenerate has a discrete critical locus there. On a
compact set on which `fderiv ℝ f` is moreover continuous, so that the critical locus is closed,
that discreteness leaves only finitely many critical points. That finiteness is what makes the
Morse chain complex of a compact manifold finitely generated, so it is the first structural input
of Morse homology. The isolation itself uses no criticality — an invertible second derivative
already makes the differential avoid any prescribed value nearby — so it is proved in the stated
generality as `TauCeti.eventually_fderiv_ne` in `TauCeti.Analysis.Calculus.SecondDerivative`, and
only its value-zero case is taken here.

Because the first-order term of the chain rule drops out at a critical point, the second
derivative there transforms as a bilinear form (`TauCeti.fderiv_fderiv_comp_apply_of_fderiv_eq_zero`
in `TauCeti.Analysis.Calculus.SecondDerivative`), and nondegeneracy is unchanged by a change of
coordinates; together with the fact that it depends only on the germ of `f`, this is what will let
the notion be read off in any chart.

## Main declarations

* `TauCeti.IsNondegenerateCriticalPoint`: `f` is twice continuously differentiable at the point,
  its differential vanishes there, and its second derivative is invertible as a map into the dual
  space.
* `TauCeti.HasNondegenerateCriticalPointsOn`: every critical point in a given set is nondegenerate.
* `TauCeti.IsNondegenerateCriticalPoint.separatingLeft`: the Hessian at a nondegenerate critical
  point is left-separating as a bilinear form.
* `TauCeti.isNondegenerateCriticalPoint_iff_separatingLeft`: in finite dimensions the converse
  holds too, so nondegeneracy is twice continuous differentiability together with the classical
  condition that the Hessian bilinear form have trivial radical.
* `TauCeti.IsNondegenerateCriticalPoint.congr_of_eventuallyEq`: nondegeneracy at a point depends
  only on the germ of the function there.
* `TauCeti.IsNondegenerateCriticalPoint.eventually_fderiv_ne_zero`: a nondegenerate critical point
  is isolated among critical points.
* `TauCeti.HasNondegenerateCriticalPointsOn.isDiscrete_setOfPred_fderiv_eq_zero`: a critical
  locus all of whose points are nondegenerate is discrete.
* `TauCeti.HasNondegenerateCriticalPointsOn.finite_setOfPred_fderiv_eq_zero`: such a critical
  locus is finite on a compact set on which `fderiv ℝ f` is continuous.
* `ContDiffAt.exists_norm_fderiv_le_mul_norm_sub` and
  `ContDiffAt.exists_abs_sub_le_mul_norm_sub_sq`: near a critical point the differential is
  bounded by a multiple of the distance to it, and the energy difference by a multiple of its
  square.
* `TauCeti.IsNondegenerateCriticalPoint.exists_mul_norm_sub_le_norm_fderiv` and
  `TauCeti.IsNondegenerateCriticalPoint.exists_mul_abs_sub_le_norm_fderiv_sq`: near a
  nondegenerate critical point the differential is bounded below by a multiple of the distance,
  and the Morse form of Łojasiewicz's inequality holds.
* `TauCeti.isNondegenerateCriticalPoint_comp_iff` and `TauCeti.IsNondegenerateCriticalPoint.comp`:
  nondegeneracy is invariant under a change of coordinates with invertible differential.
* `TauCeti.IsNondegenerateCriticalPoint.neg` and `TauCeti.isNondegenerateCriticalPoint_neg`:
  nondegeneracy is invariant under negating the function.
* `ContinuousLinearMap.isNondegenerateCriticalPoint_apply_self`: the local model. A
  continuous bilinear form `B` whose polarization `B.flip + B` is invertible makes `z ↦ B z z` a
  function with a nondegenerate critical point at the origin.
* `ContinuousLinearMap.isNondegenerateCriticalPoint_apply_self_of_flip_eq_self`: the
  symmetric case of the model, where the polarization is `2 • B`, so an invertible symmetric `B`
  suffices.

The second derivative used here is `fderiv ℝ (fderiv ℝ f) x`, which Mathlib also packages as
`bilinearIteratedFDerivTwo` and evaluates through `iteratedFDeriv_two_apply`; its symmetry at a
twice differentiable point is `ContDiffAt.isSymmSndFDerivAt`.

## References

* M. Audin, M. Damian, *Morse Theory and Floer Homology*, Springer Universitext, 2014, Chapter 1,
  for the finite-dimensional theory.
* R. S. Palais, *Morse theory on Hilbert manifolds*, Topology **2** (1963), 299--340, and
  M. Schwarz, *Morse Homology*, Birkhäuser, 1993, Chapter 1, for the nondegeneracy condition in
  Banach and Hilbert generality used here, namely invertibility of the second derivative as a map
  into the dual space.
* [Heegaard Floer homology roadmap](https://github.com/TauCetiProject/TauCetiRoadmap/blob/main/TauCetiRoadmap/HeegaardFloer/README.md),
  Lane M, "Morse homology".
-/

public section

open Filter Function Module Set Topology

namespace TauCeti

section Morse

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] {f : E → ℝ} {x : E}

/-- `f` has a **nondegenerate critical point** at `x` when it is twice continuously differentiable
at `x`, its differential vanishes at `x`, and its second derivative at `x`, viewed as a continuous
linear map from `E` to the dual space `E →L[ℝ] ℝ`, is a linear homeomorphism. The regularity is
part of the definition because `fderiv` is totalized by zero where `f` is not differentiable. -/
structure IsNondegenerateCriticalPoint (f : E → ℝ) (x : E) : Prop where
  /-- `f` is twice continuously differentiable at `x`. -/
  contDiffAt : ContDiffAt ℝ 2 f x
  /-- The differential of `f` vanishes at `x`. -/
  fderiv_eq_zero : fderiv ℝ f x = 0
  /-- The second derivative of `f` at `x` is invertible as a map into the dual space. -/
  isInvertible : (fderiv ℝ (fderiv ℝ f) x).IsInvertible

/-- `f` **has nondegenerate critical points on `s`** when every critical point of `f` lying in `s`
is nondegenerate; in particular `f` is twice continuously differentiable at each of them. No
regularity is asked for away from the critical points, so this is weaker than being a Morse
function on `s` in the textbook sense, which also demands regularity at the regular points. -/
def HasNondegenerateCriticalPointsOn (f : E → ℝ) (s : Set E) : Prop :=
  ∀ ⦃x⦄, x ∈ s → fderiv ℝ f x = 0 → IsNondegenerateCriticalPoint f x

/-- The introduction and elimination rule for `HasNondegenerateCriticalPointsOn`. It is
deliberately not a `simp` lemma: taking the unfolded form as the normal one would move the
predicate out of the shape `HasNondegenerateCriticalPointsOn.mono`,
`HasNondegenerateCriticalPointsOn.isDiscrete_setOfPred_fderiv_eq_zero` and
`HasNondegenerateCriticalPointsOn.finite_setOfPred_fderiv_eq_zero` are stated in, so a `simp` at a
hypothesis would strip its API off it. Mathlib leaves the analogous `mapsTo_iff_subset_preimage`
unannotated for the same reason. -/
theorem hasNondegenerateCriticalPointsOn_iff {s : Set E} :
    HasNondegenerateCriticalPointsOn f s ↔
      ∀ ⦃x⦄, x ∈ s → fderiv ℝ f x = 0 → IsNondegenerateCriticalPoint f x :=
  Iff.rfl

/-- Having nondegenerate critical points on `t` is inherited by every subset of `t`. -/
theorem HasNondegenerateCriticalPointsOn.mono {s t : Set E}
    (hM : HasNondegenerateCriticalPointsOn f t) (hst : s ⊆ t) :
    HasNondegenerateCriticalPointsOn f s :=
  fun _ hx ↦ hM (hst hx)

/-- At a nondegenerate critical point the Hessian is left-separating as a bilinear form: no
nonzero vector is annihilated by it. -/
theorem IsNondegenerateCriticalPoint.separatingLeft (h : IsNondegenerateCriticalPoint f x) :
    (fderiv ℝ (fderiv ℝ f) x).toBilinForm.SeparatingLeft :=
  (ContinuousLinearMap.separatingLeft_toBilinForm_iff_injective _).2 h.isInvertible.injective

/-- In finite dimensions, invertibility of the second derivative is the classical nondegeneracy of
the Hessian: the Hessian bilinear form is left-separating. -/
theorem isNondegenerateCriticalPoint_iff_separatingLeft [FiniteDimensional ℝ E] :
    IsNondegenerateCriticalPoint f x ↔
      ContDiffAt ℝ 2 f x ∧ fderiv ℝ f x = 0 ∧
        (fderiv ℝ (fderiv ℝ f) x).toBilinForm.SeparatingLeft := by
  refine ⟨fun h ↦ ⟨h.contDiffAt, h.fderiv_eq_zero, h.separatingLeft⟩,
    fun ⟨hd, h0, hnd⟩ ↦ ⟨hd, h0, ?_⟩⟩
  exact ContinuousLinearMap.isInvertible_of_injective
    ((ContinuousLinearMap.separatingLeft_toBilinForm_iff_injective _).1 hnd)

/-- Nondegeneracy at a point depends only on the germ of the function there. -/
theorem IsNondegenerateCriticalPoint.congr_of_eventuallyEq {g : E → ℝ}
    (h : IsNondegenerateCriticalPoint f x) (hg : f =ᶠ[𝓝 x] g) :
    IsNondegenerateCriticalPoint g x :=
  ⟨h.contDiffAt.congr_of_eventuallyEq hg.symm, by rw [hg.symm.fderiv_eq, h.fderiv_eq_zero],
    by rw [hg.symm.fderiv.fderiv_eq]; exact h.isInvertible⟩

/-- **A nondegenerate critical point is isolated.** Near such a point the differential of `f`
vanishes only at the point itself: the case `c = 0` of `TauCeti.eventually_fderiv_ne`, proved in
`TauCeti.Analysis.Calculus.SecondDerivative` because it uses no criticality. -/
theorem IsNondegenerateCriticalPoint.eventually_fderiv_ne_zero
    (h : IsNondegenerateCriticalPoint f x) :
    ∀ᶠ y in 𝓝[≠] x, fderiv ℝ f y ≠ 0 :=
  eventually_fderiv_ne h.contDiffAt h.isInvertible

/-- A critical locus all of whose points are nondegenerate is discrete. -/
theorem HasNondegenerateCriticalPointsOn.isDiscrete_setOfPred_fderiv_eq_zero {s : Set E}
    (hM : HasNondegenerateCriticalPointsOn f s) :
    IsDiscrete {x ∈ s | fderiv ℝ f x = 0} := by
  rw [isDiscrete_iff_nhdsNE]
  rintro y ⟨hys, hy0⟩
  rw [inf_principal_eq_bot]
  filter_upwards [(hM hys hy0).eventually_fderiv_ne_zero] with z hz
  simpa using fun _ ↦ hz

/-- **A function whose critical points on a compact set are all nondegenerate, and whose
differential is continuous there, has only finitely many critical points there.** Continuity of
`fderiv ℝ f` on `K` is what makes the critical locus closed, hence compact, and nondegeneracy is
what makes it discrete. This is the finiteness that makes the Morse complex of a compact manifold
finitely generated. -/
theorem HasNondegenerateCriticalPointsOn.finite_setOfPred_fderiv_eq_zero {K : Set E}
    (hK : IsCompact K) (hcont : ContinuousOn (fderiv ℝ f) K)
    (hM : HasNondegenerateCriticalPointsOn f K) :
    {x ∈ K | fderiv ℝ f x = 0}.Finite := by
  -- Continuity of `fderiv ℝ f` on `K` makes the critical locus a closed subset of `K`.
  have hclosed : IsClosed {x ∈ K | fderiv ℝ f x = 0} := by
    have h := hcont.preimage_isClosed_of_isClosed hK.isClosed (isClosed_singleton (x := 0))
    convert h using 1
    ext y
    simp
  exact (hK.of_isClosed_subset hclosed fun _ hx ↦ hx.1).finite
    hM.isDiscrete_setOfPred_fderiv_eq_zero

/-! ### Change of coordinates

At a critical point the first-order term of the chain rule drops out, so the second derivative
transforms as a bilinear form; this is `TauCeti.fderiv_fderiv_comp_apply_of_fderiv_eq_zero`, proved
in `TauCeti.Analysis.Calculus.SecondDerivative` because it involves no nondegeneracy. It is why the
Hessian at a critical point, and hence nondegeneracy, does not depend on the choice of chart.
-/

/-- **Nondegeneracy of a critical point does not depend on the coordinates.** If `f` is `C²` at
`φ b`, `φ` is `C²` at `b`, and the differential of `φ` at `b` is invertible, then `f ∘ φ` has a
nondegenerate critical point at `b` exactly when `f` has one at `φ b`. -/
theorem isNondegenerateCriticalPoint_comp_iff {φ : F → E} {b : F} (hf : ContDiffAt ℝ 2 f (φ b))
    (hφ : ContDiffAt ℝ 2 φ b) (hinv : (fderiv ℝ φ b).IsInvertible) :
    IsNondegenerateCriticalPoint (f ∘ φ) b ↔ IsNondegenerateCriticalPoint f (φ b) := by
  obtain ⟨e, he⟩ := hinv
  -- The differential of `f ∘ φ` at `b` is that of `f` at `φ b` precomposed with the equivalence
  -- `e`, so one vanishes exactly when the other does.
  have hcrit : fderiv ℝ (f ∘ φ) b = 0 ↔ fderiv ℝ f (φ b) = 0 := by
    rw [fderiv_comp (x := b) (hf.differentiableAt (by norm_num))
      (hφ.differentiableAt (by norm_num)), ← he]
    refine ⟨fun h ↦ ?_, fun h ↦ by rw [h]; ext u; simp⟩
    ext u
    simpa using congrArg (fun L : F →L[ℝ] ℝ ↦ L (e.symm u)) h
  -- The Hessian pulls back as `ψ ↦ ψ ∘ e` composed with the Hessian composed with `e`, and each of
  -- the three factors is invertible.
  have hEq : fderiv ℝ f (φ b) = 0 → fderiv ℝ (fderiv ℝ (f ∘ φ)) b =
      (e.symm.arrowCongr (ContinuousLinearEquiv.refl ℝ ℝ) : (E →L[ℝ] ℝ) →L[ℝ] F →L[ℝ] ℝ) ∘L
        fderiv ℝ (fderiv ℝ f) (φ b) ∘L (e : F →L[ℝ] E) := fun hc ↦ by
    ext v w
    rw [fderiv_fderiv_comp_apply_of_fderiv_eq_zero hf hφ hc, ← he]
    simp
  refine ⟨fun h ↦ ⟨hf, hcrit.1 h.fderiv_eq_zero, ?_⟩,
    fun h ↦ ⟨hf.comp b hφ, hcrit.2 h.fderiv_eq_zero, ?_⟩⟩
  · have hinv' := h.isInvertible
    rw [hEq (hcrit.1 h.fderiv_eq_zero)] at hinv'
    simpa using hinv'
  · rw [hEq h.fderiv_eq_zero]
    simpa using h.isInvertible

/-- A nondegenerate critical point of `f` at `φ b` pulls back to a nondegenerate critical point of
`f ∘ φ` at `b`, provided `φ` is `C²` at `b` and its differential there is invertible. -/
theorem IsNondegenerateCriticalPoint.comp {φ : F → E} {b : F}
    (h : IsNondegenerateCriticalPoint f (φ b)) (hφ : ContDiffAt ℝ 2 φ b)
    (hinv : (fderiv ℝ φ b).IsInvertible) :
    IsNondegenerateCriticalPoint (f ∘ φ) b :=
  (isNondegenerateCriticalPoint_comp_iff h.contDiffAt hφ hinv).2 h

/-- Negating the function preserves nondegenerate critical points: the differential and the second
derivative are both negated, and negation of the dual is a linear homeomorphism. This is the
symmetry exchanging the forward and backward directions of a negative gradient trajectory. -/
theorem IsNondegenerateCriticalPoint.neg (h : IsNondegenerateCriticalPoint f x) :
    IsNondegenerateCriticalPoint (-f) x := by
  have hfun : fderiv ℝ (-f) = -fderiv ℝ f := funext fun _ ↦ fderiv_neg
  refine ⟨ContDiffAt.neg h.contDiffAt, by rw [hfun]; simp [h.fderiv_eq_zero], ?_⟩
  have hsnd : fderiv ℝ (fderiv ℝ (-f)) x = -fderiv ℝ (fderiv ℝ f) x := by
    rw [hfun, fderiv_neg]
  have hcomp : -fderiv ℝ (fderiv ℝ f) x =
      (ContinuousLinearEquiv.neg ℝ : (E →L[ℝ] ℝ) ≃L[ℝ] (E →L[ℝ] ℝ)) ∘L
        fderiv ℝ (fderiv ℝ f) x := by
    ext v w
    simp
  rw [hsnd, hcomp]
  exact ContinuousLinearMap.isInvertible_equiv.comp h.isInvertible

/-- **Nondegeneracy of a critical point is invariant under negating the function.** Negation is
involutive, so the one-way implication `TauCeti.IsNondegenerateCriticalPoint.neg` applied twice
gives both directions. -/
@[simp]
theorem isNondegenerateCriticalPoint_neg :
    IsNondegenerateCriticalPoint (-f) x ↔ IsNondegenerateCriticalPoint f x :=
  ⟨fun h ↦ by simpa using h.neg, IsNondegenerateCriticalPoint.neg⟩

end Morse

/-! ### The quadratic model

A nondegenerate critical point looks, to second order, like a nondegenerate quadratic form. The
statements below record that the model itself has a nondegenerate critical point, so the
definition above is not vacuous. The derivatives of `z ↦ B z z` that they rest on are computed in
`TauCeti.Analysis.Calculus.Bilinear`.
-/

section Model

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]


/-- **The local model of a nondegenerate critical point.** If the polarization `B.flip + B` of a
continuous bilinear form `B` on `E` is invertible as a map into the dual space, then the quadratic
function `z ↦ B z z` has a nondegenerate critical point at the origin. -/
theorem _root_.ContinuousLinearMap.isNondegenerateCriticalPoint_apply_self (B : E →L[ℝ] E →L[ℝ] ℝ)
    (hB : (B.flip + B).IsInvertible) : IsNondegenerateCriticalPoint (fun z ↦ B z z) 0 :=
  ⟨(ContinuousLinearMap.contDiff_apply_self B).contDiffAt, by simp,
    by rw [ContinuousLinearMap.fderiv_fderiv_apply_self]; exact hB⟩

/-- A symmetric continuous bilinear form `B` on `E` which is invertible as a map into the dual
space makes `z ↦ B z z` a function with a nondegenerate critical point at the origin: its
polarization is then `2 • B`. -/
theorem _root_.ContinuousLinearMap.isNondegenerateCriticalPoint_apply_self_of_flip_eq_self
    (B : E →L[ℝ] E →L[ℝ] ℝ)
    (hsymm : B.flip = B) (hB : B.IsInvertible) :
    IsNondegenerateCriticalPoint (fun z ↦ B z z) 0 := by
  refine ContinuousLinearMap.isNondegenerateCriticalPoint_apply_self B ?_
  rw [hsymm, ← two_smul ℝ B]
  obtain ⟨e, rfl⟩ := hB
  refine _root_.ContinuousLinearMap.IsInvertible.of_inverse
    (g := (2 : ℝ)⁻¹ • (e.symm : (E →L[ℝ] ℝ) →L[ℝ] E)) ?_ ?_ <;> ext v <;> simp [smul_smul]


end Model

end TauCeti

/-! ### Upper and lower estimates on a normed space

Near a critical point, the differential is bounded above by a multiple of the distance to the
point, and the energy difference by a multiple of its square; at a nondegenerate critical point
the differential is also bounded below by a multiple of the distance. These estimates use only the
Fréchet derivative, so they hold on any real normed space; their gradient forms on a Hilbert space
are in `TauCeti.Analysis.Calculus.Morse.Linearization`. -/

namespace ContDiffAt

section NormedSpace

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {f : E → ℝ} {x : E}

/-- Near a critical point of a twice continuously differentiable function the differential is
bounded above by a multiple of the distance to that point: it vanishes at the point and is
differentiable there. -/
theorem exists_norm_fderiv_le_mul_norm_sub (hf : ContDiffAt ℝ 2 f x) (hf' : fderiv ℝ f x = 0) :
    ∃ C > 0, ∀ᶠ y in 𝓝 x, ‖fderiv ℝ f y‖ ≤ C * ‖y - x‖ := by
  simpa only [hf', sub_zero] using
    Asymptotics.isBigO_iff'.1 (hf.hasFDerivAt_fderiv le_rfl).isBigO_sub

/-- Near a critical point of a twice continuously differentiable function the absolute energy
difference `|f y - f x|` is bounded by a multiple of the squared distance to that point. This is
the mean value inequality applied along the segment from `x` to `y`, on which the differential is
bounded by a multiple of `‖y - x‖`. -/
theorem exists_abs_sub_le_mul_norm_sub_sq (hf : ContDiffAt ℝ 2 f x) (hf' : fderiv ℝ f x = 0) :
    ∃ C > 0, ∀ᶠ y in 𝓝 x, |f y - f x| ≤ C * ‖y - x‖ ^ 2 := by
  obtain ⟨C, hC, hbd⟩ := hf.exists_norm_fderiv_le_mul_norm_sub hf'
  have hdiff : ∀ᶠ y in 𝓝 x, DifferentiableAt ℝ f y := by
    filter_upwards [hf.eventually (by simp)] with y hy
    exact hy.differentiableAt (by simp)
  obtain ⟨r, hr, hball⟩ := Metric.eventually_nhds_iff.1 (hbd.and hdiff)
  refine ⟨C, hC, Metric.eventually_nhds_iff.2 ⟨r, hr, fun {y} hy ↦ ?_⟩⟩
  have hyr : ‖y - x‖ < r := by rwa [← dist_eq_norm]
  have hsub : Metric.closedBall x ‖y - x‖ ⊆ Metric.ball x r := fun z hz ↦
    lt_of_le_of_lt (Metric.mem_closedBall.1 hz) hyr
  have hkey : ‖f y - f x‖ ≤ C * ‖y - x‖ * ‖y - x‖ := by
    refine Convex.norm_image_sub_le_of_norm_fderiv_le (s := Metric.closedBall x ‖y - x‖)
      (fun z hz ↦ (hball (hsub hz)).2) (fun z hz ↦ ?_) (convex_closedBall x ‖y - x‖) ?_ ?_
    · refine ((hball (hsub hz)).1).trans (mul_le_mul_of_nonneg_left ?_ hC.le)
      have hz' := Metric.mem_closedBall.1 hz
      rwa [dist_eq_norm] at hz'
    · exact Metric.mem_closedBall_self (norm_nonneg _)
    · simp [Metric.mem_closedBall, dist_eq_norm]
  calc |f y - f x| = ‖f y - f x‖ := by rw [Real.norm_eq_abs]
    _ ≤ C * ‖y - x‖ * ‖y - x‖ := hkey
    _ = C * ‖y - x‖ ^ 2 := by ring

end NormedSpace

end ContDiffAt

namespace TauCeti

section NormedSpace

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {f : E → ℝ} {x : E}

/-- Near a nondegenerate critical point the differential is bounded below by a multiple of the
distance to that point: the second derivative is a linear homeomorphism onto the dual, hence
bounded below, and the differential differs from it by a term of smaller order. -/
theorem IsNondegenerateCriticalPoint.exists_mul_norm_sub_le_norm_fderiv
    (h : IsNondegenerateCriticalPoint f x) :
    ∃ c > 0, ∀ᶠ y in 𝓝 x, c * ‖y - x‖ ≤ ‖fderiv ℝ f y‖ := by
  obtain ⟨A, hA⟩ := h.isInvertible
  have hd : HasFDerivAt (fderiv ℝ f) (A : E →L[ℝ] E →L[ℝ] ℝ) x := by
    rw [hA]
    exact h.contDiffAt.hasFDerivAt_fderiv le_rfl
  have hb := A.isBigO_sub_rev (𝓝 x) x
  have he : Asymptotics.IsEquivalent (𝓝 x) (fun y ↦ fderiv ℝ f y - fderiv ℝ f x)
      (fun y ↦ A (y - x)) :=
    hd.isLittleO.trans_isBigO hb
  simpa only [h.fderiv_eq_zero, sub_zero] using
    Asymptotics.isBigO_iff''.1 (hb.trans he.isBigO_symm)

/-- **The Morse form of Łojasiewicz's gradient inequality on a normed space.** Near a
nondegenerate critical point the absolute energy difference is bounded by a multiple of the
squared norm of the differential; equivalently the Łojasiewicz inequality holds there with
exponent `1 / 2`. -/
theorem IsNondegenerateCriticalPoint.exists_mul_abs_sub_le_norm_fderiv_sq
    (h : IsNondegenerateCriticalPoint f x) :
    ∃ lam > 0, ∀ᶠ y in 𝓝 x, lam * |f y - f x| ≤ ‖fderiv ℝ f y‖ ^ 2 := by
  obtain ⟨c, hc, h1⟩ := h.exists_mul_norm_sub_le_norm_fderiv
  obtain ⟨C, hC, h2⟩ := h.contDiffAt.exists_abs_sub_le_mul_norm_sub_sq h.fderiv_eq_zero
  refine ⟨c ^ 2 / C, by positivity, ?_⟩
  filter_upwards [h1, h2] with y hy1 hy2
  have h3 : (c * ‖y - x‖) ^ 2 ≤ ‖fderiv ℝ f y‖ ^ 2 :=
    pow_le_pow_left₀ (by positivity) hy1 2
  calc c ^ 2 / C * |f y - f x| ≤ c ^ 2 / C * (C * ‖y - x‖ ^ 2) :=
        mul_le_mul_of_nonneg_left hy2 (by positivity)
    _ = (c * ‖y - x‖) ^ 2 := by field_simp
    _ ≤ ‖fderiv ℝ f y‖ ^ 2 := h3

end NormedSpace

end TauCeti

end
