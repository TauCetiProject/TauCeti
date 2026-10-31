/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.Deriv.Shift
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
import Mathlib.MeasureTheory.Integral.IntervalIntegral.DistLEIntegral

/-!
# The length of a path measured against a density

A **density** on a real normed space `F` is a function `ρ : F → ℝ`, thought of as a variable
conversion factor between the ambient norm and the length one wishes to measure. The length of a
path `γ : ℝ → F` over the parameter interval with endpoints `a` and `b` measured against `ρ` is

`TauCeti.densityLength ρ γ a b = ∫ t in uIcc a b, ρ (γ t) * ‖deriv γ t‖`,

the Euclidean speed `‖deriv γ t‖` weighted by the density at the point the path is passing
through. Taking `ρ = 1` gives the ordinary length of a `C¹` path; taking `ρ z = (1 - ‖z‖ ^ 2)⁻¹`
on the complex unit disc gives the hyperbolic length of
`TauCeti/Analysis/Complex/Conformal/Hyperbolic/Length.lean`, which is where this file's consumers
are.

## Why the definition is at this level

Everything proved below is a statement about the *parameter* side of the integral: how the length
responds to reversing, splitting or substituting in the parameter interval, and to changing the
path off that interval. The reparametrisation and interval-calculus results carry the density
along unchanged, as an arbitrary function of the point, and only `TauCeti.densityLength_nonneg`
inspects it at all, asking it to be nonnegative along the path; and none of it looks at the
codomain beyond its norm, so `F` is an arbitrary real normed space and `γ` an arbitrary map — not
necessarily continuous, let alone differentiable, `deriv` reading its junk value where the path is
not differentiable (`TauCeti.densityLength_eq_integral` is the reformulation for a path with a
known derivative). The hypotheses appear only where the mathematics needs them: nonnegativity of
the density for `TauCeti.densityLength_nonneg`, differentiability of the path for the two
substitution rules, which differentiate the composite, and integrability of the two integrands for
the comparison `TauCeti.densityLength_le_densityLength`, without which two comparable integrands
need not have comparable integrals. The pointwise hypotheses are asked at the *interior*
parameters only, the two endpoints forming a null set, and the two comparisons of speeds, in
`TauCeti.densityLength_le_densityLength` and in the displacement bound, only almost everywhere
there.

The one estimate that leaves the pair `(ρ, γ)` is `TauCeti.norm_sub_le_densityLength`, and it too
is a statement about the parameter side: a function of the parameter whose speed is dominated by
the density-weighted speed of `γ` is displaced, over the parameter interval, by no more than the
length of `γ` over it. It runs in a second normed space of its own, unrelated to `F`, the
hypothesis again comparing only real-valued speeds.

The integral is taken over the **unordered** interval `uIcc a b`, as in Mathlib's
`Manifold.pathELength`. This is what makes the length independent of the orientation of the
parameter interval (`TauCeti.densityLength_symm`) and nonnegative for a nonnegative density
whichever way round the endpoints are (`TauCeti.densityLength_nonneg`), and it is why the
substitution rules below hold for antitone substitutions
(`TauCeti.densityLength_comp_of_deriv_nonpos`) as they stand for monotone ones, with no sign
correction.

## Relation to Mathlib

Mathlib's `Mathlib/Geometry/Manifold/Riemannian/PathELength.lean` defines `Manifold.pathELength`,
the `ℝ≥0∞`-valued length of a path in a charted space each of whose tangent spaces carries an
`ENorm`, and `Manifold.riemannianEDist`, the infimum of such lengths. The two notions are
different in both directions: `pathELength` measures with a norm on each tangent space, which
subsumes a scalar density only after the ambient space is given a manifold structure and its
tangent spaces the corresponding `ENorm`s, and it is `ℝ≥0∞`-valued, whereas a density-weighted
length of a `C¹` path is an ordinary real number and is compared with real-valued distances
downstream. `densityLength` is therefore the elementary interval integral rather than a
`pathELength` specialisation, and the two share no lemma. Should the density-weighted case later
be routed through a Riemannian structure, the statements below are the ones to refactor.

The substitution rules are Mathlib's change of variables for a monotone or antitone substitution
(`intervalIntegral.integral_deriv_smul_comp_of_deriv_nonneg` and its `nonpos` counterpart) read
through the chain rule; the affine rule is `intervalIntegral.integral_comp_mul_add`; and the
displacement bound is Mathlib's `norm_sub_le_integral_of_norm_deriv_le_of_le`, freed from the
ordering of the parameter interval.

## Main definitions

* `TauCeti.densityLength` — the `ρ`-weighted length of a path over a parameter interval.

## Main results

* `TauCeti.densityLength_symm`, `TauCeti.densityLength_self`, `TauCeti.densityLength_const` —
  the length is unoriented, degenerate intervals and constant paths contributing nothing.
* `TauCeti.densityLength_eq_integral` — the length computed from an explicit derivative, the
  derivative being needed only at the interior parameters.
* `TauCeti.densityLength_nonneg` — a nonnegative density gives a nonnegative length.
* `TauCeti.densityLength_congr_of_eqOn` and `TauCeti.densityLength_le_densityLength` — two paths
  whose density-weighted speeds agree inside the parameter interval have equal lengths, and two
  whose integrable speeds compare almost everywhere there have comparable lengths.
* `TauCeti.norm_sub_le_densityLength` — **displacement is at most the length**: a function of the
  parameter whose speed is dominated by the density-weighted speed of the path moves, across the
  parameter interval, by no more than the length of the path over it.
* `TauCeti.densityLength_congr` — the length depends on the path only through its restriction to
  the interior of the parameter interval.
* `TauCeti.densityLength_add` — additivity along the parameter interval.
* `TauCeti.densityLength_comp_mul_add`, `TauCeti.densityLength_comp_of_deriv_nonneg`,
  `TauCeti.densityLength_comp_of_deriv_nonpos` — invariance under affine, monotone and antitone
  reparametrisation: the length is a property of the path, not of its parametrisation.

## References

* L. V. Ahlfors, *Conformal Invariants*, Ch. 1 (lengths measured against a conformal density).
-/

public section

namespace TauCeti

open MeasureTheory Set

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {ρ : F → ℝ} {γ δ : ℝ → F} {γ' : ℝ → F} {a b : ℝ}

/-- The **length of the path `γ` measured against the density `ρ`**, over the parameter interval
with endpoints `a` and `b`: the Euclidean speed `‖deriv γ t‖` integrated over the unordered
interval `uIcc a b` against the weight `ρ (γ t)`.

Taking the integral over the unordered interval makes the length independent of the orientation
of the parameter interval (`TauCeti.densityLength_symm`); together with
`TauCeti.densityLength_comp_of_deriv_nonneg` and `TauCeti.densityLength_comp_of_deriv_nonpos` this
makes it a reparametrisation invariant of the path.

The definition asks nothing of `γ` or of `ρ`; only the derivative at the interior parameters
enters (`TauCeti.densityLength_eq_integral`), the two endpoints forming a null set. It is the
intended notion of length when `γ` is a `C¹` path and `ρ` is a positive continuous density, which
is what the comparisons with a distance downstream assume; the evaluations of the length itself
need no such hypothesis. -/
noncomputable def densityLength (ρ : F → ℝ) (γ : ℝ → F) (a b : ℝ) : ℝ :=
  ∫ t in uIcc a b, ρ (γ t) * ‖deriv γ t‖

/-- The defining formula for the density-weighted length of a path. -/
theorem densityLength_def (ρ : F → ℝ) (γ : ℝ → F) (a b : ℝ) :
    densityLength ρ γ a b = ∫ t in uIcc a b, ρ (γ t) * ‖deriv γ t‖ := by
  rw [densityLength]

/-- A degenerate parameter interval carries no length. -/
@[simp]
theorem densityLength_self (ρ : F → ℝ) (γ : ℝ → F) (a : ℝ) : densityLength ρ γ a a = 0 := by
  rw [densityLength_def, uIcc_self]
  simp

/-- The length does not depend on the orientation of the parameter interval. -/
theorem densityLength_symm (ρ : F → ℝ) (γ : ℝ → F) (a b : ℝ) :
    densityLength ρ γ b a = densityLength ρ γ a b := by
  rw [densityLength_def, densityLength_def, uIcc_comm]

/-- A constant path has zero length. -/
@[simp]
theorem densityLength_const (ρ : F → ℝ) (c : F) (a b : ℝ) :
    densityLength ρ (fun _ => c) a b = 0 := by
  rw [densityLength_def]
  simp

/-- The length as an integral over the *open* parameter interval, the two endpoints forming a null
set. This is what lets every hypothesis below be asked at the interior parameters only. -/
private theorem densityLength_eq_setIntegral_uIoo (ρ : F → ℝ) (γ : ℝ → F) (a b : ℝ) :
    densityLength ρ γ a b = ∫ t in uIoo a b, ρ (γ t) * ‖deriv γ t‖ := by
  rw [densityLength_def, ← Icc_min_max, ← restrict_Ioo_eq_restrict_Icc, Ioo_min_max]

/-- **Two paths with the same density-weighted speed inside the parameter interval have the same
length.** This is the shape in which a symmetry of the pair `(ρ, γ)` — an isometry of the ambient
space preserving the density, say — is fed to the length.

As for its inequality counterpart `TauCeti.densityLength_le_densityLength`, nothing relates the
two paths, or the two densities, beyond that pointwise agreement — not even the space they run
in, the hypothesis comparing only their real-valued weighted speeds. -/
theorem densityLength_congr_of_eqOn {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]
    {ρ' : G → ℝ} {δ : ℝ → G}
    (h : EqOn (fun t => ρ' (δ t) * ‖deriv δ t‖) (fun t => ρ (γ t) * ‖deriv γ t‖) (uIoo a b)) :
    densityLength ρ' δ a b = densityLength ρ γ a b := by
  rw [densityLength_eq_setIntegral_uIoo, densityLength_eq_setIntegral_uIoo]
  exact setIntegral_congr_fun measurableSet_Ioo h

/-- The length over an ordered parameter interval as an interval integral of any function
agreeing with the density-weighted speed at the interior parameters, the two endpoints forming a
null set. -/
private theorem densityLength_eq_intervalIntegral_of_eqOn {f : ℝ → ℝ} (hab : a ≤ b)
    (hf : EqOn (fun t => ρ (γ t) * ‖deriv γ t‖) f (Ioo a b)) :
    densityLength ρ γ a b = ∫ t in a..b, f t := by
  rw [densityLength_def, uIcc_of_le hab, ← restrict_Ioo_eq_restrict_Icc,
    setIntegral_congr_fun measurableSet_Ioo hf, restrict_Ioo_eq_restrict_Icc,
    integral_Icc_eq_integral_Ioc, intervalIntegral.integral_of_le hab]

/-- The length over an ordered parameter interval as an interval integral of the density-weighted
speed. -/
theorem densityLength_eq_intervalIntegral (ρ : F → ℝ) (γ : ℝ → F) (hab : a ≤ b) :
    densityLength ρ γ a b = ∫ t in a..b, ρ (γ t) * ‖deriv γ t‖ :=
  densityLength_eq_intervalIntegral_of_eqOn hab fun _ _ => rfl

/-- The length computed from an explicit derivative rather than from `deriv`. The derivative is
only asked for at the interior parameters, the two endpoints forming a null set. -/
theorem densityLength_eq_integral (hab : a ≤ b) (hderiv : ∀ t ∈ Ioo a b, HasDerivAt γ (γ' t) t) :
    densityLength ρ γ a b = ∫ t in a..b, ρ (γ t) * ‖γ' t‖ :=
  densityLength_eq_intervalIntegral_of_eqOn hab fun t ht => by simp only [(hderiv t ht).deriv]

/-- A path along which the density is nonnegative inside the parameter interval has nonnegative
length, whichever way round its endpoints are. -/
theorem densityLength_nonneg (hρ : ∀ t ∈ uIoo a b, 0 ≤ ρ (γ t)) : 0 ≤ densityLength ρ γ a b := by
  rw [densityLength_eq_setIntegral_uIoo]
  exact setIntegral_nonneg measurableSet_Ioo fun t ht => mul_nonneg (hρ t ht) (norm_nonneg _)

/-- **Comparing density-weighted speeds compares the lengths.** If at almost every interior
parameter the density-weighted speed of `δ` is at most that of `γ`, and both speeds are integrable
over the parameter interval, then `δ` is no longer than `γ` over it, whichever way round its
endpoints are.

Nothing relates the two paths, or the two densities, beyond that comparison — not even
the space they run in, the hypotheses comparing only their real-valued weighted speeds — which is
the form in which a contraction property of a map post-composed with a path — a Schwarz--Pick
estimate, say — arrives: the chain rule turns the density-weighted speed of the composite into a
factor bounded by the density at the point times the speed of the path. The comparison is the
inequality counterpart of `TauCeti.densityLength_congr_of_eqOn`, which needs no integrability
because equal integrands have equal integrals whether or not they are integrable. As there, the
comparison is between the integrands that define the two lengths, and is asked at the interior
parameters only; as in `TauCeti.norm_sub_le_densityLength`, it is asked there only almost
everywhere, a comparison holding at every interior parameter being read through
`Filter.Eventually.of_forall`, and a path with an explicit derivative through `HasDerivAt.deriv`.
Integrability, unlike that comparison, is a genuinely additional hypothesis: the density being
arbitrary here, regularity of the path alone does not supply it, and it is the `C¹` path
*together with* a density continuous along it that does — as in the hyperbolic application, where
the path stays in the open disc on which the Poincaré density is continuous. -/
theorem densityLength_le_densityLength {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]
    {ρ' : G → ℝ} {δ : ℝ → G}
    (hδint : IntervalIntegrable (fun t => ρ' (δ t) * ‖deriv δ t‖) volume a b)
    (hγint : IntervalIntegrable (fun t => ρ (γ t) * ‖deriv γ t‖) volume a b)
    (h : ∀ᵐ t, t ∈ uIoo a b → ρ' (δ t) * ‖deriv δ t‖ ≤ ρ (γ t) * ‖deriv γ t‖) :
    densityLength ρ' δ a b ≤ densityLength ρ γ a b := by
  have hsub : uIoo a b ⊆ uIoc a b := by
    rw [uIoo_eq_union, uIoc_eq_union]
    exact union_subset_union Ioo_subset_Ioc_self Ioo_subset_Ioc_self
  rw [densityLength_eq_setIntegral_uIoo, densityLength_eq_setIntegral_uIoo]
  exact setIntegral_mono_on_ae ((intervalIntegrable_iff.mp hδint).mono_set hsub)
    ((intervalIntegrable_iff.mp hγint).mono_set hsub) measurableSet_Ioo h

/-- **Displacement is at most the length.** If a function `u` of the parameter is continuous on the
parameter interval, differentiable inside it, and its speed there is almost everywhere at most the
density-weighted speed of `γ`, then `u` moves across the interval by at most the `ρ`-length of `γ`
over it, whichever way round the endpoints are.

This is how a length bounds a distance. Taking for `u` a quantity that the length is to dominate —
for the Poincaré density on the disc, `Real.artanh ∘ (fun t => (v * γ t).re)` for a unit vector
`v`, a linear functional of `γ` read through `Real.artanh` rather than `Real.artanh ‖γ‖`, which
is not differentiable where the path crosses the origin — reduces the bound to the comparison
`hbound` between two speeds, exactly as
`TauCeti.densityLength_le_densityLength` reduces a comparison of two lengths to one. Nothing
relates `u` to `γ` beyond that comparison, not even the space it runs in: `u` takes values in a
normed space of its own, and the density-weighted speed of `γ` enters only as a real-valued upper
estimate on `‖deriv u‖`. Integrability of that estimate is needed for the same reason as there,
and both hypotheses are asked at the *interior* parameters only, the two endpoints forming a null
set — the comparison, as in Mathlib's `norm_sub_le_integral_of_norm_deriv_le_of_le`, only almost
everywhere there, a bound holding at every interior parameter being read through
`Filter.Eventually.of_forall`; a `u` with an explicit derivative is read through
`HasDerivAt.deriv`. -/
theorem norm_sub_le_densityLength {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]
    {u : ℝ → G} (hu : ContinuousOn u (uIcc a b)) (hdiff : DifferentiableOn ℝ u (uIoo a b))
    (hbound : ∀ᵐ t, t ∈ uIoo a b → ‖deriv u t‖ ≤ ρ (γ t) * ‖deriv γ t‖)
    (hint : IntervalIntegrable (fun t => ρ (γ t) * ‖deriv γ t‖) volume a b) :
    ‖u b - u a‖ ≤ densityLength ρ γ a b := by
  wlog hab : a ≤ b generalizing a b
  · rw [uIcc_comm] at hu
    rw [uIoo_comm] at hdiff hbound
    rw [← densityLength_symm, ← norm_neg, neg_sub]
    exact this hu hdiff hbound hint.symm (le_of_not_ge hab)
  rw [uIcc_of_le hab] at hu
  rw [uIoo_of_le hab] at hdiff hbound
  rw [densityLength_eq_intervalIntegral ρ γ hab]
  exact norm_sub_le_integral_of_norm_deriv_le_of_le hab hu hdiff hbound hint

/-- **The length of a path depends only on its parameter interval.** Two paths that agree inside
the interval with endpoints `a` and `b` have the same length over it: at an interior parameter they
have the same germ, hence the same derivative, and the two endpoints form a null set. -/
theorem densityLength_congr (hδ : EqOn δ γ (uIoo a b)) :
    densityLength ρ δ a b = densityLength ρ γ a b :=
  densityLength_congr_of_eqOn fun t ht => by
    have hnhds : δ =ᶠ[nhds t] γ := Filter.eventuallyEq_of_mem (isOpen_Ioo.mem_nhds ht) hδ
    simp only [hnhds.deriv_eq, hδ ht]

/-- **The length is additive along the parameter interval**: for a parameter `b` between `a` and
`c`, the lengths of the two pieces of a path add up to the length of the whole, as soon as the
density-weighted speed is integrable over the whole. For a `C¹` path and a continuous density that
hypothesis holds by continuity. -/
theorem densityLength_add {a b c : ℝ} (hb : b ∈ uIcc a c)
    (hint : IntervalIntegrable (fun t => ρ (γ t) * ‖deriv γ t‖) volume a c) :
    densityLength ρ γ a b + densityLength ρ γ b c = densityLength ρ γ a c := by
  wlog hac : a ≤ c generalizing a c
  · rw [densityLength_symm ρ γ b a, densityLength_symm ρ γ c b, densityLength_symm ρ γ c a,
      add_comm]
    exact this (uIcc_comm a c ▸ hb) hint.symm (le_of_not_ge hac)
  rw [uIcc_of_le hac] at hb
  rw [densityLength_eq_intervalIntegral ρ γ hb.1, densityLength_eq_intervalIntegral ρ γ hb.2,
    densityLength_eq_intervalIntegral ρ γ hac]
  exact intervalIntegral.integral_add_adjacent_intervals
    (hint.mono_set (uIcc_subset_uIcc_left (uIcc_of_le hac ▸ hb)))
    (hint.mono_set (uIcc_subset_uIcc_right (uIcc_of_le hac ▸ hb)))

/-- **The length is invariant under affine reparametrisation.** Replacing the parameter `t` by
`s * t + d`, an orientation-preserving reparametrisation for `0 < s` and an orientation-reversing
one for `s < 0`, transports the parameter interval and leaves the length unchanged; for `s = 0`
both sides vanish, the path being constant and the transported interval degenerate. Being a change
of variables in the parameter alone, it asks nothing of the path, unlike the reparametrisations by
a general monotone or antitone map below (`TauCeti.densityLength_comp_of_deriv_nonneg`,
`TauCeti.densityLength_comp_of_deriv_nonpos`), which need the path to be differentiable to
differentiate the composite. -/
theorem densityLength_comp_mul_add (ρ : F → ℝ) (γ : ℝ → F) (s d a b : ℝ) :
    densityLength ρ (fun t => γ (s * t + d)) a b = densityLength ρ γ (s * a + d) (s * b + d) := by
  rcases eq_or_ne s 0 with rfl | hs
  · simp
  wlog hab : a ≤ b generalizing a b
  · rw [densityLength_symm, this b a (le_of_not_ge hab), densityLength_symm]
  have hLHS : densityLength ρ (fun t => γ (s * t + d)) a b
      = |s| * ∫ t in a..b, ρ (γ (s * t + d)) * ‖deriv γ (s * t + d)‖ := by
    rw [densityLength_eq_intervalIntegral _ _ hab, ← intervalIntegral.integral_const_mul]
    refine intervalIntegral.integral_congr fun t _ => ?_
    have hderiv := deriv_comp_mul_left s (fun u : ℝ => γ (u + d)) t
    rw [deriv_comp_add_const] at hderiv
    simp only [hderiv, norm_smul, Real.norm_eq_abs]
    ring
  rw [hLHS, intervalIntegral.integral_comp_mul_add
    (fun u => ρ (γ u) * ‖deriv γ u‖) hs d, smul_eq_mul]
  rcases hs.lt_or_gt with hneg | hpos
  · have hle : s * b + d ≤ s * a + d := by nlinarith
    rw [densityLength_symm, densityLength_eq_intervalIntegral _ _ hle,
      intervalIntegral.integral_symm (s * a + d) (s * b + d), abs_of_neg hneg]
    field_simp
  · have hle : s * a + d ≤ s * b + d := by nlinarith
    rw [densityLength_eq_intervalIntegral _ _ hle, abs_of_pos hpos]
    field_simp

/-- **The length is invariant under monotone reparametrisation.** Precomposing a path with a map
`φ` that is continuous on the parameter interval and has a nonnegative derivative inside it — so
that `φ` is monotone there — reparametrises the path and transports the parameter interval,
leaving the length unchanged. The path is asked to be differentiable at the reparametrised
parameters, which is what makes the composite differentiable; no regularity beyond that is needed,
because Mathlib's change of variables for a monotone substitution
(`intervalIntegral.integral_deriv_smul_comp_of_deriv_nonneg`) asks nothing of the integrand. -/
theorem densityLength_comp_of_deriv_nonneg {φ φ' : ℝ → ℝ} (hφ : ContinuousOn φ (uIcc a b))
    (hderiv : ∀ t ∈ uIoo a b, HasDerivAt φ (φ' t) t) (hsign : ∀ t ∈ uIoo a b, 0 ≤ φ' t)
    (hγ : ∀ t ∈ uIoo a b, DifferentiableAt ℝ γ (φ t)) :
    densityLength ρ (γ ∘ φ) a b = densityLength ρ γ (φ a) (φ b) := by
  wlog hab : a ≤ b generalizing a b
  · rw [uIcc_comm] at hφ
    rw [uIoo_comm] at hderiv hsign hγ
    rw [densityLength_symm, this hφ hderiv hsign hγ (le_of_not_ge hab), densityLength_symm]
  rw [uIcc_of_le hab] at hφ
  rw [uIoo_of_le hab] at hderiv hsign hγ
  have hIoo : Ioo (min a b) (max a b) = Ioo a b := by rw [min_eq_left hab, max_eq_right hab]
  -- inside the parameter interval the density-weighted speed of `γ ∘ φ` is `φ'` times that of
  -- `γ` read at `φ`, written as a composition to meet the change of variables below
  have hEq : EqOn (fun t => ρ ((γ ∘ φ) t) * ‖deriv (γ ∘ φ) t‖)
      (fun t => φ' t • ((fun u => ρ (γ u) * ‖deriv γ u‖) ∘ φ) t) (Ioo a b) := by
    intro t ht
    have hchain : deriv (γ ∘ φ) t = φ' t • deriv γ (φ t) :=
      ((hγ t ht).hasDerivAt.scomp t (hderiv t ht)).deriv
    simp only [Function.comp_apply, hchain, norm_smul, Real.norm_eq_abs,
      abs_of_nonneg (hsign t ht), smul_eq_mul]
    ring
  have hφab : φ a ≤ φ b := by
    refine monotoneOn_of_hasDerivWithinAt_nonneg (f' := φ') (convex_Icc a b) hφ ?_ ?_
      (left_mem_Icc.2 hab) (right_mem_Icc.2 hab) hab <;> rw [interior_Icc]
    exacts [fun t ht => (hderiv t ht).hasDerivWithinAt, hsign]
  rw [densityLength_eq_intervalIntegral_of_eqOn hab hEq,
    intervalIntegral.integral_deriv_smul_comp_of_deriv_nonneg (by rwa [uIcc_of_le hab])
      (by rwa [hIoo]) (by rwa [hIoo]),
    ← densityLength_eq_intervalIntegral ρ γ hφab]

/-- **The length is invariant under antitone reparametrisation.** The orientation-reversing
counterpart of `TauCeti.densityLength_comp_of_deriv_nonneg`: precomposing a path with a map `φ`
that is continuous on the parameter interval and has a nonpositive derivative inside it — so that
`φ` is antitone there — leaves the length unchanged, the parameter interval being transported with
its orientation reversed. Together the two lemmas say that the length is a property of a path
rather than of its parametrisation. -/
theorem densityLength_comp_of_deriv_nonpos {φ φ' : ℝ → ℝ} (hφ : ContinuousOn φ (uIcc a b))
    (hderiv : ∀ t ∈ uIoo a b, HasDerivAt φ (φ' t) t) (hsign : ∀ t ∈ uIoo a b, φ' t ≤ 0)
    (hγ : ∀ t ∈ uIoo a b, DifferentiableAt ℝ γ (φ t)) :
    densityLength ρ (γ ∘ φ) a b = densityLength ρ γ (φ a) (φ b) := by
  -- `γ ∘ φ` is the path `t ↦ γ (-t)` reparametrised by the monotone map `-φ`
  have h := densityLength_comp_of_deriv_nonneg (ρ := ρ) (γ := fun u => γ (-1 * u + 0))
    (φ := -φ) (φ' := -φ') hφ.neg (fun t ht => (hderiv t ht).neg)
    (fun t ht => neg_nonneg.2 (hsign t ht)) fun t ht => ?_
  · rw [densityLength_comp_mul_add] at h
    simpa [Function.comp_def] using h
  · simpa [differentiableAt_comp_neg] using hγ t ht

end TauCeti
