/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Calculus.Morse.Cerf.Cubic
public import TauCeti.Analysis.Calculus.Morse.Cerf.Isolated
import Mathlib.Analysis.Normed.Module.FiniteDimension
import TauCeti.Analysis.Calculus.ContDiff.Prod
import TauCeti.Analysis.Normed.Operator.Surjective
import TauCeti.Topology.Algebra.Module.FiniteDimension
import TauCeti.Topology.MetricSpace.HausdorffDistance
import TauCeti.Topology.UniformSpace.HeineCantor

/-!
# Persistence and genericity of families with only birth–death degeneracies

Let `f t : E → ℝ` be a one-parameter family of functions on a finite-dimensional real normed
space. Cerf's theorem describes the degenerate critical points of a generic family: at each of
them the family is *transverse*, that is the derivative of the parametrized differential
`(t, x) ↦ d(f t)_x` is onto, and along a nonzero vector `v` of the kernel of the Hessian the third
derivative `D³(f t)_x (v, v, v)` does not vanish. These are the birth–death points, where a pair of
critical points of adjacent indices is born or dies (`TauCeti.Analysis.Calculus.Morse.Cerf.Fold`).
At a nondegenerate critical point of a jointly `C²` family both conditions hold automatically. A
family **has only birth–death degeneracies** on a set `s ⊆ ℝ × E`
(`TauCeti.HasBirthDeathCriticalPointsOn f s`) when both conditions hold at every critical point
in `s`. If such a family is jointly `C³` at every point of a compact set `K`, it has only finitely
many degenerate critical points in `K`
(`HasBirthDeathCriticalPointsOn.finite_setOf_fderiv_eq_zero_and_not_isNondegenerateCriticalPoint`).

This file proves that having only birth–death degeneracies on a compact set `K` is an open
condition, and combines it with the density statements of `TauCeti.Analysis.Calculus.Morse.Cerf`
and `TauCeti.Analysis.Calculus.Morse.Cerf.Cubic`.

* **Persistence.** If `f` has only birth–death degeneracies on `K`, with differential and
  derivative of the parametrized differential continuous on `K`, and Hessian and third derivative
  along unit vectors continuous on `K × sphere 0 1`, then so does every family `g` whose
  corresponding derivatives are uniformly close to those of `f` there
  (`TauCeti.HasBirthDeathCriticalPointsOn.exists_pos_forall_hasBirthDeathCriticalPointsOn`).
  Both conditions are open, and compactness makes them uniform: transversality, because
  surjective operators onto a finite-dimensional space form an open set
  (`TauCeti.isOpen_setOf_surjective`), and the cubic condition, because it only needs to be
  tested on the unit sphere of `E`, which is compact. Both alternatives are handled by
  `IsCompact.exists_pos_forall_mem_of_norm_le`, applied on `K` and on `K × sphere 0 1`.
* **Families of families.** For families `f p` depending jointly `C³` on a parameter `p` in a
  normed space, the parameters `p` for which `f p` has only birth–death degeneracies on `K` form an
  open set (`TauCeti.HasBirthDeathCriticalPointsOn.eventually_hasBirthDeathCriticalPointsOn`).
* **Polynomial perturbations.** For a family `f` jointly `C⁴` near `K`, the coefficients `p` of
  the polynomials of degree at most three for which `f t - cubicPerturbation p` has only
  birth–death degeneracies on `K` form an open
  (`TauCeti.isOpen_setOf_hasBirthDeathCriticalPointsOn_sub_cubicPerturbation`) and dense
  (`TauCeti.dense_setOf_hasBirthDeathCriticalPointsOn_sub_cubicPerturbation`) set, whose
  complement is Haar null
  (`TauCeti.ae_hasBirthDeathCriticalPointsOn_sub_cubicPerturbation`). Intersecting
  these sets over the closed balls of integer radius, for a family jointly `C⁴` everywhere, the
  coefficients for which `f t - cubicPerturbation p` has only birth–death degeneracies on all of
  `ℝ × E` form a residual set
  (`TauCeti.mem_residual_setOf_hasBirthDeathCriticalPointsOn_sub_cubicPerturbation`).

## Main declarations

* `TauCeti.HasBirthDeathCriticalPointsOn`: every critical point of the family in a set is
  nondegenerate or a birth–death point.
* `HasBirthDeathCriticalPointsOn.finite_setOf_fderiv_eq_zero_and_not_isNondegenerateCriticalPoint`:
  finitely many degenerate critical points in a compact set.
* `TauCeti.HasBirthDeathCriticalPointsOn.exists_pos_forall_hasBirthDeathCriticalPointsOn`:
  persistence under perturbations that are small up to third derivatives on a compact set.
* `TauCeti.HasBirthDeathCriticalPointsOn.eventually_hasBirthDeathCriticalPointsOn`: openness in a
  jointly `C³` parameter.
* `TauCeti.ae_hasBirthDeathCriticalPointsOn_sub_cubicPerturbation`: almost every cubic
  perturbation leaves only birth–death degeneracies.
* `TauCeti.isOpen_setOf_hasBirthDeathCriticalPointsOn_sub_cubicPerturbation`,
  `TauCeti.dense_setOf_hasBirthDeathCriticalPointsOn_sub_cubicPerturbation`: the good cubic
  perturbations form an open dense set.
* `TauCeti.mem_residual_setOf_hasBirthDeathCriticalPointsOn_sub_cubicPerturbation`: a generic cubic
  perturbation leaves only birth–death degeneracies.

## References

* J. Cerf, *La stratification naturelle des espaces de fonctions différentiables réelles et le
  théorème de la pseudo-isotopie*, Publ. Math. IHÉS **39** (1970), 5–173, Chapter III.
* M. Hutchings, *Lecture notes on Morse homology (with an eye towards Floer theory and
  pseudoholomorphic curves)*, 2002, §4 (generic one-parameter families and bifurcations).
-/

public section

open Function Metric Set Filter
open scoped Topology

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- A one-parameter family `f t : E → ℝ` **has only birth–death degeneracies** on a set
`s ⊆ ℝ × E` when at every point `(t, x) ∈ s` at which `x` is a critical point of `f t`, the family
is transverse, that is the derivative of the parametrized differential `(t, x) ↦ d(f t)_x` is onto,
and no nonzero vector `v` in the kernel of the Hessian of `f t` at `x` has
`D³(f t)_x (v, v, v) = 0`.

If the family is jointly `C²` at such a point, the critical point is either nondegenerate, or a
birth–death point: the Hessian has a one-dimensional kernel
(`TauCeti.finrank_ker_fderiv_fderiv_le_one`), along which the third derivative and the parameter
derivative of the differential (`TauCeti.surjective_fderiv_fderiv_iff`) do not vanish. -/
def HasBirthDeathCriticalPointsOn (f : ℝ → E → ℝ) (s : Set (ℝ × E)) : Prop :=
  ∀ ⦃z : ℝ × E⦄, z ∈ s → fderiv ℝ (f z.1) z.2 = 0 →
    Surjective (fderiv ℝ (fun w : ℝ × E ↦ fderiv ℝ (f w.1) w.2) z) ∧
      ∀ v, fderiv ℝ (fderiv ℝ (f z.1)) z.2 v = 0 →
        fderiv ℝ (fderiv ℝ (fderiv ℝ (f z.1))) z.2 v v v = 0 → v = 0

/-- The introduction and elimination rule for `HasBirthDeathCriticalPointsOn`. Like
`TauCeti.hasNondegenerateCriticalPointsOn_iff`, it is not a `simp` lemma, so that the predicate
keeps its API. -/
theorem hasBirthDeathCriticalPointsOn_iff {f : ℝ → E → ℝ} {s : Set (ℝ × E)} :
    HasBirthDeathCriticalPointsOn f s ↔ ∀ ⦃z : ℝ × E⦄, z ∈ s → fderiv ℝ (f z.1) z.2 = 0 →
      Surjective (fderiv ℝ (fun w : ℝ × E ↦ fderiv ℝ (f w.1) w.2) z) ∧
        ∀ v, fderiv ℝ (fderiv ℝ (f z.1)) z.2 v = 0 →
          fderiv ℝ (fderiv ℝ (fderiv ℝ (f z.1))) z.2 v v v = 0 → v = 0 :=
  Iff.rfl

/-- Having only birth–death degeneracies passes to subsets. -/
theorem HasBirthDeathCriticalPointsOn.mono {f : ℝ → E → ℝ} {s t : Set (ℝ × E)}
    (h : HasBirthDeathCriticalPointsOn f s) (hts : t ⊆ s) : HasBirthDeathCriticalPointsOn f t :=
  fun _ hz ↦ h (hts hz)

namespace HasBirthDeathCriticalPointsOn

/-- **A family with only birth–death degeneracies has finitely many of them in a compact set.** If
`f` has only birth–death degeneracies on a compact set `K ⊆ ℝ × E` and is jointly `C³` at every
point of `K`, then only finitely many points `(t, x) ∈ K` are degenerate critical points of
`f t`. -/
theorem finite_setOf_fderiv_eq_zero_and_not_isNondegenerateCriticalPoint [FiniteDimensional ℝ E]
    {f : ℝ → E → ℝ} {K : Set (ℝ × E)} (h : HasBirthDeathCriticalPointsOn f K) (hK : IsCompact K)
    (hf : ∀ z ∈ K, ContDiffAt ℝ 3 (uncurry f) z) :
    {z ∈ K | fderiv ℝ (f z.1) z.2 = 0 ∧ ¬ IsNondegenerateCriticalPoint (f z.1) z.2}.Finite :=
  TauCeti.finite_setOf_fderiv_eq_zero_and_not_isNondegenerateCriticalPoint hK hf
    (fun _ hz hz₀ ↦ (h hz hz₀).1) fun _ hz hz₀ ↦ (h hz hz₀).2

end HasBirthDeathCriticalPointsOn

/-! ### Persistence on compact sets -/

section Persistence

variable [FiniteDimensional ℝ E]

/-- The cubic condition of a family with only birth–death degeneracies is uniform on a compact set:
at points of `K` where the differential is small, along unit vectors on which the Hessian is
small, every number close to the third derivative is nonzero. -/
private theorem exists_pos_forall_ne_zero_of_norm_le {f : ℝ → E → ℝ} {K : Set (ℝ × E)}
    (hK : IsCompact K) (hf₁ : ContinuousOn (fun z : ℝ × E ↦ fderiv ℝ (f z.1) z.2) K)
    (hfH : ContinuousOn (fun q : (ℝ × E) × E ↦ fderiv ℝ (fderiv ℝ (f q.1.1)) q.1.2 q.2)
      (K ×ˢ sphere 0 1))
    (hf₃ : ContinuousOn (fun q : (ℝ × E) × E ↦
      fderiv ℝ (fderiv ℝ (fderiv ℝ (f q.1.1))) q.1.2 q.2 q.2 q.2) (K ×ˢ sphere 0 1))
    (h : HasBirthDeathCriticalPointsOn f K) :
    ∃ δ > 0, ∀ z ∈ K, ∀ u ∈ sphere (0 : E) 1, ∀ c : ℝ, ‖fderiv ℝ (f z.1) z.2‖ ≤ δ →
      ‖fderiv ℝ (fderiv ℝ (f z.1)) z.2 u‖ ≤ δ →
        dist c (fderiv ℝ (fderiv ℝ (fderiv ℝ (f z.1))) z.2 u u u) ≤ δ → c ≠ 0 := by
  have hfst : MapsTo Prod.fst (K ×ˢ sphere (0 : E) 1) K := fun _ hq ↦ hq.1
  obtain ⟨δ, hδ, hO⟩ := (hK.prod (isCompact_sphere (0 : E) 1)).exists_pos_forall_mem_of_norm_le
    (d := fun q : (ℝ × E) × E ↦
      (fderiv ℝ (f q.1.1) q.1.2, fderiv ℝ (fderiv ℝ (f q.1.1)) q.1.2 q.2))
    ((hf₁.comp continuousOn_fst hfst).prodMk hfH) hf₃ (isOpen_ne (x := (0 : ℝ)))
    fun q hq hq₀ hA ↦ by
      -- At a zero of `d`, the cubic condition forbids a vanishing third derivative.
      have hu : q.2 ≠ 0 := ne_zero_of_mem_unit_sphere ⟨q.2, hq.2⟩
      exact hu ((h hq.1 (congrArg Prod.fst hq₀)).2 q.2 (congrArg Prod.snd hq₀) hA)
  refine ⟨δ, hδ, fun z hz u hu c hG hH hc ↦ hO (z, u) ⟨hz, hu⟩ c ?_ hc⟩
  exact norm_prod_le_iff.2 ⟨hG, hH⟩

/-- **Only birth–death degeneracies persist under small perturbations on a compact set.**

Let `f` be a one-parameter family of functions on a finite-dimensional real normed space with only
birth–death degeneracies on a compact set `K ⊆ ℝ × E`. Suppose that its differential and the
derivative of its parametrized differential are continuous on `K`, and that its Hessian and its
third derivative, evaluated along unit vectors `u` as `Hess(f t)_x u` and `D³(f t)_x (u, u, u)`,
are continuous on `K × sphere 0 1`. Then there is `δ > 0` such that every family `g` whose
differential and derivative of the parametrized differential are within `δ` of those of `f`, and
whose Hessian and third derivative along unit vectors are within `δ` of those of `f`, at every
point of `K`, again has only birth–death degeneracies on `K`. -/
theorem HasBirthDeathCriticalPointsOn.exists_pos_forall_hasBirthDeathCriticalPointsOn
    {f : ℝ → E → ℝ} {K : Set (ℝ × E)} (hK : IsCompact K)
    (hf₁ : ContinuousOn (fun z : ℝ × E ↦ fderiv ℝ (f z.1) z.2) K)
    (hf₂ : ContinuousOn (fun z : ℝ × E ↦ fderiv ℝ (fun w : ℝ × E ↦ fderiv ℝ (f w.1) w.2) z) K)
    (hfH : ContinuousOn (fun q : (ℝ × E) × E ↦ fderiv ℝ (fderiv ℝ (f q.1.1)) q.1.2 q.2)
      (K ×ˢ sphere 0 1))
    (hf₃ : ContinuousOn (fun q : (ℝ × E) × E ↦
      fderiv ℝ (fderiv ℝ (fderiv ℝ (f q.1.1))) q.1.2 q.2 q.2 q.2) (K ×ˢ sphere 0 1))
    (h : HasBirthDeathCriticalPointsOn f K) :
    ∃ δ > 0, ∀ g : ℝ → E → ℝ,
      (∀ z ∈ K, dist (fderiv ℝ (g z.1) z.2) (fderiv ℝ (f z.1) z.2) ≤ δ) →
      (∀ z ∈ K, dist (fderiv ℝ (fun w : ℝ × E ↦ fderiv ℝ (g w.1) w.2) z)
        (fderiv ℝ (fun w : ℝ × E ↦ fderiv ℝ (f w.1) w.2) z) ≤ δ) →
      (∀ z ∈ K, ∀ u ∈ sphere (0 : E) 1,
        dist (fderiv ℝ (fderiv ℝ (g z.1)) z.2 u) (fderiv ℝ (fderiv ℝ (f z.1)) z.2 u) ≤ δ) →
      (∀ z ∈ K, ∀ u ∈ sphere (0 : E) 1, dist (fderiv ℝ (fderiv ℝ (fderiv ℝ (g z.1))) z.2 u u u)
        (fderiv ℝ (fderiv ℝ (fderiv ℝ (f z.1))) z.2 u u u) ≤ δ) →
      HasBirthDeathCriticalPointsOn g K := by
  -- Transversality is uniform near the critical points of `f` in `K`, and so is the cubic
  -- condition along unit vectors.
  obtain ⟨δ₁, hδ₁, hs⟩ := hK.exists_pos_forall_mem_of_norm_le hf₁ hf₂
    (O := {A : ℝ × E →L[ℝ] StrongDual ℝ E | Surjective A}) isOpen_setOf_surjective
    fun z hz hz₀ ↦ (h hz hz₀).1
  obtain ⟨δ₂, hδ₂, hc⟩ := exists_pos_forall_ne_zero_of_norm_le hK hf₁ hfH hf₃ h
  refine ⟨min δ₁ δ₂, lt_min hδ₁ hδ₂, fun g hg₁ hg₂ hgH hg₃ z hz hgz ↦ ?_⟩
  -- At a critical point of `g`, the differential of `f` is small.
  have hG : ‖fderiv ℝ (f z.1) z.2‖ ≤ min δ₁ δ₂ := by
    simpa [hgz] using hg₁ z hz
  refine ⟨hs z hz _ (hG.trans (min_le_left _ _)) ((hg₂ z hz).trans (min_le_left _ _)),
    fun v hv hv₃ ↦ ?_⟩
  -- A nonzero kernel vector with vanishing third derivative would give a unit one, on which the
  -- Hessian of `f` is small, since that of `g` kills it.
  by_contra hv₀
  set u : E := ‖v‖⁻¹ • v
  have hu : u ∈ sphere (0 : E) 1 := by simp [u, norm_smul, hv₀]
  have hHu : ‖fderiv ℝ (fderiv ℝ (f z.1)) z.2 u‖ ≤ min δ₁ δ₂ := by
    simpa [u, hv] using hgH z hz u hu
  have h₃u : fderiv ℝ (fderiv ℝ (fderiv ℝ (g z.1))) z.2 u u u = 0 := by simp [u, hv₃]
  exact hc z hz u hu _ (hG.trans (min_le_right _ _)) (hHu.trans (min_le_right _ _))
    ((hg₃ z hz u hu).trans (min_le_right _ _)) h₃u

end Persistence

/-! ### Openness in a parameter -/

section Parameter

variable {Λ : Type*} [NormedAddCommGroup Λ] [NormedSpace ℝ Λ]

/-- The derivatives entering `HasBirthDeathCriticalPointsOn`, read off a family of families
`f p t x` that is jointly `C³` at `(p, z)`, depend continuously on `(p, z)` there; the Hessian and
the third derivative along a vector `u`, `Hess(f p t)_x u` and `D³(f p t)_x (u, u, u)`, depend
continuously on `(p, z, u)`. -/
private theorem continuousAt_derivatives {f : Λ → ℝ → E → ℝ} {p : Λ} {z : ℝ × E}
    (hf : ContDiffAt ℝ 3 (fun q : Λ × (ℝ × E) ↦ f q.1 q.2.1 q.2.2) (p, z)) (u : E) :
    ContinuousAt (fun q : Λ × (ℝ × E) ↦ fderiv ℝ (f q.1 q.2.1) q.2.2) (p, z) ∧
      ContinuousAt (fun q : Λ × (ℝ × E) ↦
        fderiv ℝ (fun w : ℝ × E ↦ fderiv ℝ (f q.1 w.1) w.2) q.2) (p, z) ∧
      ContinuousAt (fun q : Λ × ((ℝ × E) × E) ↦ fderiv ℝ (fderiv ℝ (f q.1 q.2.1.1)) q.2.1.2 q.2.2)
        (p, (z, u)) ∧
      ContinuousAt (fun q : Λ × ((ℝ × E) × E) ↦
        fderiv ℝ (fderiv ℝ (fderiv ℝ (f q.1 q.2.1.1))) q.2.1.2 q.2.2 q.2.2 q.2.2) (p, (z, u)) := by
  -- Cache the operator-space instances of the Hessians before the third derivative layer.
  let : NormedAddCommGroup (E →L[ℝ] E →L[ℝ] ℝ) := inferInstance
  let : NormedSpace ℝ (E →L[ℝ] E →L[ℝ] ℝ) := inferInstance
  -- Regroup the variables as `((p, t), x)`, so that the spatial derivatives are slices.
  have he : ContDiffAt ℝ 3 (fun q : Λ × (ℝ × E) ↦ ((q.1, q.2.1), q.2.2)) (p, z) := by fun_prop
  have hF : ContDiffAt ℝ 3 (fun r : (Λ × ℝ) × E ↦ f r.1.1 r.1.2 r.2) ((p, z.1), z.2) :=
    hf.comp ((p, z.1), z.2) (f := fun r : (Λ × ℝ) × E ↦ (r.1.1, (r.1.2, r.2))) (by fun_prop)
  have h₁ := hF.fderiv_slice (m := 2) (by norm_num)
  have hH := h₁.fderiv_slice (m := 1) (by norm_num)
  have h₃ := hH.fderiv_slice (m := 0) (by norm_num)
  have hG : ContDiffAt ℝ 2 (fun q : Λ × (ℝ × E) ↦ fderiv ℝ (f q.1 q.2.1) q.2.2) (p, z) :=
    ContDiffAt.comp (g := fun r : (Λ × ℝ) × E ↦ fderiv ℝ (fun y ↦ f r.1.1 r.1.2 y) r.2) (p, z)
      h₁ (he.of_le (by norm_num))
  have hH' : ContDiffAt ℝ 1 (fun q : Λ × (ℝ × E) ↦ fderiv ℝ (fderiv ℝ (f q.1 q.2.1)) q.2.2)
      (p, z) :=
    ContDiffAt.comp
      (g := fun r : (Λ × ℝ) × E ↦ fderiv ℝ (fderiv ℝ (fun y ↦ f r.1.1 r.1.2 y)) r.2) (p, z)
      hH (he.of_le (by norm_num))
  have h₂ : ContDiffAt ℝ 1 (fun q : Λ × (ℝ × E) ↦
      fderiv ℝ (fun w : ℝ × E ↦ fderiv ℝ (f q.1 w.1) w.2) q.2) (p, z) :=
    hG.fderiv_slice (m := 1) (by norm_num)
  have hu : ContinuousAt (fun q : Λ × ((ℝ × E) × E) ↦ q.2.2) (p, (z, u)) := by fun_prop
  refine ⟨hG.continuousAt, h₂.continuousAt,
    (hH'.continuousAt.comp_of_eq (f := fun q : Λ × ((ℝ × E) × E) ↦ (q.1, q.2.1)) (by fun_prop)
      rfl).clm_apply hu, ?_⟩
  have hc := h₃.continuousAt.comp_of_eq (x := (p, (z, u)))
    (f := fun q : Λ × ((ℝ × E) × E) ↦ ((q.1, q.2.1.1), q.2.1.2)) (by fun_prop) rfl
  exact ((hc.clm_apply hu).clm_apply hu).clm_apply hu

variable [FiniteDimensional ℝ E]

/-- **Only birth–death degeneracies on a compact set is an open condition in a parameter.** Let
`f p` be one-parameter families of functions on a finite-dimensional real normed space, depending
on a parameter `p` in a real normed space, jointly `C³` in `p`, `t` and `x` at every point of
`{p₀} × K` for a compact set `K ⊆ ℝ × E`. If `f p₀` has only birth–death degeneracies on `K`, then
so does `f p` for every `p` close to `p₀`. -/
theorem HasBirthDeathCriticalPointsOn.eventually_hasBirthDeathCriticalPointsOn
    {f : Λ → ℝ → E → ℝ} {p₀ : Λ} {K : Set (ℝ × E)} (hK : IsCompact K)
    (hf : ∀ z ∈ K, ContDiffAt ℝ 3 (fun q : Λ × (ℝ × E) ↦ f q.1 q.2.1 q.2.2) (p₀, z))
    (h : HasBirthDeathCriticalPointsOn (f p₀) K) :
    ∀ᶠ p in 𝓝 p₀, HasBirthDeathCriticalPointsOn (f p) K := by
  have hc (z : ℝ × E) (hz : z ∈ K) (u : E) := continuousAt_derivatives (hf z hz) u
  have hKS : IsCompact (K ×ˢ sphere (0 : E) 1) := hK.prod (isCompact_sphere 0 1)
  have hH (q : (ℝ × E) × E) (hq : q ∈ K ×ˢ sphere (0 : E) 1) :
      ContinuousAt (fun r : Λ × ((ℝ × E) × E) ↦
        fderiv ℝ (fderiv ℝ (f r.1 r.2.1.1)) r.2.1.2 r.2.2) (p₀, q) :=
    (hc q.1 hq.1 q.2).2.2.1
  have h₃ (q : (ℝ × E) × E) (hq : q ∈ K ×ˢ sphere (0 : E) 1) :
      ContinuousAt (fun r : Λ × ((ℝ × E) × E) ↦
        fderiv ℝ (fderiv ℝ (fderiv ℝ (f r.1 r.2.1.1))) r.2.1.2 r.2.2 r.2.2 r.2.2) (p₀, q) :=
    (hc q.1 hq.1 q.2).2.2.2
  -- The slices at `p₀` of the jointly continuous derivatives are continuous.
  obtain ⟨δ, hδ, hpers⟩ := h.exists_pos_forall_hasBirthDeathCriticalPointsOn (f := f p₀) hK
    (fun z hz ↦ ((hc z hz 0).1.comp_of_eq (f := fun y ↦ (p₀, y)) (by fun_prop) rfl)
      |>.continuousWithinAt)
    (fun z hz ↦ ((hc z hz 0).2.1.comp_of_eq (f := fun y ↦ (p₀, y)) (by fun_prop) rfl)
      |>.continuousWithinAt)
    (fun q hq ↦ ((hH q hq).comp_of_eq (f := fun y ↦ (p₀, y)) (by fun_prop) rfl)
      |>.continuousWithinAt)
    (fun q hq ↦ ((h₃ q hq).comp_of_eq (f := fun y ↦ (p₀, y)) (by fun_prop) rfl)
      |>.continuousWithinAt)
  -- Near `p₀`, the four derivatives stay within `δ` of their values at `p₀`, uniformly.
  filter_upwards [(Metric.tendstoUniformlyOn_iff
      (F := fun (p : Λ) (z : ℝ × E) ↦ fderiv ℝ (f p z.1) z.2)).1
      (hK.tendstoUniformlyOn_of_continuousAt fun z hz ↦ (hc z hz 0).1) δ hδ,
    (Metric.tendstoUniformlyOn_iff
      (F := fun (p : Λ) (z : ℝ × E) ↦ fderiv ℝ (fun w : ℝ × E ↦ fderiv ℝ (f p w.1) w.2) z)).1
      (hK.tendstoUniformlyOn_of_continuousAt fun z hz ↦ (hc z hz 0).2.1) δ hδ,
    (Metric.tendstoUniformlyOn_iff (F := fun (p : Λ) (q : (ℝ × E) × E) ↦
      fderiv ℝ (fderiv ℝ (f p q.1.1)) q.1.2 q.2)).1
      (hKS.tendstoUniformlyOn_of_continuousAt hH) δ hδ,
    (Metric.tendstoUniformlyOn_iff (F := fun (p : Λ) (q : (ℝ × E) × E) ↦
      fderiv ℝ (fderiv ℝ (fderiv ℝ (f p q.1.1))) q.1.2 q.2 q.2 q.2)).1
      (hKS.tendstoUniformlyOn_of_continuousAt h₃) δ hδ]
    with p h₁ h₂ hH h₃
  refine hpers (f p) (fun z hz ↦ ?_) (fun z hz ↦ ?_) (fun z hz u hu ↦ ?_) fun z hz u hu ↦ ?_
  · rw [dist_comm]
    exact (h₁ z hz).le
  · rw [dist_comm]
    exact (h₂ z hz).le
  · rw [dist_comm]
    exact (hH (z, u) ⟨hz, hu⟩).le
  · rw [dist_comm]
    exact (h₃ (z, u) ⟨hz, hu⟩).le

end Parameter

/-! ### Polynomial perturbations -/

section Cubic

variable [FiniteDimensional ℝ E] {f : ℝ → E → ℝ}

/-- **The cubic perturbations keeping only birth–death degeneracies form an open set.** Let `f` be
a one-parameter family of functions on a finite-dimensional real normed space, jointly `C³` at
every point of a compact set `K ⊆ ℝ × E`. The coefficients `p` of the polynomials of degree at
most three for which `f t - cubicPerturbation p` has only birth–death degeneracies on `K` form an
open set. -/
theorem isOpen_setOf_hasBirthDeathCriticalPointsOn_sub_cubicPerturbation {K : Set (ℝ × E)}
    (hK : IsCompact K) (hf : ∀ z ∈ K, ContDiffAt ℝ 3 (uncurry f) z) :
    IsOpen {p : CubicCoefficients E |
      HasBirthDeathCriticalPointsOn (fun t y ↦ f t y - cubicPerturbation p y) K} := by
  refine isOpen_iff_mem_nhds.2 fun p₀ hp₀ ↦
    HasBirthDeathCriticalPointsOn.eventually_hasBirthDeathCriticalPointsOn
      (f := fun p t y ↦ f t y - cubicPerturbation p y) hK (fun z hz ↦ ?_) hp₀
  have hP : ContDiffAt ℝ 3 (fun q : CubicCoefficients E × (ℝ × E) ↦
      cubicPerturbation q.1 q.2.2) (p₀, z) :=
    (contDiff_cubicPerturbation.comp (contDiff_fst.prodMk contDiff_snd.snd)).contDiffAt
  exact ((hf z hz).comp (p₀, z) contDiffAt_snd).sub hP

/-- **Almost every cubic perturbation leaves only birth–death degeneracies.** Let `f` be a
one-parameter family of functions on a finite-dimensional real normed space, jointly `C⁴` at every
point of a set `W ⊆ ℝ × E`. For a Haar measure `ν` on the coefficients and `ν`-almost every `p`,
the family `f t - cubicPerturbation p` has only birth–death degeneracies on `W`. This combines
`TauCeti.ae_forall_surjective_fderiv_fderiv_sub_cubicPerturbation` and
`TauCeti.ae_forall_fderiv_fderiv_fderiv_sub_cubicPerturbation_apply_ne_zero`. -/
theorem ae_hasBirthDeathCriticalPointsOn_sub_cubicPerturbation
    [MeasurableSpace (CubicCoefficients E)] [BorelSpace (CubicCoefficients E)]
    (ν : MeasureTheory.Measure (CubicCoefficients E)) [ν.IsAddHaarMeasure] {W : Set (ℝ × E)}
    (hf : ∀ z ∈ W, ContDiffAt ℝ 4 (uncurry f) z) :
    ∀ᵐ p ∂ν, HasBirthDeathCriticalPointsOn (fun t y ↦ f t y - cubicPerturbation p y) W := by
  filter_upwards [ae_forall_surjective_fderiv_fderiv_sub_cubicPerturbation ν
      fun z hz ↦ (hf z hz).of_le (by norm_num),
    ae_forall_fderiv_fderiv_fderiv_sub_cubicPerturbation_apply_ne_zero ν hf]
    with p hs h₃ z hz hz₀
  refine ⟨hs z hz hz₀, fun v hv hv₃ ↦ ?_⟩
  by_contra hv₀
  exact h₃ z hz hz₀ v hv₀ hv hv₃

/-- **The cubic perturbations leaving only birth–death degeneracies form a dense set.** Let `f` be
a one-parameter family of functions on a finite-dimensional real normed space, jointly `C⁴` at
every point of a set `W ⊆ ℝ × E`. The coefficients `p` of the polynomials of degree at most three
for which `f t - cubicPerturbation p` has only birth–death degeneracies on `W` form a dense set:
by `TauCeti.ae_hasBirthDeathCriticalPointsOn_sub_cubicPerturbation`, their complement is a Haar
null set. -/
theorem dense_setOf_hasBirthDeathCriticalPointsOn_sub_cubicPerturbation {W : Set (ℝ × E)}
    (hf : ∀ z ∈ W, ContDiffAt ℝ 4 (uncurry f) z) :
    Dense {p : CubicCoefficients E |
      HasBirthDeathCriticalPointsOn (fun t y ↦ f t y - cubicPerturbation p y) W} := by
  borelize (CubicCoefficients E)
  exact MeasureTheory.Measure.dense_of_ae
    (ae_hasBirthDeathCriticalPointsOn_sub_cubicPerturbation MeasureTheory.Measure.addHaar hf)

/-- **Generic cubic perturbations leave only birth–death degeneracies.** Let `f` be a jointly `C⁴`
one-parameter family of functions on a finite-dimensional real normed space. For a residual set of
coefficients `p`, the family `f t - cubicPerturbation p` has only birth–death degeneracies on all
of `ℝ × E`: the good coefficients for each closed ball form an open dense set, and countably many
balls exhaust `ℝ × E`. -/
theorem mem_residual_setOf_hasBirthDeathCriticalPointsOn_sub_cubicPerturbation
    (hf : ContDiff ℝ 4 (uncurry f)) :
    {p : CubicCoefficients E |
      HasBirthDeathCriticalPointsOn (fun t y ↦ f t y - cubicPerturbation p y) univ} ∈
      residual (CubicCoefficients E) := by
  have hball (n : ℕ) : {p : CubicCoefficients E | HasBirthDeathCriticalPointsOn
      (fun t y ↦ f t y - cubicPerturbation p y) (closedBall 0 n)} ∈ residual _ :=
    residual_of_dense_open (isOpen_setOf_hasBirthDeathCriticalPointsOn_sub_cubicPerturbation
      (isCompact_closedBall 0 n) fun z _ ↦ (hf.of_le (by norm_num)).contDiffAt)
      (dense_setOf_hasBirthDeathCriticalPointsOn_sub_cubicPerturbation fun z _ ↦ hf.contDiffAt)
  refine Filter.mem_of_superset (countable_iInter_mem.2 hball) fun p hp z _ ↦ ?_
  obtain ⟨n, hn⟩ := exists_nat_ge (dist z 0)
  exact mem_iInter.1 hp n (mem_closedBall.2 hn)

end Cubic

end TauCeti
