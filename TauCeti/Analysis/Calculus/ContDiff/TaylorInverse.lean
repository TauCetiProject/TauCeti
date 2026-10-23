/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Calculus.ContDiff.FaaDiBruno

/-!
# Recovering inverse Taylor coefficients

In the Faà di Bruno formula, the partition into singletons is the only term involving the
highest coefficient of the outer series. All other terms involve strictly lower outer
coefficients. If the linear term of the inner series admits a continuous right inverse, this
gives a recursive formula for the outer coefficients from the composite. It also proves their
continuous dependence, the algebraic input to continuity of inversion in differentiable map spaces.

We use Mathlib's ordered-partition formulation of the Faà di Bruno formula, rather than
power-series composition: the coefficients here represent derivatives without factorials.
-/

public section

open Filter Topology

namespace OrderedFinpartition

/-- The sizes of the parts of an ordered partition add up to the size of the ground set. -/
@[simp]
theorem sum_partSize {n : ℕ} (c : OrderedFinpartition n) : ∑ i, c.partSize i = n := by
  simpa using c.sum_sigma_eq_sum (fun _ ↦ (1 : ℕ))

/-- A partition has as many parts as elements exactly when it is the singleton partition. -/
@[simp]
theorem length_eq_iff {n : ℕ} (c : OrderedFinpartition n) :
    c.length = n ↔ c = atomic n := by
  constructor
  · intro h
    have hs (i : Fin c.length) : c.partSize i = 1 := by
      have he : (∑ _ : Fin c.length, (1 : ℕ)) = ∑ j, c.partSize j := by
        simp [h]
      exact ((Finset.sum_eq_sum_iff_of_le (fun j _ ↦ c.partSize_pos j)).mp he i
        (Finset.mem_univ i)).symm
    rcases c with ⟨l, s, hp, e, hm, ho, hd, hc⟩
    dsimp at h hs
    subst l
    obtain rfl : s = fun _ ↦ 1 := funext hs
    have he : (fun i ↦ e i 0) = id := ho.eq_id
    refine OrderedFinpartition.ext (y := atomic n) rfl (heq_of_eq rfl) ?_
    apply heq_of_eq
    funext i j
    have hj : j = 0 := Subsingleton.elim _ _
    simpa only [hj, id_eq, atomic_emb] using congrFun he i
  · rintro rfl
    rfl

/-- A partition other than the singleton partition has strictly fewer parts than elements. -/
theorem length_lt_of_ne_atomic {n : ℕ} (c : OrderedFinpartition n) (hc : c ≠ atomic n) :
    c.length < n :=
  lt_of_le_of_ne c.length_le (fun h ↦ hc (c.length_eq_iff.mp h))

end OrderedFinpartition

namespace FormalMultilinearSeries

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  {G : Type*} [NormedAddCommGroup G] [NormedSpace 𝕜 G]

/-- The singleton partition term of Taylor composition precomposes each variable with the
linear coefficient of the inner series. -/
@[simp]
theorem compAlongOrderedFinpartition_atomic (q : FormalMultilinearSeries 𝕜 F G)
    (p : FormalMultilinearSeries 𝕜 E F) (m : ℕ) :
    q.compAlongOrderedFinpartition p (OrderedFinpartition.atomic m) =
      (q m).compContinuousLinearMap (fun _ ↦ continuousMultilinearCurryFin1 𝕜 E F (p 1)) := by
  ext v
  simp only [compAlongOrderedFinpartition_apply, OrderedFinpartition.applyOrderedFinpartition_apply,
    OrderedFinpartition.atomic_emb, ContinuousMultilinearMap.compContinuousLinearMap_apply,
    continuousMultilinearCurryFin1_apply]
  rfl

/-- Recover the highest outer Taylor coefficient from the composite and the lower outer
coefficients, using a right inverse of the inner linear coefficient. -/
theorem eq_taylorComp_sub_sum_comp (q : FormalMultilinearSeries 𝕜 F G)
    (p : FormalMultilinearSeries 𝕜 E F) (m : ℕ) (A : F →L[𝕜] E)
    (hA : (continuousMultilinearCurryFin1 𝕜 E F (p 1)).comp A = .id 𝕜 F) :
    q m = ((q.taylorComp p m) -
      ∑ c ∈ Finset.univ.erase (OrderedFinpartition.atomic m),
        q.compAlongOrderedFinpartition p c).compContinuousLinearMap (fun _ ↦ A) := by
  classical
  have hs := Finset.sum_erase_add (Finset.univ (α := OrderedFinpartition m))
    (fun c ↦ q.compAlongOrderedFinpartition p c) (Finset.mem_univ (OrderedFinpartition.atomic m))
  rw [compAlongOrderedFinpartition_atomic] at hs
  have he : q.taylorComp p m -
      ∑ c ∈ Finset.univ.erase (OrderedFinpartition.atomic m),
        q.compAlongOrderedFinpartition p c =
      (q m).compContinuousLinearMap (fun _ ↦ continuousMultilinearCurryFin1 𝕜 E F (p 1)) := by
    apply sub_eq_iff_eq_add.mpr
    simpa only [FormalMultilinearSeries.taylorComp, add_comm] using hs.symm
  rw [he]
  ext v
  simpa only [ContinuousMultilinearMap.compContinuousLinearMap_apply,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.id_apply] using
    congrArg (q m) (funext fun i ↦ congrArg (fun L : F →L[𝕜] F ↦ L (v i)) hA).symm

end FormalMultilinearSeries

namespace TauCeti

/-- The zeroth outer Taylor coefficient converges whenever the zeroth composite coefficient
converges, without any assumption on the inner series or an inverse of its linear term. -/
theorem tendsto_apply_zero_of_taylorComp
    {𝕜 : Type*} [NontriviallyNormedField 𝕜]
    {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
    {G : Type*} [NormedAddCommGroup G] [NormedSpace 𝕜 G]
    {α : Type*} {l : Filter α}
    {q : α → FormalMultilinearSeries 𝕜 F G} {p : α → FormalMultilinearSeries 𝕜 E F}
    {q₀ : FormalMultilinearSeries 𝕜 F G} {p₀ : FormalMultilinearSeries 𝕜 E F}
    (hcomp : Tendsto (fun a ↦ (q a).taylorComp (p a) 0) l (𝓝 (q₀.taylorComp p₀ 0))) :
    Tendsto (fun a ↦ q a 0) l (𝓝 (q₀ 0)) := by
  classical
  have he (q : FormalMultilinearSeries 𝕜 F G) (p : FormalMultilinearSeries 𝕜 E F) :
      (continuousMultilinearCurryFin0 𝕜 F G).symm
        (continuousMultilinearCurryFin0 𝕜 E G (q.taylorComp p 0)) = q 0 := by
    apply (continuousMultilinearCurryFin0 𝕜 F G).injective
    simp [FormalMultilinearSeries.taylorComp, OrderedFinpartition.default_eq,
      FormalMultilinearSeries.compAlongOrderedFinpartition_atomic,
      ContinuousMultilinearMap.compContinuousLinearMap_apply]
  simpa only [Function.comp_def, he] using
    ((continuousMultilinearCurryFin0 𝕜 F G).symm.continuous.tendsto _).comp
      (((continuousMultilinearCurryFin0 𝕜 E G).continuous.tendsto _).comp hcomp)

end TauCeti

/-- A positive-order Taylor coefficient of the outer series converges if the composite
coefficient, the positive lower outer coefficients, the positive inner coefficients up to
that order, and a right inverse of the inner linear coefficient converge. -/
theorem Filter.Tendsto.of_taylorComp
    {𝕜 : Type*} [NontriviallyNormedField 𝕜]
    {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
    {G : Type*} [NormedAddCommGroup G] [NormedSpace 𝕜 G]
    {α : Type*} {l : Filter α}
    {q : α → FormalMultilinearSeries 𝕜 F G} {p : α → FormalMultilinearSeries 𝕜 E F}
    {q₀ : FormalMultilinearSeries 𝕜 F G} {p₀ : FormalMultilinearSeries 𝕜 E F} {m : ℕ}
    {A : α → F →L[𝕜] E} {A₀ : F →L[𝕜] E}
    (hm : 0 < m)
    (hq : ∀ k, 0 < k → k < m → Tendsto (fun a ↦ q a k) l (𝓝 (q₀ k)))
    (hp : ∀ k, 0 < k → k ≤ m → Tendsto (fun a ↦ p a k) l (𝓝 (p₀ k)))
    (hcomp : Tendsto (fun a ↦ (q a).taylorComp (p a) m) l (𝓝 (q₀.taylorComp p₀ m)))
    (hA : Tendsto A l (𝓝 A₀))
    (hAp : ∀ᶠ a in l, (continuousMultilinearCurryFin1 𝕜 E F (p a 1)).comp (A a) = .id 𝕜 F)
    (hA₀ : (continuousMultilinearCurryFin1 𝕜 E F (p₀ 1)).comp A₀ = .id 𝕜 F) :
    Tendsto (fun a ↦ q a m) l (𝓝 (q₀ m)) := by
  classical
  have hsum : Tendsto (fun a ↦
      ∑ c ∈ Finset.univ.erase (OrderedFinpartition.atomic m),
        (q a).compAlongOrderedFinpartition (p a) c) l
      (𝓝 (∑ c ∈ Finset.univ.erase (OrderedFinpartition.atomic m),
        q₀.compAlongOrderedFinpartition p₀ c)) := by
    refine tendsto_finsetSum _ fun c hc ↦ ?_
    have hB := ((c.compAlongOrderedFinpartitionL 𝕜 E F G).continuous.tendsto _).comp
      (hq c.length (c.length_pos hm)
        (c.length_lt_of_ne_atomic (Finset.mem_erase.mp hc).1))
    have hP : Tendsto (fun a i ↦ p a (c.partSize i)) l (𝓝 fun i ↦ p₀ (c.partSize i)) :=
      tendsto_pi_nhds.2 fun i ↦ hp _ (c.partSize_pos i) (c.partSize_le i)
    exact (continuous_eval.tendsto _).comp (hB.prodMk_nhds hP)
  have hAl : Tendsto (fun a ↦ fun _ : Fin m ↦ A a) l (𝓝 fun _ : Fin m ↦ A₀) :=
    tendsto_pi_nhds.mpr fun _ ↦ hA
  have hpre := ((ContinuousMultilinearMap.compContinuousLinearMapContinuousMultilinear
    𝕜 (fun _ : Fin m ↦ F) (fun _ ↦ E) G).coe_continuous.tendsto _).comp hAl
  have h : Tendsto (fun a ↦ ((q a).taylorComp (p a) m -
      ∑ c ∈ Finset.univ.erase (OrderedFinpartition.atomic m),
        (q a).compAlongOrderedFinpartition (p a) c).compContinuousLinearMap (fun _ ↦ A a)) l
      (𝓝 ((q₀.taylorComp p₀ m -
        ∑ c ∈ Finset.univ.erase (OrderedFinpartition.atomic m),
          q₀.compAlongOrderedFinpartition p₀ c).compContinuousLinearMap (fun _ ↦ A₀))) := by
    simpa only [Function.comp_def,
      ContinuousMultilinearMap.compContinuousLinearMapContinuousMultilinear_apply_apply]
      using (isBoundedBilinearMap_apply.continuous.tendsto _).comp
        (hpre.prodMk_nhds (hcomp.sub hsum))
  rw [← q₀.eq_taylorComp_sub_sum_comp p₀ m A₀ hA₀] at h
  apply h.congr'
  filter_upwards [hAp] with a ha
  exact ((q a).eq_taylorComp_sub_sum_comp (p a) m (A a) ha).symm
