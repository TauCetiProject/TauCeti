/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Flow.Parametric
public import TauCeti.Geometry.Manifold.Flow.TimeDependent

/-!
# Time-dependent flows of families of vector fields

Let `X a` be a family of time-dependent vector fields on a manifold `M`, indexed by the points `a`
of a parameter manifold `N`, and jointly `C^n` in the parameter, the time and the point. The
time-dependent flow `φ^a_{s, t} = TauCeti.timeDependentFlowOf (X a) s t` of each field is read off
the flow of its suspension `(t, x) ↦ (1, X a t x)` on `ℝ × M`
(`TauCeti.timeDependentSuspensionField`). These suspensions form a jointly `C^n` family of
autonomous vector fields on `ℝ × M` indexed by `N`
(`TauCeti.contMDiff_timeDependentSuspensionField_param`), to which the regularity of the flows of
families of vector fields (`TauCeti.contMDiffAt_flowOf_param`) applies. So, on a boundaryless
manifold modelled on a complete normed space, for `1 ≤ n`:

* the quadruples `(a, (s, t), x)` such that the flow of `X a` from time `s` to time `t` is defined
  at `x` form a neighbourhood of each of their points
  (`TauCeti.eventually_mem_timeDependentFlowDomain_param`);
* the flow is jointly `C^n` in the parameter, the two times and the point wherever it is defined
  (`TauCeti.contMDiffAt_timeDependentFlowOf_param`);
* on a compact manifold, where every flow is defined at all times, the flow is jointly `C^n`
  everywhere (`TauCeti.contMDiff_timeDependentFlowOf_param`), and in particular so is the family
  `(a, x) ↦ φ^a_{s, t} x` of time maps between two fixed times
  (`TauCeti.contMDiff_uncurry_timeDependentFlowOf_param`).

The last statement is the regularity in the parameter of a one-parameter family of transition
diffeomorphisms `φ^λ_{s, t}`, which is what the transversality theory of one-parameter families of
time-dependent vector fields differentiates.

## References

* J. M. Lee, *Introduction to Smooth Manifolds*, 2nd ed., Graduate Texts in Mathematics 218,
  Springer, 2013, Theorem 9.48 (time-dependent flows, through the suspension) and Appendix D
  (smooth dependence of solutions of ordinary differential equations on parameters).
-/

public section

noncomputable section

open Filter Set
open scoped ContDiff Manifold Topology

namespace TauCeti

variable {E H M F G N : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [TopologicalSpace G] {J : ModelWithCorners ℝ F G}
  [TopologicalSpace N] [ChartedSpace G N]
  {X : N → ℝ → (x : M) → TangentSpace I x}

/-- **The suspensions of a family of time-dependent fields form a family.** If the family `X` of
time-dependent vector fields on `M` is jointly `C^n` in the parameter, the time and the point,
then the suspensions `(t, x) ↦ (1, X a t x)` form a jointly `C^n` family of vector fields on
`ℝ × M` indexed by `N`. -/
theorem contMDiff_timeDependentSuspensionField_param [IsManifold I 1 M] {n : ℕ∞ω}
    (hX : ContMDiff (J.prod (𝓘(ℝ).prod I)) I.tangent n
      (fun z : N × ℝ × M ↦ (⟨z.2.2, X z.1 z.2.1 z.2.2⟩ : TangentBundle I M))) :
    ContMDiff (J.prod (𝓘(ℝ).prod I)) (𝓘(ℝ).prod I).tangent n
      (fun z : N × ℝ × M ↦ (⟨z.2, timeDependentSuspensionField (X z.1) z.2⟩ :
        TangentBundle (𝓘(ℝ).prod I) (ℝ × M))) := by
  -- The suspension is the field `(1, X a)`.
  convert contMDiff_const_prod_field_param 1 hX using 3 with z
  congr 1
  exact Prod.ext (timeDependentSuspensionField_fst _ _) (timeDependentSuspensionField_snd _ _)

section Flow

variable [T2Space M] [BoundarylessManifold I M] [CompleteSpace E] [CompleteSpace F] [T2Space N]
  [BoundarylessManifold J N] [IsManifold I 1 M] [IsManifold J 1 N] {a₀ : N} {s t : ℝ} {x : M}

/-- **The domain of the flows of a family is open.** If the family `X` of time-dependent vector
fields is jointly `C¹` and the flow of `X a₀` from time `s` to time `t` is defined at `x`, then for
`(a, (s', t'), x')` near `(a₀, (s, t), x)` the flow of `X a` from time `s'` to time `t'` is
defined at `x'`. -/
theorem eventually_mem_timeDependentFlowDomain_param
    (hX : ContMDiff (J.prod (𝓘(ℝ).prod I)) I.tangent 1
      (fun z : N × ℝ × M ↦ (⟨z.2.2, X z.1 z.2.1 z.2.2⟩ : TangentBundle I M)))
    (h : ((s, t), x) ∈ timeDependentFlowDomain (X a₀)) :
    ∀ᶠ y in 𝓝 (a₀, (s, t), x), y.2 ∈ timeDependentFlowDomain (X y.1) := by
  -- Read `(a, (s', t'), x')` as the point `(a, t' - s', (s', x'))` of the parameter, the time and
  -- the point of the family of suspensions.
  have hg : Continuous fun y : N × (ℝ × ℝ) × M ↦ (y.1, y.2.1.2 - y.2.1.1, (y.2.1.1, y.2.2)) := by
    fun_prop
  filter_upwards [(hg.tendsto (a₀, (s, t), x)).eventually
    (eventually_mem_flowDomain_param (v := fun a ↦ timeDependentSuspensionField (X a))
      (contMDiff_timeDependentSuspensionField_param hX) (mem_timeDependentFlowDomain.1 h))]
    with y hy
  exact mem_timeDependentFlowDomain.2 hy

/-- **The flows of a family are jointly `C^n`.** If the family `X` of time-dependent vector fields
is jointly `C^n` in the parameter, the time and the point, with `1 ≤ n`, and the flow of `X a₀`
from time `s` to time `t` is defined at `x`, then `(a, (s', t'), x') ↦ φ^a_{s', t'} x'` is `C^n` at
`(a₀, (s, t), x)`. -/
theorem contMDiffAt_timeDependentFlowOf_param {n : ℕ∞} (hn : 1 ≤ n) [IsManifold I n M]
    [IsManifold J n N]
    (hX : ContMDiff (J.prod (𝓘(ℝ).prod I)) I.tangent n
      (fun z : N × ℝ × M ↦ (⟨z.2.2, X z.1 z.2.1 z.2.2⟩ : TangentBundle I M)))
    (h : ((s, t), x) ∈ timeDependentFlowDomain (X a₀)) :
    ContMDiffAt (J.prod ((𝓘(ℝ).prod 𝓘(ℝ)).prod I)) I n
      (fun y : N × (ℝ × ℝ) × M ↦ timeDependentFlowOf (X y.1) y.2.1.1 y.2.1.2 y.2.2)
      (a₀, (s, t), x) := by
  have hflow := contMDiffAt_flowOf_param (v := fun a ↦ timeDependentSuspensionField (X a)) hn
    (contMDiff_timeDependentSuspensionField_param hX) (mem_timeDependentFlowDomain.1 h)
  have hs : ContMDiff (J.prod ((𝓘(ℝ).prod 𝓘(ℝ)).prod I)) 𝓘(ℝ) n
      (fun y : N × (ℝ × ℝ) × M ↦ y.2.1.1) :=
    contMDiff_fst.comp (contMDiff_fst.comp contMDiff_snd)
  have ht : ContMDiff (J.prod ((𝓘(ℝ).prod 𝓘(ℝ)).prod I)) 𝓘(ℝ) n
      (fun y : N × (ℝ × ℝ) × M ↦ y.2.1.2) :=
    contMDiff_snd.comp (contMDiff_fst.comp contMDiff_snd)
  have hg : ContMDiff (J.prod ((𝓘(ℝ).prod 𝓘(ℝ)).prod I)) (J.prod (𝓘(ℝ).prod (𝓘(ℝ).prod I))) n
      (fun y : N × (ℝ × ℝ) × M ↦ (y.1, y.2.1.2 - y.2.1.1, (y.2.1.1, y.2.2))) :=
    contMDiff_fst.prodMk ((ht.sub hs).prodMk (hs.prodMk (contMDiff_snd.comp contMDiff_snd)))
  -- The flow of `X a` from `s'` to `t'` is the space component of the flow of the suspension of
  -- `X a` for time `t' - s'` from `(s', x')`.
  refine (contMDiffAt_snd.comp _ (hflow.comp
    (f := fun y : N × (ℝ × ℝ) × M ↦ (y.1, y.2.1.2 - y.2.1.1, (y.2.1.1, y.2.2))) _
      hg.contMDiffAt)).congr_of_eventuallyEq ?_
  exact Eventually.of_forall fun y ↦ timeDependentFlowOf_def

variable [CompactSpace M]

/-- **The flows of a family on a compact manifold are jointly `C^n`.** On a compact manifold, if
the family `X` of time-dependent vector fields is jointly `C^n` in the parameter, the time and the
point, with `1 ≤ n`, then `(a, (s, t), x) ↦ φ^a_{s, t} x` is `C^n`. -/
theorem contMDiff_timeDependentFlowOf_param {n : ℕ∞} (hn : 1 ≤ n) [IsManifold I n M]
    [IsManifold J n N]
    (hX : ContMDiff (J.prod (𝓘(ℝ).prod I)) I.tangent n
      (fun z : N × ℝ × M ↦ (⟨z.2.2, X z.1 z.2.1 z.2.2⟩ : TangentBundle I M))) :
    ContMDiff (J.prod ((𝓘(ℝ).prod 𝓘(ℝ)).prod I)) I n
      (fun y : N × (ℝ × ℝ) × M ↦ timeDependentFlowOf (X y.1) y.2.1.1 y.2.1.2 y.2.2) := by
  rintro ⟨a, ⟨s, t⟩, x⟩
  -- Each field of the family is `C¹`, so on the compact manifold its flow is defined everywhere.
  have hXa : ContMDiff (𝓘(ℝ).prod I) I.tangent 1
      (fun p : ℝ × M ↦ (⟨p.2, X a p.1 p.2⟩ : TangentBundle I M)) :=
    (hX.of_le (by exact_mod_cast hn)).comp (contMDiff_const.prodMk contMDiff_id)
  exact contMDiffAt_timeDependentFlowOf_param hn hX
    (mem_timeDependentFlowDomain.2
      ((isCompleteVectorField_timeDependentSuspensionField_of_compactSpace hXa).mem_flowDomain _ _))

/-- **The time maps of the flows of a family on a compact manifold are jointly `C^n`.** On a
compact manifold, if the family `X` of time-dependent vector fields is jointly `C^n` in the
parameter, the time and the point, with `1 ≤ n`, then for all times `s` and `t` the map
`(a, x) ↦ φ^a_{s, t} x` is `C^n`. -/
theorem contMDiff_uncurry_timeDependentFlowOf_param {n : ℕ∞} (hn : 1 ≤ n) [IsManifold I n M]
    [IsManifold J n N]
    (hX : ContMDiff (J.prod (𝓘(ℝ).prod I)) I.tangent n
      (fun z : N × ℝ × M ↦ (⟨z.2.2, X z.1 z.2.1 z.2.2⟩ : TangentBundle I M))) (s t : ℝ) :
    ContMDiff (J.prod I) I n (Function.uncurry fun a ↦ timeDependentFlowOf (X a) s t) :=
  (contMDiff_timeDependentFlowOf_param hn hX).comp
    (contMDiff_fst.prodMk ((contMDiff_const (c := (s, t))).prodMk contMDiff_snd))

end Flow

end TauCeti
