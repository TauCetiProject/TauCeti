/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.FDeriv.Prod
public import Mathlib.Analysis.Normed.Operator.Prod
public import TauCeti.Analysis.Normed.Operator.Holder
public import TauCeti.Topology.MetricSpace.Holder
import TauCeti.Analysis.Calculus.FDeriv.Prod
import TauCeti.Analysis.Normed.Operator.Prod

/-!
# Superposition operators on Hölder functions

For a function `A` of two variables and a function `u`, the *superposition* of `A` and `u` is
`x ↦ A x (u x)`. In a quasilinear equation `-div (A (x, u) ∇u) = f` it is the coefficient field
`a (x) = A (x, u (x))` obtained by freezing the solution. Regularity of a solution is bootstrapped
by passing Hölder regularity from `u` to `a` and back through the linear Schauder estimates. This
file proves the composition rules this needs, with explicit constants that depend on `A` only
through its bounds on `s ×ˢ t`, where `t` is a set containing the values of `u` on `s`, such as a
bounded range `[-M, M]`. The chain rule for `x ↦ A x (u x)` itself, and the bound
`‖DA‖ max 1 ‖Du‖` on its derivative, are `HasFDerivAt.superposition` and
`TauCeti.norm_fderiv_comp_graph_le`.

* **Order zero** (`HolderOnWith.superposition`). If `u` is `r`-Hölder on `s` with constant `Cᵤ`
  and values in `t`, and `A` is `r`-Hölder in its first variable with constant `Hₓ` and Lipschitz
  in its second variable with constant `L`, then `x ↦ A x (u x)` is `r`-Hölder on `s` with
  constant `Hₓ + L Cᵤ`: a Lipschitz function of a `C^{0,r}` function is `C^{0,r}`.
* **Order one** (`HolderOnWith.fderiv_superposition`). Let `edist x y ≤ D` on `s`, and let
  `γ ≤ α` and `γ ≤ β`. If `DA` is `α`-Hölder with constant `C_A` and bounded by `M_A` on
  `s ×ˢ t`, and `u` is Lipschitz on `s` with constant `L` and has a derivative that is `β`-Hölder
  with constant `C_u` and bounded by `M_u` on `s`, then the derivative of `x ↦ A x (u x)` is
  `γ`-Hölder on `s` with constant

  `max 1 M_u · C_A (max 1 L)^α D^(α - γ) + M_A C_u D^(β - γ)`.

  So `A ∈ C^{1,α}` and `u ∈ C^{1,β}` give `A (·, u) ∈ C^{1, min α β}` on bounded sets.

## References

* D. Gilbarg and N. S. Trudinger, *Elliptic Partial Differential Equations of Second Order*,
  Section 4.1 (Hölder spaces).
* R. de la Llave and R. Obaya, *Regularity of the composition operator in spaces of Hölder
  functions*, Discrete Contin. Dynam. Systems **5** (1999), 157–184.
-/

public section

open Set
open scoped NNReal ENNReal

section Metric

variable {X Y Z : Type*} [PseudoEMetricSpace X] [PseudoEMetricSpace Y] [PseudoEMetricSpace Z]

/-- **Superposition of Hölder functions.** Let `u` be `r`-Hölder on `s` with constant `Cᵤ` and
values in `t`. If `A x y` is `r`-Hölder in `x ∈ s` with constant `Hₓ` for each `y ∈ t`, and
Lipschitz in `y ∈ t` with constant `L` for each `x ∈ s`, then `x ↦ A x (u x)` is `r`-Hölder on `s`
with constant `Hₓ + L Cᵤ`. -/
theorem HolderOnWith.superposition {A : X → Y → Z} {u : X → Y} {s : Set X} {t : Set Y}
    {r Cu Hx L : ℝ≥0} (hu : HolderOnWith Cu r u s) (hut : MapsTo u s t)
    (hAx : ∀ y ∈ t, HolderOnWith Hx r (fun x ↦ A x y) s)
    (hAy : ∀ x ∈ s, LipschitzOnWith L (A x) t) :
    HolderOnWith (Hx + L * Cu) r (fun x ↦ A x (u x)) s := by
  intro x hx y hy
  calc edist (A x (u x)) (A y (u y))
      ≤ edist (A x (u x)) (A y (u x)) + edist (A y (u x)) (A y (u y)) := edist_triangle _ _ _
    _ ≤ Hx * edist x y ^ (r : ℝ) + L * (Cu * edist x y ^ (r : ℝ)) := by
        gcongr
        · exact (hAx (u x) (hut hx)).edist_le hx hy
        · exact (hAy y hy (hut hx) (hut hy)).trans (by gcongr; exact hu.edist_le hx hy)
    _ = ((Hx + L * Cu : ℝ≥0) : ℝ≥0∞) * edist x y ^ (r : ℝ) := by
        push_cast
        ring

end Metric

section Normed

variable {𝕜 E F G : Type*} [NontriviallyNormedField 𝕜] [NormedAddCommGroup E]
  [NormedSpace 𝕜 E] [NormedAddCommGroup F] [NormedSpace 𝕜 F] [NormedAddCommGroup G]
  [NormedSpace 𝕜 G]

/-- **Hölder continuity of the derivative of a superposition.** Let `edist x y ≤ D` on `s`, and
let `γ ≤ α` and `γ ≤ β`. Suppose that `A`, as a function on `E × F`, has derivative `A' p` at every
`p ∈ s ×ˢ t`, with `A'` `α`-Hölder with constant `C_A` and bounded by `M_A` there, and that `u`
maps `s` to `t`, is Lipschitz on `s` with constant `L` and has derivative `u' x` at every `x ∈ s`,
with `u'` `β`-Hölder with constant `C_u` and bounded by `M_u` on `s`. Then the derivative of
`x ↦ A x (u x)` is `γ`-Hölder on `s`, with constant
`max 1 M_u · C_A (max 1 L)^α D^(α - γ) + M_A C_u D^(β - γ)`. -/
theorem HolderOnWith.fderiv_superposition {A : E → F → G} {A' : E × F → E × F →L[𝕜] G}
    {u : E → F} {u' : E → E →L[𝕜] F} {s : Set E} {t : Set F}
    {α β γ CA MA L Cu Mu D : ℝ≥0} (hA' : HolderOnWith CA α A' (s ×ˢ t))
    (hA : ∀ p ∈ s ×ˢ t, HasFDerivAt (Function.uncurry A) (A' p) p)
    (hA'_le : ∀ p ∈ s ×ˢ t, ‖A' p‖ ≤ MA) (hu' : HolderOnWith Cu β u' s)
    (hu : ∀ x ∈ s, HasFDerivAt u (u' x) x) (hu'_le : ∀ x ∈ s, ‖u' x‖ ≤ Mu)
    (hL : LipschitzOnWith L u s) (hut : MapsTo u s t) (hs : ∀ x ∈ s, ∀ y ∈ s, edist x y ≤ D)
    (hγα : γ ≤ α) (hγβ : γ ≤ β) :
    HolderOnWith (max 1 Mu * (CA * max 1 L ^ (α : ℝ) * D ^ (α - γ : ℝ)) +
        MA * (Cu * D ^ (β - γ : ℝ))) γ (fun x ↦ fderiv 𝕜 (fun y ↦ A y (u y)) x) s := by
  -- `x ↦ (x, u x)` is Lipschitz on `s`, so `x ↦ A' (x, u x)` is `α`-Hölder there
  have hA'u : HolderOnWith (CA * max 1 L ^ (α : ℝ) * D ^ (α - γ : ℝ)) γ
      (fun x ↦ A' (x, u x)) s := by
    have h := hA'.comp (holderOnWith_one.mpr ((LipschitzWith.id.lipschitzOnWith (s := s)).prodMk
      hL)) fun x hx ↦ ⟨hx, hut hx⟩
    rw [mul_one] at h
    exact h.of_le hs hγα
  -- the derivative `x ↦ (id, u' x)` of `x ↦ (x, u x)` is `γ`-Hölder with the constant of `u'`
  have hgraph : HolderOnWith (Cu * D ^ (β - γ : ℝ)) γ
      (fun x ↦ (ContinuousLinearMap.id 𝕜 E).prod (u' x)) s := fun x hx y hy ↦ by
    refine le_of_eq_of_le ?_ ((hu'.of_le hs hγβ).edist_le hx hy)
    exact ((ContinuousLinearMap.prodₗᵢ 𝕜).isometry.edist_eq (ContinuousLinearMap.id 𝕜 E, u' x)
      (ContinuousLinearMap.id 𝕜 E, u' y)).trans (by simp [Prod.edist_eq])
  have h := (ContinuousLinearMap.compL 𝕜 E (E × F) G).holderOnWith_comp₂ hA'u hgraph
    (Mf := MA) (Mg := max 1 Mu) (fun x hx ↦ hA'_le _ ⟨hx, hut hx⟩) fun x hx ↦
      (ContinuousLinearMap.opNorm_id_prod_le _).trans <| by
        rw [NNReal.coe_max, NNReal.coe_one]
        exact max_le_max le_rfl (hu'_le x hx)
  refine (h.congr fun x hx ↦ ?_).mono_const ?_
  · exact (((hA _ ⟨hx, hut hx⟩).comp_graph (hu x hx)).fderiv).symm
  · refine (mul_le_of_le_one_left (by positivity) ?_).trans_eq (add_comm _ _)
    rw [← NNReal.coe_le_coe, coe_nnNorm, NNReal.coe_one]
    exact ContinuousLinearMap.norm_compL_le ..

end Normed
