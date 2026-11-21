/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Hamiltonian.DarbouxChart
public import TauCeti.Geometry.Symplectic.Hamiltonian.Involutive.Darboux
public import TauCeti.Geometry.Symplectic.Hamiltonian.Involutive.Extension

/-!
# The Carathéodory–Jacobi–Lie theorem

Let `σ` be a symplectic form on a manifold `M` of dimension `2n`, with the conventions
`ι_{X_f} σ = df` and `{f, g} = σ(X_f, X_g) = df(X_g)`. The **Carathéodory–Jacobi–Lie theorem**
says that any `k ≤ n` smooth functions `F₁, …, F_k` which Poisson-commute near a point `x` and have
independent differentials at `x` are the first `k` momenta of Darboux coordinates `(q, p)` near
`x`, in which `σ = ∑ᵢ dqᵢ ∧ dpᵢ`
(`TauCeti.SmoothTwoForm.IsSymplectic.exists_darbouxChart_snd_castAdd_eq`). The dimension is
written `2 (k + m)`, and the momenta `F` are indexed by `Fin.castAdd m`, so that the remaining `m`
momenta and all `k + m` positions are supplied by the theorem.

The proof extends `F` by `m` further functions to an involutive family of `k + m` independent
functions (`TauCeti.SmoothTwoForm.IsSymplectic.exists_isRegularPoint_castLE`) and takes the
Darboux chart whose momenta are that family
(`TauCeti.SmoothTwoForm.IsSymplectic.exists_darbouxChart_snd_eq`).

The positions of every Darboux chart are canonical conjugate variables of its momenta
(`TauCeti/Geometry/Symplectic/Hamiltonian/DarbouxChart.lean`). Applied to the chart of the
Carathéodory–Jacobi–Lie theorem with the function `Fᵢ`, which equals the momentum
`p_(Fin.castAdd m i)` on the source, this says that the Hamiltonian vector field of `Fᵢ` is
`∂/∂q_(Fin.castAdd m i)` (`TauCeti.SmoothTwoForm.mvfderiv_hamiltonianVectorField_eq_of_eqOn_snd`),
that `{q_(Fin.castAdd m i), Fⱼ} = δᵢⱼ`
(`TauCeti.SmoothTwoForm.poissonBracket_eq_ite_of_eqOn_fst_of_eqOn_snd`), and that the flow of `Fᵢ`
is translation in `q_(Fin.castAdd m i)`
(`TauCeti.SmoothTwoForm.apply_eq_add_smul_of_isMIntegralCurveOn`).
No compactness of the levels of `F` and no completeness of the Hamiltonian vector fields is needed.

## References

* P. Libermann and C.-M. Marle, *Symplectic Geometry and Analytical Mechanics*, Mathematics and
  its Applications 35, D. Reidel, 1987, Chapter III (the Carathéodory–Jacobi–Lie theorem).
* V. I. Arnold, *Mathematical Methods of Classical Mechanics*, 2nd ed., Graduate Texts in
  Mathematics 60, Springer, 1989, Section 49.
-/

public section

open Set Filter Module
open scoped ContDiff Manifold Topology

namespace TauCeti

namespace SmoothTwoForm

/-! ### Commuting functions as momenta -/

namespace IsSymplectic

variable {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} {M : Type*} [TopologicalSpace M]
  [ChartedSpace H M] [IsManifold I ∞ M] [BoundarylessManifold I M] [T2Space M]
  {σ : SmoothTwoForm I M} {x : M}

/-- **The Carathéodory–Jacobi–Lie theorem.** On a boundaryless Hausdorff symplectic manifold of
dimension `2 (k + m)`, let `F : M → (Fin k → ℝ)` be smooth, with components Poisson-commuting near
`x` and with independent differentials at `x`. Then the `Fᵢ` are momenta of Darboux coordinates
near `x`: there is a smooth partial diffeomorphism `chart` from `M` to
`(Fin (k + m) → ℝ) × (Fin (k + m) → ℝ)` whose source contains `x`, with positions `0` at `x` and
momenta `p_(Fin.castAdd m i) = Fᵢ`, pulling the standard form `∑ⱼ dqⱼ ∧ dpⱼ` back to `σ`. Its
positions `q_(Fin.castAdd m i)` are conjugate to the `Fᵢ`, by
`TauCeti.SmoothTwoForm.poissonBracket_eq_ite_of_eqOn_fst_of_eqOn_snd`. -/
theorem exists_darbouxChart_snd_castAdd_eq (hσ : σ.IsSymplectic) {k m : ℕ}
    (hdim : 2 * (k + m) = finrank ℝ E) {F : M → Fin k → ℝ}
    (hF : ContMDiff I 𝓘(ℝ, Fin k → ℝ) ∞ F)
    (hcomm : ∀ i j, σ.poissonBracket (F · i) (F · j) =ᶠ[𝓝 x] fun _ ↦ 0)
    (hreg : IsRegularPoint I 𝓘(ℝ, Fin k → ℝ) F x) :
    ∃ chart : PartialDiffeomorph I 𝓘(ℝ, (Fin (k + m) → ℝ) × (Fin (k + m) → ℝ)) M
        ((Fin (k + m) → ℝ) × (Fin (k + m) → ℝ)) ∞,
      x ∈ chart.source ∧ (chart x).1 = 0 ∧
        (∀ y ∈ chart.source, ∀ i, (chart y).2 (Fin.castAdd m i) = F y i) ∧
        ∀ y ∈ chart.source, ∀ v w : TangentSpace I y, SmoothBundleForm.eval₂ σ y v w =
          ∑ j, ((mvfderiv I chart y v).1 j * (mvfderiv I chart y w).2 j -
            (mvfderiv I chart y w).1 j * (mvfderiv I chart y v).2 j) := by
  -- Extend `F` to `k + m` involutive independent functions `G`, and take the Darboux chart with
  -- momenta `G`.
  obtain ⟨G, hG, hGc, hGr, hGF⟩ :=
    hσ.exists_isRegularPoint_castLE hdim.le (Nat.le_add_right k m) hF hcomm hreg
  obtain ⟨chart, hx, hcx, hsnd, hform⟩ :=
    hσ.exists_darbouxChart_snd_eq hG hGc hGr (by rw [Fintype.card_fin, hdim])
  refine ⟨chart, hx, by rw [hcx], fun y hy i ↦ ?_, hform⟩
  rw [hsnd y hy]
  exact congrFun (hGF i) y

end IsSymplectic

end SmoothTwoForm

end TauCeti
