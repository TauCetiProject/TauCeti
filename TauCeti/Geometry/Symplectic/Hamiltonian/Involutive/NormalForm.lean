/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Hamiltonian.Involutive.Darboux
public import TauCeti.Geometry.Symplectic.Hamiltonian.Involutive.Extension
import TauCeti.Geometry.Manifold.IntegralCurve.Monotone
import TauCeti.Geometry.Manifold.LocalDiffeomorph.MFDeriv

/-!
# The Carathéodory–Jacobi–Lie theorem

Let `σ` be a symplectic form on a manifold `M` of dimension `2n`, with the conventions
`ι_{X_f} σ = df` and `{f, g} = σ(X_f, X_g) = df(X_g)`. The **Carathéodory–Jacobi–Lie theorem**
says that any `k ≤ n` smooth functions `F₁, …, F_k` which Poisson-commute near a point `x` and have
independent differentials at `x` are the first `k` momenta of Darboux coordinates `(q, p)` near
`x`, in which `σ = ∑ᵢ dqᵢ ∧ dpᵢ` (`TauCeti.SmoothTwoForm.IsSymplectic.exists_darbouxChart_castAdd`).
The dimension is written `2 (k + m)`, and the momenta `F` are indexed by `Fin.castAdd m`, so that
the remaining `m` momenta and all `k + m` positions are supplied by the theorem.

The proof extends `F` by `m` further functions to an involutive family of `k + m` independent
functions (`TauCeti.SmoothTwoForm.IsSymplectic.exists_isRegularPoint_castLE`) and takes the
Darboux chart whose momenta are that family
(`TauCeti.SmoothTwoForm.IsSymplectic.exists_darbouxChart_snd_eq`).

The positions of such a chart are **canonical conjugate variables** of its momenta. This holds in
every Darboux chart, that is, every partial diffeomorphism to `(ι → ℝ) × (ι → ℝ)` pulling
`∑ᵢ dqᵢ ∧ dpᵢ` back to `σ` on its source. On that source:

* `σ` is nondegenerate (`TauCeti.SmoothTwoForm.isInvertible_flat_of_mem_source`);
* the Hamiltonian vector field of a function equal to the momentum `pᵢ` is the coordinate field
  `∂/∂qᵢ`, and that of a function equal to the position `qᵢ` is `-∂/∂pᵢ`
  (`TauCeti.SmoothTwoForm.mvfderiv_hamiltonianVectorField_eq_of_eqOn_snd`,
  `TauCeti.SmoothTwoForm.mvfderiv_hamiltonianVectorField_eq_of_eqOn_fst`);
* the coordinates satisfy the canonical relations `{qᵢ, pⱼ} = δᵢⱼ`, `{qᵢ, qⱼ} = 0` and
  `{pᵢ, pⱼ} = 0` (`TauCeti.SmoothTwoForm.poissonBracket_eq_ite_of_eqOn_fst_of_eqOn_snd`,
  `TauCeti.SmoothTwoForm.poissonBracket_eq_zero_of_eqOn_fst`,
  `TauCeti.SmoothTwoForm.poissonBracket_eq_zero_of_eqOn_snd`);
* the Hamiltonian flow of the momentum `pᵢ` translates the position `qᵢ` at unit speed and fixes
  the other coordinates, as long as it stays in the chart
  (`TauCeti.SmoothTwoForm.apply_eq_add_smul_of_isMIntegralCurveOn`).

Applied to the chart of the Carathéodory–Jacobi–Lie theorem with the function `Fᵢ`, which equals
the momentum `p_(Fin.castAdd m i)` on the source, these say that the Hamiltonian vector field of
`Fᵢ` is `∂/∂q_(Fin.castAdd m i)`, that `{q_(Fin.castAdd m i), Fⱼ} = δᵢⱼ`, and that the flow of `Fᵢ`
is translation in `q_(Fin.castAdd m i)`. No compactness of the levels of `F` and no completeness of
the Hamiltonian vector fields is needed.

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

/-! ### Canonical conjugate variables in a Darboux chart -/

section DarbouxChart

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  {σ : SmoothTwoForm I M} {ι : Type*} [Fintype ι]
  {chart : PartialDiffeomorph I 𝓘(ℝ, (ι → ℝ) × (ι → ℝ)) M ((ι → ℝ) × (ι → ℝ)) ∞} {y : M}
  (hform : ∀ y ∈ chart.source, ∀ v w : TangentSpace I y, SmoothBundleForm.eval₂ σ y v w =
    ∑ i, ((mvfderiv I chart y v).1 i * (mvfderiv I chart y w).2 i -
      (mvfderiv I chart y w).1 i * (mvfderiv I chart y v).2 i))

omit [IsManifold I ∞ M] in
/-- The differential of a position coordinate `qᵢ` of a chart is the `i`-th component of the first
half of the differential of the chart. -/
private theorem mvfderiv_fst_apply (hy : y ∈ chart.source) (i : ι) (w : TangentSpace I y) :
    mvfderiv I (fun z ↦ (chart z).1 i) y w = (mvfderiv I chart y w).1 i :=
  -- The coordinate function is `proj i ∘ fst ∘ chart`, by definition of the projections.
  ((ContinuousLinearMap.proj i).comp
    (ContinuousLinearMap.fst ℝ (ι → ℝ) (ι → ℝ))).mvfderiv_comp_apply
      (chart.mdifferentiableAt (by simp) hy) w

omit [IsManifold I ∞ M] in
/-- The differential of a momentum coordinate `pᵢ` of a chart is the `i`-th component of the second
half of the differential of the chart. -/
private theorem mvfderiv_snd_apply (hy : y ∈ chart.source) (i : ι) (w : TangentSpace I y) :
    mvfderiv I (fun z ↦ (chart z).2 i) y w = (mvfderiv I chart y w).2 i :=
  -- The coordinate function is `proj i ∘ snd ∘ chart`, by definition of the projections.
  ((ContinuousLinearMap.proj i).comp
    (ContinuousLinearMap.snd ℝ (ι → ℝ) (ι → ℝ))).mvfderiv_comp_apply
      (chart.mdifferentiableAt (by simp) hy) w

include hform

/-- **A two-form with a Darboux chart is nondegenerate on its source.** If a partial
diffeomorphism to `(ι → ℝ) × (ι → ℝ)` pulls `∑ᵢ dqᵢ ∧ dpᵢ` back to `σ` on its source, then the flat
map of `σ` is invertible at every point of that source. -/
theorem isInvertible_flat_of_mem_source (hy : y ∈ chart.source) : (σ.flat y).IsInvertible := by
  classical
  have hbij := chart.bijective_mvfderiv (by simp) hy
  have : FiniteDimensional ℝ E :=
    (LinearEquiv.ofBijective (mvfderiv I chart y).toLinearMap hbij).symm.finiteDimensional
  rw [isInvertible_flat_iff]
  refine (SmoothForm.isAlt_bilinFormAt σ y).isRefl.nondegenerate_iff_separatingLeft.2
    fun v hv ↦ hbij.1 ?_
  -- Pairing with vectors whose images are `(0, eₗ)` and `(eₗ, 0)` reads off the coordinates
  -- `(dq v)ₗ` and `-(dp v)ₗ` of the image of `v`, which therefore vanish.
  rw [map_zero]
  ext l
  · obtain ⟨w, hw⟩ := hbij.2 (0, Pi.single l 1)
    have h := hv w
    rw [SmoothForm.bilinFormAt_apply, hform y hy, hw] at h
    simpa [Pi.single_apply] using h
  · obtain ⟨w, hw⟩ := hbij.2 (Pi.single l 1, 0)
    have h := hv w
    rw [SmoothForm.bilinFormAt_apply, hform y hy, hw] at h
    simpa [Pi.single_apply] using h

/-- At a point of the source of a Darboux chart, the Hamiltonian vector field of `f` is the vector
whose contraction with `σ` is `df`. -/
private theorem hamiltonianVectorField_eq_of_eval₂_eq (hy : y ∈ chart.source) {f : M → ℝ}
    {v : TangentSpace I y} (hv : ∀ w, SmoothBundleForm.eval₂ σ y v w = mvfderiv I f y w) :
    σ.hamiltonianVectorField f y = v := by
  rw [hamiltonianVectorField_def, (isInvertible_flat_of_mem_source hform hy).inverse_apply_eq]
  ext w
  rw [flat_apply, hv]

/-- **The Hamiltonian vector field of a momentum is the conjugate position field.** In a Darboux
chart, if `f` equals the momentum `pᵢ` on the source, then at every point of the source the chart
sends the Hamiltonian vector field of `f` to `(eᵢ, 0)`: `X_f = ∂/∂qᵢ`. -/
theorem mvfderiv_hamiltonianVectorField_eq_of_eqOn_snd [DecidableEq ι] {f : M → ℝ} {i : ι}
    (hf : EqOn f (fun z ↦ (chart z).2 i) chart.source) (hy : y ∈ chart.source) :
    mvfderiv I chart y (σ.hamiltonianVectorField f y) = (Pi.single i 1, 0) := by
  obtain ⟨v, hv⟩ := (chart.bijective_mvfderiv (by simp) hy).2 (Pi.single i 1, 0)
  rw [hamiltonianVectorField_eq_of_eval₂_eq hform hy (v := v) fun w ↦ ?_, hv]
  rw [(hf.eventuallyEq_of_mem (chart.open_source.mem_nhds hy)).mvfderiv_eq,
    mvfderiv_snd_apply hy, hform y hy, hv]
  simp [Pi.single_apply]

/-- **The Hamiltonian vector field of a position is minus the conjugate momentum field.** In a
Darboux chart, if `f` equals the position `qᵢ` on the source, then at every point of the source the
chart sends the Hamiltonian vector field of `f` to `(0, -eᵢ)`: `X_f = -∂/∂pᵢ`. -/
theorem mvfderiv_hamiltonianVectorField_eq_of_eqOn_fst [DecidableEq ι] {f : M → ℝ} {i : ι}
    (hf : EqOn f (fun z ↦ (chart z).1 i) chart.source) (hy : y ∈ chart.source) :
    mvfderiv I chart y (σ.hamiltonianVectorField f y) = (0, -Pi.single i 1) := by
  obtain ⟨v, hv⟩ := (chart.bijective_mvfderiv (by simp) hy).2 (0, -Pi.single i 1)
  rw [hamiltonianVectorField_eq_of_eval₂_eq hform hy (v := v) fun w ↦ ?_, hv]
  rw [(hf.eventuallyEq_of_mem (chart.open_source.mem_nhds hy)).mvfderiv_eq,
    mvfderiv_fst_apply hy, hform y hy, hv]
  simp [Pi.single_apply]

/-- **The canonical relation `{qᵢ, pⱼ} = δᵢⱼ`.** In a Darboux chart, if `f` equals the position `qᵢ`
and `g` the momentum `pⱼ` on the source, then their Poisson bracket at every point of the source
is `1` when `i = j` and `0` otherwise. -/
theorem poissonBracket_eq_ite_of_eqOn_fst_of_eqOn_snd [DecidableEq ι] {f g : M → ℝ} {i j : ι}
    (hf : EqOn f (fun z ↦ (chart z).1 i) chart.source)
    (hg : EqOn g (fun z ↦ (chart z).2 j) chart.source) (hy : y ∈ chart.source) :
    σ.poissonBracket f g y = if i = j then 1 else 0 := by
  rw [poissonBracket_def, hform y hy, mvfderiv_hamiltonianVectorField_eq_of_eqOn_fst hform hf hy,
    mvfderiv_hamiltonianVectorField_eq_of_eqOn_snd hform hg hy]
  simp [Pi.single_apply]

/-- **The canonical relation `{qᵢ, qⱼ} = 0`.** In a Darboux chart, functions equal on the source to
positions Poisson-commute at every point of the source. -/
theorem poissonBracket_eq_zero_of_eqOn_fst {f g : M → ℝ} {i j : ι}
    (hf : EqOn f (fun z ↦ (chart z).1 i) chart.source)
    (hg : EqOn g (fun z ↦ (chart z).1 j) chart.source) (hy : y ∈ chart.source) :
    σ.poissonBracket f g y = 0 := by
  classical
  rw [poissonBracket_def, hform y hy, mvfderiv_hamiltonianVectorField_eq_of_eqOn_fst hform hf hy,
    mvfderiv_hamiltonianVectorField_eq_of_eqOn_fst hform hg hy]
  simp

/-- **The canonical relation `{pᵢ, pⱼ} = 0`.** In a Darboux chart, functions equal on the source to
momenta Poisson-commute at every point of the source. -/
theorem poissonBracket_eq_zero_of_eqOn_snd {f g : M → ℝ} {i j : ι}
    (hf : EqOn f (fun z ↦ (chart z).2 i) chart.source)
    (hg : EqOn g (fun z ↦ (chart z).2 j) chart.source) (hy : y ∈ chart.source) :
    σ.poissonBracket f g y = 0 := by
  classical
  rw [poissonBracket_def, hform y hy, mvfderiv_hamiltonianVectorField_eq_of_eqOn_snd hform hf hy,
    mvfderiv_hamiltonianVectorField_eq_of_eqOn_snd hform hg hy]
  simp

/-- **The Hamiltonian flow of a momentum translates its conjugate position.** In a Darboux chart,
let `f` equal the momentum `pᵢ` on the source, and let `γ` be an integral curve of the Hamiltonian
vector field of `f` on a preconnected set of times `s`, such as an interval, staying in the source.
Then in the chart `γ` moves along the `qᵢ`-axis at unit speed:
`chart (γ t) = chart (γ t₀) + (t - t₀) • (eᵢ, 0)`. -/
theorem apply_eq_add_smul_of_isMIntegralCurveOn [DecidableEq ι] {f : M → ℝ} {i : ι}
    (hf : EqOn f (fun z ↦ (chart z).2 i) chart.source) {γ : ℝ → M} {s : Set ℝ}
    (hγ : IsMIntegralCurveOn γ (σ.hamiltonianVectorField f) s) (hs : IsPreconnected s)
    (hγs : ∀ t ∈ s, γ t ∈ chart.source) {t₀ t : ℝ} (ht₀ : t₀ ∈ s) (ht : t ∈ s) :
    chart (γ t) = chart (γ t₀) + (t - t₀) • ((Pi.single i 1, 0) : (ι → ℝ) × (ι → ℝ)) :=
  hγ.apply_eq_add_smul_of_mvfderiv_apply_eq hs
    (fun u hu ↦ chart.mdifferentiableAt (by simp) (hγs u hu))
    (fun u hu ↦ mvfderiv_hamiltonianVectorField_eq_of_eqOn_snd hform hf (hγs u hu)) ht₀ ht

end DarbouxChart

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
theorem exists_darbouxChart_castAdd (hσ : σ.IsSymplectic) {k m : ℕ}
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
