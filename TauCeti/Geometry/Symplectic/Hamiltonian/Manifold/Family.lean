/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Hamiltonian.Manifold
import TauCeti.Geometry.Manifold.Diffeomorph.Prod

/-!
# Regularity of parametrized families of Hamiltonian vector fields on open sets

For a nondegenerate two-form `σ` on a finite-dimensional manifold `M`, a family of Hamiltonians
`H : N → M → ℝ` which is jointly `C^(n+1)` on an open set `W ⊆ N × M` has Hamiltonian vector
fields `(p, x) ↦ X_{H p}(x)` which are jointly `C^n` on `W`, for `n ≤ ∞`
(`TauCeti.SmoothTwoForm.IsNondegenerate.contMDiffOn_hamiltonianVectorField_uncurry`). The
reassociated form for a doubly parametrized family `H : P → Q → M → ℝ` on an open set
`W ⊆ P × (Q × M)` is
`TauCeti.SmoothTwoForm.IsNondegenerate.contMDiffOn_hamiltonianVectorField_prod`.
-/

public section

noncomputable section

open scoped ContDiff Manifold

namespace TauCeti.SmoothTwoForm.IsNondegenerate

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  {σ : SmoothTwoForm I M} [FiniteDimensional ℝ E]

/-- **Joint regularity of Hamiltonian vector fields of a family on an open set.** For a
nondegenerate two-form on a finite-dimensional manifold and a family of Hamiltonians
`H : N → M → ℝ` which is jointly `C^(n+1)` on an open set `W ⊆ N × M`, the Hamiltonian vector
fields `(p, x) ↦ X_{H p}(x)` are jointly `C^n` on `W`, for `n ≤ ∞`. -/
theorem contMDiffOn_hamiltonianVectorField_uncurry (h : σ.IsNondegenerate) {E' H' N : Type*}
    [NormedAddCommGroup E'] [NormedSpace ℝ E'] [TopologicalSpace H']
    {J : ModelWithCorners ℝ E' H'} [TopologicalSpace N] [ChartedSpace H' N] [IsManifold J 1 N]
    {n : WithTop ℕ∞} (hn : n ≤ ∞) {H : N → M → ℝ} {W : Set (N × M)} (hW : IsOpen W)
    (hH : ContMDiffOn (J.prod I) 𝓘(ℝ) (n + 1) (Function.uncurry H) W) :
    ContMDiffOn (J.prod I) I.tangent n
      (fun q : N × M ↦ (⟨q.2, σ.hamiltonianVectorField (H q.1) q.2⟩ : TangentBundle I M)) W :=
  fun _ hq ↦ (h.contMDiffAt_hamiltonianVectorField_uncurry hn
    (hH.contMDiffAt (hW.mem_nhds hq))).contMDiffWithinAt

/-- **Joint regularity of Hamiltonian vector fields of a doubly parametrized family on an open
set.** Reassociated form of `contMDiffOn_hamiltonianVectorField_uncurry` for a family
`H : P → Q → M → ℝ` on an open set `W ⊆ P × (Q × M)`. -/
theorem contMDiffOn_hamiltonianVectorField_prod (h : σ.IsNondegenerate) {E₁ H₁ P E₂ H₂ Q : Type*}
    [NormedAddCommGroup E₁] [NormedSpace ℝ E₁] [TopologicalSpace H₁] {J₁ : ModelWithCorners ℝ E₁ H₁}
    [TopologicalSpace P] [ChartedSpace H₁ P] [IsManifold J₁ 1 P]
    [NormedAddCommGroup E₂] [NormedSpace ℝ E₂] [TopologicalSpace H₂] {J₂ : ModelWithCorners ℝ E₂ H₂}
    [TopologicalSpace Q] [ChartedSpace H₂ Q] [IsManifold J₂ 1 Q]
    {n : WithTop ℕ∞} (hn : n ≤ ∞) {H : P → Q → M → ℝ} {W : Set (P × (Q × M))} (hW : IsOpen W)
    (hH : ContMDiffOn (J₁.prod (J₂.prod I)) 𝓘(ℝ) (n + 1)
      (fun q : P × (Q × M) ↦ H q.1 q.2.1 q.2.2) W) :
    ContMDiffOn (J₁.prod (J₂.prod I)) I.tangent n
      (fun q : P × (Q × M) ↦
        (⟨q.2.2, σ.hamiltonianVectorField (H q.1 q.2.1) q.2.2⟩ : TangentBundle I M)) W := by
  let a := Diffeomorph.prodAssocOfModels J₁ J₂ I P Q M (n + 1)
  have hH' : ContMDiffOn ((J₁.prod J₂).prod I) 𝓘(ℝ) (n + 1)
      (Function.uncurry (fun pq : P × Q ↦ H pq.1 pq.2)) (a ⁻¹' W) :=
    (hH.comp a.contMDiff.contMDiffOn (Set.mapsTo_preimage (⇑a) W)).congr
      (fun q _ ↦ by
        dsimp only [Function.comp_apply, Function.uncurry_def, a]
        rw [Diffeomorph.prodAssocOfModels_apply])
  refine ((h.contMDiffOn_hamiltonianVectorField_uncurry (J := J₁.prod J₂) hn
      (hW.preimage a.continuous) hH').comp
      (a.symm.contMDiff.of_le le_self_add).contMDiffOn
      (fun q hq ↦ by simpa [a] using hq)).congr (fun q _ ↦ ?_)
  dsimp only [Function.comp_apply, a]
  rw [Diffeomorph.prodAssocOfModels_symm_apply]

end TauCeti.SmoothTwoForm.IsNondegenerate
