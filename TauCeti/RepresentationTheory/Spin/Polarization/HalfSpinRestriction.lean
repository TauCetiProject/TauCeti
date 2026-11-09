/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.CliffordAlgebra.VolumeElement.EquivEven
public import TauCeti.RepresentationTheory.Spin.Polarization.OddVolume
public import TauCeti.RepresentationTheory.Spin.OddStructure
import TauCeti.LinearAlgebra.CliffordAlgebra.Even.Intertwiner
import TauCeti.LinearAlgebra.CliffordAlgebra.Grading
import TauCeti.LinearAlgebra.CliffordAlgebra.OrthonormalBasis

/-!
# Odd spinor modules as restricted half-spinors

Let `V` be an oriented real inner product space of odd dimension `n = 2ℓ + 1` with
`Q v = -‖v‖²`, and let `V ⊕ ℝ` be the `L²` product with the form `Q₁ (m, r) = Q m - r²`, again
`Q₁ x = -‖x‖²`, and the new unit vector `e₀ = (0, 1)`. The complexified dimension-raising map
`ψ : Cℓ(ℂ ⊗ V, Q_ℂ) → Cℓ(ℂ ⊗ (V ⊕ ℝ), Q₁_ℂ)`, `c(v) ↦ c(e₀) c(v)`, lands in the even part, so
`Cℓ(ℂ ⊗ V, Q_ℂ)` acts through `ψ` on each half-spinor space `S^μ`, the `μ`-eigenspace of the
chirality element `Γ` of `V ⊕ ℝ`, of every module `S` over `Cℓ(ℂ ⊗ (V ⊕ ℝ), Q₁_ℂ)`
(`CliffordAlgebra.EquivEven.eigenspaceComplexVolumeAction`).

This file identifies these restricted half-spinors of a spinor module `S` of `V ⊕ ℝ`, one on
which `Cℓ(ℂ ⊗ (V ⊕ ℝ), Q₁_ℂ)` acts as the whole of `End_ℂ S`, with the odd spinor modules of `V`.
Take a polarization of `ℂ ⊗ V` and a positively oriented orthonormal basis
`(e₁, f₁, …, e_ℓ, f_ℓ, u)` of `V` adapted to it, as in
`TauCeti.SpinPolarizationData.spinAction_complexVolume`, so that the central volume element
`ω_ℂ` of `V` acts on the spinor module `⋀ W` by `i λ`, where `λ = ±i` is the line coordinate of
`u`. Orient `V ⊕ ℝ` by `(e₁, f₁, …, u, e₀)`. Then `ω_ℂ` acts on `S^μ` through `ψ` by `-μ`
(`CliffordAlgebra.EquivEven.eigenspaceComplexVolumeAction_complexVolume`), and for the matching
label `i λ = -μ` there is a linear isomorphism

  `T : ⋀ W ≃ S^μ`,  `T (x · s) = ψ(x) · T s`,

unique up to a scalar. Thus the odd module labelled `ω_ℂ = 1` (`λ = -i`) is the restriction of
the negative half-spinors `S⁻` of `V ⊕ ℝ`, and the odd module labelled `ω_ℂ = -1` (`λ = i`) is the
restriction of the positive half-spinors `S⁺`. Orienting `V ⊕ ℝ` instead by
`(e₀, e₁, f₁, …, u)`, the opposite orientation since `n + 1` is even, interchanges the two:
`ω_ℂ` acts on `S^μ` by `μ`, and `⋀ W ≃ S^μ` for `i λ = μ`.

The proof compares even parts. The even Clifford algebra of `V` acts on `⋀ W` as the whole of
`End_ℂ (⋀ W)` (`TauCeti.SpinPolarizationData.evenCliffordEquivEnd`), both spaces have dimension
`2 ^ ℓ`, and a rescaling of the odd element `ω_ℂ` acts by the identity on both, so
`CliffordAlgebra.exists_linearEquiv_apply_eq_apply_of_mem_odd` applies.

## Main results

* `TauCeti.SpinPolarizationData.exists_linearEquiv_eigenspaceComplexVolume`: for `V ⊕ ℝ` oriented
  by `(e₁, …, eₙ, e₀)`, the adapted odd spinor module `⋀ W` is isomorphic to the restricted
  half-spinors `S^μ` with `i λ = -μ`, uniquely up to a scalar.
* `TauCeti.SpinPolarizationData.exists_linearEquiv_eigenspaceComplexVolume_of_cons`: the same for
  the orientation `(e₀, e₁, …, eₙ)`, with `i λ = μ`.

## References

* H. B. Lawson and M.-L. Michelsohn, *Spin Geometry* (1989), Chapter I, §3 and §5.
-/

public section

noncomputable section

namespace TauCeti.SpinPolarizationData

open CliffordAlgebra CliffordAlgebra.EquivEven Module
open scoped TensorProduct

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  {Q : QuadraticForm ℝ V} {Q₁ : QuadraticForm ℝ (WithLp 2 (V × ℝ))}
  (P : SpinPolarizationData (Q.baseChange ℂ))
  {ℓ : ℕ} [Fact (finrank ℝ V = 2 * ℓ + 1)] [Fact (finrank ℝ (WithLp 2 (V × ℝ)) = 2 * ℓ + 1 + 1)]
  {o : Orientation ℝ V (Fin (2 * ℓ + 1))}
  {o' : Orientation ℝ (WithLp 2 (V × ℝ)) (Fin (2 * ℓ + 1 + 1))}
  (hQ : ∀ v, Q v = -‖v‖ ^ 2) (hQ₁ : ∀ x, Q₁ x = Q' Q (WithLp.ofLp x))
  (b : OrthonormalBasis (Fin (2 * ℓ + 1)) ℝ V) (hb : b.toBasis.orientation = o)
  -- Term-mode index bounds, as in `TauCeti.SpinPolarizationData.spinAction_complexVolume`.
  (hbW : ∀ k : Fin ℓ,
    1 ⊗ₜ b ⟨2 * k, Nat.lt_succ_of_lt (Nat.mul_lt_mul_of_pos_left k.2 Nat.zero_lt_two)⟩ -
      Complex.I ⊗ₜ b ⟨2 * k + 1,
        Nat.succ_lt_succ (Nat.mul_lt_mul_of_pos_left k.2 Nat.zero_lt_two)⟩ ∈ P.W)
  (hbW' : ∀ k : Fin ℓ,
    1 ⊗ₜ b ⟨2 * k, Nat.lt_succ_of_lt (Nat.mul_lt_mul_of_pos_left k.2 Nat.zero_lt_two)⟩ +
      Complex.I ⊗ₜ b ⟨2 * k + 1,
        Nat.succ_lt_succ (Nat.mul_lt_mul_of_pos_left k.2 Nat.zero_lt_two)⟩ ∈ P.W')
  (hline : 1 ⊗ₜ b (Fin.last (2 * ℓ)) ∈ P.line)
  {S : Type*} [AddCommGroup S] [Module ℂ S] [Module (CliffordAlgebra (Q₁.baseChange ℂ)) S]
  [IsScalarTower ℂ (CliffordAlgebra (Q₁.baseChange ℂ)) S] [FiniteDimensional ℂ S]
  (hS : Function.Bijective
    (Algebra.lsmul ℂ ℂ S : CliffordAlgebra (Q₁.baseChange ℂ) →ₐ[ℂ] Module.End ℂ S))

include hQ hQ₁ hb hbW hbW' hS

/-- The comparison behind both orientations: if `ω_ℂ` acts on `S^μ` through `ψ` by the same
scalar `i λ` by which it acts on `⋀ W`, then `⋀ W ≃ S^μ` as `Cℓ(ℂ ⊗ V, Q_ℂ)`-modules, uniquely up
to a scalar. -/
private theorem exists_linearEquiv_of_eigenspaceComplexVolumeAction_complexVolume {μ : ℂ}
    (hμ : μ = 1 ∨ μ = -1)
    (h : eigenspaceComplexVolumeAction (E := S) hQ₁ o' μ (complexVolume Q o) =
      algebraMap ℂ _ (Complex.I * P.lineCoordinate ⟨_, hline⟩)) :
    ∃ T : ExteriorAlgebra ℂ P.W ≃ₗ[ℂ] (Algebra.lsmul ℂ ℂ S (complexVolume Q₁ o')).eigenspace μ,
      (∀ x s, T (spinAction _ P x s) = eigenspaceComplexVolumeAction hQ₁ o' μ x (T s)) ∧
      ∀ U : ExteriorAlgebra ℂ P.W →ₗ[ℂ] (Algebra.lsmul ℂ ℂ S (complexVolume Q₁ o')).eigenspace μ,
        (∀ x s, U (spinAction _ P x s) = eigenspaceComplexVolumeAction hQ₁ o' μ x (U s)) →
          ∃ c : ℂ, U = c • T.toLinearMap := by
  have hV : finrank ℂ (ℂ ⊗[ℝ] V) = 2 * ℓ + 1 := by
    rw [Module.finrank_baseChange, Fact.out (p := finrank ℝ V = 2 * ℓ + 1)]
  have hQ₁' (x : WithLp 2 (V × ℝ)) : Q₁ x = -‖x‖ ^ 2 :=
    (hQ₁ x).trans (Q'_ofLp_eq_neg_norm_sq hQ x)
  -- The even Clifford algebra of `V` acts on `⋀ W` as all of its endomorphisms.
  have hρ : Function.Bijective ((spinAction _ P).comp (even (Q.baseChange ℂ)).val) := by
    convert (P.evenCliffordEquivEnd (hV ▸ odd_two_mul_add_one ℓ)).bijective using 1
    ext x : 1
    simp
  -- Rescale `ω_ℂ` to act by the identity on both modules; `i λ ≠ 0` since `λ² = Q u = -1`.
  set c := Complex.I * P.lineCoordinate ⟨_, hline⟩
  have hc : c ≠ 0 := by
    rcases P.lineCoordinate_eq_neg_I_or_eq_I hQ b hline with h | h <;> simp [c, h]
  have : Invertible (2 : ℂ) := invertibleOfNonzero two_ne_zero
  have hω : c⁻¹ • complexVolume Q o ∈ evenOdd (Q.baseChange ℂ) 1 := by
    refine Submodule.smul_mem _ _ (involute_eq_neg_iff.1 ?_)
    rw [involute_complexVolume, (odd_two_mul_add_one ℓ).neg_one_pow, neg_one_smul]
  have h₁ : spinAction _ P (c⁻¹ • complexVolume Q o) = 1 := by
    rw [map_smul, P.spinAction_complexVolume hQ b hb hbW hbW' hline, Algebra.smul_def, ← map_mul,
      inv_mul_cancel₀ hc, map_one]
  have h₂ : eigenspaceComplexVolumeAction (E := S) hQ₁ o' μ (c⁻¹ • complexVolume Q o) = 1 := by
    rw [map_smul, h, Algebra.smul_def, ← map_mul, inv_mul_cancel₀ hc, map_one]
  -- Both modules have dimension `2 ^ ℓ`.
  have hdim : finrank ℂ (ExteriorAlgebra ℂ P.W) =
      finrank ℂ ((Algebra.lsmul ℂ ℂ S (complexVolume Q₁ o')).eigenspace μ) := by
    rw [P.finrank_exteriorAlgebra_W_of_finrank_eq_two_mul_add_one hV,
      finrank_eigenspace_complexVolume_of_bijective_lsmul o' hQ₁' hS
        ⟨ℓ + 1, by omega⟩ (by omega) hμ]
    congr 1
    omega
  obtain ⟨T, hT⟩ := exists_linearEquiv_apply_eq_apply_of_mem_odd hρ hω h₁ h₂ hdim
  exact ⟨T, hT, fun U hU ↦ exists_eq_smul_of_apply_eq_apply hρ hT hU⟩

/-- **The odd spinor modules are the restricted half-spinors of `V ⊕ ℝ`.** Let
`(e₁, f₁, …, e_ℓ, f_ℓ, u)` be a positively oriented orthonormal basis of `V` adapted to the
polarization, so that `ω_ℂ` acts on `⋀ W` by `i λ` with `λ = ±i` the line coordinate of `u`, and
orient `V ⊕ ℝ` by `(e₁, f₁, …, u, e₀)`. If `i λ = -μ`, then for every spinor module `S` of
`V ⊕ ℝ` there is a linear isomorphism `T` from `⋀ W` onto the half-spinor space `S^μ` intertwining
the Fock action with the action through `ψ`, and every linear map intertwining them is a scalar
multiple of `T`.

For `λ = -i`, the module labelled `ω_ℂ = 1`, this identifies `⋀ W` with the negative half-spinors
`S⁻`; for `λ = i`, the module labelled `ω_ℂ = -1`, with the positive half-spinors `S⁺`. -/
theorem exists_linearEquiv_eigenspaceComplexVolume
    (ho' : ((b.prod (OrthonormalBasis.singleton (Fin 1) ℝ)).reindex
      finSumFinEquiv).toBasis.orientation = o') {μ : ℂ}
    (hμ : Complex.I * P.lineCoordinate ⟨_, hline⟩ = -μ) :
    ∃ T : ExteriorAlgebra ℂ P.W ≃ₗ[ℂ] (Algebra.lsmul ℂ ℂ S (complexVolume Q₁ o')).eigenspace μ,
      (∀ x s, T (spinAction _ P x s) = eigenspaceComplexVolumeAction hQ₁ o' μ x (T s)) ∧
      ∀ U : ExteriorAlgebra ℂ P.W →ₗ[ℂ] (Algebra.lsmul ℂ ℂ S (complexVolume Q₁ o')).eigenspace μ,
        (∀ x s, U (spinAction _ P x s) = eigenspaceComplexVolumeAction hQ₁ o' μ x (U s)) →
          ∃ c : ℂ, U = c • T.toLinearMap := by
  refine exists_linearEquiv_of_eigenspaceComplexVolumeAction_complexVolume P hQ hQ₁ b hb hbW hbW'
    hline hS ?_ ?_
  · rcases P.lineCoordinate_eq_neg_I_or_eq_I hQ b hline with h | h <;>
      rw [h] at hμ <;> [right; left]
    · linear_combination hμ + Complex.I_mul_I
    · linear_combination hμ - Complex.I_mul_I
  · rw [eigenspaceComplexVolumeAction_complexVolume hQ₁ o o' (odd_two_mul_add_one ℓ) b hb
      (b.isOrthoᵢ_associated hQ) ho', hμ]

/-- **Putting `e₀` first interchanges the labels.** With the basis and polarization as in
`TauCeti.SpinPolarizationData.exists_linearEquiv_eigenspaceComplexVolume`, but `V ⊕ ℝ` oriented
by `(e₀, e₁, f₁, …, u)`, the opposite orientation: if `i λ = μ`, then `⋀ W` is isomorphic to the
half-spinor space `S^μ` of every spinor module `S` of `V ⊕ ℝ` through `ψ`, uniquely up to a
scalar. Now the module labelled `ω_ℂ = 1` is the restriction of `S⁺` and the module labelled
`ω_ℂ = -1` is the restriction of `S⁻`. -/
theorem exists_linearEquiv_eigenspaceComplexVolume_of_cons
    (ho' : ((b.prod (OrthonormalBasis.singleton (Fin 1) ℝ)).reindex
      (((Equiv.sumComm _ _).trans finSumFinEquiv).trans
        (finCongr (add_comm 1 (2 * ℓ + 1))))).toBasis.orientation = o') {μ : ℂ}
    (hμ : Complex.I * P.lineCoordinate ⟨_, hline⟩ = μ) :
    ∃ T : ExteriorAlgebra ℂ P.W ≃ₗ[ℂ] (Algebra.lsmul ℂ ℂ S (complexVolume Q₁ o')).eigenspace μ,
      (∀ x s, T (spinAction _ P x s) = eigenspaceComplexVolumeAction hQ₁ o' μ x (T s)) ∧
      ∀ U : ExteriorAlgebra ℂ P.W →ₗ[ℂ] (Algebra.lsmul ℂ ℂ S (complexVolume Q₁ o')).eigenspace μ,
        (∀ x s, U (spinAction _ P x s) = eigenspaceComplexVolumeAction hQ₁ o' μ x (U s)) →
          ∃ c : ℂ, U = c • T.toLinearMap := by
  refine exists_linearEquiv_of_eigenspaceComplexVolumeAction_complexVolume P hQ hQ₁ b hb hbW hbW'
    hline hS ?_ ?_
  · rcases P.lineCoordinate_eq_neg_I_or_eq_I hQ b hline with h | h <;>
      rw [h] at hμ <;> [left; right]
    · linear_combination -hμ - Complex.I_mul_I
    · linear_combination -hμ + Complex.I_mul_I
  · rw [eigenspaceComplexVolumeAction_complexVolume_of_cons hQ₁ o o' (odd_two_mul_add_one ℓ) b hb
      (b.isOrthoᵢ_associated hQ) ho', hμ]

end TauCeti.SpinPolarizationData
