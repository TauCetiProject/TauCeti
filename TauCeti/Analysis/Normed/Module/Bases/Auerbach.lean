/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.LinearAlgebra.Dual.Defs
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Mathlib.Analysis.Normed.Group.Continuity
import Mathlib.Analysis.Normed.Ring.Lemmas
import Mathlib.LinearAlgebra.Determinant
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Topology.Instances.Matrix
import Mathlib.Topology.Order.Compact
import TauCeti.LinearAlgebra.Dual.Lemmas
import TauCeti.LinearAlgebra.Matrix.Determinant.Basic

/-!
# Auerbach's lemma for a compact family of linear forms

Let `U` be a finite-dimensional vector space over a field `K`, `𝒜` a compact topological space,
`(ℓ_a)_{a ∈ 𝒜}` a family of linear forms on `U` whose only common zero is `0`, and `φ : K →+* L`
a ring homomorphism into a normed field `L` such that `a ↦ φ (ℓ a v)` is continuous for every
`v : U`. Then there exist `a : Fin (finrank K U) → 𝒜` and a basis
`z : Module.Basis (Fin (finrank K U)) K U` such that `ℓ (a i) (z j) = δ_{ij}` and
`‖φ (ℓ x (z k))‖ ≤ 1` for all `x : 𝒜` and all `k`.

For `K = L = ℝ` or `ℂ` and the unit sphere of the dual of a normed space, this recovers the
classical Auerbach basis.

## Main statements

* `RingHom.exists_auerbachBasis`: existence of an Auerbach basis for a compact separating family
  of linear forms measured through a ring homomorphism into a normed field.

## References

* A. E. Taylor, *A geometric theorem and its application to biorthogonal systems*,
  Bull. Amer. Math. Soc. 53 (1947), 614--616 (the maximal-determinant proof).
* S. Banach, *Théorie des opérations linéaires*, Monografie Matematyczne 1, Warszawa, 1932
  (where the lemma is attributed to H. Auerbach, c. 1930).
* J. Lindenstrauss and L. Tzafriri, *Classical Banach Spaces I*, Springer, 1977, Prop. 1.c.3.
* L. Alpöge, Lean formalization of the Riemann hypothesis for Dirichlet `L`-functions,
  `New.exists_auerbach` in `src/Lib/General/LinearAlgebra/MatrixNormBounds.lean`,
  <https://github.com/leanprover-community/riemann-hypothesis/tree/dba5aded4bf7>.
  `RingHom.exists_auerbachBasis` generalizes that lemma.
-/

public section

namespace TauCeti

variable {K U 𝒜 : Type*} [Field K] [AddCommGroup U] [Module K U] {n : ℕ}

/-- The matrix `(ℓ (f i) (b j))_{i,j}` of the forms `ℓ ∘ f` evaluated at the vectors `b`. -/
private def evalMatrix (ℓ : 𝒜 → Module.Dual K U) (b : Fin n → U) (f : Fin n → 𝒜) :
    Matrix (Fin n) (Fin n) K :=
  Matrix.of fun i j => ℓ (f i) (b j)

@[simp]
private lemma evalMatrix_apply (ℓ : 𝒜 → Module.Dual K U) (b : Fin n → U) (f : Fin n → 𝒜)
    (i j : Fin n) : evalMatrix ℓ b f i j = ℓ (f i) (b j) :=
  rfl

/-- Right multiplication by `N` replaces the vectors `b` by the combinations `∑ j, N j k • b j`. -/
private lemma evalMatrix_mul (ℓ : 𝒜 → Module.Dual K U) (b : Fin n → U) (f : Fin n → 𝒜)
    (N : Matrix (Fin n) (Fin n) K) :
    evalMatrix ℓ b f * N = evalMatrix ℓ (fun k => ∑ j, N j k • b j) f := by
  ext i k
  simp [Matrix.mul_apply, map_sum, mul_comm]

/-- If `evalMatrix ℓ b a` is invertible, the vectors `∑ j, (evalMatrix ℓ b a)⁻¹ j k • b j` are
dual to the forms `ℓ ∘ a`. -/
private lemma evalMatrix_inv_eq_one (ℓ : 𝒜 → Module.Dual K U) (b : Fin n → U) (a : Fin n → 𝒜)
    (ha : (evalMatrix ℓ b a).det ≠ 0) :
    evalMatrix ℓ (fun k => ∑ j, (evalMatrix ℓ b a)⁻¹ j k • b j) a = 1 := by
  rw [← evalMatrix_mul, Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr ha)]

/-- Replacing the form in row `k` by `ℓ x` replaces row `k` of the evaluation matrix. -/
private lemma evalMatrix_update (ℓ : 𝒜 → Module.Dual K U) (b : Fin n → U) (a : Fin n → 𝒜)
    (k : Fin n) (x : 𝒜) :
    evalMatrix ℓ b (Function.update a k x) =
      (evalMatrix ℓ b a).updateRow k fun j => ℓ x (b j) := by
  ext i j
  by_cases hik : i = k
  · subst hik
    simp
  · simp [hik]

private lemma exists_evalMatrix_det_ne_zero [FiniteDimensional K U] (ℓ : 𝒜 → Module.Dual K U)
    (hsep : ∀ v : U, (∀ a : 𝒜, ℓ a v = 0) → v = 0) :
    ∃ f : Fin (Module.finrank K U) → 𝒜, (evalMatrix ℓ (Module.finBasis K U) f).det ≠ 0 := by
  have hker : ⨅ a : 𝒜, LinearMap.ker (ℓ a) = ⊥ :=
    eq_bot_iff.2 fun v hv => hsep v fun a => (Submodule.mem_iInf _).1 hv a
  obtain ⟨f, hf⟩ := Module.Dual.exists_bijective_pi_of_iInf_ker_eq_bot ℓ hker
  have hunit := LinearEquiv.isUnit_det (LinearEquiv.ofBijective (LinearMap.pi (ℓ ∘ f)) hf)
    (Module.finBasis K U) (Pi.basisFun K (Fin (Module.finrank K U)))
  have hmat : LinearMap.toMatrix (Module.finBasis K U) (Pi.basisFun K (Fin (Module.finrank K U)))
      (LinearEquiv.ofBijective (LinearMap.pi (ℓ ∘ f)) hf) =
      evalMatrix ℓ (Module.finBasis K U) f := by
    ext i j
    simp [LinearMap.toMatrix_apply]
  rw [hmat] at hunit
  exact ⟨f, hunit.ne_zero⟩

/-- If `a` maximizes `‖φ (det (evalMatrix ℓ b ·))‖`, then every `ℓ x` has image norm at most `1`
on the vectors `∑ j, (evalMatrix ℓ b a)⁻¹ j k • b j`. -/
private lemma _root_.RingHom.norm_eval_le_one_of_isMaxOn {L : Type*} [NormedField L] (φ : K →+* L)
    (ℓ : 𝒜 → Module.Dual K U) (b : Fin n → U) (a : Fin n → 𝒜)
    (ha_max : ∀ f : Fin n → 𝒜, ‖φ (evalMatrix ℓ b f).det‖ ≤ ‖φ (evalMatrix ℓ b a).det‖)
    (x : 𝒜) (k : Fin n) :
    ‖φ (ℓ x (∑ j, (evalMatrix ℓ b a)⁻¹ j k • b j))‖ ≤ 1 := by
  by_cases ha : (evalMatrix ℓ b a).det = 0
  · simp [Matrix.nonsing_inv_apply_not_isUnit _ (by simp [ha] : ¬IsUnit (evalMatrix ℓ b a).det)]
  set z : Fin n → U := fun k => ∑ j, (evalMatrix ℓ b a)⁻¹ j k • b j
  -- `evalMatrix ℓ b (update a k x) * (evalMatrix ℓ b a)⁻¹` is the identity matrix with row `k`
  -- replaced by `ℓ x ∘ z`, so Cramer's rule computes `ℓ x (z k)` as a ratio of determinants.
  have hdet : ℓ x (z k) =
      (evalMatrix ℓ b (Function.update a k x)).det / (evalMatrix ℓ b a).det := by
    rw [← Matrix.det_updateRow_one k fun j => ℓ x (z j), ← evalMatrix_inv_eq_one ℓ b a ha,
      ← evalMatrix_update, ← evalMatrix_mul, Matrix.det_mul, Matrix.det_nonsing_inv,
      Ring.inverse_eq_inv', div_eq_mul_inv]
  rw [hdet, map_div₀, norm_div]
  exact div_le_one_of_le₀ (ha_max _) (norm_nonneg _)

/-- **Auerbach's lemma for a compact family of linear forms.**
Let `U` be a finite-dimensional vector space over a field `K`, `𝒜` a compact topological space,
`(ℓ_a)_{a ∈ 𝒜}` a family of linear forms on `U` whose only common zero is `0`, and `φ : K →+* L`
a ring homomorphism into a normed field `L` such that `a ↦ φ (ℓ a v)` is continuous for every
`v : U`. Then there exist `a : Fin (finrank K U) → 𝒜` and a basis
`z : Module.Basis (Fin (finrank K U)) K U` such that `ℓ (a i) (z j) = if i = j then 1 else 0`
and `‖φ (ℓ x (z k))‖ ≤ 1` for all `x : 𝒜` and all `k`. -/
theorem _root_.RingHom.exists_auerbachBasis {L : Type*} [FiniteDimensional K U] [TopologicalSpace 𝒜]
    [CompactSpace 𝒜] [NormedField L] (φ : K →+* L) (ℓ : 𝒜 → Module.Dual K U)
    (hcont : ∀ v : U, Continuous fun a : 𝒜 => φ (ℓ a v))
    (hsep : ∀ v : U, (∀ a : 𝒜, ℓ a v = 0) → v = 0) :
    ∃ (a : Fin (Module.finrank K U) → 𝒜) (z : Module.Basis (Fin (Module.finrank K U)) K U),
      (∀ i j, ℓ (a i) (z j) = if i = j then 1 else 0) ∧
      ∀ (x : 𝒜) (k : Fin (Module.finrank K U)), ‖φ (ℓ x (z k))‖ ≤ 1 := by
  set n := Module.finrank K U
  let b := Module.finBasis K U
  by_cases hn0 : n = 0
  · have : IsEmpty (Fin n) := by rw [hn0]; infer_instance
    exact ⟨isEmptyElim, b, fun i => isEmptyElim i, fun _ k => isEmptyElim k⟩
  have : Nonempty (Fin n) := ⟨⟨0, Nat.pos_of_ne_zero hn0⟩⟩
  obtain ⟨f₀, hf₀⟩ := exists_evalMatrix_det_ne_zero ℓ hsep
  have : Nonempty (Fin n → 𝒜) := ⟨f₀⟩
  have hM_cont : Continuous fun f : Fin n → 𝒜 => ‖φ (evalMatrix ℓ b f).det‖ := by
    simp_rw [RingHom.map_det]
    refine continuous_norm.comp (Continuous.matrix_det ?_)
    exact continuous_pi fun i => continuous_pi fun j => (hcont (b j)).comp (continuous_apply i)
  obtain ⟨a, -, ha_max⟩ := isCompact_univ.exists_isMaxOn Set.univ_nonempty hM_cont.continuousOn
  have ha_det : (evalMatrix ℓ b a).det ≠ 0 := by
    intro h0
    have hle : ‖φ (evalMatrix ℓ b f₀).det‖ ≤ ‖φ (evalMatrix ℓ b a).det‖ := ha_max (Set.mem_univ f₀)
    rw [h0, map_zero, norm_zero] at hle
    exact (norm_pos_iff.mpr ((map_ne_zero φ).mpr hf₀)).not_ge hle
  let zvec : Fin n → U := fun k => ∑ j, (evalMatrix ℓ b a)⁻¹ j k • b j
  have hdual (i k : Fin n) : ℓ (a i) (zvec k) = if i = k then 1 else 0 := by
    have h := congrFun (congrFun (evalMatrix_inv_eq_one ℓ b a ha_det) i) k
    rwa [evalMatrix_apply, Matrix.one_apply] at h
  have hz_li : LinearIndependent K zvec := by
    rw [Fintype.linearIndependent_iff]
    intro c hc i
    simpa [map_sum, hdual] using congrArg (ℓ (a i)) hc
  let z : Module.Basis (Fin n) K U :=
    basisOfLinearIndependentOfCardEqFinrank' zvec hz_li (Fintype.card_fin n)
  have hz_apply (k : Fin n) : z k = zvec k := by
    simp [z, coe_basisOfLinearIndependentOfCardEqFinrank']
  refine ⟨a, z, fun i j => by rw [hz_apply]; exact hdual i j, fun x k => ?_⟩
  rw [hz_apply]
  exact φ.norm_eval_le_one_of_isMaxOn ℓ b a (fun f => ha_max (Set.mem_univ f)) x k

end TauCeti
