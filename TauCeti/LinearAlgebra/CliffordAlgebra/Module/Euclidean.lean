/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.Basic
public import TauCeti.LinearAlgebra.CliffordAlgebra.Module.Metric
public import TauCeti.LinearAlgebra.CliffordAlgebra.RealForm.Basic

import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.LinearAlgebra.Complex.FiniteDimensional
import TauCeti.LinearAlgebra.CliffordAlgebra.Classification
import TauCeti.LinearAlgebra.CliffordAlgebra.RealForm.Four
import TauCeti.LinearAlgebra.QuadraticForm.PosDef
import TauCeti.Topology.Algebra.Module.FiniteDimension

/-!
# Euclidean actions of negative-definite Clifford algebras

Given a representation of a negative-definite real Clifford algebra `Cliff(0, q)` on a
finite-dimensional real vector space `W`, averaging any positive-definite quadratic form over the
finite signed monomial group equips `W` with an inner product for which every Clifford vector acts
skew-adjointly (`AlgHom.exists_posDef_isSymm_isSkewAdjoint_map_cliffordAlgebraι`). Conjugating along
an isometric isomorphism between `W` and any finite-dimensional real inner product space `E` of the
same `finrank` produces a continuous-linear `CliffordAlgebra` representation on `E` by
skew-symmetric operators (`AlgHom.exists_skew_map_cliffordAlgebraι_of_finrank_eq`), hence `q`
pairwise anticommuting skew-symmetric continuous linear operators squaring to `-1`
(`AlgHom.exists_skew_sq_neg_id_anticommute_clm_of_finrank_eq`).

Combined with the real Clifford algebra models `Cliff(0, 1) ≃ₐ[ℝ] ℂ`,
`Cliff(0, 3) ≃ₐ[ℝ] ℍ[ℝ] × ℍ[ℝ]`, and `Cliff(0, 7) ≃ₐ[ℝ] M₈(ℝ) × M₈(ℝ)` (together with the empty
family for `n = 0`), this yields `n` pairwise anticommuting skew-symmetric continuous linear
operators squaring to `-1` on any `(n + 1)`-dimensional real inner product space for
`n ∈ {0, 1, 3, 7}` (`TauCeti.exists_skew_sq_neg_id_anticommute_clm`), the linear algebra behind
smooth orthonormal tangent frames on `S⁰`, `S¹`, `S³`, and `S⁷`.

## Main results

* `AlgHom.exists_skew_map_cliffordAlgebraι_of_finrank_eq`: if `CliffordAlgebra Q` (for `Q` with a
  finite orthogonal `-1`-basis) has a finite-dimensional real module `W`, then any
  finite-dimensional real inner product space `E` of equal `finrank` admits an algebra homomorphism
  `CliffordAlgebra Q →ₐ[ℝ] (E →L[ℝ] E)` under which every vector acts skew-symmetrically.
* `AlgHom.exists_skew_sq_neg_id_anticommute_clm_of_finrank_eq`: if `Cliff(0, q)` has a
  finite-dimensional real module `W`, then any finite-dimensional real inner product space `E` of
  equal `finrank` admits `q` pairwise anticommuting skew-symmetric continuous linear endomorphisms
  squaring to `-1`.
* `TauCeti.exists_skew_sq_neg_id_anticommute_clm`: for `n ∈ {0, 1, 3, 7}`, every
  `(n + 1)`-dimensional real inner product space admits `n` pairwise anticommuting skew-symmetric
  continuous linear endomorphisms squaring to `-1`.

## References

* H. B. Lawson and M.-L. Michelsohn, *Spin Geometry* (1989), Chapter I, §§4–5.
* A. Hatcher, *Vector Bundles and K-Theory*, §1.1 (orthogonal multiplications and tangent frames on
  `S¹`, `S³`, and `S⁷`).
-/

public section

open CliffordAlgebra Module TauCeti
open scoped InnerProductSpace Quaternion

namespace AlgHom

/-- If `CliffordAlgebra Q`, where `Q` has a finite orthogonal basis squaring to `-1`, admits a
finite-dimensional real module `W`, then any finite-dimensional real inner product space `E` of
equal `finrank` admits an algebra homomorphism `CliffordAlgebra Q →ₐ[ℝ] (E →L[ℝ] E)` under which
every vector acts skew-symmetrically. -/
theorem exists_skew_map_cliffordAlgebraι_of_finrank_eq
    {M W E : Type*} [AddCommGroup M] [Module ℝ M] {Q : QuadraticForm ℝ M}
    [AddCommGroup W] [Module ℝ W] [FiniteDimensional ℝ W]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    (ρ : CliffordAlgebra Q →ₐ[ℝ] Module.End ℝ W)
    {I : Type*} [_root_.Finite I] (b : Module.Basis I ℝ M)
    (hb : ∀ i j, i ≠ j → Q.IsOrtho (b i) (b j)) (hQ : ∀ i, Q (b i) = -1)
    (hdim : Module.finrank ℝ W = Module.finrank ℝ E) :
    ∃ σ : CliffordAlgebra Q →ₐ[ℝ] (E →L[ℝ] E),
      ∀ (v : M) (x y : E), ⟪σ (ι Q v) x, y⟫_ℝ = -⟪x, σ (ι Q v) y⟫_ℝ := by
  let w := Module.finBasis ℝ W
  let Q₀ : QuadraticForm ℝ W :=
    (QuadraticMap.weightedSumSquares ℝ (1 : Fin (Module.finrank ℝ W) → ℝ)).comp
      w.equivFun.toLinearMap
  have hQ₀ : Q₀.PosDef :=
    ((QuadraticMap.posDef_weightedSumSquares_iff _).mpr fun _ ↦ zero_lt_one).comp
      w.equivFun.toLinearMap w.equivFun.injective
  obtain ⟨B, hBpos, hBsymm, hBskew⟩ :=
    ρ.exists_posDef_isSymm_isSkewAdjoint_map_cliffordAlgebraι b hb hQ hQ₀
  -- Equip `W` with the averaged positive-definite symmetric form, then transport to `E`.
  let core : InnerProductSpace.Core ℝ W :=
    { inner x y := B x y
      conj_inner_symm x y := by simpa using hBsymm.eq y x
      re_inner_nonneg x := by simpa using hBpos.nonneg x
      add_left x y z := by simp
      smul_left x y r := by simp
      definite x hx := hBpos.anisotropic x (by simpa using hx) }
  let := core.toNormedAddCommGroup
  let : InnerProductSpace ℝ W := InnerProductSpace.ofCore core.toCore
  have hinner (x y : W) : inner ℝ x y = B x y := (rfl)
  let U : W ≃ₗᵢ[ℝ] E := (stdOrthonormalBasis ℝ W).equiv (stdOrthonormalBasis ℝ E) (finCongr hdim)
  let conjU : Module.End ℝ W ≃ₐ[ℝ] Module.End ℝ E := U.toLinearEquiv.conjAlgEquiv ℝ
  refine ⟨(Module.End.toContinuousLinearMap E).toAlgHom.comp (conjU.toAlgHom.comp ρ),
    fun v x y ↦ ?_⟩
  have hskewv : B (ρ (ι Q v) (U.symm x)) (U.symm y) = -B (U.symm x) (ρ (ι Q v) (U.symm y)) := by
    simpa only [Pi.neg_apply, map_neg] using hBskew v (U.symm x) (U.symm y)
  have happly (z : E) :
      ((Module.End.toContinuousLinearMap E).toAlgHom.comp (conjU.toAlgHom.comp ρ)) (ι Q v) z =
        U (ρ (ι Q v) (U.symm z)) := by
    simp [conjU]
  rw [happly, happly]
  calc
    ⟪U (ρ (ι Q v) (U.symm x)), y⟫_ℝ = ⟪U (ρ (ι Q v) (U.symm x)), U (U.symm y)⟫_ℝ := by
      rw [U.apply_symm_apply]
    _ = B (ρ (ι Q v) (U.symm x)) (U.symm y) := by rw [U.inner_map_map, hinner]
    _ = -B (U.symm x) (ρ (ι Q v) (U.symm y)) := hskewv
    _ = -⟪U (U.symm x), U (ρ (ι Q v) (U.symm y))⟫_ℝ := by rw [U.inner_map_map, hinner]
    _ = -⟪x, U (ρ (ι Q v) (U.symm y))⟫_ℝ := by rw [U.apply_symm_apply]

/-- If `Cliff(0, q)` admits a finite-dimensional real module `W`, then any finite-dimensional real
inner product space `E` of equal `finrank` admits `q` pairwise anticommuting skew-symmetric
continuous linear endomorphisms squaring to `-1`. -/
theorem exists_skew_sq_neg_id_anticommute_clm_of_finrank_eq {q : ℕ}
    {W E : Type*} [AddCommGroup W] [Module ℝ W] [FiniteDimensional ℝ W]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    (ρ : CliffordAlgebra (realCliffordForm 0 q) →ₐ[ℝ] Module.End ℝ W)
    (hdim : Module.finrank ℝ W = Module.finrank ℝ E) :
    ∃ A : Fin q → (E →L[ℝ] E),
      (∀ i x y, ⟪A i x, y⟫_ℝ = -⟪x, A i y⟫_ℝ) ∧
      (∀ i x, A i (A i x) = -x) ∧
      (∀ i j, i ≠ j → ∀ x, A i (A j x) + A j (A i x) = 0) := by
  let b : Module.Basis (Fin (0 + q)) ℝ (Fin (0 + q) → ℝ) := Pi.basisFun ℝ (Fin (0 + q))
  have hb : ∀ i j, i ≠ j → (realCliffordForm 0 q).IsOrtho (b i) (b j) := fun i j hij ↦ by
    simpa [b] using isOrtho_realCliffordForm_single hij 1 1
  have hQ : ∀ i, realCliffordForm 0 q (b i) = -1 := fun i ↦ by
    simp [b]
  obtain ⟨σ, hσ⟩ := ρ.exists_skew_map_cliffordAlgebraι_of_finrank_eq b hb hQ hdim
  let e : Fin q → Fin (0 + q) := Fin.cast (Nat.zero_add q).symm
  refine ⟨fun i ↦ σ (ι (realCliffordForm 0 q) (b (e i))), fun i ↦ hσ _, fun i x ↦ ?_,
    fun i j hij x ↦ ?_⟩
  · have hsq := congrArg (fun T : E →L[ℝ] E ↦ T x)
      (σ.map_cliffordAlgebraι_mul_self_of_eq_neg_one (hQ (e i)))
    simpa only [mul_apply_eq_comp, neg_apply, one_apply_eq_self] using hsq
  · have heij : e i ≠ e j := fun h ↦ hij ((Fin.cast_injective _) h)
    have hanti := congrArg (fun T : E →L[ℝ] E ↦ T x)
      (σ.map_cliffordAlgebraι_anticommute_of_isOrtho (hb (e i) (e j) heij))
    simpa only [add_apply, mul_apply_eq_comp, zero_apply] using hanti

end AlgHom

namespace TauCeti

private noncomputable def cliffordModuleZeroOne :
    CliffordAlgebra (realCliffordForm 0 1) →ₐ[ℝ] Module.End ℝ ℂ :=
  (Algebra.lmul ℝ ℂ).comp realCliffordZeroOneEquivComplex.toAlgHom

private noncomputable def cliffordModuleZeroThree :
    CliffordAlgebra (realCliffordForm 0 3) →ₐ[ℝ] Module.End ℝ ℍ[ℝ] :=
  (Algebra.lmul ℝ ℍ[ℝ]).comp
    ((AlgHom.fst ℝ ℍ[ℝ] ℍ[ℝ]).comp realCliffordZeroThreeEquivQuaternionProd.toAlgHom)

private theorem nonempty_cliffordModule_zero_seven :
    Nonempty (CliffordAlgebra (realCliffordForm 0 7) →ₐ[ℝ] Module.End ℝ (Fin 8 → ℝ)) := by
  obtain ⟨e⟩ := realClifford_classification_of_residue_eq_seven 0 7
    (by rw [realCliffordResidue_def])
  exact ⟨(Matrix.toLinAlgEquiv' (R := ℝ) (n := Fin 8)).toAlgHom.comp
    ((AlgHom.fst ℝ (Matrix (Fin 8) (Fin 8) ℝ) (Matrix (Fin 8) (Fin 8) ℝ)).comp e.toAlgHom)⟩

/-- For `n ∈ {0, 1, 3, 7}`, every `(n + 1)`-dimensional real inner product space `E` admits `n`
pairwise anticommuting skew-symmetric continuous linear endomorphisms squaring to `-1`. For
`n ∈ {1, 3, 7}`, these arise from the real Clifford algebras `Cliff(0, 1) ≃ₐ[ℝ] ℂ`,
`Cliff(0, 3) ≃ₐ[ℝ] ℍ[ℝ] × ℍ[ℝ]`, and `Cliff(0, 7) ≃ₐ[ℝ] M₈(ℝ) × M₈(ℝ)`. -/
theorem exists_skew_sq_neg_id_anticommute_clm {n : ℕ}
    (hn : n = 0 ∨ n = 1 ∨ n = 3 ∨ n = 7)
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (hE : Module.finrank ℝ E = n + 1) :
    ∃ A : Fin n → (E →L[ℝ] E),
      (∀ i x y, ⟪A i x, y⟫_ℝ = -⟪x, A i y⟫_ℝ) ∧
      (∀ i x, A i (A i x) = -x) ∧
      (∀ i j, i ≠ j → ∀ x, A i (A j x) + A j (A i x) = 0) := by
  have : FiniteDimensional ℝ E :=
    FiniteDimensional.of_finrank_pos (by rw [hE]; exact Nat.succ_pos n)
  rcases hn with rfl | rfl | rfl | rfl
  · exact ⟨Fin.elim0, fun i ↦ i.elim0, fun i ↦ i.elim0, fun i ↦ i.elim0⟩
  · exact cliffordModuleZeroOne.exists_skew_sq_neg_id_anticommute_clm_of_finrank_eq
      (Complex.finrank_real_complex.trans hE.symm)
  · exact cliffordModuleZeroThree.exists_skew_sq_neg_id_anticommute_clm_of_finrank_eq
      (Quaternion.finrank_eq_four.trans hE.symm)
  · obtain ⟨ρ⟩ := nonempty_cliffordModule_zero_seven
    exact ρ.exists_skew_sq_neg_id_anticommute_clm_of_finrank_eq
      ((by rw [Module.finrank_fin_fun] : Module.finrank ℝ (Fin 8 → ℝ) = 8).trans hE.symm)

end TauCeti
