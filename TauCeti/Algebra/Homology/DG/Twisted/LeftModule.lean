/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.DG.Twisted.Complex
public import TauCeti.Algebra.Homology.DG.Bimodule.Defs
import TauCeti.Algebra.Ring.NegOnePow

/-!
# The twisted complex as a differential graded left module

Let `(ℳ, dM)` be a differential graded `(A, B)`-bimodule and `m : P → P → B` a matrix of
coefficients in `B`.  The twisted differential `TauCeti.twistedDifferential m ℳ dM` on `P → M` is
built from the right `B`-action; the left `A`-action, applied pointwise, commutes with it up to the
Koszul sign, so the twisted complex is a differential graded left `A`-module
(`isDGLeftModule_twistedDifferential`).

The case `A = B = M` of the regular bimodule is the complex `K_m` of free left modules of rank one
with `d x = Σ_y m x y · y`, coefficients on the left: for a twisting cocycle `m`, this is
`TauCeti.TwistingCocycle.isDGLeftModule_twistedDifferential`, and `d² = 0` is the twisting
equation.  Through `TauCeti.IsDGLeftModule.gradedOppositeRight`, every differential graded left
module is a differential graded right module over the Koszul-signed graded opposite algebra; this
is the form in which `K_m` is a complex of right modules over the opposite algebra.

To state the module structure, the total grading `TauCeti.twistedTotalGrading ℳ ind` is given its
decomposition of `P → M` (`instDecompositionTwistedTotalGrading`) and the compatibility of the
pointwise left action with the degrees (`instGradedSMulTwistedTotalGrading`).

## Main results

* `TauCeti.iSupIndep_twistedTotalGrading`, `TauCeti.iSup_twistedTotalGrading_eq_top`: the total
  grading is an internal direct sum decomposition of `P → M`.
* `TauCeti.twistedDifferential_smul`: the Koszul–Leibniz rule for the pointwise left action.
* `TauCeti.isDGLeftModule_twistedDifferential`: the twisted complex of a differential graded
  bimodule is a differential graded left module.
* `TauCeti.TwistingCocycle.isDGLeftModule_twistedDifferential`: the complex `K_m` of a twisting
  cocycle is a differential graded left module over the algebra.

## References

* J.-F. Barraud, M. Damian, V. Humilière, A. Oancea, *Floer homology with DG coefficients.
  Applications to cotangent bundles*, arXiv:2404.07953, Section 1.4.
* B. Keller, *Deriving DG categories*, Section 6.1.
-/

public section

open DirectSum MulOpposite

namespace TauCeti

universe uR uA uB uM uP

section TotalGrading

variable {R : Type uR} {M : Type uM} {P : Type uP} {ind : P → ℤ}

section GradedSMul

variable {A : Type uA} [Semiring R] [AddCommMonoid A] [Module R A] [AddCommMonoid M] [Module R M]
  [SMul A M] {𝒜 : ℤ → Submodule R A} {ℳ : ℤ → Submodule R M}

/-- The pointwise left action on `P → M` adds degrees in the total grading, as soon as the action
on `M` does. -/
instance instGradedSMulTwistedTotalGrading [SetLike.GradedSMul 𝒜 ℳ] :
    SetLike.GradedSMul 𝒜 (twistedTotalGrading ℳ ind) where
  smul_mem := by
    intro i n a f ha hf
    rw [mem_twistedTotalGrading_iff] at hf ⊢
    intro x
    have := SetLike.GradedSMul.smul_mem ha (hf x)
    simpa only [vadd_eq_add, add_assoc, Pi.smul_apply] using this

end GradedSMul

section Decomposition

variable [Ring R] [AddCommGroup M] [Module R M]
  (ℳ : ℤ → Submodule R M) [DirectSum.Decomposition ℳ]

/-- The pieces of the total grading are independent. -/
theorem iSupIndep_twistedTotalGrading : iSupIndep (twistedTotalGrading ℳ ind) := by
  rw [iSupIndep_def]
  intro n
  rw [Submodule.disjoint_def]
  intro f hf hf'
  have hle : (⨆ (k) (_ : k ≠ n), twistedTotalGrading ℳ ind k) ≤
      Submodule.pi Set.univ fun x ↦ ⨆ (j) (_ : j ≠ n + ind x), ℳ j := by
    refine iSup₂_le fun k hk g hg ↦ ?_
    rw [mem_twistedTotalGrading_iff] at hg
    rw [Submodule.mem_pi]
    intro x _
    exact Submodule.mem_iSup_of_mem (k + ind x)
      (Submodule.mem_iSup_of_mem (fun h ↦ hk (add_right_cancel h)) (hg x))
  have hind := (DirectSum.Decomposition.isInternal ℳ).submodule_iSupIndep
  rw [iSupIndep_def] at hind
  rw [mem_twistedTotalGrading_iff] at hf
  funext x
  exact Submodule.disjoint_def.mp (hind (n + ind x)) (f x) (hf x)
    (Submodule.mem_pi.mp (hle hf') x (Set.mem_univ x))

variable [Finite P]

/-- The pieces of the total grading span `P → M` when `P` is finite. -/
theorem iSup_twistedTotalGrading_eq_top : (⨆ n, twistedTotalGrading ℳ ind n) = ⊤ := by
  classical
  let _ := Fintype.ofFinite P
  rw [eq_top_iff]
  intro f _
  rw [← Finset.univ_sum_single f]
  refine Submodule.sum_mem _ fun x _ ↦ ?_
  have hsum : (Pi.single x (f x) : P → M) =
      ∑ q ∈ (decompose ℳ (f x)).support, (Pi.single x (decompose ℳ (f x) q : M) : P → M) := by
    rw [← LinearMap.coe_single R (fun _ : P ↦ M), ← map_sum, DirectSum.sum_support_decompose]
  rw [hsum]
  refine Submodule.sum_mem _ fun q _ ↦ Submodule.mem_iSup_of_mem (q - ind x) ?_
  rw [mem_twistedTotalGrading_iff]
  intro y
  by_cases hy : y = x
  · subst hy
    rw [Pi.single_eq_same, sub_add_cancel]
    exact SetLike.coe_mem _
  · rw [Pi.single_eq_of_ne hy]
    exact zero_mem _

/-- The total grading is an internal direct sum decomposition of `P → M`. -/
noncomputable instance instDecompositionTwistedTotalGrading :
    DirectSum.Decomposition (twistedTotalGrading ℳ ind) :=
  (DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top
    (iSupIndep_twistedTotalGrading ℳ) (iSup_twistedTotalGrading_eq_top ℳ)).chooseDecomposition

end Decomposition

end TotalGrading

section LeftModule

variable {R : Type uR} {A : Type uA} {B : Type uB} {M : Type uM}
  [CommRing R] [Ring A] [Ring B] [Algebra R A] [Algebra R B]
  [AddCommGroup M] [Module R M] [Module A M] [Module Bᵐᵒᵖ M]
  [IsScalarTower R A M] [IsScalarTower R Bᵐᵒᵖ M] [SMulCommClass R Bᵐᵒᵖ M] [SMulCommClass A Bᵐᵒᵖ M]
  {P : Type uP} [Fintype P] {ind : P → ℤ}
  (m : P → P → B) {ℳ : ℤ → Submodule R M} [DirectSum.Decomposition ℳ] (dM : M →ₗ[R] M)
  {𝒜 : ℤ → Submodule R A} [GradedAlgebra 𝒜] {dA : A →ₗ[R] A} {hA : IsDGAlgebra 𝒜 dA}
  {ℬ : ℤ → Submodule R B} [GradedAlgebra ℬ] {dB : B →ₗ[R] B} {hB : IsDGAlgebra ℬ dB}
  [SetLike.GradedSMul 𝒜 ℳ] [SetLike.GradedSMul (InternalGrading.ofDecomposition ℬ).opposite.piece ℳ]

/-- **The Koszul–Leibniz rule** of the twisted differential for the pointwise left action of a
homogeneous element of the algebra. -/
theorem twistedDifferential_smul (hM : IsDGBimodule hA hB ℳ dM) {p : ℤ} {a : A} (ha : a ∈ 𝒜 p)
    (f : P → M) :
    twistedDifferential m ℳ dM (a • f) =
      dA a • f + p.negOnePow • (a • twistedDifferential m ℳ dM f) := by
  classical
  -- Reduce to a homogeneous elementary tensor `α ⊗ x`.
  suffices key : ∀ (x : P) {q : ℤ} {α : M}, α ∈ ℳ q →
      twistedDifferential m ℳ dM (a • (Pi.single x α : P → M)) =
        dA a • (Pi.single x α : P → M) +
          p.negOnePow • (a • twistedDifferential m ℳ dM (Pi.single x α)) by
    rw [← Finset.univ_sum_single f, Finset.smul_sum, map_sum, Finset.smul_sum, map_sum,
      Finset.smul_sum, Finset.smul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun x _ ↦ ?_
    generalize f x = α
    induction α using DirectSum.Decomposition.inductionOn ℳ with
    | zero => simp
    | @homogeneous i α => exact key x α.2
    | add α β hα hβ =>
      rw [Pi.single_add, smul_add, map_add, hα, hβ, smul_add, map_add, smul_add, smul_add]
      abel
  intro x q α hα
  -- The two actions on `P → M` are pointwise, so they pass through `Pi.single`.
  have hsingle : ∀ (z : P) (b : A) (β : M), b • (Pi.single z β : P → M) = Pi.single z (b • β) := by
    intro z b β
    ext y
    simp only [Pi.smul_apply, Pi.single_apply]
    split_ifs <;> simp
  have hsingle' : ∀ (z : P) (ε : ℤˣ) (β : M),
      ε • (Pi.single z β : P → M) = Pi.single z (ε • β) := by
    intro z ε β
    ext y
    simp only [Pi.smul_apply, Pi.single_apply]
    split_ifs <;> simp
  rw [hsingle, twistedDifferential_single m dM x (SetLike.GradedSMul.smul_mem ha hα),
    twistedDifferential_single m dM x hα, hM.leibniz ha α, Pi.single_add, smul_add,
    Finset.smul_sum, hsingle, smul_add, Finset.smul_sum, hsingle, hsingle', add_assoc]
  congr 1
  congr 1
  refine Finset.sum_congr rfl fun y _ ↦ ?_
  rw [hsingle, hsingle']
  congr 1
  rw [vadd_eq_add, ← smul_comm a (op (m x y))]
  simp only [negOnePow_smul_eq_negOnePowCast_smul (R := R), negOnePowCast_eq_intCast,
    Int.negOnePow_add, mul_smul]
  rw [smul_comm (((q.negOnePow : ℤ) : R)) a]

/-- **The twisted complex of a differential graded bimodule is a differential graded left
module**, for the pointwise action of the left algebra. -/
theorem isDGLeftModule_twistedDifferential (hm : ∀ x y, m x y ∈ ℬ (ind y - ind x + 1))
    (htw : ∀ x y, dB (m x y) = ∑ z, (ind x - ind z).negOnePow • (m x z * m z y))
    (hM : IsDGBimodule hA hB ℳ dM) :
    IsDGLeftModule hA (twistedTotalGrading ℳ ind) (twistedDifferential m ℳ dM) where
  isHomogeneous := LinearMap.isHomogeneous_def.mpr fun _ _ hf ↦
    twistedDifferential_mem_twistedTotalGrading m dM hm hM.isHomogeneous hf
  sq_zero := twistedDifferential_sq_zero m dM hm htw hM.isDGRightModule
  leibniz ha f := twistedDifferential_smul m dM hM ha f

end LeftModule

namespace TwistingCocycle

variable {R : Type uR} {A : Type uA} [CommRing R] [Ring A] [Algebra R A]
  {P : Type uP} [Fintype P] {ind : P → ℤ}
  {𝒜 : ℤ → Submodule R A} [GradedAlgebra 𝒜] {d : A →ₗ[R] A} {h : IsDGAlgebra 𝒜 d}

/-- **The complex `K_m` of a twisting cocycle is a differential graded left module** over the
algebra: on `P → A`, with the pointwise left action, `d x = Σ_y m x y · y` has `d² = 0` by the
twisting equation. -/
theorem isDGLeftModule_twistedDifferential (m : TwistingCocycle 𝒜 d P ind) :
    IsDGLeftModule h (twistedTotalGrading 𝒜 ind) (twistedDifferential m.m 𝒜 d) :=
  TauCeti.isDGLeftModule_twistedDifferential m.m d m.mem_graded m.twisting h.isDGBimodule

end TwistingCocycle

end TauCeti
