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
coefficients in `B`, indexed by a finite set `P`.  The twisted differential
`TauCeti.twistedDifferential m ℳ dM` on `P → M` is built from the right `B`-action; the left
`A`-action, applied pointwise, commutes with it up to the Koszul sign, so the twisted complex is a
differential graded left `A`-module (`isDGLeftModule_twistedDifferential`).

The case `A = B = M` of the regular bimodule is the complex `K_m`: the free left module `P → A` on
the generators `x ∈ P`, with `x` in cohomological degree `-ind x` and `d x = Σ_y m x y · y`,
coefficients on the left.  For a twisting cocycle `m`, this is
`TauCeti.TwistingCocycle.isDGLeftModule_twistedDifferential`, and `d² = 0` is the twisting
equation.  Through `TauCeti.IsDGLeftModule.gradedOppositeRight`, every differential graded left
module is a differential graded right module over the Koszul-signed graded opposite algebra; this
is the form in which `K_m` is a complex of right modules over the opposite algebra.

The grading of the module is the total grading `TauCeti.twistedTotalGrading ℳ ind`, whose
decomposition of `P → M` and compatibility with the pointwise left action are in
`TauCeti.Algebra.Homology.DG.Twisted.Complex`.

## Main results

* `TauCeti.twistedDifferential_smul`: the Koszul–Leibniz rule for the pointwise left action, from
  its homogeneous case `TauCeti.twistedDifferential_smul_single`.
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

section Sign

variable {R : Type uR} {A : Type uA} {B : Type uB} {M : Type uM}
  [CommRing R] [Ring A] [Ring B] [Algebra R A]
  [AddCommGroup M] [Module R M] [Module A M] [Module Bᵐᵒᵖ M]
  [IsScalarTower R A M] [SMulCommClass A Bᵐᵒᵖ M]

include R in
/-- The sign bookkeeping of the Koszul–Leibniz rule: the Koszul sign of a product `a • α` of
degrees `p` and `q` splits as the sign of `a` times the sign of `α`, and the two actions commute. -/
private theorem negOnePow_add_smul_op_smul_smul (p q : ℤ) (a : A) (b : B) (α : M) :
    (p + q).negOnePow • (op b • (a • α)) = p.negOnePow • (a • (q.negOnePow • (op b • α))) := by
  -- The signs are moved to `R`-scalars, which commute with the `A`-action.
  rw [← smul_comm a (op b)]
  simp only [negOnePow_smul_eq_negOnePowCast_smul (R := R), Int.negOnePow_add, mul_smul]
  rw [smul_comm (negOnePowCast R q) a]

end Sign

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

/-- **The Koszul–Leibniz rule on a homogeneous elementary tensor**: for `a` of degree `p` and `α`
of degree `q`, `D (a • (α ⊗ x)) = dA a • (α ⊗ x) + (-1) ^ p a • D (α ⊗ x)`.  Both sides are
computed by `twistedDifferential_single` and compared through the left Leibniz rule of the
bimodule. -/
theorem twistedDifferential_smul_single [DecidableEq P] (hM : IsDGBimodule hA hB ℳ dM) {p : ℤ}
    {a : A} (ha : a ∈ 𝒜 p) (x : P) {q : ℤ} {α : M} (hα : α ∈ ℳ q) :
    twistedDifferential m ℳ dM (a • (Pi.single x α : P → M)) =
      dA a • (Pi.single x α : P → M) +
        p.negOnePow • (a • twistedDifferential m ℳ dM (Pi.single x α)) := by
  simp only [← Pi.single_smul']
  rw [twistedDifferential_single m dM x (SetLike.GradedSMul.smul_mem ha hα),
    twistedDifferential_single m dM x hα, hM.leibniz ha α, vadd_eq_add]
  simp only [Pi.single_add, smul_add, Finset.smul_sum, ← Pi.single_smul',
    negOnePow_add_smul_op_smul_smul (R := R), add_assoc]

/-- **The Koszul–Leibniz rule** of the twisted differential for the pointwise left action of a
homogeneous element of the algebra. -/
theorem twistedDifferential_smul (hM : IsDGBimodule hA hB ℳ dM) {p : ℤ} {a : A} (ha : a ∈ 𝒜 p)
    (f : P → M) :
    twistedDifferential m ℳ dM (a • f) =
      dA a • f + p.negOnePow • (a • twistedDifferential m ℳ dM f) := by
  classical
  -- Both sides are additive in `f`; reduce to the homogeneous elementary tensors `α ⊗ x`.
  rw [← Finset.univ_sum_single f, Finset.smul_sum, map_sum, Finset.smul_sum, map_sum,
    Finset.smul_sum, Finset.smul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun x _ ↦ ?_
  generalize f x = α
  induction α using DirectSum.Decomposition.inductionOn ℳ with
  | zero => simp
  | @homogeneous i α => exact twistedDifferential_smul_single m dM hM ha x α.2
  | add α β hα hβ =>
    rw [Pi.single_add, smul_add, map_add, hα, hβ, smul_add, map_add, smul_add, smul_add]
    abel

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
algebra: on the free left module `P → A`, with the pointwise left action, `d x = Σ_y m x y · y`
has `d² = 0` by the twisting equation. -/
theorem isDGLeftModule_twistedDifferential (m : TwistingCocycle 𝒜 d P ind) :
    IsDGLeftModule h (twistedTotalGrading 𝒜 ind) (twistedDifferential m.m 𝒜 d) :=
  TauCeti.isDGLeftModule_twistedDifferential m.m d m.mem_graded m.twisting h.isDGBimodule

end TwistingCocycle

end TauCeti
