/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Distribution.Symmetry
public import TauCeti.Geometry.Symplectic.Hamiltonian.LieAlgebra
public import TauCeti.Geometry.Symplectic.Lagrangian.Basic

/-!
# Real polarizations and their observables

A **real polarization** of a symplectic manifold `(M, σ)` is an involutive smooth distribution `P`
whose fibres are Lagrangian subspaces of the tangent spaces
(`TauCeti.SmoothTwoForm.IsNondegenerate.IsRealPolarization`). It is the input of geometric
quantization: the quantum states are the sections of the prequantum line that are covariantly
constant along `P`, and the classical observables that act on them are the Hamiltonians whose flows
preserve `P`.

This file builds the classical side of that picture, with the conventions `ι_{X_f} σ = df` and
`{f, g} = σ(X_f, X_g)` of `TauCeti.Geometry.Symplectic.Hamiltonian.Manifold`.

* The **observable Lie algebra** of a distribution `P`
  (`TauCeti.SmoothTwoForm.observableLieSubalgebra`) consists of the smooth functions `f` whose
  Hamiltonian vector field preserves `P`: `[X_f, Y]` is tangent to `P` for every local smooth
  vector field `Y` tangent to `P` (`TauCeti.SmoothTwoForm.mem_observableLieSubalgebra_iff`). It is
  a Lie subalgebra of the Poisson Lie algebra, the preimage of the Lie algebra of vector fields
  preserving `P` under the Lie algebra homomorphism `f ↦ -X_f`, and it contains the locally
  constant functions (`TauCeti.SmoothTwoForm.mem_observableLieSubalgebra_of_mem_ker`).
* If the fibres of `P` are coisotropic, the Hamiltonian vector field of a basic function `a`, one
  whose differential vanishes on `P`, is tangent to `P`
  (`TauCeti.SmoothTwoForm.IsNondegenerate.hamiltonianVectorField_mem_of_isCoisotropic`), because
  `σ(v, X_a) = -da(v) = 0` for `v ∈ P`. Consequently basic functions Poisson-commute
  (`TauCeti.SmoothTwoForm.IsNondegenerate.poissonBracket_eq_zero_of_isCoisotropic`).
* If moreover `P` is involutive, as for a real polarization, the basic functions are observables
  (`TauCeti.SmoothTwoForm.mem_observableLieSubalgebra_of_mem_distributionBasicSubalgebra`), and
  the observables form a module over them
  (`TauCeti.SmoothTwoForm.poissonLieAlgebraEquiv_symm_mul_mem_observableLieSubalgebra`): from
  `X_{af} = a X_f + f X_a`, the field `a X_f` preserves `P` because `a` is constant along `P`, and
  `f X_a` is tangent to the involutive `P`.

A Lagrangian subspace of a symplectic vector space, translated to every point, is a real
polarization of the constant symplectic form (`TauCeti.SymplecticForm.isRealPolarization_const`).
For the standard form on `V × V`, the momentum directions `0 × V` are Lagrangian
(`TauCeti.SymplecticForm.isLagrangian_prod_bot_top`) and give the vertical polarization.

## References

* M. Schottenloher, *Lecture Notes on Geometric Quantization*, version 15.6, 2025,
  Definition 9.8 (real polarizations).
* N. M. J. Woodhouse, *Geometric Quantization*, 2nd ed., Oxford University Press, 1992
  (real polarizations and the observables preserving them).
* J. Śniatycki, *Geometric Quantization and Quantum Mechanics*, Applied Mathematical Sciences 30,
  Springer, 1980.
-/

public section

noncomputable section

open Bundle Module VectorField
open scoped ContDiff Manifold

namespace TauCeti

namespace SmoothTwoForm

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] {σ : SmoothTwoForm I M} {P : Π x : M, Submodule ℝ (TangentSpace I x)}

/-! ### Real polarizations -/

namespace IsNondegenerate

variable (hσ : σ.IsNondegenerate)

/-- A **real polarization** of a fiberwise nondegenerate two-form `σ` is a smooth distribution `P`
whose fibres are Lagrangian subspaces of the tangent spaces, `P_x^σ = P_x`, and which is
involutive. Its rank is necessarily half the dimension of `M`. -/
structure IsRealPolarization (P : Π x : M, Submodule ℝ (TangentSpace I x)) : Prop where
  /-- A real polarization is a smooth distribution of half the dimension of `M`. -/
  isContMDiffDistribution : IsContMDiffDistribution I ∞ (finrank ℝ E / 2) P
  /-- The fibres of a real polarization are Lagrangian. -/
  isLagrangian (x : M) : (hσ.symplecticFormAt x).IsLagrangian (P x)
  /-- A real polarization is involutive. -/
  isInvolutiveDistribution : IsInvolutiveDistribution I P

variable {hσ} in
/-- **A real polarization has half the dimension of `M`**: `2 dim P_x = dim M`. -/
theorem IsRealPolarization.two_mul_finrank (hP : hσ.IsRealPolarization P) (x : M) :
    2 * finrank ℝ (P x) = finrank ℝ E :=
  (hP.isLagrangian x).two_mul_finrank

/-- **Hamiltonian vector fields of basic functions are tangent to a coisotropic distribution.** If
the differential of `f` vanishes on a coisotropic subspace `P_x`, then `X_f(x) ∈ P_x`. -/
theorem hamiltonianVectorField_mem_of_isCoisotropic {f : M → ℝ} {x : M}
    (hco : (hσ.symplecticFormAt x).IsCoisotropic (P x))
    (hf : ∀ v ∈ P x, mvfderiv I f x v = 0) :
    σ.hamiltonianVectorField f x ∈ P x := by
  -- `σ(v, X_f) = -df(v) = 0` for `v ∈ P_x`, so `X_f(x)` lies in `P_x^σ ⊆ P_x`.
  refine SymplecticForm.isCoisotropic_iff_le.1 hco <|
    SymplecticForm.mem_orthogonal_iff.2 fun v hv ↦ ?_
  rw [symplecticFormAt_apply, SmoothBundleForm.eval₂_swap σ x, hσ.eval₂_hamiltonianVectorField,
    hf v hv, neg_zero]

/-- **Basic functions Poisson-commute.** If the differentials of `f` and `g` vanish on a
coisotropic subspace `P_x`, then `{f, g}(x) = 0`. -/
theorem poissonBracket_eq_zero_of_isCoisotropic {f g : M → ℝ} {x : M}
    (hco : (hσ.symplecticFormAt x).IsCoisotropic (P x))
    (hf : ∀ v ∈ P x, mvfderiv I f x v = 0) (hg : ∀ v ∈ P x, mvfderiv I g x v = 0) :
    σ.poissonBracket f g x = 0 := by
  rw [hσ.poissonBracket_eq_mvfderiv, hf _ (hσ.hamiltonianVectorField_mem_of_isCoisotropic hco hg)]

end IsNondegenerate

/-! ### The observable Lie algebra -/

variable (σ) in
/-- The **observable Lie algebra** of a distribution `P`: the smooth functions whose Hamiltonian
vector field preserves `P`, in the sense that its bracket with every local smooth vector field
tangent to `P` is tangent to `P`. It is the preimage of the Lie algebra of vector fields preserving
`P` under the Lie algebra homomorphism `f ↦ -X_f`, hence a Lie subalgebra of the Poisson Lie
algebra. For a real polarization these are the classical observables that preserve the polarized
sections in geometric quantization. -/
def observableLieSubalgebra (hσ : σ.IsSymplectic) (P : Π x : M, Submodule ℝ (TangentSpace I x)) :
    LieSubalgebra ℝ (σ.PoissonLieAlgebra hσ) :=
  (distributionPreservingLieSubalgebra I P).comap
    ((σ.symplecticLieSubalgebra hσ.isClosed).incl.comp (σ.negHamiltonianLieHom hσ))

/-- A smooth function is an observable for `P` exactly when its Hamiltonian vector field preserves
`P`. -/
@[simp]
theorem mem_observableLieSubalgebra_iff {hσ : σ.IsSymplectic} {f : σ.PoissonLieAlgebra hσ} :
    f ∈ σ.observableLieSubalgebra hσ P ↔
      PreservesDistribution I P (σ.hamiltonianVectorField (σ.poissonLieAlgebraEquiv hσ f)) := by
  have hneg : ⇑((LieAlgebroid.tangent I M).sectionsEquiv
      (σ.negHamiltonianLieHom hσ f : (LieAlgebroid.tangent I M).Sections)) =
      -σ.hamiltonianVectorField (σ.poissonLieAlgebraEquiv hσ f) :=
    funext (negHamiltonianLieHom_apply hσ f)
  rw [observableLieSubalgebra, LieSubalgebra.mem_comap, LieHom.comp_apply,
    LieSubalgebra.coe_incl, mem_distributionPreservingLieSubalgebra_iff, hneg]
  exact ⟨fun h ↦ neg_neg (σ.hamiltonianVectorField _) ▸ h.neg, PreservesDistribution.neg⟩

/-- **Locally constant functions are observables.** A function in the kernel of `f ↦ -X_f`, that
is, with vanishing differential, has zero Hamiltonian vector field and preserves every
distribution. -/
theorem mem_observableLieSubalgebra_of_mem_ker {hσ : σ.IsSymplectic} {f : σ.PoissonLieAlgebra hσ}
    (hf : f ∈ (σ.negHamiltonianLieHom hσ).ker) : f ∈ σ.observableLieSubalgebra hσ P := by
  rw [observableLieSubalgebra, LieSubalgebra.mem_comap, LieHom.comp_apply, LieHom.mem_ker.1 hf,
    map_zero]
  exact zero_mem _

/-- **Basic functions are observables.** If the fibres of `P` are coisotropic and `P` is involutive,
as for a real polarization `hP` (via `(hP.isLagrangian x).isCoisotropic` and
`hP.isInvolutiveDistribution`), every smooth function whose differential vanishes on `P` is an
observable: its Hamiltonian vector field is tangent to `P`, hence preserves the involutive `P`. -/
theorem mem_observableLieSubalgebra_of_mem_distributionBasicSubalgebra {hσ : σ.IsSymplectic}
    (hco : ∀ x, (hσ.isNondegenerate.symplecticFormAt x).IsCoisotropic (P x))
    (hP : IsInvolutiveDistribution I P) {f : σ.PoissonLieAlgebra hσ}
    (hf : σ.poissonLieAlgebraEquiv hσ f ∈ distributionBasicSubalgebra I P) :
    f ∈ σ.observableLieSubalgebra hσ P := by
  rw [mem_observableLieSubalgebra_iff]
  rw [mem_distributionBasicSubalgebra_iff] at hf
  exact hP.preservesDistribution
    ((hσ.isNondegenerate.contMDiff_hamiltonianVectorField le_rfl
      (σ.poissonLieAlgebraEquiv hσ f).contMDiff).mdifferentiable (by simp))
    fun x ↦ hσ.isNondegenerate.hamiltonianVectorField_mem_of_isCoisotropic (hco x) (hf x)

/-- **The observables form a module over the basic functions.** If the fibres of `P` are
coisotropic and `P` is involutive, then the product `a f` of a basic function `a` and an observable
`f` is an observable: `X_{af} = a X_f + f X_a`, where `a X_f` preserves `P` because `a` is constant
along `P`, and `f X_a` is tangent to the involutive `P`. -/
theorem poissonLieAlgebraEquiv_symm_mul_mem_observableLieSubalgebra {hσ : σ.IsSymplectic}
    (hco : ∀ x, (hσ.isNondegenerate.symplecticFormAt x).IsCoisotropic (P x))
    (hP : IsInvolutiveDistribution I P) {a : C^∞⟮I, M; ℝ⟯}
    (ha : a ∈ distributionBasicSubalgebra I P) {f : σ.PoissonLieAlgebra hσ}
    (hf : f ∈ σ.observableLieSubalgebra hσ P) :
    (σ.poissonLieAlgebraEquiv hσ).symm (a * σ.poissonLieAlgebraEquiv hσ f) ∈
      σ.observableLieSubalgebra hσ P := by
  set g := σ.poissonLieAlgebraEquiv hσ f
  rw [mem_distributionBasicSubalgebra_iff] at ha
  rw [mem_observableLieSubalgebra_iff] at hf ⊢
  rw [LinearEquiv.apply_symm_apply, ContMDiffMap.coe_mul]
  have hXg := hσ.isNondegenerate.contMDiff_hamiltonianVectorField le_rfl g.contMDiff
  have hXa := hσ.isNondegenerate.contMDiff_hamiltonianVectorField le_rfl a.contMDiff
  have hmul : σ.hamiltonianVectorField (⇑a * ⇑g) =
      ⇑a • σ.hamiltonianVectorField g + ⇑g • σ.hamiltonianVectorField a :=
    funext fun x ↦ hamiltonianVectorField_mul a.mdifferentiableAt g.mdifferentiableAt
  rw [hmul]
  refine PreservesDistribution.add ((a.contMDiff.smul_section hXg).mdifferentiable (by simp))
    ((g.contMDiff.smul_section hXa).mdifferentiable (by simp))
    (hf.smul a.mdifferentiable ha (hXg.mdifferentiable (by simp)))
    (hP.preservesDistribution ((g.contMDiff.smul_section hXa).mdifferentiable (by simp))
      fun x ↦ (P x).smul_mem _ ?_)
  exact hσ.isNondegenerate.hamiltonianVectorField_mem_of_isCoisotropic (hco x) (ha x)

end SmoothTwoForm

/-! ### Constant polarizations of a symplectic vector space -/

namespace SymplecticForm

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]

/-- **Constant real polarizations.** A Lagrangian subspace `L` of a symplectic vector space,
taken at every point, is a real polarization of the constant symplectic form. For the standard
form on `V × V` and `L = 0 × V` (`TauCeti.SymplecticForm.isLagrangian_prod_bot_top`) this is the
vertical polarization by the momentum directions. -/
theorem isRealPolarization_const (omegaForm : SymplecticForm V) {L : Submodule ℝ V}
    (hL : omegaForm.IsLagrangian L) :
    omegaForm.isNondegenerate_constSmooth.IsRealPolarization (fun _ ↦ L) where
  isContMDiffDistribution := by
    have hrank : finrank ℝ L = finrank ℝ V / 2 := by
      have := hL.two_mul_finrank
      omega
    exact hrank ▸ isContMDiffDistribution_const L
  isLagrangian x := by
    rw [isNondegenerate_constSmooth_symplecticFormAt]
    exact hL
  isInvolutiveDistribution := isInvolutiveDistribution_const L.isClosed_of_finiteDimensional

end SymplecticForm

end TauCeti
