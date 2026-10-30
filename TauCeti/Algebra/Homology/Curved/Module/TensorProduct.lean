/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.Curved.Module.Defs
public import TauCeti.Algebra.Homology.Curved.Module.Right.Defs
public import TauCeti.Algebra.Homology.DG.Module.TensorProduct.Complex

/-!
# Balanced tensor complexes of curved DG modules

Let `(A, d, w)` be a curved differential graded algebra, with its curvature stored in the
right-module convention `d (d a) = a * w - w * a`. Let `M` be a curved right module, so
`dM (dM m) = m * w`, and let `N` be a curved left module, so `dN (dN n) = -(w • n)`. Neither has
cohomology in general. Their ordinary balanced tensor product `M ⊗_A N` carries the signed
differential

`d (m ⊗ n) = dM m ⊗ n + (-1) ^ |m| • m ⊗ dN n`,

which is balanced because `dM` and `dN` obey the graded Leibniz rules for the same algebra
differential. The mixed terms of its square cancel, so

`d (d (m ⊗ n)) = m * w ⊗ n - m ⊗ w • n = 0`:

the two curvature actions cancel across the balanced tensor product. Hence `M ⊗_A N` is an
ordinary cochain complex of ground-ring modules. The cancellation uses both the handedness and the
sign of the left-module curvature equation: for a left module satisfying the right-module square
`dN (dN n) = w • n`, the square of the tensor differential would be `2 • (m ⊗ w • n)`.

The differential is the Leibniz-rule tensor differential
`TauCeti.BalancedTensorProduct.leibnizDifferential` that also underlies the tensor complex of DG
modules. At curvature zero, for DG modules regarded as curved modules, it is the DG tensor
differential (`TauCeti.BalancedTensorProduct.curvedDifferential_eq_differential`). The
construction is underived and needs no flatness hypothesis.

## Main definitions

* `TauCeti.BalancedTensorProduct.curvedDifferential`: the tensor differential of a curved right
  and a curved left module over one curved DG algebra.
* `TauCeti.BalancedTensorProduct.curvedCochainComplex`: their balanced tensor product, as a
  cochain complex of ground-ring modules.

## Main results

* `TauCeti.BalancedTensorProduct.curvedDifferential_comp_self`: the curvatures cancel, so the
  tensor differential squares to zero.
* `TauCeti.BalancedTensorProduct.curvedDifferential_eq_differential`: at curvature zero
  it is the tensor differential of DG modules.

## References

* L. Positselski, *Two kinds of derived categories, Koszul duality, and
  comodule-contramodule correspondence*, Mem. Amer. Math. Soc. **212** (2011), no. 996, for
  the tensor product of a right and a left CDG-module, which is a complex. His curvature is the
  negative of the right-module curvature used here.
-/

public section

open CategoryTheory

namespace TauCeti.BalancedTensorProduct

variable {R A M N : Type*} [CommRing R] [Ring A] [Algebra R A]
  [AddCommGroup M] [Module R M] [Module Aᵐᵒᵖ M] [IsScalarTower R Aᵐᵒᵖ M]
  [AddCommGroup N] [Module R N] [Module A N] [IsScalarTower R A N]
  {𝒜 : ℤ → Submodule R A} [GradedAlgebra 𝒜] {dA : A →ₗ[R] A} {w : A}
  {h : IsCurvedDGAlgebra 𝒜 dA w} {ℳ : ℤ → Submodule R M} {𝒩 : ℤ → Submodule R N}
  [DirectSum.Decomposition ℳ] [DirectSum.Decomposition 𝒩]
  [SetLike.GradedSMul (InternalGrading.ofDecomposition 𝒜).opposite.piece ℳ]
  [SetLike.GradedSMul 𝒜 𝒩]
  {dM : M →ₗ[R] M} {dN : N →ₗ[R] N}

/-- The signed tensor differential `d (m ⊗ n) = dM m ⊗ n + (-1) ^ |m| • m ⊗ dN n` on the ordinary
balanced tensor product of a curved right module and a curved left module over the same curved
differential graded algebra. -/
noncomputable def curvedDifferential (hM : IsCurvedDGRightModule h ℳ dM)
    (hN : IsCurvedDGLeftModule h 𝒩 dN) : Module.End R (BalancedTensorProduct R A M N) :=
  leibnizDifferential hM.leibniz hN.leibniz

/-- The curved tensor differential is the tensor differential of the two Leibniz rules. -/
theorem curvedDifferential_eq_leibnizDifferential (hM : IsCurvedDGRightModule h ℳ dM)
    (hN : IsCurvedDGLeftModule h 𝒩 dN) :
    curvedDifferential hM hN = leibnizDifferential hM.leibniz hN.leibniz :=
  (rfl)

/-- On arbitrary pure tensors, the sign is represented by the grading's Koszul twist. -/
@[simp]
theorem curvedDifferential_tmul (hM : IsCurvedDGRightModule h ℳ dM)
    (hN : IsCurvedDGLeftModule h 𝒩 dN) (m : M) (n : N) :
    curvedDifferential hM hN (tmul R A m n) = tmul R A (dM m) n +
      tmul R A ((InternalGrading.ofDecomposition ℳ).koszulTwist 1 m) (dN n) :=
  leibnizDifferential_tmul hM.leibniz hN.leibniz m n

/-- The curved tensor differential has the usual sign on a homogeneous left factor. -/
theorem curvedDifferential_tmul_of_mem (hM : IsCurvedDGRightModule h ℳ dM)
    (hN : IsCurvedDGLeftModule h 𝒩 dN) {q : ℤ} {m : M} (hm : m ∈ ℳ q) (n : N) :
    curvedDifferential hM hN (tmul R A m n) =
      tmul R A (dM m) n + (((q.negOnePow : ℤ) : R)) • tmul R A m (dN n) :=
  leibnizDifferential_tmul_of_mem hM.leibniz hN.leibniz hm n

/-- **The curvatures cancel.** The tensor differential of a curved right and a curved left module
over the same curved DG algebra squares to zero: its square sends `m ⊗ n` to
`m * w ⊗ n - m ⊗ w • n`, which vanishes in the balanced tensor product. -/
@[simp]
theorem curvedDifferential_comp_self (hM : IsCurvedDGRightModule h ℳ dM)
    (hN : IsCurvedDGLeftModule h 𝒩 dN) :
    curvedDifferential hM hN ∘ₗ curvedDifferential hM hN = 0 := by
  apply hom_ext
  intro m n
  rw [LinearMap.comp_apply, curvedDifferential,
    leibnizDifferential_leibnizDifferential_tmul _ _ hM.isHomogeneous, hM.sq_eq, hN.sq_eq,
    balance, ← mk_apply, ← mk_apply, map_neg, add_neg_cancel, LinearMap.zero_apply]

/-- Applying the curved tensor differential twice gives zero. -/
@[simp]
theorem curvedDifferential_sq_zero (hM : IsCurvedDGRightModule h ℳ dM)
    (hN : IsCurvedDGLeftModule h 𝒩 dN) (z : BalancedTensorProduct R A M N) :
    curvedDifferential hM hN (curvedDifferential hM hN z) = 0 :=
  LinearMap.congr_fun (curvedDifferential_comp_self hM hN) z

/-- **Zero curvature.** For DG modules over a DG algebra, regarded as curved modules of curvature
zero, the curved tensor differential is the tensor differential of DG modules. -/
theorem curvedDifferential_eq_differential {hDG : IsDGAlgebra 𝒜 dA}
    (hM : IsDGRightModule hDG ℳ dM) (hN : IsDGLeftModule hDG 𝒩 dN) :
    curvedDifferential hM.isCurvedDGRightModule_zero hN.isCurvedDGLeftModule_zero =
      differential hM hN := by
  rw [curvedDifferential_eq_leibnizDifferential, differential_eq_leibnizDifferential]

/-! ### The balanced tensor complex -/

attribute [local instance] tensorGradedRight tensorGradedLeft

/-- The curved tensor differential has cohomological degree one. -/
theorem isHomogeneous_curvedDifferential (hM : IsCurvedDGRightModule h ℳ dM)
    (hN : IsCurvedDGLeftModule h 𝒩 dN) :
    LinearMap.IsHomogeneous (curvedDifferential hM hN)
      (grading (𝒜 := 𝒜) (InternalGrading.ofDecomposition ℳ)
        (InternalGrading.ofDecomposition 𝒩)).piece
      (grading (𝒜 := 𝒜) (InternalGrading.ofDecomposition ℳ)
        (InternalGrading.ofDecomposition 𝒩)).piece
      1 :=
  isHomogeneous_leibnizDifferential hM.leibniz hN.leibniz hM.isHomogeneous hN.isHomogeneous

/-- The ordinary balanced tensor product of a curved right module and a curved left module over
the same curved DG algebra, as a cochain complex of ground-ring modules. It is a complex because
the two curvatures cancel (`curvedDifferential_comp_self`). -/
noncomputable def curvedCochainComplex (hM : IsCurvedDGRightModule h ℳ dM)
    (hN : IsCurvedDGLeftModule h 𝒩 dN) : CochainComplex (ModuleCat R) ℤ :=
  gradedCochainComplex
    (grading (𝒜 := 𝒜) (InternalGrading.ofDecomposition ℳ)
      (InternalGrading.ofDecomposition 𝒩)).piece
    (curvedDifferential hM hN) (isHomogeneous_curvedDifferential hM hN)
    (fun _ x ↦ curvedDifferential_sq_zero hM hN x)

/-- The degree-`p` term is the degree-`p` part of the balanced tensor product. -/
@[simp]
theorem curvedCochainComplex_X (hM : IsCurvedDGRightModule h ℳ dM)
    (hN : IsCurvedDGLeftModule h 𝒩 dN) (p : ℤ) :
    (curvedCochainComplex hM hN).X p = ModuleCat.of R
      ((grading (𝒜 := 𝒜) (InternalGrading.ofDecomposition ℳ)
        (InternalGrading.ofDecomposition 𝒩)).piece p) := by
  rw [curvedCochainComplex, gradedCochainComplex_X]

/-- The degree-`p` differential is the restriction of the curved tensor differential,
transported along the canonical identifications of the complex terms. -/
@[simp]
theorem curvedCochainComplex_d (hM : IsCurvedDGRightModule h ℳ dM)
    (hN : IsCurvedDGLeftModule h 𝒩 dN) (p : ℤ) :
    (curvedCochainComplex hM hN).d p (p + 1) =
      eqToHom (curvedCochainComplex_X hM hN p) ≫
        ModuleCat.ofHom ((curvedDifferential hM hN).restrict
          (fun _ hz ↦ (isHomogeneous_curvedDifferential hM hN).map_mem hz)) ≫
        eqToHom (curvedCochainComplex_X hM hN (p + 1)).symm := by
  unfold curvedCochainComplex
  rw [gradedCochainComplex_d]

/-- On a homogeneous element, the complex differential is the curved tensor differential,
using the canonical identifications of the complex terms with the grading pieces. -/
theorem curvedCochainComplex_d_apply (hM : IsCurvedDGRightModule h ℳ dM)
    (hN : IsCurvedDGLeftModule h 𝒩 dN) (p : ℤ)
    (z : (grading (𝒜 := 𝒜) (InternalGrading.ofDecomposition ℳ)
      (InternalGrading.ofDecomposition 𝒩)).piece p) :
    ((eqToHom (curvedCochainComplex_X hM hN (p + 1)))
      ((curvedCochainComplex hM hN).d p (p + 1)
        ((eqToHom (curvedCochainComplex_X hM hN p).symm) z)) :
      BalancedTensorProduct R A M N) = curvedDifferential hM hN z := by
  unfold curvedCochainComplex
  rw [gradedCochainComplex_d_apply]

end TauCeti.BalancedTensorProduct
