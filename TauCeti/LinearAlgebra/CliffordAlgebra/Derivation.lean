/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.CliffordAlgebra.Contraction
public import TauCeti.LinearAlgebra.ExteriorAlgebra.Derivation.OfEnd
import TauCeti.LinearAlgebra.CliffordAlgebra.Basic

/-!
# Derivations of a Clifford algebra and the equivariance of the quantization map

Consider a derivation `D` of a Clifford algebra that maps the generators into the generators,
`D (ι Q m) = ι Q (A m)` for an endomorphism `A` of `M`. When the scalars act faithfully on the
Clifford algebra, for instance when `2` is invertible, such an `A` is necessarily skew-adjoint for
the polar form of `Q`. Conversely, for a nondegenerate quadratic form on a finite-dimensional
vector space over a field in which `2` is invertible, every skew-adjoint endomorphism arises this
way, as the commutator with its quadratic lift (`CliffordAlgebra.soEquivQuadratic_lie_ι`).

This file proves that Mathlib's change of form `CliffordAlgebra.changeForm` intertwines these
derivations. If `Q' - Q` is the quadratic form of a bilinear form `B` for which `A` is
skew-adjoint, and `D`, `D'` are derivations of `CliffordAlgebra Q` and `CliffordAlgebra Q'`
extending `A`, then `changeForm (D x) = D' (changeForm x)`. The key step is the commutation of a
derivation with a contraction, `D (d ⌋ x) = d ⌋ D x - (d ∘ A) ⌋ x`.

The case of interest is Chevalley's identification `CliffordAlgebra.equivExterior Q` of the
Clifford algebra with the exterior algebra, defined when `2` is invertible in `R`, whose inverse is
the *quantization map* `⋀ M → CliffordAlgebra Q`. On the exterior side the derivation extending
`A` is `ExteriorAlgebra.derivationOfEnd R M A`. When `2` is invertible, the quantization map
intertwines it with every derivation of the Clifford algebra extending `A`, in particular with the
commutator `⁅c, -⁆` by any element `c` with `⁅c, ι Q m⁆ = ι Q (A m)`. No nondegeneracy or
finiteness is needed. For the adjoint representation of a Lie algebra `𝔤` with an invariant form,
this is the `𝔤`-equivariance of the quantization map `⋀ 𝔤 → Cliff(𝔤)` used in Kostant's
description of the Clifford algebra of `𝔤`.

## Main results

* `CliffordAlgebra.isSkewAdjoint_polarBilin_of_derivation`: when `R` acts faithfully, a derivation
  extending `A` forces `A` to be skew-adjoint for the polar form.
* `CliffordAlgebra.derivation_contractLeft`: `D (d ⌋ x) = d ⌋ D x - (d ∘ A) ⌋ x`.
* `CliffordAlgebra.changeForm_derivation`: the change of form intertwines derivations extending a
  skew-adjoint endomorphism.
* `CliffordAlgebra.equivExterior_derivation`, `CliffordAlgebra.equivExterior_symm_derivationOfEnd`:
  the identification with the exterior algebra intertwines a derivation extending `A` with
  `ExteriorAlgebra.derivationOfEnd R M A`.
* `CliffordAlgebra.equivExterior_lie`, `CliffordAlgebra.lie_equivExterior_symm`: the same for the
  commutator with an element acting on the generators by `A`.

## References

* C. Chevalley, *The Algebraic Theory of Spinors*, Columbia University Press (1954), Chapter II.
* E. Meinrenken, *Clifford Algebras and Lie Theory*, Springer Ergebnisse 58 (2013), Chapter 2.
* B. Kostant, *Clifford algebra analogue of the Hopf--Koszul--Samelson theorem, the ρ-decomposition
  `C(𝔤) = End V_ρ ⊗ C(P)`, and the `𝔤`-module structure of `⋀𝔤`*, Adv. Math. 125 (1997), 275--350.
-/

public section

namespace CliffordAlgebra

open TauCeti

attribute [local instance 100] LieRing.ofAssociativeRing

variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M] {Q : QuadraticForm R M}

/-- **A derivation extending `A` forces `A` to be skew-adjoint.** If `R` acts faithfully on
`CliffordAlgebra Q` (for instance when `2` is invertible in `R`) and a derivation of
`CliffordAlgebra Q` maps each generator `ι Q m` to `ι Q (A m)`, then
`polar Q (A m) n = -polar Q m (A n)`. -/
theorem isSkewAdjoint_polarBilin_of_derivation [FaithfulSMul R (CliffordAlgebra Q)]
    (D : derivationLieAlgebra R (CliffordAlgebra Q)) {A : Module.End R M}
    (hD : ∀ m, (D : Module.End R (CliffordAlgebra Q)) (ι Q m) = ι Q (A m)) :
    (QuadraticMap.polarBilin Q).IsSkewAdjoint A := by
  intro m n
  -- Differentiate the scalar `ι Q m * ι Q n + ι Q n * ι Q m = polar Q m n`.
  have h := congrArg (D : Module.End R (CliffordAlgebra Q)) (ι_mul_ι_add_swap (Q := Q) m n)
  rw [map_add, derivationLieAlgebra.leibniz, derivationLieAlgebra.leibniz, hD, hD,
    derivationLieAlgebra.map_algebraMap] at h
  have h' : algebraMap R (CliffordAlgebra Q) (QuadraticMap.polar Q (A m) n +
      QuadraticMap.polar Q m (A n)) = 0 := by
    rw [map_add, ← ι_mul_ι_add_swap, ← ι_mul_ι_add_swap, ← h]
    abel
  simp only [QuadraticMap.polarBilin_apply_apply, Pi.neg_apply, QuadraticMap.polar_neg_right]
  exact eq_neg_of_add_eq_zero_left ((map_eq_zero_iff _
    ((faithfulSMul_iff_algebraMap_injective R (CliffordAlgebra Q)).1 inferInstance)).1 h')

/-- **A derivation and a contraction**: if a derivation `D` of `CliffordAlgebra Q` maps each
generator `ι Q m` to `ι Q (A m)`, then `D (d ⌋ x) = d ⌋ D x - (d ∘ A) ⌋ x`. -/
theorem derivation_contractLeft (D : derivationLieAlgebra R (CliffordAlgebra Q))
    {A : Module.End R M} (hD : ∀ m, (D : Module.End R (CliffordAlgebra Q)) (ι Q m) = ι Q (A m))
    (d : Module.Dual R M) (x : CliffordAlgebra Q) :
    (D : Module.End R (CliffordAlgebra Q)) (contractLeft d x) =
      contractLeft d ((D : Module.End R (CliffordAlgebra Q)) x) - contractLeft (d ∘ₗ A) x := by
  induction x using CliffordAlgebra.left_induction with
  | algebraMap r => simp
  | add x y hx hy =>
    simp only [map_add, hx, hy]
    abel
  | ι_mul x m hx =>
    simp only [contractLeft_ι_mul, map_sub, map_smul, derivationLieAlgebra.leibniz, hD, hx,
      map_add, LinearMap.comp_apply, mul_sub]
    abel

section changeForm

variable {Q' : QuadraticForm R M} {B : LinearMap.BilinForm R M}

/-- **The change of form intertwines derivations.** If `B.toQuadraticMap = Q' - Q`, the
endomorphism `A` is skew-adjoint for `B`, and `D`, `D'` are derivations of `CliffordAlgebra Q` and
`CliffordAlgebra Q'` mapping each generator `ι m` to `ι (A m)`, then
`changeForm h (D x) = D' (changeForm h x)`. -/
theorem changeForm_derivation (h : B.toQuadraticMap = Q' - Q) {A : Module.End R M}
    (hA : B.IsSkewAdjoint A) (D : derivationLieAlgebra R (CliffordAlgebra Q))
    (hD : ∀ m, (D : Module.End R (CliffordAlgebra Q)) (ι Q m) = ι Q (A m))
    (D' : derivationLieAlgebra R (CliffordAlgebra Q'))
    (hD' : ∀ m, (D' : Module.End R (CliffordAlgebra Q')) (ι Q' m) = ι Q' (A m))
    (x : CliffordAlgebra Q) :
    changeForm h ((D : Module.End R (CliffordAlgebra Q)) x) =
      (D' : Module.End R (CliffordAlgebra Q')) (changeForm h x) := by
  have hB (m : M) : B (A m) = -(B m ∘ₗ A) := LinearMap.ext fun n ↦ by simpa using hA m n
  induction x using CliffordAlgebra.left_induction with
  | algebraMap r => simp
  | add x y hx hy => simp only [map_add, hx, hy]
  | ι_mul x m hx =>
    simp only [derivationLieAlgebra.leibniz, hD, hD', map_add, map_sub, changeForm_ι_mul, hx,
      derivation_contractLeft D' hD', hB, map_neg, LinearMap.neg_apply]
    abel

end changeForm

section equivExterior

variable [Invertible (2 : R)]

/-- **The identification with the exterior algebra intertwines derivations**: for a derivation
`D` of `CliffordAlgebra Q` mapping each generator `ι Q m` to `ι Q (A m)`,
`equivExterior Q (D x) = ExteriorAlgebra.derivationOfEnd R M A (equivExterior Q x)`.

Not a `simp` lemma: `simp` unfolds `CliffordAlgebra.equivExterior` to the underlying
`CliffordAlgebra.changeFormEquiv`, so the left-hand side is not in simp-normal form. -/
theorem equivExterior_derivation (D : derivationLieAlgebra R (CliffordAlgebra Q))
    {A : Module.End R M} (hD : ∀ m, (D : Module.End R (CliffordAlgebra Q)) (ι Q m) = ι Q (A m))
    (x : CliffordAlgebra Q) :
    equivExterior Q ((D : Module.End R (CliffordAlgebra Q)) x) =
      (ExteriorAlgebra.derivationOfEnd R M A : Module.End R (ExteriorAlgebra R M))
        (equivExterior Q x) := by
  simp only [equivExterior, changeFormEquiv_apply]
  refine changeForm_derivation changeForm.associated_neg_proof (fun m n ↦ ?_) D hD _
    (ExteriorAlgebra.derivationOfEnd_ι A) x
  -- The polar form is twice the associated form, and `2` is invertible.
  have h := isSkewAdjoint_polarBilin_of_derivation D hD m n
  simp only [← QuadraticMap.two_nsmul_associated R Q, LinearMap.smul_apply,
    ← ofNat_smul_eq_nsmul (R := R)] at h
  simpa only [map_neg, LinearMap.neg_apply, neg_inj] using
    (isUnit_of_invertible (2 : R)).smul_left_cancel.mp h

/-- **The quantization map is equivariant**: the inverse of `equivExterior Q` carries
`ExteriorAlgebra.derivationOfEnd R M A` to any derivation `D` of `CliffordAlgebra Q` mapping each
generator `ι Q m` to `ι Q (A m)`. -/
theorem equivExterior_symm_derivationOfEnd (D : derivationLieAlgebra R (CliffordAlgebra Q))
    {A : Module.End R M} (hD : ∀ m, (D : Module.End R (CliffordAlgebra Q)) (ι Q m) = ι Q (A m))
    (y : ExteriorAlgebra R M) :
    (equivExterior Q).symm
        ((ExteriorAlgebra.derivationOfEnd R M A : Module.End R (ExteriorAlgebra R M)) y) =
      (D : Module.End R (CliffordAlgebra Q)) ((equivExterior Q).symm y) := by
  rw [LinearEquiv.symm_apply_eq, equivExterior_derivation D hD, LinearEquiv.apply_symm_apply]

/-- **The identification with the exterior algebra intertwines a commutator**: if
`⁅c, ι Q m⁆ = ι Q (A m)` for every `m`, then
`equivExterior Q ⁅c, x⁆ = ExteriorAlgebra.derivationOfEnd R M A (equivExterior Q x)`.

Not a `simp` lemma, for the same reason as `CliffordAlgebra.equivExterior_derivation`. -/
theorem equivExterior_lie {c : CliffordAlgebra Q} {A : Module.End R M}
    (hc : ∀ m, ⁅c, ι Q m⁆ = ι Q (A m)) (x : CliffordAlgebra Q) :
    equivExterior Q ⁅c, x⁆ =
      (ExteriorAlgebra.derivationOfEnd R M A : Module.End R (ExteriorAlgebra R M))
        (equivExterior Q x) := by
  have h := equivExterior_derivation (innerDerivation R c) (by simpa using hc) x
  rwa [coe_innerDerivation, LieAlgebra.ad_apply] at h

/-- **The quantization map intertwines a commutator**: if `⁅c, ι Q m⁆ = ι Q (A m)` for every `m`,
then `⁅c, (equivExterior Q).symm y⁆` is the quantization of
`ExteriorAlgebra.derivationOfEnd R M A y`. -/
theorem lie_equivExterior_symm {c : CliffordAlgebra Q} {A : Module.End R M}
    (hc : ∀ m, ⁅c, ι Q m⁆ = ι Q (A m)) (y : ExteriorAlgebra R M) :
    ⁅c, (equivExterior Q).symm y⁆ =
      (equivExterior Q).symm
        ((ExteriorAlgebra.derivationOfEnd R M A : Module.End R (ExteriorAlgebra R M)) y) := by
  have h := equivExterior_symm_derivationOfEnd (innerDerivation R c) (by simpa using hc) y
  rwa [coe_innerDerivation, LieAlgebra.ad_apply, eq_comm] at h

end equivExterior

end CliffordAlgebra
