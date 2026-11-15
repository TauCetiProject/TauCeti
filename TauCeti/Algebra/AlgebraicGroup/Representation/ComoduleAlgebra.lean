/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.Representation.Differential
public import TauCeti.Algebra.AlgebraicGroup.Representation.PointsAction.Basic
public import TauCeti.Algebra.Bialgebra.ComoduleAlgebra.SymmetricAlgebra
public import TauCeti.Algebra.Coalgebra.Comodule.Dual
public import TauCeti.LinearAlgebra.SymmetricAlgebra.Derivation.OfEnd

/-!
# Differentiating and evaluating comodule algebras

Let `A` be a comodule algebra over a commutative bialgebra `H`: geometrically, an action of the
affine monoid `Spec H` on `Spec A`. A tangent vector `d` at the identity of `Spec H` acts on `A`
through the differentiated representation `TauCeti.Comodule.differential`. Because the coaction is
multiplicative and `d` is a derivation at the counit, this action is a derivation of `A`: the
infinitesimal action of a Lie algebra element on functions is by vector fields.

For the symmetric algebra of a comodule `M`, with its multiplicative coaction, the differentiated
action is therefore the derivation of `Sym M` extending the differentiated action on the
generators `M`. Applied to the dual of a representation `V`, this computes the infinitesimal
action on the polynomial functions on `V`. Moreover, when `H` is a commutative Hopf algebra and
`M` is a finite projective right `H`-comodule, every coinvariant polynomial in `Sym(M*)^H` is
constant along rational orbits of `Spec H` acting on `M`.

## Main declarations

* `TauCeti.ComoduleAlgebra.differential_mul`: the Leibniz rule for the differentiated action.
* `TauCeti.ComoduleAlgebra.differential_symmetricAlgebra_ι`: on a symmetric algebra, it commutes
  with the inclusion of generators.
* `TauCeti.ComoduleAlgebra.differential_symmetricAlgebra`: on a symmetric algebra, it is the
  derivation `SymmetricAlgebra.derivationOfEnd` induced by the action on generators.
* `TauCeti.ComoduleAlgebra.lift_eval_basePointsRepresentation_of_mem_coinvariants`: coinvariant
  polynomial functions in `Sym(M*)^H` are constant on rational orbits of `Spec H` on `M`.

## References

* J. C. Jantzen, *Representations of Algebraic Groups*, I.7.
* J. S. Milne, *Algebraic Groups* (2017), §10.d.
-/

public section

open scoped TensorProduct

namespace TauCeti.ComoduleAlgebra

section Differential

variable {R H : Type*} [CommRing R] [CommRing H] [Bialgebra R H]

section Ring

variable {A : Type*} [Ring A] [Algebra R A]

variable [ComoduleAlgebra R H A]

/-- **The Leibniz rule for a comodule algebra.** A tangent vector at the identity acts on a
comodule algebra by a derivation: `d • (a * b) = (d • a) * b + a * (d • b)`. -/
theorem differential_mul (d : Derivation R H (Bialgebra.CounitAlgebra R H R)) (a b : A) :
    Comodule.differential (R := R) (H := H) d (a * b) =
      Comodule.differential (R := R) (H := H) d a * b +
        a * Comodule.differential (R := R) (H := H) d b := by
  rw [Comodule.differential_apply, Comodule.differential_apply, Comodule.differential_apply,
    coact_mul, LinearMap.tensorComponent_mul <|
      Bialgebra.CounitAlgebra.algEquivSelf_comp_apply_mul d]
  simp only [← Comodule.coactComponent_apply, Comodule.coactComponent_counit, LinearMap.id_apply]

end Ring

section SymmetricAlgebra

variable {M : Type*} [AddCommGroup M] [Module R M] [Comodule R H M]

attribute [local instance] symmetricAlgebra

/-- The differentiated action on a symmetric algebra commutes with the inclusion of generators,
since the coaction of a generator is the coaction on `M`. -/
theorem differential_symmetricAlgebra_ι (d : Derivation R H (Bialgebra.CounitAlgebra R H R))
    (m : M) :
    Comodule.differential (R := R) (H := H) d (SymmetricAlgebra.ι R M m) =
      SymmetricAlgebra.ι R M (Comodule.differential (R := R) (H := H) d m) := by
  simp [Comodule.differential_apply, symmetricAlgebra_coact, LinearMap.rTensor_def,
    LinearMap.tensorComponent_map]

/-- **The differentiated action on a symmetric algebra.** A tangent vector at the identity acts on
the symmetric algebra of a comodule `M` by the derivation extending its action on `M`. -/
theorem differential_symmetricAlgebra (d : Derivation R H (Bialgebra.CounitAlgebra R H R)) :
    Comodule.differential (R := R) (H := H) (M := SymmetricAlgebra R M) d =
      (SymmetricAlgebra.derivationOfEnd R M
        (Comodule.differential (R := R) (H := H) (M := M) d)).toLinearMap := by
  let D : Derivation R (SymmetricAlgebra R M) (SymmetricAlgebra R M) :=
    Derivation.mk' (Comodule.differential (R := R) (H := H) d) fun a b ↦ by
      rw [differential_mul, smul_eq_mul, smul_eq_mul]
      ring
  have h : D = SymmetricAlgebra.derivationOfEnd R M (Comodule.differential (R := R) (H := H) d) :=
    SymmetricAlgebra.derivation_ext fun m ↦ by
      rw [Derivation.coe_mk', differential_symmetricAlgebra_ι,
        SymmetricAlgebra.derivationOfEnd_ι]
  exact LinearMap.ext fun p ↦ by
    rw [← h, Derivation.coe_mk'_linearMap]

end SymmetricAlgebra

end Differential

section CoinvariantEvaluation

universe u v w

variable {R : Type u} {H : Type v} {M : Type w} [CommSemiring R] [CommSemiring H]
  [HopfAlgebra R H] [AddCommMonoid M] [Module R M] [Comodule R H M]
  [Module.Finite R M] [Module.Projective R M]

attribute [local instance] Comodule.dual symmetricAlgebra

/-- **Coinvariant polynomial functions are constant on rational orbits.** For any finite projective
right `H`-comodule `M`, every base-valued point `g` of `Spec H` preserves the evaluation of every
coinvariant polynomial `p ∈ Sym(M*)^H` on `M`. -/
theorem lift_eval_basePointsRepresentation_of_mem_coinvariants
    {p : SymmetricAlgebra R (Module.Dual R M)}
    (hp : p ∈ coinvariants R H (SymmetricAlgebra R (Module.Dual R M)))
    (g : WithConv (H →ₐ[R] R)) (x : M) :
    SymmetricAlgebra.lift (Module.Dual.eval R M (Comodule.basePointsRepresentation M g x)) p =
      SymmetricAlgebra.lift (Module.Dual.eval R M x) p := by
  let A := SymmetricAlgebra R (Module.Dual R M)
  let ψ : A →ₐ[R] A :=
    (Algebra.TensorProduct.rid R R A).toAlgHom.comp
      ((Algebra.TensorProduct.map (AlgHom.id R A) g⁻¹.ofConv).comp
        (coactAlgHom R H A))
  have hcomp :
      SymmetricAlgebra.lift (Module.Dual.eval R M (Comodule.basePointsRepresentation M g x)) =
        (SymmetricAlgebra.lift (Module.Dual.eval R M x)).comp ψ := by
    ext φ
    have key (t : Module.Dual R M ⊗[R] H) :
        SymmetricAlgebra.lift (Module.Dual.eval R M x)
            (Algebra.TensorProduct.rid R R A
              (Algebra.TensorProduct.map (AlgHom.id R A) g⁻¹.ofConv
                ((SymmetricAlgebra.ι R (Module.Dual R M)).rTensor H t))) =
          g⁻¹.ofConv (dualTensorHom R M H t x) := by
      induction t using _root_.TensorProduct.inductionOn with
      | tmul ξ h => simp [dualTensorHom_apply, mul_comm]
      | add s t hs ht => simp only [map_add, LinearMap.add_apply, hs, ht]
    simp [ψ, A, symmetricAlgebra_coact, Comodule.symmetricAlgebraCoact_ι, Comodule.dual_coact,
      key, ← WithConv.algHom_inv_apply]
  have hψp : ψ p = p := by
    simp [ψ, A, mem_coinvariants.mp hp]
  rw [hcomp, AlgHom.comp_apply, hψp]

end CoinvariantEvaluation

end TauCeti.ComoduleAlgebra
