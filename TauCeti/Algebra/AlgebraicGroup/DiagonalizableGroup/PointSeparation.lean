/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Algebra.AlgebraicGroup.DiagonalizableGroup.Weight
public import TauCeti.Algebra.Coalgebra.Comodule.PointSeparation

/-!
# Weights of a coefficient-generating representation separate points

For a homomorphism `D(X) → G`, two points of `D(X)` act identically on a representation of
`G` when they agree on its occurring weights. If the representation's matrix coefficients
generate the coordinate algebra of `G` and `D(X) → G` is a closed immersion, these weights
separate all algebra-valued points of `D(X)`. In particular, automorphisms of the character
group are determined by their values on the weights of such a representation. This gives a
finite set on which to detect the normalizer action when the representation is finite.

The point-separation statements work over commutative semirings and allow nonreduced value
algebras. No finite-generation hypothesis on the representation is needed here.

## References

* J. S. Milne, *Algebraic Groups* (2017), §§4.a and 21.1.
* J. C. Jantzen, *Representations of Algebraic Groups*, I.2.
-/

public section

open scoped TensorProduct

open TauCeti TauCeti.DiagonalizableGroup

namespace BialgHom

noncomputable section

variable {R H X V A : Type*} [CommSemiring R] [Semiring H] [Bialgebra R H]
  [CommMonoid X] [AddCommMonoid V] [Module R V] [Comodule R H V]
  [CommSemiring A] [Algebra R A]

/-- Points agreeing on all weights with nonzero weight spaces induce the same action on the
representation. -/
theorem endOfPoint_comp_eq_of_eqOn_weights
    (π : H →ₐc[R] MonoidAlgebra R X) (f g : MonoidAlgebra R X →ₐ[R] A)
    (hfg : ∀ x, weightSpace V π.toCoalgHom x ≠ ⊥ →
      f (MonoidAlgebra.single x 1) = g (MonoidAlgebra.single x 1)) :
    Comodule.endOfPoint V (f.comp π.toAlgHom) =
      Comodule.endOfPoint V (g.comp π.toAlgHom) := by
  classical
  apply LinearMap.ext
  intro z
  induction z using TensorProduct.inductionOn with
  | add z t hz ht => simp [hz, ht]
  | tmul a v =>
      have hv : v ∈ ⨆ x, weightSpace V π.toCoalgHom x := by
        rw [(isInternal_weightSpace V π.toCoalgHom).submodule_iSup_eq_top]
        trivial
      refine Submodule.iSup_induction (weightSpace V π.toCoalgHom)
        (motive := fun v ↦ Comodule.endOfPoint V (f.comp π.toAlgHom) (a ⊗ₜ[R] v) =
          Comodule.endOfPoint V (g.comp π.toAlgHom) (a ⊗ₜ[R] v)) hv
        (fun x v hv ↦ ?_) (by simp) (fun v w hv hw ↦ ?_)
      · by_cases hx : weightSpace V π.toCoalgHom x = ⊥
        · have hv0 : v = 0 := by simpa [hx] using hv
          simp [hv0]
        · rw [endOfPoint_tmul_of_mem_weightSpace V π f a hv,
            endOfPoint_tmul_of_mem_weightSpace V π g a hv, hfg x hx]
      · simp [TensorProduct.tmul_add, hv, hw]

/-- For a closed diagonalizable subgroup, the weights of a coefficient-generating ambient
representation separate its points over every commutative value algebra. -/
theorem eq_of_eqOn_weights_of_matrixCoefficientSubalgebra_eq_top
    (π : H →ₐc[R] MonoidAlgebra R X) (hπ : Function.Surjective π)
    (hV : Comodule.matrixCoefficientSubalgebra (R := R) (C := H) (M := V) = ⊤)
    (f g : MonoidAlgebra R X →ₐ[R] A)
    (hfg : ∀ x, weightSpace V π.toCoalgHom x ≠ ⊥ →
      f (MonoidAlgebra.single x 1) = g (MonoidAlgebra.single x 1)) : f = g := by
  have he := Comodule.eq_of_endOfPoint_eq_of_matrixCoefficientSubalgebra_eq_top
    (f.comp π.toAlgHom) (g.comp π.toAlgHom)
    (endOfPoint_comp_eq_of_eqOn_weights π f g hfg) hV
  apply AlgHom.ext
  intro y
  obtain ⟨x, rfl⟩ := hπ y
  exact AlgHom.congr_fun he x

/-- Automorphisms of the character group are determined on the occurring weights of a
coefficient-generating representation of the ambient group. -/
theorem mulEquiv_eq_of_eqOn_weights [Nontrivial R]
    (π : H →ₐc[R] MonoidAlgebra R X) (hπ : Function.Surjective π)
    (hV : Comodule.matrixCoefficientSubalgebra (R := R) (C := H) (M := V) = ⊤)
    (w w' : X ≃* X)
    (hww' : Set.EqOn w w' {x | weightSpace V π.toCoalgHom x ≠ ⊥}) : w = w' := by
  have he := eq_of_eqOn_weights_of_matrixCoefficientSubalgebra_eq_top π hπ hV
    (MonoidAlgebra.domCongr R R w).toAlgHom
    (MonoidAlgebra.domCongr R R w').toAlgHom
    (fun x hx ↦ by simp [hww' hx])
  ext x
  apply MonoidAlgebra.single_left_injective (R := R) (M := X) one_ne_zero
  simpa using AlgHom.congr_fun he (MonoidAlgebra.single x 1)

end

end BialgHom
