/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.MonoidAlgebra.MapDomain
public import Mathlib.RingTheory.TensorProduct.Basic
public import Mathlib.RingTheory.TensorProduct.Free
public import TauCeti.Algebra.BrauerAlgebra.Basic

/-!
# Changing the coefficients of the Brauer algebra

The structure constants of the Brauer algebra `B_k(δ)` in its diagram basis are the powers of the
loop value `δ`: `D₁ * D₂ = δ ^ c • (D₁ ∘ D₂)`. They are therefore carried along by any ring
homomorphism `f : R →+* S`, which sends them to the structure constants of `B_k(f δ)` over `S`.
Applying `f` to every coefficient in the diagram basis is the **coefficient-change map**
`TauCeti.BrauerAlgebra.mapRingHom f : B_k(δ) →+* B_k(f δ)`. It fixes every diagram, is functorial
in `f` (`TauCeti.BrauerAlgebra.mapRingHom_id` and `TauCeti.BrauerAlgebra.mapRingHom_comp`), and
restricts on the symmetric group to the coefficient change of the group algebra
(`TauCeti.BrauerAlgebra.mapRingHom_ofPerm`). For instance, reduction modulo a prime `p` maps the
integral Brauer algebra `B_k(δ)` over `ℤ` onto the Brauer algebra over `ZMod p` at the reduced loop
value, compatibly with all the products of diagrams (`TauCeti.BrauerAlgebra.mapRingHom_surjective`).

For an `R`-algebra `S` the coefficient change along `algebraMap R S` identifies the Brauer algebra
over `S` with the scalar extension of the Brauer algebra over `R`: the **scalar-extension
isomorphism** `TauCeti.BrauerAlgebra.scalarTensorEquiv R S δ k : S ⊗[R] B_k(δ) ≃ₐ[S]
B_k(algebraMap R S δ)` sends `s ⊗ x` to `s` times the coefficient change of `x`. Both sides are
free on the Brauer diagrams, the tensor product with the basis `1 ⊗ D`, and the isomorphism matches
the two bases. This is the form in which statements about the Brauer algebra and its actions over
a base ring, such as `ℤ` or a field, are transported to an extension of it.

## Main definitions

* `TauCeti.BrauerAlgebra.mapRingHom`: the coefficient change `B_k(δ) →+* B_k(f δ)` along a ring
  homomorphism `f`.
* `TauCeti.BrauerAlgebra.scalarTensorEquiv`: the scalar-extension isomorphism
  `S ⊗[R] B_k(δ) ≃ₐ[S] B_k(algebraMap R S δ)`.

## Main results

* `TauCeti.BrauerAlgebra.mapRingHom_of`: the coefficient change fixes every diagram.
* `TauCeti.BrauerAlgebra.mapRingHom_id` and `TauCeti.BrauerAlgebra.mapRingHom_comp`: the identity
  and composition laws.
* `TauCeti.BrauerAlgebra.mapRingHom_injective` and `TauCeti.BrauerAlgebra.mapRingHom_surjective`:
  the coefficient change along an injective, or surjective, ring homomorphism is injective, or
  surjective.
* `TauCeti.BrauerAlgebra.mapRingHom_ofPerm`: on the group algebra of `Sₖ` the coefficient change is
  Mathlib's `MonoidAlgebra.mapRingHom`.
* `TauCeti.BrauerAlgebra.scalarTensorEquiv_tmul` and
  `TauCeti.BrauerAlgebra.scalarTensorEquiv_symm_of`: the scalar-extension isomorphism on pure
  tensors and on the diagram basis.

## References

* S. Doty and J. Hu, *Schur-Weyl duality for orthogonal groups*, Proc. London Math. Soc. (3) 98
  (2009), 679-713, §1, for the integral Brauer algebra and its base change.
-/

public section

open scoped TensorProduct

namespace TauCeti

namespace BrauerAlgebra

variable {R S T : Type*} [CommSemiring R] [CommSemiring S] [CommSemiring T] {δ : R} {k : ℕ}

/-! ### The coefficient-change map -/

/-- Applying a ring homomorphism to the coefficients carries the loop-weighted stacking at the loop
value `δ` to the loop-weighted stacking at `f δ`. -/
private theorem mapRange_mulCoeff (f : R →+* S) (x y : BrauerDiagram k →₀ R) :
    Finsupp.mapRange.addMonoidHom f.toAddMonoidHom (mulCoeff δ x y) =
      mulCoeff (f δ) (Finsupp.mapRange.addMonoidHom f.toAddMonoidHom x)
        (Finsupp.mapRange.addMonoidHom f.toAddMonoidHom y) := by
  induction x using Finsupp.induction_linear with
  | zero => simp
  | add x₁ x₂ h₁ h₂ => simp only [map_add, LinearMap.add_apply, h₁, h₂]
  | single D₁ a =>
  induction y using Finsupp.induction_linear with
  | zero => simp
  | add y₁ y₂ h₁ h₂ => simp only [map_add, h₁, h₂]
  | single D₂ b => simp [mulCoeff_single_single]

/-- **The coefficient change of the Brauer algebra** along a ring homomorphism `f : R →+* S`: the
ring homomorphism `B_k(δ) →+* B_k(f δ)` applying `f` to every coefficient in the diagram basis. It
fixes every diagram (`TauCeti.BrauerAlgebra.mapRingHom_of`). -/
noncomputable def mapRingHom (f : R →+* S) : BrauerAlgebra R δ k →+* BrauerAlgebra S (f δ) k where
  toFun x := ofCoeff (Finsupp.mapRange.addMonoidHom f.toAddMonoidHom x.coeff)
  map_one' := ext <| by simp [coeff_one]
  map_mul' x y := ext <| mapRange_mulCoeff f x.coeff y.coeff
  map_zero' := ext <| by simp
  map_add' x y := ext <| by simp only [coeff_add, map_add]

/-- The coefficients of the coefficient change are the images of the coefficients. -/
@[simp]
theorem coeff_mapRingHom (f : R →+* S) (x : BrauerAlgebra R δ k) :
    (mapRingHom f x).coeff = Finsupp.mapRange f (map_zero f) x.coeff := (rfl)

/-- **The coefficient change fixes every diagram.** -/
@[simp]
theorem mapRingHom_of (f : R →+* S) (D : BrauerDiagram k) :
    mapRingHom f (of D : BrauerAlgebra R δ k) = of D :=
  ext <| by simp

/-- The coefficient change is semilinear along `f`. -/
@[simp]
theorem mapRingHom_smul (f : R →+* S) (r : R) (x : BrauerAlgebra R δ k) :
    mapRingHom f (r • x) = f r • mapRingHom f x :=
  ext <| by ext D; simp

/-- The coefficient change sends the scalars of `R` to the scalars of `S` along `f`. -/
@[simp]
theorem mapRingHom_algebraMap (f : R →+* S) (r : R) :
    mapRingHom f (algebraMap R (BrauerAlgebra R δ k) r) = algebraMap S _ (f r) := by
  rw [Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one, mapRingHom_smul, map_one]

/-- **The identity law**: changing the coefficients along the identity is the identity. -/
@[simp]
theorem mapRingHom_id :
    (mapRingHom (RingHom.id R) : BrauerAlgebra R δ k →+* BrauerAlgebra R δ k) = RingHom.id _ :=
  RingHom.ext fun _ => ext <| Finsupp.ext fun _ => (rfl)

/-- **The composition law**: changing the coefficients along `f` and then along `g` is changing them
along `g.comp f`. -/
theorem mapRingHom_comp (g : S →+* T) (f : R →+* S) :
    (mapRingHom (g.comp f) : BrauerAlgebra R δ k →+* BrauerAlgebra T (g (f δ)) k) =
      (mapRingHom g).comp (mapRingHom f) :=
  RingHom.ext fun x => ext <| by ext D; simp

/-- Changing the coefficients along `f` and then along `g` is changing them along `g.comp f`. -/
@[simp]
theorem mapRingHom_mapRingHom (g : S →+* T) (f : R →+* S) (x : BrauerAlgebra R δ k) :
    mapRingHom g (mapRingHom f x) = mapRingHom (g.comp f) x :=
  (RingHom.congr_fun (mapRingHom_comp g f) x).symm

/-- The coefficient change along an injective ring homomorphism is injective. -/
theorem mapRingHom_injective {f : R →+* S} (hf : Function.Injective f) :
    Function.Injective (mapRingHom f : BrauerAlgebra R δ k →+* BrauerAlgebra S (f δ) k) :=
  fun _ _ h => ext <| Finsupp.mapRange_injective f (map_zero f) hf <| congrArg coeff h

/-- The coefficient change along a surjective ring homomorphism is surjective: for instance every
element of the Brauer algebra over `ZMod p` lifts to the integral Brauer algebra. -/
theorem mapRingHom_surjective {f : R →+* S} (hf : Function.Surjective f) :
    Function.Surjective (mapRingHom f : BrauerAlgebra R δ k →+* BrauerAlgebra S (f δ) k) :=
  fun y => by
    obtain ⟨c, hc⟩ := Finsupp.mapRange_surjective f (map_zero f) hf y.coeff
    exact ⟨ofCoeff c, ext hc⟩

/-- **The coefficient change on the symmetric group**: on the group algebra of `Sₖ` inside the
Brauer algebra it is the coefficient change `MonoidAlgebra.mapRingHom` of the group algebra. -/
theorem mapRingHom_ofPerm (f : R →+* S) (x : MonoidAlgebra R (Equiv.Perm (Fin k))) :
    mapRingHom f (ofPerm R δ k x) =
      ofPerm S (f δ) k (MonoidAlgebra.mapRingHom (Equiv.Perm (Fin k)) f x) := by
  induction x using MonoidAlgebra.induction_linear with
  | zero => simp
  | add x y hx hy => simp only [map_add, hx, hy]
  | single σ r => simp [MonoidAlgebra.mapRingHom_single]

/-! ### The scalar-extension isomorphism -/

section ScalarTensor

variable [Algebra R S]

variable (R S δ k) in
/-- The scalar-extension isomorphism as an `S`-linear equivalence: it reads the coefficients of an
element of `S ⊗[R] B_k(δ)` in the basis `1 ⊗ D` as coefficients of an element of
`B_k(algebraMap R S δ)`. -/
private noncomputable def scalarTensorLinearEquiv :
    S ⊗[R] BrauerAlgebra R δ k ≃ₗ[S] BrauerAlgebra S (algebraMap R S δ) k :=
  (Algebra.TensorProduct.basis S (basis R δ k)).repr ≪≫ₗ
    (coeffLinearEquiv S (algebraMap R S δ) k).symm

private theorem scalarTensorLinearEquiv_tmul (s : S) (x : BrauerAlgebra R δ k) :
    scalarTensorLinearEquiv R S δ k (s ⊗ₜ x) = s • mapRingHom (algebraMap R S) x :=
  ext <| by simp [scalarTensorLinearEquiv, Algebra.TensorProduct.basis_repr_tmul]

variable (R S δ k) in
/-- **The scalar-extension isomorphism** `S ⊗[R] B_k(δ) ≃ₐ[S] B_k(algebraMap R S δ)` of the Brauer
algebra along an `R`-algebra `S`: it sends `s ⊗ x` to `s` times the coefficient change of `x`
(`TauCeti.BrauerAlgebra.scalarTensorEquiv_tmul`), so it matches the basis `1 ⊗ D` of the scalar
extension with the diagram basis over `S`. -/
noncomputable def scalarTensorEquiv :
    S ⊗[R] BrauerAlgebra R δ k ≃ₐ[S] BrauerAlgebra S (algebraMap R S δ) k :=
  AlgEquiv.ofLinearEquiv (scalarTensorLinearEquiv R S δ k)
    (by rw [Algebra.TensorProduct.one_def, scalarTensorLinearEquiv_tmul, map_one, one_smul])
    fun x y => by
      induction x using TensorProduct.inductionOn with
      | add x₁ x₂ h₁ h₂ => simp only [add_mul, map_add, h₁, h₂]
      | tmul s x =>
      induction y using TensorProduct.inductionOn with
      | add y₁ y₂ h₁ h₂ => simp only [mul_add, map_add, h₁, h₂]
      | tmul t y =>
        simp only [Algebra.TensorProduct.tmul_mul_tmul, scalarTensorLinearEquiv_tmul, map_mul,
          smul_mul_smul_comm]

/-- **The scalar-extension isomorphism on pure tensors**: `s ⊗ x` goes to `s` times the coefficient
change of `x`. -/
@[simp]
theorem scalarTensorEquiv_tmul (s : S) (x : BrauerAlgebra R δ k) :
    scalarTensorEquiv R S δ k (s ⊗ₜ x) = s • mapRingHom (algebraMap R S) x :=
  scalarTensorLinearEquiv_tmul s x

/-- **The inverse of the scalar-extension isomorphism on the diagram basis**: a diagram over `S`
comes from `1 ⊗ D`. -/
@[simp]
theorem scalarTensorEquiv_symm_of (D : BrauerDiagram k) :
    (scalarTensorEquiv R S δ k).symm (of D) = 1 ⊗ₜ of D := by
  rw [AlgEquiv.symm_apply_eq, scalarTensorEquiv_tmul, mapRingHom_of, one_smul]

end ScalarTensor

end BrauerAlgebra

end TauCeti
