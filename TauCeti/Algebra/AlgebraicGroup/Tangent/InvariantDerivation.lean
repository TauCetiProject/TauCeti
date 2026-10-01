/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.Tangent.Cotangent
public import TauCeti.Algebra.AlgebraicGroup.Representation.Differential
public import TauCeti.LinearAlgebra.TensorProduct.Basic
public import Mathlib.RingTheory.Nilpotent.Lemmas
import Mathlib.LinearAlgebra.Dual.Lemmas
import TauCeti.RingTheory.Derivation.Nilpotent

/-!
# Invariant derivations and nilpotent functions

Let `H` be a commutative bialgebra over `R`, the coordinate ring of an affine monoid. A tangent
vector at the identity is a counit-valued derivation `d`. It extends to the derivation

```text
D h = ∑ h₍₁₎ d(h₍₂₎)
```

of the whole coordinate ring: the left-invariant vector field with value `d` at the identity.
As a linear map it is the action of `d` in the differentiated regular representation
(`TauCeti.Comodule.differential`); the point here is that this action satisfies the Leibniz
rule. It satisfies `ε ∘ D = d` and the invariance identity `Δ ∘ D = (id ⊗ D) ∘ Δ`.

Over a domain of characteristic zero, every derivation of `H` sends nilpotent functions into the
prime ideal `ker ε`. Applied to the invariant extension of `d`, this shows that every tangent
vector at the identity vanishes on the nilradical. Over a field of characteristic zero it
follows that the nilradical lies in the square of the augmentation ideal: nilpotent functions
vanish to second order at the identity, so the closed subscheme they cut out has the same
tangent space as the ambient group. This is the infinitesimal input to Cartier's theorem.

## Main declarations

* `TauCeti.Bialgebra.leftInvariantDerivation`: the left-invariant derivation extending a tangent
  vector at the identity.
* `TauCeti.Bialgebra.counit_leftInvariantDerivation`: its value at the identity is the tangent
  vector.
* `TauCeti.Bialgebra.comul_leftInvariantDerivation`: its invariance under left translations.
* `TauCeti.Bialgebra.eq_leftInvariantDerivation`: a left-invariant derivation is determined
  by its value at the identity.
* `Derivation.apply_eq_zero_of_isNilpotent`: in characteristic zero, tangent vectors at the
  identity vanish on nilpotent functions.
* `TauCeti.Bialgebra.nilradical_le_augmentationIdeal_sq`: over a field of characteristic zero,
  the nilradical lies in the square of the augmentation ideal.

## References

* J. S. Milne, *Algebraic Groups* (2017), Chapter 3 (Cartier's theorem) and Chapter 10.
* W. C. Waterhouse, *Introduction to Affine Group Schemes*, Chapters 11 and 12.
-/

public section

open TensorProduct LinearMap

namespace TauCeti.Bialgebra

variable {R H : Type*} [CommRing R] [CommRing H] [_root_.Bialgebra R H]

/-- Contracting the right tensor factor against a tangent vector satisfies the Leibniz rule
with respect to contraction against the counit. -/
private theorem tensorComponent_mul (d : Derivation R H (CounitAlgebra R H R)) (X Y : H ⊗[R] H) :
    tensorComponent ((CounitAlgebra.algEquivSelf R H R).toLinearMap ∘ₗ d.toLinearMap) (X * Y) =
      tensorComponent (Coalgebra.counit (R := R)) X *
          tensorComponent ((CounitAlgebra.algEquivSelf R H R).toLinearMap ∘ₗ d.toLinearMap) Y +
        tensorComponent (Coalgebra.counit (R := R)) Y *
          tensorComponent ((CounitAlgebra.algEquivSelf R H R).toLinearMap ∘ₗ d.toLinearMap) X := by
  induction X using TensorProduct.inductionOn with
  | add X X' hX hX' => simp only [add_mul, map_add, hX, hX']; ring
  | tmul a b =>
    induction Y using TensorProduct.inductionOn with
    | add Y Y' hY hY' => simp only [mul_add, map_add, hY, hY']; ring
    | tmul a' b' =>
      simp only [Algebra.TensorProduct.tmul_mul_tmul, tensorComponent_tmul, LinearMap.comp_apply,
        AlgEquiv.toLinearMap_apply, Derivation.coeFn_coe, CounitAlgebra.algEquivSelf_apply_mul,
        Algebra.algebraMap_self, RingHom.id_apply, Algebra.smul_def, map_add, map_mul]
      ring

/-- **The left-invariant derivation extending a tangent vector at the identity**:
`h ↦ ∑ h₍₁₎ d(h₍₂₎)`. It is the action of `d` in the differentiated regular representation. -/
noncomputable def leftInvariantDerivation (d : Derivation R H (CounitAlgebra R H R)) :
    Derivation R H H :=
  Derivation.mk' (Comodule.differential (R := R) (H := H) (M := H) d) fun a b ↦ by
    have hcounit (c : H) :
        tensorComponent (Coalgebra.counit (R := R)) (Coalgebra.comul (R := R) c) = c := by
      have hc := LinearMap.congr_fun (Comodule.coactComponent_counit (R := R) (C := H) (M := H)) c
      rwa [Comodule.coactComponent_apply, Comodule.instSelf_coact, LinearMap.id_apply] at hc
    simp only [Comodule.differential_apply, Comodule.instSelf_coact,
      _root_.Bialgebra.comul_mul, tensorComponent_mul, hcounit, smul_eq_mul]

/-- The left-invariant derivation is the differentiated regular representation. -/
theorem toLinearMap_leftInvariantDerivation (d : Derivation R H (CounitAlgebra R H R)) :
    (leftInvariantDerivation d).toLinearMap = Comodule.differential (R := R) (H := H) (M := H) d :=
  Derivation.coe_mk'_linearMap _ _

/-- The left-invariant derivation contracts the comultiplication against the tangent vector. -/
theorem leftInvariantDerivation_apply (d : Derivation R H (CounitAlgebra R H R)) (h : H) :
    leftInvariantDerivation d h =
      tensorComponent ((CounitAlgebra.algEquivSelf R H R).toLinearMap ∘ₗ d.toLinearMap)
        (Coalgebra.comul (R := R) h) := by
  rw [← Derivation.coeFn_coe, toLinearMap_leftInvariantDerivation, Comodule.differential_apply,
    Comodule.instSelf_coact]

/-- **The left-invariant derivation has value `d` at the identity**: `ε ∘ D = d`. -/
@[simp]
theorem counit_leftInvariantDerivation (d : Derivation R H (CounitAlgebra R H R)) (h : H) :
    Coalgebra.counit (R := R) (leftInvariantDerivation d h) =
      CounitAlgebra.algEquivSelf R H R (d h) := by
  have h' := LinearMap.congr_fun
    (TauCeti.LinearMap.comp_tensorComponent (Coalgebra.counit (R := R) (A := H))
      ((CounitAlgebra.algEquivSelf R H R).toLinearMap ∘ₗ d.toLinearMap))
    (Coalgebra.comul (R := R) (A := H) h)
  rw [LinearMap.comp_apply, ← leftInvariantDerivation_apply] at h'
  simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, Coalgebra.rTensor_counit_comul,
    TensorProduct.lid_tmul, one_smul, AlgEquiv.toLinearMap_apply, Derivation.coeFn_coe] at h'
  exact h'

/-- **The left-invariant derivation commutes with left translations**:
`Δ ∘ D = (id ⊗ D) ∘ Δ`. -/
theorem comul_leftInvariantDerivation (d : Derivation R H (CounitAlgebra R H R)) (h : H) :
    Coalgebra.comul (R := R) (leftInvariantDerivation d h) =
      (leftInvariantDerivation d).toLinearMap.lTensor H (Coalgebra.comul (R := R) h) := by
  set φ := (CounitAlgebra.algEquivSelf R H R).toLinearMap ∘ₗ d.toLinearMap
  have hD : (leftInvariantDerivation d).toLinearMap = tensorComponent φ ∘ₗ Coalgebra.comul :=
    LinearMap.ext (leftInvariantDerivation_apply d)
  rw [leftInvariantDerivation_apply, hD, LinearMap.lTensor_comp, LinearMap.comp_apply,
    ← TauCeti.LinearMap.tensorComponent_assoc_symm,
    Coalgebra.coassoc_symm_apply, LinearMap.rTensor, tensorComponent_map, LinearMap.comp_id]

/-- A left-invariant derivation with value `d` at the identity is the left-invariant
extension of `d`. -/
theorem eq_leftInvariantDerivation (D : Derivation R H H)
    (d : Derivation R H (CounitAlgebra R H R))
    (hε : ∀ h, Coalgebra.counit (R := R) (D h) = CounitAlgebra.algEquivSelf R H R (d h))
    (hΔ : ∀ h, Coalgebra.comul (R := R) (D h) =
      D.toLinearMap.lTensor H (Coalgebra.comul (R := R) h)) :
    D = leftInvariantDerivation d := by
  have hvalue : Coalgebra.counit (R := R) ∘ₗ D.toLinearMap =
      (CounitAlgebra.algEquivSelf R H R).toLinearMap ∘ₗ d.toLinearMap := LinearMap.ext hε
  ext h
  have hc := congrArg (tensorComponent (Coalgebra.counit (R := R))) (hΔ h)
  rw [LinearMap.lTensor, tensorComponent_map, hvalue, LinearMap.id_apply,
    ← leftInvariantDerivation_apply] at hc
  have hidentity := LinearMap.congr_fun
    (Comodule.coactComponent_counit (R := R) (C := H) (M := H)) (D h)
  rw [Comodule.coactComponent_apply, Comodule.instSelf_coact, LinearMap.id_apply] at hidentity
  exact hidentity.symm.trans hc

end TauCeti.Bialgebra

namespace Derivation

open TauCeti

variable {R H : Type*} [CommRing R] [IsDomain R] [CharZero R] [CommRing H] [Bialgebra R H]

/-- **In characteristic zero, a tangent vector at the identity vanishes on nilpotent
functions.** The base ring may be any domain of characteristic zero. -/
theorem apply_eq_zero_of_isNilpotent (d : Derivation R H (Bialgebra.CounitAlgebra R H R))
    {x : H} (hx : IsNilpotent x) : d x = 0 := by
  -- The left-invariant extension sends `x` into the prime ideal `ker ε`, whose residue
  -- ring is the characteristic-zero domain `R`; its counit is the original tangent value.
  have _ : (Bialgebra.AugmentationIdeal R H).IsPrime := RingHom.ker_isPrime _
  have hmem := (Bialgebra.leftInvariantDerivation d).apply_mem_of_isNilpotent
    (p := Bialgebra.AugmentationIdeal R H) (fun n hn ↦ by simpa using hn) hx
  rw [RingHom.mem_ker] at hmem
  apply (Bialgebra.CounitAlgebra.algEquivSelf R H R).injective
  rw [← Bialgebra.counit_leftInvariantDerivation, map_zero]
  exact hmem

end Derivation

namespace TauCeti.Bialgebra

variable {k H : Type*} [Field k] [CharZero k] [CommRing H] [_root_.Bialgebra k H]

/-- **Over a field of characteristic zero, nilpotent functions vanish to second order at the
identity**: the nilradical lies in the square of the augmentation ideal. Equivalently, the
reduced closed subscheme has the same tangent space at the identity. -/
theorem nilradical_le_augmentationIdeal_sq :
    nilradical H ≤ AugmentationIdeal k H ^ 2 := by
  intro x hx
  have hx' : IsNilpotent x := mem_nilradical.mp hx
  have hxI : x ∈ AugmentationIdeal k H := (hx'.map (_root_.Bialgebra.counitAlgHom k H)).eq_zero
  rw [← (AugmentationIdeal k H).toCotangent_eq_zero ⟨x, hxI⟩,
    ← Module.forall_dual_apply_eq_zero_iff k]
  intro f
  have hf := Derivation.cotangentLinearEquiv_symm_toCotangent
    (Derivation.cotangentLinearEquiv (R := k) (A := H) (B := k) f) ⟨x, hxI⟩
  rw [LinearEquiv.symm_apply_apply] at hf
  rw [hf, Derivation.apply_eq_zero_of_isNilpotent _ hx', map_zero]

end TauCeti.Bialgebra
