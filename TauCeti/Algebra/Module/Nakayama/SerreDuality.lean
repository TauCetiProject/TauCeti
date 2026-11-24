/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.PerfectPairing.Basic
public import TauCeti.Algebra.Module.Nakayama.Hom

/-!
# Serre duality for the Nakayama functor

Let `A` be an algebra over a commutative ring `k`, let `P` be a finite projective left
`A`-module and write `ν(P) = D Hom_A(P, A)` for its Nakayama module. Serre duality says that
the pairing

`Hom_A(P, M) × Hom_A(M, ν(P)) → k`,  `(f, g) ↦ tr_P(g ∘ f)`

is perfect, where the **Nakayama trace** `tr_P : Hom_A(P, ν(P)) → k` evaluates the functional
on `Hom_A(P, P)` corresponding to a map `P → ν(P)` at the identity. Hence
`Hom_A(P, M) ≃ D Hom_A(M, ν(P))`, naturally in `P` and `M`, whenever `Hom_A(P, M)` is
reflexive over `k`; over a field this holds as soon as `Hom_A(P, M)` is finite-dimensional, for
instance when `A` is a finite-dimensional algebra and `M` a finite-dimensional module.

The pairing is the inverse of the Hom duality `TauCeti.nakayamaHomEquiv`,
`D Hom_A(P, M) ≃ Hom_A(M, ν(P))`, read with its arguments exchanged. The content of this file
is the trace description of that pairing, the cyclicity
`tr_Q(h ∘ u) = tr_P(ν(u) ∘ h)` of the Nakayama trace, which gives naturality in the projective
module, and perfectness under reflexivity.

## Main definitions

* `TauCeti.nakayamaTrace`: the Nakayama trace `tr_P : Hom_A(P, ν(P)) → k`.
* `TauCeti.nakayamaSerrePairing`: the Serre pairing `(f, g) ↦ tr_P(g ∘ f)` between
  `Hom_A(P, M)` and `Hom_A(M, ν(P))`.

## Main results

* `TauCeti.nakayamaHomEquiv_symm_apply_eq_nakayamaTrace`: the functional on `Hom_A(P, M)`
  corresponding to `g : M → ν(P)` is `f ↦ tr_P(g ∘ f)`.
* `TauCeti.nakayamaTrace_comp_comm`: the Nakayama trace is cyclic, `tr_Q(h ∘ u) = tr_P(ν(u) ∘ h)`.
* `TauCeti.nakayamaSerrePairing_comp_left` and `TauCeti.nakayamaSerrePairing_comp_right`:
  naturality of the Serre pairing in the module `M` and in the projective module `P`.
* `TauCeti.nakayamaSerrePairing.instIsPerfPair`: Serre duality, the Serre pairing is perfect
  when `Hom_A(P, M)` is reflexive over `k`. Its `LinearMap.toPerfPair` is the isomorphism
  `Hom_A(P, M) ≃ D Hom_A(M, ν(P))`.

## References

* J. Grant, *The Nakayama automorphism of a self-injective preprojective algebra*,
  https://arxiv.org/abs/1906.11817, Theorem 2.3.
* M. Auslander, I. Reiten, S. O. Smalø, *Representation Theory of Artin Algebras*,
  Cambridge University Press (1995), Section IV.2.
-/

public section

namespace TauCeti

universe u v w z t s

variable (k : Type u) (A : Type v) [CommRing k] [Ring A] [Algebra k A]
  (P : Type w) [AddCommGroup P] [Module A P] [Module k P] [IsScalarTower k A P]
  [Module.Finite A P] [Module.Projective A P]

/-- The **Nakayama trace** `tr_P : Hom_A(P, ν(P)) → k` of a finite projective module `P`: a map
`h : P → ν(P)` corresponds under `TauCeti.nakayamaHomEquiv` to a functional on `Hom_A(P, P)`, and
`tr_P(h)` is its value at the identity. For `P = A` it is evaluation of `h(1) ∈ D Hom_A(A, A)` at
the identity (`TauCeti.nakayamaTrace_self_apply`). -/
noncomputable def nakayamaTrace : (P →ₗ[A] NakayamaModule k A P) →ₗ[k] k :=
  Module.Dual.eval k (P →ₗ[A] P) LinearMap.id ∘ₗ (nakayamaHomEquiv k A P P).symm.toLinearMap

/-- The Nakayama trace evaluates the functional corresponding to a map at the identity. -/
theorem nakayamaTrace_apply (h : P →ₗ[A] NakayamaModule k A P) :
    nakayamaTrace k A P h = (nakayamaHomEquiv k A P P).symm h LinearMap.id :=
  (rfl)

variable {k A P}

/-- On the regular module, the Nakayama trace of `h : A → ν(A)` evaluates the functional
`h(1) ∈ D Hom_A(A, A)` at the identity. -/
theorem nakayamaTrace_self_apply (h : A →ₗ[A] NakayamaModule k A A) :
    nakayamaTrace k A A h = NakayamaModule.equivDual k A A (h 1) LinearMap.id := by
  have hid : balancedDualTensorHom k A A A (BalancedTensorProduct.tmul k A LinearMap.id 1) =
      LinearMap.id := by
    ext
    simp
  rw [nakayamaTrace_apply, ← nakayamaHomEquiv_symm_apply, hid]

variable {M : Type z} [AddCommGroup M] [Module A M] [Module k M] [IsScalarTower k A M]
variable {Q : Type s} [AddCommGroup Q] [Module A Q] [Module k Q] [IsScalarTower k A Q]
  [Module.Finite A Q] [Module.Projective A Q]

/-- **The Hom duality functional is given by the Nakayama trace.** The functional on
`Hom_A(P, M)` corresponding to `g : M → ν(P)` under `TauCeti.nakayamaHomEquiv` sends `f` to the
Nakayama trace of `g ∘ f`. -/
theorem nakayamaHomEquiv_symm_apply_eq_nakayamaTrace (g : M →ₗ[A] NakayamaModule k A P)
    (f : P →ₗ[A] M) :
    (nakayamaHomEquiv k A P M).symm g f = nakayamaTrace k A P (g ∘ₗ f) := by
  -- Naturality of the Hom duality in the coefficient module, along `f : P → M`.
  have h : (nakayamaHomEquiv k A P P).symm (g ∘ₗ f) =
      (f.compRight k).dualMap ((nakayamaHomEquiv k A P M).symm g) := by
    rw [LinearEquiv.symm_apply_eq, nakayamaHomEquiv_dualMap_compRight,
      LinearEquiv.apply_symm_apply]
  rw [nakayamaTrace_apply, h, LinearMap.dualMap_apply, LinearMap.compRight_apply,
    LinearMap.comp_id]

/-- **The Nakayama trace is cyclic.** For finite projective modules `P` and `Q`, a map
`u : Q → P` and a map `h : P → ν(Q)`, the Nakayama trace of `h ∘ u` on `Q` is the Nakayama trace
of `ν(u) ∘ h` on `P`. -/
theorem nakayamaTrace_comp_comm (u : Q →ₗ[A] P) (h : P →ₗ[A] NakayamaModule k A Q) :
    nakayamaTrace k A Q (h ∘ₗ u) = nakayamaTrace k A P (u.nakayamaMap ∘ₗ h) := by
  -- Both sides equal the functional corresponding to `h` on `Hom_A(Q, P)`, evaluated at `u`.
  have h' : (nakayamaHomEquiv k A P P).symm (u.nakayamaMap ∘ₗ h) =
      (u.lcomp k P).dualMap ((nakayamaHomEquiv k A Q P).symm h) := by
    rw [LinearEquiv.symm_apply_eq, nakayamaHomEquiv_dualMap_lcomp,
      LinearEquiv.apply_symm_apply]
  rw [← nakayamaHomEquiv_symm_apply_eq_nakayamaTrace, nakayamaTrace_apply, h',
    LinearMap.dualMap_apply, LinearMap.lcomp_apply', LinearMap.id_comp]

variable (k A P M)

/-- The **Serre pairing** `Hom_A(P, M) × Hom_A(M, ν(P)) → k`, `(f, g) ↦ tr_P(g ∘ f)`, for a
finite projective module `P` (`TauCeti.nakayamaSerrePairing_apply`). It is perfect when
`Hom_A(P, M)` is reflexive over `k` (`TauCeti.nakayamaSerrePairing.instIsPerfPair`). -/
noncomputable def nakayamaSerrePairing :
    (P →ₗ[A] M) →ₗ[k] (M →ₗ[A] NakayamaModule k A P) →ₗ[k] k :=
  (nakayamaHomEquiv k A P M).symm.toLinearMap.flip

variable {k A P M}

/-- The Serre pairing of `f` and `g` is the Nakayama trace of `g ∘ f`. -/
@[simp]
theorem nakayamaSerrePairing_apply (f : P →ₗ[A] M) (g : M →ₗ[A] NakayamaModule k A P) :
    nakayamaSerrePairing k A P M f g = nakayamaTrace k A P (g ∘ₗ f) :=
  nakayamaHomEquiv_symm_apply_eq_nakayamaTrace g f

/-- **Serre duality.** If `Hom_A(P, M)` is reflexive over `k`, for instance finite-dimensional
over a field, then the Serre pairing `(f, g) ↦ tr_P(g ∘ f)` between `Hom_A(P, M)` and
`Hom_A(M, ν(P))` is perfect. Its `LinearMap.toPerfPair` is the Serre duality isomorphism
`Hom_A(P, M) ≃ D Hom_A(M, ν(P))`. -/
instance nakayamaSerrePairing.instIsPerfPair [Module.IsReflexive k (P →ₗ[A] M)] :
    (nakayamaSerrePairing k A P M).IsPerfPair :=
  .flip (inferInstanceAs (nakayamaHomEquiv k A P M).symm.toLinearMap.IsPerfPair)

/-- **Serre duality is natural in the module.** For `h : M → M'`, pairing `h ∘ f` with `g` is
pairing `f` with `g ∘ h`. -/
theorem nakayamaSerrePairing_comp_left {M' : Type t} [AddCommGroup M'] [Module A M']
    [Module k M'] [IsScalarTower k A M'] (h : M →ₗ[A] M') (f : P →ₗ[A] M)
    (g : M' →ₗ[A] NakayamaModule k A P) :
    nakayamaSerrePairing k A P M' (h ∘ₗ f) g = nakayamaSerrePairing k A P M f (g ∘ₗ h) := by
  simp only [nakayamaSerrePairing_apply, LinearMap.comp_assoc]

/-- **Serre duality is natural in the projective module.** For finite projective modules `P`
and `Q` and `u : Q → P`, pairing `f ∘ u` with `g : M → ν(Q)` is pairing `f` with
`ν(u) ∘ g : M → ν(P)`. -/
theorem nakayamaSerrePairing_comp_right (u : Q →ₗ[A] P) (f : P →ₗ[A] M)
    (g : M →ₗ[A] NakayamaModule k A Q) :
    nakayamaSerrePairing k A Q M (f ∘ₗ u) g =
      nakayamaSerrePairing k A P M f (u.nakayamaMap ∘ₗ g) := by
  simp only [nakayamaSerrePairing_apply, ← LinearMap.comp_assoc, nakayamaTrace_comp_comm]

end TauCeti
