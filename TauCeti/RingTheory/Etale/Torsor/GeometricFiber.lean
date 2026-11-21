/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.Etale.Torsor.Basic
import TauCeti.RingTheory.Etale.Torsor.Descent
import TauCeti.RingTheory.Etale.Galois
import TauCeti.Algebra.Algebra.Pi

/-!
# The geometric fibre criterion for finite étale torsors

A finite étale algebra over a field with a finite group action is a torsor if and only if the set
of points over a separably closed extension is nonempty and the induced right action is simply
transitive. On the points, the Galois map sends `(g, x)` to `(x, x · g)`, where `x · g` is
precomposition of `x` by the action of `g` on the algebra. In the converse direction any point
identifies the split algebra over the separably closed field with the trivial torsor.

## References

* A. Merkurjev and F. Scavia, *Galois representations modulo `p` that do not lift modulo `p²`*,
  §1.2, [arXiv:2410.12560](https://arxiv.org/abs/2410.12560).
* The splitting over a separably closed field is `Algebra.Etale.tensorProductEquivPi`.
-/

public section

open scoped TensorProduct

namespace AlgHom

section Points

variable {G R A L : Type*} [Monoid G] [CommRing R] [CommRing A] [Algebra R A]
  [CommSemiring L] [Algebra R L] [MulSemiringAction G A] [SMulCommClass G R A]

/-- Evaluating the `g`-coordinate of the Galois map at `x` gives the pair consisting of `x`
and its right translate by `g`. -/
theorem comp_evalAlgHom_tensorToPi (x : A →ₐ[R] L) (g : G) :
    (x.comp (Pi.evalAlgHom R (fun _ : G ↦ A) g)).comp
        ((TauCeti.MulSemiringAction.tensorToPi R A G).restrictScalars R) =
      Algebra.TensorProduct.productMap x (x.comp (MulSemiringAction.toAlgHom R A g)) := by
  exact Algebra.TensorProduct.ext' fun a b ↦ by simp

end Points

section OrbitMap

open TauCeti.Algebra (IsFiniteEtaleTorsor)
open Algebra.TensorProduct (productMap)

/-- At any point `x` of a finite étale torsor with values in a nontrivial semiring without zero
divisors, the right orbit map is a bijection onto all points with values in that semiring. -/
theorem bijective_geometricOrbitMap {G R A L : Type*} [Group G] [_root_.Finite G] [CommRing R]
    [CommRing A] [Algebra R A] [CommSemiring L] [Nontrivial L] [NoZeroDivisors L] [Algebra R L]
    [MulSemiringAction G A] [SMulCommClass G R A] [h : IsFiniteEtaleTorsor G R A]
    (x : A →ₐ[R] L) :
    Function.Bijective (fun g : G ↦ x.comp (MulSemiringAction.toAlgHom R A g)) := by
  let τ := (TauCeti.MulSemiringAction.tensorToPi R A G).restrictScalars R
  let e := AlgHom.sigmaEquivPi (R := R) (fun _ : G ↦ A) L
  have hτ : Function.Bijective τ := h.bijective_tensorToPi
  have hcomp (g : G) (z : A →ₐ[R] L) :
      (e ⟨g, z⟩).comp τ = productMap z (z.comp (MulSemiringAction.toAlgHom R A g)) := by
    simpa only [e, AlgHom.sigmaEquivPi_apply] using z.comp_evalAlgHom_tensorToPi g
  constructor
  · intro g j hgj
    have hh : (e ⟨g, x⟩).comp τ = (e ⟨j, x⟩).comp τ := by
      rw [hcomp, hcomp]
      exact congrArg (productMap x) hgj
    have heq : e ⟨g, x⟩ = e ⟨j, x⟩ := AlgHom.ext fun p ↦ by
      obtain ⟨t, rfl⟩ := hτ.surjective p
      exact DFunLike.congr_fun hh t
    exact congrArg Sigma.fst (e.injective heq)
  · intro y
    let ψ := (productMap x y).comp (AlgEquiv.ofBijective τ hτ).symm.toAlgHom
    obtain ⟨⟨g, z⟩, hz⟩ := e.surjective ψ
    have heq : productMap z (z.comp (MulSemiringAction.toAlgHom R A g)) = productMap x y := by
      rw [← hcomp, hz]
      refine AlgHom.ext fun t ↦ ?_
      simp only [ψ, AlgHom.comp_apply, AlgEquiv.coe_toAlgHom, ← AlgEquiv.ofBijective_apply τ hτ,
        AlgEquiv.symm_apply_apply]
    have hzx : z = x := AlgHom.ext fun a ↦ by
      simpa using DFunLike.congr_fun heq (a ⊗ₜ[R] (1 : A))
    subst z
    exact ⟨g, AlgHom.ext fun b ↦ by simpa using DFunLike.congr_fun heq ((1 : A) ⊗ₜ[R] b)⟩

end OrbitMap

variable {G K A Ω : Type*} [Group G] [_root_.Finite G] [Field K] [CommRing A] [Algebra K A]
  [Field Ω] [Algebra K Ω] [MulSemiringAction G A] [SMulCommClass G K A]

attribute [local instance] Algebra.TensorProduct.rightMulSemiringAction

/-- A finite étale algebra with a simply transitive orbit of points over a separably closed
extension is a torsor. -/
theorem isFiniteEtaleTorsor_of_bijective_geometricOrbitMap [IsSepClosed Ω] [Algebra.Etale K A]
    (x : A →ₐ[K] Ω) (hx : Function.Bijective (fun g : G ↦
      x.comp (MulSemiringAction.toAlgHom K A g))) : TauCeti.Algebra.IsFiniteEtaleTorsor G K A := by
  let orbit := Equiv.ofBijective _ hx
  let e := (Algebra.Etale.tensorProductEquivPi K Ω A).trans
    (AlgEquiv.piCongrLeft' Ω (fun _ ↦ Ω) orbit.symm)
  refine TauCeti.Algebra.IsFiniteEtaleTorsor.of_baseChange_algEquiv_pi Ω e fun g t k ↦ ?_
  induction t using TensorProduct.inductionOn with
  | tmul ω a =>
    simp [e, orbit, Algebra.TensorProduct.rightMulSemiringAction_smul_def, mul_smul]
  | add t u ht hu => simp [smul_add, ht, hu]

end AlgHom

namespace TauCeti.Algebra.IsFiniteEtaleTorsor

variable {G K A : Type*} [Group G] [Finite G] [Field K] [CommRing A] [Algebra K A]
  [MulSemiringAction G A] [SMulCommClass G K A]

/-- The geometric fibre criterion: a finite étale algebra over a field is a torsor exactly when
its fibre over a separably closed extension is nonempty and the right action is simply transitive.
The nonemptiness condition excludes the zero algebra. -/
theorem iff_geometricFiber (Ω : Type*) [Field Ω] [Algebra K Ω] [IsSepClosed Ω]
    [_root_.Algebra.Etale K A] :
    IsFiniteEtaleTorsor G K A ↔ Nonempty (A →ₐ[K] Ω) ∧
      ∀ x : A →ₐ[K] Ω, Function.Bijective (fun g : G ↦
        x.comp (_root_.MulSemiringAction.toAlgHom K A g)) := by
  refine ⟨fun h ↦ ⟨?_, AlgHom.bijective_geometricOrbitMap⟩, ?_⟩
  · have : Nontrivial A := ((iff_field K).mp h).1
    by_contra hΩ
    let : IsEmpty (A →ₐ[K] Ω) := not_nonempty_iff.mp hΩ
    exact zero_ne_one ((_root_.Algebra.Etale.pi_id_injective K Ω A) (Subsingleton.elim _ _))
  · rintro ⟨⟨x⟩, hx⟩
    exact x.isFiniteEtaleTorsor_of_bijective_geometricOrbitMap (hx x)

end TauCeti.Algebra.IsFiniteEtaleTorsor
