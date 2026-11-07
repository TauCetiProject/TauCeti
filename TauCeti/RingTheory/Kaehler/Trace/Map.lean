/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axel Delaval, Jie Xu, Shitan Xu
-/
module

public import TauCeti.RingTheory.Kaehler.Trace.Basic

/-!
# Functoriality of the trace of differentials

The trace derivation commutes with compatible maps of finite free algebras that take a basis
to a basis (`Algebra.traceDeriv_map`), and with postcomposition of the original derivation by
a linear map (`Algebra.traceDeriv_compDer`). This includes the algebraic compatibility needed
for localization and base-change arguments.

## Source

Adapted from `Jacobian/RingTheory/Kaehler/TraceMap.lean` in the Jacobian library,
accepted release `baef7723da528551b7d2f93bd9a9a53303b04dbc`.
Only the functoriality lemmas and their matrix prerequisite are included here.
-/

@[expose] public section

open Algebra

namespace Algebra

variable {k R B M R' B' M' : Type*} [CommRing k] [CommRing R] [CommRing B] [Algebra k R]
  [Algebra R B] [AddCommGroup M] [Module R M] [Module k M] (D : Derivation k R M)
  [CommRing R'] [CommRing B'] [Algebra k R'] [Algebra R' B'] [AddCommGroup M'] [Module R' M']
  [Module k M'] (D' : Derivation k R' M')

/-- The matrix of multiplication by `ψ x` in the image of a basis is the image of the matrix of
multiplication by `x`. -/
lemma leftMulMatrix_map {ι : Type*} [Fintype ι] [DecidableEq ι] (b : Module.Basis ι R B)
    (b' : Module.Basis ι R' B') (σ : R →+* R') (ψ : B →+* B')
    (hψ : ∀ r, ψ (algebraMap R B r) = algebraMap R' B' (σ r)) (hb : ∀ i, b' i = ψ (b i))
    (x : B) : leftMulMatrix b' (ψ x) = (leftMulMatrix b x).map σ := by
  have hrepr (y : B) : b'.repr (ψ y) = Finsupp.mapRange σ σ.map_zero (b.repr y) := by
    conv_lhs => rw [← b.sum_repr y]
    rw [map_sum]
    simp_rw [Algebra.smul_def, map_mul, hψ, ← hb, ← Algebra.smul_def]
    ext i
    rw [b'.repr_sum_self, Finsupp.mapRange_apply]
  ext i j
  rw [Matrix.map_apply, leftMulMatrix_eq_repr_mul, leftMulMatrix_eq_repr_mul, hb, ← map_mul,
    hrepr, Finsupp.mapRange_apply]

variable [Module.Free R B] [Module.Finite R B] [Module.Free R' B'] [Module.Finite R' B']

/-- **Functoriality of the trace derivation.** Let `σ : R → R'`, `ψ : B → B'` and `μ : M → M'`
be compatible maps such that `ψ` maps a basis of `B` over `R` to a basis of `B'` over `R'`, and
`D' ∘ σ = μ ∘ D`. Then `traceDeriv D' (ψ a) (ψ c) = μ (traceDeriv D a c)`. -/
lemma traceDeriv_map {ι : Type*} [Finite ι] (b : Module.Basis ι R B)
    (b' : Module.Basis ι R' B') (σ : R →+* R') (ψ : B →+* B')
    (hψ : ∀ r, ψ (algebraMap R B r) = algebraMap R' B' (σ r)) (hb : ∀ i, b' i = ψ (b i))
    (μ : M →+ M') (hμ : ∀ (r : R) (m : M), μ (r • m) = σ r • μ m)
    (hD : ∀ r, D' (σ r) = μ (D r)) (a c : B) :
    traceDeriv D' (ψ a) (ψ c) = μ (traceDeriv D a c) := by
  classical
  have := Fintype.ofFinite ι
  rw [traceDeriv_eq D' b', traceDeriv_eq D b, traceDerivAux, traceDerivAux,
    leftMulMatrix_map b b' σ ψ hψ hb, leftMulMatrix_map b b' σ ψ hψ hb]
  simp only [Matrix.traceDerivForm, Matrix.map_apply, map_sum, hμ, hD]

end Algebra

namespace Algebra

variable {k R B M M' : Type*} [CommRing k] [CommRing R] [CommRing B] [Algebra k R]
  [Algebra R B] [AddCommGroup M] [Module R M] [Module k M] (D : Derivation k R M)
  [AddCommGroup M'] [Module R M'] [Module k M'] [Module.Free R B] [Module.Finite R B]

/-- The trace derivation is compatible with composition of `D` with a linear map. -/
lemma traceDeriv_compDer [IsScalarTower k R M] [IsScalarTower k R M'] (μ : M →ₗ[R] M')
    (a c : B) : traceDeriv (μ.compDer D) a c = μ (traceDeriv D a c) :=
  traceDeriv_map D (μ.compDer D) (Module.Free.chooseBasis R B) (Module.Free.chooseBasis R B)
    (RingHom.id R) (RingHom.id B) (fun _ ↦ rfl) (fun _ ↦ rfl) μ.toAddMonoidHom
    (fun r m ↦ μ.map_smul r m) (fun _ ↦ rfl) a c

end Algebra
