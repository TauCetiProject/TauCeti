/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Etale.Kaehler
public import TauCeti.RingTheory.Derivation.Determinant
public import TauCeti.RingTheory.Kaehler.Trace.Basic

/-!
# The trace of differentials for an extended derivation and base change

Let `k → R → B` be commutative rings with `B` finite free over `R`.

First, let `D : R → R` be a `k`-derivation extending to a `k`-derivation `D' : B → B`. In any
`R`-basis of `B`, applying `D` entrywise to the multiplication matrix of `a ∈ B` produces the
multiplication matrix of `D' a` plus a commutator with the connection matrix of `D'`
(`Derivation.map_leftMulMatrix`). Because left multiplication matrices commute, multiplying by the
matrix of `c ∈ B` and taking the matrix trace kills the commutator term. Hence the differential
trace pairing `Derivation.traceDeriv D a c` equals the algebraic trace `Tr_{B/R}(c * D' a)`, and
`Derivation.traceLin D` factors through the `B`-linear map `Ω[B⁄k] → B` classifying `D'`.

Second, for any `k`-derivation `D : R → M` into an `R`-module `M`, `Derivation.traceLin D` sends a
scalar multiple `b • map η` of a pulled-back Kähler differential `η ∈ Ω[R⁄k]` to
`Tr_{B/R}(b) • D.liftKaehlerDifferential η`. When `B` is formally étale over `R`, the canonical
isomorphism `B ⊗[R] Ω[R⁄k] ≃ₗ[B] Ω[B⁄k]` identifies the Kunz-Lipman differential trace
`Derivation.traceLin (KaehlerDifferential.D k R)` with `Algebra.trace R B` on the first tensor
factor.

## Main results

* `Derivation.traceDeriv_eq_trace_mul`: `traceDeriv D a c = Tr_{B/R}(c * D' a)`.
* `Derivation.liftKaehlerDifferential_traceDerivation_eq_trace_mul`: the lifted trace pairing sends
  `(ω, c)` to `Tr_{B/R}(c * D'.liftKaehlerDifferential ω)`.
* `Derivation.traceLin_eq_trace_liftKaehlerDifferential`: `traceLin D` is `Algebra.trace R B`
  composed with `D'.liftKaehlerDifferential`.
* `Derivation.traceLin_smul_map`: `traceLin D` on `b • map η` is `Tr_{B/R}(b)` times the lift of `D`
  at `η`.
* `Derivation.traceLin_D_tensorKaehlerEquivOfFormallyEtale_tmul`: for `B/R` formally étale, the
  algebraic differential trace sends `b ⊗ η` to `Tr_{B/R}(b) • η`.
-/

public section

open Algebra Matrix TensorProduct

namespace Derivation

section Self

variable {k R : Type*} [CommRing k] [CommRing R] [Algebra k R] (D : Derivation k R R)

/-- For a derivation `D : R → R` into `R` itself, `traceDerivForm D X Y` is the matrix trace of
`X * Y.map D`. -/
lemma traceDerivForm_eq_trace_mul {m n : Type*} [Fintype m] [Fintype n]
    (X : Matrix m n R) (Y : Matrix n m R) :
    traceDerivForm D X Y = (X * Y.map D).trace := by
  simp [traceDerivForm_def, Matrix.trace, Matrix.diag, Matrix.mul_apply]

end Self

section Extension

variable {k R B : Type*} [CommRing k] [CommRing R] [CommRing B] [Algebra k R] [Algebra R B]
  [Algebra k B] [Module.Free R B] [Module.Finite R B]
  (D : Derivation k R R) (D' : Derivation k B B)
  (hD : ∀ r, D' (algebraMap R B r) = algebraMap R B (D r))

include hD in
/-- **The trace derivation for an extended derivation.** If `D'` is a `k`-derivation of a finite
free `R`-algebra `B` extending `D : R → R`, then `traceDeriv D a c = Tr_{B/R}(c * D' a)`. -/
theorem traceDeriv_eq_trace_mul (a c : B) :
    traceDeriv D a c = Algebra.trace R B (c * D' a) := by
  classical
  let b := Module.Free.chooseBasis R B
  set L := Algebra.leftMulMatrix b
  set Γ : Matrix _ _ R := Matrix.of fun p q ↦ b.repr (D' (b q)) p
  have hLA : L c * L a = L a * L c := by rw [← map_mul, ← map_mul, mul_comm]
  have hcomm : (L c * (L a * Γ - Γ * L a)).trace = 0 := by
    rw [mul_sub, Matrix.trace_sub, ← Matrix.mul_assoc, ← Matrix.mul_assoc, hLA,
      Matrix.trace_mul_cycle (L c) Γ (L a), sub_self]
  rw [traceDeriv_def, traceDerivOfBasis_def, traceDerivForm_eq_trace_mul,
    map_leftMulMatrix D D' hD b a, mul_add, Matrix.trace_add, hcomm, add_zero, ← map_mul,
    Algebra.trace_eq_matrix_trace b]

variable [IsScalarTower k R B]

include hD in
/-- For an extended derivation `D'`, the Kähler lift of `traceDerivation D` pairs `(ω, c)` to
`Tr_{B/R}(c * D'.liftKaehlerDifferential ω)`. -/
theorem liftKaehlerDifferential_traceDerivation_eq_trace_mul (ω : Ω[B⁄k]) (c : B) :
    (traceDerivation (B := B) D).liftKaehlerDifferential ω c =
      Algebra.trace R B (c * D'.liftKaehlerDifferential ω) := by
  have hω : ω ∈ (⊤ : Submodule B Ω[B⁄k]) := Submodule.mem_top
  rw [← KaehlerDifferential.span_range_derivation] at hω
  induction hω using Submodule.span_induction generalizing c with
  | mem x hx =>
    obtain ⟨a, rfl⟩ := hx
    simp [traceDeriv_eq_trace_mul D D' hD]
  | zero => simp
  | add x y _ _ hx hy => simp [mul_add, hx, hy]
  | smul a x _ hx =>
    rw [LinearMap.map_smul, LinearMap.map_smul, TauCeti.Algebra.PrecompLinearMap.smul_apply,
      smul_eq_mul, smul_eq_mul, hx (a * c)]
    congr 1
    ring

include hD in
/-- **Factorization of the trace of differentials.** If `D'` extends `D : R → R` along a finite
free extension `B/R`, then `traceLin D` is `Algebra.trace R B` composed with the `B`-linear map
`Ω[B⁄k] → B` induced by `D'`. -/
theorem traceLin_eq_trace_liftKaehlerDifferential :
    traceLin (B := B) D =
      Algebra.trace R B ∘ₗ D'.liftKaehlerDifferential.restrictScalars R :=
  LinearMap.ext fun ω ↦ by
    simpa [traceLin_apply] using liftKaehlerDifferential_traceDerivation_eq_trace_mul D D' hD ω 1

include hD in
/-- Pointwise form of `Derivation.traceLin_eq_trace_liftKaehlerDifferential`. -/
theorem traceLin_apply_eq_trace_liftKaehlerDifferential (ω : Ω[B⁄k]) :
    traceLin (B := B) D ω = Algebra.trace R B (D'.liftKaehlerDifferential ω) :=
  congr($(traceLin_eq_trace_liftKaehlerDifferential D D' hD) ω)

end Extension

section BaseChange

variable {k R B M : Type*} [CommRing k] [CommRing R] [CommRing B] [Algebra k R] [Algebra R B]
  [Algebra k B] [IsScalarTower k R B] [AddCommGroup M] [Module R M] [Module k M]
  [IsScalarTower k R M] [Module.Free R B] [Module.Finite R B] (D : Derivation k R M)

/-- On a scalar multiple of a differential pulled back from `R`, `traceLin D` applies
`Algebra.trace R B` to the scalar factor and `D.liftKaehlerDifferential` to the base form. -/
@[simp]
theorem traceLin_smul_map (b : B) (η : Ω[R⁄k]) :
    traceLin (B := B) D (b • KaehlerDifferential.map k k R B η) =
      Algebra.trace R B b • D.liftKaehlerDifferential η := by
  have hη : η ∈ (⊤ : Submodule R Ω[R⁄k]) := Submodule.mem_top
  rw [← KaehlerDifferential.span_range_derivation] at hη
  induction hη using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨r, rfl⟩ := hx
    rw [KaehlerDifferential.map_D, traceLin_smul_D_algebraMap, liftKaehlerDifferential_comp_D]
  | zero => simp
  | add x y _ _ hx hy => simp [smul_add, hx, hy]
  | smul r x _ hx =>
    rw [LinearMap.map_smul, ← algebraMap_smul B r, ← mul_smul, mul_comm, mul_smul,
      algebraMap_smul B r, LinearMap.map_smul, hx, ← mul_smul, mul_comm, mul_smul,
      ← LinearMap.map_smul]

/-- On pure tensors, `traceLin D` composed with `KaehlerDifferential.mapBaseChange` acts as
`Algebra.trace R B` on the first factor and `D.liftKaehlerDifferential` on the second. -/
theorem traceLin_mapBaseChange_tmul (b : B) (η : Ω[R⁄k]) :
    traceLin (B := B) D (KaehlerDifferential.mapBaseChange k R B (b ⊗ₜ η)) =
      Algebra.trace R B b • D.liftKaehlerDifferential η := by
  rw [KaehlerDifferential.mapBaseChange_tmul, traceLin_smul_map]

/-- For a finite free formally étale `R`-algebra `B`, `traceLin D` sends `b ⊗ η` under
`B ⊗[R] Ω[R⁄k] ≃ Ω[B⁄k]` to `Tr_{B/R}(b)` times `D.liftKaehlerDifferential η`. -/
theorem traceLin_tensorKaehlerEquivOfFormallyEtale_tmul [Algebra.FormallyEtale R B]
    (b : B) (η : Ω[R⁄k]) :
    traceLin (B := B) D (KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale k R B (b ⊗ₜ η)) =
      Algebra.trace R B b • D.liftKaehlerDifferential η := by
  rw [KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale_apply, traceLin_mapBaseChange_tmul]

/-- **Kunz-Lipman differential trace for a finite free formally étale extension.** Under
`B ⊗[R] Ω[R⁄k] ≃ Ω[B⁄k]`, the algebraic Kähler differential trace
`traceLin (KaehlerDifferential.D k R) : Ω[B⁄k] →ₗ[R] Ω[R⁄k]` acts as `Algebra.trace R B` on the
first tensor factor. -/
theorem traceLin_D_tensorKaehlerEquivOfFormallyEtale_tmul [Algebra.FormallyEtale R B]
    (b : B) (η : Ω[R⁄k]) :
    traceLin (B := B) (KaehlerDifferential.D k R)
        (KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale k R B (b ⊗ₜ η)) =
      Algebra.trace R B b • η := by
  rw [traceLin_tensorKaehlerEquivOfFormallyEtale_tmul, Derivation.liftKaehlerDifferential_D,
    LinearMap.id_apply]

end BaseChange

end Derivation
