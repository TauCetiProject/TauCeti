/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.TypeAHeckeAlgebra.AtomicModel.Block.Basic
public import TauCeti.Algebra.TypeAHeckeAlgebra.AtomicModel.CycleWord.Basic
public import TauCeti.Algebra.TypeAHeckeAlgebra.Cocenter.Basic
import Mathlib.RingTheory.PowerSeries.Inverse

/-!
# Cycle-value determination and order-independence of atomic traces

Since cycle-block words span the cocenter, atomic traces are determined by their cycle values
(`TauCeti.TypeAHeckeAlgebra.atomicTrace_eq_of_cycleWord`) and, when `q ^ 2 - 1` is left-regular,
do not depend on the linear order of the alphabet
(`TauCeti.TypeAHeckeAlgebra.atomicTrace_eq_of_equiv`). Cf. Neretin (arXiv:2101.02133,
§§1.6–1.7, §3.1).
-/

public section

namespace TauCeti.TypeAHeckeAlgebra

variable {R : Type*} [CommRing R] {ι : Type*} [LinearOrder ι] [Finite ι] (pos : ι → Prop)
  [DecidablePred pos] (q : Rˣ) (p : ι → R)

/-- **Atomic traces are determined by their cycle values.** Two atomic traces agreeing on every
cycle word `ζₘ` agree on every finite Hecke algebra. -/
theorem atomicTrace_eq_of_cycleWord {ι' : Type*} [LinearOrder ι'] [Finite ι'] (pos' : ι' → Prop)
    [DecidablePred pos'] (p' : ι' → R)
    (h : ∀ m, atomicTrace pos q p m (cycleWord q m) = atomicTrace pos' q p' m (cycleWord q m))
    (n : ℕ) : atomicTrace pos q p n = atomicTrace pos' q p' n :=
  trace_eq_of_cycleWord_values (fun _ ↦ atomicTrace_mul_comm pos q p) (fun _ ↦
    atomicTrace_mul_comm pos' q p') (fun _ _ ↦ atomicTrace_castAdd_mul_natAdd pos q p) (fun _ _ ↦
      atomicTrace_castAdd_mul_natAdd pos' q p') h n

open PowerSeries in
/-- **Order-independence of atomic traces.** If `q ^ 2 - 1` is left-regular, any sign- and
weight-preserving bijection preserves the atomic trace on every finite Hecke algebra. -/
theorem atomicTrace_eq_of_equiv {ι' : Type*} [LinearOrder ι'] [Finite ι'] (pos' : ι' → Prop)
    [DecidablePred pos'] (p' : ι' → R) (hq : IsLeftRegular ((q : R) ^ 2 - 1)) (e : ι ≃ ι')
    (hpos : ∀ a, pos' (e a) ↔ pos a) (hp : ∀ a, p' (e a) = p a) (n : ℕ) :
    atomicTrace pos q p n = atomicTrace pos' q p' n := by
  have := Fintype.ofFinite ι; have := Fintype.ofFinite ι'
  refine atomicTrace_eq_of_cycleWord pos q p pos' p' (fun m ↦ ?_) n
  have hcongr (c₁ c₂ : R) : ∏ a, (cycleGeneratingFactor pos p c₁ c₂ a : PowerSeries R) =
      ∏ a, (cycleGeneratingFactor pos' p' c₁ c₂ a : PowerSeries R) :=
    Fintype.prod_equiv e _ _ fun a ↦ by simp only [coe_cycleGeneratingFactor, hpos, hp]
  have hseries := (isUnit_prod_cycleGeneratingFactor pos p ((q : R) ^ 2) 1).mul_left_injective ((
    atomicTrace_cycleWord_generating_function_eq_prod pos q p).trans ((hcongr 1 _).trans ((
      atomicTrace_cycleWord_generating_function_eq_prod pos' q p').symm.trans (congrArg _
        (hcongr _ 1).symm))))
  rcases m with _ | m <;> [simp; exact hq (by simpa using congrArg (coeff (m + 1)) hseries)]

end TauCeti.TypeAHeckeAlgebra
