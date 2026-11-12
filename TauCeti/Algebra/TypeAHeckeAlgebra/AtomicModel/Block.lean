/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.TypeAHeckeAlgebra.AtomicModel.CycleWord
public import TauCeti.Algebra.TypeAHeckeAlgebra.Cocenter.Basic
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.RingTheory.PowerSeries.Inverse

/-!
# Atomic traces are multiplicative on disjoint blocks of strands

Let `ι` be a finite linearly ordered alphabet of positive and negative letters with weights
`p : ι → R`, and let `atomicTrace pos q p n` be the atomic trace `x ↦ tr (ρ(x) * D)` on the Hecke
algebra on `n` strands, where `ρ` is the signed checked representation on the word space
`(Fin n → ι) →₀ R` and `D` is the product density of the weights.

A word on `a + b` strands is a word `u` on the first `a` strands followed by a word `v` on the last
`b` strands (`Fin.append u v`). An element `x` of the Hecke algebra on `a` strands, placed on the
first block by the left block map `TauCeti.TypeAHeckeAlgebra.castAdd`, acts on `u` and leaves `v`
alone; an element `y` on the last block, placed there by the right block map
`TauCeti.TypeAHeckeAlgebra.natAdd`, acts on `v` and leaves `u` alone. Hence the diagonal
coefficient of `castAdd x * natAdd y` at `Fin.append u v` is the product of the diagonal
coefficients of `x` at `u` and of `y` at `v`, and the product density splits in the same way.
Summing over words gives **separated-block multiplicativity**
(`TauCeti.TypeAHeckeAlgebra.atomicTrace_castAdd_mul_natAdd`):

`atomicTrace (a + b) (castAdd x * natAdd y) = atomicTrace a x * atomicTrace b y`.

No normalization of the weights and no Markov condition are needed.

Since the cycle-block words span the cocenter of each Hecke algebra, a tracial family of
functionals which is multiplicative on disjoint blocks is determined by its values on the cycle
words `ζₘ` (`TauCeti.TypeAHeckeAlgebra.trace_eq_of_cycleWord_values`). So an atomic trace is
identified on every finite Hecke algebra by its cycle values
(`TauCeti.TypeAHeckeAlgebra.atomicTrace_eq_of_cycleWord`). These cycle values are in turn fixed
by the cycle-trace generating identity
(`TauCeti.TypeAHeckeAlgebra.atomicTrace_cycleWord_generating_function`) whenever `q ^ 2 - 1`
is not a zero divisor. As that identity only involves the weights of the positive and of the
negative letters, the atomic trace then does not depend on the linear order of the alphabet,
although the signed checked representation does
(`TauCeti.TypeAHeckeAlgebra.atomicTrace_eq_of_equiv`).

## Main results

* `TauCeti.TypeAHeckeAlgebra.signedChecked_castAdd_mapDomain_append` and
  `TauCeti.TypeAHeckeAlgebra.signedChecked_natAdd_mapDomain_append`: the block maps act on the
  corresponding block of letters.
* `TauCeti.TypeAHeckeAlgebra.atomicTrace_castAdd_mul_natAdd`: separated-block multiplicativity.
* `TauCeti.TypeAHeckeAlgebra.atomicTrace_eq_of_cycleWord`: two atomic traces with the same cycle
  values agree on every finite Hecke algebra.
* `TauCeti.TypeAHeckeAlgebra.atomicTrace_eq_of_equiv`: if `q ^ 2 - 1` is not a zero divisor,
  the atomic trace only depends on the signed weights of the letters, not on their order.

## References

* Yu. A. Neretin, *Some remarks on traces on the infinite-dimensional Iwahori–Hecke algebra*,
  arXiv:2101.02133, §§1.6–1.7 and §3.1, for the signed product model.
-/

public section

open Function Finsupp

namespace TauCeti.TypeAHeckeAlgebra

variable {R : Type*} [CommRing R] {ι : Type*} [LinearOrder ι] (pos : ι → Prop) [DecidablePred pos]
  (q : Rˣ) {a b : ℕ}

/-- An element placed on the first `a` of `a + b` strands acts on the first `a` letters of a word,
holding the last `b` letters fixed. -/
@[simp]
theorem signedChecked_castAdd_mapDomain_append (x : TypeAHeckeAlgebra R q a) (v : Fin b → ι)
    (w : (Fin a → ι) →₀ R) :
    signedChecked pos q (castAdd R q a b x) (mapDomain (fun u ↦ Fin.append u v) w) =
      mapDomain (fun u ↦ Fin.append u v) (signedChecked pos q x w) := by
  set L := lmapDomain R R (fun u : Fin a → ι ↦ Fin.append u v)
  suffices h : (signedChecked pos q (castAdd R q a b x)).comp L = L.comp (signedChecked pos q x)
    by simpa [L] using LinearMap.congr_fun h w
  refine signedChecked_comp_eq_of_forall_T pos q _ L (fun i ↦ ?_) x
  have hj : BraidGroup.strand (Fin.castLE (by omega) i : Fin (a + b - 1)) =
      Fin.castAdd b (BraidGroup.strand i) := Fin.ext (by simp)
  have hk : BraidGroup.strandSucc (Fin.castLE (by omega) i : Fin (a + b - 1)) =
      Fin.castAdd b (BraidGroup.strandSucc i) := Fin.ext (by simp)
  rw [castAdd_T, signedChecked_T, signedChecked_T, LinearMap.smul_comp, LinearMap.comp_smul,
    hj, hk, signedCheckedR_castAdd_comp_lmapDomain_append]

/-- An element placed on the last `b` of `a + b` strands acts on the last `b` letters of a word,
holding the first `a` letters fixed. -/
@[simp]
theorem signedChecked_natAdd_mapDomain_append (y : TypeAHeckeAlgebra R q b) (u : Fin a → ι)
    (w : (Fin b → ι) →₀ R) :
    signedChecked pos q (natAdd R q a b y) (mapDomain (fun v ↦ Fin.append u v) w) =
      mapDomain (fun v ↦ Fin.append u v) (signedChecked pos q y w) := by
  set L := lmapDomain R R (fun v : Fin b → ι ↦ Fin.append u v)
  suffices h : (signedChecked pos q (natAdd R q a b y)).comp L = L.comp (signedChecked pos q y)
    by simpa [L] using LinearMap.congr_fun h w
  refine signedChecked_comp_eq_of_forall_T pos q _ L (fun j ↦ ?_) y
  have hj : BraidGroup.strand (⟨a + j, by omega⟩ : Fin (a + b - 1)) =
      Fin.natAdd a (BraidGroup.strand j) := Fin.ext (by simp)
  have hk : BraidGroup.strandSucc (⟨a + j, by omega⟩ : Fin (a + b - 1)) =
      Fin.natAdd a (BraidGroup.strandSucc j) := Fin.ext (by simp [Nat.add_assoc])
  rw [natAdd_T, signedChecked_T, signedChecked_T, LinearMap.smul_comp, LinearMap.comp_smul,
    hj, hk, signedCheckedR_natAdd_comp_lmapDomain_append]

/-- The coefficient at `Fin.append u v` of the image of a word `Fin.append u v'` under an element
placed on the first block vanishes unless `v' = v`, and is then the coefficient of the action on
the first block. -/
private theorem signedChecked_castAdd_single_append_apply (x : TypeAHeckeAlgebra R q a)
    (u : Fin a → ι) (v v' : Fin b → ι) (r : R) :
    signedChecked pos q (castAdd R q a b x) (single (Fin.append u v') r) (Fin.append u v) =
      single v' r v * signedChecked pos q x (single u 1) u := by
  have hinj : Injective fun u' : Fin a → ι ↦ Fin.append u' v' := fun u₁ u₂ h ↦
    funext fun i ↦ by simpa using congrFun h (Fin.castAdd b i)
  rw [← mapDomain_single (f := fun u' ↦ Fin.append u' v'),
    signedChecked_castAdd_mapDomain_append, ← smul_single_one, map_smul, mapDomain_smul,
    Finsupp.smul_apply, smul_eq_mul]
  by_cases hv : v' = v
  · subst hv
    rw [single_eq_same]
    exact congrArg _ (mapDomain_apply_of_injective hinj _ u)
  · rw [mapDomain_of_notMem_range]
    · simp [hv]
    rintro ⟨u', hu'⟩
    exact hv (funext fun j ↦ by simpa using congrFun hu' (Fin.natAdd a j))

/-- **Diagonal coefficients split along disjoint blocks.** The diagonal coefficient of
`castAdd x * natAdd y` at the word `Fin.append u v` is the product of the diagonal coefficients of
`x` at `u` and of `y` at `v`. -/
theorem signedChecked_castAdd_mul_natAdd_single_append_apply (x : TypeAHeckeAlgebra R q a)
    (y : TypeAHeckeAlgebra R q b) (u : Fin a → ι) (v : Fin b → ι) :
    signedChecked pos q (castAdd R q a b x * natAdd R q a b y) (single (Fin.append u v) 1)
        (Fin.append u v) =
      signedChecked pos q x (single u 1) u * signedChecked pos q y (single v 1) v := by
  rw [map_mul, mul_apply_eq_comp, ← mapDomain_single (f := fun v' ↦ Fin.append u v'),
    signedChecked_natAdd_mapDomain_append, mul_comm]
  generalize signedChecked pos q y (single v 1) = g
  induction g using Finsupp.induction_linear with
  | zero => simp
  | add g g' hg hg' =>
    rw [mapDomain_add, map_add, Finsupp.add_apply, hg, hg', Finsupp.add_apply, add_mul]
  | single v' r => rw [mapDomain_single, signedChecked_castAdd_single_append_apply]

variable [Finite ι] (p : ι → R)

/-- **Separated-block multiplicativity of the atomic trace.** The atomic trace of an element `x` on
the first `a` strands times an element `y` on the last `b` strands is the product of the atomic
traces of `x` and `y`. -/
theorem atomicTrace_castAdd_mul_natAdd (x : TypeAHeckeAlgebra R q a)
    (y : TypeAHeckeAlgebra R q b) :
    atomicTrace pos q p (a + b) (castAdd R q a b x * natAdd R q a b y) =
      atomicTrace pos q p a x * atomicTrace pos q p b y := by
  have := Fintype.ofFinite ι
  have he (u : Fin a → ι) (v : Fin b → ι) : Fin.appendEquiv a b (u, v) = Fin.append u v := by
    ext
    simp
  rw [atomicTrace_eq_sum, ← (Fin.appendEquiv a b).sum_comp, atomicTrace_eq_sum,
    atomicTrace_eq_sum, Finset.sum_mul_sum, ← Finset.univ_product_univ, Finset.sum_product]
  refine Finset.sum_congr rfl fun u _ ↦ Finset.sum_congr rfl fun v _ ↦ ?_
  rw [he, signedChecked_castAdd_mul_natAdd_single_append_apply,
    Fin.prod_univ_add]
  simp only [Fin.append_left, Fin.append_right]
  ring

/-- **Atomic traces are determined by their cycle values.** Two atomic traces, on possibly
different signed alphabets with possibly different weights, which agree on every cycle word `ζₘ`
agree on the Hecke algebra on any number of strands. -/
theorem atomicTrace_eq_of_cycleWord {ι' : Type*} [LinearOrder ι'] [Finite ι'] (pos' : ι' → Prop)
    [DecidablePred pos'] (p' : ι' → R)
    (h : ∀ m, atomicTrace pos q p m (cycleWord q m) = atomicTrace pos' q p' m (cycleWord q m))
    (n : ℕ) : atomicTrace pos q p n = atomicTrace pos' q p' n :=
  trace_eq_of_cycleWord_values (fun _ ↦ atomicTrace_mul_comm pos q p)
    (fun _ ↦ atomicTrace_mul_comm pos' q p') (fun _ _ ↦ atomicTrace_castAdd_mul_natAdd pos q p)
    (fun _ _ ↦ atomicTrace_castAdd_mul_natAdd pos' q p') h n

open PowerSeries in
/-- **The atomic trace does not depend on the order of the alphabet.** If `q ^ 2 - 1` is not a
zero divisor, two atomic traces whose alphabets correspond by a bijection `e`, not necessarily
monotone, preserving the signs and the weights of the letters, agree on the Hecke algebra on any
number of strands. -/
theorem atomicTrace_eq_of_equiv {ι' : Type*} [LinearOrder ι'] [Finite ι'] (pos' : ι' → Prop)
    [DecidablePred pos'] (p' : ι' → R) (hq : IsLeftRegular ((q : R) ^ 2 - 1)) (e : ι ≃ ι')
    (hpos : ∀ a, pos' (e a) ↔ pos a) (hp : ∀ a, p' (e a) = p a) (n : ℕ) :
    atomicTrace pos q p n = atomicTrace pos' q p' n := by
  have := Fintype.ofFinite ι
  have := Fintype.ofFinite ι'
  refine atomicTrace_eq_of_cycleWord pos q p pos' p' (fun m ↦ ?_) n
  -- Both generating series satisfy the same identity, with the same numerator and the same
  -- denominator, which is a unit.
  have hN := Fintype.prod_equiv e
    (fun a ↦ if pos a then 1 - C (p a) * X else 1 + C ((q : R) ^ 2 * p a) * X)
    (fun a ↦ if pos' a then 1 - C (p' a) * X else 1 + C ((q : R) ^ 2 * p' a) * X)
    fun a ↦ by simp only [hpos, hp]
  have hD := Fintype.prod_equiv e
    (fun a ↦ if pos a then 1 - C ((q : R) ^ 2 * p a) * X else 1 + C (p a) * X)
    (fun a ↦ if pos' a then 1 - C ((q : R) ^ 2 * p' a) * X else 1 + C (p' a) * X)
    fun a ↦ by simp only [hpos, hp]
  have hunit : IsUnit (∏ a, if pos a then 1 - C ((q : R) ^ 2 * p a) * X else 1 + C (p a) * X) :=
    isUnit_iff_constantCoeff.2 (by simp [map_prod, apply_ite])
  have hseries := hunit.mul_left_injective
    ((atomicTrace_cycleWord_generating_function pos q p).trans
      (hN.trans ((atomicTrace_cycleWord_generating_function pos' q p').symm.trans
        (congrArg _ hD.symm))))
  rcases m with _ | m
  · simp
  · have hcoeff := congrArg (coeff (m + 1)) hseries
    simp only [coeff_mk, Nat.add_one_ne_zero, ↓reduceIte] at hcoeff
    exact hq hcoeff

end TauCeti.TypeAHeckeAlgebra
