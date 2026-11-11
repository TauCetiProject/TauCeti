/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.UniversalEnveloping.Bialgebra
public import TauCeti.Algebra.Lie.UniversalEnveloping.PBW.Basic
public import TauCeti.LinearAlgebra.TensorProduct.Filtration.Basic

/-!
# Comultiplication preserves total PBW degree

The coproduct on a universal enveloping algebra sends PBW degree at most `n` into the
sum of tensor degrees `i + j ≤ n`. This is stronger than bounding each tensor leg by `n`.
It is the filtered-coalgebra compatibility needed when comparing integral enveloping forms
with distributions and their order filtrations. The result holds over any commutative ring,
without freeness or a PBW basis: each canonical Lie generator is primitive, so each factor
in a word contributes degree one to exactly one tensor leg.

## Main results

* `TauCeti.UniversalEnvelopingAlgebra.comul_pbwFiltration_le`: the coproduct image of a PBW
  filtration step lies in the corresponding total tensor filtration step.
* `TauCeti.UniversalEnvelopingAlgebra.comul_mem_tensorFiltration`: the elementwise bound.

## References

* J. E. Humphreys, *Introduction to Lie Algebras and Representation Theory*, §§17 and 26.
* J. C. Jantzen, *Representations of Algebraic Groups*, II.1.
-/

public section

open scoped TensorProduct

namespace TauCeti.UniversalEnvelopingAlgebra

variable (R L : Type*) [CommRing R] [LieRing L] [LieAlgebra R L]

local notation "U" => _root_.UniversalEnvelopingAlgebra R L
local notation "P" => pbwFiltration R L
local notation "T" => tensorFiltration P P

private theorem comul_prod_map_ι_mem_tensorFiltration (l : List L) :
    Coalgebra.comul (R := R) (l.map ⇑(_root_.UniversalEnvelopingAlgebra.ι R)).prod ∈
      T l.length := by
  have hmul := tensorFiltration_mul_le
    (fun i j ↦ (pbwFiltration_mul R L i j).le)
    (fun i j ↦ (pbwFiltration_mul R L i j).le)
  induction l with
  | nil =>
    simpa only [List.map_nil, List.prod_nil, List.length_nil, Bialgebra.comul_one,
      Algebra.TensorProduct.one_def] using
      tmul_mem_tensorFiltration (F := P) (G := P) (by omega : 0 + 0 ≤ 0)
        (one_mem_pbwFiltration R L 0) (one_mem_pbwFiltration R L 0)
  | cons x l ih =>
    have hx : Coalgebra.comul (R := R) (_root_.UniversalEnvelopingAlgebra.ι R x) ∈ T 1 := by
      rw [comul_ι]
      exact (T 1).add_mem
        (tmul_mem_tensorFiltration (by omega : 1 + 0 ≤ 1)
          (ι_mem_pbwFiltration_one R L x) (one_mem_pbwFiltration R L 0))
        (tmul_mem_tensorFiltration (by omega : 0 + 1 ≤ 1)
          (one_mem_pbwFiltration R L 0) (ι_mem_pbwFiltration_one R L x))
    simpa only [List.map_cons, List.prod_cons, List.length_cons, Bialgebra.comul_mul,
      Nat.add_comm 1] using hmul 1 l.length (Submodule.mul_mem_mul hx ih)

/-- The coproduct of PBW degree at most `n` has total tensor degree at most `n`. -/
theorem comul_pbwFiltration_le (n : ℕ) :
    (P n).map (Coalgebra.comul (R := R)) ≤ T n := by
  rw [Submodule.map_le_iff_le_comap, pbwFiltration_le_iff]
  intro l hl
  exact tensorFiltration_mono P P hl (comul_prod_map_ι_mem_tensorFiltration R L l)

/-- An element in PBW degree `n` has coproduct in the sum of tensor degrees `i + j ≤ n`. -/
theorem comul_mem_tensorFiltration {n : ℕ} {x : U} (hx : x ∈ P n) :
    Coalgebra.comul (R := R) x ∈ T n :=
  comul_pbwFiltration_le R L n (Submodule.mem_map_of_mem hx)

end TauCeti.UniversalEnvelopingAlgebra
