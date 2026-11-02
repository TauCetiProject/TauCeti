/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.UniversalEnveloping.Bialgebra
public import TauCeti.Algebra.Lie.UniversalEnveloping.PBW.Basic

/-!
# Comultiplication and the PBW filtration

The coproduct of an element of PBW degree at most `n` has total tensor degree at most `n`.
Here total degree means the sum of the degrees of the two tensor factors, not a separate
bound of `n` on each factor. This is the filtered coalgebra comparison needed when comparing
integral enveloping forms and their Hopf operations with the rational PBW filtration.

`pbwTensorFiltration` is the sum of the images of
`F_i U(L) ⊗ F_j U(L)` for `i + j ≤ n`. No injectivity of the tensor maps is presumed.
It is increasing, exhaustive, multiplicative, and has the scalars in degree zero.
`comul_mem_pbwTensorFiltration` proves the coproduct bound using the primitive-generator
formula. Neither a basis of the Lie algebra nor a PBW independence theorem is required;
the coefficient ring may have torsion or zero divisors.

## References

* J. E. Humphreys, *Introduction to Lie Algebras and Representation Theory*, §17.
* J. C. Jantzen, *Representations of Algebraic Groups*, II.1.
-/

public section

open scoped TensorProduct

namespace TauCeti.UniversalEnvelopingAlgebra

universe u v

variable (R : Type u) (L : Type v)
variable [CommRing R] [LieRing L] [LieAlgebra R L]

local notation "U" => _root_.UniversalEnvelopingAlgebra R L
local notation "T" => U ⊗[R] U

/-- The total PBW filtration on the tensor square: the sum of the tensor images of the
PBW steps of bidegrees `(i,j)` with `i + j ≤ n`. -/
def pbwTensorFiltration (n : ℕ) : Submodule R T :=
  ⨆ (i : ℕ) (j : ℕ) (_ : i + j ≤ n),
    Submodule.map₂ (TensorProduct.mk R U U) (pbwFiltration R L i) (pbwFiltration R L j)

/-- A submodule contains a total tensor step exactly when it contains the pure tensors
whose factor degrees sum to at most that step. -/
theorem pbwTensorFiltration_le_iff {n : ℕ} {P : Submodule R T} :
    pbwTensorFiltration R L n ≤ P ↔
      ∀ i j, i + j ≤ n → ∀ x ∈ pbwFiltration R L i,
        ∀ y ∈ pbwFiltration R L j, x ⊗ₜ[R] y ∈ P := by
  simp only [pbwTensorFiltration, iSup_le_iff, Submodule.map₂_le,
    TensorProduct.mk_apply]

/-- A pure tensor belongs to the step given by the sum of the factor degrees. -/
theorem tmul_mem_pbwTensorFiltration {i j : ℕ} {x y : U}
    (hx : x ∈ pbwFiltration R L i) (hy : y ∈ pbwFiltration R L j) :
    x ⊗ₜ[R] y ∈ pbwTensorFiltration R L (i + j) :=
  (pbwTensorFiltration_le_iff R L).1 le_rfl i j le_rfl x hx y hy

/-- The total tensor PBW filtration is increasing. -/
theorem pbwTensorFiltration_mono : Monotone (pbwTensorFiltration R L) := by
  intro m n hmn
  refine (pbwTensorFiltration_le_iff R L).2 fun i j hij x hx y hy => ?_
  exact (pbwTensorFiltration_le_iff R L).1 le_rfl i j (hij.trans hmn) x hx y hy

/-- Degree zero in the tensor square consists precisely of scalars. -/
@[simp]
theorem pbwTensorFiltration_zero : pbwTensorFiltration R L 0 = 1 := by
  have hblock : Submodule.map₂ (TensorProduct.mk R U U)
      (pbwFiltration R L 0) (pbwFiltration R L 0) = 1 := by
    simp [Submodule.one_eq_span, Submodule.map₂_span_span, Algebra.TensorProduct.one_def]
  apply le_antisymm
  · refine (pbwTensorFiltration_le_iff R L).2 fun i j hij => ?_
    have hi : i = 0 := by omega
    have hj : j = 0 := by omega
    subst i
    subst j
    exact Submodule.map₂_le.1 hblock.le
  · rw [← hblock]
    exact le_iSup_of_le 0 (le_iSup_of_le 0 (le_iSup_of_le le_rfl le_rfl))

/-- The tensor unit belongs to every total PBW step. -/
theorem one_mem_pbwTensorFiltration (n : ℕ) : (1 : T) ∈ pbwTensorFiltration R L n := by
  simpa only [Algebra.TensorProduct.one_def] using
    (pbwTensorFiltration_le_iff R L).1 le_rfl 0 0 (Nat.zero_le n)
      1 (one_mem_pbwFiltration R L 0) 1 (one_mem_pbwFiltration R L 0)

/-- Multiplication adds total tensor PBW degrees. -/
theorem mul_mem_pbwTensorFiltration {m n : ℕ} {x y : T}
    (hx : x ∈ pbwTensorFiltration R L m) (hy : y ∈ pbwTensorFiltration R L n) :
    x * y ∈ pbwTensorFiltration R L (m + n) := by
  have hleft : pbwTensorFiltration R L m ≤
      (pbwTensorFiltration R L (m + n)).comap ((LinearMap.mul R T).flip y) := by
    refine (pbwTensorFiltration_le_iff R L).2 fun i j hij a ha b hb => ?_
    have hright : pbwTensorFiltration R L n ≤
        (pbwTensorFiltration R L (m + n)).comap (LinearMap.mul R T (a ⊗ₜ[R] b)) := by
      refine (pbwTensorFiltration_le_iff R L).2 fun k l hkl c hc d hd => ?_
      simp only [Submodule.mem_comap, LinearMap.mul_apply', Algebra.TensorProduct.tmul_mul_tmul]
      exact pbwTensorFiltration_mono R L (show (i + k) + (j + l) ≤ m + n by omega)
        (tmul_mem_pbwTensorFiltration R L
          (mul_mem_pbwFiltration R L ha hc) (mul_mem_pbwFiltration R L hb hd))
    exact hright hy
  exact hleft hx

/-- The total PBW filtration exhausts the tensor square. -/
theorem iSup_pbwTensorFiltration_eq_top : ⨆ n, pbwTensorFiltration R L n = ⊤ := by
  apply top_unique
  intro z hz
  clear hz
  induction z using TensorProduct.inductionOn with
  | tmul x y =>
    obtain ⟨i, hi⟩ := exists_mem_pbwFiltration R L x
    obtain ⟨j, hj⟩ := exists_mem_pbwFiltration R L y
    exact Submodule.mem_iSup_of_mem (i + j) (tmul_mem_pbwTensorFiltration R L hi hj)
  | add x y hx hy => exact Submodule.add_mem _ hx hy

/-- Every tensor has finite total PBW degree. -/
theorem exists_mem_pbwTensorFiltration (z : T) :
    ∃ n, z ∈ pbwTensorFiltration R L n := by
  rw [← Submodule.mem_iSup_of_directed _ (pbwTensorFiltration_mono R L).directed_le,
    iSup_pbwTensorFiltration_eq_top]
  exact Submodule.mem_top

private theorem comul_ι_mem_pbwTensorFiltration_one (x : L) :
    Coalgebra.comul (R := R) (_root_.UniversalEnvelopingAlgebra.ι R x) ∈
      pbwTensorFiltration R L 1 := by
  rw [comul_ι R L]
  have hleft := tmul_mem_pbwTensorFiltration R L (i := 1) (j := 0)
    (ι_mem_pbwFiltration_one R L x) (one_mem_pbwFiltration R L 0)
  have hright := tmul_mem_pbwTensorFiltration R L (i := 0) (j := 1)
    (one_mem_pbwFiltration R L 0) (ι_mem_pbwFiltration_one R L x)
  exact (pbwTensorFiltration R L 1).add_mem hleft hright

/-- Comultiplication preserves total PBW degree, as an inclusion of mapped submodules. -/
theorem map_comul_pbwFiltration_le (n : ℕ) :
    (pbwFiltration R L n).map (Coalgebra.comul (R := R)) ≤ pbwTensorFiltration R L n := by
  rw [Submodule.map_le_iff_le_comap, pbwFiltration_le_iff]
  intro l hl
  have hword : ∀ l : List L, (Bialgebra.comulAlgHom R U) ((l.map
      ⇑(_root_.UniversalEnvelopingAlgebra.ι R)).prod) ∈
      pbwTensorFiltration R L l.length := by
    intro l
    induction l with
    | nil => simpa using one_mem_pbwTensorFiltration R L 0
    | cons a l ih =>
      simpa [Nat.add_comm] using mul_mem_pbwTensorFiltration R L
        (comul_ι_mem_pbwTensorFiltration_one R L a) ih
  exact pbwTensorFiltration_mono R L hl (hword l)

/-- The coproduct of a PBW-degree-`n` element is a sum of pure tensors with total factor
degree at most `n`. This bound is valid over any commutative coefficient ring. -/
theorem comul_mem_pbwTensorFiltration {n : ℕ} {x : U} (hx : x ∈ pbwFiltration R L n) :
    Coalgebra.comul (R := R) x ∈ pbwTensorFiltration R L n :=
  map_comul_pbwFiltration_le R L n ⟨x, hx, rfl⟩

end TauCeti.UniversalEnvelopingAlgebra
