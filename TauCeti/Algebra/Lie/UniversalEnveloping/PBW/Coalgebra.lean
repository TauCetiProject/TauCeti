/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.UniversalEnveloping.Bialgebra
public import TauCeti.Algebra.Lie.UniversalEnveloping.PBW.Basic
public import TauCeti.LinearAlgebra.TensorProduct.Filtration

/-!
# Comultiplication and the PBW filtration

The coproduct of an element of PBW degree at most `n` has total tensor degree at most `n`.
Here total degree means the sum of the degrees of the two tensor factors, not a separate
bound of `n` on each factor. This is the filtered coalgebra comparison needed when comparing
integral enveloping forms and their Hopf operations with the rational PBW filtration.

`pbwTensorFiltration` is the sum of the images of
`F_i U(L) ⊗ F_j U(L)` for `i + j ≤ n`. It specializes
`TensorProduct.filtration`, which works for arbitrary pairs of submodule filtrations.
No injectivity of the tensor maps is presumed. It is increasing, exhaustive, multiplicative,
and has the scalars in degree zero.
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
  TensorProduct.filtration (pbwFiltration R L) (pbwFiltration R L) n

/-- The tensor PBW filtration is the total tensor filtration of the PBW steps. -/
theorem pbwTensorFiltration_def (n : ℕ) : pbwTensorFiltration R L n =
    TensorProduct.filtration (pbwFiltration R L) (pbwFiltration R L) n := (rfl)

/-- A submodule contains a total tensor step exactly when it contains the pure tensors
whose factor degrees sum to at most that step. -/
theorem pbwTensorFiltration_le_iff {n : ℕ} {P : Submodule R T} :
    pbwTensorFiltration R L n ≤ P ↔
      ∀ i j, i + j ≤ n → ∀ x ∈ pbwFiltration R L i,
        ∀ y ∈ pbwFiltration R L j, x ⊗ₜ[R] y ∈ P := by
  rw [pbwTensorFiltration_def]
  exact TensorProduct.filtration_le_iff _ _

/-- A pure tensor belongs to the step given by the sum of the factor degrees. -/
theorem tmul_mem_pbwTensorFiltration {i j : ℕ} {x y : U}
    (hx : x ∈ pbwFiltration R L i) (hy : y ∈ pbwFiltration R L j) :
    x ⊗ₜ[R] y ∈ pbwTensorFiltration R L (i + j) := by
  rw [pbwTensorFiltration_def]
  exact TensorProduct.tmul_mem_filtration _ _ hx hy

/-- The total tensor PBW filtration is increasing. -/
theorem pbwTensorFiltration_mono : Monotone (pbwTensorFiltration R L) := by
  simp only [pbwTensorFiltration_def, Monotone]
  exact TensorProduct.filtration_mono _ _

/-- Degree zero in the tensor square consists precisely of scalars. -/
@[simp]
theorem pbwTensorFiltration_zero : pbwTensorFiltration R L 0 = 1 := by
  rw [pbwTensorFiltration_def]
  exact TensorProduct.filtration_zero _ _ (pbwFiltration_zero R L) (pbwFiltration_zero R L)

/-- The tensor unit belongs to every total PBW step. -/
theorem one_mem_pbwTensorFiltration (n : ℕ) : (1 : T) ∈ pbwTensorFiltration R L n := by
  rw [pbwTensorFiltration_def]
  exact TensorProduct.one_mem_filtration _ _ n

/-- Multiplication adds total tensor PBW degrees. -/
theorem mul_mem_pbwTensorFiltration {m n : ℕ} {x y : T}
    (hx : x ∈ pbwTensorFiltration R L m) (hy : y ∈ pbwTensorFiltration R L n) :
    x * y ∈ pbwTensorFiltration R L (m + n) := by
  simp only [pbwTensorFiltration_def] at hx hy ⊢
  exact TensorProduct.mul_mem_filtration _ _ hx hy

/-- The product of tensor PBW steps lies in the step of summed degree. -/
theorem pbwTensorFiltration_mul_le (m n : ℕ) :
    pbwTensorFiltration R L m * pbwTensorFiltration R L n ≤
      pbwTensorFiltration R L (m + n) :=
  Submodule.mul_le.2 fun _ hx _ hy => mul_mem_pbwTensorFiltration R L hx hy

/-- The total PBW filtration exhausts the tensor square. -/
theorem iSup_pbwTensorFiltration_eq_top : ⨆ n, pbwTensorFiltration R L n = ⊤ := by
  simp only [pbwTensorFiltration_def]
  exact TensorProduct.iSup_filtration_eq_top _ _ (pbwFiltration_mono R L)
    (pbwFiltration_mono R L) (iSup_pbwFiltration_eq_top R L) (iSup_pbwFiltration_eq_top R L)

/-- Every tensor has finite total PBW degree. -/
theorem exists_mem_pbwTensorFiltration (z : T) :
    ∃ n, z ∈ pbwTensorFiltration R L n := by
  simp only [pbwTensorFiltration_def]
  exact TensorProduct.exists_mem_filtration _ _ (pbwFiltration_mono R L)
    (pbwFiltration_mono R L) (iSup_pbwFiltration_eq_top R L) (iSup_pbwFiltration_eq_top R L) z

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
    | nil =>
      simpa only [List.map_nil, List.prod_nil, map_one, List.length_nil] using
        one_mem_pbwTensorFiltration R L 0
    | cons a l ih =>
      simp only [List.map_cons, List.prod_cons, map_mul, Bialgebra.comulAlgHom_apply,
        List.length_cons] at ih ⊢
      rw [Nat.add_comm l.length 1]
      exact mul_mem_pbwTensorFiltration R L
        (comul_ι_mem_pbwTensorFiltration_one R L a) ih
  rw [Submodule.mem_comap, ← Bialgebra.comulAlgHom_apply]
  exact pbwTensorFiltration_mono R L hl (hword l)

/-- The coproduct of a PBW-degree-`n` element is a sum of pure tensors with total factor
degree at most `n`. This bound is valid over any commutative coefficient ring. -/
theorem comul_mem_pbwTensorFiltration {n : ℕ} {x : U} (hx : x ∈ pbwFiltration R L n) :
    Coalgebra.comul (R := R) x ∈ pbwTensorFiltration R L n :=
  map_comul_pbwFiltration_le R L n ⟨x, hx, rfl⟩

end TauCeti.UniversalEnvelopingAlgebra
