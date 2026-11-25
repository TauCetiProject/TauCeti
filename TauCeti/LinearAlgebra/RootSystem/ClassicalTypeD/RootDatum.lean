/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.RootSystem.Base
public import TauCeti.LinearAlgebra.Matrix.NormTwoShell.RootPairing
public import TauCeti.LinearAlgebra.RootSystem.ClassicalTypeD.Basic
public import TauCeti.LinearAlgebra.RootSystem.SimplyConnectedRootDatum.Basic
import TauCeti.Algebra.Group.Submonoid.Closure
import TauCeti.LinearAlgebra.Matrix.Dual

/-!
# The classical root datum of type `Dₙ` on `ℤⁿ`

The vectors `±e_a ± e_b` (`a ≠ b`) of `ℤⁿ`, the integral vectors of squared length two
(`TauCeti.DynkinType.TypeDRoot`), form a root datum on `ℤⁿ × ℤⁿ` paired by the dot product, each
root being its own coroot. It is the root datum of the split special orthogonal group `SO_{2n}`
relative to its diagonal torus `diag(t₁, …, tₙ, tₙ⁻¹, …, t₁⁻¹)`. It is defined for every `n`: it
has no roots for `n ≤ 1`, it is of type `A₁ × A₁` for `n = 2` and of type `A₃` for `n = 3`.
It is the root pairing of the norm-two shell (`Matrix.PosDef.normTwoShellRootPairing`) of the
identity matrix over `ℤ`, reindexed by `TauCeti.DynkinType.TypeDRoot`.

For `2 ≤ n` the Bourbaki simple roots `e_i - e_{i+1}` and `e_{n-2} + e_{n-1}` form a base: a
positive root `e_a - e_b` (`a < b`) is the sum of the chain roots between `a` and `b`, and a
positive root `e_a + e_b` is `(e_a - e_{n-2}) + (e_b - e_{n-1}) + (e_{n-2} + e_{n-1})`. For `4 ≤ n`
these simple roots are `TauCeti.DynkinType.typeDSimpleRoot`; for `n = 2` and `n = 3` they give the
bases of types `A₁ × A₁` and `A₃`.

## Main declarations

* `TauCeti.DynkinType.typeDClassicalRootDatum`: the root datum.
* `TauCeti.DynkinType.flip_typeDClassicalRootDatum`: it is its own dual.
* `TauCeti.DynkinType.typeDClassicalBase`: the Bourbaki base for `2 ≤ n`.

## References

* N. Bourbaki, *Lie Groups and Lie Algebras, Chapters 4--6*, Plate IV.
* J. E. Humphreys, *Linear Algebraic Groups* (1975), §27.
-/

public section

open Function Set Matrix

namespace TauCeti.DynkinType

variable (n : ℕ)

/-- The integral vectors of squared length two are the norm-two shell of the identity matrix. -/
private def normTwoShellOneEquiv : (1 : Matrix (Fin n) (Fin n) ℤ).normTwoShell ≃ TypeDRoot n :=
  Equiv.subtypeEquivRight fun x => by rw [mem_normTwoShell, one_mulVec]

/-- **The classical root datum of type `Dₙ`**: the roots and coroots are the integral vectors
`±e_a ± e_b` of squared length two in `ℤⁿ`, paired by the dot product. It is the root datum of
`SO_{2n}` with its diagonal torus, defined as the root pairing of the norm-two shell of the identity
matrix. -/
noncomputable def typeDClassicalRootDatum : RootDatum (TypeDRoot n) (Fin n → ℤ) (Fin n → ℤ) :=
  (PosDef.one.normTwoShellRootPairing ℤ).map (normTwoShellOneEquiv n) (LinearEquiv.refl ℤ _)
    (LinearEquiv.refl ℤ _)

variable {n}

@[simp]
theorem typeDClassicalRootDatum_root (x : TypeDRoot n) :
    (typeDClassicalRootDatum n).root x = x.val := by
  simp [typeDClassicalRootDatum, RootPairing.map, normTwoShellOneEquiv]

@[simp]
theorem typeDClassicalRootDatum_coroot (x : TypeDRoot n) :
    (typeDClassicalRootDatum n).coroot x = x.val := by
  simp [typeDClassicalRootDatum, RootPairing.map, normTwoShellOneEquiv]

@[simp]
theorem typeDClassicalRootDatum_toLinearMap_apply (x y : Fin n → ℤ) :
    (typeDClassicalRootDatum n).toLinearMap x y = x ⬝ᵥ y := by
  simp [typeDClassicalRootDatum, RootPairing.map]

/-- The Cartan integers of the classical root datum of type `Dₙ` are dot products. -/
@[simp]
theorem typeDClassicalRootDatum_pairing (x y : TypeDRoot n) :
    (typeDClassicalRootDatum n).pairing x y = x.val ⬝ᵥ y.val := by
  rw [← RootPairing.root_coroot_eq_pairing, typeDClassicalRootDatum_toLinearMap_apply,
    typeDClassicalRootDatum_root, typeDClassicalRootDatum_coroot]

/-- **The classical root datum of type `Dₙ` is its own dual.** -/
theorem flip_typeDClassicalRootDatum :
    (typeDClassicalRootDatum n).flip = typeDClassicalRootDatum n := by
  apply RootPairing.ext
  · refine LinearMap.ext fun x => LinearMap.ext fun y => ?_
    rw [RootPairing.flip_toLinearMap, LinearMap.flip_apply,
      typeDClassicalRootDatum_toLinearMap_apply, typeDClassicalRootDatum_toLinearMap_apply,
      dotProduct_comm]
  · ext x : 1
    rw [RootPairing.flip_root, typeDClassicalRootDatum_coroot, typeDClassicalRootDatum_root]
  · exact congrArg Set.range (funext fun x => by
      rw [RootPairing.flip_coroot, typeDClassicalRootDatum_root, typeDClassicalRootDatum_coroot])

/-! ### The Bourbaki base -/

section Base

variable (hn : 2 ≤ n)

/-- The roots of the classical root datum of type `Dₙ`, as a function. -/
private theorem coe_typeDClassicalRootDatum_root :
    ⇑(typeDClassicalRootDatum n).root = Subtype.val :=
  funext typeDClassicalRootDatum_root

/-- The coroots of the classical root datum of type `Dₙ`, as a function, are the roots. -/
private theorem coe_typeDClassicalRootDatum_coroot :
    ⇑(typeDClassicalRootDatum n).coroot = Subtype.val :=
  funext typeDClassicalRootDatum_coroot

/-- The `i`-th Bourbaki simple root of type `Dₙ`, for `2 ≤ n`: the chain roots `e_i - e_{i+1}`
for the `Fin`-indices `i < n - 1` and the fork root `e_{n-2} + e_{n-1}` for `i = n - 1`. For
`4 ≤ n` it is `TauCeti.DynkinType.typeDSimpleRoot`
(`TauCeti.DynkinType.typeDClassicalSimpleRoot_eq_typeDSimpleRoot`); for `n = 2` the two simple
roots `e₀ - e₁`, `e₀ + e₁` are orthogonal (type `A₁ × A₁`) and for `n = 3` the simple roots
`e₀ - e₁`, `e₁ - e₂`, `e₁ + e₂` form a chain (type `A₃`). -/
def typeDClassicalSimpleRoot (i : Fin n) : Fin n → ℤ :=
  if h : (i : ℕ) + 1 < n then
    Pi.single i 1 - Pi.single ⟨(i : ℕ) + 1, h⟩ 1
  else
    Pi.single ⟨n - 2, by omega⟩ 1 + Pi.single ⟨n - 1, by omega⟩ 1

/-- The chain simple roots `e_i - e_{i+1}`. -/
@[simp] theorem typeDClassicalSimpleRoot_of_add_one_lt {i : Fin n} (hi : (i : ℕ) + 1 < n) :
    typeDClassicalSimpleRoot hn i = Pi.single i 1 - Pi.single ⟨(i : ℕ) + 1, hi⟩ 1 :=
  dite_eq_left hi

/-- The fork simple root `e_{n-2} + e_{n-1}`. -/
@[simp] theorem typeDClassicalSimpleRoot_of_not_add_one_lt {i : Fin n}
    (hi : ¬(i : ℕ) + 1 < n) :
    typeDClassicalSimpleRoot hn i =
      Pi.single ⟨n - 2, by omega⟩ 1 + Pi.single ⟨n - 1, by omega⟩ 1 :=
  dite_eq_right hi

/-- For `4 ≤ n` the simple roots are those of `TauCeti.DynkinType.typeDSimpleRoot`. -/
theorem typeDClassicalSimpleRoot_eq_typeDSimpleRoot (hn : 4 ≤ n) :
    typeDClassicalSimpleRoot (n := n) (by omega) = typeDSimpleRoot n hn := by
  ext i : 1
  by_cases hi : (i : ℕ) + 1 < n
  · rw [typeDClassicalSimpleRoot_of_add_one_lt _ hi, typeDSimpleRoot_of_add_one_lt hn hi]
  · rw [typeDClassicalSimpleRoot_of_not_add_one_lt _ hi, typeDSimpleRoot_of_not_add_one_lt hn hi]

/-- The simple roots have squared length two. -/
theorem typeDClassicalSimpleRoot_dotProduct_self (i : Fin n) :
    typeDClassicalSimpleRoot hn i ⬝ᵥ typeDClassicalSimpleRoot hn i = 2 := by
  by_cases hi : (i : ℕ) + 1 < n
  · rw [typeDClassicalSimpleRoot_of_add_one_lt hn hi]
    simp [dotProduct_sub, Fin.ext_iff]
  · rw [typeDClassicalSimpleRoot_of_not_add_one_lt hn hi]
    simp [dotProduct_add, Pi.single_apply, Fin.ext_iff]
    omega

/-- Twice the `k`-th fundamental coweight of type `Dₙ`, in classical orthogonal coordinates. -/
private def doubleCoweight (k : Fin n) : Fin n → ℤ := fun j =>
  if (k : ℕ) + 2 < n then (if (j : ℕ) ≤ (k : ℕ) then 2 else 0)
  else if (k : ℕ) + 1 < n then (if (j : ℕ) + 1 = n then -1 else 1)
  else 1

/-- The doubled fundamental coweights are dual to the simple roots, up to the factor two. -/
private theorem typeDClassicalSimpleRoot_dotProduct_doubleCoweight (i k : Fin n) :
    typeDClassicalSimpleRoot hn i ⬝ᵥ doubleCoweight k = if (i : ℕ) = k then 2 else 0 := by
  by_cases hi : (i : ℕ) + 1 < n
  · rw [typeDClassicalSimpleRoot_of_add_one_lt hn hi, sub_dotProduct, single_dotProduct,
      single_dotProduct]
    simp only [doubleCoweight, one_mul]
    split_ifs <;> omega
  · rw [typeDClassicalSimpleRoot_of_not_add_one_lt hn hi, add_dotProduct, single_dotProduct,
      single_dotProduct]
    simp only [doubleCoweight, one_mul]
    split_ifs <;> omega

/-- **The Bourbaki simple roots of type `Dₙ` are linearly independent**, for `2 ≤ n`. -/
theorem linearIndependent_typeDClassicalSimpleRoot :
    LinearIndependent ℤ (typeDClassicalSimpleRoot hn) :=
  linearIndependent_of_dotProduct_diagonal (c := fun _ => 2) (w := doubleCoweight)
    (fun _ => (IsRegular.of_ne_zero (by norm_num)).right)
    (fun i => by rw [typeDClassicalSimpleRoot_dotProduct_doubleCoweight, ite_eq_left rfl])
    (fun i j hij => by
      rw [typeDClassicalSimpleRoot_dotProduct_doubleCoweight, ite_eq_right (mt Fin.ext hij)])

/-- A difference `e_a - e_b` with `a ≤ b` is a sum of chain simple roots. -/
private theorem single_sub_single_mem_closure {a b : Fin n} (hab : a ≤ b) :
    Pi.single a 1 - Pi.single b 1 ∈
      AddSubmonoid.closure (range (typeDClassicalSimpleRoot hn)) := by
  obtain ⟨b, hb⟩ := b
  induction b with
  | zero =>
    obtain rfl : a = ⟨0, hb⟩ := Fin.ext (by simp [Fin.le_def] at hab; omega)
    simp
  | succ b ih =>
    by_cases hab' : a = ⟨b + 1, hb⟩
    · subst hab'
      simp
    have hab'' : a ≤ ⟨b, by omega⟩ := by
      rw [Fin.le_def] at hab ⊢
      exact Nat.le_of_lt_succ (lt_of_le_of_ne hab fun h => hab' (Fin.ext h))
    have hstep : typeDClassicalSimpleRoot hn ⟨b, by omega⟩ =
        Pi.single ⟨b, by omega⟩ 1 - Pi.single ⟨b + 1, hb⟩ 1 :=
      typeDClassicalSimpleRoot_of_add_one_lt hn (i := ⟨b, by omega⟩) hb
    have h := add_mem (ih (by omega) hab'')
      (AddSubmonoid.subset_closure (mem_range_self (⟨b, by omega⟩ : Fin n)))
    rw [hstep] at h
    simpa using h

/-- A sum `e_a + e_b` with `a < b` is `(e_a - e_{n-2}) + (e_b - e_{n-1}) + (e_{n-2} + e_{n-1})`,
a sum of simple roots. -/
private theorem single_add_single_mem_closure {a b : Fin n} (hab : a < b) :
    Pi.single a 1 + Pi.single b 1 ∈
      AddSubmonoid.closure (range (typeDClassicalSimpleRoot hn)) := by
  have hfork : typeDClassicalSimpleRoot hn ⟨n - 1, by omega⟩ =
      Pi.single ⟨n - 2, by omega⟩ 1 + Pi.single ⟨n - 1, by omega⟩ 1 :=
    typeDClassicalSimpleRoot_of_not_add_one_lt hn (by simp; omega)
  have h := add_mem (add_mem
    (single_sub_single_mem_closure hn (a := a) (b := ⟨n - 2, by omega⟩)
      (by rw [Fin.le_def]; rw [Fin.lt_def] at hab; simp; omega))
    (single_sub_single_mem_closure hn (a := b) (b := ⟨n - 1, by omega⟩)
      (by rw [Fin.le_def]; simp; omega)))
    (AddSubmonoid.subset_closure (mem_range_self (⟨n - 1, by omega⟩ : Fin n)))
  rw [hfork] at h
  convert h using 1
  abel

/-- Every root of type `Dₙ` or its negative is a sum of simple roots. -/
private theorem mem_or_neg_mem_closure (x : TypeDRoot n) :
    x.val ∈ AddSubmonoid.closure (range (typeDClassicalSimpleRoot hn)) ∨
      -x.val ∈ AddSubmonoid.closure (range (typeDClassicalSimpleRoot hn)) := by
  obtain ⟨i, j, hij, hx | hx | hx⟩ := x.exists_eq_single_sub_or_add_or_neg_add
  · rcases lt_or_gt_of_ne hij with h | h
    · exact Or.inl (hx ▸ single_sub_single_mem_closure hn h.le)
    · exact Or.inr (by rw [hx, neg_sub]; exact single_sub_single_mem_closure hn h.le)
  · rcases lt_or_gt_of_ne hij with h | h
    · exact Or.inl (hx ▸ single_add_single_mem_closure hn h)
    · exact Or.inl (by rw [hx, add_comm]; exact single_add_single_mem_closure hn h)
  · rcases lt_or_gt_of_ne hij with h | h
    · exact Or.inr (by rw [hx, neg_neg]; exact single_add_single_mem_closure hn h)
    · exact Or.inr (by rw [hx, neg_neg, add_comm]; exact single_add_single_mem_closure hn h)

/-- The `i`-th Bourbaki simple root of type `Dₙ`, as a root. -/
def typeDClassicalSimpleIndex (i : Fin n) : TypeDRoot n :=
  ⟨typeDClassicalSimpleRoot hn i, typeDClassicalSimpleRoot_dotProduct_self hn i⟩

@[simp]
theorem typeDClassicalSimpleIndex_val (i : Fin n) :
    (typeDClassicalSimpleIndex hn i).val = typeDClassicalSimpleRoot hn i :=
  (rfl)

theorem typeDClassicalSimpleIndex_injective : Injective (typeDClassicalSimpleIndex hn) :=
  fun _ _ h => (linearIndependent_typeDClassicalSimpleRoot hn).injective (congrArg Subtype.val h)

/-- **The Bourbaki base of the classical root datum of type `Dₙ`**, for `2 ≤ n`: the simple roots
`e_i - e_{i+1}` and `e_{n-2} + e_{n-1}`. -/
noncomputable def typeDClassicalBase : (typeDClassicalRootDatum n).Base where
  support := simpleSupport (typeDClassicalSimpleIndex_injective hn)
  linearIndepOn_root := by
    rw [coe_typeDClassicalRootDatum_root]
    exact linearIndepOn_simpleSupport _ _ (linearIndependent_typeDClassicalSimpleRoot hn)
  linearIndepOn_coroot := by
    rw [coe_typeDClassicalRootDatum_coroot]
    exact linearIndepOn_simpleSupport _ _ (linearIndependent_typeDClassicalSimpleRoot hn)
  root_mem_or_neg_mem x := by
    rw [coe_typeDClassicalRootDatum_root, image_simpleSupport]
    exact mem_or_neg_mem_closure hn x
  coroot_mem_or_neg_mem x := by
    rw [coe_typeDClassicalRootDatum_coroot, image_simpleSupport]
    exact mem_or_neg_mem_closure hn x

/-- The support of the Bourbaki base consists of the simple roots. -/
theorem mem_typeDClassicalBase_support {x : TypeDRoot n} :
    x ∈ (typeDClassicalBase hn).support ↔ ∃ i, typeDClassicalSimpleIndex hn i = x :=
  mem_simpleSupport _

/-- The Bourbaki base of type `Dₙ` has `n` simple roots. -/
theorem card_typeDClassicalBase_support : (typeDClassicalBase hn).support.card = n := by
  have h : (typeDClassicalBase hn).support = Finset.univ.image (typeDClassicalSimpleIndex hn) :=
    Finset.coe_injective (by
      rw [Finset.coe_image, Finset.coe_univ, image_univ]
      exact coe_simpleSupport _)
  rw [h, Finset.card_image_of_injective _ (typeDClassicalSimpleIndex_injective hn),
    Finset.card_univ, Fintype.card_fin]

end Base

/-! ### Checks -/

/-- In type `D₂ = A₁ × A₁` the two simple roots `e₀ - e₁` and `e₀ + e₁` are orthogonal. -/
example : typeDClassicalSimpleRoot (n := 2) le_rfl 0 ⬝ᵥ typeDClassicalSimpleRoot le_rfl 1 = 0 := by
  simp [typeDClassicalSimpleRoot, dotProduct, Fin.sum_univ_two]

/-- In type `D₃ = A₃` the simple roots `e₁ - e₂` and `e₁ + e₂` are orthogonal and both pair to
`-1` with `e₀ - e₁`: the Dynkin diagram is the chain `A₃` with `e₀ - e₁` in the middle. -/
example :
    typeDClassicalSimpleRoot (n := 3) (by norm_num) 1 ⬝ᵥ
        typeDClassicalSimpleRoot (by norm_num) 2 = 0 ∧
      typeDClassicalSimpleRoot (n := 3) (by norm_num) 0 ⬝ᵥ
        typeDClassicalSimpleRoot (by norm_num) 1 = -1 ∧
      typeDClassicalSimpleRoot (n := 3) (by norm_num) 0 ⬝ᵥ
        typeDClassicalSimpleRoot (by norm_num) 2 = -1 := by
  simp [typeDClassicalSimpleRoot, dotProduct, Fin.sum_univ_three, Pi.single_apply]

end TauCeti.DynkinType
