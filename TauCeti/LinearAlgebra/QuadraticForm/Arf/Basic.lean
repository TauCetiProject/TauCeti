/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.Fintype.Pi
public import TauCeti.LinearAlgebra.QuadraticForm.CharTwo
import Mathlib.Algebra.CharP.Two
import Mathlib.FieldTheory.Finiteness
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring
import TauCeti.Data.ZMod.IntUnitsPower
import TauCeti.Data.ZMod.Two
import TauCeti.LinearAlgebra.QuadraticForm.Isometry
import TauCeti.LinearAlgebra.QuadraticForm.Prod
import TauCeti.LinearAlgebra.QuadraticForm.Radical

/-!
# The Gauss sum and Arf invariant of a quadratic form over `𝔽₂`

Over an arbitrary field `K` of characteristic two, the Arf invariant of a finite-dimensional
quadratic form with nondegenerate polar form takes values in the Artin--Schreier additive quotient
`K / {t ^ 2 + t | t ∈ K}`. Over `ZMod 2`, every scalar satisfies `t ^ 2 + t = 0`, so the
Artin--Schreier subgroup vanishes and the Arf invariant is an element of `ZMod 2` itself: in any
symplectic basis `b : Module.Basis (ι ⊕ ι) (ZMod 2) V` of `Q.polarBilin`, it is given by
`∑ i : ι, Q (b (Sum.inl i)) * Q (b (Sum.inr i))`.

Following Brown and Browder, we establish basis independence through the integer Gauss sum
`Q.gaussSum = ∑ v : V, (-1 : ℤ) ^ (Q v).val`:

1. `Q.gaussSum` is manifestly independent of coordinates, invariant under isometry, and
   multiplicative under `QuadraticMap.prod` and `QuadraticMap.pi`.
2. On a binary symplectic plane `TauCeti.symplecticPlane (ZMod 2) a b`, direct evaluation over the
   four vectors of `Fin 2 → ZMod 2` gives `(-1) ^ (a * b).val * 2`.
3. Decomposing `(V, Q)` along any symplectic basis `b : Module.Basis (ι ⊕ ι) (ZMod 2) V` via
   `QuadraticMap.isometryEquivPiSymplecticPlane` therefore evaluates `Q.gaussSum` to
   `(-1) ^ (∑ i, Q (b (Sum.inl i)) * Q (b (Sum.inr i))).val * 2 ^ Fintype.card ι`. Since
   `2 ^ Fintype.card ι ≠ 0` in `ℤ`, the symplectic-basis sum depends only on `Q`.

From the Gauss-sum identity we deduce isometry invariance and orthogonal-sum additivity of
`QuadraticMap.arf`, the exact cardinality formulas for `{v : V // Q v = 0}` and
`{v : V // Q v = 1}`, the *majority-vote* characterization (`Q.arf = 0` if and only if `Q` vanishes
on strictly more vectors than it takes the value `1`), and the Gauss-sum descent identity across
`V ⧸ Q.polarBilin.ker` when `Q` vanishes on `Q.polarBilin.ker`.

## Main definitions

* `QuadraticMap.gaussSum`: the integer sum `∑ v : V, (-1 : ℤ) ^ (Q v).val` of
  `Q : QuadraticForm (ZMod 2) V`.
* `QuadraticMap.arf`: the `ZMod 2`-valued Arf invariant of `Q : QuadraticForm (ZMod 2) V` (defined
  as `0` when `V` is infinite-dimensional or `Q.polarBilin` is degenerate).

## Main results

* `QuadraticMap.gaussSum_eq_of_toMatrix_polarBilin_eq_J`: evaluation of `Q.gaussSum` in any
  symplectic basis.
* `QuadraticMap.sum_mul_eq_of_toMatrix_polarBilin_eq_J`: independence of
  `∑ i, Q (b (Sum.inl i)) * Q (b (Sum.inr i))` from the choice of symplectic basis `b`.
* `QuadraticMap.arf_eq_sum_of_toMatrix_polarBilin_eq_J`: `Q.arf` equals the symplectic-basis sum in
  every symplectic basis of `Q.polarBilin`.
* `QuadraticMap.gaussSum_eq_arf_of_finrank_eq`: `Q.gaussSum = (-1) ^ Q.arf.val * 2 ^ m` when
  `Module.finrank (ZMod 2) V = 2 * m`.
* `QuadraticMap.IsometryEquiv.arf_eq`, `QuadraticMap.Equivalent.arf_eq`, `QuadraticMap.arf_prod`,
  `QuadraticMap.arf_pi`, `QuadraticMap.arf_of_isCompl_orthogonal`: isometry invariance and
  orthogonal-sum additivity of `Q.arf`.
* `QuadraticMap.two_mul_card_eq_zero`, `QuadraticMap.card_eq_zero_of_pos`,
  `QuadraticMap.arf_eq_zero_iff_card_lt_card`: zero-locus counts and majority-vote criterion.
* `QuadraticMap.gaussSum_eq_card_ker_polarBilin_mul_gaussSum_lift`: factorization of `Q.gaussSum`
  through `V ⧸ Q.polarBilin.ker` when `Q.polarBilin.ker ≤ Q.radical`.

## References

* C. Arf, *Untersuchungen über quadratische Formen in Körpern der Charakteristik 2 (Teil I)*, J.
  Reine Angew. Math. **183** (1941), 148--167.
* W. Browder, *Surgery on Simply-Connected Manifolds*, Ergebnisse der Mathematik und ihrer
  Grenzgebiete 65, Springer (1972), Chapter III, §1.
* E. H. Brown Jr., *Generalizations of the Kervaire invariant*, Ann. of Math. (2) **95** (1972),
  368--383.
-/

public section

open TauCeti

/-! ### The Gauss sum of a quadratic form over `ZMod 2` -/

namespace QuadraticMap

section GaussSum

variable {V V₁ V₂ : Type*} [AddCommGroup V] [Module (ZMod 2) V]
  [AddCommGroup V₁] [Module (ZMod 2) V₁] [AddCommGroup V₂] [Module (ZMod 2) V₂]

/-- The integer Gauss sum `∑ v : V, (-1 : ℤ) ^ (Q v).val` of a quadratic form `Q` on a finite
`ZMod 2`-module `V`, counting `Q`-zeros with weight `+1` and `Q`-ones with weight `-1`. -/
def gaussSum [Fintype V] (Q : QuadraticForm (ZMod 2) V) : ℤ :=
  ∑ v : V, (-1 : ℤ) ^ (Q v).val

/-- Unfolds `QuadraticMap.gaussSum`. -/
theorem gaussSum_def [Fintype V] (Q : QuadraticForm (ZMod 2) V) :
    Q.gaussSum = ∑ v : V, (-1 : ℤ) ^ (Q v).val :=
  (rfl)

/-- The Gauss sum is independent of the `Fintype` instance on `V`. -/
@[congr]
theorem gaussSum_subsingleton_fintype (Q : QuadraticForm (ZMod 2) V)
    (inst₁ inst₂ : Fintype V) :
    @gaussSum V _ _ inst₁ Q = @gaussSum V _ _ inst₂ Q := by
  rw [Subsingleton.elim inst₁ inst₂]

/-- Isometric quadratic forms over `ZMod 2` have equal Gauss sums. -/
theorem IsometryEquiv.gaussSum_eq [Fintype V₁] [Fintype V₂]
    {Q₁ : QuadraticForm (ZMod 2) V₁} {Q₂ : QuadraticForm (ZMod 2) V₂}
    (e : Q₁.IsometryEquiv Q₂) : Q₁.gaussSum = Q₂.gaussSum := by
  rw [gaussSum_def, gaussSum_def]
  exact Fintype.sum_equiv e.toEquiv _ _ fun v ↦ by
    rw [← e.map_app]
    rfl

/-- Equivalent quadratic forms over `ZMod 2` have equal Gauss sums. -/
theorem Equivalent.gaussSum_eq [Fintype V₁] [Fintype V₂]
    {Q₁ : QuadraticForm (ZMod 2) V₁} {Q₂ : QuadraticForm (ZMod 2) V₂}
    (h : Q₁.Equivalent Q₂) : Q₁.gaussSum = Q₂.gaussSum := by
  obtain ⟨e⟩ := h
  exact e.gaussSum_eq

/-- The Gauss sum of the zero quadratic form on `V` is `Fintype.card V`. -/
@[simp]
theorem gaussSum_zero [Fintype V] : (0 : QuadraticForm (ZMod 2) V).gaussSum = Fintype.card V := by
  simp [gaussSum_def]

/-- On a subsingleton `ZMod 2`-space, every quadratic form has Gauss sum `1`. -/
@[simp]
theorem gaussSum_subsingleton [Fintype V] [Subsingleton V] (Q : QuadraticForm (ZMod 2) V) :
    Q.gaussSum = 1 := by
  rw [gaussSum_def, Fintype.sum_subsingleton _ (0 : V), map_zero]
  rfl

/-- The Gauss sum is multiplicative on orthogonal products. -/
@[simp]
theorem gaussSum_prod [Fintype V₁] [Fintype V₂]
    (Q₁ : QuadraticForm (ZMod 2) V₁) (Q₂ : QuadraticForm (ZMod 2) V₂) :
    (Q₁.prod Q₂).gaussSum = Q₁.gaussSum * Q₂.gaussSum := by
  simp only [gaussSum_def, Fintype.sum_prod_type, QuadraticMap.prod_apply, ← coe_hilbertSign,
    hilbertSign_add, Units.val_mul]
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl fun x _ ↦ ?_
  rw [Finset.mul_sum]

/-- The Gauss sum is multiplicative on finite orthogonal sums `QuadraticMap.pi`. -/
@[simp]
theorem gaussSum_pi {ι : Type*} [Fintype ι] [DecidableEq ι] {M : ι → Type*}
    [∀ i, AddCommGroup (M i)] [∀ i, Module (ZMod 2) (M i)] [∀ i, Fintype (M i)]
    (Q : ∀ i, QuadraticForm (ZMod 2) (M i)) :
    (QuadraticMap.pi Q).gaussSum = ∏ i, (Q i).gaussSum := by
  simp_rw [gaussSum_def, pi_apply, ← coe_hilbertSign, hilbertSign_sum, Units.coe_prod]
  exact (Fintype.prod_sum fun i v ↦ (hilbertSign (Q i v) : ℤ)).symm

end GaussSum

end QuadraticMap

namespace TauCeti

/-- On `symplecticPlane (ZMod 2) a b`, the Gauss sum equals `(-1) ^ (a * b).val * 2`. -/
@[simp]
theorem gaussSum_symplecticPlane (a b : ZMod 2) :
    (symplecticPlane (ZMod 2) a b).gaussSum = (-1 : ℤ) ^ (a * b).val * 2 := by
  let e : (Fin 2 → ZMod 2) ≃ ZMod 2 × ZMod 2 := (LinearEquiv.finTwoArrow (ZMod 2) (ZMod 2)).toEquiv
  rw [QuadraticMap.gaussSum_def,
    Fintype.sum_equiv e _ (fun p : ZMod 2 × ZMod 2 ↦
      (-1 : ℤ) ^ (a * p.1 ^ 2 + p.1 * p.2 + b * p.2 ^ 2).val) (fun x ↦ by
        simp [e, symplecticPlane_apply]),
    Fintype.sum_prod_type]
  have hsum (f : ZMod 2 → ℤ) : ∑ x : ZMod 2, f x = f 0 + f 1 := by
    change ∑ x : Fin 2, f x = f 0 + f 1
    exact Fin.sum_univ_two f
  rw [hsum]
  simp only [hsum]
  rcases a.eq_zero_or_eq_one with rfl | rfl <;>
    rcases b.eq_zero_or_eq_one with rfl | rfl <;> rfl

end TauCeti

namespace QuadraticMap

section SymplecticGaussSum

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]

/-- In any basis `b : Module.Basis (ι ⊕ ι) (ZMod 2) V` in which `Q.polarBilin` has matrix
`Matrix.J ι (ZMod 2)`, the Gauss sum of `Q` evaluates to
`(-1) ^ (∑ i, Q (b (Sum.inl i)) * Q (b (Sum.inr i))).val * 2 ^ Fintype.card ι`. -/
theorem gaussSum_eq_of_toMatrix_polarBilin_eq_J [Fintype V]
    {ι : Type*} [Fintype ι] [DecidableEq ι] (Q : QuadraticForm (ZMod 2) V)
    {b : Module.Basis (ι ⊕ ι) (ZMod 2) V}
    (hb : LinearMap.BilinForm.toMatrix b Q.polarBilin = Matrix.J ι (ZMod 2)) :
    Q.gaussSum =
      (-1 : ℤ) ^ (∑ i : ι, Q (b (Sum.inl i)) * Q (b (Sum.inr i))).val * 2 ^ Fintype.card ι := by
  rw [(Q.isometryEquivPiSymplecticPlane b hb).gaussSum_eq, gaussSum_pi]
  simp only [gaussSum_symplecticPlane, Finset.prod_mul_distrib, Finset.prod_const,
    Finset.card_univ, ← coe_hilbertSign, ← Units.coe_prod, hilbertSign_sum]

/-- **Basis independence of the symplectic-basis Arf sum.** Any two symplectic bases of
`Q.polarBilin` yield the same sum `∑ i, Q (b (Sum.inl i)) * Q (b (Sum.inr i))` in `ZMod 2`. -/
theorem sum_mul_eq_of_toMatrix_polarBilin_eq_J
    {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    (Q : QuadraticForm (ZMod 2) V)
    {b : Module.Basis (ι ⊕ ι) (ZMod 2) V} {c : Module.Basis (κ ⊕ κ) (ZMod 2) V}
    (hb : LinearMap.BilinForm.toMatrix b Q.polarBilin = Matrix.J ι (ZMod 2))
    (hc : LinearMap.BilinForm.toMatrix c Q.polarBilin = Matrix.J κ (ZMod 2)) :
    ∑ i : ι, Q (b (Sum.inl i)) * Q (b (Sum.inr i)) =
      ∑ j : κ, Q (c (Sum.inl j)) * Q (c (Sum.inr j)) := by
  let _ : Fintype V := Fintype.ofEquiv _ b.equivFun.toEquiv.symm
  have hcard_sum : Fintype.card (ι ⊕ ι) = Fintype.card (κ ⊕ κ) := by
    rw [← Module.finrank_eq_card_basis b, ← Module.finrank_eq_card_basis c]
  have hcard : Fintype.card ι = Fintype.card κ := by
    simp only [Fintype.card_sum] at hcard_sum
    omega
  have hg : (-1 : ℤ) ^ (∑ i : ι, Q (b (Sum.inl i)) * Q (b (Sum.inr i))).val * 2 ^ Fintype.card κ =
      (-1 : ℤ) ^ (∑ j : κ, Q (c (Sum.inl j)) * Q (c (Sum.inr j))).val * 2 ^ Fintype.card κ := by
    conv_lhs => rw [← hcard]
    rw [← Q.gaussSum_eq_of_toMatrix_polarBilin_eq_J hb,
      Q.gaussSum_eq_of_toMatrix_polarBilin_eq_J hc]
  have hsign := mul_right_cancel₀ (pow_ne_zero (Fintype.card κ) (by decide : (2 : ℤ) ≠ 0)) hg
  exact hilbertSign_injective (Units.ext (by simpa only [coe_hilbertSign] using hsign))

end SymplecticGaussSum

/-! ### The Arf invariant -/

section Arf

variable {V V₁ V₂ : Type*} [AddCommGroup V] [Module (ZMod 2) V]
  [AddCommGroup V₁] [Module (ZMod 2) V₁] [AddCommGroup V₂] [Module (ZMod 2) V₂]

/-- The **Arf invariant** of a quadratic form `Q : QuadraticForm (ZMod 2) V`, taking values in
`ZMod 2`.

When `V` is finite-dimensional and `Q.polarBilin` is nondegenerate, `Q.arf` is the sum
`∑ i, Q (b (Sum.inl i)) * Q (b (Sum.inr i))` in any symplectic basis `b` of `Q.polarBilin`
(`QuadraticMap.arf_eq_sum_of_toMatrix_polarBilin_eq_J`). Outside that regime it defaults to `0`. -/
noncomputable def arf (Q : QuadraticForm (ZMod 2) V) : ZMod 2 :=
  open scoped Classical in
  if h : FiniteDimensional (ZMod 2) V ∧ Q.polarBilin.Nondegenerate then
    letI : FiniteDimensional (ZMod 2) V := h.1
    let spec := Q.exists_basis_toMatrix_polarBilin_eq_J h.2
    let b := spec.choose_spec.choose
    ∑ i : Fin spec.choose, Q (b (Sum.inl i)) * Q (b (Sum.inr i))
  else 0

/-- Outside finite dimension, `Q.arf` takes the default value `0`. -/
theorem arf_of_not_finiteDimensional (Q : QuadraticForm (ZMod 2) V)
    (h : ¬FiniteDimensional (ZMod 2) V) : Q.arf = 0 := by
  simp [arf, h]

/-- When `Q.polarBilin` is degenerate, `Q.arf` takes the default value `0`. -/
theorem arf_of_not_nondegenerate_polarBilin (Q : QuadraticForm (ZMod 2) V)
    (h : ¬Q.polarBilin.Nondegenerate) : Q.arf = 0 := by
  simp [arf, h]

/-- In any finite basis `b : Module.Basis (ι ⊕ ι) (ZMod 2) V` putting `Q.polarBilin` in standard
symplectic form `Matrix.J ι (ZMod 2)`, `Q.arf` equals
`∑ i : ι, Q (b (Sum.inl i)) * Q (b (Sum.inr i))`. -/
theorem arf_eq_sum_of_toMatrix_polarBilin_eq_J {ι : Type*} [Fintype ι] [DecidableEq ι]
    (Q : QuadraticForm (ZMod 2) V) {b : Module.Basis (ι ⊕ ι) (ZMod 2) V}
    (hb : LinearMap.BilinForm.toMatrix b Q.polarBilin = Matrix.J ι (ZMod 2)) :
    Q.arf = ∑ i : ι, Q (b (Sum.inl i)) * Q (b (Sum.inr i)) := by
  have hfd : FiniteDimensional (ZMod 2) V := Module.Finite.of_basis b
  have hnd : Q.polarBilin.Nondegenerate := nondegenerate_polarBilin_of_toMatrix_eq_J hb
  simp only [arf, hfd, hnd, and_self, ↓reduceDIte]
  exact Q.sum_mul_eq_of_toMatrix_polarBilin_eq_J
    (Q.exists_basis_toMatrix_polarBilin_eq_J hnd).choose_spec.choose_spec hb

/-- **Gauss-sum formula for the Arf invariant.** For a quadratic form `Q` on a finite `ZMod 2`-space
`V` of dimension `2 * m` with nondegenerate polar form, `Q.gaussSum = (-1) ^ Q.arf.val * 2 ^ m`. -/
theorem gaussSum_eq_arf_of_finrank_eq [Fintype V] {Q : QuadraticForm (ZMod 2) V}
    (hQ : Q.polarBilin.Nondegenerate) {m : ℕ} (hdim : Module.finrank (ZMod 2) V = 2 * m) :
    Q.gaussSum = (-1 : ℤ) ^ Q.arf.val * 2 ^ m := by
  obtain ⟨k, b, hb⟩ := Q.exists_basis_toMatrix_polarBilin_eq_J hQ
  have hkm : k = m := by
    have hcard := Module.finrank_eq_card_basis b
    simp only [Fintype.card_sum, Fintype.card_fin] at hcard
    omega
  subst hkm
  rw [Q.arf_eq_sum_of_toMatrix_polarBilin_eq_J hb, Q.gaussSum_eq_of_toMatrix_polarBilin_eq_J hb,
    Fintype.card_fin]

/-- On a subsingleton `ZMod 2`-space, `Q.arf = 0`. -/
@[simp]
theorem arf_subsingleton [Subsingleton V] (Q : QuadraticForm (ZMod 2) V) : Q.arf = 0 := by
  let b : Module.Basis (Fin 0 ⊕ Fin 0) (ZMod 2) V := Module.Basis.empty V
  have hb : LinearMap.BilinForm.toMatrix b Q.polarBilin = Matrix.J (Fin 0) (ZMod 2) := by
    ext x
    exact x.elim isEmptyElim isEmptyElim
  rw [Q.arf_eq_sum_of_toMatrix_polarBilin_eq_J hb]
  simp

/-- Isometric quadratic forms over `ZMod 2` have the same Arf invariant. -/
theorem IsometryEquiv.arf_eq {Q₁ : QuadraticForm (ZMod 2) V₁} {Q₂ : QuadraticForm (ZMod 2) V₂}
    (e : Q₁.IsometryEquiv Q₂) : Q₁.arf = Q₂.arf := by
  by_cases h₁ : FiniteDimensional (ZMod 2) V₁ ∧ Q₁.polarBilin.Nondegenerate
  · obtain ⟨_, hnd₁⟩ := h₁
    have hnd₂ : Q₂.polarBilin.Nondegenerate := e.nondegenerate_polarBilin_iff.mp hnd₁
    obtain ⟨m, b₁, _⟩ := Q₁.exists_basis_toMatrix_polarBilin_eq_J hnd₁
    let _ : Fintype V₁ := Fintype.ofEquiv _ b₁.equivFun.toEquiv.symm
    let _ : Fintype V₂ := Fintype.ofEquiv _ (b₁.map e.toLinearEquiv).equivFun.toEquiv.symm
    have hdim₁ : Module.finrank (ZMod 2) V₁ = 2 * m := by
      have hc := Module.finrank_eq_card_basis b₁
      simp only [Fintype.card_sum, Fintype.card_fin] at hc
      omega
    have hdim₂ : Module.finrank (ZMod 2) V₂ = 2 * m :=
      e.toLinearEquiv.finrank_eq.symm.trans hdim₁
    have hg := e.gaussSum_eq
    rw [Q₁.gaussSum_eq_arf_of_finrank_eq hnd₁ hdim₁,
      Q₂.gaussSum_eq_arf_of_finrank_eq hnd₂ hdim₂] at hg
    have hsign := mul_right_cancel₀ (pow_ne_zero m (by decide : (2 : ℤ) ≠ 0)) hg
    exact hilbertSign_injective (Units.ext (by simpa only [coe_hilbertSign] using hsign))
  · have h₂ : ¬(FiniteDimensional (ZMod 2) V₂ ∧ Q₂.polarBilin.Nondegenerate) := by
      rintro ⟨_, hnd₂⟩
      exact h₁ ⟨Module.Finite.equiv e.symm.toLinearEquiv,
        e.nondegenerate_polarBilin_iff.mpr hnd₂⟩
    simp only [arf, h₁, h₂, ↓reduceDIte]

/-- Equivalent quadratic forms over `ZMod 2` have the same Arf invariant. -/
theorem Equivalent.arf_eq {Q₁ : QuadraticForm (ZMod 2) V₁} {Q₂ : QuadraticForm (ZMod 2) V₂}
    (h : Q₁.Equivalent Q₂) : Q₁.arf = Q₂.arf := by
  obtain ⟨e⟩ := h
  exact e.arf_eq

/-- **Additivity of the Arf invariant on orthogonal products.** -/
theorem arf_prod [FiniteDimensional (ZMod 2) V₁] [FiniteDimensional (ZMod 2) V₂]
    {Q₁ : QuadraticForm (ZMod 2) V₁} {Q₂ : QuadraticForm (ZMod 2) V₂}
    (hQ₁ : Q₁.polarBilin.Nondegenerate) (hQ₂ : Q₂.polarBilin.Nondegenerate) :
    (Q₁.prod Q₂).arf = Q₁.arf + Q₂.arf := by
  obtain ⟨m₁, b₁, _⟩ := Q₁.exists_basis_toMatrix_polarBilin_eq_J hQ₁
  obtain ⟨m₂, b₂, _⟩ := Q₂.exists_basis_toMatrix_polarBilin_eq_J hQ₂
  let _ : Fintype V₁ := Fintype.ofEquiv _ b₁.equivFun.toEquiv.symm
  let _ : Fintype V₂ := Fintype.ofEquiv _ b₂.equivFun.toEquiv.symm
  have hdim₁ : Module.finrank (ZMod 2) V₁ = 2 * m₁ := by
    have hc := Module.finrank_eq_card_basis b₁
    simp only [Fintype.card_sum, Fintype.card_fin] at hc
    omega
  have hdim₂ : Module.finrank (ZMod 2) V₂ = 2 * m₂ := by
    have hc := Module.finrank_eq_card_basis b₂
    simp only [Fintype.card_sum, Fintype.card_fin] at hc
    omega
  have hdim : Module.finrank (ZMod 2) (V₁ × V₂) = 2 * (m₁ + m₂) := by
    rw [Module.finrank_prod, hdim₁, hdim₂, mul_add]
  have hnd : (Q₁.prod Q₂).polarBilin.Nondegenerate :=
    nondegenerate_polarBilin_prod_iff.mpr ⟨hQ₁, hQ₂⟩
  have hg := gaussSum_prod Q₁ Q₂
  rw [(Q₁.prod Q₂).gaussSum_eq_arf_of_finrank_eq hnd hdim,
    Q₁.gaussSum_eq_arf_of_finrank_eq hQ₁ hdim₁,
    Q₂.gaussSum_eq_arf_of_finrank_eq hQ₂ hdim₂] at hg
  have hcalc : ((-1 : ℤ) ^ Q₁.arf.val * 2 ^ m₁) * ((-1 : ℤ) ^ Q₂.arf.val * 2 ^ m₂) =
      (-1 : ℤ) ^ (Q₁.arf + Q₂.arf).val * 2 ^ (m₁ + m₂) := by
    simp only [← coe_hilbertSign, hilbertSign_add, Units.val_mul, pow_add]
    ring
  rw [hcalc] at hg
  have hsign := mul_right_cancel₀ (pow_ne_zero (m₁ + m₂) (by decide : (2 : ℤ) ≠ 0)) hg
  exact hilbertSign_injective (Units.ext (by simpa only [coe_hilbertSign] using hsign))

/-- The Arf invariant of `Q.prod Q` vanishes for every quadratic form `Q` over `ZMod 2`. -/
@[simp]
theorem arf_prod_self (Q : QuadraticForm (ZMod 2) V) : (Q.prod Q).arf = 0 := by
  by_cases h : FiniteDimensional (ZMod 2) V ∧ Q.polarBilin.Nondegenerate
  · obtain ⟨_, hQ⟩ := h
    rw [arf_prod hQ hQ, CharTwo.add_self_eq_zero]
  · have hprod : ¬(FiniteDimensional (ZMod 2) (V × V) ∧ (Q.prod Q).polarBilin.Nondegenerate) := by
      rintro ⟨_, hnd⟩
      exact h ⟨Module.Finite.of_surjective (LinearMap.fst (ZMod 2) V V) Prod.fst_surjective,
        (nondegenerate_polarBilin_prod_iff.mp hnd).1⟩
    simp only [arf, hprod, ↓reduceDIte]

/-- **Additivity of the Arf invariant on finite orthogonal sums.** -/
theorem arf_pi {ι : Type*} [Fintype ι] {M : ι → Type*}
    [∀ i, AddCommGroup (M i)] [∀ i, Module (ZMod 2) (M i)]
    [∀ i, FiniteDimensional (ZMod 2) (M i)]
    {Q : ∀ i, QuadraticForm (ZMod 2) (M i)} (hQ : ∀ i, (Q i).polarBilin.Nondegenerate) :
    (QuadraticMap.pi Q).arf = ∑ i, (Q i).arf := by
  classical
  have hfin (i : ι) : ∃ m : ℕ, Nonempty (Module.Basis (Fin m ⊕ Fin m) (ZMod 2) (M i)) := by
    obtain ⟨m, b, _⟩ := (Q i).exists_basis_toMatrix_polarBilin_eq_J (hQ i)
    exact ⟨m, ⟨b⟩⟩
  choose m hm using hfin
  let b : ∀ i, Module.Basis (Fin (m i) ⊕ Fin (m i)) (ZMod 2) (M i) :=
    fun i ↦ Classical.choice (hm i)
  let _ : ∀ i, Fintype (M i) := fun i ↦ Fintype.ofEquiv _ (b i).equivFun.toEquiv.symm
  have hdim_i (i : ι) : Module.finrank (ZMod 2) (M i) = 2 * m i := by
    have hc := Module.finrank_eq_card_basis (b i)
    simp only [Fintype.card_sum, Fintype.card_fin] at hc
    omega
  have hdim : Module.finrank (ZMod 2) (∀ i, M i) = 2 * ∑ i, m i := by
    rw [Module.finrank_pi_fintype, Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ ↦ hdim_i i
  have hnd : (QuadraticMap.pi Q).polarBilin.Nondegenerate :=
    nondegenerate_polarBilin_pi_iff.mpr hQ
  have hg := gaussSum_pi Q
  rw [(QuadraticMap.pi Q).gaussSum_eq_arf_of_finrank_eq hnd hdim] at hg
  have hprod : ∏ i, (Q i).gaussSum = (-1 : ℤ) ^ (∑ i, (Q i).arf).val * 2 ^ ∑ i, m i := by
    calc
      ∏ i, (Q i).gaussSum = ∏ i, ((-1 : ℤ) ^ ((Q i).arf).val * 2 ^ m i) :=
        Finset.prod_congr rfl fun i _ ↦ (Q i).gaussSum_eq_arf_of_finrank_eq (hQ i) (hdim_i i)
      _ = (∏ i, (-1 : ℤ) ^ ((Q i).arf).val) * ∏ i, (2 : ℤ) ^ m i := Finset.prod_mul_distrib
      _ = (-1 : ℤ) ^ (∑ i, (Q i).arf).val * 2 ^ ∑ i, m i := by
        simp only [← coe_hilbertSign, ← Units.coe_prod, hilbertSign_sum,
          Finset.prod_pow_eq_pow_sum]
  rw [hprod] at hg
  have hsign := mul_right_cancel₀ (pow_ne_zero (∑ i, m i) (by decide : (2 : ℤ) ≠ 0)) hg
  exact hilbertSign_injective (Units.ext (by simpa only [coe_hilbertSign] using hsign))

/-- **Additivity of the Arf invariant across an internal polar-orthogonal decomposition.** -/
theorem arf_of_isCompl_orthogonal [FiniteDimensional (ZMod 2) V]
    {Q : QuadraticForm (ZMod 2) V} (hQ : Q.polarBilin.Nondegenerate)
    (W : Submodule (ZMod 2) V)
    (hW : IsCompl W (LinearMap.BilinForm.orthogonal Q.polarBilin W)) :
    Q.arf =
      (Q.restrict W).arf + (Q.restrict (LinearMap.BilinForm.orthogonal Q.polarBilin W)).arf := by
  have he := IsometryEquiv.prodRestrictOrthogonal Q W hW
  have hnd_prod :
      ((Q.restrict W).prod
        (Q.restrict (LinearMap.BilinForm.orthogonal Q.polarBilin W))).polarBilin.Nondegenerate :=
    he.nondegenerate_polarBilin_iff.mpr hQ
  obtain ⟨hndW, hndW'⟩ := nondegenerate_polarBilin_prod_iff.mp hnd_prod
  rw [← he.arf_eq, arf_prod hndW hndW']

end Arf

end QuadraticMap

namespace TauCeti

/-- The Arf invariant of `symplecticPlane (ZMod 2) a b` is `a * b`. -/
@[simp]
theorem arf_symplecticPlane (a b : ZMod 2) :
    (symplecticPlane (ZMod 2) a b).arf = a * b := by
  have hdim : Module.finrank (ZMod 2) (Fin 2 → ZMod 2) = 2 * 1 := by
    simp
  have hg := (symplecticPlane (ZMod 2) a b).gaussSum_eq_arf_of_finrank_eq
    (nondegenerate_polarBilin_symplecticPlane a b) hdim
  rw [gaussSum_symplecticPlane, pow_one] at hg
  have hsign := mul_right_cancel₀ (by decide : (2 : ℤ) ≠ 0) hg.symm
  exact hilbertSign_injective (Units.ext (by simpa only [coe_hilbertSign] using hsign))

end TauCeti

/-! ### Zero-locus counts, majority vote, and polar-kernel descent of the Gauss sum -/

namespace QuadraticMap

section ZeroCountAndDescent

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V] [Fintype V]

/-- On a subsingleton `ZMod 2`-space, `0` is the unique zero of `Q`, so `{v : V // Q v = 0}` has
cardinality `1`. -/
@[simp]
theorem card_eq_zero_subsingleton [Subsingleton V] (Q : QuadraticForm (ZMod 2) V) :
    Fintype.card {v : V // Q v = 0} = 1 :=
  Fintype.card_eq_one_iff.mpr ⟨⟨0, map_zero Q⟩, fun ⟨v, _⟩ ↦ Subtype.ext (Subsingleton.elim v 0)⟩

/-- In dimension zero (`m = 0`), `{v : V // Q v = 0}` has cardinality `1`. -/
theorem card_eq_zero_of_finrank_eq_zero (Q : QuadraticForm (ZMod 2) V)
    (hdim : Module.finrank (ZMod 2) V = 0) :
    Fintype.card {v : V // Q v = 0} = 1 := by
  have : Subsingleton V := Module.finrank_zero_iff.mp hdim
  exact Q.card_eq_zero_subsingleton

/-- Every vector of `V` satisfies either `Q v = 0` or `Q v = 1`, partitioning `V`. -/
theorem card_eq_zero_add_card_eq_one (Q : QuadraticForm (ZMod 2) V) :
    Fintype.card {v : V // Q v = 0} + Fintype.card {v : V // Q v = 1} = Fintype.card V := by
  rw [Fintype.card_subtype, Fintype.card_subtype]
  have hnot : Finset.filter (fun v : V ↦ Q v = 1) Finset.univ =
      Finset.filter (fun v : V ↦ ¬Q v = 0) Finset.univ := by
    ext v
    simp [ZMod.ne_zero_iff_eq_one]
  rw [hnot, Finset.card_filter_add_card_filter_not]
  exact Finset.card_univ

/-- The Gauss sum of `Q` is the difference between the number of `Q`-zeros and `Q`-ones. -/
theorem gaussSum_eq_card_sub_card (Q : QuadraticForm (ZMod 2) V) :
    Q.gaussSum = (Fintype.card {v : V // Q v = 0} : ℤ) - Fintype.card {v : V // Q v = 1} := by
  rw [gaussSum_def, ← Finset.sum_filter_add_sum_filter_not Finset.univ (fun v : V ↦ Q v = 0)]
  have h0 : ∑ v ∈ Finset.univ with Q v = 0, (-1 : ℤ) ^ (Q v).val =
      Fintype.card {v : V // Q v = 0} := by
    rw [Fintype.card_subtype]
    have hconst : ∑ v ∈ Finset.univ with Q v = 0, (-1 : ℤ) ^ (Q v).val =
        ∑ _v ∈ Finset.filter (fun v : V ↦ Q v = 0) Finset.univ, (1 : ℤ) := by
      refine Finset.sum_congr rfl fun v hv ↦ ?_
      rw [(Finset.mem_filter.mp hv).2]
      rfl
    rw [hconst, Finset.sum_const, nsmul_one]
  have h1 : ∑ v ∈ Finset.univ with ¬Q v = 0, (-1 : ℤ) ^ (Q v).val =
      -(Fintype.card {v : V // Q v = 1} : ℤ) := by
    have hnot : Finset.filter (fun v : V ↦ ¬Q v = 0) Finset.univ =
        Finset.filter (fun v : V ↦ Q v = 1) Finset.univ := by
      ext v
      simp [ZMod.ne_zero_iff_eq_one]
    rw [hnot, Fintype.card_subtype]
    have hconst : ∑ v ∈ Finset.univ with Q v = 1, (-1 : ℤ) ^ (Q v).val =
        ∑ _v ∈ Finset.filter (fun v : V ↦ Q v = 1) Finset.univ, (-1 : ℤ) := by
      refine Finset.sum_congr rfl fun v hv ↦ ?_
      rw [(Finset.mem_filter.mp hv).2]
      rfl
    rw [hconst, Finset.sum_const, nsmul_eq_mul, mul_neg_one]
  rw [h0, h1, sub_eq_add_neg]

/-- Twice the number of `Q`-zeros equals `Fintype.card V + Q.gaussSum`. -/
theorem two_mul_card_eq_zero_eq_card_add_gaussSum (Q : QuadraticForm (ZMod 2) V) :
    2 * (Fintype.card {v : V // Q v = 0} : ℤ) = Fintype.card V + Q.gaussSum := by
  have hpart : (Fintype.card {v : V // Q v = 0} : ℤ) + Fintype.card {v : V // Q v = 1} =
      Fintype.card V := by exact_mod_cast Q.card_eq_zero_add_card_eq_one
  have hg := Q.gaussSum_eq_card_sub_card
  omega

/-- Twice the number of `Q`-ones equals `Fintype.card V - Q.gaussSum`. -/
theorem two_mul_card_eq_one_eq_card_sub_gaussSum (Q : QuadraticForm (ZMod 2) V) :
    2 * (Fintype.card {v : V // Q v = 1} : ℤ) = Fintype.card V - Q.gaussSum := by
  have hpart : (Fintype.card {v : V // Q v = 0} : ℤ) + Fintype.card {v : V // Q v = 1} =
      Fintype.card V := by exact_mod_cast Q.card_eq_zero_add_card_eq_one
  have hg := Q.gaussSum_eq_card_sub_card
  omega

/-- For `Q` with nondegenerate polar form and `Module.finrank (ZMod 2) V = 2 * m` (`m = 0`
included), `2 * #{v : V | Q v = 0} = 2 ^ (2 * m) + (-1) ^ Q.arf.val * 2 ^ m`. -/
theorem two_mul_card_eq_zero {Q : QuadraticForm (ZMod 2) V}
    (hQ : Q.polarBilin.Nondegenerate) {m : ℕ} (hdim : Module.finrank (ZMod 2) V = 2 * m) :
    2 * (Fintype.card {v : V // Q v = 0} : ℤ) =
      2 ^ (2 * m) + (-1 : ℤ) ^ Q.arf.val * 2 ^ m := by
  have hcard : (Fintype.card V : ℤ) = 2 ^ (2 * m) := by
    rw [Module.card_eq_pow_finrank (K := ZMod 2), ZMod.card, hdim]
    norm_cast
  rw [Q.two_mul_card_eq_zero_eq_card_add_gaussSum, hcard,
    Q.gaussSum_eq_arf_of_finrank_eq hQ hdim]

/-- For `Q` with nondegenerate polar form and `Module.finrank (ZMod 2) V = 2 * m` (`m = 0`
included), `2 * #{v : V | Q v = 1} = 2 ^ (2 * m) - (-1) ^ Q.arf.val * 2 ^ m`. -/
theorem two_mul_card_eq_one {Q : QuadraticForm (ZMod 2) V}
    (hQ : Q.polarBilin.Nondegenerate) {m : ℕ} (hdim : Module.finrank (ZMod 2) V = 2 * m) :
    2 * (Fintype.card {v : V // Q v = 1} : ℤ) =
      2 ^ (2 * m) - (-1 : ℤ) ^ Q.arf.val * 2 ^ m := by
  have hcard : (Fintype.card V : ℤ) = 2 ^ (2 * m) := by
    rw [Module.card_eq_pow_finrank (K := ZMod 2), ZMod.card, hdim]
    norm_cast
  rw [Q.two_mul_card_eq_one_eq_card_sub_gaussSum, hcard,
    Q.gaussSum_eq_arf_of_finrank_eq hQ hdim]

/-- For `1 ≤ m` and `Module.finrank (ZMod 2) V = 2 * m` with `Q.polarBilin` nondegenerate,
`#{v : V | Q v = 0} = 2 ^ (2 * m - 1) + (-1) ^ Q.arf.val * 2 ^ (m - 1)`. -/
theorem card_eq_zero_of_pos {Q : QuadraticForm (ZMod 2) V}
    (hQ : Q.polarBilin.Nondegenerate) {m : ℕ} (hm : 1 ≤ m)
    (hdim : Module.finrank (ZMod 2) V = 2 * m) :
    (Fintype.card {v : V // Q v = 0} : ℤ) =
      2 ^ (2 * m - 1) + (-1 : ℤ) ^ Q.arf.val * 2 ^ (m - 1) := by
  have h2 := Q.two_mul_card_eq_zero hQ hdim
  have hp1 : (2 : ℤ) ^ (2 * m) = 2 * 2 ^ (2 * m - 1) := by
    conv_lhs => rw [(by omega : 2 * m = (2 * m - 1) + 1), pow_succ']
  have hp2 : (2 : ℤ) ^ m = 2 * 2 ^ (m - 1) := by
    conv_lhs => rw [(by omega : m = (m - 1) + 1), pow_succ']
  rw [hp1, hp2] at h2
  apply mul_left_cancel₀ (by decide : (2 : ℤ) ≠ 0)
  linear_combination h2

/-- For `1 ≤ m` and `Module.finrank (ZMod 2) V = 2 * m` with `Q.polarBilin` nondegenerate,
`#{v : V | Q v = 1} = 2 ^ (2 * m - 1) - (-1) ^ Q.arf.val * 2 ^ (m - 1)`. -/
theorem card_eq_one_of_pos {Q : QuadraticForm (ZMod 2) V}
    (hQ : Q.polarBilin.Nondegenerate) {m : ℕ} (hm : 1 ≤ m)
    (hdim : Module.finrank (ZMod 2) V = 2 * m) :
    (Fintype.card {v : V // Q v = 1} : ℤ) =
      2 ^ (2 * m - 1) - (-1 : ℤ) ^ Q.arf.val * 2 ^ (m - 1) := by
  have h2 := Q.two_mul_card_eq_one hQ hdim
  have hp1 : (2 : ℤ) ^ (2 * m) = 2 * 2 ^ (2 * m - 1) := by
    conv_lhs => rw [(by omega : 2 * m = (2 * m - 1) + 1), pow_succ']
  have hp2 : (2 : ℤ) ^ m = 2 * 2 ^ (m - 1) := by
    conv_lhs => rw [(by omega : m = (m - 1) + 1), pow_succ']
  rw [hp1, hp2] at h2
  apply mul_left_cancel₀ (by decide : (2 : ℤ) ≠ 0)
  linear_combination h2

/-- For `Q` with nondegenerate polar form on a finite `ZMod 2`-space, `Q.arf = 0` if and only if
`0 < Q.gaussSum`. This holds in dimension zero as well. -/
theorem arf_eq_zero_iff_gaussSum_pos {Q : QuadraticForm (ZMod 2) V}
    (hQ : Q.polarBilin.Nondegenerate) :
    Q.arf = 0 ↔ 0 < Q.gaussSum := by
  obtain ⟨m, hm⟩ := Q.even_finrank_of_nondegenerate_polarBilin hQ
  rw [Q.gaussSum_eq_arf_of_finrank_eq hQ (by omega : Module.finrank (ZMod 2) V = 2 * m)]
  have hpow : (0 : ℤ) < 2 ^ m := pow_pos (by decide : (0 : ℤ) < 2) m
  rcases Q.arf.eq_zero_or_eq_one with h0 | h1
  · rw [h0]
    have hval : (-1 : ℤ) ^ (0 : ZMod 2).val = 1 := rfl
    rw [hval, one_mul]
    exact ⟨fun _ ↦ hpow, fun _ ↦ rfl⟩
  · rw [h1]
    have hval : (-1 : ℤ) ^ (1 : ZMod 2).val = -1 := rfl
    rw [hval]
    exact ⟨fun h ↦ absurd h (by decide), fun h ↦ absurd h (by omega)⟩

/-- For `Q` with nondegenerate polar form on a finite `ZMod 2`-space, `Q.arf = 1` if and only if
`Q.gaussSum < 0`. -/
theorem arf_eq_one_iff_gaussSum_neg {Q : QuadraticForm (ZMod 2) V}
    (hQ : Q.polarBilin.Nondegenerate) :
    Q.arf = 1 ↔ Q.gaussSum < 0 := by
  obtain ⟨m, hm⟩ := Q.even_finrank_of_nondegenerate_polarBilin hQ
  rw [Q.gaussSum_eq_arf_of_finrank_eq hQ (by omega : Module.finrank (ZMod 2) V = 2 * m)]
  have hpow : (0 : ℤ) < 2 ^ m := pow_pos (by decide : (0 : ℤ) < 2) m
  rcases Q.arf.eq_zero_or_eq_one with h0 | h1
  · rw [h0]
    have hval : (-1 : ℤ) ^ (0 : ZMod 2).val = 1 := rfl
    rw [hval, one_mul]
    exact ⟨fun h ↦ absurd h (by decide), fun h ↦ absurd h (by omega)⟩
  · rw [h1]
    have hval : (-1 : ℤ) ^ (1 : ZMod 2).val = -1 := rfl
    rw [hval]
    exact ⟨fun _ ↦ by omega, fun _ ↦ rfl⟩

/-- **Majority-vote characterization of `Q.arf = 0`.** A quadratic form `Q` with nondegenerate
polar form on a finite `ZMod 2`-space has `Q.arf = 0` if and only if `Q` vanishes on strictly more
vectors than it takes the value `1`. -/
theorem arf_eq_zero_iff_card_lt_card {Q : QuadraticForm (ZMod 2) V}
    (hQ : Q.polarBilin.Nondegenerate) :
    Q.arf = 0 ↔ Fintype.card {v : V // Q v = 1} < Fintype.card {v : V // Q v = 0} := by
  rw [Q.arf_eq_zero_iff_gaussSum_pos hQ, Q.gaussSum_eq_card_sub_card]
  omega

/-- **Majority-vote characterization of `Q.arf = 1`.** A quadratic form `Q` with nondegenerate
polar form on a finite `ZMod 2`-space has `Q.arf = 1` if and only if `Q` takes the value `1` on
strictly more vectors than it vanishes on. -/
theorem arf_eq_one_iff_card_lt_card {Q : QuadraticForm (ZMod 2) V}
    (hQ : Q.polarBilin.Nondegenerate) :
    Q.arf = 1 ↔ Fintype.card {v : V // Q v = 0} < Fintype.card {v : V // Q v = 1} := by
  rw [Q.arf_eq_one_iff_gaussSum_neg hQ, Q.gaussSum_eq_card_sub_card]
  omega

/-- **Gauss-sum descent across `Q.polarBilin.ker`.** When `Q.polarBilin.ker ≤ Q.radical`
(equivalently, `Q` vanishes on `Q.polarBilin.ker`), the Gauss sum of `Q` factors as
`Fintype.card Q.polarBilin.ker` times the Gauss sum of the nondegenerate quotient form
`Q.lift Q.polarBilin.ker h`. -/
theorem gaussSum_eq_card_ker_polarBilin_mul_gaussSum_lift (Q : QuadraticForm (ZMod 2) V)
    (h : Q.polarBilin.ker ≤ Q.radical) [Fintype Q.polarBilin.ker]
    [Fintype (V ⧸ Q.polarBilin.ker)] :
    Q.gaussSum = Fintype.card Q.polarBilin.ker * (Q.lift Q.polarBilin.ker h).gaussSum := by
  have hrad : Q.radical = Q.polarBilin.ker :=
    le_antisymm Q.radical_le_ker_polarBilin h
  let eRad : Q.radical ≃ₗ[ZMod 2] Q.polarBilin.ker := LinearEquiv.ofEq _ _ hrad
  let _ : Fintype Q.radical := Fintype.ofEquiv _ eRad.symm.toEquiv
  let eQuot : (V ⧸ Q.radical) ≃ₗ[ZMod 2] (V ⧸ Q.polarBilin.ker) :=
    Submodule.quotEquivOfEq Q.radical Q.polarBilin.ker hrad
  let _ : Fintype (V ⧸ Q.radical) := Fintype.ofEquiv _ eQuot.symm.toEquiv
  have hsplit := (IsometryEquiv.prodRadicalLift Q).symm.gaussSum_eq
  rw [gaussSum_prod, gaussSum_zero] at hsplit
  have hcard : Fintype.card Q.radical = Fintype.card Q.polarBilin.ker :=
    Fintype.card_congr eRad.toEquiv
  have heq : (Q.lift Q.radical le_rfl).IsometryEquiv (Q.lift Q.polarBilin.ker h) :=
    { toLinearEquiv := eQuot
      map_app' := fun x ↦ by
        induction x using Submodule.Quotient.induction_on with
        | H m => rfl }
  rw [hsplit, hcard, heq.gaussSum_eq]

end ZeroCountAndDescent

end QuadraticMap
