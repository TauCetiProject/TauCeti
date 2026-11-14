/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.QuadraticForm.Arf.Basic
import Mathlib.Algebra.CharP.Two
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Ring
import TauCeti.LinearAlgebra.BilinearForm.LinearIndependent
import TauCeti.LinearAlgebra.QuadraticForm.Isometry
import TauCeti.LinearAlgebra.QuadraticForm.Representation

/-!
# Classification of nonsingular quadratic forms over `𝔽₂` by the Arf invariant

Every polar-nondegenerate plane over `𝔽₂` (`ZMod 2`) is isometric either to the hyperbolic plane
`TauCeti.Arf.hyperbolicPlane` (`x₀ x₁`, Arf `0`, Gauss sum `2`, `3` zeros) or to the unique
anisotropic plane `TauCeti.Arf.anisotropicPlane` (`x₀² + x₀ x₁ + x₁²`, Arf `1`, Gauss sum `-2`,
`1` zero). Orthogonal sums of two anisotropic planes are explicitly isometric to orthogonal sums of
two hyperbolic planes (`TauCeti.Arf.anisotropicProdAnisotropicEquiv`), so every finite-dimensional
polar-nondegenerate space over `𝔽₂` decomposes into hyperbolic planes when `Q.arf = 0` and one
anisotropic plane plus hyperbolic planes when `Q.arf = 1`.

As immediate consequences:
* **Arf's classification theorem** (`QuadraticMap.equivalent_iff_finrank_eq_and_arf_eq`): two
  finite-dimensional polar-nondegenerate quadratic spaces over `𝔽₂` are isometric if and only if
  they have the same dimension and the same Arf invariant.
* **Lagrangian vanishing criteria**
  (`QuadraticMap.arf_eq_zero_iff_exists_isTotallyIsotropic_orthogonal_eq`,
  `QuadraticMap.arf_eq_zero_iff_exists_isTotallyIsotropic_finrank_eq`,
  `QuadraticMap.arf_eq_zero_iff_exists_isTotallyIsotropic_finrank_eq_div_two`): `Q.arf = 0` holds
  if and only if `V` admits a `Q`-totally isotropic Lagrangian subspace (`U = U^⊥` for
  `Q.polarBilin`, equivalently `2 * finrank U = finrank V`).

## Main definitions

* `TauCeti.Arf.hyperbolicPlane`: the standard hyperbolic plane `x ↦ x 0 * x 1` on `Fin 2 → ZMod 2`.
* `TauCeti.Arf.anisotropicPlane`: the anisotropic plane `x ↦ x 0 ^ 2 + x 0 * x 1 + x 1 ^ 2` on
  `Fin 2 → ZMod 2`.
* `TauCeti.Arf.anisotropicProdAnisotropicEquiv`: explicit computable isometry equivalence between
  `anisotropicPlane.prod anisotropicPlane` and `hyperbolicPlane.prod hyperbolicPlane`.
* `TauCeti.Arf.diagonalSubmodule`: the two-dimensional diagonal `Q`-zero Lagrangian subspace of
  `anisotropicPlane.prod anisotropicPlane`.

## Main results

* `QuadraticMap.equivalent_pi_hyperbolicPlane_iff_arf_eq_zero`,
  `QuadraticMap.equivalent_anisotropicPlane_prod_pi_hyperbolicPlane_iff_arf_eq_one`, and
  `QuadraticMap.exists_plane_decomposition`: normal-form plane decomposition for `Q.arf = 0` and
  `Q.arf = 1`.
* `QuadraticMap.equivalent_iff_finrank_eq_and_arf_eq`: classification of finite polar-nondegenerate
  quadratic spaces over `𝔽₂` by `finrank` and `arf`.
* `QuadraticMap.arf_eq_zero_iff_exists_isTotallyIsotropic_orthogonal_eq` and
  `QuadraticMap.arf_eq_zero_iff_exists_isTotallyIsotropic_finrank_eq`: vanishing of `Q.arf` is
  equivalent to the existence of a `Q`-totally isotropic Lagrangian subspace.

## References

* C. Arf, *Untersuchungen über quadratische Formen in Körpern der Charakteristik 2 (Teil I)*,
  J. Reine Angew. Math. **183** (1941), 148–167.
* W. Browder, *Surgery on Simply-Connected Manifolds*, Ergebnisse der Mathematik und ihrer
  Grenzgebiete **65**, Springer-Verlag (1972), §III.1.
* L. Pyronneau, *Arf invariant*, §2.1 (Theorem 2.15).
-/

public section

/-! ### Model hyperbolic and anisotropic planes over `𝔽₂` -/

namespace TauCeti.Arf

open _root_.QuadraticMap

/-- The standard hyperbolic plane `Q(x₀, x₁) = x₀ * x₁` on `Fin 2 → ZMod 2`. -/
@[expose]
def hyperbolicPlane : QuadraticForm (ZMod 2) (Fin 2 → ZMod 2) :=
  QuadraticMap.proj (R := ZMod 2) (0 : Fin 2) (1 : Fin 2)

/-- Evaluating `TauCeti.Arf.hyperbolicPlane`. -/
@[simp]
theorem hyperbolicPlane_apply (x : Fin 2 → ZMod 2) : hyperbolicPlane x = x 0 * x 1 := by
  simp [hyperbolicPlane]

/-- Polar form of `TauCeti.Arf.hyperbolicPlane`. -/
@[simp]
theorem polar_hyperbolicPlane (x y : Fin 2 → ZMod 2) :
    polar hyperbolicPlane x y = x 0 * y 1 + x 1 * y 0 := by
  have h2 (z : ZMod 2) : z + z = 0 := CharTwo.add_self_eq_zero z
  calc polar hyperbolicPlane x y
      = (x 0 * x 1 + x 0 * x 1) + (y 0 * y 1 + y 0 * y 1) + (x 0 * y 1 + x 1 * y 0) := by
        simp only [polar, hyperbolicPlane_apply, Pi.add_apply, CharTwo.sub_eq_add]
        ring
    _ = x 0 * y 1 + x 1 * y 0 := by simp [h2]

/-- The standard anisotropic plane `Q(x₀, x₁) = x₀ ^ 2 + x₀ * x₁ + x₁ ^ 2` on `Fin 2 → ZMod 2`. -/
@[expose]
def anisotropicPlane : QuadraticForm (ZMod 2) (Fin 2 → ZMod 2) :=
  QuadraticMap.proj (R := ZMod 2) (0 : Fin 2) (0 : Fin 2) +
    QuadraticMap.proj (R := ZMod 2) (0 : Fin 2) (1 : Fin 2) +
    QuadraticMap.proj (R := ZMod 2) (1 : Fin 2) (1 : Fin 2)

/-- Evaluating `TauCeti.Arf.anisotropicPlane`. -/
@[simp]
theorem anisotropicPlane_apply (x : Fin 2 → ZMod 2) :
    anisotropicPlane x = x 0 ^ 2 + x 0 * x 1 + x 1 ^ 2 := by
  simp only [anisotropicPlane, add_apply, QuadraticMap.proj_apply]
  ring

/-- Polar form of `TauCeti.Arf.anisotropicPlane`: the diagonal squares cancel in characteristic two,
leaving the same alternating form `x₀ y₁ + x₁ y₀` as `hyperbolicPlane`. -/
@[simp]
theorem polar_anisotropicPlane (x y : Fin 2 → ZMod 2) :
    polar anisotropicPlane x y = x 0 * y 1 + x 1 * y 0 := by
  simp only [polar, anisotropicPlane_apply, Pi.add_apply, CharTwo.sub_eq_add, CharTwo.add_sq]
  have h2 (z : ZMod 2) : z + z = 0 := CharTwo.add_self_eq_zero z
  calc
    x 0 ^ 2 + y 0 ^ 2 + (x 0 + y 0) * (x 1 + y 1) + (x 1 ^ 2 + y 1 ^ 2) +
        (x 0 ^ 2 + x 0 * x 1 + x 1 ^ 2) + (y 0 ^ 2 + y 0 * y 1 + y 1 ^ 2) =
      (x 0 ^ 2 + x 0 ^ 2) + (y 0 ^ 2 + y 0 ^ 2) + (x 1 ^ 2 + x 1 ^ 2) +
        (y 1 ^ 2 + y 1 ^ 2) + (x 0 * x 1 + x 0 * x 1) + (y 0 * y 1 + y 0 * y 1) +
        (x 0 * y 1 + x 1 * y 0) := by ring
    _ = x 0 * y 1 + x 1 * y 0 := by simp [h2]

/-- The polar bilinear form of `TauCeti.Arf.hyperbolicPlane` is nondegenerate. -/
theorem nondegenerate_polarBilin_hyperbolicPlane :
    hyperbolicPlane.polarBilin.Nondegenerate := by
  have hrefl : hyperbolicPlane.polarBilin.IsRefl := fun x y h ↦ by simpa [polar_comm] using h
  rw [LinearMap.IsRefl.nondegenerate_iff_separatingLeft hrefl]
  intro x hx
  have h0 : x 0 = 0 := by simpa using hx ![0, 1]
  have h1 : x 1 = 0 := by simpa using hx ![1, 0]
  ext i
  fin_cases i <;> assumption

/-- `TauCeti.Arf.hyperbolicPlane` is nondegenerate as a quadratic form. -/
theorem nondegenerate_hyperbolicPlane : hyperbolicPlane.Nondegenerate :=
  QuadraticMap.nondegenerate_of_ker_polarBilin_eq_bot <|
    LinearMap.separatingLeft_iff_ker_eq_bot.mp nondegenerate_polarBilin_hyperbolicPlane.1

/-- The polar bilinear form of `TauCeti.Arf.anisotropicPlane` is nondegenerate. -/
theorem nondegenerate_polarBilin_anisotropicPlane :
    anisotropicPlane.polarBilin.Nondegenerate := by
  have hpol : anisotropicPlane.polarBilin = hyperbolicPlane.polarBilin := by
    ext x y
    simp
  rw [hpol]
  exact nondegenerate_polarBilin_hyperbolicPlane

/-- `TauCeti.Arf.anisotropicPlane` is nondegenerate as a quadratic form. -/
theorem nondegenerate_anisotropicPlane : anisotropicPlane.Nondegenerate :=
  QuadraticMap.nondegenerate_of_ker_polarBilin_eq_bot <|
    LinearMap.separatingLeft_iff_ker_eq_bot.mp nondegenerate_polarBilin_anisotropicPlane.1

/-- `TauCeti.Arf.anisotropicPlane` has no nonzero isotropic vector. -/
theorem anisotropic_anisotropicPlane : anisotropicPlane.Anisotropic := by
  intro x hx
  have key : ∀ a b : ZMod 2, a ^ 2 + a * b + b ^ 2 = 0 → a = 0 ∧ b = 0 := by decide
  obtain ⟨hx0, hx1⟩ := key (x 0) (x 1) (by simpa using hx)
  ext i
  fin_cases i
  · exact hx0
  · exact hx1

/-- `TauCeti.Arf.hyperbolicPlane` is not anisotropic (`![1, 0]` is a nonzero zero). -/
theorem not_anisotropic_hyperbolicPlane : ¬ hyperbolicPlane.Anisotropic := by
  intro h
  have hzero := h ![1, 0] (by simp)
  exact one_ne_zero (congrFun hzero 0)

/-- The standard basis vector `![1, 0]` spans a one-dimensional totally isotropic subspace of
`TauCeti.Arf.hyperbolicPlane`. -/
theorem isTotallyIsotropic_span_hyperbolicPlane :
    hyperbolicPlane.IsTotallyIsotropic (ZMod 2 ∙ (![1, 0] : Fin 2 → ZMod 2)) := by
  simp

private noncomputable def planeSymplecticBasis :
    Module.Basis (Fin 1 ⊕ Fin 1) (ZMod 2) (Fin 2 → ZMod 2) :=
  (Pi.basisFun (ZMod 2) (Fin 2)).reindex
    { toFun := fun i ↦ if i = 0 then Sum.inl 0 else Sum.inr 0
      invFun := Sum.elim (fun _ ↦ 0) (fun _ ↦ 1)
      left_inv := fun i ↦ by fin_cases i <;> rfl
      right_inv := fun x ↦ by rcases x with i | i <;> fin_cases i <;> rfl }

/-- `TauCeti.Arf.hyperbolicPlane` has Arf invariant `0`. -/
@[simp]
theorem arf_hyperbolicPlane : hyperbolicPlane.arf = 0 := by
  have hb : LinearMap.BilinForm.toMatrix planeSymplecticBasis hyperbolicPlane.polarBilin =
      Matrix.J (Fin 1) (ZMod 2) := by
    refine (_root_.QuadraticMap.toMatrix_polarBilin_eq_J_iff (Q := hyperbolicPlane)).mpr
      ⟨fun i j ↦ ?_, fun i j ↦ ?_, fun i j ↦ ?_⟩ <;>
      fin_cases i <;> fin_cases j <;> simp [planeSymplecticBasis]
  rw [_root_.QuadraticMap.arf_eq_sum_of_toMatrix_polarBilin_eq_J hb]
  simp [planeSymplecticBasis]

/-- `TauCeti.Arf.anisotropicPlane` has Arf invariant `1`. -/
@[simp]
theorem arf_anisotropicPlane : anisotropicPlane.arf = 1 := by
  have hb : LinearMap.BilinForm.toMatrix planeSymplecticBasis anisotropicPlane.polarBilin =
      Matrix.J (Fin 1) (ZMod 2) := by
    refine (_root_.QuadraticMap.toMatrix_polarBilin_eq_J_iff (Q := anisotropicPlane)).mpr
      ⟨fun i j ↦ ?_, fun i j ↦ ?_, fun i j ↦ ?_⟩
    · fin_cases i; fin_cases j; exact anisotropicPlane.polar_self_eq_zero _
    · fin_cases i; fin_cases j; exact anisotropicPlane.polar_self_eq_zero _
    · fin_cases i; fin_cases j; simp [planeSymplecticBasis]
  rw [_root_.QuadraticMap.arf_eq_sum_of_toMatrix_polarBilin_eq_J hb]
  simp [planeSymplecticBasis]

/-- Gauss sum of `TauCeti.Arf.hyperbolicPlane`: `3 - 1 = 2`. -/
theorem sum_neg_one_pow_hyperbolicPlane :
    ∑ v : Fin 2 → ZMod 2, (-1 : ℤ) ^ (hyperbolicPlane v).val = 2 := by
  have hdim : Module.finrank (ZMod 2) (Fin 2 → ZMod 2) = 2 * 1 := by simp
  rw [_root_.QuadraticMap.sum_neg_one_pow_val_apply_of_finrank_eq_two_mul
    nondegenerate_polarBilin_hyperbolicPlane hdim, arf_hyperbolicPlane]
  decide

/-- Gauss sum of `TauCeti.Arf.anisotropicPlane`: `1 - 3 = -2`. -/
theorem sum_neg_one_pow_anisotropicPlane :
    ∑ v : Fin 2 → ZMod 2, (-1 : ℤ) ^ (anisotropicPlane v).val = -2 := by
  have hdim : Module.finrank (ZMod 2) (Fin 2 → ZMod 2) = 2 * 1 := by simp
  rw [_root_.QuadraticMap.sum_neg_one_pow_val_apply_of_finrank_eq_two_mul
    nondegenerate_polarBilin_anisotropicPlane hdim, arf_anisotropicPlane]
  decide

/-- `TauCeti.Arf.hyperbolicPlane` has `3` isotropic vectors. -/
theorem card_hyperbolicPlane_eq_zero :
    Fintype.card {v : Fin 2 → ZMod 2 // hyperbolicPlane v = 0} = 3 := by
  have hdim : Module.finrank (ZMod 2) (Fin 2 → ZMod 2) = 2 * 1 := by simp
  have h := _root_.QuadraticMap.card_apply_eq_zero_of_finrank_eq_two_mul
    nondegenerate_polarBilin_hyperbolicPlane hdim le_rfl
  rw [arf_hyperbolicPlane] at h
  have hval : (-1 : ℤ) ^ (0 : ZMod 2).val = 1 := by decide
  rw [hval] at h
  omega

/-- `TauCeti.Arf.anisotropicPlane` has `1` isotropic vector (`0`). -/
theorem card_anisotropicPlane_eq_zero :
    Fintype.card {v : Fin 2 → ZMod 2 // anisotropicPlane v = 0} = 1 := by
  have hdim : Module.finrank (ZMod 2) (Fin 2 → ZMod 2) = 2 * 1 := by simp
  have h := _root_.QuadraticMap.card_apply_eq_zero_of_finrank_eq_two_mul
    nondegenerate_polarBilin_anisotropicPlane hdim le_rfl
  rw [arf_anisotropicPlane] at h
  have hval : (-1 : ℤ) ^ (1 : ZMod 2).val = -1 := by decide
  rw [hval] at h
  omega

/-- Explicit computable isometry equivalence between the orthogonal sum of two anisotropic planes
and the orthogonal sum of two hyperbolic planes over `𝔽₂`. -/
@[expose]
def anisotropicProdAnisotropicEquiv :
    (anisotropicPlane.prod anisotropicPlane).IsometryEquiv
      (hyperbolicPlane.prod hyperbolicPlane) where
  toFun p :=
    (![p.1 0 + p.2 1, p.1 1 + p.2 1],
      ![p.1 0 + p.1 1 + p.2 0 + p.2 1, p.1 0 + p.1 1 + p.2 0])
  invFun q :=
    (![q.1 0 + q.2 0 + q.2 1, q.1 1 + q.2 0 + q.2 1],
      ![q.1 0 + q.1 1 + q.2 1, q.2 0 + q.2 1])
  map_add' p q := by
    ext i <;> fin_cases i <;> simp <;> ring
  map_smul' c p := by
    ext i <;> fin_cases i <;> simp <;> ring
  left_inv := by decide
  right_inv := by decide
  map_app' := by decide

/-- Forward action of `TauCeti.Arf.anisotropicProdAnisotropicEquiv`. -/
@[simp]
theorem anisotropicProdAnisotropicEquiv_apply (p : (Fin 2 → ZMod 2) × (Fin 2 → ZMod 2)) :
    anisotropicProdAnisotropicEquiv p =
      (![p.1 0 + p.2 1, p.1 1 + p.2 1],
        ![p.1 0 + p.1 1 + p.2 0 + p.2 1, p.1 0 + p.1 1 + p.2 0]) :=
  rfl

/-- Inverse action of `TauCeti.Arf.anisotropicProdAnisotropicEquiv`. -/
@[simp]
theorem anisotropicProdAnisotropicEquiv_symm_apply (q : (Fin 2 → ZMod 2) × (Fin 2 → ZMod 2)) :
    anisotropicProdAnisotropicEquiv.symm q =
      (![q.1 0 + q.2 0 + q.2 1, q.1 1 + q.2 0 + q.2 1],
        ![q.1 0 + q.1 1 + q.2 1, q.2 0 + q.2 1]) :=
  rfl

/-- The diagonal submodule `{(x, x) | x : Fin 2 → ZMod 2}` inside the four-dimensional space of two
copies of `Fin 2 → ZMod 2`. -/
@[expose]
def diagonalSubmodule : Submodule (ZMod 2) ((Fin 2 → ZMod 2) × (Fin 2 → ZMod 2)) :=
  LinearMap.range (LinearMap.id.prod LinearMap.id)

/-- The diagonal submodule is totally isotropic for `anisotropicPlane.prod anisotropicPlane`. -/
theorem isTotallyIsotropic_diagonalSubmodule :
    (anisotropicPlane.prod anisotropicPlane).IsTotallyIsotropic diagonalSubmodule := by
  rw [_root_.QuadraticMap.isTotallyIsotropic_iff]
  rintro _ ⟨x, rfl⟩
  simp [CharTwo.add_self_eq_zero]

/-- The diagonal submodule of `(Fin 2 → ZMod 2) × (Fin 2 → ZMod 2)` has dimension `2`. -/
@[simp]
theorem finrank_diagonalSubmodule : Module.finrank (ZMod 2) diagonalSubmodule = 2 := by
  have hinj : Function.Injective
      (LinearMap.id.prod LinearMap.id :
        (Fin 2 → ZMod 2) →ₗ[ZMod 2] (Fin 2 → ZMod 2) × (Fin 2 → ZMod 2)) :=
    fun x y h ↦ congrArg Prod.fst h
  rw [diagonalSubmodule, ← (LinearEquiv.ofInjective _ hinj).finrank_eq]
  simp

/-- The diagonal submodule is a Lagrangian (`U^⊥ = U`) for
`anisotropicPlane.prod anisotropicPlane`. -/
theorem orthogonal_diagonalSubmodule :
    LinearMap.BilinForm.orthogonal (anisotropicPlane.prod anisotropicPlane).polarBilin
      diagonalSubmodule = diagonalSubmodule := by
  have hnd : (anisotropicPlane.prod anisotropicPlane).polarBilin.Nondegenerate :=
    _root_.QuadraticMap.nondegenerate_polarBilin_prod_iff.mpr
      ⟨nondegenerate_polarBilin_anisotropicPlane, nondegenerate_polarBilin_anisotropicPlane⟩
  exact (_root_.QuadraticMap.IsTotallyIsotropic.orthogonal_polarBilin_eq_self_iff
    (Q := (anisotropicPlane.prod anisotropicPlane : QuadraticForm (ZMod 2) _))
    isTotallyIsotropic_diagonalSubmodule hnd).mpr (by simp)

end TauCeti.Arf

/-! ### Plane decomposition, classification by dimension and Arf, and Lagrangian criterion -/

namespace QuadraticMap

section Classification

open TauCeti.Arf

private theorem zmod2_cases : ∀ c : ZMod 2, c = 0 ∨ c = 1 := by decide

/-- A two-dimensional polar-nondegenerate space over `𝔽₂` with `Q.arf = 0` is isometric to
`TauCeti.Arf.hyperbolicPlane`. -/
private theorem equivalent_hyperbolicPlane_of_arf_eq_zero {V : Type*} [AddCommGroup V]
    [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V] {Q : QuadraticForm (ZMod 2) V}
    (hQ : Q.polarBilin.Nondegenerate) (hdim : Module.finrank (ZMod 2) V = 2) (harf : Q.arf = 0) :
    Q.Equivalent hyperbolicPlane := by
  have hm : Module.finrank (ZMod 2) V / 2 = 1 := by omega
  obtain ⟨b, hb⟩ := exists_basis_toMatrix_polarBilin_eq_J hQ
  obtain ⟨_, _, hlr⟩ := (toMatrix_polarBilin_eq_J_iff (Q := Q)).mp hb
  have huniv : (Finset.univ : Finset (Fin (Module.finrank (ZMod 2) V / 2))) =
      {⟨0, by omega⟩} := by
    ext i
    simp only [Finset.mem_univ, Finset.mem_singleton, true_iff]
    ext
    omega
  have hmul : Q (b (.inl ⟨0, by omega⟩)) * Q (b (.inr ⟨0, by omega⟩)) = 0 := by
    have hsum := (arf_eq_sum_of_toMatrix_polarBilin_eq_J hb).symm.trans harf
    rwa [huniv, Finset.sum_singleton] at hsum
  set a := b (.inl ⟨0, by omega⟩)
  set c := b (.inr ⟨0, by omega⟩)
  have hpol_ac : polar Q a c = 1 := by simpa [a, c] using hlr ⟨0, by omega⟩ ⟨0, by omega⟩
  -- Pick a hyperbolic pair `(u, w)` with `Q u = 0`, `Q w = 0`, and `polar Q u w = 1`.
  obtain ⟨u, w, hu, hw, huw⟩ : ∃ u w : V, Q u = 0 ∧ Q w = 0 ∧ polar Q u w = 1 := by
    rcases mul_eq_zero.mp hmul with ha0 | hc0
    · refine ⟨a, c + Q c • a, ha0, ?_, ?_⟩
      · simp [QuadraticMap.map_add Q, QuadraticMap.map_smul, ha0, polar_comm Q c a, hpol_ac,
          CharTwo.add_self_eq_zero]
      · simp [hpol_ac, Q.polar_self_eq_zero]
    · refine ⟨c, a + Q a • c, hc0, ?_, ?_⟩
      · simp [QuadraticMap.map_add Q, QuadraticMap.map_smul, hc0, hpol_ac,
          CharTwo.add_self_eq_zero]
      · simp [polar_comm Q c a, hpol_ac, Q.polar_self_eq_zero]
  let d : Fin 2 → V := ![u, w]
  have hli : LinearIndependent (ZMod 2) d := by
    apply LinearMap.BilinForm.linearIndependent_of_det_ne_zero (B := Q.polarBilin)
    rw [Matrix.det_fin_two]
    simp [d, Q.polar_self_eq_zero, huw, polar_comm Q w u]
  let b₂ := basisOfLinearIndependentOfCardEqFinrank hli (by simp [hdim])
  have hb₂ : ⇑b₂ = d := coe_basisOfLinearIndependentOfCardEqFinrank hli (by simp [hdim])
  refine ⟨({ toLinearEquiv := b₂.equivFun.symm
             map_app' := fun x ↦ ?_ } : hyperbolicPlane.IsometryEquiv Q).symm⟩
  have hx : b₂.equivFun.symm x = x 0 • u + x 1 • w := by
    simp [Module.Basis.equivFun_symm_apply, Fin.sum_univ_two, hb₂, d]
  change Q (b₂.equivFun.symm x) = hyperbolicPlane x
  rw [hx, QuadraticMap.map_add Q, QuadraticMap.map_smul, QuadraticMap.map_smul, hu, hw,
    polar_smul_left, polar_smul_right, huw]
  simp [smul_eq_mul]

/-- A two-dimensional polar-nondegenerate space over `𝔽₂` with `Q.arf = 1` is isometric to
`TauCeti.Arf.anisotropicPlane`. -/
private theorem equivalent_anisotropicPlane_of_arf_eq_one {V : Type*} [AddCommGroup V]
    [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V] {Q : QuadraticForm (ZMod 2) V}
    (hQ : Q.polarBilin.Nondegenerate) (hdim : Module.finrank (ZMod 2) V = 2) (harf : Q.arf = 1) :
    Q.Equivalent anisotropicPlane := by
  have hm : Module.finrank (ZMod 2) V / 2 = 1 := by omega
  obtain ⟨b, hb⟩ := exists_basis_toMatrix_polarBilin_eq_J hQ
  obtain ⟨_, _, hlr⟩ := (toMatrix_polarBilin_eq_J_iff (Q := Q)).mp hb
  have huniv : (Finset.univ : Finset (Fin (Module.finrank (ZMod 2) V / 2))) =
      {⟨0, by omega⟩} := by
    ext i
    simp only [Finset.mem_univ, Finset.mem_singleton, true_iff]
    ext
    omega
  have hmul : Q (b (.inl ⟨0, by omega⟩)) * Q (b (.inr ⟨0, by omega⟩)) = 1 := by
    have hsum := (arf_eq_sum_of_toMatrix_polarBilin_eq_J hb).symm.trans harf
    rwa [huniv, Finset.sum_singleton] at hsum
  set a := b (.inl ⟨0, by omega⟩)
  set c := b (.inr ⟨0, by omega⟩)
  have key : ∀ x y : ZMod 2, x * y = 1 → x = 1 ∧ y = 1 := by decide
  obtain ⟨ha1, hc1⟩ := key (Q a) (Q c) hmul
  have hpol_ac : polar Q a c = 1 := by simpa [a, c] using hlr ⟨0, by omega⟩ ⟨0, by omega⟩
  let d : Fin 2 → V := ![a, c]
  have hli : LinearIndependent (ZMod 2) d := by
    apply LinearMap.BilinForm.linearIndependent_of_det_ne_zero (B := Q.polarBilin)
    rw [Matrix.det_fin_two]
    simp [d, Q.polar_self_eq_zero, hpol_ac, polar_comm Q c a]
  let b₂ := basisOfLinearIndependentOfCardEqFinrank hli (by simp [hdim])
  have hb₂ : ⇑b₂ = d := coe_basisOfLinearIndependentOfCardEqFinrank hli (by simp [hdim])
  refine ⟨({ toLinearEquiv := b₂.equivFun.symm
             map_app' := fun x ↦ ?_ } : anisotropicPlane.IsometryEquiv Q).symm⟩
  have hx : b₂.equivFun.symm x = x 0 • a + x 1 • c := by
    simp [Module.Basis.equivFun_symm_apply, Fin.sum_univ_two, hb₂, d]
  change Q (b₂.equivFun.symm x) = anisotropicPlane x
  rw [hx, QuadraticMap.map_add Q, QuadraticMap.map_smul, QuadraticMap.map_smul, ha1, hc1,
    polar_smul_left, polar_smul_right, hpol_ac, anisotropicPlane_apply]
  simp only [smul_eq_mul, mul_one]
  ring

/-- A two-dimensional polar-nondegenerate space over `𝔽₂` is isometric to `hyperbolicPlane` if and
only if its Arf invariant is `0`. -/
theorem equivalent_hyperbolicPlane_iff_arf_eq_zero {V : Type*} [AddCommGroup V]
    [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V] {Q : QuadraticForm (ZMod 2) V}
    (hQ : Q.polarBilin.Nondegenerate) (hdim : Module.finrank (ZMod 2) V = 2) :
    Q.Equivalent hyperbolicPlane ↔ Q.arf = 0 :=
  ⟨fun h ↦ h.arf_eq.trans arf_hyperbolicPlane, equivalent_hyperbolicPlane_of_arf_eq_zero hQ hdim⟩

/-- A two-dimensional polar-nondegenerate space over `𝔽₂` is isometric to `anisotropicPlane` if and
only if its Arf invariant is `1`. -/
theorem equivalent_anisotropicPlane_iff_arf_eq_one {V : Type*} [AddCommGroup V]
    [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V] {Q : QuadraticForm (ZMod 2) V}
    (hQ : Q.polarBilin.Nondegenerate) (hdim : Module.finrank (ZMod 2) V = 2) :
    Q.Equivalent anisotropicPlane ↔ Q.arf = 1 :=
  ⟨fun h ↦ h.arf_eq.trans arf_anisotropicPlane, equivalent_anisotropicPlane_of_arf_eq_one hQ hdim⟩

/-- A two-dimensional polar-nondegenerate quadratic form over `𝔽₂` is anisotropic if and only if
its Arf invariant is `1`. -/
theorem anisotropic_iff_arf_eq_one_of_finrank_eq_two {V : Type*} [AddCommGroup V]
    [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V] {Q : QuadraticForm (ZMod 2) V}
    (hQ : Q.polarBilin.Nondegenerate) (hdim : Module.finrank (ZMod 2) V = 2) :
    Q.Anisotropic ↔ Q.arf = 1 := by
  refine ⟨fun haniso ↦ ?_, fun harf ↦
    (equivalent_anisotropicPlane_of_arf_eq_one hQ hdim harf).anisotropic_iff.mpr
      anisotropic_anisotropicPlane⟩
  rcases zmod2_cases Q.arf with h0 | h1
  · exact False.elim (not_anisotropic_hyperbolicPlane
      ((equivalent_hyperbolicPlane_of_arf_eq_zero hQ hdim h0).anisotropic_iff.mp haniso))
  · exact h1

/-- Express any `2 * m`-dimensional polar-nondegenerate space as an orthogonal sum of `m`
coordinate planes on `Fin 2 → ZMod 2`. -/
private theorem exists_equivalent_pi_planes {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
    [FiniteDimensional (ZMod 2) V] {Q : QuadraticForm (ZMod 2) V}
    (hQ : Q.polarBilin.Nondegenerate) {m : ℕ} (hm : Module.finrank (ZMod 2) V = 2 * m) :
    ∃ P : Fin m → QuadraticForm (ZMod 2) (Fin 2 → ZMod 2),
      (∀ i, (P i).polarBilin.Nondegenerate) ∧ Q.Equivalent (QuadraticMap.pi P) := by
  obtain ⟨b₀, hb₀⟩ := exists_basis_toMatrix_polarBilin_eq_J hQ
  have hm' : Module.finrank (ZMod 2) V / 2 = m := by omega
  let b : Module.Basis (Fin m ⊕ Fin m) (ZMod 2) V :=
    b₀.reindex ((finCongr hm').sumCongr (finCongr hm'))
  have hb : LinearMap.BilinForm.toMatrix b Q.polarBilin = Matrix.J (Fin m) (ZMod 2) := by
    obtain ⟨hll, hrr, hlr⟩ := (toMatrix_polarBilin_eq_J_iff (Q := Q)).mp hb₀
    refine (toMatrix_polarBilin_eq_J_iff (Q := Q)).mpr
      ⟨fun i j ↦ by simpa [b] using hll _ _, fun i j ↦ by simpa [b] using hrr _ _,
        fun i j ↦ by simpa [b, Fin.ext_iff] using hlr (Fin.cast hm'.symm i) (Fin.cast hm'.symm j)⟩
  let φ : (Fin m → Fin 2 → ZMod 2) ≃ₗ[ZMod 2] (Fin m ⊕ Fin m → ZMod 2) :=
    { toFun g := Sum.elim (fun i ↦ g i 0) (fun i ↦ g i 1)
      invFun c i := ![c (Sum.inl i), c (Sum.inr i)]
      map_add' _ _ := by ext (i | i) <;> rfl
      map_smul' _ _ := by ext (i | i) <;> rfl
      left_inv g := by ext i j; fin_cases j <;> rfl
      right_inv c := by ext (i | i) <;> rfl }
  let P (i : Fin m) : QuadraticForm (ZMod 2) (Fin 2 → ZMod 2) :=
    Q (b (.inl i)) • QuadraticMap.proj 0 0 + QuadraticMap.proj 0 1 +
      Q (b (.inr i)) • QuadraticMap.proj 1 1
  have hequiv : (QuadraticMap.pi P).IsometryEquiv Q :=
    { toLinearEquiv := φ.trans b.equivFun.symm
      map_app' g := by
        change Q (b.equivFun.symm (φ g)) = QuadraticMap.pi P g
        rw [apply_equivFun_symm_of_toMatrix_polarBilin_eq_J hb, QuadraticMap.pi_apply]
        refine Finset.sum_congr rfl fun i _ ↦ ?_
        simp only [φ, LinearEquiv.coe_mk, LinearMap.coe_mk, AddHom.coe_mk, Sum.elim_inl,
          Sum.elim_inr, P, add_apply, smul_apply, QuadraticMap.proj_apply, smul_eq_mul]
        ring }
  have hndP : (QuadraticMap.pi P).polarBilin.Nondegenerate := by
    have hrefl : (QuadraticMap.pi P).polarBilin.IsRefl := fun x y h ↦ by simpa [polar_comm] using h
    rw [LinearMap.IsRefl.nondegenerate_iff_separatingLeft hrefl]
    intro g hg
    apply hequiv.injective
    rw [map_zero]
    refine hQ.1 (hequiv g) fun v ↦ ?_
    have hv := hg (hequiv.symm v)
    rw [polarBilin_apply_apply] at hv ⊢
    rw [← hequiv.polar_apply, hequiv.apply_symm_apply] at hv
    exact hv
  exact ⟨P, nondegenerate_polarBilin_pi_iff.mp hndP, ⟨hequiv.symm⟩⟩

private def anisotropicProdAnisotropicProdPiEquiv (d : ℕ) :
    (anisotropicPlane.prod
      (anisotropicPlane.prod (QuadraticMap.pi fun _ : Fin d ↦ hyperbolicPlane))).IsometryEquiv
      (QuadraticMap.pi fun _ : Fin (d + 2) ↦ hyperbolicPlane) :=
  let Hpi := QuadraticMap.pi fun _ : Fin d ↦ hyperbolicPlane
  (QuadraticMap.IsometryEquiv.prodAssoc anisotropicPlane anisotropicPlane Hpi).symm
    |>.trans (anisotropicProdAnisotropicEquiv.prod (QuadraticMap.IsometryEquiv.refl Hpi))
    |>.trans (QuadraticMap.IsometryEquiv.prodAssoc hyperbolicPlane hyperbolicPlane Hpi)
    |>.trans ((QuadraticMap.IsometryEquiv.refl hyperbolicPlane).prod
      (QuadraticMap.IsometryEquiv.consPi fun _ : Fin (d + 1) ↦ hyperbolicPlane))
    |>.trans (QuadraticMap.IsometryEquiv.consPi fun _ : Fin (d + 2) ↦ hyperbolicPlane)

private def hyperbolicProdAnisotropicProdPiEquiv (d : ℕ) :
    (hyperbolicPlane.prod
      (anisotropicPlane.prod (QuadraticMap.pi fun _ : Fin d ↦ hyperbolicPlane))).IsometryEquiv
      (anisotropicPlane.prod (QuadraticMap.pi fun _ : Fin (d + 1) ↦ hyperbolicPlane)) :=
  let Hpi := QuadraticMap.pi fun _ : Fin d ↦ hyperbolicPlane
  (QuadraticMap.IsometryEquiv.prodLeftComm hyperbolicPlane anisotropicPlane Hpi).trans
    ((QuadraticMap.IsometryEquiv.refl anisotropicPlane).prod
      (QuadraticMap.IsometryEquiv.consPi fun _ : Fin (d + 1) ↦ hyperbolicPlane))

/-- Simultaneous induction establishing the normal-form plane decomposition for both values of
`Q.arf ∈ {0, 1}`. -/
private theorem plane_normal_form_aux :
    ∀ m : ℕ,
      (∀ (Q : QuadraticForm (ZMod 2) (Fin m → Fin 2 → ZMod 2)),
        Q.polarBilin.Nondegenerate → Q.arf = 0 →
        Q.Equivalent (QuadraticMap.pi fun _ : Fin m ↦ hyperbolicPlane)) ∧
      (∀ k : ℕ, m = k + 1 → ∀ (Q : QuadraticForm (ZMod 2) (Fin m → Fin 2 → ZMod 2)),
        Q.polarBilin.Nondegenerate → Q.arf = 1 →
        Q.Equivalent
          (anisotropicPlane.prod (QuadraticMap.pi fun _ : Fin k ↦ hyperbolicPlane))) := by
  intro m
  induction m with
  | zero =>
    refine ⟨fun Q _ _ ↦ ?_, fun k hk ↦ by omega⟩
    refine ⟨{ toLinearEquiv := LinearEquiv.refl _ _
              map_app' := fun x ↦ ?_ }⟩
    change (QuadraticMap.pi fun _ : Fin 0 ↦ hyperbolicPlane) x = Q x
    rw [Subsingleton.elim x 0, map_zero, map_zero]
  | succ m ih =>
    have step0 : ∀ (P : Fin (m + 1) → QuadraticForm (ZMod 2) (Fin 2 → ZMod 2)),
        (∀ i, (P i).polarBilin.Nondegenerate) →
        ((QuadraticMap.pi P).arf = 0 →
          (QuadraticMap.pi P).Equivalent
            (QuadraticMap.pi fun _ : Fin (m + 1) ↦ hyperbolicPlane)) ∧
        ((QuadraticMap.pi P).arf = 1 →
          (QuadraticMap.pi P).Equivalent
            (anisotropicPlane.prod (QuadraticMap.pi fun _ : Fin m ↦ hyperbolicPlane))) := by
      intro P hP
      let P' : Fin m → QuadraticForm (ZMod 2) (Fin 2 → ZMod 2) := fun i ↦ P i.succ
      have hcons : (QuadraticMap.pi P).Equivalent ((P 0).prod (QuadraticMap.pi P')) :=
        ⟨(QuadraticMap.IsometryEquiv.consPi P).symm⟩
      have hnd' : (QuadraticMap.pi P').polarBilin.Nondegenerate :=
        nondegenerate_polarBilin_pi_iff.mpr fun i ↦ hP i.succ
      have harf_split : (QuadraticMap.pi P).arf = (P 0).arf + (QuadraticMap.pi P').arf := by
        rw [hcons.arf_eq, arf_prod (hP 0) hnd']
      have hdim0 : Module.finrank (ZMod 2) (Fin 2 → ZMod 2) = 2 := by simp
      rcases m with _ | d
      · have harf' : (QuadraticMap.pi P').arf = 0 := arf_of_subsingleton _
        obtain ⟨e'⟩ := ih.1 (QuadraticMap.pi P') hnd' harf'
        refine ⟨fun h0 ↦ ?_, fun h1 ↦ ?_⟩
        · have hP0 : (P 0).arf = 0 := by simpa [harf'] using harf_split.symm.trans h0
          obtain ⟨e₀⟩ := equivalent_hyperbolicPlane_of_arf_eq_zero (hP 0) hdim0 hP0
          exact hcons.trans ⟨(e₀.prod e').trans
            (QuadraticMap.IsometryEquiv.consPi fun _ : Fin 1 ↦ hyperbolicPlane)⟩
        · have hP0 : (P 0).arf = 1 := by simpa [harf'] using harf_split.symm.trans h1
          obtain ⟨e₀⟩ := equivalent_anisotropicPlane_of_arf_eq_one (hP 0) hdim0 hP0
          exact hcons.trans ⟨e₀.prod e'⟩
      · refine ⟨fun h0 ↦ ?_, fun h1 ↦ ?_⟩
        · have h_eq : (P 0).arf = (QuadraticMap.pi P').arf :=
            CharTwo.add_eq_zero.mp (harf_split.symm.trans h0)
          rcases zmod2_cases (P 0).arf with hP0 | hP0
          · obtain ⟨e₀⟩ := equivalent_hyperbolicPlane_of_arf_eq_zero (hP 0) hdim0 hP0
            obtain ⟨e'⟩ := ih.1 (QuadraticMap.pi P') hnd' (h_eq.symm.trans hP0)
            exact hcons.trans ⟨(e₀.prod e').trans
              (QuadraticMap.IsometryEquiv.consPi fun _ : Fin (d + 2) ↦ hyperbolicPlane)⟩
          · obtain ⟨e₀⟩ := equivalent_anisotropicPlane_of_arf_eq_one (hP 0) hdim0 hP0
            obtain ⟨e'⟩ := ih.2 d rfl (QuadraticMap.pi P') hnd' (h_eq.symm.trans hP0)
            exact hcons.trans ⟨(e₀.prod e').trans (anisotropicProdAnisotropicProdPiEquiv d)⟩
        · rcases zmod2_cases (P 0).arf with hP0 | hP0
          · have hP' : (QuadraticMap.pi P').arf = 1 := by
              simpa [hP0] using harf_split.symm.trans h1
            obtain ⟨e₀⟩ := equivalent_hyperbolicPlane_of_arf_eq_zero (hP 0) hdim0 hP0
            obtain ⟨e'⟩ := ih.2 d rfl (QuadraticMap.pi P') hnd' hP'
            exact hcons.trans ⟨(e₀.prod e').trans (hyperbolicProdAnisotropicProdPiEquiv d)⟩
          · have hP' : (QuadraticMap.pi P').arf = 0 := by
              simpa [hP0] using harf_split.symm.trans h1
            obtain ⟨e₀⟩ := equivalent_anisotropicPlane_of_arf_eq_one (hP 0) hdim0 hP0
            obtain ⟨e'⟩ := ih.1 (QuadraticMap.pi P') hnd' hP'
            exact hcons.trans ⟨e₀.prod e'⟩
    have hfinrank : Module.finrank (ZMod 2) (Fin (m + 1) → Fin 2 → ZMod 2) = 2 * (m + 1) := by
      rw [Module.finrank_pi_fintype (ZMod 2)]
      simp
      ring
    refine ⟨fun Q hQ h0 ↦ ?_, fun k hk Q hQ h1 ↦ ?_⟩
    · obtain ⟨P, hP, heq⟩ := exists_equivalent_pi_planes hQ hfinrank
      exact heq.trans ((step0 P hP).1 (heq.symm.arf_eq.trans h0))
    · obtain rfl : m = k := by omega
      obtain ⟨P, hP, heq⟩ := exists_equivalent_pi_planes hQ hfinrank
      exact heq.trans ((step0 P hP).2 (heq.symm.arf_eq.trans h1))

/-- **Hyperbolic-plane decomposition.** A polar-nondegenerate quadratic space of dimension `2 * m`
over `𝔽₂` is isometric to the orthogonal sum of `m` hyperbolic planes if and only if `Q.arf = 0`. -/
theorem equivalent_pi_hyperbolicPlane_iff_arf_eq_zero {V : Type*} [AddCommGroup V]
    [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V] {Q : QuadraticForm (ZMod 2) V}
    (hQ : Q.polarBilin.Nondegenerate) {m : ℕ} (hm : Module.finrank (ZMod 2) V = 2 * m) :
    Q.Equivalent (QuadraticMap.pi fun _ : Fin m ↦ hyperbolicPlane) ↔ Q.arf = 0 := by
  refine ⟨fun h ↦ ?_, fun harf ↦ ?_⟩
  · rw [h.arf_eq, arf_pi fun _ ↦ nondegenerate_polarBilin_hyperbolicPlane]
    simp
  · obtain ⟨P, hP, heq⟩ := exists_equivalent_pi_planes hQ hm
    exact heq.trans
      ((plane_normal_form_aux m).1 (QuadraticMap.pi P)
        (nondegenerate_polarBilin_pi_iff.mpr hP) (heq.symm.arf_eq.trans harf))

/-- **Anisotropic-plus-hyperbolic plane decomposition.** A polar-nondegenerate quadratic space of
dimension `2 * (m + 1)` over `𝔽₂` is isometric to one anisotropic plane plus `m` hyperbolic planes
if and only if `Q.arf = 1`. -/
theorem equivalent_anisotropicPlane_prod_pi_hyperbolicPlane_iff_arf_eq_one {V : Type*}
    [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
    {Q : QuadraticForm (ZMod 2) V} (hQ : Q.polarBilin.Nondegenerate) {m : ℕ}
    (hm : Module.finrank (ZMod 2) V = 2 * (m + 1)) :
    Q.Equivalent (anisotropicPlane.prod (QuadraticMap.pi fun _ : Fin m ↦ hyperbolicPlane)) ↔
      Q.arf = 1 := by
  refine ⟨fun h ↦ ?_, fun harf ↦ ?_⟩
  · rw [h.arf_eq, arf_prod nondegenerate_polarBilin_anisotropicPlane
      (nondegenerate_polarBilin_pi_iff.mpr fun _ ↦ nondegenerate_polarBilin_hyperbolicPlane),
      arf_anisotropicPlane, arf_pi fun _ ↦ nondegenerate_polarBilin_hyperbolicPlane]
    simp
  · obtain ⟨P, hP, heq⟩ := exists_equivalent_pi_planes hQ hm
    exact heq.trans
      ((plane_normal_form_aux (m + 1)).2 m rfl (QuadraticMap.pi P)
        (nondegenerate_polarBilin_pi_iff.mpr hP) (heq.symm.arf_eq.trans harf))

/-- **Normal-form dichotomy** for any finite-dimensional polar-nondegenerate quadratic space over
`𝔽₂`: either `Q.arf = 0` and `Q` splits into `finrank / 2` hyperbolic planes, or `Q.arf = 1`,
`1 ≤ finrank / 2`, and `Q` splits into one anisotropic plane and `finrank / 2 - 1` hyperbolic
planes. -/
theorem exists_plane_decomposition {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
    [FiniteDimensional (ZMod 2) V] {Q : QuadraticForm (ZMod 2) V}
    (hQ : Q.polarBilin.Nondegenerate) :
    (Q.arf = 0 ∧
        Q.Equivalent
          (QuadraticMap.pi fun _ : Fin (Module.finrank (ZMod 2) V / 2) ↦ hyperbolicPlane)) ∨
      (Q.arf = 1 ∧ 1 ≤ Module.finrank (ZMod 2) V / 2 ∧
        Q.Equivalent (anisotropicPlane.prod (QuadraticMap.pi
          fun _ : Fin (Module.finrank (ZMod 2) V / 2 - 1) ↦ hyperbolicPlane))) := by
  have hdim := (two_mul_finrank_div_two_of_nondegenerate_polarBilin hQ).symm
  rcases zmod2_cases Q.arf with harf | harf
  · exact Or.inl ⟨harf, (equivalent_pi_hyperbolicPlane_iff_arf_eq_zero hQ hdim).mpr harf⟩
  · right
    have hm1 : 1 ≤ Module.finrank (ZMod 2) V / 2 := by
      by_contra h0
      have hfin0 : Module.finrank (ZMod 2) V = 0 := by omega
      have : Subsingleton V := Module.finrank_zero_iff.mp hfin0
      exact zero_ne_one ((arf_of_subsingleton Q).symm.trans harf)
    have hdim' : Module.finrank (ZMod 2) V = 2 * ((Module.finrank (ZMod 2) V / 2 - 1) + 1) := by
      omega
    exact ⟨harf, hm1,
      (equivalent_anisotropicPlane_prod_pi_hyperbolicPlane_iff_arf_eq_one hQ hdim').mpr harf⟩

/-- **Arf's classification theorem over `𝔽₂`.** Two finite-dimensional polar-nondegenerate quadratic
spaces over `ZMod 2` are isometric if and only if they have the same dimension and the same Arf
invariant. -/
theorem equivalent_iff_finrank_eq_and_arf_eq {V₁ V₂ : Type*}
    [AddCommGroup V₁] [Module (ZMod 2) V₁] [FiniteDimensional (ZMod 2) V₁]
    [AddCommGroup V₂] [Module (ZMod 2) V₂] [FiniteDimensional (ZMod 2) V₂]
    {Q₁ : QuadraticForm (ZMod 2) V₁} {Q₂ : QuadraticForm (ZMod 2) V₂}
    (h₁ : Q₁.polarBilin.Nondegenerate) (h₂ : Q₂.polarBilin.Nondegenerate) :
    Q₁.Equivalent Q₂ ↔
      Module.finrank (ZMod 2) V₁ = Module.finrank (ZMod 2) V₂ ∧ Q₁.arf = Q₂.arf := by
  refine ⟨fun ⟨e⟩ ↦ ⟨e.toLinearEquiv.finrank_eq, e.arf_eq⟩, fun ⟨hdim, harf⟩ ↦ ?_⟩
  have heven₂ := two_mul_finrank_div_two_of_nondegenerate_polarBilin h₂
  rcases exists_plane_decomposition h₁ with ⟨ha₁, heq₁⟩ | ⟨ha₁, hm₁, heq₁⟩
  · have heq₂ := (equivalent_pi_hyperbolicPlane_iff_arf_eq_zero h₂ heven₂.symm).mpr
      (harf.symm.trans ha₁)
    rw [hdim] at heq₁
    exact heq₁.trans heq₂.symm
  · rw [hdim] at hm₁ heq₁
    have hdim₂ : Module.finrank (ZMod 2) V₂ =
        2 * ((Module.finrank (ZMod 2) V₂ / 2 - 1) + 1) := by omega
    have heq₂ := (equivalent_anisotropicPlane_prod_pi_hyperbolicPlane_iff_arf_eq_one h₂ hdim₂).mpr
      (harf.symm.trans ha₁)
    exact heq₁.trans heq₂.symm

/-! ### Totally isotropic Lagrangian criteria for vanishing Arf invariant -/

/-- **Lagrangian criterion for `Q.arf = 0`.** In a finite-dimensional polar-nondegenerate quadratic
space over `ZMod 2`, `Q.arf = 0` if and only if `V` contains a `Q`-totally isotropic subspace equal
to its own `Q.polarBilin`-orthogonal complement. -/
theorem arf_eq_zero_iff_exists_isTotallyIsotropic_orthogonal_eq {V : Type*}
    [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
    {Q : QuadraticForm (ZMod 2) V} (hQ : Q.polarBilin.Nondegenerate) :
    Q.arf = 0 ↔
      ∃ U : Submodule (ZMod 2) V,
        Q.IsTotallyIsotropic U ∧ LinearMap.BilinForm.orthogonal Q.polarBilin U = U := by
  refine ⟨fun harf ↦ ?_, fun ⟨U, hU, horth⟩ ↦ ?_⟩
  · set m := Module.finrank (ZMod 2) V / 2
    have hdim := (two_mul_finrank_div_two_of_nondegenerate_polarBilin hQ).symm
    obtain ⟨e⟩ := (equivalent_pi_hyperbolicPlane_iff_arf_eq_zero hQ hdim).mpr harf
    let ι : (Fin m → ZMod 2) →ₗ[ZMod 2] (Fin m → Fin 2 → ZMod 2) :=
      { toFun c i := ![c i, 0]
        map_add' _ _ := by ext i j; fin_cases j <;> simp
        map_smul' _ _ := by ext i j; fin_cases j <;> simp }
    have hι_inj : Function.Injective ι := fun c₁ c₂ h ↦ funext fun i ↦ by
      simpa [ι] using congrFun (congrFun h i) 0
    let U : Submodule (ZMod 2) V := (LinearMap.range ι).map e.symm.toLinearEquiv.toLinearMap
    have hU : Q.IsTotallyIsotropic U := by
      rw [isTotallyIsotropic_iff]
      rintro _ ⟨_, ⟨c, rfl⟩, rfl⟩
      simp [ι, QuadraticMap.pi_apply]
    have hfinU : Module.finrank (ZMod 2) U = m := by
      have heq : (Fin m → ZMod 2) ≃ₗ[ZMod 2] U :=
        (LinearEquiv.ofInjective ι hι_inj).trans
          (e.symm.toLinearEquiv.submoduleMap (LinearMap.range ι))
      simpa using heq.finrank_eq.symm
    exact ⟨U, hU, (hU.orthogonal_polarBilin_eq_self_iff hQ).mpr (by omega)⟩
  · obtain ⟨b, hb, _, hQinl, hQinr⟩ :=
      exists_hyperbolic_basis_of_isTotallyIsotropic hQ (Module.finBasis (ZMod 2) U) hU horth
    rw [arf_eq_sum_of_toMatrix_polarBilin_eq_J hb]
    simp [hQinl, hQinr]

/-- **Half-dimension criterion for `Q.arf = 0` (multiplicative form).** `Q.arf = 0` holds if and
only if `V` contains a `Q`-totally isotropic subspace `U` with `2 * finrank U = finrank V`. -/
theorem arf_eq_zero_iff_exists_isTotallyIsotropic_finrank_eq {V : Type*}
    [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
    {Q : QuadraticForm (ZMod 2) V} (hQ : Q.polarBilin.Nondegenerate) :
    Q.arf = 0 ↔
      ∃ U : Submodule (ZMod 2) V,
        Q.IsTotallyIsotropic U ∧ 2 * Module.finrank (ZMod 2) U = Module.finrank (ZMod 2) V := by
  rw [arf_eq_zero_iff_exists_isTotallyIsotropic_orthogonal_eq hQ]
  exact exists_congr fun U ↦ and_congr_right fun hU ↦ hU.orthogonal_polarBilin_eq_self_iff hQ

/-- **Half-dimension criterion for `Q.arf = 0` (quotient form).** `Q.arf = 0` holds if and only if
`V` contains a `Q`-totally isotropic subspace `U` of dimension `finrank (ZMod 2) V / 2`. -/
theorem arf_eq_zero_iff_exists_isTotallyIsotropic_finrank_eq_div_two {V : Type*}
    [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
    {Q : QuadraticForm (ZMod 2) V} (hQ : Q.polarBilin.Nondegenerate) :
    Q.arf = 0 ↔
      ∃ U : Submodule (ZMod 2) V,
        Q.IsTotallyIsotropic U ∧
          Module.finrank (ZMod 2) U = Module.finrank (ZMod 2) V / 2 := by
  have h2 := two_mul_finrank_div_two_of_nondegenerate_polarBilin hQ
  rw [arf_eq_zero_iff_exists_isTotallyIsotropic_finrank_eq hQ]
  exact exists_congr fun U ↦ and_congr_right fun _ ↦ ⟨by omega, by omega⟩

end Classification

end QuadraticMap
