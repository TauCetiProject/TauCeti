/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.Modules.Differentials.LocallyFreeQuotient.Spec
public import Mathlib.Algebra.DualNumber
public import Mathlib.RingTheory.Kaehler.Polynomial

/-!
# Checks for locally free quotients of the differentials of affine schemes

* For the affine plane `𝔸²_k = Spec k[x, y]` and `d = 1`, the two coordinate quotients
  `dx ↦ 1, dy ↦ 0` and `dx ↦ 0, dy ↦ 1` of `Ω_{𝔸²/k} = 𝒪 dx ⊕ 𝒪 dy` onto `𝒪` both witness the
  predicate, and they have the different kernels `𝒪 dy` and `𝒪 dx`: no morphism of sheaves carries
  the first quotient to the second. Here the smooth locus of dimension `1` is empty, and the
  uniqueness of locally free quotients of rank `d`, which assumes that the smooth locus of
  dimension `d` is dense, fails.
* For the dual numbers `X = Spec k[ε]/(ε²)` over a field `k` of characteristic `2`, `Ω_{X/k}` is
  free on `dε`: `a + bε ↦ b` is a derivation, so `dε ↦ 1` is a locally free quotient of rank `1`.
  The predicate records neither the dimension (`X` is zero-dimensional) nor reducedness.
-/

public section

open AlgebraicGeometry CategoryTheory TauCeti.AlgebraicGeometry KaehlerDifferential

namespace TauCeti.LocallyFreeQuotientAffineExample

universe u

noncomputable section

variable (k : Type u) [Field k]

/-- The coordinate ring `k[x, y]` of the affine plane. -/
abbrev planeRing : CommRingCat.{u} := .of (MvPolynomial (Fin 2) k)

/-- The quotient `Ω[k[x, y]⁄k] → k[x, y]` sending `d xⱼ` to `1` if `j = i` and to `0` otherwise:
the `i`-th coordinate in the basis `dx, dy`. -/
def coordinateQuotient (i : Fin 2) : Ω[planeRing k⁄k] →ₗ[planeRing k] (Fin 1 → planeRing k) :=
  LinearMap.pi fun _ ↦ (mvPolynomialBasis k (Fin 2)).coord i

/-- The coordinate quotients are surjective. -/
theorem coordinateQuotient_surjective (i : Fin 2) :
    Function.Surjective (coordinateQuotient k i) := fun v ↦
  ⟨v 0 • mvPolynomialBasis k (Fin 2) i, funext fun j ↦ by
    simp [coordinateQuotient, Subsingleton.elim j 0]⟩

-- **Check.** Each coordinate quotient witnesses the predicate for `𝔸²_k` and `d = 1`.
example (i : Fin 2) : HasLocallyFreeQuotientOfDifferentials k (Spec (planeRing k)) 1 :=
  hasLocallyFreeQuotientOfDifferentials_Spec_of_surjective k _ _
    (coordinateQuotient_surjective k i)

/-- `dy` lies in the kernel of the first coordinate quotient. -/
theorem dy_mem_ker_coordinateQuotient_zero :
    mvPolynomialBasis k (Fin 2) 1 ∈ LinearMap.ker (coordinateQuotient k 0) := by
  rw [LinearMap.mem_ker]
  funext j
  simp [coordinateQuotient]

/-- `dy` does not lie in the kernel of the second coordinate quotient. -/
theorem dy_notMem_ker_coordinateQuotient_one :
    mvPolynomialBasis k (Fin 2) 1 ∉ LinearMap.ker (coordinateQuotient k 1) := fun h ↦ by
  simpa [coordinateQuotient] using congrFun (LinearMap.mem_ker.mp h) 0

-- **Check.** The two coordinate quotients have different kernels.
example : LinearMap.ker (coordinateQuotient k 0) ≠ LinearMap.ker (coordinateQuotient k 1) :=
  fun h ↦ dy_notMem_ker_coordinateQuotient_one k (h ▸ dy_mem_ker_coordinateQuotient_zero k)

-- **Check.** No morphism of sheaves carries the first coordinate quotient to the second.
example : ¬ ∃ φ, differentialsSpecToTilde k _ (coordinateQuotient k 0) ≫ φ =
    differentialsSpecToTilde k _ (coordinateQuotient k 1) := by
  rintro ⟨φ, hφ⟩
  exact dy_notMem_ker_coordinateQuotient_one k
    (ker_le_ker_of_differentialsSpecToTilde_comp_eq k _ _ _ φ hφ
      (dy_mem_ker_coordinateQuotient_zero k))

/-- The ring `k[ε]/(ε²)` of dual numbers. -/
abbrev dualNumberRing : CommRingCat.{u} := .of (DualNumber k)

/-- In characteristic `2`, `a + bε ↦ b` is a `k`-derivation of `k[ε]/(ε²)`: the Leibniz rule
holds up to the term `2bb'ε`. -/
def dualNumberDerivation (h2 : (2 : k) = 0) : Derivation k (DualNumber k) (DualNumber k) where
  toFun x := TrivSqZeroExt.inl x.snd
  map_add' x y := by simp
  map_smul' c x := by ext <;> simp
  map_one_eq_zero' := by simp
  leibniz' x y := by
    ext
    · simp [mul_comm]
    · simp only [TrivSqZeroExt.snd_mul, TrivSqZeroExt.snd_inl, TrivSqZeroExt.fst_inl,
        smul_eq_mul, MulOpposite.smul_eq_mul_unop, MulOpposite.unop_op, TrivSqZeroExt.snd_add,
        LinearMap.coe_mk, AddHom.coe_mk]
      linear_combination (-(x.snd * y.snd)) * h2

/-- The derivation `a + bε ↦ b`. -/
@[simp]
lemma dualNumberDerivation_apply (h2 : (2 : k) = 0) (x : DualNumber k) :
    dualNumberDerivation k h2 x = TrivSqZeroExt.inl x.snd :=
  (rfl)

/-- In characteristic `2`, the map `Ω[k[ε]/(ε²)⁄k] → k[ε]/(ε²)` induced by `a + bε ↦ b`, sending
`dε` to `1`, is surjective. -/
theorem surjective_dualNumberQuotient (h2 : (2 : k) = 0) :
    Function.Surjective (LinearMap.pi fun _ : Fin 1 ↦
      (dualNumberDerivation k h2).liftKaehlerDifferential :
        Ω[dualNumberRing k⁄k] →ₗ[dualNumberRing k] (Fin 1 → dualNumberRing k)) := fun v ↦
  ⟨v 0 • D k (DualNumber k) DualNumber.eps, funext fun j ↦ by
    simp [Subsingleton.elim j 0]⟩

-- **Check.** Over a field of characteristic `2`, `Ω_{X/k}` for `X = Spec k[ε]/(ε²)` has a locally
-- free quotient of rank `1`.
example (h2 : (2 : k) = 0) :
    HasLocallyFreeQuotientOfDifferentials k (Spec (dualNumberRing k)) 1 :=
  hasLocallyFreeQuotientOfDifferentials_Spec_of_surjective k _ _
    (surjective_dualNumberQuotient k h2)

end

end TauCeti.LocallyFreeQuotientAffineExample
