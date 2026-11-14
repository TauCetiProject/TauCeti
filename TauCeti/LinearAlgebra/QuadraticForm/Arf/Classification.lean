/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.BilinearForm.LagrangianBasis
public import TauCeti.LinearAlgebra.QuadraticForm.Arf.Basic
public import TauCeti.LinearAlgebra.QuadraticForm.TotallyIsotropic

import Mathlib.FieldTheory.Finiteness
import Mathlib.LinearAlgebra.Basis.Fin
import Mathlib.LinearAlgebra.Dimension.Constructions

/-!
# Classification, zero counts, and Lagrangian criterion for quadratic forms over `ZMod 2`

This file classifies finite-dimensional quadratic forms over `ZMod 2` whose polar bilinear forms
are nondegenerate, computes their exact zero counts, and proves the Lagrangian vanishing criterion
for the Arf invariant.

Every binary symplectic plane `symplecticPlane (ZMod 2) a b` is explicitly isometric to the
diagonal-coefficient plane `symplecticPlane (ZMod 2) (a * b) (a * b)`: the hyperbolic plane `x₀ x₁`
when `a * b = 0`, and the anisotropic plane `x₀² + x₀ x₁ + x₁²` when `a = b = 1`. Moreover, over
every commutative ring of characteristic two, the orthogonal sum of two copies of
`x₀² + x₀ x₁ + x₁²` is explicitly isometric to the orthogonal sum of two hyperbolic planes.

Consequently, every `2 m`-dimensional quadratic space `(V, q)` over `ZMod 2` with nondegenerate
polar form is isometric to a unique standard normal form `TauCeti.arfNormalForm m q.arf`: `m`
hyperbolic planes when `q.arf = 0`, and one anisotropic plane orthogonally summed with `m - 1`
hyperbolic planes when `q.arf = 1` (for `m = 0` only `q.arf = 0` occurs). Two such spaces are
isometric if and only if they have the same dimension and the same Arf invariant.

## Main definitions

* `TauCeti.isometryEquivSymplecticPlane`: explicit involution normalizing
  `symplecticPlane (ZMod 2) a b` to `symplecticPlane (ZMod 2) (a * b) (a * b)`.
* `TauCeti.isometryEquivProdSymplecticPlaneOneOne`: explicit characteristic-two isometry from two
  hyperbolic planes to two copies of `symplecticPlane R 1 1`.
* `TauCeti.arfNormalForm m c`: the standard `2 m`-dimensional normal form over `ZMod 2` with
  parameter `c : ZMod 2`.
* `TauCeti.isometryEquivArfNormalFormOfPi`: computable reduction of any finite orthogonal sum of
  binary symplectic planes over `ZMod 2` to `TauCeti.arfNormalForm`.

## Main results

* `TauCeti.anisotropic_symplecticPlane_iff`: `symplecticPlane (ZMod 2) a b` is anisotropic if and
  only if `a = 1 ∧ b = 1`.
* `QuadraticMap.isTotallyIsotropic_range_inl_add_inr`: in characteristic two, the diagonal subspace
  `{(v, v) | v ∈ V}` of `V × V` is totally isotropic for `q.prod q` of dimension `finrank R V`.
* `QuadraticMap.equivalent_arfNormalForm` and
  `QuadraticMap.equivalent_iff_finrank_eq_and_arf_eq`: **Arf's classification theorem** over
  `ZMod 2` by dimension and Arf invariant.
* `QuadraticMap.two_mul_card_filter_apply_eq_zero`,
  `QuadraticMap.card_filter_apply_eq_zero_of_finrank_eq_two_mul`,
  `QuadraticMap.card_filter_apply_eq_zero_of_arf_eq_zero`, and
  `QuadraticMap.card_filter_apply_eq_zero_of_arf_eq_one`: exact zero counts
  `2 ^ (2 m - 1) ± 2 ^ (m - 1)`.
* `QuadraticMap.arf_eq_zero_iff_exists_basis_toMatrix_eq_J_apply_eq_zero`,
  `QuadraticMap.arf_eq_zero_iff_exists_isTotallyIsotropic_eq_orthogonal`, and
  `QuadraticMap.arf_eq_zero_iff_exists_isTotallyIsotropic_two_mul_finrank_eq`: `q.arf = 0` if and
  only if `V` admits a hyperbolic symplectic basis, equivalently a Lagrangian or half-dimensional
  `q`-totally isotropic subspace.

## References

* C. Arf, *Untersuchungen über quadratische Formen in Körpern der Charakteristik 2 (Teil I)*,
  J. Reine Angew. Math. **183** (1941), 148--167.
* J. Milnor and D. Husemoller, *Symmetric Bilinear Forms*, Ergebnisse der Mathematik und ihrer
  Grenzgebiete **73**, Springer (1973), Appendix 1.
* A. Pyronneau, *Arf invariant* (2024), §2.1--2.2.
-/

public section

open scoped CharTwo

namespace TauCeti

section PlaneClassification

/-- The coordinate line spanned by `![1, 0]` is totally isotropic for the hyperbolic plane
`symplecticPlane R 0 0`. -/
theorem isTotallyIsotropic_span_symplecticPlane_zero_zero {R : Type*} [CommSemiring R] :
    (symplecticPlane R 0 0).IsTotallyIsotropic (R ∙ (![1, 0] : Fin 2 → R)) := by
  rw [QuadraticMap.isTotallyIsotropic_span_singleton_iff]
  simp

private theorem zmod_two_eq_zero_or_one (x : ZMod 2) : x = 0 ∨ x = 1 := by
  revert x; decide

/-- Over `ZMod 2`, the binary symplectic plane `symplecticPlane (ZMod 2) a b` is anisotropic if and
only if `a = 1` and `b = 1`. -/
@[simp]
theorem anisotropic_symplecticPlane_iff (a b : ZMod 2) :
    (symplecticPlane (ZMod 2) a b).Anisotropic ↔ a = 1 ∧ b = 1 := by
  refine ⟨fun h ↦ ⟨?_, ?_⟩, fun ⟨ha, hb⟩ x hx ↦ ?_⟩
  · rcases zmod_two_eq_zero_or_one a with rfl | rfl
    · exact absurd (congrFun (h ![1, 0] (by simp)) 0) one_ne_zero
    · rfl
  · rcases zmod_two_eq_zero_or_one b with rfl | rfl
    · exact absurd (congrFun (h ![0, 1] (by simp)) 1) one_ne_zero
    · rfl
  · subst ha hb
    have h01 : x 0 = 0 ∧ x 1 = 0 := by
      simp only [symplecticPlane_apply] at hx
      generalize x 0 = c₀ at hx ⊢
      generalize x 1 = c₁ at hx ⊢
      revert c₀ c₁ hx; decide
    exact funext (Fin.forall_fin_two.mpr h01)

/-- The plane `x₀² + x₀ x₁ + x₁²` over `ZMod 2` is anisotropic. -/
theorem anisotropic_symplecticPlane_one_one :
    (symplecticPlane (ZMod 2) 1 1).Anisotropic :=
  (anisotropic_symplecticPlane_iff 1 1).mpr ⟨rfl, rfl⟩

/-- Explicit self-inverse linear equivalence normalizing `symplecticPlane (ZMod 2) a b` to
`symplecticPlane (ZMod 2) (a * b) (a * b)`: it acts as the identity when `a = b`, sends
`x ↦ ![x 0, x 1 + x 0]` when `(a, b) = (1, 0)`, and sends `x ↦ ![x 0 + x 1, x 1]` when
`(a, b) = (0, 1)`. -/
def isometryEquivSymplecticPlane (a b : ZMod 2) :
    (symplecticPlane (ZMod 2) a b).IsometryEquiv
      (symplecticPlane (ZMod 2) (a * b) (a * b)) where
  toFun x := ![x 0 + b * (1 + a) * x 1, x 1 + a * (1 + b) * x 0]
  invFun x := ![x 0 + b * (1 + a) * x 1, x 1 + a * (1 + b) * x 0]
  map_add' x y := by
    ext i
    fin_cases i <;> simp <;> ring
  map_smul' r x := by
    ext i
    fin_cases i <;> simp <;> ring
  left_inv x := by
    ext i
    fin_cases i <;> rcases zmod_two_eq_zero_or_one a with rfl | rfl <;>
      rcases zmod_two_eq_zero_or_one b with rfl | rfl <;> simp
  right_inv x := by
    ext i
    fin_cases i <;> rcases zmod_two_eq_zero_or_one a with rfl | rfl <;>
      rcases zmod_two_eq_zero_or_one b with rfl | rfl <;> simp
  map_app' x := by
    rcases zmod_two_eq_zero_or_one a with rfl | rfl <;>
      rcases zmod_two_eq_zero_or_one b with rfl | rfl <;> simp <;> ring

/-- Action of `TauCeti.isometryEquivSymplecticPlane` on vectors. -/
@[simp]
theorem isometryEquivSymplecticPlane_apply (a b : ZMod 2) (x : Fin 2 → ZMod 2) :
    isometryEquivSymplecticPlane a b x =
      ![x 0 + b * (1 + a) * x 1, x 1 + a * (1 + b) * x 0] :=
  (rfl)

private theorem prodSymplecticPlaneOneOne_left_inv {R : Type*} [CommRing R] [CharP R 2]
    (p : (Fin 2 → R) × (Fin 2 → R)) :
    (let q : (Fin 2 → R) × (Fin 2 → R) :=
      (![p.1 0 + p.1 1, p.1 1 + p.2 0 + p.2 1], ![p.1 0 + p.1 1 + p.2 1, p.2 0 + p.2 1])
    (![q.1 0 + q.1 1 + q.2 1, q.1 1 + q.2 1],
      ![q.1 0 + q.2 0 + q.2 1, q.1 0 + q.2 0])) = p := by
  refine Prod.ext (funext fun i ↦ ?_) (funext fun i ↦ ?_) <;> fin_cases i <;>
    simp only [Fin.zero_eta, Fin.mk_one, Matrix.cons_val_zero, Matrix.cons_val_one]
  · calc (p.1 0 + p.1 1) + (p.1 1 + p.2 0 + p.2 1) + (p.2 0 + p.2 1)
        = p.1 0 + (2 : R) * (p.1 1 + p.2 0 + p.2 1) := by ring
      _ = p.1 0 := by simp
  · calc (p.1 1 + p.2 0 + p.2 1) + (p.2 0 + p.2 1) = p.1 1 + (2 : R) * (p.2 0 + p.2 1) := by ring
      _ = p.1 1 := by simp
  · calc (p.1 0 + p.1 1) + (p.1 0 + p.1 1 + p.2 1) + (p.2 0 + p.2 1)
        = p.2 0 + (2 : R) * (p.1 0 + p.1 1 + p.2 1) := by ring
      _ = p.2 0 := by simp
  · calc (p.1 0 + p.1 1) + (p.1 0 + p.1 1 + p.2 1) = p.2 1 + (2 : R) * (p.1 0 + p.1 1) := by ring
      _ = p.2 1 := by simp

private theorem prodSymplecticPlaneOneOne_right_inv {R : Type*} [CommRing R] [CharP R 2]
    (q : (Fin 2 → R) × (Fin 2 → R)) :
    (let p : (Fin 2 → R) × (Fin 2 → R) :=
      (![q.1 0 + q.1 1 + q.2 1, q.1 1 + q.2 1], ![q.1 0 + q.2 0 + q.2 1, q.1 0 + q.2 0])
    (![p.1 0 + p.1 1, p.1 1 + p.2 0 + p.2 1],
      ![p.1 0 + p.1 1 + p.2 1, p.2 0 + p.2 1])) = q := by
  refine Prod.ext (funext fun i ↦ ?_) (funext fun i ↦ ?_) <;> fin_cases i <;>
    simp only [Fin.zero_eta, Fin.mk_one, Matrix.cons_val_zero, Matrix.cons_val_one]
  · calc (q.1 0 + q.1 1 + q.2 1) + (q.1 1 + q.2 1) = q.1 0 + (2 : R) * (q.1 1 + q.2 1) := by ring
      _ = q.1 0 := by simp
  · calc (q.1 1 + q.2 1) + (q.1 0 + q.2 0 + q.2 1) + (q.1 0 + q.2 0)
        = q.1 1 + (2 : R) * (q.1 0 + q.2 0 + q.2 1) := by ring
      _ = q.1 1 := by simp
  · calc (q.1 0 + q.1 1 + q.2 1) + (q.1 1 + q.2 1) + (q.1 0 + q.2 0)
        = q.2 0 + (2 : R) * (q.1 0 + q.1 1 + q.2 1) := by ring
      _ = q.2 0 := by simp
  · calc (q.1 0 + q.2 0 + q.2 1) + (q.1 0 + q.2 0) = q.2 1 + (2 : R) * (q.1 0 + q.2 0) := by ring
      _ = q.2 1 := by simp

private theorem prodSymplecticPlaneOneOne_map_app {R : Type*} [CommRing R] [CharP R 2]
    (p : (Fin 2 → R) × (Fin 2 → R)) :
    ((symplecticPlane R 1 1).prod (symplecticPlane R 1 1))
        (![p.1 0 + p.1 1, p.1 1 + p.2 0 + p.2 1],
          ![p.1 0 + p.1 1 + p.2 1, p.2 0 + p.2 1]) =
      ((symplecticPlane R 0 0).prod (symplecticPlane R 0 0)) p := by
  simp only [QuadraticMap.prod_apply, symplecticPlane_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one, zero_mul, zero_add, add_zero]
  calc
    1 * ((p.1 0 + p.1 1) * (p.1 0 + p.1 1)) +
        (p.1 0 + p.1 1) * (p.1 1 + p.2 0 + p.2 1) +
        1 * ((p.1 1 + p.2 0 + p.2 1) * (p.1 1 + p.2 0 + p.2 1)) +
      (1 * ((p.1 0 + p.1 1 + p.2 1) * (p.1 0 + p.1 1 + p.2 1)) +
        (p.1 0 + p.1 1 + p.2 1) * (p.2 0 + p.2 1) +
        1 * ((p.2 0 + p.2 1) * (p.2 0 + p.2 1)))
      = p.1 0 * p.1 1 + p.2 0 * p.2 1 +
          (2 : R) * (p.1 0 * p.1 0 + 2 * p.1 1 * p.1 1 + p.2 0 * p.2 0 + 2 * p.2 1 * p.2 1 +
            2 * p.1 0 * p.1 1 + p.1 0 * p.2 0 + 2 * p.1 0 * p.2 1 +
            2 * p.1 1 * p.2 0 + 3 * p.1 1 * p.2 1 + 2 * p.2 0 * p.2 1) := by ring
    _ = p.1 0 * p.1 1 + p.2 0 * p.2 1 := by simp

/-- Over any commutative ring of characteristic two, the orthogonal sum of two hyperbolic planes
`x₀ x₁ ⊕ y₀ y₁` is explicitly isometric to the orthogonal sum of two copies of
`x₀² + x₀ x₁ + x₁²`. -/
def isometryEquivProdSymplecticPlaneOneOne (R : Type*) [CommRing R] [CharP R 2] :
    ((symplecticPlane R 0 0).prod (symplecticPlane R 0 0)).IsometryEquiv
      ((symplecticPlane R 1 1).prod (symplecticPlane R 1 1)) where
  toFun p := (![p.1 0 + p.1 1, p.1 1 + p.2 0 + p.2 1],
    ![p.1 0 + p.1 1 + p.2 1, p.2 0 + p.2 1])
  invFun q := (![q.1 0 + q.1 1 + q.2 1, q.1 1 + q.2 1],
    ![q.1 0 + q.2 0 + q.2 1, q.1 0 + q.2 0])
  map_add' p₁ p₂ := by
    refine Prod.ext (funext fun i ↦ ?_) (funext fun i ↦ ?_) <;> fin_cases i <;> simp <;> ring
  map_smul' r p := by
    refine Prod.ext (funext fun i ↦ ?_) (funext fun i ↦ ?_) <;> fin_cases i <;> simp <;> ring
  left_inv := prodSymplecticPlaneOneOne_left_inv
  right_inv := prodSymplecticPlaneOneOne_right_inv
  map_app' := prodSymplecticPlaneOneOne_map_app

/-- Forward evaluation of `TauCeti.isometryEquivProdSymplecticPlaneOneOne`. -/
@[simp]
theorem isometryEquivProdSymplecticPlaneOneOne_apply {R : Type*} [CommRing R] [CharP R 2]
    (p : (Fin 2 → R) × (Fin 2 → R)) :
    isometryEquivProdSymplecticPlaneOneOne R p =
      (![p.1 0 + p.1 1, p.1 1 + p.2 0 + p.2 1],
        ![p.1 0 + p.1 1 + p.2 1, p.2 0 + p.2 1]) :=
  (rfl)

/-- Absorbing two diagonal-coefficient binary planes over `ZMod 2` into one plane of Arf invariant
`c₁ + c₂` and one hyperbolic plane. -/
def isometryEquivProdSymplecticPlaneDiag (c₁ c₂ : ZMod 2) :
    ((symplecticPlane (ZMod 2) c₁ c₁).prod (symplecticPlane (ZMod 2) c₂ c₂)).IsometryEquiv
      ((symplecticPlane (ZMod 2) (c₁ + c₂) (c₁ + c₂)).prod (symplecticPlane (ZMod 2) 0 0)) :=
  match c₁, c₂ with
  | 0, 0 => QuadraticMap.IsometryEquiv.refl _
  | 1, 0 => QuadraticMap.IsometryEquiv.refl _
  | 0, 1 => QuadraticMap.IsometryEquiv.prodComm _ _
  | 1, 1 => (isometryEquivProdSymplecticPlaneOneOne (ZMod 2)).symm

end PlaneClassification

section NormalForm

/-- The standard `2 m`-dimensional quadratic normal form over `ZMod 2` with parameter `c : ZMod 2`:
`m` hyperbolic planes when `c = 0`, and `symplecticPlane (ZMod 2) 1 1` orthogonally summed with
`m - 1` hyperbolic planes when `c = 1` and `m ≥ 1`. -/
def arfNormalForm (m : ℕ) (c : ZMod 2) : QuadraticForm (ZMod 2) (Fin m → Fin 2 → ZMod 2) :=
  QuadraticMap.pi fun i : Fin m ↦
    if (i : ℕ) = 0 then symplecticPlane (ZMod 2) c c else symplecticPlane (ZMod 2) 0 0

/-- At `c = 0`, `TauCeti.arfNormalForm` is the orthogonal sum of `m` hyperbolic planes. -/
@[simp]
theorem arfNormalForm_zero_right (m : ℕ) :
    arfNormalForm m 0 = QuadraticMap.pi fun _ : Fin m ↦ symplecticPlane (ZMod 2) 0 0 := by
  ext x
  simp [arfNormalForm]

/-- The polar bilinear form of `TauCeti.arfNormalForm` is always nondegenerate. -/
@[simp]
theorem nondegenerate_polarBilin_arfNormalForm (m : ℕ) (c : ZMod 2) :
    (arfNormalForm m c).polarBilin.Nondegenerate := by
  rw [arfNormalForm, QuadraticMap.nondegenerate_polarBilin_pi_iff]
  intro i
  split_ifs <;> exact nondegenerate_polarBilin_symplecticPlane _ _

private theorem arfNormalForm_succ_tail (m : ℕ) (c : ZMod 2) :
    (QuadraticMap.pi fun i : Fin m ↦
      if ((i.succ : Fin (m + 1)) : ℕ) = 0 then symplecticPlane (ZMod 2) c c
      else symplecticPlane (ZMod 2) 0 0) = arfNormalForm m 0 := by
  ext x
  simp [arfNormalForm]

/-- Splitting off the first plane of `TauCeti.arfNormalForm (m + 1) c` exhibits it as
`symplecticPlane (ZMod 2) c c` orthogonally summed with `arfNormalForm m 0`. -/
def isometryEquivArfNormalFormSucc (m : ℕ) (c : ZMod 2) :
    ((symplecticPlane (ZMod 2) c c).prod (arfNormalForm m 0)).IsometryEquiv
      (arfNormalForm (m + 1) c) :=
  arfNormalForm_succ_tail m c ▸
    (QuadraticMap.IsometryEquiv.consPi fun i : Fin (m + 1) ↦
      if (i : ℕ) = 0 then symplecticPlane (ZMod 2) c c else symplecticPlane (ZMod 2) 0 0)

/-- The Arf invariant of `TauCeti.arfNormalForm m c` is `0` when `m = 0` and `c` when `1 ≤ m`. -/
@[simp]
theorem arf_arfNormalForm (m : ℕ) (c : ZMod 2) :
    (arfNormalForm m c).arf = if m = 0 then 0 else c := by
  cases m with
  | zero => simp
  | succ m =>
    rw [← (isometryEquivArfNormalFormSucc m c).arf_eq,
      QuadraticMap.arf_prod (nondegenerate_polarBilin_symplecticPlane c c)
        (nondegenerate_polarBilin_arfNormalForm m 0),
      QuadraticMap.arf_symplecticPlane, arfNormalForm_zero_right,
      QuadraticMap.arf_pi fun _ ↦ nondegenerate_polarBilin_symplecticPlane 0 0]
    simp [mul_self_eq c]
where
  mul_self_eq (x : ZMod 2) : x * x = x := by revert x; decide

/-- Computably reducing any finite orthogonal sum of binary symplectic planes over `ZMod 2` to
`TauCeti.arfNormalForm m (∑ i, a i * b i)`. -/
def isometryEquivArfNormalFormOfPi :
    ∀ (m : ℕ) (a b : Fin m → ZMod 2),
      (QuadraticMap.pi fun i : Fin m ↦ symplecticPlane (ZMod 2) (a i) (b i)).IsometryEquiv
        (arfNormalForm m (∑ i : Fin m, a i * b i))
  | 0, _, _ => QuadraticMap.IsometryEquiv.refl _
  | 1, a, b =>
    let e₀ := (QuadraticMap.IsometryEquiv.consPi fun i : Fin 1 ↦
      symplecticPlane (ZMod 2) (a i) (b i)).symm
    let e₁ := (isometryEquivSymplecticPlane (a 0) (b 0)).prod
      (QuadraticMap.IsometryEquiv.refl (arfNormalForm 0 0))
    let e₂ := isometryEquivArfNormalFormSucc 0 (a 0 * b 0)
    have hsum : ∑ i : Fin 1, a i * b i = a 0 * b 0 := Fin.sum_univ_one _
    hsum ▸ (e₀.trans (e₁.trans e₂))
  | k + 2, a, b =>
    let c₀ := a 0 * b 0
    let c' := ∑ i : Fin (k + 1), a i.succ * b i.succ
    let eSplit := (QuadraticMap.IsometryEquiv.consPi fun i : Fin (k + 2) ↦
      symplecticPlane (ZMod 2) (a i) (b i)).symm
    let eIH := (isometryEquivSymplecticPlane (a 0) (b 0)).prod
      ((isometryEquivArfNormalFormOfPi (k + 1) (fun i ↦ a i.succ) (fun i ↦ b i.succ)).trans
        (isometryEquivArfNormalFormSucc k c').symm)
    let eCombine := ((QuadraticMap.IsometryEquiv.prodAssoc _ _ _).symm.trans
      ((isometryEquivProdSymplecticPlaneDiag c₀ c').prod
        (QuadraticMap.IsometryEquiv.refl (arfNormalForm k 0)))).trans
      ((QuadraticMap.IsometryEquiv.prodAssoc _ _ _).trans
        (((QuadraticMap.IsometryEquiv.refl _).prod
          (isometryEquivArfNormalFormSucc k 0)).trans
          (isometryEquivArfNormalFormSucc (k + 1) (c₀ + c'))))
    have hsum : ∑ i : Fin (k + 2), a i * b i = c₀ + c' := Fin.sum_univ_succ _
    hsum ▸ (eSplit.trans (eIH.trans eCombine))

end NormalForm

end TauCeti

namespace QuadraticMap

open TauCeti

section DiagonalTotallyIsotropic

variable {R V : Type*} [CommSemiring R] [CharP R 2] [AddCommMonoid V] [Module R V]

/-- In characteristic two, the diagonal submodule `{(v, v) | v ∈ V}` of `V × V` is totally
isotropic for `q.prod q`. -/
theorem isTotallyIsotropic_range_inl_add_inr (q : QuadraticForm R V) :
    (q.prod q).IsTotallyIsotropic
      (LinearMap.range (LinearMap.inl R V V + LinearMap.inr R V V)) := by
  rw [isTotallyIsotropic_iff]
  rintro _ ⟨v, rfl⟩
  simp

omit [CommSemiring R] [CharP R 2] [AddCommMonoid V] [Module R V] in
/-- The diagonal submodule `LinearMap.range (inl + inr)` has the same `finrank` as `V`. -/
theorem finrank_range_inl_add_inr {R V : Type*} [Semiring R] [AddCommMonoid V] [Module R V] :
    Module.finrank R (LinearMap.range (LinearMap.inl R V V + LinearMap.inr R V V)) =
      Module.finrank R V :=
  LinearMap.finrank_range_of_inj fun _ _ huv ↦ by simpa using congrArg Prod.fst huv

end DiagonalTotallyIsotropic

section Classification

variable {V W : Type*} [AddCommGroup V] [Module (ZMod 2) V]
  [AddCommGroup W] [Module (ZMod 2) W]

/-- Every finite-dimensional quadratic form over `ZMod 2` with nondegenerate polar form is
equivalent to `TauCeti.arfNormalForm (finrank (ZMod 2) V / 2) q.arf`. -/
theorem equivalent_arfNormalForm [FiniteDimensional (ZMod 2) V]
    {q : QuadraticForm (ZMod 2) V} (hq : q.polarBilin.Nondegenerate) :
    q.Equivalent (arfNormalForm (Module.finrank (ZMod 2) V / 2) q.arf) := by
  obtain ⟨m, b, hb⟩ := LinearMap.BilinForm.IsAlt.exists_basis_toMatrix_eq_J q.isAlt_polarBilin hq
  have hdim : Module.finrank (ZMod 2) V / 2 = m := by
    rw [Module.finrank_eq_card_basis b, Fintype.card_sum, Fintype.card_fin]
    omega
  rw [hdim, q.arf_eq_sum_of_toMatrix_eq_J b hb]
  exact ⟨(q.isometryEquivPiSymplecticPlane b hb).trans
    (isometryEquivArfNormalFormOfPi m (fun i ↦ q (b (Sum.inl i))) (fun i ↦ q (b (Sum.inr i))))⟩

/-- **Arf's classification theorem over `ZMod 2`.** Two finite-dimensional quadratic spaces over
`ZMod 2` with nondegenerate polar forms are isometric if and only if they have the same dimension
and the same Arf invariant. -/
theorem equivalent_iff_finrank_eq_and_arf_eq
    [FiniteDimensional (ZMod 2) V] [FiniteDimensional (ZMod 2) W]
    {q₁ : QuadraticForm (ZMod 2) V} {q₂ : QuadraticForm (ZMod 2) W}
    (hq₁ : q₁.polarBilin.Nondegenerate) (hq₂ : q₂.polarBilin.Nondegenerate) :
    q₁.Equivalent q₂ ↔
      Module.finrank (ZMod 2) V = Module.finrank (ZMod 2) W ∧ q₁.arf = q₂.arf := by
  refine ⟨fun ⟨e⟩ ↦ ⟨e.toLinearEquiv.finrank_eq, e.arf_eq⟩, fun ⟨hdim, harf⟩ ↦ ?_⟩
  refine (q₁.equivalent_arfNormalForm hq₁).trans ?_
  rw [hdim, harf]
  exact (q₂.equivalent_arfNormalForm hq₂).symm

/-- A finite-dimensional quadratic space over `ZMod 2` with nondegenerate polar form is equivalent
to the orthogonal sum of `m` hyperbolic planes if and only if `finrank (ZMod 2) V = 2 * m` and
`q.arf = 0`. -/
theorem equivalent_pi_symplecticPlane_zero_zero_iff [FiniteDimensional (ZMod 2) V]
    {q : QuadraticForm (ZMod 2) V} (hq : q.polarBilin.Nondegenerate) (m : ℕ) :
    q.Equivalent (QuadraticMap.pi fun _ : Fin m ↦ symplecticPlane (ZMod 2) 0 0) ↔
      Module.finrank (ZMod 2) V = 2 * m ∧ q.arf = 0 := by
  rw [← arfNormalForm_zero_right m,
    equivalent_iff_finrank_eq_and_arf_eq hq (nondegenerate_polarBilin_arfNormalForm m 0)]
  have hfinrank : Module.finrank (ZMod 2) (Fin m → Fin 2 → ZMod 2) = 2 * m := by
    simp [Module.finrank_pi_fintype, mul_comm]
  rw [hfinrank, arfNormalForm_zero_right,
    arf_pi fun _ ↦ nondegenerate_polarBilin_symplecticPlane 0 0]
  simp

/-- A quadratic space `(V, q)` over `ZMod 2` is equivalent to `symplecticPlane (ZMod 2) 1 1`
orthogonally summed with `m` hyperbolic planes if and only if `finrank (ZMod 2) V = 2 * (m + 1)`
and `q.arf = 1`. Both finite-dimensionality of `V` and polar nondegeneracy of `q` follow
automatically from either side. -/
theorem equivalent_symplecticPlane_one_one_prod_pi_iff (q : QuadraticForm (ZMod 2) V) (m : ℕ) :
    q.Equivalent
        ((symplecticPlane (ZMod 2) 1 1).prod
          (QuadraticMap.pi fun _ : Fin m ↦ symplecticPlane (ZMod 2) 0 0)) ↔
      Module.finrank (ZMod 2) V = 2 * (m + 1) ∧ q.arf = 1 := by
  have htail : arfNormalForm m 0 =
      QuadraticMap.pi fun _ : Fin m ↦ symplecticPlane (ZMod 2) 0 0 :=
    arfNormalForm_zero_right m
  have heq :
      q.Equivalent
        ((symplecticPlane (ZMod 2) 1 1).prod
          (QuadraticMap.pi fun _ : Fin m ↦ symplecticPlane (ZMod 2) 0 0)) ↔
      q.Equivalent (arfNormalForm (m + 1) 1) := by
    rw [← htail]
    exact ⟨fun h ↦ h.trans ⟨isometryEquivArfNormalFormSucc m 1⟩,
      fun h ↦ h.trans ⟨(isometryEquivArfNormalFormSucc m 1).symm⟩⟩
  have hfinrank : Module.finrank (ZMod 2) (Fin (m + 1) → Fin 2 → ZMod 2) = 2 * (m + 1) := by
    simp [Module.finrank_pi_fintype, mul_comm]
  rw [heq]
  refine ⟨fun ⟨e⟩ ↦ ⟨e.toLinearEquiv.finrank_eq.trans hfinrank, by simp [e.arf_eq]⟩,
    fun ⟨hdim, harf⟩ ↦ ?_⟩
  have hfin : FiniteDimensional (ZMod 2) V := by
    by_contra hnf
    exact zero_ne_one (arf_of_not_finiteDimensional hnf ▸ harf)
  have hq : q.polarBilin.Nondegenerate := by
    by_contra hnd
    exact zero_ne_one (arf_of_not_nondegenerate_polarBilin hnd ▸ harf)
  exact (equivalent_iff_finrank_eq_and_arf_eq hq
    (nondegenerate_polarBilin_arfNormalForm (m + 1) 1)).mpr
      ⟨hdim.trans hfinrank.symm, by simp [harf]⟩

end Classification

section ZeroCount

/-- For any quadratic form `q` on a finite `ZMod 2`-module `V`, twice the number of zeros of `q`
equals `card V + q.gaussSum`. No nondegeneracy hypothesis is needed. -/
theorem two_mul_card_filter_apply_eq_zero {V : Type*} [AddCommMonoid V] [Module (ZMod 2) V]
    [Fintype V] (q : QuadraticForm (ZMod 2) V) :
    2 * ((Finset.univ.filter fun v : V ↦ q v = 0).card : ℤ) =
      (Fintype.card V : ℤ) + q.gaussSum := by
  have hpart := Finset.card_filter_add_card_filter_not (s := Finset.univ) (fun v : V ↦ q v = 0)
  rw [Finset.card_univ] at hpart
  have hgauss :
      q.gaussSum =
        ((Finset.univ.filter fun v : V ↦ q v = 0).card : ℤ) -
          ((Finset.univ.filter fun v : V ↦ ¬ q v = 0).card : ℤ) := by
    rw [gaussSum_def, ← Finset.sum_filter_add_sum_filter_not Finset.univ (fun v : V ↦ q v = 0)]
    have h0 : ∑ v ∈ Finset.univ.filter (fun v : V ↦ q v = 0), (-1 : ℤ) ^ (q v).val =
        ((Finset.univ.filter fun v : V ↦ q v = 0).card : ℤ) := by
      calc
        ∑ v ∈ Finset.univ.filter (fun v : V ↦ q v = 0), (-1 : ℤ) ^ (q v).val
          = ∑ _v ∈ Finset.univ.filter (fun v : V ↦ q v = 0), (1 : ℤ) := by
            refine Finset.sum_congr rfl fun v hv ↦ ?_
            rw [(Finset.mem_filter.mp hv).2]
            rfl
        _ = ((Finset.univ.filter fun v : V ↦ q v = 0).card : ℤ) := by simp
    have h1 : ∑ v ∈ Finset.univ.filter (fun v : V ↦ ¬ q v = 0), (-1 : ℤ) ^ (q v).val =
        -((Finset.univ.filter fun v : V ↦ ¬ q v = 0).card : ℤ) := by
      calc
        ∑ v ∈ Finset.univ.filter (fun v : V ↦ ¬ q v = 0), (-1 : ℤ) ^ (q v).val
          = ∑ _v ∈ Finset.univ.filter (fun v : V ↦ ¬ q v = 0), (-1 : ℤ) := by
            refine Finset.sum_congr rfl fun v hv ↦ ?_
            have hne := (Finset.mem_filter.mp hv).2
            generalize q v = c at hne ⊢
            revert c hne; decide
        _ = -((Finset.univ.filter fun v : V ↦ ¬ q v = 0).card : ℤ) := by simp
    rw [h0, h1, sub_eq_add_neg]
  omega

/-- On a subsingleton `ZMod 2`-module, the unique vector `0` is the sole zero of `q`. -/
@[simp]
theorem card_filter_apply_eq_zero_subsingleton {V : Type*} [AddCommMonoid V] [Module (ZMod 2) V]
    [Fintype V] [Subsingleton V] (q : QuadraticForm (ZMod 2) V) :
    (Finset.univ.filter fun v : V ↦ q v = 0).card = 1 := by
  have h2 := q.two_mul_card_filter_apply_eq_zero
  let _ : Unique V := uniqueOfSubsingleton (0 : V)
  rw [Fintype.card_unique, gaussSum_subsingleton] at h2
  omega

/-- **Signed zero-count formula.** For a quadratic form `q` on a finite `ZMod 2`-space `V` of
dimension `2 * m` (`1 ≤ m`) with nondegenerate polar form,
`#{v | q v = 0} = 2 ^ (2 * m - 1) + (-1) ^ q.arf.val * 2 ^ (m - 1)` in `ℤ`. -/
theorem card_filter_apply_eq_zero_of_finrank_eq_two_mul {V : Type*} [AddCommGroup V]
    [Module (ZMod 2) V] [Fintype V] {q : QuadraticForm (ZMod 2) V}
    (hq : q.polarBilin.Nondegenerate) {m : ℕ} (hm : Module.finrank (ZMod 2) V = 2 * m)
    (hm_pos : 1 ≤ m) :
    ((Finset.univ.filter fun v : V ↦ q v = 0).card : ℤ) =
      (2 : ℤ) ^ (2 * m - 1) + (-1 : ℤ) ^ q.arf.val * (2 : ℤ) ^ (m - 1) := by
  have h2 := q.two_mul_card_filter_apply_eq_zero
  have hcard : Fintype.card V = 2 ^ (2 * m) := by
    rw [Module.card_eq_pow_finrank (K := ZMod 2) (V := V), ZMod.card 2, hm]
  rw [hcard, Nat.cast_pow, Nat.cast_ofNat, q.gaussSum_eq_of_finrank_eq_two_mul hq hm] at h2
  have h2m : 2 * m = (2 * m - 1) + 1 := by omega
  have hm1 : m = (m - 1) + 1 := by omega
  have hp₁ : (2 : ℤ) ^ (2 * m) = 2 * (2 : ℤ) ^ (2 * m - 1) := by
    conv_lhs => rw [h2m, pow_succ']
  have hp₂ : (2 : ℤ) ^ m = 2 * (2 : ℤ) ^ (m - 1) := by
    conv_lhs => rw [hm1, pow_succ']
  rw [hp₁, hp₂] at h2
  linarith

/-- Natural-number zero count when `q.arf = 0` and `1 ≤ m`:
`#{v | q v = 0} = 2 ^ (2 * m - 1) + 2 ^ (m - 1)`. -/
theorem card_filter_apply_eq_zero_of_arf_eq_zero {V : Type*} [AddCommGroup V]
    [Module (ZMod 2) V] [Fintype V] {q : QuadraticForm (ZMod 2) V}
    (hq : q.polarBilin.Nondegenerate) (harf : q.arf = 0) {m : ℕ}
    (hm : Module.finrank (ZMod 2) V = 2 * m) (hm_pos : 1 ≤ m) :
    (Finset.univ.filter fun v : V ↦ q v = 0).card = 2 ^ (2 * m - 1) + 2 ^ (m - 1) := by
  have hz := q.card_filter_apply_eq_zero_of_finrank_eq_two_mul hq hm hm_pos
  rw [harf] at hz
  norm_num at hz
  exact_mod_cast hz

/-- Natural-number zero count when `q.arf = 1`:
`#{v | q v = 0} = 2 ^ (2 * m - 1) - 2 ^ (m - 1)`. Both polar nondegeneracy of `q` and `1 ≤ m`
follow automatically from `q.arf = 1`. -/
theorem card_filter_apply_eq_zero_of_arf_eq_one {V : Type*} [AddCommGroup V]
    [Module (ZMod 2) V] [Fintype V] {q : QuadraticForm (ZMod 2) V}
    (harf : q.arf = 1) {m : ℕ} (hm : Module.finrank (ZMod 2) V = 2 * m) :
    (Finset.univ.filter fun v : V ↦ q v = 0).card = 2 ^ (2 * m - 1) - 2 ^ (m - 1) := by
  have hq : q.polarBilin.Nondegenerate := by
    by_contra hnd
    exact zero_ne_one (arf_of_not_nondegenerate_polarBilin hnd ▸ harf)
  have hm_pos : 1 ≤ m := by
    rcases Nat.eq_zero_or_pos m with rfl | hpos
    · have : FiniteDimensional (ZMod 2) V := Module.Finite.of_finite
      have : Subsingleton V := Module.finrank_zero_iff.mp (by simpa using hm)
      rw [arf_subsingleton] at harf
      exact absurd harf zero_ne_one
    · exact hpos
  have hz := q.card_filter_apply_eq_zero_of_finrank_eq_two_mul hq hm hm_pos
  have hle : 2 ^ (m - 1) ≤ 2 ^ (2 * m - 1) :=
    Nat.pow_le_pow_right (by omega) (by omega)
  have hz' : ((Finset.univ.filter fun v : V ↦ q v = 0).card : ℤ) =
      ((2 ^ (2 * m - 1) - 2 ^ (m - 1) : ℕ) : ℤ) := by
    rw [Nat.cast_sub hle]
    push_cast
    rw [harf, ZMod.val_one] at hz
    linarith
  exact Int.ofNat.inj hz'

end ZeroCount

section LagrangianCriterion

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]

/-- The standard symplectic basis of `Fin m → Fin 2 → ZMod 2` indexed by `Fin m ⊕ Fin m`, sending
`inl i` to `Pi.single i ![1, 0]` and `inr i` to `Pi.single i ![0, 1]`. -/
private noncomputable def arfNormalFormBasis (m : ℕ) :
    Module.Basis (Fin m ⊕ Fin m) (ZMod 2) (Fin m → Fin 2 → ZMod 2) :=
  Module.Basis.ofEquivFun
    { toFun := fun f ↦ Sum.elim (fun i ↦ f i 0) (fun i ↦ f i 1)
      invFun := fun g i ↦ ![g (Sum.inl i), g (Sum.inr i)]
      map_add' := fun f₁ f₂ ↦ by ext x; rcases x with i | i <;> simp
      map_smul' := fun r f ↦ by ext x; rcases x with i | i <;> simp
      left_inv := fun f ↦ by ext i j; fin_cases j <;> simp
      right_inv := fun g ↦ by ext x; rcases x with i | i <;> simp }

private theorem arfNormalFormBasis_inl (m : ℕ) (i : Fin m) :
    arfNormalFormBasis m (Sum.inl i) = Pi.single i ![1, 0] := by
  ext j k
  rcases eq_or_ne j i with rfl | hji
  · fin_cases k <;> simp [arfNormalFormBasis, Module.Basis.coe_ofEquivFun]
  · fin_cases k <;> simp [arfNormalFormBasis, Module.Basis.coe_ofEquivFun, hji]

private theorem arfNormalFormBasis_inr (m : ℕ) (i : Fin m) :
    arfNormalFormBasis m (Sum.inr i) = Pi.single i ![0, 1] := by
  ext j k
  rcases eq_or_ne j i with rfl | hji
  · fin_cases k <;> simp [arfNormalFormBasis, Module.Basis.coe_ofEquivFun]
  · fin_cases k <;> simp [arfNormalFormBasis, Module.Basis.coe_ofEquivFun, hji]

private theorem toMatrix_polarBilin_arfNormalForm_zero (m : ℕ) :
    LinearMap.BilinForm.toMatrix (arfNormalFormBasis m) (arfNormalForm m 0).polarBilin =
      Matrix.J (Fin m) (ZMod 2) := by
  rw [toMatrix_polarBilin_eq_J_iff]
  refine ⟨fun i j ↦ ?_, fun i j ↦ ?_, fun i j ↦ ?_⟩ <;>
    simp only [arfNormalFormBasis_inl, arfNormalFormBasis_inr, arfNormalForm_zero_right,
      QuadraticMap.Ring.polar_pi]
  · refine Finset.sum_eq_zero fun k _ ↦ ?_
    by_cases hki : k = i <;> by_cases hkj : k = j <;> simp_all
  · refine Finset.sum_eq_zero fun k _ ↦ ?_
    by_cases hki : k = i <;> by_cases hkj : k = j <;> simp_all
  · rw [Finset.sum_eq_single i (fun k _ hki ↦ ?_) (fun hi ↦ absurd (Finset.mem_univ i) hi)]
    · by_cases hij : i = j <;> simp [hij]
    · simp [Pi.single_eq_of_ne hki]

/-- **Hyperbolic symplectic basis criterion.** A finite-dimensional quadratic space `(V, q)` over
`ZMod 2` with nondegenerate polar form has `q.arf = 0` if and only if `V` admits a symplectic basis
whose basis vectors are all `q`-isotropic. -/
theorem arf_eq_zero_iff_exists_basis_toMatrix_eq_J_apply_eq_zero
    {q : QuadraticForm (ZMod 2) V} (hq : q.polarBilin.Nondegenerate) :
    q.arf = 0 ↔
      ∃ (m : ℕ) (b : Module.Basis (Fin m ⊕ Fin m) (ZMod 2) V),
        LinearMap.BilinForm.toMatrix b q.polarBilin = Matrix.J (Fin m) (ZMod 2) ∧
        (∀ i, q (b (Sum.inl i)) = 0) ∧ (∀ i, q (b (Sum.inr i)) = 0) := by
  refine ⟨fun harf ↦ ?_, fun ⟨m, b, hb, h₀, _⟩ ↦ ?_⟩
  · have heqv := q.equivalent_arfNormalForm hq
    set m := Module.finrank (ZMod 2) V / 2
    rw [harf] at heqv
    obtain ⟨e⟩ := heqv.symm
    let b₀ := arfNormalFormBasis m
    have hb : LinearMap.BilinForm.toMatrix (b₀.map e.toLinearEquiv) q.polarBilin =
        Matrix.J (Fin m) (ZMod 2) := by
      rw [← toMatrix_polarBilin_arfNormalForm_zero m]
      ext x y
      simp only [b₀, LinearMap.BilinForm.toMatrix_apply, Module.Basis.map_apply,
        IsometryEquiv.coe_toLinearEquiv, polarBilin_apply_apply, IsometryEquiv.polar_apply]
    refine ⟨m, b₀.map e.toLinearEquiv, hb, fun i ↦ ?_, fun i ↦ ?_⟩
    · simp only [Module.Basis.map_apply, IsometryEquiv.coe_toLinearEquiv, e.map_app, b₀,
        arfNormalFormBasis_inl, arfNormalForm_zero_right, QuadraticMap.pi_apply]
      refine Finset.sum_eq_zero fun k _ ↦ ?_
      by_cases hki : k = i <;> simp [hki]
    · simp only [Module.Basis.map_apply, IsometryEquiv.coe_toLinearEquiv, e.map_app, b₀,
        arfNormalFormBasis_inr, arfNormalForm_zero_right, QuadraticMap.pi_apply]
      refine Finset.sum_eq_zero fun k _ ↦ ?_
      by_cases hki : k = i <;> simp [hki]
  · rw [q.arf_eq_sum_of_toMatrix_eq_J b hb]
    simp [h₀]

/-- **Lagrangian vanishing criterion for the Arf invariant.** A finite-dimensional quadratic space
`(V, q)` over `ZMod 2` with nondegenerate polar form has `q.arf = 0` if and only if `V` contains a
Lagrangian subspace `W = Wᗮ` on which `q` vanishes identically. -/
theorem arf_eq_zero_iff_exists_isTotallyIsotropic_eq_orthogonal
    {q : QuadraticForm (ZMod 2) V} (hq : q.polarBilin.Nondegenerate) :
    q.arf = 0 ↔
      ∃ W : Submodule (ZMod 2) V,
        q.IsTotallyIsotropic W ∧ W = LinearMap.BilinForm.orthogonal q.polarBilin W := by
  refine ⟨fun harf ↦ ?_, fun ⟨W, hW, horth⟩ ↦ ?_⟩
  · have heqv := q.equivalent_arfNormalForm hq
    rw [harf] at heqv
    obtain ⟨e⟩ := heqv.symm
    set m := Module.finrank (ZMod 2) V / 2
    let f : (Fin m → ZMod 2) →ₗ[ZMod 2] (Fin m → Fin 2 → ZMod 2) :=
      { toFun := fun u i ↦ ![u i, 0]
        map_add' := fun u v ↦ by ext i j; fin_cases j <;> simp
        map_smul' := fun r u ↦ by ext i j; fin_cases j <;> simp }
    have hf_inj : Function.Injective f := fun u v huv ↦
      funext fun i ↦ congrFun (congrFun huv i) 0
    have hU_iso : (arfNormalForm m 0).IsTotallyIsotropic (LinearMap.range f) := by
      rw [isTotallyIsotropic_iff]
      rintro _ ⟨u, rfl⟩
      simp [f]
    let W : Submodule (ZMod 2) V := (LinearMap.range f).map e.toLinearEquiv.toLinearMap
    have hW_iso : q.IsTotallyIsotropic W := by
      rw [← isTotallyIsotropic_comp_iff]
      refine isTotallyIsotropic_iff.mpr fun x hx ↦ ?_
      simpa [e.map_app] using hU_iso.apply_eq_zero hx
    have hW_dim : 2 * Module.finrank (ZMod 2) W = Module.finrank (ZMod 2) V := by
      have hdimV : Module.finrank (ZMod 2) (Fin m → Fin 2 → ZMod 2) = Module.finrank (ZMod 2) V :=
        e.toLinearEquiv.finrank_eq
      rw [LinearEquiv.finrank_map_eq, LinearMap.finrank_range_of_inj hf_inj, ← hdimV]
      simp [Module.finrank_pi_fintype, mul_comm]
    exact ⟨W, hW_iso, (hW_iso.eq_orthogonal_polarBilin_iff hq).mpr hW_dim⟩
  · let eW := Module.finBasis (ZMod 2) W
    obtain ⟨b, hb, hinl⟩ :=
      LinearMap.BilinForm.IsAlt.exists_basis_toMatrix_eq_J_inl_eq q.isAlt_polarBilin hq eW horth
    rw [q.arf_eq_sum_of_toMatrix_eq_J b hb]
    refine Finset.sum_eq_zero fun i _ ↦ ?_
    rw [hinl i, hW.apply_eq_zero (eW i).2, zero_mul]

omit [FiniteDimensional (ZMod 2) V] in
/-- **Half-dimensional `q`-zero subspace criterion.** A quadratic space `(V, q)` over `ZMod 2` with
nondegenerate polar form has `q.arf = 0` if and only if `V` contains a `q`-totally isotropic
subspace `W` satisfying `2 * finrank (ZMod 2) W = finrank (ZMod 2) V` (including the
infinite-dimensional junk case via `W = ⊥`). -/
theorem arf_eq_zero_iff_exists_isTotallyIsotropic_two_mul_finrank_eq
    {q : QuadraticForm (ZMod 2) V} (hq : q.polarBilin.Nondegenerate) :
    q.arf = 0 ↔
      ∃ W : Submodule (ZMod 2) V,
        q.IsTotallyIsotropic W ∧ 2 * Module.finrank (ZMod 2) W = Module.finrank (ZMod 2) V := by
  by_cases hfin : FiniteDimensional (ZMod 2) V
  · rw [arf_eq_zero_iff_exists_isTotallyIsotropic_eq_orthogonal hq]
    exact exists_congr fun W ↦ and_congr_right fun hW ↦ hW.eq_orthogonal_polarBilin_iff hq
  · exact ⟨fun _ ↦ ⟨⊥, isTotallyIsotropic_bot, by simp [Module.finrank_of_not_finite hfin]⟩,
      fun _ ↦ arf_of_not_finiteDimensional hfin⟩

end LagrangianCriterion

end QuadraticMap

namespace TauCeti

section Examples

/-! ### Kernel-checked verification examples -/

/-- The hyperbolic plane `x₀ x₁` has Arf invariant `0`, Gauss sum `+2`, and `3` zeros, whereas the
anisotropic plane `x₀² + x₀ x₁ + x₁²` has Arf invariant `1`, Gauss sum `-2`, and `1` zero. -/
example :
    (symplecticPlane (ZMod 2) 0 0).arf = 0 ∧
    (symplecticPlane (ZMod 2) 0 0).gaussSum = 2 ∧
    (Finset.univ.filter fun v ↦ symplecticPlane (ZMod 2) 0 0 v = 0).card = 3 ∧
    (symplecticPlane (ZMod 2) 1 1).arf = 1 ∧
    (symplecticPlane (ZMod 2) 1 1).gaussSum = -2 ∧
    (Finset.univ.filter fun v ↦ symplecticPlane (ZMod 2) 1 1 v = 0).card = 1 := by
  refine ⟨by simp, by simp, ?_, by simp, by simp [ZMod.val_one], ?_⟩
  · exact (symplecticPlane (ZMod 2) 0 0).card_filter_apply_eq_zero_of_arf_eq_zero
      (nondegenerate_polarBilin_symplecticPlane 0 0) (by simp) (m := 1) (by simp) (le_refl 1)
  · exact (symplecticPlane (ZMod 2) 1 1).card_filter_apply_eq_zero_of_arf_eq_one
      (by simp) (m := 1) (by simp)

/-- On `(ZMod 2)⁴`, both `q₀ ⊕ q₀` and `q₁ ⊕ q₁` have Arf invariant `0`, Gauss sum `+4`, and `10`
zeros, whereas `q₀ ⊕ q₁` has Arf invariant `1`, Gauss sum `-4`, and `6` zeros. -/
example :
    ((symplecticPlane (ZMod 2) 0 0).prod (symplecticPlane (ZMod 2) 0 0)).arf = 0 ∧
    ((symplecticPlane (ZMod 2) 0 0).prod (symplecticPlane (ZMod 2) 0 0)).gaussSum = 4 ∧
    (Finset.univ.filter fun v ↦
      ((symplecticPlane (ZMod 2) 0 0).prod (symplecticPlane (ZMod 2) 0 0)) v = 0).card = 10 ∧
    ((symplecticPlane (ZMod 2) 1 1).prod (symplecticPlane (ZMod 2) 1 1)).arf = 0 ∧
    ((symplecticPlane (ZMod 2) 1 1).prod (symplecticPlane (ZMod 2) 1 1)).gaussSum = 4 ∧
    (Finset.univ.filter fun v ↦
      ((symplecticPlane (ZMod 2) 1 1).prod (symplecticPlane (ZMod 2) 1 1)) v = 0).card = 10 ∧
    ((symplecticPlane (ZMod 2) 0 0).prod (symplecticPlane (ZMod 2) 1 1)).arf = 1 ∧
    ((symplecticPlane (ZMod 2) 0 0).prod (symplecticPlane (ZMod 2) 1 1)).gaussSum = -4 ∧
    (Finset.univ.filter fun v ↦
      ((symplecticPlane (ZMod 2) 0 0).prod (symplecticPlane (ZMod 2) 1 1)) v = 0).card = 6 := by
  have hnd0 := nondegenerate_polarBilin_symplecticPlane (0 : ZMod 2) 0
  have hnd1 := nondegenerate_polarBilin_symplecticPlane (1 : ZMod 2) 1
  have hdim : Module.finrank (ZMod 2) ((Fin 2 → ZMod 2) × (Fin 2 → ZMod 2)) = 2 * 2 := by simp
  have harf00 : ((symplecticPlane (ZMod 2) 0 0).prod (symplecticPlane (ZMod 2) 0 0)).arf = 0 := by
    rw [QuadraticMap.arf_prod hnd0 hnd0]; simp
  have harf11 : ((symplecticPlane (ZMod 2) 1 1).prod (symplecticPlane (ZMod 2) 1 1)).arf = 0 := by
    rw [QuadraticMap.arf_prod hnd1 hnd1]; simp
  have harf01 : ((symplecticPlane (ZMod 2) 0 0).prod (symplecticPlane (ZMod 2) 1 1)).arf = 1 := by
    rw [QuadraticMap.arf_prod hnd0 hnd1]; simp
  refine ⟨harf00, by simp, ?_, harf11, by simp [ZMod.val_one], ?_,
    harf01, by simp [ZMod.val_one], ?_⟩
  · exact QuadraticMap.card_filter_apply_eq_zero_of_arf_eq_zero
      (QuadraticMap.nondegenerate_polarBilin_prod_iff.mpr ⟨hnd0, hnd0⟩) harf00 hdim (by omega)
  · exact QuadraticMap.card_filter_apply_eq_zero_of_arf_eq_zero
      (QuadraticMap.nondegenerate_polarBilin_prod_iff.mpr ⟨hnd1, hnd1⟩) harf11 hdim (by omega)
  · exact QuadraticMap.card_filter_apply_eq_zero_of_arf_eq_one harf01 hdim

/-- Symplectic basis change on `q₀(x) = x₀ x₁`: replacing `(![1, 0], ![0, 1])` by
`(![1, 1], ![0, 1])` preserves the symplectic pairing (`polar q₀ ![1, 1] ![0, 1] = 1`), changes the
naive sum `q₀(e) + q₀(f)` from `0` to `1`, and preserves the Arf product `q₀(e) * q₀(f) = 0`. -/
example :
    let q₀ := symplecticPlane (ZMod 2) 0 0
    QuadraticMap.polar q₀ ![1, 1] ![0, 1] = 1 ∧
    q₀ ![1, 0] + q₀ ![0, 1] = 0 ∧
    q₀ ![1, 1] + q₀ ![0, 1] = 1 ∧
    q₀ ![1, 0] * q₀ ![0, 1] = q₀ ![1, 1] * q₀ ![0, 1] := by
  simp

/-- On the zero-dimensional space (`m = 0`), `arfNormalForm 0 0` has Arf invariant `0`, Gauss sum
`1`, and `1` zero. -/
example :
    (arfNormalForm 0 0).arf = 0 ∧
    (arfNormalForm 0 0).gaussSum = 1 ∧
    (Finset.univ.filter fun v ↦ arfNormalForm 0 0 v = 0).card = 1 :=
  ⟨by simp, by simp, by simp⟩

end Examples

end TauCeti
