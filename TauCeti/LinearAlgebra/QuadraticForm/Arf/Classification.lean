/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.QuadraticForm.Arf.Basic
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.Tactic.FinCases
import TauCeti.Data.ZMod.Two
import TauCeti.LinearAlgebra.QuadraticForm.Prod

/-!
# Normal forms, Arf's classification theorem, and quadratic Lagrangians over `𝔽₂`

Every binary symplectic plane `TauCeti.symplecticPlane (ZMod 2) a b` over `ZMod 2` is explicitly
isometric to `TauCeti.symplecticPlane (ZMod 2) (a * b) (a * b)`: either the hyperbolic plane
`symplecticPlane (ZMod 2) 0 0` (Arf invariant `0`) or the anisotropic plane
`symplecticPlane (ZMod 2) 1 1` (Arf invariant `1`). Combining this binary reduction with
`QuadraticMap.isometryEquivPiSymplecticPlane` and the four-dimensional relation
`TauCeti.isometryEquivSymplecticPlaneOneProd` (`11 ⊕ 11 ≃qᵢ 00 ⊕ 00`) yields the complete
classification of finite-dimensional quadratic forms over `ZMod 2` with nondegenerate polar form:

1. **Canonical normal forms.** For `Module.finrank (ZMod 2) V = 2 * m` and `Q.polarBilin`
   nondegenerate, `Q.arf = 0` if and only if `Q` is isometric to `m` hyperbolic planes
   `symplecticPlane (ZMod 2) 0 0`, while `Q.arf = 1` if and only if `m = k + 1` and `Q` is
   isometric to `symplecticPlane (ZMod 2) 1 1` orthogonal-summed with `k` hyperbolic planes.
2. **Arf's theorem over `𝔽₂`.** Two finite-dimensional quadratic spaces over `ZMod 2` with
   nondegenerate polar forms are isometric if and only if they have the same dimension and the same
   Arf invariant (`QuadraticMap.equivalent_iff_finrank_eq_and_arf_eq`).
3. **Quadratic Lagrangian characterization of `Q.arf = 0`.** A finite-dimensional quadratic space
   `(V, Q)` over `ZMod 2` with nondegenerate polar form satisfies `Q.arf = 0` if and only if `V`
   contains a `Q`-totally-isotropic subspace equal to its own polar orthogonal complement,
   equivalently of half the ambient dimension.

## Main definitions

* `TauCeti.isometryEquivSymplecticPlaneMul`: explicit involutive isometry from
  `symplecticPlane (ZMod 2) a b` to `symplecticPlane (ZMod 2) (a * b) (a * b)`.

## Main results

* `TauCeti.equivalent_symplecticPlane_iff`: `symplecticPlane (ZMod 2) a b` and
  `symplecticPlane (ZMod 2) c d` are equivalent if and only if `a * b = c * d`.
* `QuadraticMap.arf_eq_zero_iff_equivalent_pi_symplecticPlane_zero`,
  `QuadraticMap.arf_eq_one_iff_exists_equivalent_symplecticPlane_one_prod_pi`,
  `QuadraticMap.arf_eq_one_iff_equivalent_symplecticPlane_one_prod_pi`: normal-form
  characterizations of `Q.arf = 0` and `Q.arf = 1`.
* `QuadraticMap.equivalent_iff_finrank_eq_and_arf_eq`: Arf's classification theorem over `ZMod 2`.
* `QuadraticMap.arf_eq_zero_iff_exists_isTotallyIsotropic_orthogonal_eq`,
  `QuadraticMap.arf_eq_zero_iff_exists_isTotallyIsotropic_two_mul_finrank_eq`,
  `QuadraticMap.arf_eq_zero_iff_exists_isTotallyIsotropic_finrank_eq`: half-dimensional
  `Q`-totally-isotropic (quadratic Lagrangian) criteria for `Q.arf = 0`.

## References

* C. Arf, *Untersuchungen über quadratische Formen in Körpern der Charakteristik 2 (Teil I)*, J.
  Reine Angew. Math. **183** (1941), 148--167.
* W. Browder, *Surgery on Simply-Connected Manifolds*, Ergebnisse der Mathematik und ihrer
  Grenzgebiete 65, Springer (1972), Chapter III, §1.
* R. Elman, N. Karpenko, and A. Merkurjev, *The Algebraic and Geometric Theory of Quadratic Forms*,
  American Mathematical Society Colloquium Publications 56 (2008), Chapter II, §13.
* A. Pyronneau, *The Arf and Rohklin's invariant* (January 2024), §2.1, Lemma 2.13 and
  Theorem 2.15, pp. 4--5.
-/

public section

namespace TauCeti

private def symplecticPlaneMulLinearMap (a b : ZMod 2) :
    (Fin 2 → ZMod 2) →ₗ[ZMod 2] (Fin 2 → ZMod 2) where
  toFun x := ![x 0 + (1 + a) * b * x 1, a * (1 + b) * x 0 + x 1]
  map_add' x y := by
    ext i
    fin_cases i <;> simp [mul_add, add_assoc, add_left_comm]
  map_smul' r x := by
    ext i
    fin_cases i <;> simp [mul_add, mul_assoc, mul_left_comm]

private theorem involutive_symplecticPlaneMulLinearMap (a b : ZMod 2) :
    Function.Involutive (symplecticPlaneMulLinearMap a b) := fun x ↦ by
  have h : ∀ a b x₀ x₁ : ZMod 2,
      (x₀ + (1 + a) * b * x₁ + (1 + a) * b * (a * (1 + b) * x₀ + x₁) = x₀) ∧
      (a * (1 + b) * (x₀ + (1 + a) * b * x₁) + (a * (1 + b) * x₀ + x₁) = x₁) := by decide
  ext i
  fin_cases i <;>
    simp only [symplecticPlaneMulLinearMap, LinearMap.coe_mk, AddHom.coe_mk,
      Fin.zero_eta, Fin.mk_one, Matrix.cons_val_zero, Matrix.cons_val_one]
  · exact (h a b (x 0) (x 1)).1
  · exact (h a b (x 0) (x 1)).2

/-- Over `ZMod 2`, every binary symplectic plane `symplecticPlane (ZMod 2) a b` is explicitly
isometric via an involution to `symplecticPlane (ZMod 2) (a * b) (a * b)` (either the hyperbolic
plane `symplecticPlane (ZMod 2) 0 0` or the anisotropic plane `symplecticPlane (ZMod 2) 1 1`). -/
def isometryEquivSymplecticPlaneMul (a b : ZMod 2) :
    (symplecticPlane (ZMod 2) a b).IsometryEquiv (symplecticPlane (ZMod 2) (a * b) (a * b)) where
  toLinearEquiv := LinearEquiv.ofInvolutive (symplecticPlaneMulLinearMap a b)
    (involutive_symplecticPlaneMulLinearMap a b)
  map_app' x := by
    have h : ∀ a b x₀ x₁ : ZMod 2,
        a * b * (x₀ + (1 + a) * b * x₁) ^ 2 +
          (x₀ + (1 + a) * b * x₁) * (a * (1 + b) * x₀ + x₁) +
          a * b * (a * (1 + b) * x₀ + x₁) ^ 2 =
        a * x₀ ^ 2 + x₀ * x₁ + b * x₁ ^ 2 := by decide
    simp only [symplecticPlaneMulLinearMap, symplecticPlane_apply]
    exact h a b (x 0) (x 1)

/-- Coordinates of `TauCeti.isometryEquivSymplecticPlaneMul`. -/
@[simp]
theorem isometryEquivSymplecticPlaneMul_apply (a b : ZMod 2) (x : Fin 2 → ZMod 2) :
    isometryEquivSymplecticPlaneMul a b x =
      ![x 0 + (1 + a) * b * x 1, a * (1 + b) * x 0 + x 1] :=
  (rfl)

/-- Coordinates of the inverse of `TauCeti.isometryEquivSymplecticPlaneMul`. -/
@[simp]
theorem isometryEquivSymplecticPlaneMul_symm_apply (a b : ZMod 2) (x : Fin 2 → ZMod 2) :
    (isometryEquivSymplecticPlaneMul a b).symm x =
      ![x 0 + (1 + a) * b * x 1, a * (1 + b) * x 0 + x 1] :=
  (rfl)

/-- Binary symplectic planes over `ZMod 2` are isometric if and only if the products of their
diagonal coefficients agree. -/
theorem equivalent_symplecticPlane_iff {a b c d : ZMod 2} :
    (symplecticPlane (ZMod 2) a b).Equivalent (symplecticPlane (ZMod 2) c d) ↔ a * b = c * d := by
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · simpa using h.arf_eq
  · exact ⟨(isometryEquivSymplecticPlaneMul a b).trans
      (h ▸ (isometryEquivSymplecticPlaneMul c d).symm)⟩

/-- The orthogonal sum of `m` hyperbolic planes `symplecticPlane (ZMod 2) 0 0` has Arf invariant
`0`. -/
@[simp]
theorem arf_pi_symplecticPlane_zero (m : ℕ) :
    (QuadraticMap.pi fun _ : Fin m ↦ symplecticPlane (ZMod 2) 0 0).arf = 0 := by
  rw [QuadraticMap.arf_pi fun _ ↦ nondegenerate_polarBilin_symplecticPlane 0 0]
  simp

/-- The orthogonal sum of one anisotropic plane `symplecticPlane (ZMod 2) 1 1` and `k` hyperbolic
planes `symplecticPlane (ZMod 2) 0 0` has Arf invariant `1`. -/
@[simp]
theorem arf_symplecticPlane_one_prod_pi_zero (k : ℕ) :
    ((symplecticPlane (ZMod 2) 1 1).prod
      (QuadraticMap.pi fun _ : Fin k ↦ symplecticPlane (ZMod 2) 0 0)).arf = 1 := by
  rw [QuadraticMap.arf_prod (nondegenerate_polarBilin_symplecticPlane 1 1)
    (QuadraticMap.nondegenerate_polarBilin_pi_iff.mpr fun _ ↦
      nondegenerate_polarBilin_symplecticPlane 0 0),
    arf_symplecticPlane, arf_pi_symplecticPlane_zero]
  rfl

end TauCeti

namespace QuadraticMap

open TauCeti

/-- Adjoining a hyperbolic plane to `11 ⊕ 00^k` gives `11 ⊕ 00^(k + 1)`. -/
private def isometryEquivZeroProdOneProdPiZero (k : ℕ) :
    ((symplecticPlane (ZMod 2) 0 0).prod
      ((symplecticPlane (ZMod 2) 1 1).prod
        (QuadraticMap.pi fun _ : Fin k ↦ symplecticPlane (ZMod 2) 0 0))).IsometryEquiv
      ((symplecticPlane (ZMod 2) 1 1).prod
        (QuadraticMap.pi fun _ : Fin (k + 1) ↦ symplecticPlane (ZMod 2) 0 0)) :=
  (IsometryEquiv.prodLeftComm _ _ _).trans
    ((IsometryEquiv.refl _).prod
      (IsometryEquiv.consPi fun _ : Fin (k + 1) ↦ symplecticPlane (ZMod 2) 0 0))

/-- Cancelling the pair of anisotropic planes in `11 ⊕ (11 ⊕ 00^k)` via `11 ⊕ 11 ≃qᵢ 00 ⊕ 00`
gives `00^(k + 2)`. -/
private def isometryEquivOneProdOneProdPiZero (k : ℕ) :
    ((symplecticPlane (ZMod 2) 1 1).prod
      ((symplecticPlane (ZMod 2) 1 1).prod
        (QuadraticMap.pi fun _ : Fin k ↦ symplecticPlane (ZMod 2) 0 0))).IsometryEquiv
      (QuadraticMap.pi fun _ : Fin (k + 2) ↦ symplecticPlane (ZMod 2) 0 0) :=
  (((((IsometryEquiv.prodAssoc _ _ _).symm.trans
    (isometryEquivSymplecticPlaneOneProd.prod (IsometryEquiv.refl _))).trans
    (IsometryEquiv.prodAssoc _ _ _)).trans
    ((IsometryEquiv.refl _).prod
      (IsometryEquiv.consPi fun _ : Fin (k + 1) ↦ symplecticPlane (ZMod 2) 0 0))).trans
    (IsometryEquiv.consPi fun _ : Fin (k + 2) ↦ symplecticPlane (ZMod 2) 0 0))

/-- Simultaneous normal-form reduction of an orthogonal sum of normalized planes
`symplecticPlane (ZMod 2) (c i) (c i)`: pairs of anisotropic planes cancel into pairs of hyperbolic
planes via `TauCeti.isometryEquivSymplecticPlaneOneProd`. -/
private theorem normalForm_pi_symplecticPlane :
    ∀ (m : ℕ) (c : Fin m → ZMod 2),
      (∑ i, c i = 0 →
        (QuadraticMap.pi fun i : Fin m ↦ symplecticPlane (ZMod 2) (c i) (c i)).Equivalent
          (QuadraticMap.pi fun _ : Fin m ↦ symplecticPlane (ZMod 2) 0 0)) ∧
      (∑ i, c i = 1 →
        ∃ k : ℕ, m = k + 1 ∧
          (QuadraticMap.pi fun i : Fin m ↦ symplecticPlane (ZMod 2) (c i) (c i)).Equivalent
            ((symplecticPlane (ZMod 2) 1 1).prod
              (QuadraticMap.pi fun _ : Fin k ↦ symplecticPlane (ZMod 2) 0 0)))
  | 0, c => by
      refine ⟨fun _ ↦ ?_, fun h1 ↦ by simp at h1⟩
      have hfun : (fun i : Fin 0 ↦ symplecticPlane (ZMod 2) (c i) (c i)) =
          fun _ : Fin 0 ↦ symplecticPlane (ZMod 2) 0 0 :=
        funext fun i ↦ Fin.elim0 i
      rw [hfun]
      exact ⟨IsometryEquiv.refl _⟩
  | m + 1, c => by
      let c' : Fin m → ZMod 2 := fun i ↦ c i.succ
      obtain ⟨ih0, ih1⟩ := normalForm_pi_symplecticPlane m c'
      -- Peel off the `0`-th plane and reduce the remaining `m` planes by the induction hypothesis.
      have esplit :
          (QuadraticMap.pi fun i : Fin (m + 1) ↦
            symplecticPlane (ZMod 2) (c i) (c i)).IsometryEquiv
            ((symplecticPlane (ZMod 2) (c 0) (c 0)).prod
              (QuadraticMap.pi fun i : Fin m ↦ symplecticPlane (ZMod 2) (c' i) (c' i))) :=
        (IsometryEquiv.consPi fun i : Fin (m + 1) ↦ symplecticPlane (ZMod 2) (c i) (c i)).symm
      refine ⟨fun hsum ↦ ?_, fun hsum ↦ ?_⟩
      · -- Even parity (`∑ i, c i = 0`): either `00 ⊕ 00^m` or `11 ⊕ (11 ⊕ 00^k)`.
        rw [Fin.sum_univ_succ] at hsum
        rcases (c 0).eq_zero_or_eq_one with hc0 | hc0
        · have hsum' : ∑ i, c' i = 0 := by simpa [c', hc0] using hsum
          obtain ⟨e'⟩ := ih0 hsum'
          rw [hc0] at esplit
          exact ⟨(esplit.trans ((IsometryEquiv.refl _).prod e')).trans
            (IsometryEquiv.consPi fun _ : Fin (m + 1) ↦ symplecticPlane (ZMod 2) 0 0)⟩
        · have hsum' : ∑ i, c' i = 1 :=
            (CharTwo.add_eq_zero.mp (by simpa [c', hc0] using hsum)).symm
          obtain ⟨k, rfl, ⟨e'⟩⟩ := ih1 hsum'
          rw [hc0] at esplit
          exact ⟨(esplit.trans ((IsometryEquiv.refl _).prod e')).trans
            (isometryEquivOneProdOneProdPiZero k)⟩
      · -- Odd parity (`∑ i, c i = 1`): either `00 ⊕ (11 ⊕ 00^k)` or `11 ⊕ 00^m`.
        rw [Fin.sum_univ_succ] at hsum
        rcases (c 0).eq_zero_or_eq_one with hc0 | hc0
        · have hsum' : ∑ i, c' i = 1 := by simpa [c', hc0] using hsum
          obtain ⟨k, rfl, ⟨e'⟩⟩ := ih1 hsum'
          rw [hc0] at esplit
          exact ⟨k + 1, rfl, ⟨(esplit.trans ((IsometryEquiv.refl _).prod e')).trans
            (isometryEquivZeroProdOneProdPiZero k)⟩⟩
        · have hsum' : ∑ i, c' i = 0 := by simpa [c', hc0] using hsum
          obtain ⟨e'⟩ := ih0 hsum'
          rw [hc0] at esplit
          exact ⟨m, rfl, ⟨esplit.trans ((IsometryEquiv.refl _).prod e')⟩⟩

section Classification

variable {V V₁ V₂ : Type*} [AddCommGroup V] [Module (ZMod 2) V]
  [AddCommGroup V₁] [Module (ZMod 2) V₁] [AddCommGroup V₂] [Module (ZMod 2) V₂]

/-- **Hyperbolic normal form (`Q.arf = 0`).** A finite-dimensional quadratic space over `ZMod 2` of
dimension `2 * m` with nondegenerate polar form has `Q.arf = 0` if and only if it is isometric to
the orthogonal sum of `m` hyperbolic planes `symplecticPlane (ZMod 2) 0 0`. -/
theorem arf_eq_zero_iff_equivalent_pi_symplecticPlane_zero [FiniteDimensional (ZMod 2) V]
    {Q : QuadraticForm (ZMod 2) V} (hQ : Q.polarBilin.Nondegenerate) {m : ℕ}
    (hdim : Module.finrank (ZMod 2) V = 2 * m) :
    Q.arf = 0 ↔ Q.Equivalent (QuadraticMap.pi fun _ : Fin m ↦ symplecticPlane (ZMod 2) 0 0) := by
  refine ⟨fun harf ↦ ?_, fun h ↦ h.arf_eq.trans (arf_pi_symplecticPlane_zero m)⟩
  obtain ⟨b, hb⟩ := Q.exists_basis_toMatrix_polarBilin_eq_J_of_finrank_eq hQ hdim
  let c : Fin m → ZMod 2 := fun i ↦ Q (b (Sum.inl i)) * Q (b (Sum.inr i))
  have hc_sum : ∑ i, c i = 0 := by
    rw [← Q.arf_eq_sum_of_toMatrix_polarBilin_eq_J hb, harf]
  obtain ⟨enorm⟩ := (normalForm_pi_symplecticPlane m c).1 hc_sum
  exact ⟨((Q.isometryEquivPiSymplecticPlane b hb).trans
    (IsometryEquiv.pi fun i ↦
      isometryEquivSymplecticPlaneMul (Q (b (Sum.inl i))) (Q (b (Sum.inr i))))).trans enorm⟩

/-- **Anisotropic normal form (`Q.arf = 1`).** A quadratic space over `ZMod 2` with
`Module.finrank (ZMod 2) V = 2 * m` has `Q.arf = 1` if and only if `m = k + 1` and `Q` is isometric
to `symplecticPlane (ZMod 2) 1 1` orthogonal-summed with `k` hyperbolic planes. -/
theorem arf_eq_one_iff_exists_equivalent_symplecticPlane_one_prod_pi
    {Q : QuadraticForm (ZMod 2) V} {m : ℕ} (hdim : Module.finrank (ZMod 2) V = 2 * m) :
    Q.arf = 1 ↔
      ∃ k : ℕ, m = k + 1 ∧
        Q.Equivalent
          ((symplecticPlane (ZMod 2) 1 1).prod
            (QuadraticMap.pi fun _ : Fin k ↦ symplecticPlane (ZMod 2) 0 0)) := by
  refine ⟨fun harf ↦ ?_, fun ⟨k, _, h⟩ ↦ h.arf_eq.trans (arf_symplecticPlane_one_prod_pi_zero k)⟩
  have hne : Q.arf ≠ 0 := by rw [harf]; decide
  have : FiniteDimensional (ZMod 2) V := Q.finiteDimensional_of_arf_ne_zero hne
  have hQ : Q.polarBilin.Nondegenerate := Q.nondegenerate_polarBilin_of_arf_ne_zero hne
  obtain ⟨b, hb⟩ := Q.exists_basis_toMatrix_polarBilin_eq_J_of_finrank_eq hQ hdim
  let c : Fin m → ZMod 2 := fun i ↦ Q (b (Sum.inl i)) * Q (b (Sum.inr i))
  have hc_sum : ∑ i, c i = 1 := by
    rw [← Q.arf_eq_sum_of_toMatrix_polarBilin_eq_J hb, harf]
  obtain ⟨k, hmk, ⟨enorm⟩⟩ := (normalForm_pi_symplecticPlane m c).2 hc_sum
  exact ⟨k, hmk, ⟨((Q.isometryEquivPiSymplecticPlane b hb).trans
    (IsometryEquiv.pi fun i ↦
      isometryEquivSymplecticPlaneMul (Q (b (Sum.inl i))) (Q (b (Sum.inr i))))).trans enorm⟩⟩

/-- When `Module.finrank (ZMod 2) V = 2 * (k + 1)`, `Q.arf = 1` if and only if `Q` is isometric to
`symplecticPlane (ZMod 2) 1 1` orthogonal-summed with `k` hyperbolic planes. -/
theorem arf_eq_one_iff_equivalent_symplecticPlane_one_prod_pi
    {Q : QuadraticForm (ZMod 2) V} {k : ℕ}
    (hdim : Module.finrank (ZMod 2) V = 2 * (k + 1)) :
    Q.arf = 1 ↔
      Q.Equivalent
        ((symplecticPlane (ZMod 2) 1 1).prod
          (QuadraticMap.pi fun _ : Fin k ↦ symplecticPlane (ZMod 2) 0 0)) := by
  rw [Q.arf_eq_one_iff_exists_equivalent_symplecticPlane_one_prod_pi hdim]
  refine ⟨fun ⟨k', hk', heq⟩ ↦ ?_, fun heq ↦ ⟨k, rfl, heq⟩⟩
  obtain rfl : k' = k := by omega
  exact heq

/-- Any quadratic space over `ZMod 2` with `Q.arf = 1` has positive `finrank`. -/
theorem finrank_pos_of_arf_eq_one {Q : QuadraticForm (ZMod 2) V} (harf : Q.arf = 1) :
    0 < Module.finrank (ZMod 2) V := by
  have : FiniteDimensional (ZMod 2) V :=
    Q.finiteDimensional_of_arf_ne_zero (by rw [harf]; decide)
  by_contra h
  have : Subsingleton V := Module.finrank_zero_iff.mp (Nat.eq_zero_of_not_pos h)
  exact absurd (Q.arf_subsingleton.symm.trans harf) (by decide)

/-- **Arf's theorem over `𝔽₂`.** Two finite-dimensional quadratic spaces over `ZMod 2` with
nondegenerate polar bilinear forms are isometric if and only if they have the same dimension and the
same Arf invariant. -/
theorem equivalent_iff_finrank_eq_and_arf_eq
    [FiniteDimensional (ZMod 2) V₁] [FiniteDimensional (ZMod 2) V₂]
    {Q₁ : QuadraticForm (ZMod 2) V₁} {Q₂ : QuadraticForm (ZMod 2) V₂}
    (hQ₁ : Q₁.polarBilin.Nondegenerate) (hQ₂ : Q₂.polarBilin.Nondegenerate) :
    Q₁.Equivalent Q₂ ↔
      Module.finrank (ZMod 2) V₁ = Module.finrank (ZMod 2) V₂ ∧ Q₁.arf = Q₂.arf := by
  refine ⟨fun ⟨e⟩ ↦ ⟨e.toLinearEquiv.finrank_eq, e.arf_eq⟩, fun ⟨hdim, harf⟩ ↦ ?_⟩
  obtain ⟨m, hm₁⟩ := Q₁.even_finrank_of_nondegenerate_polarBilin hQ₁
  have hdim₁ : Module.finrank (ZMod 2) V₁ = 2 * m := by omega
  have hdim₂ : Module.finrank (ZMod 2) V₂ = 2 * m := hdim.symm.trans hdim₁
  rcases Q₁.arf.eq_zero_or_eq_one with h0 | h1
  · obtain ⟨e₁⟩ := (Q₁.arf_eq_zero_iff_equivalent_pi_symplecticPlane_zero hQ₁ hdim₁).mp h0
    obtain ⟨e₂⟩ :=
      (Q₂.arf_eq_zero_iff_equivalent_pi_symplecticPlane_zero hQ₂ hdim₂).mp (harf.symm.trans h0)
    exact ⟨e₁.trans e₂.symm⟩
  · obtain ⟨k, rfl, ⟨e₁⟩⟩ :=
      (Q₁.arf_eq_one_iff_exists_equivalent_symplecticPlane_one_prod_pi hdim₁).mp h1
    obtain ⟨e₂⟩ :=
      (Q₂.arf_eq_one_iff_equivalent_symplecticPlane_one_prod_pi hdim₂).mp (harf.symm.trans h1)
    exact ⟨e₁.trans e₂.symm⟩

/-- **Quadratic Lagrangian criterion for `Q.arf = 0` (fixed half-dimension `m`).** For a
finite-dimensional quadratic space over `ZMod 2` of dimension `2 * m` with nondegenerate polar
form, `Q.arf = 0` if and only if `V` contains an `m`-dimensional `Q`-totally-isotropic subspace. -/
theorem arf_eq_zero_iff_exists_isTotallyIsotropic_finrank_eq [FiniteDimensional (ZMod 2) V]
    {Q : QuadraticForm (ZMod 2) V} (hQ : Q.polarBilin.Nondegenerate) {m : ℕ}
    (hdim : Module.finrank (ZMod 2) V = 2 * m) :
    Q.arf = 0 ↔
      ∃ U : Submodule (ZMod 2) V, Q.IsTotallyIsotropic U ∧ Module.finrank (ZMod 2) U = m := by
  rw [Q.arf_eq_zero_iff_equivalent_pi_symplecticPlane_zero hQ hdim,
    Q.equivalent_pi_symplecticPlane_zero_iff_exists_isTotallyIsotropic_finrank_eq hQ hdim]

/-- **Quadratic Lagrangian criterion for `Q.arf = 0` (self-orthogonal form).** For a
finite-dimensional quadratic space over `ZMod 2` with nondegenerate polar form, `Q.arf = 0` if and
only if `V` contains a `Q`-totally-isotropic subspace equal to its own `Q.polarBilin`-orthogonal
complement. -/
theorem arf_eq_zero_iff_exists_isTotallyIsotropic_orthogonal_eq [FiniteDimensional (ZMod 2) V]
    {Q : QuadraticForm (ZMod 2) V} (hQ : Q.polarBilin.Nondegenerate) :
    Q.arf = 0 ↔
      ∃ U : Submodule (ZMod 2) V,
        Q.IsTotallyIsotropic U ∧ LinearMap.BilinForm.orthogonal Q.polarBilin U = U := by
  obtain ⟨m, hm⟩ := Q.even_finrank_of_nondegenerate_polarBilin hQ
  have hdim : Module.finrank (ZMod 2) V = 2 * m := by omega
  rw [Q.arf_eq_zero_iff_equivalent_pi_symplecticPlane_zero hQ hdim,
    Q.equivalent_pi_symplecticPlane_zero_iff_exists_isTotallyIsotropic_orthogonal_eq hQ hdim]

/-- **Quadratic Lagrangian criterion for `Q.arf = 0` (ambient dimension form).** For a
finite-dimensional quadratic space over `ZMod 2` with nondegenerate polar form, `Q.arf = 0` if and
only if `V` contains a `Q`-totally-isotropic subspace of half the ambient dimension. -/
theorem arf_eq_zero_iff_exists_isTotallyIsotropic_two_mul_finrank_eq
    [FiniteDimensional (ZMod 2) V] {Q : QuadraticForm (ZMod 2) V}
    (hQ : Q.polarBilin.Nondegenerate) :
    Q.arf = 0 ↔
      ∃ U : Submodule (ZMod 2) V,
        Q.IsTotallyIsotropic U ∧ 2 * Module.finrank (ZMod 2) U = Module.finrank (ZMod 2) V := by
  obtain ⟨m, hm⟩ := Q.even_finrank_of_nondegenerate_polarBilin hQ
  have hdim : Module.finrank (ZMod 2) V = 2 * m := by omega
  rw [Q.arf_eq_zero_iff_equivalent_pi_symplecticPlane_zero hQ hdim,
    Q.equivalent_pi_symplecticPlane_zero_iff_exists_isTotallyIsotropic_two_mul_finrank_eq hQ hdim]

end Classification

end QuadraticMap
