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
  American Mathematical Society Colloquium Publications 56 (2008), Chapter II, §14.
-/

public section

namespace TauCeti

/-- Over `ZMod 2`, every binary symplectic plane `symplecticPlane (ZMod 2) a b` is explicitly
isometric via an involution to `symplecticPlane (ZMod 2) (a * b) (a * b)` (either the hyperbolic
plane `symplecticPlane (ZMod 2) 0 0` or the anisotropic plane `symplecticPlane (ZMod 2) 1 1`). -/
def isometryEquivSymplecticPlaneMul (a b : ZMod 2) :
    (symplecticPlane (ZMod 2) a b).IsometryEquiv (symplecticPlane (ZMod 2) (a * b) (a * b)) where
  toFun x := ![x 0 + (1 + a) * b * x 1, a * (1 + b) * x 0 + x 1]
  invFun x := ![x 0 + (1 + a) * b * x 1, a * (1 + b) * x 0 + x 1]
  map_add' x y := by
    ext i
    fin_cases i <;> simp [mul_add, add_assoc, add_left_comm]
  map_smul' r x := by
    ext i
    fin_cases i <;> simp [mul_add, mul_assoc, mul_left_comm]
  left_inv x := by
    ext i
    fin_cases i <;>
      rcases a.eq_zero_or_eq_one with rfl | rfl <;>
      rcases b.eq_zero_or_eq_one with rfl | rfl <;>
      rcases (x 0).eq_zero_or_eq_one with hx0 | hx0 <;>
      rcases (x 1).eq_zero_or_eq_one with hx1 | hx1 <;>
      (simp only [Fin.zero_eta, Fin.mk_one, Matrix.cons_val_zero, Matrix.cons_val_one, hx0, hx1];
        rfl)
  right_inv x := by
    ext i
    fin_cases i <;>
      rcases a.eq_zero_or_eq_one with rfl | rfl <;>
      rcases b.eq_zero_or_eq_one with rfl | rfl <;>
      rcases (x 0).eq_zero_or_eq_one with hx0 | hx0 <;>
      rcases (x 1).eq_zero_or_eq_one with hx1 | hx1 <;>
      (simp only [Fin.zero_eta, Fin.mk_one, Matrix.cons_val_zero, Matrix.cons_val_one, hx0, hx1];
        rfl)
  map_app' x := by
    rcases a.eq_zero_or_eq_one with rfl | rfl <;>
      rcases b.eq_zero_or_eq_one with rfl | rfl <;>
      rcases (x 0).eq_zero_or_eq_one with hx0 | hx0 <;>
      rcases (x 1).eq_zero_or_eq_one with hx1 | hx1 <;>
      (simp only [symplecticPlane_apply, Matrix.cons_val_zero, Matrix.cons_val_one, hx0, hx1];
        rfl)

/-- Coordinates of `TauCeti.isometryEquivSymplecticPlaneMul`. -/
@[simp]
theorem isometryEquivSymplecticPlaneMul_apply (a b : ZMod 2) (x : Fin 2 → ZMod 2) :
    isometryEquivSymplecticPlaneMul a b x =
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

end TauCeti

namespace QuadraticMap

open TauCeti

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
      have esplit :=
        (IsometryEquiv.consPi fun i : Fin (m + 1) ↦ symplecticPlane (ZMod 2) (c i) (c i)).symm
      refine ⟨fun hsum ↦ ?_, fun hsum ↦ ?_⟩
      · rw [Fin.sum_univ_succ] at hsum
        rcases (c 0).eq_zero_or_eq_one with hc0 | hc0
        · have hsum' : ∑ i, c' i = 0 := by simpa [c', hc0] using hsum
          obtain ⟨e'⟩ := ih0 hsum'
          have esplit0 :
              (QuadraticMap.pi fun i : Fin (m + 1) ↦
                symplecticPlane (ZMod 2) (c i) (c i)).IsometryEquiv
                ((symplecticPlane (ZMod 2) 0 0).prod
                  (QuadraticMap.pi fun i : Fin m ↦ symplecticPlane (ZMod 2) (c' i) (c' i))) := by
            simpa [c', hc0] using esplit
          exact ⟨(esplit0.trans ((IsometryEquiv.refl _).prod e')).trans
            (IsometryEquiv.consPi fun _ : Fin (m + 1) ↦ symplecticPlane (ZMod 2) 0 0)⟩
        · have hsum' : ∑ i, c' i = 1 := by
            rcases (∑ i, c' i).eq_zero_or_eq_one with hs | hs
            · exfalso
              revert hsum
              simp [c', hc0, hs]
            · exact hs
          obtain ⟨k, rfl, ⟨e'⟩⟩ := ih1 hsum'
          have esplit1 :
              (QuadraticMap.pi fun i : Fin (k + 1 + 1) ↦
                symplecticPlane (ZMod 2) (c i) (c i)).IsometryEquiv
                ((symplecticPlane (ZMod 2) 1 1).prod
                  (QuadraticMap.pi fun i : Fin (k + 1) ↦
                    symplecticPlane (ZMod 2) (c' i) (c' i))) := by
            simpa [c', hc0] using esplit
          exact ⟨((((((esplit1.trans ((IsometryEquiv.refl _).prod e')).trans
            (IsometryEquiv.prodAssoc _ _ _).symm).trans
            (isometryEquivSymplecticPlaneOneProd.prod (IsometryEquiv.refl _))).trans
            (IsometryEquiv.prodAssoc _ _ _)).trans
            ((IsometryEquiv.refl _).prod
              (IsometryEquiv.consPi fun _ : Fin (k + 1) ↦ symplecticPlane (ZMod 2) 0 0))).trans
            (IsometryEquiv.consPi fun _ : Fin (k + 2) ↦ symplecticPlane (ZMod 2) 0 0))⟩
      · rw [Fin.sum_univ_succ] at hsum
        rcases (c 0).eq_zero_or_eq_one with hc0 | hc0
        · have hsum' : ∑ i, c' i = 1 := by simpa [c', hc0] using hsum
          obtain ⟨k, rfl, ⟨e'⟩⟩ := ih1 hsum'
          have esplit0 :
              (QuadraticMap.pi fun i : Fin (k + 1 + 1) ↦
                symplecticPlane (ZMod 2) (c i) (c i)).IsometryEquiv
                ((symplecticPlane (ZMod 2) 0 0).prod
                  (QuadraticMap.pi fun i : Fin (k + 1) ↦
                    symplecticPlane (ZMod 2) (c' i) (c' i))) := by
            simpa [c', hc0] using esplit
          refine ⟨k + 1, rfl, ⟨(((esplit0.trans ((IsometryEquiv.refl _).prod e')).trans
            (IsometryEquiv.prodLeftComm _ _ _)).trans
            ((IsometryEquiv.refl _).prod
              (IsometryEquiv.consPi fun _ : Fin (k + 1) ↦ symplecticPlane (ZMod 2) 0 0)))⟩⟩
        · have hsum' : ∑ i, c' i = 0 := by
            rcases (∑ i, c' i).eq_zero_or_eq_one with hs | hs
            · exact hs
            · exfalso
              revert hsum
              simp [c', hc0, hs]
          obtain ⟨e'⟩ := ih0 hsum'
          have esplit1 :
              (QuadraticMap.pi fun i : Fin (m + 1) ↦
                symplecticPlane (ZMod 2) (c i) (c i)).IsometryEquiv
                ((symplecticPlane (ZMod 2) 1 1).prod
                  (QuadraticMap.pi fun i : Fin m ↦ symplecticPlane (ZMod 2) (c' i) (c' i))) := by
            simpa [c', hc0] using esplit
          exact ⟨m, rfl, ⟨esplit1.trans ((IsometryEquiv.refl _).prod e')⟩⟩

section Classification

variable {V V₁ V₂ : Type*} [AddCommGroup V] [Module (ZMod 2) V]
  [AddCommGroup V₁] [Module (ZMod 2) V₁] [AddCommGroup V₂] [Module (ZMod 2) V₂]

/-- The orthogonal sum of `m` hyperbolic planes `symplecticPlane (ZMod 2) 0 0` has Arf invariant
`0`. -/
@[simp]
theorem arf_pi_symplecticPlane_zero (m : ℕ) :
    (QuadraticMap.pi fun _ : Fin m ↦ symplecticPlane (ZMod 2) 0 0).arf = 0 := by
  rw [arf_pi fun _ ↦ nondegenerate_polarBilin_symplecticPlane 0 0]
  simp

/-- The orthogonal sum of one anisotropic plane `symplecticPlane (ZMod 2) 1 1` and `k` hyperbolic
planes `symplecticPlane (ZMod 2) 0 0` has Arf invariant `1`. -/
@[simp]
theorem arf_symplecticPlane_one_prod_pi_zero (k : ℕ) :
    ((symplecticPlane (ZMod 2) 1 1).prod
      (QuadraticMap.pi fun _ : Fin k ↦ symplecticPlane (ZMod 2) 0 0)).arf = 1 := by
  rw [arf_prod (nondegenerate_polarBilin_symplecticPlane 1 1)
    (nondegenerate_polarBilin_pi_iff.mpr fun _ ↦ nondegenerate_polarBilin_symplecticPlane 0 0),
    arf_symplecticPlane, arf_pi_symplecticPlane_zero]
  rfl

/-- **Hyperbolic normal form (`Q.arf = 0`).** A finite-dimensional quadratic space over `ZMod 2` of
dimension `2 * m` with nondegenerate polar form has `Q.arf = 0` if and only if it is isometric to
the orthogonal sum of `m` hyperbolic planes `symplecticPlane (ZMod 2) 0 0`. -/
theorem arf_eq_zero_iff_equivalent_pi_symplecticPlane_zero [FiniteDimensional (ZMod 2) V]
    {Q : QuadraticForm (ZMod 2) V} (hQ : Q.polarBilin.Nondegenerate) {m : ℕ}
    (hdim : Module.finrank (ZMod 2) V = 2 * m) :
    Q.arf = 0 ↔ Q.Equivalent (QuadraticMap.pi fun _ : Fin m ↦ symplecticPlane (ZMod 2) 0 0) := by
  refine ⟨fun harf ↦ ?_, fun h ↦ h.arf_eq.trans (arf_pi_symplecticPlane_zero m)⟩
  obtain ⟨k, b, hb⟩ := Q.exists_basis_toMatrix_polarBilin_eq_J hQ
  have hkm : k = m := by
    have hc := Module.finrank_eq_card_basis b
    simp only [Fintype.card_sum, Fintype.card_fin] at hc
    omega
  subst hkm
  let c : Fin k → ZMod 2 := fun i ↦ Q (b (Sum.inl i)) * Q (b (Sum.inr i))
  have hc_sum : ∑ i, c i = 0 := by
    rw [← Q.arf_eq_sum_of_toMatrix_polarBilin_eq_J hb, harf]
  obtain ⟨enorm⟩ := (normalForm_pi_symplecticPlane k c).1 hc_sum
  exact ⟨((Q.isometryEquivPiSymplecticPlane b hb).trans
    (IsometryEquiv.pi fun i ↦
      isometryEquivSymplecticPlaneMul (Q (b (Sum.inl i))) (Q (b (Sum.inr i))))).trans enorm⟩

/-- **Anisotropic normal form (`Q.arf = 1`).** A finite-dimensional quadratic space over `ZMod 2`
of dimension `2 * m` with nondegenerate polar form has `Q.arf = 1` if and only if `m = k + 1` and
`Q` is isometric to `symplecticPlane (ZMod 2) 1 1` orthogonal-summed with `k` hyperbolic planes. -/
theorem arf_eq_one_iff_exists_equivalent_symplecticPlane_one_prod_pi
    [FiniteDimensional (ZMod 2) V] {Q : QuadraticForm (ZMod 2) V}
    (hQ : Q.polarBilin.Nondegenerate) {m : ℕ} (hdim : Module.finrank (ZMod 2) V = 2 * m) :
    Q.arf = 1 ↔
      ∃ k : ℕ, m = k + 1 ∧
        Q.Equivalent
          ((symplecticPlane (ZMod 2) 1 1).prod
            (QuadraticMap.pi fun _ : Fin k ↦ symplecticPlane (ZMod 2) 0 0)) := by
  refine ⟨fun harf ↦ ?_, fun ⟨k, _, h⟩ ↦ h.arf_eq.trans (arf_symplecticPlane_one_prod_pi_zero k)⟩
  obtain ⟨n, b, hb⟩ := Q.exists_basis_toMatrix_polarBilin_eq_J hQ
  have hnm : n = m := by
    have hc := Module.finrank_eq_card_basis b
    simp only [Fintype.card_sum, Fintype.card_fin] at hc
    omega
  subst hnm
  let c : Fin n → ZMod 2 := fun i ↦ Q (b (Sum.inl i)) * Q (b (Sum.inr i))
  have hc_sum : ∑ i, c i = 1 := by
    rw [← Q.arf_eq_sum_of_toMatrix_polarBilin_eq_J hb, harf]
  obtain ⟨k, hnk, ⟨enorm⟩⟩ := (normalForm_pi_symplecticPlane n c).2 hc_sum
  exact ⟨k, hnk, ⟨((Q.isometryEquivPiSymplecticPlane b hb).trans
    (IsometryEquiv.pi fun i ↦
      isometryEquivSymplecticPlaneMul (Q (b (Sum.inl i))) (Q (b (Sum.inr i))))).trans enorm⟩⟩

/-- When `Module.finrank (ZMod 2) V = 2 * (k + 1)` and `Q.polarBilin` is nondegenerate, `Q.arf = 1`
if and only if `Q` is isometric to `symplecticPlane (ZMod 2) 1 1` orthogonal-summed with `k`
hyperbolic planes. -/
theorem arf_eq_one_iff_equivalent_symplecticPlane_one_prod_pi
    [FiniteDimensional (ZMod 2) V] {Q : QuadraticForm (ZMod 2) V}
    (hQ : Q.polarBilin.Nondegenerate) {k : ℕ}
    (hdim : Module.finrank (ZMod 2) V = 2 * (k + 1)) :
    Q.arf = 1 ↔
      Q.Equivalent
        ((symplecticPlane (ZMod 2) 1 1).prod
          (QuadraticMap.pi fun _ : Fin k ↦ symplecticPlane (ZMod 2) 0 0)) := by
  rw [Q.arf_eq_one_iff_exists_equivalent_symplecticPlane_one_prod_pi hQ hdim]
  refine ⟨fun ⟨k', hk', heq⟩ ↦ ?_, fun heq ↦ ⟨k, rfl, heq⟩⟩
  obtain rfl : k' = k := by omega
  exact heq

/-- Any finite-dimensional quadratic space over `ZMod 2` with `Q.arf = 1` has positive dimension. -/
theorem finrank_pos_of_arf_eq_one [FiniteDimensional (ZMod 2) V]
    {Q : QuadraticForm (ZMod 2) V} (harf : Q.arf = 1) :
    0 < Module.finrank (ZMod 2) V := by
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
      (Q₁.arf_eq_one_iff_exists_equivalent_symplecticPlane_one_prod_pi hQ₁ hdim₁).mp h1
    obtain ⟨e₂⟩ :=
      (Q₂.arf_eq_one_iff_equivalent_symplecticPlane_one_prod_pi hQ₂ hdim₂).mp (harf.symm.trans h1)
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
