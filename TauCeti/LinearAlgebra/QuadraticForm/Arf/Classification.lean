/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.QuadraticForm.Arf.Basic
public import TauCeti.LinearAlgebra.QuadraticForm.Representation

/-!
# Classification of polar-nondegenerate quadratic forms over `𝔽₂`

Over `𝔽₂ = ZMod 2`, a binary symplectic plane `TauCeti.symplecticPlane (ZMod 2) a b`
(`(x₀, x₁) ↦ a x₀² + x₀ x₁ + b x₁²`) has only two isometry classes:

* when `a * b = 0`, at least one basis vector is isotropic and a coordinate shear identifies the
  plane with `TauCeti.splitHyperbolicPlane (ZMod 2)` (`Arf = 0`);
* when `a * b = 1`, `a = b = 1` and the plane `symplecticPlane (ZMod 2) 1 1`
  (`(x₀, x₁) ↦ x₀² + x₀ x₁ + x₁²`) is anisotropic (`Arf = 1`).

Since the orthogonal sum of two `[1, 1]` planes is isometric to the orthogonal sum of two split
hyperbolic planes (`TauCeti.isometryEquivSymplecticPlaneOneOneProd`), pairs of `[1, 1]` planes
cancel in orthogonal sums. Every finite-dimensional quadratic space `(V, Q)` over `𝔽₂` with
nondegenerate polar bilinear form therefore reduces to a canonical normal form determined by its
even dimension `2 * m` and its Arf invariant `Q.arf hQ ∈ ZMod 2`:

* if `Q.arf hQ = 0`, `Q` is equivalent to the orthogonal sum of `m` split hyperbolic planes;
* if `Q.arf hQ = 1`, then `m ≥ 1` and `Q` is equivalent to `symplecticPlane (ZMod 2) 1 1` plus
  `m - 1` split hyperbolic planes.

Consequently:

* **Arf's classification theorem over `𝔽₂`**: two finite-dimensional quadratic spaces over `𝔽₂`
  with nondegenerate polar forms are equivalent if and only if they have the same `finrank` and the
  same Arf invariant (`QuadraticMap.equivalent_iff_finrank_eq_and_arf_eq`).
* **Anisotropic forms over `𝔽₂`**: a polar-nondegenerate space over `𝔽₂` is anisotropic if and only
  if its dimension is `0`, or its dimension is `2` and `Q.arf hQ = 1`
  (`QuadraticMap.anisotropic_iff_finrank_eq_zero_or_finrank_eq_two_and_arf_eq_one`).
* **Metabolic and Lagrangian characterizations of `Arf(Q) = 0`**: `Q.arf hQ = 0` if and only if `Q`
  admits a symplectic basis of `Q`-isotropic vectors, if and only if `V` contains a
  `Q`-totally-isotropic polar-Lagrangian subspace, if and only if `V` contains a
  `Q`-totally-isotropic subspace of half the ambient dimension. In particular, the evaluation form
  `QuadraticForm.dualProd (ZMod 2) U` on `Dual (ZMod 2) U × U` has Arf invariant `0`.

## Main results

* `TauCeti.anisotropic_symplecticPlane_iff`: `symplecticPlane (ZMod 2) a b` is anisotropic iff
  `a = 1 ∧ b = 1`.
* `QuadraticMap.equivalent_pi_splitHyperbolicPlane_of_arf_eq_zero`,
  `QuadraticMap.equivalent_symplecticPlane_one_one_prod_pi_of_arf_eq_one`: canonical normal forms
  of polar-nondegenerate quadratic spaces over `ZMod 2`.
* `QuadraticMap.equivalent_iff_finrank_eq_and_arf_eq`: Arf's classification theorem over `ZMod 2`.
* `QuadraticMap.anisotropic_iff_finrank_eq_zero_or_finrank_eq_two_and_arf_eq_one`: characterization
  of anisotropic polar-nondegenerate quadratic spaces over `ZMod 2`.
* `QuadraticMap.arf_eq_zero_iff_exists_basis_toMatrix_polarBilin_eq_J_and_apply_eq_zero`,
  `QuadraticMap.arf_eq_zero_iff_exists_isTotallyIsotropic_and_eq_orthogonal`,
  `QuadraticMap.arf_eq_zero_iff_exists_isTotallyIsotropic_and_two_mul_finrank_eq`: equivalent
  criteria for `Q.arf hQ = 0`.
* `QuadraticForm.arf_dualProd`: `QuadraticForm.dualProd (ZMod 2) U` has Arf invariant `0`.

## References

* C. Arf, *Untersuchungen über quadratische Formen in Körpern der Charakteristik 2 (Teil I)*,
  J. Reine Angew. Math. 183 (1941), 148–167.
* W. Browder, *Surgery on Simply-Connected Manifolds*, Ergebnisse der Mathematik und ihrer
  Grenzgebiete 65, Springer (1972), §III.1.
* R. Pyronneau, *The Arf Invariant* (expository notes), §2.1.
-/

public section

open Module QuadraticMap

namespace TauCeti

/-- Over `ZMod 2`, `a * b = 1` forces `a = 1` and `b = 1`, identifying
`symplecticPlane (ZMod 2) a b` with `symplecticPlane (ZMod 2) 1 1`. -/
theorem symplecticPlane_eq_one_one_of_mul_eq_one {a b : ZMod 2} (hab : a * b = 1) :
    symplecticPlane (ZMod 2) a b = symplecticPlane (ZMod 2) 1 1 := by
  obtain ⟨rfl, rfl⟩ := ZMod.mul_eq_one_iff.mp hab
  rfl

/-- Over `ZMod 2`, `symplecticPlane (ZMod 2) a b` is anisotropic if and only if `a = 1` and
`b = 1`. -/
theorem anisotropic_symplecticPlane_iff {a b : ZMod 2} :
    (symplecticPlane (ZMod 2) a b).Anisotropic ↔ a = 1 ∧ b = 1 := by
  refine ⟨fun h ↦ ?_, fun ⟨ha, hb⟩ x hx ↦ ?_⟩
  · rcases ZMod.eq_zero_or_eq_one (a * b) with hab | hab
    · exact False.elim (not_anisotropic_splitHyperbolicPlane
        ((equivalent_splitHyperbolicPlane_of_mul_eq_zero hab).anisotropic_iff.mp h))
    · exact ZMod.mul_eq_one_iff.mp hab
  · subst ha hb
    rw [symplecticPlane_apply] at hx
    rcases ZMod.eq_zero_or_eq_one (x 0) with h0 | h0 <;>
      rcases ZMod.eq_zero_or_eq_one (x 1) with h1 | h1
    · ext i
      fin_cases i <;> simp [h0, h1]
    · simp [h0, h1] at hx
    · simp [h0, h1] at hx
    · simp only [h0, h1, one_mul] at hx
      exact absurd hx (by decide)

/-- The binary plane `symplecticPlane (ZMod 2) 1 1` (`x₀² + x₀ x₁ + x₁²`) over `𝔽₂` is
anisotropic. -/
theorem anisotropic_symplecticPlane_one_one :
    (symplecticPlane (ZMod 2) 1 1).Anisotropic :=
  anisotropic_symplecticPlane_iff.mpr ⟨rfl, rfl⟩

end TauCeti

namespace QuadraticMap

/-! ### Normal forms of orthogonal sums of binary symplectic planes over `ZMod 2` -/

private theorem normal_form_pi_symplecticPlane :
    ∀ (m : ℕ) (a b : Fin m → ZMod 2),
      (∑ i : Fin m, a i * b i = 0 →
        (QuadraticMap.pi fun i : Fin m ↦
          TauCeti.symplecticPlane (ZMod 2) (a i) (b i)).Equivalent
          (QuadraticMap.pi fun _ : Fin m ↦ TauCeti.splitHyperbolicPlane (ZMod 2))) ∧
      (∀ k, m = k + 1 → ∑ i : Fin m, a i * b i = 1 →
        (QuadraticMap.pi fun i : Fin m ↦
          TauCeti.symplecticPlane (ZMod 2) (a i) (b i)).Equivalent
          ((TauCeti.symplecticPlane (ZMod 2) 1 1).prod
            (QuadraticMap.pi fun _ : Fin k ↦ TauCeti.splitHyperbolicPlane (ZMod 2))))
  | 0, _, _ => ⟨fun _ ↦ ⟨IsometryEquiv.pi fun i ↦ i.elim0⟩, by rintro _ ⟨⟩⟩
  | m + 1, a, b => by
    let H := TauCeti.splitHyperbolicPlane (ZMod 2)
    let A := TauCeti.symplecticPlane (ZMod 2) 1 1
    obtain ⟨ih0, ih1⟩ := normal_form_pi_symplecticPlane m (a ∘ Fin.succ) (b ∘ Fin.succ)
    have hcons : (QuadraticMap.pi fun i : Fin (m + 1) ↦
        TauCeti.symplecticPlane (ZMod 2) (a i) (b i)).Equivalent
        ((TauCeti.symplecticPlane (ZMod 2) (a 0) (b 0)).prod
          (QuadraticMap.pi fun i : Fin m ↦
            TauCeti.symplecticPlane (ZMod 2) (a i.succ) (b i.succ))) :=
      ⟨(IsometryEquiv.consPi _).symm⟩
    refine ⟨fun hsum ↦ ?_, fun k hk hsum ↦ ?_⟩
    · rw [Fin.sum_univ_succ] at hsum
      rcases ZMod.eq_zero_or_eq_one (a 0 * b 0) with h0 | h1
      · have htail : ∑ i : Fin m, a i.succ * b i.succ = 0 := by simpa [h0] using hsum
        exact hcons.trans <| ((TauCeti.equivalent_splitHyperbolicPlane_of_mul_eq_zero h0).prod
          (ih0 htail)).trans ⟨IsometryEquiv.consPi fun _ : Fin (m + 1) ↦ H⟩
      · rw [TauCeti.symplecticPlane_eq_one_one_of_mul_eq_one h1] at hcons
        have htail : ∑ i : Fin m, a i.succ * b i.succ = 1 := by
          rw [h1, CharTwo.add_eq_zero] at hsum; exact hsum.symm
        rcases m with _ | l
        · simp at htail
        · have hAA : (A.prod (A.prod (QuadraticMap.pi fun _ : Fin l ↦ H))).Equivalent
              (QuadraticMap.pi fun _ : Fin (l + 2) ↦ H) :=
            ⟨(IsometryEquiv.prodAssoc A A _).symm.trans <|
              (TauCeti.isometryEquivSymplecticPlaneOneOneProd.prod (.refl _)).trans <|
              (IsometryEquiv.prodAssoc H H _).trans <|
              ((IsometryEquiv.refl H).prod (IsometryEquiv.consPi fun _ : Fin (l + 1) ↦ H)).trans
                (IsometryEquiv.consPi fun _ : Fin (l + 2) ↦ H)⟩
          exact hcons.trans <| ((Equivalent.refl A).prod (ih1 l rfl htail)).trans hAA
    · obtain rfl : m = k := Nat.succ.inj hk
      rw [Fin.sum_univ_succ] at hsum
      rcases ZMod.eq_zero_or_eq_one (a 0 * b 0) with h0 | h1
      · have htail : ∑ i : Fin m, a i.succ * b i.succ = 1 := by simpa [h0] using hsum
        rcases m with _ | l
        · simp at htail
        · exact hcons.trans <| ((TauCeti.equivalent_splitHyperbolicPlane_of_mul_eq_zero h0).prod
            (ih1 l rfl htail)).trans ⟨(IsometryEquiv.prodLeftComm H A _).trans
              ((IsometryEquiv.refl A).prod (IsometryEquiv.consPi fun _ : Fin (l + 1) ↦ H))⟩
      · rw [TauCeti.symplecticPlane_eq_one_one_of_mul_eq_one h1] at hcons
        have htail : ∑ i : Fin m, a i.succ * b i.succ = 0 :=
          add_left_cancel ((h1 ▸ hsum).trans (add_zero (1 : ZMod 2)).symm)
        exact hcons.trans ((Equivalent.refl A).prod (ih0 htail))

/-- An orthogonal sum of `m` binary symplectic planes over `𝔽₂` whose Arf sum `∑ i, a i * b i`
vanishes is equivalent to the orthogonal sum of `m` split hyperbolic planes. -/
theorem equivalent_pi_splitHyperbolicPlane_of_sum_mul_eq_zero {m : ℕ} {a b : Fin m → ZMod 2}
    (h : ∑ i : Fin m, a i * b i = 0) :
    (QuadraticMap.pi fun i : Fin m ↦ TauCeti.symplecticPlane (ZMod 2) (a i) (b i)).Equivalent
      (QuadraticMap.pi fun _ : Fin m ↦ TauCeti.splitHyperbolicPlane (ZMod 2)) :=
  (normal_form_pi_symplecticPlane m a b).1 h

/-- An orthogonal sum of `k + 1` binary symplectic planes over `𝔽₂` whose Arf sum
`∑ i, a i * b i` equals `1` is equivalent to `symplecticPlane (ZMod 2) 1 1` plus `k` split
hyperbolic planes. -/
theorem equivalent_symplecticPlane_one_one_prod_pi_of_sum_mul_eq_one {k : ℕ}
    {a b : Fin (k + 1) → ZMod 2} (h : ∑ i : Fin (k + 1), a i * b i = 1) :
    (QuadraticMap.pi fun i : Fin (k + 1) ↦
      TauCeti.symplecticPlane (ZMod 2) (a i) (b i)).Equivalent
      ((TauCeti.symplecticPlane (ZMod 2) 1 1).prod
        (QuadraticMap.pi fun _ : Fin k ↦ TauCeti.splitHyperbolicPlane (ZMod 2))) :=
  (normal_form_pi_symplecticPlane (k + 1) a b).2 k rfl h

/-! ### Normal forms, classification, anisotropy, and metabolic criteria -/

section Classification

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
  {Q : QuadraticForm (ZMod 2) V}

/-- A polar-nondegenerate quadratic space over `𝔽₂` of dimension `2 * m` and Arf invariant `0` is
equivalent to the orthogonal sum of `m` split hyperbolic planes. -/
theorem equivalent_pi_splitHyperbolicPlane_of_arf_eq_zero {m : ℕ}
    (hQ : Q.polarBilin.Nondegenerate) (hm : Module.finrank (ZMod 2) V = 2 * m)
    (harf : Q.arf hQ = 0) :
    Q.Equivalent (QuadraticMap.pi fun _ : Fin m ↦ TauCeti.splitHyperbolicPlane (ZMod 2)) := by
  obtain ⟨b, hb⟩ := Q.exists_basis_toMatrix_polarBilin_eq_J_of_finrank_eq_two_mul hQ hm
  exact Equivalent.trans ⟨Q.isometryEquivPiSymplecticPlaneOfToMatrixEqJ b hb⟩
    (equivalent_pi_splitHyperbolicPlane_of_sum_mul_eq_zero
      ((Q.arf_eq_sum_of_toMatrix_polarBilin_eq_J hQ b hb).symm.trans harf))

/-- Any polar-nondegenerate quadratic space over `𝔽₂` with Arf invariant `1` has positive
dimension. -/
theorem finrank_pos_of_arf_eq_one (hQ : Q.polarBilin.Nondegenerate) (harf : Q.arf hQ = 1) :
    0 < Module.finrank (ZMod 2) V := by
  by_contra! h0
  have hzero : Module.finrank (ZMod 2) V = 0 := Nat.eq_zero_of_le_zero h0
  have : Subsingleton V := not_nontrivial_iff_subsingleton.mp fun hnt ↦
    (Module.finrank_pos_iff.mpr hnt).ne' hzero
  exact zero_ne_one ((Q.arf_of_subsingleton hQ).symm.trans harf)

/-- A polar-nondegenerate quadratic space over `𝔽₂` of dimension `2 * (k + 1)` and Arf invariant
`1` is equivalent to `symplecticPlane (ZMod 2) 1 1` plus `k` split hyperbolic planes. -/
theorem equivalent_symplecticPlane_one_one_prod_pi_of_arf_eq_one {k : ℕ}
    (hQ : Q.polarBilin.Nondegenerate) (hm : Module.finrank (ZMod 2) V = 2 * (k + 1))
    (harf : Q.arf hQ = 1) :
    Q.Equivalent ((TauCeti.symplecticPlane (ZMod 2) 1 1).prod
      (QuadraticMap.pi fun _ : Fin k ↦ TauCeti.splitHyperbolicPlane (ZMod 2))) := by
  obtain ⟨b, hb⟩ := Q.exists_basis_toMatrix_polarBilin_eq_J_of_finrank_eq_two_mul hQ hm
  exact Equivalent.trans ⟨Q.isometryEquivPiSymplecticPlaneOfToMatrixEqJ b hb⟩
    (equivalent_symplecticPlane_one_one_prod_pi_of_sum_mul_eq_one
      ((Q.arf_eq_sum_of_toMatrix_polarBilin_eq_J hQ b hb).symm.trans harf))

/-- **Arf's classification theorem over `𝔽₂`.**

Two finite-dimensional quadratic forms over `ZMod 2` with nondegenerate polar bilinear forms are
equivalent if and only if they have the same `finrank` and the same Arf invariant. -/
theorem equivalent_iff_finrank_eq_and_arf_eq {V₁ V₂ : Type*}
    [AddCommGroup V₁] [Module (ZMod 2) V₁] [FiniteDimensional (ZMod 2) V₁]
    [AddCommGroup V₂] [Module (ZMod 2) V₂] [FiniteDimensional (ZMod 2) V₂]
    {Q₁ : QuadraticForm (ZMod 2) V₁} {Q₂ : QuadraticForm (ZMod 2) V₂}
    (hQ₁ : Q₁.polarBilin.Nondegenerate) (hQ₂ : Q₂.polarBilin.Nondegenerate) :
    Q₁.Equivalent Q₂ ↔
      Module.finrank (ZMod 2) V₁ = Module.finrank (ZMod 2) V₂ ∧
        Q₁.arf hQ₁ = Q₂.arf hQ₂ := by
  refine ⟨fun ⟨e⟩ ↦ ⟨e.toLinearEquiv.finrank_eq, e.arf_eq hQ₁ hQ₂⟩, fun ⟨hdim, harf⟩ ↦ ?_⟩
  obtain ⟨m, hm₁⟩ := (Q₁.even_finrank_of_nondegenerate_polarBilin hQ₁).exists_two_nsmul
  simp only [two_nsmul, ← two_mul] at hm₁
  have hm₂ : Module.finrank (ZMod 2) V₂ = 2 * m := hdim.symm.trans hm₁
  rcases ZMod.eq_zero_or_eq_one (Q₁.arf hQ₁) with h0 | h1
  · exact (Q₁.equivalent_pi_splitHyperbolicPlane_of_arf_eq_zero hQ₁ hm₁ h0).trans
      (Q₂.equivalent_pi_splitHyperbolicPlane_of_arf_eq_zero hQ₂ hm₂ (harf.symm.trans h0)).symm
  · rcases m with _ | k
    · exact absurd (Q₁.finrank_pos_of_arf_eq_one hQ₁ h1) (by omega)
    · exact (Q₁.equivalent_symplecticPlane_one_one_prod_pi_of_arf_eq_one hQ₁ hm₁ h1).trans
        (Q₂.equivalent_symplecticPlane_one_one_prod_pi_of_arf_eq_one hQ₂ hm₂
          (harf.symm.trans h1)).symm

/-- **Characterization of anisotropic polar-nondegenerate quadratic forms over `𝔽₂`.**

A polar-nondegenerate quadratic space over `𝔽₂` is anisotropic if and only if it is
zero-dimensional, or it is two-dimensional with Arf invariant `1`. In particular, every
polar-nondegenerate quadratic space over `𝔽₂` of dimension at least `4` is isotropic. -/
theorem anisotropic_iff_finrank_eq_zero_or_finrank_eq_two_and_arf_eq_one
    (hQ : Q.polarBilin.Nondegenerate) :
    Q.Anisotropic ↔
      Module.finrank (ZMod 2) V = 0 ∨
        Module.finrank (ZMod 2) V = 2 ∧ Q.arf hQ = 1 := by
  refine ⟨fun hA ↦ ?_, ?_⟩
  · obtain ⟨m, hm⟩ := (Q.even_finrank_of_nondegenerate_polarBilin hQ).exists_two_nsmul
    simp only [two_nsmul, ← two_mul] at hm
    rcases m with _ | _ | k
    · exact Or.inl hm
    · refine Or.inr ⟨hm, (ZMod.eq_zero_or_eq_one (Q.arf hQ)).resolve_left fun h0 ↦ ?_⟩
      have heq := Q.equivalent_pi_splitHyperbolicPlane_of_arf_eq_zero hQ hm h0
      exact TauCeti.not_anisotropic_splitHyperbolicPlane
        (anisotropic_of_pi (heq.anisotropic_iff.mp hA) 0)
    · exfalso
      rcases ZMod.eq_zero_or_eq_one (Q.arf hQ) with h0 | h1
      · have heq := Q.equivalent_pi_splitHyperbolicPlane_of_arf_eq_zero hQ hm h0
        exact TauCeti.not_anisotropic_splitHyperbolicPlane
          (anisotropic_of_pi (heq.anisotropic_iff.mp hA) 0)
      · have heq := Q.equivalent_symplecticPlane_one_one_prod_pi_of_arf_eq_one hQ hm h1
        exact TauCeti.not_anisotropic_splitHyperbolicPlane
          (anisotropic_of_pi (anisotropic_of_prod (heq.anisotropic_iff.mp hA)).2 0)
  · rintro (h0 | ⟨h2, harf⟩)
    · have : Subsingleton V := not_nontrivial_iff_subsingleton.mp fun hnt ↦
        (Module.finrank_pos_iff.mpr hnt).ne' h0
      intro x _
      exact Subsingleton.elim x 0
    · have heq := Q.equivalent_symplecticPlane_one_one_prod_pi_of_arf_eq_one hQ (k := 0) h2 harf
      have hunit : ((TauCeti.symplecticPlane (ZMod 2) 1 1).prod
          (QuadraticMap.pi fun _ : Fin 0 ↦ TauCeti.splitHyperbolicPlane (ZMod 2))).Equivalent
          (TauCeti.symplecticPlane (ZMod 2) 1 1) :=
        ⟨(IsometryEquiv.prodComm _ _).trans (IsometryEquiv.uniqueProd _ _)⟩
      exact (heq.trans hunit).anisotropic_iff.mpr TauCeti.anisotropic_symplecticPlane_one_one

/-- A polar-nondegenerate quadratic space over `𝔽₂` has Arf invariant `0` if and only if it is
equivalent to an orthogonal sum of split hyperbolic planes. -/
theorem arf_eq_zero_iff_equivalent_pi_splitHyperbolicPlane (hQ : Q.polarBilin.Nondegenerate) :
    Q.arf hQ = 0 ↔
      ∃ m : ℕ, Q.Equivalent (QuadraticMap.pi fun _ : Fin m ↦
        TauCeti.splitHyperbolicPlane (ZMod 2)) := by
  refine ⟨fun harf ↦ ?_, fun ⟨m, heq⟩ ↦ ?_⟩
  · obtain ⟨m, hm⟩ := (Q.even_finrank_of_nondegenerate_polarBilin hQ).exists_two_nsmul
    simp only [two_nsmul, ← two_mul] at hm
    exact ⟨m, Q.equivalent_pi_splitHyperbolicPlane_of_arf_eq_zero hQ hm harf⟩
  · rw [heq.arf_eq hQ (nondegenerate_polarBilin_pi_iff.mpr fun _ ↦
      TauCeti.nondegenerate_polarBilin_splitHyperbolicPlane)]
    simp

/-- A polar-nondegenerate quadratic space over `𝔽₂` has Arf invariant `0` if and only if it admits
a symplectic basis of `Q`-isotropic vectors. -/
theorem arf_eq_zero_iff_exists_basis_toMatrix_polarBilin_eq_J_and_apply_eq_zero
    (hQ : Q.polarBilin.Nondegenerate) :
    Q.arf hQ = 0 ↔
      ∃ (m : ℕ) (b : Basis (Fin m ⊕ Fin m) (ZMod 2) V),
        LinearMap.BilinForm.toMatrix b Q.polarBilin = Matrix.J (Fin m) (ZMod 2) ∧
          ∀ x, Q (b x) = 0 :=
  (Q.arf_eq_zero_iff_equivalent_pi_splitHyperbolicPlane hQ).trans
    Q.equivalent_pi_splitHyperbolicPlane_iff_exists_basis_apply_eq_zero

/-- **Lagrangian criterion for `Arf(Q) = 0`.**

A polar-nondegenerate quadratic space over `𝔽₂` has Arf invariant `0` if and only if it contains a
`Q`-totally-isotropic polar-Lagrangian subspace
`U = LinearMap.BilinForm.orthogonal Q.polarBilin U`. -/
theorem arf_eq_zero_iff_exists_isTotallyIsotropic_and_eq_orthogonal
    (hQ : Q.polarBilin.Nondegenerate) :
    Q.arf hQ = 0 ↔
      ∃ U : Submodule (ZMod 2) V,
        Q.IsTotallyIsotropic U ∧ U = LinearMap.BilinForm.orthogonal Q.polarBilin U :=
  (Q.arf_eq_zero_iff_equivalent_pi_splitHyperbolicPlane hQ).trans
    (Q.equivalent_pi_splitHyperbolicPlane_iff_exists_isTotallyIsotropic_and_eq_orthogonal hQ)

/-- **Metabolizer criterion for `Arf(Q) = 0`.**

A polar-nondegenerate quadratic space over `𝔽₂` has Arf invariant `0` if and only if it contains a
`Q`-totally-isotropic subspace of half the ambient dimension. -/
theorem arf_eq_zero_iff_exists_isTotallyIsotropic_and_two_mul_finrank_eq
    (hQ : Q.polarBilin.Nondegenerate) :
    Q.arf hQ = 0 ↔
      ∃ U : Submodule (ZMod 2) V,
        Q.IsTotallyIsotropic U ∧ 2 * Module.finrank (ZMod 2) U = Module.finrank (ZMod 2) V :=
  (Q.arf_eq_zero_iff_equivalent_pi_splitHyperbolicPlane hQ).trans
    (Q.equivalent_pi_splitHyperbolicPlane_iff_exists_isTotallyIsotropic_and_two_mul_finrank_eq hQ)

/-- The canonical evaluation quadratic form `QuadraticForm.dualProd (ZMod 2) V` on
`Module.Dual (ZMod 2) V × V` has Arf invariant `0`. -/
@[simp]
theorem _root_.QuadraticForm.arf_dualProd
    (hQ : (QuadraticForm.dualProd (ZMod 2) V).polarBilin.Nondegenerate :=
      QuadraticForm.nondegenerate_polarBilin_dualProd) :
    (QuadraticForm.dualProd (ZMod 2) V).arf hQ = 0 := by
  refine (arf_eq_zero_iff_exists_isTotallyIsotropic_and_two_mul_finrank_eq hQ).mpr
    ⟨LinearMap.range (LinearMap.inr (ZMod 2) (Module.Dual (ZMod 2) V) V), ?_, ?_⟩
  · refine isTotallyIsotropic_iff.mpr ?_
    rintro _ ⟨v, rfl⟩
    simp
  · rw [LinearMap.finrank_range_of_inj LinearMap.inr_injective, Module.finrank_prod,
      Subspace.dual_finrank_eq, two_mul]

end Classification

end QuadraticMap
