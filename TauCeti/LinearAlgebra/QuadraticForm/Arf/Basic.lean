/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Field.ZMod
public import Mathlib.FieldTheory.Finiteness
public import TauCeti.Data.ZMod.Two
public import TauCeti.LinearAlgebra.QuadraticForm.SymplecticBasis

/-!
# The Arf invariant and Gauss sum of a quadratic form over `𝔽₂`

Let `Q` be a quadratic form on a finite-dimensional vector space `V` over `𝔽₂ = ZMod 2` whose
polar bilinear form `Q.polarBilin` is nondegenerate. By
`QuadraticMap.exists_basis_toMatrix_polarBilin_eq_J`, `V` has even dimension `2 * m` and admits a
symplectic basis `(e₁, …, eₘ, f₁, …, fₘ)` for `Q.polarBilin`. The **Arf invariant**
`QuadraticMap.arf Q hQ : ZMod 2` is the scalar

$$\operatorname{Arf}(Q) = \sum_{i = 1}^{m} Q(e_i) Q(f_i) \in \mathbb{F}_2.$$

Independence of the chosen symplectic basis is proved via the finite **Gauss sum**
`∑ v : V, (-1 : ℤ) ^ (Q v).val`: in any symplectic basis indexed by `ι ⊕ ι`, the space splits into
`|ι|` mutually orthogonal binary symplectic planes
`TauCeti.symplecticPlane (ZMod 2) (Q eᵢ) (Q fᵢ)`, each plane contributes
`(-1) ^ (Q eᵢ * Q fᵢ).val * 2`, and multiplying over `i : ι` yields

$$\sum_{v \in V} (-1)^{Q(v)} = (-1)^{\operatorname{Arf}(Q)} \cdot 2^m.$$

Since `2^m > 0` in `ℤ` and `a ↦ (-1 : ℤ) ^ a.val` is injective on `ZMod 2`, the sum
`∑ i, Q eᵢ * Q fᵢ` depends only on `Q` and not on the symplectic basis.

The Gauss sum immediately determines how many vectors of `V` take value `0` versus `1`:
`2 * #{v | Q v = 0} = 2^(2m) + (-1)^Arf(Q) * 2^m` (so
`#{v | Q v = 0} = 2^(2m - 1) + (-1)^Arf(Q) * 2^(m - 1)` whenever `m ≥ 1`), and `Q` has Arf
invariant `0` (respectively `1`) if and only if strictly more vectors satisfy `Q v = 0` than
`Q v = 1` (respectively `Q v = 1` than `Q v = 0`) — the classical "democratic" characterization
of the Arf invariant.

Finally, for an arbitrary (possibly degenerate) finite-dimensional quadratic form `Q` over `𝔽₂`:
* if `Q` is nonzero on some vector of `Q.polarBilin.ker`, translation by that vector flips `Q` and
  forces `∑ v : V, (-1) ^ (Q v).val = 0`;
* if `Q` vanishes on `Q.polarBilin.ker` (equivalently `Q.radical = Q.polarBilin.ker`), the induced
  form `Q.lift Q.radical le_rfl` on `V ⧸ Q.radical` has nondegenerate polar form and
  `∑ v : V, (-1) ^ (Q v).val = Fintype.card Q.radical * (-1) ^ Arf(Q.lift) * 2 ^ (finrank / 2)`.

## Main definitions

* `QuadraticMap.arf`: the `ZMod 2`-valued Arf invariant of a finite-dimensional quadratic form over
  `ZMod 2` with nondegenerate polar bilinear form.

## Main results

* `QuadraticMap.sum_mul_eq_of_toMatrix_polarBilin_eq_J`: `∑ i, Q eᵢ * Q fᵢ` is independent of the
  symplectic basis.
* `QuadraticMap.arf_eq_sum_of_toMatrix_polarBilin_eq_J`: `Q.arf hQ` equals `∑ i, Q eᵢ * Q fᵢ` in
  every symplectic basis.
* `QuadraticMap.sum_neg_one_pow_val_eq`,
  `QuadraticMap.sum_neg_one_pow_val_eq_of_finrank_eq_two_mul`: the Gauss-sum identity
  `∑ v, (-1) ^ (Q v).val = (-1) ^ (Q.arf hQ).val * 2 ^ m`.
* `QuadraticMap.two_mul_card_filter_apply_eq_zero`,
  `QuadraticMap.card_filter_apply_eq_zero_of_pos`,
  `QuadraticMap.card_filter_apply_eq_one`: exact counts of vectors with `Q v = 0` and `Q v = 1`.
* `QuadraticMap.arf_eq_zero_iff_card_filter_lt`, `QuadraticMap.arf_eq_one_iff_card_filter_lt`:
  majority-value characterization of `Q.arf hQ`.
* `QuadraticMap.IsometryEquiv.arf_eq`, `QuadraticMap.Equivalent.arf_eq`: isometry invariance.
* `QuadraticMap.arf_prod`, `QuadraticMap.arf_pi`: additivity under orthogonal sums.
* `QuadraticMap.sum_neg_one_pow_val_eq_zero_of_mem_ker_polarBilin`,
  `QuadraticMap.sum_neg_one_pow_val_eq_card_radical_mul`: Gauss-sum dichotomy for general
  (possibly degenerate) forms over `𝔽₂`.

## References

* C. Arf, *Untersuchungen über quadratische Formen in Körpern der Charakteristik 2 (Teil I)*,
  J. Reine Angew. Math. 183 (1941), 148–167.
* W. Browder, *Surgery on Simply-Connected Manifolds*, Ergebnisse der Mathematik und ihrer
  Grenzgebiete 65, Springer (1972), §III.1.
* R. Pyronneau, *The Arf Invariant* (expository notes), §2.1.
-/

public section

open Module QuadraticMap

namespace QuadraticMap

/-! ### General Gauss-sum identities over `ZMod 2` -/

section GaussSumGeneral

/-- An isometric equivalence between finite quadratic spaces over `𝔽₂` preserves the Gauss sum. -/
theorem IsometryEquiv.sum_neg_one_pow_val_eq {V₁ V₂ : Type*}
    [AddCommGroup V₁] [Module (ZMod 2) V₁] [Fintype V₁]
    [AddCommGroup V₂] [Module (ZMod 2) V₂] [Fintype V₂]
    {Q₁ : QuadraticForm (ZMod 2) V₁} {Q₂ : QuadraticForm (ZMod 2) V₂}
    (e : Q₁.IsometryEquiv Q₂) :
    ∑ v : V₁, (-1 : ℤ) ^ (Q₁ v).val = ∑ w : V₂, (-1 : ℤ) ^ (Q₂ w).val :=
  Fintype.sum_equiv e.toEquiv _ _ fun v ↦ by
    rw [← e.map_app]
    rfl

/-- The Gauss sum of an orthogonal product over `𝔽₂` is the product of the Gauss sums of its
factors. -/
theorem sum_neg_one_pow_val_prod {V₁ V₂ : Type*}
    [AddCommGroup V₁] [Module (ZMod 2) V₁] [Fintype V₁]
    [AddCommGroup V₂] [Module (ZMod 2) V₂] [Fintype V₂]
    (Q₁ : QuadraticForm (ZMod 2) V₁) (Q₂ : QuadraticForm (ZMod 2) V₂) :
    ∑ v : V₁ × V₂, (-1 : ℤ) ^ (Q₁.prod Q₂ v).val =
      (∑ v₁ : V₁, (-1 : ℤ) ^ (Q₁ v₁).val) * ∑ v₂ : V₂, (-1 : ℤ) ^ (Q₂ v₂).val := by
  rw [Fintype.sum_prod_type, Finset.sum_mul]
  refine Finset.sum_congr rfl fun v₁ _ ↦ ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun v₂ _ ↦ ?_
  rw [QuadraticMap.prod_apply, ZMod.neg_one_pow_val_add]

/-- The Gauss sum of a finite orthogonal sum over `𝔽₂` is the product of the component Gauss
sums. -/
theorem sum_neg_one_pow_val_pi {ι : Type*} [Fintype ι] [DecidableEq ι] {Vᵢ : ι → Type*}
    [∀ i, AddCommGroup (Vᵢ i)] [∀ i, Module (ZMod 2) (Vᵢ i)] [∀ i, Fintype (Vᵢ i)]
    (Q : ∀ i, QuadraticForm (ZMod 2) (Vᵢ i)) :
    ∑ v : ∀ i, Vᵢ i, (-1 : ℤ) ^ (QuadraticMap.pi Q v).val =
      ∏ i : ι, ∑ x : Vᵢ i, (-1 : ℤ) ^ (Q i x).val := by
  calc ∑ v : ∀ i, Vᵢ i, (-1 : ℤ) ^ (QuadraticMap.pi Q v).val
      = ∑ v : ∀ i, Vᵢ i, ∏ i : ι, (-1 : ℤ) ^ (Q i (v i)).val := by
        refine Fintype.sum_congr _ _ fun v ↦ ?_
        rw [QuadraticMap.pi_apply, ZMod.neg_one_pow_val_sum]
    _ = ∏ i : ι, ∑ x : Vᵢ i, (-1 : ℤ) ^ (Q i x).val :=
        (Fintype.prod_sum fun i x ↦ (-1 : ℤ) ^ (Q i x).val).symm

/-- On a binary symplectic plane `symplecticPlane (ZMod 2) a b`, the four-element Gauss sum equals
`(-1) ^ (a * b).val * 2`. -/
theorem _root_.TauCeti.sum_neg_one_pow_val_symplecticPlane (a b : ZMod 2) :
    ∑ x : Fin 2 → ZMod 2, (-1 : ℤ) ^ (TauCeti.symplecticPlane (ZMod 2) a b x).val =
      (-1 : ℤ) ^ (a * b).val * 2 := by
  have heq : ∑ x : Fin 2 → ZMod 2, (-1 : ℤ) ^ (TauCeti.symplecticPlane (ZMod 2) a b x).val =
      ∑ p : ZMod 2 × ZMod 2, (-1 : ℤ) ^ (a * (p.1 * p.1) + p.1 * p.2 + b * (p.2 * p.2)).val :=
    Fintype.sum_equiv (finTwoArrowEquiv (ZMod 2)) _ _ fun x ↦ by
      simp [TauCeti.symplecticPlane_apply, finTwoArrowEquiv]
  rw [heq]
  clear heq
  revert a b
  decide

/-- In any symplectic basis `b : Basis (ι ⊕ ι) (ZMod 2) V` for `Q.polarBilin`, the Gauss sum of `Q`
is `(-1) ^ (∑ i, Q eᵢ * Q fᵢ).val * 2 ^ |ι|`. -/
theorem sum_neg_one_pow_val_eq_of_toMatrix_polarBilin_eq_J {V ι : Type*}
    [AddCommGroup V] [Module (ZMod 2) V] [Fintype V] [Fintype ι] [DecidableEq ι]
    (Q : QuadraticForm (ZMod 2) V) (b : Basis (ι ⊕ ι) (ZMod 2) V)
    (hb : LinearMap.BilinForm.toMatrix b Q.polarBilin = Matrix.J ι (ZMod 2)) :
    ∑ v : V, (-1 : ℤ) ^ (Q v).val =
      (-1 : ℤ) ^ (∑ i : ι, Q (b (Sum.inl i)) * Q (b (Sum.inr i))).val * 2 ^ Fintype.card ι := by
  calc ∑ v : V, (-1 : ℤ) ^ (Q v).val
      = ∑ x : ι → Fin 2 → ZMod 2, (-1 : ℤ) ^
          (QuadraticMap.pi (fun i ↦
            TauCeti.symplecticPlane (ZMod 2) (Q (b (Sum.inl i))) (Q (b (Sum.inr i)))) x).val :=
        (Q.isometryEquivPiSymplecticPlaneOfToMatrixEqJ b hb).sum_neg_one_pow_val_eq
    _ = ∏ i : ι, ((-1 : ℤ) ^ (Q (b (Sum.inl i)) * Q (b (Sum.inr i))).val * 2) := by
        rw [sum_neg_one_pow_val_pi]
        exact Fintype.prod_congr _ _ fun i ↦
          TauCeti.sum_neg_one_pow_val_symplecticPlane _ _
    _ = (-1 : ℤ) ^ (∑ i : ι, Q (b (Sum.inl i)) * Q (b (Sum.inr i))).val * 2 ^ Fintype.card ι := by
        rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ,
          ← ZMod.neg_one_pow_val_sum]

/-- Every vector of a finite space over `𝔽₂` satisfies `Q v = 0` or `Q v = 1`, so the two level
sets partition `V`. -/
theorem card_filter_apply_eq_zero_add_card_filter_apply_eq_one {V : Type*}
    [AddCommGroup V] [Module (ZMod 2) V] [Fintype V] (Q : QuadraticForm (ZMod 2) V) :
    (Finset.univ.filter fun v : V ↦ Q v = 0).card +
      (Finset.univ.filter fun v : V ↦ Q v = 1).card = Fintype.card V := by
  have hnot : (Finset.univ.filter fun v : V ↦ Q v = 1) =
      Finset.univ.filter fun v : V ↦ ¬ Q v = 0 := by
    ext v
    rcases ZMod.eq_zero_or_eq_one (Q v) with h | h <;> simp [h]
  rw [hnot, Finset.card_filter_add_card_filter_not, Finset.card_univ]

/-- The Gauss sum of `Q` over `𝔽₂` is the difference between the number of isotropic vectors and
the number of anisotropic vectors. -/
theorem sum_neg_one_pow_val_eq_sub_card_filter {V : Type*}
    [AddCommGroup V] [Module (ZMod 2) V] [Fintype V] (Q : QuadraticForm (ZMod 2) V) :
    ∑ v : V, (-1 : ℤ) ^ (Q v).val =
      ((Finset.univ.filter fun v : V ↦ Q v = 0).card : ℤ) -
        ((Finset.univ.filter fun v : V ↦ Q v = 1).card : ℤ) := by
  have hnot : (Finset.univ.filter fun v : V ↦ Q v = 1) =
      Finset.univ.filter fun v : V ↦ ¬ Q v = 0 := by
    ext v
    rcases ZMod.eq_zero_or_eq_one (Q v) with h | h <;> simp [h]
  calc ∑ v : V, (-1 : ℤ) ^ (Q v).val
      = ∑ v : V, (if Q v = 0 then (1 : ℤ) else -1) :=
        Fintype.sum_congr _ _ fun v ↦ ZMod.neg_one_pow_val_eq_ite (Q v)
    _ = (∑ _ ∈ Finset.univ.filter (fun v : V ↦ Q v = 0), (1 : ℤ)) +
        ∑ _ ∈ Finset.univ.filter (fun v : V ↦ ¬ Q v = 0), (-1 : ℤ) := by
        rw [← Finset.sum_ite]
    _ = ((Finset.univ.filter fun v : V ↦ Q v = 0).card : ℤ) -
        ((Finset.univ.filter fun v : V ↦ Q v = 1).card : ℤ) := by
        rw [hnot]
        simp [sub_eq_add_neg]

/-- If `Q` is nonzero on a vector in the kernel of `Q.polarBilin`, its Gauss sum vanishes. -/
theorem sum_neg_one_pow_val_eq_zero_of_mem_ker_polarBilin {V : Type*}
    [AddCommGroup V] [Module (ZMod 2) V] [Fintype V] (Q : QuadraticForm (ZMod 2) V)
    {x : V} (hx : x ∈ Q.polarBilin.ker) (hxQ : Q x ≠ 0) :
    ∑ v : V, (-1 : ℤ) ^ (Q v).val = 0 := by
  have hx1 : Q x = 1 := (ZMod.eq_zero_or_eq_one (Q x)).resolve_left hxQ
  have hshift (v : V) : Q (v + x) = Q v + 1 := by
    have hpol : polar Q v x = 0 := by
      rw [polar_comm]
      simpa [polarBilin_apply_apply] using LinearMap.congr_fun hx v
    rw [QuadraticMap.map_add Q v x, hx1, hpol, add_zero]
  have hsum : ∑ v : V, (-1 : ℤ) ^ (Q v).val = -(∑ v : V, (-1 : ℤ) ^ (Q v).val) := by
    calc ∑ v : V, (-1 : ℤ) ^ (Q v).val
        = ∑ v : V, (-1 : ℤ) ^ (Q (v + x)).val :=
          (Equiv.sum_comp (Equiv.addRight x) fun v ↦ (-1 : ℤ) ^ (Q v).val).symm
      _ = ∑ v : V, ((-1 : ℤ) ^ (Q v).val * (-1)) := by
          refine Fintype.sum_congr _ _ fun v ↦ ?_
          rw [hshift, ZMod.neg_one_pow_val_add]
          rfl
      _ = -(∑ v : V, (-1 : ℤ) ^ (Q v).val) := by
          rw [← Finset.sum_mul, mul_neg_one]
  omega

/-- Over `𝔽₂`, the Gauss sum of `Q` factors through the quotient by `Q.radical` with multiplicity
`Fintype.card Q.radical`. -/
theorem sum_neg_one_pow_val_eq_card_radical_mul_lift {V : Type*}
    [AddCommGroup V] [Module (ZMod 2) V] [Fintype V] (Q : QuadraticForm (ZMod 2) V)
    [Fintype Q.radical] [Fintype (V ⧸ Q.radical)] :
    ∑ v : V, (-1 : ℤ) ^ (Q v).val =
      Fintype.card Q.radical * ∑ q : V ⧸ Q.radical, (-1 : ℤ) ^ (Q.lift Q.radical le_rfl q).val := by
  rw [← (IsometryEquiv.prodRadicalLift Q).sum_neg_one_pow_val_eq, sum_neg_one_pow_val_prod]
  simp

end GaussSumGeneral

/-! ### Basis independence and definition of `QuadraticMap.arf` -/

/-- **Basis independence of the Arf sum.**

For any two symplectic bases `b` and `b'` of a quadratic space over `𝔽₂`, the sums
`∑ i, Q (b (inl i)) * Q (b (inr i))` and `∑ j, Q (b' (inl j)) * Q (b' (inr j))` coincide. -/
theorem sum_mul_eq_of_toMatrix_polarBilin_eq_J {V ι ι' : Type*}
    [AddCommGroup V] [Module (ZMod 2) V] [Fintype ι] [DecidableEq ι] [Fintype ι'] [DecidableEq ι']
    (Q : QuadraticForm (ZMod 2) V)
    (b : Basis (ι ⊕ ι) (ZMod 2) V) (hb : LinearMap.BilinForm.toMatrix b Q.polarBilin =
      Matrix.J ι (ZMod 2))
    (b' : Basis (ι' ⊕ ι') (ZMod 2) V) (hb' : LinearMap.BilinForm.toMatrix b' Q.polarBilin =
      Matrix.J ι' (ZMod 2)) :
    ∑ i : ι, Q (b (Sum.inl i)) * Q (b (Sum.inr i)) =
      ∑ j : ι', Q (b' (Sum.inl j)) * Q (b' (Sum.inr j)) := by
  let _ : Fintype V := Fintype.ofEquiv ((ι ⊕ ι) → ZMod 2) b.equivFun.symm.toEquiv
  have hcard : Fintype.card ι = Fintype.card ι' := by
    have hsum : Fintype.card (ι ⊕ ι) = Fintype.card (ι' ⊕ ι') :=
      Fintype.card_congr (b.indexEquiv b')
    simp only [Fintype.card_sum] at hsum
    omega
  have hg1 := Q.sum_neg_one_pow_val_eq_of_toMatrix_polarBilin_eq_J b hb
  have hg2 := Q.sum_neg_one_pow_val_eq_of_toMatrix_polarBilin_eq_J b' hb'
  rw [← hcard] at hg2
  have hpow : (-1 : ℤ) ^ (∑ i : ι, Q (b (Sum.inl i)) * Q (b (Sum.inr i))).val =
      (-1 : ℤ) ^ (∑ j : ι', Q (b' (Sum.inl j)) * Q (b' (Sum.inr j))).val :=
    mul_right_cancel₀ (pow_ne_zero (Fintype.card ι) (by decide)) (hg1.symm.trans hg2)
  exact ZMod.neg_one_pow_val_inj hpow

/-- **The Arf invariant of a finite-dimensional quadratic form over `𝔽₂` with nondegenerate polar
bilinear form.**

In any symplectic basis `(e₁, …, eₘ, f₁, …, fₘ)` for `Q.polarBilin`, it equals
`∑ i, Q eᵢ * Q fᵢ ∈ ZMod 2`; see `QuadraticMap.arf_eq_sum_of_toMatrix_polarBilin_eq_J`. -/
noncomputable def arf {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
    [FiniteDimensional (ZMod 2) V] (Q : QuadraticForm (ZMod 2) V)
    (hQ : Q.polarBilin.Nondegenerate) : ZMod 2 :=
  let m := (Q.exists_basis_toMatrix_polarBilin_eq_J hQ).choose
  let b := (Q.exists_basis_toMatrix_polarBilin_eq_J hQ).choose_spec.choose
  ∑ i : Fin m, Q (b (Sum.inl i)) * Q (b (Sum.inr i))

section ArfProperties

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V] {Q : QuadraticForm (ZMod 2) V}

/-- In any symplectic basis `b : Basis (ι ⊕ ι) (ZMod 2) V` for `Q.polarBilin`, `Q.arf hQ` equals
`∑ i : ι, Q (b (Sum.inl i)) * Q (b (Sum.inr i))`. -/
theorem arf_eq_sum_of_toMatrix_polarBilin_eq_J [FiniteDimensional (ZMod 2) V]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (hQ : Q.polarBilin.Nondegenerate) (b : Basis (ι ⊕ ι) (ZMod 2) V)
    (hb : LinearMap.BilinForm.toMatrix b Q.polarBilin = Matrix.J ι (ZMod 2)) :
    Q.arf hQ = ∑ i : ι, Q (b (Sum.inl i)) * Q (b (Sum.inr i)) :=
  Q.sum_mul_eq_of_toMatrix_polarBilin_eq_J _
    (Q.exists_basis_toMatrix_polarBilin_eq_J hQ).choose_spec.choose_spec b hb

/-- Formula for `Q.arf hQ` on a basis `b : Basis (ι ⊕ ι) (ZMod 2) V` with polar-isotropic halves
paired by the Kronecker delta. -/
theorem arf_eq_sum_of_polar_eq [FiniteDimensional (ZMod 2) V]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (hQ : Q.polarBilin.Nondegenerate) (b : Basis (ι ⊕ ι) (ZMod 2) V)
    (hll : ∀ i j, polar Q (b (Sum.inl i)) (b (Sum.inl j)) = 0)
    (hrr : ∀ i j, polar Q (b (Sum.inr i)) (b (Sum.inr j)) = 0)
    (hlr : ∀ i j, polar Q (b (Sum.inl i)) (b (Sum.inr j)) = if i = j then 1 else 0) :
    Q.arf hQ = ∑ i : ι, Q (b (Sum.inl i)) * Q (b (Sum.inr i)) :=
  Q.arf_eq_sum_of_toMatrix_polarBilin_eq_J hQ b
    ((Q.toMatrix_polarBilin_eq_J_iff b).mpr ⟨hll, hrr, hlr⟩)

/-- On a zero-dimensional space, the Arf invariant vanishes. -/
@[simp]
theorem arf_of_subsingleton [Subsingleton V] (hQ : Q.polarBilin.Nondegenerate) :
    Q.arf hQ = 0 := by
  have hb : LinearMap.BilinForm.toMatrix (Basis.empty V : Basis (Empty ⊕ Empty) (ZMod 2) V)
      Q.polarBilin = Matrix.J Empty (ZMod 2) := by
    ext x
    exact x.elim isEmptyElim isEmptyElim
  simpa using Q.arf_eq_sum_of_toMatrix_polarBilin_eq_J hQ (Basis.empty V) hb

/-- **Gauss-sum formula for the Arf invariant.**

For a quadratic form `Q` over `𝔽₂` of dimension `2 * m` with nondegenerate polar form,
`∑ v : V, (-1) ^ (Q v).val = (-1) ^ (Q.arf hQ).val * 2 ^ m`. -/
theorem sum_neg_one_pow_val_eq_of_finrank_eq_two_mul [Fintype V] {m : ℕ}
    (hQ : Q.polarBilin.Nondegenerate) (hm : Module.finrank (ZMod 2) V = 2 * m) :
    ∑ v : V, (-1 : ℤ) ^ (Q v).val = (-1 : ℤ) ^ (Q.arf hQ).val * 2 ^ m := by
  obtain ⟨b, hb⟩ := Q.exists_basis_toMatrix_polarBilin_eq_J_of_finrank_eq_two_mul hQ hm
  rw [Q.arf_eq_sum_of_toMatrix_polarBilin_eq_J hQ b hb,
    Q.sum_neg_one_pow_val_eq_of_toMatrix_polarBilin_eq_J b hb, Fintype.card_fin]

/-- Dimension-free form of the Gauss-sum formula:
`∑ v : V, (-1) ^ (Q v).val = (-1) ^ (Q.arf hQ).val * 2 ^ (finrank (ZMod 2) V / 2)`. -/
theorem sum_neg_one_pow_val_eq [Fintype V] (hQ : Q.polarBilin.Nondegenerate) :
    ∑ v : V, (-1 : ℤ) ^ (Q v).val =
      (-1 : ℤ) ^ (Q.arf hQ).val * 2 ^ (Module.finrank (ZMod 2) V / 2) := by
  obtain ⟨m, hm⟩ := (Q.even_finrank_of_nondegenerate_polarBilin hQ).exists_two_nsmul
  simp only [two_nsmul, ← two_mul] at hm
  rw [Q.sum_neg_one_pow_val_eq_of_finrank_eq_two_mul hQ hm, hm,
    Nat.mul_div_cancel_left m (by decide)]

/-- Twice the number of isotropic vectors of `Q` equals `2 ^ (2 * m) + (-1) ^ Arf(Q) * 2 ^ m`. -/
theorem two_mul_card_filter_apply_eq_zero [Fintype V] {m : ℕ}
    (hQ : Q.polarBilin.Nondegenerate) (hm : Module.finrank (ZMod 2) V = 2 * m) :
    2 * ((Finset.univ.filter fun v : V ↦ Q v = 0).card : ℤ) =
      2 ^ (2 * m) + (-1 : ℤ) ^ (Q.arf hQ).val * 2 ^ m := by
  have htotZ : ((Finset.univ.filter fun v : V ↦ Q v = 0).card : ℤ) +
      ((Finset.univ.filter fun v : V ↦ Q v = 1).card : ℤ) = 2 ^ (2 * m) := by
    have htot := Q.card_filter_apply_eq_zero_add_card_filter_apply_eq_one
    rw [Module.card_eq_pow_finrank (K := ZMod 2), ZMod.card, hm] at htot
    exact_mod_cast htot
  have hdiff := (Q.sum_neg_one_pow_val_eq_sub_card_filter).symm.trans
    (Q.sum_neg_one_pow_val_eq_of_finrank_eq_two_mul hQ hm)
  linarith [htotZ, hdiff]

/-- Twice the number of vectors with `Q v = 1` equals `2 ^ (2 * m) - (-1) ^ Arf(Q) * 2 ^ m`. -/
theorem two_mul_card_filter_apply_eq_one [Fintype V] {m : ℕ}
    (hQ : Q.polarBilin.Nondegenerate) (hm : Module.finrank (ZMod 2) V = 2 * m) :
    2 * ((Finset.univ.filter fun v : V ↦ Q v = 1).card : ℤ) =
      2 ^ (2 * m) - (-1 : ℤ) ^ (Q.arf hQ).val * 2 ^ m := by
  have htotZ : ((Finset.univ.filter fun v : V ↦ Q v = 0).card : ℤ) +
      ((Finset.univ.filter fun v : V ↦ Q v = 1).card : ℤ) = 2 ^ (2 * m) := by
    have htot := Q.card_filter_apply_eq_zero_add_card_filter_apply_eq_one
    rw [Module.card_eq_pow_finrank (K := ZMod 2), ZMod.card, hm] at htot
    exact_mod_cast htot
  have hdiff := (Q.sum_neg_one_pow_val_eq_sub_card_filter).symm.trans
    (Q.sum_neg_one_pow_val_eq_of_finrank_eq_two_mul hQ hm)
  linarith [htotZ, hdiff]

/-- **Isotropic-vector count in positive even dimension `2 * m`.**

When `0 < m`, the number of vectors with `Q v = 0` is
`2 ^ (2 * m - 1) + (-1) ^ Arf(Q) * 2 ^ (m - 1)`. -/
theorem card_filter_apply_eq_zero_of_pos [Fintype V] {m : ℕ}
    (hQ : Q.polarBilin.Nondegenerate) (hm : Module.finrank (ZMod 2) V = 2 * m) (hm0 : 0 < m) :
    ((Finset.univ.filter fun v : V ↦ Q v = 0).card : ℤ) =
      2 ^ (2 * m - 1) + (-1 : ℤ) ^ (Q.arf hQ).val * 2 ^ (m - 1) := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hm0.ne'
  have h2 := Q.two_mul_card_filter_apply_eq_zero hQ hm
  have hk : 2 * (k + 1) = (2 * k + 1) + 1 := rfl
  simp only [Nat.succ_eq_add_one, hk, Nat.add_sub_cancel, pow_succ'] at h2 ⊢
  linarith

/-- In even dimension `2 * m`, the number of vectors with `Q v = 1` is
`2 ^ (2 * m - 1) - (-1) ^ Arf(Q) * 2 ^ (m - 1)` (valid for `m = 0` as well via natural-number
subtraction `0 - 1 = 0`). -/
theorem card_filter_apply_eq_one [Fintype V] {m : ℕ}
    (hQ : Q.polarBilin.Nondegenerate) (hm : Module.finrank (ZMod 2) V = 2 * m) :
    ((Finset.univ.filter fun v : V ↦ Q v = 1).card : ℤ) =
      2 ^ (2 * m - 1) - (-1 : ℤ) ^ (Q.arf hQ).val * 2 ^ (m - 1) := by
  rcases m with _ | k
  · have : Subsingleton V := not_nontrivial_iff_subsingleton.mp fun hnt ↦
      (Module.finrank_pos_iff.mpr hnt).ne' hm
    have hempty : (Finset.univ.filter fun v : V ↦ Q v = 1) = ∅ := by
      ext v
      simp [Subsingleton.elim v 0]
    simp [hempty]
  · have h2 := Q.two_mul_card_filter_apply_eq_one hQ hm
    have hk : 2 * (k + 1) = (2 * k + 1) + 1 := rfl
    simp only [hk, Nat.add_sub_cancel, pow_succ'] at h2 ⊢
    linarith

/-- **Majority characterization of `Arf(Q) = 0`.**

The Arf invariant vanishes if and only if strictly more vectors satisfy `Q v = 0` than `Q v = 1`. -/
theorem arf_eq_zero_iff_card_filter_lt [Fintype V] (hQ : Q.polarBilin.Nondegenerate) :
    Q.arf hQ = 0 ↔
      (Finset.univ.filter fun v : V ↦ Q v = 1).card <
        (Finset.univ.filter fun v : V ↦ Q v = 0).card := by
  have hdiff := (Q.sum_neg_one_pow_val_eq_sub_card_filter).symm.trans
    (Q.sum_neg_one_pow_val_eq hQ)
  have hpow : (0 : ℤ) < 2 ^ (Module.finrank (ZMod 2) V / 2) := by positivity
  rcases ZMod.eq_zero_or_eq_one (Q.arf hQ) with harf | harf
  · rw [harf] at hdiff ⊢
    simp only [ZMod.val_zero, pow_zero, one_mul, true_iff] at hdiff ⊢
    omega
  · rw [harf] at hdiff ⊢
    have h01 : (1 : ZMod 2) ≠ 0 := by decide
    simp only [h01, ZMod.val_one, pow_one, neg_one_mul, false_iff] at hdiff ⊢
    omega

/-- **Majority characterization of `Arf(Q) = 1`.**

The Arf invariant equals `1` if and only if strictly more vectors satisfy `Q v = 1` than
`Q v = 0`. -/
theorem arf_eq_one_iff_card_filter_lt [Fintype V] (hQ : Q.polarBilin.Nondegenerate) :
    Q.arf hQ = 1 ↔
      (Finset.univ.filter fun v : V ↦ Q v = 0).card <
        (Finset.univ.filter fun v : V ↦ Q v = 1).card := by
  have hdiff := (Q.sum_neg_one_pow_val_eq_sub_card_filter).symm.trans
    (Q.sum_neg_one_pow_val_eq hQ)
  have hpow : (0 : ℤ) < 2 ^ (Module.finrank (ZMod 2) V / 2) := by positivity
  rcases ZMod.eq_zero_or_eq_one (Q.arf hQ) with harf | harf
  · rw [harf] at hdiff ⊢
    have h01 : (0 : ZMod 2) ≠ 1 := by decide
    simp only [h01, ZMod.val_zero, pow_zero, one_mul, false_iff] at hdiff ⊢
    omega
  · rw [harf] at hdiff ⊢
    simp only [ZMod.val_one, pow_one, neg_one_mul, true_iff] at hdiff ⊢
    omega

/-- When `Q` vanishes on `Q.polarBilin.ker` (so `Q.lift Q.radical le_rfl` has nondegenerate polar
form), the Gauss sum of `Q` is `|Q.radical| * (-1) ^ Arf(Q.lift) * 2 ^ (finrank / 2)`. -/
theorem sum_neg_one_pow_val_eq_card_radical_mul [Fintype V] (Q : QuadraticForm (ZMod 2) V)
    [Fintype Q.radical] (hker : ∀ x ∈ Q.polarBilin.ker, Q x = 0) :
    ∑ v : V, (-1 : ℤ) ^ (Q v).val =
      Fintype.card Q.radical *
        ((-1 : ℤ) ^ ((Q.lift Q.radical le_rfl).arf
          (nondegenerate_polarBilin_lift_radical_iff_forall_ker.mpr hker)).val *
          2 ^ (Module.finrank (ZMod 2) (V ⧸ Q.radical) / 2)) := by
  let _ : Fintype (V ⧸ Q.radical) := Fintype.ofFinite _
  rw [Q.sum_neg_one_pow_val_eq_card_radical_mul_lift,
    (Q.lift Q.radical le_rfl).sum_neg_one_pow_val_eq
      (nondegenerate_polarBilin_lift_radical_iff_forall_ker.mpr hker)]

end ArfProperties

/-! ### Invariance under isometry and additivity under orthogonal sums -/

section InvarianceAndSums

/-- An isometric equivalence between finite-dimensional quadratic spaces over `𝔽₂` preserves the
Arf invariant. -/
theorem IsometryEquiv.arf_eq {V₁ V₂ : Type*}
    [AddCommGroup V₁] [Module (ZMod 2) V₁] [FiniteDimensional (ZMod 2) V₁]
    [AddCommGroup V₂] [Module (ZMod 2) V₂] [FiniteDimensional (ZMod 2) V₂]
    {Q₁ : QuadraticForm (ZMod 2) V₁} {Q₂ : QuadraticForm (ZMod 2) V₂}
    (e : Q₁.IsometryEquiv Q₂)
    (hQ₁ : Q₁.polarBilin.Nondegenerate) (hQ₂ : Q₂.polarBilin.Nondegenerate) :
    Q₁.arf hQ₁ = Q₂.arf hQ₂ := by
  classical
  let _ : Fintype V₁ :=
    Fintype.ofEquiv _ (IsNoetherian.finsetBasis (ZMod 2) V₁).equivFun.symm.toEquiv
  let _ : Fintype V₂ :=
    Fintype.ofEquiv _ (IsNoetherian.finsetBasis (ZMod 2) V₂).equivFun.symm.toEquiv
  have hg := e.sum_neg_one_pow_val_eq
  rw [Q₁.sum_neg_one_pow_val_eq hQ₁, Q₂.sum_neg_one_pow_val_eq hQ₂,
    e.toLinearEquiv.finrank_eq] at hg
  exact ZMod.neg_one_pow_val_inj
    (mul_right_cancel₀ (pow_ne_zero _ (by decide)) hg)

/-- Isometric finite-dimensional quadratic forms over `𝔽₂` have equal Arf invariants. -/
theorem Equivalent.arf_eq {V₁ V₂ : Type*}
    [AddCommGroup V₁] [Module (ZMod 2) V₁] [FiniteDimensional (ZMod 2) V₁]
    [AddCommGroup V₂] [Module (ZMod 2) V₂] [FiniteDimensional (ZMod 2) V₂]
    {Q₁ : QuadraticForm (ZMod 2) V₁} {Q₂ : QuadraticForm (ZMod 2) V₂}
    (h : Q₁.Equivalent Q₂)
    (hQ₁ : Q₁.polarBilin.Nondegenerate) (hQ₂ : Q₂.polarBilin.Nondegenerate) :
    Q₁.arf hQ₁ = Q₂.arf hQ₂ := by
  obtain ⟨e⟩ := h
  exact e.arf_eq hQ₁ hQ₂

/-- **Additivity of the Arf invariant under orthogonal products.** -/
@[simp]
theorem arf_prod {V₁ V₂ : Type*}
    [AddCommGroup V₁] [Module (ZMod 2) V₁] [FiniteDimensional (ZMod 2) V₁]
    [AddCommGroup V₂] [Module (ZMod 2) V₂] [FiniteDimensional (ZMod 2) V₂]
    (Q₁ : QuadraticForm (ZMod 2) V₁) (Q₂ : QuadraticForm (ZMod 2) V₂)
    (hQ : (Q₁.prod Q₂).polarBilin.Nondegenerate) :
    (Q₁.prod Q₂).arf hQ =
      Q₁.arf (nondegenerate_polarBilin_prod_iff.mp hQ).1 +
        Q₂.arf (nondegenerate_polarBilin_prod_iff.mp hQ).2 := by
  classical
  let hQ₁ := (nondegenerate_polarBilin_prod_iff.mp hQ).1
  let hQ₂ := (nondegenerate_polarBilin_prod_iff.mp hQ).2
  let _ : Fintype V₁ :=
    Fintype.ofEquiv _ (IsNoetherian.finsetBasis (ZMod 2) V₁).equivFun.symm.toEquiv
  let _ : Fintype V₂ :=
    Fintype.ofEquiv _ (IsNoetherian.finsetBasis (ZMod 2) V₂).equivFun.symm.toEquiv
  obtain ⟨m₁, hm₁⟩ := (Q₁.even_finrank_of_nondegenerate_polarBilin hQ₁).exists_two_nsmul
  obtain ⟨m₂, hm₂⟩ := (Q₂.even_finrank_of_nondegenerate_polarBilin hQ₂).exists_two_nsmul
  simp only [two_nsmul, ← two_mul] at hm₁ hm₂
  have hm : Module.finrank (ZMod 2) (V₁ × V₂) = 2 * (m₁ + m₂) := by
    rw [Module.finrank_prod, hm₁, hm₂, mul_add]
  have hg := sum_neg_one_pow_val_prod Q₁ Q₂
  rw [(Q₁.prod Q₂).sum_neg_one_pow_val_eq_of_finrank_eq_two_mul hQ hm,
    Q₁.sum_neg_one_pow_val_eq_of_finrank_eq_two_mul hQ₁ hm₁,
    Q₂.sum_neg_one_pow_val_eq_of_finrank_eq_two_mul hQ₂ hm₂] at hg
  have hmul : (-1 : ℤ) ^ ((Q₁.prod Q₂).arf hQ).val * 2 ^ (m₁ + m₂) =
      (-1 : ℤ) ^ (Q₁.arf hQ₁ + Q₂.arf hQ₂).val * 2 ^ (m₁ + m₂) := by
    rw [hg, ZMod.neg_one_pow_val_add, pow_add]
    ring
  exact ZMod.neg_one_pow_val_inj (mul_right_cancel₀ (pow_ne_zero _ (by decide)) hmul)

/-- **Additivity of the Arf invariant under finite orthogonal sums.** -/
@[simp]
theorem arf_pi {ι : Type*} [Fintype ι] {Vᵢ : ι → Type*}
    [∀ i, AddCommGroup (Vᵢ i)] [∀ i, Module (ZMod 2) (Vᵢ i)]
    [∀ i, FiniteDimensional (ZMod 2) (Vᵢ i)]
    (Q : ∀ i, QuadraticForm (ZMod 2) (Vᵢ i))
    (hQ : (QuadraticMap.pi Q).polarBilin.Nondegenerate) :
    (QuadraticMap.pi Q).arf hQ =
      ∑ i : ι, (Q i).arf (nondegenerate_polarBilin_pi_iff.mp hQ i) := by
  classical
  let hQi : ∀ i, (Q i).polarBilin.Nondegenerate := nondegenerate_polarBilin_pi_iff.mp hQ
  let _ : ∀ i, Fintype (Vᵢ i) := fun i ↦
    Fintype.ofEquiv _ (IsNoetherian.finsetBasis (ZMod 2) (Vᵢ i)).equivFun.symm.toEquiv
  have heven (i : ι) : 2 * (Module.finrank (ZMod 2) (Vᵢ i) / 2) =
      Module.finrank (ZMod 2) (Vᵢ i) := by
    obtain ⟨m, hm⟩ := ((Q i).even_finrank_of_nondegenerate_polarBilin (hQi i)).exists_two_nsmul
    simp only [two_nsmul] at hm
    omega
  have hdim : Module.finrank (ZMod 2) (∀ i, Vᵢ i) =
      2 * ∑ i : ι, (Module.finrank (ZMod 2) (Vᵢ i) / 2) := by
    rw [Module.finrank_pi_fintype, Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ ↦ (heven i).symm
  have hg := sum_neg_one_pow_val_pi Q
  rw [(QuadraticMap.pi Q).sum_neg_one_pow_val_eq_of_finrank_eq_two_mul hQ hdim] at hg
  have hprod : (∏ i : ι, ∑ x : Vᵢ i, (-1 : ℤ) ^ (Q i x).val) =
      (-1 : ℤ) ^ (∑ i : ι, (Q i).arf (hQi i)).val *
        2 ^ (∑ i : ι, (Module.finrank (ZMod 2) (Vᵢ i) / 2)) := by
    calc (∏ i : ι, ∑ x : Vᵢ i, (-1 : ℤ) ^ (Q i x).val)
        = ∏ i : ι, ((-1 : ℤ) ^ ((Q i).arf (hQi i)).val *
            2 ^ (Module.finrank (ZMod 2) (Vᵢ i) / 2)) :=
          Fintype.prod_congr _ _ fun i ↦ (Q i).sum_neg_one_pow_val_eq (hQi i)
      _ = (-1 : ℤ) ^ (∑ i : ι, (Q i).arf (hQi i)).val *
            2 ^ (∑ i : ι, (Module.finrank (ZMod 2) (Vᵢ i) / 2)) := by
          rw [Finset.prod_mul_distrib, ← ZMod.neg_one_pow_val_sum, Finset.prod_pow_eq_pow_sum]
  exact ZMod.neg_one_pow_val_inj
    (mul_right_cancel₀ (pow_ne_zero _ (by decide)) (hg.trans hprod))

end InvarianceAndSums

end QuadraticMap

namespace TauCeti

/-- The Arf invariant of `TauCeti.symplecticPlane (ZMod 2) a b` is `a * b`. -/
@[simp]
theorem arf_symplecticPlane (a b : ZMod 2)
    (hQ : (symplecticPlane (ZMod 2) a b).polarBilin.Nondegenerate :=
      nondegenerate_polarBilin_symplecticPlane a b) :
    (symplecticPlane (ZMod 2) a b).arf hQ = a * b := by
  have hg := sum_neg_one_pow_val_symplecticPlane a b
  have hdim : Module.finrank (ZMod 2) (Fin 2 → ZMod 2) = 2 * 1 := by simp
  rw [(symplecticPlane (ZMod 2) a b).sum_neg_one_pow_val_eq_of_finrank_eq_two_mul hQ hdim,
    pow_one] at hg
  exact ZMod.neg_one_pow_val_inj (mul_right_cancel₀ (by decide : (2 : ℤ) ≠ 0) hg)

/-- The split hyperbolic plane over `𝔽₂` has Arf invariant `0`. -/
@[simp]
theorem arf_splitHyperbolicPlane
    (hQ : (splitHyperbolicPlane (ZMod 2)).polarBilin.Nondegenerate :=
      nondegenerate_polarBilin_splitHyperbolicPlane) :
    (splitHyperbolicPlane (ZMod 2)).arf hQ = 0 := by
  have heq : (splitHyperbolicPlane (ZMod 2)).Equivalent (symplecticPlane (ZMod 2) 0 0) := by
    rw [symplecticPlane_zero_zero]
    exact Equivalent.refl _
  rw [heq.arf_eq hQ (nondegenerate_polarBilin_symplecticPlane 0 0), arf_symplecticPlane, mul_zero]

end TauCeti
