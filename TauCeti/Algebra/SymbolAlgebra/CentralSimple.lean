/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.SymbolAlgebra.Basic
public import TauCeti.Algebra.BrauerGroup.Group
public import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.FreeModule.Finite.Matrix
import TauCeti.Algebra.BrauerGroup.Trivial

/-!
# Cyclic algebras are central simple

Let `K` be a field, `n ≠ 0`, `ζ ∈ K` a primitive `n`-th root of unity and `a, b ∈ Kˣ`. This file
proves that the symbol algebra `(a, b)_ζ` of `TauCeti/Algebra/SymbolAlgebra/Basic.lean`, generated
by `x, y` with `x ^ n = a`, `y ^ n = b` and `y * x = ζ • (x * y)`, is a central simple
`K`-algebra of dimension `n ^ 2`: the **cyclic algebra** `(a, b)_ζ`. It defines its class in the
Brauer group, and shows that the class is trivial when `b = 1`.

Both structural proofs compare coordinates in the monomial basis `x ^ i * y ^ j`, `i, j < n`.
Conjugation by the unit `x` multiplies `x ^ i * y ^ j` by `ζ ^ j`, and conjugation by `y`
multiplies it by `ζ ^ i`; since `ζ` is a primitive `n`-th root of unity these two characters
separate the `n ^ 2` monomials.

* **Simplicity**: a nonzero element `z` of a two-sided ideal with two distinct monomials `p ≠ q`
  in its support gives the element `φ z - c_q • z` of the ideal, where `φ` is a conjugation whose
  characters `c` separate `p` from `q`. It is nonzero with a smaller support. An element of minimal
  support is therefore a nonzero multiple of a monomial, which is a unit.
* **Centrality**: a central element is fixed by both conjugations, so all its coordinates off the
  monomial `1` vanish.

For `b = 1`, the representation `TauCeti.SymbolAlgebra.toEndAdjoinRoot` of `(a, 1)_ζ` on the
`n`-dimensional space `K[X]/(X ^ n - a)` is injective because the algebra is simple, hence an
isomorphism by counting dimensions; so `(a, 1)_ζ` is split and its Brauer class is trivial.

## Main definitions

* `TauCeti.SymbolAlgebra.brauerClass`: the Brauer class of the cyclic algebra `(a, b)_ζ`.
* `TauCeti.SymbolAlgebra.algEquivEndAdjoinRoot`: `(a, 1)_ζ ≃ₐ[K] End_K(K[X]/(X ^ n - a))`.

## Main results

* `TauCeti.SymbolAlgebra.isSimpleRing`: the cyclic algebra is simple.
* `TauCeti.SymbolAlgebra.isCentral`: the cyclic algebra is central.
* `TauCeti.SymbolAlgebra.brauerClass_one_right`: the Brauer class of `(a, 1)_ζ` is trivial.

## References

* P. Gille, T. Szamuely, *Central Simple Algebras and Galois Cohomology*, CUP (2006), §2.5.
* The coordinate-comparison proofs of simplicity and centrality follow the crossed-product case in
  `TauCeti/Algebra/CrossedProduct/CentralSimple.lean`.
-/

public section

open Polynomial

namespace TauCeti

namespace SymbolAlgebra

variable {K : Type*} [Field K] {n : ℕ} [NeZero n] {ζ a b : K}

/-- If the monomials are eigenvectors of a linear map `φ`, the coordinates of `φ z` are those of `z`
multiplied by the eigenvalues. -/
private theorem repr_apply_of_eigen (hζ : ζ ^ n = 1)
    (φ : SymbolAlgebra n ζ a b →ₗ[K] SymbolAlgebra n ζ a b) (c : Fin n × Fin n → K)
    (h : ∀ r, φ (basis hζ r) = c r • basis hζ r) (z : SymbolAlgebra n ζ a b) (r : Fin n × Fin n) :
    (basis hζ).repr (φ z) r = c r * (basis hζ).repr z r := by
  classical
  have : (basis hζ).coord r ∘ₗ φ = c r • (basis hζ).coord r := (basis hζ).ext fun s => by
    by_cases hsr : s = r
    · subst hsr; simp [h, -basis_apply]
    · simp [h, hsr, -basis_apply]
  simpa using congr($this z)

/-- The generator `x` as a unit, for `a ≠ 0`. -/
private noncomputable def unitX (ha : a ≠ 0) : (SymbolAlgebra n ζ a b)ˣ :=
  (isUnit_x (Ne.isUnit ha)).unit

/-- The generator `y` as a unit, for `b ≠ 0`. -/
private noncomputable def unitY (hb : b ≠ 0) : (SymbolAlgebra n ζ a b)ˣ :=
  (isUnit_y (Ne.isUnit hb)).unit

private theorem coe_unitX (ha : a ≠ 0) :
    ((unitX (n := n) (ζ := ζ) (b := b) ha : (SymbolAlgebra n ζ a b)ˣ) : SymbolAlgebra n ζ a b) =
      x :=
  IsUnit.unit_spec _

private theorem coe_unitY (hb : b ≠ 0) :
    ((unitY (n := n) (ζ := ζ) (a := a) hb : (SymbolAlgebra n ζ a b)ˣ) : SymbolAlgebra n ζ a b) =
      y :=
  IsUnit.unit_spec _

/-- Conjugation `z ↦ x⁻¹ * z * x` by the unit `x`. -/
private noncomputable def conjX (ha : a ≠ 0) : SymbolAlgebra n ζ a b →ₗ[K] SymbolAlgebra n ζ a b :=
  LinearMap.mulLeft K ((unitX ha)⁻¹ : (SymbolAlgebra n ζ a b)ˣ).val ∘ₗ
    LinearMap.mulRight K (unitX ha : (SymbolAlgebra n ζ a b)ˣ).val

/-- Conjugation `z ↦ y * z * y⁻¹` by the unit `y`. -/
private noncomputable def conjY (hb : b ≠ 0) : SymbolAlgebra n ζ a b →ₗ[K] SymbolAlgebra n ζ a b :=
  LinearMap.mulLeft K (unitY hb : (SymbolAlgebra n ζ a b)ˣ).val ∘ₗ
    LinearMap.mulRight K ((unitY hb)⁻¹ : (SymbolAlgebra n ζ a b)ˣ).val

private theorem conjX_apply (ha : a ≠ 0) (z : SymbolAlgebra n ζ a b) :
    conjX ha z = ((unitX (n := n) (ζ := ζ) (b := b) ha)⁻¹ : (SymbolAlgebra n ζ a b)ˣ).val *
      (z * (unitX (n := n) (ζ := ζ) (b := b) ha : (SymbolAlgebra n ζ a b)ˣ).val) :=
  rfl

private theorem conjY_apply (hb : b ≠ 0) (z : SymbolAlgebra n ζ a b) :
    conjY hb z = (unitY (n := n) (ζ := ζ) (a := a) hb : (SymbolAlgebra n ζ a b)ˣ).val *
      (z * ((unitY (n := n) (ζ := ζ) (a := a) hb)⁻¹ : (SymbolAlgebra n ζ a b)ˣ).val) :=
  rfl

private theorem conjX_basis (hζ : ζ ^ n = 1) (ha : a ≠ 0) (p : Fin n × Fin n) :
    conjX (b := b) ha (basis hζ p) = ζ ^ (p.2 : ℕ) • basis hζ p := by
  rw [conjX_apply, basis_apply, coe_unitX, x_pow_mul_y_pow_mul_x, mul_smul_comm, ← coe_unitX ha,
    Units.inv_mul_cancel_left]

private theorem conjY_basis (hζ : ζ ^ n = 1) (hb : b ≠ 0) (p : Fin n × Fin n) :
    conjY (a := a) hb (basis hζ p) = ζ ^ (p.1 : ℕ) • basis hζ p := by
  rw [conjY_apply, basis_apply, ← mul_assoc, coe_unitY, y_mul_x_pow_mul_y_pow, smul_mul_assoc,
    ← coe_unitY hb, Units.mul_inv_cancel_right]

private theorem conjX_mem (ha : a ≠ 0) (I : TwoSidedIdeal (SymbolAlgebra n ζ a b)) {z}
    (hz : z ∈ I) : conjX ha z ∈ I := by
  rw [conjX_apply]
  exact I.mul_mem_left _ _ (I.mul_mem_right _ _ hz)

private theorem conjY_mem (hb : b ≠ 0) (I : TwoSidedIdeal (SymbolAlgebra n ζ a b)) {z}
    (hz : z ∈ I) : conjY hb z ∈ I := by
  rw [conjY_apply]
  exact I.mul_mem_left _ _ (I.mul_mem_right _ _ hz)

/-- Two distinct monomials are separated by one of the two conjugations: one of them preserves every
two-sided ideal and has the monomials as eigenvectors with different eigenvalues at `p` and `q`. -/
private theorem exists_conj_separating (hζ : IsPrimitiveRoot ζ n) (ha : a ≠ 0) (hb : b ≠ 0)
    {p q : Fin n × Fin n} (hpq : p ≠ q) :
    ∃ (φ : SymbolAlgebra n ζ a b →ₗ[K] SymbolAlgebra n ζ a b) (c : Fin n × Fin n → K),
      (∀ r, φ (basis hζ.pow_eq_one r) = c r • basis hζ.pow_eq_one r) ∧
      (∀ I : TwoSidedIdeal (SymbolAlgebra n ζ a b), ∀ z ∈ I, φ z ∈ I) ∧ c p ≠ c q := by
  by_cases h2 : p.2 = q.2
  · have h1 : p.1 ≠ q.1 := fun h1 => hpq (Prod.ext h1 h2)
    exact ⟨conjY hb, fun r => ζ ^ (r.1 : ℕ), conjY_basis _ hb, fun I _ hz => conjY_mem hb I hz,
      fun h => h1 (Fin.ext (hζ.pow_inj p.1.isLt q.1.isLt h))⟩
  · exact ⟨conjX ha, fun r => ζ ^ (r.2 : ℕ), conjX_basis _ ha, fun I _ hz => conjX_mem ha I hz,
      fun h => h2 (Fin.ext (hζ.pow_inj p.2.isLt q.2.isLt h))⟩

/-- A nonzero element of a two-sided ideal whose support has at most `k` monomials yields a
monomial in the ideal. -/
private theorem exists_basis_mem (hζ : IsPrimitiveRoot ζ n) (ha : a ≠ 0) (hb : b ≠ 0)
    (I : TwoSidedIdeal (SymbolAlgebra n ζ a b)) (k : ℕ) :
    ∀ z ∈ I, z ≠ 0 → ((basis hζ.pow_eq_one).repr z).support.card ≤ k →
      ∃ p, basis hζ.pow_eq_one p ∈ I := by
  set B := basis (a := a) (b := b) hζ.pow_eq_one
  induction k with
  | zero =>
    intro z _ hz hcard
    simp_all
  | succ k ih =>
    classical
    intro z hzI hz hcard
    have hpos : 0 < (B.repr z).support.card := by simp_all
    rcases (Nat.succ_le_of_lt hpos).eq_or_lt with h1 | h1
    · -- a single monomial `c • B p` with `c ≠ 0`
      obtain ⟨p, c, hc, hp⟩ := Finsupp.card_support_eq_one'.1 h1.symm
      refine ⟨p, ?_⟩
      have hz' : z = c • B p := by rw [← B.repr_symm_single, ← hp, LinearEquiv.symm_apply_apply]
      have := I.mul_mem_left (algebraMap K _ c⁻¹) _ hzI
      rwa [hz', ← Algebra.smul_def, smul_smul, inv_mul_cancel₀ hc, one_smul] at this
    · -- two distinct monomials `p ≠ q`, separated by a conjugation `φ`
      obtain ⟨p, hp, q, hq, hpq⟩ := Finset.one_lt_card.1 h1
      obtain ⟨φ, c, hφ, hφI, hc⟩ := exists_conj_separating hζ ha hb hpq
      have hrepr : ∀ r, B.repr (φ z - c q • z) r = (c r - c q) * B.repr z r := fun r => by
        rw [map_sub, Finsupp.sub_apply, repr_apply_of_eigen _ φ c hφ, map_smul, Finsupp.smul_apply,
          smul_eq_mul, sub_mul]
      refine ih (φ z - c q • z) (I.sub_mem (hφI I z hzI) ?_) ?_ ?_
      · rw [Algebra.smul_def]
        exact I.mul_mem_left _ _ hzI
      · intro h0
        have := hrepr p
        rw [h0, map_zero, Finsupp.zero_apply] at this
        exact mul_ne_zero (sub_ne_zero.2 hc) (Finsupp.mem_support_iff.1 hp) this.symm
      · have hsub : (B.repr (φ z - c q • z)).support ⊆ (B.repr z).support.erase q := fun r hr => by
          rw [Finsupp.mem_support_iff, hrepr] at hr
          refine Finset.mem_erase.2 ⟨?_, Finsupp.mem_support_iff.2 (right_ne_zero_of_mul hr)⟩
          rintro rfl
          simp at hr
        have := Finset.card_le_card hsub
        rw [Finset.card_erase_of_mem hq] at this
        omega

/-- **The cyclic algebra `(a, b)_ζ` is a simple ring** when `ζ` is a primitive `n`-th root of unity
and `a, b ≠ 0`. -/
theorem isSimpleRing (hζ : IsPrimitiveRoot ζ n) (ha : a ≠ 0) (hb : b ≠ 0) :
    IsSimpleRing (SymbolAlgebra n ζ a b) :=
  have := nontrivial (a := a) (b := b) hζ.pow_eq_one
  .of_eq_bot_or_eq_top fun I => or_iff_not_imp_left.2 fun hI => by
    obtain ⟨z, hzI, hz : z ≠ 0⟩ := IsConcreteLE.exists_of_lt (bot_lt_iff_ne_bot.2 hI)
    obtain ⟨p, hp⟩ := exists_basis_mem hζ ha hb I _ z hzI hz le_rfl
    obtain ⟨u, hu⟩ : IsUnit (basis (a := a) (b := b) hζ.pow_eq_one p) := by
      rw [basis_apply]
      exact ((isUnit_x (Ne.isUnit ha)).pow _).mul ((isUnit_y (Ne.isUnit hb)).pow _)
    apply I.one_mem_iff.1
    rw [← u.inv_mul, hu]
    exact I.mul_mem_left _ _ hp

/-- **The cyclic algebra `(a, b)_ζ` is central** when `ζ` is a primitive `n`-th root of unity and
`a, b ≠ 0`. -/
theorem isCentral (hζ : IsPrimitiveRoot ζ n) (ha : a ≠ 0) (hb : b ≠ 0) :
    Algebra.IsCentral K (SymbolAlgebra n ζ a b) where
  out z hz := by
    classical
    set B := basis (a := a) (b := b) hζ.pow_eq_one
    rw [Subalgebra.mem_center_iff] at hz
    -- a coordinate whose eigenvalue under a conjugation fixing `z` is not `1` vanishes
    have hfix : ∀ (φ : SymbolAlgebra n ζ a b →ₗ[K] SymbolAlgebra n ζ a b)
        (c : Fin n × Fin n → K), (∀ r, φ (B r) = c r • B r) → φ z = z →
        ∀ r, c r ≠ 1 → B.repr z r = 0 := fun φ c hφ hφz r hr => by
      have h := repr_apply_of_eigen _ φ c hφ z r
      rw [hφz] at h
      exact (mul_eq_zero.1 (by linear_combination -h)).resolve_left (sub_ne_zero.2 hr)
    have hx : conjX (b := b) ha z = z := by
      rw [conjX_apply, ← hz, Units.inv_mul_cancel_left]
    have hy : conjY (a := a) hb z = z := by
      rw [conjY_apply, ← mul_assoc, hz, Units.mul_inv_cancel_right]
    have h0 : ∀ r : Fin n × Fin n, r ≠ 0 → B.repr z r = 0 := fun r hr => by
      by_cases h2 : r.2 = 0
      · refine hfix _ _ (conjY_basis _ hb) hy r fun h => ?_
        have h1 : r.1 = 0 := Fin.ext (hζ.pow_inj r.1.isLt (NeZero.pos n) (by simp [h]))
        exact hr (Prod.ext h1 h2)
      · exact hfix _ _ (conjX_basis _ ha) hx r fun h =>
          h2 (Fin.ext (hζ.pow_inj r.2.isLt (NeZero.pos n) (by simp [h])))
    have hz1 : z = B.repr z 0 • B 0 := B.repr.injective <| Finsupp.ext fun r => by
      rw [map_smul, B.repr_self, Finsupp.smul_apply, Finsupp.single_apply]
      by_cases hr : (0 : Fin n × Fin n) = r
      · subst hr
        simp
      · simp [hr, h0 r (Ne.symm hr)]
    rw [hz1, basis_apply]
    simp [Algebra.smul_def]

/-- The **Brauer class** of the cyclic algebra `(a, b)_ζ`, for `ζ` a primitive `n`-th root of unity
and `a, b ≠ 0`. -/
noncomputable def brauerClass (hζ : IsPrimitiveRoot ζ n) (ha : a ≠ 0) (hb : b ≠ 0) :
    BrauerGroup K :=
  have := isCentral hζ ha hb
  have := isSimpleRing hζ ha hb
  have := finite (a := a) (b := b) hζ.pow_eq_one
  BrauerGroup.mk (CSA.of K (SymbolAlgebra n ζ a b))

/-- `K[X]/(X ^ n - a)` has dimension `n`. -/
private theorem finrank_adjoinRoot (a : K) : Module.finrank K (AdjoinRoot (X ^ n - C a)) = n := by
  rw [(AdjoinRoot.powerBasis' (monic_X_pow_sub_C a (NeZero.ne n))).finrank,
    AdjoinRoot.powerBasis'_dim, natDegree_X_pow_sub_C]

private theorem nontrivial_adjoinRoot (a : K) : Nontrivial (AdjoinRoot (X ^ n - C a)) :=
  Module.nontrivial_of_finrank_pos (R := K) (by rw [finrank_adjoinRoot]; exact NeZero.pos n)

/-- `(a, 1)_ζ` is the endomorphism algebra of the `n`-dimensional space `K[X]/(X ^ n - a)`, through
its representation `TauCeti.SymbolAlgebra.toEndAdjoinRoot`. -/
noncomputable def algEquivEndAdjoinRoot (hζ : IsPrimitiveRoot ζ n) (ha : a ≠ 0) :
    SymbolAlgebra n ζ a 1 ≃ₐ[K] Module.End K (AdjoinRoot (X ^ n - C a)) :=
  have := isSimpleRing hζ ha one_ne_zero
  have := finite (a := a) (b := 1) hζ.pow_eq_one
  have := (monic_X_pow_sub_C a (NeZero.ne n)).finite_adjoinRoot
  have := (monic_X_pow_sub_C a (NeZero.ne n)).free_adjoinRoot
  have := nontrivial_adjoinRoot (n := n) a
  AlgEquiv.ofBijective (toEndAdjoinRoot a hζ.pow_eq_one) <| by
    have hinj := (toEndAdjoinRoot a hζ.pow_eq_one).toRingHom.injective
    refine ⟨hinj, ?_⟩
    exact (LinearMap.injective_iff_surjective_of_finrank_eq_finrank (f :=
      (toEndAdjoinRoot a hζ.pow_eq_one).toLinearMap)
      (by rw [finrank_eq hζ.pow_eq_one, Module.finrank_linearMap, finrank_adjoinRoot, sq])).1 hinj

@[simp]
theorem algEquivEndAdjoinRoot_apply (hζ : IsPrimitiveRoot ζ n) (ha : a ≠ 0)
    (z : SymbolAlgebra n ζ a 1) :
    algEquivEndAdjoinRoot hζ ha z = toEndAdjoinRoot a hζ.pow_eq_one z := by
  unfold algEquivEndAdjoinRoot
  exact AlgEquiv.ofBijective_apply _ _ _

/-- **The cyclic algebra `(a, 1)_ζ` is split**: its Brauer class is trivial. -/
theorem brauerClass_one_right (hζ : IsPrimitiveRoot ζ n) (ha : a ≠ 0) :
    brauerClass hζ ha one_ne_zero = 1 := by
  have := (monic_X_pow_sub_C a (NeZero.ne n)).finite_adjoinRoot
  have := nontrivial_adjoinRoot (n := n) a
  rw [brauerClass, BrauerGroup.mk_eq_one_iff]
  exact (IsBrauerEquivalent.of_algEquiv K (algEquivEndAdjoinRoot hζ ha)).trans
    (isBrauerTrivial_end K _)

end SymbolAlgebra

end TauCeti
