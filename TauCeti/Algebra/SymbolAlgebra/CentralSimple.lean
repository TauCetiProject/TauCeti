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
import TauCeti.LinearAlgebra.Eigenspace.DiagonalBasis

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
separate the `n ^ 2` monomials, so the monomial basis jointly diagonalizes the two conjugations
with pairwise distinct joint eigenvalues.

* **Simplicity**: a two-sided ideal is invariant under both conjugations, so it contains every
  monomial occurring in one of its elements (`Module.Basis.self_mem_of_repr_ne_zero_of_forall`);
  a nonzero ideal therefore contains a monomial, which is a unit.
* **Centrality**: a central element is fixed by both conjugations, so all its coordinates off the
  monomial `1` vanish (`Module.Basis.repr_eq_zero_of_weight_ne`).

For `b = 1`, the representation `TauCeti.SymbolAlgebra.toEndAdjoinRoot` of `(a, 1)_ζ` on the
`n`-dimensional space `K[X]/(X ^ n - a)` is injective because the algebra is simple, hence an
isomorphism by counting dimensions; so `(a, 1)_ζ` is split and its Brauer class is trivial.

## Main definitions

* `TauCeti.SymbolAlgebra.brauerClass`: the Brauer class of the cyclic algebra `(a, b)_ζ`.
* `TauCeti.SymbolAlgebra.algEquivEndAdjoinRoot`: `(a, 1)_ζ ≃ₐ[K] End_K(K[X]/(X ^ n - a))`.

## Main results

* `TauCeti.SymbolAlgebra.isSimpleRing`: the cyclic algebra is simple.
* `TauCeti.SymbolAlgebra.isCentral`: the cyclic algebra is central.
* `TauCeti.SymbolAlgebra.brauerClass_eq_mk`: the Brauer class is that of `(a, b)_ζ` as a
  central simple algebra.
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
  LinearMap.mulLeftRight K
    (((unitX ha)⁻¹ : (SymbolAlgebra n ζ a b)ˣ).val, (unitX ha : (SymbolAlgebra n ζ a b)ˣ).val)

/-- Conjugation `z ↦ y * z * y⁻¹` by the unit `y`. -/
private noncomputable def conjY (hb : b ≠ 0) : SymbolAlgebra n ζ a b →ₗ[K] SymbolAlgebra n ζ a b :=
  LinearMap.mulLeftRight K
    ((unitY hb : (SymbolAlgebra n ζ a b)ˣ).val, ((unitY hb)⁻¹ : (SymbolAlgebra n ζ a b)ˣ).val)

private theorem conjX_basis (hζ : ζ ^ n = 1) (ha : a ≠ 0) (p : Fin n × Fin n) :
    conjX (b := b) ha (basis hζ p) = ζ ^ (p.2 : ℕ) • basis hζ p := by
  rw [conjX, LinearMap.mulLeftRight_apply, mul_assoc, basis_apply,
    coe_unitX, x_pow_mul_y_pow_mul_x, mul_smul_comm, ← coe_unitX ha, Units.inv_mul_cancel_left]

private theorem conjY_basis (hζ : ζ ^ n = 1) (hb : b ≠ 0) (p : Fin n × Fin n) :
    conjY (a := a) hb (basis hζ p) = ζ ^ (p.1 : ℕ) • basis hζ p := by
  rw [conjY, LinearMap.mulLeftRight_apply, basis_apply,
    coe_unitY, y_mul_x_pow_mul_y_pow, smul_mul_assoc, ← coe_unitY hb, Units.mul_inv_cancel_right]

private theorem conjX_mem (ha : a ≠ 0) (I : TwoSidedIdeal (SymbolAlgebra n ζ a b)) {z}
    (hz : z ∈ I) : conjX ha z ∈ I := by
  rw [conjX, LinearMap.mulLeftRight_apply]
  exact I.mul_mem_right _ _ (I.mul_mem_left _ _ hz)

private theorem conjY_mem (hb : b ≠ 0) (I : TwoSidedIdeal (SymbolAlgebra n ζ a b)) {z}
    (hz : z ∈ I) : conjY hb z ∈ I := by
  rw [conjY, LinearMap.mulLeftRight_apply]
  exact I.mul_mem_right _ _ (I.mul_mem_left _ _ hz)

/-- The two conjugations act diagonally on the monomial basis: conjugation by `x` scales
`x ^ i * y ^ j` by `ζ ^ j` and conjugation by `y` scales it by `ζ ^ i`. -/
private theorem conj_basis (hζ : ζ ^ n = 1) (ha : a ≠ 0) (hb : b ≠ 0) (p : Fin n × Fin n)
    (j : Fin 2) :
    ![conjX (b := b) ha, conjY (a := a) hb] j (basis hζ p) =
      ![ζ ^ (p.2 : ℕ), ζ ^ (p.1 : ℕ)] j • basis hζ p := by
  fin_cases j
  exacts [conjX_basis hζ ha p, conjY_basis hζ hb p]

omit [NeZero n] in
/-- The joint eigenvalues of the two conjugations separate the monomials. -/
private theorem injective_conjWeight (hζ : IsPrimitiveRoot ζ n) :
    Function.Injective fun p : Fin n × Fin n => (![ζ ^ (p.2 : ℕ), ζ ^ (p.1 : ℕ)] : Fin 2 → K) := by
  intro p q h
  have h0 : ζ ^ (p.2 : ℕ) = ζ ^ (q.2 : ℕ) := by simpa using congr_fun h 0
  have h1 : ζ ^ (p.1 : ℕ) = ζ ^ (q.1 : ℕ) := by simpa using congr_fun h 1
  exact Prod.ext (Fin.ext (hζ.pow_inj p.1.isLt q.1.isLt h1))
    (Fin.ext (hζ.pow_inj p.2.isLt q.2.isLt h0))

/-- **The cyclic algebra `(a, b)_ζ` is a simple ring** when `ζ` is a primitive `n`-th root of unity
and `a, b ≠ 0`. -/
theorem isSimpleRing (hζ : IsPrimitiveRoot ζ n) (ha : a ≠ 0) (hb : b ≠ 0) :
    IsSimpleRing (SymbolAlgebra n ζ a b) :=
  have := nontrivial (a := a) (b := b) hζ.pow_eq_one
  .of_eq_bot_or_eq_top fun I => or_iff_not_imp_left.2 fun hI => by
    obtain ⟨z, hzI, hz⟩ := IsConcreteLE.exists_of_lt (bot_lt_iff_ne_bot.2 hI)
    rw [TwoSidedIdeal.mem_bot] at hz
    set B := basis (a := a) (b := b) hζ.pow_eq_one
    obtain ⟨p, hpz⟩ := Finsupp.ne_iff.1 (B.repr.map_ne_zero_iff.2 hz)
    -- `I` is invariant under both conjugations, which jointly separate the monomials, so it
    -- contains every monomial in the support of `z`
    have hp : B p ∈ I := by
      have := B.self_mem_of_repr_ne_zero_of_forall (W := I.asIdeal.restrictScalars K)
        (conj_basis _ ha hb) (injective_conjWeight hζ)
        (fun j v hv => by
          rw [Submodule.restrictScalars_mem, TwoSidedIdeal.mem_asIdeal] at hv ⊢
          fin_cases j
          exacts [conjX_mem ha I hv, conjY_mem hb I hv])
        (by rwa [Submodule.restrictScalars_mem, TwoSidedIdeal.mem_asIdeal]) hpz
      rwa [Submodule.restrictScalars_mem, TwoSidedIdeal.mem_asIdeal] at this
    obtain ⟨u, hu⟩ : IsUnit (B p) := by
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
    have hx : conjX (b := b) ha z = z := by
      rw [conjX, LinearMap.mulLeftRight_apply, mul_assoc, ← hz, Units.inv_mul_cancel_left]
    have hy : conjY (a := a) hb z = z := by
      rw [conjY, LinearMap.mulLeftRight_apply, hz, Units.mul_inv_cancel_right]
    -- `z` is fixed by both conjugations, so its coordinates off the monomial `1`, whose joint
    -- eigenvalue is not `(1, 1)`, vanish
    have h0 : ∀ r : Fin n × Fin n, r ≠ 0 → B.repr z r = 0 := fun r hr =>
      B.repr_eq_zero_of_weight_ne (conj_basis _ ha hb) (c := fun _ => 1)
        (fun j => by fin_cases j <;> simp [hx, hy])
        fun h => hr (injective_conjWeight hζ (h.trans (by funext j; fin_cases j <;> simp)))
    have hz1 : z = B.repr z 0 • B 0 := B.eq_smul_of_repr_support_subset_singleton fun r hr =>
      Finset.mem_singleton.2 (by_contra fun h => Finsupp.mem_support_iff.1 hr (h0 r h))
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

/-- The Brauer class of the cyclic algebra `(a, b)_ζ` is the class of `(a, b)_ζ` as a central
simple algebra, for any instances of centrality, simplicity and finite dimensionality (such as
`isCentral`, `isSimpleRing` and `finite`). -/
theorem brauerClass_eq_mk (hζ : IsPrimitiveRoot ζ n) (ha : a ≠ 0) (hb : b ≠ 0)
    [Algebra.IsCentral K (SymbolAlgebra n ζ a b)] [IsSimpleRing (SymbolAlgebra n ζ a b)]
    [FiniteDimensional K (SymbolAlgebra n ζ a b)] :
    brauerClass hζ ha hb = BrauerGroup.mk (CSA.of K (SymbolAlgebra n ζ a b)) := by
  -- The instance arguments are propositions, so they agree with those chosen in `brauerClass`.
  rw [brauerClass]

/-- `K[X]/(X ^ n - a)` is nontrivial, being free of rank `n ≠ 0` (`standardTameCover_free`). -/
private instance : Nontrivial (AdjoinRoot (X ^ n - C a)) :=
  Module.nontrivial_of_finrank_pos (R := K) <| by
    rw [(standardTameCover_free K a n NeZero.one_le).2]
    exact NeZero.pos n

/-- `(a, 1)_ζ` is the endomorphism algebra of the `n`-dimensional space `K[X]/(X ^ n - a)`, through
its representation `TauCeti.SymbolAlgebra.toEndAdjoinRoot`. -/
noncomputable def algEquivEndAdjoinRoot (hζ : IsPrimitiveRoot ζ n) (ha : a ≠ 0) :
    SymbolAlgebra n ζ a 1 ≃ₐ[K] Module.End K (AdjoinRoot (X ^ n - C a)) :=
  have := isSimpleRing hζ ha one_ne_zero
  have := finite (a := a) (b := 1) hζ.pow_eq_one
  have := (standardTameCover_free K a n NeZero.one_le).1
  AlgEquiv.ofBijective (toEndAdjoinRoot a hζ.pow_eq_one) <| by
    have hinj := (toEndAdjoinRoot a hζ.pow_eq_one).toRingHom.injective
    have hfin := (standardTameCover_free K a n NeZero.one_le).2
    refine ⟨hinj, ?_⟩
    exact (LinearMap.injective_iff_surjective_of_finrank_eq_finrank (f :=
      (toEndAdjoinRoot a hζ.pow_eq_one).toLinearMap)
      (by rw [finrank_eq hζ.pow_eq_one, Module.finrank_linearMap, hfin, sq])).1 hinj

@[simp]
theorem algEquivEndAdjoinRoot_apply (hζ : IsPrimitiveRoot ζ n) (ha : a ≠ 0)
    (z : SymbolAlgebra n ζ a 1) :
    algEquivEndAdjoinRoot hζ ha z = toEndAdjoinRoot a hζ.pow_eq_one z := by
  unfold algEquivEndAdjoinRoot
  exact AlgEquiv.ofBijective_apply _ _ _

/-- **The cyclic algebra `(a, 1)_ζ` is split**: its Brauer class is trivial. -/
theorem brauerClass_one_right (hζ : IsPrimitiveRoot ζ n) (ha : a ≠ 0) :
    brauerClass hζ ha one_ne_zero = 1 := by
  have := isCentral hζ ha one_ne_zero
  have := isSimpleRing hζ ha one_ne_zero
  have := finite (a := a) (b := 1) hζ.pow_eq_one
  rw [brauerClass_eq_mk, BrauerGroup.mk_eq_one_iff]
  exact (IsBrauerEquivalent.of_algEquiv K (algEquivEndAdjoinRoot hζ ha)).trans
    (isBrauerTrivial_end K _)

end SymbolAlgebra

end TauCeti
