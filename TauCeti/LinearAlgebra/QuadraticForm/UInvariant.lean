/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.ENat.Lattice
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.FieldTheory.IsSepClosed
public import TauCeti.LinearAlgebra.QuadraticForm.Representation
public import TauCeti.LinearAlgebra.QuadraticForm.Witt.Decomposition
import Mathlib.Data.ENat.Basic
import TauCeti.LinearAlgebra.QuadraticForm.Basic
import TauCeti.LinearAlgebra.QuadraticForm.Complex
import TauCeti.LinearAlgebra.QuadraticForm.Diagonal.SquareClass
import TauCeti.LinearAlgebra.QuadraticForm.FiniteField
import TauCeti.LinearAlgebra.QuadraticForm.PosDef

/-!
# The `u`-invariant of a field

The *`u`-invariant* `u(K) ∈ ℕ∞` of a field `K` is the supremum of the dimensions of anisotropic
quadratic spaces over `K` (Kaplansky 1953; Lam, *Introduction to Quadratic Forms over Fields*,
Chapter XI, §6; Elman–Karpenko–Merkurjev, §36). Because every finite-dimensional `K`-vector space of
dimension `n` is `K`-linearly isomorphic to `Fin n → K`, taking the supremum over coordinate forms
`Q : QuadraticForm K (Fin n → K)` avoids any universe parameter while bounding the dimension of
every anisotropic quadratic space over `K` in any universe
(`QuadraticMap.Anisotropic.finrank_le_uInvariant`).

Defining `uInvariant K` directly via `QuadraticForm K (Fin n → K)` rather than diagonal
presentations makes the invariant valid in **every characteristic**, including characteristic two:
for instance, over `𝔽₂` every binary diagonal form `a x² + b y²` is isotropic while the binary norm
form `x² + x y + y²` is anisotropic, so `u(𝔽₂) = 2`. When `2` is invertible in `K`, every
anisotropic form is regular and diagonalizable, so `uInvariant K` agrees with the supremum of the
ranks of anisotropic classes in `RegularFormClass K`
(`TauCeti.uInvariant_eq_iSup_regularFormClass`).

## Main definitions and results

* `TauCeti.uInvariant`: the `u`-invariant `u(K) : ℕ∞` of a field `K`.
* `QuadraticMap.Anisotropic.finrank_le_uInvariant` and
  `QuadraticForm.not_anisotropic_of_uInvariant_lt_finrank`: every anisotropic form over `K` has
  `finrank ≤ u(K)`, and every form of `finrank > u(K)` is isotropic.
* `TauCeti.uInvariant_le_natCast_iff`: `u(K) ≤ n` if and only if every quadratic form on
  `Fin (n + 1) → K` is isotropic.
* `TauCeti.one_le_uInvariant` and `TauCeti.uInvariant_ne_zero`: `1 ≤ u(K)` for every field `K`.
* `RingEquiv.uInvariant_eq`: isomorphic fields have equal `u`-invariants.
* `QuadraticForm.represents_of_radical_eq_bot_of_uInvariant_le_finrank` and
  `QuadraticForm.represents_of_uInvariant_le_finrank`: every quadratic form with trivial radical
  (or nondegenerate) of dimension at least `u(K)` represents every scalar in `K` (Lam XI.6.4 (1)).
* `TauCeti.RegularFormClass.rank_anisotropicPart_le_uInvariant` and
  `TauCeti.uInvariant_eq_iSup_regularFormClass`: compatibility with Witt decomposition and
  `RegularFormClass` when `2` is invertible.
* `TauCeti.isSquare_of_uInvariant_eq_one` and `TauCeti.uInvariant_eq_one_iff`: `u(K) = 1` implies
  every element of `K` is a square (in any characteristic), and the converse holds when `2` is
  invertible.
* `TauCeti.uInvariant_of_isAlgClosed`, `TauCeti.uInvariant_of_isSepClosed`,
  `TauCeti.uInvariant_of_finite`, and `TauCeti.uInvariant_eq_top_of_isStrictOrderedRing`:
  `u(K) = 1` for algebraically closed fields (and separably closed fields of characteristic `≠ 2`),
  `u(K) = 2` for finite fields (in all characteristics), and `u(K) = ⊤` for strictly ordered fields.

The nonarchimedean local-field evaluation `u(K) = 4` (O'Meara 63:19) is proved in
`TauCeti.NumberTheory.LocalField.QuadraticForm.Isotropy` (`TauCeti.uInvariant_eq_four`), and the
real specialization `u(ℝ) = ⊤` is recorded in `TauCeti.LinearAlgebra.QuadraticForm.Real`
(`TauCeti.uInvariant_real`).

## References

* I. Kaplansky, *Quadratic forms*, J. Math. Soc. Japan **5** (1953), 200–207.
* T. Y. Lam, *Introduction to Quadratic Forms over Fields*, Chapter XI, §6, Examples 6.2 and
  Proposition 6.4.
* R. Elman, N. Karpenko, A. Merkurjev, *The Algebraic and Geometric Theory of Quadratic Forms*,
  §36.
-/

public section

open QuadraticMap QuadraticForm

namespace TauCeti

universe u v

/-- The *`u`-invariant* `u(K) ∈ ℕ∞` of a field `K`: the supremum of `n : ℕ` for which there exists
an anisotropic quadratic form on `Fin n → K`. Valid in arbitrary characteristic. -/
noncomputable def uInvariant (K : Type u) [Field K] : ℕ∞ :=
  ⨆ (n : ℕ) (_ : ∃ Q : QuadraticForm K (Fin n → K), Q.Anisotropic), (n : ℕ∞)

/-- Explicit `iSup` formula for `TauCeti.uInvariant`. -/
theorem uInvariant_def (K : Type u) [Field K] :
    uInvariant K = ⨆ (n : ℕ) (_ : ∃ Q : QuadraticForm K (Fin n → K), Q.Anisotropic), (n : ℕ∞) :=
  (rfl)

section General

variable {K : Type u} [Field K]

/-- An anisotropic quadratic form on `Fin n → K` witnesses `(n : ℕ∞) ≤ uInvariant K`. -/
theorem le_uInvariant_of_anisotropic_fin {n : ℕ} {Q : QuadraticForm K (Fin n → K)}
    (hQ : Q.Anisotropic) : (n : ℕ∞) ≤ uInvariant K :=
  le_iSup₂_of_le n ⟨Q, hQ⟩ le_rfl

/-- Every anisotropic quadratic form on a `K`-vector space `V` (in any universe) has
`Module.finrank K V ≤ uInvariant K`. If `V` is infinite-dimensional, `Module.finrank K V = 0` so the
inequality holds trivially. -/
theorem _root_.QuadraticMap.Anisotropic.finrank_le_uInvariant
    {V : Type v} [AddCommGroup V] [Module K V] {Q : QuadraticForm K V} (hQ : Q.Anisotropic) :
    (Module.finrank K V : ℕ∞) ≤ uInvariant K := by
  by_cases hV : Module.Finite K V
  · let e := (Module.finBasis K V).equivFun.symm
    exact le_uInvariant_of_anisotropic_fin (hQ.comp e.toLinearMap e.injective)
  · rw [Module.finrank_of_not_finite hV, Nat.cast_zero]
    exact zero_le

/-- Any quadratic form whose underlying space has finite dimension strictly exceeding `uInvariant K`
is isotropic. -/
theorem _root_.QuadraticForm.not_anisotropic_of_uInvariant_lt_finrank
    {V : Type v} [AddCommGroup V] [Module K V] (Q : QuadraticForm K V)
    (h : uInvariant K < Module.finrank K V) : ¬ Q.Anisotropic :=
  fun hQ ↦ not_le_of_gt h hQ.finrank_le_uInvariant

/-- Upper-bound characterization of `uInvariant K`. -/
theorem uInvariant_le_iff {c : ℕ∞} :
    uInvariant K ≤ c ↔ ∀ (n : ℕ) (Q : QuadraticForm K (Fin n → K)), Q.Anisotropic → (n : ℕ∞) ≤ c :=
  by simp [uInvariant_def]

/-- Finite upper-bound criterion for `uInvariant K`: `u(K) ≤ n` if and only if every quadratic form
on `Fin (n + 1) → K` is isotropic, since any higher-dimensional anisotropic space contains an
`(n + 1)`-dimensional anisotropic subspace. -/
theorem uInvariant_le_natCast_iff {n : ℕ} :
    uInvariant K ≤ n ↔ ∀ Q : QuadraticForm K (Fin (n + 1) → K), ¬ Q.Anisotropic := by
  constructor
  · intro h Q hQ
    have hle : ((n + 1 : ℕ) : ℕ∞) ≤ n := (le_uInvariant_of_anisotropic_fin hQ).trans h
    norm_cast at hle
    omega
  · intro hiso
    rw [uInvariant_le_iff]
    intro m Q hQ
    by_contra! hlt
    norm_cast at hlt
    have hmn : n + 1 ≤ m := by omega
    let f : (Fin (n + 1) → K) →ₗ[K] (Fin m → K) :=
      Fintype.linearCombination K (Pi.basisFun K (Fin m) ∘ Fin.castLE hmn)
    have hf : Function.Injective f :=
      ((Pi.basisFun K (Fin m)).linearIndependent.comp _
        (Fin.castLE_injective hmn)).fintypeLinearCombination_injective
    exact hiso (Q.comp f) (hQ.comp f hf)

/-- To prove `uInvariant K = n` for a natural number `n`, it suffices to exhibit an `n`-dimensional
anisotropic form and show that every `(n + 1)`-dimensional coordinate form is isotropic. -/
theorem uInvariant_eq_natCast_of_anisotropic_of_forall
    {n : ℕ} {V : Type v} [AddCommGroup V] [Module K V] {Q : QuadraticForm K V}
    (hQ : Q.Anisotropic) (hdim : Module.finrank K V = n)
    (hiso : ∀ R : QuadraticForm K (Fin (n + 1) → K), ¬ R.Anisotropic) :
    uInvariant K = n :=
  le_antisymm (uInvariant_le_natCast_iff.mpr hiso) (hdim ▸ hQ.finrank_le_uInvariant)

/-- Every field has `1 ≤ u(K)`, witnessed by the one-dimensional form `x ↦ x²`. -/
theorem one_le_uInvariant : 1 ≤ uInvariant K := by
  have hQ : (weightedSumSquares K (1 : Fin 1 → K)).Anisotropic := by
    intro v hv
    ext i
    fin_cases i
    simpa [weightedSumSquares_apply] using hv
  simpa using le_uInvariant_of_anisotropic_fin hQ

/-- The `u`-invariant of a field is never zero. -/
theorem uInvariant_ne_zero : uInvariant K ≠ 0 :=
  ne_of_gt (zero_lt_one.trans_le one_le_uInvariant)

private theorem uInvariant_le_of_ringEquiv {L : Type v} [Field L] (e : K ≃+* L) :
    uInvariant K ≤ uInvariant L := by
  rw [uInvariant_le_iff]
  intro n Q hQ
  exact le_uInvariant_of_anisotropic_fin ((e.anisotropic_congrPiQuadraticForm_iff Q).mpr hQ)

/-- Isomorphic fields have the same `u`-invariant. -/
theorem _root_.RingEquiv.uInvariant_eq {L : Type v} [Field L] (e : K ≃+* L) :
    uInvariant K = uInvariant L :=
  le_antisymm (uInvariant_le_of_ringEquiv e) (uInvariant_le_of_ringEquiv e.symm)

/-- **Universal forms in dimension at least `u(K)`** (Lam, Chapter XI, Proposition 6.4 (1),
characteristic-free form): any quadratic form `Q` with trivial quadratic radical whose underlying
space has finite dimension `Module.finrank K V ≥ u(K)` represents every scalar in `K`. -/
theorem _root_.QuadraticForm.represents_of_radical_eq_bot_of_uInvariant_le_finrank
    {V : Type v} [AddCommGroup V] [Module K V] (Q : QuadraticForm K V) (hQ : Q.radical = ⊥)
    (h : uInvariant K ≤ Module.finrank K V) (c : K) :
    Q.Represents c := by
  by_cases hc : c = 0
  · subst hc
    exact QuadraticMap.represents_zero Q
  have h1 : (1 : ℕ∞) ≤ Module.finrank K V := one_le_uInvariant.trans h
  have hpos : 0 < Module.finrank K V := by
    have : 1 ≤ Module.finrank K V := by exact_mod_cast h1
    omega
  have : FiniteDimensional K V := Module.finite_of_finrank_pos hpos
  let u : Kˣ := Units.mk0 c hc
  suffices u ∈ Q.unitValueSet by simpa [u, mem_unitValueSet] using this
  rw [mem_unitValueSet_iff_not_anisotropic_prod_of_radical_eq_bot Q hQ u]
  refine not_anisotropic_of_uInvariant_lt_finrank _ (h.trans_lt ?_)
  rw [Module.finrank_prod, Module.finrank_self]
  norm_cast
  omega

/-- The represented-unit value set of any quadratic form with trivial radical in dimension at least
`u(K)` is all of `Kˣ`. -/
@[simp]
theorem _root_.QuadraticForm.unitValueSet_eq_top_of_radical_eq_bot_of_uInvariant_le_finrank
    {V : Type v} [AddCommGroup V] [Module K V] (Q : QuadraticForm K V) (hQ : Q.radical = ⊥)
    (h : uInvariant K ≤ Module.finrank K V) :
    Q.unitValueSet = ⊤ :=
  eq_top_iff.mpr fun u _ ↦
    mem_unitValueSet.mpr (Q.represents_of_radical_eq_bot_of_uInvariant_le_finrank hQ h u)

/-- Any nondegenerate quadratic form of finite dimension at least `u(K)` represents every scalar in
`K` (Lam, Chapter XI, Proposition 6.4 (1)). -/
theorem _root_.QuadraticForm.represents_of_uInvariant_le_finrank
    {V : Type v} [AddCommGroup V] [Module K V] (Q : QuadraticForm K V) (hQ : Q.Nondegenerate)
    (h : uInvariant K ≤ Module.finrank K V) (c : K) :
    Q.Represents c :=
  Q.represents_of_radical_eq_bot_of_uInvariant_le_finrank hQ.radical_eq_bot h c

/-- The represented-unit value set of any nondegenerate quadratic form of finite dimension at least
`u(K)` is all of `Kˣ`. -/
@[simp]
theorem _root_.QuadraticForm.unitValueSet_eq_top_of_uInvariant_le_finrank
    {V : Type v} [AddCommGroup V] [Module K V] (Q : QuadraticForm K V) (hQ : Q.Nondegenerate)
    (h : uInvariant K ≤ Module.finrank K V) :
    Q.unitValueSet = ⊤ :=
  Q.unitValueSet_eq_top_of_radical_eq_bot_of_uInvariant_le_finrank hQ.radical_eq_bot h

/-- `u(K) = ⊤` if and only if `K` admits an anisotropic quadratic form in every dimension
`n : ℕ`. -/
theorem uInvariant_eq_top_iff :
    uInvariant K = ⊤ ↔ ∀ n : ℕ, ∃ Q : QuadraticForm K (Fin n → K), Q.Anisotropic := by
  constructor
  · intro htop n
    cases n with
    | zero => exact ⟨0, fun x _ ↦ Subsingleton.elim x 0⟩
    | succ m =>
      by_contra! hall
      have hle : uInvariant K ≤ m := uInvariant_le_natCast_iff.mpr hall
      rw [htop] at hle
      exact ENat.natCast_ne_top m (top_unique hle)
  · intro hall
    by_contra hne
    lift uInvariant K to ℕ using hne with m hm
    obtain ⟨Q, hQ⟩ := hall (m + 1)
    have hle : ((m + 1 : ℕ) : ℕ∞) ≤ m := hm ▸ le_uInvariant_of_anisotropic_fin hQ
    norm_cast at hle
    omega

/-- Every anisotropic regular-form class over `K` has rank at most `uInvariant K`. -/
theorem RegularFormClass.Anisotropic.rank_le_uInvariant {c : RegularFormClass K}
    (hc : c.Anisotropic) : (c.rank : ℕ∞) ≤ uInvariant K := by
  induction c using Quotient.inductionOn with
  | h p =>
    rw [RegularFormClass.rank_mk]
    exact le_uInvariant_of_anisotropic_fin ((RegularFormClass.anisotropic_mk p).mp hc)

/-- If `u(K) = 1` (in any characteristic), then every element of `K` is a square: the
one-dimensional form `x ↦ x²` is anisotropic and hence universal by
`QuadraticForm.represents_of_radical_eq_bot_of_uInvariant_le_finrank`. -/
theorem isSquare_of_uInvariant_eq_one (hu : uInvariant K = 1) (a : K) : IsSquare a := by
  have hQ : (weightedSumSquares K (1 : Fin 1 → K)).Anisotropic := by
    intro v hv
    ext i
    fin_cases i
    simpa [weightedSumSquares_apply] using hv
  have hrep := QuadraticForm.represents_of_radical_eq_bot_of_uInvariant_le_finrank
    (weightedSumSquares K (1 : Fin 1 → K)) hQ.radical_eq_bot (by simp [hu]) a
  obtain ⟨v, hv⟩ := (represents_iff _ _).mp hrep
  have hv0 : v 0 * v 0 = a := by simpa [weightedSumSquares_apply] using hv
  exact ⟨v 0, hv0.symm⟩

end General

section InvertibleTwo

variable {K : Type u} [Field K] [Invertible (2 : K)]

/-- In the Witt decomposition of any regular-form class `c`, the rank of its anisotropic kernel
`c.anisotropicPart` is bounded by `uInvariant K`. -/
theorem RegularFormClass.rank_anisotropicPart_le_uInvariant (c : RegularFormClass K) :
    (c.anisotropicPart.rank : ℕ∞) ≤ uInvariant K :=
  c.anisotropic_anisotropicPart.rank_le_uInvariant

/-- When `2` is invertible in `K`, every anisotropic form is regular and diagonalizable, so
`uInvariant K` equals the supremum of the ranks of anisotropic classes in `RegularFormClass K`. -/
theorem uInvariant_eq_iSup_regularFormClass (K : Type u) [Field K] [Invertible (2 : K)] :
    uInvariant K = ⨆ (c : RegularFormClass K) (_ : c.Anisotropic), (c.rank : ℕ∞) := by
  refine le_antisymm ?_ (iSup₂_le fun c hc ↦ hc.rank_le_uInvariant)
  rw [uInvariant_le_iff]
  intro n Q hQ
  have hnd : Q.Nondegenerate := hQ.nondegenerate
  have hani : (formClass Q hnd).Anisotropic := (Q.anisotropic_formClass hnd).mpr hQ
  have hrk : (formClass Q hnd).rank = n := by simp [rank_formClass]
  exact hrk ▸ le_iSup₂_of_le (formClass Q hnd) hani le_rfl

/-- Over a field in which `2` is invertible, `u(K) = 1` if and only if every element of `K` is a
square (Lam, Chapter XI, Example 6.2 (1)). The characteristic-two exclusion in the converse is
sharp: every element of `𝔽₂` is a square, yet `u(𝔽₂) = 2` via `x² + x y + y²`. -/
theorem uInvariant_eq_one_iff : uInvariant K = 1 ↔ ∀ a : K, IsSquare a := by
  refine ⟨isSquare_of_uInvariant_eq_one, fun hsq ↦ ?_⟩
  refine le_antisymm ((uInvariant_le_natCast_iff (n := 1)).mpr fun Q hQ ↦ ?_) one_le_uInvariant
  obtain ⟨w, he⟩ := Q.equivalent_weightedSumSquares_units_of_nondegenerate'
    (QuadraticMap.separatingLeft_of_anisotropic Q hQ)
  have h1 : (weightedSumSquares K w).Equivalent (weightedSumSquares K (1 : Fin _ → Kˣ)) :=
    equivalent_weightedSumSquares_of_isSquare_div fun i ↦ by
      simpa [Units.isSquare_coe_iff] using hsq (w i : K)
  have hani : (weightedSumSquares K (1 : Fin (Module.finrank K (Fin 2 → K)) → Kˣ)).Anisotropic :=
    (he.trans h1).anisotropic_iff.mp hQ
  rw [Module.finrank_fin_fun] at hani
  have h11 : weightedSumSquares K (1 : Fin 2 → Kˣ) = weightedSumSquares K ![(1 : K), 1] := by
    rw [weightedSumSquares_units]
    congr 1
    ext i
    fin_cases i <;> rfl
  rw [h11, anisotropic_binary_iff] at hani
  exact hani (hsq _)

/-- Every separably closed field in which `2` is invertible has `u(K) = 1`. -/
@[simp]
theorem uInvariant_of_isSepClosed (K : Type u) [Field K] [IsSepClosed K] [Invertible (2 : K)] :
    uInvariant K = 1 := by
  have : NeZero (2 : K) := ⟨Invertible.ne_zero (2 : K)⟩
  exact uInvariant_eq_one_iff.mpr fun a ↦ IsSepClosed.isSquare a

end InvertibleTwo

section FieldClasses

/-- Every algebraically closed field (of arbitrary characteristic) has `u(K) = 1`
(Lam, Chapter XI, Example 6.2 (1)). -/
@[simp]
theorem uInvariant_of_isAlgClosed (K : Type u) [Field K] [IsAlgClosed K] :
    uInvariant K = 1 :=
  le_antisymm
    ((uInvariant_le_natCast_iff (n := 1)).mpr fun Q ↦
      QuadraticForm.not_anisotropic_of_isAlgClosed Q (by simp))
    one_le_uInvariant

/-- Every finite field (of arbitrary characteristic) has `u(K) = 2`
(Lam, Chapter XI, Example 6.2 (2)). -/
@[simp]
theorem uInvariant_of_finite (K : Type u) [Field K] [Finite K] :
    uInvariant K = 2 := by
  obtain ⟨Q, hQ⟩ := QuadraticForm.exists_anisotropic_fin_two_of_finite K
  exact uInvariant_eq_natCast_of_anisotropic_of_forall hQ (by simp) fun R ↦
    QuadraticForm.not_anisotropic_of_finite R (by simp)

/-- Every strictly ordered field (in particular `ℚ` and `ℝ`) has `u(K) = ⊤`, witnessed in every
dimension `n` by the positive definite sum of `n` squares `∑ i, xᵢ²`
(Lam, Chapter XI, Example 6.2). -/
theorem uInvariant_eq_top_of_isStrictOrderedRing (K : Type u) [Field K] [LinearOrder K]
    [IsStrictOrderedRing K] : uInvariant K = ⊤ :=
  uInvariant_eq_top_iff.mpr fun n ↦
    ⟨weightedSumSquares K (1 : Fin n → K),
      ((posDef_weightedSumSquares_iff _).mpr fun _ ↦ zero_lt_one).anisotropic⟩

end FieldClasses

end TauCeti
