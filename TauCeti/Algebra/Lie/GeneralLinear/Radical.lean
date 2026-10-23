/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.GeneralLinear.Basic
import TauCeti.Algebra.Lie.GeneralLinear.DiagonalCartan

/-!
# The radicals of `gl n K` and `sl n K`

`TauCeti/Algebra/Lie/GeneralLinear/Basic.lean` identifies the centre of `gl n R` (the scalar
matrices) and its derived ideal (`sl n R`), and shows that the two are complementary submodules as
soon as the size of the matrices is invertible. This file proves the reductivity criterion itself,
Mathlib's `LieAlgebra.HasCentralRadical`: over a field in which `2 ≠ 0`, the solvable radical of
`gl n K` **is** its centre. This makes the reductive vocabulary applicable to `gl n`, whose Killing
form is degenerate.

The same structure shows that `sl n K` has trivial radical when `2` and the nonempty matrix size
are nonzero. In characteristic zero this is registered as an instance, so Cartan's criterion makes
the Killing-form API available by typeclass synthesis.

The proof is the structure of the Lie ideals of `gl n K`. The centre is always an abelian, hence
solvable, ideal, so it is contained in the radical. For the other inclusion, every solvable ideal
must consist of scalar matrices, and that is a consequence of the sharper statement
`TauCeti.slIdeal_le_of_notMem_center`: **a Lie ideal containing a single non-central matrix already
contains all of `sl n K`**. Since `sl n K` is perfect (`TauCeti.lie_slIdeal_slIdeal`) and nonzero as
soon as there are two indices, it is not solvable, so no solvable ideal reaches outside the centre.

The ideal-generation argument runs through matrix units, and only two brackets are needed.
Bracketing against a diagonal matrix rescales a matrix unit,
`⁅diagonal d, Eₚq c⁆ = Eₚq ((dₚ - d_q) c)` (`TauCeti.lie_single_of_mem_diagonalCartan`, from the
diagonal Cartan subalgebra file), which extracts `Eₚq` from any diagonal element separating the
indices `p` and `q`. Bracketing twice against `Eⱼᵢ` annihilates everything except one entry,
`(ad Eⱼᵢ)² x = Eⱼᵢ (-2 xᵢⱼ)` (`TauCeti.lie_single_lie_single_of_ne`), which extracts `Eⱼᵢ` from any
element with a nonzero `(i, j)` entry. A non-central matrix is either non-diagonal, and then the
second bracket applies, or diagonal with two distinct entries, and then the first does. Once one
off-diagonal matrix unit lies in the ideal, so does the difference of diagonal units
`E_bb - Eₐₐ = ⁅E_bₐ, Eₐb⁆`, which separates `b` from every other index; that produces every unit in
the row and the column of `b`, then every difference of diagonal units, and finally, by the first
bracket again, all the remaining units.

## Main results

* `TauCeti.slIdeal_le_of_notMem_center`: **a Lie ideal of `gl n K` containing a non-central matrix
  contains `sl n K`**; equivalently `TauCeti.slIdeal_le_or_le_center`, every Lie ideal of `gl n K`
  either contains `sl n K` or consists of scalar matrices.
* `TauCeti.lie_slIdeal_slIdeal`: **`sl n R` is perfect**, `⁅sl n R, sl n R⁆ = sl n R`, whenever `2`
  is invertible in `R`, whence `TauCeti.not_isSolvable_slIdeal`: it is not solvable when `R` is
  nontrivial and there are at least two indices.
* `TauCeti.radical_matrix_eq_center` and `TauCeti.hasCentralRadical_matrix`: **`gl n K` is
  reductive**, its radical being its centre.
* `TauCeti.hasTrivialRadical_sl`: **`sl n K` has trivial radical** when `2` and the nonempty
  matrix size are nonzero; the characteristic-zero case is a named instance.

## Implementation notes

The hypothesis `(2 : K) ≠ 0` is genuinely needed, and not an artefact of the bracket computations:
in `gl 2 (ZMod 2)` the span of `E₁₂` and the identity matrix is a Lie ideal containing a non-central
element but not `E₂₁`, and there `sl 2 (ZMod 2)` is nilpotent, so it is a solvable ideal strictly
larger than the centre. No invertibility of the size of the matrices is needed, however: the
statement is proved uniformly in the index type, the case of at most one index being the abelian
one, where the radical and the centre are both everything.

Only the results about ideals are stated over a field, because the generation argument divides by an
arbitrary nonzero matrix entry. The two bracket identities in `Basic.lean` need only a ring, and
perfectness of `sl n R` — which divides by `2` alone — is stated over a commutative ring in which
`2` is a unit, non-solvability adding only `Nontrivial R`; the radical computation specialises these
to a field.

The bracket against a diagonal matrix comes from `TauCeti.lie_single_of_mem_diagonalCartan`.
The matrix-unit bracket identities live alongside the other ring-level computations in
`TauCeti/Algebra/Lie/GeneralLinear/Basic.lean`.

## References

* J. Dixmier, *Enveloping Algebras*, AMS GSM 11 (1996), Section 1.6 (reductive Lie algebras).
* J. E. Humphreys, *Introduction to Lie Algebras and Representation Theory*, Springer GTM 9 (1972),
  Section 1.2 (the ideals of the classical linear Lie algebras).
-/

public section

namespace TauCeti

open Matrix LieAlgebra

attribute [local instance 100] LieRing.ofAssociativeRing

variable {R : Type*} {n : Type*} [DecidableEq n] [Fintype n]

/-! ### Matrix units inside a Lie ideal -/

section Ideals

variable {K : Type*} [Field K] (I : LieIdeal K (Matrix n n K))

/-- **A diagonal element of a Lie ideal separating two indices contributes their matrix unit.** -/
theorem single_mem_of_diagonal_mem {d : n → K} (hd : diagonal d ∈ I) {p q : n}
    (hpq : d p ≠ d q) (c : K) : single p q c ∈ I := by
  have hmem := lie_mem_left K (Matrix n n K) I _ (single p q ((d p - d q)⁻¹ * c)) hd
  rwa [lie_single_of_mem_diagonalCartan (diagonal_mem_diagonalCartan d), diagonal_apply_eq,
    diagonal_apply_eq, smul_single, smul_eq_mul, ← mul_assoc,
    mul_inv_cancel₀ (sub_ne_zero.mpr hpq), one_mul] at hmem

/-- **A Lie ideal containing a difference of diagonal matrix units contains the matrix unit between
any two indices that the difference separates**, the separation being read off from the diagonal
entries of `Eₐₐ - E_bb`.

This is the shape in which the generation argument below applies
`TauCeti.single_mem_of_diagonal_mem`, so it stays private. -/
private theorem single_mem_of_single_self_sub_single_self_mem {a b : n}
    (hmem : single a a (1 : K) - single b b (1 : K) ∈ I) {p q : n}
    (hpq : (single a a (1 : K) - single b b (1 : K)) p p
        ≠ (single a a (1 : K) - single b b (1 : K)) q q) (c : K) :
    single p q c ∈ I := by
  rw [← Matrix.diagonal_single a (1 : K), ← Matrix.diagonal_single b (1 : K),
    Matrix.diagonal_sub] at hmem hpq
  rw [diagonal_apply_eq, diagonal_apply_eq] at hpq
  exact single_mem_of_diagonal_mem I hmem hpq c

/-- **An element of a Lie ideal with a nonzero off-diagonal entry contributes the transposed matrix
unit there.** -/
theorem single_mem_of_apply_ne_zero (htwo : (2 : K) ≠ 0) {x : Matrix n n K} (hx : x ∈ I) {i j : n}
    (hij : i ≠ j) (hxij : x i j ≠ 0) (c : K) : single j i c ∈ I := by
  have hne : -(2 * x i j) ≠ 0 := neg_ne_zero.mpr (mul_ne_zero htwo hxij)
  have hmem : single j i (-(2 * x i j)) ∈ I := by
    have h := I.lie_mem (x := single j i (1 : K)) (I.lie_mem (x := single j i (1 : K)) hx)
    rwa [lie_single_lie_single_of_ne hij] at h
  have hscal : ((-(2 * x i j))⁻¹ * c) * (-(2 * x i j)) = c := by
    rw [mul_comm ((-(2 * x i j))⁻¹) c, mul_assoc, inv_mul_cancel₀ hne, mul_one]
  have h := SMulMemClass.smul_mem ((-(2 * x i j))⁻¹ * c) hmem
  rwa [smul_single, smul_eq_mul, hscal] at h

/-- **One off-diagonal matrix unit generates `sl n K`**: a Lie ideal of `gl n K` containing `Eₐb`
for some `a ≠ b` contains every trace-zero matrix. -/
theorem slIdeal_le_of_single_mem (htwo : (2 : K) ≠ 0) {a b : n} (hab : a ≠ b)
    (hmem : single a b (1 : K) ∈ I) : slIdeal K n ≤ I := by
  -- The difference of diagonal units `E_bb - Eₐₐ` lies in the ideal.
  have hsub : single b b (1 : K) - single a a (1 : K) ∈ I := by
    have h := I.lie_mem (x := single b a (1 : K)) hmem
    rwa [lie_single_single_eq_sub b a 1] at h
  -- Hence every matrix unit in the row and in the column of `b`.
  have hrow : ∀ p : n, p ≠ b → ∀ c : K, single b p c ∈ I ∧ single p b c ∈ I := by
    intro p hpb c
    have hsep : (single b b (1 : K) - single a a (1 : K)) b b
        ≠ (single b b (1 : K) - single a a (1 : K)) p p := by
      have hlhs : (single b b (1 : K) - single a a (1 : K)) b b = 1 := by
        simp [hab]
      rw [hlhs]
      rcases eq_or_ne p a with hpa | hpa
      · rw [hpa]
        have hrhs : (single b b (1 : K) - single a a (1 : K)) a a = -1 := by
          simp [hab.symm]
        rw [hrhs]
        simpa only [ne_eq, eq_neg_iff_add_eq_zero, one_add_one_eq_two] using htwo
      · have hrhs : (single b b (1 : K) - single a a (1 : K)) p p = 0 := by
          simp [hpb.symm, hpa.symm]
        rw [hrhs]
        exact one_ne_zero
    exact ⟨single_mem_of_single_self_sub_single_self_mem I hsub hsep c,
      single_mem_of_single_self_sub_single_self_mem I hsub hsep.symm c⟩
  -- Hence every difference of diagonal units.
  have hdiff : ∀ (p q : n) (c : K), single p p c - single q q c ∈ I := by
    have key : ∀ (p : n) (c : K), single p p c - single b b c ∈ I := by
      intro p c
      rcases eq_or_ne p b with hpb | hpb
      · rw [hpb]
        simp
      · have h := I.lie_mem (x := single p b c) (hrow p hpb 1).1
        rwa [lie_single_single_eq_sub p b c] at h
    intro p q c
    have h := sub_mem (key p c) (key q c)
    rwa [sub_sub_sub_cancel_right] at h
  -- Hence every off-diagonal unit, and so all of `sl n K`.
  have hoff : ∀ {p q : n}, p ≠ q → ∀ c : K, single p q c ∈ I := by
    intro p q hpq c
    rcases eq_or_ne q b with hqb | hqb
    · rw [hqb] at hpq ⊢
      exact (hrow p hpq c).2
    rcases eq_or_ne p b with hpb | hpb
    · rw [hpb] at hpq ⊢
      exact (hrow q (Ne.symm hpq) c).1
    have hsep : (single p p (1 : K) - single b b (1 : K)) p p
        ≠ (single p p (1 : K) - single b b (1 : K)) q q := by
      simp [hpb.symm, hqb.symm, hpq]
    exact single_mem_of_single_self_sub_single_self_mem I (hdiff p b 1) hsep c
  intro A hA
  rw [← LieSubmodule.mem_toSubmodule]
  exact mem_of_trace_eq_zero_of_single_mem (fun hpq c => hoff hpq c) (fun p q c => hdiff p q c)
    (mem_slIdeal_iff.mp hA)

/-- **A Lie ideal of `gl n K` containing a non-central matrix contains `sl n K`.** -/
theorem slIdeal_le_of_notMem_center (htwo : (2 : K) ≠ 0) {x : Matrix n n K} (hxI : x ∈ I)
    (hx : x ∉ LieAlgebra.center K (Matrix n n K)) : slIdeal K n ≤ I := by
  by_cases hoff : ∀ i j : n, i ≠ j → x i j = 0
  · -- `x` is diagonal, and not a scalar, so two of its diagonal entries differ.
    have hx' : x = diagonal fun k ↦ x k k :=
      (Matrix.IsDiag.diagonal_diag fun _ _ hij ↦ hoff _ _ hij).symm
    have hxd : (diagonal fun k => x k k) ∈ I := hx' ▸ hxI
    obtain ⟨p, q, hpq⟩ : ∃ p q : n, x p p ≠ x q q := by
      by_contra hcon
      have hall : ∀ p q : n, x p p = x q q := by simpa using hcon
      refine hx (mem_center_matrix_iff.mpr ?_)
      rcases isEmpty_or_nonempty n with hempty | hne
      · have := hempty
        exact ⟨0, by rw [Subsingleton.elim x 0, zero_smul]⟩
      · obtain ⟨k⟩ := hne
        refine ⟨x k k, ?_⟩
        rw [Matrix.smul_one_eq_diagonal]
        exact hx'.trans (congrArg diagonal (funext fun i ↦ hall i k))
    exact slIdeal_le_of_single_mem I htwo (fun h => hpq (by rw [h]))
      (single_mem_of_diagonal_mem I hxd hpq 1)
  · obtain ⟨i, j, hij, hxij⟩ : ∃ i j : n, i ≠ j ∧ x i j ≠ 0 := by simpa using hoff
    exact slIdeal_le_of_single_mem I htwo hij.symm
      (single_mem_of_apply_ne_zero I htwo hxI hij hxij 1)

/-- **The Lie ideals of `gl n K` are the scalar ones and those containing `sl n K`.** -/
theorem slIdeal_le_or_le_center (htwo : (2 : K) ≠ 0) :
    slIdeal K n ≤ I ∨ I ≤ LieAlgebra.center K (Matrix n n K) := by
  by_cases hle : I ≤ LieAlgebra.center K (Matrix n n K)
  · exact Or.inr hle
  · obtain ⟨x, hxI, hx⟩ := IsConcreteLE.not_le_iff_exists.mp hle
    exact Or.inl (slIdeal_le_of_notMem_center I htwo hxI hx)

end Ideals

/-! ### `sl n K` is perfect, hence not solvable -/

section Perfect

variable [CommRing R]

/-- **`sl n R` is perfect** whenever `2` is invertible in `R`: `⁅sl n R, sl n R⁆ = sl n R`.

Each off-diagonal matrix unit is `Eₚq c = ⁅Eₚₚ - E_qq, Eₚq (t c)⁆` for an inverse `t` of `2`, and
each difference of diagonal units is `Eₚₚ c - E_qq c = ⁅Eₚq c, E_qₚ⁆`; all four factors have trace
zero. -/
theorem lie_slIdeal_slIdeal (htwo : IsUnit (2 : R)) :
    ⁅slIdeal R n, slIdeal R n⁆ = slIdeal R n := by
  obtain ⟨t, ht⟩ := htwo.exists_left_inv
  refine le_antisymm (LieSubmodule.lie_le_right _ _) fun A hA => ?_
  rw [← LieSubmodule.mem_toSubmodule]
  refine mem_of_trace_eq_zero_of_single_mem ?_ ?_ (mem_slIdeal_iff.mp hA)
  · intro p q hpq c
    have hx : single p p (1 : R) - single q q (1 : R) ∈ slIdeal R n := by simp [mem_slIdeal_iff]
    have hy : single p q (t * c) ∈ slIdeal R n := by simp [mem_slIdeal_iff, hpq]
    have h := LieSubmodule.lie_mem_lie hx hy
    rw [lie_single_self_sub_single_self_single hpq, ← mul_assoc, mul_comm (2 : R) t, ht,
      one_mul] at h
    exact h
  · intro p q c
    rcases eq_or_ne p q with rfl | hpq
    · simp
    have hx : single p q c ∈ slIdeal R n := by simp [mem_slIdeal_iff, hpq]
    have hy : single q p (1 : R) ∈ slIdeal R n := by simp [mem_slIdeal_iff, hpq.symm]
    have h := LieSubmodule.lie_mem_lie hx hy
    rw [lie_single_single_eq_sub p q c] at h
    exact h

/-- `sl n R` is nonzero over a nontrivial ring as soon as there are two indices. -/
theorem slIdeal_ne_bot [Nontrivial n] [Nontrivial R] : slIdeal R n ≠ ⊥ := by
  obtain ⟨p, q, hpq⟩ := exists_pair_ne n
  intro hbot
  have hmem : single p q (1 : R) ∈ slIdeal R n := by simp [mem_slIdeal_iff, hpq]
  rw [hbot, LieSubmodule.mem_bot] at hmem
  have happ : single p q (1 : R) p q = (0 : Matrix n n R) p q := by rw [hmem]
  simp at happ

/-- **`sl n R` is not solvable** when `2` is invertible in a nontrivial `R` and there are at least
two indices: it is perfect and nonzero, so its derived series is constant. -/
theorem not_isSolvable_slIdeal [Nontrivial n] [Nontrivial R] (htwo : IsUnit (2 : R)) :
    ¬ LieAlgebra.IsSolvable (slIdeal R n) := by
  intro hsolv
  have hconst : ∀ m : ℕ, derivedSeriesOfIdeal R (Matrix n n R) m (slIdeal R n) = slIdeal R n := by
    intro m
    induction m with
    | zero => rw [derivedSeriesOfIdeal_zero]
    | succ m ih => rw [derivedSeriesOfIdeal_succ, ih, lie_slIdeal_slIdeal htwo]
  obtain ⟨k, hk⟩ := LieAlgebra.IsSolvable.solvable R (slIdeal R n)
  rw [LieIdeal.derivedSeries_eq_bot_iff, hconst k] at hk
  exact slIdeal_ne_bot hk

end Perfect

/-! ### The radical of `gl n K` -/

section Radical

variable {K : Type*} [Field K]

/-- **The radical of `gl n K` is its centre**, for any field in which `2 ≠ 0`: `gl n K` is
reductive.

Every solvable Lie ideal consists of scalar matrices, since an ideal containing a non-central matrix
contains the non-solvable `sl n K` (`TauCeti.slIdeal_le_of_notMem_center`), and conversely the
centre is itself a solvable ideal. -/
theorem radical_matrix_eq_center (htwo : (2 : K) ≠ 0) :
    radical K (Matrix n n K) = LieAlgebra.center K (Matrix n n K) := by
  refine le_antisymm (sSup_le ?_) (center_le_radical K (Matrix n n K))
  intro I hI
  rw [Set.mem_ofPred_eq] at hI
  by_contra hIc
  obtain ⟨x, hxI, hx⟩ := IsConcreteLE.not_le_iff_exists.mp hIc
  rcases subsingleton_or_nontrivial n with hn | hn
  · simp only [center_matrix_eq_top, LieSubmodule.mem_top, not_true_eq_false] at hx
  exact not_isSolvable_slIdeal (isUnit_iff_ne_zero.mpr htwo)
    (LieAlgebra.le_solvable_ideal_solvable (slIdeal_le_of_notMem_center I htwo hxI hx) hI)

/-- **`gl n K` is reductive**, for any field in which `2 ≠ 0`. -/
theorem hasCentralRadical_matrix (htwo : (2 : K) ≠ 0) :
    LieAlgebra.HasCentralRadical K (Matrix n n K) :=
  ⟨radical_matrix_eq_center htwo⟩

/-- Over a field of characteristic zero — the setting of the reductive structure theory — `gl n K`
is reductive with no side hypothesis. -/
instance [CharZero K] : LieAlgebra.HasCentralRadical K (Matrix n n K) :=
  hasCentralRadical_matrix two_ne_zero

end Radical

/-! ### Semisimplicity of the special linear Lie algebra -/

section SpecialLinear

variable (K : Type*) [Field K]
variable (n : Type*) [Fintype n] [DecidableEq n]

/-- The inclusion of an ideal of `sl n` into `gl n` has ideal range. Scalar matrices commute with
the image, while the `sl n` summand preserves the ideal. -/
private theorem slIncl_isIdealMorphism
    (hn : Nonempty n → (Fintype.card n : K) ≠ 0) (J : LieIdeal K (SpecialLinear.sl n K)) :
    ((SpecialLinear.sl n K).incl.comp J.incl).IsIdealMorphism := by
  rw [LieHom.isIdealMorphism_iff]
  intro A y
  obtain ⟨X, r, rfl⟩ := exists_sl_add_smul_one_eq (fun h ↦ isUnit_iff_ne_zero.mpr (hn h)) A
  refine ⟨⟨⁅X, (y : SpecialLinear.sl n K)⁆, J.lie_mem y.property⟩, ?_⟩
  simp [LieRing.of_associative_ring_bracket, add_mul, mul_add]

/-- **The special linear Lie algebra has trivial radical.** If `2` and, for nonempty `n`, the
cardinality of `n` are nonzero, a solvable ideal of `sl n` maps to a solvable ideal of `gl n`,
hence lies in the scalar matrices. Its image also lies in the complementary derived ideal `sl n`,
so the original ideal vanishes. -/
theorem hasTrivialRadical_sl (htwo : (2 : K) ≠ 0)
    (hn : Nonempty n → (Fintype.card n : K) ≠ 0) :
    LieAlgebra.HasTrivialRadical K (SpecialLinear.sl n K) := by
  rw [LieAlgebra.hasTrivialRadical_iff_no_solvable_ideals]
  intro J hJ
  rw [eq_bot_iff]
  intro x hx
  let f : J →ₗ⁅K⁆ Matrix n n K := (SpecialLinear.sl n K).incl.comp J.incl
  have hf : f.IsIdealMorphism := slIncl_isIdealMorphism K n hn J
  have hsolv : LieAlgebra.IsSolvable f.idealRange := by
    let _ : LieAlgebra.IsSolvable J := hJ
    -- The Lie structure of a Lie ideal is by definition that of its underlying subalgebra
    -- (`LieIdeal.lieAlgebra`), so solvability transfers along `hf.eq : f.idealRange = f.range`.
    change LieAlgebra.IsSolvable (f.idealRange : LieSubalgebra K (Matrix n n K))
    rw [hf.eq]
    infer_instance
  have hcenter : f ⟨x, hx⟩ ∈ LieAlgebra.center K (Matrix n n K) := by
    rw [← radical_matrix_eq_center htwo]
    exact (LieIdeal.solvable_iff_le_radical K _ f.idealRange).mp hsolv
      (f.mem_idealRange ⟨x, hx⟩)
  cases isEmpty_or_nonempty n with
  | inl hn' =>
      let _ := hn'
      exact Subsingleton.elim _ _
  | inr hn' =>
      let _ := hn'
      let _ : Invertible (Fintype.card n : K) := invertibleOfNonzero (hn hn')
      have hderived : f ⟨x, hx⟩ ∈ (derivedSeries K (Matrix n n K) 1).toSubmodule := by
        rw [derivedSeries_one_eq_slIdeal K n, LieSubmodule.mem_toSubmodule, mem_slIdeal_iff]
        exact x.property
      have hzero : f ⟨x, hx⟩ = 0 :=
        (isCompl_center_derivedSeries_one_matrix K n).disjoint.le_bot ⟨hcenter, hderived⟩
      apply Subtype.ext
      simpa only [f, LieHom.coe_comp, Function.comp_apply, LieSubalgebra.coe_incl,
        LieIdeal.incl_apply, ZeroMemClass.coe_zero] using hzero

/-- In characteristic zero, `sl n` has trivial radical. -/
instance instHasTrivialRadicalSl [CharZero K] :
    LieAlgebra.HasTrivialRadical K (SpecialLinear.sl n K) :=
  hasTrivialRadical_sl K n two_ne_zero fun h ↦ by
    let _ := h
    exact Nat.cast_ne_zero.mpr Fintype.card_ne_zero

end SpecialLinear

end TauCeti
