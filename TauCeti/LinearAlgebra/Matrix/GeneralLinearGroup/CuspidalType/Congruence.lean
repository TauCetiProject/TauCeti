/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Group.AddChar
public import Mathlib.Basic.Complex.Basic
public import Mathlib.LinearAlgebra.Matrix.Charpoly.Basic
public import Mathlib.LinearAlgebra.Matrix.Trace
public import Mathlib.RingTheory.DedekindDomain.Basic
public import Mathlib.RingTheory.Ideal.Quotient.Basic
public import Mathlib.RingTheory.Localization.FractionRing
public import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.CuspidalType.Basic
import Mathlib.Analysis.Fourier.FiniteAbelian.PontryaginDuality
import Mathlib.LinearAlgebra.Charpoly.ToMatrix
import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas
import Mathlib.RingTheory.Ideal.Quotient.Index
import TauCeti.FieldTheory.Finite.Irreducible
import TauCeti.LinearAlgebra.Charpoly.Quotient
import TauCeti.LinearAlgebra.Matrix.Charpoly.Companion
import TauCeti.LinearAlgebra.Matrix.Defs
import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.Map
import TauCeti.LinearAlgebra.Matrix.IdealEntries
import TauCeti.LinearAlgebra.Matrix.Idempotent.Basic
import TauCeti.LinearAlgebra.Matrix.Idempotent.Integral

/-!
# Cuspidal types of principal congruence subgroups

Let `R` be a commutative ring, `I` an ideal and `K(I) = ker(GL n R → GL n (R ⧸ I))` the principal
congruence subgroup of level `I`. For a matrix `b` over `R` and an additive character `ψ` of
`R ⧸ I ^ 2`, the formula `k ↦ ψ (tr (b * (k - 1)))` is a character `Matrix.congruenceChar b ψ` of
`K(I)`, trivial on `K(I ^ 2)`: the products `(k - 1) * (l - 1)` have entries in `I ^ 2`.

When `R` is a Dedekind domain with fraction field `K` and `𝔭` is a prime ideal, this character is a
cuspidal type relative to `K` (`TauCeti.IsCuspidalType`) as soon as the reduction of `b` modulo
`𝔭` has irreducible characteristic polynomial and `ψ` is nontrivial on the image of `𝔭`. Given an
idempotent `ε ≠ 0, 1` over `K`, take an idempotent `e` over `R` with the same column space
(`IsIdempotentElem.exists_isIdempotentElem_matrix_map`). For `x ∈ 𝔭` the elements
`1 + x * e * Y * (1 - e)` lie in `K(𝔭)` and in the unipotent radical attached to `ε`, and the
character takes the value `ψ (x * tr ((1 - e) * b * e * Y))` there. If all the traces
`tr ((1 - e) * b * e * Y)` lay in `𝔭`, then `(1 - e) * b * e` would vanish modulo `𝔭`: the
reduction of `b` would preserve the column space of the reduction of `e`, a nonzero proper
subspace, against the irreducibility of its characteristic polynomial.

Over a finite residue field such a `b` exists, as a lift of the companion matrix of an irreducible
polynomial of degree `n`, and so does `ψ`, since `R ⧸ 𝔭 ^ 2` is finite. This gives a cuspidal type
of `K(𝔭)` with values in `ℂˣ`, trivial on `K(𝔭 ^ 2)`. For the ring of integers `𝒪` of a
nonarchimedean local field, with uniformizer `ϖ`, it is a cuspidal type of `1 + ϖ M_n(𝒪)` trivial
on `1 + ϖ ^ 2 M_n(𝒪)`.

## Main definitions

* `Matrix.congruenceChar b ψ`: the character `k ↦ ψ (tr (b * (k - 1)))` of `K(I)`.

## Main results

* `Matrix.congruenceChar_eq_one_of_mem_ker`: it is trivial on `K(I ^ 2)`.
* `TauCeti.isCuspidalType_congruenceChar`: over a Dedekind domain, it is a cuspidal type when `b`
  has irreducible characteristic polynomial modulo the prime `𝔭` and `ψ` is nontrivial on `𝔭`.
* `TauCeti.exists_isCuspidalType`: over a Dedekind domain with a nonzero prime `𝔭` of finite
  residue field, `K(𝔭)` has a cuspidal type with values in `ℂˣ` that is trivial on `K(𝔭 ^ 2)`.

## References

* C. J. Bushnell and P. C. Kutzko, *The admissible dual of `GL(N)` via compact open subgroups*,
  Annals of Mathematics Studies 129 (1993), Chapter 1, for the characters `ψ_b` of congruence
  subgroups attached to strata.
* L. Alpöge and L. Sernau, Lean formalization of the generalized Riemann hypothesis for Dirichlet
  `L`-functions (`Lib/GaloisRep/Main/CuspidalTypes.lean`, `New.Variety.exists_isCuspidalType`),
  <https://github.com/lsernau/grh-lean> (Apache 2.0), for the choice of `b` with irreducible
  characteristic polynomial modulo `𝔭` and of `ψ` nontrivial on `𝔭`.
-/

public section

open Matrix Polynomial

variable {n R M : Type*} [Fintype n] [DecidableEq n] [CommRing R] [Monoid M]

namespace Matrix

variable {I : Ideal R}

/-- The entries of `k - 1` lie in `I` for `k` in the principal congruence subgroup of level `I`. -/
private theorem sub_one_apply_mem {k : GL n R}
    (hk : k ∈ (GeneralLinearGroup.map (Ideal.Quotient.mk I)).ker) (i j : n) :
    ((k : Matrix n n R) - 1 : Matrix n n R) i j ∈ I := by
  rw [Matrix.sub_apply]
  exact (GeneralLinearGroup.mem_ker_map_quotientMk_iff I).mp hk i j

omit [DecidableEq n] in
/-- The trace of `b * X` lies in an ideal containing the entries of `X`. -/
private theorem trace_mul_mem {J : Ideal R} (b : Matrix n n R) {X : Matrix n n R}
    (hX : ∀ i j, X i j ∈ J) : (b * X).trace ∈ J :=
  Ideal.sum_mem _ fun i _ ↦ mul_apply_mem_left hX b i i

/-- For a matrix `b` and an additive character `ψ` of `R ⧸ I ^ 2`, the character
`k ↦ ψ (tr (b * (k - 1)))` of the principal congruence subgroup `ker(GL n R → GL n (R ⧸ I))`. It is
multiplicative because `(k * l - 1) - (k - 1) - (l - 1) = (k - 1) * (l - 1)` has entries in
`I ^ 2`. -/
def congruenceChar (b : Matrix n n R) (ψ : AddChar (R ⧸ I ^ 2) M) :
    (GeneralLinearGroup.map (n := n) (Ideal.Quotient.mk I)).ker →* M where
  toFun k := ψ (Ideal.Quotient.mk (I ^ 2) (b * ((k : GL n R) - 1 : Matrix n n R)).trace)
  map_one' := by simp
  map_mul' k l := by
    rw [← AddChar.map_add_eq_mul, ← map_add]
    refine congrArg ψ (Ideal.Quotient.eq.mpr ?_)
    have h : ((k : GL n R) : Matrix n n R) * ((l : GL n R) : Matrix n n R) - 1 =
        ((k : GL n R) - 1 : Matrix n n R) + ((l : GL n R) - 1 : Matrix n n R) +
        ((k : GL n R) - 1 : Matrix n n R) * ((l : GL n R) - 1 : Matrix n n R) := by
      noncomm_ring
    rw [Subgroup.coe_mul, Units.val_mul, h, mul_add, mul_add, trace_add, trace_add,
      add_sub_cancel_left, pow_two]
    exact trace_mul_mem b (mul_apply_mem_mul (sub_one_apply_mem k.property)
      (sub_one_apply_mem l.property))

/-- The value of `Matrix.congruenceChar b ψ` at `k` is `ψ (tr (b * (k - 1)))`. -/
@[simp]
theorem congruenceChar_apply (b : Matrix n n R) (ψ : AddChar (R ⧸ I ^ 2) M)
    (k : (GeneralLinearGroup.map (n := n) (Ideal.Quotient.mk I)).ker) :
    b.congruenceChar ψ k =
      ψ (Ideal.Quotient.mk (I ^ 2) (b * ((k : GL n R) - 1 : Matrix n n R)).trace) :=
  (rfl)

/-- The character `Matrix.congruenceChar b ψ` is trivial on the principal congruence subgroup of
level `I ^ 2`. -/
theorem congruenceChar_eq_one_of_mem_ker (b : Matrix n n R) (ψ : AddChar (R ⧸ I ^ 2) M)
    {k : (GeneralLinearGroup.map (n := n) (Ideal.Quotient.mk I)).ker}
    (hk : (k : GL n R) ∈ (GeneralLinearGroup.map (n := n) (Ideal.Quotient.mk (I ^ 2))).ker) :
    b.congruenceChar ψ k = 1 := by
  rw [congruenceChar_apply, Ideal.Quotient.eq_zero_iff_mem.mpr
    (trace_mul_mem b (sub_one_apply_mem hk)), AddChar.map_zero_eq_one]

end Matrix

namespace TauCeti

/-- Over a field, an idempotent `e` with `(1 - e) * b * e = 0`, whose column space `b` preserves,
is `0` or `1` when the characteristic polynomial of `b` is irreducible. -/
private theorem eq_zero_or_eq_one_of_irreducible_charpoly {k : Type*} [Field k]
    {b e : Matrix n n k} (hb : Irreducible b.charpoly) (he : IsIdempotentElem e)
    (h : (1 - e) * b * e = 0) : e = 0 ∨ e = 1 := by
  rw [sub_mul, sub_mul, one_mul, sub_eq_zero] at h
  have hW : LinearMap.range e.toLin' ≤ (LinearMap.range e.toLin').comap b.toLin' := by
    rintro _ ⟨v, rfl⟩
    exact ⟨(b * e) *ᵥ v, by simp only [toLin'_apply, mulVec_mulVec, ← mul_assoc, ← h]⟩
  by_contra! hne
  refine b.toLin'.not_irreducible_charpoly_of_le_comap hW (fun h0 ↦ hne.1 ?_) (fun h1 ↦ hne.2 ?_)
    (by rwa [charpoly_toLin'])
  · exact toLin'.injective (by rw [LinearMap.range_eq_bot.mp h0, map_zero])
  · refine toLin'.injective (LinearMap.ext fun v ↦ ?_)
    obtain ⟨w, rfl⟩ := LinearMap.range_eq_top.mp h1 v
    rw [toLin'_one, LinearMap.id_apply, ← LinearMap.comp_apply, ← toLin'_mul, he.eq]

/-- If an integral idempotent `e` has reduction `≠ 0, 1` modulo a maximal ideal `𝔭` and `b` has
irreducible characteristic polynomial modulo `𝔭`, some trace `tr ((1 - e) * b * e * Y)` avoids
`𝔭`. -/
private theorem exists_trace_notMem {𝔭 : Ideal R} [𝔭.IsMaximal] {b e : Matrix n n R}
    (hb : Irreducible (b.map (Ideal.Quotient.mk 𝔭)).charpoly) (he : IsIdempotentElem e)
    (h₀ : e.map (Ideal.Quotient.mk 𝔭) ≠ 0) (h₁ : e.map (Ideal.Quotient.mk 𝔭) ≠ 1) :
    ∃ Y : Matrix n n R, ((1 - e) * b * e * Y).trace ∉ 𝔭 := by
  let := Ideal.Quotient.field 𝔭
  by_contra! h
  have hz : (Ideal.Quotient.mk 𝔭).mapMatrix ((1 - e) * b * e) = 0 := by
    ext i j
    simpa [trace_mul_single, Ideal.Quotient.eq_zero_iff_mem] using h (single j i 1)
  simp only [map_mul, map_sub, map_one, RingHom.mapMatrix_apply] at hz
  exact (eq_zero_or_eq_one_of_irreducible_charpoly hb (he.matrix_map _) hz).elim h₀ h₁

/-- For idempotents `ε` and `e` with the same column space, `ε * Y * (1 - ε)` and `e * Y * (1 - e)`
range over the same matrices. -/
private theorem mul_mul_one_sub_eq {A : Type*} [Ring A] {ε e : A} (h₁ : ε * e = e)
    (h₂ : e * ε = ε) (W : A) : ε * (e * W * (1 - e)) * (1 - ε) = e * W * (1 - e) := by
  rw [← mul_assoc, ← mul_assoc, h₁, mul_assoc, mul_sub (1 - e), mul_one, sub_mul, one_mul, h₂,
    sub_self, sub_zero]

variable (K : Type*) [Field K] [Algebra R K] [IsFractionRing R K]

/-- **The characters `ψ_b` are cuspidal types.** Let `R` be a Dedekind domain with fraction field
`K` and `𝔭` a prime ideal. If the reduction of `b` modulo `𝔭` has irreducible characteristic
polynomial and the additive character `ψ` of `R ⧸ 𝔭 ^ 2` is nontrivial on the image of `𝔭`, then
`k ↦ ψ (tr (b * (k - 1)))` is a cuspidal type of the principal congruence subgroup of level `𝔭`,
relative to `K`. -/
theorem isCuspidalType_congruenceChar [IsDedekindDomain R] {𝔭 : Ideal R} [𝔭.IsPrime]
    {b : Matrix n n R} (hb : Irreducible (b.map (Ideal.Quotient.mk 𝔭)).charpoly)
    {ψ : AddChar (R ⧸ 𝔭 ^ 2) M} (hψ : ∃ x ∈ 𝔭, ψ (Ideal.Quotient.mk (𝔭 ^ 2) x) ≠ 1) :
    IsCuspidalType K (b.congruenceChar ψ) := by
  obtain ⟨x, hx, hψx⟩ := hψ
  have h𝔭 : 𝔭.IsMaximal := ‹𝔭.IsPrime›.isMaximal fun h ↦ hψx (by
    rw [h, Ideal.mem_bot] at hx
    rw [hx, map_zero, AddChar.map_zero_eq_one])
  refine isCuspidalType_iff.mpr fun ε hε hε₀ hε₁ ↦ ?_
  -- An integral idempotent `e` with the column space of `ε`, and a trace `c ∉ 𝔭` with `r c ≡ 1`.
  obtain ⟨e, he, hεe, heε⟩ := hε.exists_isIdempotentElem_matrix_map (R := R)
  obtain ⟨Y, hY⟩ := exists_trace_notMem hb he
    (fun h ↦ hε₀ (by rw [← heε, he.eq_zero_of_matrix_map_eq_zero _ h]; simp))
    (fun h ↦ hε₁ (by
      have h' := he.one_sub.eq_zero_of_matrix_map_eq_zero (Ideal.Quotient.mk 𝔭)
        (by simp [Matrix.map_sub, h])
      rw [sub_eq_zero] at h'
      simpa [← h'] using hεe))
  obtain ⟨r, i, hi, hri⟩ := h𝔭.exists_inv hY
  -- The element `k = 1 + Z` of the congruence subgroup, `Z = e * ((x * r) • Y) * (1 - e)`.
  set Z := e * ((x * r) • Y) * (1 - e) with hZ
  have hZZ : IsNilpotent Z := ⟨2, by
    rw [pow_two, hZ, show e * ((x * r) • Y) * (1 - e) * (e * ((x * r) • Y) * (1 - e)) =
      e * ((x * r) • Y) * ((1 - e) * e) * ((x * r) • Y) * (1 - e) by simp only [mul_assoc],
      he.one_sub_mul_self, mul_zero, zero_mul, zero_mul]⟩
  have hk : hZZ.isUnit_one_add.unit ∈ (GeneralLinearGroup.map (Ideal.Quotient.mk 𝔭)).ker := by
    refine (GeneralLinearGroup.mem_ker_map_quotientMk_iff 𝔭).mpr fun a c ↦ ?_
    rw [IsUnit.unit_spec, ← Matrix.sub_apply, add_sub_cancel_left]
    exact mul_mul_apply_mem (fun _ _ ↦ by simpa [mul_assoc] using 𝔭.mul_mem_right _ hx) _ _ a c
  refine ⟨⟨_, hk⟩, ⟨(algebraMap R K).mapMatrix Z, ?_⟩, ?_⟩
  · rw [← RingHom.mapMatrix_apply] at hεe heε
    rw [IsUnit.unit_spec, ← RingHom.mapMatrix_apply, map_add, map_one, hZ]
    simp only [map_mul, map_sub, map_one]
    rw [mul_mul_one_sub_eq hεe heε]
  · have htr : (b * Z).trace = x * r * ((1 - e) * b * e * Y).trace := by
      rw [hZ, show b * (e * ((x * r) • Y) * (1 - e)) = (x * r) • (b * (e * Y) * (1 - e)) by
        simp only [mul_smul_comm, smul_mul_assoc, mul_assoc], trace_smul, trace_mul_comm,
        smul_eq_mul]
      simp only [mul_assoc]
    rw [Matrix.congruenceChar_apply, IsUnit.unit_spec, add_sub_cancel_left, htr]
    convert hψx using 2
    refine Ideal.Quotient.eq.mpr ?_
    rw [show x * r * ((1 - e) * b * e * Y).trace - x = x * -i by linear_combination x * hri,
      pow_two]
    exact Ideal.mul_mem_mul hx (neg_mem hi)

/-- **Existence of cuspidal types.** Let `R` be a Dedekind domain with fraction field `K` and
`𝔭 ≠ ⊥` a prime ideal with finite residue field. The principal congruence subgroup
`ker(GL n R → GL n (R ⧸ 𝔭))` has a cuspidal type relative to `K` with values in `ℂˣ` that is
trivial on the principal congruence subgroup of level `𝔭 ^ 2`. -/
theorem exists_isCuspidalType [IsDedekindDomain R] {𝔭 : Ideal R} [𝔭.IsPrime] (h𝔭 : 𝔭 ≠ ⊥)
    [Finite (R ⧸ 𝔭)] :
    ∃ θ : (GeneralLinearGroup.map (n := n) (Ideal.Quotient.mk 𝔭)).ker →* ℂˣ,
      IsCuspidalType K θ ∧ ∀ k : (GeneralLinearGroup.map (n := n) (Ideal.Quotient.mk 𝔭)).ker,
        (k : GL n R) ∈ (GeneralLinearGroup.map (n := n) (Ideal.Quotient.mk (𝔭 ^ 2))).ker →
          θ k = 1 := by
  rcases isEmpty_or_nonempty n with hn | hn
  · refine ⟨1, isCuspidalType_iff.mpr fun ε _ h₀ _ ↦ ?_, fun _ _ ↦ rfl⟩
    exact absurd (Matrix.ext fun i ↦ isEmptyElim i) h₀
  have : 𝔭.IsMaximal := ‹𝔭.IsPrime›.isMaximal h𝔭
  let := Ideal.Quotient.field 𝔭
  -- A lift `b` of the companion matrix of an irreducible polynomial of degree `n` modulo `𝔭`.
  obtain ⟨f, hfm, hfi, hfd⟩ :=
    exists_monic_irreducible_natDegree_eq (R ⧸ 𝔭) (Fintype.card n) Fintype.card_pos
  obtain ⟨b, hb⟩ := Matrix.map_surjective Ideal.Quotient.mk_surjective
    (reindex ((finCongr hfd).trans (Fintype.equivFin n).symm)
      ((finCongr hfd).trans (Fintype.equivFin n).symm) f.companion)
  -- A character `ψ` of the finite group `R ⧸ 𝔭 ^ 2` that is nontrivial at some `x ∈ 𝔭 \ 𝔭 ^ 2`.
  obtain ⟨x, hx, hx₂⟩ := IsConcreteLE.exists_of_lt (by simpa using Ideal.pow_succ_lt_pow h𝔭 1)
  have := Ideal.finite_quotient_pow (IsNoetherian.noetherian 𝔭) 2
  obtain ⟨ψ, hψ⟩ := (AddChar.exists_apply_ne_zero (a := Ideal.Quotient.mk (𝔭 ^ 2) x)).mpr
    (by rwa [Ne, Ideal.Quotient.eq_zero_iff_mem])
  refine ⟨(b.congruenceChar ψ).toHomUnits, IsCuspidalType.of_comp (f := Units.coeHom ℂ) ?_,
    fun k hk ↦ Units.ext (by simpa using b.congruenceChar_eq_one_of_mem_ker ψ hk)⟩
  convert isCuspidalType_congruenceChar K (b := b)
    (by rwa [show b.map (Ideal.Quotient.mk 𝔭) = _ from hb, charpoly_reindex,
      charpoly_companion hfm]) ⟨x, hx, hψ⟩
  ext
  simp

end TauCeti
