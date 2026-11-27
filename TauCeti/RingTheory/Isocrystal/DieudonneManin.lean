/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.LinearAlgebra.Basis.Defs
public import Mathlib.RingTheory.LaurentSeries
public import Mathlib.RingTheory.Valuation.Basic
public import TauCeti.Algebra.Category.FiniteIsocrystal.Basic
public import TauCeti.RingTheory.Isocrystal.CyclicBlock
public import TauCeti.RingTheory.Isocrystal.StandardBlock
public import TauCeti.RingTheory.LaurentSeries.CoefficientFrobenius
import Mathlib.Data.Rat.Lemmas
import Mathlib.LinearAlgebra.Basis.Prod
import Mathlib.LinearAlgebra.Basis.VectorSpace
import TauCeti.Algebra.Category.FiniteIsocrystal.EqualCharacteristic
import TauCeti.Data.Fin.Basic
import TauCeti.RingTheory.LaurentSeries.Basic

/-!
# Equal-characteristic Dieudonné–Manin classification

Over `L = k((π))` with `k` an algebraically closed field of characteristic `p > 0` and
`σ = LaurentSeries.coefficientFrobenius p f` the arithmetic `p^f`-Frobenius acting on coefficients
and fixing `π = X`, every finite isocrystal `(V, Φ)` admits a basis decomposed into simple standard
blocks `D(s, r)` of coprime slopes `s / r`, and the resulting multiset of block slopes is unique.

## Main definitions

* `TauCeti.CyclicSlopeDecomposition`: a basis of `V` partitioned into coprime standard blocks
  `D(s, r)`.
* `TauCeti.CyclicSlopeDecomposition.slopes`: the multiset of slopes `s / r` of the blocks.
* `TauCeti.CyclicSlopeDecomposition.blockEquiv`: the linear equivalence identifying `V` with the
  product of the block spaces `Fin (D.rank i) → L`.

## Main results

* `TauCeti.CyclicSlopeDecomposition.nonempty`: every finite isocrystal over `k((π))` admits a
  coprime cyclic slope decomposition.
* `TauCeti.CyclicSlopeDecomposition.blockEquiv_intertwines`: `blockEquiv` intertwines `Φ` with
  the standard block Frobenius on each block.
* `TauCeti.CyclicSlopeDecomposition.slopes_eq_of_valuation`: uniqueness of the slope multiset for
  any field `L` with an automorphism `σ` fixing `π ≠ 0` and preserving a valuation `v` with
  `v π ≠ 1`.
* `TauCeti.dieudonneManinEqualChar`: existence and slope uniqueness for finite isocrystals over
  `k((π))`.
* `TauCeti.FiniteIsocrystal.dieudonneManinEqualChar`: categorical form for `D : FiniteIsocrystal σ`.

## References

* L. Fargues and J.-M. Fontaine, *Courbes et fibrés vectoriels en théorie de Hodge p-adique*,
  Astérisque 406 (2018), §8.2.3.
* K. S. Kedlaya, *Slope filtrations revisited*, Doc. Math. 10 (2005), 447–525, §4.5 (4.5.3–4.5.8,
  pp. 497–499).
-/

public section

open Finset Function Module
open scoped LaurentSeries

namespace TauCeti

/-! ### Slope decompositions and splitting of extensions -/

section Splitting

attribute [local instance] RingHomInvPair.of_ringEquiv RingHomInvPair.of_ringEquiv_symm

/-- A basis of `V` partitioned into coprime cyclic Frobenius blocks `D(s, r)`.
The last vector of each block maps to `π ^ s` times its first vector. -/
structure CyclicSlopeDecomposition {L V : Type*} [Field L] [AddCommGroup V] [Module L V]
    {σ : L ≃+* L} (Φ : V →ₛₗ[(σ : L →+* L)] V) (π : L) where
  /-- The number of cyclic blocks in the decomposition. -/
  blocks : ℕ
  /-- The dimension `r` of block `i`. -/
  rank : Fin blocks → ℕ+
  /-- The power `s` of `π` picked up when the cycle of block `i` closes (slope `s / r`). -/
  exponent : Fin blocks → ℤ
  /-- Coprimality of `|s|` and `r` for each block. -/
  coprime : ∀ i, (exponent i).natAbs.Coprime (rank i)
  /-- The `L`-basis of `V` indexed by `(i, j)` with `j : Fin (rank i)`. -/
  basis : Module.Basis (Σ i, Fin (rank i)) L V
  /-- Frobenius sends `e_j ↦ e_{j+1}` and the last vector of block `i` to `π ^ s • e_0`. -/
  frobenius_basis : ∀ i j, Φ (basis ⟨i, j⟩) =
    (if j.val + 1 = rank i then π ^ exponent i else 1) •
      basis ⟨i, finRotate (rank i) j⟩

/-- The multiset of simple-block slopes, counting each block once. -/
def CyclicSlopeDecomposition.slopes {L V : Type*} [Field L] [AddCommGroup V]
    [Module L V] {σ : L ≃+* L} {Φ : V →ₛₗ[(σ : L →+* L)] V} {π : L}
    (D : CyclicSlopeDecomposition Φ π) : Multiset ℚ :=
  (List.ofFn fun i ↦ (D.exponent i : ℚ) / (D.rank i : ℕ) : List ℚ)

/-- The number of slopes in a decomposition equals the number of blocks. -/
@[simp]
theorem CyclicSlopeDecomposition.card_slopes {L V : Type*} [Field L] [AddCommGroup V]
    [Module L V] {σ : L ≃+* L} {Φ : V →ₛₗ[(σ : L →+* L)] V} {π : L}
    (D : CyclicSlopeDecomposition Φ π) :
    D.slopes.card = D.blocks := by
  simp [CyclicSlopeDecomposition.slopes]

/-- The multiplicity of `q` in `D.slopes` equals the number of blocks of slope `q`. -/
theorem CyclicSlopeDecomposition.count_slopes {L V : Type*} [Field L] [AddCommGroup V]
    [Module L V] {σ : L ≃+* L} {Φ : V →ₛₗ[(σ : L →+* L)] V} {π : L}
    (D : CyclicSlopeDecomposition Φ π) (q : ℚ) :
    D.slopes.count q =
      (Finset.univ.filter fun i : Fin D.blocks ↦
        (D.exponent i : ℚ) / (D.rank i : ℕ) = q).card := by
  rw [CyclicSlopeDecomposition.slopes, Multiset.coe_count, List.count_ofFn]

/-- The ranks of the blocks in a cyclic slope decomposition sum to the dimension of `V`. -/
theorem CyclicSlopeDecomposition.sum_rank_eq_finrank {L V : Type*} [Field L] [AddCommGroup V]
    [Module L V] {σ : L ≃+* L} {Φ : V →ₛₗ[(σ : L →+* L)] V} {π : L}
    (D : CyclicSlopeDecomposition Φ π) :
    (∑ i : Fin D.blocks, (D.rank i : ℕ)) = Module.finrank L V := by
  rw [Module.finrank_eq_card_basis D.basis, Fintype.card_sigma]
  simp

private noncomputable def sectionProdEquiv {L V : Type*} [Field L] [AddCommGroup V] [Module L V]
    {r : ℕ+} (ι : (Fin r → L) →ₗ[L] V) (hι : Injective ι)
    (sec : (V ⧸ LinearMap.range ι) →ₗ[L] V)
    (hq_sec : ∀ y, (LinearMap.range ι).mkQ (sec y) = y) :
    ((Fin r → L) × (V ⧸ LinearMap.range ι)) ≃ₗ[L] V :=
  have hdisj : Disjoint (LinearMap.range ι) (LinearMap.range sec) := by
    rw [disjoint_iff_inf_le]
    rintro z ⟨⟨x, rfl⟩, ⟨y, hy⟩⟩
    have hy0 : y = 0 := by
      have := congrArg (LinearMap.range ι).mkQ hy
      rw [hq_sec, Submodule.mkQ_apply,
        (Submodule.Quotient.mk_eq_zero (LinearMap.range ι)).2 ⟨x, rfl⟩] at this
      exact this
    simp [← hy, hy0]
  have hsec_inj : Injective sec := fun y₁ y₂ h ↦ by
    simpa [hq_sec] using congrArg (LinearMap.range ι).mkQ h
  have hinj : Injective (ι.coprod sec) := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_coprod_of_disjoint_range ι sec hdisj,
      LinearMap.ker_eq_bot.2 hι, LinearMap.ker_eq_bot.2 hsec_inj]
    exact Submodule.ext fun ⟨a, b⟩ ↦ by simp
  have hsurj : Surjective (ι.coprod sec) := fun z ↦ by
    have hz : z - sec ((LinearMap.range ι).mkQ z) ∈ LinearMap.range ι := by
      rw [← Submodule.Quotient.mk_eq_zero (LinearMap.range ι), ← Submodule.mkQ_apply, map_sub,
        hq_sec, sub_self]
    obtain ⟨x, hx⟩ := hz
    exact ⟨(x, (LinearMap.range ι).mkQ z), by simp [hx]⟩
  LinearEquiv.ofBijective (ι.coprod sec) ⟨hinj, hsurj⟩

@[simp]
private theorem sectionProdEquiv_apply {L V : Type*} [Field L] [AddCommGroup V] [Module L V]
    {r : ℕ+} (ι : (Fin r → L) →ₗ[L] V) (hι : Injective ι)
    (sec : (V ⧸ LinearMap.range ι) →ₗ[L] V)
    (hq_sec : ∀ y, (LinearMap.range ι).mkQ (sec y) = y)
    (p : (Fin r → L) × (V ⧸ LinearMap.range ι)) :
    sectionProdEquiv ι hι sec hq_sec p = ι p.1 + sec p.2 :=
  LinearMap.coprod_apply ι sec p

private def consBlockIdxEquiv {b : ℕ} (r : ℕ+) (rk : Fin b → ℕ+) :
    Fin r ⊕ (Σ i : Fin b, Fin (rk i)) ≃
      Σ i : Fin (b + 1), Fin (Fin.cases (motive := fun _ ↦ ℕ+) r rk i) :=
  let rank : Fin (b + 1) → ℕ+ := Fin.cases r rk
  have hr0 : (rank 0 : ℕ) = (r : ℕ) := by simp [rank]
  have hrs (i : Fin b) : (rank i.succ : ℕ) = (rk i : ℕ) := by simp [rank]
  { toFun := Sum.elim (fun j ↦ ⟨0, finCongr hr0.symm j⟩)
      (fun ij ↦ ⟨ij.1.succ, finCongr (hrs ij.1).symm ij.2⟩)
    invFun ij := Fin.cases
      (motive := fun i ↦
        Fin (Fin.cases (motive := fun _ ↦ ℕ+) r rk i) →
          Fin r ⊕ (Σ i' : Fin b, Fin (rk i')))
      (fun j ↦ Sum.inl (finCongr hr0 j)) (fun i j ↦ Sum.inr ⟨i, finCongr (hrs i) j⟩) ij.1 ij.2
    left_inv := by
      rintro (j | ⟨i, j⟩)
      · exact congrArg Sum.inl (Fin.ext rfl) -- `Fin.cases ... 0` reduces definitionally
      · exact congrArg (fun x : Fin (rk i) ↦ Sum.inr (⟨i, x⟩ : Σ i' : Fin b, Fin (rk i')))
          (Fin.ext rfl) -- `Fin.cases ... i.succ` reduces definitionally
    right_inv := by
      rintro ⟨i, j⟩
      revert j
      refine Fin.cases ?_ ?_ i
      · intro j; exact Sigma.ext rfl (heq_of_eq (Fin.ext rfl))
      · intro i j; exact Sigma.ext rfl (heq_of_eq (Fin.ext rfl)) }

private theorem consBlockIdxEquiv_symm_zero {b : ℕ} (r : ℕ+) (rk : Fin b → ℕ+)
    (h0 : ((Fin.cases (motive := fun _ ↦ ℕ+) r rk 0 : ℕ+) : ℕ) = (r : ℕ))
    (j : Fin (Fin.cases (motive := fun _ ↦ ℕ+) r rk 0)) :
    (consBlockIdxEquiv r rk).symm ⟨0, j⟩ = Sum.inl (finCongr h0 j) :=
  congrArg Sum.inl (Fin.ext rfl)

private theorem consBlockIdxEquiv_symm_succ {b : ℕ} (r : ℕ+) (rk : Fin b → ℕ+)
    (i : Fin b) (hs : ((Fin.cases (motive := fun _ ↦ ℕ+) r rk i.succ : ℕ+) : ℕ) = (rk i : ℕ))
    (j : Fin (Fin.cases (motive := fun _ ↦ ℕ+) r rk i.succ)) :
    (consBlockIdxEquiv r rk).symm ⟨i.succ, j⟩ = Sum.inr ⟨i, finCongr hs j⟩ :=
  congrArg (fun x : Fin (rk i) ↦ Sum.inr (⟨i, x⟩ : Σ i' : Fin b, Fin (rk i'))) (Fin.ext rfl)

private theorem cyclicSlopeDecomposition_cons_frobenius_basis {L V : Type*} [Field L]
    [AddCommGroup V] [Module L V] {σ : L ≃+* L} (Φ : V →ₛₗ[(σ : L →+* L)] V) (π : L)
    {s : ℤ} {r : ℕ+} (ι : (Fin r → L) →ₗ[L] V) (hι : Injective ι)
    (hinter : ∀ x, ι (standardBlockFrobenius σ π s r x) = Φ (ι x))
    (hW : LinearMap.range ι ≤ (LinearMap.range ι).comap Φ)
    (D_Q : CyclicSlopeDecomposition ((LinearMap.range ι).mapQ (LinearMap.range ι) Φ hW) π)
    (sec : (V ⧸ LinearMap.range ι) →ₗ[L] V)
    (hq_sec : ∀ y, (LinearMap.range ι).mkQ (sec y) = y)
    (hΦ_sec : ∀ y, Φ (sec y) = sec ((LinearMap.range ι).mapQ (LinearMap.range ι) Φ hW y))
    (i : Fin (D_Q.blocks + 1))
    (j : Fin (Fin.cases (motive := fun _ ↦ ℕ+) r D_Q.rank i)) :
    let rk : Fin (D_Q.blocks + 1) → ℕ+ := Fin.cases r D_Q.rank
    let exp : Fin (D_Q.blocks + 1) → ℤ := Fin.cases s D_Q.exponent
    let e_V := sectionProdEquiv ι hι sec hq_sec
    let e_idx := consBlockIdxEquiv r D_Q.rank
    let bas : Basis (Σ i : Fin (D_Q.blocks + 1), Fin (rk i)) L V :=
      (((Pi.basisFun L (Fin r)).prod D_Q.basis).map e_V).reindex e_idx
    Φ (bas ⟨i, j⟩) =
      (if j.val + 1 = rk i then π ^ exp i else 1) • bas ⟨i, finRotate (rk i) j⟩ := by
  intro rk exp e_V e_idx bas
  have hr0 : (rk 0 : ℕ) = (r : ℕ) := by simp [rk]
  have hrs (i' : Fin D_Q.blocks) : (rk i'.succ : ℕ) = (D_Q.rank i' : ℕ) := by simp [rk]
  refine Fin.cases (motive := fun i ↦ ∀ j : Fin (rk i),
      Φ (bas ⟨i, j⟩) = (if j.val + 1 = rk i then π ^ exp i else 1) •
        bas ⟨i, finRotate (rk i) j⟩)
    (fun j ↦ ?_) (fun i j ↦ ?_) i j
  · have hbas (l : Fin (rk 0)) : bas ⟨0, l⟩ = ι (Pi.single (finCongr hr0 l) 1) := by
      dsimp only [bas, e_idx]
      rw [Basis.reindex_apply, Basis.map_apply, consBlockIdxEquiv_symm_zero r D_Q.rank hr0,
        Basis.prod_apply, Sum.elim_inl, comp_apply, Pi.basisFun_apply, LinearMap.inl_apply,
        sectionProdEquiv_apply, map_zero, add_zero]
    rw [hbas, hbas, Fin.finCongr_finRotate, ← hinter, ← map_smul]
    congr 1
    by_cases hj : j.val + 1 = rk 0
    · have hj' : (finCongr hr0 j).val + 1 = r := by simpa [hr0] using hj
      simp only [hj, ↓reduceIte, exp, Fin.cases_zero]
      rw [standardBlockFrobenius_single_of_val_add_one_eq hj' 1]
      ext; simp [Pi.single_apply]
    · have hj' : (finCongr hr0 j).val + 1 ≠ r := by simpa [hr0] using hj
      simp only [hj, ↓reduceIte, one_smul]
      exact (standardBlockFrobenius_single_of_val_add_one_ne hj' 1).trans (by simp)
  · have hbas (l : Fin (rk i.succ)) :
        bas ⟨i.succ, l⟩ = sec (D_Q.basis ⟨i, finCongr (hrs i) l⟩) := by
      dsimp only [bas, e_idx]
      rw [Basis.reindex_apply, Basis.map_apply, consBlockIdxEquiv_symm_succ r D_Q.rank i (hrs i),
        Basis.prod_apply, Sum.elim_inr, comp_apply, LinearMap.inr_apply, sectionProdEquiv_apply,
        map_zero, zero_add]
    rw [hbas, hbas, Fin.finCongr_finRotate, hΦ_sec, D_Q.frobenius_basis, map_smul]
    simp [hrs, exp]

private noncomputable def cyclicSlopeDecomposition_cons {L V : Type*} [Field L]
    [AddCommGroup V] [Module L V] {σ : L ≃+* L} (Φ : V →ₛₗ[(σ : L →+* L)] V) (π : L)
    {s : ℤ} {r : ℕ+} (hcop : s.natAbs.Coprime r)
    (ι : (Fin r → L) →ₗ[L] V) (hι : Injective ι)
    (hinter : ∀ x, ι (standardBlockFrobenius σ π s r x) = Φ (ι x))
    (hW : LinearMap.range ι ≤ (LinearMap.range ι).comap Φ)
    (D_Q : CyclicSlopeDecomposition ((LinearMap.range ι).mapQ (LinearMap.range ι) Φ hW) π)
    (sec : (V ⧸ LinearMap.range ι) →ₗ[L] V)
    (hq_sec : ∀ y, (LinearMap.range ι).mkQ (sec y) = y)
    (hΦ_sec : ∀ y, Φ (sec y) = sec ((LinearMap.range ι).mapQ (LinearMap.range ι) Φ hW y)) :
    CyclicSlopeDecomposition Φ π :=
  let rk : Fin (D_Q.blocks + 1) → ℕ+ := Fin.cases r D_Q.rank
  let exp : Fin (D_Q.blocks + 1) → ℤ := Fin.cases s D_Q.exponent
  let e_V := sectionProdEquiv ι hι sec hq_sec
  let e_idx := consBlockIdxEquiv r D_Q.rank
  let bas : Basis (Σ i : Fin (D_Q.blocks + 1), Fin (rk i)) L V :=
    (((Pi.basisFun L (Fin r)).prod D_Q.basis).map e_V).reindex e_idx
  { blocks := D_Q.blocks + 1
    rank := rk
    exponent := exp
    coprime := Fin.cases (motive := fun i ↦ (exp i).natAbs.Coprime (rk i))
      (by simpa [rk, exp] using hcop) (fun i ↦ by simpa [rk, exp] using D_Q.coprime i)
    basis := bas
    frobenius_basis :=
      cyclicSlopeDecomposition_cons_frobenius_basis Φ π ι hι hinter hW D_Q sec hq_sec hΦ_sec }

/-- **Existence of cyclic slope decompositions.** Every finite isocrystal `(V, Φ)` over `k((π))`
(with `k` algebraically closed of characteristic `p > 0` and `f > 0`) admits a decomposition into
coprime cyclic standard blocks `D(s, r)` (Kedlaya 2005, §4.5, 4.5.3–4.5.8, pp. 497–499). -/
theorem CyclicSlopeDecomposition.nonempty {p : ℕ} [Fact p.Prime] (f : ℕ+)
    (k : Type*) [Field k] [CharP k p] [IsAlgClosed k]
    (V : Type*) [AddCommGroup V] [Module (LaurentSeries k) V]
    [FiniteDimensional (LaurentSeries k) V]
    (Φ : V →ₛₗ[(LaurentSeries.coefficientFrobenius (k := k) p f :
      LaurentSeries k →+* LaurentSeries k)] V)
    (hΦ : Bijective Φ) :
    Nonempty (CyclicSlopeDecomposition Φ (HahnSeries.single 1 1)) := by
  classical
  induction hfin : Module.finrank (LaurentSeries k) V using Nat.strong_induction_on
      generalizing V with
  | _ n ih =>
    rcases eq_or_ne n 0 with rfl | hn
    · have : Subsingleton V := Module.finrank_zero_iff.1 hfin
      exact ⟨⟨0, Fin.elim0, Fin.elim0, fun i ↦ i.elim0, Basis.empty V, fun i ↦ i.elim0⟩⟩
    have : Nontrivial V := Module.finrank_pos_iff.1 (hfin ▸ Nat.pos_of_ne_zero hn)
    let σ : LaurentSeries k ≃ₐ[ℤ] LaurentSeries k :=
      { LaurentSeries.coefficientFrobenius (k := k) p f with
        commutes' := fun c ↦ by simp [eq_intCast] }
    let D : FiniteIsocrystal σ := FiniteIsocrystal.of σ V Φ hΦ
    obtain ⟨s, r, hcop, ι, hι, hinter⟩ :=
      exists_injective_intertwines_standardBlock (Φ := Φ) hΦ.injective
    let W := LinearMap.range ι
    have hW : ∀ x ∈ W, D.frobenius x ∈ W := by rintro _ ⟨x, rfl⟩; exact ⟨_, hinter x⟩
    have hfinW : 0 < Module.finrank (LaurentSeries k) W := by
      have : Nontrivial W := ⟨⟨⟨ι (Pi.single (0 : Fin r) 1), ⟨_, rfl⟩⟩, 0, fun h ↦ by
        have h0 : Pi.single (0 : Fin r) (1 : LaurentSeries k) = 0 :=
          hι ((congrArg Subtype.val h).trans (map_zero ι).symm)
        simpa using congrFun h0 0⟩⟩
      exact Module.finrank_pos (R := LaurentSeries k)
    have hlt : Module.finrank (LaurentSeries k) (V ⧸ W) < n := by
      have hadd := Submodule.finrank_quotient_add_finrank W
      omega
    have hΦ_Q : D.quotientFrobenius W hW = W.mapQ W Φ hW := by
      ext x
      exact (D.quotientFrobenius_mk W hW x).trans (Submodule.mapQ_apply W W Φ (h := hW) x).symm
    have hΦ_Q_bij : Bijective (W.mapQ W Φ hW) := by
      rw [← hΦ_Q]
      exact D.quotientFrobenius_bijective W hW
    obtain ⟨D_Q⟩ := ih (Module.finrank (LaurentSeries k) (V ⧸ W)) hlt (V ⧸ W)
      (W.mapQ W Φ hW) hΦ_Q_bij rfl
    have : CategoryTheory.IsSplitEpi (D.quotientπ W hW) :=
      FiniteIsocrystal.isSplitEpi_of_epi rfl f.pos (D.quotientπ W hW)
    let sec := CategoryTheory.section_ (D.quotientπ W hW)
    have hq_sec (y : V ⧸ W) : W.mkQ (sec.hom y) = y := by
      have h := congrArg (fun g : D.quotient W hW ⟶ D.quotient W hW ↦ g.hom y)
        (CategoryTheory.IsSplitEpi.id (D.quotientπ W hW))
      simpa only [FiniteIsocrystal.hom_comp, LinearMap.comp_apply,
        FiniteIsocrystal.quotientπ_hom, FiniteIsocrystal.hom_id, LinearMap.id_apply] using h
    have hΦ_sec (y : V ⧸ W) : Φ (sec.hom y) = sec.hom (W.mapQ W Φ hW y) := by
      rw [← hΦ_Q]
      exact (sec.hom_frobenius y).symm
    exact ⟨cyclicSlopeDecomposition_cons Φ (HahnSeries.single 1 1) hcop ι hι hinter hW D_Q
      sec.hom hq_sec hΦ_sec⟩

end Splitting

/-! ### Uniqueness of slopes -/

section Uniqueness

/-- The linear equivalence from `V` to the product of block spaces `Fin (D.rank i) → L` induced
by `D.basis`. -/
noncomputable def CyclicSlopeDecomposition.blockEquiv {L V : Type*} [Field L]
    [AddCommGroup V] [Module L V] {σ : L ≃+* L} {Φ : V →ₛₗ[(σ : L →+* L)] V} {π : L}
    (D : CyclicSlopeDecomposition Φ π) :
    V ≃ₗ[L] (∀ i : Fin D.blocks, Fin (D.rank i) → L) :=
  D.basis.equivFun.trans (LinearEquiv.piCurry L fun _ _ ↦ L)

/-- The image under `D.blockEquiv` of the basis vector `D.basis ⟨b, j⟩` is the `j`-th standard
basis vector in block `b`. -/
@[simp]
theorem CyclicSlopeDecomposition.blockEquiv_basis {L V : Type*} [Field L]
    [AddCommGroup V] [Module L V] {σ : L ≃+* L} {Φ : V →ₛₗ[(σ : L →+* L)] V} {π : L}
    (D : CyclicSlopeDecomposition Φ π) (b : Fin D.blocks) (j : Fin (D.rank b)) :
    D.blockEquiv (D.basis ⟨b, j⟩) = Pi.single b (Pi.single j 1) := by
  ext k l
  by_cases hk : k = b
  · subst hk
    simp [CyclicSlopeDecomposition.blockEquiv, Sigma.curry, Pi.single_apply, Finsupp.single_apply,
      eq_comm]
  · simp [CyclicSlopeDecomposition.blockEquiv, Sigma.curry, hk]

/-- `D.blockEquiv` intertwines `Φ` with `standardBlockFrobenius` on each block. -/
theorem CyclicSlopeDecomposition.blockEquiv_intertwines {L V : Type*} [Field L]
    [AddCommGroup V] [Module L V] {σ : L ≃+* L} {Φ : V →ₛₗ[(σ : L →+* L)] V} {π : L}
    (D : CyclicSlopeDecomposition Φ π) (v : V) (i : Fin D.blocks) :
    D.blockEquiv (Φ v) i =
      standardBlockFrobenius σ π (D.exponent i) (D.rank i) (D.blockEquiv v i) := by
  have hbas (b : Fin D.blocks) (j : Fin (D.rank b)) :
      D.blockEquiv (Φ (D.basis ⟨b, j⟩)) i =
        standardBlockFrobenius σ π (D.exponent i) (D.rank i)
          (D.blockEquiv (D.basis ⟨b, j⟩) i) := by
    rw [D.frobenius_basis, map_smul, Pi.smul_apply, D.blockEquiv_basis, D.blockEquiv_basis]
    by_cases hib : i = b
    · subst hib
      rw [Pi.single_eq_same, Pi.single_eq_same]
      by_cases hj : j.val + 1 = D.rank i
      · rw [standardBlockFrobenius_single_of_val_add_one_eq hj, map_one, mul_one]
        ext; simp [hj, Pi.single_apply]
      · rw [standardBlockFrobenius_single_of_val_add_one_ne hj, map_one]
        simp [hj]
    · simp [Pi.single_eq_of_ne hib]
  conv_lhs => rw [← D.basis.sum_repr v]
  conv_rhs => rw [← D.basis.sum_repr v]
  rw [map_sum, map_sum, Finset.sum_apply, map_sum, Finset.sum_apply, map_sum]
  refine Finset.sum_congr rfl fun ⟨b, j⟩ _ ↦ ?_
  rw [map_smulₛₗ, map_smul, Pi.smul_apply, map_smul, Pi.smul_apply, map_smulₛₗ,
    RingHom.coe_coe, hbas]

private theorem isotypic_component_zero {L V Γ₀ : Type*} [Field L]
    [LinearOrderedCommGroupWithZero Γ₀] [AddCommGroup V] [Module L V] {σ : L ≃+* L}
    {Φ : V →ₛₗ[(σ : L →+* L)] V} {π : L} {v : Valuation L Γ₀}
    (hv : ∀ x, v (σ x) = v x) (hπ : π ≠ 0) (hvπ : v π ≠ 1) (hσπ : σ π = π)
    (D₁ D₂ : CyclicSlopeDecomposition Φ π) (i₁ : Fin D₁.blocks) (i₂ : Fin D₂.blocks)
    (hslope : (D₁.exponent i₁ : ℚ) / (D₁.rank i₁ : ℕ) ≠
      (D₂.exponent i₂ : ℚ) / (D₂.rank i₂ : ℕ))
    (x : Fin (D₁.rank i₁) → L) :
    D₂.blockEquiv (D₁.blockEquiv.symm (Pi.single i₁ x)) i₂ = 0 := by
  let f : (Fin (D₁.rank i₁) → L) →ₗ[L] (Fin (D₂.rank i₂) → L) :=
    { toFun y := D₂.blockEquiv (D₁.blockEquiv.symm (Pi.single i₁ y)) i₂
      map_add' y₁ y₂ := by simp [Pi.single_add, map_add]
      map_smul' c y := by simp [Pi.single_smul, map_smul] }
  have hf : ∀ y, f (standardBlockFrobenius σ π (D₁.exponent i₁) (D₁.rank i₁) y) =
      standardBlockFrobenius σ π (D₂.exponent i₂) (D₂.rank i₂) (f y) := by
    intro y
    let v₀ : V := D₁.blockEquiv.symm (Pi.single i₁ y)
    have hv₀ : D₁.blockEquiv (Φ v₀) =
        Pi.single i₁ (standardBlockFrobenius σ π (D₁.exponent i₁) (D₁.rank i₁) y) := by
      ext k l
      rw [D₁.blockEquiv_intertwines]
      by_cases hk : k = i₁
      · subst hk; simp [v₀]
      · have hzero : D₁.blockEquiv v₀ k = 0 := by simp [v₀, hk]
        simp [hzero, hk]
    have hMΦ : D₂.blockEquiv (D₁.blockEquiv.symm
        (Pi.single i₁ (standardBlockFrobenius σ π (D₁.exponent i₁) (D₁.rank i₁) y))) =
        D₂.blockEquiv (Φ v₀) :=
      congrArg D₂.blockEquiv (D₁.blockEquiv.symm_apply_eq.2 hv₀.symm)
    have hf' := congrFun hMΦ i₂
    rw [D₂.blockEquiv_intertwines] at hf'
    simpa [f, v₀] using hf'
  exact LinearMap.congr_fun
    (eq_zero_of_intertwines_standardBlock hv hπ hvπ hσπ hslope hf) x

private noncomputable def isotypicSliceExt {L V : Type*} [Field L] [AddCommGroup V]
    [Module L V] {σ : L ≃+* L} {Φ : V →ₛₗ[(σ : L →+* L)] V} {π : L}
    (D : CyclicSlopeDecomposition Φ π) (q : ℚ)
    [DecidablePred fun i : Fin D.blocks ↦ (D.exponent i : ℚ) / (D.rank i : ℕ) = q] :
    (∀ i : {i : Fin D.blocks // (D.exponent i : ℚ) / (D.rank i : ℕ) = q},
      Fin (D.rank i.val) → L) →ₗ[L] (∀ i : Fin D.blocks, Fin (D.rank i) → L) where
  toFun x i := if hi : (D.exponent i : ℚ) / (D.rank i : ℕ) = q then x ⟨i, hi⟩ else 0
  map_add' x₁ x₂ := by
    ext i l
    by_cases hi : (D.exponent i : ℚ) / (D.rank i : ℕ) = q <;> simp [hi]
  map_smul' c x := by
    ext i l
    by_cases hi : (D.exponent i : ℚ) / (D.rank i : ℕ) = q <;> simp [hi]

private theorem isotypicSliceExt_apply {L V : Type*} [Field L] [AddCommGroup V]
    [Module L V] {σ : L ≃+* L} {Φ : V →ₛₗ[(σ : L →+* L)] V} {π : L}
    (D : CyclicSlopeDecomposition Φ π) (q : ℚ)
    [DecidablePred fun i : Fin D.blocks ↦ (D.exponent i : ℚ) / (D.rank i : ℕ) = q]
    (x : ∀ i : {i : Fin D.blocks // (D.exponent i : ℚ) / (D.rank i : ℕ) = q},
      Fin (D.rank i.val) → L) (i : Fin D.blocks) :
    isotypicSliceExt D q x i =
      if hi : (D.exponent i : ℚ) / (D.rank i : ℕ) = q then x ⟨i, hi⟩ else 0 :=
  rfl

private theorem isotypicSliceExt_map_eq {L V Γ₀ : Type*} [Field L]
    [LinearOrderedCommGroupWithZero Γ₀] [AddCommGroup V] [Module L V] {σ : L ≃+* L}
    {Φ : V →ₛₗ[(σ : L →+* L)] V} {π : L} {v : Valuation L Γ₀}
    (hv : ∀ x, v (σ x) = v x) (hπ : π ≠ 0) (hvπ : v π ≠ 1) (hσπ : σ π = π)
    (D₁ D₂ : CyclicSlopeDecomposition Φ π) (q : ℚ)
    [DecidablePred fun i : Fin D₁.blocks ↦ (D₁.exponent i : ℚ) / (D₁.rank i : ℕ) = q]
    [DecidablePred fun i : Fin D₂.blocks ↦ (D₂.exponent i : ℚ) / (D₂.rank i : ℕ) = q]
    (x : ∀ i : {i : Fin D₁.blocks // (D₁.exponent i : ℚ) / (D₁.rank i : ℕ) = q},
      Fin (D₁.rank i.val) → L) :
    isotypicSliceExt D₂ q (fun i' ↦ D₂.blockEquiv (D₁.blockEquiv.symm (isotypicSliceExt D₁ q x))
      i'.val) = D₂.blockEquiv (D₁.blockEquiv.symm (isotypicSliceExt D₁ q x)) := by
  ext i' m
  by_cases hi' : (D₂.exponent i' : ℚ) / (D₂.rank i' : ℕ) = q
  · simp [isotypicSliceExt, hi']
  · simp only [isotypicSliceExt_apply, hi', ↓reduceDIte, Pi.zero_apply]
    have hsum : isotypicSliceExt D₁ q x =
        ∑ j : Fin D₁.blocks, Pi.single j (isotypicSliceExt D₁ q x j) :=
      (Finset.univ_sum_single _).symm
    rw [hsum, map_sum, map_sum, Finset.sum_apply, Finset.sum_apply]
    refine (Finset.sum_eq_zero fun j _ ↦ ?_).symm
    by_cases hj : (D₁.exponent j : ℚ) / (D₁.rank j : ℕ) = q
    · have hne : (D₁.exponent j : ℚ) / (D₁.rank j : ℕ) ≠
          (D₂.exponent i' : ℚ) / (D₂.rank i' : ℕ) :=
        hj.symm ▸ (Ne.symm hi')
      exact congrFun (isotypic_component_zero hv hπ hvπ hσπ D₁ D₂ j i' hne
        (isotypicSliceExt D₁ q x j)) m
    · simp [isotypicSliceExt, hj]

private noncomputable def isotypicBlockEquiv {L V Γ₀ : Type*} [Field L]
    [LinearOrderedCommGroupWithZero Γ₀] [AddCommGroup V] [Module L V] {σ : L ≃+* L}
    {Φ : V →ₛₗ[(σ : L →+* L)] V} {π : L} {v : Valuation L Γ₀}
    (hv : ∀ x, v (σ x) = v x) (hπ : π ≠ 0) (hvπ : v π ≠ 1) (hσπ : σ π = π)
    (D D' : CyclicSlopeDecomposition Φ π) (q : ℚ) :
    (∀ i : {i : Fin D.blocks // (D.exponent i : ℚ) / (D.rank i : ℕ) = q},
      Fin (D.rank i.val) → L) ≃ₗ[L]
    (∀ i' : {i' : Fin D'.blocks // (D'.exponent i' : ℚ) / (D'.rank i' : ℕ) = q},
      Fin (D'.rank i'.val) → L) := by
  classical
  let M := D.blockEquiv.symm.trans D'.blockEquiv
  exact
    { toFun x i' := M (isotypicSliceExt D q x) i'.val
      invFun y i := M.symm (isotypicSliceExt D' q y) i.val
      left_inv x := by
        ext ⟨i, hi⟩ l
        have h := isotypicSliceExt_map_eq hv hπ hvπ hσπ D D' q x
        dsimp only [M, LinearEquiv.trans_apply, LinearEquiv.symm_trans_apply,
          LinearEquiv.symm_symm] at h ⊢
        rw [h, D'.blockEquiv.symm_apply_apply, D.blockEquiv.apply_symm_apply]
        simp [isotypicSliceExt, hi]
      right_inv y := by
        ext ⟨i', hi'⟩ l
        have h := isotypicSliceExt_map_eq hv hπ hvπ hσπ D' D q y
        dsimp only [M, LinearEquiv.trans_apply, LinearEquiv.symm_trans_apply,
          LinearEquiv.symm_symm] at h ⊢
        rw [h, D.blockEquiv.symm_apply_apply, D'.blockEquiv.apply_symm_apply]
        simp [isotypicSliceExt, hi']
      map_add' x₁ x₂ := by ext i' m; simp [map_add]
      map_smul' c x := by ext i' m; simp [map_smul] }

/-- **Uniqueness of slopes for arbitrary valued fields.** If `σ` fixes `π ≠ 0` and preserves a
valuation `v` with `v π ≠ 1`, then any two coprime cyclic slope decompositions of the same
isocrystal `(V, Φ)` have the same multiset of slopes
(Kedlaya 2005, §4.5, 4.5.3–4.5.8, pp. 497–499). -/
theorem CyclicSlopeDecomposition.slopes_eq_of_valuation {L V Γ₀ : Type*} [Field L]
    [LinearOrderedCommGroupWithZero Γ₀] [AddCommGroup V] [Module L V] {σ : L ≃+* L}
    {Φ : V →ₛₗ[(σ : L →+* L)] V} {π : L} (v : Valuation L Γ₀) (hv : ∀ x, v (σ x) = v x)
    (hπ : π ≠ 0) (hvπ : v π ≠ 1) (hσπ : σ π = π)
    (D D' : CyclicSlopeDecomposition Φ π) : D.slopes = D'.slopes := by
  classical
  refine Multiset.ext.2 fun q ↦ ?_
  have heq := (isotypicBlockEquiv hv hπ hvπ hσπ D D' q).finrank_eq
  rw [Module.finrank_pi_fintype, Module.finrank_pi_fintype] at heq
  have hden (D₀ : CyclicSlopeDecomposition Φ π)
      (i : {i : Fin D₀.blocks // (D₀.exponent i : ℚ) / (D₀.rank i : ℕ) = q}) :
      Module.finrank L (Fin (D₀.rank i.val) → L) = q.den := by
    rw [Module.finrank_pi, Fintype.card_fin]
    have hcop :
        Nat.Coprime (D₀.exponent i.val).natAbs ((D₀.rank i.val : ℕ) : ℤ).natAbs := by
      simpa using D₀.coprime i.val
    have hr_pos : (0 : ℤ) < (D₀.rank i.val : ℕ) := by exact_mod_cast (D₀.rank i.val).pos
    have hq := Rat.den_div_eq_of_coprime hr_pos hcop
    rw [← Int.natCast_inj]
    simpa [i.property] using hq.symm
  simp_rw [hden D, hden D', Finset.sum_const, Finset.card_univ, Fintype.card_subtype,
    smul_eq_mul] at heq
  rw [D.count_slopes, D'.count_slopes]
  exact Nat.eq_of_mul_eq_mul_right q.den_pos heq

/-- **Dieudonné–Manin classification in equal characteristic.** Over `k((π))` with `k` an
algebraically closed field of characteristic `p > 0` and arithmetic `p^f`-Frobenius (`f > 0`),
every finite isocrystal admits a coprime cyclic block decomposition, and its multiset of block
slopes is unique (Kedlaya 2005, §4.5, 4.5.3–4.5.8, pp. 497–499; Fargues–Fontaine, §8.2.3). -/
theorem dieudonneManinEqualChar (p : ℕ) [Fact p.Prime] (f : ℕ+)
    (k : Type*) [Field k] [CharP k p] [IsAlgClosed k]
    (V : Type*) [AddCommGroup V] [Module (LaurentSeries k) V]
    [FiniteDimensional (LaurentSeries k) V]
    (Φ : V →ₛₗ[(LaurentSeries.coefficientFrobenius (k := k) p f :
      LaurentSeries k →+* LaurentSeries k)] V)
    (hΦ : Function.Bijective Φ) :
    ∃ D : CyclicSlopeDecomposition Φ (HahnSeries.single 1 1),
      ∀ D' : CyclicSlopeDecomposition Φ (HahnSeries.single 1 1), D.slopes = D'.slopes := by
  obtain ⟨D⟩ := CyclicSlopeDecomposition.nonempty f k V Φ hΦ
  exact ⟨D, fun D' ↦ CyclicSlopeDecomposition.slopes_eq_of_valuation Valued.v
    (LaurentSeries.valuation_coefficientFrobenius p f)
    (HahnSeries.single_ne_zero one_ne_zero)
    (LaurentSeries.valuation_single_one_ne_one (K := k))
    (LaurentSeries.coefficientFrobenius_X p f) D D'⟩

/-- **Dieudonné–Manin classification for `FiniteIsocrystal` in equal characteristic.** Every
object `D : FiniteIsocrystal σ` over `k((π))`
(where `σ.toRingEquiv = LaurentSeries.coefficientFrobenius p f`) admits a coprime cyclic slope
decomposition whose slope multiset is unique (Kedlaya 2005, §4.5, 4.5.3–4.5.8, pp. 497–499). -/
theorem FiniteIsocrystal.dieudonneManinEqualChar (p : ℕ) [Fact p.Prime] (f : ℕ+)
    {E k : Type*} [CommRing E] [Field k] [CharP k p] [IsAlgClosed k]
    [Algebra E (LaurentSeries k)] {σ : LaurentSeries k ≃ₐ[E] LaurentSeries k}
    (hσ : σ.toRingEquiv = LaurentSeries.coefficientFrobenius p f)
    (D : FiniteIsocrystal.{u} σ) :
    ∃ dec : CyclicSlopeDecomposition (σ := σ.toRingEquiv) D.frobenius (HahnSeries.single 1 1),
      ∀ dec' : CyclicSlopeDecomposition (σ := σ.toRingEquiv) D.frobenius (HahnSeries.single 1 1),
        dec.slopes = dec'.slopes := by
  have hgen : ∀ {σ₀ : LaurentSeries k ≃+* LaurentSeries k}
      (h : σ₀ = LaurentSeries.coefficientFrobenius p f)
      (Φ : D →ₛₗ[(σ₀ : LaurentSeries k →+* LaurentSeries k)] D),
      Bijective Φ →
        ∃ dec : CyclicSlopeDecomposition Φ (HahnSeries.single 1 1),
          ∀ dec' : CyclicSlopeDecomposition Φ (HahnSeries.single 1 1),
            dec.slopes = dec'.slopes := by
    rintro _ rfl Φ hΦ
    exact TauCeti.dieudonneManinEqualChar p f k D Φ hΦ
  exact hgen hσ D.frobenius D.frobenius_bijective

end Uniqueness

end TauCeti
