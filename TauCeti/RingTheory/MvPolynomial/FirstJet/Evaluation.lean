/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Matrix.Rank
public import Mathlib.LinearAlgebra.Matrix.ToLin
public import TauCeti.RingTheory.MvPolynomial.FirstJet.Algebra
public import TauCeti.RingTheory.MvPolynomial.JetInterpolation
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.Tactic.NormNum

/-!
# Additional properties of bounded first-jet maps, matrices, and well-poised points

This file complements `TauCeti.RingTheory.MvPolynomial.JetInterpolation` with:
* Identification of the coordinates of `TauCeti.firstJetMap` with `TauCeti.jetAlgebra` and its
  kernel with `TauCeti.doubleIdeal` (`TauCeti.mem_ker_firstJetMap_iff_mem_doubleIdeal_of_pairwise`,
  `TauCeti.mem_ker_firstJetMap_iff_mem_doubleIdeal`,
  `TauCeti.wellPoised_iff_surjective_quotientMk`).
* Base-change naturality (`TauCeti.firstJetMap_map`, `TauCeti.firstJetMatrix_map`),
  `LinearMap.toMatrix` representation (`TauCeti.toMatrix_firstJetMap`), reindexing of
  `firstJetMatrix`, and the identification
  `(firstJetMatrix P d).rank = finrank (range (firstJetMap P d))`
  (`TauCeti.rank_firstJetMatrix_eq_finrank_range`).
* Full-column-rank and dimension-bound criteria (`TauCeti.rank_firstJetMatrix_le`,
  `TauCeti.injective_firstJetMap_iff_rank_eq`, `TauCeti.WellPoised.card_mul_le`,
  `TauCeti.WellPoised.injective`).

## References

* J.-M. Couveignes, *Enumerating number fields*, Annals of Mathematics 192 (2020), 487–497, §3.
* M. C. Brambilla and G. Ottaviani, *On the Alexander–Hirschowitz Theorem*, J. Pure Appl. Algebra
  212 (2008), 1229–1251 (arXiv:math/0701409v2), §§1–2.
-/

public section

namespace TauCeti

open Matrix MvPolynomial

section Basic

variable {σ ι κ R S : Type*} [CommSemiring R] [CommSemiring S]

/-- The `none` coordinate of `firstJetMap P d f i` is the scalar component of `jetAlgebra`. -/
theorem firstJetMap_apply_none_eq_fst_jetAlgebra [DecidableEq σ] (P : ι → σ → R) (d : ℕ)
    (f : restrictTotalDegree σ R d) (i : ι) :
    firstJetMap P d f i none = (jetAlgebra (P i) (f : MvPolynomial σ R)).fst := by
  simp

/-- The `some j` coordinate of `firstJetMap P d f i` is the `j`-th infinitesimal component of
`jetAlgebra`. -/
theorem firstJetMap_apply_some_eq_snd_jetAlgebra [DecidableEq σ] (P : ι → σ → R) (d : ℕ)
    (f : restrictTotalDegree σ R d) (i : ι) (j : σ) :
    firstJetMap P d f i (some j) = (jetAlgebra (P i) (f : MvPolynomial σ R)).snd j := by
  simp

/-- A bounded polynomial lies in `LinearMap.ker (firstJetMap P d)` if and only if its value and
all first partial derivatives vanish at every point `P i`. -/
theorem mem_ker_firstJetMap {P : ι → σ → R} {d : ℕ} {f : restrictTotalDegree σ R d} :
    f ∈ LinearMap.ker (firstJetMap P d) ↔
      ∀ i, eval (P i) (f : MvPolynomial σ R) = 0 ∧
        ∀ j, eval (P i) (pderiv j (f : MvPolynomial σ R)) = 0 := by
  rw [LinearMap.mem_ker, _root_.funext_iff]
  simp only [Pi.zero_apply, _root_.funext_iff, Option.forall, firstJetMap_apply_none,
    firstJetMap_apply_some]

/-- Naturality of `firstJetMap` under a change of coefficients `φ : R →+* S`. -/
theorem firstJetMap_map (φ : R →+* S) (P : ι → σ → R) (d : ℕ) (f : restrictTotalDegree σ R d)
    (i : ι) (z : Option σ) :
    firstJetMap (fun i ↦ φ ∘ P i) d
        ⟨map φ (f : MvPolynomial σ R),
          (restrictTotalDegree_eq_restrictSupport σ S d).symm ▸
            map_mem_restrictSupport φ ((restrictTotalDegree_eq_restrictSupport σ R d) ▸ f.property)⟩
        i z =
      φ (firstJetMap P d f i z) := by
  cases z with
  | none =>
    rw [firstJetMap_apply_none, firstJetMap_apply_none, eval_map]
    exact (hom_eval₂ f.val (RingHom.id R) φ (P i)).symm
  | some j =>
    rw [firstJetMap_apply_some, firstJetMap_apply_some, pderiv_map, eval_map]
    exact (hom_eval₂ (pderiv j f.val) (RingHom.id R) φ (P i)).symm

/-- `firstJetMatrix P d` is the matrix of `firstJetMap P d` (uncurried) in the monomial basis of
`restrictTotalDegree σ R d` and the standard basis of `ι × Option σ → R`. -/
theorem toMatrix_firstJetMap [Finite σ] [Finite ι] {d : ℕ}
    [Fintype {a : σ →₀ ℕ // a.degree ≤ d}] [DecidableEq {a : σ →₀ ℕ // a.degree ≤ d}]
    (P : ι → σ → R) :
    LinearMap.toMatrix (basisRestrictTotalDegree σ R d) (Pi.basisFun R (ι × Option σ))
      ((LinearEquiv.curry R R ι (Option σ)).symm.toLinearMap ∘ₗ firstJetMap P d) =
      firstJetMatrix P d := by
  ext ⟨i, z⟩ a
  simp [LinearMap.toMatrix_apply, firstJetMap_basisRestrictTotalDegree]

/-- Naturality of `firstJetMatrix` under a ring homomorphism `φ : R →+* S`. -/
theorem firstJetMatrix_map (φ : R →+* S) (P : ι → σ → R) (d : ℕ) :
    firstJetMatrix (fun i ↦ φ ∘ P i) d = (firstJetMatrix P d).map φ := by
  ext ⟨i, z⟩ a
  cases z with
  | none => simp [Finsupp.prod]
  | some j => simp [Finsupp.prod]

/-- Reindexing points along an equivalence permutes the rows of `firstJetMatrix`. -/
theorem firstJetMatrix_comp_equiv (P : ι → σ → R) (e : κ ≃ ι) (d : ℕ) :
    firstJetMatrix (P ∘ e) d = (firstJetMatrix P d).submatrix (Prod.map e id) id := by
  ext ⟨j, z⟩ a
  cases z <;> simp

/-- The rank of `firstJetMatrix P d` equals the `finrank` of the range of `firstJetMap P d`. -/
theorem rank_firstJetMatrix_eq_finrank_range [Finite σ] {d : ℕ} (P : ι → σ → R) :
    (firstJetMatrix P d).rank = Module.finrank R (LinearMap.range (firstJetMap P d)) := by
  have := Fintype.ofFinite σ
  classical
  let eDom : restrictTotalDegree σ R d ≃ₗ[R] ({a : σ →₀ ℕ // a.degree ≤ d} → R) :=
    (basisRestrictTotalDegree σ R d).equivFun
  let eCod : (ι × Option σ → R) ≃ₗ[R] (ι → Option σ → R) := LinearEquiv.curry R R ι (Option σ)
  have hcomp : firstJetMap P d =
      eCod.toLinearMap ∘ₗ (firstJetMatrix P d).mulVecLin ∘ₗ eDom.toLinearMap := by
    ext f i z
    have h1 := congrFun (firstJetMatrix_mulVec P d f) (i, z)
    simpa [eDom, eCod] using h1.symm
  have hrange : LinearMap.range (firstJetMap P d) =
      (LinearMap.range (firstJetMatrix P d).mulVecLin).map eCod.toLinearMap := by
    rw [hcomp, LinearMap.range_comp, LinearMap.range_comp_of_range_eq_top _ eDom.range]
  rw [← Matrix.finrank_range_mulVecLin, hrange]
  exact (eCod.submoduleMap (LinearMap.range (firstJetMatrix P d).mulVecLin)).finrank_eq

/-- Reindexing points along an equivalence preserves the rank of `firstJetMatrix`. -/
theorem rank_firstJetMatrix_comp_equiv [Finite σ] {d : ℕ} (P : ι → σ → R) (e : κ ≃ ι) :
    (firstJetMatrix (P ∘ e) d).rank = (firstJetMatrix P d).rank := by
  rw [rank_firstJetMatrix_eq_finrank_range, rank_firstJetMatrix_eq_finrank_range]
  let eCod : (ι → Option σ → R) ≃ₗ[R] (κ → Option σ → R) :=
    LinearEquiv.funCongrLeft R (Option σ → R) e
  have hcomp : firstJetMap (P ∘ e) d = eCod.toLinearMap ∘ₗ firstJetMap P d := by
    rw [firstJetMap_comp]
    rfl
  rw [hcomp, LinearMap.range_comp]
  exact (eCod.submoduleMap (LinearMap.range (firstJetMap P d))).finrank_eq.symm

end Basic

section CommRing

variable {σ ι R : Type*} [CommRing R]

/-- For a finite family of points with pairwise comaximal evaluation ideals, a bounded polynomial
lies in the kernel of `firstJetMap P d` if and only if it lies in `doubleIdeal P`. -/
theorem mem_ker_firstJetMap_iff_mem_doubleIdeal_of_pairwise [Finite ι] {P : ι → σ → R}
    (hP : Pairwise (Function.onFun IsCoprime fun i ↦ RingHom.ker (eval (P i)))) {d : ℕ}
    {f : restrictTotalDegree σ R d} :
    f ∈ LinearMap.ker (firstJetMap P d) ↔ (f : MvPolynomial σ R) ∈ doubleIdeal P := by
  rw [mem_ker_firstJetMap, mem_doubleIdeal_iff_of_pairwise hP]

end CommRing

section WellPoised

variable {σ ι κ R : Type*} [CommSemiring R]

/-- For pairwise comaximal point ideals in finitely many variables, well-poisedness in degree `d`
is equivalent to surjectivity of the quotient map
`MvPolynomial σ R → MvPolynomial σ R ⧸ doubleIdeal P` restricted to `restrictTotalDegree σ R d`. -/
theorem wellPoised_iff_surjective_quotientMk_of_pairwise {R : Type*} [CommRing R]
    [Finite σ] [Finite ι] {P : ι → σ → R}
    (hP : Pairwise (Function.onFun IsCoprime fun i ↦ RingHom.ker (eval (P i)))) (d : ℕ) :
    WellPoised P d ↔
      Function.Surjective
        ((Ideal.Quotient.mkₐ R (doubleIdeal P)).toLinearMap ∘ₗ
          (restrictTotalDegree σ R d).subtype) := by
  classical
  let e : (ι → TrivSqZeroExt R (σ → R)) ≃ₗ[R] (ι → Option σ → R) :=
    { toFun := fun v i z ↦ z.elim (v i).fst (v i).snd
      invFun := fun y i ↦ TrivSqZeroExt.inl (y i none) + TrivSqZeroExt.inr fun j ↦ y i (some j)
      left_inv := fun v ↦ _root_.funext fun i ↦ by ext <;> simp
      right_inv := fun y ↦ _root_.funext fun i ↦ _root_.funext fun z ↦ by cases z <;> simp
      map_add' := fun _ _ ↦ _root_.funext fun _ ↦ _root_.funext fun z ↦ by cases z <;> rfl
      map_smul' := fun _ _ ↦ _root_.funext fun _ ↦ _root_.funext fun z ↦ by cases z <;> rfl }
  have hcomp : firstJetMap P d =
      e.toLinearMap ∘ₗ (doublePointQuotientEquivOfPairwise hP).toLinearMap ∘ₗ
        (Ideal.Quotient.mkₐ R (doubleIdeal P)).toLinearMap ∘ₗ
        (restrictTotalDegree σ R d).subtype := by
    ext f i z
    cases z <;> simp [e]
  rw [wellPoised_iff, hcomp]
  refine ⟨fun hs y ↦ ?_,
    fun hs ↦ e.surjective.comp ((doublePointQuotientEquivOfPairwise hP).surjective.comp hs)⟩
  obtain ⟨f, hf⟩ := hs (e (doublePointQuotientEquivOfPairwise hP y))
  exact ⟨f, (doublePointQuotientEquivOfPairwise hP).injective (e.injective hf)⟩

/-- Reindexing a point tuple along an equivalence preserves well-poisedness. -/
theorem WellPoised.comp_equiv {P : ι → σ → R} {d : ℕ} (h : WellPoised P d) (e : κ ≃ ι) :
    WellPoised (P ∘ e) d :=
  h.comp_injective e.injective

/-- Over a nontrivial commutative semiring, a well-poised tuple must consist of distinct points. -/
theorem WellPoised.injective [Nontrivial R] {P : ι → σ → R} {d : ℕ} (h : WellPoised P d) :
    Function.Injective P := by
  classical
  intro i j hij
  by_contra hne
  obtain ⟨f, hf⟩ := (wellPoised_iff.1 h) (Function.update 0 i fun _ ↦ 1)
  have hi : eval (P i) (f : MvPolynomial σ R) = 1 := by
    simpa using congrFun (congrFun hf i) none
  have hj : eval (P j) (f : MvPolynomial σ R) = 0 := by
    simpa [Function.update_of_ne (Ne.symm hne)] using congrFun (congrFun hf j) none
  rw [hij, hj] at hi
  exact zero_ne_one hi

/-- The empty tuple is well poised in every degree. -/
theorem wellPoised_of_isEmpty [IsEmpty ι] (P : ι → σ → R) (d : ℕ) : WellPoised P d :=
  wellPoised_iff.2 fun _ ↦ ⟨0, _root_.funext fun i ↦ isEmptyElim i⟩

end WellPoised

section Field

variable {σ ι k : Type*} [Field k]

/-- Over a field, for a finite injective tuple `P`, a bounded polynomial lies in the kernel of
`firstJetMap P d` if and only if it lies in `doubleIdeal P`. -/
theorem mem_ker_firstJetMap_iff_mem_doubleIdeal [Finite ι] {P : ι → σ → k}
    (hP : Function.Injective P) {d : ℕ} {f : restrictTotalDegree σ k d} :
    f ∈ LinearMap.ker (firstJetMap P d) ↔ (f : MvPolynomial σ k) ∈ doubleIdeal P :=
  mem_ker_firstJetMap_iff_mem_doubleIdeal_of_pairwise
    (fun _ _ hij ↦ isCoprime_ker_eval (hP.ne hij))

/-- Over a field, a finite injective tuple `P` is well poised in degree `d` if and only if the
quotient map `MvPolynomial σ k → MvPolynomial σ k ⧸ doubleIdeal P` is surjective on
`restrictTotalDegree σ k d`. -/
theorem wellPoised_iff_surjective_quotientMk [Finite σ] [Finite ι] {P : ι → σ → k}
    (hP : Function.Injective P) (d : ℕ) :
    WellPoised P d ↔
      Function.Surjective
        ((Ideal.Quotient.mkₐ k (doubleIdeal P)).toLinearMap ∘ₗ
          (restrictTotalDegree σ k d).subtype) :=
  wellPoised_iff_surjective_quotientMk_of_pairwise
    (fun _ _ hij ↦ isCoprime_ker_eval (hP.ne hij)) d

/-- The rank of `firstJetMatrix P d` is bounded above by the minimum of the source polynomial
dimension `(d + r choose r)` and the target jet dimension `n * (r + 1)`. -/
theorem rank_firstJetMatrix_le [Fintype σ] [Fintype ι] {d : ℕ} (P : ι → σ → k) :
    (firstJetMatrix P d).rank ≤
      min ((d + Fintype.card σ).choose (Fintype.card σ))
        (Fintype.card ι * (Fintype.card σ + 1)) := by
  classical
  have : Module.Finite k (restrictTotalDegree σ k d) :=
    Module.Finite.of_basis (basisRestrictTotalDegree σ k d)
  rw [rank_firstJetMatrix_eq_finrank_range]
  refine le_min ?_ ?_
  · have hrn := LinearMap.finrank_range_add_finrank_ker (firstJetMap P d)
    have hdom : Module.finrank k (restrictTotalDegree σ k d) =
        (d + Fintype.card σ).choose (Fintype.card σ) :=
      TauCeti.finrank_restrictTotalDegree σ k d
    omega
  · calc
      Module.finrank k (LinearMap.range (firstJetMap P d))
        ≤ Module.finrank k (ι → Option σ → k) := Submodule.finrank_le _
      _ = Fintype.card ι * (Fintype.card σ + 1) := by
        simp [Module.finrank_pi_fintype, Fintype.card_option]

/-- **Full row rank criterion.** Over a field, `firstJetMap P d` is surjective if and only if
`firstJetMatrix P d` has rank `Fintype.card ι * (Fintype.card σ + 1)`. -/
theorem surjective_firstJetMap_iff_rank_eq [Fintype σ] [Fintype ι] {d : ℕ} (P : ι → σ → k) :
    Function.Surjective (firstJetMap P d) ↔
      (firstJetMatrix P d).rank = Fintype.card ι * (Fintype.card σ + 1) := by
  rw [← wellPoised_iff, wellPoised_iff_rank]

/-- **Full column rank criterion.** Over a field, `firstJetMap P d` is injective if and only if
`firstJetMatrix P d` has rank `(d + Fintype.card σ).choose (Fintype.card σ)`. -/
theorem injective_firstJetMap_iff_rank_eq [Fintype σ] {d : ℕ} (P : ι → σ → k) :
    Function.Injective (firstJetMap P d) ↔
      (firstJetMatrix P d).rank = (d + Fintype.card σ).choose (Fintype.card σ) := by
  classical
  have : Module.Finite k (restrictTotalDegree σ k d) :=
    Module.Finite.of_basis (basisRestrictTotalDegree σ k d)
  rw [← LinearMap.ker_eq_bot, rank_firstJetMatrix_eq_finrank_range]
  have hrn := LinearMap.finrank_range_add_finrank_ker (firstJetMap P d)
  have hdom : Module.finrank k (restrictTotalDegree σ k d) =
      (d + Fintype.card σ).choose (Fintype.card σ) :=
    TauCeti.finrank_restrictTotalDegree σ k d
  constructor
  · intro hker
    rw [hker, finrank_bot, add_zero] at hrn
    exact hrn.trans hdom
  · intro hrank
    have hker0 : Module.finrank k (LinearMap.ker (firstJetMap P d)) = 0 := by omega
    exact Submodule.finrank_eq_zero.1 hker0

/-- **Necessary dimension bound for well-poisedness.** If `P` is well poised in degree `d`, then
`Fintype.card ι * (Fintype.card σ + 1) ≤ (d + Fintype.card σ).choose (Fintype.card σ)`. -/
theorem WellPoised.card_mul_le [Fintype σ] [Fintype ι] {P : ι → σ → k} {d : ℕ}
    (h : WellPoised P d) :
    Fintype.card ι * (Fintype.card σ + 1) ≤ (d + Fintype.card σ).choose (Fintype.card σ) := by
  classical
  have hle := rank_firstJetMatrix_le (d := d) P
  rw [(wellPoised_iff_rank).1 h] at hle
  exact (le_min_iff.1 hle).1

end Field

/-! ### Examples -/

/-- For `f = X 0 ^ 2` at `P = 3` in `𝔸¹`, the first jet is `(9, 6)`. -/
example :
    let P : Fin 1 → Fin 1 → ℚ := fun _ _ ↦ 3
    let f : restrictTotalDegree (Fin 1) ℚ 2 :=
      ⟨X 0 ^ 2, (mem_restrictTotalDegree (Fin 1) 2 _).2 <|
        (totalDegree_pow _ _).trans (by simp [totalDegree_X])⟩
    firstJetMap P 2 f 0 none = 9 ∧ firstJetMap P 2 f 0 (some 0) = 6 := by
  intro P f
  refine ⟨?_, ?_⟩
  · simp [P, f]
    norm_num
  · simp [P, f, sq]
    norm_num

/-- One point at the origin in `𝔸²` is well poised in degree `1` and has first-jet rank `3`. -/
example :
    let P : Fin 1 → Fin 2 → ℚ := fun _ _ ↦ 0
    WellPoised P 1 ∧ (firstJetMatrix P 1).rank = 3 := by
  intro P
  have hw : WellPoised P 1 := wellPoised_of_subsingleton P le_rfl
  exact ⟨hw, by simpa using (wellPoised_iff_rank).1 hw⟩

end TauCeti
