/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.CStarAlgebra.FiniteDimensional.Basic
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.Matrix.Diagonal
import TauCeti.RingTheory.Idempotents.Matrix

/-!
# Low-dimensional complex C⋆-algebras and nonunital matrix embeddings

Applying the matrix-block `⋆`-decomposition `TauCeti.CStarWedderburnPresentation` from
`TauCeti.Analysis.CStarAlgebra.FiniteDimensional.Basic`, this file establishes rank bounds on
orthogonal idempotents in finite-dimensional C⋆-algebras, characterizes when the commutative
algebra `Fin m → ℂ` embeds (possibly nonunitally) into `CStarMatrix (Fin n) (Fin n) ℂ`, and
classifies complex C⋆-algebras of dimension at most `4`:

* Every complex C⋆-algebra of dimension `< 4` is commutative and `⋆`-isomorphic to
  `Fin (Module.finrank ℂ A) → ℂ`; in particular dimensions `1`, `2`, and `3` each admit a unique
  `⋆`-isomorphism class (`ℂ`, `Fin 2 → ℂ`, and `Fin 3 → ℂ`).
* No `3`-dimensional complex C⋆-algebra admits an injective `NonUnitalStarAlgHom` into
  `CStarMatrix (Fin 2) (Fin 2) ℂ`, even without unitality, and no `⋆`-subalgebra of
  `CStarMatrix (Fin 2) (Fin 2) ℂ` has complex dimension `3`.
* Every `4`-dimensional complex C⋆-algebra is `⋆`-isomorphic either to `Fin 4 → ℂ` or to
  `CStarMatrix (Fin 2) (Fin 2) ℂ`; these two are not `⋆`-isomorphic, making `4` the least complex
  dimension admitting two non-`⋆`-isomorphic C⋆-algebras.

## Main results

* `CStarMatrix.card_orthogonalIdempotents_le`,
  `TauCeti.CStarWedderburnPresentation.card_orthogonalIdempotents_le`: cardinality bounds on
  families of pairwise orthogonal nonzero idempotents.
* `CStarAlgebra.exists_injective_nonUnitalStarAlgHom_cstarMatrix_iff`: `Fin m → ℂ` embeds as a
  nonunital `⋆`-algebra into `CStarMatrix (Fin n) (Fin n) ℂ` if and only if `m ≤ n`.
* `CStarAlgebra.isMulCommutative_of_finrank_lt_four`,
  `CStarAlgebra.nonempty_starAlgEquiv_fun_of_finrank_lt_four`,
  `CStarAlgebra.nonempty_starAlgEquiv_of_finrank_eq_of_lt_four`: commutativity and uniqueness of
  `⋆`-isomorphism class below dimension `4`.
* `CStarAlgebra.not_injective_nonUnitalStarAlgHom_cstarMatrix_two_of_finrank_eq_three`,
  `CStarMatrix.finrank_ne_three_of_nonUnitalStarSubalgebra`: non-embeddability of `ℂ³` into
  `M₂(ℂ)`.
* `CStarAlgebra.nonempty_starAlgEquiv_of_finrank_eq_four`,
  `CStarAlgebra.isEmpty_starAlgEquiv_fin_four_cstarMatrix_two`,
  `CStarAlgebra.isLeast_finrank_exists_isEmpty_starAlgEquiv`: classification in dimension `4` and
  minimality of dimension `4` for non-`⋆`-isomorphic pairs.
-/

public section

open scoped BigOperators ComplexOrder

universe u v

/-! ### Orthogonal idempotent bounds and nonunital commutative embeddings -/

/-- A finite family of pairwise orthogonal nonzero idempotents in `CStarMatrix n n ℂ` has
cardinality at most `Fintype.card n`. -/
theorem CStarMatrix.card_orthogonalIdempotents_le {ι n : Type*} [Fintype ι] [Fintype n]
    [DecidableEq n] {e : ι → CStarMatrix n n ℂ} (he : OrthogonalIdempotents e)
    (hne : ∀ i, e i ≠ 0) : Fintype.card ι ≤ Fintype.card n := by
  let φ : CStarMatrix n n ℂ →+* Matrix n n ℂ :=
    CStarMatrix.ofMatrixStarAlgEquiv.symm.toRingEquiv.toRingHom
  refine (he.map φ).card_le_of_matrix fun i h ↦ hne i ?_
  exact EquivLike.injective CStarMatrix.ofMatrixStarAlgEquiv.symm
    (h.trans (map_zero CStarMatrix.ofMatrixStarAlgEquiv.symm).symm)

/-- Pushing the coordinate projections `Pi.single k 1` of `Fin m → ℂ` along an injective
nonunital algebra homomorphism yields `m` pairwise orthogonal nonzero idempotents. -/
private theorem orthogonalIdempotents_map_single {A F : Type*} [Semiring A] [Module ℂ A] {m : ℕ}
    [FunLike F (Fin m → ℂ) A] [NonUnitalAlgHomClass F ℂ (Fin m → ℂ) A] (φ : F)
    (hφ : Function.Injective φ) :
    OrthogonalIdempotents (fun k : Fin m ↦ φ (Pi.single k 1)) ∧
      ∀ k : Fin m, φ (Pi.single k 1) ≠ 0 := by
  refine ⟨⟨fun k ↦ ?_, fun k₁ k₂ hk ↦ ?_⟩, fun k h ↦ ?_⟩
  · rw [IsIdempotentElem, ← map_mul, ← Pi.single_mul, one_mul]
  · dsimp only
    have hzero : (Pi.single k₁ (1 : ℂ) * Pi.single k₂ 1 : Fin m → ℂ) = 0 := by
      ext j
      by_cases h1 : k₁ = j
      · subst h1; simp [hk]
      · simp [h1]
    rw [← map_mul, hzero, map_zero]
  · have hk0 : (Pi.single k (1 : ℂ) : Fin m → ℂ) = 0 := hφ (h.trans (map_zero φ).symm)
    exact one_ne_zero (α := ℂ) (by simpa using congrFun hk0 k)

namespace TauCeti.CStarWedderburnPresentation

/-- In an algebra admitting a `CStarWedderburnPresentation`, any finite family of pairwise
orthogonal nonzero idempotents has cardinality at most `∑ i, P.degree i`. -/
theorem card_orthogonalIdempotents_le {A : Type u} [Semiring A] [SMul ℂ A] [Star A]
    (P : CStarWedderburnPresentation A) {ι : Type*} [Fintype ι] {e : ι → A}
    (he : OrthogonalIdempotents e) (hne : ∀ k, e k ≠ 0) :
    Fintype.card ι ≤ ∑ i, P.degree i := by
  classical
  let S (i : Fin P.blockCount) := {k : ι // P.matrixStarAlgEquiv (e k) i ≠ 0}
  have hcard (i : Fin P.blockCount) : Fintype.card (S i) ≤ P.degree i := by
    let φ_i : A →+* Matrix (Fin (P.degree i)) (Fin (P.degree i)) ℂ :=
      (Pi.evalRingHom _ i).comp P.matrixStarAlgEquiv.toRingEquiv.toRingHom
    have he_i : OrthogonalIdempotents (fun k : S i ↦ φ_i (e k.1)) :=
      (he.map φ_i).embedding ⟨Subtype.val, Subtype.val_injective⟩
    simpa only [Fintype.card_fin] using he_i.card_le_of_matrix fun k ↦ k.2
  have hex (k : ι) : ∃ i, P.matrixStarAlgEquiv (e k) i ≠ 0 := by
    refine Function.ne_iff.mp fun h ↦ hne k (EquivLike.injective P.matrixStarAlgEquiv ?_)
    exact h.trans (map_zero P.matrixStarAlgEquiv).symm
  let g : ι → Σ i, S i := fun k ↦ ⟨(hex k).choose, ⟨k, (hex k).choose_spec⟩⟩
  have hg : Function.Injective g := fun _ _ h ↦ congrArg (fun x ↦ x.2.1) h
  calc
    Fintype.card ι ≤ Fintype.card (Σ i, S i) := Fintype.card_le_of_injective g hg
    _ = ∑ i, Fintype.card (S i) := Fintype.card_sigma
    _ ≤ ∑ i, P.degree i := Finset.sum_le_sum fun i _ ↦ hcard i

/-- If `Fin m → ℂ` embeds via a (possibly nonunital) `⋆`-algebra homomorphism into `A`, then `m`
is bounded by the sum of the matrix block degrees of any `CStarWedderburnPresentation` of `A`. -/
theorem le_sum_degree_of_injective_nonUnitalStarAlgHom {A : Type u} [Semiring A] [Module ℂ A]
    [Star A] (P : CStarWedderburnPresentation A) {m : ℕ} (φ : (Fin m → ℂ) →⋆ₙₐ[ℂ] A)
    (hφ : Function.Injective φ) : m ≤ ∑ i, P.degree i := by
  obtain ⟨he, hne⟩ := orthogonalIdempotents_map_single φ hφ
  simpa only [Fintype.card_fin] using P.card_orthogonalIdempotents_le he hne

end TauCeti.CStarWedderburnPresentation

namespace CStarAlgebra

/-- The finite-dimensional commutative C⋆-algebra `Fin m → ℂ` admits an injective (possibly
nonunital) `⋆`-algebra homomorphism into `CStarMatrix (Fin n) (Fin n) ℂ` if and only if `m ≤ n`. -/
theorem exists_injective_nonUnitalStarAlgHom_cstarMatrix_iff {m n : ℕ} :
    (∃ φ : (Fin m → ℂ) →⋆ₙₐ[ℂ] CStarMatrix (Fin n) (Fin n) ℂ, Function.Injective φ) ↔ m ≤ n := by
  refine ⟨fun ⟨φ, hφ⟩ ↦ ?_, fun hmn ↦ ?_⟩
  · obtain ⟨he, hne⟩ := orthogonalIdempotents_map_single φ hφ
    simpa only [Fintype.card_fin] using CStarMatrix.card_orthogonalIdempotents_le he hne
  · let trunc (f : Fin m → ℂ) (j : Fin n) : ℂ := if h : j.1 < m then f ⟨j.1, h⟩ else 0
    let φ : (Fin m → ℂ) →⋆ₙₐ[ℂ] CStarMatrix (Fin n) (Fin n) ℂ :=
      { toFun f := CStarMatrix.ofMatrix (Matrix.diagonal (trunc f))
        map_smul' r f := by
          ext i j
          by_cases hij : i = j
          · subst hij; by_cases hi : i.1 < m <;> simp [trunc, Matrix.diagonal, hi]
          · simp [Matrix.diagonal, hij]
        map_zero' := by
          ext i j
          by_cases hij : i = j <;> simp [trunc, Matrix.diagonal, hij]
        map_add' f g := by
          ext i j
          by_cases hij : i = j
          · subst hij; by_cases hi : i.1 < m <;> simp [trunc, Matrix.diagonal, hi]
          · simp [Matrix.diagonal, hij]
        map_mul' f g := by
          have hmul : trunc f * trunc g = trunc (f * g) := by
            ext j
            by_cases hj : j.1 < m <;> simp [trunc, hj]
          exact congrArg CStarMatrix.ofMatrix
            ((Matrix.diagonal_mul_diagonal (trunc f) (trunc g)).trans
              (congrArg Matrix.diagonal hmul)).symm
        map_star' f := by
          ext i j
          rw [CStarMatrix.star_apply]
          by_cases hij : i = j
          · subst hij; by_cases hi : i.1 < m <;> simp [trunc, Matrix.diagonal, hi]
          · simp [Matrix.diagonal, hij, Ne.symm hij] }
    refine ⟨φ, fun f g hfg ↦ ?_⟩
    ext k
    let j : Fin n := ⟨k.1, k.2.trans_le hmn⟩
    simpa [φ, trunc, j, Matrix.diagonal, k.2] using congrFun (congrFun hfg j) j

/-! ### Classification in complex dimensions below `4` -/

section BelowFour

variable {A : Type u} [NonUnitalCStarAlgebra A] [FiniteDimensional ℂ A]

/-- Every complex C⋆-algebra of dimension strictly less than `4` is multiplicatively commutative. -/
theorem isMulCommutative_of_finrank_lt_four (h : Module.finrank ℂ A < 4) :
    IsMulCommutative A := by
  let P := cstarWedderburnPresentation A
  refine P.isMulCommutative_iff_forall_degree_eq_one.mpr fun i ↦ ?_
  have hsq : P.degree i ^ 2 < 4 := (P.sq_degree_le_finrank i).trans_lt h
  have hge : 1 ≤ P.degree i := P.one_le_degree i
  nlinarith

/-- Every complex C⋆-algebra of dimension `< 4` is `⋆`-isomorphic to
`Fin (Module.finrank ℂ A) → ℂ`. -/
theorem nonempty_starAlgEquiv_fun_of_finrank_lt_four (h : Module.finrank ℂ A < 4) :
    Nonempty (A ≃⋆ₐ[ℂ] (Fin (Module.finrank ℂ A) → ℂ)) :=
  (isMulCommutative_iff_nonempty_starAlgEquiv_fun A).mp (isMulCommutative_of_finrank_lt_four h)

/-- Any two complex C⋆-algebras of the same complex dimension `< 4` are `⋆`-algebra isomorphic. -/
theorem nonempty_starAlgEquiv_of_finrank_eq_of_lt_four {B : Type v} [NonUnitalCStarAlgebra B]
    [FiniteDimensional ℂ B] (hAB : Module.finrank ℂ A = Module.finrank ℂ B)
    (h : Module.finrank ℂ A < 4) : Nonempty (A ≃⋆ₐ[ℂ] B) := by
  obtain ⟨eA⟩ := nonempty_starAlgEquiv_fun_of_finrank_lt_four h
  obtain ⟨eB⟩ := nonempty_starAlgEquiv_fun_of_finrank_lt_four (hAB ▸ h)
  exact ⟨eA.trans ((StarAlgEquiv.piCongrLeft ℂ (fun _ ↦ ℂ) (finCongr hAB)).trans eB.symm)⟩

/-- Every `1`-dimensional complex C⋆-algebra is `⋆`-isomorphic to `ℂ`. -/
theorem nonempty_starAlgEquiv_complex_of_finrank_eq_one (h : Module.finrank ℂ A = 1) :
    Nonempty (A ≃⋆ₐ[ℂ] ℂ) := by
  obtain ⟨e⟩ := nonempty_starAlgEquiv_fun_of_finrank_lt_four (by omega : Module.finrank ℂ A < 4)
  exact ⟨e.trans ((StarAlgEquiv.piCongrLeft ℂ (fun _ ↦ ℂ) (finCongr h)).trans
    (StarAlgEquiv.funUnique ℂ (Fin 1) ℂ))⟩

/-- Every `2`-dimensional complex C⋆-algebra is `⋆`-isomorphic to `Fin 2 → ℂ`. -/
theorem nonempty_starAlgEquiv_fin_two_of_finrank_eq_two (h : Module.finrank ℂ A = 2) :
    Nonempty (A ≃⋆ₐ[ℂ] (Fin 2 → ℂ)) := by
  obtain ⟨e⟩ := nonempty_starAlgEquiv_fun_of_finrank_lt_four (by omega : Module.finrank ℂ A < 4)
  exact ⟨e.trans (StarAlgEquiv.piCongrLeft ℂ (fun _ ↦ ℂ) (finCongr h))⟩

/-- Every `3`-dimensional complex C⋆-algebra is `⋆`-isomorphic to `Fin 3 → ℂ`. -/
theorem nonempty_starAlgEquiv_fin_three_of_finrank_eq_three (h : Module.finrank ℂ A = 3) :
    Nonempty (A ≃⋆ₐ[ℂ] (Fin 3 → ℂ)) := by
  obtain ⟨e⟩ := nonempty_starAlgEquiv_fun_of_finrank_lt_four (by omega : Module.finrank ℂ A < 4)
  exact ⟨e.trans (StarAlgEquiv.piCongrLeft ℂ (fun _ ↦ ℂ) (finCongr h))⟩

/-- **No `3`-dimensional complex C⋆-algebra embeds into `M₂(ℂ)`, even nonunitally**: any
`NonUnitalStarAlgHom` from `A` into `CStarMatrix (Fin 2) (Fin 2) ℂ` fails to be injective. -/
theorem not_injective_nonUnitalStarAlgHom_cstarMatrix_two_of_finrank_eq_three
    (h : Module.finrank ℂ A = 3) (φ : A →⋆ₙₐ[ℂ] CStarMatrix (Fin 2) (Fin 2) ℂ) :
    ¬Function.Injective φ := by
  obtain ⟨e⟩ := nonempty_starAlgEquiv_fin_three_of_finrank_eq_three h
  intro hφ
  have hex : ∃ ψ : (Fin 3 → ℂ) →⋆ₙₐ[ℂ] CStarMatrix (Fin 2) (Fin 2) ℂ, Function.Injective ψ :=
    ⟨φ.comp e.symm.toNonUnitalStarAlgHom, hφ.comp e.symm.injective⟩
  have hle : 3 ≤ 2 := exists_injective_nonUnitalStarAlgHom_cstarMatrix_iff.mp hex
  omega

end BelowFour

end CStarAlgebra

/-- No `⋆`-subalgebra (unital or not) of `CStarMatrix (Fin 2) (Fin 2) ℂ` has complex dimension
`3`. -/
theorem CStarMatrix.finrank_ne_three_of_nonUnitalStarSubalgebra
    (S : NonUnitalStarSubalgebra ℂ (CStarMatrix (Fin 2) (Fin 2) ℂ)) :
    Module.finrank ℂ S ≠ 3 := by
  have : FiniteDimensional ℂ (CStarMatrix (Fin 2) (Fin 2) ℂ) :=
    Module.Finite.equiv CStarMatrix.ofMatrixₗ
  have : FiniteDimensional ℂ S :=
    Module.Finite.of_injective S.toSubmodule.subtype Subtype.val_injective
  have : IsClosed (S : Set (CStarMatrix (Fin 2) (Fin 2) ℂ)) :=
    S.toSubmodule.isClosed_of_finiteDimensional
  let _ : NonUnitalCStarAlgebra S := NonUnitalStarSubalgebra.nonUnitalCStarAlgebra S
  intro hdim
  exact CStarAlgebra.not_injective_nonUnitalStarAlgHom_cstarMatrix_two_of_finrank_eq_three hdim
    (NonUnitalStarSubalgebraClass.subtype S) Subtype.val_injective

/-! ### Classification in dimension `4` and least nonisomorphic dimension -/

/-- `CStarMatrix (Fin 2) (Fin 2) ℂ` is not multiplicatively commutative. -/
theorem CStarMatrix.not_isMulCommutative_two :
    ¬IsMulCommutative (CStarMatrix (Fin 2) (Fin 2) ℂ) := by
  intro hcomm
  let x : CStarMatrix (Fin 2) (Fin 2) ℂ := CStarMatrix.ofMatrix (Matrix.single 0 1 1)
  let y : CStarMatrix (Fin 2) (Fin 2) ℂ := CStarMatrix.ofMatrix (Matrix.single 1 0 1)
  have hxy := congrFun (congrFun (hcomm.is_comm.comm x y) 0) 0
  simp [x, y, CStarMatrix.mul_apply, Matrix.single_apply] at hxy

namespace CStarAlgebra

/-- **Classification in dimension `4`**: every `4`-dimensional complex C⋆-algebra is `⋆`-isomorphic
either to `Fin 4 → ℂ` or to `CStarMatrix (Fin 2) (Fin 2) ℂ`. -/
theorem nonempty_starAlgEquiv_of_finrank_eq_four {A : Type u} [NonUnitalCStarAlgebra A]
    [FiniteDimensional ℂ A] (h : Module.finrank ℂ A = 4) :
    Nonempty (A ≃⋆ₐ[ℂ] (Fin 4 → ℂ)) ∨ Nonempty (A ≃⋆ₐ[ℂ] CStarMatrix (Fin 2) (Fin 2) ℂ) := by
  let P := cstarWedderburnPresentation A
  by_cases hall : ∀ i, P.degree i = 1
  · have : IsMulCommutative A := P.isMulCommutative_iff_forall_degree_eq_one.mpr hall
    obtain ⟨e⟩ := (isMulCommutative_iff_nonempty_starAlgEquiv_fun A).mp inferInstance
    exact Or.inl ⟨e.trans (StarAlgEquiv.piCongrLeft ℂ (fun _ ↦ ℂ) (finCongr h))⟩
  · obtain ⟨i₀, hi₀⟩ := not_forall.mp hall
    have hge₂ : 2 ≤ P.degree i₀ := lt_of_le_of_ne (P.one_le_degree i₀) (Ne.symm hi₀)
    have hsq_le : P.degree i₀ ^ 2 ≤ 4 := h ▸ P.sq_degree_le_finrank i₀
    have hd₂ : P.degree i₀ = 2 := by nlinarith
    have hsum : ∑ j : Fin P.blockCount, P.degree j ^ 2 = 4 := P.finrank_eq_sum_sq.symm.trans h
    have herase : ∑ j ∈ Finset.univ.erase i₀, P.degree j ^ 2 = 0 := by
      have hsplit := Finset.add_sum_erase Finset.univ (fun j ↦ P.degree j ^ 2) (Finset.mem_univ i₀)
      rw [hsum, hd₂] at hsplit
      omega
    have hunique_idx : ∀ j : Fin P.blockCount, j = i₀ := by
      intro j
      by_contra hne
      have hmem : j ∈ Finset.univ.erase i₀ := Finset.mem_erase.mpr ⟨hne, Finset.mem_univ j⟩
      have hzero : P.degree j ^ 2 = 0 :=
        (Finset.sum_eq_zero_iff.mp herase) j hmem
      have hpos : 1 ≤ P.degree j := P.one_le_degree j
      nlinarith
    let _ : Unique (Fin P.blockCount) := ⟨⟨i₀⟩, hunique_idx⟩
    have e₁ : A ≃⋆ₐ[ℂ] CStarMatrix (Fin (P.degree i₀)) (Fin (P.degree i₀)) ℂ :=
      P.equiv.trans (StarAlgEquiv.piUnique ℂ
        (fun j : Fin P.blockCount ↦ CStarMatrix (Fin (P.degree j)) (Fin (P.degree j)) ℂ))
    exact Or.inr ⟨e₁.trans (CStarMatrix.reindexₐ ℂ ℂ (finCongr hd₂))⟩

/-- `Fin 4 → ℂ` and `CStarMatrix (Fin 2) (Fin 2) ℂ` are not `⋆`-algebra isomorphic. -/
theorem isEmpty_starAlgEquiv_fin_four_cstarMatrix_two :
    IsEmpty ((Fin 4 → ℂ) ≃⋆ₐ[ℂ] CStarMatrix (Fin 2) (Fin 2) ℂ) := by
  refine ⟨fun e ↦ CStarMatrix.not_isMulCommutative_two ⟨⟨fun x y ↦ ?_⟩⟩⟩
  apply e.symm.injective
  rw [map_mul, map_mul, mul_comm]

/-- **`4` is the least complex dimension admitting two non-`⋆`-isomorphic complex C⋆-algebras**,
realized by the commutative algebra `Fin 4 → ℂ` and the full matrix algebra
`CStarMatrix (Fin 2) (Fin 2) ℂ`. -/
theorem isLeast_finrank_exists_isEmpty_starAlgEquiv :
    IsLeast {d : ℕ | ∃ (A B : Type) (_ : CStarAlgebra A) (_ : CStarAlgebra B)
      (_ : FiniteDimensional ℂ A) (_ : FiniteDimensional ℂ B),
      Module.finrank ℂ A = d ∧ Module.finrank ℂ B = d ∧ IsEmpty (A ≃⋆ₐ[ℂ] B)} 4 := by
  refine ⟨?_, ?_⟩
  · have : FiniteDimensional ℂ (CStarMatrix (Fin 2) (Fin 2) ℂ) :=
      Module.Finite.equiv CStarMatrix.ofMatrixₗ
    have hdimM : Module.finrank ℂ (CStarMatrix (Fin 2) (Fin 2) ℂ) = 4 := by
      simpa [Module.finrank_matrix] using
        (CStarMatrix.ofMatrixₗ (m := Fin 2) (n := Fin 2) (R := ℂ) (A := ℂ)).symm.finrank_eq
    exact ⟨Fin 4 → ℂ, CStarMatrix (Fin 2) (Fin 2) ℂ, inferInstance, inferInstance,
      inferInstance, inferInstance, by simp, hdimM, isEmpty_starAlgEquiv_fin_four_cstarMatrix_two⟩
  · rintro d ⟨A, B, _, _, _, _, rfl, hB, hempty⟩
    by_contra! hlt
    obtain ⟨e⟩ := nonempty_starAlgEquiv_of_finrank_eq_of_lt_four hB.symm hlt
    exact hempty.false e

end CStarAlgebra
