/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.TotallySplit
public import TauCeti.RingTheory.Etale.AdjoinRoot
public import TauCeti.RingTheory.Etale.Idempotent
public import TauCeti.RingTheory.Idempotents.Refinement
public import TauCeti.RingTheory.Spectrum.Prime.FreeLocus
public import TauCeti.RingTheory.Unramified.Section.Idempotent

import Mathlib.RingTheory.Finiteness.ModuleFinitePresentation
import Mathlib.RingTheory.Finiteness.Prod
import Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra
import Mathlib.RingTheory.Flat.Rank
import Mathlib.Tactic.LinearCombination

/-!
# Rings without nonsplit finite étale covers

A finite étale `R`-algebra `T` is *totally split* (`TauCeti.Algebra.IsTotallySplit`) if
`T ≃ₐ[R] ∏_{j < m} R ⧸ (1 - e_j)` for finitely many idempotents `e_j` of `R`. Geometrically,
`Spec T → Spec R` is a disjoint union of finitely many clopen subsets of `Spec R`, so its rank may
vary over the components of `Spec R`; Mathlib's `Algebra.IsFiniteSplit` is the constant-rank
case `T ≃ₐ[R] (Fin n → R)` (`TauCeti.Algebra.IsTotallySplit.of_isFiniteSplit`). A ring `R` *has
no nonsplit finite étale covers* (`TauCeti.IsFiniteEtaleSplit`) if every finite étale `R`-algebra
is totally split. No topology is involved, and the zero ring is allowed.

This is the conclusion of Scholze's Lemma 15.3 for the perfectoid tower `A_∞`, and it is used
there only through sections of faithfully flat covers and roots of separable polynomials.

## Main results

* `TauCeti.Algebra.IsTotallySplit.quotient_span_singleton`: a quotient of a totally split algebra
  by an idempotent is totally split.
* `TauCeti.Algebra.IsTotallySplit.nonempty_algHom_of_faithfulSMul`: a totally split algebra with
  injective structure map, for example a faithfully flat one, has a section.
* `TauCeti.isFiniteEtaleSplit_iff_exists_section`: `R` has no nonsplit finite étale covers if and
  only if every faithfully flat finite étale `R`-algebra admits an `R`-algebra map to `R`.
* `TauCeti.IsFiniteEtaleSplit.exists_root`: over such a ring, every monic polynomial of positive
  degree whose derivative is a unit modulo it has a root.
* `TauCeti.isFiniteEtaleSplit_iff_isSepClosed`: a field has no nonsplit finite étale covers if
  and only if it is separably closed.

## Implementation notes

The section criterion is proved by induction on an upper bound of the rank of `T`, which is a
locally constant function on `Spec R`. The support of `T` is cut out by an idempotent `e₀`, and
`T × R ⧸ (e₀)` is faithfully flat. Its section splits off a copy of `R`, leaving a cover of smaller
rank; `T` is recovered from the result as a quotient by an idempotent.

## References

* P. Scholze, *Étale cohomology of diamonds*, Lemma 15.3.
* P. Scholze and J. Weinstein, *Berkeley lectures on p-adic geometry*, Lemma 10.1.6.
-/

public section

open Polynomial

universe u

namespace TauCeti

namespace Algebra

variable (R T : Type*) [CommRing R] [CommRing T] [Algebra R T]

/-- An `R`-algebra `T` is *totally split* if `T ≃ₐ[R] ∏_{j < m} R ⧸ (1 - e_j)` for finitely many
idempotents `e_j` of `R` (repetitions and zeros allowed). Mathlib's `Algebra.IsFiniteSplit` is the
case where every `e_j` is `1`; in general the number of sheets may vary over the clopen components
of `Spec R`. -/
def IsTotallySplit : Prop :=
  ∃ (m : ℕ) (e : Fin m → R), (∀ j, IsIdempotentElem (e j)) ∧
    Nonempty (T ≃ₐ[R] ((j : Fin m) → R ⧸ Ideal.span {1 - e j}))

namespace IsTotallySplit

variable {R T}

/-- A product of quotients by idempotents indexed by any finite type is totally split. -/
theorem of_algEquiv_pi {ι : Type*} [Finite ι] (e : ι → R) (he : ∀ i, IsIdempotentElem (e i))
    (φ : T ≃ₐ[R] ((i : ι) → R ⧸ Ideal.span {1 - e i})) : IsTotallySplit R T := by
  cases nonempty_fintype ι
  let σ := Fintype.equivFin ι
  exact ⟨Fintype.card ι, e ∘ σ.symm, fun j ↦ he _,
    ⟨φ.trans (AlgEquiv.piCongrLeft R (fun i ↦ R ⧸ Ideal.span {1 - e i}) σ.symm).symm⟩⟩

/-- Total splitting is invariant under isomorphism of algebras. -/
theorem of_algEquiv {T' : Type*} [CommRing T'] [Algebra R T'] (h : IsTotallySplit R T)
    (φ : T ≃ₐ[R] T') : IsTotallySplit R T' := by
  obtain ⟨m, e, he, ⟨ψ⟩⟩ := h
  exact ⟨m, e, he, ⟨φ.symm.trans ψ⟩⟩

/-- An algebra of constant split rank is totally split, with every idempotent equal to `1`. -/
theorem of_isFiniteSplit [Algebra.IsFiniteSplit R T] : IsTotallySplit R T := by
  obtain ⟨n, ⟨φ⟩⟩ := Algebra.IsFiniteSplit.nonempty_algEquiv_fun R T
  let q : (R ⧸ Ideal.span {(1 : R) - 1}) ≃ₐ[R] R :=
    (Ideal.quotientEquivAlgOfEq R (by simp)).trans (AlgEquiv.quotientBot R R)
  exact ⟨n, fun _ ↦ 1, fun _ ↦ .one, ⟨φ.trans (AlgEquiv.piCongrRight fun _ ↦ q.symm)⟩⟩

variable (R T) in
/-- The zero algebra, and more generally any subsingleton algebra, is totally split: it is the
empty product. -/
theorem of_subsingleton [Subsingleton T] : IsTotallySplit R T :=
  have := Algebra.IsFiniteSplit.of_subsingleton_top (R := R) (S := T)
  of_isFiniteSplit

variable (R) in
/-- The base ring is totally split over itself, with one sheet. -/
theorem self : IsTotallySplit R R :=
  of_isFiniteSplit

/-- A product of two totally split algebras is totally split. -/
theorem prod {A B : Type*} [CommRing A] [CommRing B] [Algebra R A] [Algebra R B]
    (hA : IsTotallySplit R A) (hB : IsTotallySplit R B) : IsTotallySplit R (A × B) := by
  obtain ⟨m, e, he, ⟨φ⟩⟩ := hA
  obtain ⟨n, f, hf, ⟨ψ⟩⟩ := hB
  let Q : Fin m ⊕ Fin n → Type _ := fun k ↦ R ⧸ Ideal.span {1 - Sum.elim e f k}
  let χ : ((k : Fin m ⊕ Fin n) → Q k) →ₐ[R]
      ((i : Fin m) → Q (.inl i)) × ((j : Fin n) → Q (.inr j)) :=
    (AlgHom.pi fun i ↦ Pi.evalAlgHom R Q (.inl i)).prod
      (AlgHom.pi fun j ↦ Pi.evalAlgHom R Q (.inr j))
  have hχ : Function.Bijective χ := (Equiv.sumPiEquivProdPi Q).bijective
  exact of_algEquiv_pi (Sum.elim e f) (Sum.rec he hf)
    ((φ.prodCongr ψ).trans (AlgEquiv.ofBijective χ hχ).symm)

/-- The componentwise quotient map `∏ j, R ⧸ I j → ∏ j, R ⧸ J j` for ideals `I j ≤ J j`. -/
private def piFactorₐ {ι : Type*} {I J : ι → Ideal R} (hle : ∀ j, I j ≤ J j) :
    ((j : ι) → R ⧸ I j) →ₐ[R] ((j : ι) → R ⧸ J j) :=
  AlgHom.pi fun j ↦ (Ideal.Quotient.factorₐ R (hle j)).comp (Pi.evalAlgHom R _ j)

private theorem piFactorₐ_apply {ι : Type*} {I J : ι → Ideal R} (hle : ∀ j, I j ≤ J j)
    (x : (j : ι) → R ⧸ I j) (j : ι) :
    piFactorₐ hle x j = Ideal.Quotient.factor (hle j) (x j) :=
  rfl

private theorem piFactorₐ_surjective {ι : Type*} {I J : ι → Ideal R} (hle : ∀ j, I j ≤ J j) :
    Function.Surjective (piFactorₐ hle) := fun y ↦
  ⟨fun j ↦ (Ideal.Quotient.factor_surjective (hle j) (y j)).choose,
    funext fun j ↦ (Ideal.Quotient.factor_surjective (hle j) (y j)).choose_spec⟩

/-- A quotient of a totally split algebra by an idempotent, that is, a direct factor of it, is
totally split. -/
theorem quotient_span_singleton (h : IsTotallySplit R T) {ε : T} (hε : IsIdempotentElem ε) :
    IsTotallySplit R (T ⧸ Ideal.span {ε}) := by
  obtain ⟨m, e, he, ⟨φ⟩⟩ := h
  let ε' := φ ε
  have hε' : IsIdempotentElem ε' := hε.map φ
  choose a ha using fun j ↦ Ideal.Quotient.mk_surjective (ε' j)
  have hmk (j : Fin m) : Ideal.Quotient.mk (Ideal.span {1 - e j}) (e j) = 1 := by
    rw [← map_one (Ideal.Quotient.mk _), Ideal.Quotient.eq]
    exact Ideal.mem_span_singleton'.mpr ⟨-1, by ring⟩
  -- The lift `a j` is idempotent modulo `1 - e j`, which `e j` annihilates.
  have hsq (j : Fin m) : e j * (a j * a j - a j) = 0 := by
    have hmem : a j * a j - a j ∈ Ideal.span {1 - e j} := by
      rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, map_mul, ha, sub_eq_zero]
      exact congrFun hε'.eq j
    obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.mp hmem
    rw [← hc, mul_left_comm, (he j).mul_one_sub_self, mul_zero]
  -- The component of `T ⧸ (ε)` over the `j`-th factor is cut out by `e j * (1 - a j)`.
  let e' : Fin m → R := fun j ↦ e j * (1 - a j)
  have he' (j : Fin m) : IsIdempotentElem (e' j) := by
    unfold IsIdempotentElem
    linear_combination (1 - a j) ^ 2 * (he j).eq + hsq j
  have hle (j : Fin m) : Ideal.span {1 - e j} ≤ Ideal.span {1 - e' j} :=
    Ideal.span_singleton_le_span_singleton.mpr
      ⟨1 - e j, by linear_combination (a j - 1) * (he j).eq⟩
  have hker : RingHom.ker (piFactorₐ hle) = Ideal.span {ε'} := by
    rw [← Ideal.pi_span]
    ext x
    simp only [RingHom.mem_ker, Ideal.mem_pi, funext_iff, Pi.zero_apply, piFactorₐ_apply]
    refine forall_congr' fun j ↦ ?_
    rw [← RingHom.mem_ker, Ideal.Quotient.factor_ker, Ideal.map_span, Set.image_singleton]
    simp [e', hmk, ha]
  exact ⟨m, e', he', ⟨(Ideal.quotientEquivAlg _ (Ideal.span {ε'}) φ
    (by simp [ε', Ideal.map_span])).trans ((Ideal.quotientEquivAlgOfEq R hker.symm).trans
      (Ideal.quotientKerAlgEquivOfSurjective (piFactorₐ_surjective hle)))⟩⟩

/-- A factor of a totally split product is totally split: `A` is the quotient of `A × B` by the
idempotent `(0, 1)`. -/
theorem of_prod_fst {A B : Type*} [CommRing A] [CommRing B] [Algebra R A] [Algebra R B]
    (h : IsTotallySplit R (A × B)) : IsTotallySplit R A := by
  have hfst : RingHom.ker (AlgHom.fst R A B) = Ideal.span {((0, 1) : A × B)} := by
    ext ⟨a, b⟩
    simp only [RingHom.mem_ker, AlgHom.fst_apply, Ideal.mem_span_singleton']
    refine ⟨fun ha ↦ ⟨(0, b), by simp [ha]⟩, fun ⟨⟨_, c⟩, hc⟩ ↦ ?_⟩
    simpa using (congrArg Prod.fst hc).symm
  exact (h.quotient_span_singleton (ε := ((0, 1) : A × B)) (by ext <;> simp)).of_algEquiv
    ((Ideal.quotientEquivAlgOfEq R hfst.symm).trans
      (Ideal.quotientKerAlgEquivOfSurjective (f := AlgHom.fst R A B) Prod.fst_surjective))

/-- A totally split algebra with injective structure map, for example a faithfully flat one, has
a section: injectivity says that the components `D(e j)` cover `Spec R`, and a section is
assembled from an orthogonal refinement of this cover. -/
theorem nonempty_algHom_of_faithfulSMul (h : IsTotallySplit R T) [FaithfulSMul R T] :
    Nonempty (T →ₐ[R] R) := by
  obtain ⟨m, e, he, ⟨φ⟩⟩ := h
  have hcover : ∏ j, (1 - e j) = 0 := by
    apply FaithfulSMul.algebraMap_injective R T
    apply φ.injective
    rw [map_zero, map_zero, AlgEquiv.commutes]
    funext j
    rw [Pi.algebraMap_apply, Ideal.Quotient.algebraMap_eq, Pi.zero_apply,
      Ideal.Quotient.eq_zero_iff_mem]
    exact Ideal.mem_span_singleton.mpr (Finset.dvd_prod_of_mem _ (Finset.mem_univ j))
  obtain ⟨f, hf, hfe⟩ := exists_completeOrthogonalIdempotents_of_prod_one_sub_eq_zero e he hcover
  have hle (j : Fin m) : Ideal.span {1 - e j} ≤ Ideal.span {1 - f j} :=
    Ideal.span_singleton_le_span_singleton.mpr ⟨1 - e j, by linear_combination -(hfe j)⟩
  let ι : R ≃ₐ[R] ((j : Fin m) → R ⧸ Ideal.span {1 - f j}) :=
    AlgEquiv.ofBijective (Algebra.ofId R _) hf.bijective_pi
  exact ⟨ι.symm.toAlgHom.comp ((piFactorₐ hle).comp φ.toAlgHom)⟩

/-- A totally split algebra is étale. -/
theorem etale (h : IsTotallySplit R T) : Algebra.Etale R T := by
  obtain ⟨m, e, he, ⟨φ⟩⟩ := h
  have (j : Fin m) : Algebra.Etale R (R ⧸ Ideal.span {1 - e j}) :=
    Etale.quotient_span_singleton (he j).one_sub
  exact .of_equiv φ.symm

/-- A totally split algebra is finite. -/
theorem finite (h : IsTotallySplit R T) : Module.Finite R T := by
  obtain ⟨m, e, -, ⟨φ⟩⟩ := h
  exact .equiv φ.symm.toLinearEquiv

end IsTotallySplit

end Algebra

/-- A ring `R` *has no nonsplit finite étale covers* if every finite étale `R`-algebra is totally
split. This is the conclusion of Scholze's Lemma 15.3 for the perfectoid tower `A_∞`. -/
class IsFiniteEtaleSplit (R : Type u) [CommRing R] : Prop where
  /-- Every finite étale `R`-algebra is totally split. -/
  isTotallySplit (T : Type u) [CommRing T] [Algebra R T] [Algebra.Etale R T]
    [Module.Finite R T] : Algebra.IsTotallySplit R T

variable {R : Type u} [CommRing R]

/-- The zero ring has no nonsplit finite étale covers: every algebra over it is the empty
product. -/
instance (priority := 100) IsFiniteEtaleSplit.of_subsingleton [Subsingleton R] :
    IsFiniteEtaleSplit R where
  isTotallySplit T _ _ _ _ :=
    have : Subsingleton T := RingHom.codomain_trivial (algebraMap R T)
    .of_subsingleton R T

/-- Adding the complement of its support to a finite étale algebra `T` gives an algebra of rank
`max 1 (rank T)` at every prime, hence a faithfully flat one. -/
private theorem exists_rankAtStalk_prod_quotient_eq_max (T : Type*) [CommRing T] [Algebra R T]
    [Algebra.Etale R T] [Module.Finite R T] :
    ∃ e₀ : R, IsIdempotentElem e₀ ∧ ∀ p : PrimeSpectrum R,
      Module.rankAtStalk (R := R) (T × R ⧸ Ideal.span {e₀}) p =
        max 1 (Module.rankAtStalk (R := R) T p) := by
  have : Module.FinitePresentation R T := .of_finite_of_finitePresentation R T
  obtain ⟨e₀, he₀, hsupp⟩ := Module.exists_isIdempotentElem_basicOpen_eq_support (R := R) T
  have : Algebra.Etale R (R ⧸ Ideal.span {e₀}) := Algebra.Etale.quotient_span_singleton he₀
  refine ⟨e₀, he₀, fun p ↦ ?_⟩
  have hU₁ : Module.rankAtStalk (R := R) (R ⧸ Ideal.span {e₀}) p ≤ 1 :=
    Module.rankAtStalk_le_one_iff_surjective.mpr Ideal.Quotient.mk_surjective p
  have hU₀ : 0 < Module.rankAtStalk (R := R) (R ⧸ Ideal.span {e₀}) p ↔ e₀ ∈ p.asIdeal := by
    rw [PrimeSpectrum.rankAtStalk_pos_iff_mem_range_comap, Ideal.Quotient.algebraMap_eq,
      range_comap_of_surjective _ _ Ideal.Quotient.mk_surjective]
    simp
  have hT : 0 < Module.rankAtStalk (R := R) T p ↔ e₀ ∉ p.asIdeal := by
    rw [Module.rankAtStalk_pos_iff_mem_support, ← hsupp, SetLike.mem_coe,
      PrimeSpectrum.mem_basicOpen]
  rw [Module.rankAtStalk_prod, Pi.add_apply]
  by_cases hp : e₀ ∈ p.asIdeal
  · have := hU₀.mpr hp
    have := hT.not.mpr (not_not.mpr hp)
    omega
  · have := hU₀.not.mpr hp
    have := hT.mpr hp
    omega

/-- If every faithfully flat finite étale `R`-algebra has a section, then every finite étale
`R`-algebra of rank at most `N` is totally split. -/
private theorem isTotallySplit_of_rankAtStalk_le
    (H : ∀ (T : Type u) [CommRing T] [Algebra R T] [Algebra.Etale R T] [Module.Finite R T]
      [Module.FaithfullyFlat R T], Nonempty (T →ₐ[R] R)) (N : ℕ) :
    ∀ (T : Type u) [CommRing T] [Algebra R T] [Algebra.Etale R T] [Module.Finite R T],
      (∀ p, Module.rankAtStalk (R := R) T p ≤ N) → Algebra.IsTotallySplit R T := by
  induction N with
  | zero =>
    intro T _ _ _ _ hT
    have : Subsingleton T :=
      Module.rankAtStalk_eq_zero_iff_subsingleton.mp (funext fun p ↦ Nat.le_zero.mp (hT p))
    exact .of_subsingleton R T
  | succ N ih =>
    intro T _ _ _ _ hT
    -- `T × R ⧸ (e₀)` is faithfully flat and its rank is still at most `N + 1`.
    obtain ⟨e₀, he₀, hrank⟩ := exists_rankAtStalk_prod_quotient_eq_max (R := R) T
    have : Algebra.Etale R (R ⧸ Ideal.span {e₀}) := Algebra.Etale.quotient_span_singleton he₀
    have : Module.FaithfullyFlat R (T × R ⧸ Ideal.span {e₀}) :=
      .of_comap_surjective (PrimeSpectrum.rankAtStalk_pos_iff_comap_surjective.mp
        fun p ↦ by rw [hrank]; omega)
    -- Its section splits off a copy of `R`, and the complement has rank at most `N`.
    obtain ⟨σ⟩ := H (T × R ⧸ Ideal.span {e₀})
    obtain ⟨ε, hε, -, hker⟩ := Algebra.FormallyUnramified.exists_isIdempotentElem_ker_eq_span R _ σ
    let ψ := Algebra.FormallyUnramified.prodOfKerEqSpan σ hε hker
    have : Algebra.Etale R ((T × R ⧸ Ideal.span {e₀}) ⧸ Ideal.span {ε}) :=
      Algebra.Etale.quotient_span_singleton hε
    have hsplit := ih ((T × R ⧸ Ideal.span {e₀}) ⧸ Ideal.span {ε}) fun p ↦ by
      have : Nontrivial R := PrimeSpectrum.nonempty_iff_nontrivial.mp ⟨p⟩
      have h := congrFun (Module.rankAtStalk_eq_of_equiv ψ.toLinearEquiv) p
      rw [hrank, Module.rankAtStalk_prod, Pi.add_apply, Module.rankAtStalk_self,
        Pi.one_apply] at h
      have := hT p
      omega
    -- `T` is a factor of `T × R ⧸ (e₀) ≃ R × (T × R ⧸ (e₀)) ⧸ (ε)`.
    exact (((Algebra.IsTotallySplit.self R).prod hsplit).of_algEquiv ψ.symm).of_prod_fst

/-- A ring has no nonsplit finite étale covers if and only if every faithfully flat finite étale
algebra over it admits a section. Faithful flatness is needed: over a nonzero ring the zero
algebra is finite étale and totally split, but has no section. -/
theorem isFiniteEtaleSplit_iff_exists_section :
    IsFiniteEtaleSplit R ↔ ∀ (T : Type u) [CommRing T] [Algebra R T] [Algebra.Etale R T]
      [Module.Finite R T] [Module.FaithfullyFlat R T], Nonempty (T →ₐ[R] R) := by
  refine ⟨fun h T _ _ _ _ _ ↦ (h.isTotallySplit T).nonempty_algHom_of_faithfulSMul,
    fun H ↦ ⟨fun T _ _ _ _ ↦ ?_⟩⟩
  have : Module.FinitePresentation R T := .of_finite_of_finitePresentation R T
  obtain ⟨N, hN⟩ := (Module.isLocallyConstant_rankAtStalk (R := R) (M := T)).range_finite.bddAbove
  exact isTotallySplit_of_rankAtStalk_le H N T fun p ↦ hN ⟨p, rfl⟩

/-- Over a ring without nonsplit finite étale covers, every monic polynomial of positive degree
whose derivative is a unit modulo it, that is, every separable one
(`Polynomial.separable_iff_isUnit_mk_derivative`), has a root: `R[X] ⧸ (P)` is finite étale and
free of positive rank, so it has a section. -/
theorem IsFiniteEtaleSplit.exists_root [IsFiniteEtaleSplit R] {P : R[X]} (hP : P.Monic)
    (hd : 0 < P.natDegree) (hu : IsUnit (AdjoinRoot.mk P (derivative P))) :
    ∃ r : R, P.IsRoot r := by
  cases subsingleton_or_nontrivial R
  · exact ⟨0, Subsingleton.elim _ _⟩
  have := hP.isStandardEtale_adjoinRoot (separable_iff_isUnit_mk_derivative.mpr hu)
  let pb := AdjoinRoot.powerBasis' hP
  have : Module.Finite R (AdjoinRoot P) := pb.finite
  have : Module.Free R (AdjoinRoot P) := .of_basis pb.basis
  have : Nontrivial (AdjoinRoot P) :=
    Module.nontrivial_of_finrank_pos (by rwa [pb.finrank, AdjoinRoot.powerBasis'_dim])
  obtain ⟨σ⟩ := isFiniteEtaleSplit_iff_exists_section.mp ‹_› (AdjoinRoot P)
  refine ⟨σ (AdjoinRoot.root P), ?_⟩
  rw [Polynomial.IsRoot, ← Polynomial.coe_aeval_eq_eval, Polynomial.aeval_algHom_apply,
    AdjoinRoot.aeval_eq, AdjoinRoot.mk_self, map_zero]

/-- A field has no nonsplit finite étale covers if and only if it is separably closed. -/
theorem isFiniteEtaleSplit_iff_isSepClosed (K : Type u) [Field K] :
    IsFiniteEtaleSplit K ↔ IsSepClosed K := by
  refine ⟨fun _ ↦ IsSepClosed.of_exists_root K fun p hp hirr hsep ↦ ?_,
    fun _ ↦ ⟨fun T _ _ _ _ ↦ .of_isFiniteSplit⟩⟩
  exact IsFiniteEtaleSplit.exists_root hp hirr.natDegree_pos
    (separable_iff_isUnit_mk_derivative.mp hsep)

end TauCeti
