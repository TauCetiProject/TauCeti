/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Etale.Finite
public import Mathlib.RingTheory.TotallySplit
public import TauCeti.RingTheory.Etale.AdjoinRoot
public import TauCeti.RingTheory.Etale.Idempotent
public import TauCeti.RingTheory.Idempotents.Refinement
public import TauCeti.RingTheory.Spectrum.Prime.FreeLocus
public import TauCeti.RingTheory.Unramified.Section.Idempotent

import Mathlib.Algebra.Algebra.Shrink
import Mathlib.RingTheory.Finiteness.ModuleFinitePresentation
import Mathlib.RingTheory.Finiteness.Prod
import Mathlib.RingTheory.Finiteness.Small
import Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra
import Mathlib.RingTheory.Flat.Rank
import Mathlib.RingTheory.TensorProduct.Pi
import Mathlib.RingTheory.TensorProduct.Quotient
import Mathlib.Tactic.LinearCombination
import TauCeti.RingTheory.AdjoinRoot.Separable
import TauCeti.RingTheory.Ideal.Quotient.Operations
import TauCeti.RingTheory.Ideal.Quotient.Pi

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
* `TauCeti.IsFiniteEtaleSplit.of_isSepClosed`: the instance for separably closed fields.
* `TauCeti.Algebra.IsTotallySplit.baseChange`: total splitting is stable under base change.
* `TauCeti.IsFiniteEtaleSplit.nonempty_algHom`: a faithfully flat finite étale `R`-algebra maps to
  every `R`-algebra without nonsplit finite étale covers.
* `TauCeti.IsFiniteEtaleSplit.pi`, `TauCeti.IsFiniteEtaleSplit.prod`: products of rings without
  nonsplit finite étale covers have none.
* `TauCeti.isFiniteEtaleSplit_iff_of_isEquivalence`: the condition is invariant under a ring map
  along which base change `CommAlgCat.FiniteEtale.baseChange` is an equivalence of categories.

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

variable {R T} in
/-- Unfolding lemma for `IsTotallySplit`: it recovers the idempotents and the algebra isomorphism
in modules where the body of the definition is not exposed. -/
theorem isTotallySplit_iff : IsTotallySplit R T ↔
    ∃ (m : ℕ) (e : Fin m → R), (∀ j, IsIdempotentElem (e j)) ∧
      Nonempty (T ≃ₐ[R] ((j : Fin m) → R ⧸ Ideal.span {1 - e j})) :=
  Iff.rfl

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

/-- A quotient of a totally split algebra by an idempotent, that is, a direct factor of it, is
totally split. -/
theorem quotient_span_singleton (h : IsTotallySplit R T) {ε : T} (hε : IsIdempotentElem ε) :
    IsTotallySplit R (T ⧸ Ideal.span {ε}) := by
  obtain ⟨m, e, he, ⟨φ⟩⟩ := h
  let ε' := φ ε
  have hε' : IsIdempotentElem ε' := hε.map φ
  choose a ha using fun j ↦ Ideal.Quotient.mk_surjective (ε' j)
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
  have hker : RingHom.ker (Ideal.Quotient.piFactorₐ R hle) = Ideal.span {ε'} := by
    rw [← Ideal.pi_span]
    ext x
    simp only [RingHom.mem_ker, Ideal.mem_pi, funext_iff, Pi.zero_apply,
      Ideal.Quotient.piFactorₐ_apply]
    refine forall_congr' fun j ↦ ?_
    rw [← RingHom.mem_ker, Ideal.Quotient.factor_ker, Ideal.map_span, Set.image_singleton]
    simp [e', ha]
  exact ⟨m, e', he', ⟨(Ideal.quotientEquivAlg _ (Ideal.span {ε'}) φ
    (by simp [ε', Ideal.map_span])).trans ((Ideal.quotientEquivAlgOfEq R hker.symm).trans
      (Ideal.quotientKerAlgEquivOfSurjective (Ideal.Quotient.piFactorₐ_surjective R hle)))⟩⟩

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

/-- The second factor of a totally split product is totally split: swap the factors and apply
`of_prod_fst`. -/
theorem of_prod_snd {A B : Type*} [CommRing A] [CommRing B] [Algebra R A] [Algebra R B]
    (h : IsTotallySplit R (A × B)) : IsTotallySplit R B :=
  (h.of_algEquiv (AlgEquiv.ofRingEquiv (f := RingEquiv.prodComm) fun _ ↦ by simp)).of_prod_fst

/-- A totally split algebra with injective structure map, for example a faithfully flat one, has
a section: injectivity says that the components `D(e j)` cover `Spec R`, and a section is
assembled from an orthogonal refinement of this cover. -/
theorem nonempty_algHom_of_faithfulSMul (h : IsTotallySplit R T) [FaithfulSMul R T] :
    Nonempty (T →ₐ[R] R) := by
  obtain ⟨m, e, he, ⟨φ⟩⟩ := h
  have hcover : ∏ j, (1 - e j) = 0 := by
    apply FaithfulSMul.algebraMap_injective R T
    refine φ.injective (funext fun j ↦ ?_)
    simpa using Ideal.Quotient.eq_zero_iff_mem.mpr <| Ideal.mem_span_singleton.mpr <|
      Finset.dvd_prod_of_mem (fun i ↦ 1 - e i) (Finset.mem_univ j)
  obtain ⟨f, hf, hfe⟩ := exists_completeOrthogonalIdempotents_of_prod_one_sub_eq_zero e he hcover
  have hle (j : Fin m) : Ideal.span {1 - e j} ≤ Ideal.span {1 - f j} :=
    Ideal.span_singleton_le_span_singleton.mpr ⟨1 - e j, by linear_combination -(hfe j)⟩
  let ι : R ≃ₐ[R] ((j : Fin m) → R ⧸ Ideal.span {1 - f j}) :=
    AlgEquiv.ofBijective (Algebra.ofId R _) hf.bijective_pi
  exact ⟨ι.symm.toAlgHom.comp ((Ideal.Quotient.piFactorₐ R hle).comp φ.toAlgHom)⟩

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

open TensorProduct in
/-- Total splitting is stable under base change: if `T ≃ₐ[R] ∏ R ⧸ (1 - e_j)`, then
`S ⊗[R] T ≃ₐ[S] ∏ S ⧸ (1 - e_j)`, with the images of the same idempotents. -/
theorem baseChange (S : Type*) [CommRing S] [Algebra R S] (h : IsTotallySplit R T) :
    IsTotallySplit S (S ⊗[R] T) := by
  obtain ⟨m, e, he, ⟨φ⟩⟩ := h
  refine ⟨m, algebraMap R S ∘ e, fun j ↦ (he j).map _, ⟨?_⟩⟩
  refine (Algebra.TensorProduct.congr AlgEquiv.refl φ).trans <|
    (Algebra.TensorProduct.piRight R S S _).trans <| AlgEquiv.piCongrRight fun j ↦ ?_
  exact (Algebra.TensorProduct.quotIdealMapEquivTensorQuot S (Ideal.span {1 - e j})).symm.trans
    (Ideal.quotientEquivAlgOfEq S (by simp [Ideal.map_span]))

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
    have : Module.FinitePresentation R T := .of_finite_of_finitePresentation R T
    obtain ⟨e₀, he₀, hrank⟩ := Module.exists_rankAtStalk_prod_quotient_eq_max (R := R) T
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
  simp [← Polynomial.coe_aeval_eq_eval, Polynomial.aeval_algHom_apply]

/-- A separably closed field has no nonsplit finite étale covers: every finite étale algebra over
it has constant split rank. -/
instance IsFiniteEtaleSplit.of_isSepClosed (K : Type u) [Field K] [IsSepClosed K] :
    IsFiniteEtaleSplit K :=
  ⟨fun _ _ _ _ _ ↦ .of_isFiniteSplit⟩

/-- A field has no nonsplit finite étale covers if and only if it is separably closed. -/
theorem isFiniteEtaleSplit_iff_isSepClosed (K : Type u) [Field K] :
    IsFiniteEtaleSplit K ↔ IsSepClosed K := by
  refine ⟨fun _ ↦ IsSepClosed.of_exists_root K fun p hp hirr hsep ↦ ?_, fun _ ↦ inferInstance⟩
  exact IsFiniteEtaleSplit.exists_root hp hirr.natDegree_pos
    (separable_iff_isUnit_mk_derivative.mp hsep)

/-- Over a ring without nonsplit finite étale covers, a finite étale algebra in any universe is
totally split. The defining property of `IsFiniteEtaleSplit R` only quantifies over algebras in
the universe of `R`; a finite algebra is small over `R`, so it applies to an isomorphic copy. -/
theorem Algebra.IsTotallySplit.of_isFiniteEtaleSplit [IsFiniteEtaleSplit R] (T : Type*)
    [CommRing T] [Algebra R T] [Algebra.Etale R T] [Module.Finite R T] :
    Algebra.IsTotallySplit R T := by
  have : Small.{u} T := Module.Finite.small R T
  have : Algebra.Etale R (Shrink.{u} T) := .of_equiv (Shrink.algEquiv R T).symm
  exact (IsFiniteEtaleSplit.isTotallySplit (Shrink.{u} T)).of_algEquiv (Shrink.algEquiv R T)

open TensorProduct in
/-- A faithfully flat finite étale `R`-algebra `T` admits an `R`-algebra map to every
`R`-algebra `S` without nonsplit finite étale covers: the base change `S ⊗[R] T` is faithfully
flat and finite étale over `S`, hence has a section. -/
theorem IsFiniteEtaleSplit.nonempty_algHom (S : Type*) [CommRing S] [Algebra R S]
    [IsFiniteEtaleSplit S] (T : Type*) [CommRing T] [Algebra R T] [Algebra.Etale R T]
    [Module.Finite R T] [Module.FaithfullyFlat R T] : Nonempty (T →ₐ[R] S) := by
  obtain ⟨σ⟩ := (Algebra.IsTotallySplit.of_isFiniteEtaleSplit (R := S)
    (S ⊗[R] T)).nonempty_algHom_of_faithfulSMul
  exact ⟨(σ.restrictScalars R).comp Algebra.TensorProduct.includeRight⟩

/-- A product of rings without nonsplit finite étale covers, over any index type, has none: a
faithfully flat finite étale algebra over the product maps to every factor, and these maps
assemble to a section. -/
instance IsFiniteEtaleSplit.pi {ι : Type*} (A : ι → Type*) [∀ i, CommRing (A i)]
    [∀ i, IsFiniteEtaleSplit (A i)] : IsFiniteEtaleSplit ((i : ι) → A i) := by
  refine isFiniteEtaleSplit_iff_exists_section.mpr fun T _ _ _ _ _ ↦ ?_
  let (i : ι) : Algebra ((i : ι) → A i) (A i) := (Pi.evalRingHom A i).toAlgebra
  have σ (i : ι) :=
    Classical.choice (IsFiniteEtaleSplit.nonempty_algHom (R := (i : ι) → A i) (A i) T)
  exact ⟨{ RingHom.pi fun i ↦ (σ i).toRingHom with
    commutes' := fun r ↦ funext fun i ↦ (σ i).commutes r }⟩

/-- A product of two rings without nonsplit finite étale covers has none: a faithfully flat
finite étale algebra over the product maps to both factors, and these maps assemble to a
section. -/
instance IsFiniteEtaleSplit.prod (A B : Type*) [CommRing A] [CommRing B] [IsFiniteEtaleSplit A]
    [IsFiniteEtaleSplit B] : IsFiniteEtaleSplit (A × B) := by
  refine isFiniteEtaleSplit_iff_exists_section.mpr fun T _ _ _ _ _ ↦ ?_
  let : Algebra (A × B) A := (RingHom.fst A B).toAlgebra
  let : Algebra (A × B) B := (RingHom.snd A B).toAlgebra
  obtain ⟨σ⟩ := IsFiniteEtaleSplit.nonempty_algHom (R := A × B) A T
  obtain ⟨τ⟩ := IsFiniteEtaleSplit.nonempty_algHom (R := A × B) B T
  exact ⟨{ σ.toRingHom.prod τ.toRingHom with
    commutes' := fun r ↦ Prod.ext (σ.commutes r) (τ.commutes r) }⟩

section BaseChange

open CategoryTheory CommAlgCat TensorProduct

variable (R' : Type*) [CommRing R'] [Algebra R R']

/-- If every finite étale `R'`-algebra is a base change of a finite étale `R`-algebra, and `R` has
no nonsplit finite étale covers, then neither does `R'`. -/
theorem IsFiniteEtaleSplit.of_essSurj_baseChange [IsFiniteEtaleSplit R]
    [(FiniteEtale.baseChange.{u} R R').EssSurj] : IsFiniteEtaleSplit R' where
  isTotallySplit T _ _ _ _ := by
    let F := FiniteEtale.baseChange.{u} R R'
    -- `F` lands in algebras in the universe of `R' ⊗[R] A`, which may be larger than that of
    -- `T`, so lift `T` there.
    have : Algebra.Etale R' (ULift.{u} T) := .of_equiv ULift.algEquiv.symm
    have : Module.Finite R' (ULift.{u} T) := .equiv ULift.algEquiv.symm.toLinearEquiv
    let A := F.objPreimage (.of R' (ULift.{u} T))
    -- `F.obj A` is by definition `R' ⊗[R] A`, so `F.obj A ≅ ULift T` is an `AlgEquiv`.
    exact ((IsFiniteEtaleSplit.isTotallySplit A.obj).baseChange R').of_algEquiv
      ((algEquivOfIso ((ObjectProperty.ι _).mapIso (F.objObjPreimageIso _))).trans
        ULift.algEquiv)

/-- If base change along `R → R'` is full on finite étale algebras and `R'` has no nonsplit
finite étale covers, then neither does `R`: the section of `R' ⊗[R] T` over `R'` descends to a
section of `T` over `R`. -/
theorem IsFiniteEtaleSplit.of_full_baseChange [IsFiniteEtaleSplit R']
    [(FiniteEtale.baseChange.{u} R R').Full] : IsFiniteEtaleSplit R := by
  refine isFiniteEtaleSplit_iff_exists_section.mpr fun T _ _ _ _ _ ↦ ?_
  obtain ⟨σ⟩ := (Algebra.IsTotallySplit.of_isFiniteEtaleSplit (R := R')
    (R' ⊗[R] T)).nonempty_algHom_of_faithfulSMul
  let F := FiniteEtale.baseChange.{u} R R'
  -- `F.obj (.of R T)` and `F.obj (.of R R)` are by definition `R' ⊗[R] T` and `R' ⊗[R] R`.
  let f : F.obj (.of R T) ⟶ F.obj (.of R R) :=
    FiniteEtale.ofHom ((Algebra.TensorProduct.rid R R' R').symm.toAlgHom.comp σ)
  exact ⟨(F.preimage f).hom.hom⟩

/-- Having no nonsplit finite étale covers is invariant under a ring map along which base change
is an equivalence of categories of finite étale algebras. -/
theorem isFiniteEtaleSplit_iff_of_isEquivalence
    [(FiniteEtale.baseChange.{u} R R').IsEquivalence] :
    IsFiniteEtaleSplit R ↔ IsFiniteEtaleSplit R' :=
  ⟨fun _ ↦ .of_essSurj_baseChange (R := R) R',
    fun _ ↦ .of_full_baseChange R'⟩

end BaseChange

end TauCeti
