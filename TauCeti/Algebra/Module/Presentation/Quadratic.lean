/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.TensorProduct.Free
public import TauCeti.RingTheory.FittingIdeal.Determinant
public import TauCeti.RingTheory.Spectrum.Prime.FreeLocus

/-!
# Quadratic presentations

Let `R` be a commutative ring. A *quadratic presentation* of an `R`-module `N` is a presentation
with as many relations as generators: a square matrix `φ` of size `m ≥ 1` and a surjection
`π : R^m → N` whose kernel is the image of `φ : R^m → R^m`, so that `N ≅ coker φ`. The size
`m ≥ 1` is part of the data: the zero module is presented by `R →(1) R`, not by the empty
matrix.

The zeroth Fitting ideal of a quadratically presented module is computed by a single
determinant, `Fitt₀(N) = (det φ)`, so it is principal. Dasgupta and Kakde state their
Fitting-ideal comparisons for quadratically presented modules over the coefficient orders of the
Brumer–Stark conjecture. Base change preserves quadratic presentations, with the relation matrix
mapped entrywise. A quotient `R ⧸ I` is quadratically presented exactly when `I` is principal,
since its zeroth Fitting ideal is `I`.

Over a ring with finitely many maximal ideals, a presentation `P₁ → P₀ → N → 0` by finite flat
(for instance finite projective) modules of the same constant rank is quadratic: such modules
are free (Mathlib's `Module.nonempty_basis_of_flat_of_finrank_eq`), and a choice of bases turns
the presentation into a square matrix. This applies to `ℤ_p[G]` for a finite abelian group `G`,
a finite algebra over the local ring `ℤ_p`. Over a general ring it fails: for a non-principal
ideal `I` of a Dedekind domain, `I → R → R ⧸ I → 0` is such a presentation of rank one, but
`R ⧸ I` is not quadratically presented.

## Main definitions

* `TauCeti.QuadraticPresentation R N`: a quadratic presentation of `N`, with its size
  `P.size ≥ 1`, its relation matrix `P.rel` and its surjection `P.gen : R^m → N`.
* `TauCeti.IsQuadraticallyPresented R N`: `N` has a quadratic presentation.
* `TauCeti.QuadraticPresentation.ofExact`: the quadratic presentation read off an exact sequence
  `P₁ → P₀ → N → 0` from bases of `P₀` and `P₁` of the same size.
* `TauCeti.QuadraticPresentation.cokernel`, `TauCeti.QuadraticPresentation.quotientSpanSingleton`,
  `TauCeti.QuadraticPresentation.ofSubsingleton`, `TauCeti.QuadraticPresentation.ofBasis`: the
  presentations of the cokernel of a square matrix, of `R ⧸ (a)`, of the zero module, and of a
  free module of positive finite rank with zero relation matrix.
* `TauCeti.QuadraticPresentation.map`, `TauCeti.QuadraticPresentation.baseChange`: transport
  along a linear equivalence and base change along an algebra `R → S`.

## Main results

* `TauCeti.QuadraticPresentation.fittingIdeal_eq`: `Fitt₀(N) = (det φ)`.
* `TauCeti.QuadraticPresentation.baseChange_rel`: the base change of a presentation by `φ` is
  presented by the image of `φ`.
* `TauCeti.isQuadraticallyPresented_iff_exists_linearEquiv`: `N` is quadratically presented iff
  it is isomorphic to the cokernel of a square matrix of positive size.
* `TauCeti.isQuadraticallyPresented_quotient_iff`: `R ⧸ I` is quadratically presented iff `I` is
  principal.
* `TauCeti.isQuadraticallyPresented_of_finite_maximalSpectrum`: over a ring with finitely many
  maximal ideals, a presentation by finite flat modules of the same constant rank yields a
  quadratic presentation.

## References

* S. Dasgupta, M. Kakde, *On the Brumer–Stark conjecture*, Ann. of Math. (2) 197 (2023),
  §2.3 (quadratically presented modules and their Fitting ideals) and Remark A.7 (locally
  quadratic presentations over `ℤ_p[G]`).
-/

public section

noncomputable section

open Module

open scoped Matrix TensorProduct

namespace TauCeti

variable {R N N' : Type*} [CommRing R] [AddCommGroup N] [Module R N] [AddCommGroup N']
  [Module R N']

variable (R N) in
/-- A quadratic presentation `R^m →φ R^m →π N → 0` of an `R`-module `N`: a square matrix `φ` of
size `m ≥ 1` and a surjection `π : R^m → N` whose kernel is the image of `φ`. -/
@[ext]
structure QuadraticPresentation where
  /-- The number `m ≥ 1` of generators, which is also the number of relations. -/
  size : ℕ
  size_pos : 0 < size
  /-- The square relation matrix `φ`; its columns span the relations among the generators. -/
  rel : Matrix (Fin size) (Fin size) R
  /-- The surjection `π : R^m → N` sending the standard basis vectors to the generators. -/
  gen : (Fin size → R) →ₗ[R] N
  gen_surjective : Function.Surjective gen
  range_rel_eq_ker : LinearMap.range (Matrix.toLin' rel) = LinearMap.ker gen

variable (R N) in
/-- `N` is quadratically presented over `R`: it has a quadratic presentation. -/
def IsQuadraticallyPresented : Prop :=
  Nonempty (QuadraticPresentation R N)

namespace QuadraticPresentation

variable (P : QuadraticPresentation R N)

/-- The presentation `R^m →φ R^m →π N` is exact at the middle term. -/
theorem exact : Function.Exact (Matrix.toLin' P.rel) P.gen :=
  LinearMap.exact_iff.2 P.range_rel_eq_ker.symm

/-- The relations hold among the generators. -/
@[simp]
theorem gen_mulVec (v : Fin P.size → R) : P.gen (P.rel *ᵥ v) = 0 :=
  P.exact.apply_apply_eq_zero v

/-- A module with a quadratic presentation is quadratically presented. -/
theorem isQuadraticallyPresented (P : QuadraticPresentation R N) :
    IsQuadraticallyPresented R N :=
  ⟨P⟩

/-- A quadratically presented module is finite. -/
theorem finite (P : QuadraticPresentation R N) : Module.Finite R N :=
  Module.Finite.of_surjective P.gen P.gen_surjective

/-- A quadratically presented module is finitely presented. -/
theorem finitePresentation (P : QuadraticPresentation R N) : Module.FinitePresentation R N :=
  Module.finitePresentation_of_surjective P.gen P.gen_surjective <| by
    rw [← P.range_rel_eq_ker, LinearMap.range_eq_map]
    exact Module.Finite.fg_top.map _

/-- The zeroth Fitting ideal of a quadratically presented module is generated by the determinant
of the relation matrix. -/
theorem fittingIdeal_eq (P : QuadraticPresentation R N) [Module.Finite R N] :
    fittingIdeal R N 0 = Ideal.span {P.rel.det} :=
  P.rel.fittingIdeal_zero_eq_span_det_of_ker_eq_range P.gen_surjective <| by
    rw [← P.range_rel_eq_ker, Matrix.toLin'_apply']

/-- A quadratically presented module is the cokernel of its relation matrix. -/
def cokernelEquiv : ((Fin P.size → R) ⧸ LinearMap.range (Matrix.toLin' P.rel)) ≃ₗ[R] N :=
  (Submodule.quotEquivOfEq _ _ P.range_rel_eq_ker).trans
    (P.gen.quotKerEquivOfSurjective P.gen_surjective)

/-- The identification of the cokernel of `P.rel` with `N` sends the class of `v` to `P.gen v`. -/
@[simp]
theorem cokernelEquiv_mk (v : Fin P.size → R) :
    P.cokernelEquiv (Submodule.Quotient.mk v) = P.gen v :=
  (rfl)

/-- The quadratic presentation of the cokernel of a square matrix of positive size. -/
@[expose, simps]
def cokernel {m : ℕ} (hm : 0 < m) (A : Matrix (Fin m) (Fin m) R) :
    QuadraticPresentation R ((Fin m → R) ⧸ LinearMap.range (Matrix.toLin' A)) where
  size := m
  size_pos := hm
  rel := A
  gen := (LinearMap.range (Matrix.toLin' A)).mkQ
  gen_surjective := Submodule.mkQ_surjective _
  range_rel_eq_ker := (Submodule.ker_mkQ _).symm

/-- The transport of a quadratic presentation along a linear equivalence, with the same relation
matrix. -/
@[expose, simps]
def map (e : N ≃ₗ[R] N') : QuadraticPresentation R N' where
  size := P.size
  size_pos := P.size_pos
  rel := P.rel
  gen := e.toLinearMap ∘ₗ P.gen
  gen_surjective := e.surjective.comp P.gen_surjective
  range_rel_eq_ker := by rw [LinearEquiv.ker_comp, P.range_rel_eq_ker]

/-- The quadratic presentation `R →(1) R → N → 0` of a zero module. -/
@[expose, simps]
def ofSubsingleton [Subsingleton N] : QuadraticPresentation R N where
  size := 1
  size_pos := one_pos
  rel := 1
  gen := 0
  gen_surjective _ := ⟨0, Subsingleton.elim _ _⟩
  range_rel_eq_ker := by rw [Matrix.toLin'_one, LinearMap.range_id, LinearMap.ker_zero]

/-- The quadratic presentation `R^m →(0) R^m → N → 0` of a free module with a basis of positive
size `m`. -/
@[expose, simps]
def ofBasis {m : ℕ} (hm : 0 < m) (b : Basis (Fin m) R N) : QuadraticPresentation R N where
  size := m
  size_pos := hm
  rel := 0
  gen := b.equivFun.symm.toLinearMap
  gen_surjective := b.equivFun.symm.surjective
  range_rel_eq_ker := by rw [map_zero, LinearMap.range_zero, LinearEquiv.ker]

/-- The quadratic presentation `R →(a) R → R ⧸ (a) → 0` of size one. -/
@[expose, simps]
def quotientSpanSingleton (a : R) : QuadraticPresentation R (R ⧸ Ideal.span {a}) where
  size := 1
  size_pos := one_pos
  rel := !![a]
  gen := (Ideal.span {a}).mkQ ∘ₗ LinearMap.proj 0
  gen_surjective x := by
    obtain ⟨y, rfl⟩ := Submodule.mkQ_surjective _ x
    exact ⟨fun _ ↦ y, rfl⟩
  range_rel_eq_ker := by
    ext v
    simp only [LinearMap.mem_range, Matrix.toLin'_apply, LinearMap.mem_ker, LinearMap.coe_comp,
      Function.comp_apply, LinearMap.coe_proj, Function.eval, Submodule.mkQ_apply,
      Submodule.Quotient.mk_eq_zero, Ideal.mem_span_singleton']
    constructor
    · rintro ⟨w, rfl⟩
      exact ⟨w 0, by simp [Matrix.mulVec, dotProduct, mul_comm]⟩
    · rintro ⟨c, hc⟩
      refine ⟨fun _ ↦ c, funext fun i ↦ ?_⟩
      rw [Subsingleton.elim i 0]
      simp [Matrix.mulVec, dotProduct, ← hc, mul_comm]

/-- The presentation of `R ⧸ (a)` has determinant `a`. -/
theorem det_quotientSpanSingleton_rel (a : R) : (quotientSpanSingleton a).rel.det = a :=
  Matrix.det_fin_one_of a

variable {P₀ P₁ : Type*} [AddCommGroup P₀] [Module R P₀] [AddCommGroup P₁] [Module R P₁]

/-- The quadratic presentation read off an exact sequence `P₁ →f P₀ →π N → 0` from bases of `P₁`
and `P₀` of the same positive size: the relation matrix is the matrix of `f` in these bases. -/
@[expose, simps]
def ofExact {m : ℕ} (hm : 0 < m) (b₁ : Basis (Fin m) R P₁) (b₀ : Basis (Fin m) R P₀)
    {f : P₁ →ₗ[R] P₀} {π : P₀ →ₗ[R] N} (hf : Function.Exact f π) (hπ : Function.Surjective π) :
    QuadraticPresentation R N where
  size := m
  size_pos := hm
  rel := LinearMap.toMatrix b₁ b₀ f
  gen := π ∘ₗ b₀.equivFun.symm.toLinearMap
  gen_surjective := hπ.comp b₀.equivFun.symm.surjective
  range_rel_eq_ker := by
    -- In coordinates, the relation matrix acts as `f` conjugated by the basis equivalences.
    have hrel : Matrix.toLin' (LinearMap.toMatrix b₁ b₀ f) =
        b₀.equivFun.toLinearMap ∘ₗ f ∘ₗ b₁.equivFun.symm.toLinearMap :=
      LinearMap.ext fun x ↦ by
        simpa only [Matrix.toLin'_apply, LinearMap.comp_apply, LinearEquiv.coe_coe,
          ← Basis.equivFun_apply, LinearEquiv.apply_symm_apply] using
          LinearMap.toMatrix_mulVec_repr b₁ b₀ f (b₁.equivFun.symm x)
    rw [hrel, LinearMap.range_comp,
      LinearMap.range_comp_of_range_eq_top _ (LinearEquiv.range _), LinearMap.ker_comp,
      LinearMap.exact_iff.1 hf, Submodule.map_equiv_eq_comap_symm]

variable (S : Type*) [CommRing S] [Algebra R S]

/-- The base change `S ⊗ R^m → S ⊗ R^m → S ⊗ N → 0` of a quadratic presentation, in the bases
`1 ⊗ eᵢ`; its relation matrix is the image of the original one (`baseChange_rel`). -/
@[expose]
def baseChange : QuadraticPresentation S (S ⊗[R] N) :=
  ofExact P.size_pos (Algebra.TensorProduct.basis S (Pi.basisFun R (Fin P.size)))
    (Algebra.TensorProduct.basis S (Pi.basisFun R (Fin P.size)))
    (f := (Matrix.toLin' P.rel).baseChange S) (π := P.gen.baseChange S)
    (lTensor_exact S P.exact P.gen_surjective)
    (LinearMap.lTensor_surjective S P.gen_surjective)

/-- The base change of a presentation has the same size. -/
@[simp]
theorem baseChange_size : (P.baseChange S).size = P.size :=
  rfl

/-- The relation matrix of the base change is the original relation matrix mapped entrywise along
`algebraMap R S`. -/
@[simp]
theorem baseChange_rel : (P.baseChange S).rel = P.rel.map (algebraMap R S) :=
  -- The relation matrix of `P.baseChange S` is by definition (`ofExact_rel`) the matrix of the
  -- base change of `toLin' P.rel` in the bases `1 ⊗ eᵢ`.
  (LinearMap.toMatrix_baseChange S (Matrix.toLin' P.rel) _ _).trans <| by
    rw [LinearMap.toMatrix_eq_toMatrix', LinearMap.toMatrix'_toLin']

/-- The generator map of the base change sends `v` to `∑ᵢ vᵢ ⊗ xᵢ`, where the `xᵢ` are the
original generators. This is not a simp lemma: `baseChange_size` rewrites the index type
`Fin (P.baseChange S).size` in its left-hand side. -/
theorem baseChange_gen_apply (v : Fin (P.baseChange S).size → S) :
    (P.baseChange S).gen v = ∑ i : Fin P.size, v i ⊗ₜ P.gen (Pi.single i 1) := by
  -- The generator map of `P.baseChange S` is by definition (`ofExact_gen`) the base change of
  -- `P.gen` composed with the coordinates in the basis `1 ⊗ eᵢ`.
  revert v
  change ∀ v : Fin P.size → S, P.gen.baseChange S
    ((Algebra.TensorProduct.basis S (Pi.basisFun R (Fin P.size))).equivFun.symm v) = _
  intro v
  simp [Basis.equivFun_symm_apply, TensorProduct.smul_tmul']

end QuadraticPresentation

namespace IsQuadraticallyPresented

/-- A quadratically presented module is finitely presented. -/
theorem finitePresentation (h : IsQuadraticallyPresented R N) : Module.FinitePresentation R N :=
  h.some.finitePresentation

/-- The zeroth Fitting ideal of a quadratically presented module is principal. -/
theorem isPrincipal_fittingIdeal [Module.Finite R N] (h : IsQuadraticallyPresented R N) :
    (fittingIdeal R N 0).IsPrincipal :=
  ⟨⟨h.some.rel.det, h.some.fittingIdeal_eq⟩⟩

/-- Being quadratically presented is invariant under linear equivalence. -/
theorem of_equiv (h : IsQuadraticallyPresented R N) (e : N ≃ₗ[R] N') :
    IsQuadraticallyPresented R N' :=
  (h.some.map e).isQuadraticallyPresented

/-- The zero module is quadratically presented, by `R →(1) R`. -/
theorem of_subsingleton [Subsingleton N] : IsQuadraticallyPresented R N :=
  QuadraticPresentation.ofSubsingleton.isQuadraticallyPresented

/-- The base change of a quadratically presented module is quadratically presented. -/
theorem baseChange (h : IsQuadraticallyPresented R N) (S : Type*) [CommRing S] [Algebra R S] :
    IsQuadraticallyPresented S (S ⊗[R] N) :=
  (h.some.baseChange S).isQuadraticallyPresented

variable {P₀ P₁ : Type*} [AddCommGroup P₀] [Module R P₀] [AddCommGroup P₁] [Module R P₁]

/-- A module presented by an exact sequence `P₁ → P₀ → N → 0` of free modules with bases of the
same size is quadratically presented; for the empty basis, `N` is zero. -/
theorem of_exact {m : ℕ} (b₁ : Basis (Fin m) R P₁) (b₀ : Basis (Fin m) R P₀)
    {f : P₁ →ₗ[R] P₀} {π : P₀ →ₗ[R] N} (hf : Function.Exact f π) (hπ : Function.Surjective π) :
    IsQuadraticallyPresented R N := by
  rcases m.eq_zero_or_pos with rfl | hm
  · have : Subsingleton P₀ := b₀.equivFun.toEquiv.subsingleton
    have : Subsingleton N := hπ.subsingleton
    exact of_subsingleton
  · exact (QuadraticPresentation.ofExact hm b₁ b₀ hf hπ).isQuadraticallyPresented

/-- A finite free module is quadratically presented: by the zero relation matrix of
`QuadraticPresentation.ofBasis` in positive rank, and by `R →(1) R` in rank zero. -/
theorem of_free [Module.Free R N] [Module.Finite R N] : IsQuadraticallyPresented R N := by
  cases subsingleton_or_nontrivial R
  · have := Module.subsingleton R N
    exact of_subsingleton
  let b := Module.finBasis R N
  rcases (finrank R N).eq_zero_or_pos with h | h
  · have : Subsingleton N := (b.reindex (finCongr h)).equivFun.toEquiv.subsingleton
    exact of_subsingleton
  · exact (QuadraticPresentation.ofBasis h b).isQuadraticallyPresented

end IsQuadraticallyPresented

/-- A module is quadratically presented iff it is isomorphic to the cokernel of a square matrix
of positive size. -/
theorem isQuadraticallyPresented_iff_exists_linearEquiv :
    IsQuadraticallyPresented R N ↔ ∃ m, 0 < m ∧ ∃ A : Matrix (Fin m) (Fin m) R,
      Nonempty (((Fin m → R) ⧸ LinearMap.range (Matrix.toLin' A)) ≃ₗ[R] N) := by
  refine ⟨fun ⟨P⟩ ↦ ⟨P.size, P.size_pos, P.rel, ⟨P.cokernelEquiv⟩⟩, ?_⟩
  rintro ⟨m, hm, A, ⟨e⟩⟩
  exact ((QuadraticPresentation.cokernel hm A).map e).isQuadraticallyPresented

/-- A quotient `R ⧸ I` is quadratically presented iff `I` is principal: its zeroth Fitting ideal
is `I`. -/
theorem isQuadraticallyPresented_quotient_iff (I : Ideal R) :
    IsQuadraticallyPresented R (R ⧸ I) ↔ I.IsPrincipal := by
  refine ⟨fun h ↦ fittingIdeal_quotient_zero I ▸ h.isPrincipal_fittingIdeal, fun hI ↦ ?_⟩
  obtain ⟨a, rfl⟩ := hI.principal
  exact (QuadraticPresentation.quotientSpanSingleton a).isQuadraticallyPresented

/-- Over a ring with finitely many maximal ideals, a module presented by an exact sequence
`P₁ → P₀ → N → 0` of finite flat modules (for instance finite projective modules) whose ranks
at every maximal ideal are all equal to the same `r` is quadratically presented: `P₀` and `P₁`
are free of rank `r`. -/
theorem isQuadraticallyPresented_of_finite_maximalSpectrum [Finite (MaximalSpectrum R)]
    {P₀ P₁ : Type*} [AddCommGroup P₀] [Module R P₀] [AddCommGroup P₁] [Module R P₁]
    [Module.Finite R P₀] [Module.Flat R P₀] [Module.Finite R P₁] [Module.Flat R P₁]
    {f : P₁ →ₗ[R] P₀} {π : P₀ →ₗ[R] N} (hf : Function.Exact f π) (hπ : Function.Surjective π)
    {r : ℕ} (h₀ : ∀ 𝔪 : MaximalSpectrum R, rankAtStalk P₀ 𝔪.toPrimeSpectrum = r)
    (h₁ : ∀ 𝔪 : MaximalSpectrum R, rankAtStalk P₁ 𝔪.toPrimeSpectrum = r) :
    IsQuadraticallyPresented R N := by
  obtain ⟨b₀⟩ := Module.nonempty_basis_of_flat_of_finrank_eq R P₀ r fun 𝔪 ↦
    (finrank_quotient_tensorProduct_eq_rankAtStalk P₀ 𝔪).trans (h₀ 𝔪)
  obtain ⟨b₁⟩ := Module.nonempty_basis_of_flat_of_finrank_eq R P₁ r fun 𝔪 ↦
    (finrank_quotient_tensorProduct_eq_rankAtStalk P₁ 𝔪).trans (h₁ 𝔪)
  exact .of_exact b₁ b₀ hf hπ

end TauCeti
