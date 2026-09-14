/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Matrix.FiniteDimensional
public import TauCeti.Algebra.Module.ProjectiveCover.Basic
public import TauCeti.RingTheory.CompositionSeries.Additivity
public import TauCeti.RingTheory.Semisimple.Schur

/-!
# Hom out of a projective cover counts composition factors

Let `k` be a field, `A` a `k`-algebra, `S` a simple `A`-module and `f : P →ₗ[A] S` a projective
cover of `S`. This file proves the multiplicity formula

`dim_k Hom_A(P, M) = [M : S] · dim_k End_A(S)`,

where `[M : S]` is the Jordan--Hölder multiplicity `TauCeti.jordanHolderMultiplicity`. It is the
integral pairing between projectives and modules made explicit: reading `dim_k Hom_A(P, -)` off a
module of finite length returns its `S`-multiplicity, scaled by the dimension of the division
algebra `D = End_A(S)`. Over a splitting field `D` is `k` and the scale disappears, so the hom
dimension *is* the multiplicity; over a general field the scale is genuinely there, which is why
the raw hom dimension is not the multiplicity coordinate.

Two facts drive the proof. Since `P` is projective, `Hom_A(P, -)` is exact, so `dim_k Hom_A(P, -)`
is additive in short exact sequences. Since the kernel of a projective cover is superfluous, it
lies in the radical of `P`, which every map into a simple module annihilates; precomposition with
`f` therefore identifies `Hom_A(S, T)` with `Hom_A(P, T)` for every simple `T`, and Schur's lemma
evaluates the latter. Induction along a composition series of `M` adds up the factors.

That identification is proved for a projective cover of an arbitrary module, not just of a simple
one: a cover is invisible to a simple target.

## Main results

* `TauCeti.IsProjectiveCover.exists_comp_eq`: a map into a simple module factors through a
  projective cover of its source, and `TauCeti.IsProjectiveCover.linearMapEquiv`: precomposition
  with a projective cover `f : P →ₗ[A] M` is an isomorphism `Hom_A(M, T) ≃ₗ[k] Hom_A(P, T)` for
  every simple `T`.
* `TauCeti.finrank_linearMap_quotient_add_finrank_linearMap`: additivity of `dim_k Hom_A(P, -)`
  for a projective `P`.
* `TauCeti.IsProjectiveCover.finrank_linearMap_eq_finrank_end` and
  `TauCeti.IsProjectiveCover.finrank_linearMap_eq_zero`: the diagonal evaluation
  `dim_k Hom_A(Pᵢ, Sⱼ) = δᵢⱼ · dim_k Dᵢ`.
* `TauCeti.IsProjectiveCover.finrank_linearMap_eq_jordanHolderMultiplicity_mul_finrank_end`: **the
  multiplicity formula** `dim_k Hom_A(P, M) = [M : S] · dim_k End_A(S)`.
* `TauCeti.IsProjectiveCover.finrank_linearMap_eq_jordanHolderMultiplicity`: its split form, and
  `TauCeti.IsProjectiveCover.finrank_linearMap_eq_jordanHolderMultiplicity_of_isAlgClosed` over an
  algebraically closed field.

## References

* Peter Webb, *A Course in Finite Group Representation Theory*, Chapter 7, Section 7.4,
  Proposition 7.4.1 and Corollary 7.4.2, for the division-endomorphism form over an arbitrary
  field.
* Ibrahim Assem, Daniel Simson and Andrzej Skowroński, *Elements of the Representation Theory of
  Associative Algebras I*, Chapter I, Section 5 and Chapter III, Section 3.
-/

public section

universe w

namespace TauCeti

/-! ### A projective cover is invisible to a simple target -/

section Factorization

variable {A P M T : Type*} [Ring A] [AddCommGroup P] [Module A P] [AddCommGroup M] [Module A M]
  [AddCommGroup T] [Module A T] [IsSimpleModule A T]

/-- Every map from the source of a projective cover into a simple module factors through the
cover: the kernel of the cover is superfluous, hence contained in the radical of the source, which
the map annihilates. -/
theorem IsProjectiveCover.exists_comp_eq {f : P →ₗ[A] M} (hf : IsProjectiveCover f)
    (φ : P →ₗ[A] T) : ∃ ψ : M →ₗ[A] T, ψ ∘ₗ f = φ := by
  have hle : LinearMap.ker f ≤ LinearMap.ker φ :=
    hf.ker_le_jacobson.trans (IsSemisimpleModule.jacobson_le_ker A A P T φ)
  refine ⟨((LinearMap.ker f).liftQ φ hle) ∘ₗ
    (f.quotKerEquivOfSurjective hf.surjective).symm.toLinearMap, ?_⟩
  ext p
  have hmk : (f.quotKerEquivOfSurjective hf.surjective).symm (f p) = Submodule.Quotient.mk p := by
    rw [LinearEquiv.symm_apply_eq]
    simp [LinearMap.quotKerEquivOfSurjective]
  simp [hmk]

end Factorization

section LinearMapEquiv

variable {k A P M T : Type*} [CommSemiring k] [Ring A] [Algebra k A]
  [AddCommGroup P] [Module A P] [AddCommGroup M] [Module A M]
  [AddCommGroup T] [Module k T] [Module A T] [IsScalarTower k A T] [IsSimpleModule A T]

variable (k) in
/-- **A projective cover is invisible to a simple target.** Precomposition with a projective cover
`f : P →ₗ[A] M` is a `k`-linear isomorphism from `Hom_A(M, T)` to `Hom_A(P, T)` for every simple
`A`-module `T`: it is injective because `f` is onto, and surjective by
`TauCeti.IsProjectiveCover.exists_comp_eq`.

Compare `TauCeti.homCongrRight`, which transports a hom space along an isomorphism of its target:
here the map on the source side is only a cover, and it is the simplicity of `T` that makes the
induced map on hom spaces invertible. -/
noncomputable def IsProjectiveCover.linearMapEquiv {f : P →ₗ[A] M} (hf : IsProjectiveCover f) :
    (M →ₗ[A] T) ≃ₗ[k] (P →ₗ[A] T) :=
  LinearEquiv.ofBijective
    { toFun ψ := ψ ∘ₗ f
      map_add' _ _ := rfl
      map_smul' _ _ := rfl }
    ⟨fun ψ ψ' h => LinearMap.ext fun m => by
        obtain ⟨p, rfl⟩ := hf.surjective m
        exact DFunLike.congr_fun h p,
      fun φ => hf.exists_comp_eq φ⟩

@[simp]
theorem IsProjectiveCover.linearMapEquiv_apply {f : P →ₗ[A] M} (hf : IsProjectiveCover f)
    (ψ : M →ₗ[A] T) : hf.linearMapEquiv k ψ = ψ ∘ₗ f :=
  (rfl)

/-- The inverse of `TauCeti.IsProjectiveCover.linearMapEquiv` is the factorization through the
cover. -/
@[simp]
theorem IsProjectiveCover.linearMapEquiv_symm_comp {f : P →ₗ[A] M} (hf : IsProjectiveCover f)
    (φ : P →ₗ[A] T) : ((hf.linearMapEquiv k).symm φ) ∘ₗ f = φ := by
  rw [← IsProjectiveCover.linearMapEquiv_apply (k := k) hf ((hf.linearMapEquiv k).symm φ),
    LinearEquiv.apply_symm_apply]

end LinearMapEquiv

/-! ### Additivity of the dimension of a hom space out of a projective -/

section Additivity

variable {k A P M : Type*} [Field k] [Ring A] [Algebra k A]
  [AddCommGroup P] [Module k P] [Module A P] [IsScalarTower k A P] [FiniteDimensional k P]
  [Module.Projective A P]
  [AddCommGroup M] [Module k M] [Module A M] [IsScalarTower k A M] [FiniteDimensional k M]

variable (k P) in
/-- **`dim_k Hom_A(P, -)` is additive**, for `P` projective and finite-dimensional over `k`: the
functor `Hom_A(P, -)` is exact, so a submodule and its quotient split the dimension of the hom
space out of `P`. -/
theorem finrank_linearMap_quotient_add_finrank_linearMap (N : Submodule A M) :
    Module.finrank k (P →ₗ[A] M ⧸ N) + Module.finrank k (P →ₗ[A] N)
      = Module.finrank k (P →ₗ[A] M) := by
  have : FiniteDimensional k N :=
    Module.Finite.of_injective ((N.subtype).restrictScalars k) N.injective_subtype
  have : FiniteDimensional k (M ⧸ N) :=
    Module.Finite.of_surjective ((N.mkQ).restrictScalars k) N.mkQ_surjective
  set α : (P →ₗ[A] N) →ₗ[k] (P →ₗ[A] M) := LinearMap.compRight k N.subtype with hα
  set β : (P →ₗ[A] M) →ₗ[k] (P →ₗ[A] M ⧸ N) := LinearMap.compRight k N.mkQ with hβ
  have hβsurj : Function.Surjective β := fun g =>
    (Module.projective_lifting_property N.mkQ g N.mkQ_surjective).imp fun _ h => h
  have hαinj : Function.Injective α := fun g g' h =>
    LinearMap.ext fun p => Subtype.ext (DFunLike.congr_fun h p)
  have hker : LinearMap.ker β = LinearMap.range α := by
    ext g
    refine ⟨fun hg => ?_, ?_⟩
    · have hmem : ∀ p, g p ∈ N := fun p =>
        (Submodule.Quotient.mk_eq_zero N).mp (DFunLike.congr_fun hg p)
      exact ⟨g.codRestrict N hmem, by ext p; simp [hα]⟩
    · rintro ⟨g', rfl⟩
      ext p
      simp [hα, hβ]
  have h1 := LinearMap.finrank_range_add_finrank_ker β
  rw [hker, LinearMap.range_eq_top.mpr hβsurj, Submodule.topEquiv.finrank_eq,
    ← (LinearEquiv.ofInjective α hαinj).finrank_eq] at h1
  exact h1

end Additivity

/-! ### The multiplicity formula -/

section Multiplicity

variable {k A P S : Type*} [Field k] [Ring A] [Algebra k A]
  [AddCommGroup P] [Module A P]
  [AddCommGroup S] [Module k S] [Module A S] [IsScalarTower k A S] [IsSimpleModule A S]

variable {T : Type*} [AddCommGroup T] [Module k T] [Module A T] [IsScalarTower k A T]
  [IsSimpleModule A T]

omit [IsSimpleModule A S] in
/-- **The diagonal value of the projective/simple pairing.** If the simple module `T` is
isomorphic to `S`, the hom space out of a projective cover of `S` has the dimension of the
division algebra `End_A(S)`. -/
theorem IsProjectiveCover.finrank_linearMap_eq_finrank_end {f : P →ₗ[A] S}
    (hf : IsProjectiveCover f) (e : T ≃ₗ[A] S) :
    Module.finrank k (P →ₗ[A] T) = Module.finrank k (Module.End A S) := by
  rw [← (hf.linearMapEquiv (k := k) (T := T)).finrank_eq, ← (homCongrRight k (S := S) e).finrank_eq]

omit [Module k S] [IsScalarTower k A S] in
/-- **The off-diagonal value of the projective/simple pairing.** Between a projective cover of `S`
and a simple module not isomorphic to `S` the hom space vanishes, by Schur's lemma. -/
theorem IsProjectiveCover.finrank_linearMap_eq_zero {f : P →ₗ[A] S}
    (hf : IsProjectiveCover f) (he : IsEmpty (T ≃ₗ[A] S)) :
    Module.finrank k (P →ₗ[A] T) = 0 := by
  rw [← (hf.linearMapEquiv (k := k) (T := T)).finrank_eq]
  exact finrank_linearMap_eq_zero_of_isEmpty_linearEquiv ⟨fun e => he.elim e.symm⟩

/-- The simple case of the multiplicity formula, the step of the induction on a composition
series. -/
private theorem finrank_linearMap_simple_eq {f : P →ₗ[A] S} (hf : IsProjectiveCover f) :
    Module.finrank k (P →ₗ[A] T)
      = jordanHolderMultiplicity A T S * Module.finrank k (Module.End A S) := by
  by_cases h : Nonempty (T ≃ₗ[A] S)
  · rw [hf.finrank_linearMap_eq_finrank_end h.some,
      jordanHolderMultiplicity_eq_one_of_isSimpleModule_of_linearEquiv S h.some, one_mul]
  · rw [hf.finrank_linearMap_eq_zero (not_nonempty_iff.mp h),
      jordanHolderMultiplicity_eq_zero_of_isEmpty_linearEquiv_of_isSimpleModule S
        (not_nonempty_iff.mp h), zero_mul]

section Formula

variable [Module k P] [IsScalarTower k A P] [FiniteDimensional k P]

/-- **The multiplicity formula.** For a projective cover `f : P →ₗ[A] S` of a simple module `S`
and a module `M` of finite length, the dimension of `Hom_A(P, M)` is the Jordan--Hölder
multiplicity of `S` in `M`, scaled by the dimension of the division algebra `End_A(S)`.

The Noetherian and Artinian hypotheses on `M` follow from `FiniteDimensional k M`, but are binders
here because `TauCeti.jordanHolderMultiplicity A M S` does not elaborate without them, so a caller
holds them already in order to state the conclusion. -/
theorem IsProjectiveCover.finrank_linearMap_eq_jordanHolderMultiplicity_mul_finrank_end
    {f : P →ₗ[A] S} (hf : IsProjectiveCover f) (M : Type w) [AddCommGroup M] [Module k M]
    [Module A M] [IsScalarTower k A M] [FiniteDimensional k M] [IsNoetherian A M]
    [IsArtinian A M] :
    Module.finrank k (P →ₗ[A] M)
      = jordanHolderMultiplicity A M S * Module.finrank k (Module.End A S) := by
  have hP : Module.Projective A P := hf.projective
  have hlen : IsFiniteLength A M :=
    isFiniteLength_iff_isNoetherian_isArtinian.mpr ⟨inferInstance, inferInstance⟩
  refine IsFiniteLength.rec (motive := fun (M : Type w) _ _ _ ↦
    ∀ [Module k M] [IsScalarTower k A M] [FiniteDimensional k M] [IsNoetherian A M]
      [IsArtinian A M], Module.finrank k (P →ₗ[A] M)
        = jordanHolderMultiplicity A M S * Module.finrank k (Module.End A S)) ?_ ?_ hlen
  · intro M _ _ _ _ _ _ _ _
    rw [jordanHolderMultiplicity_eq_zero_of_subsingleton S, zero_mul]
    have : Subsingleton (P →ₗ[A] M) := ⟨fun _ _ => LinearMap.ext fun _ => Subsingleton.elim _ _⟩
    exact Module.finrank_zero_of_subsingleton
  · intro M _ _ N _ _ ih _ _ _ _ _
    have : FiniteDimensional k N :=
      Module.Finite.of_injective ((N.subtype).restrictScalars k) N.injective_subtype
    have : FiniteDimensional k (M ⧸ N) :=
      Module.Finite.of_surjective ((N.mkQ).restrictScalars k) N.mkQ_surjective
    rw [← finrank_linearMap_quotient_add_finrank_linearMap k P N, ih,
      finrank_linearMap_simple_eq hf, jordanHolderMultiplicity_eq_submodule_add_quotient (S := S) N]
    ring

/-- **The split form of the multiplicity formula.** When the simple module `S` is absolutely
simple -- its endomorphism algebra is one-dimensional -- the dimension of `Hom_A(P, M)` is the
Jordan--Hölder multiplicity of `S` in `M` on the nose. -/
theorem IsProjectiveCover.finrank_linearMap_eq_jordanHolderMultiplicity {f : P →ₗ[A] S}
    (hf : IsProjectiveCover f) (hend : Module.finrank k (Module.End A S) = 1) (M : Type w)
    [AddCommGroup M] [Module k M] [Module A M] [IsScalarTower k A M] [FiniteDimensional k M]
    [IsNoetherian A M] [IsArtinian A M] :
    Module.finrank k (P →ₗ[A] M) = jordanHolderMultiplicity A M S := by
  rw [hf.finrank_linearMap_eq_jordanHolderMultiplicity_mul_finrank_end M, hend, mul_one]

/-- Over an algebraically closed field a finite-dimensional simple module is absolutely simple, so
the dimension of `Hom_A(P, M)` is the Jordan--Hölder multiplicity of `S` in `M`. -/
theorem IsProjectiveCover.finrank_linearMap_eq_jordanHolderMultiplicity_of_isAlgClosed
    [IsAlgClosed k] [FiniteDimensional k S] {f : P →ₗ[A] S} (hf : IsProjectiveCover f)
    (M : Type w) [AddCommGroup M] [Module k M] [Module A M] [IsScalarTower k A M]
    [FiniteDimensional k M] [IsNoetherian A M] [IsArtinian A M] :
    Module.finrank k (P →ₗ[A] M) = jordanHolderMultiplicity A M S :=
  hf.finrank_linearMap_eq_jordanHolderMultiplicity
    (by rw [(endAlgEquivSelfOfIsSimpleModule (k := k) (A := A) (S := S)).toLinearEquiv.finrank_eq,
      Module.finrank_self]) M

end Formula

end Multiplicity

end TauCeti
