/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.MonoidAlgebra.Module
public import TauCeti.RingTheory.DedekindDomain.AdicValuation.FaithfullyFlat
import Mathlib.LinearAlgebra.Dimension.FreeAndStrongRankCondition
import Mathlib.LinearAlgebra.TensorProduct.Pi
import Mathlib.NumberTheory.NumberField.Completion.FinitePlace
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.TensorProduct.Free

/-!
# Locally free lattices over an order

Let `A` be a Dedekind domain with fraction field `K`, and for a height-one prime `v` of `A` let
`𝒪_v = v.adicCompletionIntegers K` be the ring of integers of the completion `K_v`. Let `Λ` be an
`A`-algebra, possibly noncommutative, for instance an `A`-order in a finite-dimensional
`K`-algebra. A left `Λ`-module `M` is a *locally free `Λ`-lattice of rank `n`* if it is finitely
generated over `A` and, for every `v`, the completion `𝒪_v ⊗[A] M` is isomorphic to
`𝒪_v ⊗[A] Λⁿ` as a module over `𝒪_v ⊗[A] Λ`. Here `𝒪_v ⊗[A] M` carries the module structure
`TauCeti.CentralBaseChange.module`, `(s ⊗ l) • (s' ⊗ m) = (s * s') ⊗ (l • m)`; an
`𝒪_v ⊗[A] Λ`-linear map between such modules is the same as an `𝒪_v`-linear map commuting with
the action of every element of `Λ`.

Locally free lattices are the objects whose classes make up the locally free class group of an
order. Free lattices are locally free, and the notion is invariant under isomorphism and additive
in direct sums. If `A` is not a field, the rank satisfies
`dim_K (K ⊗[A] M) = n * dim_K (K ⊗[A] Λ)`, so it is determined by `M` when `K ⊗[A] Λ ≠ 0`, and a
locally free lattice of rank zero vanishes. If moreover `Λ` is finite over `A`, a locally free
lattice is a finitely generated projective `Λ`-module: its completions are free, and projectivity
of a finitely presented module descends from the completions. Over a field there are no
height-one primes, so the completion condition is vacuous there.

For the monoid algebra `Λ = A[G]`, local freeness of rank one says that every completion has a
normal basis: an `𝒪_v`-basis indexed by `G` whose elements are the translates `g • b₁` of one
element. Over `Λ = A`, a nonzero ideal of `A` is locally free of rank one, since its completions
are nonzero ideals of the discrete valuation rings `𝒪_v`; a nonprincipal ideal is not free, so
local freeness does not imply freeness.

## Main definitions

* `TauCeti.LocallyFree.IsLocallyFreeOfRank A K Λ M n`: `M` is a locally free `Λ`-lattice of
  rank `n`.

## Main results

* `TauCeti.LocallyFree.IsLocallyFreeOfRank.of_free`: `Λⁿ` is locally free of rank `n`.
* `TauCeti.LocallyFree.IsLocallyFreeOfRank.self`: `Λ` is locally free of rank one over itself.
* `TauCeti.LocallyFree.IsLocallyFreeOfRank.of_linearEquiv`: local freeness is invariant under
  `Λ`-linear isomorphisms.
* `TauCeti.LocallyFree.IsLocallyFreeOfRank.prod`: ranks add in binary products.
* `TauCeti.LocallyFree.IsLocallyFreeOfRank.finrank`: if `A` is not a field,
  `dim_K (K ⊗[A] M) = n * dim_K (K ⊗[A] Λ)`.
* `TauCeti.LocallyFree.IsLocallyFreeOfRank.subsingleton`: if `A` is not a field, a locally free
  lattice of rank zero is zero.
* `TauCeti.LocallyFree.IsLocallyFreeOfRank.finitePresentation`: if `Λ` is finite over `A`, a
  locally free lattice is finitely presented over `Λ`.
* `TauCeti.LocallyFree.IsLocallyFreeOfRank.projective`: if `A` is not a field and `Λ` is finite
  over `A`, a locally free lattice is projective over `Λ`.
* `TauCeti.LocallyFree.isLocallyFreeOfRank_one_groupRing_iff`: over `A[G]`, local freeness of
  rank one is the existence of a normal basis of every completion.
* `TauCeti.LocallyFree.isLocallyFreeOfRank_one_of_ne_bot`: a nonzero ideal of `A` is locally
  free of rank one over `A`.
* `TauCeti.LocallyFree.not_free_of_not_isPrincipal`: a nonprincipal ideal is not free, so local
  freeness does not imply freeness.

## References

* H. Johnston, *Notes on Galois modules*, Definition 10.2 and Example 10.6.
* J. Voight, *Quaternion algebras*, Graduate Texts in Mathematics 288, Springer, 2021, 20.2.8,
  where local freeness is defined with the localizations instead of the completions, and 20.2.6,
  where locally free lattices are shown to be projective.
-/

public section

open IsDedekindDomain Module TensorProduct

attribute [local instance low] TauCeti.CentralBaseChange.module

namespace TauCeti.LocallyFree

variable (A : Type*) [CommRing A] [IsDedekindDomain A] (K : Type*) [Field K] [Algebra A K]
  [IsFractionRing A K] (Λ : Type*) [Ring Λ] [Algebra A Λ]
  (M : Type*) [AddCommGroup M] [Module A M] [Module Λ M] [IsScalarTower A Λ M]

/-- A left `Λ`-module `M` is a *locally free `Λ`-lattice of rank `n`* if it is finitely generated
over `A` and, for every height-one prime `v` of `A`, the completion `𝒪_v ⊗[A] M` is isomorphic
to `𝒪_v ⊗[A] Λⁿ` as a module over `𝒪_v ⊗[A] Λ`, where `𝒪_v = v.adicCompletionIntegers K`. The
`𝒪_v ⊗[A] Λ`-module structures are `TauCeti.CentralBaseChange.module`. -/
structure IsLocallyFreeOfRank (n : ℕ) : Prop where
  /-- A locally free lattice is finitely generated over `A`. -/
  finite : Module.Finite A M
  /-- Every completion `𝒪_v ⊗[A] M` is isomorphic to `𝒪_v ⊗[A] Λⁿ` as an `𝒪_v ⊗[A] Λ`-module. -/
  nonempty_linearEquiv (v : HeightOneSpectrum A) :
    Nonempty (v.adicCompletionIntegers K ⊗[A] M ≃ₗ[v.adicCompletionIntegers K ⊗[A] Λ]
      v.adicCompletionIntegers K ⊗[A] (Fin n → Λ))

variable {A K Λ M}

namespace IsLocallyFreeOfRank

variable (A K) in
/-- The free module `Λⁿ` is locally free of rank `n`. -/
theorem of_free [Module.Finite A Λ] (n : ℕ) : IsLocallyFreeOfRank A K Λ (Fin n → Λ) n :=
  ⟨inferInstance, fun _ ↦ ⟨.refl _ _⟩⟩

variable {N : Type*} [AddCommGroup N] [Module A N] [Module Λ N] [IsScalarTower A Λ N] {n m : ℕ}

/-- Local freeness is invariant under `Λ`-linear isomorphisms. -/
theorem of_linearEquiv (h : IsLocallyFreeOfRank A K Λ M n) (φ : M ≃ₗ[Λ] N) :
    IsLocallyFreeOfRank A K Λ N n where
  finite := have := h.finite; .equiv (φ.restrictScalars A)
  nonempty_linearEquiv v :=
    ⟨(CentralBaseChange.congr _ φ).symm.trans (h.nonempty_linearEquiv v).some⟩

variable (A K Λ) in
/-- `Λ` is locally free of rank one over itself. -/
theorem self [Module.Finite A Λ] : IsLocallyFreeOfRank A K Λ Λ 1 :=
  (of_free A K 1).of_linearEquiv (LinearEquiv.funUnique (Fin 1) Λ Λ)

/-- The product of locally free lattices of ranks `n` and `m` is locally free of rank `n + m`. -/
theorem prod (hM : IsLocallyFreeOfRank A K Λ M n) (hN : IsLocallyFreeOfRank A K Λ N m) :
    IsLocallyFreeOfRank A K Λ (M × N) (n + m) where
  finite := have := hM.finite; have := hN.finite; inferInstance
  nonempty_linearEquiv v :=
    -- `Λⁿ × Λᵐ ≃ Λⁿ⁺ᵐ`, splitting `Fin (n + m)` as `Fin n ⊕ Fin m`.
    let φ : ((Fin n → Λ) × (Fin m → Λ)) ≃ₗ[Λ] (Fin (n + m) → Λ) :=
      (LinearEquiv.sumArrowLequivProdArrow (Fin n) (Fin m) Λ Λ).symm.trans
        (LinearEquiv.funCongrLeft Λ Λ finSumFinEquiv.symm)
    ⟨(CentralBaseChange.prodRight A _ Λ M N).trans <|
      ((hM.nonempty_linearEquiv v).some.prodCongr (hN.nonempty_linearEquiv v).some).trans <|
        (CentralBaseChange.prodRight A _ Λ _ _).symm.trans (CentralBaseChange.congr _ φ)⟩

/-- The `K`-dimension of `K ⊗[A] X` is the `K_v`-dimension of `K_v ⊗[𝒪_v] (𝒪_v ⊗[A] X)`, via
`K_v ⊗[𝒪_v] (𝒪_v ⊗[A] X) ≃ K_v ⊗[A] X ≃ K_v ⊗[K] (K ⊗[A] X)`. -/
private theorem finrank_eq_finrank_adicCompletion (v : HeightOneSpectrum A) (X : Type*)
    [AddCommGroup X] [Module A X] :
    finrank K (K ⊗[A] X) = finrank (v.adicCompletion K)
      (v.adicCompletion K ⊗[v.adicCompletionIntegers K] (v.adicCompletionIntegers K ⊗[A] X)) := by
  rw [← Module.finrank_baseChange (R := v.adicCompletion K) (M' := K ⊗[A] X),
    (AlgebraTensorModule.cancelBaseChange A K (v.adicCompletion K) (v.adicCompletion K)
      X).finrank_eq,
    ← (AlgebraTensorModule.cancelBaseChange A (v.adicCompletionIntegers K) (v.adicCompletion K)
      (v.adicCompletion K) X).finrank_eq]

omit [IsDedekindDomain A] [IsFractionRing A K] in
variable (K Λ) in
/-- `dim_K (K ⊗[A] Λⁿ) = n * dim_K (K ⊗[A] Λ)`. The dimensions are compared as cardinals, since
`K ⊗[A] Λ` need not be finite-dimensional. -/
private theorem finrank_tensor_fun (n : ℕ) :
    finrank K (K ⊗[A] (Fin n → Λ)) = n * finrank K (K ⊗[A] Λ) := by
  rw [(TensorProduct.piRight A K K fun _ : Fin n ↦ Λ).finrank_eq, Module.finrank,
    rank_fun_eq_lift_mul, Cardinal.toNat_mul, Cardinal.toNat_lift, Cardinal.toNat_natCast,
    Fintype.card_fin, Module.finrank]

/-- If `A` is not a field, the dimension over the fraction field of a locally free lattice of rank
`n` is `dim_K (K ⊗[A] M) = n * dim_K (K ⊗[A] Λ)`, so `n` is determined by `M` when
`K ⊗[A] Λ ≠ 0`. -/
theorem finrank (hA : ¬IsField A) (h : IsLocallyFreeOfRank A K Λ M n) :
    finrank K (K ⊗[A] M) = n * finrank K (K ⊗[A] Λ) := by
  obtain ⟨J, hJ⟩ := Ideal.exists_maximal A
  let v : HeightOneSpectrum A := ⟨J, hJ.isPrime, Ring.ne_bot_of_isMaximal_of_not_isField hJ hA⟩
  let S := v.adicCompletionIntegers K
  -- Compare both sides over `K_v` at one height-one prime `v`.
  let e := ((h.nonempty_linearEquiv v).some.restrictScalars S).baseChange S (v.adicCompletion K) _ _
  rw [finrank_eq_finrank_adicCompletion v, e.finrank_eq, ← finrank_eq_finrank_adicCompletion v,
    finrank_tensor_fun]

/-- If `A` is not a field, a locally free lattice of rank zero is zero. -/
theorem subsingleton (hA : ¬IsField A) (h : IsLocallyFreeOfRank A K Λ M 0) : Subsingleton M :=
  (subsingleton_iff_forall_subsingleton_adicCompletionIntegers_tensor K M hA).mpr fun v ↦
    (h.nonempty_linearEquiv v).some.toEquiv.subsingleton

/-- If `Λ` is finite over `A`, a locally free lattice is finitely presented over `Λ`: `Λ` is left
noetherian, being finite over the noetherian ring `A`, and `M` is finitely generated over `Λ`
since it is so over `A`. -/
theorem finitePresentation [Module.Finite A Λ] (h : IsLocallyFreeOfRank A K Λ M n) :
    Module.FinitePresentation Λ M :=
  have := h.finite
  have := IsNoetherianRing.of_finite A Λ
  have := Module.Finite.of_restrictScalars_finite A Λ M
  Module.finitePresentation_of_finite Λ M

/-- **Locally free lattices are projective.** If `A` is not a field and `Λ` is finite over `A`, a
locally free `Λ`-lattice is a finitely generated projective `Λ`-module: every completion
`𝒪_v ⊗[A] M ≃ 𝒪_v ⊗[A] Λⁿ` is free over `𝒪_v ⊗[A] Λ`, and projectivity of the finitely
presented module `M` descends from the completions. Finite generation over `Λ` is
`finitePresentation`. -/
theorem projective [Module.Finite A Λ] (hA : ¬IsField A) (h : IsLocallyFreeOfRank A K Λ M n) :
    Module.Projective Λ M :=
  have := h.finitePresentation
  have (v : HeightOneSpectrum A) : Module.Projective (v.adicCompletionIntegers K ⊗[A] Λ)
      (v.adicCompletionIntegers K ⊗[A] M) :=
    .of_equiv (h.nonempty_linearEquiv v).some.symm
  projective_of_forall_projective_adicCompletionIntegers K hA

end IsLocallyFreeOfRank

section GroupRing

variable {G : Type*} [Monoid G] [Module (MonoidAlgebra A G) M]
  [IsScalarTower A (MonoidAlgebra A G) M]

variable (A G) in
/-- The basis `1 ⊗ (g)` of `S ⊗[A] A[G]¹` over `S`, indexed by `G`. -/
private noncomputable def tensorBasis (S : Type*) [CommRing S] [Algebra A S] :
    Basis G S (S ⊗[A] (Fin 1 → MonoidAlgebra A G)) :=
  Algebra.TensorProduct.basis S
    ((MonoidAlgebra.basis G A).map (LinearEquiv.funUnique (Fin 1) A (MonoidAlgebra A G)).symm)

omit [IsDedekindDomain A] in
/-- The basis vector `1 ⊗ (g)` is the translate of `1 ⊗ (1)` by `g`. -/
private theorem tensorBasis_apply (S : Type*) [CommRing S] [Algebra A S] (g : G) :
    tensorBasis A G S g =
      ((1 : S) ⊗ₜ[A] MonoidAlgebra.single g (1 : A)) • ((1 : S) ⊗ₜ[A] Pi.single 0 1) := by
  rw [CentralBaseChange.tmul_smul_tmul, mul_one, ← Pi.single_smul, smul_eq_mul, mul_one]
  simp only [tensorBasis, Algebra.TensorProduct.basis_apply, Basis.map_apply,
    MonoidAlgebra.basis_apply]
  congr 1
  ext i
  simp [Subsingleton.elim i 0]

/-- **Locally free lattices of rank one over a monoid algebra.** A module `M` over `A[G]` is
locally free of rank one if and only if it is finitely generated over `A` and every completion
`𝒪_v ⊗[A] M` has a normal basis: an `𝒪_v`-basis `b` indexed by `G` with `b g = g • b 1`. -/
theorem isLocallyFreeOfRank_one_groupRing_iff :
    IsLocallyFreeOfRank A K (MonoidAlgebra A G) M 1 ↔ Module.Finite A M ∧
      ∀ v : HeightOneSpectrum A, ∃ b : Basis G (v.adicCompletionIntegers K)
        (v.adicCompletionIntegers K ⊗[A] M), ∀ g : G,
          b g = ((1 : v.adicCompletionIntegers K) ⊗ₜ[A] MonoidAlgebra.single g (1 : A)) • b 1 := by
  refine ⟨fun h ↦ ⟨h.finite, fun v ↦ ?_⟩, fun ⟨hfin, h⟩ ↦ ⟨hfin, fun v ↦ ?_⟩⟩
  · -- Transport the basis `1 ⊗ (g)` of `𝒪_v ⊗[A] A[G]¹` along the local isomorphism.
    let e := (h.nonempty_linearEquiv v).some
    refine ⟨(tensorBasis A G _).map (e.symm.restrictScalars _), fun g ↦ ?_⟩
    simp only [Basis.map_apply, LinearEquiv.restrictScalars_apply, tensorBasis_apply, map_smul,
      ← MonoidAlgebra.one_def, ← Algebra.TensorProduct.one_def, one_smul]
  · -- The `𝒪_v ⊗[A] A[G]`-linear map `𝒪_v ⊗[A] A[G]¹ → 𝒪_v ⊗[A] M` sending `1 ⊗ (1)` to `b 1`
    -- carries the basis `1 ⊗ (g)` to `b`, so it is an isomorphism.
    obtain ⟨b, hb⟩ := h v
    let ψ := (CentralBaseChange.freeHomEquiv A (v.adicCompletionIntegers K) (MonoidAlgebra A G) M
      (Fin 1)).symm fun _ ↦ b 1
    have hψ : ψ.restrictScalars (v.adicCompletionIntegers K) =
        ((tensorBasis A G _).equiv b (.refl G)).toLinearMap :=
      (tensorBasis A G _).ext fun g ↦ by
        rw [LinearMap.restrictScalars_apply, LinearEquiv.coe_coe, Basis.equiv_apply,
          Equiv.refl_apply, hb, tensorBasis_apply, map_smul,
          CentralBaseChange.freeHomEquiv_symm_apply_tmul_single]
    have hbij : Function.Bijective ψ := by
      rw [← LinearMap.coe_restrictScalars (v.adicCompletionIntegers K) ψ, hψ]
      exact LinearEquiv.bijective _
    exact ⟨(LinearEquiv.ofBijective ψ hbij).symm⟩

end GroupRing

section Ideal

/-- A nonzero ideal `I` of `A` is locally free of rank one over `A`. -/
theorem isLocallyFreeOfRank_one_of_ne_bot {I : Ideal A} (hI : I ≠ ⊥) :
    IsLocallyFreeOfRank A K A I 1 where
  finite := inferInstance
  nonempty_linearEquiv v := by
    -- The completion of the inclusion `I → A` is injective since `𝒪_v` is flat over `A`, and its
    -- image is a nonzero ideal of the discrete valuation ring `𝒪_v`.
    let f : v.adicCompletionIntegers K ⊗[A] I →ₗ[v.adicCompletionIntegers K]
        v.adicCompletionIntegers K :=
      (AlgebraTensorModule.rid A _ _).toLinearMap ∘ₗ I.subtype.baseChange _
    have hf : Function.Injective f :=
      (AlgebraTensorModule.rid A _ _).injective.comp
        (Module.Flat.lTensor_preserves_injective_linearMap _ I.injective_subtype)
    obtain ⟨x, hx⟩ := (IsPrincipalIdealRing.principal (LinearMap.range f)).principal
    have hx0 : x ≠ 0 := by
      rintro rfl
      obtain ⟨a, ha, ha0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hI
      have : f (1 ⊗ₜ ⟨a, ha⟩) ∈ LinearMap.range f := LinearMap.mem_range_self f _
      rw [hx, Submodule.span_singleton_eq_bot.mpr rfl, Submodule.mem_bot] at this
      simp only [f, LinearMap.coe_comp, Function.comp_apply, LinearMap.baseChange_tmul,
        Submodule.coe_subtype, LinearEquiv.coe_coe, AlgebraTensorModule.rid_tmul,
        Algebra.smul_def, mul_one] at this
      exact ha0 (FaithfulSMul.algebraMap_injective A _ (this.trans (map_zero _).symm))
    -- `𝒪_v ⊗[A] I ≃ range f = (x) ≃ 𝒪_v ≃ 𝒪_v ⊗[A] A¹`, and `𝒪_v`-linear maps are
    -- `𝒪_v ⊗[A] A`-linear since `𝒪_v → 𝒪_v ⊗[A] A` is surjective.
    have hsurj : Function.Surjective (algebraMap (v.adicCompletionIntegers K)
        (v.adicCompletionIntegers K ⊗[A] A)) := fun t ↦
      let r := Algebra.TensorProduct.rid A (v.adicCompletionIntegers K) (v.adicCompletionIntegers K)
      ⟨r t, r.injective (by simp [r])⟩
    exact ⟨LinearEquiv.extendScalarsOfSurjective hsurj <| (LinearEquiv.ofInjective f hf).trans <|
      (LinearEquiv.ofEq _ _ hx).trans <|
        (LinearEquiv.toSpanNonzeroSingleton _ _ x hx0).symm.trans <|
          (AlgebraTensorModule.rid A _ _).symm.trans
            ((LinearEquiv.funUnique (Fin 1) A A).symm.baseChange A _ _ _)⟩

omit [IsDedekindDomain A] in
/-- **Local freeness does not imply freeness.** A nonprincipal ideal `I` of `A` is not a free
`A`-module. Over a Dedekind domain it is still locally free of rank one, by
`isLocallyFreeOfRank_one_of_ne_bot`. -/
theorem not_free_of_not_isPrincipal [Nontrivial A] {I : Ideal A} (hI : ¬I.IsPrincipal) :
    ¬Module.Free A I :=
  -- A free ideal has rank at most one, hence is principal.
  fun _ ↦ hI <|
    (Submodule.rank_le_one_iff_isPrincipal I).mp ((Submodule.rank_le I).trans_eq (rank_self A))

end Ideal

end TauCeti.LocallyFree
