/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Dual.BaseChange
public import Mathlib.LinearAlgebra.TensorProduct.RightExactness
public import Mathlib.RingTheory.Kaehler.TensorProduct
public import Mathlib.RingTheory.LocalRing.ResidueField.Ideal
public import Mathlib.RingTheory.TensorProduct.Finite
public import TauCeti.RingTheory.FittingIdeal.Generators

/-!
# Base change of Fitting ideals

For an `R`-algebra `S` and a finite `R`-module `M`, the Fitting ideals of `S ⊗[R] M` are the
extensions of those of `M`: `Fitt_k(S ⊗[R] M) = Fitt_k(M) S`. A surjection from a finite free
module onto `M` base changes to a surjection onto `S ⊗[R] M`. By right exactness of the tensor
product, its kernel is the base change of the original kernel, and the minors of these relations
generate the extension of the ideal of minors of the original relations.

Since localization is a base change (`IsLocalizedModule.isBaseChange`), the Fitting ideals of a
module commute with localization. This is the compatibility needed for the Fitting ideals of a
quasi-coherent module of finite type to glue to a quasi-coherent ideal sheaf; for the sheaf of
relative differentials, this compatibility is used in constructing the intended singular-locus
ideal.

Base change to a field `K` detects the rank of the fibre: `Fitt_k(M)` extends to the zero ideal
of `K` exactly when `K ⊗[R] M` has dimension greater than `k`. For the residue field `κ(p)` of a
prime `p`, this identifies the zero locus of `Fitt_k(M)`: `Fitt_k(M) ⊆ p` exactly when the fibre
`κ(p) ⊗[R] M` has dimension greater than `k`.

The Kähler differentials of a base change are the base change of the Kähler differentials, so
their Fitting ideals, which cut out the singular locus of a relative curve, are compatible with
base change of the ground ring: if `B = S ⊗[R] A`, then `Fitt_k(Ω[B⁄S]) = Fitt_k(Ω[A⁄R]) B`.

## Main results

* `IsBaseChange.minorsIdeal_span_image`: the minors ideals of the `S`-span of the image of a
  submodule `N` of a free module of finite rank under a base change are the extensions of the
  minors ideals of `N`.
* `Submodule.minorsIdeal_baseChange`: the same for `N.baseChange S`.
* `TauCeti.fittingIdeal_baseChange`: `Fitt_k(S ⊗[R] M) = Fitt_k(M) S`.
* `IsBaseChange.fittingIdeal_eq_map`: the same for any base change of `M`, in particular for a
  localization of `M`.
* `TauCeti.fittingIdeal_map_eq_bot_iff_lt_finrank`: `Fitt_k(M) K = 0` for a field `K` exactly
  when `k < dim_K K ⊗[R] M`.
* `TauCeti.fittingIdeal_le_iff_lt_finrank`: `Fitt_k(M) ⊆ p` exactly when
  `k < dim_{κ(p)} κ(p) ⊗[R] M`.
* `TauCeti.fittingIdeal_kaehlerDifferential_eq_map`: `Fitt_k(Ω[B⁄S]) = Fitt_k(Ω[A⁄R]) B` for
  `B = S ⊗[R] A`.

## References

* [Stacks Project, Tag 07ZA](https://stacks.math.columbia.edu/tag/07ZA), part (3): Fitting ideals
  commute with base change.
* [Stacks Project, Tag 07ZC](https://stacks.math.columbia.edu/tag/07ZC), for the description of the
  zero locus of `Fitt_k(M)` by the dimensions of the fibres of `M`.
-/

public section

noncomputable section

open LinearMap Module TensorProduct

namespace IsBaseChange

variable {R S F W : Type*} [CommRing R] [CommRing S] [Algebra R S] [AddCommGroup F] [Module R F]
  [AddCommGroup W] [Module R W] [Module S W] [IsScalarTower R S W] {j : F →ₗ[R] W}

/-- Let `j : F → W` exhibit `W` as the base change of a free `R`-module `F` of finite rank to `S`.
The minors ideals of the `S`-submodule of `W` spanned by the image of a submodule `N` of `F` are
the extensions to `S` of the minors ideals of `N`. -/
theorem minorsIdeal_span_image [Free R F] [Module.Finite R F] (hj : IsBaseChange S j)
    (N : Submodule R F) (p : ℕ) :
    (Submodule.span S (j '' N)).minorsIdeal p = (N.minorsIdeal p).map (algebraMap R S) := by
  have hmap (f : Fin p → Dual R F) (v : Fin p → F) :
      (Matrix.of fun i k ↦ hj.toDual (f k) (j (v i))).det =
        algebraMap R S (Matrix.of fun i k ↦ f k (v i)).det := by
    rw [RingHom.map_det]
    congr 1
    ext i k
    simp [toDual_comp_apply]
  refine le_antisymm ?_ (Ideal.map_le_iff_le_comap.2 <| Submodule.minorsIdeal_le_iff.2 ?_)
  · rw [Submodule.minorsIdeal_span, TauCeti.minorsIdealOfSet_def]
    refine Ideal.span_le.2 ?_
    rintro _ ⟨g, w, hw, rfl⟩
    choose v hv hvw using hw
    obtain rfl : w = fun i ↦ j (v i) := funext fun i ↦ (hvw i).symm
    -- The determinant is multilinear in the functionals `g k`, which are `S`-linear combinations
    -- of base changes of functionals on `F` since `Dual S W` is the base change of `Dual R F`.
    let μ : MultilinearMap S (fun _ : Fin p ↦ Dual S W) S :=
      (Matrix.detRowAlternating.compLinearMap
        (LinearMap.pi fun i ↦ LinearMap.applyₗ (j (v i)))).toMultilinearMap
    have hμ (g : Fin p → Dual S W) : μ g = (Matrix.of fun i k ↦ g k (j (v i))).det := by
      rw [← Matrix.det_transpose]
      simp only [μ, Matrix.detRowAlternating_compLinearMap_pi_apply,
        LinearMap.applyₗ_apply_apply]
      apply congrArg Matrix.det
      ext i k
      simp only [Matrix.transpose_apply, Matrix.of_apply]
    have hg (k : Fin p) : g k ∈ Submodule.span S (Set.range hj.toDual) :=
      hj.dual.inductionOn (g k) (fun f ↦ Submodule.subset_span ⟨f, rfl⟩)
        (fun s _ h ↦ Submodule.smul_mem _ s h) fun _ _ h₁ h₂ ↦ add_mem h₁ h₂
    rw [SetLike.mem_coe, ← hμ]
    refine Submodule.span_le.2 ?_ (μ.map_mem_span_image_pi (fun _ ↦ Set.range hj.toDual) hg)
    rintro _ ⟨g', hg', rfl⟩
    choose f hf using fun k ↦ hg' k trivial
    obtain rfl : g' = fun k ↦ hj.toDual (f k) := funext fun k ↦ (hf k).symm
    rw [SetLike.mem_coe, hμ, hmap]
    exact Ideal.mem_map_of_mem _ (Submodule.det_mem_minorsIdeal f hv)
  · intro f v hv
    rw [Ideal.mem_comap, ← hmap]
    exact Submodule.det_mem_minorsIdeal _ fun i ↦ Submodule.subset_span ⟨v i, hv i, rfl⟩

end IsBaseChange

namespace Submodule

variable {R F : Type*} (S : Type*) [CommRing R] [CommRing S] [Algebra R S] [AddCommGroup F]
  [Module R F]

/-- The minors ideals of the base change of a submodule of a free module of finite rank are the
extensions of its minors ideals. -/
@[simp]
theorem minorsIdeal_baseChange [Free R F] [Module.Finite R F] (N : Submodule R F) (p : ℕ) :
    (N.baseChange S).minorsIdeal p = (N.minorsIdeal p).map (algebraMap R S) := by
  rw [baseChange_eq_span, map_coe]
  exact (TensorProduct.isBaseChange R F S).minorsIdeal_span_image N p

end Submodule

namespace TauCeti

variable {R M : Type*} (S : Type*) [CommRing R] [CommRing S] [Algebra R S] [AddCommGroup M]
  [Module R M] [Module.Finite R M]

variable (M) in
/-- **Fitting ideals commute with base change**: `Fitt_k(S ⊗[R] M) = Fitt_k(M) S`. -/
@[simp]
theorem fittingIdeal_baseChange (k : ℕ) :
    fittingIdeal S (S ⊗[R] M) k = (fittingIdeal R M k).map (algebraMap R S) := by
  nontriviality S
  have := (algebraMap R S).domain_nontrivial
  obtain ⟨n, φ, hφ⟩ := Module.Finite.exists_fin' R M
  -- By right exactness, `S ⊗ ker φ → S ⊗ Rⁿ → S ⊗ M → 0` is a presentation of `S ⊗ M`, so the
  -- kernel of `φ.baseChange S` is the range `(ker φ).baseChange S` of `S ⊗ ker φ`.
  have hker : ker (φ.baseChange S) = (ker φ).baseChange S :=
    exact_iff.1 (lTensor_exact S φ.exact_subtype_ker_map hφ)
  rw [fittingIdeal_eq_minorsIdeal_ker hφ,
    fittingIdeal_eq_minorsIdeal_ker (baseChange_surjective S hφ), hker, finrank_baseChange,
    Submodule.minorsIdeal_baseChange]

end TauCeti

namespace IsBaseChange

variable {R M M' : Type*} {S : Type*} [CommRing R] [CommRing S] [Algebra R S] [AddCommGroup M]
  [Module R M] [Module.Finite R M] [AddCommGroup M'] [Module R M'] [Module S M']
  [IsScalarTower R S M'] {g : M →ₗ[R] M'}

open TauCeti in
/-- **Fitting ideals commute with base change**: if `g : M → M'` exhibits `M'` as the base change
of `M` to `S`, then `Fitt_k(M') = Fitt_k(M) S`. This applies to localizations of `M` by
`IsLocalizedModule.isBaseChange`. -/
theorem fittingIdeal_eq_map (hg : IsBaseChange S g) (k : ℕ) :
    (letI : Module.Finite S M' := Module.Finite.equiv hg.equiv
     fittingIdeal S M' k) = (fittingIdeal R M k).map (algebraMap R S) := by
  let : Module.Finite S M' := Module.Finite.equiv hg.equiv
  rw [← fittingIdeal_congr hg.equiv, fittingIdeal_baseChange]

end IsBaseChange

namespace TauCeti

variable {R F M : Type*} [CommRing R] [AddCommGroup F] [Module R F] [AddCommGroup M]
  [Module R M] [Module.Finite R M]

/-- The extension of `Fitt_k(M)` to a field `K` vanishes exactly when the fibre `K ⊗[R] M` has
dimension greater than `k`. -/
@[simp]
theorem fittingIdeal_map_eq_bot_iff_lt_finrank (K : Type*) [Field K] [Algebra R K] (k : ℕ) :
    (fittingIdeal R M k).map (algebraMap R K) = ⊥ ↔ k < finrank K (K ⊗[R] M) := by
  rw [← not_le, ← fittingIdeal_eq_top_iff_finrank_le, fittingIdeal_baseChange]
  -- An ideal of the field `K` is `⊥` or `⊤`.
  rcases Ideal.eq_bot_or_top ((fittingIdeal R M k).map (algebraMap R K)) with h | h <;> simp [h]

/-- The zero locus of the `k`-th Fitting ideal of a finite module `M` is the set of primes `p` at
which the fibre `κ(p) ⊗[R] M` has dimension greater than `k`. -/
@[simp]
theorem fittingIdeal_le_iff_lt_finrank (p : Ideal R) [p.IsPrime] (k : ℕ) :
    fittingIdeal R M k ≤ p ↔ k < finrank p.ResidueField (p.ResidueField ⊗[R] M) := by
  rw [← fittingIdeal_map_eq_bot_iff_lt_finrank, Ideal.map_eq_bot_iff_le_ker,
    Ideal.ker_algebraMap_residueField]

section Kaehler

variable (R S A B : Type*) [CommRing R] [CommRing S] [Algebra R S] [CommRing A] [CommRing B]
  [Algebra R A] [Algebra R B] [Algebra A B] [Algebra S B] [IsScalarTower R A B]
  [IsScalarTower R S B] [Algebra.IsPushout R S A B] [Module.Finite A Ω[A⁄R]]

/-- **Fitting ideals of Kähler differentials commute with base change**: if `B = S ⊗[R] A`, then
`Fitt_k(Ω[B⁄S]) = Fitt_k(Ω[A⁄R]) B`, since `Ω[B⁄S]` is the base change `B ⊗[A] Ω[A⁄R]`
(`KaehlerDifferential.tensorKaehlerEquiv`). -/
theorem fittingIdeal_kaehlerDifferential_eq_map (k : ℕ) :
    (haveI : Module.Finite B Ω[B⁄S] := .equiv (KaehlerDifferential.tensorKaehlerEquiv R S A B)
     fittingIdeal B Ω[B⁄S] k) = (fittingIdeal A Ω[A⁄R] k).map (algebraMap A B) := by
  have : Module.Finite B Ω[B⁄S] := .equiv (KaehlerDifferential.tensorKaehlerEquiv R S A B)
  rw [← fittingIdeal_congr (KaehlerDifferential.tensorKaehlerEquiv R S A B),
    fittingIdeal_baseChange]

end Kaehler

end TauCeti
