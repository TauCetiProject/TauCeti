/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.BigOperators.Finprod
public import Mathlib.Order.PiLex
public import Mathlib.Order.WellFoundedSet
public import TauCeti.RingTheory.LocalRing.HilbertSamuel
public import TauCeti.RingTheory.MvPowerSeries.FormalDivision
import Mathlib.LinearAlgebra.Isomorphisms
import Mathlib.RingTheory.LocalRing.Length
import TauCeti.Data.Finsupp.UpperSet
import TauCeti.Data.Finsupp.Weight
import TauCeti.RingTheory.LocalRing.ResidueField.Quotient

/-!
# Hilbert–Samuel functions of ideals in multivariate formal power series

For any local commutative ring `R`, the residue field of `MvPowerSeries σ R` is canonically
`R`-isomorphic to `IsLocalRing.ResidueField R`, so the `MvPowerSeries σ R`-length of any module
equals its `R`-module length (`MvPowerSeries.length_restrictScalars`).

Over a field `K` in finitely many variables `σ`, given a degree-compatible monomial order
`ord : MonomialOrder σ` — one satisfying `Monotone (Finsupp.degree ∘ ord.toSyn.symm)`, such as
`MonomialOrder.degLex` — Hironaka's normal-form remainder `ord.normalRemainder I` preserves every
power `𝔪 ^ n` of the maximal ideal (`MonomialOrder.normalRemainder_mem_maximalIdeal_pow`).
Evaluating the coefficients of `ord.normalRemainder I f` on exponents of degree `< n` outside
`ord.initialDiagram I` induces a canonical `K`-linear isomorphism
`MvPowerSeries σ K ⧸ (I ⊔ 𝔪 ^ n) ≃ₗ[K] (({α | α.degree < n} \ ord.initialDiagram I) → K)`
(`MonomialOrder.quotientSupMaximalIdealPowEquiv`).

Taking lengths yields the diagram formula for the Hilbert–Samuel function
(`MonomialOrder.hilbertSamuel_eq_ncard_degree_le_sdiff_initialDiagram`):
`I.hilbertSamuel ℓ = ({α : σ →₀ ℕ | α.degree ≤ ℓ} \ ord.initialDiagram I).ncard`.
In particular, `(⊥ : Ideal (MvPowerSeries σ K)).hilbertSamuel ℓ = (card σ + ℓ).choose (card σ)`
(`Ideal.hilbertSamuel_mvPowerSeries_bot`). Combining the diagram formula with the lexicographic
well-foundedness of complement-counting functions of upper sets in `σ →₀ ℕ`
(`Finsupp.isWF_range_toLex_ncard_degree_le_sdiff`) yields Bierstone–Milman's stabilization theorem:
the set of Hilbert–Samuel functions realized by ideals of `MvPowerSeries σ K` is well-founded in
`Lex (ℕ → ℕ∞)` (`MvPowerSeries.isWF_range_toLex_hilbertSamuel`), so every lexicographically — and in
particular every pointwise — antitone sequence of Hilbert–Samuel functions of ideals in
`MvPowerSeries σ K` stabilizes (`MvPowerSeries.exists_hilbertSamuel_eq_of_antitone_lex`,
`MvPowerSeries.exists_hilbertSamuel_eq_of_antitone`).

## Main definitions

* `MonomialOrder.quotientSupMaximalIdealPowEquiv`: canonical `K`-linear isomorphism identifying
  `MvPowerSeries σ K ⧸ (I ⊔ 𝔪 ^ n)` with functions on `{α | α.degree < n} \ ord.initialDiagram I`.

## Main results

* `MvPowerSeries.length_restrictScalars`: module length over `MvPowerSeries σ R` agrees with
  `R`-module length for any local commutative ring `R`.
* `MonomialOrder.hilbertSamuel_eq_ncard_degree_le_sdiff_initialDiagram`: `I.hilbertSamuel ℓ`
  counts exponents of degree at most `ℓ` outside `ord.initialDiagram I`.
* `Ideal.hilbertSamuel_mvPowerSeries_bot`: `(⊥ : Ideal (MvPowerSeries σ K)).hilbertSamuel ℓ` equals
  `(Fintype.card σ + ℓ).choose (Fintype.card σ)`.
* `MvPowerSeries.isWF_range_toLex_hilbertSamuel`: the set of Hilbert–Samuel functions realized by
  ideals of `MvPowerSeries σ K` is well-founded in `Lex (ℕ → ℕ∞)`.
* `MvPowerSeries.exists_hilbertSamuel_eq_of_antitone_lex`,
  `MvPowerSeries.exists_hilbertSamuel_eq_of_antitone`: lexicographic and pointwise Hilbert–Samuel
  stabilization for sequences of ideals in `MvPowerSeries σ K`.

## References

* Edward Bierstone and Pierre D. Milman, *Uniformization of analytic spaces*, J. Amer. Math. Soc. 2
  (1989), 801–836, Theorem 5.2.1 (pp. 820–821).
* Edward Bierstone and Pierre D. Milman, *Canonical desingularization in characteristic zero by
  blowing up the maximum strata of a local invariant*, Invent. Math. 128 (1997), 207–302,
  Corollary 3.20 (p. 239).
-/

public section

open scoped MonomialOrder

namespace MvPowerSeries

/-- For any `MvPowerSeries σ R`-module `M` over a local commutative ring `R`, its `R`-module length
equals its `MvPowerSeries σ R`-module length, since the residue field of `MvPowerSeries σ R` is
`R`-isomorphic to `IsLocalRing.ResidueField R`. -/
theorem length_restrictScalars {σ R M : Type*} [CommRing R] [IsLocalRing R]
    [AddCommGroup M] [Module R M] [Module (MvPowerSeries σ R) M]
    [IsScalarTower R (MvPowerSeries σ R) M] :
    Module.length R M = Module.length (MvPowerSeries σ R) M := by
  have : IsLocalHom (algebraMap R (MvPowerSeries σ R)) :=
    isLocalHom_of_leftInverse MvPowerSeries.constantCoeff fun r ↦ by simp [algebraMap_apply]
  let ev : MvPowerSeries σ R →ₐ[R] IsLocalRing.ResidueField R :=
    { (IsLocalRing.residue R).comp MvPowerSeries.constantCoeff with
      commutes' := fun r ↦ by simp [IsLocalRing.ResidueField.algebraMap_eq, algebraMap_apply] }
  have hev : Function.Surjective ev := fun x ↦ by
    obtain ⟨r, rfl⟩ := IsLocalRing.residue_surjective x
    exact ⟨algebraMap R _ r, by simp [ev.commutes, IsLocalRing.ResidueField.algebraMap_eq]⟩
  have hres : Module.length (IsLocalRing.ResidueField R)
      (IsLocalRing.ResidueField (MvPowerSeries σ R)) = 1 := by
    rw [← Module.length_eq_of_surjective (S := R) (IsLocalRing.residue_surjective (R := R)),
      (TauCeti.residueFieldAlgEquivOfSurjective hev).toLinearEquiv.length_eq,
      Module.length_eq_of_surjective (S := R) (IsLocalRing.residue_surjective (R := R)),
      Module.length_eq_one]
  rw [IsLocalRing.length_restrictScalars R (MvPowerSeries σ R) M, hres, mul_one]

end MvPowerSeries

namespace MonomialOrder

section HilbertSamuel

variable {σ K : Type*} [Finite σ] [Field K] (ord : MonomialOrder σ)

/-- Coefficient-evaluation map sending `f` to the restriction of `ord.normalRemainder I f` to
exponents of degree `< n` outside `ord.initialDiagram I`. -/
private noncomputable def normalRemainderEval (I : Ideal (MvPowerSeries σ K)) (n : ℕ) :
    MvPowerSeries σ K →ₗ[K]
      (↥({α : σ →₀ ℕ | α.degree < n} \ ord.initialDiagram I) → K) :=
  LinearMap.pi fun α ↦ (MvPowerSeries.coeff α.val).comp (ord.normalRemainder I)

@[simp]
private theorem normalRemainderEval_apply (I : Ideal (MvPowerSeries σ K)) (n : ℕ)
    (f : MvPowerSeries σ K)
    (α : ↥({α : σ →₀ ℕ | α.degree < n} \ ord.initialDiagram I)) :
    ord.normalRemainderEval I n f α = MvPowerSeries.coeff α.val (ord.normalRemainder I f) := by
  simp [normalRemainderEval]

private theorem ker_normalRemainderEval (hdeg : Monotone (Finsupp.degree ∘ ord.toSyn.symm))
    (I : Ideal (MvPowerSeries σ K)) (n : ℕ) :
    LinearMap.ker (ord.normalRemainderEval I n) =
      (I ⊔ IsLocalRing.maximalIdeal (MvPowerSeries σ K) ^ n).restrictScalars K := by
  ext f
  rw [LinearMap.mem_ker, Submodule.restrictScalars_mem]
  refine ⟨fun hf ↦ ?_, fun hf ↦ ?_⟩
  · have hrem_mem : ord.normalRemainder I f ∈
        IsLocalRing.maximalIdeal (MvPowerSeries σ K) ^ n := by
      rw [MvPowerSeries.mem_maximalIdeal_pow_iff_le_order]
      refine MvPowerSeries.nat_le_order fun γ hγ ↦ ?_
      by_cases hD : γ ∈ ord.initialDiagram I
      · by_contra hc
        exact ord.notMem_initialDiagram_of_mem_support_normalRemainder I f
          (MvPowerSeries.mem_support.mpr hc) hD
      · simpa using congrFun hf ⟨γ, hγ, hD⟩
    have hsum : (f - ord.normalRemainder I f) + ord.normalRemainder I f = f := sub_add_cancel _ _
    exact hsum ▸ Submodule.add_mem_sup (ord.sub_normalRemainder_mem I f) hrem_mem
  · obtain ⟨g, hg, h, hh, rfl⟩ := Submodule.mem_sup.mp hf
    funext ⟨α, hα_deg, _⟩
    simp only [normalRemainderEval_apply, map_add, ord.normalRemainder_eq_zero_iff.mpr hg, zero_add]
    have hh' := MvPowerSeries.mem_maximalIdeal_pow_iff_le_order.mp
      (ord.normalRemainder_mem_maximalIdeal_pow hdeg I hh)
    exact MvPowerSeries.coeff_of_lt_order ((Nat.cast_lt.mpr hα_deg).trans_le hh')

private theorem normalRemainderEval_sum_monomial (I : Ideal (MvPowerSeries σ K)) (n : ℕ)
    [Fintype ↥({α : σ →₀ ℕ | α.degree < n} \ ord.initialDiagram I)]
    (v : ↥({α : σ →₀ ℕ | α.degree < n} \ ord.initialDiagram I) → K) :
    ord.normalRemainderEval I n (∑ β, MvPowerSeries.monomial β.val (v β)) = v := by
  classical
  have hg_comp : (∑ β, MvPowerSeries.monomial β.val (v β)) ∈ ord.complementSubmodule I :=
    Submodule.sum_mem _ fun β _ ↦ ord.monomial_mem_complementSubmodule_iff.mpr (Or.inr β.property.2)
  funext α
  rw [normalRemainderEval_apply,
    ord.normalRemainder_eq_self_of_mem_complementSubmodule hg_comp, map_sum,
    Finset.sum_eq_single α]
  · exact MvPowerSeries.coeff_monomial_same α.val (v α)
  · intro β _ hβα
    exact MvPowerSeries.coeff_monomial_ne (fun h ↦ hβα (Subtype.ext h.symm)) (v β)
  · intro hα
    exact absurd (Finset.mem_univ α) hα

private theorem surjective_normalRemainderEval (I : Ideal (MvPowerSeries σ K)) (n : ℕ) :
    Function.Surjective (ord.normalRemainderEval I n) := by
  have hfin : ({α : σ →₀ ℕ | α.degree < n} \ ord.initialDiagram I).Finite :=
    (Finsupp.finite_of_degree_lt n).sdiff
  have : Fintype ↥({α : σ →₀ ℕ | α.degree < n} \ ord.initialDiagram I) := hfin.fintype
  exact fun v ↦ ⟨_, ord.normalRemainderEval_sum_monomial I n v⟩

/-- For any degree-compatible monomial order `ord`, the quotient `MvPowerSeries σ K ⧸ (I ⊔ 𝔪 ^ n)`
is canonically `K`-linearly isomorphic to the space of functions on the complement of
`ord.initialDiagram I` in `{α | α.degree < n}`. -/
noncomputable def quotientSupMaximalIdealPowEquiv
    (hdeg : Monotone (Finsupp.degree ∘ ord.toSyn.symm))
    (I : Ideal (MvPowerSeries σ K)) (n : ℕ) :
    (MvPowerSeries σ K ⧸ (I ⊔ IsLocalRing.maximalIdeal (MvPowerSeries σ K) ^ n)) ≃ₗ[K]
      (↥({α : σ →₀ ℕ | α.degree < n} \ ord.initialDiagram I) → K) :=
  (Submodule.Quotient.restrictScalarsEquiv K
      (I ⊔ IsLocalRing.maximalIdeal (MvPowerSeries σ K) ^ n)).symm ≪≫ₗ
    Submodule.quotEquivOfEq _ _ (ord.ker_normalRemainderEval hdeg I n).symm ≪≫ₗ
    (ord.normalRemainderEval I n).quotKerEquivOfSurjective
      (ord.surjective_normalRemainderEval I n)

/-- Forward evaluation of `quotientSupMaximalIdealPowEquiv` on a quotient class. -/
@[simp]
theorem quotientSupMaximalIdealPowEquiv_mk
    (hdeg : Monotone (Finsupp.degree ∘ ord.toSyn.symm))
    (I : Ideal (MvPowerSeries σ K)) (n : ℕ) (f : MvPowerSeries σ K)
    (α : ↥({α : σ →₀ ℕ | α.degree < n} \ ord.initialDiagram I)) :
    ord.quotientSupMaximalIdealPowEquiv hdeg I n (Ideal.Quotient.mk _ f) α =
      MvPowerSeries.coeff α.val (ord.normalRemainder I f) := by
  simp [quotientSupMaximalIdealPowEquiv, ← Ideal.Quotient.mk_eq_mk]

/-- Inverse of `quotientSupMaximalIdealPowEquiv`: sums the corresponding monomials modulo
`I ⊔ 𝔪 ^ n`. -/
@[simp]
theorem quotientSupMaximalIdealPowEquiv_symm_apply
    (hdeg : Monotone (Finsupp.degree ∘ ord.toSyn.symm))
    (I : Ideal (MvPowerSeries σ K)) (n : ℕ)
    (v : ↥({α : σ →₀ ℕ | α.degree < n} \ ord.initialDiagram I) → K) :
    (ord.quotientSupMaximalIdealPowEquiv hdeg I n).symm v =
      Ideal.Quotient.mk _ (∑ᶠ β, MvPowerSeries.monomial β.val (v β)) := by
  have hfin : ({α : σ →₀ ℕ | α.degree < n} \ ord.initialDiagram I).Finite :=
    (Finsupp.finite_of_degree_lt n).sdiff
  have : Fintype ↥({α : σ →₀ ℕ | α.degree < n} \ ord.initialDiagram I) := hfin.fintype
  rw [finsum_eq_sum_of_fintype]
  apply (ord.quotientSupMaximalIdealPowEquiv hdeg I n).injective
  rw [LinearEquiv.apply_symm_apply]
  funext α
  rw [quotientSupMaximalIdealPowEquiv_mk, ← ord.normalRemainderEval_apply,
    ord.normalRemainderEval_sum_monomial]

/-- **Diagram formula for the Hilbert–Samuel function** (Bierstone–Milman, Corollary 3.20): for any
degree-compatible monomial order `ord` on finitely many variables over a field `K`, the
Hilbert–Samuel function of `I : Ideal (MvPowerSeries σ K)` at degree `ℓ` counts the exponents of
total degree at most `ℓ` outside `ord.initialDiagram I`. -/
theorem hilbertSamuel_eq_ncard_degree_le_sdiff_initialDiagram
    (hdeg : Monotone (Finsupp.degree ∘ ord.toSyn.symm))
    (I : Ideal (MvPowerSeries σ K)) (ℓ : ℕ) :
    I.hilbertSamuel ℓ =
      (({α : σ →₀ ℕ | α.degree ≤ ℓ} \ ord.initialDiagram I).ncard : ℕ∞) := by
  rw [Ideal.hilbertSamuel_def, ← MvPowerSeries.length_restrictScalars,
    (ord.quotientSupMaximalIdealPowEquiv hdeg I (ℓ + 1)).length_eq,
    Module.length_pi, Module.length_eq_one K K, mul_one, ENat.card_coe_set_eq]
  simp_rw [Nat.lt_succ_iff]
  exact (Finsupp.finite_of_degree_le ℓ).sdiff.cast_ncard_eq.symm

end HilbertSamuel

end MonomialOrder

namespace Ideal

/-- In finitely many variables over a field `K`, the Hilbert–Samuel function of the zero ideal of
`MvPowerSeries σ K` is the binomial coefficient `(Fintype.card σ + ℓ).choose (Fintype.card σ)`. -/
theorem hilbertSamuel_mvPowerSeries_bot {σ K : Type*} [Fintype σ] [Field K] (ℓ : ℕ) :
    (⊥ : Ideal (MvPowerSeries σ K)).hilbertSamuel ℓ =
      ((Fintype.card σ + ℓ).choose (Fintype.card σ) : ℕ∞) := by
  let _ : LinearOrder σ := LinearOrder.lift' (Fintype.equivFin σ) (Fintype.equivFin σ).injective
  have _ : WellFoundedGT σ := Finite.wellFounded_of_trans_of_irrefl _
  rw [MonomialOrder.degLex.hilbertSamuel_eq_ncard_degree_le_sdiff_initialDiagram
      Finsupp.DegLex.monotone_degree ⊥ ℓ,
    MonomialOrder.initialDiagram_bot, Set.sdiff_empty, Finsupp.ncard_degree_le]

end Ideal

namespace MvPowerSeries

section Stabilization

variable {σ K : Type*} [Finite σ] [Field K]

/-- **Bierstone–Milman lexicographic well-foundedness for formal power series**: in finitely many
variables over a field `K`, the set of Hilbert–Samuel functions realized by ideals of
`MvPowerSeries σ K` is well-founded in the lexicographic order on `ℕ → ℕ∞`. -/
theorem isWF_range_toLex_hilbertSamuel (σ K : Type*) [Finite σ] [Field K] :
    (Set.range fun I : Ideal (MvPowerSeries σ K) ↦ toLex I.hilbertSamuel).IsWF := by
  obtain ⟨n, ⟨e⟩⟩ := Finite.exists_equiv_fin σ
  let _ : LinearOrder σ := LinearOrder.lift' e e.injective
  have _ : WellFoundedGT σ := Finite.wellFounded_of_trans_of_irrefl _
  let castLex : Lex (ℕ → ℕ) → Lex (ℕ → ℕ∞) := fun x ↦ toLex fun ℓ ↦ (ofLex x ℓ : ℕ∞)
  have hcast : StrictMono castLex := by
    rintro x y ⟨m, hm_eq, hm_lt⟩
    exact ⟨m, fun k hk ↦ congrArg Nat.cast (hm_eq k hk), Nat.cast_lt.mpr hm_lt⟩
  refine ((Finsupp.isWF_range_toLex_ncard_degree_le_sdiff σ).isPWO.image_of_monotone
    hcast.monotone).isWF.mono ?_
  rintro _ ⟨I, rfl⟩
  refine ⟨toLex fun ℓ ↦ ({α : σ →₀ ℕ | α.degree ≤ ℓ} \
      MonomialOrder.degLex.initialDiagram I).ncard,
    ⟨⟨MonomialOrder.degLex.initialDiagram I,
      MonomialOrder.degLex.isUpperSet_initialDiagram I⟩, rfl⟩, ?_⟩
  apply ofLex.injective
  funext ℓ
  simpa [castLex] using
    (MonomialOrder.degLex.hilbertSamuel_eq_ncard_degree_le_sdiff_initialDiagram
      Finsupp.DegLex.monotone_degree I ℓ).symm

/-- **Lexicographic Hilbert–Samuel stabilization** (Bierstone–Milman, Theorem 5.2.1): for any
sequence of ideals `I : ℕ → Ideal (MvPowerSeries σ K)` in finitely many variables over a field,
if `j ↦ toLex (I j).hilbertSamuel` is antitone, then `j ↦ (I j).hilbertSamuel` is eventually
constant. -/
theorem exists_hilbertSamuel_eq_of_antitone_lex (I : ℕ → Ideal (MvPowerSeries σ K))
    (h : Antitone fun j ↦ toLex (I j).hilbertSamuel) :
    ∃ j₀, ∀ j, j₀ ≤ j → (I j).hilbertSamuel = (I j₀).hilbertSamuel := by
  have hwf : (Set.range fun j ↦ toLex (I j).hilbertSamuel).IsWF :=
    (isWF_range_toLex_hilbertSamuel σ K).mono (Set.range_subset_iff.mpr fun j ↦ ⟨I j, rfl⟩)
  obtain ⟨j₀, hj₀⟩ := hwf.min_mem (Set.range_nonempty _)
  dsimp only at hj₀
  refine ⟨j₀, fun j hj ↦ ?_⟩
  have heq : toLex (I j).hilbertSamuel = toLex (I j₀).hilbertSamuel :=
    eq_of_le_of_not_lt (h hj) (hj₀ ▸ hwf.not_lt_min (Set.range_nonempty _) ⟨j, rfl⟩)
  exact congrArg ofLex heq

/-- **Pointwise Hilbert–Samuel stabilization**: for any sequence of ideals
`I : ℕ → Ideal (MvPowerSeries σ K)` in finitely many variables over a field, if
`j ↦ (I j).hilbertSamuel` is antitone, then `j ↦ (I j).hilbertSamuel` is eventually constant. -/
theorem exists_hilbertSamuel_eq_of_antitone (I : ℕ → Ideal (MvPowerSeries σ K))
    (h : Antitone fun j ↦ (I j).hilbertSamuel) :
    ∃ j₀, ∀ j, j₀ ≤ j → (I j).hilbertSamuel = (I j₀).hilbertSamuel :=
  exists_hilbertSamuel_eq_of_antitone_lex I (Pi.toLex_monotone.comp_antitone h)

end Stabilization

end MvPowerSeries

section Examples

-- The singular quotient `K⟦x⟧ / (x²)` has `H(0) = 1` and `H(ℓ + 1) = 2` for every `ℓ`.
example {K : Type*} [Field K] (ℓ : ℕ) :
    (Ideal.span {(MvPowerSeries.X (0 : Fin 1) : MvPowerSeries (Fin 1) K) ^ 2}).hilbertSamuel
      (ℓ + 1) = 2 := by
  have hspan :
      (Ideal.span {(MvPowerSeries.X (0 : Fin 1) : MvPowerSeries (Fin 1) K) ^ 2}) =
        Ideal.span ((fun α ↦ MvPowerSeries.monomial α (1 : K)) ''
          {Finsupp.single (0 : Fin 1) 2}) := by
    rw [Set.image_singleton, MvPowerSeries.X_pow_eq]
  rw [MonomialOrder.degLex.hilbertSamuel_eq_ncard_degree_le_sdiff_initialDiagram
      Finsupp.DegLex.monotone_degree, hspan, MonomialOrder.initialDiagram_span_monomial,
    Set.biUnion_singleton]
  have hset : {α : Fin 1 →₀ ℕ | α.degree ≤ ℓ + 1} \ Set.Ici (Finsupp.single (0 : Fin 1) 2) =
      {(0 : Fin 1 →₀ ℕ), Finsupp.single (0 : Fin 1) 1} := by
    ext α
    simp [Finsupp.degree_eq_sum, Finsupp.le_def, Finsupp.ext_iff]
    omega
  rw [hset, Set.ncard_pair (by
    intro h
    have := congrArg (fun f : Fin 1 →₀ ℕ ↦ f 0) h
    simp at this)]
  norm_cast

-- Without realizability by ideals, `ℕ → ℕ∞` admits infinite strictly lex-decreasing sequences, so
-- `MvPowerSeries.isWF_range_toLex_hilbertSamuel` is genuinely non-trivial.
example : ∃ f : ℕ → ℕ → ℕ∞, StrictAnti fun j ↦ toLex (f j) := by
  refine ⟨fun j ℓ ↦ if j ≤ ℓ then 1 else 0, fun a b hab ↦ ⟨a, fun k hk ↦ ?_, ?_⟩⟩
  · have hka : ¬ a ≤ k := not_le.mpr hk
    have hkb : ¬ b ≤ k := not_le.mpr (hk.trans hab)
    simp [hka, hkb]
  · have hab' : ¬ b ≤ a := not_le.mpr hab
    simp [hab']

end Examples
