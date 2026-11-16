/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Order.PiLex
public import Mathlib.Order.WellFoundedSet
public import TauCeti.RingTheory.LocalRing.HilbertSamuel
public import TauCeti.RingTheory.MvPowerSeries.FormalDivision
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.Isomorphisms
import Mathlib.Order.OrderIsoNat
import Mathlib.RingTheory.LocalRing.Length
import TauCeti.Data.Finsupp.UpperSet
import TauCeti.RingTheory.LocalRing.ResidueField.Quotient

/-!
# Hilbert–Samuel functions of ideals in multivariate formal power series

For finitely many variables `σ` over a field `K`, the residue field of `MvPowerSeries σ K` is
canonically isomorphic to `K`, so the `MvPowerSeries σ K`-length of any module equals its
`K`-vector-space length (`MvPowerSeries.length_restrictScalars`).

Given a degree-compatible monomial order `ord : MonomialOrder σ` — one satisfying
`Monotone (Finsupp.degree ∘ ord.toSyn.symm)`, such as `MonomialOrder.degLex` — Hironaka's
normal-form remainder `ord.normalRemainder I` does not decrease total-degree order
(`MonomialOrder.order_le_order_normalRemainder`) and therefore preserves every power `𝔪 ^ n` of the
maximal ideal (`MonomialOrder.normalRemainder_mem_maximalIdeal_pow`). Evaluating the coefficients of
`ord.normalRemainder I f` on exponents of degree `< n` outside `ord.initialDiagram I` induces a
canonical `K`-linear isomorphism
`MvPowerSeries σ K ⧸ (I ⊔ 𝔪 ^ n) ≃ₗ[K] (({α | α.degree < n} \ ord.initialDiagram I) → K)`
(`MonomialOrder.quotientSupMaximalIdealPowEquiv`).

Taking lengths yields the diagram formula for the Hilbert–Samuel function
(`MonomialOrder.hilbertSamuel_eq_ncard_compl_initialDiagram`):
`I.hilbertSamuel ℓ = ({α : σ →₀ ℕ | α.degree ≤ ℓ} \ ord.initialDiagram I).ncard`.
In particular, `(⊥ : Ideal (MvPowerSeries σ K)).hilbertSamuel ℓ = (card σ + ℓ).choose (card σ)`
(`Ideal.hilbertSamuel_mvPowerSeries_bot`). Combining the diagram formula with the lexicographic
well-foundedness of complement-counting functions of upper sets in `σ →₀ ℕ`
(`Finsupp.isWF_range_toLex_ncard_degree_le_diff`) yields Bierstone–Milman's stabilization theorem:
the set of Hilbert–Samuel functions realized by ideals of `MvPowerSeries σ K` is well-founded in
`Lex (ℕ → ℕ∞)` (`MvPowerSeries.isWF_range_toLex_hilbertSamuel`), so every lexicographically — and in
particular every pointwise — antitone sequence of Hilbert–Samuel functions of ideals in
`MvPowerSeries σ K` stabilizes (`MvPowerSeries.exists_hilbertSamuel_eq_of_antitone_lex`,
`MvPowerSeries.exists_hilbertSamuel_eq_of_antitone`).

## Main definitions

* `MonomialOrder.quotientSupMaximalIdealPowEquiv`: canonical `K`-linear isomorphism identifying
  `MvPowerSeries σ K ⧸ (I ⊔ 𝔪 ^ n)` with functions on `{α | α.degree < n} \ ord.initialDiagram I`.

## Main results

* `MvPowerSeries.length_restrictScalars`: module length over `MvPowerSeries σ K` agrees with
  `K`-vector-space length.
* `MonomialOrder.order_le_order_normalRemainder`,
  `MonomialOrder.normalRemainder_mem_maximalIdeal_pow`: normal remainders for a degree-compatible
  monomial order never drop total-degree order and preserve maximal-ideal powers.
* `MonomialOrder.hilbertSamuel_eq_ncard_compl_initialDiagram`: `I.hilbertSamuel ℓ` counts
  exponents of degree at most `ℓ` outside `ord.initialDiagram I`.
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

/-- For any `MvPowerSeries σ K`-module `M` over a field `K`, its `K`-vector-space length equals
its `MvPowerSeries σ K`-module length, since the residue field of `MvPowerSeries σ K` is
`K`-isomorphic to `K`. -/
theorem length_restrictScalars {σ K M : Type*} [Field K]
    [AddCommGroup M] [Module K M] [Module (MvPowerSeries σ K) M]
    [IsScalarTower K (MvPowerSeries σ K) M] :
    Module.length K M = Module.length (MvPowerSeries σ K) M := by
  let ev : MvPowerSeries σ K →ₐ[K] K :=
    { MvPowerSeries.constantCoeff with commutes' := constantCoeff_C }
  have hev : Function.Surjective ev := fun c ↦ ⟨C c, constantCoeff_C c⟩
  have hres : Module.length (IsLocalRing.ResidueField K)
      (IsLocalRing.ResidueField (MvPowerSeries σ K)) = 1 := by
    rw [← Module.length_eq_of_surjective (S := K) (IsLocalRing.residue_surjective (R := K)),
      (TauCeti.residueFieldAlgEquivOfSurjective hev).toLinearEquiv.length_eq,
      Module.length_eq_finrank]
    simp
  rw [IsLocalRing.length_restrictScalars K (MvPowerSeries σ K) M, hres, mul_one]

end MvPowerSeries

namespace MonomialOrder

section HilbertSamuel

variable {σ K : Type*} [Finite σ] [Field K] (ord : MonomialOrder σ)

/-- For a degree-compatible monomial order `ord`, taking the normal remainder modulo `I` does not
decrease total-degree order. -/
theorem order_le_order_normalRemainder (hdeg : Monotone (Finsupp.degree ∘ ord.toSyn.symm))
    (I : Ideal (MvPowerSeries σ K)) (f : MvPowerSeries σ K) :
    f.order ≤ (ord.normalRemainder I f).order := by
  by_cases htop : f.order = ⊤
  · have hf0 : f = 0 :=
      MvPowerSeries.ext fun γ ↦ MvPowerSeries.coeff_of_lt_order (htop ▸ WithTop.coe_lt_top _)
    simp [hf0]
  · obtain ⟨n, hn⟩ := WithTop.ne_top_iff_exists.mp htop
    rw [← hn]
    have hS : IsLowerSet {s : ord.syn | (ord.toSyn.symm s).degree < n} :=
      fun _ _ hle hs ↦ lt_of_le_of_lt (hdeg hle) hs
    have hf : ∀ γ, ord.toSyn γ ∈ {s : ord.syn | (ord.toSyn.symm s).degree < n} →
        MvPowerSeries.coeff γ f = 0 := by
      intro γ hγ
      simp only [Set.mem_ofPred_eq, AddEquiv.symm_apply_apply] at hγ
      exact MvPowerSeries.coeff_of_lt_order (hn ▸ Nat.cast_lt.mpr hγ)
    have hrem := ord.coeff_normalRemainder_eq_zero_of_isLowerSet (I := I) hS hf
    refine MvPowerSeries.nat_le_order fun γ hγ ↦ hrem γ ?_
    simpa only [Set.mem_ofPred_eq, AddEquiv.symm_apply_apply] using hγ

/-- For a degree-compatible monomial order `ord`, the normal-remainder projection modulo `I`
preserves every power `𝔪 ^ n` of the maximal ideal of `MvPowerSeries σ K`. -/
theorem normalRemainder_mem_maximalIdeal_pow (hdeg : Monotone (Finsupp.degree ∘ ord.toSyn.symm))
    (I : Ideal (MvPowerSeries σ K)) {f : MvPowerSeries σ K} {n : ℕ}
    (hf : f ∈ IsLocalRing.maximalIdeal (MvPowerSeries σ K) ^ n) :
    ord.normalRemainder I f ∈ IsLocalRing.maximalIdeal (MvPowerSeries σ K) ^ n := by
  rw [MvPowerSeries.mem_maximalIdeal_pow_iff_le_order] at hf ⊢
  exact hf.trans (ord.order_le_order_normalRemainder hdeg I f)

/-- Coefficient-evaluation map sending `f` to the restriction of `ord.normalRemainder I f` to
exponents of degree `< n` outside `ord.initialDiagram I`. -/
private noncomputable def normalRemainderEval (I : Ideal (MvPowerSeries σ K)) (n : ℕ) :
    MvPowerSeries σ K →ₗ[K]
      (↥({α : σ →₀ ℕ | α.degree < n} \ ord.initialDiagram I) → K) :=
  LinearMap.pi fun α ↦ (MvPowerSeries.coeff α.1).comp (ord.normalRemainder I)

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
      · exact congrFun hf ⟨γ, hγ, hD⟩
    have hsum : (f - ord.normalRemainder I f) + ord.normalRemainder I f = f := sub_add_cancel _ _
    exact hsum ▸ Submodule.add_mem_sup (ord.sub_normalRemainder_mem I f) hrem_mem
  · obtain ⟨g, hg, h, hh, rfl⟩ := Submodule.mem_sup.mp hf
    funext ⟨α, hα_deg, _⟩
    simp only [normalRemainderEval, LinearMap.pi_apply, LinearMap.comp_apply, map_add,
      ord.normalRemainder_eq_zero_iff.mpr hg, map_zero, zero_add]
    have hh' := MvPowerSeries.mem_maximalIdeal_pow_iff_le_order.mp
      (ord.normalRemainder_mem_maximalIdeal_pow hdeg I hh)
    exact MvPowerSeries.coeff_of_lt_order ((Nat.cast_lt.mpr hα_deg).trans_le hh')

private theorem normalRemainderEval_sum_monomial (I : Ideal (MvPowerSeries σ K)) (n : ℕ)
    [Fintype ↥({α : σ →₀ ℕ | α.degree < n} \ ord.initialDiagram I)]
    (v : ↥({α : σ →₀ ℕ | α.degree < n} \ ord.initialDiagram I) → K) :
    ord.normalRemainderEval I n (∑ β, MvPowerSeries.monomial β.1 (v β)) = v := by
  classical
  have hg_comp : (∑ β, MvPowerSeries.monomial β.1 (v β)) ∈ ord.complementSubmodule I :=
    Submodule.sum_mem _ fun β _ ↦ ord.monomial_mem_complementSubmodule_iff.mpr (Or.inr β.2.2)
  funext α
  rw [normalRemainderEval, LinearMap.pi_apply, LinearMap.comp_apply,
    ord.normalRemainder_eq_self_of_mem_complementSubmodule hg_comp, map_sum,
    Finset.sum_eq_single α]
  · exact MvPowerSeries.coeff_monomial_same α.1 (v α)
  · intro β _ hβα
    exact MvPowerSeries.coeff_monomial_ne (fun h ↦ hβα (Subtype.ext h.symm)) (v β)
  · intro hα
    exact absurd (Finset.mem_univ α) hα

private theorem surjective_normalRemainderEval (I : Ideal (MvPowerSeries σ K)) (n : ℕ) :
    Function.Surjective (ord.normalRemainderEval I n) := by
  have hfin : ({α : σ →₀ ℕ | α.degree < n} \ ord.initialDiagram I).Finite :=
    ((Finsupp.finite_of_degree_le n).subset fun _ hα ↦ Nat.le_of_lt hα).sdiff
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
      MvPowerSeries.coeff α.1 (ord.normalRemainder I f) := by
  rw [quotientSupMaximalIdealPowEquiv, LinearEquiv.trans_apply, LinearEquiv.trans_apply,
    ← Ideal.Quotient.mk_eq_mk, Submodule.Quotient.restrictScalarsEquiv_symm_mk,
    Submodule.quotEquivOfEq_mk, LinearMap.quotKerEquivOfSurjective_apply_mk,
    normalRemainderEval, LinearMap.pi_apply, LinearMap.comp_apply]

/-- Inverse of `quotientSupMaximalIdealPowEquiv`: sums the corresponding monomials modulo
`I ⊔ 𝔪 ^ n`. -/
theorem quotientSupMaximalIdealPowEquiv_symm_apply
    (hdeg : Monotone (Finsupp.degree ∘ ord.toSyn.symm))
    (I : Ideal (MvPowerSeries σ K)) (n : ℕ)
    [Fintype ↥({α : σ →₀ ℕ | α.degree < n} \ ord.initialDiagram I)]
    (v : ↥({α : σ →₀ ℕ | α.degree < n} \ ord.initialDiagram I) → K) :
    (ord.quotientSupMaximalIdealPowEquiv hdeg I n).symm v =
      Ideal.Quotient.mk _ (∑ β, MvPowerSeries.monomial β.1 (v β)) := by
  apply (ord.quotientSupMaximalIdealPowEquiv hdeg I n).injective
  rw [LinearEquiv.apply_symm_apply]
  funext α
  rw [quotientSupMaximalIdealPowEquiv_mk]
  exact (congrFun (ord.normalRemainderEval_sum_monomial I n v) α).symm

/-- **Diagram formula for the Hilbert–Samuel function** (Bierstone–Milman, Corollary 3.20): for any
degree-compatible monomial order `ord` on finitely many variables over a field `K`, the
Hilbert–Samuel function of `I : Ideal (MvPowerSeries σ K)` at degree `ℓ` counts the exponents of
total degree at most `ℓ` outside `ord.initialDiagram I`. -/
theorem hilbertSamuel_eq_ncard_compl_initialDiagram
    (hdeg : Monotone (Finsupp.degree ∘ ord.toSyn.symm))
    (I : Ideal (MvPowerSeries σ K)) (ℓ : ℕ) :
    I.hilbertSamuel ℓ =
      (({α : σ →₀ ℕ | α.degree ≤ ℓ} \ ord.initialDiagram I).ncard : ℕ∞) := by
  have hfin : ({α : σ →₀ ℕ | α.degree < ℓ + 1} \ ord.initialDiagram I).Finite :=
    ((Finsupp.finite_of_degree_le ℓ).subset fun _ hα ↦ Nat.lt_succ_iff.mp hα).sdiff
  have : Fintype ↥({α : σ →₀ ℕ | α.degree < ℓ + 1} \ ord.initialDiagram I) := hfin.fintype
  rw [Ideal.hilbertSamuel_def, ← MvPowerSeries.length_restrictScalars,
    (ord.quotientSupMaximalIdealPowEquiv hdeg I (ℓ + 1)).length_eq,
    Module.length_eq_finrank, Module.finrank_fintype_fun_eq_card, ← Nat.card_eq_fintype_card,
    Nat.card_coe_set_eq]
  simp_rw [Nat.lt_succ_iff]

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
  rw [MonomialOrder.degLex.hilbertSamuel_eq_ncard_compl_initialDiagram
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
  refine Set.isWF_iff_no_descending_seq.mpr fun f hf hmem ↦ ?_
  choose I hI using hmem
  dsimp only at hI
  let D (j : ℕ) : UpperSet (σ →₀ ℕ) :=
    ⟨MonomialOrder.degLex.initialDiagram (I j),
      MonomialOrder.degLex.isUpperSet_initialDiagram (I j)⟩
  let g : ℕ → Lex (ℕ → ℕ) := fun j ↦
    toLex fun ℓ ↦ ({α : σ →₀ ℕ | α.degree ≤ ℓ} \ (D j : Set (σ →₀ ℕ))).ncard
  have hg_cast (j ℓ : ℕ) : (g j ℓ : ℕ∞) = (I j).hilbertSamuel ℓ :=
    (MonomialOrder.degLex.hilbertSamuel_eq_ncard_compl_initialDiagram
      Finsupp.DegLex.monotone_degree (I j) ℓ).symm
  have hg_anti : StrictAnti g := by
    intro a b hab
    have hlt : toLex (I b).hilbertSamuel < toLex (I a).hilbertSamuel := by
      rw [hI a, hI b]
      exact hf hab
    obtain ⟨m, hm_eq, hm_lt⟩ := hlt
    simp only [Pi.toLex_apply, ← hg_cast] at hm_eq hm_lt
    exact ⟨m, fun k hk ↦ Nat.cast_injective (hm_eq k hk), Nat.cast_lt.mp hm_lt⟩
  exact (Set.isWF_iff_no_descending_seq.mp
    (Finsupp.isWF_range_toLex_ncard_degree_le_diff σ)) g hg_anti fun j ↦ ⟨D j, rfl⟩

/-- **Lexicographic Hilbert–Samuel stabilization** (Bierstone–Milman, Theorem 5.2.1): every sequence
of ideals `I : ℕ → Ideal (MvPowerSeries σ K)` in finitely many variables over a field whose
Hilbert–Samuel functions are lexicographically antitone is eventually constant. -/
theorem exists_hilbertSamuel_eq_of_antitone_lex (I : ℕ → Ideal (MvPowerSeries σ K))
    (h : Antitone fun j ↦ toLex (I j).hilbertSamuel) :
    ∃ j₀, ∀ j, j₀ ≤ j → (I j).hilbertSamuel = (I j₀).hilbertSamuel := by
  let S := Set.range fun J : Ideal (MvPowerSeries σ K) ↦ toLex J.hilbertSamuel
  have : WellFoundedLT S := isWF_range_toLex_hilbertSamuel σ K
  let u : ℕ → S := fun j ↦ ⟨toLex (I j).hilbertSamuel, ⟨I j, rfl⟩⟩
  obtain ⟨j₀, hj₀⟩ := WellFoundedLT.antitone_chain_condition (f := u) (fun _ _ hab ↦ h hab)
  exact ⟨j₀, fun j hj ↦ congrArg (fun x : S ↦ ofLex x.1) (hj₀ j hj).symm⟩

/-- **Pointwise Hilbert–Samuel stabilization**: every sequence of ideals
`I : ℕ → Ideal (MvPowerSeries σ K)` in finitely many variables over a field whose Hilbert–Samuel
functions are pointwise antitone is eventually constant. -/
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
  rw [MonomialOrder.degLex.hilbertSamuel_eq_ncard_compl_initialDiagram
      Finsupp.DegLex.monotone_degree, hspan, MonomialOrder.initialDiagram_span_monomial,
    Set.biUnion_singleton]
  have hset : {α : Fin 1 →₀ ℕ | α.degree ≤ ℓ + 1} \ Set.Ici (Finsupp.single (0 : Fin 1) 2) =
      {(0 : Fin 1 →₀ ℕ), Finsupp.single (0 : Fin 1) 1} := by
    ext α
    simp only [Set.mem_sdiff, Set.mem_ofPred_eq, Set.mem_Ici, Set.mem_insert_iff,
      Set.mem_singleton_iff, Finsupp.degree_eq_sum, Fin.sum_univ_one, Finsupp.le_def,
      Fin.forall_fin_one, Finsupp.single_eq_same, Finsupp.ext_iff, Finsupp.coe_zero, Pi.zero_apply]
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
