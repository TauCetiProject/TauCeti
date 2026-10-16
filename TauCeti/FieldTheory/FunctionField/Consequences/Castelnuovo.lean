/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.FieldTheory.FunctionField.Consequences.Nonspecial
public import TauCeti.FieldTheory.FunctionField.Consequences.RiemannInequality
public import TauCeti.FieldTheory.FunctionField.Place.Extension.IntegralBasis.AlmostEverywhere
public import TauCeti.FieldTheory.FunctionField.Place.Extension.Kummer
public import TauCeti.FieldTheory.FunctionField.Place.Extension.Splitting.Basic
public import TauCeti.FieldTheory.IntermediateField.Adjoin.PrimitiveElement
import Mathlib.FieldTheory.Normal.Basic
import TauCeti.FieldTheory.FunctionField.ConstantExtension.Degree
import TauCeti.FieldTheory.FunctionField.ConstantExtension.Genus
import TauCeti.FieldTheory.FunctionField.ConstantExtension.ResidueField
import TauCeti.FieldTheory.IntermediateField.Adjoin.EqTop

/-!
# Castelnuovo's inequality

Let `F / k` be an algebraic function field with exact constant field `k`, and let `F₁`, `F₂` be
subfields of `F` containing `k`, of genera `g₁`, `g₂`, over which `F` is finite of degrees
`n₁ = [F : F₁]` and `n₂ = [F : F₂]`. **Castelnuovo's inequality** bounds the genus of `F`:

`g ≤ n₁ g₁ + n₂ g₂ + (n₁ - 1) (n₂ - 1)`.

This file proves it first whenever `F₁` has a place `P₁` that splits completely in `F` into places
whose restrictions to `F₂` are pairwise distinct and rational, and `F₂` has at least `g₂` further
rational places. Over a perfect constant field, with `F / F₁` separable and `F = F₁ F₂`, the
inequality then holds unconditionally. Write a primitive element `y` of `F / F₁` as `∑ cᵢ zᵢ` with
`cᵢ ∈ F₁` and `zᵢ ∈ F₂`, and take a place `P₁` of `F₁` at which the minimal polynomial of `y` has
separable reduction, the `cᵢ` are regular, and the `zᵢ` are regular at every place above. Pass to
a finite constant field extension `F · k'`, over which `F · k'`, `F₁ · k'` and `F₂ · k'` have the
genera of `F`, `F₁` and `F₂`, and `[F · k' : Fᵢ · k'] = [F : Fᵢ]`. There every place above `P₁` is
rational and `F₂ · k'` has enough rational places. Kummer's theorem then gives `n₁` places over
`P₁` at which `y` takes distinct constant values. The presentation of `y` computes each of these
values from the restrictions of the place to `F₁` and to `F₂`, so the places have distinct
restrictions to `F₂`. This finite extension replaces Stichtenoth's passage to an algebraic closure
of `k`.

The proof chooses an `F₁`-basis of `F` made of functions of `F₂` with few poles, and feeds it to
the bound `g ≤ 1 + n₁ (g₁ - 1) + deg C` for a basis of `F / F₁` inside `L(C)`
(`TauCeti.genus_le_one_add_finrank_mul_genus_sub_one_add_degree`). Let `P⁽⁰⁾, …, P⁽ⁿ¹⁻¹⁾` be the
places of `F` over `P₁` and `Q⁽ⁱ⁾` their restrictions to `F₂`. Take a nonspecial effective
divisor `B` of `F₂` of degree `g₂` away from the `Q⁽ⁱ⁾` (Stichtenoth, Proposition 1.6.12). For
`i ≠ 0`, Riemann's theorem gives `ℓ(B + Q⁽ⁱ⁾) ≥ 2 > ℓ(B)`, so some `wᵢ ∈ L(B + Q⁽ⁱ⁾)` has a pole
at `Q⁽ⁱ⁾` and none at the other `Q⁽ʲ⁾`; put `w₀ = 1`. In a relation `∑ aᵢ wᵢ = 0` with
`aᵢ ∈ F₁`, the coefficients have the same order at every `P⁽ʲ⁾`, namely `e (P⁽ʲ⁾ ∣ P₁)` times
their order at `P₁`; looking at the place `P⁽ⁱ⁾` of a coefficient of least order shows that the
`i`-th term has strictly least order there, which is impossible. So the `wᵢ` are a basis of
`F / F₁` inside `L(A)`, `A = B + ∑_{i ≠ 0} Q⁽ⁱ⁾`, of degree `g₂ + n₁ - 1`, and the conorm of `A`
to `F` has degree `n₂ (g₂ + n₁ - 1)`.

The split-place form of the inequality does not assume `F = F₁ F₂`: the basis above consists of
elements of `F₂`. The hypothesis enters the general theorem only through the presentation of `y`.

## Main results

* `TauCeti.genus_le_finrank_mul_genus_add_finrank_mul_genus_add_of_isSplitCompletely`:
  **Castelnuovo's inequality** `g ≤ n₁ g₁ + n₂ g₂ + (n₁ - 1) (n₂ - 1)`, from a place of `F₁`
  splitting completely in `F` with distinct rational restrictions to `F₂`.
* `TauCeti.genus_le_finrank_mul_genus_add_finrank_mul_genus_add`: **Castelnuovo's inequality**
  over a perfect field, for `F = F₁ F₂` with `F / F₁` separable.

## References

* H. Stichtenoth, *Algebraic Function Fields and Codes*, 2nd ed., GTM 254, Springer, 2009,
  Proposition 3.11.1 and Theorem 3.11.3.
-/

public section

open scoped IntermediateField Polynomial

namespace TauCeti

open AlgebraicGeometry

variable {k F₁ F₂ F : Type*} [Field k] [Field F₁] [Field F₂] [Field F]
variable [Algebra k F₁] [Algebra k F₂] [Algebra k F] [Algebra F₁ F] [Algebra F₂ F]
variable [IsScalarTower k F₁ F] [IsScalarTower k F₂ F]
variable [FiniteDimensional F₁ F] [FiniteDimensional F₂ F]

/-- **Castelnuovo's inequality** (Stichtenoth, Theorem 3.11.3), from a split place. Let `F / k`
have exact constants and let `F₁`, `F₂` be subfields of `F` containing `k` over which `F` is
finite. Suppose a place `P₁` of `F₁` splits completely in `F`, the places of `F` over it restrict
to pairwise distinct rational places of `F₂`, and `F₂` has a set `T` of at least `g(F₂)` rational
places containing none of these restrictions. Then

`g(F) ≤ [F : F₁] g(F₁) + [F : F₂] g(F₂) + ([F : F₁] - 1) ([F : F₂] - 1)`.

Neither `k` nor the subfields need be perfect or separable over anything; only the constants of
`F` have to be exact. -/
theorem genus_le_finrank_mul_genus_add_finrank_mul_genus_add_of_isSplitCompletely
    (hF : IsFunctionField k F) (hex : IsIntegrallyClosedIn k F) {P₁ : Place k F₁}
    (hsplit : P₁.IsSplitCompletely (k' := k) (F' := F))
    (hinj : Set.InjOn (fun P : Place k F ↦ P.restrict k F₂) {P | P.restrict k F₁ = P₁})
    (hdeg : ∀ P : Place k F, P.restrict k F₁ = P₁ → (P.restrict k F₂).degree = 1)
    {T : Set (Place k F₂)} (hT : ∀ Q ∈ T, Q.degree = 1) (hcard : (genus k F₂ : ℕ∞) ≤ T.encard)
    (hdisj : ∀ P : Place k F, P.restrict k F₁ = P₁ → P.restrict k F₂ ∉ T) :
    genus k F ≤ Module.finrank F₁ F * genus k F₁ + Module.finrank F₂ F * genus k F₂ +
      (Module.finrank F₁ F - 1) * (Module.finrank F₂ F - 1) := by
  classical
  have : Algebra.IsAlgebraic F₂ F := Algebra.IsAlgebraic.of_finite F₂ F
  have hF₂ : IsFunctionField k F₂ := hF.of_isAlgebraic_top
  have hex₂ : IsIntegrallyClosedIn k F₂ :=
    (IsScalarTower.toAlgHom k F₂ F).isIntegrallyClosedIn (algebraMap F₂ F).injective hex
  -- A nonspecial effective divisor `B` of degree `g(F₂)` supported on `T`.
  obtain ⟨B, hB0, hBT, hBdeg, hBdim, -⟩ :=
    Divisor.exists_degree_eq_genus_dim_eq_one hF₂ hex₂ hT hcard
  have hBQ : ∀ Q, Q ∉ T → B.coeff Q = 0 := fun Q hQ ↦ by
    by_contra h
    exact hQ (hBT (WeilDivisor.mem_support_iff.mpr h))
  -- The places of `F` over `P₁`, one of which is singled out.
  set S := (Place.finite_setOf_restrict_eq (k' := k) (F' := F) k F₁ P₁).toFinset with hSdef
  have hS : ∀ P, P ∈ S ↔ P.restrict k F₁ = P₁ := fun P ↦ Set.Finite.mem_toFinset _
  have hScard : S.card = Module.finrank F₁ F := by
    rw [hSdef, ← Set.ncard_eq_toFinset_card _ _]
    exact (Place.isSplitCompletely_def P₁).mp hsplit
  obtain ⟨P₀, hP₀⟩ : S.Nonempty := Finset.card_pos.mp (hScard ▸ Module.finrank_pos)
  -- At every rational place `Q` of `F₂`, a function `w Q ∈ L(B + Q)` with a pole at `Q`.
  choose! w hwL hwpole using fun (Q : Place k F₂) (hQ : Q.degree = 1) ↦
    Divisor.exists_mem_riemannRochSpace_add_ofPoint_ord_neg hF₂ hB0 hBdeg hBdim hQ
  -- The basis: `1` at `P₀`, and `w` of the restriction at the other places over `P₁`.
  let u : S → F₂ := fun P ↦ if (P : Place k F) = P₀ then 1 else w ((P : Place k F).restrict k F₂)
  have hli : LinearIndependent F₁ fun P : S ↦ algebraMap F₂ F (u P) := by
    refine Place.linearIndependent_of_ord_neg_of_restrict_eq (P := Subtype.val)
      (fun P ↦ (hS P).mp P.2) (i₀ := ⟨P₀, hP₀⟩) (by simp [u]) (by simp [u]) ?_ ?_
    · intro P hP
      have hP' : (P : Place k F) ≠ P₀ := fun h ↦ hP (Subtype.ext h)
      simp only [u, hP', ↓reduceIte]
      rw [Place.ord_algebraMap_restrict k F₂]
      have hpole := hwpole _ (hdeg P ((hS P).mp P.2))
      have he : (0 : ℤ) < Place.ramificationIdx F₂ (P : Place k F) := by
        exact_mod_cast Place.ramificationIdx_pos F₂ _
      exact mul_neg_of_pos_of_neg he hpole
    · intro P P' hPP'
      by_cases h' : (P' : Place k F) = P₀
      · simp [u, h']
      simp only [u, h', ↓reduceIte]
      rw [Place.ord_algebraMap_restrict k F₂]
      have hQQ' : (P : Place k F).restrict k F₂ ≠ (P' : Place k F).restrict k F₂ := fun h ↦
        hPP' (Subtype.ext (hinj ((hS _).mp P.2) ((hS _).mp P'.2) h))
      have hord :
          0 ≤ ((P : Place k F).restrict k F₂).ord (w ((P' : Place k F).restrict k F₂)) := by
        rcases eq_or_ne (w ((P' : Place k F).restrict k F₂)) 0 with h0 | h0
        · rw [h0, Place.ord_zero]
        have := (mem_riemannRochSpace_iff_neg_le_ord h0).mp
          (hwL _ (hdeg P' ((hS P').mp P'.2))) ((P : Place k F).restrict k F₂)
        rw [WeilDivisor.coeff_add, WeilDivisor.coeff_ofPoint_of_ne hQQ',
          hBQ _ (hdisj P ((hS P).mp P.2))] at this
        omega
      positivity
  -- All of it lies in `L(A)` for `A = B + ∑_{P ≠ P₀} P|_{F₂}`, of degree `g(F₂) + [F : F₁] - 1`.
  set A : Divisor k F₂ := B + ∑ P ∈ S.erase P₀, WeilDivisor.ofPoint (P.restrict k F₂) with hAdef
  have hu : ∀ P, u P ∈ riemannRochSpace A := by
    intro P
    by_cases hP : (P : Place k F) = P₀
    · simp only [u, hP, ↓reduceIte]
      exact one_mem_riemannRochSpace_iff.mpr
        (add_nonneg hB0 (Finset.sum_nonneg fun Q _ ↦ WeilDivisor.zero_le_ofPoint _))
    · simp only [u, hP, ↓reduceIte]
      refine riemannRochSpace_mono (add_le_add le_rfl ?_) (hwL _ (hdeg P ((hS P).mp P.2)))
      exact Finset.single_le_sum (f := fun P : Place k F ↦ WeilDivisor.ofPoint (P.restrict k F₂))
        (fun _ _ ↦ WeilDivisor.zero_le_ofPoint _) (Finset.mem_erase.mpr ⟨hP, P.2⟩)
  have hdegA : Divisor.degree A = genus k F₂ + (Module.finrank F₁ F - 1 : ℕ) := by
    rw [hAdef, Divisor.degree_add, hBdeg, map_sum, Finset.sum_congr rfl fun P hP ↦ by
      rw [Divisor.degree_ofPoint, hdeg P ((hS P).mp (Finset.mem_of_mem_erase hP))],
      Finset.sum_const, Finset.card_erase_of_mem hP₀, hScard]
    simp
  -- Apply the bound for a basis of `F / F₁` inside `L(Con A)`.
  have : Nonempty S := ⟨⟨P₀, hP₀⟩⟩
  let b := basisOfLinearIndependentOfCardEqFinrank hli (by rw [Fintype.card_coe, hScard])
  have hb : ∀ i, b i ∈ riemannRochSpace (Divisor.conorm k F A) := fun i ↦ by
    simp only [b, coe_basisOfLinearIndependentOfCardEqFinrank]
    exact (mem_riemannRochSpace_conorm_iff hF A _).mpr (hu i)
  have h := genus_le_one_add_finrank_mul_genus_sub_one_add_degree hF hex b hb
  rw [Divisor.degree_conorm_of_finrank_eq_one (k' := k) (F' := F) hF₂ (Module.finrank_self k) A,
    hdegA] at h
  have hn₁ : 1 ≤ Module.finrank F₁ F := Module.finrank_pos
  have hn₂ : 1 ≤ Module.finrank F₂ F := Module.finrank_pos
  zify [hn₁, hn₂]
  push_cast [hn₁] at h
  linarith

/-- At a rational place `P₁` of `F₁`, let `y = ∑ cᵢ zᵢ` with `cᵢ ∈ F₁` regular at `P₁` and `zᵢ ∈ F₂`
regular at the places of `F` above `P₁`. Then the constant to which `y` is congruent at a place
over `P₁` is determined by the restriction of that place to `F₂`, when this restriction is
rational: it is `∑ cᵢ(P₁) zᵢ(Q)`. -/
private theorem eq_of_valuation_sub_lt_one_of_restrict_eq {P₁ : Place k F₁} (hP₁ : P₁.degree = 1)
    {y : F} {ι : Type*} [Fintype ι] (c : ι → F₁) (z : ι → F₂)
    (hyz : y = ∑ i, algebraMap F₁ F (c i) * algebraMap F₂ F (z i)) (hc : ∀ i, c i ∈ P₁.integers)
    (hz : ∀ i, ∀ P : Place k F, P.restrict k F₁ = P₁ → algebraMap F₂ F (z i) ∈ P.integers)
    {P P' : Place k F} (hP : P.restrict k F₁ = P₁) (hP' : P'.restrict k F₁ = P₁)
    (hPP' : P.restrict k F₂ = P'.restrict k F₂) (hQ : (P.restrict k F₂).degree = 1) {a b : k}
    (ha : P.valuation (y - algebraMap k F a) < 1) (hb : P'.valuation (y - algebraMap k F b) < 1) :
    a = b := by
  -- The residues `cᵢ(P₁)` and `zᵢ(Q)` of the coefficients, all in `k`.
  choose e he using fun i ↦
    (Place.degree_eq_one_iff_forall_exists_valuation_sub_lt_one P₁).mp hP₁ (c i) (hc i)
  choose d hd using fun i ↦
    (Place.degree_eq_one_iff_forall_exists_valuation_sub_lt_one _).mp hQ (z i)
      ((Place.mem_integers_restrict_iff k F₂ P (z i)).mpr (hz i P hP))
  -- At every place `R` over `P₁` restricting to `Q`, `y` is congruent to `∑ cᵢ(P₁) zᵢ(Q)`.
  have hval (R : Place k F) (hR : R.restrict k F₁ = P₁) (hRQ : R.restrict k F₂ = P.restrict k F₂) :
      R.valuation (y - algebraMap k F (∑ i, e i * d i)) < 1 := by
    rw [hyz, map_sum, ← Finset.sum_sub_distrib]
    refine Valuation.map_sum_lt _ one_ne_zero fun i _ ↦ ?_
    have hc' : R.valuation (algebraMap F₁ F (c i) - algebraMap k F (e i)) < 1 := by
      rw [IsScalarTower.algebraMap_apply k F₁ F, ← map_sub,
        Valuation.HasExtension.val_map_lt_one_iff (R.restrict k F₁).valuation, hR]
      exact he i
    have hz' : R.valuation (algebraMap F₂ F (z i) - algebraMap k F (d i)) < 1 := by
      rw [IsScalarTower.algebraMap_apply k F₂ F, ← map_sub,
        Valuation.HasExtension.val_map_lt_one_iff (R.restrict k F₂).valuation, hRQ]
      exact hd i
    have hsum : algebraMap F₁ F (c i) * algebraMap F₂ F (z i) - algebraMap k F (e i * d i) =
        (algebraMap F₁ F (c i) - algebraMap k F (e i)) * algebraMap F₂ F (z i) +
          algebraMap k F (e i) * (algebraMap F₂ F (z i) - algebraMap k F (d i)) := by
      rw [map_mul]
      ring
    rw [hsum]
    refine Valuation.map_add_lt _ ?_ ?_
    · rw [map_mul]
      exact (mul_le_of_le_one_right' (R.mem_integers_iff.mp (hz i R hR))).trans_lt hc'
    · rw [map_mul]
      exact (mul_le_of_le_one_left' (R.mem_integers_iff.mp (R.algebraMap_mem_integers _))).trans_lt
        hz'
  exact (P.eq_of_valuation_sub_lt_one ha (hval P hP rfl)).trans
    (P'.eq_of_valuation_sub_lt_one hb (hval P' hP' hPP'.symm)).symm

/-- Castelnuovo's inequality from a place `P₁` of `F₁` all of whose extensions to `F` are rational,
at which a primitive element `y` of `F / F₁` has separable reduction, given a presentation
`y = ∑ cᵢ zᵢ` with `cᵢ ∈ F₁` regular at `P₁` and `zᵢ ∈ F₂` regular above `P₁`, and enough rational
places of `F₂`. -/
private theorem genus_le_of_forall_degree_eq_one (hF : IsFunctionField k F)
    (hex : IsIntegrallyClosedIn k F) {P₁ : Place k F₁}
    (hdeg : ∀ P : Place k F, P.restrict k F₁ = P₁ → P.degree = 1) {y : F} (hy : F₁⟮y⟯ = ⊤)
    {φ : P₁.integers[X]} (hmin : φ.map (algebraMap P₁.integers F₁) = minpoly F₁ y)
    (hsep : (φ.map (IsLocalRing.residue P₁.integers)).Separable) {ι : Type*} [Fintype ι]
    (c : ι → F₁) (z : ι → F₂) (hyz : y = ∑ i, algebraMap F₁ F (c i) * algebraMap F₂ F (z i))
    (hc : ∀ i, c i ∈ P₁.integers)
    (hz : ∀ i, ∀ P : Place k F, P.restrict k F₁ = P₁ → algebraMap F₂ F (z i) ∈ P.integers)
    (hrat : ((genus k F₂ + Module.finrank F₁ F : ℕ) : ℕ∞) ≤
      {Q : Place k F₂ | Q.degree = 1}.encard) :
    genus k F ≤ Module.finrank F₁ F * genus k F₁ + Module.finrank F₂ F * genus k F₂ +
      (Module.finrank F₁ F - 1) * (Module.finrank F₂ F - 1) := by
  /- Kummer's theorem turns the separable reduction into `[F : F₁]` places `R a` over `P₁`, one for
  each root `a ∈ k` of the reduction, with `y ≡ a` at `R a`. Read through the restrictions of `R a`
  to `F₁` and `F₂`, the presentation of `y` computes `a`, so distinct roots give places with
  distinct restrictions to `F₂`, and the split-place form of the inequality applies. -/
  classical
  have : Algebra.IsAlgebraic F₁ F := Algebra.IsAlgebraic.of_finite F₁ F
  have : Algebra.IsAlgebraic F₂ F := Algebra.IsAlgebraic.of_finite F₂ F
  have hF₁ : IsFunctionField k F₁ := hF.of_isAlgebraic_top
  have hF₂ : IsFunctionField k F₂ := hF.of_isAlgebraic_top
  -- `P₁` is rational, and every place over it has relative degree one.
  have hrel (P : Place k F) (hP : P.restrict k F₁ = P₁) :
      P₁.degree = 1 ∧ Place.relativeDegree k F₁ P = 1 := by
    have h := Place.degree_eq_degree_restrict_mul_relativeDegree k F₁ P
    rw [hdeg P hP, hP] at h
    exact ⟨Nat.eq_one_of_mul_eq_one_right h.symm, Nat.eq_one_of_mul_eq_one_left h.symm⟩
  obtain ⟨P₀, hP₀⟩ :=
    Place.restrict_surjective_of_finiteDimensional (k' := k) (F' := F) hF₁ hF P₁
  have hP₁ : P₁.degree = 1 := (hrel P₀ hP₀).1
  -- Kummer's theorem: the reduction splits, and each of its roots gives a place over `P₁`.
  have hsplit := Place.splits_map_residue_of_forall_relativeDegree_eq_one (k' := k) hF₁ P₁ y hmin
    fun P hP ↦ (hrel P hP).2
  obtain ⟨s, hs, hsP⟩ := Place.exists_finset_card_eq_forall_exists_restrict_eq_valuation_sub_lt_one
    (k' := k) hF₁ P₁ hP₁ y hmin hsep hsplit
  have hsdeg : s.card = Module.finrank F₁ F := by
    rw [hs, ← _root_.Polynomial.natDegree_map_eq_of_injective
      (IsFractionRing.injective P₁.integers F₁), hmin,
      ← IntermediateField.adjoin.finrank (IsIntegral.of_finite F₁ y), hy,
      IntermediateField.finrank_top']
  have : Nonempty (Place k F) := (Place.infinite hF).nonempty
  choose! R hR hRv using hsP
  -- The places over `P₁` restrict to rational places of `F₂`.
  have hdeg₂ (P : Place k F) (hP : P.restrict k F₁ = P₁) : (P.restrict k F₂).degree = 1 :=
    le_antisymm ((Place.degree_restrict_le k F₂ P).trans (hdeg P hP).le)
      ((P.restrict k F₂).one_le_degree_of_isFunctionField hF₂)
  -- The constant `a` is determined by the restriction of `R a` to `F₂`, so the places `R a` have
  -- pairwise distinct restrictions to `F₂`.
  have hdist : ∀ a ∈ s, ∀ a' ∈ s, (R a).restrict k F₂ = (R a').restrict k F₂ → a = a' :=
    fun a ha a' ha' h ↦ eq_of_valuation_sub_lt_one_of_restrict_eq hP₁ c z hyz hc hz (hR a ha)
      (hR a' ha') h (hdeg₂ _ (hR a ha)) (hRv a ha) (hRv a' ha')
  -- So the places over `P₁` are exactly the `R a`, and `P₁` splits completely.
  set S := {P : Place k F | P.restrict k F₁ = P₁}
  have hSfin : S.Finite := Place.finite_setOf_restrict_eq (k' := k) (F' := F) k F₁ P₁
  have hRinj : Set.InjOn R s := fun a ha a' ha' h ↦ hdist a ha a' ha' (by rw [h])
  have himg : R '' s = S := by
    refine Set.eq_of_subset_of_ncard_le (by rintro _ ⟨a, ha, rfl⟩; exact hR a ha) ?_ hSfin
    rw [hRinj.ncard_image, Set.ncard_coe_finset, hsdeg]
    exact Place.ncard_setOf_restrict_eq_le_finrank (k' := k) (F' := F) k F₁ P₁
  have hScard : S.ncard = Module.finrank F₁ F := by
    rw [← himg, hRinj.ncard_image, Set.ncard_coe_finset, hsdeg]
  have hsplitc : P₁.IsSplitCompletely (k' := k) (F' := F) :=
    (Place.isSplitCompletely_def P₁).mpr hScard
  have hinj : Set.InjOn (fun P : Place k F ↦ P.restrict k F₂) S := by
    rw [← himg]
    rintro _ ⟨a, ha, rfl⟩ _ ⟨a', ha', rfl⟩ h
    rw [hdist a ha a' ha' h]
  -- Removing the restrictions of `S` leaves at least `g(F₂)` rational places of `F₂`.
  set T := {Q : Place k F₂ | Q.degree = 1} \ (fun P : Place k F ↦ P.restrict k F₂) '' S
  refine genus_le_finrank_mul_genus_add_finrank_mul_genus_add_of_isSplitCompletely hF hex hsplitc
    hinj hdeg₂ (T := T) (fun Q hQ ↦ hQ.1) ?_ (fun P hP h ↦ h.2 ⟨P, hP, rfl⟩)
  have hle := Set.encard_le_encard_sdiff_add_encard {Q : Place k F₂ | Q.degree = 1}
    ((fun P : Place k F ↦ P.restrict k F₂) '' S)
  have himg_le : ((fun P : Place k F ↦ P.restrict k F₂) '' S).encard ≤ Module.finrank F₁ F :=
    (Set.encard_image_le _ _).trans (by rw [← hSfin.cast_ncard_eq, hScard])
  have := hrat.trans (hle.trans (add_le_add_right himg_le _))
  push_cast at this
  exact (ENat.add_le_add_iff_right (ENat.natCast_ne_top _)).mp this

omit [Algebra k F₂] [IsScalarTower k F₂ F] [FiniteDimensional F₂ F] in
/-- For `y ∈ F`, with `F / F₁` separable, and finitely many `cᵢ ∈ F₁` and `zᵢ ∈ F₂`, all but
finitely many places `P₁` of `F₁` have the following properties: the minimal polynomial of `y` has
separable reduction at `P₁`, the `cᵢ` are regular at `P₁`, and the `zᵢ` are regular at every place
of `F` above `P₁`. -/
private theorem exists_place_separable_reduction (hF : IsFunctionField k F)
    [Algebra.IsSeparable F₁ F] (y : F) {ι : Type*} [Finite ι] (c : ι → F₁) (z : ι → F₂) :
    ∃ (P₁ : Place k F₁) (φ : P₁.integers[X]), φ.map (algebraMap P₁.integers F₁) = minpoly F₁ y ∧
      (φ.map (IsLocalRing.residue P₁.integers)).Separable ∧ (∀ i, c i ∈ P₁.integers) ∧
        ∀ i, ∀ R : Place k F, R.restrict k F₁ = P₁ → algebraMap F₂ F (z i) ∈ R.integers := by
  have : Algebra.IsAlgebraic F₁ F := Algebra.IsAlgebraic.of_finite F₁ F
  have hF₁ : IsFunctionField k F₁ := hF.of_isAlgebraic_top
  have hbad : ({P : Place k F₁ | ¬ ∃ φ : P.integers[X],
      φ.map (algebraMap P.integers F₁) = minpoly F₁ y ∧
        (φ.map (IsLocalRing.residue P.integers)).Separable} ∪
      (⋃ i, {P : Place k F₁ | P.ord (c i) < 0}) ∪
      ⋃ i, (fun R : Place k F ↦ R.restrict k F₁) ''
        {R : Place k F | R.ord (algebraMap F₂ F (z i)) < 0}).Finite :=
    ((Place.finite_setOf_not_exists_map_eq_and_separable hF₁ (minpoly F₁ y)
      (Algebra.IsSeparable.isSeparable F₁ y)).union
      (Set.finite_iUnion fun i ↦ Place.finite_setOf_ord_neg hF₁ (c i))).union
      (Set.finite_iUnion fun i ↦ (Place.finite_setOf_ord_neg hF _).image _)
  have := Place.infinite hF₁
  obtain ⟨P₁, hP₁⟩ := hbad.infinite_compl.nonempty
  rw [Set.mem_compl_iff, Set.mem_union, Set.mem_union, not_or, not_or] at hP₁
  obtain ⟨⟨hgood, hc⟩, hz⟩ := hP₁
  obtain ⟨φ, hmin, hsep⟩ := not_not.mp hgood
  exact ⟨P₁, φ, hmin, hsep,
    fun i ↦ P₁.mem_integers_iff_ord_nonneg.mpr (not_lt.mp fun h ↦ hc (Set.mem_iUnion.mpr ⟨i, h⟩)),
    fun i R hR ↦ R.mem_integers_iff_ord_nonneg.mpr
      (not_lt.mp fun h ↦ hz (Set.mem_iUnion.mpr ⟨i, R, h, hR⟩))⟩

omit [Algebra k F₂] [Algebra F₂ F] [IsScalarTower k F₂ F] [FiniteDimensional F₂ F] in
/-- A subfield `F₁` of `F` after a finite separable constant field extension `F' = F · k'`: the
compositum `F₁ · k'` inside `F'` is the constant field extension of `F₁` by `k'`, so it is a
function field over `k'` of the genus of `F₁`, finite over `F₁`, and `F'` is finite over it of
degree `[F : F₁]`. -/
private theorem constantCompositum_subfield {k' F' : Type*} [Field k'] [Field F'] [Algebra k k']
    [Algebra k F'] [Algebra k' F'] [Algebra F F'] [IsScalarTower k k' F'] [IsScalarTower k F F']
    [FiniteDimensional k k'] [Algebra.IsSeparable k k'] [Algebra F₁ F'] [IsScalarTower F₁ F F']
    [IsScalarTower k F₁ F'] [Algebra k' (constantCompositum F₁ k' F')]
    [IsScalarTower k' (constantCompositum F₁ k' F') F']
    [IsScalarTower k k' (constantCompositum F₁ k' F')] (hF : IsFunctionField k F)
    (hex : IsIntegrallyClosedIn k F) (h : constantCompositum F k' F' = ⊤) :
    constantCompositum F₁ k' (constantCompositum F₁ k' F') = ⊤ ∧
      IsFunctionField k' (constantCompositum F₁ k' F') ∧
      FiniteDimensional F₁ (constantCompositum F₁ k' F') ∧
      FiniteDimensional (constantCompositum F₁ k' F') F' ∧
      Module.finrank (constantCompositum F₁ k' F') F' = Module.finrank F₁ F ∧
      genus k' (constantCompositum F₁ k' F') = genus k F₁ := by
  have : Algebra.IsAlgebraic F₁ F := Algebra.IsAlgebraic.of_finite F₁ F
  have hF₁ : IsFunctionField k F₁ := hF.of_isAlgebraic_top
  have hex₁ : IsIntegrallyClosedIn k F₁ :=
    (IsScalarTower.toAlgHom k F₁ F).isIntegrallyClosedIn (algebraMap F₁ F).injective hex
  have hcc : constantCompositum F₁ k' (constantCompositum F₁ k' F') = ⊤ :=
    (constantCompositum_eq_top_iff F₁ k' F' _).mpr rfl
  have : FiniteDimensional F₁ (constantCompositum F₁ k' F') :=
    finiteDimensional_of_constantCompositum_eq_top (k := k) hcc
  have hn := finrank_over_constantCompositum_eq_finrank_of_constantCompositum_eq_top (E := F₁) hex h
  exact ⟨hcc, hF₁.of_constantCompositum_eq_top hcc, inferInstance,
    Module.finite_of_finrank_pos (hn ▸ Module.finrank_pos), hn,
    genus_eq_genus_of_constantCompositum_eq_top hF₁ hex₁ hcc⟩

/-- Castelnuovo's inequality after a constant field extension. Let `F' = F · k'` for a finite normal
extension `k' / k`, let `P₁` be a place of `F₁` at which a primitive element `y = ∑ cᵢ zᵢ` of
`F / F₁` has separable reduction, with `cᵢ ∈ F₁` regular at `P₁` and `zᵢ ∈ F₂` regular above `P₁`.
If the residue fields of the places of `F` over `P₁`, and those of `g(F₂) + [F : F₁]` places of
`F₂`, embed into `k'`, then the inequality holds for `F`. -/
private theorem genus_le_of_constantCompositum_eq_top [PerfectField k] {k' F' : Type*} [Field k']
    [Field F'] [Algebra k k'] [Algebra k F'] [Algebra k' F'] [Algebra F F'] [IsScalarTower k k' F']
    [IsScalarTower k F F'] [FiniteDimensional k k'] [Normal k k'] (hF : IsFunctionField k F)
    (hex : IsIntegrallyClosedIn k F) (h : constantCompositum F k' F' = ⊤) {y : F}
    (hy : F₁⟮y⟯ = ⊤) {P₁ : Place k F₁} {φ : P₁.integers[X]}
    (hmin : φ.map (algebraMap P₁.integers F₁) = minpoly F₁ y)
    (hsep : (φ.map (IsLocalRing.residue P₁.integers)).Separable) {ι : Type*} [Fintype ι]
    (c : ι → F₁) (z : ι → F₂) (hyz : y = ∑ i, algebraMap F₁ F (c i) * algebraMap F₂ F (z i))
    (hc : ∀ i, c i ∈ P₁.integers)
    (hz : ∀ i, ∀ R : Place k F, R.restrict k F₁ = P₁ → algebraMap F₂ F (z i) ∈ R.integers)
    (hembR : ∀ R : Place k F, R.restrict k F₁ = P₁ → Nonempty (R.ResidueField →ₐ[k] k'))
    {TQ : Finset (Place k F₂)} (hTQ : TQ.card = genus k F₂ + Module.finrank F₁ F)
    (hembQ : ∀ Q ∈ TQ, Nonempty (Q.ResidueField →ₐ[k] k')) :
    genus k F ≤ Module.finrank F₁ F * genus k F₁ + Module.finrank F₂ F * genus k F₂ +
      (Module.finrank F₁ F - 1) * (Module.finrank F₂ F - 1) := by
  /- Over `k'`, the composita `F₁ · k'` and `F₂ · k'` have the genera of `F₁` and `F₂`, and `F'` is
  finite over them of the same degrees. The places of `F'` over a place `P₁'` of `F₁ · k'` above
  `P₁` are rational, `y` keeps its minimal polynomial and its presentation, and some places of
  `F₂ · k'` over the chosen places of `F₂` are rational. So the inequality over `k'` from
  `genus_le_of_forall_degree_eq_one` is the inequality for `F`. -/
  have : Algebra.IsAlgebraic F₁ F := Algebra.IsAlgebraic.of_finite F₁ F
  have : Algebra.IsAlgebraic F₂ F := Algebra.IsAlgebraic.of_finite F₂ F
  have hF₁ : IsFunctionField k F₁ := hF.of_isAlgebraic_top
  have hF₂ : IsFunctionField k F₂ := hF.of_isAlgebraic_top
  have hex₂ : IsIntegrallyClosedIn k F₂ :=
    (IsScalarTower.toAlgHom k F₂ F).isIntegrallyClosedIn (algebraMap F₂ F).injective hex
  have : Algebra.IsSeparable k k' := Algebra.IsAlgebraic.isSeparable_of_perfectField
  have : FiniteDimensional F F' := finiteDimensional_of_constantCompositum_eq_top (k := k) h
  have hF' : IsFunctionField k' F' := hF.of_constantCompositum_eq_top h
  have hex' : IsIntegrallyClosedIn k' F' := hex.of_constantCompositum_eq_top h
  -- The algebra structures making `F₁ ⊆ F₁ · k' ⊆ F'` and `F₂ ⊆ F₂ · k' ⊆ F'` towers over `k`.
  let : Algebra F₁ F' := ((algebraMap F F').comp (algebraMap F₁ F)).toAlgebra
  let : Algebra F₂ F' := ((algebraMap F F').comp (algebraMap F₂ F)).toAlgebra
  have : IsScalarTower F₁ F F' := IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  have : IsScalarTower F₂ F F' := IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  have : IsScalarTower k F₁ F' := IsScalarTower.of_algebraMap_eq fun c ↦ by
    rw [IsScalarTower.algebraMap_apply F₁ F F', ← IsScalarTower.algebraMap_apply k F₁ F,
      ← IsScalarTower.algebraMap_apply k F F']
  have : IsScalarTower k F₂ F' := IsScalarTower.of_algebraMap_eq fun c ↦ by
    rw [IsScalarTower.algebraMap_apply F₂ F F', ← IsScalarTower.algebraMap_apply k F₂ F,
      ← IsScalarTower.algebraMap_apply k F F']
  set F₁' := constantCompositum F₁ k' F'
  set F₂' := constantCompositum F₂ k' F'
  let : Algebra k' F₁' := constantCompositumAlgebra F₁ k' F'
  let : Algebra k' F₂' := constantCompositumAlgebra F₂ k' F'
  have : IsScalarTower k' F₁' F' := isScalarTower_constantCompositum F₁ k' F'
  have : IsScalarTower k' F₂' F' := isScalarTower_constantCompositum F₂ k' F'
  have : IsScalarTower k k' F₁' := isScalarTower_base_constantCompositum k F₁ k' F'
  have : IsScalarTower k k' F₂' := isScalarTower_base_constantCompositum k F₂ k' F'
  -- The composita `F₁ · k'` and `F₂ · k'` inside `F'` have the genera and degrees of `F₁`, `F₂`.
  obtain ⟨-, hF₁', _, _, hn₁, hg₁⟩ := constantCompositum_subfield (F₁ := F₁) hF hex h
  obtain ⟨hcc₂, hF₂', _, _, hn₂, hg₂⟩ := constantCompositum_subfield (F₁ := F₂) hF hex h
  have hg := genus_eq_genus_of_constantCompositum_eq_top hF hex h
  -- A place `P₁'` of `F₁ · k'` over `P₁`; every place of `F'` above it is rational.
  obtain ⟨P₁', rfl⟩ :=
    Place.restrict_surjective_of_finiteDimensional (k' := k') (F' := F₁') hF₁ hF₁' P₁
  have hover (R' : Place k' F') (hR' : R'.restrict k' F₁' = P₁') :
      (R'.restrict k F).restrict k F₁ = P₁'.restrict k F₁ := by
    rw [Place.restrict_restrict, ← hR', Place.restrict_restrict]
  have hdeg' (R' : Place k' F') (hR' : R'.restrict k' F₁' = P₁') : R'.degree = 1 := by
    obtain ⟨φR⟩ := hembR _ (hover R' hR')
    exact Place.degree_eq_one_of_constantCompositum_eq_top hF hex h R' φR
  -- `y` stays a primitive element over `F₁ · k'`, with the same minimal polynomial.
  have hmin' : (φ.map (algebraMap (P₁'.restrict k F₁).integers P₁'.integers)).map
      (algebraMap P₁'.integers F₁') = minpoly F₁' (algebraMap F F' y) := by
    have hcomp : (algebraMap P₁'.integers F₁').comp
        (algebraMap (P₁'.restrict k F₁).integers P₁'.integers) =
        (algebraMap F₁ F₁').comp (algebraMap (P₁'.restrict k F₁).integers F₁) :=
      RingHom.ext fun x ↦ Subtype.ext (by simp [IsScalarTower.algebraMap_apply F₁ F F'])
    rw [Polynomial.map_map, hcomp, ← Polynomial.map_map, hmin,
      minpoly_algebraMap_eq_map_of_constantCompositum_eq_top hex h hy]
  have hsep' : ((φ.map (algebraMap (P₁'.restrict k F₁).integers P₁'.integers)).map
      (IsLocalRing.residue P₁'.integers)).Separable := by
    have hcomp : (IsLocalRing.residue P₁'.integers).comp
        (algebraMap (P₁'.restrict k F₁).integers P₁'.integers) =
        (algebraMap (P₁'.restrict k F₁).ResidueField P₁'.ResidueField).comp
          (IsLocalRing.residue (P₁'.restrict k F₁).integers) :=
      RingHom.ext fun x ↦ (IsLocalRing.ResidueField.algebraMap_residue x).symm
    rw [Polynomial.map_map, hcomp, ← Polynomial.map_map]
    exact hsep.map
  -- The places of `F₂ · k'` over the chosen places of `F₂` are rational.
  have hrat : ((genus k' F₂' + Module.finrank F₁' F' : ℕ) : ℕ∞) ≤
      {Q' : Place k' F₂' | Q'.degree = 1}.encard := by
    rw [hg₂, hn₁, ← hTQ]
    have hsurj := Place.restrict_surjective_of_finiteDimensional (k' := k') (F' := F₂') hF₂ hF₂'
    choose Q' hQ' using fun Q : Place k F₂ ↦ hsurj Q
    simp only at hQ'
    have hdegQ (Q₀ : Place k' F₂') (hQ₀ : Q₀.restrict k F₂ ∈ TQ) : Q₀.degree = 1 := by
      obtain ⟨φQ⟩ := hembQ _ hQ₀
      exact Place.degree_eq_one_of_constantCompositum_eq_top hF₂ hex₂ hcc₂ Q₀ φQ
    have hinj : Set.InjOn Q' TQ := fun Q _ Q₂ _ hQ ↦ by rw [← hQ' Q, ← hQ' Q₂, hQ]
    rw [← Set.encard_coe_eq_coe_finsetCard, ← hinj.encard_image]
    refine Set.encard_le_encard ?_
    rintro _ ⟨Q, hQ, rfl⟩
    exact hdegQ (Q' Q) (by rw [hQ' Q]; exact hQ)
  have key := genus_le_of_forall_degree_eq_one hF' hex' hdeg'
    (adjoin_simple_eq_top_of_constantCompositum_eq_top h hy) hmin' hsep'
    (fun i ↦ algebraMap F₁ F₁' (c i)) (fun i ↦ algebraMap F₂ F₂' (z i))
    (by
      rw [hyz, map_sum]
      refine Finset.sum_congr rfl fun i _ ↦ ?_
      rw [map_mul, ← IsScalarTower.algebraMap_apply F₁ F₁' F',
        ← IsScalarTower.algebraMap_apply F₂ F₂' F', IsScalarTower.algebraMap_apply F₁ F F',
        IsScalarTower.algebraMap_apply F₂ F F'])
    (fun i ↦ (Place.mem_integers_restrict_iff k F₁ P₁' (c i)).mp (hc i))
    (fun i R' hR' ↦ by
      rw [← IsScalarTower.algebraMap_apply F₂ F₂' F', IsScalarTower.algebraMap_apply F₂ F F']
      exact (Place.mem_integers_restrict_iff k F R' _).mp (hz i _ (hover R' hR')))
    hrat
  rwa [hg, hg₁, hg₂, hn₁, hn₂] at key

/-- A field `K` generated over `k` by an integral element `x` embeds into every extension `k'` of
`k` over which some nonzero multiple of the minimal polynomial of `x` splits. -/
private theorem nonempty_algHom_of_minpoly_dvd {K k' : Type*} [Field K] [Field k'] [Algebra k K]
    [Algebra k k'] {x : K} (hx : k⟮x⟯ = ⊤) (hint : IsIntegral k x) {f : k[X]} (hf0 : f ≠ 0)
    (hdvd : minpoly k x ∣ f) (hsplit : (f.map (algebraMap k k')).Splits) :
    Nonempty (K →ₐ[k] k') := by
  refine IntermediateField.nonempty_algHom_of_adjoin_splits (S := {x}) (fun s hs ↦ ?_) hx
  rw [Set.mem_singleton_iff.mp hs]
  exact ⟨hint, hsplit.of_dvd (Polynomial.map_ne_zero hf0) (Polynomial.map_dvd _ hdvd)⟩

/-- **Castelnuovo's inequality** (Stichtenoth, Theorem 3.11.3). Let `F / k` be a function field
over a perfect field `k`, with exact constant field `k`, and let `F₁`, `F₂` be subfields of `F`
containing `k` with `F = F₁ F₂`, `F` finite over both, and `F / F₁` separable. Then

`g(F) ≤ [F : F₁] g(F₁) + [F : F₂] g(F₂) + ([F : F₁] - 1) ([F : F₂] - 1)`. -/
theorem genus_le_finrank_mul_genus_add_finrank_mul_genus_add [PerfectField k]
    (hF : IsFunctionField k F) (hex : IsIntegrallyClosedIn k F) [Algebra.IsSeparable F₁ F]
    (htop : IntermediateField.adjoin F₁ (Set.range (algebraMap F₂ F)) = ⊤) :
    genus k F ≤ Module.finrank F₁ F * genus k F₁ + Module.finrank F₂ F * genus k F₂ +
      (Module.finrank F₁ F - 1) * (Module.finrank F₂ F - 1) := by
  classical
  have : Algebra.IsAlgebraic F₁ F := Algebra.IsAlgebraic.of_finite F₁ F
  have : Algebra.IsAlgebraic F₂ F := Algebra.IsAlgebraic.of_finite F₂ F
  have hF₂ : IsFunctionField k F₂ := hF.of_isAlgebraic_top
  /- A primitive element `y` of `F / F₁`, written as an `F₁`-linear combination of elements of
  `F₂`, and a place `P₁` of `F₁` of separable reduction for `y`. -/
  obtain ⟨y, hy⟩ := Field.exists_primitive_element F₁ F
  have hspan : y ∈ Submodule.span F₁ (Set.range (algebraMap F₂ F)) := by
    rw [IntermediateField.span_range_eq_top_of_adjoin_range_eq_top htop]
    exact Submodule.mem_top
  obtain ⟨n, c, z', hyz'⟩ := Submodule.mem_span_set'.mp hspan
  choose z hz using fun i ↦ (z' i).2
  have hyz : y = ∑ i, algebraMap F₁ F (c i) * algebraMap F₂ F (z i) := by
    rw [← hyz']
    exact Finset.sum_congr rfl fun i _ ↦ by rw [hz, Algebra.smul_def]
  obtain ⟨P₁, φ, hmin, hsep, hc, hz'⟩ := exists_place_separable_reduction hF y c z
  /- The residue fields to be made rational: those of the places of `F` over `P₁`, and those of
  `g(F₂) + [F : F₁]` places of `F₂`. Each is generated over `k` by one element, `k` being
  perfect, and `f` is the product of the minimal polynomials of these generators. -/
  have hSR := Place.finite_setOf_restrict_eq (k' := k) (F' := F) k F₁ P₁
  have := Place.infinite hF₂
  obtain ⟨TQ, hTQ⟩ :=
    Infinite.exists_subset_card_eq (Place k F₂) (genus k F₂ + Module.finrank F₁ F)
  choose α hα hαint using fun R : Place k F ↦
    letI := R.finiteDimensional_residueField hF
    ((Field.exists_primitive_element k R.ResidueField).imp fun a ha ↦ ⟨ha, .of_finite k a⟩ :
      ∃ a : R.ResidueField, k⟮a⟯ = ⊤ ∧ IsIntegral k a)
  choose β hβ hβint using fun Q : Place k F₂ ↦
    letI := Q.finiteDimensional_residueField hF₂
    ((Field.exists_primitive_element k Q.ResidueField).imp fun b hb ↦ ⟨hb, .of_finite k b⟩ :
      ∃ b : Q.ResidueField, k⟮b⟯ = ⊤ ∧ IsIntegral k b)
  set f : k[X] := (∏ R ∈ hSR.toFinset, minpoly k (α R)) * ∏ Q ∈ TQ, minpoly k (β Q)
  have hf0 : f ≠ 0 := mul_ne_zero (Finset.prod_ne_zero_iff.mpr fun R _ ↦ minpoly.ne_zero (hαint R))
    (Finset.prod_ne_zero_iff.mpr fun Q _ ↦ minpoly.ne_zero (hβint Q))
  obtain ⟨F', k', _, _, hsplit, -, h⟩ :=
    exists_finiteDimensional_normal_splits_constantCompositum_eq_top F f
  -- The residue fields of the chosen places embed into `k'`, since `f` splits in `k'`.
  exact genus_le_of_constantCompositum_eq_top hF hex h hy hmin hsep c z hyz hc hz'
    (fun R hR ↦ nonempty_algHom_of_minpoly_dvd (hα R) (hαint R) hf0
      ((Finset.dvd_prod_of_mem _ (hSR.mem_toFinset.mpr hR)).mul_right _) hsplit) hTQ
    (fun Q hQ ↦ nonempty_algHom_of_minpoly_dvd (hβ Q) (hβint Q) hf0
      ((Finset.dvd_prod_of_mem _ hQ).mul_left _) hsplit)

end TauCeti
