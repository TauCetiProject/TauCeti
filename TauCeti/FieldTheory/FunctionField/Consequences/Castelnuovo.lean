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
public import TauCeti.FieldTheory.FunctionField.Place.Extension.Splitting
public import TauCeti.FieldTheory.IntermediateField.Adjoin.PrimitiveElement

/-!
# Castelnuovo's inequality

Let `F / k` be an algebraic function field with exact constant field `k`, and let `F₁`, `F₂` be
subfields of `F` containing `k`, of genera `g₁`, `g₂`, over which `F` is finite of degrees
`n₁ = [F : F₁]` and `n₂ = [F : F₂]`. **Castelnuovo's inequality** bounds the genus of `F`:

`g ≤ n₁ g₁ + n₂ g₂ + (n₁ - 1) (n₂ - 1)`.

This file proves it whenever `F₁` has a place `P₁` that splits completely in `F` into places
whose restrictions to `F₂` are pairwise distinct and rational, and `F₂` has at least `g₂` further
rational places. Over an algebraically closed constant field, with `F / F₁` separable and
`F = F₁ F₂`, such a place exists, which gives the inequality there unconditionally: a primitive
element `y` of `F / F₁` can be taken in `F₂`, and at a place of separable reduction of its minimal
polynomial, Kummer's theorem gives `n₁` places over `P₁` at which `y` takes distinct constant
values.

The proof chooses an `F₁`-basis of `F` made of functions of `F₂` with few poles, and feeds it to
the bound `g ≤ 1 + n₁ (g₁ - 1) + deg C` for a basis of `F / F₁` inside `L(C)`
(`TauCeti.genus_le_one_add_finrank_mul_genus_sub_one_add_degree`). Let `P⁽⁰⁾, …, P⁽ⁿ¹⁻¹⁾` be the
places of `F` over `P₁` and `Q⁽ⁱ⁾` their restrictions to `F₂`. Take a nonspecial effective
divisor `B` of `F₂` of degree `g₂` away from the `Q⁽ⁱ⁾` (Stichtenoth, Proposition 1.6.12). For
`i ≠ 0`, Riemann's theorem gives `ℓ(B + Q⁽ⁱ⁾) ≥ 2 > ℓ(B)`, so some `zᵢ ∈ L(B + Q⁽ⁱ⁾)` has a pole
at `Q⁽ⁱ⁾` and none at the other `Q⁽ʲ⁾`; put `z₀ = 1`. In a relation `∑ cᵢ zᵢ = 0` with
`cᵢ ∈ F₁`, the coefficients have the same order at every `P⁽ʲ⁾`, namely `e (P⁽ʲ⁾ ∣ P₁)` times
their order at `P₁`; looking at the place `P⁽ⁱ⁾` of a coefficient of least order shows that the
`i`-th term has strictly least order there, which is impossible. So the `zᵢ` are a basis of
`F / F₁` inside `L(A)`, `A = B + ∑_{i ≠ 0} Q⁽ⁱ⁾`, of degree `g₂ + n₁ - 1`, and the conorm of `A`
to `F` has degree `n₂ (g₂ + n₁ - 1)`.

The hypothesis `F = F₁ F₂` of the classical statement is not needed separately: the basis above
consists of elements of `F₂`.

## Main results

* `TauCeti.Place.linearIndependent_of_ord_neg_of_restrict_eq`: functions of `F` with a pole at
  one place over `P₁` each, and regular at the others, are linearly independent over `F₁`.
* `TauCeti.genus_le_finrank_mul_genus_add_finrank_mul_genus_add_of_isSplitCompletely`:
  **Castelnuovo's inequality** `g ≤ n₁ g₁ + n₂ g₂ + (n₁ - 1) (n₂ - 1)`, from a place of `F₁`
  splitting completely in `F` with distinct rational restrictions to `F₂`.
* `TauCeti.genus_le_finrank_mul_genus_add_finrank_mul_genus_add_of_isAlgClosed`:
  **Castelnuovo's inequality** over an algebraically closed field, for `F = F₁ F₂` with `F / F₁`
  separable.

## References

* H. Stichtenoth, *Algebraic Function Fields and Codes*, 2nd ed., GTM 254, Springer, 2009,
  Proposition 3.11.1 and Theorem 3.11.3.
-/

public section

namespace TauCeti

open AlgebraicGeometry

namespace Place

variable {k F₁ F : Type*} [Field k] [Field F₁] [Field F]
variable [Algebra k F₁] [Algebra k F] [Algebra F₁ F] [IsScalarTower k F₁ F]
variable [Algebra.IsIntegral F₁ F]

/-- The order of `c • z` at a place `P` of `F` over the place `P₁` of `F₁`, for `c ∈ F₁`. -/
private theorem ord_smul_of_restrict_eq {P₁ : Place k F₁} {P : Place k F}
    (hP : P.restrict k F₁ = P₁) {c : F₁} (hc : c ≠ 0) {z : F} (hz : z ≠ 0) :
    P.ord (c • z) = ramificationIdx F₁ P * P₁.ord c + P.ord z := by
  rw [Algebra.smul_def, P.ord_mul ((map_ne_zero _).mpr hc) hz, ord_algebraMap_restrict k F₁ P c,
    hP]

/-- **Poles at the places over a place give independence over the subfield.** Let `P i` be places
of `F` over one place `P₁` of `F₁`, and let `z i ∈ F` be regular at `P j` for `j ≠ i`. If `z i`
has a pole at `P i` for every `i ≠ i₀`, and `z i₀` is a nonzero function without zero at `P i₀`,
then the `z i` are linearly independent over `F₁`. -/
theorem linearIndependent_of_ord_neg_of_restrict_eq {ι : Type*} [Finite ι] {P₁ : Place k F₁}
    {P : ι → Place k F} (hP : ∀ i, (P i).restrict k F₁ = P₁) {z : ι → F} {i₀ : ι}
    (hz₀ : z i₀ ≠ 0) (hord₀ : (P i₀).ord (z i₀) ≤ 0) (hpole : ∀ i, i ≠ i₀ → (P i).ord (z i) < 0)
    (hreg : ∀ i j, i ≠ j → 0 ≤ (P i).ord (z j)) :
    LinearIndependent F₁ z := by
  classical
  have := Fintype.ofFinite ι
  have hz : ∀ i, z i ≠ 0 := fun i ↦ by
    rcases eq_or_ne i i₀ with rfl | hi
    · exact hz₀
    · rintro h
      have := hpole i hi
      rw [h, ord_zero] at this
      exact this.false
  rw [Fintype.linearIndependent_iff]
  intro c hc
  by_contra! hne
  obtain ⟨i₁, hi₁⟩ := hne
  -- A coefficient of least order at `P₁`.
  obtain ⟨m, hmS, hmin⟩ := Finset.exists_min_image (Finset.univ.filter fun i ↦ c i ≠ 0)
    (fun i ↦ P₁.ord (c i)) ⟨i₁, by simpa using hi₁⟩
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hmS hmin
  -- The index at whose place the sum is tested: a minimizer other than `i₀` if there is one.
  obtain ⟨j, hcj, hjmin, hlt⟩ : ∃ j, c j ≠ 0 ∧ P₁.ord (c j) = P₁.ord (c m) ∧
      ∀ i, i ≠ j → c i ≠ 0 →
        (P j).ord (c j • z j) < (P j).ord (c i • z i) := by
    by_cases hA : ∃ j, j ≠ i₀ ∧ c j ≠ 0 ∧ P₁.ord (c j) = P₁.ord (c m)
    · obtain ⟨j, hji₀, hcj, hjm⟩ := hA
      refine ⟨j, hcj, hjm, fun i hij hci ↦ ?_⟩
      rw [ord_smul_of_restrict_eq (hP j) hcj (hz j), ord_smul_of_restrict_eq (hP j) hci (hz i)]
      have he : (0 : ℤ) ≤ ramificationIdx F₁ (P j) := by positivity
      have := mul_le_mul_of_nonneg_left (hjm ▸ hmin i hci) he
      linarith [hpole j hji₀, hreg j i (Ne.symm hij)]
    · push Not at hA
      have hm : m = i₀ := by
        by_contra h
        exact hA m h hmS rfl
      subst hm
      refine ⟨m, hmS, rfl, fun i hij hci ↦ ?_⟩
      rw [ord_smul_of_restrict_eq (hP m) hmS (hz m), ord_smul_of_restrict_eq (hP m) hci (hz i)]
      have he : (0 : ℤ) < ramificationIdx F₁ (P m) := by exact_mod_cast ramificationIdx_pos F₁ _
      have hlt := lt_of_le_of_ne (hmin i hci) (Ne.symm (hA i hij hci))
      have := mul_lt_mul_of_pos_left hlt he
      linarith [hreg m i (Ne.symm hij)]
  -- The summand of index `j` has strictly least order at `P j`, so the sum is nonzero.
  refine (P j).sum_ne_zero_of_forall_ord_lt (s := Finset.univ.filter fun i ↦ c i ≠ 0)
    (f := fun i ↦ c i • z i) (by simpa using hcj) (smul_ne_zero hcj (hz j))
    (fun i hi hij ↦ hlt i hij (by simpa using hi)) ?_
  rw [Finset.sum_filter_of_ne fun i _ h ↦ left_ne_zero_of_smul h]
  exact hc

end Place

variable {k F₁ F₂ F : Type*} [Field k] [Field F₁] [Field F₂] [Field F]
variable [Algebra k F₁] [Algebra k F₂] [Algebra k F] [Algebra F₁ F] [Algebra F₂ F]
variable [IsScalarTower k F₁ F] [IsScalarTower k F₂ F]
variable [FiniteDimensional F₁ F] [FiniteDimensional F₂ F]

/-- For an effective divisor `B` of `F₂` with `deg B = g(F₂)` and `ℓ(B) = 1`, and a rational place
`Q`, some function of `L(B + Q)` has a pole at `Q`: Riemann's theorem gives `ℓ(B + Q) ≥ 2`. -/
private theorem exists_mem_riemannRochSpace_add_ofPoint_ord_neg (hF₂ : IsFunctionField k F₂)
    {B : Divisor k F₂} (hB : 0 ≤ B) (hBdeg : Divisor.degree B = genus k F₂)
    (hBdim : Divisor.dim B = 1) {Q : Place k F₂} (hQ : Q.degree = 1) :
    ∃ z ∈ riemannRochSpace (B + WeilDivisor.ofPoint Q), Q.ord z < 0 := by
  have := finiteDimensional_riemannRochSpace hF₂ (B + WeilDivisor.ofPoint Q)
  have hdim := Divisor.degree_add_one_sub_genus_le_dim hF₂ (B + WeilDivisor.ofPoint Q)
  rw [Divisor.degree_add, Divisor.degree_ofPoint, hBdeg, hQ] at hdim
  have hlt : riemannRochSpace B < riemannRochSpace (B + WeilDivisor.ofPoint Q) := by
    refine Submodule.lt_of_le_of_finrank_lt_finrank (riemannRochSpace_mono ?_) ?_
    · exact WeilDivisor.le_add_ofPoint B Q
    · rw [← Divisor.dim_def, ← Divisor.dim_def, hBdim]
      push_cast at hdim
      omega
  obtain ⟨z, hz, hzB⟩ := IsConcreteLE.exists_of_lt hlt
  refine ⟨z, hz, ?_⟩
  have h := Divisor.ord_eq_neg_coeff_of_not_mem_sub_ofPoint hz (by rwa [add_sub_cancel_right])
  rw [h, WeilDivisor.coeff_add, WeilDivisor.coeff_ofPoint_self]
  have := WeilDivisor.coeff_le_coeff hB Q
  rw [WeilDivisor.coeff_zero] at this
  omega

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
    isIntegrallyClosedIn_iff.mpr ⟨(algebraMap k F₂).injective, fun {z} hz ↦ by
      obtain ⟨c, hc⟩ := (isIntegrallyClosedIn_iff.mp hex).2
        (hz.map (IsScalarTower.toAlgHom k F₂ F))
      exact ⟨c, (algebraMap F₂ F).injective (by
        rw [← IsScalarTower.algebraMap_apply]; exact hc)⟩⟩
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
    exists_mem_riemannRochSpace_add_ofPoint_ord_neg hF₂ hB0 hBdeg hBdim hQ
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
  have hofPoint : ∀ Q : Place k F₂, 0 ≤ WeilDivisor.ofPoint Q := fun Q ↦ by
    simpa using WeilDivisor.le_add_ofPoint (0 : Divisor k F₂) Q
  have hu : ∀ P, u P ∈ riemannRochSpace A := by
    intro P
    by_cases hP : (P : Place k F) = P₀
    · simp only [u, hP, ↓reduceIte]
      exact one_mem_riemannRochSpace_iff.mpr
        (add_nonneg hB0 (Finset.sum_nonneg fun Q _ ↦ hofPoint _))
    · simp only [u, hP, ↓reduceIte]
      refine riemannRochSpace_mono (add_le_add le_rfl ?_) (hwL _ (hdeg P ((hS P).mp P.2)))
      exact Finset.single_le_sum (f := fun P : Place k F ↦ WeilDivisor.ofPoint (P.restrict k F₂))
        (fun _ _ ↦ hofPoint _) (Finset.mem_erase.mpr ⟨hP, P.2⟩)
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

/-- **Castelnuovo's inequality over an algebraically closed field** (Stichtenoth,
Theorem 3.11.3). Let `F / k` be a function field over an algebraically closed field `k`, and let
`F₁`, `F₂` be subfields of `F` containing `k` with `F = F₁ F₂`, `F` finite over both, and `F / F₁`
separable. (The constants of `F` are automatically exact.) Then

`g(F) ≤ [F : F₁] g(F₁) + [F : F₂] g(F₂) + ([F : F₁] - 1) ([F : F₂] - 1)`. -/
theorem genus_le_finrank_mul_genus_add_finrank_mul_genus_add_of_isAlgClosed [IsAlgClosed k]
    (hF : IsFunctionField k F) [Algebra.IsSeparable F₁ F]
    (htop : IntermediateField.adjoin F₁ (Set.range (algebraMap F₂ F)) = ⊤) :
    genus k F ≤ Module.finrank F₁ F * genus k F₁ + Module.finrank F₂ F * genus k F₂ +
      (Module.finrank F₁ F - 1) * (Module.finrank F₂ F - 1) := by
  classical
  have : Algebra.IsAlgebraic F₁ F := Algebra.IsAlgebraic.of_finite F₁ F
  have : Algebra.IsAlgebraic F₂ F := Algebra.IsAlgebraic.of_finite F₂ F
  have hF₁ : IsFunctionField k F₁ := hF.of_isAlgebraic_top
  have hF₂ : IsFunctionField k F₂ := hF.of_isAlgebraic_top
  have hex : IsIntegrallyClosedIn k F := isIntegrallyClosedIn_iff.mpr
    ⟨(algebraMap k F).injective, fun {z} hz ↦ minpoly.mem_range_of_degree_eq_one k z
      (IsAlgClosed.degree_eq_one_of_irreducible k (minpoly.irreducible hz))⟩
  -- A primitive element `y` of `F / F₁` taken in `F₂`.
  obtain ⟨_, ⟨y₂, rfl⟩, hy⟩ := Field.exists_mem_adjoin_simple_eq_top k
    (V := LinearMap.range (IsScalarTower.toAlgHom k F₂ F).toLinearMap) (by
      convert htop using 2
      ext
      simp)
  set y := (IsScalarTower.toAlgHom k F₂ F).toLinearMap y₂
  have hy' : y = algebraMap F₂ F y₂ := by simp [y]
  have := Place.infinite hF₁
  obtain ⟨P₁, hP₁⟩ := (Place.finite_setOf_not_exists_map_eq_minpoly_and_separable hF₁ y
    (Algebra.IsSeparable.isSeparable F₁ y)).infinite_compl.nonempty
  obtain ⟨φ, hmin, hsep⟩ := not_not.mp hP₁
  obtain ⟨s, hs, hsP⟩ :=
    Place.exists_finset_card_eq_forall_exists_restrict_eq_valuation_sub_lt_one (k' := k) hF₁ P₁ y
      hmin hsep
  have hsdeg : s.card = Module.finrank F₁ F := by
    rw [hs, ← _root_.Polynomial.natDegree_map_eq_of_injective
      (IsFractionRing.injective P₁.integers F₁), hmin,
      ← IntermediateField.adjoin.finrank (IsIntegral.of_finite F₁ y), hy,
      IntermediateField.finrank_top']
  have : Nonempty (Place k F) := (Place.infinite hF).nonempty
  choose! R hR hRv using hsP
  -- The places `R a` have pairwise distinct restrictions to `F₂`: `y - a` vanishes at `R a`.
  have hRv₂ : ∀ a ∈ s, ((R a).restrict k F₂).valuation (y₂ - algebraMap k F₂ a) < 1 := by
    intro a ha
    rcases eq_or_ne (y₂ - algebraMap k F₂ a) 0 with h0 | h0
    · rw [h0, map_zero]
      exact zero_lt_one
    have h := hRv a ha
    rw [hy', IsScalarTower.algebraMap_apply k F₂ F, ← map_sub,
      Place.valuation_lt_one_iff_ord_pos _ ((map_ne_zero _).mpr h0),
      Place.ord_algebraMap_restrict k F₂] at h
    exact (Place.valuation_lt_one_iff_ord_pos _ h0).mpr (pos_of_mul_pos_right h (by positivity))
  have hdist : ∀ a ∈ s, ∀ a' ∈ s, (R a).restrict k F₂ = (R a').restrict k F₂ → a = a' := by
    intro a ha a' ha' h
    by_contra hne
    set Q := (R a).restrict k F₂
    have h1 := hRv₂ a ha
    have h2 := hRv₂ a' ha'
    rw [← h] at h2
    have hsub :=
      Valuation.map_sub Q.valuation (y₂ - algebraMap k F₂ a) (y₂ - algebraMap k F₂ a')
    rw [sub_sub_sub_cancel_left, ← map_sub,
      Q.isTrivialOn.eq_one _ (sub_ne_zero.mpr (Ne.symm hne))] at hsub
    exact (hsub.trans_lt (max_lt h1 h2)).false
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
  have hsplit : P₁.IsSplitCompletely (k' := k) (F' := F) :=
    (Place.isSplitCompletely_def P₁).mpr hScard
  have hinj : Set.InjOn (fun P : Place k F ↦ P.restrict k F₂) S := by
    rw [← himg]
    rintro _ ⟨a, ha, rfl⟩ _ ⟨a', ha', rfl⟩ h
    rw [hdist a ha a' ha' h]
  -- Every place is rational, and the restrictions of `S` leave infinitely many places of `F₂`.
  have := Place.infinite hF₂
  refine genus_le_finrank_mul_genus_add_finrank_mul_genus_add_of_isSplitCompletely hF hex hsplit
    hinj (fun P _ ↦ (P.restrict k F₂).degree_eq_one_of_isAlgClosed_of_isFunctionField hF₂)
    (T := ((fun P : Place k F ↦ P.restrict k F₂) '' S)ᶜ)
    (fun Q _ ↦ Q.degree_eq_one_of_isAlgClosed_of_isFunctionField hF₂) ?_
    (fun P hP h ↦ h ⟨P, hP, rfl⟩)
  rw [(hSfin.image _).infinite_compl.encard_eq]
  exact le_top

end TauCeti
