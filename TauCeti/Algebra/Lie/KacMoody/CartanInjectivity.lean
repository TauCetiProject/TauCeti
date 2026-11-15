/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.KacMoody.Triangular
import TauCeti.Algebra.Lie.Presentation.Serre.Triangular

/-!
# Cartan injectivity for generalized Cartan matrices

For an arbitrary integer matrix `A`, `TauCeti.KacMoody.cartanElement` need not be injective: if
`Aᵢⱼ > 0` for `i ≠ j`, the truncated Serre relation imposes `⁅eᵢ, eⱼ⁆ = 0`, and bracketing with
`fᵢ` kills `eⱼ` and `hⱼ`. When `A` satisfies the three axioms of a generalized Cartan matrix
(`A i i = 2`, `A i j ≤ 0` for `i ≠ j`, and `A i j = 0 ↔ A j i = 0`), `H` embeds faithfully into
`TauCeti.KacMoody.PresentedLieAlgebra R` over any field `K`:

1. In the auxiliary Lie algebra presented by the Chevalley relations without Serre's relations,
   Kac's word representation on `List I →₀ K` sends `fᵢ` to left concatenation by `i`, `x ∈ H` to
   the diagonal weight operator shifted by `λ ∈ H*`, and `eᵢ` to the unique operator satisfying
   `eᵢ([]) = 0` and `⁅eᵢ, fⱼ⁆ = δᵢⱼ hᵢ`. Evaluating on `[]` separates `H` from `n₀⁻ + n₀⁺`.
2. Every positive Serre relator commutes with every `fₖ` and is an `ad H`-eigenvector, so the
   positive and negative Serre relators generate Lie ideals contained in `n₀⁺` and `n₀⁻`. Passing
   to the quotient preserves `H` and keeps `n⁻ + n⁺` disjoint from `𝔥`.

## Main definitions

* `TauCeti.KacMoody.cartanEquiv`: the linear equivalence `H ≃ₗ[K] cartanSubalgebra R` when `A` is
  a generalized Cartan matrix.

## Main results

* `TauCeti.KacMoody.cartanElement_injective`: `cartanElement R` is injective for a generalized
  Cartan matrix over any field.
* `TauCeti.KacMoody.positiveGenerator_ne_zero`, `TauCeti.KacMoody.negativeGenerator_ne_zero`, and
  `TauCeti.KacMoody.linearIndependent_cartanElement_coroot`: nonvanishing of Chevalley generators
  and linear independence of simple coroots in `PresentedLieAlgebra R`.
* `TauCeti.KacMoody.disjoint_negativeSubalgebra_sup_positiveSubalgebra_cartanSubalgebra` and
  `TauCeti.KacMoody.derivedSeries_one_inf_cartanSubalgebra`: `(n⁻ + n⁺) ∩ 𝔥 = 0` and
  `⁅𝔤, 𝔤⁆ ∩ 𝔥 = 𝔥'`.
* `TauCeti.KacMoody.cartanElement_mem_center_iff`: `cartanElement R x` is central in `𝔤` if and
  only if `x ∈ R.cartanCenter`.

## References

* V. G. Kac, *Infinite-dimensional Lie algebras*, third edition, Cambridge University Press, 1990,
  Theorem 1.2, §1.3, and §3.3.
-/

public section

open LieAlgebra LieSubalgebra

namespace TauCeti

namespace KacMoody

variable {I K H : Type*} [Field K] [AddCommGroup H] [Module K H] {A : Matrix I I ℤ}
  (R : CartanRealization (A.map (Int.cast : ℤ → K)) H)

/-! ## The auxiliary Chevalley presentation and Kac's word representation -/

open _root_.FreeLieAlgebra Generator in
/-- The Chevalley relators of `R`, omitting Serre's relations. -/
private inductive IsAuxRelator : FreeLieAlgebra K (Generator I H) → Prop
  | cartan_add (x y : H) :
      IsAuxRelator (of K (cartan (x + y)) - of K (cartan x) - of K (cartan y))
  | cartan_smul (c : K) (x : H) : IsAuxRelator (of K (cartan (c • x)) - c • of K (cartan x))
  | lie_cartan_cartan (x y : H) :
      IsAuxRelator ⁅of K (cartan x : Generator I H), of K (cartan y)⁆
  | lie_cartan_positive (x : H) (j : I) :
      IsAuxRelator (⁅of K (cartan x : Generator I H), of K (positive j)⁆ -
        R.root j x • of K (positive j))
  | lie_cartan_negative (x : H) (j : I) :
      IsAuxRelator (⁅of K (cartan x : Generator I H), of K (negative j)⁆ +
        R.root j x • of K (negative j))
  | lie_positive_negative_self (i : I) :
      IsAuxRelator (⁅of K (positive i : Generator I H), of K (negative i)⁆ -
        of K (cartan (R.coroot i)))
  | lie_positive_negative_of_ne (i j : I) (hij : i ≠ j) :
      IsAuxRelator ⁅of K (positive i : Generator I H), of K (negative j)⁆

private noncomputable def auxIdeal : LieIdeal K (FreeLieAlgebra K (Generator I H)) :=
  LieSubmodule.lieSpan K _ {x | IsAuxRelator R x}

private abbrev AuxLieAlgebra : Type _ :=
  FreeLieAlgebra K (Generator I H) ⧸ auxIdeal R

private noncomputable def auxMk : FreeLieAlgebra K (Generator I H) →ₗ⁅K⁆ AuxLieAlgebra R :=
  LieIdeal.mkQ (auxIdeal R)

private theorem auxMk_eq_zero_of_isAuxRelator {x : FreeLieAlgebra K (Generator I H)}
    (hx : IsAuxRelator R x) : auxMk R x = 0 :=
  (LieIdeal.mkQ_apply _ x).trans
    (LieSubmodule.Quotient.mk_eq_zero'.mpr (LieSubmodule.subset_lieSpan hx))

private noncomputable def auxCartan : H →ₗ[K] AuxLieAlgebra R where
  toFun x := auxMk R (FreeLieAlgebra.of K (Generator.cartan x))
  map_add' x y := by
    have h := auxMk_eq_zero_of_isAuxRelator R (.cartan_add x y)
    rwa [map_sub, map_sub, sub_sub, sub_eq_zero] at h
  map_smul' c x := by
    have h := auxMk_eq_zero_of_isAuxRelator R (.cartan_smul c x)
    rwa [map_sub, map_smul, sub_eq_zero] at h

private noncomputable def auxE (i : I) : AuxLieAlgebra R :=
  auxMk R (FreeLieAlgebra.of K (Generator.positive i))

private noncomputable def auxF (i : I) : AuxLieAlgebra R :=
  auxMk R (FreeLieAlgebra.of K (Generator.negative i))

private theorem lieSpan_auxGenerators_eq_top :
    lieSpan K (AuxLieAlgebra R)
      (Set.range (auxCartan R) ∪ Set.range (auxE R) ∪ Set.range (auxF R)) = ⊤ := by
  set S := lieSpan K (AuxLieAlgebra R)
    (Set.range (auxCartan R) ∪ Set.range (auxE R) ∪ Set.range (auxF R))
  have hle : lieSpan K (FreeLieAlgebra K (Generator I H))
      (Set.range (FreeLieAlgebra.of K)) ≤ S.comap (auxMk R) := by
    refine lieSpan_le.mpr ?_
    rintro _ ⟨g, rfl⟩
    cases g with
    | cartan x => exact subset_lieSpan (Or.inl (Or.inl ⟨x, rfl⟩))
    | positive i => exact subset_lieSpan (Or.inl (Or.inr ⟨i, rfl⟩))
    | negative i => exact subset_lieSpan (Or.inr ⟨i, rfl⟩)
  refine eq_top_iff.2 fun y _ => ?_
  obtain ⟨x, rfl⟩ := (auxIdeal R).surjective_mkQ y
  exact hle (by rw [FreeLieAlgebra.lieSpan_range_of_eq_top]; trivial)

/-- Data in a Lie algebra satisfying the Chevalley relations of `R`, without Serre's relations. -/
private structure SatisfiesChevalley {L : Type*} [LieRing L] [LieAlgebra K L]
    (φ : H →ₗ[K] L) (E F : I → L) : Prop where
  lie_cartan_cartan : ∀ x y, ⁅φ x, φ y⁆ = 0
  lie_cartan_positive : ∀ x j, ⁅φ x, E j⁆ = R.root j x • E j
  lie_cartan_negative : ∀ x j, ⁅φ x, F j⁆ = -(R.root j x • F j)
  lie_positive_negative_self : ∀ i, ⁅E i, F i⁆ = φ (R.coroot i)
  lie_positive_negative_of_ne : ∀ i j, i ≠ j → ⁅E i, F j⁆ = 0

private theorem satisfiesChevalley_aux :
    SatisfiesChevalley R (auxCartan R) (auxE R) (auxF R) where
  lie_cartan_cartan x y := by
    simpa [auxCartan] using auxMk_eq_zero_of_isAuxRelator R (.lie_cartan_cartan x y)
  lie_cartan_positive x j := by
    simpa [auxCartan, auxE, sub_eq_zero] using
      auxMk_eq_zero_of_isAuxRelator R (.lie_cartan_positive x j)
  lie_cartan_negative x j := by
    simpa [auxCartan, auxF, add_eq_zero_iff_eq_neg] using
      auxMk_eq_zero_of_isAuxRelator R (.lie_cartan_negative x j)
  lie_positive_negative_self i := by
    simpa [auxCartan, auxE, auxF, sub_eq_zero] using
      auxMk_eq_zero_of_isAuxRelator R (.lie_positive_negative_self i)
  lie_positive_negative_of_ne i j hij := by
    simpa [auxE, auxF] using auxMk_eq_zero_of_isAuxRelator R (.lie_positive_negative_of_ne i j hij)

section AuxLift

variable {L : Type*} [LieRing L] [LieAlgebra K L] {φ : H →ₗ[K] L} {E F : I → L}

private theorem SatisfiesChevalley.neg_swap (h : SatisfiesChevalley R φ E F) :
    SatisfiesChevalley R (-φ) (-F) (-E) where
  lie_cartan_cartan x y := by simp [h.lie_cartan_cartan x y]
  lie_cartan_positive x j := by simp [h.lie_cartan_negative x j]
  lie_cartan_negative x j := by simp [h.lie_cartan_positive x j]
  lie_positive_negative_self i := by simp [← lie_skew (F i) (E i), h.lie_positive_negative_self i]
  lie_positive_negative_of_ne i j hij := by
    simp [← lie_skew (F i) (E j), h.lie_positive_negative_of_ne j i hij.symm]

private noncomputable def auxLift (h : SatisfiesChevalley R φ E F) : AuxLieAlgebra R →ₗ⁅K⁆ L :=
  let g : Generator I H → L := fun | .cartan x => φ x | .positive i => E i | .negative i => F i
  (auxIdeal R).liftQ (FreeLieAlgebra.lift K g) <| LieSubmodule.lieSpan_le.mpr fun x hx => by
    rw [SetLike.mem_coe, LieHom.mem_ker]
    induction hx with
    | cartan_add _ _ | cartan_smul _ _ => simp [g]
    | lie_cartan_cartan x y => simpa [g] using h.lie_cartan_cartan x y
    | lie_cartan_positive x j => simpa [g, sub_eq_zero] using h.lie_cartan_positive x j
    | lie_cartan_negative x j => simpa [g, add_eq_zero_iff_eq_neg] using h.lie_cartan_negative x j
    | lie_positive_negative_self i => simpa [g, sub_eq_zero] using h.lie_positive_negative_self i
    | lie_positive_negative_of_ne i j hij => simpa [g] using h.lie_positive_negative_of_ne i j hij

private theorem auxLift_auxCartan (h : SatisfiesChevalley R φ E F) (x : H) :
    auxLift R h (auxCartan R x) = φ x :=
  (LieIdeal.liftQ_apply _ _ _ _).trans (FreeLieAlgebra.lift_of_apply _ _)

private theorem auxLift_auxE (h : SatisfiesChevalley R φ E F) (i : I) :
    auxLift R h (auxE R i) = E i :=
  (LieIdeal.liftQ_apply _ _ _ _).trans (FreeLieAlgebra.lift_of_apply _ _)

private theorem auxLift_auxF (h : SatisfiesChevalley R φ E F) (i : I) :
    auxLift R h (auxF R i) = F i :=
  (LieIdeal.liftQ_apply _ _ _ _).trans (FreeLieAlgebra.lift_of_apply _ _)

end AuxLift

/-! ### Kac's representation on `List I →₀ K` -/

attribute [local instance 100] LieRing.ofAssociativeRing

@[simp]
private theorem end_lie_apply (T S : Module.End K (List I →₀ K)) (v : List I →₀ K) :
    ⁅T, S⁆ v = T (S v) - S (T v) :=
  rfl

private def wordWeight (w : List I) : Module.Dual K H :=
  (w.map R.root).sum

@[simp] private theorem wordWeight_nil : wordWeight R [] = 0 := (rfl)

@[simp]
private theorem wordWeight_cons (j : I) (w : List I) :
    wordWeight R (j :: w) = R.root j + wordWeight R w :=
  List.sum_cons

private noncomputable def wordF (i : I) : Module.End K (List I →₀ K) :=
  Finsupp.lmapDomain K K (List.cons i)

@[simp]
private theorem wordF_single (i : I) (w : List I) (c : K) :
    wordF i (Finsupp.single w c) = Finsupp.single (i :: w) c := by
  rw [wordF, Finsupp.lmapDomain_apply, Finsupp.mapDomain_single]

private noncomputable def wordH (lam : Module.Dual K H) :
    H →ₗ[K] Module.End K (List I →₀ K) where
  toFun x := Finsupp.linearCombination K fun w => Finsupp.single w ((lam - wordWeight R w) x)
  map_add' x y := Finsupp.lhom_ext fun w c => by
    simp only [LinearMap.add_apply, Finsupp.linearCombination_single, Finsupp.smul_single',
      ← Finsupp.single_add, LinearMap.sub_apply, map_add]
    congr 1; ring
  map_smul' c x := Finsupp.lhom_ext fun w d => by
    simp only [RingHom.id_apply, LinearMap.smul_apply, Finsupp.linearCombination_single,
      Finsupp.smul_single', LinearMap.sub_apply, map_smul, smul_eq_mul]
    congr 1; ring

@[simp]
private theorem wordH_single (lam : Module.Dual K H) (x : H) (w : List I) (c : K) :
    wordH R lam x (Finsupp.single w c) =
      Finsupp.single w (c * ((lam - wordWeight R w) x)) := by
  change Finsupp.linearCombination K _ (Finsupp.single w c) = _
  rw [Finsupp.linearCombination_single, Finsupp.smul_single']

private theorem wordH_wordF_apply (lam : Module.Dual K H) (x : H) (j : I) (u : List I →₀ K) :
    wordH R lam x (wordF j u) = wordF j (wordH R lam x u) - R.root j x • wordF j u := by
  induction u using Finsupp.induction_linear with
  | zero => simp
  | add _ _ h₁ h₂ => simp only [map_add, smul_add, h₁, h₂]; abel
  | single w c =>
    simp only [wordF_single, wordH_single, wordWeight_cons, Finsupp.smul_single',
      ← Finsupp.single_sub, LinearMap.sub_apply, LinearMap.add_apply]
    congr 1; ring

private theorem wordH_comm_apply (lam : Module.Dual K H) (x y : H) (u : List I →₀ K) :
    wordH R lam x (wordH R lam y u) = wordH R lam y (wordH R lam x u) := by
  induction u using Finsupp.induction_linear with
  | zero => simp
  | add _ _ h₁ h₂ => simp [h₁, h₂]
  | single w c => simp only [wordH_single]; congr 1; ring

private noncomputable def wordEOnWord [DecidableEq I] (lam : Module.Dual K H) (i : I) :
    List I → (List I →₀ K)
  | [] => 0
  | j :: w => wordF j (wordEOnWord lam i w) +
      if i = j then Finsupp.single w ((lam - wordWeight R w) (R.coroot i)) else 0

private noncomputable def wordE [DecidableEq I] (lam : Module.Dual K H) (i : I) :
    Module.End K (List I →₀ K) :=
  Finsupp.linearCombination K (wordEOnWord R lam i)

@[simp]
private theorem wordE_single_nil [DecidableEq I] (lam : Module.Dual K H) (i : I) (c : K) :
    wordE R lam i (Finsupp.single [] c) = 0 := by
  simp [wordE, wordEOnWord]

private theorem wordE_wordF_apply [DecidableEq I] (lam : Module.Dual K H) (i j : I)
    (v : List I →₀ K) :
    wordE R lam i (wordF j v) =
      wordF j (wordE R lam i v) + (if i = j then wordH R lam (R.coroot i) v else 0) := by
  induction v using Finsupp.induction_linear with
  | zero => simp
  | add _ _ hu hv => simp only [map_add, hu, hv]; split_ifs <;> abel
  | single w c =>
    simp only [wordF_single, wordE, Finsupp.linearCombination_single, wordEOnWord, smul_add,
      map_smul]
    split_ifs with hij
    · subst hij; rw [wordH_single, Finsupp.smul_single']
    · simp

private theorem satisfiesChevalley_word [DecidableEq I] (lam : Module.Dual K H) :
    SatisfiesChevalley R (wordH R lam) (wordE R lam) wordF where
  lie_cartan_cartan x y := LinearMap.ext fun v => by simp [wordH_comm_apply R lam x y v]
  lie_cartan_negative x j := LinearMap.ext fun v => by simp [wordH_wordF_apply R lam x j v]
  lie_positive_negative_self i := LinearMap.ext fun v => by simp [wordE_wordF_apply]
  lie_positive_negative_of_ne i j hij := LinearMap.ext fun v => by simp [wordE_wordF_apply, hij]
  lie_cartan_positive x i := Finsupp.lhom_ext fun w c => by
    induction w generalizing c with
    | nil => simp
    | cons j w ih =>
      have hcons : Finsupp.single (j :: w) c = wordF j (Finsupp.single w c) := by simp
      have ihc := ih c
      simp only [end_lie_apply, LinearMap.smul_apply] at ihc ⊢
      rw [hcons, wordE_wordF_apply, wordH_wordF_apply, map_add, wordH_wordF_apply,
        sub_eq_iff_eq_add'.1 ihc, map_add, map_smul, map_sub, map_smul, wordE_wordF_apply,
        wordE_wordF_apply, smul_add, smul_add]
      split_ifs with hij
      · subst hij; rw [wordH_comm_apply]; abel
      · simp only [map_zero, smul_zero]; abel

/-- In `AuxLieAlgebra R`, if `auxCartan R x` lies in the sum of the subalgebras generated by `auxF`
and `auxE`, then `x = 0`. -/
private theorem eq_zero_of_auxCartan_mem_sup {x : H}
    (hx : auxCartan R x ∈
      (lieSpan K (AuxLieAlgebra R) (Set.range (auxF R))).toSubmodule ⊔
        (lieSpan K (AuxLieAlgebra R) (Set.range (auxE R))).toSubmodule) :
    x = 0 := by
  classical
  refine (Module.Basis.ofVectorSpace K H).eval_injective ?_
  ext lam
  obtain ⟨uF, huF, uE, huE, huv⟩ := Submodule.mem_sup.1 hx
  let ρ := auxLift R (satisfiesChevalley_word R lam)
  let v₀ : List I →₀ K := Finsupp.single [] 1
  have hE0 : ρ uE v₀ = 0 := by
    have hspan : ρ uE ∈ lieSpan K _ (ρ '' Set.range (auxE R)) := by
      rw [← LieSubalgebra.map_lieSpan]; exact ⟨uE, huE, rfl⟩
    have hmem := lieSpan_le_lieAnnihilator K (Module.End K (List I →₀ K)) (v := v₀) (by
      rintro _ ⟨_, ⟨i, rfl⟩, rfl⟩; simp [ρ, v₀, auxLift_auxE]) hspan
    simpa [mem_lieAnnihilator] using hmem
  have hFgen : ∀ (i : I) (v : List I →₀ K), (wordF (K := K) i v) [] = 0 := fun i v => by
    induction v using Finsupp.induction_linear <;> simp_all
  have hF0 : (ρ uF v₀) [] = 0 := by
    let SF : LieSubalgebra K (Module.End K (List I →₀ K)) :=
      { carrier := {T | ∀ v, (T v) [] = 0}
        zero_mem' := fun _ => rfl
        add_mem' := fun ha hb v => by simp [ha v, hb v]
        smul_mem' := fun _ _ ha v => by simp [ha v]
        lie_mem' := fun {T S} hT hS v => by simp [hT (S v), hS (T v)] }
    have hle : lieSpan K (AuxLieAlgebra R) (Set.range (auxF R)) ≤ SF.comap ρ := by
      rw [lieSpan_le]
      rintro _ ⟨i, rfl⟩ v
      exact (congrArg (fun T : Module.End K (List I →₀ K) => (T v) [])
        (auxLift_auxF R (satisfiesChevalley_word R lam) i)).trans (hFgen i v)
    exact hle huF v₀
  simpa [ρ, v₀, auxLift_auxCartan, hE0, hF0] using congrArg (fun z => (ρ z v₀) []) huv.symm

/-! ### Invariance of the Serre ideal in a Chevalley realization -/

private theorem ad_pow_succ'_apply {L : Type*} [LieRing L] [LieAlgebra K L]
    (x y : L) (n : ℕ) : (ad K L x ^ (n + 1)) y = ⁅x, (ad K L x ^ n) y⁆ := by
  rw [pow_succ', _root_.mul_apply_eq_comp, ad_apply]

private theorem lie_cartan_ad_pow_E {L : Type*} [LieRing L] [LieAlgebra K L]
    {φ : H →ₗ[K] L} {E F : I → L} (h : SatisfiesChevalley R φ E F) (i j : I) (x : H) (m : ℕ) :
    ⁅φ x, (ad K L (E i) ^ m) (E j)⁆ =
      (R.root j x + (m : K) * R.root i x) • (ad K L (E i) ^ m) (E j) := by
  induction m with
  | zero => simp [h.lie_cartan_positive]
  | succ m ih =>
    rw [ad_pow_succ'_apply, leibniz_lie, h.lie_cartan_positive, ih, smul_lie, lie_smul, ← add_smul]
    congr 1; push_cast; ring

private theorem lie_F_self_ad_pow_lie_E_E {L : Type*} [LieRing L] [LieAlgebra K L]
    {φ : H →ₗ[K] L} {E F : I → L} (h : SatisfiesChevalley R φ E F)
    (hdiag : ∀ i, A i i = 2) {i j : I} (hij : i ≠ j) (m : ℕ) :
    ⁅F i, (ad K L (E i) ^ m) ⁅E i, E j⁆⁆ =
      -(((m + 1 : ℤ) * (A i j + m)) • (ad K L (E i) ^ m) (E j)) := by
  induction m with
  | zero =>
    rw [pow_zero, _root_.one_apply_eq_self, leibniz_lie, ← lie_skew (F i) (E i),
      h.lie_positive_negative_self, ← lie_skew (F i) (E j),
      h.lie_positive_negative_of_ne j i hij.symm, neg_zero, lie_zero, add_zero, neg_lie,
      h.lie_cartan_positive]
    simp [Int.cast_smul_eq_zsmul]
  | succ m ih =>
    have hcoroot := lie_cartan_ad_pow_E R h i j (R.coroot i) (m + 1)
    rw [R.root_coroot, R.root_coroot, Matrix.map_apply, Matrix.map_apply, hdiag i] at hcoroot
    rw [ad_pow_succ'_apply, leibniz_lie, ← lie_skew (F i) (E i), h.lie_positive_negative_self,
      neg_lie, ih, ← ad_pow_succ_apply, hcoroot, lie_neg, lie_zsmul, ← ad_pow_succ'_apply]
    have hcast : ((A i j : K) + ((m + 1 : ℕ) : K) * (2 : ℤ)) • (ad K L (E i) ^ (m + 1)) (E j) =
        (A i j + 2 * (m + 1 : ℤ)) • (ad K L (E i) ^ (m + 1)) (E j) := by
      rw [← Int.cast_smul_eq_zsmul K]; congr 1; push_cast; ring
    rw [hcast, ← neg_add, ← add_zsmul]
    congr 2; push_cast; ring

/-- In any Lie algebra with Chevalley generators `(φ, E, F)` for a generalized Cartan matrix `A`,
every positive Serre relator commutes with every lowering generator `F k`. -/
private theorem lie_F_ad_pow_lie_E_E {L : Type*} [LieRing L] [LieAlgebra K L]
    {φ : H →ₗ[K] L} {E F : I → L} (h : SatisfiesChevalley R φ E F)
    (hdiag : ∀ i, A i i = 2) (hoff : ∀ i j, i ≠ j → A i j ≤ 0)
    (hzero : ∀ i j, A i j = 0 ↔ A j i = 0) (k i j : I) :
    ⁅F k, (ad K L (E i) ^ (-A i j).toNat) ⁅E i, E j⁆⁆ = 0 := by
  rcases eq_or_ne i j with rfl | hij
  · simp
  rcases eq_or_ne k i with rfl | hki
  · rw [lie_F_self_ad_pow_lie_E_E R h hdiag hij]
    have hA : A k j + ((-A k j).toNat : ℤ) = 0 := by
      have := Int.toNat_of_nonneg (neg_nonneg.2 (hoff k j hij)); omega
    rw [hA, mul_zero, zero_zsmul, neg_zero]
  · have hcomm : ∀ (m : ℕ) (z : L),
        ⁅F k, (ad K L (E i) ^ m) z⁆ = (ad K L (E i) ^ m) ⁅F k, z⁆ := fun m z => by
      induction m with
      | zero => rfl
      | succ m ih =>
        rw [ad_pow_succ'_apply, leibniz_lie, ← lie_skew (F k) (E i),
          h.lie_positive_negative_of_ne i k hki.symm, neg_zero, zero_lie, zero_add, ih,
          ad_pow_succ'_apply]
    rw [hcomm]
    rcases eq_or_ne k j with rfl | hkj
    · have hinner : ⁅F k, ⁅E i, E k⁆⁆ = A k i • E i := by
        rw [leibniz_lie, ← lie_skew (F k) (E i), h.lie_positive_negative_of_ne i k hij,
          neg_zero, zero_lie, zero_add, ← lie_skew (F k) (E k), h.lie_positive_negative_self,
          lie_neg, ← lie_skew (E i), neg_neg, h.lie_cartan_positive]
        simp [Int.cast_smul_eq_zsmul]
      rw [hinner, map_zsmul]
      rcases eq_or_ne ((-A i k).toNat) 0 with hn0 | hnpos
      · have hAik : A i k = 0 := by
          have := hoff i k hij; have := Int.toNat_eq_zero.1 hn0; omega
        rw [(hzero i k).1 hAik, zero_zsmul]
      · obtain ⟨m, hm⟩ := Nat.exists_eq_succ_of_ne_zero hnpos
        rw [hm, ad_pow_succ_apply, lie_self, map_zero, zsmul_zero]
    · rw [leibniz_lie, ← lie_skew (F k) (E i), h.lie_positive_negative_of_ne i k hki.symm,
        ← lie_skew (F k) (E j), h.lie_positive_negative_of_ne j k hkj.symm]
      simp

private noncomputable def serreWord (E : I → AuxLieAlgebra R) (i j : I) (w : List I) :
    AuxLieAlgebra R :=
  w.foldr (fun l y => ⁅E l, y⁆) ((ad K (AuxLieAlgebra R) (E i) ^ (-A i j).toNat) ⁅E i, E j⁆)

@[simp]
private theorem serreWord_nil (E : I → AuxLieAlgebra R) (i j : I) :
    serreWord R E i j [] = (ad K (AuxLieAlgebra R) (E i) ^ (-A i j).toNat) ⁅E i, E j⁆ :=
  rfl

@[simp]
private theorem serreWord_cons (E : I → AuxLieAlgebra R) (i j l : I) (w : List I) :
    serreWord R E i j (l :: w) = ⁅E l, serreWord R E i j w⁆ :=
  rfl

private noncomputable def serreWordSubmodule (E : I → AuxLieAlgebra R) :
    Submodule K (AuxLieAlgebra R) :=
  Submodule.span K {z | ∃ (i j : I) (w : List I), serreWord R E i j w = z}

private theorem serreWordSubmodule_le_lieSpan (E : I → AuxLieAlgebra R) :
    serreWordSubmodule R E ≤ (lieSpan K (AuxLieAlgebra R) (Set.range E)).toSubmodule := by
  rw [serreWordSubmodule, Submodule.span_le]
  rintro _ ⟨i, j, w, rfl⟩
  have hrel : (ad K (AuxLieAlgebra R) (E i) ^ (-A i j).toNat) ⁅E i, E j⁆ ∈
      lieSpan K (AuxLieAlgebra R) (Set.range E) := by
    generalize (-A i j).toNat = m
    induction m with
    | zero => exact lie_mem _ (subset_lieSpan ⟨i, rfl⟩) (subset_lieSpan ⟨j, rfl⟩)
    | succ m ih => rw [ad_pow_succ'_apply]; exact lie_mem _ (subset_lieSpan ⟨i, rfl⟩) ih
  induction w with
  | nil => exact hrel
  | cons l w ih => rw [serreWord_cons]; exact lie_mem _ (subset_lieSpan ⟨l, rfl⟩) ih

private theorem lie_E_mem_serreWordSubmodule (E : I → AuxLieAlgebra R) (l : I)
    {y : AuxLieAlgebra R} (hy : y ∈ serreWordSubmodule R E) :
    ⁅E l, y⁆ ∈ serreWordSubmodule R E := by
  induction hy using Submodule.span_induction with
  | mem _ hz => obtain ⟨i, j, w, rfl⟩ := hz; exact Submodule.subset_span ⟨i, j, l :: w, rfl⟩
  | zero => simp
  | add _ _ _ _ ha hb => rw [lie_add]; exact add_mem ha hb
  | smul c _ _ ha => rw [lie_smul]; exact Submodule.smul_mem _ c ha

private theorem lie_cartan_mem_serreWordSubmodule {φ : H →ₗ[K] AuxLieAlgebra R}
    {E F : I → AuxLieAlgebra R} (h : SatisfiesChevalley R φ E F) (x : H)
    {y : AuxLieAlgebra R} (hy : y ∈ serreWordSubmodule R E) :
    ⁅φ x, y⁆ ∈ serreWordSubmodule R E := by
  have hwt_word : ∀ (i j : I) (w : List I), ∃ c : K,
      ⁅φ x, serreWord R E i j w⁆ = c • serreWord R E i j w := fun i j w => by
    induction w with
    | nil =>
      refine ⟨R.root j x + (((-A i j).toNat + 1 : ℕ) : K) * R.root i x, ?_⟩
      rw [serreWord_nil, ← ad_pow_succ_apply]
      exact lie_cartan_ad_pow_E R h i j x _
    | cons l w ih =>
      obtain ⟨c, hc⟩ := ih
      exact ⟨R.root l x + c, by
        rw [serreWord_cons, leibniz_lie, h.lie_cartan_positive, hc, smul_lie, lie_smul, add_smul]⟩
  induction hy using Submodule.span_induction with
  | mem _ hz =>
    obtain ⟨i, j, w, rfl⟩ := hz
    obtain ⟨c, hc⟩ := hwt_word i j w
    exact hc ▸ Submodule.smul_mem _ c (Submodule.subset_span ⟨i, j, w, rfl⟩)
  | zero => simp
  | add _ _ _ _ ha hb => rw [lie_add]; exact add_mem ha hb
  | smul c _ _ ha => rw [lie_smul]; exact Submodule.smul_mem _ c ha

private theorem lie_F_mem_serreWordSubmodule {φ : H →ₗ[K] AuxLieAlgebra R}
    {E F : I → AuxLieAlgebra R} (h : SatisfiesChevalley R φ E F)
    (hdiag : ∀ i, A i i = 2) (hoff : ∀ i j, i ≠ j → A i j ≤ 0)
    (hzero : ∀ i j, A i j = 0 ↔ A j i = 0) (k : I)
    {y : AuxLieAlgebra R} (hy : y ∈ serreWordSubmodule R E) :
    ⁅F k, y⁆ ∈ serreWordSubmodule R E := by
  induction hy using Submodule.span_induction with
  | mem _ hz =>
    obtain ⟨i, j, w, rfl⟩ := hz
    induction w with
    | nil =>
      rw [serreWord_nil, lie_F_ad_pow_lie_E_E R h hdiag hoff hzero k i j]
      exact zero_mem _
    | cons l w ih =>
      rw [serreWord_cons, leibniz_lie, ← lie_skew (F k) (E l)]
      refine add_mem ?_ (lie_E_mem_serreWordSubmodule R E l ih)
      rcases eq_or_ne l k with rfl | hlk
      · rw [h.lie_positive_negative_self, neg_lie]
        exact neg_mem (lie_cartan_mem_serreWordSubmodule R h (R.coroot l)
          (Submodule.subset_span ⟨i, j, w, rfl⟩))
      · rw [h.lie_positive_negative_of_ne l k hlk, neg_zero, zero_lie]; exact zero_mem _
  | zero => simp
  | add _ _ _ _ ha hb => rw [lie_add]; exact add_mem ha hb
  | smul c _ _ ha => rw [lie_smul]; exact Submodule.smul_mem _ c ha

/-- In `AuxLieAlgebra R`, the Lie ideal generated by the Serre relators of `(φ, E, F)` lies inside
the Lie subalgebra generated by `E`. -/
private theorem serreLieIdeal_le_lieSpan {φ : H →ₗ[K] AuxLieAlgebra R}
    {E F : I → AuxLieAlgebra R} (h : SatisfiesChevalley R φ E F)
    (hgen : lieSpan K (AuxLieAlgebra R) (Set.range φ ∪ Set.range E ∪ Set.range F) = ⊤)
    (hdiag : ∀ i, A i i = 2) (hoff : ∀ i j, i ≠ j → A i j ≤ 0)
    (hzero : ∀ i j, A i j = 0 ↔ A j i = 0) :
    (LieSubmodule.lieSpan K (AuxLieAlgebra R)
      {z | ∃ i j : I, (ad K (AuxLieAlgebra R) (E i) ^ (-A i j).toNat) ⁅E i, E j⁆ = z}).toSubmodule ≤
      (lieSpan K (AuxLieAlgebra R) (Set.range E)).toSubmodule := by
  have hall : ∀ x : AuxLieAlgebra R, ∀ y ∈ serreWordSubmodule R E,
      ⁅x, y⁆ ∈ serreWordSubmodule R E := fun x => by
    have hx : x ∈ lieSpan K (AuxLieAlgebra R) (Set.range φ ∪ Set.range E ∪ Set.range F) :=
      hgen ▸ mem_top x
    induction hx using lieSpan_induction with
    | mem _ hz =>
      rcases hz with (⟨u, rfl⟩ | ⟨l, rfl⟩) | ⟨k, rfl⟩
      · exact fun _ => lie_cartan_mem_serreWordSubmodule R h u
      · exact fun _ => lie_E_mem_serreWordSubmodule R E l
      · exact fun _ => lie_F_mem_serreWordSubmodule R h hdiag hoff hzero k
    | zero => simp
    | add _ _ _ _ ha hb => intro y hy; rw [add_lie]; exact add_mem (ha y hy) (hb y hy)
    | smul c _ _ ha => intro y hy; rw [smul_lie]; exact Submodule.smul_mem _ c (ha y hy)
    | lie _ _ _ _ ha hb => intro y hy; rw [lie_lie]; exact sub_mem (ha _ (hb y hy)) (hb _ (ha y hy))
  let I_ideal : LieIdeal K (AuxLieAlgebra R) :=
    { serreWordSubmodule R E with lie_mem := fun {x y} hy => hall x y hy }
  have hspan_le : LieSubmodule.lieSpan K (AuxLieAlgebra R)
      {z | ∃ i j : I, (ad K _ (E i) ^ (-A i j).toNat) ⁅E i, E j⁆ = z} ≤ I_ideal := by
    rw [LieSubmodule.lieSpan_le]
    rintro _ ⟨i, j, rfl⟩
    exact Submodule.subset_span ⟨i, j, [], rfl⟩
  exact fun _ hz => serreWordSubmodule_le_lieSpan R E (hspan_le hz)

private noncomputable def auxSerreIdeal : LieIdeal K (AuxLieAlgebra R) :=
  LieSubmodule.lieSpan K (AuxLieAlgebra R)
      {z | ∃ i j : I,
        (ad K (AuxLieAlgebra R) (-auxF R i) ^ (-A i j).toNat) ⁅-auxF R i, -auxF R j⁆ = z} ⊔
    LieSubmodule.lieSpan K (AuxLieAlgebra R)
      {z | ∃ i j : I,
        (ad K (AuxLieAlgebra R) (auxE R i) ^ (-A i j).toNat) ⁅auxE R i, auxE R j⁆ = z}

private theorem satisfiesRelations_auxSerreQuotient :
    SatisfiesRelations R ((LieIdeal.mkQ (auxSerreIdeal R)).toLinearMap ∘ₗ auxCartan R)
      (LieIdeal.mkQ (auxSerreIdeal R) ∘ auxE R)
      (LieIdeal.mkQ (auxSerreIdeal R) ∘ auxF R) := by
  let q := LieIdeal.mkQ (auxSerreIdeal R)
  have hc := satisfiesChevalley_aux R
  refine
    { lie_cartan_cartan := fun u v => by
        rw [LinearMap.comp_apply, LinearMap.comp_apply, LieHom.coe_toLinearMap, ← LieHom.map_lie,
          hc.lie_cartan_cartan, map_zero]
      lie_cartan_positive := fun u j => by
        rw [LinearMap.comp_apply, Function.comp_apply, LieHom.coe_toLinearMap, ← LieHom.map_lie,
          hc.lie_cartan_positive, map_smul]
      lie_cartan_negative := fun u j => by
        rw [LinearMap.comp_apply, Function.comp_apply, LieHom.coe_toLinearMap, ← LieHom.map_lie,
          hc.lie_cartan_negative, map_neg, map_smul]
      lie_positive_negative_self := fun i => by
        rw [Function.comp_apply, Function.comp_apply, LinearMap.comp_apply, LieHom.coe_toLinearMap,
          ← LieHom.map_lie, hc.lie_positive_negative_self]
      lie_positive_negative_of_ne := fun i j hij => by
        rw [Function.comp_apply, Function.comp_apply, ← LieHom.map_lie,
          hc.lie_positive_negative_of_ne i j hij, map_zero]
      serre_positive := fun i j => ?_
      serre_negative := fun i j => ?_ }
  · simp only [Function.comp_apply, ← LieHom.map_lie, ← LieHom.map_ad_pow]
    exact (LieIdeal.mkQ_apply _ _).trans <| LieSubmodule.Quotient.mk_eq_zero'.2 <|
      LieSubmodule.mem_sup_right (LieSubmodule.subset_lieSpan ⟨i, j, rfl⟩)
  · rw [Function.comp_apply, Function.comp_apply]
    have hneg : (ad K _ (-(q (auxF R i))) ^ (-A i j).toNat) ⁅q (auxF R i), q (auxF R j)⁆ = 0 := by
      have hbr : ⁅q (auxF R i), q (auxF R j)⁆ = q ⁅-auxF R i, -auxF R j⁆ := by
        rw [neg_lie, lie_neg, neg_neg, LieHom.map_lie]
      rw [← map_neg q, hbr, ← LieHom.map_ad_pow]
      exact (LieIdeal.mkQ_apply _ _).trans <| LieSubmodule.Quotient.mk_eq_zero'.2 <|
        LieSubmodule.mem_sup_left (LieSubmodule.subset_lieSpan ⟨i, j, rfl⟩)
    have hpos := ad_neg_pow_apply_eq_zero hneg
    rwa [neg_neg] at hpos

/-! ## Cartan injectivity and consequences -/

variable (hdiag : ∀ i, A i i = 2) (hoff : ∀ i j, i ≠ j → A i j ≤ 0)
  (hzero : ∀ i j, A i j = 0 ↔ A j i = 0)
include hdiag hoff hzero

private theorem auxSerreIdeal_le_sup :
    (auxSerreIdeal R).toSubmodule ≤
      (lieSpan K (AuxLieAlgebra R) (Set.range (auxF R))).toSubmodule ⊔
        (lieSpan K (AuxLieAlgebra R) (Set.range (auxE R))).toSubmodule := by
  have hJpos := serreLieIdeal_le_lieSpan R (satisfiesChevalley_aux R)
    (lieSpan_auxGenerators_eq_top R) hdiag hoff hzero
  let Sneg : Set (AuxLieAlgebra R) :=
    Set.range (-(auxCartan R)) ∪ Set.range (-auxF R) ∪ Set.range (-auxE R)
  have hgen_neg : lieSpan K (AuxLieAlgebra R) Sneg = ⊤ := by
    rw [eq_top_iff, ← lieSpan_auxGenerators_eq_top R, lieSpan_le]
    rintro _ ((⟨u, rfl⟩ | ⟨i, rfl⟩) | ⟨i, rfl⟩)
    · have hm : -(auxCartan R (-u)) ∈ Sneg := Or.inl (Or.inl ⟨-u, rfl⟩)
      simpa using neg_mem (subset_lieSpan (R := K) (L := AuxLieAlgebra R) hm)
    · have hm : (-auxE R) i ∈ Sneg := Or.inr ⟨i, rfl⟩
      simpa using neg_mem (subset_lieSpan (R := K) (L := AuxLieAlgebra R) hm)
    · have hm : (-auxF R) i ∈ Sneg := Or.inl (Or.inr ⟨i, rfl⟩)
      simpa using neg_mem (subset_lieSpan (R := K) (L := AuxLieAlgebra R) hm)
  have hspan_negF : lieSpan K (AuxLieAlgebra R) (Set.range (-auxF R)) ≤
      lieSpan K (AuxLieAlgebra R) (Set.range (auxF R)) := by
    rw [lieSpan_le]
    rintro _ ⟨i, rfl⟩
    exact neg_mem (subset_lieSpan (Set.mem_range_self i))
  rw [auxSerreIdeal, LieSubmodule.sup_toSubmodule]
  exact sup_le_sup (fun _ hz => hspan_negF
    (serreLieIdeal_le_lieSpan R (satisfiesChevalley_aux R).neg_swap hgen_neg hdiag hoff hzero hz))
    hJpos

/-- Core non-collapse lemma: if `cartanElement R x` lies in `n⁻ + n⁺`, then `x = 0`. -/
private theorem eq_zero_of_cartanElement_mem_sup {x : H}
    (hx : cartanElement R x ∈
      (negativeSubalgebra R).toSubmodule ⊔ (positiveSubalgebra R).toSubmodule) :
    x = 0 := by
  let q := LieIdeal.mkQ (auxSerreIdeal R)
  let π : PresentedLieAlgebra R →ₗ⁅K⁆ AuxLieAlgebra R ⧸ auxSerreIdeal R :=
    lift (satisfiesRelations_auxSerreQuotient R)
  obtain ⟨uF, huF, uE, huE, huv⟩ := Submodule.mem_sup.1 hx
  have hπF : π uF ∈ (lieSpan K (AuxLieAlgebra R) (Set.range (auxF R))).map q := by
    suffices (negativeSubalgebra R).map π =
        (lieSpan K (AuxLieAlgebra R) (Set.range (auxF R))).map q from this ▸ ⟨uF, huF, rfl⟩
    rw [negativeSubalgebra_def, LieSubalgebra.map_lieSpan, LieSubalgebra.map_lieSpan,
      ← Set.range_comp, ← Set.range_comp]
    congr 2; funext i; exact lift_negativeGenerator _ i
  have hπE : π uE ∈ (lieSpan K (AuxLieAlgebra R) (Set.range (auxE R))).map q := by
    suffices (positiveSubalgebra R).map π =
        (lieSpan K (AuxLieAlgebra R) (Set.range (auxE R))).map q from this ▸ ⟨uE, huE, rfl⟩
    rw [positiveSubalgebra_def, LieSubalgebra.map_lieSpan, LieSubalgebra.map_lieSpan,
      ← Set.range_comp, ← Set.range_comp]
    congr 2; funext i; exact lift_positiveGenerator _ i
  obtain ⟨wF, hwF, hwFq⟩ := (LieSubalgebra.mem_map q _ _).1 hπF
  obtain ⟨wE, hwE, hwEq⟩ := (LieSubalgebra.mem_map q _ _).1 hπE
  have hdiff : auxCartan R x - (wF + wE) ∈ auxSerreIdeal R := by
    rw [← LieSubmodule.Quotient.mk_eq_zero']
    refine (LieIdeal.mkQ_apply (auxSerreIdeal R) _).symm.trans ?_
    rw [map_sub, sub_eq_zero]
    calc
      q (auxCartan R x) = π (cartanElement R x) :=
        (lift_cartanElement (satisfiesRelations_auxSerreQuotient R) x).symm
      _ = π uF + π uE := by rw [← huv, map_add]
      _ = q (wF + wE) := by rw [← hwFq, ← hwEq, map_add]
  have hwFE : wF + wE ∈
      (lieSpan K (AuxLieAlgebra R) (Set.range (auxF R))).toSubmodule ⊔
        (lieSpan K (AuxLieAlgebra R) (Set.range (auxE R))).toSubmodule :=
    add_mem (Submodule.mem_sup_left hwF) (Submodule.mem_sup_right hwE)
  exact eq_zero_of_auxCartan_mem_sup R
    (by simpa using add_mem (auxSerreIdeal_le_sup R hdiag hoff hzero hdiff) hwFE)

/-- **Cartan injectivity.** For a generalized Cartan matrix `A` over any field `K`, the canonical
linear map `TauCeti.KacMoody.cartanElement R : H →ₗ[K] PresentedLieAlgebra R` is injective. -/
theorem cartanElement_injective : Function.Injective (cartanElement R) :=
  (injective_iff_map_eq_zero _).2 fun _ hx =>
    eq_zero_of_cartanElement_mem_sup R hdiag hoff hzero (hx ▸ zero_mem _)

/-- The linear equivalence between the realization `H` and `TauCeti.KacMoody.cartanSubalgebra R`
induced by `TauCeti.KacMoody.cartanElement` for a generalized Cartan matrix. -/
noncomputable def cartanEquiv : H ≃ₗ[K] cartanSubalgebra R :=
  (LinearEquiv.ofInjective (cartanElement R)
      (cartanElement_injective R hdiag hoff hzero)).trans
    (LinearEquiv.ofEq _ _ (cartanSubalgebra_toSubmodule R).symm)

/-- Coercing `TauCeti.KacMoody.cartanEquiv` to the ambient Lie algebra gives
`TauCeti.KacMoody.cartanElement`. -/
@[simp]
theorem coe_cartanEquiv_apply (x : H) :
    (cartanEquiv R hdiag hoff hzero x : PresentedLieAlgebra R) = cartanElement R x :=
  (rfl)

/-- The inverse of `TauCeti.KacMoody.cartanEquiv` recovers `x` from `cartanElement R x`. -/
@[simp]
theorem cartanEquiv_symm_cartanElement (x : H) :
    (cartanEquiv R hdiag hoff hzero).symm
        ⟨cartanElement R x, cartanElement_mem_cartanSubalgebra R x⟩ = x :=
  (cartanEquiv R hdiag hoff hzero).injective (Subtype.ext (by simp))

/-- For a generalized Cartan matrix, every raising generator `eᵢ` is nonzero. -/
theorem positiveGenerator_ne_zero (i : I) : positiveGenerator R i ≠ 0 := fun h0 =>
  R.coroot_linearIndependent.ne_zero i <| cartanElement_injective R hdiag hoff hzero <| by
    simpa [h0] using (lie_positiveGenerator_negativeGenerator_self R i).symm

/-- For a generalized Cartan matrix, every lowering generator `fᵢ` is nonzero. -/
theorem negativeGenerator_ne_zero (i : I) : negativeGenerator R i ≠ 0 := fun h0 =>
  R.coroot_linearIndependent.ne_zero i <| cartanElement_injective R hdiag hoff hzero <| by
    simpa [h0] using (lie_positiveGenerator_negativeGenerator_self R i).symm

/-- For a generalized Cartan matrix, the images of the simple coroots in
`TauCeti.KacMoody.PresentedLieAlgebra R` are linearly independent. -/
theorem linearIndependent_cartanElement_coroot :
    LinearIndependent K (fun i => cartanElement R (R.coroot i)) :=
  R.coroot_linearIndependent.map' (cartanElement R)
    (LinearMap.ker_eq_bot.2 (cartanElement_injective R hdiag hoff hzero))

/-- For a generalized Cartan matrix over any field `K`, `n⁻ + n⁺` has trivial intersection with
`𝔥`. -/
theorem disjoint_negativeSubalgebra_sup_positiveSubalgebra_cartanSubalgebra :
    Disjoint ((negativeSubalgebra R).toSubmodule ⊔ (positiveSubalgebra R).toSubmodule)
      (cartanSubalgebra R).toSubmodule := by
  rw [cartanSubalgebra_toSubmodule, Submodule.disjoint_def]
  rintro y hy ⟨x, rfl⟩
  rw [eq_zero_of_cartanElement_mem_sup R hdiag hoff hzero hy, map_zero]

/-- **Intersection of the derived algebra with the Cartan subalgebra**: the image of Serre's
presentation meets `LinearMap.range (cartanElement R)` in the image of `R.corootSpan`. -/
theorem range_serreHom_inf_range_cartanElement [DecidableEq I] :
    (serreHom R).range.toSubmodule ⊓ LinearMap.range (cartanElement R) =
      R.corootSpan.map (cartanElement R) := by
  rw [range_serreHom_toSubmodule_eq, sup_right_comm, sup_comm,
    sup_inf_assoc_of_le _ LinearMap.map_le_range, ← cartanSubalgebra_toSubmodule,
    (disjoint_negativeSubalgebra_sup_positiveSubalgebra_cartanSubalgebra R hdiag hoff
      hzero).eq_bot, sup_bot_eq]

/-- **Intersection of `⁅𝔤, 𝔤⁆` with `𝔥`**: the derived subalgebra meets `𝔥` in the image of the
coroot span `R.corootSpan`. -/
theorem derivedSeries_one_inf_cartanSubalgebra :
    (derivedSeries K (PresentedLieAlgebra R) 1).toSubmodule ⊓
        (cartanSubalgebra R).toSubmodule =
      R.corootSpan.map (cartanElement R) := by
  classical
  have hd : (derivedSeries K (PresentedLieAlgebra R) 1).toSubmodule =
      (serreHom R).range.toSubmodule := by
    simpa using (congrArg LieSubalgebra.toSubmodule (range_serreHom_eq_derivedSeries R)).symm
  rw [hd, cartanSubalgebra_toSubmodule,
    range_serreHom_inf_range_cartanElement R hdiag hoff hzero]

/-- For a generalized Cartan matrix, `cartanElement R x` lies in the center of
`TauCeti.KacMoody.PresentedLieAlgebra R` if and only if `x` lies in `R.cartanCenter`. -/
theorem cartanElement_mem_center_iff {x : H} :
    cartanElement R x ∈ LieAlgebra.center K (PresentedLieAlgebra R) ↔ x ∈ R.cartanCenter := by
  refine ⟨fun hx => (R.mem_cartanCenter_iff x).2 fun i => ?_,
    cartanElement_mem_center_of_mem_cartanCenter R⟩
  have h0 : ⁅cartanElement R x, positiveGenerator R i⁆ = 0 := by
    rw [← lie_skew, (LieModule.mem_maxTrivSubmodule K _ _ _).1 hx (positiveGenerator R i), neg_zero]
  rw [lie_cartanElement_positiveGenerator] at h0
  exact (smul_eq_zero.1 h0).resolve_right (positiveGenerator_ne_zero R hdiag hoff hzero i)

end KacMoody

end TauCeti
