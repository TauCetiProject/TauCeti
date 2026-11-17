/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.JamesReducedProduct
public import TauCeti.Topology.Category.TopPair.Quotient

/-!
# The quotients of the word-length filtration of the James reduced product

Let `(X, x₀)` be a pointed space with closed basepoint, and let `J_r X` be the reduced words of
length at most `r` in the James reduced product `J X`
(`TauCeti.JamesReducedProduct.filtration`). This file identifies each quotient
`J_(r+1) X / J_r X` of consecutive stages with the `(r + 1)`-fold smash power of `X`, the quotient
of `Xʳ⁺¹` by its **fat wedge**, the words some letter of which is the basepoint
(`TauCeti.JamesReducedProduct.fatWedge`). These quotients compute the homology of `J X` stage by
stage, which is how the James model computes the homology of the loop space `ΩΣX`.

The identification rests on two facts.

* **Combinatorics.** A word of length `r + 1` reduces into `J_r X` exactly when it lies in the fat
  wedge (`TauCeti.JamesReducedProduct.mk_mem_filtration_iff_mem_fatWedge`), and two words outside
  the fat wedge with the same reduced word are equal (`TauCeti.JamesReducedProduct.mk_injOn`).
* **Topology.** The topology of `J X` is the final topology of the reductions of words of every
  length, but a set of words of length at most `r` is already tested by the words of length `r`
  (`TauCeti.JamesReducedProduct.isClosed_iff_of_subset_filtration`). So `J_r X` carries the
  quotient topology of the compactly generated power `k(Xʳ)`, and when `Xʳ` is compactly
  generated, for instance when `X` is metrizable or compact Hausdorff, the reduction of words
  `Xʳ → J_r X` is a quotient map
  (`TauCeti.JamesReducedProduct.isQuotientMap_filtrationMk`).

Both quotients are formed with `TopPair.ordinaryPairQuotient`, for the pairs
`(Xʳ⁺¹, fat wedge)` (`TauCeti.JamesReducedProduct.fatWedgePair`) and `(J_(r+1) X, J_r X)`
(`TauCeti.JamesReducedProduct.filtrationPair`).

## Main definitions

* `TauCeti.JamesReducedProduct.fatWedge`: the words of length `n` with a letter equal to the
  basepoint.
* `TauCeti.JamesReducedProduct.filtrationMk`: the reduction of words `Xʳ → J_r X`.
* `TauCeti.JamesReducedProduct.fatWedgePair`, `TauCeti.JamesReducedProduct.filtrationPair`: the
  pairs `(Xⁿ, fat wedge)` and `(J_(r+1) X, J_r X)`.
* `TauCeti.JamesReducedProduct.filtrationQuotientHomeomorph`: the homeomorphism
  `Xʳ⁺¹ / fat wedge ≃ₜ J_(r+1) X / J_r X` induced by the reduction of words.

## Main results

* `TauCeti.JamesReducedProduct.mk_mem_filtration_iff_mem_fatWedge`: the words of length `r + 1`
  reducing into `J_r X` form the fat wedge.
* `TauCeti.JamesReducedProduct.isClosed_iff_of_subset_filtration`: closed subsets of `J_r X` are
  detected by the words of length `r`.
* `TauCeti.JamesReducedProduct.isQuotientMap_filtrationMk`: `Xʳ → J_r X` is a quotient map.

## References

* I. M. James, *Reduced product spaces*, Ann. of Math. (2) 62 (1955), 170–197.
* A. Hatcher, *Algebraic Topology*, Cambridge University Press, 2002, Section 3.C.
-/

public section

noncomputable section

universe u

open Set Topology

namespace TauCeti

namespace JamesReducedProduct

variable {X : Type u} {x₀ : X}

/-! ### The fat wedge -/

variable (X x₀) in
/-- The **fat wedge** of `Xⁿ`: the words of length `n` some letter of which is the basepoint. The
quotient of `Xⁿ` by the fat wedge is the `n`-fold smash power of `(X, x₀)`. -/
def fatWedge (n : ℕ) : Set (Fin n → X) :=
  {v | ∃ i, v i = x₀}

@[simp]
theorem mem_fatWedge_iff {n : ℕ} {v : Fin n → X} : v ∈ fatWedge X x₀ n ↔ ∃ i, v i = x₀ :=
  Iff.rfl

theorem notMem_fatWedge_iff {n : ℕ} {v : Fin n → X} : v ∉ fatWedge X x₀ n ↔ ∀ i, v i ≠ x₀ := by
  simp

/-- A word of length `r + 1` reduces into the stage `J_r X` of the word-length filtration exactly
when one of its letters is the basepoint. -/
theorem mk_mem_filtration_iff_mem_fatWedge {r : ℕ} {v : Fin (r + 1) → X} :
    mk v ∈ filtration X x₀ r ↔ v ∈ fatWedge X x₀ (r + 1) := by
  classical
  refine ⟨fun h => ?_, fun ⟨i, hi⟩ => ?_⟩
  · by_contra hv
    rw [notMem_fatWedge_iff] at hv
    rw [mem_filtration_iff, length_mk, Finset.filter_true_of_mem fun i _ => hv i,
      Finset.card_univ, Fintype.card_fin] at h
    omega
  · rw [← mk_removeNth_of_eq_basepoint hi]
    exact mk_mem_filtration _

variable (x₀) in
/-- The reduced word of a word of length `r`, as a point of the stage `J_r X` of the word-length
filtration. -/
def filtrationMk {r : ℕ} (v : Fin r → X) : filtration X x₀ r :=
  ⟨mk v, mk_mem_filtration v⟩

@[simp]
theorem coe_filtrationMk {r : ℕ} (v : Fin r → X) :
    (filtrationMk x₀ v : JamesReducedProduct X x₀) = mk v :=
  (rfl)

/-- Every reduced word of length at most `r` is the reduced word of a word of length `r`. -/
theorem surjective_filtrationMk {r : ℕ} :
    Function.Surjective (filtrationMk x₀ : (Fin r → X) → filtration X x₀ r) := fun w => by
  obtain ⟨v, hv⟩ : (w : JamesReducedProduct X x₀) ∈ range (mk : (Fin r → X) → _) := by
    rw [range_mk]
    exact w.2
  exact ⟨v, Subtype.ext hv⟩

/-! ### The topology of the stages of the filtration -/

section Topology

variable [TopologicalSpace X]

/-- **The stage `J_r X` carries the quotient topology of `k(Xʳ)`.** When the basepoint is closed,
a set of reduced words of length at most `r` is closed in `J X` as soon as its preimages under the
reductions of the continuous families of words of length `r` over compact Hausdorff spaces are
closed: words of other lengths need not be tested. -/
theorem isClosed_iff_of_subset_filtration (h : IsClosed ({x₀} : Set X)) {r : ℕ}
    {s : Set (JamesReducedProduct X x₀)} (hs : s ⊆ filtration X x₀ r) :
    IsClosed s ↔ ∀ (S : CompHaus.{u}) (g : C(S, Fin r → X)),
      IsClosed ((fun t => (mk (g t) : JamesReducedProduct X x₀)) ⁻¹' s) := by
  refine ⟨fun hc S g => isClosed_iff.1 hc r S g, fun H => isClosed_iff.2 fun n => ?_⟩
  -- The test of closedness by the families of words of length `n`.
  let Test : ℕ → Prop := fun n => ∀ (S : CompHaus.{u}) (g : C(S, Fin n → X)),
    IsClosed ((fun t => (mk (g t) : JamesReducedProduct X x₀)) ⁻¹' s)
  -- Appending the basepoint passes the test from length `n + 1` down to length `n`.
  have down (n : ℕ) (hn : Test (n + 1)) : Test n := fun S g => by
    have := hn S ⟨fun t => Fin.snoc (g t) x₀, g.continuous.finSnoc continuous_const⟩
    simpa only [ContinuousMap.coe_mk, mk_snoc_basepoint] using this
  -- From length `r` on, a word reducing into `s` has a letter equal to the basepoint, and
  -- deleting it passes the test from length `n` up to length `n + 1`.
  have up (n : ℕ) (hrn : r ≤ n) (hn : Test n) : Test (n + 1) := fun S g => by
    have hpre : (fun t => (mk (g t) : JamesReducedProduct X x₀)) ⁻¹' s =
        ⋃ i, {t | g t i = x₀} ∩
          (fun t => (mk (i.removeNth (g t)) : JamesReducedProduct X x₀)) ⁻¹' s := by
      ext t
      simp only [mem_preimage, mem_iUnion, mem_inter_iff, mem_ofPred_eq]
      refine ⟨fun ht => ?_, fun ⟨i, hi, ht⟩ => ?_⟩
      · obtain ⟨i, hi⟩ := mk_mem_filtration_iff_mem_fatWedge.1 (filtration_monotone hrn (hs ht))
        exact ⟨i, hi, by rwa [mk_removeNth_of_eq_basepoint hi]⟩
      · rwa [← mk_removeNth_of_eq_basepoint hi]
    rw [hpre]
    exact isClosed_iUnion_of_finite fun i =>
      (h.preimage ((continuous_apply i).comp g.continuous)).inter
        (hn S ⟨fun t => i.removeNth (g t),
          continuous_pi fun _ => (continuous_apply _).comp g.continuous⟩)
  rcases le_total n r with hnr | hrn
  · exact Nat.decreasingInduction (motive := fun k _ => Test k) (fun k _ hk => down k hk) H hnr
  · exact Nat.le_induction (motive := fun k _ => Test k) H (fun k hk => up k hk) n hrn

/-- When `Xʳ` is compactly generated, the reduction of words of length `r` is continuous. -/
@[fun_prop]
theorem continuous_filtrationMk {r : ℕ} [UCompactlyGeneratedSpace.{u} (Fin r → X)] :
    Continuous (filtrationMk x₀ : (Fin r → X) → filtration X x₀ r) :=
  (continuous_mk continuous_id).subtype_mk _

/-- When the basepoint is closed and `Xʳ` is compactly generated, the reduction of words of length
`r` is a quotient map `Xʳ → J_r X` onto the `r`-th stage of the word-length filtration. -/
theorem isQuotientMap_filtrationMk (h : IsClosed ({x₀} : Set X)) {r : ℕ}
    [UCompactlyGeneratedSpace.{u} (Fin r → X)] :
    IsQuotientMap (filtrationMk x₀ : (Fin r → X) → filtration X x₀ r) := by
  refine isQuotientMap_iff_isClosed.2 ⟨surjective_filtrationMk, fun s =>
    ⟨fun hs => hs.preimage continuous_filtrationMk, fun hs => ?_⟩⟩
  rw [(isClosed_filtration h r).isClosedEmbedding_subtypeVal.isClosed_iff_image_isClosed,
    isClosed_iff_of_subset_filtration h (image_subset_iff.2 fun w _ => w.2)]
  intro S g
  have hpre : (fun t => (mk (g t) : JamesReducedProduct X x₀)) ⁻¹' (Subtype.val '' s) =
      g ⁻¹' (filtrationMk x₀ ⁻¹' s) := by
    ext t
    simp only [mem_preimage, Subtype.exists, exists_and_right, exists_eq_right, mem_image]
    exact ⟨fun ⟨_, ht⟩ => ht, fun ht => ⟨mk_mem_filtration _, ht⟩⟩
  rw [hpre]
  exact hs.preimage g.continuous

/-! ### The filtration quotients -/

variable (X x₀) in
/-- The pair `(Xⁿ, fat wedge)`. Its pointed quotient is the `n`-fold smash power of `(X, x₀)`. -/
abbrev fatWedgePair (n : ℕ) : TopPair.{u} :=
  TopPair.ofSubset (X := TopCat.of (Fin n → X)) (fatWedge X x₀ n)

variable (X x₀) in
/-- The pair `(J_(r+1) X, J_r X)` of consecutive stages of the word-length filtration. -/
abbrev filtrationPair (r : ℕ) : TopPair.{u} :=
  TopPair.ofSubset (X := TopCat.of (filtration X x₀ (r + 1)))
    {w | (w : JamesReducedProduct X x₀) ∈ filtration X x₀ r}

instance (n : ℕ) : Nonempty (fatWedgePair X x₀ (n + 1)).snd :=
  ⟨⟨fun _ => x₀, 0, rfl⟩⟩

instance (r : ℕ) : Nonempty (filtrationPair X x₀ r).snd :=
  ⟨⟨⟨1, one_mem_filtration _⟩, one_mem_filtration _⟩⟩

variable (h : IsClosed ({x₀} : Set X)) (r : ℕ) [UCompactlyGeneratedSpace.{u} (Fin (r + 1) → X)]

/-- Reduce a word of length `r + 1` and collapse `J_r X`. -/
private def reduceCollapse :
    TopCat.of (Fin (r + 1) → X) ⟶ (filtrationPair X x₀ r).ordinaryPairQuotient :=
  TopCat.ofHom ⟨fun v => (filtrationPair X x₀ r).ordinaryPairQuotientπ (filtrationMk x₀ v),
    (filtrationPair X x₀ r).ordinaryPairQuotientπ.hom.continuous.comp continuous_filtrationMk⟩

/-- The map `Xʳ⁺¹ / fat wedge → J_(r+1) X / J_r X` induced by the reduction of words. -/
private def filtrationQuotientMap :
    (fatWedgePair X x₀ (r + 1)).ordinaryPairQuotient ⟶
      (filtrationPair X x₀ r).ordinaryPairQuotient :=
  (fatWedgePair X x₀ (r + 1)).ordinaryPairQuotientDesc (reduceCollapse r)
    (filtrationPair X x₀ r).ordinaryPairQuotientBasepoint fun b =>
      ((filtrationPair X x₀ r).ordinaryPairQuotientπ_eq_basepoint_iff _).2
        ⟨⟨filtrationMk x₀ b.1, mk_mem_filtration_iff_mem_fatWedge.2 b.2⟩, rfl⟩

private theorem filtrationQuotientMap_π (v : Fin (r + 1) → X) :
    filtrationQuotientMap r ((fatWedgePair X x₀ (r + 1)).ordinaryPairQuotientπ v) =
      (filtrationPair X x₀ r).ordinaryPairQuotientπ (filtrationMk x₀ v) :=
  TopPair.ordinaryPairQuotientπ_desc_apply (fatWedgePair X x₀ (r + 1)) (reduceCollapse r) _ _ v

include h in
private theorem isHomeomorph_filtrationQuotientMap :
    IsHomeomorph (filtrationQuotientMap (x₀ := x₀) r) := by
  have hπP := (fatWedgePair X x₀ (r + 1)).isQuotientMap_ordinaryPairQuotientπ
  rw [isHomeomorph_iff_isQuotientMap_injective]
  refine ⟨IsQuotientMap.of_comp (fatWedgePair X x₀ (r + 1)).ordinaryPairQuotientπ.hom.continuous
    (filtrationQuotientMap r).hom.continuous ?_, ?_⟩
  · have hcomp : filtrationQuotientMap r ∘ (fatWedgePair X x₀ (r + 1)).ordinaryPairQuotientπ =
        (filtrationPair X x₀ r).ordinaryPairQuotientπ ∘ filtrationMk x₀ :=
      funext (filtrationQuotientMap_π r)
    rw [hcomp]
    exact (filtrationPair X x₀ r).isQuotientMap_ordinaryPairQuotientπ.comp
      (isQuotientMap_filtrationMk h)
  · intro z₁ z₂ hz
    obtain ⟨v, rfl⟩ : ∃ v : Fin (r + 1) → X,
        (fatWedgePair X x₀ (r + 1)).ordinaryPairQuotientπ v = z₁ := hπP.surjective z₁
    obtain ⟨w, rfl⟩ : ∃ w : Fin (r + 1) → X,
        (fatWedgePair X x₀ (r + 1)).ordinaryPairQuotientπ w = z₂ := hπP.surjective z₂
    rw [filtrationQuotientMap_π, filtrationQuotientMap_π] at hz
    replace hz := ((filtrationPair X x₀ r).ordinaryPairQuotientπ_eq_iff
      (filtrationMk x₀ v) (filtrationMk x₀ w)).1 hz
    refine ((fatWedgePair X x₀ (r + 1)).ordinaryPairQuotientπ_eq_iff v w).2 ?_
    -- The ranges of the subspace inclusions are the subspaces themselves.
    have hP (u : Fin (r + 1) → X) :
        u ∈ range (fatWedgePair X x₀ (r + 1)).map ↔ u ∈ fatWedge X x₀ (r + 1) :=
      ⟨fun ⟨b, hb⟩ => hb ▸ b.2, fun hu => ⟨⟨u, hu⟩, rfl⟩⟩
    have hQ (u : Fin (r + 1) → X) :
        filtrationMk x₀ u ∈ range (filtrationPair X x₀ r).map ↔
          u ∈ fatWedge X x₀ (r + 1) :=
      ⟨fun ⟨⟨⟨w', _⟩, hw'⟩, hb⟩ => mk_mem_filtration_iff_mem_fatWedge.1 <| by
          have hb' : w' = mk u := congrArg Subtype.val hb
          exact hb' ▸ hw',
        fun hu => ⟨⟨_, mk_mem_filtration_iff_mem_fatWedge.2 hu⟩, rfl⟩⟩
    rcases hz with hz | ⟨hv, hw⟩
    · have hmk : (mk v : JamesReducedProduct X x₀) = mk w := congrArg Subtype.val hz
      by_cases hv : v ∈ fatWedge X x₀ (r + 1)
      · have hw : w ∈ fatWedge X x₀ (r + 1) := by
          rw [← mk_mem_filtration_iff_mem_fatWedge, ← hmk]
          exact mk_mem_filtration_iff_mem_fatWedge.2 hv
        exact Or.inr ⟨(hP v).2 hv, (hP w).2 hw⟩
      · have hw : w ∉ fatWedge X x₀ (r + 1) := fun hw => hv <| by
          rw [← mk_mem_filtration_iff_mem_fatWedge, hmk]
          exact mk_mem_filtration_iff_mem_fatWedge.2 hw
        exact Or.inl (mk_injOn (notMem_fatWedge_iff.1 hv) (notMem_fatWedge_iff.1 hw) hmk)
    · exact Or.inr ⟨(hP v).2 ((hQ v).1 hv), (hP w).2 ((hQ w).1 hw)⟩

/-- **The filtration quotients of the James reduced product are smash powers.** For a pointed
space with closed basepoint whose power `Xʳ⁺¹` is compactly generated, the reduction of words
induces a homeomorphism from the quotient of `Xʳ⁺¹` by its fat wedge, the `(r + 1)`-fold smash
power of `X`, onto the quotient `J_(r+1) X / J_r X` of consecutive stages of the word-length
filtration. -/
def filtrationQuotientHomeomorph :
    (fatWedgePair X x₀ (r + 1)).ordinaryPairQuotient ≃ₜ
      (filtrationPair X x₀ r).ordinaryPairQuotient :=
  (isHomeomorph_filtrationQuotientMap h r).homeomorph

@[simp]
theorem filtrationQuotientHomeomorph_π (v : Fin (r + 1) → X) :
    filtrationQuotientHomeomorph h r ((fatWedgePair X x₀ (r + 1)).ordinaryPairQuotientπ v) =
      (filtrationPair X x₀ r).ordinaryPairQuotientπ (filtrationMk x₀ v) :=
  filtrationQuotientMap_π r v

@[simp]
theorem filtrationQuotientHomeomorph_symm_π (v : Fin (r + 1) → X) :
    (filtrationQuotientHomeomorph h r).symm
        ((filtrationPair X x₀ r).ordinaryPairQuotientπ (filtrationMk x₀ v)) =
      (fatWedgePair X x₀ (r + 1)).ordinaryPairQuotientπ v := by
  rw [Homeomorph.symm_apply_eq, filtrationQuotientHomeomorph_π]

@[simp]
theorem filtrationQuotientHomeomorph_basepoint :
    filtrationQuotientHomeomorph h r (fatWedgePair X x₀ (r + 1)).ordinaryPairQuotientBasepoint =
      (filtrationPair X x₀ r).ordinaryPairQuotientBasepoint :=
  TopPair.ordinaryPairQuotientDesc_basepoint _ _ _ _

end Topology

end JamesReducedProduct

end TauCeti
