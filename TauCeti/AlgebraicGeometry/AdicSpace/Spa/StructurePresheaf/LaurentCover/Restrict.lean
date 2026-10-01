/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
module

public import TauCeti.AlgebraicGeometry.AdicSpace.Spa.StructurePresheaf.LaurentCover.Basic
public import TauCeti.AlgebraicGeometry.AdicSpace.Spa.StructurePresheaf.Localization

import TauCeti.RingTheory.Huber.LocalizationTopology.StronglyNoetherian

/-!
# The Laurent cover restricted to a rational subset

Let `W = R(T/s)` be a rational subset of `X = Spa(A, A⁺)` and `f ∈ A`. The two pieces
`W ∩ {|f| ≤ 1}` and `W ∩ {|f| ≥ 1}` cover `W`. When `A` is a strongly noetherian Tate ring and
`A⁺` consists of power-bounded elements, the augmented two-piece Čech sequence of the
presentation-limit presheaf for this cover of `W` is exact: a section over `W` is determined by its
restrictions to the two pieces, sections over the pieces that agree on their overlap come from a
section over `W`, and every section over the overlap is a difference of restrictions from the
pieces. For `W = X` and complete Hausdorff `A` this is Wedhorn's Lemma 8.33, proved in
`TauCeti.AlgebraicGeometry.AdicSpace.Spa.StructurePresheaf.LaurentCover.Basic`.

The general case is the first step of the proof of Wedhorn's Lemma 8.34(i). Let `B = A⟨T/s⟩` with
plus ring `A_U⁺`, and let `j : Spa(B, A_U⁺) → X` be induced by the structure map `ρ : A → B`
(pullback along `j` is `locOpensComap`). Then `j⁻¹(W)` is all of `Spa(B, A_U⁺)`, and `j⁻¹` carries
the Laurent cover of `f` to the Laurent cover of `ρ(f)` (`locOpensComap_laurentCoverOpen`).
Wedhorn's Remark 8.4 (`presentationLimitLocIso`) identifies the presentation limits over rational
opens `V ⊆ W` with those over `j⁻¹(V)`, compatibly with restriction. Since `B` is again a complete
Hausdorff strongly noetherian Tate ring, Lemma 8.33 for `B` transports to the restricted cover. In
particular `A` itself need not be complete.

## Main results

* `TauCeti.ValuationSpectrum.locOpensComap_laurentCoverOpen` : the pullback of a Laurent piece of
  `f` along `j` is the corresponding Laurent piece of `ρ(f)`.
* `TauCeti.ValuationSpectrum.injective_presentationLimitMap_inf_laurentCoverOpen` : restriction
  from `R(T/s)` to the two pieces is injective.
* `TauCeti.ValuationSpectrum.exists_presentationLimitMap_eq_of_inf_laurentCoverOpen` : sections
  over the two pieces that agree on their overlap come from a section over `R(T/s)`.
* `TauCeti.ValuationSpectrum.surjective_presentationLimitMap_sub_inf_laurentCoverOpen` : the
  difference of restrictions from the two pieces onto their overlap is surjective.

## References

* [T. Wedhorn, *Adic Spaces*][wedhorn_adic] (arXiv:1910.05934v1), Remark 8.4, Lemma 8.33 and
  Lemma 8.34(i).
-/

public section

open CategoryTheory TopologicalSpace TauCeti.Huber TauCeti.Huber.PairOfDefinition

universe v

namespace TauCeti.ValuationSpectrum

/-! ### Pulling back the Laurent cover -/

section Pullback

variable {A : Type v} [CommRing A] [UniformSpace A] [IsTopologicalRing A]
  (P : PairOfDefinition A) (Aplus : Subring A) (T : Finset A) (s : A)
  (S : Type v) [CommRing S] [Algebra A S] [IsLocalization.Away s S]
  (hden : HasDenominatorPower P T s S)

/-- **The Laurent cover pulled back to a rational subset.** Pulling the Laurent piece
`laurentCoverOpen Aplus f b` back along `Spa(A⟨T/s⟩, A_U⁺) → Spa(A, A⁺)` gives the corresponding
Laurent piece of the image of `f` in `A⟨T/s⟩`. -/
theorem locOpensComap_laurentCoverOpen (f : A) (b : Bool) :
    letI := locUniformSpace P T s S hden
    letI := isUniformAddGroup_locUniformSpace P T s S hden
    letI := isTopologicalRing_locUniformSpace P T s S hden
    locOpensComap P Aplus T s S hden (laurentCoverOpen Aplus f b) =
      laurentCoverOpen (completedPlusSubring P Aplus T s S hden)
        (toCompletionLoc P T s S hden f) b := by
  let _ := locUniformSpace P T s S hden
  have _ := isUniformAddGroup_locUniformSpace P T s S hden
  have _ := isTopologicalRing_locUniformSpace P T s S hden
  rw [laurentCoverOpen, laurentCoverOpen, locOpensComap_spaBasicOpen]
  cases b <;> simp only [Bool.cond_true, Bool.cond_false, Finset.image_insert,
    Finset.image_singleton, map_one]

/-- The pullback of the Laurent piece of `f` restricted to `R(T/s)` is the Laurent piece of the
image of `f`, since the pullback of `R(T/s)` is the whole localized spectrum. -/
theorem locOpensComap_inf_laurentCoverOpen (f : A) (b : Bool) :
    letI := locUniformSpace P T s S hden
    letI := isUniformAddGroup_locUniformSpace P T s S hden
    letI := isTopologicalRing_locUniformSpace P T s S hden
    locOpensComap P Aplus T s S hden (spaBasicOpen Aplus T s ⊓ laurentCoverOpen Aplus f b) =
      laurentCoverOpen (completedPlusSubring P Aplus T s S hden)
        (toCompletionLoc P T s S hden f) b := by
  rw [locOpensComap_inf, locOpensComap_spaBasicOpen_self, top_inf_eq,
    locOpensComap_laurentCoverOpen]

end Pullback

/-! ### Transport along Wedhorn's Remark 8.4 -/

section Transport

variable {A : Type v} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
  (P : PairOfDefinition A) (Aplus : Subring A) (T : Finset A) (s : A)
  (S : Type v) [CommRing S] [Algebra A S] [IsLocalization.Away s S]
  (hden : HasDenominatorPower P T s S) (hAplus : ∀ ⦃a⦄, a ∈ Aplus → IsPowerBounded a)
  (hT : IsOpen (Ideal.span (T : Set A) : Set A))

include hAplus hT

-- `presentationLimitMap_comp_presentationLimitLocIso_hom` evaluated at a section, restated with
-- `.hom.1` so that `rw` and `simp` match the `.hom.1` terms below.
private theorem presentationLimitLocIso_hom_presentationLimitMap_apply {V V' : Opens ↥(spa Aplus)}
    (hV : V ∈ spaRationalOpens Aplus) (hV' : V' ∈ spaRationalOpens Aplus)
    (hVW : V ≤ spaBasicOpen Aplus T s) (h : V' ≤ V) (x : presentationLimit (P := P) Aplus V) :
    letI := locUniformSpace P T s S hden
    letI := isUniformAddGroup_locUniformSpace P T s S hden
    letI := isTopologicalRing_locUniformSpace P T s S hden
    (presentationLimitLocIso P Aplus T s S hden hAplus hT V' hV' (h.trans hVW)).hom.hom.1
        ((presentationLimitMap (P := P) h).hom.1 x) =
      (presentationLimitMap (P := completionLocalization P T s S hden)
        (locOpensComap_mono P Aplus T s S hden h)).hom.1
          ((presentationLimitLocIso P Aplus T s S hden hAplus hT V hV hVW).hom.hom.1 x) :=
  ConcreteCategory.congr_hom (presentationLimitMap_comp_presentationLimitLocIso_hom P Aplus T s S
    hden hAplus hT hV hV' hVW h) x

-- `presentationLimitLocIso` is a bijection on sections, stated for `.hom.hom.1`.
private theorem bijective_presentationLimitLocIso_hom {V : Opens ↥(spa Aplus)}
    (hV : V ∈ spaRationalOpens Aplus) (hVW : V ≤ spaBasicOpen Aplus T s) :
    letI := locUniformSpace P T s S hden
    letI := isUniformAddGroup_locUniformSpace P T s S hden
    letI := isTopologicalRing_locUniformSpace P T s S hden
    Function.Bijective (presentationLimitLocIso P Aplus T s S hden hAplus hT V hV hVW).hom.hom.1 :=
  ⟨Function.LeftInverse.injective
      (presentationLimitLocIso P Aplus T s S hden hAplus hT V hV hVW).hom_inv_id_apply,
    Function.RightInverse.surjective
      (presentationLimitLocIso P Aplus T s S hden hAplus hT V hV hVW).inv_hom_id_apply⟩

/-- **Injectivity transported along rational localization.** Restriction from `R(T/s)` to rational
opens `U i ⊆ R(T/s)` is injective as soon as restriction from the pullback of `R(T/s)` to the
pullbacks of the `U i` is injective. -/
theorem injective_presentationLimitMap_of_locOpensComap {ι : Type*}
    {U : ι → Opens ↥(spa Aplus)} (hU : ∀ i, U i ∈ spaRationalOpens Aplus)
    (hUW : ∀ i, U i ≤ spaBasicOpen Aplus T s) :
    letI := locUniformSpace P T s S hden
    letI := isUniformAddGroup_locUniformSpace P T s S hden
    letI := isTopologicalRing_locUniformSpace P T s S hden
    ∀ {W' : Opens ↥(spa (completedPlusSubring P Aplus T s S hden))}
      {U' : ι → Opens ↥(spa (completedPlusSubring P Aplus T s S hden))},
      locOpensComap P Aplus T s S hden (spaBasicOpen Aplus T s) = W' →
      (∀ i, locOpensComap P Aplus T s S hden (U i) = U' i) → ∀ hU'W' : ∀ i, U' i ≤ W',
      (Function.Injective fun (y : presentationLimit (P := completionLocalization P T s S hden)
          (completedPlusSubring P Aplus T s S hden) W') i ↦
        (presentationLimitMap (P := completionLocalization P T s S hden) (hU'W' i)).hom.1 y) →
      Function.Injective fun (x : presentationLimit (P := P) Aplus (spaBasicOpen Aplus T s)) i ↦
        (presentationLimitMap (P := P) (hUW i)).hom.1 x := by
  intro W' U' hW' hU' _ h x y hxy
  subst hW'
  obtain rfl : U' = fun i ↦ locOpensComap P Aplus T s S hden (U i) := funext fun i ↦ (hU' i).symm
  have hW := spaBasicOpen_mem_spaRationalOpens (Aplus := Aplus) (s := s) hT
  -- apply Remark 8.4 over `R(T/s)` and over each `U i`, which commutes with restriction
  refine (bijective_presentationLimitLocIso_hom P Aplus T s S hden hAplus hT hW le_rfl).1 <|
    h <| funext fun i ↦ ?_
  simp only [← presentationLimitLocIso_hom_presentationLimitMap_apply P Aplus T s S hden hAplus hT
    hW (hU i) le_rfl (hUW i)]
  exact congrArg _ (congrFun hxy i)

/-- **Gluing transported along rational localization.** Sections over two rational opens
`U b ⊆ R(T/s)` that agree on their overlap glue over `R(T/s)` as soon as the analogous gluing
statement holds for the pullbacks of `R(T/s)`, the `U b`, and their overlap. -/
theorem exists_presentationLimitMap_eq_of_locOpensComap {U : Bool → Opens ↥(spa Aplus)}
    (hU : ∀ b, U b ∈ spaRationalOpens Aplus) (hUW : ∀ b, U b ≤ spaBasicOpen Aplus T s) :
    letI := locUniformSpace P T s S hden
    letI := isUniformAddGroup_locUniformSpace P T s S hden
    letI := isTopologicalRing_locUniformSpace P T s S hden
    ∀ {W' O' : Opens ↥(spa (completedPlusSubring P Aplus T s S hden))}
      {U' : Bool → Opens ↥(spa (completedPlusSubring P Aplus T s S hden))},
      locOpensComap P Aplus T s S hden (spaBasicOpen Aplus T s) = W' →
      (∀ b, locOpensComap P Aplus T s S hden (U b) = U' b) →
      locOpensComap P Aplus T s S hden (U true ⊓ U false) = O' →
      ∀ (hU'W' : ∀ b, U' b ≤ W') (h₁ : O' ≤ U' true) (h₂ : O' ≤ U' false),
      (∀ y : ∀ b, presentationLimit (P := completionLocalization P T s S hden)
          (completedPlusSubring P Aplus T s S hden) (U' b),
        (presentationLimitMap (P := completionLocalization P T s S hden) h₁).hom.1 (y true) =
          (presentationLimitMap (P := completionLocalization P T s S hden) h₂).hom.1 (y false) →
        ∃ c : presentationLimit (P := completionLocalization P T s S hden)
            (completedPlusSubring P Aplus T s S hden) W', ∀ b,
          (presentationLimitMap (P := completionLocalization P T s S hden) (hU'W' b)).hom.1 c =
            y b) →
      ∀ x : ∀ b, presentationLimit (P := P) Aplus (U b),
        (presentationLimitMap (P := P) (inf_le_left : U true ⊓ U false ≤ _)).hom.1 (x true) =
          (presentationLimitMap (P := P) (inf_le_right : U true ⊓ U false ≤ _)).hom.1 (x false) →
        ∃ a : presentationLimit (P := P) Aplus (spaBasicOpen Aplus T s), ∀ b,
          (presentationLimitMap (P := P) (hUW b)).hom.1 a = x b := by
  intro W' O' U' hW' hU' hO' _ _ _ h x hx
  subst hW' hO'
  obtain rfl : U' = fun b ↦ locOpensComap P Aplus T s S hden (U b) := funext fun b ↦ (hU' b).symm
  have _ : IsHuberRing A := ⟨⟨P⟩⟩
  have hW := spaBasicOpen_mem_spaRationalOpens (Aplus := Aplus) (s := s) hT
  have hO := inf_mem_spaRationalOpens (hU true) (hU false)
  have nat (b : Bool) := presentationLimitLocIso_hom_presentationLimitMap_apply P Aplus T s S hden
    hAplus hT (hU b) hO (hUW b)
  -- apply Remark 8.4 to `x`, glue over the pullbacks, and pull the gluing back to `R(T/s)`
  obtain ⟨c, hc⟩ := h (fun b ↦ (presentationLimitLocIso P Aplus T s S hden hAplus hT _ (hU b)
    (hUW b)).hom.hom.1 (x b)) <| by rw [← nat true inf_le_left, ← nat false inf_le_right, hx]
  obtain ⟨a, rfl⟩ := (bijective_presentationLimitLocIso_hom P Aplus T s S hden hAplus hT hW
    le_rfl).2 c
  refine ⟨a, fun b ↦ (bijective_presentationLimitLocIso_hom P Aplus T s S hden hAplus hT (hU b)
    (hUW b)).1 ?_⟩
  rw [presentationLimitLocIso_hom_presentationLimitMap_apply P Aplus T s S hden hAplus hT hW (hU b)
    le_rfl (hUW b), hc b]

-- The difference of restrictions from two rational opens `U b ⊆ R(T/s)` onto their overlap is
-- surjective as soon as the same holds for the pullbacks `U' b` and `O'` of the `U b` and of their
-- overlap.
private theorem surjective_presentationLimitMap_sub_of_locOpensComap
    {U : Bool → Opens ↥(spa Aplus)} (hU : ∀ b, U b ∈ spaRationalOpens Aplus)
    (hUW : ∀ b, U b ≤ spaBasicOpen Aplus T s) :
    letI := locUniformSpace P T s S hden
    letI := isUniformAddGroup_locUniformSpace P T s S hden
    letI := isTopologicalRing_locUniformSpace P T s S hden
    ∀ {O' : Opens ↥(spa (completedPlusSubring P Aplus T s S hden))}
      {U' : Bool → Opens ↥(spa (completedPlusSubring P Aplus T s S hden))},
      (∀ b, locOpensComap P Aplus T s S hden (U b) = U' b) →
      locOpensComap P Aplus T s S hden (U true ⊓ U false) = O' →
      ∀ (h₁ : O' ≤ U' true) (h₂ : O' ≤ U' false),
      (Function.Surjective fun (y : presentationLimit (P := completionLocalization P T s S hden)
            (completedPlusSubring P Aplus T s S hden) (U' true) ×
          presentationLimit (P := completionLocalization P T s S hden)
            (completedPlusSubring P Aplus T s S hden) (U' false)) ↦
        (presentationLimitMap (P := completionLocalization P T s S hden) h₁).hom.1 y.1 -
          (presentationLimitMap (P := completionLocalization P T s S hden) h₂).hom.1 y.2) →
      Function.Surjective fun (x : presentationLimit (P := P) Aplus (U true) ×
          presentationLimit (P := P) Aplus (U false)) ↦
        (presentationLimitMap (P := P) (inf_le_left : U true ⊓ U false ≤ _)).hom.1 x.1 -
          (presentationLimitMap (P := P) (inf_le_right : U true ⊓ U false ≤ _)).hom.1 x.2 := by
  intro O' U' hU' hO' _ _ h z
  subst hO'
  obtain rfl : U' = fun b ↦ locOpensComap P Aplus T s S hden (U b) := funext fun b ↦ (hU' b).symm
  have _ : IsHuberRing A := ⟨⟨P⟩⟩
  have hO := inf_mem_spaRationalOpens (hU true) (hU false)
  have σ (b : Bool) := bijective_presentationLimitLocIso_hom P Aplus T s S hden hAplus hT (hU b)
    (hUW b)
  -- apply Remark 8.4 to `z`, write its image as a difference over the pullbacks, and pull the two
  -- sections back to the `U b`
  obtain ⟨⟨y₁, y₂⟩, hy⟩ := h ((presentationLimitLocIso P Aplus T s S hden hAplus hT _ hO
    (inf_le_left.trans (hUW true))).hom.hom.1 z)
  obtain ⟨x₁, rfl⟩ := (σ true).2 y₁
  obtain ⟨x₂, rfl⟩ := (σ false).2 y₂
  refine ⟨(x₁, x₂), (bijective_presentationLimitLocIso_hom P Aplus T s S hden hAplus hT hO
    (inf_le_left.trans (hUW true))).1 ?_⟩
  rw [map_sub, presentationLimitLocIso_hom_presentationLimitMap_apply P Aplus T s S hden hAplus hT
    (hU true) hO (hUW true) inf_le_left, presentationLimitLocIso_hom_presentationLimitMap_apply P
    Aplus T s S hden hAplus hT (hU false) hO (hUW false) inf_le_right]
  exact hy

end Transport

/-! ### Lemma 8.33 on a rational subset -/

section Rational

variable {A : Type v} [CommRing A] [UniformSpace A] [IsTopologicalRing A] [IsTateRing A]
  [IsStronglyNoetherian A] (P : PairOfDefinition A) {Aplus : Subring A}

/-- **Wedhorn's Lemma 8.33 on a rational subset, injectivity.** Let `A` be a strongly noetherian
Tate ring, `A⁺` a subring of power-bounded elements, `R(T/s)` a rational subset of `Spa(A, A⁺)` and
`f ∈ A`. A section of `presentationLimit` over `R(T/s)` is determined by its restrictions to the
two pieces `R(T/s) ⊓ laurentCoverOpen Aplus f b` of the Laurent cover of `f` restricted to
`R(T/s)`. For the Laurent cover of the whole adic spectrum of a complete Hausdorff `A`, see
`injective_presentationLimitMap_laurentCoverOpen`. -/
theorem injective_presentationLimitMap_inf_laurentCoverOpen
    (hAplus : ∀ ⦃a⦄, a ∈ Aplus → IsPowerBounded a) {T : Finset A} {s : A}
    (hT : IsOpen (Ideal.span (T : Set A) : Set A)) (f : A) :
    Function.Injective fun (x : presentationLimit (P := P) Aplus (spaBasicOpen Aplus T s))
        (b : Bool) ↦
      (presentationLimitMap (P := P)
        (inf_le_left : spaBasicOpen Aplus T s ⊓ laurentCoverOpen Aplus f b ≤ _)).hom.1 x := by
  -- `A⟨T/s⟩` is again a strongly noetherian Tate ring, with plus ring of power-bounded elements
  have hden := hasDenominatorPower_of_isOpen_span P T s (Localization.Away s) hT
  let _ := locUniformSpace P T s _ hden
  have _ := isUniformAddGroup_locUniformSpace P T s _ hden
  have _ := isTopologicalRing_locUniformSpace P T s _ hden
  have _ := isTateRing_completion_locTopology_of_isTateRing P T s _ hden
  have _ := isStronglyNoetherian_completion P T s _ hden
    (eq_top_mono (Ideal.span_mono (Set.subset_insert _ _)) (IsTateRing.eq_top_of_isOpen hT))
  -- transport Lemma 8.33 for `A⟨T/s⟩` along Remark 8.4
  exact injective_presentationLimitMap_of_locOpensComap P Aplus T s _ hden hAplus hT
    (fun b ↦ inf_mem_spaRationalOpens (spaBasicOpen_mem_spaRationalOpens hT)
      (laurentCoverOpen_mem_spaRationalOpens Aplus f b)) (fun _ ↦ inf_le_left)
    (locOpensComap_spaBasicOpen_self P Aplus T s _ hden)
    (locOpensComap_inf_laurentCoverOpen P Aplus T s _ hden f) (fun _ ↦ le_top)
    (injective_presentationLimitMap_laurentCoverOpen _
      (isPowerBounded_of_mem_completedPlusSubring P Aplus hAplus T s _ hden) _)

/-- **Wedhorn's Lemma 8.33 on a rational subset, gluing.** Let `A` be a strongly noetherian Tate
ring, `A⁺` a subring of power-bounded elements, `R(T/s)` a rational subset of `Spa(A, A⁺)` and
`f ∈ A`. Sections `x b` of `presentationLimit` over the two pieces
`R(T/s) ⊓ laurentCoverOpen Aplus f b` that agree on their overlap are the restrictions of one
section over `R(T/s)`, which is unique by `injective_presentationLimitMap_inf_laurentCoverOpen`.
For the Laurent cover of the whole adic spectrum of a complete Hausdorff `A`, see
`exists_presentationLimitMap_eq_of_laurentCoverOpen`. -/
theorem exists_presentationLimitMap_eq_of_inf_laurentCoverOpen
    (hAplus : ∀ ⦃a⦄, a ∈ Aplus → IsPowerBounded a) {T : Finset A} {s : A}
    (hT : IsOpen (Ideal.span (T : Set A) : Set A)) (f : A)
    (x : ∀ b, presentationLimit (P := P) Aplus
      (spaBasicOpen Aplus T s ⊓ laurentCoverOpen Aplus f b))
    (hx : (presentationLimitMap (P := P) (inf_le_left :
        (spaBasicOpen Aplus T s ⊓ laurentCoverOpen Aplus f true) ⊓
          (spaBasicOpen Aplus T s ⊓ laurentCoverOpen Aplus f false) ≤ _)).hom.1 (x true) =
      (presentationLimitMap (P := P) (inf_le_right :
        (spaBasicOpen Aplus T s ⊓ laurentCoverOpen Aplus f true) ⊓
          (spaBasicOpen Aplus T s ⊓ laurentCoverOpen Aplus f false) ≤ _)).hom.1 (x false)) :
    ∃ a : presentationLimit (P := P) Aplus (spaBasicOpen Aplus T s), ∀ b,
      (presentationLimitMap (P := P)
        (inf_le_left : spaBasicOpen Aplus T s ⊓ laurentCoverOpen Aplus f b ≤ _)).hom.1 a = x b := by
  -- `A⟨T/s⟩` is again a strongly noetherian Tate ring, with plus ring of power-bounded elements
  have hden := hasDenominatorPower_of_isOpen_span P T s (Localization.Away s) hT
  let _ := locUniformSpace P T s _ hden
  have _ := isUniformAddGroup_locUniformSpace P T s _ hden
  have _ := isTopologicalRing_locUniformSpace P T s _ hden
  have _ := isTateRing_completion_locTopology_of_isTateRing P T s _ hden
  have _ := isStronglyNoetherian_completion P T s _ hden
    (eq_top_mono (Ideal.span_mono (Set.subset_insert _ _)) (IsTateRing.eq_top_of_isOpen hT))
  have hU := locOpensComap_inf_laurentCoverOpen P Aplus T s _ hden f
  have hO : locOpensComap P Aplus T s _ hden ((spaBasicOpen Aplus T s ⊓
      laurentCoverOpen Aplus f true) ⊓ (spaBasicOpen Aplus T s ⊓ laurentCoverOpen Aplus f false)) =
      laurentCoverOpen _ (toCompletionLoc P T s _ hden f) true ⊓
        laurentCoverOpen _ (toCompletionLoc P T s _ hden f) false := by
    rw [locOpensComap_inf, hU, hU]
  -- transport Lemma 8.33 for `A⟨T/s⟩` along Remark 8.4
  exact exists_presentationLimitMap_eq_of_locOpensComap P Aplus T s _ hden hAplus hT
    (fun b ↦ inf_mem_spaRationalOpens (spaBasicOpen_mem_spaRationalOpens hT)
      (laurentCoverOpen_mem_spaRationalOpens Aplus f b)) (fun _ ↦ inf_le_left)
    (locOpensComap_spaBasicOpen_self P Aplus T s _ hden) hU hO (fun _ ↦ le_top) inf_le_left
    inf_le_right (exists_presentationLimitMap_eq_of_laurentCoverOpen _
      (isPowerBounded_of_mem_completedPlusSubring P Aplus hAplus T s _ hden) _) x hx

/-- **Wedhorn's Lemma 8.33 on a rational subset, degree-one surjectivity.** Let `A` be a strongly
noetherian Tate ring, `A⁺` a subring of power-bounded elements, `R(T/s)` a rational subset of
`Spa(A, A⁺)` and `f ∈ A`. Every section of `presentationLimit` over the overlap of the two pieces
`R(T/s) ⊓ laurentCoverOpen Aplus f b` is the difference of the restrictions of sections over the
pieces. Together with `injective_presentationLimitMap_inf_laurentCoverOpen` and
`exists_presentationLimitMap_eq_of_inf_laurentCoverOpen`, this is exactness of the augmented Čech
complex of the Laurent cover of `f` restricted to `R(T/s)`. For the Laurent cover of the whole adic
spectrum of a complete Hausdorff `A`, see `surjective_presentationLimitMap_sub_laurentCoverOpen`. -/
theorem surjective_presentationLimitMap_sub_inf_laurentCoverOpen
    (hAplus : ∀ ⦃a⦄, a ∈ Aplus → IsPowerBounded a) {T : Finset A} {s : A}
    (hT : IsOpen (Ideal.span (T : Set A) : Set A)) (f : A) :
    Function.Surjective fun (x : presentationLimit (P := P) Aplus
          (spaBasicOpen Aplus T s ⊓ laurentCoverOpen Aplus f true) ×
        presentationLimit (P := P) Aplus
          (spaBasicOpen Aplus T s ⊓ laurentCoverOpen Aplus f false)) ↦
      (presentationLimitMap (P := P) (inf_le_left :
        (spaBasicOpen Aplus T s ⊓ laurentCoverOpen Aplus f true) ⊓
          (spaBasicOpen Aplus T s ⊓ laurentCoverOpen Aplus f false) ≤ _)).hom.1 x.1 -
      (presentationLimitMap (P := P) (inf_le_right :
        (spaBasicOpen Aplus T s ⊓ laurentCoverOpen Aplus f true) ⊓
          (spaBasicOpen Aplus T s ⊓ laurentCoverOpen Aplus f false) ≤ _)).hom.1 x.2 := by
  -- `A⟨T/s⟩` is again a strongly noetherian Tate ring, with plus ring of power-bounded elements
  have hden := hasDenominatorPower_of_isOpen_span P T s (Localization.Away s) hT
  let _ := locUniformSpace P T s _ hden
  have _ := isUniformAddGroup_locUniformSpace P T s _ hden
  have _ := isTopologicalRing_locUniformSpace P T s _ hden
  have _ := isTateRing_completion_locTopology_of_isTateRing P T s _ hden
  have _ := isStronglyNoetherian_completion P T s _ hden
    (eq_top_mono (Ideal.span_mono (Set.subset_insert _ _)) (IsTateRing.eq_top_of_isOpen hT))
  have hU := locOpensComap_inf_laurentCoverOpen P Aplus T s _ hden f
  have hO : locOpensComap P Aplus T s _ hden ((spaBasicOpen Aplus T s ⊓
      laurentCoverOpen Aplus f true) ⊓ (spaBasicOpen Aplus T s ⊓ laurentCoverOpen Aplus f false)) =
      laurentCoverOpen _ (toCompletionLoc P T s _ hden f) true ⊓
        laurentCoverOpen _ (toCompletionLoc P T s _ hden f) false := by
    rw [locOpensComap_inf, hU, hU]
  -- transport Lemma 8.33 for `A⟨T/s⟩` along Remark 8.4
  exact surjective_presentationLimitMap_sub_of_locOpensComap P Aplus T s _ hden hAplus hT
    (fun b ↦ inf_mem_spaRationalOpens (spaBasicOpen_mem_spaRationalOpens hT)
      (laurentCoverOpen_mem_spaRationalOpens Aplus f b)) (fun _ ↦ inf_le_left) hU hO inf_le_left
    inf_le_right (surjective_presentationLimitMap_sub_laurentCoverOpen _
      (isPowerBounded_of_mem_completedPlusSubring P Aplus hAplus T s _ hden) _)

end Rational

end TauCeti.ValuationSpectrum
