/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Limits.Shapes.Products
public import Mathlib.CategoryTheory.Limits.Shapes.ZeroMorphisms
public import Mathlib.Algebra.Homology.ShortComplex.Exact
public import Mathlib.Algebra.Group.End
public import Mathlib.Algebra.Order.Interval.Finset.SuccPred
public import Mathlib.Data.Int.Interval
public import Mathlib.Data.Int.SuccPred

/-!
# Split maps between coproducts, and cokernels of maps between coproducts

## Reindexing a coproduct along an injection is split

Let `X : I → C` be a family of objects of a category with zero morphisms and coproducts, and let
`f : J → I` be injective.  Reindexing along `f` gives a map `∐ (X ∘ f) ⟶ ∐ X`, and this file
shows that it is a split monomorphism: the retraction sends the summand indexed by `f j` back to
the one indexed by `j`, and kills the summands indexed outside the range of `f`.

Mathlib's `CategoryTheory.Limits.MonoCoprod.mono_map'_of_injective` proves the same map is a
monomorphism in a category satisfying `MonoCoprod`; the splitting below needs zero morphisms
instead, and is the stronger statement in the situations where both apply.

Chain complexes built as coproducts over a set of simplices, singular or simplicial, get their
degreewise splittings this way: for a pair of spaces the singular simplices of the subspace form a
subset of those of the ambient space, so the short exact sequence of chains of the pair is split in
each degree, and therefore stays exact after applying a contravariant `Hom(-, M)`.

## The kernel of the codiagonal

Let `R` be an object of a preadditive category with a zero object, and let `ι` be a type with a
distinguished element `i₀`.  The codiagonal `Sigma.desc (fun _ ↦ 𝟙 R) : ∐ (fun _ : ι ↦ R) ⟶ R`,
the identity on every summand, is a split epimorphism with section the inclusion of the summand
`i₀`, and its kernel is the coproduct of the summands indexed by `i ≠ i₀`, embedded through the
differences `ι_i - ι_{i₀}` of coproduct inclusions (`TauCeti.sigmaιSubι`).  The short complex
`∐_{i ≠ i₀} R ⟶ ∐_ι R ⟶ R` is split (`TauCeti.sigmaDescIdSplitting`), which identifies the kernel
of the codiagonal with `∐_{i ≠ i₀} R` (`TauCeti.kernelSigmaDescIdIso`).

Reduced homology in degree zero is the kernel of an augmentation of this form, so this identifies
it with a coproduct indexed by the path components other than that of a chosen basepoint.

## Cokernels commute with coproducts

In a category with zero morphisms, let `f i : X i ⟶ Y i` be a family of morphisms with cokernels
`c i`, and let `g : ∐ X ⟶ ∐ Y` be the morphism between coproducts induced by the `f i`.  A cokernel
of `g` is then a coproduct of the cokernels `c i`, with legs induced by the coproduct inclusions
(`TauCeti.isColimitCofanMkCokernelCofork`).  The relative chains of a pair are the cokernel of the
map from the chains of the subspace to those of the ambient space, so this is how additivity
passes from absolute to relative chains.

## `𝟙 - τ` on a coproduct over a free `ℤ`-set is split

Let `e` be a permutation of a type `S`, and suppose some height `h : S → ℤ` satisfies
`h (e s) = h s + 1`, so that `e` generates a free action of `ℤ` on `S`.  On a coproduct
`⨁_S R` of copies of one object of a preadditive category, let `t` send the summand of `s` to the
summand of `e s`.  Then `𝟙 - t` is a split monomorphism (`TauCeti.isSplitMono_id_sub`).  The
retraction `TauCeti.shiftRetraction` telescopes along each orbit, from height `0` to the summand
at hand.  This is why the chains of an infinite cyclic cover inject into themselves under
`𝟙 - τ_*`, for the deck transformation `τ`.
-/

public section

open CategoryTheory Limits

universe w

namespace TauCeti

section Reindex

variable {C : Type*} [Category* C] [HasZeroMorphisms C] [HasCoproducts.{w} C]

open scoped Classical in
/-- Reindexing a coproduct along an injective map of index types is a split monomorphism. -/
instance isSplitMono_sigmaMap' {I J : Type w} (X : I → C) (f : J ⟶ I) [Mono f] :
    IsSplitMono (Sigma.map' f fun j ↦ 𝟙 ((X ∘ f) j)) :=
  IsSplitMono.mk'
    { retraction := Sigma.desc fun i ↦
        if h : i ∈ Set.range f then
          eqToHom (congrArg X h.choose_spec).symm ≫ Sigma.ι (X ∘ f) h.choose
        else 0
      id := by
        refine Sigma.hom_ext _ _ fun j ↦ ?_
        have h : f j ∈ Set.range f := ⟨j, rfl⟩
        have hj : h.choose = j := (mono_iff_injective f).1 ‹_› h.choose_spec
        rw [← Category.assoc, Sigma.ι_comp_map', Category.id_comp, Sigma.ι_comp_desc,
          dite_eq_left h, Category.comp_id]
        exact Sigma.eqToHom_comp_ι (X ∘ f) hj }

end Reindex

noncomputable section Codiagonal

variable {C : Type*} [Category* C] [Preadditive C] [HasCoproducts.{w} C] (R : C) {ι : Type w}
  (i₀ : ι)

/-- The morphism `∐_{i ≠ i₀} R ⟶ ∐_ι R` whose component at `i` is the difference `ι_i - ι_{i₀}`
of coproduct inclusions.  It is a kernel of the codiagonal `∐_ι R ⟶ R`
(`TauCeti.isKernelSigmaιSubι`). -/
def sigmaιSubι : (∐ fun _ : {i // i ≠ i₀} ↦ R) ⟶ ∐ fun _ : ι ↦ R :=
  Sigma.desc fun i ↦ Sigma.ι (fun _ : ι ↦ R) i.1 - Sigma.ι (fun _ : ι ↦ R) i₀

@[reassoc (attr := simp)]
lemma ι_sigmaιSubι (i : {i // i ≠ i₀}) :
    Sigma.ι (fun _ : {i // i ≠ i₀} ↦ R) i ≫ sigmaιSubι R i₀ =
      Sigma.ι (fun _ : ι ↦ R) i.1 - Sigma.ι (fun _ : ι ↦ R) i₀ :=
  Sigma.ι_comp_desc _ _

/-- The differences of coproduct inclusions are killed by the codiagonal. -/
@[reassoc (attr := simp)]
lemma sigmaιSubι_desc_id : sigmaιSubι R i₀ ≫ Sigma.desc (fun _ ↦ 𝟙 R) = 0 := by
  ext i
  simp [Preadditive.sub_comp]

open scoped Classical in
/-- The retraction of `TauCeti.sigmaιSubι`: the identity on the summands indexed by `i ≠ i₀` and
zero on the summand indexed by `i₀`. -/
def sigmaιSubιRetraction : (∐ fun _ : ι ↦ R) ⟶ ∐ fun _ : {i // i ≠ i₀} ↦ R :=
  Sigma.desc fun i ↦ if h : i = i₀ then 0 else Sigma.ι (fun _ : {i // i ≠ i₀} ↦ R) ⟨i, h⟩

@[reassoc (attr := simp)]
lemma ι_sigmaιSubιRetraction_of_ne {i : ι} (h : i ≠ i₀) :
    Sigma.ι (fun _ : ι ↦ R) i ≫ sigmaιSubιRetraction R i₀ =
      Sigma.ι (fun _ : {i // i ≠ i₀} ↦ R) ⟨i, h⟩ := by
  simp [sigmaιSubιRetraction, h]

@[reassoc (attr := simp)]
lemma ι_sigmaιSubιRetraction_self :
    Sigma.ι (fun _ : ι ↦ R) i₀ ≫ sigmaιSubιRetraction R i₀ = 0 := by
  simp [sigmaιSubιRetraction]

/-- The short complex `∐_{i ≠ i₀} R ⟶ ∐_ι R ⟶ R` formed by the differences of coproduct
inclusions and the codiagonal. -/
abbrev sigmaDescIdShortComplex : ShortComplex C :=
  ShortComplex.mk (sigmaιSubι R i₀) (Sigma.desc fun _ ↦ 𝟙 R) (sigmaιSubι_desc_id R i₀)

/-- The short complex `∐_{i ≠ i₀} R ⟶ ∐_ι R ⟶ R` is split: the inclusion of the summand `i₀`
sections the codiagonal, and `TauCeti.sigmaιSubιRetraction` retracts the differences. -/
def sigmaDescIdSplitting : (sigmaDescIdShortComplex R i₀).Splitting where
  r := sigmaιSubιRetraction R i₀
  s := Sigma.ι (fun _ : ι ↦ R) i₀
  f_r := by
    ext ⟨i, hi⟩
    simp [Preadditive.sub_comp, hi]
  s_g := by simp
  id := by
    ext i
    by_cases h : i = i₀
    · subst h
      simp
    · simp [Preadditive.comp_add, h]

variable [HasZeroObject C]

/-- The differences of coproduct inclusions form a kernel of the codiagonal. -/
def isKernelSigmaιSubι :
    IsLimit (KernelFork.ofι (sigmaιSubι R i₀) (sigmaιSubι_desc_id R i₀)) :=
  (sigmaDescIdSplitting R i₀).fIsKernel

/-- The kernel of the codiagonal `∐_ι R ⟶ R` is the coproduct of the copies of `R` indexed by
`i ≠ i₀`. -/
def kernelSigmaDescIdIso [HasKernel (Sigma.desc fun _ : ι ↦ 𝟙 R)] :
    kernel (Sigma.desc fun _ : ι ↦ 𝟙 R) ≅ ∐ fun _ : {i // i ≠ i₀} ↦ R :=
  IsLimit.conePointUniqueUpToIso (kernelIsKernel _) (isKernelSigmaιSubι R i₀)

@[reassoc (attr := simp)]
lemma kernelSigmaDescIdIso_inv_ι [HasKernel (Sigma.desc fun _ : ι ↦ 𝟙 R)] :
    (kernelSigmaDescIdIso R i₀).inv ≫ kernel.ι (Sigma.desc fun _ : ι ↦ 𝟙 R) =
      sigmaιSubι R i₀ :=
  IsLimit.conePointUniqueUpToIso_inv_comp _ _ WalkingParallelPair.zero

end Codiagonal

section Cokernel

variable {C : Type*} [Category* C] [HasZeroMorphisms C] {ι : Type*} {X Y : ι → C}
  {f : ∀ i, X i ⟶ Y i} {c : ∀ i, CokernelCofork (f i)} (hc : ∀ i, IsColimit (c i))
  {cX : Cofan X} (hX : IsColimit cX) {cY : Cofan Y} (hY : IsColimit cY) {g : cX.pt ⟶ cY.pt}
  (hg : ∀ i, cX.inj i ≫ g = f i ≫ cY.inj i) {c' : CokernelCofork g} (hc' : IsColimit c')
  (φ : ∀ i, (c i).pt ⟶ c'.pt) (hφ : ∀ i, (c i).π ≫ φ i = cY.inj i ≫ c'.π)

include hX hg in
private lemma comp_cofanDesc_eq_zero (s : Cofan fun i ↦ (c i).pt) :
    g ≫ Cofan.IsColimit.desc hY (fun i ↦ (c i).π ≫ s.inj i) = 0 :=
  Cofan.IsColimit.hom_ext hX _ _ fun i ↦ by
    rw [reassoc_of% (hg i), Cofan.IsColimit.fac, CokernelCofork.condition_assoc, zero_comp,
      comp_zero]

include hX hg hφ in
/-- **Cokernels commute with coproducts.**  Let `f i : X i ⟶ Y i` be a family of morphisms with
cokernels `c i`, and let `g : ∐ X ⟶ ∐ Y` be the morphism between coproducts induced by the `f i`.
Then a cokernel `c'` of `g` is the coproduct of the cokernels `c i`, with legs the maps
`φ i : (c i).pt ⟶ c'.pt` induced by the coproduct inclusions `Y i ⟶ ∐ Y`. -/
def isColimitCofanMkCokernelCofork : IsColimit (Cofan.mk c'.pt φ) :=
  Cofan.IsColimit.mk _
    (fun s ↦ hc'.desc (CokernelCofork.ofπ _ (comp_cofanDesc_eq_zero hX hY hg s)))
    (fun s i ↦ Cofork.IsColimit.hom_ext (hc i) <| by
      rw [cofan_mk_inj, reassoc_of% (hφ i), Cofork.IsColimit.π_desc, Cofork.π_ofπ,
        Cofan.IsColimit.fac])
    (fun s m hm ↦ Cofork.IsColimit.hom_ext hc' <| Cofan.IsColimit.hom_ext hY _ _ fun i ↦ by
      rw [Cofork.IsColimit.π_desc, Cofork.π_ofπ, Cofan.IsColimit.fac, ← reassoc_of% (hφ i), ← hm,
        cofan_mk_inj])

end Cokernel

noncomputable section Shift

variable {C : Type*} [Category* C] [Preadditive C] {S : Type*} {R : C}
  {c : Cofan fun _ : S ↦ R} (hc : IsColimit c) (e : Equiv.Perm S) (h : S → ℤ)

/-- The telescoping retraction of `𝟙 - e_*` on a coproduct `⨁_S R`, for a permutation `e` of `S`
raising a height `h : S → ℤ` by one.  On the summand of `s`, at height `m = h s`, it is
`∑_{m ≤ k < 0} ι_{e^(k - m) s} - ∑_{0 ≤ k < m} ι_{e^(k - m) s}`: for `m < 0` the sum of the summands
at heights `m, …, -1` of the `e`-orbit of `s`, and for `m ≥ 0` minus the sum of those at heights
`0, …, m - 1` (see `TauCeti.id_sub_comp_shiftRetraction`). -/
def shiftRetraction : c.pt ⟶ c.pt :=
  Cofan.IsColimit.desc hc fun s ↦
    ∑ k ∈ Finset.Ico (h s) 0, c.inj ((e ^ (k - h s)) s) -
      ∑ k ∈ Finset.Ico 0 (h s), c.inj ((e ^ (k - h s)) s)

/-- The telescoping retraction on the summand of `s`. -/
@[reassoc (attr := simp)]
lemma inj_shiftRetraction (s : S) :
    c.inj s ≫ shiftRetraction hc e h =
      ∑ k ∈ Finset.Ico (h s) 0, c.inj ((e ^ (k - h s)) s) -
        ∑ k ∈ Finset.Ico 0 (h s), c.inj ((e ^ (k - h s)) s) :=
  Cofan.IsColimit.fac hc _ s

variable {e h}

/-- The telescoping retraction is a left inverse of `𝟙 - t`, where `t` moves the summand of `s` to
the summand of `e s`, as soon as `e` raises the height `h` by one. -/
@[reassoc]
theorem id_sub_comp_shiftRetraction (hh : ∀ s, h (e s) = h s + 1) {t : c.pt ⟶ c.pt}
    (ht : ∀ s, c.inj s ≫ t = c.inj (e s)) :
    (𝟙 c.pt - t) ≫ shiftRetraction hc e h = 𝟙 c.pt := by
  refine Cofan.IsColimit.hom_ext hc _ _ fun s ↦ ?_
  -- Both summands are indexed by the orbit of `s`, through `k ↦ e ^ (k - h s) s`.
  have he : ∀ k : ℤ, (e ^ (k - (h s + 1))) (e s) = (e ^ (k - h s)) s := fun k ↦ by
    rw [← Equiv.Perm.mul_apply, ← zpow_add_one]
    congr 2
    omega
  rw [Preadditive.sub_comp, Preadditive.comp_sub, Category.id_comp, reassoc_of% ht,
    inj_shiftRetraction, inj_shiftRetraction, Category.comp_id]
  simp only [hh, he]
  -- The two sums for `e s` differ from those for `s` only in the term `k = h s`, which is `s`.
  rcases lt_or_ge (h s) 0 with hs | hs
  · rw [Finset.Ico_eq_empty_of_le hs.le, Finset.Ico_eq_empty_of_le (by omega : 0 ≥ h s + 1),
      ← Finset.insert_Ico_add_one_left_eq_Ico hs, Finset.sum_insert (by simp)]
    simp
  · rw [Finset.Ico_eq_empty_of_le hs, Finset.Ico_eq_empty_of_le (by omega : h s + 1 ≥ 0),
      ← Finset.insert_Ico_right_eq_Ico_add_one hs, Finset.sum_insert (by simp)]
    simp

include hc in
/-- On a coproduct `⨁_S R`, the endomorphism `𝟙 - t`, where `t` moves the summand of `s` to the
summand of `e s`, is a split monomorphism as soon as some height `h : S → ℤ` is raised by one
by `e`.  Such a height exists exactly when `e` generates a free action of `ℤ` on `S`. -/
theorem isSplitMono_id_sub (hh : ∀ s, h (e s) = h s + 1) {t : c.pt ⟶ c.pt}
    (ht : ∀ s, c.inj s ≫ t = c.inj (e s)) :
    IsSplitMono (𝟙 c.pt - t) :=
  IsSplitMono.mk' ⟨shiftRetraction hc e h, id_sub_comp_shiftRetraction hc hh ht⟩

end Shift

end TauCeti
