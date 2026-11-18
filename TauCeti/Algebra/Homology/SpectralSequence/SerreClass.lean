/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Homology.SpectralSequence.Basic
public import TauCeti.Algebra.Homology.ShortComplex.SerreClass

/-!
# Spectral sequences modulo a Serre class

Let `P` be a Serre class in an abelian category `C`: a class of objects containing zero and
closed under subobjects, quotients and extensions, for instance the torsion abelian groups or the
abelian groups killed by some power of a fixed integer. Serre's theory of classes of abelian
groups computes in spectral sequences modulo `P`. This file proves the three facts about the
pages of a spectral sequence on which those computations rest.

* **Survival.** Each page is the homology of the previous one, so its objects are subquotients
  of those of every earlier page. Hence an object which lies in `P` on some page lies in `P` on
  every later page (`CategoryTheory.SpectralSequence.prop_page_X_of_le`). For the Serre class of
  zero objects this is `CategoryTheory.SpectralSequence.isZero_page_X_of_le`.
* **Recovery from a later page.** Conversely, suppose that every object joined to the position
  `pq` by a differential of one of the pages `r ≤ s < r'` lies in `P` on the page `r`. Then the
  object at `pq` lies in `P` on the page `r` exactly when it does on the page `r'`
  (`CategoryTheory.SpectralSequence.prop_page_X_iff_of_forall`): on each page in between the
  object is an extension of its homology by objects of `P`. For instance, in a first-quadrant
  homological spectral sequence whose objects off the bottom row of the page `r ≥ 2` lie in `P`,
  an object of the bottom row lies in `P` on the page `r` as soon as it does on some later page,
  for instance once it has stabilized to a vanishing limit term. This is the argument by which
  the second part of Proposition 5.11 of Barraud–Damian–Humilière–Oancea shows, through the
  path-loop fibration `Ω²Q → P Ω₀Q → Ω₀Q`, that the positive-degree homology of `Ω₀Q` is
  torsion of a bounded power of `d` when the positive homology of `Ω²Q` is.
* **Comparison.** A morphism of spectral sequences which is an isomorphism modulo `P` on every
  object of the page `r` is an isomorphism modulo `P` on every object of every later page
  (`CategoryTheory.SpectralSequence.Hom.isoModSerre_hom_f_of_le`), by the five lemma modulo a
  Serre class (`CategoryTheory.ObjectProperty.isoModSerre_homologyMap`). This is the comparison
  theorem modulo `P`; for `P` the class of zero objects, isomorphisms modulo `P` are the
  isomorphisms and it recovers `CategoryTheory.SpectralSequence.Hom.isIso_hom_f_of_le`.

## Main results

* `CategoryTheory.SpectralSequence.prop_page_X_of_le`: an object in `P` stays in `P` on later
  pages; this only uses closure under subobjects and quotients.
* `CategoryTheory.SpectralSequence.prop_page_X_of_prop_page_X_add_one`: an object whose
  neighbours on the page `s` lie in `P` lies in `P` if it does on the page `s + 1`.
* `CategoryTheory.SpectralSequence.prop_page_X_iff_of_forall`: an object whose neighbours lie in
  `P` on the page `r` lies in `P` on the page `r` exactly when it does on a later page.
* `CategoryTheory.SpectralSequence.Hom.isoModSerre_hom_f_of_le`: the comparison theorem modulo a
  Serre class.

## References

* J.-P. Serre, *Groupes d'homotopie et classes de groupes abéliens*, Ann. of Math. 58 (1953),
  258–294.
* J.-F. Barraud, M. Damian, V. Humilière, A. Oancea, *Floer homology with DG coefficients.
  Applications to cotangent bundles*, arXiv:2404.07953, Theorem 5.12 and Proposition 5.11.
-/

public section

namespace CategoryTheory.SpectralSequence

open Limits

variable {C κ : Type*} [Category* C] [Abelian C] {c : ℤ → ComplexShape κ} {r₀ : ℤ}
  (E : SpectralSequence C c r₀) (P : ObjectProperty C)

/-- **Objects in a Serre class stay in it.** If the object at `pq` lies in a class `P` closed
under subobjects and quotients, for instance a Serre class, on the page `r`, it lies in `P` on
every later page `r' ≥ r`, since each page is the homology of the previous one. -/
lemma prop_page_X_of_le [P.IsClosedUnderSubobjects] [P.IsClosedUnderQuotients] {r : ℤ}
    (hr : r₀ ≤ r) {pq : κ} (h : P ((E.page r).X pq)) (r' : ℤ) (hrr' : r ≤ r') :
    P ((E.page r' (hr.trans hrr')).X pq) := by
  induction r', hrr' using Int.leInduction with
  | base => exact h
  | succ r' hrr' ih =>
    exact P.prop_of_iso (E.iso r' (r' + 1) pq rfl (hr.trans hrr'))
      (P.prop_homology_of_prop_X₂ (S := (E.page r' (hr.trans hrr')).sc pq) ih)

variable [P.IsSerreClass]

/-- **One page back.** If every object joined to the position `pq` by a differential of the page
`s` lies in a Serre class `P`, then the object at `pq` on the page `s` lies in `P` as soon as it
does on the page `s + 1`: it is an extension of its homology by objects of `P`. -/
lemma prop_page_X_of_prop_page_X_add_one {s : ℤ} (hs : r₀ ≤ s) {pq : κ}
    (h : ∀ pq', (c s).Rel pq pq' ∨ (c s).Rel pq' pq → P ((E.page s).X pq'))
    (h' : P ((E.page (s + 1)).X pq)) : P ((E.page s).X pq) := by
  refine P.prop_X₂_of_prop_homology (S := (E.page s).sc pq) ?_ ?_
    (P.prop_of_iso (E.iso s (s + 1) pq rfl hs).symm h')
  · by_cases hrel : (c s).Rel ((c s).prev pq) pq
    · exact Or.inr (h _ (Or.inr hrel))
    · exact Or.inl ((E.page s).shape _ _ hrel)
  · by_cases hrel : (c s).Rel pq ((c s).next pq)
    · exact Or.inr (h _ (Or.inl hrel))
    · exact Or.inl ((E.page s).shape _ _ hrel)

/-- **Objects with neighbours in a Serre class.** Suppose that on the page `r` every object
joined to the position `pq` by a differential of one of the pages `s` with `r ≤ s < r'` lies in a
Serre class `P`. Then the object at `pq` lies in `P` on the page `r'` exactly when it does on the
page `r`. -/
lemma prop_page_X_iff_of_forall {r : ℤ} (hr : r₀ ≤ r) {pq : κ} (r' : ℤ) (hrr' : r ≤ r')
    (h : ∀ s, r ≤ s → s < r' → ∀ pq', (c s).Rel pq pq' ∨ (c s).Rel pq' pq →
      P ((E.page r).X pq')) :
    P ((E.page r' (hr.trans hrr')).X pq) ↔ P ((E.page r).X pq) := by
  refine ⟨fun h' ↦ ?_, fun h' ↦ E.prop_page_X_of_le P hr h' r' hrr'⟩
  induction r', hrr' using Int.leInduction with
  | base => exact h'
  | succ r' hrr' ih =>
    refine ih (fun s hrs hs ↦ h s hrs (hs.trans (Int.lt_add_one_iff.2 le_rfl))) ?_
    -- The neighbours of `pq` on the page `r'` lie in `P`, since they do on the page `r`.
    exact E.prop_page_X_of_prop_page_X_add_one P (hr.trans hrr')
      (fun pq' hpq' ↦ E.prop_page_X_of_le P hr
        (h r' hrr' (Int.lt_add_one_iff.2 le_rfl) pq' hpq') r' hrr') h'

namespace Hom

variable {E} {E' : SpectralSequence C c r₀} (f : E ⟶ E')

/-- **The comparison theorem modulo a Serre class.** A morphism of spectral sequences which is an
isomorphism modulo a Serre class `P` on every object of the page `r` is an isomorphism modulo `P`
on every object of every page `r' ≥ r`. -/
lemma isoModSerre_hom_f_of_le (r : ℤ) (hr : r₀ ≤ r)
    (h : ∀ pq, P.isoModSerre ((f.hom r hr).f pq)) (r' : ℤ) (hrr' : r ≤ r') (pq : κ) :
    P.isoModSerre ((f.hom r' (hr.trans hrr')).f pq) := by
  induction r', hrr' using Int.leInduction generalizing pq with
  | base => exact h pq
  | succ r' hrr' ih =>
    -- The component on the page `r' + 1` is the map induced on homology by the page `r'`,
    -- up to the identifications of both spectral sequences.
    have hcomm : (f.hom (r' + 1) (hr.trans (hrr'.trans (Int.le_add_one le_rfl)))).f pq =
        (E.iso r' (r' + 1) pq rfl (hr.trans hrr')).inv ≫
          HomologicalComplex.homologyMap (f.hom r' (hr.trans hrr')) pq ≫
            (E'.iso r' (r' + 1) pq rfl (hr.trans hrr')).hom := by
      rw [f.comm r' (r' + 1) pq rfl (hr.trans hrr'), Iso.inv_hom_id_assoc]
    rw [hcomm]
    refine P.isoModSerre.comp_mem _ _ (P.isoModSerre_of_isIso _)
      (P.isoModSerre.comp_mem _ _ ?_ (P.isoModSerre_of_isIso _))
    exact P.isoModSerre_homologyMap _ (ih _) (ih _) (ih _)

end Hom

end CategoryTheory.SpectralSequence
