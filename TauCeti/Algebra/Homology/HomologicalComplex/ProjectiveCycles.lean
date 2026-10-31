/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Abelian.Projective.Dimension
public import TauCeti.Algebra.Homology.HomotopyCofiber
public import TauCeti.Algebra.Homology.Boundaries

/-!
# Projective cycles and contractible complexes

This file collects the facts about cycles of complexes that are needed to show that complexes of
projectives are homotopically projective in finite global dimension. The complexes may have any
shape, possibly unbounded in both directions or cyclic.

* The cycles of a contractible complex are retracts of its terms; so they are projective when
  the terms are. This only needs a preadditive category. (A contractible complex is acyclic,
  `Homotopy.acyclic`; conversely, an acyclic complex whose cycles are projective is contractible,
  `HomologicalComplex.Acyclic.nonempty_homotopy_id_zero_of_projective_cycles` in
  `TauCeti.Algebra.Homology.Split`.)
* In an abelian category, a short exact sequence `0 ⟶ X₁ ⟶ X₂ ⟶ X₃ ⟶ 0` of complexes with `X₃`
  exact at a degree `j` which is the target of a relation induces a short exact sequence of cycles
  in degree `j`. When the cycles of `X₂` in degree `j` have projective dimension `< n`, those of
  `X₁` do as soon as those of `X₃` have projective dimension `< n + 1`. In particular, when the
  cycles of `X₂` are projective, those of `X₁` are syzygies of those of `X₃`, and their projective
  dimension drops by one.
* With enough projectives, and when every index is both the source and the target of a relation
  of the shape, every complex receives a degreewise epimorphism from a contractible complex with
  projective terms, the mapping cone of the identity of a complex with zero differential made of
  projective presentations of the terms.

Iterating the last two points replaces an acyclic complex by acyclic complexes whose cycles have
smaller and smaller projective dimension, until the cycles are projective.

## Main results

* `Homotopy.projective_cycles`: the cycles of a contractible complex of projectives are projective.
* `CategoryTheory.ShortComplex.ShortExact.hasProjectiveDimensionLT_cycles_X₁`: dimension shifting
  for the cycles of a short exact sequence of complexes.
* `HomologicalComplex.exists_projective_contractible_epi_f`: when every index is both the source
  and the target of a relation, every complex is the target of a degreewise epimorphism from a
  contractible complex with projective terms.

## References

* C. Weibel, *An Introduction to Homological Algebra*, Section 4.1 (dimension shifting).
-/

public section

open CategoryTheory Limits

variable {C : Type*} [Category* C] {ι : Type*} {c : ComplexShape ι}

namespace Homotopy

variable [Preadditive C] {K : HomologicalComplex C c} (h : Homotopy (𝟙 K) 0)
include h

/-- In a contractible complex, the cycles in degree `j` are a retract of the term in degree `i`
for every relation `i → j`; in particular they are projective when that term is. -/
lemma projective_cycles {i j : ι} (hij : c.Rel i j) [K.HasHomology j] [Projective (K.X i)] :
    Projective (K.cycles j) :=
  Retract.projective (Y := K.X i) ⟨K.iCycles j ≫ h.hom j i, K.toCycles i j, by
    have H := h.comm j
    rw [prevD_eq _ hij] at H
    rw [← cancel_mono (K.iCycles j)]
    simpa [dNext] using congr(K.iCycles j ≫ $H).symm⟩

end Homotopy

variable [Abelian C]

/-- Let `0 ⟶ X₁ ⟶ X₂ ⟶ X₃ ⟶ 0` be a short exact sequence of complexes and `i → j` a relation of
the shape, where `X₃` is exact at `j`. It gives a short exact sequence
`0 ⟶ Z(X₁) ⟶ Z(X₂) ⟶ Z(X₃) ⟶ 0` of cycles in degree `j`, so the cycles of `X₁` have projective
dimension `< n` when those of `X₂` have projective dimension `< n` and those of `X₃` have
projective dimension `< n + 1`. -/
lemma CategoryTheory.ShortComplex.ShortExact.hasProjectiveDimensionLT_cycles_X₁
    {S : ShortComplex (HomologicalComplex C c)} (hS : S.ShortExact) {i j : ι} (hij : c.Rel i j)
    (h₃ : S.X₃.ExactAt j) (n : ℕ) (h₂ : HasProjectiveDimensionLT (S.X₂.cycles j) n)
    (hZ : HasProjectiveDimensionLT (S.X₃.cycles j) (n + 1)) :
    HasProjectiveDimensionLT (S.X₁.cycles j) n := by
  have := hS.mono_f
  have : Epi (S.g.f i) :=
    ((HomologicalComplex.shortExact_iff_degreewise_shortExact S).mp hS i).epi_g
  have := HomologicalComplex.epi_cyclesMap_of_exactAt S.g hij h₃
  have hT : (ShortComplex.mk _ _ (by rw [← HomologicalComplex.cyclesMap_comp, S.zero,
      HomologicalComplex.cyclesMap_zero] : HomologicalComplex.cyclesMap S.f j ≫
        HomologicalComplex.cyclesMap S.g j = 0)).ShortExact :=
    { exact := HomologicalComplex.cycles_left_exact S hS.exact j }
  exact hT.hasProjectiveDimensionLT_X₁ n h₂ hZ

/-- In an abelian category with enough projectives, every complex is the target of a morphism
which is an epimorphism in every degree, from a contractible complex with projective terms. The
source is the mapping cone of the identity of a complex with zero differential, whose term in
degree `j` is a projective presentation of `Lᵢ` for the relation `i → j`. Every index must be
both the source and the target of a relation of the shape. -/
theorem HomologicalComplex.exists_projective_contractible_epi_f [EnoughProjectives C]
    (hc : ∀ i, ∃ j, c.Rel i j) (hc' : ∀ j, ∃ i, c.Rel i j) (L : HomologicalComplex C c) :
    ∃ (Q : HomologicalComplex C c) (π : Q ⟶ L), (∀ i, Projective (Q.X i)) ∧
      (∀ i, Epi (π.f i)) ∧ Nonempty (Homotopy (𝟙 Q) 0) := by
  classical
  let G : HomologicalComplex C c :=
    { X j := Projective.over (L.X (c.prev j))
      d _ _ := 0 }
  let h (j i : ι) (hij : c.Rel i j) : G.X j ⟶ L.X i :=
    Projective.π _ ≫ (L.XIsoOfEq (c.prev_eq' hij)).hom
  let hα : Homotopy (𝟙 G ≫ Homotopy.nullHomotopicMap' h) 0 :=
    (Homotopy.ofEq (Category.id_comp _)).trans (Homotopy.nullHomotopy' h)
  refine ⟨homotopyCofiber (𝟙 G), homotopyCofiber.desc _ _ hα, fun i ↦ ?_, fun i ↦ ?_,
    ⟨homotopyCofiber.homotopyToZeroOfId G hc'⟩⟩
  · obtain ⟨j, hij⟩ := hc i
    exact Projective.of_iso (homotopyCofiber.XIsoBiprod (𝟙 G) i j hij).symm inferInstance
  · obtain ⟨j, hij⟩ := hc i
    -- On the summand `G.X j`, the morphism is the projective presentation of `L.X i`.
    refine epi_of_epi_fac (f := homotopyCofiber.inlX (𝟙 G) j i hij) (h := h j i hij) ?_
    simp [hα, h, dite_eq_left hij]
