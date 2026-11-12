/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.HomologicalComplex.Projective.Cycles

/-!
# Projective replacements of complexes with terms of bounded projective dimension

In an abelian category with enough projectives, every complex whose terms have projective
dimension `< d` receives a quasi-isomorphism from a complex with projective terms
(`HomologicalComplex.exists_quasiIso_of_hasProjectiveDimensionLT`). The complexes may have any
shape in which every index is both the source and the target of a relation, so they may be
unbounded in both directions or cyclic; no bound on the complex itself is needed.

The replacement is built by induction on the bound on the projective dimension of the terms.
Cover `X` by a degreewise epimorphism `π : Q ⟶ X` from a complex `Q` with projective terms
(`HomologicalComplex.exists_projective_contractible_epi_f`). The terms of its kernel `N` are
syzygies of those of `X`, so by induction there is a quasi-isomorphism `q : P ⟶ N` from a complex
`P` of projectives. The mapping cone of `P ⟶ N ⟶ Q` again has projective terms, and maps to `X`
by a quasi-isomorphism: it factors through the mapping cone of `N ⟶ Q`, which computes the
cokernel `X` of `N ⟶ Q` (`CategoryTheory.ShortComplex.ShortExact.quasiIso_homotopyCofiberDesc`).

## Main results

* `HomologicalComplex.exists_quasiIso_of_hasProjectiveDimensionLT`: complexes with terms of
  bounded projective dimension have projective replacements.

## References

* T. Stai, *The triangulated hull of periodic complexes*, Mathematical Research Letters **25**
  (2018), 199–236, Section 3.
-/

public section

universe v u

namespace HomologicalComplex

open CategoryTheory CategoryTheory.Limits

variable {C : Type u} [Category.{v} C] [Abelian C] [EnoughProjectives C] {ι : Type*}
  {c : ComplexShape ι}

/-- The induction on the bound on the projective dimension of the terms. -/
private lemma exists_quasiIso_of_hasProjectiveDimensionLT_succ (hc : ∀ i, ∃ j, c.Rel i j)
    (hc' : ∀ j, ∃ i, c.Rel i j) (m : ℕ) :
    ∀ X : HomologicalComplex C c, (∀ i, HasProjectiveDimensionLT (X.X i) (m + 1)) →
      ∃ (P : HomologicalComplex C c) (_ : ∀ i, Projective (P.X i)) (π : P ⟶ X),
        QuasiIso π := by
  classical
  induction m with
  | zero =>
    intro X hX
    exact ⟨X, fun i ↦ projective_iff_hasProjectiveDimensionLT_one.mpr (hX i), 𝟙 X,
      inferInstance⟩
  | succ m ih =>
    intro X hX
    obtain ⟨Q, π, hQ, _, -⟩ := X.exists_projective_contractible_epi_f hc hc'
    have : Epi π := epi_of_epi_f π inferInstance
    -- The short exact sequence `0 ⟶ ker π ⟶ Q ⟶ X ⟶ 0`.
    have hS : (ShortComplex.mk (kernel.ι π) π (kernel.condition π)).ShortExact :=
      { exact := ShortComplex.exact_of_f_is_kernel _ (kernelIsKernel π) }
    have hN (i : ι) : HasProjectiveDimensionLT ((kernel π).X i) (m + 1) :=
      have := hQ i
      ((shortExact_iff_degreewise_shortExact _).1 hS i).hasProjectiveDimensionLT_X₁ (m + 1)
        (hasProjectiveDimensionLT_of_ge (Q.X i) 1 (m + 1) (by lia)) (hX i)
    obtain ⟨P, _, q, _⟩ := ih (kernel π) hN
    let α : Arrow.mk (q ≫ kernel.ι π) ⟶ Arrow.mk (kernel.ι π) := Arrow.homMk q (𝟙 Q) (by simp)
    have : QuasiIso α.left := by dsimp [α]; infer_instance
    have : QuasiIso α.right := by dsimp [α]; infer_instance
    have := homotopyCofiber.quasiIso_mapArrowHom _ _ hc' α
    have := hS.quasiIso_homotopyCofiberDesc hc'
    refine ⟨homotopyCofiber (q ≫ kernel.ι π), fun i ↦ ?_,
      homotopyCofiber.mapArrowHom _ _ hc' α ≫
        homotopyCofiber.desc (kernel.ι π) π (Homotopy.ofEq (kernel.condition π)), inferInstance⟩
    obtain ⟨j, hij⟩ := hc i
    exact Projective.of_iso (homotopyCofiber.XIsoBiprod (q ≫ kernel.ι π) i j hij).symm
      inferInstance

/-- In an abelian category with enough projectives, a complex whose terms all have projective
dimension `< d` receives a quasi-isomorphism from a complex with projective terms. Every index of
the shape must be both the source and the target of a relation. -/
theorem exists_quasiIso_of_hasProjectiveDimensionLT (hc : ∀ i, ∃ j, c.Rel i j)
    (hc' : ∀ j, ∃ i, c.Rel i j) (X : HomologicalComplex C c) (d : ℕ)
    (hd : ∀ i, HasProjectiveDimensionLT (X.X i) d) :
    ∃ (P : HomologicalComplex C c) (_ : ∀ i, Projective (P.X i)) (π : P ⟶ X), QuasiIso π :=
  exists_quasiIso_of_hasProjectiveDimensionLT_succ hc hc' d X
    fun i ↦ hasProjectiveDimensionLT_of_ge _ d (d + 1) (by lia)

end HomologicalComplex
