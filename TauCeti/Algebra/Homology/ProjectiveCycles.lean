/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Abelian.Projective.Dimension
public import TauCeti.Algebra.Homology.HomotopyCofiber
public import TauCeti.Algebra.Homology.Split

/-!
# Projective cycles and contractible complexes

This file collects the facts about cycles of complexes in an abelian category that are needed to
show that complexes of projectives are homotopically projective in finite global dimension. The
complexes may have any shape, possibly unbounded in both directions or cyclic.

* The cycles of a contractible complex are retracts of its terms; so they are projective when
  the terms are. (A contractible complex is acyclic, `Homotopy.acyclic`.)
* Conversely, an acyclic complex whose cycles are projective is contractible: for a relation
  `i → j`, the short exact sequence `0 ⟶ Zᵢ ⟶ Kᵢ ⟶ Zⱼ ⟶ 0` splits, and the complex is homotopy
  equivalent to its homology, which vanishes.
* A short exact sequence `0 ⟶ X₁ ⟶ X₂ ⟶ X₃ ⟶ 0` of complexes with `X₃` exact at a degree `j`
  which is the target of a relation induces a short exact sequence of cycles in degree `j`. When
  the cycles of `X₂` in degree `j` are projective, those of `X₁` are syzygies of those of `X₃`,
  and their projective dimension drops by one.
* With enough projectives, and when every index is both the source and the target of a relation
  of the shape, every complex receives a degreewise epimorphism from a contractible complex with
  projective terms, the mapping cone of the identity of a complex with zero differential made of
  projective presentations of the terms.

Iterating the last two points replaces an acyclic complex by acyclic complexes whose cycles have
smaller and smaller projective dimension, until the cycles are projective.

## Main results

* `Homotopy.projective_cycles`: the cycles of a contractible complex of projectives are projective.
* `HomologicalComplex.Acyclic.nonempty_homotopy_id_zero_of_projective_cycles`: an acyclic complex
  whose cycles are projective is contractible.
* `CategoryTheory.ShortComplex.ShortExact.hasProjectiveDimensionLT_cycles_X₁`: dimension shifting
  for the cycles of a short exact sequence of complexes.
* `HomologicalComplex.exists_projective_contractible_epi_f`: when every index is both the source
  and the target of a relation, every complex is the target of a degreewise epimorphism from a
  contractible complex with projective terms.

## References

* C. Weibel, *An Introduction to Homological Algebra*, Sections 1.4 (split complexes) and 4.1
  (dimension shifting).
-/

public section

open CategoryTheory Limits

variable {C : Type*} [Category* C] [Abelian C] {ι : Type*} {c : ComplexShape ι}

namespace Homotopy

variable {K : HomologicalComplex C c} (h : Homotopy (𝟙 K) 0)
include h

/-- In a contractible complex, the cycles in degree `j` are a retract of the term in degree `i`
for every relation `i → j`; in particular they are projective when that term is. -/
lemma projective_cycles {i j : ι} (hij : c.Rel i j) [Projective (K.X i)] :
    Projective (K.cycles j) :=
  Retract.projective (Y := K.X i) ⟨K.iCycles j ≫ h.hom j i, K.toCycles i j, by
    have H := h.comm j
    rw [prevD_eq _ hij] at H
    rw [← cancel_mono (K.iCycles j)]
    simpa [dNext] using congr(K.iCycles j ≫ $H).symm⟩

end Homotopy

namespace HomologicalComplex.Acyclic

variable {K : HomologicalComplex C c} (hK : K.Acyclic)
include hK

/-- In an acyclic complex, the cycles `Zᵢ` split off the term `Kᵢ` once the cycles of the next
degree are projective. -/
lemma isSplitMono_iCycles (i : ι) [Projective (K.cycles (c.next i))] :
    IsSplitMono (K.iCycles i) := by
  by_cases hi : c.Rel i (c.next i)
  · have := (hK (c.next i)).isIso_kernel_ι_homologyπ
    have : Projective (kernel (K.homologyπ (c.next i))) :=
      Projective.of_iso (asIso (kernel.ι (K.homologyπ (c.next i)))).symm inferInstance
    exact K.isSplitMono_iCycles_of_projective_kernel_homologyπ hi
  · have := K.isIso_iCycles i (c.next i) rfl (K.shape _ _ hi)
    exact .mk' ⟨inv (K.iCycles i), IsIso.hom_inv_id _⟩

/-- An acyclic complex whose cycles are projective is contractible. -/
theorem nonempty_homotopy_id_zero_of_projective_cycles (hZ : ∀ i, Projective (K.cycles i)) :
    Nonempty (Homotopy (𝟙 K) 0) := by
  have (i : ι) : IsSplitMono (K.iCycles i) := hK.isSplitMono_iCycles i
  have (i : ι) : IsSplitEpi (K.homologyπ i) :=
    ⟨⟨0, (hK i).isZero_homology.eq_of_src _ _⟩⟩
  obtain ⟨L, hL, ⟨e⟩⟩ := K.exists_homotopyEquiv_d_eq_zero
  -- The terms of `L` are its homology objects, which vanish because `K` is acyclic.
  have hLX (i : ι) : IsZero (L.X i) :=
    ((hK i).isZero_homology.of_iso (e.toHomologyIso i).symm).of_iso
      ((L.iCyclesIso i (c.next i) rfl (hL _ _)).symm ≪≫ L.isoHomologyπ (c.prev i) i rfl (hL _ _))
  refine ⟨e.homotopyHomInvId.symm.trans (Homotopy.ofEq ?_)⟩
  ext i
  simp [(hLX i).eq_zero_of_tgt (e.hom.f i)]

end HomologicalComplex.Acyclic

/-- Let `0 ⟶ X₁ ⟶ X₂ ⟶ X₃ ⟶ 0` be a short exact sequence of complexes and `i → j` a relation of
the shape, where `X₃` is exact at `j` and the cycles of `X₂` in degree `j` are projective. It gives
a short exact sequence `0 ⟶ Z(X₁) ⟶ Z(X₂) ⟶ Z(X₃) ⟶ 0` of cycles in degree `j`, so the cycles of
`X₁` have projective dimension `< m + 1` when those of `X₃` have projective dimension `< m + 2`. -/
lemma CategoryTheory.ShortComplex.ShortExact.hasProjectiveDimensionLT_cycles_X₁
    {S : ShortComplex (HomologicalComplex C c)} (hS : S.ShortExact) {i j : ι} (hij : c.Rel i j)
    (h₃ : S.X₃.ExactAt j) (h₂ : Projective (S.X₂.cycles j)) (m : ℕ)
    (hZ : HasProjectiveDimensionLT (S.X₃.cycles j) (m + 2)) :
    HasProjectiveDimensionLT (S.X₁.cycles j) (m + 1) := by
  have := hS.mono_f
  have : Epi (S.g.f i) :=
    ((HomologicalComplex.shortExact_iff_degreewise_shortExact S).mp hS i).epi_g
  have := HomologicalComplex.epi_cyclesMap_of_exactAt S.g hij h₃
  have hT : (ShortComplex.mk _ _ (by rw [← HomologicalComplex.cyclesMap_comp, S.zero,
      HomologicalComplex.cyclesMap_zero] : HomologicalComplex.cyclesMap S.f j ≫
        HomologicalComplex.cyclesMap S.g j = 0)).ShortExact :=
    { exact := HomologicalComplex.cycles_left_exact S hS.exact j }
  exact hT.hasProjectiveDimensionLT_X₁ (m + 1)
    (hasProjectiveDimensionLT_of_ge _ 1 (m + 1) (by lia)) hZ

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
