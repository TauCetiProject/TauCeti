/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.SimplicialSet.AnodyneExtensions.WeakHomotopyEquivalence
public import TauCeti.AlgebraicTopology.SimplicialSet.Factorization
import Mathlib.CategoryTheory.MorphismProperty.RetractArgument

/-!
# Kan fibrations which are weak homotopy equivalences

Let `p : X ⟶ Y` be a Kan fibration whose source `X` is a Kan complex. We prove that `p` is a
trivial fibration, that is, has the right lifting property with respect to all monomorphisms,
exactly when it is a simplicial homotopy equivalence
(`SSet.rlp_monomorphisms_iff_exists_homotopy_inverse`). Given a homotopy inverse `g`, lifting
the homotopy from `g ≫ p` to `𝟙 Y` along `p` deforms `g` into a section `s` of `p`, and `p ≫ s`
is still homotopic to `𝟙 X`. Such a section extends to a shrinking of `p`
(`SSet.Shrinking.ofHomotopy`), and a shrinkable Kan fibration is a trivial fibration.

When `Y` is a Kan complex, the simplicial homotopy equivalences between Kan complexes are the weak
homotopy equivalences of `SSet.IsWeakHomotopyEquivalence`, so a Kan fibration with target a Kan
complex is a trivial fibration exactly when it is a weak homotopy equivalence
(`SSet.rlp_monomorphisms_iff_isWeakHomotopyEquivalence`).

By the retract argument, a monomorphism `i : A ⟶ B` into a Kan complex is then anodyne exactly
when it is a weak homotopy equivalence (`SSet.anodyneExtensions_iff_isWeakHomotopyEquivalence`):
factor `i` as an anodyne extension `j : A ⟶ Z` followed by a Kan fibration `q : Z ⟶ B`. Then `Z`
is a Kan complex and `q` is a weak homotopy equivalence by two out of three, hence a trivial
fibration, and `i` is a retract of `j`. The anodyne extensions are the trivial cofibrations of
the Kan–Quillen model structure, and this identifies them among the monomorphisms into Kan
complexes with the maps which are weak homotopy equivalences.

## Main declarations

* `SSet.rlp_monomorphisms_of_homotopy_inverse`: a Kan fibration with source a Kan complex which
  is a simplicial homotopy equivalence is a trivial fibration.
* `SSet.rlp_monomorphisms_iff_exists_homotopy_inverse`: the corresponding characterization.
* `SSet.isWeakHomotopyEquivalence_of_rlp_monomorphisms`: a trivial fibration is a weak homotopy
  equivalence.
* `SSet.rlp_monomorphisms_iff_isWeakHomotopyEquivalence`: a Kan fibration with target a Kan
  complex is a trivial fibration exactly when it is a weak homotopy equivalence.
* `SSet.anodyneExtensions_iff_isWeakHomotopyEquivalence`: a monomorphism into a Kan complex is
  anodyne exactly when it is a weak homotopy equivalence.

## References

* J. Lurie, *Kerodon*, Proposition 3.2.7.2 (Tag 00X1).
* A. Dold, *Partitions of unity in the theory of fibrations*, Ann. of Math. 78 (1963).
-/

public section

universe u

open CategoryTheory MonoidalCategory CartesianMonoidalCategory Limits MorphismProperty
  HomotopicalAlgebra

open scoped Simplicial

namespace SSet

open modelCategoryQuillen

variable {X Y : SSet.{u}}

/-- A Kan fibration whose source is a Kan complex and which is a simplicial homotopy equivalence
has the right lifting property with respect to all monomorphisms: it is a trivial fibration. -/
theorem rlp_monomorphisms_of_homotopy_inverse (p : X ⟶ Y) [Fibration p] [KanComplex X]
    (g : Y ⟶ X) (H₁ : Homotopy (p ≫ g) (𝟙 X)) (H₂ : Homotopy (g ≫ p) (𝟙 Y)) :
    (monomorphisms SSet.{u}).rlp p := by
  -- Lift `H₂` along `p`, starting at `g`: its other end is a section `s` of `p`, homotopic to `g`.
  have := (anodyneExtensions.horn_ι (n := 1) 0).whiskerLeft Y p (mem_fibrations p)
  have sq : CommSq (fst Y _ ≫ g) (Y ◁ Λ[1, 0].ι) p H₂.h :=
    ⟨by rw [whiskerLeft_horn_one_zero_ι]; simp only [Category.assoc]; rw [H₂.h₀]⟩
  let s : Y ⟶ X := ι₁ ≫ sq.lift
  have hs : s ≫ p = 𝟙 Y := by rw [Category.assoc, sq.fac_right, H₂.h₁]
  -- The end `ι₀` of the cylinder factors through `Y ⊗ Λ[1, 0]`, by way of its vertex.
  have e : horn.ι 0 1 (by decide) ≫ Λ[1, 0].ι = stdSimplex.{u}.δ 1 := horn.ι_ι _ _ _
  have L : Homotopy g s := .mk' sq.lift (by
    rw [← fstStdSimplexZeroIso_inv_whiskerLeft_stdSimplex_δ_one_assoc, ← e,
      MonoidalCategory.whiskerLeft_comp_assoc, sq.fac_left]
    simp) rfl
  -- Since `X` is a Kan complex, `p ≫ s` is homotopic to `p ≫ g`, hence to `𝟙 X`.
  obtain ⟨K⟩ := (L.precomp p).nonempty_symm
  obtain ⟨K⟩ := K.nonempty_trans H₁
  exact (Shrinking.ofHomotopy s hs K).rlp_monomorphisms

/-- A Kan fibration whose source is a Kan complex has the right lifting property with respect to
all monomorphisms (it is a trivial fibration) exactly when it is a simplicial homotopy
equivalence. -/
theorem rlp_monomorphisms_iff_exists_homotopy_inverse (p : X ⟶ Y) [Fibration p] [KanComplex X] :
    (monomorphisms SSet.{u}).rlp p ↔
      ∃ g : Y ⟶ X, Nonempty (Homotopy (p ≫ g) (𝟙 X)) ∧ Nonempty (Homotopy (g ≫ p) (𝟙 Y)) := by
  exact ⟨exists_homotopy_inverse_of_rlp_monomorphisms,
    fun ⟨g, ⟨H₁⟩, ⟨H₂⟩⟩ ↦ rlp_monomorphisms_of_homotopy_inverse p g H₁ H₂⟩

/-- A morphism with the right lifting property with respect to all monomorphisms (a trivial
fibration) is a weak homotopy equivalence: a section of it, together with a homotopy from the
composite of the morphism and the section to the identity, is a homotopy inverse. -/
theorem isWeakHomotopyEquivalence_of_rlp_monomorphisms {p : X ⟶ Y}
    (hp : (monomorphisms SSet.{u}).rlp p) : IsWeakHomotopyEquivalence p := by
  obtain ⟨g, ⟨H₁⟩, ⟨H₂⟩⟩ := exists_homotopy_inverse_of_rlp_monomorphisms hp
  exact .of_homotopy p H₁ H₂

/-- A Kan fibration whose target is a Kan complex has the right lifting property with respect to
all monomorphisms (it is a trivial fibration) exactly when it is a weak homotopy equivalence. -/
theorem rlp_monomorphisms_iff_isWeakHomotopyEquivalence (p : X ⟶ Y) [Fibration p]
    [KanComplex Y] : (monomorphisms SSet.{u}).rlp p ↔ IsWeakHomotopyEquivalence p := by
  have : KanComplex X := isFibrant_of_fibration p
  rw [rlp_monomorphisms_iff_exists_homotopy_inverse,
    isWeakHomotopyEquivalence_iff_exists_homotopy_inverse]

/-- A monomorphism into a Kan complex is an anodyne extension exactly when it is a weak homotopy
equivalence. -/
theorem anodyneExtensions_iff_isWeakHomotopyEquivalence {A B : SSet.{u}} (i : A ⟶ B) [Mono i]
    [KanComplex B] : anodyneExtensions i ↔ IsWeakHomotopyEquivalence i := by
  refine ⟨fun hi ↦ hi.isWeakHomotopyEquivalence, fun _ ↦ ?_⟩
  -- Factor `i` as an anodyne extension `j` followed by a Kan fibration `q`.
  let h := factorizationData anodyneExtensions (fibrations SSet.{u}) i
  have : Fibration h.p := (fibration_iff _).2 h.hp
  have : KanComplex h.Z := isFibrant_of_fibration h.p
  have := h.hi.isWeakHomotopyEquivalence
  have : IsWeakHomotopyEquivalence (h.i ≫ h.p) := by rwa [h.fac]
  have := IsWeakHomotopyEquivalence.of_precomp h.i h.p
  -- Then `q` is a trivial fibration, so `i` is a retract of `j`.
  have := (rlp_monomorphisms_iff_isWeakHomotopyEquivalence h.p).2 this i
    (monomorphisms.infer_property i)
  exact MorphismProperty.of_retract (P := (fibrations SSet.{u}).llp)
    (RetractArrow.ofLeftLiftingProperty h.fac) h.hi

end SSet
