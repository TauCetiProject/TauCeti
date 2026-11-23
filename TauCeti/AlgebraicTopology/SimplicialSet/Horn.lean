/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicTopology.Quasicategory.InnerFibration
public import Mathlib.AlgebraicTopology.SimplicialSet.KanComplex
public import TauCeti.AlgebraicTopology.SimplicialSet.Op

/-!
# Lifting against horn inclusions

A map of simplicial sets `Λ[n + 1, i] ⟶ X` out of a horn is the same as a compatible family of
`n`-simplices of `X`, one for each face `j ≠ i` (`SSet.horn.IsCompatible`). Accordingly, a map
`p : X ⟶ Y` has the right lifting property with respect to the horn inclusion
`Λ[n + 1, i] ⟶ Δ[n + 1]` exactly when every compatible family of faces lying over the faces of
an `(n + 1)`-simplex of `Y` extends to an `(n + 1)`-simplex of `X` over it
(`SSet.hasLiftingProperty_horn_ι_iff`). This is the relative form of Mathlib's criterion
`SSet.KanComplex.iff` for Kan complexes, which also gives the horn-extension criterion
`SSet.kanComplex_of_hornFilling`. It reduces horn-lifting conditions to statements about
simplices and their faces, which is how such conditions are transported along constructions
that act on simplices, such as universe lifts.

Kan fibrations and inner fibrations are the maps with the right lifting property with respect
to all horn inclusions, respectively all inner horn inclusions
(`SSet.modelCategoryQuillen.rlp_J_iff`, `SSet.mem_innerFibrations_iff`). Through the horn-reversal
isomorphism `SSet.horn.opIso`, the opposite functor `SSet.opFunctor` exchanges lifting against
`Λ[n, i]` and `Λ[n, i.rev]` (`SSet.hasLiftingProperty_horn_ι_opFunctor_map_iff`), and therefore
preserves and reflects Kan fibrations, inner fibrations, Kan complexes and quasicategories.

The map `SSet.horn.IsCompatible.desc` induced by a compatible family `f` sends a simplex of the
face `j` to its image under `f j` (`SSet.horn.IsCompatible.desc_app_ι_app`), and when it extends
to a simplex `σ`, the faces of `σ` are the members of `f`
(`SSet.horn.IsCompatible.δ_yonedaEquiv_of_desc_eq`). An edge of a face of a horn is an edge of
the horn (`SSet.horn.ι_app_edge`).
-/

public section

open CategoryTheory Limits HomotopicalAlgebra Simplicial
open SSet.modelCategoryQuillen

universe u

namespace SSet

variable {X Y : SSet.{u}}

/-- The edge from `a` to `b` of the face `j` of a horn `Λ[n + 1, i]` is the edge of the horn
between the corresponding vertices `j.succAbove a` and `j.succAbove b`. -/
lemma horn.ι_app_edge {n : ℕ} (i j : Fin (n + 2)) (hj : j ≠ i) (a b : Fin (n + 1))
    (hab : a ≤ b) :
    (horn.ι.{u} i j hj).app _ (stdSimplex.edge n a b hab) =
      horn.edge (n + 1) i (j.succAbove a) (j.succAbove b)
        (Fin.strictMono_succAbove j |>.monotone hab)
        ((Finset.card_le_card (t := Finset.univ.erase j) (by
          simp [Finset.insert_subset_iff, hj.symm, Fin.succAbove_ne])).trans (by simp)) := by
  refine injective_of_mono (Subcomplex.ι.{u} Λ[n + 1, i] |>.app _) ?_
  rw [← NatTrans.comp_app_apply, horn.ι_ι]
  refine stdSimplex.ext _ _ fun k ↦ ?_
  fin_cases k <;> rfl

namespace horn.IsCompatible

variable {n : ℕ} {i : Fin (n + 2)} {f : ∀ (j : Fin (n + 2)) (_ : j ≠ i), Δ[n] ⟶ X}

/-- The map out of a horn induced by a compatible family `f` sends a simplex `x` of the face `j`
to its image under `f j`. -/
lemma desc_app_ι_app (hf : horn.IsCompatible f) (j : Fin (n + 2)) (hj : j ≠ i)
    {d : SimplexCategoryᵒᵖ} (x : Δ[n].obj d) :
    hf.desc.app _ ((horn.ι i j hj).app _ x) = (f j hj).app _ x := by
  rw [← NatTrans.comp_app_apply, hf.ι_desc]

/-- If the map out of a horn induced by a compatible family `f` extends along
`Λ[n + 1, i] ⟶ Δ[n + 1]` to a simplex `σ`, then the faces of `σ` are the members of `f`. -/
lemma δ_yonedaEquiv_of_desc_eq (hf : horn.IsCompatible f) {σ : Δ[n + 1] ⟶ X}
    (hσ : hf.desc = Λ[n + 1, i].ι ≫ σ) (j : Fin (n + 2)) (hj : j ≠ i) :
    X.δ j (yonedaEquiv σ) = yonedaEquiv (f j hj) := by
  rw [← stdSimplex.yonedaEquiv_δ_comp, ← horn.ι_ι_assoc i j hj, ← hσ, hf.ι_desc]

end horn.IsCompatible

/-- A map `p` has the right lifting property with respect to the horn inclusion
`Λ[n + 1, i] ⟶ Δ[n + 1]` exactly when every compatible family of faces in the source of `p`,
lying over the faces of an `(n + 1)`-simplex `b` of the target, extends to an
`(n + 1)`-simplex over `b`. -/
theorem hasLiftingProperty_horn_ι_iff (p : X ⟶ Y) {n : ℕ} (i : Fin (n + 2)) :
    HasLiftingProperty Λ[n + 1, i].ι p ↔
      ∀ (f : ∀ (j : Fin (n + 2)) (_ : j ≠ i), Δ[n] ⟶ X) (_ : horn.IsCompatible f)
        (b : Δ[n + 1] ⟶ Y) (_ : ∀ (j : Fin (n + 2)) (hj : j ≠ i),
          f j hj ≫ p = stdSimplex.δ j ≫ b),
        ∃ φ : Δ[n + 1] ⟶ X,
          (∀ (j : Fin (n + 2)) (hj : j ≠ i), stdSimplex.δ j ≫ φ = f j hj) ∧ φ ≫ p = b := by
  refine ⟨fun _ f hf b comm ↦ ?_, fun h ↦ ⟨fun {t b} sq ↦ ?_⟩⟩
  · have sq : CommSq hf.desc Λ[n + 1, i].ι p b :=
      ⟨horn.hom_ext' fun j hj ↦ by simpa using comm j hj⟩
    exact ⟨sq.lift, fun j hj ↦ by simp [← horn.ι_ι_assoc i j hj], by simp⟩
  · obtain ⟨φ, hφ, hφp⟩ := h _ (horn.IsCompatible.of_hom t) b fun j hj ↦ by
      rw [Category.assoc, sq.w, ← horn.ι_ι_assoc i j hj]
    exact ⟨⟨{ l := φ
              fac_left := horn.hom_ext' fun j hj ↦ by rw [horn.ι_ι_assoc, hφ]
              fac_right := hφp }⟩⟩

/-- A map is a Kan fibration exactly when it has the right lifting property with respect to every
horn inclusion. -/
theorem modelCategoryQuillen.rlp_J_iff (p : X ⟶ Y) :
    J.rlp p ↔ ∀ (n : ℕ) (i : Fin (n + 2)), HasLiftingProperty Λ[n + 1, i].ι p := by
  refine ⟨fun h n i ↦ h _ ?_, fun h _ _ _ hj ↦ ?_⟩
  · simp only [J, MorphismProperty.iSup_iff]
    exact ⟨n, ⟨i⟩⟩
  · simp only [J, MorphismProperty.iSup_iff] at hj
    obtain ⟨n, ⟨i⟩⟩ := hj
    exact h n i

/-- A map is an inner fibration exactly when it has the right lifting property with respect to
every inner horn inclusion. -/
theorem mem_innerFibrations_iff (p : X ⟶ Y) :
    innerFibrations p ↔ ∀ (n : ℕ) (i : Fin (n + 3)), 0 < i → i < Fin.last (n + 2) →
      HasLiftingProperty Λ[n + 2, i].ι p := by
  refine ⟨fun h n i h0 hn ↦ h _ ⟨i, h0, hn⟩, ?_⟩
  rintro h _ _ _ ⟨i, h0, hn⟩
  exact h _ i h0 hn

/-- A simplicial set in which every horn `Λ[n + 1, i] ⟶ Z` extends to `Δ[n + 1] ⟶ Z` is a Kan
complex. -/
theorem kanComplex_of_hornFilling (Z : SSet.{u})
    (h : ∀ ⦃n : ℕ⦄ ⦃i : Fin (n + 2)⦄ (σ₀ : (Λ[n + 1, i] : SSet.{u}) ⟶ Z),
      ∃ σ : Δ[n + 1] ⟶ Z, σ₀ = Λ[n + 1, i].ι ≫ σ) : KanComplex Z := by
  rw [KanComplex.iff]
  intro n i f hf
  obtain ⟨σ, hσ⟩ := h hf.desc
  exact ⟨σ, fun j hj ↦ by rw [← horn.ι_ι_assoc i j hj, ← hσ, hf.ι_desc]⟩

/-- A simplicial set is a Kan complex if and only if every horn `Λ[n + 1, i] ⟶ Z` extends to
`Δ[n + 1] ⟶ Z`. -/
theorem kanComplex_iff_hornFilling (Z : SSet.{u}) :
    KanComplex Z ↔ ∀ ⦃n : ℕ⦄ ⦃i : Fin (n + 2)⦄ (σ₀ : (Λ[n + 1, i] : SSet.{u}) ⟶ Z),
      ∃ σ : Δ[n + 1] ⟶ Z, σ₀ = Λ[n + 1, i].ι ≫ σ :=
  ⟨fun _ _ _ σ₀ ↦ KanComplex.hornFilling σ₀, kanComplex_of_hornFilling Z⟩

/-- The monoidal unit `𝟙_ SSet` is terminal, hence a Kan complex. -/
instance : KanComplex (MonoidalCategory.tensorUnit SSet.{u}) :=
  (isFibrant_iff_of_isTerminal (𝟙 _) CartesianMonoidalCategory.isTerminalTensorUnit).2 inferInstance

/-- Every map out of a `1`-horn `Λ[1, i]` extends to a degenerate `1`-simplex. -/
lemma horn.exists_extension_one (i : Fin 2) (σ₀ : (Λ[1, i] : SSet.{u}) ⟶ X) :
    ∃ σ : Δ[1] ⟶ X, σ₀ = Λ[1, i].ι ≫ σ := by
  have hi : i.rev ≠ i := by fin_cases i <;> decide
  refine ⟨SSet.const (σ₀.app _ (horn.face i i.rev hi)), horn.hom_ext _ _ fun j hj ↦ ?_⟩
  have hji : j = i.rev := by fin_cases i <;> fin_cases j <;> simp_all
  subst hji
  simp [SSet.const, Subsingleton.elim (SimplexCategory.const ⦋0⦌ ⦋0⦌ 0) (𝟙 ⦋0⦌)]

/-- A quasicategory in which all outer horns `Λ[n + 2, 0]` and `Λ[n + 2, Fin.last (n + 2)]` extend
to `Δ[n + 2]` is a Kan complex. -/
theorem kanComplex_of_outerHornFilling (Z : SSet.{u}) [Quasicategory Z]
    (h₀ : ∀ ⦃n : ℕ⦄ (σ₀ : (Λ[n + 2, 0] : SSet.{u}) ⟶ Z),
      ∃ σ : Δ[n + 2] ⟶ Z, σ₀ = Λ[n + 2, 0].ι ≫ σ)
    (hₙ : ∀ ⦃n : ℕ⦄ (σ₀ : (Λ[n + 2, Fin.last (n + 2)] : SSet.{u}) ⟶ Z),
      ∃ σ : Δ[n + 2] ⟶ Z, σ₀ = Λ[n + 2, Fin.last (n + 2)].ι ≫ σ) :
    KanComplex Z := by
  refine kanComplex_of_hornFilling Z fun {n} {i} σ₀ ↦ ?_
  obtain _ | m := n
  · exact horn.exists_extension_one i σ₀
  · by_cases hi₀ : i = 0
    · subst hi₀
      exact h₀ σ₀
    · by_cases hiₙ : i = Fin.last (m + 2)
      · subst hiₙ
        exact hₙ σ₀
      · exact Quasicategory.hornFilling (Fin.pos_iff_ne_zero.2 hi₀)
          (lt_of_le_of_ne (Fin.le_last i) hiₙ) σ₀

/-- The opposite of a map `p` has the right lifting property with respect to `Λ[n, i] ⟶ Δ[n]`
exactly when `p` has the right lifting property with respect to the reversed horn inclusion
`Λ[n, i.rev] ⟶ Δ[n]`. -/
theorem hasLiftingProperty_horn_ι_opFunctor_map_iff (p : X ⟶ Y) {n : ℕ} (i : Fin (n + 1)) :
    HasLiftingProperty Λ[n, i].ι (opFunctor.map p) ↔
      HasLiftingProperty Λ[n, i.rev].ι p :=
  (opEquivalence.toAdjunction.hasLiftingProperty_iff Λ[n, i].ι p).symm.trans
    (HasLiftingProperty.iff_of_arrow_iso_left
      (Arrow.isoMk (horn.opIso n i) (stdSimplex.opIso ⦋n⦌) (horn.opIso_hom_ι n i)) p)

/-- The opposite functor preserves and reflects Kan fibrations. -/
theorem fibration_opFunctor_map_iff (p : X ⟶ Y) :
    Fibration (opFunctor.map p) ↔ Fibration p := by
  simp only [fibration_iff, rlp_J_iff, hasLiftingProperty_horn_ι_opFunctor_map_iff]
  exact ⟨fun h n i ↦ Fin.rev_rev i ▸ h n i.rev, fun h n i ↦ h n i.rev⟩

instance (p : X ⟶ Y) [Fibration p] : Fibration (opFunctor.map p) :=
  (fibration_opFunctor_map_iff p).2 inferInstance

/-- The opposite functor preserves and reflects inner fibrations. -/
theorem innerFibration_opFunctor_map_iff (p : X ⟶ Y) :
    InnerFibration (opFunctor.map p) ↔ InnerFibration p := by
  simp only [innerFibration_iff, mem_innerFibrations_iff,
    hasLiftingProperty_horn_ι_opFunctor_map_iff]
  refine ⟨fun h n i h0 hn ↦ ?_, fun h n i h0 hn ↦ h n i.rev
    (by simpa using Fin.rev_lt_rev.2 hn) (by simpa using Fin.rev_lt_rev.2 h0)⟩
  exact Fin.rev_rev i ▸ h n i.rev
    (by simpa using Fin.rev_lt_rev.2 hn) (by simpa using Fin.rev_lt_rev.2 h0)

instance (p : X ⟶ Y) [InnerFibration p] : InnerFibration (opFunctor.map p) :=
  (innerFibration_opFunctor_map_iff p).2 inferInstance

/-- The opposite functor preserves and reflects Kan complexes. -/
theorem kanComplex_op_iff (X : SSet.{u}) :
    KanComplex X.op ↔ KanComplex X :=
  ⟨fun _ ↦
    have : IsFibrant ((opFunctor ⋙ opFunctor).obj X) := inferInstanceAs (KanComplex X.op.op)
    isFibrant_of_fibration (X := X) (opFunctorCompOpFunctorIso.inv.app X),
    fun _ ↦ inferInstance⟩

/-- The opposite functor preserves and reflects quasicategories. -/
theorem quasicategory_op_iff (X : SSet.{u}) :
    Quasicategory X.op ↔ Quasicategory X := by
  rw [quasicategory_iff_of_isTerminal (opFunctor.map (stdSimplex.isTerminalObj₀.from X))
      stdSimplex.isTerminalOpObj₀, innerFibration_opFunctor_map_iff,
    ← quasicategory_iff_of_isTerminal _ stdSimplex.isTerminalObj₀]

instance (X : SSet.{u}) [Quasicategory X] : Quasicategory X.op :=
  (quasicategory_op_iff X).2 inferInstance

end SSet
