/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicTopology.SimplicialSet.AnodyneExtensions.PushoutProduct
public import Mathlib.AlgebraicTopology.SimplicialSet.Homotopy
public import Mathlib.AlgebraicTopology.SimplicialSet.SubcomplexColimits

/-!
# Trivial fibrations of simplicial sets are shrinkable

A morphism `p : X ⟶ Y` of simplicial sets is *shrinkable* (in the sense of Dold) when it has a
section `s` such that `p ≫ s` is homotopic to `𝟙 X` through a homotopy over `Y`, that is, a
homotopy `h : X ⊗ Δ[1] ⟶ X` with `h ≫ p = fst ≫ p`. This is the simplicial analogue of a
fibrewise deformation of `X` onto the image of a section.

We prove that a morphism has the right lifting property with respect to all monomorphisms (a
trivial fibration for the Kan–Quillen model structure, see `SSet.rlp_monomorphisms`) exactly when
it is a Kan fibration which is shrinkable:

* a trivial fibration has a section, by lifting against `⊥ ⟶ Y`, and the homotopy is obtained by
  lifting against the inclusion into `X ⊗ Δ[1]` of the union of the two ends `X ⊗ {0}` and
  `X ⊗ {1}`;
* conversely, given a square from a monomorphism `i : A ⟶ B` to a shrinkable Kan fibration `p`,
  the composite of the bottom map with the section agrees with the top map up to the fibrewise
  homotopy; lifting against the anodyne pushout-product of `i` with the vertex `0` of `Δ[1]`
  transports it to an actual lift at the other end.

In particular a trivial fibration is a simplicial homotopy equivalence, compatibly with the
projection to `Y`. This is the combinatorial input for the comparison of trivial fibrations with
weak equivalences in the Kan–Quillen model structure.

## Main declarations

* `SSet.Shrinking p`: a section of `p` together with a homotopy over `Y` from `p ≫ s` to `𝟙 X`.
* `SSet.horn_one_zero_ι_eq_const`: the horn `Λ[1, 0]` is the vertex `0` of `Δ[1]`.
* `SSet.Shrinking.ofRLP`: a trivial fibration is shrinkable.
* `SSet.Shrinking.rlp_monomorphisms`: a shrinkable Kan fibration is a trivial fibration.
* `SSet.rlp_monomorphisms_iff`: the resulting characterization of trivial fibrations.

## References

* A. Dold, *Partitions of unity in the theory of fibrations*, Ann. of Math. 78 (1963).
* P. G. Goerss and J. F. Jardine, *Simplicial homotopy theory*, Progress in Mathematics 174,
  Birkhäuser, 1999, Chapter I.
-/

public section

universe u

open CategoryTheory MonoidalCategory CartesianMonoidalCategory Limits MorphismProperty
  HomotopicalAlgebra

open scoped Simplicial

namespace SSet

open modelCategoryQuillen

variable {X Y : SSet.{u}}

/-- The two ends `X ⊗ {0}` and `X ⊗ {1}` of the cylinder `X ⊗ Δ[1]` are disjoint. -/
lemma range_ι₀_inf_range_ι₁ :
    Subcomplex.range (ι₀ : X ⟶ X ⊗ Δ[1]) ⊓ Subcomplex.range ι₁ = ⊥ := by
  ext ⟨n⟩ z
  induction n using SimplexCategory.rec with | _ n
  simp only [Subfunctor.min_obj, Set.mem_inter_iff, Subfunctor.range_obj, Set.mem_range,
    Subfunctor.bot_obj, Set.mem_empty_iff_false, iff_false, not_and]
  rintro ⟨x, rfl⟩ ⟨y, h⟩
  have := congrArg (fun z : (X ⊗ Δ[1] : SSet.{u}) _⦋n⦌ ↦ z.2 0) h
  simp at this

/-- The horn `Λ[1, 0]` is the vertex `0` of `Δ[1]`: every simplex of it is constant at `0`. -/
lemma horn_one_zero_ι_eq_const : Λ[1, 0].ι = const (stdSimplex.obj₀Equiv.{u}.symm 0) := by
  ext ⟨n⟩ x
  induction n using SimplexCategory.rec with | _ n
  obtain ⟨σ, hσ⟩ := x
  refine stdSimplex.ext _ _ fun k ↦ ?_
  rw [mem_horn_iff_notMem_range] at hσ
  obtain ⟨j, hj, hj'⟩ := hσ
  obtain rfl : j = 1 := by fin_cases j <;> simp_all
  have h0 : σ k = 0 := by
    have : σ k ≠ 1 := fun h ↦ hj' ⟨k, h⟩
    omega
  -- The two sides are the vertex `σ k` and the vertex of the constant simplex at `0`.
  exact h0

/-- A *shrinking* of a morphism `p : X ⟶ Y` of simplicial sets: a section `s` of `p` together
with a homotopy from `p ≫ s` to `𝟙 X` over `Y`. A morphism admitting a shrinking is shrinkable
in the sense of Dold. -/
structure Shrinking (p : X ⟶ Y) where
  /-- The section of `p`. -/
  section_ : Y ⟶ X
  /-- The section is a right inverse of `p`. -/
  section_comp : section_ ≫ p = 𝟙 Y := by cat_disch
  /-- The homotopy from `p ≫ section_` to the identity. -/
  homotopy : Homotopy (p ≫ section_) (𝟙 X)
  /-- The homotopy lies over `Y`. -/
  homotopy_h_comp : homotopy.h ≫ p = fst X Δ[1] ≫ p := by cat_disch

namespace Shrinking

attribute [reassoc (attr := simp)] section_comp homotopy_h_comp

variable {p : X ⟶ Y}

/-- A morphism with the right lifting property with respect to all monomorphisms has a
section. -/
private lemma exists_section (hp : (monomorphisms SSet.{u}).rlp p) : ∃ s : Y ⟶ X, s ≫ p = 𝟙 Y := by
  have := hp _ (monomorphisms.infer_property (⊥ : Y.Subcomplex).ι)
  have sq : CommSq (Subcomplex.isInitialBot.to X) (⊥ : Y.Subcomplex).ι p (𝟙 Y) :=
    ⟨Subcomplex.isInitialBot.hom_ext _ _⟩
  exact ⟨sq.lift, sq.fac_right⟩

/-- A trivial fibration is shrinkable: given a section `s` of `p`, lifting against the inclusion
of the two ends of the cylinder the map which is `p ≫ s` on `X ⊗ {0}` and the identity on
`X ⊗ {1}` gives a homotopy over `Y`. -/
private lemma exists_homotopy (hp : (monomorphisms SSet.{u}).rlp p) (s : Y ⟶ X) (hs : s ≫ p = 𝟙 Y) :
    ∃ H : Homotopy (p ≫ s) (𝟙 X), H.h ≫ p = fst X Δ[1] ≫ p := by
  let A₀ := Subcomplex.range (ι₀ : X ⟶ X ⊗ Δ[1])
  let A₁ := Subcomplex.range (ι₁ : X ⟶ X ⊗ Δ[1])
  have hsq := (show Subcomplex.BicartSq ⊥ A₀ A₁ (A₀ ⊔ A₁) from
    ⟨rfl, range_ι₀_inf_range_ι₁⟩).isPushout
  let φ : ((A₀ ⊔ A₁ : (X ⊗ Δ[1]).Subcomplex) : SSet.{u}) ⟶ X :=
    hsq.desc (A₀.ι ≫ fst _ _ ≫ p ≫ s) (A₁.ι ≫ fst _ _) (Subcomplex.isInitialBot.hom_ext _ _)
  have sq : CommSq φ (A₀ ⊔ A₁).ι p (fst _ _ ≫ p) :=
    ⟨hsq.hom_ext (by simp [φ, hs]) (by simp [φ])⟩
  have := hp _ (monomorphisms.infer_property (A₀ ⊔ A₁).ι)
  have h₀ : ι₀ = Subcomplex.toRange ι₀ ≫ Subcomplex.homOfLE le_sup_left ≫ (A₀ ⊔ A₁).ι := rfl
  have h₁ : ι₁ = Subcomplex.toRange ι₁ ≫ Subcomplex.homOfLE le_sup_right ≫ (A₀ ⊔ A₁).ι := rfl
  refine ⟨⟨sq.lift, ?_, ?_, ?_⟩, sq.fac_right⟩
  · rw [h₀, Category.assoc, Category.assoc, sq.fac_left]
    simp only [φ, hsq.inl_desc]
    exact (Subcomplex.toRange_ι_assoc ι₀ _).trans (ι₀_fst_assoc _ _)
  · rw [h₁, Category.assoc, Category.assoc, sq.fac_left]
    simp only [φ, hsq.inr_desc]
    exact (Subcomplex.toRange_ι_assoc ι₁ _).trans (ι₁_fst _)
  · ext _ ⟨⟨_, hx⟩, _⟩
    simp at hx

/-- A morphism with the right lifting property with respect to all monomorphisms (a trivial
fibration) admits a shrinking. -/
noncomputable def ofRLP (hp : (monomorphisms SSet.{u}).rlp p) : Shrinking p where
  section_ := (exists_section hp).choose
  section_comp := (exists_section hp).choose_spec
  homotopy := (exists_homotopy hp _ (exists_section hp).choose_spec).choose
  homotopy_h_comp := (exists_homotopy hp _ (exists_section hp).choose_spec).choose_spec

/-- A shrinkable Kan fibration has the right lifting property with respect to all monomorphisms:
given a square from a monomorphism `i : A ⟶ B` to `p` with bottom map `b`, the map `b ≫ s` is
deformed along the fibrewise homotopy, relative to `A`, into a lift. -/
theorem rlp_monomorphisms [Fibration p] (h : Shrinking p) : (monomorphisms SSet.{u}).rlp p := by
  intro A B i (hi : Mono i)
  refine ⟨fun {a b} sq ↦ ?_⟩
  let P := Functor.PushoutObjObj.ofHasPushout (curriedTensor SSet.{u}) i Λ[1, 0].ι
  have hP : anodyneExtensions P.ι := anodyneExtensions_pushoutObjObjι P (.horn_ι 0)
  have := hP p (mem_fibrations p)
  let φ : P.pt ⟶ X := P.isPushout.desc (fst _ _ ≫ b ≫ h.section_) (a ▷ _ ≫ h.homotopy.h) (by
    have e : X ◁ Λ[1, 0].ι ≫ h.homotopy.h = fst _ _ ≫ p ≫ h.section_ := by
      have hι : X ◁ Λ[1, 0].ι = fst _ _ ≫ ι₀ := CartesianMonoidalCategory.hom_ext _ _
        (by simp) (by simp [horn_one_zero_ι_eq_const, comp_const])
      rw [hι, Category.assoc, Homotopy.h₀]
    dsimp
    rw [whisker_exchange_assoc, e]
    simp [sq.w_assoc])
  have sq' : CommSq φ P.ι p (fst _ _ ≫ b) := ⟨P.hom_ext (by simp [φ]) (by
    simp [φ, sq.w])⟩
  exact ⟨⟨{ l := ι₁ ≫ sq'.lift
            fac_left := by
              have e : i ▷ Δ[1] = P.inr ≫ P.ι := P.inr_ι.symm
              rw [← ι₁_comp_assoc, e, Category.assoc, sq'.fac_left]
              simp [φ]
            fac_right := by simp }⟩⟩

end Shrinking

/-- A morphism of simplicial sets has the right lifting property with respect to all monomorphisms
(it is a trivial fibration for the Kan–Quillen model structure) if and only if it is a Kan
fibration admitting a shrinking. -/
theorem rlp_monomorphisms_iff {p : X ⟶ Y} :
    (monomorphisms SSet.{u}).rlp p ↔ Fibration p ∧ Nonempty (Shrinking p) :=
  ⟨fun hp ↦ ⟨(modelCategoryQuillen.fibration_iff p).2 (antitone_rlp J_le_monomorphisms _ hp),
    ⟨.ofRLP hp⟩⟩, fun ⟨_, ⟨h⟩⟩ ↦ h.rlp_monomorphisms⟩

end SSet
