/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Abelian.FunctorCategory
public import Mathlib.CategoryTheory.Abelian.SerreClass.MorphismProperty
public import Mathlib.CategoryTheory.Filtered.Final
public import Mathlib.CategoryTheory.Limits.FunctorCategory.EpiMono

/-!
# Pro-zero diagrams and pro-isomorphisms

A diagram `F : J ⥤ C` in a category with zero morphisms is *pro-zero* if every object `F j` is
killed by some map of the diagram: for every `j` there is `f : i ⟶ j` with `F.map f = 0`. For an
inverse system `A₀ ← A₁ ← A₂ ← ⋯` this says that for every `n` some composite transition
`Aₘ → Aₙ` with `m ≥ n` is zero; for a cofiltered `J` it says that `F` is the zero pro-object.
Being pro-zero is a condition on the transition maps, not on the limit: the tower
`ℤ ← ℤ ← ⋯` with transitions multiplication by a prime `p` has zero limit but is not pro-zero.

In an abelian category, pro-zero diagrams form a Serre class of the functor category. The
*pro-isomorphisms* are the morphisms of diagrams whose kernel and cokernel are pro-zero; this is
Mathlib's `ObjectProperty.isoModSerre` for that Serre class, so pro-isomorphisms are stable under
composition and retracts and satisfy two-out-of-three. Pro-zero diagrams, and pro-isomorphisms, are
the error terms that derived limits of towers cannot see.

## Main declarations

* `CategoryTheory.Functor.IsProZero`: pro-zero diagrams.
* `CategoryTheory.Functor.isProZero_iff_forall_exists_le`: the form of the condition for inverse
  systems indexed by a preorder.
* `CategoryTheory.Functor.IsProZero.isZero_of_isLimit`: a limit of a pro-zero diagram is zero.
* `CategoryTheory.Functor.isProZero_comp_iff`: being pro-zero is invariant under reindexing along an
  initial functor out of a cofiltered category; `CategoryTheory.Functor.isProZero_monotone_comp_iff`
  is the case of a cofinal monotone reindexing of inverse systems.
* `CategoryTheory.Functor.isSerreClass_isProZero`: in an abelian category, pro-zero diagrams form a
  Serre class.
* `CategoryTheory.Functor.proIsomorphisms`: the pro-isomorphisms of diagrams.

## References

* B. Bhatt, *On the direct summand conjecture and its derived variant*, Invent. Math. 212 (2018),
  §3 (pro-zero towers, in their almost form).
-/

public section

namespace CategoryTheory

open Limits ZeroObject

universe v₁ v₂ v₃ u₁ u₂ u₃ u₄

namespace Functor

variable {J : Type u₁} [Category.{v₁} J] {C : Type u₂} [Category.{v₂} C]

section HasZeroMorphisms

variable [HasZeroMorphisms C]

/-- A diagram `F : J ⥤ C` is *pro-zero* if every object `F j` is killed by some map of the diagram:
for every `j` there is `f : i ⟶ j` with `F.map f = 0`. For towers `ℕᵒᵖ ⥤ C` this says that every
term is killed by some later composite transition (`isProZero_iff_forall_exists_le`). -/
def IsProZero (F : J ⥤ C) : Prop :=
  ∀ j, ∃ (i : J) (f : i ⟶ j), F.map f = 0

lemma isProZero_iff (F : J ⥤ C) : F.IsProZero ↔ ∀ j, ∃ (i : J) (f : i ⟶ j), F.map f = 0 :=
  Iff.rfl

/-- A zero diagram is pro-zero. -/
lemma isProZero_of_isZero {F : J ⥤ C} (hF : IsZero F) : F.IsProZero :=
  fun j ↦ ⟨j, 𝟙 j, by simpa using congr_app (hF.eq_of_src (𝟙 F) 0) j⟩

@[simp]
lemma isProZero_zero [HasZeroObject C] : (0 : J ⥤ C).IsProZero :=
  isProZero_of_isZero (isZero_zero _)

/-- A diagram indexed by the opposite of a preorder is pro-zero exactly when every term is killed by
the transition from some later term. -/
lemma isProZero_iff_forall_exists_le {ι : Type u₃} [Preorder ι] (F : ιᵒᵖ ⥤ C) :
    F.IsProZero ↔ ∀ i, ∃ (j : ι) (h : i ≤ j), F.map (homOfLE h).op = 0 := by
  refine ⟨fun hF i ↦ ?_, fun hF i ↦ ?_⟩
  · obtain ⟨j, f, hf⟩ := hF (Opposite.op i)
    exact ⟨j.unop, leOfHom f.unop, by rwa [Subsingleton.elim (homOfLE _).op f]⟩
  · obtain ⟨j, h, hj⟩ := hF i.unop
    exact ⟨Opposite.op j, (homOfLE h).op, hj⟩

/-- A tower whose successive transitions are zero is pro-zero, whatever its terms. -/
lemma isProZero_of_map_succ_eq_zero (F : ℕᵒᵖ ⥤ C)
    (hF : ∀ n, F.map (homOfLE (Nat.le_succ n)).op = 0) : F.IsProZero :=
  (isProZero_iff_forall_exists_le F).2 fun n ↦ ⟨n + 1, Nat.le_succ n, hF n⟩

/-- The limit of a pro-zero diagram is a zero object. -/
lemma IsProZero.isZero_of_isLimit {F : J ⥤ C} (hF : F.IsProZero) {c : Cone F} (hc : IsLimit c) :
    IsZero c.pt := by
  rw [IsZero.iff_id_eq_zero]
  refine hc.hom_ext fun j ↦ ?_
  obtain ⟨i, f, hf⟩ := hF j
  rw [← c.w f, hf]
  simp

/-- **Cofinal reindexing.** For an initial functor `G : I ⥤ J` out of a cofiltered category, a
diagram `F : J ⥤ C` is pro-zero exactly when `G ⋙ F` is. -/
theorem isProZero_comp_iff {I : Type u₃} [Category.{v₃} I] [IsCofilteredOrEmpty I]
    (G : I ⥤ J) [G.Initial] (F : J ⥤ C) : (G ⋙ F).IsProZero ↔ F.IsProZero := by
  have hG := ((initial_iff_of_isCofiltered G).1 inferInstance).1
  refine ⟨fun hF j ↦ ?_, fun hF i ↦ ?_⟩
  · obtain ⟨c, ⟨u⟩⟩ := hG j
    obtain ⟨i, g, hg⟩ := hF c
    exact ⟨G.obj i, G.map g ≫ u, by rw [F.map_comp, ← comp_map, hg, zero_comp]⟩
  · -- Kill `F (G i)` by some `f : j ⟶ G i`, reach `j` from some `G c`, and compare the resulting
    -- map `G c ⟶ G i` with a map in the image of `G` over a common lower bound of `c` and `i`.
    obtain ⟨j, f, hf⟩ := hF (G.obj i)
    obtain ⟨c, ⟨u⟩⟩ := hG j
    obtain ⟨c', t, ht⟩ := Initial.exists_eq G
      (G.map (IsCofiltered.minToLeft c i) ≫ u ≫ f) (G.map (IsCofiltered.minToRight c i))
    refine ⟨c', t ≫ IsCofiltered.minToRight c i, ?_⟩
    rw [comp_map, G.map_comp, ← ht]
    simp [hf]

/-- **Cofinal monotone reindexing of inverse systems.** If `φ : ι → κ` is monotone and cofinal and
`ι` is directed, then an inverse system `F` indexed by `κ` is pro-zero exactly when its
reindexing along `φ` is. -/
theorem isProZero_monotone_comp_iff {ι : Type u₃} {κ : Type u₄} [Preorder ι] [IsDirectedOrder ι]
    [Preorder κ] {φ : ι → κ} (hφ : Monotone φ) (hcof : ∀ k, ∃ i, k ≤ φ i) (F : κᵒᵖ ⥤ C) :
    (hφ.functor.op ⋙ F).IsProZero ↔ F.IsProZero :=
  have := (hφ.final_functor_iff).2 hcof
  isProZero_comp_iff _ F

end HasZeroMorphisms

section Abelian

variable [Abelian C]

/-- In an abelian category, pro-zero diagrams form a Serre class of the functor category: they
contain zero and are closed under subobjects, quotients and extensions. -/
instance isSerreClass_isProZero : ObjectProperty.IsSerreClass (IsProZero (J := J) (C := C)) where
  exists_zero := ⟨0, isZero_zero _, isProZero_zero⟩
  prop_of_mono {X Y} f _ hY j := by
    obtain ⟨i, g, hg⟩ := hY j
    refine ⟨i, g, (cancel_mono (f.app j)).1 ?_⟩
    rw [f.naturality, hg]
    simp
  prop_of_epi {X Y} f _ hX j := by
    obtain ⟨i, g, hg⟩ := hX j
    refine ⟨i, g, (cancel_epi (f.app i)).1 ?_⟩
    rw [← f.naturality, hg]
    simp
  prop_X₂_of_shortExact {S} hS h₁ h₃ j := by
    -- Kill `S.X₁ j` by `a : i ⟶ j` and `S.X₃ i` by `b : k ⟶ i`; then `S.X₂.map b` factors through
    -- `S.X₁ i` by exactness at `i`, so `S.X₂.map (b ≫ a)` factors through `S.X₁.map a = 0`.
    obtain ⟨i, a, ha⟩ := h₁ j
    obtain ⟨k, b, hb⟩ := h₃ i
    have hSi := hS.map_of_exact ((evaluation J C).obj i)
    have := hSi.mono_f
    have hk : S.X₂.map b ≫ S.g.app i = 0 := by rw [S.g.naturality, hb]; simp
    refine ⟨k, b ≫ a, ?_⟩
    rw [S.X₂.map_comp, ← hSi.exact.lift_f (S.X₂.map b) hk]
    dsimp
    rw [Category.assoc, ← S.f.naturality, ha]
    simp

/-- The *pro-isomorphisms* of diagrams `J ⥤ C`: the morphisms whose kernel and cokernel are
pro-zero (`proIsomorphisms_iff`). This is Mathlib's class `ObjectProperty.isoModSerre` of
isomorphisms modulo the Serre class of pro-zero diagrams, so pro-isomorphisms are stable under
composition and retracts and satisfy two-out-of-three. -/
abbrev proIsomorphisms (J : Type u₁) [Category.{v₁} J] (C : Type u₂) [Category.{v₂} C]
    [Abelian C] : MorphismProperty (J ⥤ C) :=
  ObjectProperty.isoModSerre (IsProZero (J := J) (C := C))

lemma proIsomorphisms_iff {F G : J ⥤ C} (f : F ⟶ G) :
    proIsomorphisms J C f ↔ (Limits.kernel f).IsProZero ∧ (Limits.cokernel f).IsProZero :=
  Iff.rfl

example : (proIsomorphisms J C).IsMultiplicative := inferInstance

example : (proIsomorphisms J C).HasTwoOutOfThreeProperty := inferInstance

end Abelian

end Functor

end CategoryTheory
