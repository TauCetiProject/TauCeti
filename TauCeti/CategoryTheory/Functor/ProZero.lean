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
public import Mathlib.CategoryTheory.Linear.FunctorCategory

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
* `CategoryTheory.MorphismProperty.forall_exists_iff_forall_exists_le` and
  `CategoryTheory.MorphismProperty.forall_exists_map_iff_of_initial`: the preorder form and the
  cofinal reindexing of the condition that every object is the target of a morphism with a given
  property, shared by pro-zero and pro-`r`-torsion diagrams.
* `CategoryTheory.Functor.isProZero_comp_iff`: being pro-zero is invariant under reindexing along an
  initial functor out of a cofiltered category; `CategoryTheory.Functor.isProZero_monotone_comp_iff`
  is the case of a cofinal monotone reindexing of inverse systems.
* `CategoryTheory.Functor.IsProTorsionBy`: in an `R`-linear category, the diagrams that `r : R`
  kills as pro-objects, with the same reindexing lemmas, closure of the killing scalars under
  addition and multiplication (`CategoryTheory.Functor.IsProTorsionBy.add`,
  `CategoryTheory.Functor.IsProTorsionBy.mul_left`), the case `r = 1`
  (`CategoryTheory.Functor.isProTorsionBy_one_iff`) and closure under subobjects, quotients and
  extensions (`CategoryTheory.Functor.IsProTorsionBy.of_shortExact`).
* `CategoryTheory.Functor.isSerreClass_isProZero`: in an abelian category, pro-zero diagrams form a
  Serre class.
* `CategoryTheory.Functor.proIsomorphisms`: the pro-isomorphisms of diagrams.
* `CategoryTheory.Functor.proIsomorphisms_kernel_ι_smul_id_iff`: in an `R`-linear abelian
  category, the inclusion of the kernel of `r • 𝟙 F` (for a tower of modules, the subtower of
  `r`-torsion) is a pro-isomorphism exactly when `F` is pro-`r`-torsion.

## References

* B. Bhatt, *On the direct summand conjecture and its derived variant*, Invent. Math. 212 (2018),
  §3 (pro-zero towers, in their almost form).
-/

public section

namespace CategoryTheory

open Limits ZeroObject

universe w v₁ v₂ v₃ u₁ u₂ u₃ u₄

namespace MorphismProperty

/-- Over the opposite of a preorder, every object is the target of a morphism satisfying `P`
exactly when every `i` has some `j ≥ i` whose transition `j ⟶ i` satisfies `P`. -/
lemma forall_exists_iff_forall_exists_le {ι : Type u₃} [Preorder ι] (P : MorphismProperty ιᵒᵖ) :
    (∀ j, ∃ (i : ιᵒᵖ) (f : i ⟶ j), P f) ↔ ∀ i, ∃ (j : ι) (h : i ≤ j), P (homOfLE h).op := by
  refine ⟨fun hP i ↦ ?_, fun hP i ↦ ?_⟩
  · obtain ⟨j, f, hf⟩ := hP (Opposite.op i)
    exact ⟨j.unop, leOfHom f.unop, by rwa [Subsingleton.elim (homOfLE _).op f]⟩
  · obtain ⟨j, h, hj⟩ := hP i.unop
    exact ⟨Opposite.op j, (homOfLE h).op, hj⟩

/-- **Cofinal reindexing.** Let `P` be a property of morphisms of `J` that is stable under
precomposition and postcomposition with arbitrary morphisms (`P.RespectsLeft ⊤` and
`P.RespectsRight ⊤`). For an initial functor `G : I ⥤ J` out
of a cofiltered category, every object of `J` is the target of a morphism satisfying `P` exactly
when every object of `I` is the target of a morphism whose image under `G` satisfies `P`. -/
theorem forall_exists_map_iff_of_initial {J : Type u₁} [Category.{v₁} J] (P : MorphismProperty J)
    [P.RespectsLeft ⊤] [P.RespectsRight ⊤]
    {I : Type u₃} [Category.{v₃} I] [IsCofilteredOrEmpty I] (G : I ⥤ J) [G.Initial] :
    (∀ i, ∃ (c : I) (f : c ⟶ i), P (G.map f)) ↔ ∀ j, ∃ (i : J) (f : i ⟶ j), P f := by
  have hG := ((Functor.initial_iff_of_isCofiltered G).1 inferInstance).1
  refine ⟨fun hP j ↦ ?_, fun hP i ↦ ?_⟩
  · obtain ⟨c, ⟨u⟩⟩ := hG j
    obtain ⟨i, g, hg⟩ := hP c
    exact ⟨G.obj i, G.map g ≫ u, RespectsRight.postcomp (Q := ⊤) _ trivial _ hg⟩
  · -- Find `f : j ⟶ G i` satisfying `P`, reach `j` from some `G c`, and compare the resulting
    -- map `G c ⟶ G i` with a map in the image of `G` over a common lower bound of `c` and `i`.
    obtain ⟨j, f, hf⟩ := hP (G.obj i)
    obtain ⟨c, ⟨u⟩⟩ := hG j
    obtain ⟨c', t, ht⟩ := Functor.Initial.exists_eq G
      (G.map (IsCofiltered.minToLeft c i) ≫ u ≫ f) (G.map (IsCofiltered.minToRight c i))
    refine ⟨c', t ≫ IsCofiltered.minToRight c i, ?_⟩
    rw [G.map_comp, ← ht, ← Category.assoc, ← Category.assoc]
    exact RespectsLeft.precomp (Q := ⊤) _ trivial _ hf

end MorphismProperty

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
    F.IsProZero ↔ ∀ i, ∃ (j : ι) (h : i ≤ j), F.map (homOfLE h).op = 0 :=
  MorphismProperty.forall_exists_iff_forall_exists_le fun _ _ f ↦ F.map f = 0

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
    (G : I ⥤ J) [G.Initial] (F : J ⥤ C) : (G ⋙ F).IsProZero ↔ F.IsProZero :=
  have : MorphismProperty.RespectsLeft (fun _ _ f ↦ F.map f = 0 : MorphismProperty J) ⊤ :=
    ⟨fun _ _ _ h ↦ by rw [F.map_comp, h, comp_zero]⟩
  have : MorphismProperty.RespectsRight (fun _ _ f ↦ F.map f = 0 : MorphismProperty J) ⊤ :=
    ⟨fun _ _ _ h ↦ by rw [F.map_comp, h, zero_comp]⟩
  MorphismProperty.forall_exists_map_iff_of_initial (fun _ _ f ↦ F.map f = 0) G

/-- **Cofinal monotone reindexing of inverse systems.** If `φ : ι → κ` is monotone and cofinal and
`ι` is directed, then an inverse system `F` indexed by `κ` is pro-zero exactly when its
reindexing along `φ` is. -/
theorem isProZero_monotone_comp_iff {ι : Type u₃} {κ : Type u₄} [Preorder ι] [IsDirectedOrder ι]
    [Preorder κ] {φ : ι → κ} (hφ : Monotone φ) (hcof : ∀ k, ∃ i, k ≤ φ i) (F : κᵒᵖ ⥤ C) :
    (hφ.functor.op ⋙ F).IsProZero ↔ F.IsProZero :=
  have := (hφ.final_functor_iff).2 hcof
  isProZero_comp_iff _ F

end HasZeroMorphisms

section Linear

variable [Preadditive C] {R : Type w} [Semiring R] [Linear R C]

/-- A diagram `F : J ⥤ C` in an `R`-linear category is *pro-`r`-torsion* if `r` kills, for every
`j`, some map `F.map f : F i ⟶ F j` of the diagram. For a cofiltered `J` this says that `r` kills
`F` as a pro-object. -/
def IsProTorsionBy (F : J ⥤ C) (r : R) : Prop :=
  ∀ j, ∃ (i : J) (f : i ⟶ j), r • F.map f = 0

lemma isProTorsionBy_iff (F : J ⥤ C) (r : R) :
    F.IsProTorsionBy r ↔ ∀ j, ∃ (i : J) (f : i ⟶ j), r • F.map f = 0 :=
  Iff.rfl

/-- A pro-zero diagram is pro-`r`-torsion for every `r`. -/
lemma IsProZero.isProTorsionBy {F : J ⥤ C} (hF : F.IsProZero) (r : R) : F.IsProTorsionBy r :=
  fun j ↦
    have ⟨i, f, hf⟩ := hF j
    ⟨i, f, by rw [hf, smul_zero]⟩

/-- Every diagram is pro-`0`-torsion. -/
@[simp]
lemma isProTorsionBy_zero (F : J ⥤ C) : F.IsProTorsionBy (0 : R) :=
  fun j ↦ ⟨j, 𝟙 j, zero_smul R _⟩

/-- A diagram is pro-`1`-torsion exactly when it is pro-zero. -/
@[simp]
lemma isProTorsionBy_one_iff {F : J ⥤ C} : F.IsProTorsionBy (1 : R) ↔ F.IsProZero := by
  simp only [isProTorsionBy_iff, isProZero_iff, one_smul]

/-- If `r` kills a diagram as a pro-object, then so does every left multiple `s * r`. -/
lemma IsProTorsionBy.mul_left {F : J ⥤ C} {r : R} (s : R) (h : F.IsProTorsionBy r) :
    F.IsProTorsionBy (s * r) := fun j ↦
  have ⟨i, f, hf⟩ := h j
  ⟨i, f, by rw [mul_smul, hf, smul_zero]⟩

/-- A diagram indexed by the opposite of a preorder is pro-`r`-torsion exactly when `r` kills, for
every `i`, the transition into `F i` from some later term. -/
lemma isProTorsionBy_iff_forall_exists_le {ι : Type u₃} [Preorder ι] (F : ιᵒᵖ ⥤ C) (r : R) :
    F.IsProTorsionBy r ↔ ∀ i, ∃ (j : ι) (h : i ≤ j), r • F.map (homOfLE h).op = 0 :=
  MorphismProperty.forall_exists_iff_forall_exists_le fun _ _ f ↦ r • F.map f = 0

/-- Over a cofiltered index category, the scalars `r` for which a diagram is pro-`r`-torsion are
closed under addition. -/
lemma IsProTorsionBy.add [IsCofilteredOrEmpty J] {F : J ⥤ C} {r s : R} (hr : F.IsProTorsionBy r)
    (hs : F.IsProTorsionBy s) : F.IsProTorsionBy (r + s) := fun j ↦ by
  obtain ⟨i₁, f₁, h₁⟩ := hr j
  obtain ⟨i₂, f₂, h₂⟩ := hs j
  obtain ⟨k, g₁, g₂, hg⟩ := IsCofiltered.cospan f₁ f₂
  refine ⟨k, g₁ ≫ f₁, ?_⟩
  rw [add_smul]
  nth_rw 2 [hg]
  simp only [F.map_comp, ← Linear.comp_smul, h₁, h₂, comp_zero, add_zero]

/-- **Cofinal reindexing.** For an initial functor `G : I ⥤ J` out of a cofiltered category, a
diagram `F : J ⥤ C` is pro-`r`-torsion exactly when `G ⋙ F` is. -/
theorem isProTorsionBy_comp_iff {I : Type u₃} [Category.{v₃} I] [IsCofilteredOrEmpty I]
    (G : I ⥤ J) [G.Initial] (F : J ⥤ C) (r : R) :
    (G ⋙ F).IsProTorsionBy r ↔ F.IsProTorsionBy r :=
  have : MorphismProperty.RespectsLeft (fun _ _ f ↦ r • F.map f = 0 : MorphismProperty J) ⊤ :=
    ⟨fun _ _ _ h ↦ by rw [F.map_comp, ← Linear.comp_smul, h, comp_zero]⟩
  have : MorphismProperty.RespectsRight (fun _ _ f ↦ r • F.map f = 0 : MorphismProperty J) ⊤ :=
    ⟨fun _ _ _ h ↦ by rw [F.map_comp, ← Linear.smul_comp, h, zero_comp]⟩
  MorphismProperty.forall_exists_map_iff_of_initial (fun _ _ f ↦ r • F.map f = 0) G

/-- **Cofinal monotone reindexing of inverse systems.** If `φ : ι → κ` is monotone and cofinal and
`ι` is directed, then an inverse system `F` indexed by `κ` is pro-`r`-torsion exactly when its
reindexing along `φ` is. -/
theorem isProTorsionBy_monotone_comp_iff {ι : Type u₃} {κ : Type u₄} [Preorder ι]
    [IsDirectedOrder ι] [Preorder κ] {φ : ι → κ} (hφ : Monotone φ) (hcof : ∀ k, ∃ i, k ≤ φ i)
    (F : κᵒᵖ ⥤ C) (r : R) : (hφ.functor.op ⋙ F).IsProTorsionBy r ↔ F.IsProTorsionBy r :=
  have := (hφ.final_functor_iff).2 hcof
  isProTorsionBy_comp_iff _ F r

/-- Over a commutative ring of scalars, if `r` kills a diagram as a pro-object, then so does every
multiple `r * s`. -/
lemma IsProTorsionBy.mul_right {R : Type w} [CommSemiring R] [Linear R C] {F : J ⥤ C} {r : R}
    (s : R) (h : F.IsProTorsionBy r) : F.IsProTorsionBy (r * s) :=
  mul_comm s r ▸ h.mul_left s

end Linear

section Abelian

variable [Abelian C]

section Linear

variable {R : Type w} [Semiring R] [Linear R C] {r : R}

/-- A subdiagram of a pro-`r`-torsion diagram is pro-`r`-torsion. -/
lemma IsProTorsionBy.of_mono {X Y : J ⥤ C} (f : X ⟶ Y) [Mono f] (hY : Y.IsProTorsionBy r) :
    X.IsProTorsionBy r := fun j ↦ by
  obtain ⟨i, g, hg⟩ := hY j
  refine ⟨i, g, (cancel_mono (f.app j)).1 ?_⟩
  rw [Linear.smul_comp, f.naturality, ← Linear.comp_smul, hg]
  simp

/-- A quotient of a pro-`r`-torsion diagram is pro-`r`-torsion. -/
lemma IsProTorsionBy.of_epi {X Y : J ⥤ C} (f : X ⟶ Y) [Epi f] (hX : X.IsProTorsionBy r) :
    Y.IsProTorsionBy r := fun j ↦ by
  obtain ⟨i, g, hg⟩ := hX j
  refine ⟨i, g, (cancel_epi (f.app i)).1 ?_⟩
  rw [Linear.comp_smul, ← f.naturality, ← Linear.smul_comp, hg]
  simp

/-- In a short exact sequence of diagrams, if `b` kills the subdiagram and `a` kills the quotient
as pro-objects, then `a * b` kills the middle term as a pro-object. -/
lemma IsProTorsionBy.of_shortExact {T : ShortComplex (J ⥤ C)} (hT : T.ShortExact) {a b : R}
    (h₁ : T.X₁.IsProTorsionBy b) (h₃ : T.X₃.IsProTorsionBy a) : T.X₂.IsProTorsionBy (a * b) := by
  intro j
  -- Let `b` kill `T.X₁.map α` for some `α : i ⟶ j` and `a` kill `T.X₃.map β` for some
  -- `β : k ⟶ i`. Then `a • T.X₂.map β` factors through `T.X₁ i` by exactness at `i`, and
  -- `(a * b) • T.X₂.map (β ≫ α)` factors through `b • T.X₁.map α = 0`.
  obtain ⟨i, α, hα⟩ := h₁ j
  obtain ⟨k, β, hβ⟩ := h₃ i
  have hTi := hT.map_of_exact ((evaluation J C).obj i)
  have := hTi.mono_f
  have hk : (a • T.X₂.map β) ≫ T.g.app i = 0 := by
    rw [Linear.smul_comp, T.g.naturality, ← Linear.comp_smul, hβ, comp_zero]
  refine ⟨k, β ≫ α, ?_⟩
  rw [T.X₂.map_comp, mul_smul, ← Linear.comp_smul, ← Linear.smul_comp,
    ← hTi.exact.lift_f _ hk]
  dsimp
  rw [Category.assoc, Linear.comp_smul, ← T.f.naturality, ← Linear.smul_comp, hα]
  simp

end Linear

/-- In an abelian category, pro-zero diagrams form a Serre class of the functor category: they
contain zero and are closed under subobjects, quotients and extensions. These are the cases
`r = 1` of the closure properties of pro-`r`-torsion diagrams, for the `ℕ`-linear structure. -/
instance isSerreClass_isProZero : ObjectProperty.IsSerreClass (IsProZero (J := J) (C := C)) where
  exists_zero := ⟨0, isZero_zero _, isProZero_zero⟩
  prop_of_mono f _ hY :=
    isProTorsionBy_one_iff.mp (((isProTorsionBy_one_iff (R := ℕ)).mpr hY).of_mono f)
  prop_of_epi f _ hX :=
    isProTorsionBy_one_iff.mp (((isProTorsionBy_one_iff (R := ℕ)).mpr hX).of_epi f)
  prop_X₂_of_shortExact hS h₁ h₃ := by
    simpa using
      ((isProTorsionBy_one_iff (R := ℕ)).mpr h₁).of_shortExact hS (isProTorsionBy_one_iff.mpr h₃)

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

section Linear

variable {R : Type w} [Semiring R] [Linear R C]

/-- **Torsion subdiagrams.** In an `R`-linear abelian category, the inclusion of the kernel of
`r • 𝟙 F` (for a tower of modules, the subtower of `r`-torsion elements) is a pro-isomorphism
exactly when `F` is pro-`r`-torsion: `r` kills, for every `j`, some map `F.map f : F i ⟶ F j` of
the diagram. -/
theorem proIsomorphisms_kernel_ι_smul_id_iff (r : R) (F : J ⥤ C) :
    proIsomorphisms J C (kernel.ι (r • 𝟙 F)) ↔ F.IsProTorsionBy r := by
  -- The inclusion is a monomorphism, so it is a pro-isomorphism iff its cokernel, the coimage of
  -- `r • 𝟙 F`, is pro-zero. The coimage sits between the epimorphism `coimage.π` out of `F` and
  -- the monomorphism `factorThruCoimage` into `F`, whose composite is `r • 𝟙 F`.
  set g := r • 𝟙 F
  have key : ∀ {i j : J} (f : i ⟶ j),
      (Abelian.coimage g).map f = 0 ↔ r • F.map f = 0 := fun {i j} f ↦ by
    rw [← cancel_epi ((Abelian.coimage.π g).app i), ← cancel_mono
      ((Abelian.factorThruCoimage g).app j), comp_zero, zero_comp, Category.assoc,
      ← NatTrans.naturality_assoc,
      ← NatTrans.comp_app, Abelian.coimage.fac]
    simp [g]
  refine (ObjectProperty.isoModSerre_iff_of_mono (P := IsProZero) (kernel.ι g)).trans ?_
  exact forall_congr' fun j ↦ exists_congr fun i ↦ exists_congr fun f ↦ key f

end Linear

end Abelian

end Functor

end CategoryTheory
