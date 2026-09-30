/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.LocallyConstant.Basic
public import Mathlib.Topology.Sets.Closeds
public import TauCeti.Algebra.Category.ModuleCat.Sheaf.FiniteLocallyFree
public import TauCeti.AlgebraicGeometry.VectorBundle.FiniteLocallyFree

/-!
# The rank of a finite locally free sheaf

A finite locally free sheaf `E` on a scheme `X` is free on a finite basis over an open
neighbourhood of every point. Its rank at `x` is the number of elements of such a basis around
`x`. This does not depend on the neighbourhood or on the basis: two bases around `x` restrict to
bases of `E` over their common neighbourhood `W`, and since `Γ(X, W)` is a nonzero commutative
ring, isomorphic finite free sheaves over `W` have bases of the same cardinality. As the same
basis computes the rank at every point of its neighbourhood, the rank is a locally constant
function `X → ℕ`. It need not be constant: on a disconnected scheme the rank may differ between
components.

## Main declarations

* `TauCeti.AlgebraicGeometry.FiniteLocallyFreeSheaf.rank`: the rank of a finite locally free
  sheaf, as a locally constant function on `X`, computed on any local basis by
  `FiniteLocallyFreeSheaf.rank_apply_eq_natCard`;
* `TauCeti.AlgebraicGeometry.FiniteLocallyFreeSheaf.rankLocus`: the clopen locus where the rank
  takes a given value;
* `FiniteLocallyFreeSheaf.rank_eq_of_iso`, `FiniteLocallyFreeSheaf.rank_free_apply` and
  `FiniteLocallyFreeSheaf.rank_pullback_apply`: the rank is invariant under isomorphism, is `|I|`
  for the free sheaf on `I`, and is preserved by pullback;
* `FiniteLocallyFreeSheaf.isInvertible_iff_forall_rank_eq_one`: the invertible sheaves are exactly
  the finite locally free sheaves of rank one at every point, so that the fully faithful inclusion
  `InvertibleSheaf.toFiniteLocallyFree` identifies `InvertibleSheaf X` with the rank-one objects
  (`InvertibleSheaf.rank_toFiniteLocallyFree_apply`).

## References

* [The Stacks Project, Tag 01C9](https://stacks.math.columbia.edu/tag/01C9)
* [R. Hartshorne, *Algebraic Geometry*][hartshorne1977], Chapter II, Section 5
-/

public section

open CategoryTheory TopologicalSpace

namespace TauCeti

namespace AlgebraicGeometry

open _root_.AlgebraicGeometry

universe u

noncomputable section

variable {X : Scheme.{u}}

/-- Two finite bases of an `𝒪_X`-module over open neighbourhoods of a common point have the same
number of elements. -/
theorem _root_.AlgebraicGeometry.Scheme.Modules.natCard_generatingSections_eq_of_mem
    {M : X.Modules} {U V : X.Opens} {x : X} (hU : x ∈ U) (hV : x ∈ V)
    (σ : (M.over U).GeneratingSections) (τ : (M.over V).GeneratingSections)
    [IsIso σ.π] [IsIso τ.π] [Finite σ.I] [Finite τ.I] : Nat.card σ.I = Nat.card τ.I := by
  let W : X.Opens := U ⊓ V
  have : Nonempty W := ⟨⟨x, hU, hV⟩⟩
  let f : W ⟶ U := homOfLE inf_le_left
  let g : W ⟶ V := homOfLE inf_le_right
  have : σ.IsFiniteType := ⟨inferInstance⟩
  have : τ.IsFiniteType := ⟨inferInstance⟩
  have : Finite (σ.restrict f).I :=
    (SheafOfModules.GeneratingSections.isFiniteType_restrict σ f).finite
  have : Finite (τ.restrict g).I :=
    (SheafOfModules.GeneratingSections.isFiniteType_restrict τ g).finite
  have := SheafOfModules.GeneratingSections.isIso_restrict_π σ f
  have := SheafOfModules.GeneratingSections.isIso_restrict_π τ g
  -- The ring of sections of the restricted structure sheaf over the terminal object of the slice
  -- is `Γ(X, W)`, which is nonzero because `W` is nonempty.
  have : Nontrivial ((SheafOfModules.ringCatSheaf (X.sheaf.over W)).obj.obj
      (Opposite.op (Over.mk (𝟙 W)))) := inferInstanceAs (Nontrivial Γ(X, W))
  rw [← congrArg Nat.card (SheafOfModules.GeneratingSections.restrict_I σ f),
    ← congrArg Nat.card (SheafOfModules.GeneratingSections.restrict_I τ g)]
  -- The isomorphism is elaborated on its own: against the expected type, phrased with the
  -- structure sheaf of the slice, instance search does not find the `IsIso` instances above.
  exact SheafOfModules.natCard_eq_of_iso_free (R := X.sheaf.over W)
    (asIso (σ.restrict f).π ≪≫ (asIso (τ.restrict g).π).symm :) (Opposite.op (Over.mk (𝟙 W)))

namespace FiniteLocallyFreeSheaf

/-- A finite locally free sheaf is free on a finite basis over some open neighbourhood of each
point. -/
theorem exists_generatingSections (E : FiniteLocallyFreeSheaf X) (x : X) :
    ∃ (U : X.Opens) (_ : x ∈ U) (σ : (E.obj.over U).GeneratingSections),
      IsIso σ.π ∧ Finite σ.I := by
  obtain ⟨q, hq, hq'⟩ :=
    (SheafOfModules.isFiniteLocallyFree_iff_exists_isLocallyFreeData_isFiniteType E.obj).1
      E.property
  obtain ⟨i, hi⟩ := ((Opens.coversTop_iff _ _).1 q.coversTop).exists_mem x
  exact ⟨q.X i, hi, q.generators i, hq.isIso i, (hq'.isFiniteType i).finite⟩

/-- The number of elements of a finite basis of `E` over a neighbourhood of `x`, for the basis
chosen by `exists_generatingSections`. -/
private def rankAt (E : FiniteLocallyFreeSheaf X) (x : X) : ℕ :=
  Nat.card (E.exists_generatingSections x).choose_spec.choose_spec.choose.I

private theorem rankAt_eq (E : FiniteLocallyFreeSheaf X) {U : X.Opens} {x : X} (hx : x ∈ U)
    (σ : (E.obj.over U).GeneratingSections) [IsIso σ.π] [Finite σ.I] :
    E.rankAt x = Nat.card σ.I := by
  obtain ⟨_, _⟩ := (E.exists_generatingSections x).choose_spec.choose_spec.choose_spec
  exact Scheme.Modules.natCard_generatingSections_eq_of_mem
    (E.exists_generatingSections x).choose_spec.choose hx _ σ

/-- The rank of a finite locally free sheaf `E` on `X`, as a locally constant function on `X`.
Its value at `x` is the number of elements of a basis of `E` over any open neighbourhood of `x`
on which `E` is free (`rank_apply_eq_natCard`). -/
def rank (E : FiniteLocallyFreeSheaf X) : LocallyConstant X ℕ where
  toFun := E.rankAt
  isLocallyConstant := by
    refine (IsLocallyConstant.iff_exists_open _).2 fun x ↦ ?_
    obtain ⟨U, hx, σ, _, _⟩ := E.exists_generatingSections x
    exact ⟨U, U.isOpen, hx, fun y hy ↦ by rw [E.rankAt_eq hy σ, E.rankAt_eq hx σ]⟩

/-- The rank of `E` at `x` is the number of elements of any basis of `E` over an open
neighbourhood of `x`. -/
theorem rank_apply_eq_natCard (E : FiniteLocallyFreeSheaf X) {U : X.Opens} {x : X}
    (hx : x ∈ U) (σ : (E.obj.over U).GeneratingSections) [IsIso σ.π] [Finite σ.I] :
    E.rank x = Nat.card σ.I :=
  E.rankAt_eq hx σ

/-- The characteristic equation of `rank`, for a basis of a module equal to the underlying module
and with the instance arguments passed explicitly. It is used where the underlying module is only
propositionally equal to the module the basis is given on, or where instance search does not
recognize the hypotheses on the basis. -/
private theorem rank_apply_eq_natCard_of_obj_eq (E : FiniteLocallyFreeSheaf X) {M : X.Modules}
    (h : E.obj = M) {U : X.Opens} {x : X} (hx : x ∈ U) (σ : (M.over U).GeneratingSections)
    (hσ : IsIso σ.π) (hI : Finite σ.I) : E.rank x = Nat.card σ.I := by
  subst h
  exact E.rank_apply_eq_natCard hx σ

/-- Isomorphic finite locally free sheaves have the same rank. -/
theorem rank_eq_of_iso {E F : FiniteLocallyFreeSheaf X} (e : E.obj ≅ F.obj) :
    E.rank = F.rank := by
  ext x
  obtain ⟨U, hx, σ, hσ, hI⟩ := E.exists_generatingSections x
  let p := ((SheafOfModules.overFunctor X.ringCatSheaf U).mapIso e).hom
  rw [E.rank_apply_eq_natCard hx σ, F.rank_apply_eq_natCard_of_obj_eq rfl hx (σ.ofEpi p)
    (SheafOfModules.GeneratingSections.isIso_ofEpi_π σ p hσ) hI,
    SheafOfModules.GeneratingSections.ofEpi_I]

/-- The free sheaf on a finite type `I` has rank `|I|` at every point. -/
@[simp]
theorem rank_free_apply (I : Type u) [Finite I] (x : X) :
    (free X I).rank x = Nat.card I :=
  -- The global basis of the free sheaf, restricted to `⊤`; its index type is `I` itself.
  let σ := (SheafOfModules.free.generatingSections (R := X.ringCatSheaf) I).localGeneratorsData
  (free X I).rank_apply_eq_natCard_of_obj_eq (free_obj X I) (Opens.mem_top x)
    (σ.generators (⊤ : X.Opens))
    (SheafOfModules.LocalGeneratorsData.IsLocallyFreeData.isIso (q := σ) (⊤ : X.Opens))
    ‹Finite I›

/-- The rank of the pullback of a finite locally free sheaf `E` along `f : X ⟶ Y` at `x` is the
rank of `E` at `f x`. -/
@[simp]
theorem rank_pullback_apply {Y : Scheme.{u}} (f : X ⟶ Y) (E : FiniteLocallyFreeSheaf Y)
    (x : X) : ((pullback f).obj E).rank x = E.rank (f x) := by
  obtain ⟨U, hx, σ, hσ, hI⟩ := E.exists_generatingSections (f x)
  let τ := σ.mapIso (Scheme.Modules.pullbackOver f U) (Scheme.Modules.pullbackOverUnitIso f U)
    (Scheme.Modules.pullbackOverObjIso f U E.obj)
  have hτ : Nat.card τ.I = Nat.card σ.I :=
    congrArg Nat.card (SheafOfModules.GeneratingSections.mapIso_I _ _ _ _)
  rw [E.rank_apply_eq_natCard hx σ, ← hτ]
  exact ((pullback f).obj E).rank_apply_eq_natCard_of_obj_eq (pullback_obj_obj f E)
    (U := f ⁻¹ᵁ U) hx τ (SheafOfModules.GeneratingSections.isIso_mapIso_π _ _ _ _)
    (by rw [SheafOfModules.GeneratingSections.mapIso_I]; exact hI)

/-- The rank locus of `E` in rank `n`: the clopen set of points at which `E` has rank `n`. -/
def rankLocus (E : FiniteLocallyFreeSheaf X) (n : ℕ) : TopologicalSpace.Clopens X :=
  ⟨E.rank ⁻¹' {n}, E.rank.isLocallyConstant.isClopen_fiber n⟩

/-- A point lies in the rank locus of `E` in rank `n` exactly when `E` has rank `n` there. -/
@[simp]
theorem mem_rankLocus {E : FiniteLocallyFreeSheaf X} {n : ℕ} {x : X} :
    x ∈ E.rankLocus n ↔ E.rank x = n :=
  Iff.rfl

end FiniteLocallyFreeSheaf

/-- An invertible sheaf has rank one at every point. -/
@[simp]
theorem InvertibleSheaf.rank_toFiniteLocallyFree_apply (L : InvertibleSheaf X) (x : X) :
    ((InvertibleSheaf.toFiniteLocallyFree X).obj L).rank x = 1 := by
  obtain ⟨q, hq⟩ := L.property.exists_isInvertible
  obtain ⟨i, hi⟩ := ((Opens.coversTop_iff _ _).1 q.coversTop).exists_mem x
  have := hq.basisSubsingleton i
  rw [FiniteLocallyFreeSheaf.rank_apply_eq_natCard_of_obj_eq _ rfl hi (q.generators i)
    (hq.isLocallyFreeData.isIso i) Finite.of_subsingleton, Nat.card_eq_one_iff_unique]
  exact ⟨inferInstance, hq.basisNonempty i⟩

/-- A finite locally free sheaf is invertible if and only if it has rank one at every point. -/
theorem FiniteLocallyFreeSheaf.isInvertible_iff_forall_rank_eq_one
    (E : FiniteLocallyFreeSheaf X) :
    SheafOfModules.isInvertible X E.obj ↔ ∀ x, E.rank x = 1 := by
  refine ⟨fun h x ↦ ?_, fun h ↦ ?_⟩
  · rw [E.rank_eq_of_iso (F := (InvertibleSheaf.toFiniteLocallyFree X).obj ⟨E.obj, h⟩)
      (Iso.refl _)]
    exact InvertibleSheaf.rank_toFiniteLocallyFree_apply _ x
  -- Around each point `x`, a finite basis of `E` has `E.rank x = 1` elements, so it trivializes
  -- `E` by the structure sheaf.
  choose U hU σ hσ hI using E.exists_generatingSections
  have hu (x : X) : Nonempty (Unique (σ x).I) :=
    (unique_iff_subsingleton_and_nonempty _).2 <| Nat.card_eq_one_iff_unique.1 <|
      (E.rank_apply_eq_natCard_of_obj_eq rfl (hU x) (σ x) (hσ x) (hI x)).symm.trans (h x)
  -- The free sheaf on the one-element basis is the coproduct of a single copy of the unit. The
  -- `IsIso` hypothesis is passed explicitly: against the expected type, phrased with the
  -- structure sheaf of the slice, instance search does not find it.
  exact (SheafOfModules.LocalTrivializations.ofForallMem X U hU fun x ↦
    letI := (hu x).some
    (Limits.coproductUniqueIso fun _ : (σ x).I ↦ _root_.SheafOfModules.unit _).symm ≪≫
      @asIso _ _ _ _ (σ x).π (hσ x)).isInvertible

end

end AlgebraicGeometry

end TauCeti
