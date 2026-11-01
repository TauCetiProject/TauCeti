/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.Finsupp.Weight
public import TauCeti.CategoryTheory.Abelian.Injective.Basic
public import TauCeti.CategoryTheory.Semisimple.Multiplicity

/-!
# Split monomorphisms and finite semisimplicity

In a finite semisimple category every object is injective, so every monomorphism splits: a
monomorphism out of a simple object splits by Schur's lemma, and a finite biproduct of injective
objects is injective.

Conversely, splitting of monomorphisms is how finite semisimplicity is recognised in practice.
Let `F : D ⥤ C` be a faithful additive functor from an abelian category to a finite semisimple
category. If every monomorphism of `D` splits, then `D` is finite semisimple: an object which is
neither zero nor simple has a nonzero proper subobject, which splits off as a biproduct summand,
and the total simple multiplicity of the image under `F` of each summand is strictly smaller.

The splitting hypothesis is supplied by a Maschke-type averaging argument. If moreover `F`
preserves monomorphisms, and the identity functor of `D` maps into `F ⋙ G` for some `G : C ⥤ D`
by a natural transformation whose components are split monomorphisms, then a retraction of
`F.map m` for a monomorphism `m` of `D` transports along `G` to a retraction of `m`. So `D` is
finite semisimple (`TauCeti.IsFiniteSemisimpleCategory.of_natTrans`). This is the shape of the
proof that the Drinfeld centre of a fusion category of nonzero global dimension is semisimple,
where `F` forgets the half-braiding and `G` is the induction functor. It is also the shape of the
classical proof of Maschke's theorem, with `G` coinduction from the trivial group.

## Main results

* `TauCeti.IsFiniteSemisimpleCategory.injective`: every object of a finite semisimple category is
  injective.
* `TauCeti.IsFiniteSemisimpleCategory.isSplitMono_of_mono`: every monomorphism of a finite
  semisimple category splits.
* `TauCeti.IsFiniteSemisimpleCategory.of_faithful`: an abelian category in which every
  monomorphism splits, with a faithful additive functor to a finite semisimple category, is
  finite semisimple.
* `TauCeti.IsFiniteSemisimpleCategory.of_natTrans`: the Maschke-type criterion above.

## References

* P. Etingof, D. Nikshych, V. Ostrik, *On fusion categories*, Ann. of Math. **162** (2005), §2
* [P. Etingof, S. Gelaki, D. Nikshych, V. Ostrik, *Tensor categories*][egno15], §§1.8, 9.3
-/

public section

noncomputable section

namespace TauCeti

open CategoryTheory Limits

universe v v' u u'

namespace IsFiniteSemisimpleCategory

section Injective

variable {C : Type u} [Category.{v} C] [Abelian C] [IsFiniteSemisimpleCategory C]

/-- Every object of a finite semisimple category is injective. -/
instance injective (X : C) : Injective X := by
  obtain ⟨ι, hι, f, hf, hbf, ⟨e⟩⟩ := exists_biproduct_simples X
  -- A monomorphism out of a simple object is nonzero, hence split.
  have (i : ι) : Injective (f i) := by
    have := hf i
    exact (injective_iff_forall_isSplitMono _).2 fun Y g _ ↦
      isSplitMono_of_nonzero_from_simple fun hg ↦
        Simple.not_isZero (f i) (IsZero.of_mono_eq_zero g hg)
  -- A finite biproduct of injective objects is injective. Mathlib's instance for `⨁` asks for the
  -- index type to live in the universe of morphisms, so the extension is built by hand.
  refine ⟨fun {A B} g m _ ↦ ⟨biproduct.lift (fun i ↦
    Injective.factorThru (g ≫ e.hom ≫ biproduct.π f i) m) ≫ e.inv, ?_⟩⟩
  rw [← cancel_mono e.hom]
  ext i
  simp

/-- Every monomorphism of a finite semisimple category splits. -/
theorem isSplitMono_of_mono {X Y : C} (f : X ⟶ Y) [Mono f] : IsSplitMono f :=
  (injective_iff_forall_isSplitMono X).1 inferInstance f

end Injective

variable {C : Type u} [Category.{v} C] [Abelian C]

/-- A zero object is the biproduct of the empty family of simple objects. -/
private theorem exists_biproduct_simples_of_isZero {X : C} (hX : IsZero X) :
    ∃ (ι : Type) (_ : Fintype ι) (f : ι → C) (_ : ∀ i, Simple (f i)) (_ : HasBiproduct f),
      Nonempty (X ≅ ⨁ f) := by
  let _ : HasFiniteBiproducts C := Abelian.hasFiniteBiproducts
  refine ⟨Empty, inferInstance, Empty.elim, fun i ↦ i.elim, inferInstance, ⟨hX.iso ?_⟩⟩
  exact (IsZero.iff_id_eq_zero _).2 (biproduct.hom_ext _ _ fun i ↦ i.elim)

/-- A simple object is the biproduct of the family consisting of itself. -/
private theorem exists_biproduct_simples_of_simple (X : C) [Simple X] :
    ∃ (ι : Type) (_ : Fintype ι) (f : ι → C) (_ : ∀ i, Simple (f i)) (_ : HasBiproduct f),
      Nonempty (X ≅ ⨁ f) := by
  let _ : HasFiniteBiproducts C := Abelian.hasFiniteBiproducts
  exact ⟨Unit, inferInstance, fun _ ↦ X, fun _ ↦ inferInstance, inferInstance,
    ⟨(biproductUniqueIso fun _ : Unit ↦ X).symm⟩⟩

/-- Decompositions of `X` and `Y` into finite biproducts of simple objects combine to one of
`X ⊞ Y`. -/
private theorem exists_biproduct_simples_biprod {X Y : C}
    (hX : ∃ (ι : Type) (_ : Fintype ι) (f : ι → C) (_ : ∀ i, Simple (f i)) (_ : HasBiproduct f),
      Nonempty (X ≅ ⨁ f))
    (hY : ∃ (ι : Type) (_ : Fintype ι) (f : ι → C) (_ : ∀ i, Simple (f i)) (_ : HasBiproduct f),
      Nonempty (Y ≅ ⨁ f)) :
    ∃ (ι : Type) (_ : Fintype ι) (f : ι → C) (_ : ∀ i, Simple (f i)) (_ : HasBiproduct f),
      Nonempty (X ⊞ Y ≅ ⨁ f) := by
  obtain ⟨ι, hι, f, hf, hbf, ⟨e⟩⟩ := hX
  obtain ⟨κ, hκ, g, hg, hbg, ⟨d⟩⟩ := hY
  let _ : HasFiniteBiproducts C := Abelian.hasFiniteBiproducts
  refine ⟨ι ⊕ κ, inferInstance, Sum.elim f g, fun | .inl i => hf i | .inr j => hg j,
    inferInstance, ⟨biprod.mapIso e d ≪≫ (biproductSumIso f g).symm⟩⟩

variable {D : Type u'} [Category.{v'} D] [Abelian D]

/-- An abelian category in which every monomorphism splits is finite semisimple if it has a
faithful additive functor to a finite semisimple category. -/
theorem of_faithful [IsFiniteSemisimpleCategory C] (F : D ⥤ C) [F.Faithful] [F.Additive]
    (h : ∀ ⦃X Y : D⦄ (f : X ⟶ Y) [Mono f], IsSplitMono f) :
    IsFiniteSemisimpleCategory D where
  exists_biproduct_simples X := by
    -- Induct on the total simple multiplicity of `F.obj X`.
    suffices ∀ (n : ℕ) (X : D), (simpleMultiplicities (F.obj X)).degree = n →
        ∃ (ι : Type) (_ : Fintype ι) (f : ι → D) (_ : ∀ i, Simple (f i))
          (_ : HasBiproduct f), Nonempty (X ≅ ⨁ f) from this _ X rfl
    intro n
    induction n using Nat.strong_induction_on with | _ n ih => ?_
    intro X hn
    by_cases hX : IsZero X
    · exact exists_biproduct_simples_of_isZero hX
    by_cases hXs : Simple X
    · exact exists_biproduct_simples_of_simple X
    -- Otherwise `X` has a nonzero subobject `f : Y ⟶ X` which is not an isomorphism.
    obtain ⟨Y, f, _, hf, hfi⟩ : ∃ (Y : D) (f : Y ⟶ X) (_ : Mono f), f ≠ 0 ∧ ¬IsIso f := by
      by_contra! H
      exact hXs ⟨fun f _ ↦ ⟨fun _ hf ↦ hX (IsZero.of_epi_eq_zero f hf),
        fun hf ↦ H _ f inferInstance hf⟩⟩
    -- The subobject splits off: `X ≅ Y ⊞ Z`, where `Z` is the cokernel of `f`.
    have := h f
    let Z := cokernel f
    let e : X ≅ Y ⊞ Z :=
      biprod.uniqueUpToIso _ _ (isBilimitBinaryBiconeOfIsSplitMonoOfCokernel
        (cokernelIsCokernel f))
    have hY : ¬IsZero Y := fun hY ↦ hf (hY.eq_of_src _ _)
    have hZ : ¬IsZero Z := fun hZ ↦ hfi (by
      have := Preadditive.epi_of_isZero_cokernel f hZ
      exact isIso_of_mono_of_epi f)
    -- Both summands have strictly smaller total multiplicity under `F`.
    have hF {W : D} (hW : ¬IsZero W) : (simpleMultiplicities (F.obj W)).degree ≠ 0 := by
      rw [Ne, Finsupp.degree_eq_zero_iff, simpleMultiplicities_eq_zero_iff]
      refine fun hFW ↦ hW ((IsZero.iff_id_eq_zero _).2 (F.map_eq_zero_iff.1 ?_))
      rw [F.map_id]
      exact hFW.eq_of_src _ _
    have := preservesBinaryBiproducts_of_preservesBiproducts F
    have hsum : n = (simpleMultiplicities (F.obj Y)).degree +
        (simpleMultiplicities (F.obj Z)).degree := by
      rw [← hn, simpleMultiplicities_eq_of_iso (F.mapIso e ≪≫ F.mapBiprod Y Z),
        simpleMultiplicities_biprod, map_add]
    obtain ⟨ι, hι, g, hg, hbg, ⟨d⟩⟩ := exists_biproduct_simples_biprod
      (ih _ (by have := hF hZ; omega) Y rfl) (ih _ (by have := hF hY; omega) Z rfl)
    exact ⟨ι, hι, g, hg, hbg, ⟨e ≪≫ d⟩⟩

/-- A Maschke-type criterion for finite semisimplicity. Let `F : D ⥤ C` be a faithful additive
functor which preserves monomorphisms, from an abelian category to a finite semisimple category.
If the identity functor of `D` maps into `F ⋙ G`, for some `G : C ⥤ D`, by a natural
transformation whose components are split monomorphisms, then `D` is finite semisimple. -/
theorem of_natTrans [IsFiniteSemisimpleCategory C] (F : D ⥤ C) [F.Faithful] [F.Additive]
    [F.PreservesMonomorphisms] (G : C ⥤ D) (i : 𝟭 D ⟶ F ⋙ G)
    [∀ X, IsSplitMono (i.app X)] : IsFiniteSemisimpleCategory D :=
  of_faithful F fun A B m _ ↦ by
    -- A retraction `r` of `F.map m` gives the retraction `i.app B ≫ G.map r ≫ retraction`
    -- of `m`, by naturality of `i`.
    have := isSplitMono_of_mono (F.map m)
    refine IsSplitMono.mk' ⟨i.app B ≫ G.map (retraction (F.map m)) ≫ retraction (i.app A), ?_⟩
    have hi := i.naturality m
    simp only [Functor.id_map, Functor.comp_map] at hi
    rw [reassoc_of% hi, ← G.map_comp_assoc, IsSplitMono.id, G.map_id, Category.id_comp,
      IsSplitMono.id]

end IsFiniteSemisimpleCategory

end TauCeti
