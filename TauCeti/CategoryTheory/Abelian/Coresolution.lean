/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Homology.ShortComplex.Limits
public import Mathlib.CategoryTheory.ObjectProperty.Basic
public import Mathlib.CategoryTheory.Preadditive.Injective.Basic
public import TauCeti.Algebra.Homology.ExactSequence
public import TauCeti.Algebra.Homology.ShortComplex.Exact
public import TauCeti.Algebra.Homology.ShortComplex.ShortExact
public import TauCeti.CategoryTheory.Limits.Shapes.Biproduct

/-!
# Coresolutions with `n` terms

In an abelian category `C`, a *coresolution with `n` terms* of an object `X` is an exact sequence
`0 → X → I⁰ → I¹ → ⋯ → Iⁿ⁻¹`, exact at `X` and at `I⁰, …, Iⁿ⁻²`, but not necessarily at the last
term. It is written as `S : ComposableArrows C (n + 1)` with `S.obj' 0` a zero object,
`S.obj' 1 = X` and `S.obj' (i + 2) = Iⁱ` (`CategoryTheory.ComposableArrows.IsCoresolution`);
exactness at `X` says that `X ⟶ I⁰` is a monomorphism. Unlike Mathlib's
`CategoryTheory.InjectiveResolution`, which is infinite, these truncated coresolutions need no
enough injectives.

The *`i`-th cosyzygy* of `S` is `cokernel (S.map' i (i + 1))`
(`CategoryTheory.ComposableArrows.cosyzygy`): the zeroth one is `X`, and the `(i + 1)`-st is the
cokernel of the monomorphism `cosyzygy i ⟶ Iⁱ` induced by `S`
(`CategoryTheory.ComposableArrows.IsCoresolution.cosyzygyι`).

Coresolutions are built one term at a time: an embedding `ι : X ⟶ I` followed by a coresolution of
`cokernel ι` gives a coresolution of `X` (`CategoryTheory.ComposableArrows.coresolutionCons`), and
every coresolution with `n + 1` terms arises this way, by its tail
(`CategoryTheory.ComposableArrows.IsCoresolution.tail`). For the existence of coresolutions whose
terms satisfy a property `P` (`CategoryTheory.HasCoresolution`) this is
`CategoryTheory.hasCoresolution_succ_iff`. When `P` consists of injective objects and is closed
under binary biproducts, the objects with such a coresolution are closed under extensions
(`CategoryTheory.HasCoresolution.of_shortExact`, the horseshoe argument) and under retracts
(`CategoryTheory.HasCoresolution.of_retract`).

## Main definitions

* `CategoryTheory.ComposableArrows.IsCoresolution`: coresolutions with `n` terms.
* `CategoryTheory.ComposableArrows.cosyzygy`: the cosyzygies of a coresolution.
* `CategoryTheory.ComposableArrows.coresolutionCons` and
  `CategoryTheory.ComposableArrows.IsCoresolution.tail`: splicing an embedding with a coresolution
  of its cokernel, and the converse.
* `CategoryTheory.HasCoresolution P X n`: `X` has a coresolution with `n` terms satisfying `P`.

## Main results

* `CategoryTheory.hasCoresolution_succ_iff`: the recursive description of coresolutions.
* `CategoryTheory.HasCoresolution.of_shortExact`: closure under extensions.
* `CategoryTheory.HasCoresolution.of_retract`: closure under retracts.
* `CategoryTheory.HasCoresolution.map`: exact functors carry coresolutions to coresolutions.

## References

* H. Cartan, S. Eilenberg, *Homological Algebra*, Princeton University Press (1956), §V.2 (the
  horseshoe lemma).
-/

public section

universe v v' u u'

namespace CategoryTheory

open Limits ZeroObject

variable {C : Type u} [Category.{v} C] [Abelian C]

namespace ComposableArrows

variable {n : ℕ}

/-- `S : ComposableArrows C (n + 1)` is a **coresolution with `n` terms** of `S.obj' 1`: the
sequence `0 → S.obj' 1 → S.obj' 2 → ⋯ → S.obj' (n + 1)` is exact, starting at a zero object. The
terms are `S.obj' (i + 2)` for `i < n`; there is no exactness condition at the last one. -/
structure IsCoresolution (S : ComposableArrows C (n + 1)) : Prop where
  /-- The sequence is exact. -/
  exact : S.Exact
  /-- The sequence starts at a zero object. -/
  isZero_left : IsZero S.left

/-- The `i`-th **cosyzygy** of `S : ComposableArrows C (n + 1)`, the cokernel of
`S.map' i (i + 1)`. For a coresolution of `X`, the zeroth cosyzygy is `X`
(`CategoryTheory.ComposableArrows.IsCoresolution.cosyzygyZeroIso`). -/
noncomputable abbrev cosyzygy (S : ComposableArrows C (n + 1)) (i : ℕ) (hi : i ≤ n := by valid) :
    C :=
  cokernel (S.map' i (i + 1))

namespace IsCoresolution

variable {S : ComposableArrows C (n + 1)} (hS : S.IsCoresolution)
include hS

/-- The first map of a coresolution is a monomorphism. -/
theorem mono_map'_one_two (hn : 1 ≤ n) : Mono (S.map' 1 2) :=
  (ShortComplex.exact_iff_mono _ (hS.isZero_left.eq_of_src _ _)).1 (hS.exact.exact 0)

/-- The embedding of the `i`-th cosyzygy into the `i`-th term `S.obj' (i + 2)`. -/
noncomputable def cosyzygyι (i : ℕ) (hi : i < n := by valid) : S.cosyzygy i ⟶ S.obj' (i + 2) :=
  cokernel.desc _ (S.map' (i + 1) (i + 2)) (hS.exact.toIsComplex.zero i)

theorem cosyzygyι_eq_cokernelDesc (i : ℕ) (hi : i < n) :
    hS.cosyzygyι i = cokernel.desc _ (S.map' (i + 1) (i + 2)) (hS.exact.toIsComplex.zero i) :=
  (rfl)

@[reassoc (attr := simp)]
theorem π_cosyzygyι (i : ℕ) (hi : i < n := by valid) :
    cokernel.π (S.map' i (i + 1)) ≫ hS.cosyzygyι i = S.map' (i + 1) (i + 2) :=
  cokernel.π_desc _ _ _

instance mono_cosyzygyι (i : ℕ) (hi : i < n) : Mono (hS.cosyzygyι i) :=
  (hS.exact.exact i).mono_cokernelDesc

/-- The zeroth cosyzygy of a coresolution of `X` is `X`. -/
noncomputable def cosyzygyZeroIso : S.cosyzygy 0 ≅ S.obj' 1 :=
  cokernelIsoOfEq (hS.isZero_left.eq_of_src _ 0) ≪≫ cokernelZeroIsoTarget

@[simp]
theorem cosyzygyZeroIso_inv : hS.cosyzygyZeroIso.inv = cokernel.π (S.map' 0 1) := by
  rw [cosyzygyZeroIso, Iso.trans_inv, cokernelZeroIsoTarget_inv, π_comp_cokernelIsoOfEq_inv]

@[reassoc (attr := simp)]
theorem π_cosyzygyZeroIso_hom : cokernel.π (S.map' 0 1) ≫ hS.cosyzygyZeroIso.hom = 𝟙 _ := by
  rw [← hS.cosyzygyZeroIso_inv, Iso.inv_hom_id]

/-- The `(i + 1)`-st cosyzygy is the cokernel of the embedding of the `i`-th one. -/
noncomputable def cosyzygySuccIso (i : ℕ) (hi : i < n := by valid) :
    S.cosyzygy (i + 1) ≅ cokernel (hS.cosyzygyι i) :=
  cokernelIsoOfEq (hS.π_cosyzygyι i).symm ≪≫ cokernelEpiComp _ _

@[reassoc (attr := simp)]
theorem π_cosyzygySuccIso_hom (i : ℕ) (hi : i < n) :
    cokernel.π (S.map' (i + 1) (i + 2)) ≫ (hS.cosyzygySuccIso i).hom =
      cokernel.π (hS.cosyzygyι i) := by
  simp [cosyzygySuccIso]

@[reassoc (attr := simp)]
theorem π_cosyzygySuccIso_inv (i : ℕ) (hi : i < n) :
    cokernel.π (hS.cosyzygyι i) ≫ (hS.cosyzygySuccIso i).inv =
      cokernel.π (S.map' (i + 1) (i + 2)) := by
  rw [Iso.comp_inv_eq, π_cosyzygySuccIso_hom _ i hi]

omit hS in
/-- Dropping the last term of a coresolution with `n + 1` terms leaves one with `n` terms. -/
theorem δlast {S : ComposableArrows C (n + 2)} (hS : S.IsCoresolution) :
    S.δlast.IsCoresolution :=
  ⟨hS.exact.δlast, hS.isZero_left⟩

omit hS in
/-- Coresolutions are invariant under isomorphisms of composable arrows. -/
theorem of_iso {S T : ComposableArrows C (n + 1)} (hS : S.IsCoresolution) (e : S ≅ T) :
    T.IsCoresolution :=
  ⟨exact_of_iso e hS.exact, hS.isZero_left.of_iso (e.app 0).symm⟩

end IsCoresolution

section Map

variable {D : Type u'} [Category.{v'} D] [Abelian D] (F : C ⥤ D) [F.PreservesZeroMorphisms]
  [F.PreservesHomology]

/-- **Exact functors carry coresolutions to coresolutions.** -/
theorem IsCoresolution.map {S : ComposableArrows C (n + 1)} (hS : S.IsCoresolution) :
    ComposableArrows.IsCoresolution (S ⋙ F) where
  exact :=
    { zero i hi := by
        dsimp only [ComposableArrows.map', Functor.comp_map]
        rw [← F.map_comp, hS.exact.toIsComplex.zero' i (i + 1) (i + 2), F.map_zero]
      exact i hi :=
        ShortComplex.exact_of_iso
          (ShortComplex.isoMk (Iso.refl _) (Iso.refl _) (Iso.refl _) (by simp) (by simp))
          ((hS.exact.exact i).map F) }
  isZero_left := F.map_isZero hS.isZero_left

end Map

section Cons

namespace CoresolutionCons

/-- The objects `0, X, I, T.obj' 2, T.obj' 3, …` of `coresolutionCons ι T e`. -/
@[expose]
noncomputable def obj (X I : C) (T : ComposableArrows C (n + 1)) : Fin (n + 3) → C
  | ⟨0, _⟩ => 0
  | ⟨1, _⟩ => X
  | ⟨2, _⟩ => I
  | ⟨k + 3, _⟩ => T.obj' (k + 2)

/-- The arrows `0 ⟶ X`, `ι`, `I ⟶ cokernel ι ≅ T.obj' 1 ⟶ T.obj' 2` and then those of `T`, of
`coresolutionCons ι T e`. -/
@[expose]
noncomputable def map {X I : C} (ι : X ⟶ I) (T : ComposableArrows C (n + 1))
    (e : cokernel ι ≅ T.obj' 1) : ∀ i : Fin (n + 2), obj X I T i.castSucc ⟶ obj X I T i.succ
  | ⟨0, _⟩ => 0
  | ⟨1, _⟩ => ι
  | ⟨2, _⟩ => cokernel.π ι ≫ e.hom ≫ T.map' 1 2
  | ⟨k + 3, _⟩ => T.map' (k + 2) (k + 3)

end CoresolutionCons

variable {X I : C} (ι : X ⟶ I) (T : ComposableArrows C (n + 1)) (e : cokernel ι ≅ T.obj' 1)

/-- **Splicing an embedding with a coresolution of its cokernel.** For `ι : X ⟶ I` and a
coresolution `T` of `cokernel ι`, identified with `T.obj' 1` by `e`, this is the sequence
`0 → X → I → T.obj' 2 → T.obj' 3 → ⋯`. -/
@[expose]
noncomputable def coresolutionCons : ComposableArrows C (n + 2) :=
  mkOfObjOfMapSucc (CoresolutionCons.obj X I T) (CoresolutionCons.map ι T e)

@[simp]
theorem coresolutionCons_obj'_zero : (coresolutionCons ι T e).obj' 0 = 0 := rfl

@[simp]
theorem coresolutionCons_obj'_one : (coresolutionCons ι T e).obj' 1 = X := rfl

@[simp]
theorem coresolutionCons_obj'_two : (coresolutionCons ι T e).obj' 2 = I := rfl

@[simp]
theorem coresolutionCons_obj'_add_three (k : ℕ) (hk : k + 3 ≤ n + 2) :
    (coresolutionCons ι T e).obj' (k + 3) = T.obj' (k + 2) := rfl

theorem coresolutionCons_map'_zero_one : (coresolutionCons ι T e).map' 0 1 = 0 :=
  mkOfObjOfMapSucc_map_succ _ _ 0

theorem coresolutionCons_map'_one_two : (coresolutionCons ι T e).map' 1 2 = ι :=
  mkOfObjOfMapSucc_map_succ _ _ 1

theorem coresolutionCons_map'_two_three (hn : 1 ≤ n) :
    (coresolutionCons ι T e).map' 2 3 = cokernel.π ι ≫ e.hom ≫ T.map' 1 2 :=
  mkOfObjOfMapSucc_map_succ _ _ 2

theorem coresolutionCons_map'_add_three (k : ℕ) (hk : k + 4 ≤ n + 2) :
    (coresolutionCons ι T e).map' (k + 3) (k + 4) = T.map' (k + 2) (k + 3) :=
  mkOfObjOfMapSucc_map_succ _ _ (k + 3)

variable {ι T e}

/-- The zero compositions of `coresolutionCons ι T e`. -/
private theorem coresolutionCons_zero (hT : T.IsCoresolution) (i : ℕ) (hi : i + 2 ≤ n + 2) :
    CoresolutionCons.map ι T e ⟨i, by omega⟩ ≫ CoresolutionCons.map ι T e ⟨i + 1, by omega⟩ = 0 :=
  match i, hi with
  | 0, _ => zero_comp
  | 1, _ => by
    -- The two arrows are `ι` and `cokernel.π ι ≫ e.hom ≫ T.map' 1 2`.
    change ι ≫ cokernel.π ι ≫ e.hom ≫ T.map' 1 2 = 0
    simp
  | 2, _ => by
    -- The two arrows are `cokernel.π ι ≫ e.hom ≫ T.map' 1 2` and `T.map' 2 3`.
    change (cokernel.π ι ≫ e.hom ≫ T.map' 1 2) ≫ T.map' 2 3 = 0
    rw [Category.assoc, Category.assoc, hT.exact.toIsComplex.zero' 1 2 3, comp_zero, comp_zero]
  | k + 3, _ => hT.exact.toIsComplex.zero (k + 2)

/-- An embedding followed by a coresolution of its cokernel is a coresolution. -/
theorem IsCoresolution.coresolutionCons [Mono ι] (hT : T.IsCoresolution) :
    (coresolutionCons ι T e).IsCoresolution where
  isZero_left := isZero_zero C
  exact := by
    refine exact_mkOfObjOfMapSucc _ _ (coresolutionCons_zero hT) (fun i hi ↦ ?_)
    match i, hi with
    | 0, _ => exact (ShortComplex.exact_iff_mono _ rfl).2 ‹Mono ι›
    | 1, _ =>
      -- The arrows are `ι` and `cokernel.π ι ≫ e.hom ≫ T.map' 1 2`, whose last factor is mono.
      have := hT.mono_map'_one_two (by omega)
      change (ShortComplex.mk ι (cokernel.π ι ≫ e.hom ≫ T.map' 1 2) _).Exact
      exact (ShortComplex.exact_mk_comp_mono_iff ι (cokernel.π ι) (e.hom ≫ T.map' 1 2) _
        (cokernel.condition ι)).2 (ShortComplex.exact_of_g_is_cokernel _ (cokernelIsCokernel ι))
    | 2, _ =>
      -- The arrows are `cokernel.π ι ≫ e.hom ≫ T.map' 1 2` and `T.map' 2 3`; the epimorphisms
      -- `cokernel.π ι` and `e.hom` can be dropped from the first.
      change (ShortComplex.mk (cokernel.π ι ≫ e.hom ≫ T.map' 1 2) (T.map' 2 3) _).Exact
      have h₁₂₃ := hT.exact.toIsComplex.zero' 1 2 3
      exact (ShortComplex.exact_mk_epi_comp_iff (cokernel.π ι) (e.hom ≫ T.map' 1 2) (T.map' 2 3)
        _ (by rw [Category.assoc, h₁₂₃, comp_zero])).2
        ((ShortComplex.exact_mk_epi_comp_iff e.hom (T.map' 1 2) (T.map' 2 3)
          (by rw [Category.assoc, h₁₂₃, comp_zero]) h₁₂₃).2 (hT.exact.exact' 1 2 3))
    | k + 3, _ => exact hT.exact.exact (k + 2)

end Cons

section Tail

namespace CoresolutionTail

/-- The objects `0, cosyzygy 1, S.obj' 3, S.obj' 4, …` of the tail of `S`. -/
@[expose]
noncomputable def obj (S : ComposableArrows C (n + 2)) : Fin (n + 2) → C
  | ⟨0, _⟩ => 0
  | ⟨1, _⟩ => S.cosyzygy 1
  | ⟨k + 2, _⟩ => S.obj' (k + 3)

/-- The arrows of the tail of `S`. -/
@[expose]
noncomputable def map {S : ComposableArrows C (n + 2)} (hS : S.IsCoresolution) :
    ∀ i : Fin (n + 1), obj S i.castSucc ⟶ obj S i.succ
  | ⟨0, _⟩ => 0
  | ⟨1, _⟩ => hS.cosyzygyι 1
  | ⟨k + 2, _⟩ => S.map' (k + 3) (k + 4)

end CoresolutionTail

variable {S : ComposableArrows C (n + 2)} (hS : S.IsCoresolution)

/-- The **tail** of a coresolution `0 → X → I⁰ → I¹ → ⋯`: the coresolution
`0 → cosyzygy 1 → I¹ → I² → ⋯` of the first cosyzygy `cokernel (X ⟶ I⁰)`. -/
@[expose]
noncomputable def IsCoresolution.tail : ComposableArrows C (n + 1) :=
  mkOfObjOfMapSucc (CoresolutionTail.obj S) (CoresolutionTail.map hS)

@[simp]
theorem IsCoresolution.tail_obj'_zero : hS.tail.obj' 0 = 0 := rfl

@[simp]
theorem IsCoresolution.tail_obj'_one : hS.tail.obj' 1 = S.cosyzygy 1 := rfl

@[simp]
theorem IsCoresolution.tail_obj'_add_two (k : ℕ) (hk : k + 2 ≤ n + 1) :
    hS.tail.obj' (k + 2) = S.obj' (k + 3) := rfl

theorem IsCoresolution.tail_map'_zero_one : hS.tail.map' 0 1 = 0 :=
  mkOfObjOfMapSucc_map_succ _ _ 0

theorem IsCoresolution.tail_map'_one_two (hn : 1 ≤ n) : hS.tail.map' 1 2 = hS.cosyzygyι 1 :=
  mkOfObjOfMapSucc_map_succ _ _ 1

theorem IsCoresolution.tail_map'_add_two (k : ℕ) (hk : k + 3 ≤ n + 1) :
    hS.tail.map' (k + 2) (k + 3) = S.map' (k + 3) (k + 4) :=
  mkOfObjOfMapSucc_map_succ _ _ (k + 2)

/-- The zero compositions of the tail. -/
private theorem tail_zero (i : ℕ) (hi : i + 2 ≤ n + 1) :
    CoresolutionTail.map hS ⟨i, by omega⟩ ≫ CoresolutionTail.map hS ⟨i + 1, by omega⟩ = 0 :=
  match i, hi with
  | 0, _ => zero_comp
  | 1, _ => by
    -- The two arrows are `cosyzygyι 1` and `S.map' 3 4`.
    change hS.cosyzygyι 1 ≫ S.map' 3 4 = 0
    rw [← cancel_epi (cokernel.π (S.map' 1 2)), comp_zero, hS.π_cosyzygyι_assoc 1]
    exact hS.exact.toIsComplex.zero' 2 3 4
  | k + 2, _ => hS.exact.toIsComplex.zero (k + 3)

/-- The tail of a coresolution is a coresolution. -/
theorem IsCoresolution.isCoresolution_tail : hS.tail.IsCoresolution where
  isZero_left := isZero_zero C
  exact := by
    refine exact_mkOfObjOfMapSucc _ _ (tail_zero hS) (fun i hi ↦ ?_)
    match i, hi with
    | 0, _ =>
      have := hS.mono_cosyzygyι 1 (by omega)
      exact (ShortComplex.exact_iff_mono _ rfl).2 this
    | 1, _ =>
      -- The arrows are `cosyzygyι 1` and `S.map' 3 4`. Precomposed with the epimorphism
      -- `cokernel.π (S.map' 1 2)`, the first becomes `S.map' 2 3`.
      change (ShortComplex.mk (hS.cosyzygyι 1) (S.map' 3 4) _).Exact
      have h := hS.exact.toIsComplex.zero' 2 3 4
      refine (ShortComplex.exact_mk_epi_comp_iff (cokernel.π (S.map' 1 2)) (hS.cosyzygyι 1)
        (S.map' 3 4) (by rw [hS.π_cosyzygyι 1]; exact h) _).1 ?_
      exact ShortComplex.exact_of_iso (S₁ := ShortComplex.mk (S.map' 2 3) (S.map' 3 4) h)
        (ShortComplex.isoMk (Iso.refl _) (Iso.refl _) (Iso.refl _)
          (by rw [Iso.refl_hom, Iso.refl_hom, Category.comp_id, Category.id_comp]
              exact hS.π_cosyzygyι 1) (by simp))
        (hS.exact.exact' 2 3 4)
    | k + 2, _ => exact hS.exact.exact (k + 3)

end Tail

end ComposableArrows

open ComposableArrows

/-- `X` **has a coresolution with `n` terms satisfying `P`**: there is a coresolution
`0 → X → I⁰ → ⋯ → Iⁿ⁻¹` (`CategoryTheory.ComposableArrows.IsCoresolution`) whose terms `Iⁱ` all
satisfy `P`. -/
def HasCoresolution (P : ObjectProperty C) (X : C) (n : ℕ) : Prop :=
  ∃ S : ComposableArrows C (n + 1), S.IsCoresolution ∧ Nonempty (S.obj' 1 ≅ X) ∧
    ∀ (i : ℕ) (hi : i < n), P (S.obj' (i + 2))

variable {P : ObjectProperty C}

theorem hasCoresolution_iff {X : C} {n : ℕ} :
    HasCoresolution P X n ↔ ∃ S : ComposableArrows C (n + 1), S.IsCoresolution ∧
      Nonempty (S.obj' 1 ≅ X) ∧ ∀ (i : ℕ) (hi : i < n), P (S.obj' (i + 2)) :=
  Iff.rfl

/-- Every object has a coresolution with no terms, `0 → X`. -/
@[simp]
theorem hasCoresolution_zero (X : C) : HasCoresolution P X 0 :=
  ⟨mk₁ (0 : 0 ⟶ X), ⟨(mk₁ (0 : 0 ⟶ X)).exact₁, isZero_zero C⟩, ⟨Iso.refl _⟩,
    fun _ hi ↦ absurd hi (Nat.not_lt_zero _)⟩

theorem HasCoresolution.of_iso {X Y : C} {n : ℕ} (h : HasCoresolution P X n) (e : X ≅ Y) :
    HasCoresolution P Y n := by
  obtain ⟨S, hS, ⟨e'⟩, hP⟩ := h
  exact ⟨S, hS, ⟨e' ≪≫ e⟩, hP⟩

theorem hasCoresolution_iff_of_iso {X Y : C} {n : ℕ} (e : X ≅ Y) :
    HasCoresolution P X n ↔ HasCoresolution P Y n :=
  ⟨fun h ↦ h.of_iso e, fun h ↦ h.of_iso e.symm⟩

/-- **Coresolutions are built one term at a time.** `X` has a coresolution with `n + 1` terms
satisfying `P` exactly when it embeds into an object `I` satisfying `P` such that `cokernel ι` has
a coresolution with `n` terms satisfying `P`. -/
theorem hasCoresolution_succ_iff {X : C} {n : ℕ} :
    HasCoresolution P X (n + 1) ↔
      ∃ (I : C) (ι : X ⟶ I), Mono ι ∧ P I ∧ HasCoresolution P (cokernel ι) n := by
  constructor
  · rintro ⟨S, hS, ⟨e⟩, hP⟩
    have := hS.mono_map'_one_two (by omega)
    refine ⟨S.obj' 2, e.inv ≫ S.map' 1 2, inferInstance, hP 0 (by omega),
      ⟨hS.tail, hS.isCoresolution_tail, ⟨(cokernelEpiComp e.inv (S.map' 1 2)).symm⟩,
        fun i hi ↦ hP (i + 1) (by omega)⟩⟩
  · rintro ⟨I, ι, hι, hI, T, hT, ⟨e⟩, hP⟩
    refine ⟨coresolutionCons ι T e.symm, hT.coresolutionCons, ⟨Iso.refl _⟩, fun i hi ↦ ?_⟩
    match i, hi with
    | 0, _ => exact hI
    | k + 1, _ => exact hP k (by omega)

/-- `X` has a coresolution with one term satisfying `P` exactly when it embeds into an object
satisfying `P`. -/
theorem hasCoresolution_one_iff {X : C} :
    HasCoresolution P X 1 ↔ ∃ (I : C) (ι : X ⟶ I), Mono ι ∧ P I := by
  rw [hasCoresolution_succ_iff]
  exact ⟨fun ⟨I, ι, hι, hI, _⟩ ↦ ⟨I, ι, hι, hI⟩,
    fun ⟨I, ι, hι, hI⟩ ↦ ⟨I, ι, hι, hI, hasCoresolution_zero _⟩⟩

/-- `X` has a coresolution with two terms satisfying `P` exactly when it has a copresentation
`0 → X → I⁰ → I¹`, exact at `X` and `I⁰`, with `I⁰` and `I¹` satisfying `P`. -/
theorem hasCoresolution_two_iff {X : C} :
    HasCoresolution P X 2 ↔
      ∃ (I₀ I₁ : C) (f : X ⟶ I₀) (g : I₀ ⟶ I₁) (w : f ≫ g = 0), Mono f ∧
        (ShortComplex.mk f g w).Exact ∧ P I₀ ∧ P I₁ := by
  rw [hasCoresolution_succ_iff]
  constructor
  · rintro ⟨I₀, f, hf, hI₀, h⟩
    obtain ⟨I₁, ι, hι, hI₁⟩ := hasCoresolution_one_iff.1 h
    refine ⟨I₀, I₁, f, cokernel.π f ≫ ι, by simp, hf, ?_, hI₀, hI₁⟩
    rw [ShortComplex.exact_mk_comp_mono_iff f (cokernel.π f) ι _ (cokernel.condition f)]
    exact ShortComplex.exact_of_g_is_cokernel _ (cokernelIsCokernel f)
  · rintro ⟨I₀, I₁, f, g, w, hf, hfg, hI₀, hI₁⟩
    have := hfg.mono_cokernelDesc
    exact ⟨I₀, f, hf, hI₀, hasCoresolution_one_iff.2 ⟨I₁, cokernel.desc f g w, this, hI₁⟩⟩

/-- Dropping the last term of a coresolution with `n + 1` terms leaves one with `n` terms. -/
theorem HasCoresolution.of_succ {X : C} {n : ℕ} (h : HasCoresolution P X (n + 1)) :
    HasCoresolution P X n := by
  obtain ⟨S, hS, e, hP⟩ := h
  exact ⟨S.δlast, hS.δlast, e, fun i hi ↦ hP i (by omega)⟩

theorem HasCoresolution.of_le {X : C} {m n : ℕ} (h : HasCoresolution P X n) (hmn : m ≤ n) :
    HasCoresolution P X m := by
  induction hmn with
  | refl => exact h
  | step _ ih => exact ih h.of_succ

/-- **Coresolutions add up.** If `P` is closed under binary biproducts, then coresolutions with
`n` terms satisfying `P` of `X` and of `Y` give one of `X ⊞ Y`. -/
theorem HasCoresolution.biprod (hP : ∀ A B : C, P A → P B → P (A ⊞ B)) {n : ℕ} :
    ∀ {X Y : C}, HasCoresolution P X n → HasCoresolution P Y n → HasCoresolution P (X ⊞ Y) n := by
  induction n with
  | zero => exact fun _ _ ↦ hasCoresolution_zero _
  | succ n ih =>
    intro X Y hX hY
    obtain ⟨I, ι, hι, hI, hX'⟩ := hasCoresolution_succ_iff.1 hX
    obtain ⟨J, κ, hκ, hJ, hY'⟩ := hasCoresolution_succ_iff.1 hY
    refine hasCoresolution_succ_iff.2 ⟨I ⊞ J, biprod.map ι κ, inferInstance, hP _ _ hI hJ, ?_⟩
    exact (ih hX' hY').of_iso (IsColimit.coconePointUniqueUpToIso
      (CokernelCofork.isColimitBiprod (cokernelIsCokernel ι) (cokernelIsCokernel κ))
      (colimit.isColimit _))

/-- **Coresolutions of extensions** (the horseshoe lemma). Let `P` be a property of injective
objects closed under binary biproducts. If the ends of a short exact sequence
`0 → B → A → Ω → 0` have coresolutions with `n` terms satisfying `P`, so does the middle: an
embedding `B ⟶ Q` extends to `A`, and together with an embedding `Ω ⟶ I` it embeds `A` into
`Q ⊞ I`, with the cokernels again forming a short exact sequence. -/
theorem HasCoresolution.of_shortExact (hP : ∀ Y, P Y → Injective Y)
    (hPb : ∀ A B : C, P A → P B → P (A ⊞ B)) {n : ℕ} :
    ∀ {L : ShortComplex C}, L.ShortExact → HasCoresolution P L.X₁ n → HasCoresolution P L.X₃ n →
      HasCoresolution P L.X₂ n := by
  induction n with
  | zero => exact fun _ _ _ ↦ hasCoresolution_zero _
  | succ n ih =>
    intro L hL h₁ h₃
    obtain ⟨Q, β, hβ, hQ, hβ'⟩ := hasCoresolution_succ_iff.1 h₁
    obtain ⟨I, ω, hω, hI, hω'⟩ := hasCoresolution_succ_iff.1 h₃
    have := hP Q hQ
    have := hL.mono_f
    have := hL.epi_g
    let β₂ : L.X₂ ⟶ Q := Injective.factorThru β L.f
    have hβ₂ : L.f ≫ β₂ = β := Injective.comp_factorThru _ _
    let ι : L.X₂ ⟶ Q ⊞ I := biprod.lift β₂ (L.g ≫ ω)
    let L₂ : ShortComplex C := ShortComplex.mk (biprod.inl : Q ⟶ Q ⊞ I) biprod.snd (by simp)
    let v : L ⟶ L₂ :=
      { τ₁ := β
        τ₂ := ι
        τ₃ := ω
        comm₁₂ := by ext <;> simp [ι, L₂, hβ₂]
        comm₂₃ := by simp [ι, L₂] }
    have hι : Mono ι :=
      ShortComplex.mono_τ₂_of_exact_of_mono (φ := v) hL.exact (S₂ := L₂)
    let L₃ : ShortComplex C :=
      { f := cokernel.map β ι L.f biprod.inl (by ext <;> simp [ι, hβ₂])
        g := cokernel.map ι ω L.g biprod.snd (by simp [ι])
        zero := by ext; simp }
    let π : L₂ ⟶ L₃ :=
      { τ₁ := cokernel.π β
        τ₂ := cokernel.π ι
        τ₃ := cokernel.π ω }
    have w : v ≫ π = 0 := by ext <;> simp [v, π]
    have hπ : IsColimit (CokernelCofork.ofπ π w) := by
      apply ShortComplex.isColimitOfIsColimitπ <;>
        apply (CokernelCofork.isColimitMapCoconeEquiv _ _).2
      · exact cokernelIsCokernel _
      · exact cokernelIsCokernel _
      · exact cokernelIsCokernel _
    have hL₃ : L₃.ShortExact := ShortComplex.ShortExact.of_isColimit_cokernelCofork
      (ShortComplex.Splitting.ofHasBinaryBiproduct Q I).shortExact hL.exact v π w hπ
    exact hasCoresolution_succ_iff.2 ⟨Q ⊞ I, ι, hι, hPb _ _ hQ hI, ih hL₃ hβ' hω'⟩

/-- The complement `cokernel r.i` of a retract `X` of `Y` is again a retract of `Y`. -/
private noncomputable def retractCokernel {X Y : C} (r : Retract X Y) :
    Retract (cokernel r.i) Y where
  i := cokernel.desc r.i (𝟙 Y - r.r ≫ r.i) (by simp)
  r := cokernel.π r.i
  retract := by
    ext
    simp

/-- **Coresolutions of retracts.** Let `P` be a property of injective objects closed under binary
biproducts. If `Y` has a coresolution with `n` terms satisfying `P`, so does every retract `X` of
`Y`: if `Y` embeds into `I`, then `X` embeds into `I` too, and the cokernel is an extension of the
cokernel of `Y ⟶ I` by the complement of `X` in `Y`. -/
theorem HasCoresolution.of_retract (hP : ∀ Y, P Y → Injective Y)
    (hPb : ∀ A B : C, P A → P B → P (A ⊞ B)) {n : ℕ} :
    ∀ {X Y : C}, Retract X Y → HasCoresolution P Y n → HasCoresolution P X n := by
  induction n with
  | zero => exact fun _ _ ↦ hasCoresolution_zero _
  | succ n ih =>
    intro X Y r hY
    obtain ⟨I, ι, hι, hI, hY'⟩ := hasCoresolution_succ_iff.1 hY
    refine hasCoresolution_succ_iff.2 ⟨I, r.i ≫ ι, inferInstance, hI, ?_⟩
    exact HasCoresolution.of_shortExact hP hPb
      (TauCeti.kernelCokernelCompSequence_snakeInput_L₃_shortExact r.i ι)
      (ih (retractCokernel r) hY.of_succ) hY'

section Map

variable {D : Type u'} [Category.{v'} D] [Abelian D] (F : C ⥤ D) [F.PreservesZeroMorphisms]
  [F.PreservesHomology] {Q : ObjectProperty D}

/-- **Exact functors carry coresolutions to coresolutions.** If an exact functor `F` sends objects
satisfying `P` to objects satisfying `Q`, it carries coresolutions with terms in `P` to
coresolutions with terms in `Q`. -/
theorem HasCoresolution.map (hPQ : ∀ Y, P Y → Q (F.obj Y)) {X : C} {n : ℕ}
    (h : HasCoresolution P X n) : HasCoresolution Q (F.obj X) n := by
  obtain ⟨S, hS, ⟨e⟩, hP⟩ := h
  exact ⟨S ⋙ F, hS.map F, ⟨F.mapIso e⟩, fun i hi ↦ hPQ _ (hP i hi)⟩

end Map

end CategoryTheory
