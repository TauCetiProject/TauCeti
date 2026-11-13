/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Homology.ExactSequence
public import Mathlib.CategoryTheory.ObjectProperty.Basic
public import TauCeti.CategoryTheory.Abelian.Injective.Envelope

/-!
# Coresolutions with `n` terms and minimal injective coresolutions

In an abelian category `C`, a *coresolution with `n` terms* of an object `X` is an exact sequence
`0 → X → I⁰ → I¹ → ⋯ → Iⁿ⁻¹`, exact at `X` and at `I⁰, …, Iⁿ⁻²`, but not necessarily at the last
term. It is written as `S : ComposableArrows C (n + 1)` with `S.obj' 0` a zero object,
`S.obj' 1 = X` and `S.obj' (i + 2) = Iⁱ` (`CategoryTheory.ComposableArrows.IsCoresolution`);
exactness at `X` says that `X ⟶ I⁰` is a monomorphism. Unlike Mathlib's
`CategoryTheory.InjectiveResolution`, which is an infinite resolution, these truncated
coresolutions need no enough injectives: a coresolution with `n` terms only asks for the first `n`
cosyzygies to embed into suitable objects.

The *`i`-th cosyzygy* of `S` is `cokernel (S.map' i (i + 1))`
(`CategoryTheory.ComposableArrows.cosyzygy`): the zeroth one is `X`, and the `(i + 1)`-st is the
cokernel of the monomorphism `cosyzygy i ⟶ Iⁱ` induced by `S`
(`CategoryTheory.ComposableArrows.IsCoresolution.cosyzygyι`). A coresolution is **minimal
injective** when each `Iⁱ` is injective and each `cosyzygy i ⟶ Iⁱ` is an injective envelope, that
is, an essential monomorphism (`TauCeti.IsEssentialMono`).

The main results compare coresolutions. A minimal injective coresolution of a retract of `X` is a
termwise retract of every injective coresolution of `X`
(`CategoryTheory.ComposableArrows.IsMinimalInjectiveCoresolution.nonempty_retract`), by induction
on the cosyzygies through
`TauCeti.IsEssentialMono.nonempty_retract_and_nonempty_retract_cokernel`. Two minimal injective
coresolutions of the same object have isomorphic terms
(`CategoryTheory.ComposableArrows.IsMinimalInjectiveCoresolution.nonempty_iso`), and a minimal
injective coresolution with `n` terms exists as soon as the first `n` cosyzygies have injective
envelopes (`CategoryTheory.ComposableArrows.exists_isMinimalInjectiveCoresolution`).

Coresolutions are built one term at a time: an embedding `ι : X ⟶ I` followed by a coresolution of
`cokernel ι` gives a coresolution of `X` (`CategoryTheory.ComposableArrows.coresolutionCons`), and
every coresolution with `n + 1` terms arises this way (`CategoryTheory.hasCoresolution_succ_iff`
for the existence of coresolutions whose terms satisfy a property `P`).

## Main definitions

* `CategoryTheory.ComposableArrows.IsCoresolution`, `IsInjectiveCoresolution` and
  `IsMinimalInjectiveCoresolution`: coresolutions with `n` terms, with injective terms, and minimal
  injective ones.
* `CategoryTheory.ComposableArrows.cosyzygy`: the cosyzygies of a coresolution.
* `CategoryTheory.HasCoresolution P X n`: `X` has a coresolution with `n` terms satisfying `P`.

## Main results

* `CategoryTheory.ComposableArrows.IsMinimalInjectiveCoresolution.nonempty_retract`: a minimal
  injective coresolution is a termwise retract of any injective coresolution.
* `CategoryTheory.ComposableArrows.IsMinimalInjectiveCoresolution.nonempty_iso`: minimal injective
  coresolutions are unique up to isomorphism of their terms.
* `CategoryTheory.ComposableArrows.exists_isMinimalInjectiveCoresolution`: existence, given
  injective envelopes.
* `CategoryTheory.hasCoresolution_succ_iff`: the recursive description of coresolutions.

## References

* I. Assem, D. Simson, A. Skowroński, *Elements of the Representation Theory of Associative
  Algebras, Vol. 1*, LMS Student Texts 65, CUP (2006), I.5.
* F. W. Anderson, K. R. Fuller, *Rings and Categories of Modules*, 2nd ed., Springer GTM 13
  (1992), §18.
-/

public section

universe v u

namespace CategoryTheory

open Limits TauCeti ZeroObject

variable {C : Type u} [Category.{v} C] [Abelian C]

namespace ComposableArrows

variable {n : ℕ}

section General

variable {m : ℕ} (obj : Fin (m + 1) → C) (mapSucc : ∀ i : Fin m, obj i.castSucc ⟶ obj i.succ)

/-- The composable arrows `mkOfObjOfMapSucc obj mapSucc` are exact as soon as consecutive
`mapSucc` compose to zero and form exact short complexes. -/
theorem exact_mkOfObjOfMapSucc
    (w : ∀ (i : ℕ) (hi : i + 2 ≤ m), mapSucc ⟨i, by omega⟩ ≫ mapSucc ⟨i + 1, by omega⟩ = 0)
    (h : ∀ (i : ℕ) (hi : i + 2 ≤ m), (ShortComplex.mk _ _ (w i hi)).Exact) :
    (mkOfObjOfMapSucc obj mapSucc).Exact where
  zero i hi := by
    rw [mkOfObjOfMapSucc_map_succ obj mapSucc i (by omega),
      mkOfObjOfMapSucc_map_succ obj mapSucc (i + 1) (by omega)]
    exact w i hi
  exact i hi := by
    refine ShortComplex.exact_of_iso ?_ (h i hi)
    exact ShortComplex.isoMk (Iso.refl _) (Iso.refl _) (Iso.refl _)
      (by simp [mkOfObjOfMapSucc_map_succ obj mapSucc i (by omega)])
      (by simp [mkOfObjOfMapSucc_map_succ obj mapSucc (i + 1) (by omega)])

end General

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

@[reassoc (attr := simp)]
theorem π_cosyzygyι (i : ℕ) (hi : i < n := by valid) :
    cokernel.π (S.map' i (i + 1)) ≫ hS.cosyzygyι i = S.map' (i + 1) (i + 2) :=
  cokernel.π_desc _ _ _

instance mono_cosyzygyι (i : ℕ) (hi : i < n) : Mono (hS.cosyzygyι i) :=
  (hS.exact.exact i).mono_cokernelDesc

/-- The zeroth cosyzygy of a coresolution of `X` is `X`. -/
noncomputable def cosyzygyZeroIso : S.cosyzygy 0 ≅ S.obj' 1 :=
  cokernelIsoOfEq (hS.isZero_left.eq_of_src _ 0) ≪≫ cokernelZeroIsoTarget

/-- The `(i + 1)`-st cosyzygy is the cokernel of the embedding of the `i`-th one. -/
noncomputable def cosyzygySuccIso (i : ℕ) (hi : i < n := by valid) :
    S.cosyzygy (i + 1) ≅ cokernel (hS.cosyzygyι i) :=
  cokernelIsoOfEq (hS.π_cosyzygyι i).symm ≪≫ cokernelEpiComp _ _

end IsCoresolution

/-- An **injective coresolution with `n` terms**: a coresolution whose terms `S.obj' (i + 2)`,
`i < n`, are injective. -/
structure IsInjectiveCoresolution (S : ComposableArrows C (n + 1)) : Prop
    extends S.IsCoresolution where
  /-- The terms are injective. -/
  injective (i : ℕ) (hi : i < n) : Injective (S.obj' (i + 2))

/-- A **minimal injective coresolution with `n` terms**: an injective coresolution in which every
cosyzygy embeds into the next term by an injective envelope, that is, an essential
monomorphism. -/
structure IsMinimalInjectiveCoresolution (S : ComposableArrows C (n + 1)) : Prop
    extends S.IsInjectiveCoresolution where
  /-- Each cosyzygy embeds into the next term by an essential monomorphism. -/
  isEssentialMono (i : ℕ) (hi : i < n) :
    IsEssentialMono (cokernel.desc (S.map' i (i + 1)) (S.map' (i + 1) (i + 2))
      (exact.toIsComplex.zero i))

theorem IsMinimalInjectiveCoresolution.isEssentialMono_cosyzygyι
    {S : ComposableArrows C (n + 1)} (hS : S.IsMinimalInjectiveCoresolution) (i : ℕ)
    (hi : i < n) : IsEssentialMono (hS.toIsCoresolution.cosyzygyι i) :=
  hS.isEssentialMono i hi

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
theorem coresolutionCons_obj_one : (coresolutionCons ι T e).obj' 1 = X := rfl

@[simp]
theorem coresolutionCons_obj_two : (coresolutionCons ι T e).obj' 2 = I := rfl

@[simp]
theorem coresolutionCons_obj_add_three (k : ℕ) (hk : k + 3 ≤ n + 2) :
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

/-- An embedding followed by a coresolution of its cokernel is a coresolution. -/
theorem IsCoresolution.coresolutionCons [Mono ι] (hT : T.IsCoresolution) :
    (coresolutionCons ι T e).IsCoresolution where
  isZero_left := isZero_zero C
  exact := by
    refine exact_mkOfObjOfMapSucc _ _ (fun i hi ↦ ?_) (fun i hi ↦ ?_)
    · match i, hi with
      | 0, _ => exact zero_comp
      | 1, _ =>
        change ι ≫ cokernel.π ι ≫ e.hom ≫ T.map' 1 2 = 0
        rw [cokernel.condition_assoc, zero_comp]
      | 2, _ =>
        change (cokernel.π ι ≫ e.hom ≫ T.map' 1 2) ≫ T.map' 2 3 = 0
        rw [Category.assoc, Category.assoc, hT.exact.toIsComplex.zero' 1 2 3, comp_zero,
          comp_zero]
      | k + 3, _ => exact hT.exact.toIsComplex.zero (k + 2)
    · match i, hi with
      | 0, _ => exact (ShortComplex.exact_iff_mono _ rfl).2 ‹Mono ι›
      | 1, _ =>
        have w : ι ≫ cokernel.π ι ≫ e.hom ≫ T.map' 1 2 = 0 := by
          rw [cokernel.condition_assoc, zero_comp]
        change (ShortComplex.mk ι (cokernel.π ι ≫ e.hom ≫ T.map' 1 2) w).Exact
        have := hT.mono_map'_one_two (by omega)
        exact (ShortComplex.exact_iff_of_epi_of_isIso_of_mono
          (S₁ := ShortComplex.mk ι (cokernel.π ι) (cokernel.condition ι))
          (S₂ := ShortComplex.mk ι (cokernel.π ι ≫ e.hom ≫ T.map' 1 2) w)
          { τ₁ := 𝟙 X, τ₂ := 𝟙 I, τ₃ := e.hom ≫ T.map' 1 2, comm₁₂ := by simp,
            comm₂₃ := by simp }).1
          (ShortComplex.exact_of_g_is_cokernel _ (cokernelIsCokernel ι))
      | 2, _ =>
        have w : (cokernel.π ι ≫ e.hom ≫ T.map' 1 2) ≫ T.map' 2 3 = 0 := by
          rw [Category.assoc, Category.assoc, hT.exact.toIsComplex.zero' 1 2 3, comp_zero,
            comp_zero]
        change (ShortComplex.mk (cokernel.π ι ≫ e.hom ≫ T.map' 1 2) (T.map' 2 3) w).Exact
        exact (ShortComplex.exact_iff_of_epi_of_isIso_of_mono
          (S₁ := ShortComplex.mk (cokernel.π ι ≫ e.hom ≫ T.map' 1 2) (T.map' 2 3) w)
          (S₂ := ShortComplex.mk (T.map' 1 2) (T.map' 2 3) (hT.exact.toIsComplex.zero' 1 2 3))
          { τ₁ := cokernel.π ι ≫ e.hom, τ₂ := 𝟙 _, τ₃ := 𝟙 _, comm₁₂ := by simp,
            comm₂₃ := by simp }).2 (hT.exact.exact' 1 2 3)
      | k + 3, _ => exact hT.exact.exact (k + 2)

/-- An embedding into an injective object followed by an injective coresolution of its cokernel
is an injective coresolution. -/
theorem IsInjectiveCoresolution.coresolutionCons [Mono ι] [Injective I]
    (hT : T.IsInjectiveCoresolution) : (coresolutionCons ι T e).IsInjectiveCoresolution where
  toIsCoresolution := hT.toIsCoresolution.coresolutionCons
  injective i hi := by
    match i, hi with
    | 0, _ => exact ‹Injective I›
    | k + 1, _ => exact hT.injective k (by omega)

omit [Abelian C] in
/-- Essentiality only depends on the morphism. -/
private theorem isEssentialMono_congr {A B : C} {f f' : A ⟶ B} (h : f = f') :
    IsEssentialMono f ↔ IsEssentialMono f' := by
  subst h
  rfl

/-- `cokernel.desc f g w` is an essential monomorphism exactly when `cokernel.desc f' g' w'` is,
for `f = f'` and `g = g'`. -/
private theorem isEssentialMono_cokernelDesc_congr {A B D : C} {f f' : A ⟶ B} {g g' : B ⟶ D}
    (hf : f = f') (hg : g = g') (w : f ≫ g = 0) (w' : f' ≫ g' = 0) :
    IsEssentialMono (cokernel.desc f g w) ↔ IsEssentialMono (cokernel.desc f' g' w') := by
  subst hf hg
  rfl

/-- Dividing out by a zero morphism does not change essentiality. -/
private theorem isEssentialMono_cokernelDesc_of_eq_zero {A B D : C} {f : A ⟶ B} (hf : f = 0)
    {g : B ⟶ D} (w : f ≫ g = 0) : IsEssentialMono (cokernel.desc f g w) ↔ IsEssentialMono g := by
  subst hf
  have : cokernel.desc (0 : A ⟶ B) g w = inv (cokernel.π (0 : A ⟶ B)) ≫ g := by
    simp [← cancel_epi (cokernel.π (0 : A ⟶ B))]
  rw [this]
  exact isEssentialMono_iso_comp_iff (asIso (inv (cokernel.π (0 : A ⟶ B)))) g

/-- Precomposing with an epimorphism does not change the essentiality of the induced map out of
the cokernel. -/
private theorem isEssentialMono_cokernelDesc_epi_comp {A A' B D : C} (p : A' ⟶ A) [Epi p]
    (f : A ⟶ B) {g : B ⟶ D} (w : (p ≫ f) ≫ g = 0) (w' : f ≫ g = 0) :
    IsEssentialMono (cokernel.desc (p ≫ f) g w) ↔ IsEssentialMono (cokernel.desc f g w') := by
  have : cokernel.desc (p ≫ f) g w = (cokernelEpiComp p f).hom ≫ cokernel.desc f g w' := by
    ext
    simp [cokernelEpiComp]
  rw [this]
  exact isEssentialMono_iso_comp_iff _ _

/-- An injective envelope followed by a minimal injective coresolution of its cokernel is a
minimal injective coresolution. -/
theorem IsMinimalInjectiveCoresolution.coresolutionCons [Injective I] (hι : IsEssentialMono ι)
    (hT : T.IsMinimalInjectiveCoresolution) :
    (coresolutionCons ι T e).IsMinimalInjectiveCoresolution where
  toIsInjectiveCoresolution := by
    have := hι.mono
    exact hT.toIsInjectiveCoresolution.coresolutionCons
  isEssentialMono i hi := by
    match i, hi with
    | 0, _ =>
      refine (isEssentialMono_cokernelDesc_of_eq_zero (coresolutionCons_map'_zero_one ι T e)
        _).2 ?_
      exact (isEssentialMono_congr (coresolutionCons_map'_one_two ι T e)).2 hι
    | 1, _ =>
      have h₀ : IsEssentialMono (cokernel.desc (T.map' 0 1) (T.map' 1 2)
          (hT.exact.toIsComplex.zero' 0 1 2)) := hT.isEssentialMono 0 (by omega)
      rw [isEssentialMono_cokernelDesc_of_eq_zero (hT.isZero_left.eq_of_src _ _)] at h₀
      have w : ι ≫ cokernel.π ι ≫ e.hom ≫ T.map' 1 2 = 0 := by
        rw [cokernel.condition_assoc, zero_comp]
      refine (isEssentialMono_cokernelDesc_congr (coresolutionCons_map'_one_two ι T e)
        (coresolutionCons_map'_two_three ι T e (by omega)) _ w).2 ?_
      have : cokernel.desc ι (cokernel.π ι ≫ e.hom ≫ T.map' 1 2) w = e.hom ≫ T.map' 1 2 := by
        ext
        simp
      refine (isEssentialMono_congr this).2 ?_
      rw [isEssentialMono_iso_comp_iff]
      exact h₀
    | 2, _ =>
      have h₁₂₃ := hT.exact.toIsComplex.zero' 1 2 3
      have w : (cokernel.π ι ≫ e.hom ≫ T.map' 1 2) ≫ T.map' 2 3 = 0 := by
        rw [Category.assoc, Category.assoc, h₁₂₃, comp_zero, comp_zero]
      have w' : ((cokernel.π ι ≫ e.hom) ≫ T.map' 1 2) ≫ T.map' 2 3 = 0 := by
        rw [Category.assoc, h₁₂₃, comp_zero]
      refine (isEssentialMono_cokernelDesc_congr (coresolutionCons_map'_two_three ι T e (by omega))
        (coresolutionCons_map'_add_three ι T e 0 (by omega)) _ w).2 ?_
      refine (isEssentialMono_cokernelDesc_congr (Category.assoc _ _ _).symm rfl w w').2 ?_
      exact (isEssentialMono_cokernelDesc_epi_comp _ _ w' h₁₂₃).2 (hT.isEssentialMono 1 (by omega))
    | k + 3, _ =>
      exact (isEssentialMono_cokernelDesc_congr (coresolutionCons_map'_add_three ι T e k (by omega))
        (coresolutionCons_map'_add_three ι T e (k + 1) (by omega)) _
        (hT.exact.toIsComplex.zero' (k + 2) (k + 3) (k + 4))).2
        (hT.isEssentialMono (k + 2) (by omega))

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
theorem IsCoresolution.tail_obj_one : hS.tail.obj' 1 = S.cosyzygy 1 := rfl

@[simp]
theorem IsCoresolution.tail_obj_add_two (k : ℕ) (hk : k + 2 ≤ n + 1) :
    hS.tail.obj' (k + 2) = S.obj' (k + 3) := rfl

/-- The tail of a coresolution is a coresolution. -/
theorem IsCoresolution.isCoresolution_tail : hS.tail.IsCoresolution where
  isZero_left := isZero_zero C
  exact := by
    refine exact_mkOfObjOfMapSucc _ _ (fun i hi ↦ ?_) (fun i hi ↦ ?_)
    · match i, hi with
      | 0, _ => exact zero_comp
      | 1, h =>
        change hS.cosyzygyι 1 ≫ S.map' 3 4 = 0
        rw [← cancel_epi (cokernel.π (S.map' 1 2)), comp_zero]
        exact (hS.π_cosyzygyι_assoc 1 (by omega) _).trans (hS.exact.toIsComplex.zero' 2 3 4)
      | k + 2, _ => exact hS.exact.toIsComplex.zero (k + 3)
    · match i, hi with
      | 0, _ =>
        have := hS.mono_cosyzygyι 1 (by omega)
        exact (ShortComplex.exact_iff_mono _ rfl).2 this
      | 1, h =>
        have w : hS.cosyzygyι 1 ≫ S.map' 3 4 = 0 := by
          rw [← cancel_epi (cokernel.π (S.map' 1 2)), comp_zero]
          exact (hS.π_cosyzygyι_assoc 1 (by omega) _).trans (hS.exact.toIsComplex.zero' 2 3 4)
        change (ShortComplex.mk (hS.cosyzygyι 1) (S.map' 3 4) w).Exact
        exact (ShortComplex.exact_iff_of_epi_of_isIso_of_mono
          (S₁ := ShortComplex.mk (S.map' 2 3) (S.map' 3 4) (hS.exact.toIsComplex.zero' 2 3 4))
          (S₂ := ShortComplex.mk (hS.cosyzygyι 1) (S.map' 3 4) w)
          { τ₁ := cokernel.π _, τ₂ := 𝟙 _, τ₃ := 𝟙 _,
            comm₁₂ := by rw [Category.comp_id]; exact hS.π_cosyzygyι 1 (by omega),
            comm₂₃ := by simp }).1 (hS.exact.exact' 2 3 4)
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

/-- Every object has a coresolution with no terms, `0 → X`. -/
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

/-- Dropping the last term of a coresolution with `n + 1` terms leaves one with `n` terms. -/
theorem HasCoresolution.of_succ {X : C} {n : ℕ} (h : HasCoresolution P X (n + 1)) :
    HasCoresolution P X n := by
  obtain ⟨S, hS, e, hP⟩ := h
  exact ⟨S.δlast, ⟨hS.exact.δlast, hS.isZero_left⟩, e, fun i hi ↦ hP i (by omega)⟩

theorem HasCoresolution.of_le {X : C} {m n : ℕ} (h : HasCoresolution P X n) (hmn : m ≤ n) :
    HasCoresolution P X m := by
  induction hmn with
  | refl => exact h
  | step _ ih => exact ih h.of_succ

namespace ComposableArrows

namespace IsMinimalInjectiveCoresolution

variable {E S : ComposableArrows C (n + 1)}

/-- The cosyzygies of a minimal injective coresolution of a retract of `X` are retracts of the
cosyzygies of any injective coresolution of `X`. -/
theorem nonempty_retract_cosyzygy (hE : E.IsMinimalInjectiveCoresolution)
    (hS : S.IsInjectiveCoresolution) (r : Retract (E.obj' 1) (S.obj' 1)) :
    ∀ (i : ℕ) (hi : i ≤ n), Nonempty (Retract (E.cosyzygy i) (S.cosyzygy i))
  | 0, _ => ⟨(Retract.ofIso hE.cosyzygyZeroIso).trans
      (r.trans (Retract.ofIso hS.cosyzygyZeroIso.symm))⟩
  | i + 1, hi => by
    obtain ⟨r'⟩ := nonempty_retract_cosyzygy hE hS r i (by omega)
    have := hE.injective i (by omega)
    have := hS.injective i (by omega)
    have := hS.mono_cosyzygyι i (by omega)
    obtain ⟨-, ⟨r''⟩⟩ :=
      (hE.isEssentialMono_cosyzygyι i (by omega)).nonempty_retract_and_nonempty_retract_cokernel
      (j := hS.cosyzygyι i _) r'
    exact ⟨(Retract.ofIso (hE.cosyzygySuccIso i)).trans
      (r''.trans (Retract.ofIso (hS.cosyzygySuccIso i).symm))⟩

/-- **A minimal injective coresolution is a termwise retract of any injective coresolution.** If
`E` is a minimal injective coresolution of a retract of `S.obj' 1` and `S` is an injective
coresolution, both with `n` terms, then every term of `E` is a retract of the corresponding term
of `S`. -/
theorem nonempty_retract (hE : E.IsMinimalInjectiveCoresolution)
    (hS : S.IsInjectiveCoresolution) (r : Retract (E.obj' 1) (S.obj' 1)) (i : ℕ) (hi : i < n) :
    Nonempty (Retract (E.obj' (i + 2)) (S.obj' (i + 2))) := by
  obtain ⟨r'⟩ := hE.nonempty_retract_cosyzygy hS r i (by omega)
  have := hE.injective i hi
  have := hS.injective i hi
  have := hS.mono_cosyzygyι i hi
  exact ((hE.isEssentialMono_cosyzygyι i hi).nonempty_retract_and_nonempty_retract_cokernel
    (j := hS.cosyzygyι i hi) r').1

/-- The inductive step of the uniqueness of minimal injective coresolutions: an isomorphism of
`i`-th cosyzygies extends to an isomorphism of `i`-th terms. -/
private theorem exists_iso_term (hE : E.IsMinimalInjectiveCoresolution)
    (hS : S.IsMinimalInjectiveCoresolution) (i : ℕ) (hi : i < n)
    (a : E.cosyzygy i ≅ S.cosyzygy i) :
    ∃ b : E.obj' (i + 2) ≅ S.obj' (i + 2), hE.cosyzygyι i ≫ b.hom = a.hom ≫ hS.cosyzygyι i := by
  have := hE.injective i hi
  have := hS.injective i hi
  exact (hE.isEssentialMono_cosyzygyι i hi).exists_iso
    ((isEssentialMono_iso_comp_iff a _).2 (hS.isEssentialMono_cosyzygyι i hi))

/-- The cosyzygies of two minimal injective coresolutions of the same object are isomorphic. -/
theorem nonempty_iso_cosyzygy (hE : E.IsMinimalInjectiveCoresolution)
    (hS : S.IsMinimalInjectiveCoresolution) (e : E.obj' 1 ≅ S.obj' 1) :
    ∀ (i : ℕ) (hi : i ≤ n), Nonempty (E.cosyzygy i ≅ S.cosyzygy i)
  | 0, _ => ⟨hE.cosyzygyZeroIso ≪≫ e ≪≫ hS.cosyzygyZeroIso.symm⟩
  | i + 1, hi => by
    obtain ⟨a⟩ := nonempty_iso_cosyzygy hE hS e i (by omega)
    obtain ⟨b, hb⟩ := exists_iso_term hE hS i (by omega) a
    exact ⟨hE.cosyzygySuccIso i ≪≫ cokernel.mapIso _ _ a b hb ≪≫ (hS.cosyzygySuccIso i).symm⟩

/-- **Minimal injective coresolutions are unique.** Two minimal injective coresolutions with `n`
terms of the same object have isomorphic terms. -/
theorem nonempty_iso (hE : E.IsMinimalInjectiveCoresolution)
    (hS : S.IsMinimalInjectiveCoresolution) (e : E.obj' 1 ≅ S.obj' 1) (i : ℕ) (hi : i < n) :
    Nonempty (E.obj' (i + 2) ≅ S.obj' (i + 2)) := by
  obtain ⟨a⟩ := hE.nonempty_iso_cosyzygy hS e i (by omega)
  obtain ⟨b, -⟩ := exists_iso_term hE hS i hi a
  exact ⟨b⟩

end IsMinimalInjectiveCoresolution

/-- **Existence of minimal injective coresolutions.** Let `Q` be a property of objects such that
every object satisfying `Q` has an injective envelope whose target and cokernel satisfy `Q`. Then
every object satisfying `Q` has a minimal injective coresolution with `n` terms, all of which
satisfy `Q`. Taking `Q` to hold everywhere, this says that if every object has an injective
envelope, then every object has minimal injective coresolutions of every length. -/
theorem exists_isMinimalInjectiveCoresolution {Q : ObjectProperty C}
    (hQ : ∀ X, Q X → ∃ (I : C) (ι : X ⟶ I), Injective I ∧ IsEssentialMono ι ∧ Q I ∧
      Q (cokernel ι))
    (n : ℕ) {X : C} (hX : Q X) :
    ∃ S : ComposableArrows C (n + 1), S.IsMinimalInjectiveCoresolution ∧
      Nonempty (S.obj' 1 ≅ X) ∧ ∀ (i : ℕ) (hi : i < n), Q (S.obj' (i + 2)) := by
  induction n generalizing X with
  | zero =>
    exact ⟨mk₁ (0 : 0 ⟶ X),
      { exact := (mk₁ _).exact₁
        isZero_left := isZero_zero C
        injective := fun _ hi ↦ absurd hi (Nat.not_lt_zero _)
        isEssentialMono := fun _ hi ↦ absurd hi (Nat.not_lt_zero _) },
      ⟨Iso.refl _⟩, fun _ hi ↦ absurd hi (Nat.not_lt_zero _)⟩
  | succ n ih =>
    obtain ⟨I, ι, hI, hι, hQI, hQc⟩ := hQ X hX
    obtain ⟨T, hT, ⟨e⟩, hQT⟩ := ih hQc
    exact ⟨coresolutionCons ι T e.symm, hT.coresolutionCons hι, ⟨Iso.refl _⟩,
      fun i hi ↦ match i, hi with
        | 0, _ => hQI
        | k + 1, _ => hQT k (by omega)⟩

end ComposableArrows

end CategoryTheory
