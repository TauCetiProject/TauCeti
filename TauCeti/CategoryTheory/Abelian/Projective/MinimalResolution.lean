/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Homology.ExactSequence
public import Mathlib.CategoryTheory.ObjectProperty.ClosedUnderIsomorphisms
public import TauCeti.CategoryTheory.Abelian.Projective.Cover

/-!
# Resolutions with `n` terms and minimal projective resolutions

In an abelian category `C`, a *resolution with `n` terms* of an object `X` is an exact sequence
`Pₙ₋₁ → ⋯ → P₁ → P₀ → X → 0`, exact at `X` and at `P₀, …, Pₙ₋₂`, but not necessarily at the last
term. It is written as `S : ComposableArrows C (n + 1)` with `S.obj' (n + 1)` a zero object and
`S.obj' n = X` (`CategoryTheory.ComposableArrows.IsResolution`); the terms are `S.obj' j` for
`j < n`, so that `S.obj' j = Pₙ₋₁₋ⱼ`. Exactness at `X` says that `P₀ ⟶ X` is an epimorphism. Unlike
Mathlib's `CategoryTheory.ProjectiveResolution`, which is an infinite resolution, these truncated
resolutions need no enough projectives. This is the dual of
`TauCeti/CategoryTheory/Abelian/Injective/MinimalCoresolution.lean`.

The *syzygy at position `j`* of `S` is `kernel (S.map' j (j + 1))`
(`CategoryTheory.ComposableArrows.syzygy`): the one at position `n` is `X`, and the one at position
`j` is the kernel of the epimorphism `S.obj' j ⟶ syzygy (j + 1)` induced by `S`
(`CategoryTheory.ComposableArrows.IsResolution.syzygyπ`). A resolution is **minimal projective**
when its terms are projective and each `S.obj' j ⟶ syzygy (j + 1)` is a projective cover, that is,
an essential epimorphism (`TauCeti.IsEssentialEpi`).

A minimal projective resolution of a retract of `X` is a termwise retract of every projective
resolution of `X`
(`CategoryTheory.ComposableArrows.IsMinimalProjectiveResolution.nonempty_retract`), by induction
on the syzygies through `TauCeti.IsEssentialEpi.nonempty_retract_and_nonempty_retract_kernel`.
Two minimal projective
resolutions of the same object have isomorphic terms
(`CategoryTheory.ComposableArrows.IsMinimalProjectiveResolution.nonempty_iso`), and a minimal
projective resolution with `n` terms exists as soon as the first `n` syzygies have projective
covers (`CategoryTheory.ComposableArrows.exists_isMinimalProjectiveResolution`); it is built by
covering the last syzygy and prepending the cover (`CategoryTheory.ComposableArrows.precomp`).

## Main definitions

* `CategoryTheory.ComposableArrows.IsResolution`, `IsProjectiveResolution` and
  `IsMinimalProjectiveResolution`: resolutions with `n` terms, with projective terms, and minimal
  projective ones.
* `CategoryTheory.ComposableArrows.syzygy`: the syzygies of a resolution.

## Main results

* `CategoryTheory.ComposableArrows.IsMinimalProjectiveResolution.nonempty_retract`: a minimal
  projective resolution is a termwise retract of any projective resolution.
* `CategoryTheory.ComposableArrows.IsMinimalProjectiveResolution.nonempty_iso`: minimal projective
  resolutions are unique up to isomorphism of their terms.
* `CategoryTheory.ComposableArrows.exists_isMinimalProjectiveResolution`: existence, given
  projective covers.

## References

* I. Assem, D. Simson, A. Skowroński, *Elements of the Representation Theory of Associative
  Algebras, Vol. 1*, LMS Student Texts 65, CUP (2006), I.5.
* F. W. Anderson, K. R. Fuller, *Rings and Categories of Modules*, 2nd ed., Springer GTM 13
  (1992), §17.
-/

public section

universe v u

namespace CategoryTheory

open Limits TauCeti ZeroObject

variable {C : Type u} [Category.{v} C] [Abelian C]

namespace ComposableArrows

variable {n : ℕ}

/-- `S : ComposableArrows C (n + 1)` is a **resolution with `n` terms** of `S.obj' n`: the
sequence `S.obj' 0 → ⋯ → S.obj' n → S.obj' (n + 1)` is exact and ends at a zero object. The terms
are `S.obj' j` for `j < n`; there is no exactness condition at the first one. -/
structure IsResolution (S : ComposableArrows C (n + 1)) : Prop where
  /-- The sequence is exact. -/
  exact : S.Exact
  /-- The sequence ends at a zero object. -/
  isZero_right : IsZero S.right

/-- The **syzygy at position `j`** of `S : ComposableArrows C (n + 1)`, the kernel of
`S.map' j (j + 1)`. For a resolution of `X`, the syzygy at position `n` is `X`
(`CategoryTheory.ComposableArrows.IsResolution.syzygyLastIso`). -/
noncomputable abbrev syzygy (S : ComposableArrows C (n + 1)) (j : ℕ) (hj : j ≤ n := by valid) :
    C :=
  kernel (S.map' j (j + 1))

namespace IsResolution

variable {S : ComposableArrows C (n + 1)} (hS : S.IsResolution)
include hS

/-- The epimorphism from the term `S.obj' j` onto the syzygy at position `j + 1`. -/
noncomputable def syzygyπ (j : ℕ) (hj : j < n := by valid) : S.obj' j ⟶ S.syzygy (j + 1) :=
  kernel.lift (S.map' (j + 1) (j + 2)) (S.map' j (j + 1)) (hS.exact.toIsComplex.zero j)

@[reassoc (attr := simp)]
theorem syzygyπ_ι (j : ℕ) (hj : j < n := by valid) :
    hS.syzygyπ j ≫ kernel.ι (S.map' (j + 1) (j + 2)) = S.map' j (j + 1) :=
  kernel.lift_ι _ _ _

instance epi_syzygyπ (j : ℕ) (hj : j < n) : Epi (hS.syzygyπ j) :=
  (hS.exact.exact j).epi_kernelLift

/-- The syzygy at position `n` of a resolution of `X` is `X`. -/
noncomputable def syzygyLastIso : S.syzygy n ≅ S.obj' n :=
  kernelIsoOfEq (hS.isZero_right.eq_of_tgt _ 0) ≪≫ kernelZeroIsoSource

/-- The syzygy at position `j` is the kernel of the projection onto the next one. -/
noncomputable def syzygyIsoKernel (j : ℕ) (hj : j < n := by valid) :
    S.syzygy j ≅ kernel (hS.syzygyπ j) :=
  kernelIsoOfEq (hS.syzygyπ_ι j).symm ≪≫ kernelCompMono _ _

end IsResolution

/-- A **projective resolution with `n` terms**: a resolution whose terms `S.obj' j`, `j < n`, are
projective. -/
structure IsProjectiveResolution (S : ComposableArrows C (n + 1)) : Prop
    extends S.IsResolution where
  /-- The terms are projective. -/
  projective (j : ℕ) (hj : j < n) : Projective (S.obj' j)

/-- A **minimal projective resolution with `n` terms**: a projective resolution in which every term
maps onto the next syzygy by a projective cover, that is, an essential epimorphism. -/
structure IsMinimalProjectiveResolution (S : ComposableArrows C (n + 1)) : Prop
    extends S.IsProjectiveResolution where
  /-- Each term maps onto the next syzygy by an essential epimorphism. -/
  isEssentialEpi (j : ℕ) (hj : j < n) :
    IsEssentialEpi (kernel.lift (S.map' (j + 1) (j + 2)) (S.map' j (j + 1))
      (exact.toIsComplex.zero j))

omit [Abelian C] in
/-- Essentiality only depends on the morphism. -/
private theorem isEssentialEpi_congr {A B : C} {f f' : A ⟶ B} (h : f = f') :
    IsEssentialEpi f ↔ IsEssentialEpi f' := by
  subst h
  rfl

namespace IsMinimalProjectiveResolution

variable {E S : ComposableArrows C (n + 1)}

theorem isEssentialEpi_syzygyπ (hE : E.IsMinimalProjectiveResolution) (j : ℕ) (hj : j < n) :
    IsEssentialEpi (hE.toIsResolution.syzygyπ j) :=
  hE.isEssentialEpi j hj

/-- The syzygies of a minimal projective resolution of a retract of `X` are retracts of the
syzygies of any projective resolution of `X`, counted from the right. -/
private theorem nonempty_retract_syzygy (hE : E.IsMinimalProjectiveResolution)
    (hS : S.IsProjectiveResolution) (r : Retract (E.obj' n) (S.obj' n)) :
    ∀ (k j : ℕ) (hj : j + k = n), Nonempty (Retract (E.syzygy j) (S.syzygy j))
  | 0, j, hj => by
    obtain rfl : j = n := by omega
    exact ⟨(Retract.ofIso hE.syzygyLastIso).trans (r.trans (Retract.ofIso hS.syzygyLastIso.symm))⟩
  | k + 1, j, hj => by
    obtain ⟨r'⟩ := nonempty_retract_syzygy hE hS r k (j + 1) (by omega)
    have := hE.projective j (by omega)
    have := hS.projective j (by omega)
    have := hS.epi_syzygyπ j (by omega)
    obtain ⟨-, ⟨r''⟩⟩ :=
      (hE.isEssentialEpi_syzygyπ j (by omega)).nonempty_retract_and_nonempty_retract_kernel
      (q := hS.syzygyπ j _) r'
    exact ⟨(Retract.ofIso (hE.syzygyIsoKernel j)).trans
      (r''.trans (Retract.ofIso (hS.syzygyIsoKernel j).symm))⟩

/-- **A minimal projective resolution is a termwise retract of any projective resolution.** If
`E` is a minimal projective resolution of a retract of `S.obj' n` and `S` is a projective
resolution, both with `n` terms, then every term of `E` is a retract of the corresponding term of
`S`. -/
theorem nonempty_retract (hE : E.IsMinimalProjectiveResolution)
    (hS : S.IsProjectiveResolution) (r : Retract (E.obj' n) (S.obj' n)) (j : ℕ) (hj : j < n) :
    Nonempty (Retract (E.obj' j) (S.obj' j)) := by
  obtain ⟨r'⟩ := nonempty_retract_syzygy hE hS r (n - (j + 1)) (j + 1) (by omega)
  have := hE.projective j hj
  have := hS.projective j hj
  have := hS.epi_syzygyπ j hj
  exact ((hE.isEssentialEpi_syzygyπ j hj).nonempty_retract_and_nonempty_retract_kernel
    (q := hS.syzygyπ j hj) r').1

/-- The inductive step of the uniqueness of minimal projective resolutions: an isomorphism of
syzygies at position `j + 1` lifts to an isomorphism of the terms at position `j`. -/
private theorem exists_iso_term (hE : E.IsMinimalProjectiveResolution)
    (hS : S.IsMinimalProjectiveResolution) (j : ℕ) (hj : j < n)
    (a : E.syzygy (j + 1) ≅ S.syzygy (j + 1)) :
    ∃ b : E.obj' j ≅ S.obj' j, hE.syzygyπ j ≫ a.hom = b.hom ≫ hS.syzygyπ j := by
  have := hE.projective j hj
  have := hS.projective j hj
  obtain ⟨b, hb⟩ :=
    ((isEssentialEpi_comp_iso_iff _ a).2 (hE.isEssentialEpi_syzygyπ j hj)).exists_iso
      (hS.isEssentialEpi_syzygyπ j hj)
  exact ⟨b, hb.symm⟩

private theorem nonempty_iso_syzygy (hE : E.IsMinimalProjectiveResolution)
    (hS : S.IsMinimalProjectiveResolution) (e : E.obj' n ≅ S.obj' n) :
    ∀ (k j : ℕ) (hj : j + k = n), Nonempty (E.syzygy j ≅ S.syzygy j)
  | 0, j, hj => by
    obtain rfl : j = n := by omega
    exact ⟨hE.syzygyLastIso ≪≫ e ≪≫ hS.syzygyLastIso.symm⟩
  | k + 1, j, hj => by
    obtain ⟨a⟩ := nonempty_iso_syzygy hE hS e k (j + 1) (by omega)
    obtain ⟨b, hb⟩ := exists_iso_term hE hS j (by omega) a
    exact ⟨hE.syzygyIsoKernel j ≪≫ kernel.mapIso _ _ b a hb ≪≫ (hS.syzygyIsoKernel j).symm⟩

/-- **Minimal projective resolutions are unique.** Two minimal projective resolutions with `n`
terms of the same object have isomorphic terms. -/
theorem nonempty_iso (hE : E.IsMinimalProjectiveResolution)
    (hS : S.IsMinimalProjectiveResolution) (e : E.obj' n ≅ S.obj' n) (j : ℕ) (hj : j < n) :
    Nonempty (E.obj' j ≅ S.obj' j) := by
  obtain ⟨a⟩ := nonempty_iso_syzygy hE hS e (n - (j + 1)) (j + 1) (by omega)
  obtain ⟨b, -⟩ := exists_iso_term hE hS j hj a
  exact ⟨b⟩

end IsMinimalProjectiveResolution

/-- **Existence of minimal projective resolutions.** Let `Q` be an isomorphism-closed property of
objects such that every object satisfying `Q` has a projective cover whose source and kernel
satisfy `Q`. Then every object satisfying `Q` has a minimal projective resolution with `n` terms,
all of which satisfy `Q`, and whose syzygy at position `0` satisfies `Q`. -/
theorem exists_isMinimalProjectiveResolution {Q : ObjectProperty C}
    [Q.IsClosedUnderIsomorphisms]
    (hQ : ∀ X, Q X → ∃ (P : C) (π : P ⟶ X), Projective P ∧ IsEssentialEpi π ∧ Q P ∧
      Q (kernel π))
    (n : ℕ) {X : C} (hX : Q X) :
    ∃ S : ComposableArrows C (n + 1), S.IsMinimalProjectiveResolution ∧
      Nonempty (S.obj' n ≅ X) ∧ (∀ (j : ℕ) (hj : j < n), Q (S.obj' j)) ∧ Q (S.syzygy 0) := by
  induction n with
  | zero =>
    refine ⟨mk₁ (0 : X ⟶ 0),
      { exact := (mk₁ _).exact₁
        isZero_right := isZero_zero C
        projective := fun _ hj ↦ absurd hj (Nat.not_lt_zero _)
        isEssentialEpi := fun _ hj ↦ absurd hj (Nat.not_lt_zero _) },
      ⟨Iso.refl _⟩, fun _ hj ↦ absurd hj (Nat.not_lt_zero _), ?_⟩
    exact Q.prop_of_iso kernelZeroIsoSource.symm hX
  | succ n ih =>
    obtain ⟨S, hS, ⟨e⟩, hQS, hQ₀⟩ := ih
    obtain ⟨P, π, hP, hπ, hQP, hQπ⟩ := hQ _ hQ₀
    have := hπ.epi
    let S' : ComposableArrows C (n + 2) := S.precomp (π ≫ kernel.ι (S.map' 0 1))
    have w : (π ≫ kernel.ι _) ≫ S.map' 0 1 = 0 := by
      rw [Category.assoc, kernel.condition, comp_zero]
    have hexact : S'.Exact := by
      refine exact_of_δ₀ (exact₂_mk _ w ?_) hS.exact
      have h : (ShortComplex.mk (kernel.ι (S.map' 0 1)) (S.map' 0 1) (kernel.condition _)).Exact :=
        ShortComplex.exact_of_f_is_kernel _ (kernelIsKernel _)
      exact (ShortComplex.exact_iff_of_epi_of_isIso_of_mono
        (S₁ := ShortComplex.mk _ _ w)
        (S₂ := ShortComplex.mk (kernel.ι _) _ (kernel.condition _))
        { τ₁ := π, τ₂ := 𝟙 _, τ₃ := 𝟙 _, comm₁₂ := by rw [Category.comp_id],
          comm₂₃ := by simp }).2 h
    have hmin : S'.IsMinimalProjectiveResolution :=
      { exact := hexact
        isZero_right := hS.isZero_right
        projective := fun j hj ↦ match j, hj with
          | 0, _ => hP
          | k + 1, _ => hS.projective k (by omega)
        isEssentialEpi := fun j hj ↦ match j, hj with
          | 0, _ => by
            have : kernel.lift (S'.map' 1 2) (S'.map' 0 1) (hexact.toIsComplex.zero' 0 1 2) =
                π := by
              refine (cancel_mono (kernel.ι _)).1 ?_
              exact kernel.lift_ι _ _ _
            exact (isEssentialEpi_congr this).2 hπ
          | k + 1, _ => hS.isEssentialEpi k (by omega) }
    refine ⟨S', hmin, ⟨e⟩, ?_, ?_⟩
    · intro j hj
      match j, hj with
      | 0, _ => exact hQP
      | k + 1, _ => exact hQS k (by omega)
    · exact Q.prop_of_iso (kernelCompMono π (kernel.ι _)).symm hQπ

end ComposableArrows

end CategoryTheory
