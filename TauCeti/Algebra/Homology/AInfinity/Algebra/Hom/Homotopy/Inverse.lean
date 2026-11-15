/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.AInfinity.Algebra.Hom.Homotopy.Trans
public import TauCeti.Algebra.Homology.AInfinity.Algebra.Hom.Iso
import TauCeti.Algebra.Homology.Contraction.Linear.Homology

/-!
# Homotopy inverses of morphisms of A-infinity algebras

An `A∞` morphism `f : AA ⟶ BB` is a *homotopy equivalence* (`TauCeti.AInfinityHom.IsHomotopyEquiv`)
when there exists an `A∞` morphism `g : BB ⟶ AA` such that `g ∘ f` and `f ∘ g` are homotopic to the
respective identities.

Over an arbitrary commutative ring `R`, without any field or splitting assumption on the underlying
graded modules, `f` is an `A∞` homotopy equivalence if and only if its arity-one component
`f.linearPart : A →ₗ[R] B` admits a graded chain-homotopy inverse
(`TauCeti.AInfinityHom.isHomotopyEquiv_iff_nonempty_linearHomotopyInverse`).

Given chain-homotopy inverse data `c : f.LinearHomotopyInverse` with `inv : B →ₗ[R] A` and chain
homotopies `homotopyLeft` and `homotopyRight`, the construction proceeds in three steps:

1. **Vogt normalization** (`vogtHomotopyLeft`, `vogtTheta`): replacing `homotopyLeft` by
   `h_A' = h_A - inv ∘ (f₁ ∘ h_A - h_B ∘ f₁)` preserves `1 - inv ∘ f₁ = d_A ∘ h_A' + h_A' ∘ d_A`
   and upgrades `(h_A', h_B)` to a coherent chain-homotopy equivalence with coherence witness
   `θ = h_B ∘ (f₁ ∘ h_A - h_B ∘ f₁)` satisfying `f₁ ∘ h_A' - h_B ∘ f₁ = d_B ∘ θ - θ ∘ d_A`.
2. **Simultaneous inductive obstruction killing along the bar filtration**: at stage `n`, if a
   degree-`0` Taylor map `γ` and degree-`(-1)` Taylor map `η` satisfy the morphism equation
   `E = b_A ∘ G - G ∘ b_B = 0` and right-homotopy equation
   `R = (1 - F ∘ G) - (b_B ∘ H + H ∘ b_B) = 0` on words of length at most `n`, then on words of
   length at most `n + 1` both `E` and `R` land in single letters (`Φ = -π ∘ E`, `Ψ = π ∘ R`) and
   satisfy `Φ ∘ b_B^(1) = -d_A ∘ Φ` and `Ψ ∘ b_B^(1) = d_B ∘ Ψ - f₁ ∘ Φ`.  Adding
   `Δγ = inv ∘ Ψ + h_A' ∘ Φ` and `Δη = h_B ∘ Ψ - θ ∘ Φ` kills both obstructions on
   `filtration (n + 1)` without altering lower arities.  Starting at `n = 0` with `(0, 0)` yields a
   right homotopy inverse `g` with `g.linearPart = c.inv` and `Homotopy (id BB) (f.comp g)` with
   arity-one component `c.homotopyRight`.
3. **Two-sided upgrade**: applying the same right-inverse construction to `g` using `c.symm`
   produces `f'` with `Homotopy (id AA) (g.comp f')`; composing homotopies via
   `TauCeti.AInfinityHom.Homotopy.trans` and `TauCeti.AInfinityHom.Homotopy.symm` upgrades `g` to a
   two-sided homotopy inverse of `f`.

Over a field `K`, every graded complex contracts onto its homology
(`TauCeti.InternalGrading.homologyContraction`), so every quasi-isomorphism `hf : f.IsQuasiIso`
carries canonical chain-homotopy inverse data `hf.linearHomotopyInverse`, hence an `A∞` homotopy
inverse `hf.homotopyInverse` (`TauCeti.AInfinityHom.isHomotopyEquiv_iff_isQuasiIso`).

## Main definitions

* `TauCeti.AInfinityHom.IsHomotopyEquiv`: an `A∞` morphism admitting a two-sided homotopy inverse.
* `TauCeti.AInfinityHom.LinearHomotopyInverse`: graded chain-homotopy inverse data for
  `f.linearPart`.
* `TauCeti.AInfinityHom.homotopyInverse`: the `A∞` homotopy inverse lifting `LinearHomotopyInverse`.
* `TauCeti.AInfinityHom.IsQuasiIso.homotopyInverse`: over a field, an `A∞` homotopy inverse of a
  quasi-isomorphism.

## Main results

* `TauCeti.AInfinityHom.linearPart_homotopyInverse` and
  `TauCeti.AInfinityHom.linearHomotopy_idCompHomotopyInverseHomotopy`: the lifted homotopy inverse
  and right homotopy recover `c.inv` and `c.homotopyRight` in arity one.
* `TauCeti.AInfinityHom.isHomotopyEquiv_iff_nonempty_linearHomotopyInverse`: Whitehead theorem for
  `A∞` morphisms over a commutative ring.
* `TauCeti.AInfinityHom.IsQuasiIso.isHomotopyEquiv` and
  `TauCeti.AInfinityHom.isHomotopyEquiv_iff_isQuasiIso`: over a field, `A∞` homotopy equivalences
  are precisely the quasi-isomorphisms.

## References

* K. Lefèvre-Hasegawa, *Sur les A-infini catégories*, thèse de doctorat, Université Paris 7
  (2003), Theorem 1.3.1.2.
* B. Keller, *Introduction to A-infinity algebras and modules*, Section 3.7.
* R. M. Vogt, *A note on homotopy equivalences*, Proc. Amer. Math. Soc. 32 (1972), 627--629.
* A. Prouté, *A-infini-structures, modèle minimal de Baues-Lemaire et homologie des fibrations*,
  Reprints in Theory and Applications of Categories 21 (2011), Section 4.
-/

public section

open scoped TensorProduct

namespace TauCeti

universe uR uK uA uB uC

namespace AInfinityHom

open ReducedTensorWords

section CommRing

variable {R : Type uR} {A : Type uA} {B : Type uB} {C : Type uC}
  [CommRing R]
  [AddCommGroup A] [Module R A]
  [AddCommGroup B] [Module R B]
  [AddCommGroup C] [Module R C]
  {AA : AInfinityAlgebra R A} {BB : AInfinityAlgebra R B} {CC : AInfinityAlgebra R C}

/-! ### Homotopy equivalences of A-infinity algebras -/

/-- An `A∞` morphism `f : AA ⟶ BB` is a **homotopy equivalence** when there exists an `A∞` morphism
`g : BB ⟶ AA` such that `g ∘ f` and `f ∘ g` are homotopic to the respective identities. -/
def IsHomotopyEquiv (f : AInfinityHom AA BB) : Prop :=
  ∃ g : AInfinityHom BB AA,
    (g.comp f).Homotopic (AInfinityHom.id AA) ∧ (f.comp g).Homotopic (AInfinityHom.id BB)

/-- Unfolding lemma for `IsHomotopyEquiv`. -/
theorem isHomotopyEquiv_def (f : AInfinityHom AA BB) :
    f.IsHomotopyEquiv ↔
      ∃ g : AInfinityHom BB AA,
        (g.comp f).Homotopic (AInfinityHom.id AA) ∧ (f.comp g).Homotopic (AInfinityHom.id BB) :=
  Iff.rfl

/-- The identity `A∞` morphism is a homotopy equivalence. -/
@[simp]
theorem isHomotopyEquiv_id (AA : AInfinityAlgebra R A) : (AInfinityHom.id AA).IsHomotopyEquiv :=
  ⟨AInfinityHom.id AA, (Homotopy.refl _).copy (comp_id _).symm rfl |>.homotopic,
    (Homotopy.refl _).copy (comp_id _).symm rfl |>.homotopic⟩

/-- Homotopy equivalences of `A∞` algebras are closed under composition. -/
theorem IsHomotopyEquiv.comp {g : AInfinityHom BB CC} {f : AInfinityHom AA BB}
    (hg : g.IsHomotopyEquiv) (hf : f.IsHomotopyEquiv) : (g.comp f).IsHomotopyEquiv := by
  obtain ⟨g', hg₁, hg₂⟩ := hg
  obtain ⟨f', hf₁, hf₂⟩ := hf
  refine ⟨f'.comp g', ?_, ?_⟩
  · have h₁ : ((f'.comp g').comp (g.comp f)).Homotopic (f'.comp ((g'.comp g).comp f)) :=
      ((Homotopy.refl _).copy rfl (by rw [comp_assoc, comp_assoc])).homotopic
    have h₂ : (f'.comp ((g'.comp g).comp f)).Homotopic (f'.comp f) :=
      ((hg₁.compLeft f).trans ((Homotopy.refl _).copy (id_comp f).symm rfl).homotopic).compRight f'
    exact h₁.trans (h₂.trans hf₁)
  · have h₁ : ((g.comp f).comp (f'.comp g')).Homotopic (g.comp ((f.comp f').comp g')) :=
      ((Homotopy.refl _).copy rfl (by rw [comp_assoc, comp_assoc])).homotopic
    have h₂ : (g.comp ((f.comp f').comp g')).Homotopic (g.comp g') :=
      ((hf₂.compLeft g').trans ((Homotopy.refl _).copy (id_comp g').symm rfl).homotopic).compRight g
    exact h₁.trans (h₂.trans hg₂)

/-- Every strict `A∞` isomorphism is a homotopy equivalence. -/
theorem IsIso.isHomotopyEquiv {f : AInfinityHom AA BB} (hf : f.IsIso) : f.IsHomotopyEquiv := by
  obtain ⟨g, hg₁, hg₂⟩ := (isIso_def f).1 hf
  exact ⟨g, ((Homotopy.refl _).copy hg₁.symm rfl).homotopic,
    ((Homotopy.refl _).copy hg₂.symm rfl).homotopic⟩

/-- Every `A∞` homotopy equivalence is a quasi-isomorphism. -/
theorem IsHomotopyEquiv.isQuasiIso {f : AInfinityHom AA BB} (hf : f.IsHomotopyEquiv) :
    f.IsQuasiIso := by
  obtain ⟨g, hg₁, hg₂⟩ := hf
  rw [isQuasiIso_def]
  refine Function.bijective_iff_has_inverse.2 ⟨g.cohomologyMap, fun x ↦ ?_, fun y ↦ ?_⟩
  · have e := hg₁.cohomologyMap_eq
    rw [cohomologyMap_comp, cohomologyMap_id] at e
    exact DFunLike.congr_fun e x
  · have e := hg₂.cohomologyMap_eq
    rw [cohomologyMap_comp, cohomologyMap_id] at e
    exact DFunLike.congr_fun e y

/-- Homotopic `A∞` morphisms are homotopy equivalences together. -/
theorem Homotopic.isHomotopyEquiv_iff {f g : AInfinityHom AA BB} (h : f.Homotopic g) :
    f.IsHomotopyEquiv ↔ g.IsHomotopyEquiv := by
  refine ⟨fun ⟨k, hk₁, hk₂⟩ ↦ ⟨k, (h.symm.compRight k).trans hk₁, (h.symm.compLeft k).trans hk₂⟩,
    fun ⟨k, hk₁, hk₂⟩ ↦ ⟨k, (h.compRight k).trans hk₁, (h.compLeft k).trans hk₂⟩⟩

/-- Two out of three: if `f` and `g ∘ f` are homotopy equivalences, then so is `g`. -/
theorem IsHomotopyEquiv.of_precomp {g : AInfinityHom BB CC} {f : AInfinityHom AA BB}
    (hf : f.IsHomotopyEquiv) (hgf : (g.comp f).IsHomotopyEquiv) : g.IsHomotopyEquiv := by
  obtain ⟨f', hf₁, hf₂⟩ := hf
  have hf' : f'.IsHomotopyEquiv := ⟨f, hf₂, hf₁⟩
  have hcomp : ((g.comp f).comp f').Homotopic g :=
    (((Homotopy.refl _).copy rfl (comp_assoc g f f')).homotopic.trans
      (hf₂.compRight g)).trans (((Homotopy.refl _).copy (comp_id g).symm rfl).homotopic)
  exact hcomp.isHomotopyEquiv_iff.1 (hgf.comp hf')

/-- Two out of three: if `g` and `g ∘ f` are homotopy equivalences, then so is `f`. -/
theorem IsHomotopyEquiv.of_postcomp {g : AInfinityHom BB CC} {f : AInfinityHom AA BB}
    (hg : g.IsHomotopyEquiv) (hgf : (g.comp f).IsHomotopyEquiv) : f.IsHomotopyEquiv := by
  obtain ⟨g', hg₁, hg₂⟩ := hg
  have hg' : g'.IsHomotopyEquiv := ⟨g, hg₂, hg₁⟩
  have hcomp : (g'.comp (g.comp f)).Homotopic f :=
    (((Homotopy.refl _).copy rfl (comp_assoc g' g f).symm).homotopic.trans
      (hg₁.compLeft f)).trans (((Homotopy.refl _).copy (id_comp f).symm rfl).homotopic)
  exact hcomp.isHomotopyEquiv_iff.1 (hg'.comp hgf)

/-! ### Graded chain-homotopy inverse data and Vogt normalization -/

/-- Graded chain-homotopy inverse data for the arity-one component `f.linearPart` of an `A∞`
morphism `f : AA ⟶ BB`: a degree-zero chain map `inv : B →ₗ[R] A` together with degree-`(-1)` chain
homotopies `homotopyLeft` from `id_A` to `inv ∘ f.linearPart` and `homotopyRight` from `id_B` to
`f.linearPart ∘ inv`. -/
structure LinearHomotopyInverse (f : AInfinityHom AA BB) where
  /-- The chain-homotopy inverse of `f.linearPart`. -/
  inv : B →ₗ[R] A
  /-- The left chain homotopy: `1 - inv ∘ f₁ = d_A ∘ homotopyLeft + homotopyLeft ∘ d_A`. -/
  homotopyLeft : A →ₗ[R] A
  /-- The right chain homotopy: `1 - f₁ ∘ inv = d_B ∘ homotopyRight + homotopyRight ∘ d_B`. -/
  homotopyRight : B →ₗ[R] B
  /-- `inv` preserves internal degrees. -/
  isHomogeneous_inv : LinearMap.IsHomogeneous inv BB.grading.piece AA.grading.piece 0
  /-- `inv` is a chain map for the unary differentials. -/
  differential_comp_inv : AA.differential ∘ₗ inv = inv ∘ₗ BB.differential
  /-- `homotopyLeft` has internal degree `-1`. -/
  isHomogeneous_homotopyLeft :
    LinearMap.IsHomogeneous homotopyLeft AA.grading.piece AA.grading.piece (-1)
  /-- `homotopyLeft` is a chain homotopy from `1` to `inv ∘ f.linearPart`. -/
  id_sub_inv_comp_linearPart :
    LinearMap.id - inv ∘ₗ f.linearPart =
      AA.differential ∘ₗ homotopyLeft + homotopyLeft ∘ₗ AA.differential
  /-- `homotopyRight` has internal degree `-1`. -/
  isHomogeneous_homotopyRight :
    LinearMap.IsHomogeneous homotopyRight BB.grading.piece BB.grading.piece (-1)
  /-- `homotopyRight` is a chain homotopy from `1` to `f.linearPart ∘ inv`. -/
  id_sub_linearPart_comp_inv :
    LinearMap.id - f.linearPart ∘ₗ inv =
      BB.differential ∘ₗ homotopyRight + homotopyRight ∘ₗ BB.differential

private theorem differential_comp_linearPart (f : AInfinityHom AA BB) :
    BB.differential ∘ₗ f.linearPart = f.linearPart ∘ₗ AA.differential :=
  LinearMap.ext fun a ↦ by
    rw [LinearMap.comp_apply, LinearMap.comp_apply, AInfinityAlgebra.differential_apply,
      AInfinityAlgebra.differential_apply, f.linearPart_m_one]

/-- Extract graded chain-homotopy inverse data for `f.linearPart` from an `A∞` homotopy
equivalence. -/
theorem IsHomotopyEquiv.nonempty_linearHomotopyInverse {f : AInfinityHom AA BB}
    (hf : f.IsHomotopyEquiv) : Nonempty f.LinearHomotopyInverse := by
  obtain ⟨g, hg₁, hg₂⟩ := hf
  obtain ⟨h₁⟩ := (homotopic_def _ _).1 hg₁
  obtain ⟨h₂⟩ := (homotopic_def _ _).1 hg₂
  refine ⟨{
    inv := g.linearPart
    homotopyLeft := h₁.symm.linearHomotopy
    homotopyRight := h₂.symm.linearHomotopy
    isHomogeneous_inv := g.isHomogeneous_linearPart
    differential_comp_inv := differential_comp_linearPart g
    isHomogeneous_homotopyLeft := LinearMap.isHomogeneous_def.2 fun _ _ ha ↦
      h₁.symm.linearHomotopy_mem ha
    id_sub_inv_comp_linearPart := LinearMap.ext fun a ↦ by
      have e := h₁.symm.linearPart_sub_linearPart a
      simpa only [linearPart_id, linearPart_comp, LinearMap.sub_apply, LinearMap.add_apply,
        LinearMap.comp_apply, LinearMap.id_apply, AInfinityAlgebra.differential_apply] using e
    isHomogeneous_homotopyRight := LinearMap.isHomogeneous_def.2 fun _ _ hb ↦
      h₂.symm.linearHomotopy_mem hb
    id_sub_linearPart_comp_inv := LinearMap.ext fun b ↦ by
      have e := h₂.symm.linearPart_sub_linearPart b
      simpa only [linearPart_id, linearPart_comp, LinearMap.sub_apply, LinearMap.add_apply,
        LinearMap.comp_apply, LinearMap.id_apply, AInfinityAlgebra.differential_apply] using e
  }⟩

namespace LinearHomotopyInverse

/-- Swap the roles of `f` and `g` in `LinearHomotopyInverse` when `g.linearPart = c.inv`. -/
noncomputable def symm {f : AInfinityHom AA BB} (c : f.LinearHomotopyInverse)
    {g : AInfinityHom BB AA} (hg : g.linearPart = c.inv) : g.LinearHomotopyInverse where
  inv := f.linearPart
  homotopyLeft := c.homotopyRight
  homotopyRight := c.homotopyLeft
  isHomogeneous_inv := f.isHomogeneous_linearPart
  differential_comp_inv := differential_comp_linearPart f
  isHomogeneous_homotopyLeft := c.isHomogeneous_homotopyRight
  id_sub_inv_comp_linearPart := by rw [hg]; exact c.id_sub_linearPart_comp_inv
  isHomogeneous_homotopyRight := c.isHomogeneous_homotopyLeft
  id_sub_linearPart_comp_inv := by rw [hg]; exact c.id_sub_inv_comp_linearPart

private noncomputable def vogtDelta {f : AInfinityHom AA BB} (c : f.LinearHomotopyInverse) :
    A →ₗ[R] B :=
  f.linearPart ∘ₗ c.homotopyLeft - c.homotopyRight ∘ₗ f.linearPart

private noncomputable def vogtHomotopyLeft {f : AInfinityHom AA BB} (c : f.LinearHomotopyInverse) :
    A →ₗ[R] A :=
  c.homotopyLeft - c.inv ∘ₗ c.vogtDelta

private noncomputable def vogtTheta {f : AInfinityHom AA BB} (c : f.LinearHomotopyInverse) :
    A →ₗ[R] B :=
  c.homotopyRight ∘ₗ c.vogtDelta

private theorem isHomogeneous_vogtDelta {f : AInfinityHom AA BB} (c : f.LinearHomotopyInverse) :
    LinearMap.IsHomogeneous c.vogtDelta AA.grading.piece BB.grading.piece (-1) := by
  have h₁ : LinearMap.IsHomogeneous (f.linearPart ∘ₗ c.homotopyLeft)
      AA.grading.piece BB.grading.piece (-1) := by
    simpa only [add_zero] using f.isHomogeneous_linearPart.comp c.isHomogeneous_homotopyLeft
  have h₂ : LinearMap.IsHomogeneous (c.homotopyRight ∘ₗ f.linearPart)
      AA.grading.piece BB.grading.piece (-1) := by
    simpa only [zero_add] using c.isHomogeneous_homotopyRight.comp f.isHomogeneous_linearPart
  exact h₁.sub h₂

private theorem isHomogeneous_vogtHomotopyLeft {f : AInfinityHom AA BB}
    (c : f.LinearHomotopyInverse) :
    LinearMap.IsHomogeneous c.vogtHomotopyLeft AA.grading.piece AA.grading.piece (-1) := by
  have h : LinearMap.IsHomogeneous (c.inv ∘ₗ c.vogtDelta)
      AA.grading.piece AA.grading.piece (-1) := by
    simpa only [add_zero] using c.isHomogeneous_inv.comp c.isHomogeneous_vogtDelta
  exact c.isHomogeneous_homotopyLeft.sub h

private theorem isHomogeneous_vogtTheta {f : AInfinityHom AA BB} (c : f.LinearHomotopyInverse) :
    LinearMap.IsHomogeneous c.vogtTheta AA.grading.piece BB.grading.piece (-2) := by
  rw [vogtTheta]
  simpa only [show (-1 : ℤ) + -1 = -2 by decide] using
    c.isHomogeneous_homotopyRight.comp c.isHomogeneous_vogtDelta

private theorem differential_comp_vogtDelta_add {f : AInfinityHom AA BB}
    (c : f.LinearHomotopyInverse) :
    BB.differential ∘ₗ c.vogtDelta + c.vogtDelta ∘ₗ AA.differential = 0 := by
  have hdf := differential_comp_linearPart f
  have h₁ : BB.differential ∘ₗ (f.linearPart ∘ₗ c.homotopyLeft) +
      (f.linearPart ∘ₗ c.homotopyLeft) ∘ₗ AA.differential =
      f.linearPart ∘ₗ (LinearMap.id - c.inv ∘ₗ f.linearPart) := by
    rw [← LinearMap.comp_assoc, hdf, LinearMap.comp_assoc, LinearMap.comp_assoc,
      ← LinearMap.comp_add, ← c.id_sub_inv_comp_linearPart]
  have h₂ : BB.differential ∘ₗ (c.homotopyRight ∘ₗ f.linearPart) +
      (c.homotopyRight ∘ₗ f.linearPart) ∘ₗ AA.differential =
      (LinearMap.id - f.linearPart ∘ₗ c.inv) ∘ₗ f.linearPart :=
    LinearMap.ext fun a ↦ by
      have e₁ := LinearMap.congr_fun hdf a
      have e₂ := LinearMap.congr_fun c.id_sub_linearPart_comp_inv (f.linearPart a)
      simp only [LinearMap.add_apply, LinearMap.sub_apply, LinearMap.comp_apply,
        LinearMap.id_apply] at e₁ e₂ ⊢
      rw [← e₁]
      exact e₂.symm
  calc
    BB.differential ∘ₗ c.vogtDelta + c.vogtDelta ∘ₗ AA.differential =
        (BB.differential ∘ₗ (f.linearPart ∘ₗ c.homotopyLeft) +
          (f.linearPart ∘ₗ c.homotopyLeft) ∘ₗ AA.differential) -
        (BB.differential ∘ₗ (c.homotopyRight ∘ₗ f.linearPart) +
          (c.homotopyRight ∘ₗ f.linearPart) ∘ₗ AA.differential) := by
      simp only [vogtDelta, LinearMap.comp_sub, LinearMap.sub_comp]
      abel
    _ = 0 := by
      rw [h₁, h₂, LinearMap.comp_sub, LinearMap.sub_comp, LinearMap.comp_id, LinearMap.id_comp,
        LinearMap.comp_assoc, sub_self]

private theorem id_sub_inv_comp_vogtHomotopyLeft {f : AInfinityHom AA BB}
    (c : f.LinearHomotopyInverse) :
    LinearMap.id - c.inv ∘ₗ f.linearPart =
      AA.differential ∘ₗ c.vogtHomotopyLeft + c.vogtHomotopyLeft ∘ₗ AA.differential := by
  have hzero : AA.differential ∘ₗ (c.inv ∘ₗ c.vogtDelta) +
      (c.inv ∘ₗ c.vogtDelta) ∘ₗ AA.differential = 0 := by
    rw [← LinearMap.comp_assoc, c.differential_comp_inv, LinearMap.comp_assoc,
      LinearMap.comp_assoc, ← LinearMap.comp_add, c.differential_comp_vogtDelta_add,
      LinearMap.comp_zero]
  calc
    LinearMap.id - c.inv ∘ₗ f.linearPart =
        (AA.differential ∘ₗ c.homotopyLeft + c.homotopyLeft ∘ₗ AA.differential) - 0 := by
      rw [c.id_sub_inv_comp_linearPart, sub_zero]
    _ = AA.differential ∘ₗ c.vogtHomotopyLeft + c.vogtHomotopyLeft ∘ₗ AA.differential := by
      rw [← hzero, vogtHomotopyLeft, LinearMap.comp_sub, LinearMap.sub_comp]
      abel

private theorem linearPart_comp_vogtHomotopyLeft_sub {f : AInfinityHom AA BB}
    (c : f.LinearHomotopyInverse) :
    f.linearPart ∘ₗ c.vogtHomotopyLeft - c.homotopyRight ∘ₗ f.linearPart =
      BB.differential ∘ₗ c.vogtTheta - c.vogtTheta ∘ₗ AA.differential := by
  have hdδ : BB.differential ∘ₗ c.vogtDelta = -(c.vogtDelta ∘ₗ AA.differential) :=
    eq_neg_of_add_eq_zero_left c.differential_comp_vogtDelta_add
  calc
    f.linearPart ∘ₗ c.vogtHomotopyLeft - c.homotopyRight ∘ₗ f.linearPart =
        (LinearMap.id - f.linearPart ∘ₗ c.inv) ∘ₗ c.vogtDelta := by
      simp only [vogtHomotopyLeft, vogtDelta, LinearMap.comp_sub, LinearMap.sub_comp,
        LinearMap.id_comp, LinearMap.comp_assoc]
      abel
    _ = BB.differential ∘ₗ c.vogtTheta - c.vogtTheta ∘ₗ AA.differential :=
      LinearMap.ext fun a ↦ by
        have h₁ := LinearMap.congr_fun c.id_sub_linearPart_comp_inv (c.vogtDelta a)
        have h₂ := LinearMap.congr_fun hdδ a
        simp only [LinearMap.sub_apply, LinearMap.add_apply, LinearMap.comp_apply,
          LinearMap.id_apply, LinearMap.neg_apply] at h₁ h₂
        simp only [vogtTheta, LinearMap.sub_apply, LinearMap.comp_apply, LinearMap.id_apply]
        rw [h₁, h₂, map_neg]
        abel

end LinearHomotopyInverse

/-! ### Stage-n right-homotopy inverse approximations and obstruction step -/

private structure ApproxRightInverse (f : AInfinityHom AA BB) (n : ℕ) where
  gamma : ReducedTensorWords R B →ₗ[R] A
  eta : ReducedTensorWords R B →ₗ[R] B
  isHomogeneous_gamma : LinearMap.IsHomogeneous gamma
    (gradedPiece (BB.grading.shift 1)) (AA.grading.shift 1).piece 0
  isHomogeneous_eta : LinearMap.IsHomogeneous eta
    (gradedPiece (BB.grading.shift 1)) (BB.grading.shift 1).piece (-1)
  errMorphism_zero : ∀ w ∈ filtration R B n,
    (AA.barDifferential ∘ₗ coalgHom R gamma - coalgHom R gamma ∘ₗ BB.barDifferential) w = 0
  errHomotopy_zero : ∀ w ∈ filtration R B n,
    (((LinearMap.id : ReducedTensorWords R B →ₗ[R] ReducedTensorWords R B) -
        f.barMap ∘ₗ coalgHom R gamma) -
      (BB.barDifferential ∘ₗ
          gradedCoderivAlong (BB.grading.shift 1) 1
            (LinearMap.id : ReducedTensorWords R B →ₗ[R] ReducedTensorWords R B)
            (f.barMap ∘ₗ coalgHom R gamma) eta +
        gradedCoderivAlong (BB.grading.shift 1) 1
            (LinearMap.id : ReducedTensorWords R B →ₗ[R] ReducedTensorWords R B)
            (f.barMap ∘ₗ coalgHom R gamma) eta ∘ₗ BB.barDifferential)) w = 0

private noncomputable def ApproxRightInverse.approxZero (f : AInfinityHom AA BB) :
    ApproxRightInverse f 0 where
  gamma := 0
  eta := 0
  isHomogeneous_gamma := LinearMap.isHomogeneous_zero _ _ _
  isHomogeneous_eta := LinearMap.isHomogeneous_zero _ _ _
  errMorphism_zero w hw := by
    rw [filtration_zero, Submodule.mem_bot] at hw; rw [hw, map_zero]
  errHomotopy_zero w hw := by
    rw [filtration_zero, Submodule.mem_bot] at hw; rw [hw, map_zero]

private noncomputable def ApproxRightInverse.barG {f : AInfinityHom AA BB} {n : ℕ}
    (s : ApproxRightInverse f n) : ReducedTensorWords R B →ₗ[R] ReducedTensorWords R A :=
  coalgHom R s.gamma

private noncomputable def ApproxRightInverse.barH {f : AInfinityHom AA BB} {n : ℕ}
    (s : ApproxRightInverse f n) : ReducedTensorWords R B →ₗ[R] ReducedTensorWords R B :=
  gradedCoderivAlong (BB.grading.shift 1) 1
    (LinearMap.id : ReducedTensorWords R B →ₗ[R] ReducedTensorWords R B)
    (f.barMap ∘ₗ s.barG) s.eta

private noncomputable def ApproxRightInverse.errMorphism {f : AInfinityHom AA BB} {n : ℕ}
    (s : ApproxRightInverse f n) : ReducedTensorWords R B →ₗ[R] ReducedTensorWords R A :=
  AA.barDifferential ∘ₗ s.barG - s.barG ∘ₗ BB.barDifferential

private noncomputable def ApproxRightInverse.errHomotopy {f : AInfinityHom AA BB} {n : ℕ}
    (s : ApproxRightInverse f n) : ReducedTensorWords R B →ₗ[R] ReducedTensorWords R B :=
  ((LinearMap.id : ReducedTensorWords R B →ₗ[R] ReducedTensorWords R B) - f.barMap ∘ₗ s.barG) -
    (BB.barDifferential ∘ₗ s.barH + s.barH ∘ₗ BB.barDifferential)

private noncomputable def ApproxRightInverse.phi {f : AInfinityHom AA BB} {n : ℕ}
    (s : ApproxRightInverse f n) : ReducedTensorWords R B →ₗ[R] A :=
  -(letter R A ∘ₗ s.errMorphism)

private noncomputable def ApproxRightInverse.psi {f : AInfinityHom AA BB} {n : ℕ}
    (s : ApproxRightInverse f n) : ReducedTensorWords R B →ₗ[R] B :=
  letter R B ∘ₗ s.errHomotopy

private theorem ApproxRightInverse.errMorphism_apply_zero {f : AInfinityHom AA BB} {n : ℕ}
    (s : ApproxRightInverse f n) {w : ReducedTensorWords R B} (hw : w ∈ filtration R B n) :
    s.errMorphism w = 0 := by
  rw [ApproxRightInverse.errMorphism, ApproxRightInverse.barG]
  exact s.errMorphism_zero w hw

private theorem ApproxRightInverse.errHomotopy_apply_zero {f : AInfinityHom AA BB} {n : ℕ}
    (s : ApproxRightInverse f n) {w : ReducedTensorWords R B} (hw : w ∈ filtration R B n) :
    s.errHomotopy w = 0 := by
  rw [ApproxRightInverse.errHomotopy, ApproxRightInverse.barH, ApproxRightInverse.barG]
  exact s.errHomotopy_zero w hw

private theorem ApproxRightInverse.isHomogeneous_barG {f : AInfinityHom AA BB} {n : ℕ}
    (s : ApproxRightInverse f n) :
    LinearMap.IsHomogeneous s.barG (gradedPiece (BB.grading.shift 1))
      (gradedPiece (AA.grading.shift 1)) 0 :=
  isHomogeneous_coalgHom s.isHomogeneous_gamma

private theorem ApproxRightInverse.isHomogeneous_barH {f : AInfinityHom AA BB} {n : ℕ}
    (s : ApproxRightInverse f n) :
    LinearMap.IsHomogeneous s.barH (gradedPiece (BB.grading.shift 1))
      (gradedPiece (BB.grading.shift 1)) (-1) :=
  isHomogeneous_gradedCoderivAlong (LinearMap.isHomogeneous_id _)
    (by simpa only [add_zero] using f.isHomogeneous_barMap.comp s.isHomogeneous_barG)
    s.isHomogeneous_eta

private theorem ApproxRightInverse.isHomogeneous_phi {f : AInfinityHom AA BB} {n : ℕ}
    (s : ApproxRightInverse f n) :
    LinearMap.IsHomogeneous s.phi (gradedPiece (BB.grading.shift 1))
      (AA.grading.shift 1).piece 1 := by
  have h₁ : LinearMap.IsHomogeneous (AA.barDifferential ∘ₗ s.barG)
      (gradedPiece (BB.grading.shift 1)) (gradedPiece (AA.grading.shift 1)) 1 := by
    simpa only [zero_add] using AA.isHomogeneous_barDifferential.comp s.isHomogeneous_barG
  have h₂ : LinearMap.IsHomogeneous (s.barG ∘ₗ BB.barDifferential)
      (gradedPiece (BB.grading.shift 1)) (gradedPiece (AA.grading.shift 1)) 1 := by
    simpa only [add_zero] using s.isHomogeneous_barG.comp BB.isHomogeneous_barDifferential
  rw [ApproxRightInverse.phi, ApproxRightInverse.errMorphism]
  simpa only [add_zero] using ((isHomogeneous_letter (AA.grading.shift 1)).comp (h₁.sub h₂)).neg

private theorem ApproxRightInverse.isHomogeneous_psi {f : AInfinityHom AA BB} {n : ℕ}
    (s : ApproxRightInverse f n) :
    LinearMap.IsHomogeneous s.psi (gradedPiece (BB.grading.shift 1))
      (BB.grading.shift 1).piece 0 := by
  have hFG : LinearMap.IsHomogeneous (LinearMap.id - f.barMap ∘ₗ s.barG)
      (gradedPiece (BB.grading.shift 1)) (gradedPiece (BB.grading.shift 1)) 0 :=
    (LinearMap.isHomogeneous_id _).sub
      (by simpa only [add_zero] using f.isHomogeneous_barMap.comp s.isHomogeneous_barG)
  have hbH : LinearMap.IsHomogeneous (BB.barDifferential ∘ₗ s.barH)
      (gradedPiece (BB.grading.shift 1)) (gradedPiece (BB.grading.shift 1)) 0 := by
    simpa only [neg_add_cancel] using BB.isHomogeneous_barDifferential.comp s.isHomogeneous_barH
  have hHb : LinearMap.IsHomogeneous (s.barH ∘ₗ BB.barDifferential)
      (gradedPiece (BB.grading.shift 1)) (gradedPiece (BB.grading.shift 1)) 0 := by
    simpa only [add_neg_cancel] using s.isHomogeneous_barH.comp BB.isHomogeneous_barDifferential
  rw [ApproxRightInverse.psi, ApproxRightInverse.errHomotopy]
  simpa only [add_zero] using
    (isHomogeneous_letter (BB.grading.shift 1)).comp (hFG.sub (hbH.add hHb))

private theorem ApproxRightInverse.errMorphism_eq_ofLetter {f : AInfinityHom AA BB} {n : ℕ}
    (s : ApproxRightInverse f n) {z : ReducedTensorWords R B}
    (hz : z ∈ filtration R B (n + 1)) :
    s.errMorphism z = -ofLetter R A (s.phi z) := by
  have hD₁ : IsGradedCoderivationAlong (BB.grading.shift 1) 1 s.barG s.barG
      (AA.barDifferential ∘ₗ s.barG) :=
    AA.isGradedCoderivation_barDifferential.comp_isCoalgHom
      (isCoalgHom_coalgHom s.gamma) s.isHomogeneous_barG
  have hD₂ : IsGradedCoderivationAlong (BB.grading.shift 1) 1 s.barG s.barG
      (s.barG ∘ₗ BB.barDifferential) := by
    rw [ApproxRightInverse.barG]
    simpa only [LinearMap.comp_id] using
      (isCoalgHom_coalgHom s.gamma).comp_isGradedCoderivationAlong
        (isGradedCoderivationAlong_id_id_iff.2 BB.isGradedCoderivation_barDifferential)
  have heq := sub_apply_eq_ofLetter_letter_of_mem_filtration_succ
    (G := BB.grading.shift 1) 1 (fun _ hw ↦ sub_eq_zero.1 (s.errMorphism_apply_zero hw)) hz
    (hD₁.deconcatenation_apply z) (hD₂.deconcatenation_apply z)
  rw [ApproxRightInverse.phi, LinearMap.neg_apply, LinearMap.comp_apply, map_neg, neg_neg]
  exact heq

private theorem ApproxRightInverse.errHomotopy_eq_ofLetter {f : AInfinityHom AA BB} {n : ℕ}
    (s : ApproxRightInverse f n) {z : ReducedTensorWords R B}
    (hz : z ∈ filtration R B (n + 1)) :
    s.errHomotopy z = ofLetter R B (s.psi z) := by
  have hD₁ : IsGradedCoderivationAlong (BB.grading.shift 1) 0 LinearMap.id (f.barMap ∘ₗ s.barG)
      (LinearMap.id - f.barMap ∘ₗ s.barG) :=
    (isCoalgHom_id B).isGradedCoderivationAlong_sub
      (f.isCoalgHom_barMap.comp (isCoalgHom_coalgHom s.gamma))
  have hH : IsGradedCoderivationAlong (BB.grading.shift 1) 1 LinearMap.id (f.barMap ∘ₗ s.barG)
      s.barH :=
    isGradedCoderivationAlong_gradedCoderivAlong (isCoalgHom_id B)
      (f.isCoalgHom_barMap.comp (isCoalgHom_coalgHom s.gamma)) s.eta
  have hFG : ∀ w ∈ filtration R B n,
      BB.barDifferential ((f.barMap ∘ₗ s.barG) w) = (f.barMap ∘ₗ s.barG) (BB.barDifferential w) :=
    fun w hw ↦ by
      have herr := sub_eq_zero.1 (s.errMorphism_apply_zero hw)
      simp only [LinearMap.comp_apply] at herr
      rw [LinearMap.comp_apply, LinearMap.comp_apply, f.barDifferential_barMap, herr]
  have hD₂_dec := hH.deconcatenation_comp_add_comp_of_mem_filtration s.isHomogeneous_barH
    (by decide) BB.isGradedCoderivation_barDifferential BB.isHomogeneous_barDifferential (by decide)
    BB.isGradedCoderivation_barDifferential (LinearMap.isHomogeneous_id _) (fun _ _ ↦ rfl) hFG hz
  have htwist0 : LinearMap.rTensor (ReducedTensorWords R B)
      (map R ((BB.grading.shift 1).koszulTwist 0)) (deconcatenation R B z) =
      deconcatenation R B z := by
    rw [InternalGrading.koszulTwist_zero, map_id, LinearMap.rTensor_id, LinearMap.id_apply]
  exact sub_apply_eq_ofLetter_letter_of_mem_filtration_succ (G := BB.grading.shift 1) 0
    (fun _ hw ↦ sub_eq_zero.1 (s.errHomotopy_apply_zero hw)) hz (hD₁.deconcatenation_apply z)
    (by rwa [htwist0])

private theorem ApproxRightInverse.phi_unaryBarDifferential {f : AInfinityHom AA BB} {n : ℕ}
    (s : ApproxRightInverse f n) {z : ReducedTensorWords R B}
    (hz : z ∈ filtration R B (n + 1)) :
    s.phi (BB.unaryBarDifferential z) = -AA.differential (s.phi z) := by
  have hid : (AA.barDifferential ∘ₗ s.errMorphism + s.errMorphism ∘ₗ BB.barDifferential) z = 0 := by
    have e : AA.barDifferential ∘ₗ s.errMorphism + s.errMorphism ∘ₗ BB.barDifferential = 0 := by
      simp only [ApproxRightInverse.errMorphism, LinearMap.comp_sub, LinearMap.sub_comp,
        ← LinearMap.comp_assoc, AA.barDifferential_sq, LinearMap.zero_comp]
      simp only [LinearMap.comp_assoc, BB.barDifferential_sq, LinearMap.comp_zero]
      abel
    exact LinearMap.congr_fun e z
  have hhigh : s.errMorphism (BB.higherBarDifferential z) = 0 :=
    s.errMorphism_apply_zero (BB.higherBarDifferential_filtration n ⟨z, hz, rfl⟩)
  have hl := congrArg (letter R A) hid
  rw [LinearMap.add_apply, LinearMap.comp_apply, LinearMap.comp_apply, map_zero, map_add,
    s.errMorphism_eq_ofLetter hz, map_neg, map_neg, AA.barDifferential_ofLetter, letter_ofLetter,
    ← AInfinityAlgebra.differential_apply, BB.barDifferential_eq_unary_add_higher,
    LinearMap.add_apply, map_add, hhigh, add_zero] at hl
  have hφu : letter R A (s.errMorphism (BB.unaryBarDifferential z)) =
      -s.phi (BB.unaryBarDifferential z) := by
    simp only [ApproxRightInverse.phi, LinearMap.neg_apply, LinearMap.comp_apply, neg_neg]
  rw [hφu] at hl
  rw [← sub_eq_zero]
  calc
    s.phi (BB.unaryBarDifferential z) - -AA.differential (s.phi z) =
        -(-AA.differential (s.phi z) + -s.phi (BB.unaryBarDifferential z)) := by abel
    _ = 0 := by rw [hl, neg_zero]

private theorem ApproxRightInverse.psi_unaryBarDifferential {f : AInfinityHom AA BB} {n : ℕ}
    (s : ApproxRightInverse f n) {z : ReducedTensorWords R B}
    (hz : z ∈ filtration R B (n + 1)) :
    s.psi (BB.unaryBarDifferential z) = BB.differential (s.psi z) - f.linearPart (s.phi z) := by
  have hid : (BB.barDifferential ∘ₗ s.errHomotopy - s.errHomotopy ∘ₗ BB.barDifferential) z =
      -(f.barMap (s.errMorphism z)) := by
    have e : BB.barDifferential ∘ₗ s.errHomotopy - s.errHomotopy ∘ₗ BB.barDifferential =
        -(f.barMap ∘ₗ s.errMorphism) := by
      simp only [ApproxRightInverse.errHomotopy, ApproxRightInverse.errMorphism, LinearMap.comp_sub,
        LinearMap.sub_comp, LinearMap.comp_add, LinearMap.add_comp, LinearMap.comp_id,
        LinearMap.id_comp, ← LinearMap.comp_assoc, BB.barDifferential_sq, LinearMap.zero_comp,
        f.barDifferential_comp_barMap]
      simp only [LinearMap.comp_assoc, BB.barDifferential_sq, LinearMap.comp_zero]
      abel
    simpa only [LinearMap.neg_apply, LinearMap.comp_apply] using LinearMap.congr_fun e z
  have hhigh : s.errHomotopy (BB.higherBarDifferential z) = 0 :=
    s.errHomotopy_apply_zero (BB.higherBarDifferential_filtration n ⟨z, hz, rfl⟩)
  have hl := congrArg (letter R B) hid
  rw [LinearMap.sub_apply, LinearMap.comp_apply, LinearMap.comp_apply, map_sub,
    s.errHomotopy_eq_ofLetter hz, BB.barDifferential_ofLetter, letter_ofLetter,
    ← AInfinityAlgebra.differential_apply, s.errMorphism_eq_ofLetter hz, map_neg, map_neg, map_neg,
    neg_neg, f.barMap_ofLetter, letter_ofLetter, BB.barDifferential_eq_unary_add_higher,
    LinearMap.add_apply, map_add, hhigh, add_zero] at hl
  have hψu : letter R B (s.errHomotopy (BB.unaryBarDifferential z)) =
      s.psi (BB.unaryBarDifferential z) := rfl
  rw [hψu] at hl
  rw [← hl]
  abel

private noncomputable def ApproxRightInverse.deltaGamma {f : AInfinityHom AA BB} {n : ℕ}
    (s : ApproxRightInverse f n) (c : f.LinearHomotopyInverse) :
    ReducedTensorWords R B →ₗ[R] A :=
  c.inv ∘ₗ s.psi + c.vogtHomotopyLeft ∘ₗ s.phi

private noncomputable def ApproxRightInverse.deltaEta {f : AInfinityHom AA BB} {n : ℕ}
    (s : ApproxRightInverse f n) (c : f.LinearHomotopyInverse) :
    ReducedTensorWords R B →ₗ[R] B :=
  c.homotopyRight ∘ₗ s.psi - c.vogtTheta ∘ₗ s.phi

private theorem ApproxRightInverse.deltaGamma_zero {f : AInfinityHom AA BB} {n : ℕ}
    (s : ApproxRightInverse f n) (c : f.LinearHomotopyInverse) {w : ReducedTensorWords R B}
    (hw : w ∈ filtration R B n) : s.deltaGamma c w = 0 := by
  simp only [ApproxRightInverse.deltaGamma, ApproxRightInverse.phi, ApproxRightInverse.psi,
    LinearMap.add_apply, LinearMap.comp_apply, LinearMap.neg_apply,
    s.errMorphism_apply_zero hw, s.errHomotopy_apply_zero hw, map_zero, neg_zero, add_zero]

private theorem ApproxRightInverse.deltaEta_zero {f : AInfinityHom AA BB} {n : ℕ}
    (s : ApproxRightInverse f n) (c : f.LinearHomotopyInverse) {w : ReducedTensorWords R B}
    (hw : w ∈ filtration R B n) : s.deltaEta c w = 0 := by
  simp only [ApproxRightInverse.deltaEta, ApproxRightInverse.phi, ApproxRightInverse.psi,
    LinearMap.sub_apply, LinearMap.comp_apply, LinearMap.neg_apply,
    s.errMorphism_apply_zero hw, s.errHomotopy_apply_zero hw, map_zero, neg_zero, sub_zero]

private theorem ApproxRightInverse.isHomogeneous_deltaGamma {f : AInfinityHom AA BB} {n : ℕ}
    (s : ApproxRightInverse f n) (c : f.LinearHomotopyInverse) :
    LinearMap.IsHomogeneous (s.deltaGamma c) (gradedPiece (BB.grading.shift 1))
      (AA.grading.shift 1).piece 0 := by
  have h₁ : LinearMap.IsHomogeneous (c.inv ∘ₗ s.psi)
      (gradedPiece (BB.grading.shift 1)) (AA.grading.shift 1).piece 0 := by
    simpa only [add_zero] using
      (LinearMap.isHomogeneous_shift_piece_iff.2 c.isHomogeneous_inv).comp s.isHomogeneous_psi
  have h₂ : LinearMap.IsHomogeneous (c.vogtHomotopyLeft ∘ₗ s.phi)
      (gradedPiece (BB.grading.shift 1)) (AA.grading.shift 1).piece 0 := by
    simpa only [add_neg_cancel] using
      (LinearMap.isHomogeneous_shift_piece_iff.2 c.isHomogeneous_vogtHomotopyLeft).comp
        s.isHomogeneous_phi
  exact h₁.add h₂

private theorem ApproxRightInverse.isHomogeneous_deltaEta {f : AInfinityHom AA BB} {n : ℕ}
    (s : ApproxRightInverse f n) (c : f.LinearHomotopyInverse) :
    LinearMap.IsHomogeneous (s.deltaEta c) (gradedPiece (BB.grading.shift 1))
      (BB.grading.shift 1).piece (-1) := by
  have h₁ : LinearMap.IsHomogeneous (c.homotopyRight ∘ₗ s.psi)
      (gradedPiece (BB.grading.shift 1)) (BB.grading.shift 1).piece (-1) := by
    simpa only [zero_add] using
      (LinearMap.isHomogeneous_shift_piece_iff.2 c.isHomogeneous_homotopyRight).comp
        s.isHomogeneous_psi
  have h₂ : LinearMap.IsHomogeneous (c.vogtTheta ∘ₗ s.phi)
      (gradedPiece (BB.grading.shift 1)) (BB.grading.shift 1).piece (-1) := by
    simpa only [show (1 : ℤ) + -2 = -1 by decide] using
      (LinearMap.isHomogeneous_shift_piece_iff.2 c.isHomogeneous_vogtTheta).comp s.isHomogeneous_phi
  exact h₁.sub h₂

private theorem ApproxRightInverse.coalgHom_step_barDifferential {f : AInfinityHom AA BB} {n : ℕ}
    (s : ApproxRightInverse f n) (c : f.LinearHomotopyInverse)
    {z : ReducedTensorWords R B} (hz : z ∈ filtration R B (n + 1)) :
    coalgHom R (s.gamma + s.deltaGamma c) (BB.barDifferential z) =
      s.barG (BB.barDifferential z) +
        ofLetter R A (s.deltaGamma c (BB.unaryBarDifferential z)) := by
  have hu : BB.unaryBarDifferential z ∈ filtration R B (n + 1) :=
    BB.unaryBarDifferential_filtration (n + 1) ⟨z, hz, rfl⟩
  have hh : BB.higherBarDifferential z ∈ filtration R B n :=
    BB.higherBarDifferential_filtration n ⟨z, hz, rfl⟩
  rw [BB.barDifferential_eq_unary_add_higher, LinearMap.add_apply, map_add, map_add,
    coalgHom_add_apply_of_mem_filtration_succ _ (fun _ hw ↦ s.deltaGamma_zero c hw) hu,
    coalgHom_add_apply_of_mem_filtration_succ _ (fun _ hw ↦ s.deltaGamma_zero c hw)
      (filtration_monotone R B n.le_succ hh),
    s.deltaGamma_zero c hh, map_zero, add_zero, ApproxRightInverse.barG]
  abel

private theorem ApproxRightInverse.step_errMorphism_zero {f : AInfinityHom AA BB} {n : ℕ}
    (s : ApproxRightInverse f n) (c : f.LinearHomotopyInverse) {z : ReducedTensorWords R B}
    (hz : z ∈ filtration R B (n + 1)) :
    (AA.barDifferential ∘ₗ coalgHom R (s.gamma + s.deltaGamma c) -
        coalgHom R (s.gamma + s.deltaGamma c) ∘ₗ BB.barDifferential) z = 0 := by
  rw [LinearMap.sub_apply, LinearMap.comp_apply, LinearMap.comp_apply,
    coalgHom_add_apply_of_mem_filtration_succ _ (fun _ hw ↦ s.deltaGamma_zero c hw) hz,
    s.coalgHom_step_barDifferential c hz, map_add]
  have heq : AA.barDifferential (coalgHom R s.gamma z) +
        AA.barDifferential (ofLetter R A (s.deltaGamma c z)) -
      (s.barG (BB.barDifferential z) +
        ofLetter R A (s.deltaGamma c (BB.unaryBarDifferential z))) =
      s.errMorphism z + AA.barDifferential (ofLetter R A (s.deltaGamma c z)) -
        ofLetter R A (s.deltaGamma c (BB.unaryBarDifferential z)) := by
    simp only [ApproxRightInverse.errMorphism, ApproxRightInverse.barG, LinearMap.sub_apply,
      LinearMap.comp_apply]
    abel
  rw [heq, s.errMorphism_eq_ofLetter hz, AA.barDifferential_ofLetter,
    ← AInfinityAlgebra.differential_apply, ← map_neg, ← map_add, ← map_sub]
  refine (congrArg (ofLetter R A) ?_).trans (map_zero _)
  have hdinv := LinearMap.congr_fun c.differential_comp_inv (s.psi z)
  have hvogt := LinearMap.congr_fun c.id_sub_inv_comp_vogtHomotopyLeft (s.phi z)
  simp only [LinearMap.sub_apply, LinearMap.add_apply, LinearMap.comp_apply,
    LinearMap.id_apply] at hdinv hvogt
  simp only [ApproxRightInverse.deltaGamma, LinearMap.add_apply, LinearMap.comp_apply,
    s.phi_unaryBarDifferential hz, s.psi_unaryBarDifferential hz, map_add, map_sub, map_neg, hdinv]
  calc
    -s.phi z + (c.inv (BB.differential (s.psi z)) +
        AA.differential (c.vogtHomotopyLeft (s.phi z))) -
        (c.inv (BB.differential (s.psi z)) - c.inv (f.linearPart (s.phi z)) +
          -c.vogtHomotopyLeft (AA.differential (s.phi z))) =
      (AA.differential (c.vogtHomotopyLeft (s.phi z)) +
        c.vogtHomotopyLeft (AA.differential (s.phi z))) -
      (s.phi z - c.inv (f.linearPart (s.phi z))) := by abel
    _ = 0 := by rw [← hvogt, sub_self]

private theorem ApproxRightInverse.step_barH_apply {f : AInfinityHom AA BB} {n : ℕ}
    (s : ApproxRightInverse f n) (c : f.LinearHomotopyInverse) {u : ReducedTensorWords R B}
    (hu : u ∈ filtration R B (n + 1)) :
    gradedCoderivAlong (BB.grading.shift 1) 1
        (LinearMap.id : ReducedTensorWords R B →ₗ[R] ReducedTensorWords R B)
        (f.barMap ∘ₗ coalgHom R (s.gamma + s.deltaGamma c)) (s.eta + s.deltaEta c) u =
      s.barH u + ofLetter R B (s.deltaEta c u) := by
  have hF' : ∀ w ∈ filtration R B n,
      (f.barMap ∘ₗ coalgHom R (s.gamma + s.deltaGamma c)) w = (f.barMap ∘ₗ s.barG) w :=
    fun w hw ↦ by
      rw [LinearMap.comp_apply, LinearMap.comp_apply,
        coalgHom_add_apply_of_mem_filtration_succ _ (fun _ h ↦ s.deltaGamma_zero c h)
          (filtration_monotone R B n.le_succ hw),
        s.deltaGamma_zero c hw, map_zero, add_zero, ApproxRightInverse.barG]
  exact gradedCoderivAlong_add_apply_of_mem_filtration_succ (isCoalgHom_id B)
    (f.isCoalgHom_barMap.comp (isCoalgHom_coalgHom s.gamma))
    (f.isCoalgHom_barMap.comp (isCoalgHom_coalgHom _)) s.eta hF'
    (fun _ hw ↦ s.deltaEta_zero c hw) hu

private theorem ApproxRightInverse.step_barH_barDifferential {f : AInfinityHom AA BB} {n : ℕ}
    (s : ApproxRightInverse f n) (c : f.LinearHomotopyInverse)
    {z : ReducedTensorWords R B} (hz : z ∈ filtration R B (n + 1)) :
    gradedCoderivAlong (BB.grading.shift 1) 1
        (LinearMap.id : ReducedTensorWords R B →ₗ[R] ReducedTensorWords R B)
        (f.barMap ∘ₗ coalgHom R (s.gamma + s.deltaGamma c))
        (s.eta + s.deltaEta c) (BB.barDifferential z) =
      s.barH (BB.barDifferential z) +
        ofLetter R B (s.deltaEta c (BB.unaryBarDifferential z)) := by
  have hu : BB.unaryBarDifferential z ∈ filtration R B (n + 1) :=
    BB.unaryBarDifferential_filtration (n + 1) ⟨z, hz, rfl⟩
  have hh : BB.higherBarDifferential z ∈ filtration R B n :=
    BB.higherBarDifferential_filtration n ⟨z, hz, rfl⟩
  rw [BB.barDifferential_eq_unary_add_higher, LinearMap.add_apply, map_add, map_add,
    s.step_barH_apply c hu, s.step_barH_apply c (filtration_monotone R B n.le_succ hh),
    s.deltaEta_zero c hh, map_zero, add_zero]
  abel

private theorem ApproxRightInverse.step_errHomotopy_zero {f : AInfinityHom AA BB} {n : ℕ}
    (s : ApproxRightInverse f n) (c : f.LinearHomotopyInverse) {z : ReducedTensorWords R B}
    (hz : z ∈ filtration R B (n + 1)) :
    (((LinearMap.id : ReducedTensorWords R B →ₗ[R] ReducedTensorWords R B) -
        f.barMap ∘ₗ coalgHom R (s.gamma + s.deltaGamma c)) -
      (BB.barDifferential ∘ₗ
          gradedCoderivAlong (BB.grading.shift 1) 1
            (LinearMap.id : ReducedTensorWords R B →ₗ[R] ReducedTensorWords R B)
            (f.barMap ∘ₗ coalgHom R (s.gamma + s.deltaGamma c)) (s.eta + s.deltaEta c) +
        gradedCoderivAlong (BB.grading.shift 1) 1
            (LinearMap.id : ReducedTensorWords R B →ₗ[R] ReducedTensorWords R B)
            (f.barMap ∘ₗ coalgHom R (s.gamma + s.deltaGamma c)) (s.eta + s.deltaEta c) ∘ₗ
          BB.barDifferential)) z = 0 := by
  simp only [LinearMap.sub_apply, LinearMap.add_apply, LinearMap.comp_apply, LinearMap.id_apply]
  rw [coalgHom_add_apply_of_mem_filtration_succ _ (fun _ hw ↦ s.deltaGamma_zero c hw) hz,
    s.step_barH_apply c hz, s.step_barH_barDifferential c hz, map_add, map_add, f.barMap_ofLetter,
    BB.barDifferential_ofLetter, ← AInfinityAlgebra.differential_apply]
  have heq : z - (f.barMap (coalgHom R s.gamma z) +
        ofLetter R B (f.linearPart (s.deltaGamma c z))) -
      (BB.barDifferential (s.barH z) + ofLetter R B (BB.differential (s.deltaEta c z)) +
        (s.barH (BB.barDifferential z) +
          ofLetter R B (s.deltaEta c (BB.unaryBarDifferential z)))) =
      s.errHomotopy z - ofLetter R B (f.linearPart (s.deltaGamma c z) +
        BB.differential (s.deltaEta c z) + s.deltaEta c (BB.unaryBarDifferential z)) := by
    simp only [ApproxRightInverse.errHomotopy, ApproxRightInverse.barG, LinearMap.sub_apply,
      LinearMap.add_apply, LinearMap.comp_apply, LinearMap.id_apply, map_add]
    abel
  rw [heq, s.errHomotopy_eq_ofLetter hz, ← map_sub]
  refine (congrArg (ofLetter R B) ?_).trans (map_zero _)
  have hright := LinearMap.congr_fun c.id_sub_linearPart_comp_inv (s.psi z)
  have hcoh := LinearMap.congr_fun c.linearPart_comp_vogtHomotopyLeft_sub (s.phi z)
  simp only [LinearMap.sub_apply, LinearMap.add_apply, LinearMap.comp_apply,
    LinearMap.id_apply] at hright hcoh
  simp only [ApproxRightInverse.deltaGamma, ApproxRightInverse.deltaEta, LinearMap.add_apply,
    LinearMap.sub_apply, LinearMap.comp_apply, s.phi_unaryBarDifferential hz,
    s.psi_unaryBarDifferential hz, map_add, map_sub, map_neg]
  calc
    s.psi z - ((f.linearPart (c.inv (s.psi z)) + f.linearPart (c.vogtHomotopyLeft (s.phi z))) +
        (BB.differential (c.homotopyRight (s.psi z)) - BB.differential (c.vogtTheta (s.phi z))) +
        ((c.homotopyRight (BB.differential (s.psi z)) -
            c.homotopyRight (f.linearPart (s.phi z))) - -c.vogtTheta (AA.differential (s.phi z)))) =
      ((s.psi z - f.linearPart (c.inv (s.psi z))) -
        (BB.differential (c.homotopyRight (s.psi z)) +
          c.homotopyRight (BB.differential (s.psi z)))) -
      ((f.linearPart (c.vogtHomotopyLeft (s.phi z)) - c.homotopyRight (f.linearPart (s.phi z))) -
        (BB.differential (c.vogtTheta (s.phi z)) - c.vogtTheta (AA.differential (s.phi z)))) := by
      abel
    _ = 0 := by rw [hright, hcoh, sub_self, sub_self, sub_zero]

private noncomputable def ApproxRightInverse.step {f : AInfinityHom AA BB} {n : ℕ}
    (s : ApproxRightInverse f n) (c : f.LinearHomotopyInverse) : ApproxRightInverse f (n + 1) where
  gamma := s.gamma + s.deltaGamma c
  eta := s.eta + s.deltaEta c
  isHomogeneous_gamma := s.isHomogeneous_gamma.add (s.isHomogeneous_deltaGamma c)
  isHomogeneous_eta := s.isHomogeneous_eta.add (s.isHomogeneous_deltaEta c)
  errMorphism_zero _ hz := s.step_errMorphism_zero c hz
  errHomotopy_zero _ hz := s.step_errHomotopy_zero c hz

private noncomputable def ApproxRightInverse.seq {f : AInfinityHom AA BB}
    (c : f.LinearHomotopyInverse) : ∀ n : ℕ, ApproxRightInverse f n
  | 0 => ApproxRightInverse.approxZero f
  | n + 1 => (ApproxRightInverse.seq c n).step c

private theorem ApproxRightInverse.seq_gamma_succ_of_mem_filtration {f : AInfinityHom AA BB}
    (c : f.LinearHomotopyInverse) (n : ℕ) {z : ReducedTensorWords R B}
    (hz : z ∈ filtration R B n) :
    (ApproxRightInverse.seq c (n + 1)).gamma z = (ApproxRightInverse.seq c n).gamma z := by
  simp only [ApproxRightInverse.seq, ApproxRightInverse.step, LinearMap.add_apply,
    (ApproxRightInverse.seq c n).deltaGamma_zero c hz, add_zero]

private theorem ApproxRightInverse.seq_eta_succ_of_mem_filtration {f : AInfinityHom AA BB}
    (c : f.LinearHomotopyInverse) (n : ℕ) {z : ReducedTensorWords R B}
    (hz : z ∈ filtration R B n) :
    (ApproxRightInverse.seq c (n + 1)).eta z = (ApproxRightInverse.seq c n).eta z := by
  simp only [ApproxRightInverse.seq, ApproxRightInverse.step, LinearMap.add_apply,
    (ApproxRightInverse.seq c n).deltaEta_zero c hz, add_zero]

private theorem ApproxRightInverse.seq_gamma_eq_of_le {f : AInfinityHom AA BB}
    (c : f.LinearHomotopyInverse) {k n : ℕ} (hkn : k ≤ n) {z : ReducedTensorWords R B}
    (hz : z ∈ filtration R B k) :
    (ApproxRightInverse.seq c n).gamma z = (ApproxRightInverse.seq c k).gamma z := by
  induction n, hkn using Nat.le_induction with
  | base => rfl
  | succ n hkn ih =>
      rw [ApproxRightInverse.seq_gamma_succ_of_mem_filtration c n
        (filtration_monotone R B hkn hz), ih]

private theorem ApproxRightInverse.seq_eta_eq_of_le {f : AInfinityHom AA BB}
    (c : f.LinearHomotopyInverse) {k n : ℕ} (hkn : k ≤ n) {z : ReducedTensorWords R B}
    (hz : z ∈ filtration R B k) :
    (ApproxRightInverse.seq c n).eta z = (ApproxRightInverse.seq c k).eta z := by
  induction n, hkn using Nat.le_induction with
  | base => rfl
  | succ n hkn ih =>
      rw [ApproxRightInverse.seq_eta_succ_of_mem_filtration c n
        (filtration_monotone R B hkn hz), ih]

private theorem ApproxRightInverse.approxZero_phi_ofLetter (f : AInfinityHom AA BB) (b : B) :
    (ApproxRightInverse.approxZero f).phi (ofLetter R B b) = 0 := by
  simp only [ApproxRightInverse.phi, ApproxRightInverse.errMorphism, ApproxRightInverse.barG,
    ApproxRightInverse.approxZero, LinearMap.neg_apply, LinearMap.comp_apply,
    LinearMap.sub_apply, BB.barDifferential_ofLetter, coalgHom_ofLetter, LinearMap.zero_apply,
    map_zero, sub_self, neg_zero]

private theorem ApproxRightInverse.approxZero_psi_ofLetter (f : AInfinityHom AA BB) (b : B) :
    (ApproxRightInverse.approxZero f).psi (ofLetter R B b) = b := by
  simp only [ApproxRightInverse.psi, ApproxRightInverse.errHomotopy, ApproxRightInverse.barG,
    ApproxRightInverse.barH, ApproxRightInverse.approxZero, LinearMap.comp_apply,
    LinearMap.sub_apply, LinearMap.add_apply, LinearMap.id_apply, BB.barDifferential_ofLetter,
    coalgHom_ofLetter, gradedCoderivAlong_ofLetter, LinearMap.zero_apply, map_zero, add_zero,
    sub_zero, letter_ofLetter]

private theorem ApproxRightInverse.seq_one_gamma_ofLetter {f : AInfinityHom AA BB}
    (c : f.LinearHomotopyInverse) (b : B) :
    (ApproxRightInverse.seq c 1).gamma (ofLetter R B b) = c.inv b := by
  rw [ApproxRightInverse.seq, ApproxRightInverse.seq, ApproxRightInverse.step, LinearMap.add_apply,
    ApproxRightInverse.deltaGamma, LinearMap.add_apply, LinearMap.comp_apply, LinearMap.comp_apply,
    ApproxRightInverse.approxZero_phi_ofLetter, ApproxRightInverse.approxZero_psi_ofLetter,
    map_zero, add_zero]
  simp only [ApproxRightInverse.approxZero, LinearMap.zero_apply, zero_add]

private theorem ApproxRightInverse.seq_one_eta_ofLetter {f : AInfinityHom AA BB}
    (c : f.LinearHomotopyInverse) (b : B) :
    (ApproxRightInverse.seq c 1).eta (ofLetter R B b) = c.homotopyRight b := by
  rw [ApproxRightInverse.seq, ApproxRightInverse.seq, ApproxRightInverse.step, LinearMap.add_apply,
    ApproxRightInverse.deltaEta, LinearMap.sub_apply, LinearMap.comp_apply, LinearMap.comp_apply,
    ApproxRightInverse.approxZero_phi_ofLetter, ApproxRightInverse.approxZero_psi_ofLetter,
    map_zero, sub_zero]
  simp only [ApproxRightInverse.approxZero, LinearMap.zero_apply, zero_add]

/-! ### Assembling the A-infinity homotopy inverse -/

private noncomputable def invTaylor {f : AInfinityHom AA BB} (c : f.LinearHomotopyInverse) :
    ReducedTensorWords R B →ₗ[R] A :=
  DirectSum.toModule R {k : ℕ // 0 < k} _ fun k ↦ (ApproxRightInverse.seq c k.1).gamma ∘ₗ of R B k

private noncomputable def invHomotopyTaylor {f : AInfinityHom AA BB}
    (c : f.LinearHomotopyInverse) : ReducedTensorWords R B →ₗ[R] B :=
  DirectSum.toModule R {k : ℕ // 0 < k} _ fun k ↦ (ApproxRightInverse.seq c k.1).eta ∘ₗ of R B k

private theorem invTaylor_apply_of_mem_filtration {f : AInfinityHom AA BB}
    (c : f.LinearHomotopyInverse) {n : ℕ} {z : ReducedTensorWords R B}
    (hz : z ∈ filtration R B n) : invTaylor c z = (ApproxRightInverse.seq c n).gamma z := by
  suffices hle : filtration R B n ≤
      LinearMap.eqLocus (invTaylor c) (ApproxRightInverse.seq c n).gamma from hle hz
  rw [filtration_le_iff]
  rintro k hk _ ⟨x, rfl⟩
  rw [LinearMap.mem_eqLocus, invTaylor, toModule_of, LinearMap.comp_apply,
    ApproxRightInverse.seq_gamma_eq_of_le c hk (of_mem_filtration R B le_rfl x)]

private theorem invHomotopyTaylor_apply_of_mem_filtration {f : AInfinityHom AA BB}
    (c : f.LinearHomotopyInverse) {n : ℕ} {z : ReducedTensorWords R B}
    (hz : z ∈ filtration R B n) : invHomotopyTaylor c z = (ApproxRightInverse.seq c n).eta z := by
  suffices hle : filtration R B n ≤
      LinearMap.eqLocus (invHomotopyTaylor c) (ApproxRightInverse.seq c n).eta from hle hz
  rw [filtration_le_iff]
  rintro k hk _ ⟨x, rfl⟩
  rw [LinearMap.mem_eqLocus, invHomotopyTaylor, toModule_of, LinearMap.comp_apply,
    ApproxRightInverse.seq_eta_eq_of_le c hk (of_mem_filtration R B le_rfl x)]

private theorem coalgHom_invTaylor_apply_of_mem_filtration {f : AInfinityHom AA BB}
    (c : f.LinearHomotopyInverse) {n : ℕ} {z : ReducedTensorWords R B}
    (hz : z ∈ filtration R B n) :
    coalgHom R (invTaylor c) z = coalgHom R (ApproxRightInverse.seq c n).gamma z :=
  (isCoalgHom_coalgHom _).apply_eq_of_mem_filtration (isCoalgHom_coalgHom _)
    (fun _ hu ↦ by
      rw [← LinearMap.comp_apply (letter R A), letter_comp_coalgHom,
        ← LinearMap.comp_apply (letter R A), letter_comp_coalgHom,
        invTaylor_apply_of_mem_filtration c hu]) hz

private theorem isHomogeneous_invTaylor {f : AInfinityHom AA BB} (c : f.LinearHomotopyInverse) :
    LinearMap.IsHomogeneous (invTaylor c) (gradedPiece (BB.grading.shift 1))
      (AA.grading.shift 1).piece 0 := by
  rw [LinearMap.isHomogeneous_def]
  intro p z hz
  obtain ⟨n, hn⟩ := exists_mem_filtration R B z
  rw [invTaylor_apply_of_mem_filtration c hn]
  exact (ApproxRightInverse.seq c n).isHomogeneous_gamma.map_mem hz

private theorem isHomogeneous_invHomotopyTaylor {f : AInfinityHom AA BB}
    (c : f.LinearHomotopyInverse) :
    LinearMap.IsHomogeneous (invHomotopyTaylor c) (gradedPiece (BB.grading.shift 1))
      (BB.grading.shift 1).piece (-1) := by
  rw [LinearMap.isHomogeneous_def]
  intro p z hz
  obtain ⟨n, hn⟩ := exists_mem_filtration R B z
  rw [invHomotopyTaylor_apply_of_mem_filtration c hn]
  exact (ApproxRightInverse.seq c n).isHomogeneous_eta.map_mem hz

private theorem taylor_comp_coalgHom_invTaylor {f : AInfinityHom AA BB}
    (c : f.LinearHomotopyInverse) :
    AA.taylor ∘ₗ coalgHom R (invTaylor c) = invTaylor c ∘ₗ BB.barDifferential := by
  refine LinearMap.ext fun z ↦ ?_
  obtain ⟨n, hn⟩ := exists_mem_filtration R B z
  have he := congrArg (letter R A) ((ApproxRightInverse.seq c n).errMorphism_zero z hn)
  rw [LinearMap.sub_apply, map_sub, map_zero, sub_eq_zero, LinearMap.comp_apply,
    LinearMap.comp_apply, ← LinearMap.comp_apply (letter R A), AA.letter_comp_barDifferential,
    ← LinearMap.comp_apply (letter R A), letter_comp_coalgHom] at he
  rw [LinearMap.comp_apply, LinearMap.comp_apply, coalgHom_invTaylor_apply_of_mem_filtration c hn,
    he, invTaylor_apply_of_mem_filtration c (BB.barDifferential_mem_filtration hn)]

/-- **The `A∞` homotopy inverse of `f` lifting graded chain-homotopy inverse data `c`.** -/
noncomputable def homotopyInverse (f : AInfinityHom AA BB) (c : f.LinearHomotopyInverse) :
    AInfinityHom BB AA :=
  ofTaylor (invTaylor c) (isHomogeneous_invTaylor c) (taylor_comp_coalgHom_invTaylor c)

/-- The linear part of `f.homotopyInverse c` is `c.inv`. -/
@[simp]
theorem linearPart_homotopyInverse (f : AInfinityHom AA BB) (c : f.LinearHomotopyInverse) :
    (f.homotopyInverse c).linearPart = c.inv := by
  refine LinearMap.ext fun b ↦ ?_
  rw [linearPart_apply, homotopyInverse, taylor_ofTaylor,
    invTaylor_apply_of_mem_filtration c (ofLetter_mem_filtration R B b),
    ApproxRightInverse.seq_one_gamma_ofLetter]

private theorem rightHomotopy_taylor_eq (f : AInfinityHom AA BB) (c : f.LinearHomotopyInverse) :
    (AInfinityHom.id BB).taylor - (f.comp (f.homotopyInverse c)).taylor =
      BB.taylor ∘ₗ gradedCoderivAlong (BB.grading.shift 1) 1
        (AInfinityHom.id BB).barMap (f.comp (f.homotopyInverse c)).barMap (invHomotopyTaylor c) +
      invHomotopyTaylor c ∘ₗ BB.barDifferential := by
  refine LinearMap.ext fun z ↦ ?_
  obtain ⟨n, hn⟩ := exists_mem_filtration R B z
  have hFG : ∀ w ∈ filtration R B n,
      (f.comp (f.homotopyInverse c)).barMap w =
        (f.barMap ∘ₗ coalgHom R (ApproxRightInverse.seq c n).gamma) w := fun w hw ↦ by
    rw [barMap_comp, LinearMap.comp_apply, LinearMap.comp_apply, homotopyInverse, barMap_ofTaylor,
      coalgHom_invTaylor_apply_of_mem_filtration c hw]
  have hH : gradedCoderivAlong (BB.grading.shift 1) 1 (AInfinityHom.id BB).barMap
        (f.comp (f.homotopyInverse c)).barMap (invHomotopyTaylor c) z =
      gradedCoderivAlong (BB.grading.shift 1) 1 LinearMap.id
        (f.barMap ∘ₗ coalgHom R (ApproxRightInverse.seq c n).gamma)
        (ApproxRightInverse.seq c n).eta z :=
    gradedCoderivAlong_apply_eq_of_mem_filtration (BB.grading.shift 1) 1
      (fun _ _ ↦ by rw [barMap_id]) hFG
      (fun _ hw ↦ invHomotopyTaylor_apply_of_mem_filtration c hw) hn
  have hr := congrArg (letter R B) ((ApproxRightInverse.seq c n).errHomotopy_zero z hn)
  have hlD := LinearMap.congr_fun BB.letter_comp_barDifferential
    (gradedCoderivAlong (BB.grading.shift 1) 1 LinearMap.id
      (f.barMap ∘ₗ coalgHom R (ApproxRightInverse.seq c n).gamma)
      (ApproxRightInverse.seq c n).eta z)
  have hlH := LinearMap.congr_fun
    (letter_comp_gradedCoderivAlong (BB.grading.shift 1) 1 LinearMap.id
      (f.barMap ∘ₗ coalgHom R (ApproxRightInverse.seq c n).gamma) (ApproxRightInverse.seq c n).eta)
    (BB.barDifferential z)
  simp only [LinearMap.sub_apply, LinearMap.add_apply, LinearMap.comp_apply, LinearMap.id_apply,
    map_sub, map_add, map_zero, sub_eq_zero] at hr hlD hlH
  rw [hlD, hlH] at hr
  rw [LinearMap.sub_apply, LinearMap.add_apply, LinearMap.comp_apply, LinearMap.comp_apply, hH,
    invHomotopyTaylor_apply_of_mem_filtration c (BB.barDifferential_mem_filtration hn), ← hr]
  simp only [taylor_def, LinearMap.comp_apply, barMap_id, LinearMap.id_apply, hFG z hn]

/-- The right homotopy from `id BB` to `f.comp (f.homotopyInverse c)` constructed alongside
`f.homotopyInverse c`, with arity-one component `c.homotopyRight`. -/
noncomputable def idCompHomotopyInverseHomotopy (f : AInfinityHom AA BB)
    (c : f.LinearHomotopyInverse) :
    Homotopy (AInfinityHom.id BB) (f.comp (f.homotopyInverse c)) :=
  Homotopy.ofTaylor (invHomotopyTaylor c) (isHomogeneous_invHomotopyTaylor c)
    (rightHomotopy_taylor_eq f c)

/-- The arity-one component of `f.idCompHomotopyInverseHomotopy c` is `c.homotopyRight`. -/
@[simp]
theorem linearHomotopy_idCompHomotopyInverseHomotopy (f : AInfinityHom AA BB)
    (c : f.LinearHomotopyInverse) :
    (f.idCompHomotopyInverseHomotopy c).linearHomotopy = c.homotopyRight := by
  refine LinearMap.ext fun b ↦ ?_
  rw [Homotopy.linearHomotopy_apply, idCompHomotopyInverseHomotopy, Homotopy.taylor_ofTaylor,
    invHomotopyTaylor_apply_of_mem_filtration c (ofLetter_mem_filtration R B b),
    ApproxRightInverse.seq_one_eta_ofLetter]

/-- The right `A∞` homotopy witnessing `(f.comp (f.homotopyInverse c)).Homotopic (id BB)`. -/
noncomputable def compHomotopyInverseHomotopy (f : AInfinityHom AA BB)
    (c : f.LinearHomotopyInverse) :
    Homotopy (f.comp (f.homotopyInverse c)) (AInfinityHom.id BB) :=
  (f.idCompHomotopyInverseHomotopy c).symm

/-- The left `A∞` homotopy witnessing `((f.homotopyInverse c).comp f).Homotopic (id AA)`. -/
noncomputable def homotopyInverseCompHomotopy (f : AInfinityHom AA BB)
    (c : f.LinearHomotopyInverse) :
    Homotopy ((f.homotopyInverse c).comp f) (AInfinityHom.id AA) := by
  let g := f.homotopyInverse c
  let c' := c.symm (f.linearPart_homotopyInverse c)
  let f' := g.homotopyInverse c'
  let H_right : Homotopy (AInfinityHom.id BB) (f.comp g) := f.idCompHomotopyInverseHomotopy c
  let H'_right : Homotopy (AInfinityHom.id AA) (g.comp f') := g.idCompHomotopyInverseHomotopy c'
  let Hf₁ : Homotopy f' (f.comp (g.comp f')) :=
    (H_right.compLeft f').copy (id_comp f') (comp_assoc f g f')
  let Hf₂ : Homotopy (f.comp (g.comp f')) f :=
    (H'_right.compRight f).symm.copy rfl (comp_id f)
  exact (H'_right.trans ((Hf₁.trans Hf₂).compRight g)).symm

/-- An `A∞` morphism whose linear part admits a graded chain-homotopy inverse is an `A∞` homotopy
equivalence. -/
theorem isHomotopyEquiv_of_linearHomotopyInverse (f : AInfinityHom AA BB)
    (c : f.LinearHomotopyInverse) : f.IsHomotopyEquiv :=
  ⟨f.homotopyInverse c, (f.homotopyInverseCompHomotopy c).homotopic,
    (f.compHomotopyInverseHomotopy c).homotopic⟩

/-- The `A∞` homotopy inverse `f.homotopyInverse c` is itself a homotopy equivalence. -/
@[simp]
theorem isHomotopyEquiv_homotopyInverse (f : AInfinityHom AA BB)
    (c : f.LinearHomotopyInverse) : (f.homotopyInverse c).IsHomotopyEquiv :=
  ⟨f, (f.compHomotopyInverseHomotopy c).homotopic,
    (f.homotopyInverseCompHomotopy c).homotopic⟩

/-- **Whitehead theorem for `A∞` morphisms over a commutative ring**: an `A∞` morphism is a
homotopy equivalence if and only if its linear part admits a graded chain-homotopy inverse. -/
theorem isHomotopyEquiv_iff_nonempty_linearHomotopyInverse (f : AInfinityHom AA BB) :
    f.IsHomotopyEquiv ↔ Nonempty f.LinearHomotopyInverse :=
  ⟨IsHomotopyEquiv.nonempty_linearHomotopyInverse,
    fun ⟨c⟩ ↦ f.isHomotopyEquiv_of_linearHomotopyInverse c⟩

end CommRing

/-! ### Homotopy inverses of quasi-isomorphisms over a field -/

section Field

variable {K : Type uK} [Field K]

section SingleAlgebra

variable {A : Type uA} [AddCommGroup A] [Module K A]

private theorem isHomogeneous_differential_field (𝒜 : AInfinityAlgebra K A) :
    LinearMap.IsHomogeneous 𝒜.differential 𝒜.grading.piece 𝒜.grading.piece 1 :=
  LinearMap.isHomogeneous_def.2 fun _ _ hx ↦ 𝒜.differential_mem_piece hx

private noncomputable def unaryHomologyContraction (𝒜 : AInfinityAlgebra K A) :
    LinearSpecialContraction 𝒜.differential
      (0 : Module.End K (𝒜.differential.homology 𝒜.differential_comp_self_eq_zero)) :=
  𝒜.grading.homologyContraction (isHomogeneous_differential_field 𝒜)
    𝒜.differential_comp_self_eq_zero

private theorem isHomogeneous_cohomologyEquivHomology_field (𝒜 : AInfinityAlgebra K A) :
    LinearMap.IsHomogeneous (𝒜.cohomologyEquivHomology : 𝒜.Cohomology →ₗ[K] _)
      𝒜.cohomologyGrading.piece
      (𝒜.grading.homology (isHomogeneous_differential_field 𝒜)
        𝒜.differential_comp_self_eq_zero).piece 0 :=
  LinearMap.isHomogeneous_def.2 fun _ _ hc ↦ by
    obtain ⟨x, hx, hp, rfl⟩ := 𝒜.mem_cohomologyGrading_piece_iff.1 hc
    rw [add_zero, LinearEquiv.coe_coe, AInfinityAlgebra.cohomologyEquivHomology_cohomologyClass]
    exact 𝒜.grading.homologyπ_mem_homology_piece _ _ hp

private theorem isHomogeneous_cohomologyEquivHomology_symm_field (𝒜 : AInfinityAlgebra K A) :
    LinearMap.IsHomogeneous (𝒜.cohomologyEquivHomology.symm : _ →ₗ[K] 𝒜.Cohomology)
      (𝒜.grading.homology (isHomogeneous_differential_field 𝒜)
        𝒜.differential_comp_self_eq_zero).piece
      𝒜.cohomologyGrading.piece 0 :=
  LinearMap.isHomogeneous_def.2 fun _ _ hy ↦ by
    obtain ⟨z, hz, rfl⟩ := (𝒜.grading.mem_homology_piece_iff _ _).1 hy
    rw [add_zero, LinearEquiv.coe_coe,
      AInfinityAlgebra.cohomologyEquivHomology_symm_homologyπ]
    exact 𝒜.cohomologyClass_mem_cohomologyGrading_piece _ hz

end SingleAlgebra

variable {A : Type uA} {B : Type uB}
  [AddCommGroup A] [Module K A]
  [AddCommGroup B] [Module K B]
  {AA : AInfinityAlgebra K A} {BB : AInfinityAlgebra K B}

private theorem linearPart_mem_ker_differential (f : AInfinityHom AA BB) {z : A}
    (hz : z ∈ LinearMap.ker AA.differential) :
    f.linearPart z ∈ LinearMap.ker BB.differential := by
  rw [← BB.cycles_def]
  exact f.linearPart_mem_cycles (by rwa [AA.cycles_def])

namespace IsQuasiIso

private noncomputable def homologyEquivInv {f : AInfinityHom AA BB} (hf : f.IsQuasiIso) :
    BB.differential.homology BB.differential_comp_self_eq_zero →ₗ[K]
      AA.differential.homology AA.differential_comp_self_eq_zero :=
  AA.cohomologyEquivHomology.toLinearMap ∘ₗ
    hf.cohomologyLinearEquiv.symm.toLinearMap ∘ₗ
      BB.cohomologyEquivHomology.symm.toLinearMap

private theorem isHomogeneous_homologyEquivInv {f : AInfinityHom AA BB} (hf : f.IsQuasiIso) :
    LinearMap.IsHomogeneous hf.homologyEquivInv
      (BB.grading.homology (isHomogeneous_differential_field BB)
        BB.differential_comp_self_eq_zero).piece
      (AA.grading.homology (isHomogeneous_differential_field AA)
        AA.differential_comp_self_eq_zero).piece 0 := by
  have hinv : LinearMap.IsHomogeneous hf.cohomologyLinearEquiv.symm.toLinearMap
      BB.cohomologyGrading.piece AA.cohomologyGrading.piece 0 :=
    LinearMap.isHomogeneous_def.2 fun _ _ hc ↦ by
      simpa only [add_zero, LinearEquiv.coe_coe, ← cohomologyMapInv_apply] using
        hf.cohomologyMapInv_mem_cohomologyGrading_piece hc
  rw [homologyEquivInv]
  simpa only [add_zero] using (isHomogeneous_cohomologyEquivHomology_field AA).comp
    (hinv.comp (isHomogeneous_cohomologyEquivHomology_symm_field BB))

private theorem homologyEquivInv_homologyπ_linearPart {f : AInfinityHom AA BB}
    (hf : f.IsQuasiIso) {z : A} (hz : z ∈ LinearMap.ker AA.differential) :
    hf.homologyEquivInv (BB.differential.homologyπ BB.differential_comp_self_eq_zero
      ⟨f.linearPart z, linearPart_mem_ker_differential f hz⟩) =
      AA.differential.homologyπ AA.differential_comp_self_eq_zero ⟨z, hz⟩ := by
  have hzA : z ∈ AA.cycles := by rwa [AA.cycles_def]
  have hclass : hf.cohomologyLinearEquiv.symm
      (BB.cohomologyClass (f.linearPart_mem_cycles hzA)) = AA.cohomologyClass hzA := by
    apply hf.cohomologyLinearEquiv.injective
    rw [LinearEquiv.apply_symm_apply, cohomologyLinearEquiv_apply, cohomologyMap_cohomologyClass]
  simp only [homologyEquivInv, LinearMap.comp_apply, LinearEquiv.coe_coe,
    AInfinityAlgebra.cohomologyEquivHomology_symm_homologyπ, hclass,
    AInfinityAlgebra.cohomologyEquivHomology_cohomologyClass]

private theorem homologyπ_linearPart_incl_homologyEquivInv {f : AInfinityHom AA BB}
    (hf : f.IsQuasiIso) (y : BB.differential.homology BB.differential_comp_self_eq_zero) :
    BB.differential.homologyπ BB.differential_comp_self_eq_zero
      ⟨f.linearPart ((unaryHomologyContraction AA).incl (hf.homologyEquivInv y)),
        linearPart_mem_ker_differential f (AA.grading.homologyContraction_incl_mem_ker
          (isHomogeneous_differential_field AA) AA.differential_comp_self_eq_zero _)⟩ = y := by
  obtain ⟨⟨b, hb⟩, rfl⟩ := BB.differential.homologyπ_surjective BB.differential_comp_self_eq_zero y
  have hb' : b ∈ BB.cycles := by rwa [BB.cycles_def]
  set x := hf.cohomologyLinearEquiv.symm (BB.cohomologyClass hb')
  have hx_eq : f.cohomologyMap x = BB.cohomologyClass hb' := by
    rw [← cohomologyLinearEquiv_apply hf, LinearEquiv.apply_symm_apply]
  have hinc_ker := AA.grading.homologyContraction_incl_mem_ker
    (isHomogeneous_differential_field AA) AA.differential_comp_self_eq_zero
    (AA.cohomologyEquivHomology x)
  have hinc_cyc : (unaryHomologyContraction AA).incl (AA.cohomologyEquivHomology x) ∈ AA.cycles :=
    (congrArg (_ ∈ ·) AA.cycles_def).mpr hinc_ker
  have hclass_inc : AA.cohomologyClass hinc_cyc = x := by
    apply AA.cohomologyEquivHomology.injective
    rw [AInfinityAlgebra.cohomologyEquivHomology_cohomologyClass]
    exact AA.grading.homologyπ_homologyContraction_incl _ _ _
  have heq_inv : hf.homologyEquivInv
      (BB.differential.homologyπ BB.differential_comp_self_eq_zero ⟨b, hb⟩) =
      AA.cohomologyEquivHomology x := by
    simp only [homologyEquivInv, x, LinearMap.comp_apply, LinearEquiv.coe_coe,
      AInfinityAlgebra.cohomologyEquivHomology_symm_homologyπ]
  simp_rw [heq_inv]
  apply BB.cohomologyEquivHomology.symm.injective
  rw [AInfinityAlgebra.cohomologyEquivHomology_symm_homologyπ,
    AInfinityAlgebra.cohomologyEquivHomology_symm_homologyπ]
  calc
    BB.cohomologyClass _ = f.cohomologyMap (AA.cohomologyClass hinc_cyc) :=
      (cohomologyMap_cohomologyClass f hinc_cyc).symm
    _ = BB.cohomologyClass _ := by rw [hclass_inc, hx_eq]

private noncomputable def homologyLinearInv {f : AInfinityHom AA BB} (hf : f.IsQuasiIso) :
    B →ₗ[K] A :=
  (unaryHomologyContraction AA).incl ∘ₗ hf.homologyEquivInv ∘ₗ (unaryHomologyContraction BB).proj

private noncomputable def homologyPhi {f : AInfinityHom AA BB} (hf : f.IsQuasiIso) :
    A →ₗ[K] AA.differential.homology AA.differential_comp_self_eq_zero :=
  (unaryHomologyContraction AA).proj -
    hf.homologyEquivInv ∘ₗ (unaryHomologyContraction BB).proj ∘ₗ f.linearPart

private noncomputable def homologyPsi {f : AInfinityHom AA BB} (hf : f.IsQuasiIso) :
    BB.differential.homology BB.differential_comp_self_eq_zero →ₗ[K] B :=
  (unaryHomologyContraction BB).incl -
    f.linearPart ∘ₗ (unaryHomologyContraction AA).incl ∘ₗ hf.homologyEquivInv

private theorem isHomogeneous_homologyPhi {f : AInfinityHom AA BB} (hf : f.IsQuasiIso) :
    LinearMap.IsHomogeneous hf.homologyPhi AA.grading.piece
      (AA.grading.homology (isHomogeneous_differential_field AA)
        AA.differential_comp_self_eq_zero).piece 0 := by
  rw [homologyPhi, unaryHomologyContraction, unaryHomologyContraction]
  refine (AA.grading.isHomogeneous_homologyContraction_proj _ _).sub ?_
  have h₁ := (BB.grading.isHomogeneous_homologyContraction_proj
    (isHomogeneous_differential_field BB) BB.differential_comp_self_eq_zero).comp
    f.isHomogeneous_linearPart
  simpa only [add_zero] using hf.isHomogeneous_homologyEquivInv.comp h₁

private theorem isHomogeneous_homologyPsi {f : AInfinityHom AA BB} (hf : f.IsQuasiIso) :
    LinearMap.IsHomogeneous hf.homologyPsi
      (BB.grading.homology (isHomogeneous_differential_field BB)
        BB.differential_comp_self_eq_zero).piece BB.grading.piece 0 := by
  rw [homologyPsi, unaryHomologyContraction, unaryHomologyContraction]
  refine (BB.grading.isHomogeneous_homologyContraction_incl _ _).sub ?_
  have h₁ := (AA.grading.isHomogeneous_homologyContraction_incl
    (isHomogeneous_differential_field AA) AA.differential_comp_self_eq_zero).comp
    hf.isHomogeneous_homologyEquivInv
  simpa only [add_zero] using f.isHomogeneous_linearPart.comp h₁

private theorem homologyPhi_eq {f : AInfinityHom AA BB} (hf : f.IsQuasiIso) :
    hf.homologyPhi =
      hf.homologyPhi ∘ₗ (unaryHomologyContraction AA).homotopy ∘ₗ AA.differential := by
  have hker : ∀ z ∈ LinearMap.ker AA.differential, hf.homologyPhi z = 0 := fun z hz ↦ by
    simp only [homologyPhi, unaryHomologyContraction, LinearMap.sub_apply, LinearMap.comp_apply,
      InternalGrading.homologyContraction_proj_of_mem_ker _ _ _ hz,
      InternalGrading.homologyContraction_proj_of_mem_ker _ _ _
        (linearPart_mem_ker_differential f hz),
      hf.homologyEquivInv_homologyπ_linearPart hz, sub_self]
  refine LinearMap.ext fun x ↦ ?_
  simp only [LinearMap.comp_apply]
  rw [← sub_eq_zero, ← map_sub]
  refine hker _ ?_
  have hc := LinearMap.congr_fun
    (unaryHomologyContraction AA).dM_comp_homotopy_add_homotopy_comp_dM (AA.differential x)
  have hdd := LinearMap.congr_fun AA.differential_comp_self_eq_zero x
  have hpd := LinearMap.congr_fun (unaryHomologyContraction AA).proj_comp_dM x
  simp only [LinearMap.add_apply, LinearMap.sub_apply, LinearMap.comp_apply, LinearMap.id_apply,
    LinearMap.zero_apply] at hc hdd hpd
  rw [LinearMap.mem_ker, map_sub]
  rw [hdd, map_zero, add_zero, hpd, map_zero, sub_zero] at hc
  rw [hc, sub_self]

private theorem homologyPsi_eq {f : AInfinityHom AA BB} (hf : f.IsQuasiIso) :
    BB.differential ∘ₗ ((unaryHomologyContraction BB).homotopy ∘ₗ hf.homologyPsi) =
      hf.homologyPsi := by
  have hdA : AA.differential ∘ₗ (unaryHomologyContraction AA).incl = 0 := by
    rw [(unaryHomologyContraction AA).dM_comp_incl, LinearMap.comp_zero]
  have hdB : BB.differential ∘ₗ (unaryHomologyContraction BB).incl = 0 := by
    rw [(unaryHomologyContraction BB).dM_comp_incl, LinearMap.comp_zero]
  refine LinearMap.ext fun y ↦ ?_
  have hy_ker : hf.homologyPsi y ∈ LinearMap.ker BB.differential := by
    have eB := LinearMap.congr_fun hdB y
    have ef := LinearMap.congr_fun (differential_comp_linearPart f)
      ((unaryHomologyContraction AA).incl (hf.homologyEquivInv y))
    have eA := LinearMap.congr_fun hdA (hf.homologyEquivInv y)
    simp only [LinearMap.comp_apply, LinearMap.zero_apply] at eB ef eA
    rw [homologyPsi, LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.comp_apply,
      LinearMap.comp_apply, map_sub, eB, ef, eA, map_zero, sub_zero]
  have hy_proj : (unaryHomologyContraction BB).proj (hf.homologyPsi y) = 0 := by
    have hp := LinearMap.congr_fun (unaryHomologyContraction BB).proj_comp_incl y
    simp only [LinearMap.comp_apply, LinearMap.id_apply] at hp
    have hzB : f.linearPart ((unaryHomologyContraction AA).incl (hf.homologyEquivInv y)) ∈
        LinearMap.ker BB.differential :=
      linearPart_mem_ker_differential f (AA.grading.homologyContraction_incl_mem_ker _ _ _)
    rw [homologyPsi, LinearMap.sub_apply, LinearMap.comp_apply, LinearMap.comp_apply, map_sub, hp]
    rw [unaryHomologyContraction, InternalGrading.homologyContraction_proj_of_mem_ker _ _ _ hzB,
      hf.homologyπ_linearPart_incl_homologyEquivInv y, sub_self]
  have hc := LinearMap.congr_fun
    (unaryHomologyContraction BB).dM_comp_homotopy_add_homotopy_comp_dM (hf.homologyPsi y)
  simp only [LinearMap.add_apply, LinearMap.sub_apply, LinearMap.comp_apply, LinearMap.id_apply,
    LinearMap.mem_ker.1 hy_ker, map_zero, add_zero, hy_proj, sub_zero] at hc
  exact hc

private theorem id_sub_homologyLinearInv_comp {f : AInfinityHom AA BB} (hf : f.IsQuasiIso) :
    LinearMap.id - hf.homologyLinearInv ∘ₗ f.linearPart =
      AA.differential ∘ₗ ((unaryHomologyContraction AA).homotopy +
          (unaryHomologyContraction AA).incl ∘ₗ hf.homologyPhi ∘ₗ
            (unaryHomologyContraction AA).homotopy) +
        ((unaryHomologyContraction AA).homotopy +
          (unaryHomologyContraction AA).incl ∘ₗ hf.homologyPhi ∘ₗ
            (unaryHomologyContraction AA).homotopy) ∘ₗ AA.differential := by
  set cA := unaryHomologyContraction AA
  have hdA : AA.differential ∘ₗ cA.incl = 0 := by rw [cA.dM_comp_incl, LinearMap.comp_zero]
  have h₁ : AA.differential ∘ₗ (cA.incl ∘ₗ hf.homologyPhi ∘ₗ cA.homotopy) +
      (cA.incl ∘ₗ hf.homologyPhi ∘ₗ cA.homotopy) ∘ₗ AA.differential =
      cA.incl ∘ₗ hf.homologyPhi := by
    rw [← LinearMap.comp_assoc, hdA, LinearMap.zero_comp, zero_add, LinearMap.comp_assoc,
      LinearMap.comp_assoc, ← hf.homologyPhi_eq]
  calc
    LinearMap.id - hf.homologyLinearInv ∘ₗ f.linearPart =
        (LinearMap.id - cA.incl ∘ₗ cA.proj) + cA.incl ∘ₗ hf.homologyPhi := by
      simp only [homologyLinearInv, homologyPhi, cA, LinearMap.comp_sub, LinearMap.comp_assoc]
      abel
    _ = _ := by
      rw [← cA.dM_comp_homotopy_add_homotopy_comp_dM, ← h₁, LinearMap.comp_add, LinearMap.add_comp]
      abel

private theorem id_sub_comp_homologyLinearInv {f : AInfinityHom AA BB} (hf : f.IsQuasiIso) :
    LinearMap.id - f.linearPart ∘ₗ hf.homologyLinearInv =
      BB.differential ∘ₗ ((unaryHomologyContraction BB).homotopy +
          (unaryHomologyContraction BB).homotopy ∘ₗ hf.homologyPsi ∘ₗ
            (unaryHomologyContraction BB).proj) +
        ((unaryHomologyContraction BB).homotopy +
          (unaryHomologyContraction BB).homotopy ∘ₗ hf.homologyPsi ∘ₗ
            (unaryHomologyContraction BB).proj) ∘ₗ BB.differential := by
  set cB := unaryHomologyContraction BB
  have hpdB : cB.proj ∘ₗ BB.differential = 0 := by rw [cB.proj_comp_dM, LinearMap.zero_comp]
  have h₂ : BB.differential ∘ₗ (cB.homotopy ∘ₗ hf.homologyPsi ∘ₗ cB.proj) +
      (cB.homotopy ∘ₗ hf.homologyPsi ∘ₗ cB.proj) ∘ₗ BB.differential =
      hf.homologyPsi ∘ₗ cB.proj :=
    LinearMap.ext fun y ↦ by
      have e₁ := LinearMap.congr_fun hf.homologyPsi_eq (cB.proj y)
      have e₂ := LinearMap.congr_fun hpdB y
      simp only [cB, LinearMap.add_apply, LinearMap.comp_apply, LinearMap.zero_apply] at e₁ e₂ ⊢
      rw [e₁, e₂, map_zero, map_zero, add_zero]
  calc
    LinearMap.id - f.linearPart ∘ₗ hf.homologyLinearInv =
        (LinearMap.id - cB.incl ∘ₗ cB.proj) + hf.homologyPsi ∘ₗ cB.proj := by
      simp only [homologyLinearInv, homologyPsi, cB, LinearMap.sub_comp, LinearMap.comp_assoc]
      abel
    _ = _ := by
      conv_lhs => rw [← cB.dM_comp_homotopy_add_homotopy_comp_dM, ← h₂]
      rw [LinearMap.comp_add, LinearMap.add_comp]
      abel

/-- Over a field, a quasi-isomorphism of `A∞` algebras induces graded chain-homotopy inverse data
on the unary complexes via the contractions onto homology. -/
noncomputable def linearHomotopyInverse {f : AInfinityHom AA BB} (hf : f.IsQuasiIso) :
    f.LinearHomotopyInverse where
  inv := hf.homologyLinearInv
  homotopyLeft := (unaryHomologyContraction AA).homotopy +
    (unaryHomologyContraction AA).incl ∘ₗ hf.homologyPhi ∘ₗ (unaryHomologyContraction AA).homotopy
  homotopyRight := (unaryHomologyContraction BB).homotopy +
    (unaryHomologyContraction BB).homotopy ∘ₗ hf.homologyPsi ∘ₗ (unaryHomologyContraction BB).proj
  isHomogeneous_inv := by
    rw [homologyLinearInv, unaryHomologyContraction, unaryHomologyContraction]
    have h₁ := hf.isHomogeneous_homologyEquivInv.comp
      (BB.grading.isHomogeneous_homologyContraction_proj
        (isHomogeneous_differential_field BB) BB.differential_comp_self_eq_zero)
    simpa only [add_zero] using (AA.grading.isHomogeneous_homologyContraction_incl _ _).comp h₁
  differential_comp_inv := by
    simp only [homologyLinearInv, ← LinearMap.comp_assoc,
      (unaryHomologyContraction AA).dM_comp_incl, LinearMap.comp_zero, LinearMap.zero_comp]
    simp only [LinearMap.comp_assoc, (unaryHomologyContraction BB).proj_comp_dM,
      LinearMap.zero_comp, LinearMap.comp_zero]
  isHomogeneous_homotopyLeft := by
    rw [unaryHomologyContraction]
    refine (AA.grading.isHomogeneous_homologyContraction_homotopy _ _).add ?_
    have h₁ := hf.isHomogeneous_homologyPhi.comp
      (AA.grading.isHomogeneous_homologyContraction_homotopy
        (isHomogeneous_differential_field AA) AA.differential_comp_self_eq_zero)
    simpa only [zero_add, add_zero] using
      (AA.grading.isHomogeneous_homologyContraction_incl _ _).comp h₁
  id_sub_inv_comp_linearPart := hf.id_sub_homologyLinearInv_comp
  isHomogeneous_homotopyRight := by
    rw [unaryHomologyContraction]
    refine (BB.grading.isHomogeneous_homologyContraction_homotopy _ _).add ?_
    have h₁ := hf.isHomogeneous_homologyPsi.comp
      (BB.grading.isHomogeneous_homologyContraction_proj
        (isHomogeneous_differential_field BB) BB.differential_comp_self_eq_zero)
    simpa only [zero_add, add_zero] using
      (BB.grading.isHomogeneous_homologyContraction_homotopy _ _).comp h₁
  id_sub_linearPart_comp_inv := hf.id_sub_comp_homologyLinearInv

/-- **Over a field, every quasi-isomorphism of `A∞` algebras admits an `A∞` homotopy inverse.** -/
noncomputable def homotopyInverse {f : AInfinityHom AA BB} (hf : f.IsQuasiIso) :
    AInfinityHom BB AA :=
  f.homotopyInverse hf.linearHomotopyInverse

/-- Left homotopy witnessing `(hf.homotopyInverse.comp f).Homotopic (id AA)`. -/
noncomputable def homotopyInverseCompHomotopy {f : AInfinityHom AA BB} (hf : f.IsQuasiIso) :
    Homotopy (hf.homotopyInverse.comp f) (AInfinityHom.id AA) :=
  f.homotopyInverseCompHomotopy hf.linearHomotopyInverse

/-- Right homotopy witnessing `(f.comp hf.homotopyInverse).Homotopic (id BB)`. -/
noncomputable def compHomotopyInverseHomotopy {f : AInfinityHom AA BB} (hf : f.IsQuasiIso) :
    Homotopy (f.comp hf.homotopyInverse) (AInfinityHom.id BB) :=
  f.compHomotopyInverseHomotopy hf.linearHomotopyInverse

/-- The `A∞` homotopy inverse of a quasi-isomorphism induces `hf.cohomologyMapInv` on
cohomology. -/
@[simp]
theorem cohomologyMap_homotopyInverse {f : AInfinityHom AA BB} (hf : f.IsQuasiIso) :
    hf.homotopyInverse.cohomologyMap = hf.cohomologyMapInv := by
  have heq := hf.homotopyInverseCompHomotopy.cohomologyMap_eq
  rw [cohomologyMap_comp, cohomologyMap_id] at heq
  ext c
  have h₁ := DFunLike.congr_fun hf.cohomologyMap_comp_cohomologyMapInv c
  have h₂ := DFunLike.congr_fun heq (hf.cohomologyMapInv c)
  simp only [NonUnitalAlgHom.comp_apply, NonUnitalAlgHom.coe_id, id_eq] at h₁ h₂
  exact (congrArg _ h₁.symm).trans h₂

/-- **Over a field, every quasi-isomorphism of `A∞` algebras is an `A∞` homotopy equivalence.** -/
theorem isHomotopyEquiv {f : AInfinityHom AA BB} (hf : f.IsQuasiIso) : f.IsHomotopyEquiv :=
  f.isHomotopyEquiv_of_linearHomotopyInverse hf.linearHomotopyInverse

/-- The `A∞` homotopy inverse `hf.homotopyInverse` of a quasi-isomorphism is itself a homotopy
equivalence. -/
@[simp]
theorem isHomotopyEquiv_homotopyInverse {f : AInfinityHom AA BB} (hf : f.IsQuasiIso) :
    hf.homotopyInverse.IsHomotopyEquiv :=
  f.isHomotopyEquiv_homotopyInverse hf.linearHomotopyInverse

/-- The `A∞` homotopy inverse `hf.homotopyInverse` of a quasi-isomorphism is itself a
quasi-isomorphism. -/
@[simp]
theorem isQuasiIso_homotopyInverse {f : AInfinityHom AA BB} (hf : f.IsQuasiIso) :
    hf.homotopyInverse.IsQuasiIso :=
  hf.isHomotopyEquiv_homotopyInverse.isQuasiIso

end IsQuasiIso

/-- **Whitehead theorem for `A∞` morphisms over a field**: an `A∞` morphism is a homotopy
equivalence if and only if it is a quasi-isomorphism. -/
theorem isHomotopyEquiv_iff_isQuasiIso (f : AInfinityHom AA BB) :
    f.IsHomotopyEquiv ↔ f.IsQuasiIso :=
  ⟨IsHomotopyEquiv.isQuasiIso, IsQuasiIso.isHomotopyEquiv⟩

end Field

end AInfinityHom

end TauCeti
