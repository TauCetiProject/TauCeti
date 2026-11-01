/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

import Mathlib.Analysis.Complex.Polynomial.Basic
public import TauCeti.RepresentationTheory.ClassicalGroups.Rational.SpecialLinear
public import TauCeti.RepresentationTheory.ClassicalGroups.SpecialLinear
public import TauCeti.RepresentationTheory.ClassicalGroups.Weight.CentralCharacter
public import TauCeti.RepresentationTheory.ClassicalGroups.WeylModule.Classification
public import TauCeti.RepresentationTheory.ClassicalGroups.WeylModule.Rational
public import TauCeti.RepresentationTheory.ClassicalGroups.WeylModule.Weight.HighestWeight

/-!
# Weyl modules restricted to the special linear group

The rational Weyl module `TauCeti.rationalWeylRep` of a dominant weight `λ` is the determinant
twist `det^{λₙ} ⊗ 𝕊^μ(kⁿ)` of the Weyl module of the polynomial part `μ` of `λ`, and that twist is
exactly what the special linear subgroup cannot see: `det` is constantly `1` on `SL n k`.  This
file restricts the Weyl modules along the inclusion `SL n k ↪ GL n k` and records that
invisibility.

The carrier-level form is `TauCeti.rationalWeylSLRep_eq_weylSLRepOfShape`: the rational Weyl
module of `λ` restricts to the Weyl module of its polynomial part
`TauCeti.DominantWeight.detShiftShape`, and here it is an equality of representations, not merely
an isomorphism, because `TauCeti.rationalWeylRep` is built on the carrier of that Weyl module.
The twist-by-twist form, which says the same thing for an arbitrary representation of `GL n k`, is
`TauCeti.tprodDetPowerSLEquiv`, beside the determinant powers themselves.

Rewriting the shape with `TauCeti.DominantWeight.detShiftShape_shift` turns the carrier-level form
into the statement that the restriction depends on `λ` only through its class modulo the constant
weights `m·(1, …, 1)`, and `TauCeti.DominantWeight.detShiftShape_eq_detShiftShape_iff` says that
the polynomial part is a complete invariant of that class.  Those classes are indexed by the Young
diagrams of at most `n - 1` rows
(`TauCeti.DominantWeight.colLen_zero_detShiftShape_le_pred` and
`TauCeti.DominantWeight.detShiftShape_weightOfShape`), so the Weyl modules of such diagrams
already exhaust the restrictions.  On the bundled representations, where there is no carrier to
rewrite, that invariance is stated outright as `TauCeti.rationalWeylSLFDRep_shift`.

Over `ℂ`, these restrictions are irreducible exactly when the shape has at most `n` rows.
In particular every rational Weyl module restricts irreducibly. The underlying restriction theorem
`Representation.isIrreducible_comp_toGL_iff` is available over any algebraically closed field.
Algebraic closure enters through that restriction theorem;
`TauCeti.isIrreducible_weylRepOfShape_iff` for the original `GL` module requires only a field of
characteristic zero.

Conversely, over an algebraically closed field of characteristic zero the restriction sees the
class of `λ` modulo the constant weights and nothing less: `V_λ` and `V_λ'` restrict to equivalent
representations of `SL n k` exactly when `λ' = λ + m·(1, …, 1)`
(`TauCeti.nonempty_equiv_rationalWeylSLRep_iff`). Scalar matrices act on `V_λ` by the power
`∑ᵢ λᵢ` of the scalar, so by `Representation.nonempty_equiv_comp_toGL_iff` an equivalence of the
restrictions is an equivalence of `GL n k`-representations between a determinant twist
`det ^ t ⊗ V_λ` and `V_λ'`; comparing highest weights gives `λ' = λ + t·(1, …, 1)`. Equivalently,
the Weyl modules of distinct Young diagrams with at most `n - 1` rows restrict to non-isomorphic
representations of `SL n k` (`TauCeti.nonempty_equiv_weylSLRepOfShape_iff`).

Over `ℂ` these restrictions are all the irreducible rational representations of `SL n ℂ`
(`TauCeti.IsRationalSLRep.exists_nonempty_equiv_rationalWeylSLRep`). The determinant-one scalar
matrices act on an irreducible `ρ` by a power character `z ↦ z ^ a`, so `ρ` extends to a
representation `Representation.extendToGL` of `GL n ℂ`, which is irreducible and again rational
(`TauCeti.IsRationalSLRep.isRationalRep_extendToGL`). The classification for `GL n ℂ` makes the
extension some `V_λ`, and restricting back gives `ρ`. Together with the injectivity above, this is
the theorem of the highest weight for `SL n ℂ`: the irreducible rational representations are
indexed by the Young diagrams with at most `n - 1` rows, equivalently by the dominant weights modulo
the constant weights (`TauCeti.IsRationalSLRep.existsUnique_nonempty_equiv_weylSLRepOfShape`).

## Main definitions

* `TauCeti.weylSLRepOfShape`: the Weyl module of a Young diagram, as a representation of
  `SL n k`, with `TauCeti.weylSLFDRepOfShape` its bundled form.
* `TauCeti.rationalWeylSLRep`: the rational Weyl module of a dominant weight, as a representation
  of `SL n k`, with `TauCeti.rationalWeylSLFDRep` its bundled form.

## Main results

* `TauCeti.rationalWeylSLRep_eq_weylSLRepOfShape`: **the determinant twist disappears on
  `SL n k`** -- the rational Weyl module of `λ` restricts to the Weyl module of the polynomial
  part of `λ`.
* `TauCeti.rationalWeylSLFDRep_shift`: **the restriction only depends on `λ` modulo the constant
  weights**.
* `TauCeti.isIrreducible_weylSLRepOfShape_iff`: over `ℂ`, the restriction is irreducible
  exactly when the shape has at most `n` rows.
* `TauCeti.simple_rationalWeylSLFDRep`: every rational Weyl module over `ℂ` stays simple
  on restriction.
* `TauCeti.nonempty_equiv_rationalWeylSLRep_iff` and
  `TauCeti.nonempty_iso_rationalWeylSLFDRep_iff`: **the restrictions of `V_λ` and `V_λ'` to
  `SL n k` are isomorphic exactly when `λ` and `λ'` differ by a constant weight.**
* `TauCeti.nonempty_equiv_weylSLRepOfShape_iff`: Young diagrams with at most `n - 1` rows are
  recovered from the restrictions of their Weyl modules to `SL n k`.
* `TauCeti.isRationalSLRep_weylSLRepOfShape`: the restricted Weyl modules are rational.
* `TauCeti.isRationalSLRep_rationalWeylSLRep`: the restrictions of the rational Weyl modules are
  rational.
* `TauCeti.IsRationalSLRep.exists_nonempty_equiv_rationalWeylSLRep`: **every irreducible rational
  representation of `SL n ℂ` is the restriction of a rational Weyl module.**
* `TauCeti.IsRationalSLRep.existsUnique_nonempty_equiv_weylSLRepOfShape` and
  `FDRep.existsUnique_nonempty_iso_weylSLFDRepOfShape`: **the highest-weight classification for
  `SL n ℂ`**, by the Young diagrams with at most `n - 1` rows.

## References

* W. Fulton and J. Harris, *Representation Theory: A First Course* (1991), Lecture 15, where the
  rational representations of `GL n` over an algebraically closed field of characteristic zero are
  the determinant twists of the polynomial ones and the irreducible representations of `SL n` are
  indexed by the dominant weights modulo `(1, …, 1)`.
-/

public section

universe u

namespace TauCeti

section CommRing

variable (k : Type u) [CommRing k] [Algebra ℚ k] (n : ℕ)

/-! ## The Weyl module of a shape -/

/-- **The Weyl module of a Young diagram as a representation of `SL n k`**, restricting
`TauCeti.weylRepOfShape` along the inclusion of the special linear group. -/
noncomputable def weylSLRepOfShape (μ : YoungDiagram) :
    Representation k (Matrix.SpecialLinearGroup (Fin n) k)
      ↥(weylModuleOfShape k n μ).toSubmodule :=
  (weylRepOfShape k n μ).comp Matrix.SpecialLinearGroup.toGL

@[simp]
theorem weylSLRepOfShape_apply (μ : YoungDiagram) (g : Matrix.SpecialLinearGroup (Fin n) k) :
    weylSLRepOfShape k n μ g = weylRepOfShape k n μ (Matrix.SpecialLinearGroup.toGL g) :=
  (rfl)

/-! ## The rational Weyl module of a dominant weight -/

/-- **The rational Weyl module of a dominant weight as a representation of `SL n k`**, restricting
`TauCeti.rationalWeylRep` along the inclusion of the special linear group. -/
noncomputable def rationalWeylSLRep (l : DominantWeight n) :
    Representation k (Matrix.SpecialLinearGroup (Fin n) k)
      ↥(weylModuleOfShape k n l.detShiftShape).toSubmodule :=
  (rationalWeylRep k n l).comp Matrix.SpecialLinearGroup.toGL

/-- The restricted action of a rational Weyl module, read at the image of the matrix.

This is deliberately not a `simp` lemma: `TauCeti.rationalWeylSLRep_eq_weylSLRepOfShape` is the
normal form, and it already rewrites the left-hand side here. -/
theorem rationalWeylSLRep_apply (l : DominantWeight n)
    (g : Matrix.SpecialLinearGroup (Fin n) k) :
    rationalWeylSLRep k n l g = rationalWeylRep k n l (Matrix.SpecialLinearGroup.toGL g) :=
  (rfl)

/-- **The determinant twist disappears on the special linear group**: the rational Weyl module of
a dominant weight `λ` restricts to the Weyl module of the polynomial part of `λ`.  The two are
equal, not merely isomorphic, because `TauCeti.rationalWeylRep` twists the action on the carrier
of that very Weyl module.

Rewriting the shape with `TauCeti.DominantWeight.detShiftShape_shift` turns this into the
statement that the restriction depends on `λ` only through its class modulo the constant weights
`m·(1, …, 1)`, and `TauCeti.DominantWeight.detShiftShape_eq_detShiftShape_iff` says that the
polynomial part is a complete invariant of that class. -/
@[simp]
theorem rationalWeylSLRep_eq_weylSLRepOfShape (l : DominantWeight n) :
    rationalWeylSLRep k n l = weylSLRepOfShape k n l.detShiftShape := by
  refine MonoidHom.ext fun g => LinearMap.ext fun x => ?_
  have hdet : (Matrix.GeneralLinearGroup.det (Matrix.SpecialLinearGroup.toGL g) : kˣ) = 1 := by
    simp
  rw [rationalWeylSLRep_apply, weylSLRepOfShape_apply, rationalWeylRep_apply, hdet, one_zpow,
    Units.val_one, one_smul]

end CommRing

section Bundled

variable (k : Type u) [CommRing k] [Algebra ℚ k] [IsNoetherianRing k] (n : ℕ)

/-- The Weyl module of a shape over `SL n k`, bundled as an object of `FDRep`, in parallel with
`TauCeti.weylFDRepOfShape`: the Noetherian hypothesis is all the bundling asks, a submodule of the
tensor power being finitely generated as soon as the base ring is Noetherian. -/
noncomputable abbrev weylSLFDRepOfShape (μ : YoungDiagram) :
    FDRep k (Matrix.SpecialLinearGroup (Fin n) k) :=
  FDRep.of (V := ↥(weylModuleOfShape k n μ).toSubmodule) (weylSLRepOfShape k n μ)

/-- The rational Weyl module of a dominant weight over `SL n k`, bundled as an object of `FDRep`,
in parallel with `TauCeti.rationalWeylFDRep`. -/
noncomputable abbrev rationalWeylSLFDRep (l : DominantWeight n) :
    FDRep k (Matrix.SpecialLinearGroup (Fin n) k) :=
  FDRep.of (V := ↥(weylModuleOfShape k n l.detShiftShape).toSubmodule) (rationalWeylSLRep k n l)

/-- **The restriction depends on the weight only modulo the constant weights**: `λ` and
`λ + m·(1, …, 1)` restrict to the same representation of `SL n k`.  Bundled as an equality of
`FDRep` objects this says so outright, with no carrier to rewrite by hand: the two sides are built
on the Weyl modules of the polynomial parts of `λ + m·(1, …, 1)` and of `λ`, which
`TauCeti.DominantWeight.detShiftShape_shift` identifies.  Together with
`TauCeti.DominantWeight.detShiftShape_eq_detShiftShape_iff`, which says that the polynomial part
is a complete invariant of the class of `λ`, this is the sense in which the restricted rational
Weyl modules are indexed by the dominant weights modulo the constant weights. -/
@[simp]
theorem rationalWeylSLFDRep_shift (l : DominantWeight n) (m : ℤ) :
    rationalWeylSLFDRep k n (l.shift m) = rationalWeylSLFDRep k n l := by
  have key : ∀ l' : DominantWeight n,
      rationalWeylSLFDRep k n l' = weylSLFDRepOfShape k n l'.detShiftShape := fun l' => by
    rw [rationalWeylSLFDRep, rationalWeylSLRep_eq_weylSLRepOfShape]
  rw [key, key, DominantWeight.detShiftShape_shift]

end Bundled

section Field

variable (k : Type u) [Field k] [CharZero k] (n : ℕ)

/-! ## Characters -/

/-- The character of the Weyl module of a shape over `SL n k` is the character of the Weyl module
over `GL n k`, read at the image of the matrix. -/
@[simp]
theorem char_weylSLRepOfShape (μ : YoungDiagram) (g : Matrix.SpecialLinearGroup (Fin n) k) :
    Representation.character (V := ↥(weylModuleOfShape k n μ).toSubmodule)
        (weylSLRepOfShape k n μ) g
      = Representation.character (V := ↥(weylModuleOfShape k n μ).toSubmodule)
        (weylRepOfShape k n μ) (Matrix.SpecialLinearGroup.toGL g) :=
  (rfl)

end Field

section Complex

/-- A Weyl module over `ℂ` stays irreducible upon restriction to `SL n ℂ` exactly when
its shape has at most `n` rows. -/
@[simp]
theorem isIrreducible_weylSLRepOfShape_iff (n : ℕ) (μ : YoungDiagram) :
    Representation.IsIrreducible (V := ↥(weylModuleOfShape ℂ n μ).toSubmodule)
      (weylSLRepOfShape ℂ n μ) ↔ μ.colLen 0 ≤ n := by
  refine ⟨fun h => ?_, fun hn => ?_⟩
  · exact not_lt.mp fun hn =>
      Submodule.nontrivial_iff_ne_bot.mp h.nontrivial
        (by rw [(weylModuleOfShape_eq_bot_iff ℂ n μ).mpr hn,
          Subrepresentation.toSubmodule_bot])
  · exact (Representation.isIrreducible_comp_toGL_iff _).mpr
      ((isIrreducible_weylRepOfShape_iff μ).mpr hn)

/-- The Weyl module of a shape, bundled over `SL n ℂ`, is simple exactly when the shape
has at most `n` rows. -/
@[simp]
theorem simple_weylSLFDRepOfShape_iff (n : ℕ) (μ : YoungDiagram) :
    CategoryTheory.Simple (weylSLFDRepOfShape ℂ n μ) ↔ μ.colLen 0 ≤ n := by
  rw [FDRep.simple_iff_isIrreducible]
  exact isIrreducible_weylSLRepOfShape_iff n μ

/-- Every rational Weyl module over `ℂ` restricts irreducibly to `SL n ℂ`. -/
instance isIrreducible_rationalWeylSLRep (n : ℕ) (l : DominantWeight n) :
    Representation.IsIrreducible (V := ↥(weylModuleOfShape ℂ n l.detShiftShape).toSubmodule)
      (rationalWeylSLRep ℂ n l) := by
  rw [rationalWeylSLRep_eq_weylSLRepOfShape]
  exact (isIrreducible_weylSLRepOfShape_iff n l.detShiftShape).mpr
    l.colLen_zero_detShiftShape_le

/-- Every bundled rational Weyl module over `ℂ` restricts to a simple `SL n ℂ` representation. -/
instance simple_rationalWeylSLFDRep (n : ℕ) (l : DominantWeight n) :
    CategoryTheory.Simple (rationalWeylSLFDRep ℂ n l) :=
  (FDRep.simple_iff_isIrreducible _).mpr (isIrreducible_rationalWeylSLRep n l)

end Complex

/-! ## Distinct restrictions -/

section Classification

open CategoryTheory

variable (k : Type u) [Field k] [IsAlgClosed k] [CharZero k] {n : ℕ}

/-- **The restrictions of rational Weyl modules to `SL n k` are isomorphic exactly when the dominant
weights differ by a constant weight.** Over an algebraically closed field of characteristic zero,
`V_λ` and `V_λ'` restrict to equivalent representations of `SL n k` exactly when
`λ' = λ + m·(1, …, 1)` for an integer `m`. -/
theorem nonempty_equiv_rationalWeylSLRep_iff {l l' : DominantWeight n} :
    Nonempty ((rationalWeylSLRep k n l).Equiv (rationalWeylSLRep k n l')) ↔
      ∃ m : ℤ, l' = l.shift m := by
  refine ⟨fun h => ?_, fun ⟨m, hm⟩ => ?_⟩
  · rcases Nat.eq_zero_or_pos n with rfl | hn
    · exact ⟨0, Subsingleton.elim _ _⟩
    have : NeZero (Fintype.card (Fin n) : k) := ⟨by simpa using hn.ne'⟩
    have := nontrivial_weylModuleOfShape k n l.detShiftShape l.colLen_zero_detShiftShape_le
    -- Scalar matrices act on `V_λ` by the power `∑ᵢ λᵢ`, so the equivalence of restrictions is a
    -- `GL n k`-equivalence between a determinant twist of `V_λ` and `V_λ'`.
    obtain ⟨t, -, ⟨e⟩⟩ := (Representation.nonempty_equiv_comp_toGL_iff
      (apply_scalar_eq_zpow_smul_of_weightSpace_ne_bot
        (weightSpace_rationalWeylRep_self_ne_bot k l))
      (apply_scalar_eq_zpow_smul_of_weightSpace_ne_bot
        (weightSpace_rationalWeylRep_self_ne_bot k l'))).mp h
    -- The twist moves every weight of `V_λ` by `t`, so its highest weight is `λ + t·(1, …, 1)`.
    have hdom (a : Fin n → ℤ)
        (ha : weightSpace (W := ↥(weylModuleOfShape k n l.detShiftShape).toSubmodule)
          (rationalWeylRep k n l) (a - fun _ => t) ≠ ⊥) (m : ℕ) :
        ∑ j ∈ Finset.univ.filter fun j : Fin n => (j : ℕ) < m, a j ≤
          ∑ j ∈ Finset.univ.filter fun j : Fin n => (j : ℕ) < m, (l.1 j + t) := by
      have h := sum_le_sum_of_weightSpace_rationalWeylRep_ne_bot ha m
      simp only [Pi.sub_apply, Finset.sum_sub_distrib] at h
      rw [Finset.sum_add_distrib]
      linarith
    have hl : weightSpace (W := ↥(weylModuleOfShape k n l.detShiftShape).toSubmodule)
        (Representation.charTwist ((Matrix.GeneralLinearGroup.det : GL (Fin n) k →* kˣ) ^ t)
          (rationalWeylRep k n l)) (fun j => l.1 j + t) ≠ ⊥ := by
      have h : ((fun j => l.1 j + t) - fun _ => t) = l.1 := by
        funext j
        simp
      rw [weightSpace_charTwist_detPow, h]
      exact weightSpace_rationalWeylRep_self_ne_bot k l
    have key := e.eq_of_forall_sum_filter_lt_le hl
      (fun a ha => hdom a (by rwa [weightSpace_charTwist_detPow] at ha))
      (weightSpace_rationalWeylRep_self_ne_bot k l')
      (fun _ ha => sum_le_sum_of_weightSpace_rationalWeylRep_ne_bot ha)
    exact ⟨t, Subtype.ext (funext fun i => by
      rw [DominantWeight.shift_apply, ← key])⟩
  · subst hm
    exact ⟨FDRep.isoToEquiv (eqToIso (rationalWeylSLFDRep_shift k n l m).symm)⟩

/-- **The bundled restrictions of rational Weyl modules to `SL n k` are isomorphic exactly when the
dominant weights differ by a constant weight**, over an algebraically closed field of
characteristic zero. -/
theorem nonempty_iso_rationalWeylSLFDRep_iff {l l' : DominantWeight n} :
    Nonempty (rationalWeylSLFDRep k n l ≅ rationalWeylSLFDRep k n l') ↔
      ∃ m : ℤ, l' = l.shift m := by
  refine ⟨fun ⟨i⟩ => (nonempty_equiv_rationalWeylSLRep_iff k).mp ⟨FDRep.isoToEquiv i⟩, ?_⟩
  rintro ⟨m, rfl⟩
  exact ⟨eqToIso (rationalWeylSLFDRep_shift k n l m).symm⟩

/-- **A Young diagram with at most `n - 1` rows is recovered from the restriction of its Weyl module
to `SL n k`**, over an algebraically closed field of characteristic zero. The row bound on both
diagrams is needed: adding a full column of height `n` to a diagram does not change the restriction,
since it twists the `GL n k`-module by the determinant. -/
theorem nonempty_equiv_weylSLRepOfShape_iff {μ ν : YoungDiagram} (hμ : μ.colLen 0 ≤ n - 1)
    (hν : ν.colLen 0 ≤ n - 1) :
    Nonempty ((weylSLRepOfShape k n μ).Equiv (weylSLRepOfShape k n ν)) ↔ μ = ν := by
  rw [← DominantWeight.detShiftShape_weightOfShape hμ,
    ← DominantWeight.detShiftShape_weightOfShape hν, ← rationalWeylSLRep_eq_weylSLRepOfShape,
    ← rationalWeylSLRep_eq_weylSLRepOfShape, nonempty_equiv_rationalWeylSLRep_iff,
    DominantWeight.detShiftShape_eq_detShiftShape_iff]

end Classification

/-! ## The irreducible rational representations of `SL n ℂ` -/

section RationalClassification

open CategoryTheory

variable {n : ℕ}

/-- The restriction of a rational Weyl module to `SL n ℂ` is rational. -/
theorem isRationalSLRep_rationalWeylSLRep (l : DominantWeight n) :
    IsRationalSLRep (rationalWeylSLRep ℂ n l) :=
  (isRationalRep_rationalWeylRep n l).comp_toGL

/-- The Weyl module of a shape is a rational representation of `SL n ℂ`. -/
@[simp]
theorem isRationalSLRep_weylSLRepOfShape (n : ℕ) (μ : YoungDiagram) :
    IsRationalSLRep (weylSLRepOfShape ℂ n μ) :=
  (isPolynomialRep_weylRepOfShape n μ).isRationalRep.comp_toGL

namespace IsRationalSLRep

variable {W : Type*} [AddCommGroup W] [Module ℂ W]
  {ρ : Representation ℂ (Matrix.SpecialLinearGroup (Fin n) ℂ) W}

/-- **Every irreducible rational representation of `SL n ℂ` is the restriction of a rational Weyl
module**: it is equivalent to the restriction `TauCeti.rationalWeylSLRep` of `V_λ` for some
dominant weight `λ`. -/
theorem exists_nonempty_equiv_rationalWeylSLRep (hρ : IsRationalSLRep ρ) [ρ.IsIrreducible] :
    ∃ l : DominantWeight n, Nonempty (ρ.Equiv (rationalWeylSLRep ℂ n l)) := by
  have := hρ.finite
  obtain ⟨a, ha⟩ : ∃ a : ℤ, ∀ (s : Matrix.SpecialLinearGroup (Fin n) ℂ) (z : ℂˣ),
      Matrix.SpecialLinearGroup.toGL s = Matrix.GeneralLinearGroup.scalar (Fin n) z →
        ∀ v, ρ s v = ((z ^ a : ℂˣ) : ℂ) • v := by
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · refine ⟨0, fun s z _ v => ?_⟩
      rw [Subsingleton.elim s 1, map_one, zpow_zero, Units.val_one, one_smul, Module.End.one_apply]
    · have : NeZero (Fintype.card (Fin n) : ℂ) := ⟨by simpa using hn.ne'⟩
      exact Representation.IsIrreducible.exists_forall_apply_eq_zpow_smul ρ
  have : (ρ.extendToGL a ha).IsIrreducible :=
    (Representation.isIrreducible_extendToGL_iff ρ a ha).mpr ‹_›
  obtain ⟨l, ⟨e⟩⟩ := (hρ.isRationalRep_extendToGL a ha).exists_nonempty_equiv_rationalWeylRep
  refine ⟨l, ⟨Representation.Equiv.mk e.toLinearEquiv fun s => LinearMap.ext fun v => ?_⟩⟩
  simpa [rationalWeylSLRep_apply] using Representation.IntertwiningMap.isIntertwining _ _
    e.toIntertwiningMap (Matrix.SpecialLinearGroup.toGL s) v

/-- **The highest-weight classification of the irreducible rational representations of
`SL n ℂ`**: an irreducible rational representation is equivalent to the restriction of the Weyl
module of exactly one Young diagram with at most `n - 1` rows. Equivalently, by
`TauCeti.nonempty_equiv_rationalWeylSLRep_iff`, it is the restriction of `V_λ` for a dominant
weight `λ` determined up to the constant weights `m·(1, …, 1)`. -/
theorem existsUnique_nonempty_equiv_weylSLRepOfShape (hρ : IsRationalSLRep ρ)
    [ρ.IsIrreducible] :
    ∃! μ : YoungDiagram, μ.colLen 0 ≤ n - 1 ∧ Nonempty (ρ.Equiv (weylSLRepOfShape ℂ n μ)) := by
  obtain ⟨l, ⟨e⟩⟩ := hρ.exists_nonempty_equiv_rationalWeylSLRep
  rw [rationalWeylSLRep_eq_weylSLRepOfShape] at e
  refine ⟨l.detShiftShape, ⟨l.colLen_zero_detShiftShape_le_pred, ⟨e⟩⟩,
    fun μ ⟨hμ, ⟨e'⟩⟩ => ?_⟩
  exact (nonempty_equiv_weylSLRepOfShape_iff ℂ hμ l.colLen_zero_detShiftShape_le_pred).mp
    ⟨e'.symm.trans e⟩

end IsRationalSLRep

end RationalClassification

end TauCeti

namespace FDRep

open CategoryTheory TauCeti

variable {n : ℕ}

/-- **The highest-weight classification in `FDRep`**: a simple finite-dimensional representation
of `SL n ℂ` whose action is rational is isomorphic to the restricted Weyl module of exactly one
Young diagram with at most `n - 1` rows. -/
theorem existsUnique_nonempty_iso_weylSLFDRepOfShape
    (V : FDRep ℂ (Matrix.SpecialLinearGroup (Fin n) ℂ)) [Simple V] (hV : IsRationalSLRep V.ρ) :
    ∃! μ : YoungDiagram, μ.colLen 0 ≤ n - 1 ∧ Nonempty (V ≅ weylSLFDRepOfShape ℂ n μ) := by
  have := (simple_iff_isIrreducible V).mp inferInstance
  obtain ⟨μ, ⟨hμ, ⟨e⟩⟩, hu⟩ := hV.existsUnique_nonempty_equiv_weylSLRepOfShape
  refine ⟨μ, ⟨hμ, ⟨e.toLinearEquiv.toFDRepIso fun g x ↦ ?_⟩⟩, fun ν ⟨hν, ⟨i⟩⟩ ↦
    hu ν ⟨hν, ⟨isoToEquiv i⟩⟩⟩
  exact LinearMap.congr_fun (e.isIntertwining' g) x

end FDRep
