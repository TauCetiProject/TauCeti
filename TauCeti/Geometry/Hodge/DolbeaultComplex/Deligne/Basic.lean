/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Basic
public import Mathlib.Algebra.Homology.HomologicalComplex
public import TauCeti.Geometry.Hodge.DolbeaultComplex.Basic

/-!
# The Deligne complex of a real Dolbeault complex

For a real Dolbeault complex `A` and an integer `p`, the Deligne complex `D(A, p)` is the real
cochain complex with terms

* `Dᵃ(A, p) = A_ℝ(p - 1) ∩ ⨁ {Aʳˢ | r + s = a - 1, r < p, s < p}` for `a < 2p`, and
* `Dᵃ(A, p) = A_ℝ(p) ∩ ⨁ {Aʳˢ | r + s = a, p ≤ r, p ≤ s}` for `2p ≤ a`,

where `A_ℝ(p) = (2πi)ᵖ A_ℝ` is the twisted real structure `TauCeti.Hodge.Conjugation.twist`. In
the notation of the Hodge filtrations, the first family is `A_ℝ(p - 1) ∩ F^{a-p, a-p}` in total
degree `a - 1`, and the second is `A_ℝ(p) ∩ F^{p, p}` in total degree `a`. The differential is

* `x ↦ -π(d x)` for `a < 2p - 1`, where `π` projects onto the types `(r, s)` with `r < p` and
  `s < p`,
* `x ↦ -2 ∂∂bar x` for `a = 2p - 1`, and
* `x ↦ d x` for `2p ≤ a`.

In the critical degree `2p - 1` the term is the part of type `(p - 1, p - 1)` in
`A_ℝ(p - 1)`, and the differential raises the degree of the underlying vectors by two. Burgos
showed that this complex is homotopy equivalent to the Deligne cone
`fib(A_ℝ(p) ⊕ FᵖA → A)`, so that for the logarithmic Dolbeault algebra of a smooth complex variety
it computes real Deligne–Beilinson cohomology; that comparison is not part of this file.

The terms are real subspaces of the single ambient space `A`, and the differential in each degree
is the restriction of a complex-linear endomorphism of `A`,
`TauCeti.Hodge.DolbeaultComplex.deligneDiff`. That endomorphism squares to zero on the whole of
`A`, not only on the terms.

## Main definitions

* `TauCeti.Hodge.DolbeaultComplex.delignePiece`: the term `Dᵃ(A, p)`.
* `TauCeti.Hodge.DolbeaultComplex.deligneDiff`: the endomorphism of `A` restricting to the
  differential out of degree `a`.
* `TauCeti.Hodge.DolbeaultComplex.deligneComplex`: the Deligne complex `D(A, p)`.
* `TauCeti.Hodge.DolbeaultComplex.deligneMap`: the map of Deligne complexes induced by a morphism
  of real Dolbeault complexes, compatible with identities and composition.

## Main results

* `TauCeti.Hodge.DolbeaultComplex.deligneDiff_mem`: the differential carries `Dᵃ(A, p)` into
  `Dᵃ⁺¹(A, p)`.
* `TauCeti.Hodge.DolbeaultComplex.deligneDiff_deligneDiff`: the differential squares to zero.
* `TauCeti.Hodge.DolbeaultComplex.mem_delignePiece_two_mul_sub_one_iff`: the critical term
  `D²ᵖ⁻¹(A, p)` is the twisted real part of type `(p - 1, p - 1)`.

## References

* J. I. Burgos Gil, *Arithmetic Chow rings and Deligne–Beilinson cohomology*, J. Algebraic Geom.
  6 (1997), 335–377.
* J. I. Burgos Gil, J. Kramer, U. Kühn, *Cohomological arithmetic Chow rings*, J. Inst. Math.
  Jussieu 6 (2007), Definitions 5.7–5.10 and Proposition 5.12.
-/

public section

open CategoryTheory TauCeti.DirectSum

namespace TauCeti.Hodge

universe u

namespace DolbeaultComplex

variable {A : Type u} [AddCommGroup A] [Module ℂ A] {𝒜 : ℤ × ℤ → Submodule ℂ A}
  (X : DolbeaultComplex 𝒜)

/-- The term `Dᵃ(A, p)` of the Deligne complex: for `a < 2p` the vectors of `A_ℝ(p - 1)` with
types `(r, s)` satisfying `r + s = a - 1`, `r < p` and `s < p`, and for `2p ≤ a` the vectors of
`A_ℝ(p)` with types satisfying `r + s = a`, `p ≤ r` and `p ≤ s`. -/
def delignePiece (p a : ℤ) : Submodule ℝ A :=
  if a < 2 * p then
    (⨆ i : {i : ℤ × ℤ | i.1 + i.2 = a - 1 ∧ i.1 < p ∧ i.2 < p}, 𝒜 i).restrictScalars ℝ ⊓
      X.conj.twist (p - 1)
  else
    (⨆ i : {i : ℤ × ℤ | i.1 + i.2 = a ∧ p ≤ i.1 ∧ p ≤ i.2}, 𝒜 i).restrictScalars ℝ ⊓
      X.conj.twist p

variable {X}

/-- Membership in a Deligne term below the critical degree. -/
theorem mem_delignePiece_of_lt {p a : ℤ} (h : a < 2 * p) {x : A} :
    x ∈ X.delignePiece p a ↔
      x ∈ (⨆ i : {i : ℤ × ℤ | i.1 + i.2 = a - 1 ∧ i.1 < p ∧ i.2 < p}, 𝒜 i) ∧
        x ∈ X.conj.twist (p - 1) := by
  rw [delignePiece, ite_eq_left h, Submodule.mem_inf, Submodule.restrictScalars_mem]

/-- Membership in a Deligne term from the critical degree on. -/
theorem mem_delignePiece_of_le {p a : ℤ} (h : 2 * p ≤ a) {x : A} :
    x ∈ X.delignePiece p a ↔
      x ∈ (⨆ i : {i : ℤ × ℤ | i.1 + i.2 = a ∧ p ≤ i.1 ∧ p ≤ i.2}, 𝒜 i) ∧
        x ∈ X.conj.twist p := by
  rw [delignePiece, ite_eq_right (not_lt.2 h), Submodule.mem_inf, Submodule.restrictScalars_mem]

/-- The term of the Deligne complex in the critical degree `2p - 1` consists of the vectors of
type `(p - 1, p - 1)` in the real twist `A_ℝ(p - 1)`. -/
theorem mem_delignePiece_two_mul_sub_one_iff {p : ℤ} {x : A} :
    x ∈ X.delignePiece p (2 * p - 1) ↔ x ∈ 𝒜 (p - 1, p - 1) ∧ x ∈ X.conj.twist (p - 1) := by
  rw [mem_delignePiece_of_lt (by omega)]
  refine and_congr_left' ⟨fun hx ↦ ?_, fun hx ↦ Submodule.mem_iSup_of_mem ⟨(p - 1, p - 1), ?_⟩ hx⟩
  · refine (iSup_le fun i ↦ ?_ : _ ≤ 𝒜 (p - 1, p - 1)) hx
    obtain ⟨⟨r, s⟩, hrs⟩ := i
    obtain ⟨rfl, rfl⟩ : r = p - 1 ∧ s = p - 1 := by simp only [Set.mem_ofPred_eq] at hrs; omega
    exact le_rfl
  · simp only [Set.mem_ofPred_eq]
    omega

variable (X) [DirectSum.Decomposition 𝒜]

/-- The complex-linear endomorphism of `A` whose restriction to `Dᵃ(A, p)` is the differential
of the Deligne complex: `-π ∘ d` below the critical degree, where `π` projects onto the types
`(r, s)` with `r < p` and `s < p`; `-2 ∂∂bar` in the critical degree `2p - 1`; and `d` from
degree `2p` on. -/
noncomputable def deligneDiff (p a : ℤ) : A →ₗ[ℂ] A :=
  if a + 1 < 2 * p then -(supportedProj 𝒜 {i | i.1 < p ∧ i.2 < p} ∘ₗ X.d)
  else if a + 1 = 2 * p then -(2 • (X.del ∘ₗ X.delBar))
  else X.d

variable {X}

/-- Below the critical degree the Deligne differential is minus the projection of `d` onto the
types `(r, s)` with `r < p` and `s < p`. -/
theorem deligneDiff_of_lt {p a : ℤ} (h : a + 1 < 2 * p) (x : A) :
    X.deligneDiff p a x = -supportedProj 𝒜 {i | i.1 < p ∧ i.2 < p} (X.d x) := by
  rw [deligneDiff, ite_eq_left h, LinearMap.neg_apply, LinearMap.comp_apply]

/-- In the critical degree `2p - 1` the Deligne differential is `-2 ∂∂bar`. -/
theorem deligneDiff_of_eq {p a : ℤ} (h : a + 1 = 2 * p) (x : A) :
    X.deligneDiff p a x = -(2 • X.del (X.delBar x)) := by
  rw [deligneDiff, ite_eq_right h.not_lt, ite_eq_left h, LinearMap.neg_apply,
    LinearMap.smul_apply, LinearMap.comp_apply]

/-- From degree `2p` on the Deligne differential is the total differential `d`. -/
theorem deligneDiff_of_le {p a : ℤ} (h : 2 * p ≤ a) (x : A) :
    X.deligneDiff p a x = X.d x := by
  rw [deligneDiff, ite_eq_right (by omega), ite_eq_right (by omega)]

/-- Conjugation commutes with the projection onto the types `(r, s)` with `r < p` and `s < p`, a
set of types stable under exchanging indices. -/
theorem conj_supportedProj_low (p : ℤ) (y : A) :
    X.conj.toEquiv (supportedProj 𝒜 {i | i.1 < p ∧ i.2 < p} y) =
      supportedProj 𝒜 {i | i.1 < p ∧ i.2 < p} (X.conj.toEquiv y) :=
  X.conj_supportedProj (fun i ↦ by simp only [Set.mem_ofPred_eq, Prod.fst_swap, Prod.snd_swap,
    and_comm]) y

/-- `∂∂bar` kills every projection of `d` onto a set of types. -/
private theorem del_delBar_supportedProj_d (S : Set (ℤ × ℤ)) (y : A) :
    X.del (X.delBar (supportedProj 𝒜 S (X.d y))) = 0 := by
  induction y using DirectSum.Decomposition.inductionOn 𝒜 with
  | zero => simp
  | @homogeneous i y =>
    simp only [d_apply, map_add]
    have h₁ : X.del (X.delBar (supportedProj 𝒜 S (X.del y))) = 0 := by
      by_cases hi : (i.1 + 1, i.2) ∈ S
      · rw [supportedProj_of_mem (X.del_mem y.property) hi, del_delBar_del]
      · rw [supportedProj_of_notMem (X.del_mem y.property) hi, map_zero, map_zero]
    have h₂ : X.del (X.delBar (supportedProj 𝒜 S (X.delBar y))) = 0 := by
      by_cases hi : (i.1, i.2 + 1) ∈ S
      · rw [supportedProj_of_mem (X.delBar_mem y.property) hi, del_delBar_delBar]
      · rw [supportedProj_of_notMem (X.delBar_mem y.property) hi, map_zero, map_zero]
    rw [h₁, h₂, add_zero]
  | add y z hy hz => rw [map_add, map_add, map_add, map_add, hy, hz, add_zero]

/-- The Deligne differential squares to zero, on the whole ambient space. -/
@[simp]
theorem deligneDiff_deligneDiff (p a : ℤ) (x : A) :
    X.deligneDiff p (a + 1) (X.deligneDiff p a x) = 0 := by
  rcases lt_trichotomy (a + 1 + 1) (2 * p) with h | h | h
  · rw [deligneDiff_of_lt h, deligneDiff_of_lt (by omega), map_neg, map_neg, neg_neg]
    -- Split `d x` along the types `(r, s)` with `r, s < p` and the others: `d` carries no type
    -- of the second kind into the first, and `d d x = 0`.
    have hc := X.supportedProj_d_supportedProj_eq_zero (S := {i : ℤ × ℤ | i.1 < p ∧ i.2 < p})
      (T := {i | i.1 < p ∧ i.2 < p}ᶜ)
      (fun i hi ↦ by simp only [Set.mem_compl_iff, Set.mem_ofPred_eq] at hi ⊢; omega) (X.d x)
    have hs := supportedProj_union 𝒜 {i : ℤ × ℤ | i.1 < p ∧ i.2 < p} disjoint_compl_right (X.d x)
    rw [Set.union_compl_self, supportedProj_univ] at hs
    have hd := congrArg (fun y ↦ supportedProj 𝒜 {i | i.1 < p ∧ i.2 < p} (X.d y)) hs
    rwa [map_add, map_add, d_d, map_zero, hc, add_zero, eq_comm] at hd
  · rw [deligneDiff_of_eq h, deligneDiff_of_lt (by omega), map_neg, map_neg,
      del_delBar_supportedProj_d, neg_zero, smul_zero, neg_zero]
  · rcases eq_or_lt_of_le (Int.add_one_le_iff.2 h) with h' | h'
    · rw [deligneDiff_of_le (by omega), deligneDiff_of_eq (by omega), map_neg, map_nsmul,
        d_del_delBar, smul_zero, neg_zero]
    · rw [deligneDiff_of_le (by omega), deligneDiff_of_le (by omega), d_d]

/-- The Deligne differential carries `Dᵃ(A, p)` into `Dᵃ⁺¹(A, p)`. -/
theorem deligneDiff_mem {p a : ℤ} {x : A} (hx : x ∈ X.delignePiece p a) :
    X.deligneDiff p a x ∈ X.delignePiece p (a + 1) := by
  rcases lt_trichotomy (a + 1) (2 * p) with h | h | h
  · rw [mem_delignePiece_of_lt (by omega)] at hx
    rw [mem_delignePiece_of_lt h, deligneDiff_of_lt h]
    refine ⟨neg_mem ?_, neg_mem ?_⟩
    · have hD : {i : ℤ × ℤ | i.1 + i.2 = a - 1 ∧ i.1 < p ∧ i.2 < p} ⊆ {i | i.1 + i.2 = a - 1} :=
        fun _ hi ↦ hi.1
      have hL : ({i : ℤ × ℤ | i.1 < p ∧ i.2 < p} ∩ {i | i.1 + i.2 = a}) ⊆
          {i | i.1 + i.2 = a + 1 - 1 ∧ i.1 < p ∧ i.2 < p} :=
        fun _ hi ↦ ⟨hi.2.trans (add_sub_cancel_right a 1).symm, hi.1⟩
      exact mem_iSup_of_subset hL (supportedProj_mem_iSup_inter
        (X.d_mem_iSup_degree (sub_add_cancel a 1) (mem_iSup_of_subset hD hx.1)))
    · exact X.conj.map_mem_twist X.conj (f := supportedProj 𝒜 {i | i.1 < p ∧ i.2 < p} ∘ₗ X.d)
        (fun y ↦ by simp only [LinearMap.comp_apply, conj_supportedProj_low, conj_d]) hx.2
  · rw [mem_delignePiece_of_lt (by omega)] at hx
    rw [mem_delignePiece_of_le h.ge, deligneDiff_of_eq h]
    refine ⟨neg_mem (nsmul_mem ?_ 2), neg_mem (nsmul_mem ?_ 2)⟩
    · refine X.del_mem_iSup (S := {i : ℤ × ℤ | i.1 + 1 = p ∧ i.2 = p}) ?_
        (X.delBar_mem_iSup ?_ hx.1)
      · intro i hi
        simp only [Set.mem_ofPred_eq] at hi ⊢
        omega
      · intro i hi
        simp only [Set.mem_ofPred_eq] at hi ⊢
        omega
    · have h₁ := X.conj.map_mem_twist_add_one X.conj (f := X.del ∘ₗ X.delBar)
        (fun y ↦ conj_del_delBar X y) hx.2
      rwa [sub_add_cancel] at h₁
  · rw [mem_delignePiece_of_le (by omega)] at hx
    rw [mem_delignePiece_of_le (by omega), deligneDiff_of_le (by omega)]
    exact ⟨X.d_mem_iSup (fun i hi ↦ by simp only [Set.mem_ofPred_eq] at hi ⊢; omega) hx.1,
      X.conj.map_mem_twist X.conj (conj_d X) hx.2⟩

variable (X)

/-- The Deligne complex `D(A, p)` of a real Dolbeault complex: the real cochain complex whose
term in degree `a` is `TauCeti.Hodge.DolbeaultComplex.delignePiece` and whose differential is the
restriction of `TauCeti.Hodge.DolbeaultComplex.deligneDiff`.

The body is exposed so that the terms of the complex are the real subspaces
`TauCeti.Hodge.DolbeaultComplex.delignePiece` of `A` and their elements are vectors of `A`. -/
@[expose]
noncomputable def deligneComplex (p : ℤ) : CochainComplex (ModuleCat.{u} ℝ) ℤ :=
  CochainComplex.of (fun a ↦ ModuleCat.of ℝ (X.delignePiece p a))
    (fun a ↦ ModuleCat.ofHom (LinearMap.restrict (p := X.delignePiece p a)
      (q := X.delignePiece p (a + 1)) ((X.deligneDiff p a).restrictScalars ℝ)
      fun _ hx ↦ deligneDiff_mem hx))
    fun a ↦ ModuleCat.hom_ext
      (LinearMap.ext fun x ↦ Subtype.ext (deligneDiff_deligneDiff p a x.val))

/-- The term of the Deligne complex in degree `a` is `Dᵃ(A, p)`. -/
@[simp]
theorem deligneComplex_X (p a : ℤ) :
    (X.deligneComplex p).X a = ModuleCat.of ℝ (X.delignePiece p a) :=
  (rfl)

/-- The differential of the Deligne complex out of degree `a` is the restriction of
`TauCeti.Hodge.DolbeaultComplex.deligneDiff`. -/
@[simp]
theorem deligneComplex_d_apply (p a : ℤ) (x : X.delignePiece p a) :
    Subtype.val (p := (· ∈ X.delignePiece p (a + 1))) ((X.deligneComplex p).d a (a + 1) x) =
      X.deligneDiff p a x := by
  simp only [deligneComplex, CochainComplex.of_d, ModuleCat.hom_ofHom]
  -- The terms of `CochainComplex.of` are only definitionally the subtypes `delignePiece`, so
  -- `LinearMap.coe_restrict_apply` cannot be rewritten here and is applied up to that unfolding.
  exact LinearMap.coe_restrict_apply _ x

section Hom

variable {B : Type u} [AddCommGroup B] [Module ℂ B] {ℬ : ℤ × ℤ → Submodule ℂ B}
  [DirectSum.Decomposition ℬ] {Y : DolbeaultComplex ℬ}
  {C : Type u} [AddCommGroup C] [Module ℂ C] {𝒞 : ℤ × ℤ → Submodule ℂ C}
  [DirectSum.Decomposition 𝒞] {Z : DolbeaultComplex 𝒞}

variable {X}

omit [DirectSum.Decomposition 𝒜] [DirectSum.Decomposition ℬ] in
/-- A morphism of real Dolbeault complexes carries each Deligne term into the corresponding
one. -/
theorem Hom.map_mem_delignePiece (f : Hom X Y) {p a : ℤ} {x : A}
    (hx : x ∈ X.delignePiece p a) : f x ∈ Y.delignePiece p a := by
  have hf : ∀ y, Y.conj.toEquiv (f y) = f (X.conj.toEquiv y) := fun y ↦ (f.map_conj y).symm
  by_cases h : a < 2 * p
  · rw [mem_delignePiece_of_lt h] at hx ⊢
    exact ⟨f.map_mem_iSup hx.1, X.conj.map_mem_twist Y.conj hf hx.2⟩
  · rw [mem_delignePiece_of_le (not_lt.1 h)] at hx ⊢
    exact ⟨f.map_mem_iSup hx.1, X.conj.map_mem_twist Y.conj hf hx.2⟩

/-- A morphism of real Dolbeault complexes commutes with the Deligne differentials. -/
theorem Hom.map_deligneDiff (f : Hom X Y) (p a : ℤ) (x : A) :
    f (X.deligneDiff p a x) = Y.deligneDiff p a (f x) := by
  rcases lt_trichotomy (a + 1) (2 * p) with h | h | h
  · rw [deligneDiff_of_lt h, deligneDiff_of_lt h, map_neg, f.map_supportedProj, f.map_d]
  · rw [deligneDiff_of_eq h, deligneDiff_of_eq h, map_neg, map_nsmul, f.map_del, f.map_delBar]
  · rw [deligneDiff_of_le (by omega), deligneDiff_of_le (by omega), f.map_d]

/-- The map of Deligne complexes `D(A, p) ⟶ D(B, p)` induced by a morphism of real Dolbeault
complexes: in each degree, the restriction of the underlying linear map. -/
noncomputable def deligneMap (f : Hom X Y) (p : ℤ) : X.deligneComplex p ⟶ Y.deligneComplex p :=
  CochainComplex.ofHom
    (fun a ↦ ModuleCat.ofHom (LinearMap.restrict (p := X.delignePiece p a)
      (q := Y.delignePiece p a) (f.toLinearMap.restrictScalars ℝ)
      fun _ hx ↦ f.map_mem_delignePiece hx))
    fun a ↦ by
      ext x
      simp only [deligneComplex, CochainComplex.of_d, ModuleCat.hom_comp, ModuleCat.hom_ofHom]
      exact Subtype.ext (f.map_deligneDiff p a x.val).symm

/-- In each degree, the map of Deligne complexes induced by a morphism is the morphism. -/
@[simp]
theorem deligneMap_f_apply (f : Hom X Y) (p a : ℤ) (x : X.delignePiece p a) :
    Subtype.val (p := (· ∈ Y.delignePiece p a)) ((deligneMap f p).f a x) = f x :=
  (rfl)

/-- The identity morphism induces the identity of the Deligne complex. -/
@[simp]
theorem deligneMap_id (p : ℤ) : deligneMap (Hom.id X) p = 𝟙 (X.deligneComplex p) := by
  ext a x
  -- The terms of `deligneComplex` are only definitionally the subtypes `delignePiece`, so
  -- `deligneMap_f_apply` cannot be rewritten here and is applied up to that unfolding.
  exact Subtype.ext ((deligneMap_f_apply (Hom.id X) p a x).trans (Hom.id_apply _))

/-- The map of Deligne complexes induced by a composite is the composite of the induced maps. -/
@[reassoc, simp]
theorem deligneMap_comp (g : Hom Y Z) (f : Hom X Y) (p : ℤ) :
    deligneMap (g.comp f) p = deligneMap f p ≫ deligneMap g p := by
  ext a x
  -- As in `deligneMap_id`, `deligneMap_f_apply` is applied up to unfolding the terms.
  exact Subtype.ext ((deligneMap_f_apply (g.comp f) p a x).trans (Hom.comp_apply g f _))

end Hom

end DolbeaultComplex

end TauCeti.Hodge
