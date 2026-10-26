/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Flat.IsBaseChange
public import TauCeti.RingTheory.Invariant.EquivalenceRelation.Basic
public import TauCeti.RingTheory.IsTensorProduct.Pushout

/-!
# Base change of affine equivalence relations and their invariants

Let `s = algebraMap A B` and `t : A →+* B` give two morphisms `Spec B ⇉ Spec A`, and let `R` be a
ring of coefficients on which they agree, `t ∘ (R → A) = s ∘ (R → A)`. Base change along a map
`R → R'` replaces `A` by `A' = R' ⊗[R] A` and `B` by `B' = A' ⊗[A] B`, with first morphism
`A' → B'`; these are expressed by `Algebra.IsPushout R R' A A'` and `Algebra.IsPushout A A' B B'`,
so that localizations are allowed as well as tensor products. The second morphism is the ring
homomorphism `t' : A' →+* B'` which is `t` on `A` and the first morphism on `R'`; it exists by
`Algebra.IsPushout.liftRingHom`, and the results below take any `t'` with these two properties.

This file proves two facts about this base change.

* If `Spec B ⇉ Spec A` is an equivalence relation, so is `Spec B' ⇉ Spec A'`
  (`RingHom.IsSpecEquivRel.of_isPushout`). A point of `Spec B'` is a point of `Spec B` together
  with a compatible point of `Spec R'`, so reflexivity, symmetry and transitivity are inherited.
  When `B` is a finite projective `A`-module, so is `B'` over `A'`
  (`Module.Finite.of_isPushout`, `Module.Projective.of_isPushout`).
* If `R'` is flat over `R`, the invariants commute with base change: the ring of invariants
  `{a' : s' a' = t' a'}` of `A'` is generated over `R'` by the image of the ring of invariants
  `{a : s a = t a}` of `A` (`RingHom.eqLocus_eq_adjoin_of_isPushout`). In particular, if `R` is
  the ring of invariants of `A`, then `R'` is the ring of invariants of `A'`
  (`RingHom.eqLocus_eq_range_of_isPushout`). The proof applies Mathlib's
  `IsBaseChange.of_left_exact` to the exact sequence `0 → {s = t} → A → B`, `a ↦ s a - t a`.

Base change along the flat maps `C → C_𝔭` from the ring of invariants `C` to its localizations
reduces the construction of the quotient of an affine scheme by a finite locally free equivalence
relation (SGA 3, Exposé V, Théorème 4.1) to the case of a local ring of invariants.

## Main results

* `RingHom.IsSpecEquivRel.of_isPushout`: an equivalence relation remains one after base change.
* `RingHom.eqLocus_eq_adjoin_of_isPushout`: after flat base change, the invariants are generated
  by the image of the invariants.
* `RingHom.eqLocus_eq_range_of_isPushout`: flat base change of the ring of invariants is the ring
  of invariants of the base change.

## References

* M. Demazure and A. Grothendieck, *Schémas en groupes (SGA 3)*, Exposé V, §4.
* The Stacks Project, Chapter *Groupoid Schemes*, Section *Finite flat groupoids, affine case*.
-/

public section

open Algebra

universe u

namespace RingHom

section EquivRel

variable {A B A' B' : Type u} {R' : Type*} [CommRing A] [CommRing B] [CommRing R'] [CommRing A']
  [CommRing B'] [Algebra A B] [Algebra R' A'] [Algebra A A'] [Algebra A' B'] [Algebra B B']
  [Algebra A B'] [IsScalarTower A A' B'] [IsScalarTower A B B'] [IsPushout A A' B B']
  {t : A →+* B} {t' : A' →+* B'}

/-- **Base change of an equivalence relation.** If `Spec B ⇉ Spec A`, given by `s = algebraMap A B`
and `t`, is an equivalence relation, then so is its base change `Spec B' ⇉ Spec A'` along any map
`R → R'`, where `A' = R' ⊗[R] A`, `B' = A' ⊗[A] B`, and `t' : A' →+* B'` is `t` on `A` and the first
morphism on `R'`. -/
theorem IsSpecEquivRel.of_isPushout (R : Type*) [CommRing R] [Algebra R A] [Algebra R R']
    [Algebra R A'] [IsScalarTower R R' A'] [IsScalarTower R A A'] [IsPushout R R' A A']
    (h : (algebraMap A B).IsSpecEquivRel t)
    (ht₁ : t'.comp (algebraMap A A') = (algebraMap B B').comp t)
    (ht₂ : t'.comp (algebraMap R' A') = (algebraMap A' B').comp (algebraMap R' A')) :
    (algebraMap A' B').IsSpecEquivRel t' := by
  have ht₁' (a : A) : t' (algebraMap A A' a) = algebraMap B B' (t a) := congr($ht₁ a)
  have ht₂' (r : R') : t' (algebraMap R' A' r) = algebraMap A' B' (algebraMap R' A' r) :=
    congr($ht₂ r)
  have hA (a : A) : algebraMap B B' (algebraMap A B a) = algebraMap A' B' (algebraMap A A' a) := by
    rw [← IsScalarTower.algebraMap_apply, ← IsScalarTower.algebraMap_apply]
  -- a ring homomorphism out of `A' = R' ⊗[R] A` is determined on `A` and on `R'`
  have extA {T : Type u} [CommRing T] {f g : A' →+* T}
      (hfA : ∀ a, f (algebraMap A A' a) = g (algebraMap A A' a))
      (hfR : ∀ r, f (algebraMap R' A' r) = g (algebraMap R' A' r)) : f = g :=
    IsPushout.ringHom_ext (R := R) (RingHom.ext hfR) (RingHom.ext hfA)
  refine ⟨fun T _ x y hs ht ↦ ?_, fun T _ u ↦ ?_, fun T _ x ↦ ?_, fun T _ x y hxy ↦ ?_⟩
  · -- a point of `Spec B' = Spec (A' ⊗[A] B)` is determined by its images in `Spec A'` and
    -- `Spec B`, and the latter is determined by its two images in `Spec A`
    refine IsPushout.ringHom_ext (R := A) hs
      (h.ext (RingHom.ext fun a ↦ ?_) (RingHom.ext fun a ↦ ?_))
    · simpa [hA] using congr($hs (algebraMap A A' a))
    · simpa [ht₁'] using congr($ht (algebraMap A A' a))
  · obtain ⟨z, hzs, hzt⟩ := h.refl (u.comp (algebraMap A A'))
    refine ⟨IsPushout.liftRingHom B' u z hzs.symm, RingHom.ext fun x ↦ by simp,
      extA (fun a ↦ ?_) (fun r ↦ by simp [ht₂'])⟩
    simpa [ht₁'] using congr($hzt a)
  · obtain ⟨z, hzs, hzt⟩ := h.symm (x.comp (algebraMap B B'))
    have hxz : (x.comp t').comp (algebraMap A A') = z.comp (algebraMap A B) :=
      RingHom.ext fun a ↦ by simpa [ht₁'] using congr($hzs a).symm
    refine ⟨IsPushout.liftRingHom B' (x.comp t') z hxz, RingHom.ext fun x ↦ by simp,
      extA (fun a ↦ ?_) (fun r ↦ by simp [ht₂'])⟩
    simpa [ht₁', hA] using congr($hzt a)
  · obtain ⟨z, hzs, hzt⟩ := h.trans (x.comp (algebraMap B B')) (y.comp (algebraMap B B'))
      (RingHom.ext fun a ↦ by simpa [ht₁', hA] using congr($hxy (algebraMap A A' a)))
    have hxz : (x.comp (algebraMap A' B')).comp (algebraMap A A') = z.comp (algebraMap A B) :=
      RingHom.ext fun a ↦ by simpa [hA] using congr($hzs a).symm
    refine ⟨IsPushout.liftRingHom B' (x.comp (algebraMap A' B')) z hxz,
      RingHom.ext fun x ↦ by simp, extA (fun a ↦ ?_) (fun r ↦ ?_)⟩
    · simpa [ht₁'] using congr($hzt a)
    · simpa [ht₂'] using congr($hxy (algebraMap R' A' r))

end EquivRel

variable {R A B R' A' B' : Type*} [CommRing R] [CommRing A] [CommRing B] [CommRing R']
  [CommRing A'] [CommRing B'] [Algebra R A] [Algebra A B] [Algebra R R'] [Algebra R' A']
  [Algebra R A'] [Algebra A A'] [IsScalarTower R R' A'] [IsScalarTower R A A']
  [IsPushout R R' A A'] [Algebra A' B'] [Algebra B B'] [Algebra A B'] [IsScalarTower A A' B']
  [IsScalarTower A B B'] [IsPushout A A' B B']
  {t : A →+* B} {t' : A' →+* B'}

section Invariants

-- The R-linear map `a ↦ s a - t a` of the invariants sequence, after equipping `B` with its
-- `R`-algebra structure through `A`.
private noncomputable def diff
    (ht : t.comp (algebraMap R A) = (algebraMap A B).comp (algebraMap R A)) :
    letI : Algebra R B := ((algebraMap A B).comp (algebraMap R A)).toAlgebra
    A →ₗ[R] B :=
  letI : Algebra R B := ((algebraMap A B).comp (algebraMap R A)).toAlgebra
  { toFun a := algebraMap A B a - t a
    map_add' a b := by simp only [map_add]; abel
    map_smul' r a := by
      have hr := congr($ht r)
      simp only [RingHom.comp_apply] at hr
      simp only [Algebra.smul_def, map_mul, hr, RingHom.id_apply, RingHom.algebraMap_toAlgebra,
        RingHom.comp_apply, mul_sub] }

private theorem diff_apply
    (ht : t.comp (algebraMap R A) = (algebraMap A B).comp (algebraMap R A)) (a : A) :
    diff ht a = algebraMap A B a - t a :=
  rfl

-- The images of the invariants of `A` and of `R'` are invariants of `A'`; this needs no flatness.
omit [IsPushout A A' B B'] in
private theorem adjoin_le_eqLocus
    (ht₁ : t'.comp (algebraMap A A') = (algebraMap B B').comp t)
    (ht₂ : t'.comp (algebraMap R' A') = (algebraMap A' B').comp (algebraMap R' A')) {x : A'}
    (hx : x ∈ adjoin R' (algebraMap A A' '' (algebraMap A B).eqLocus t)) :
    x ∈ (algebraMap A' B').eqLocus t' := by
  induction hx using adjoin_induction with
  | mem x hx =>
    obtain ⟨a, ha, rfl⟩ := hx
    rw [mem_eqLocus, ← RingHom.comp_apply t', ht₁, RingHom.comp_apply, ← mem_eqLocus.mp ha,
      ← IsScalarTower.algebraMap_apply, ← IsScalarTower.algebraMap_apply]
  | algebraMap r => exact (congr($ht₂ r)).symm
  | add x y _ _ hx hy => exact add_mem hx hy
  | mul x y _ _ hx hy => exact mul_mem hx hy

/-- **Invariants commute with flat base change.** Let `Spec B ⇉ Spec A`, given by
`s = algebraMap A B` and `t`, agree on `R`, and let `A' = R' ⊗[R] A`, `B' = A' ⊗[A] B` and
`t' : A' →+* B'` be the base change along a flat map `R → R'`. Then the invariants
`{a' : s' a' = t' a'}` of `A'` form the `R'`-subalgebra generated by the image of the invariants
`{a : s a = t a}` of `A`. -/
theorem eqLocus_eq_adjoin_of_isPushout [Module.Flat R R']
    (ht : t.comp (algebraMap R A) = (algebraMap A B).comp (algebraMap R A))
    (ht₁ : t'.comp (algebraMap A A') = (algebraMap B B').comp t)
    (ht₂ : t'.comp (algebraMap R' A') = (algebraMap A' B').comp (algebraMap R' A')) :
    (algebraMap A' B').eqLocus t' =
      (adjoin R' (algebraMap A A' '' (algebraMap A B).eqLocus t)).toSubring := by
  -- equip `B` and `B'` with their algebra structures over `R` and `R'`
  let : Algebra R B := ((algebraMap A B).comp (algebraMap R A)).toAlgebra
  have : IsScalarTower R A B := .of_algebraMap_eq fun _ ↦ rfl
  let : Algebra R' B' := ((algebraMap A' B').comp (algebraMap R' A')).toAlgebra
  have : IsScalarTower R' A' B' := .of_algebraMap_eq fun _ ↦ rfl
  let : Algebra R B' := ((algebraMap A B').comp (algebraMap R A)).toAlgebra
  have : IsScalarTower R A B' := .of_algebraMap_eq fun _ ↦ rfl
  have : IsScalarTower R B B' := .of_algebraMap_eq fun r ↦ IsScalarTower.algebraMap_apply A B B' _
  have : IsScalarTower R A' B' := .of_algebraMap_eq fun r ↦ by
    simp only [RingHom.algebraMap_toAlgebra, RingHom.comp_apply,
      IsScalarTower.algebraMap_apply R A A', ← IsScalarTower.algebraMap_apply A A' B']
  have : IsScalarTower R R' B' := .of_algebraMap_eq fun r ↦ by
    simp only [RingHom.algebraMap_toAlgebra, RingHom.comp_apply,
      ← IsScalarTower.algebraMap_apply R R' A', IsScalarTower.algebraMap_apply R A A',
      ← IsScalarTower.algebraMap_apply A A' B']
  -- `B'` is the base change of `B` along `R → R'`, by pasting the two pushout squares
  have : IsPushout R R' B B' :=
    have := IsPushout.symm (inferInstance : IsPushout R R' A A')
    ((IsPushout.comp_iff R A R' A').mpr (IsPushout.symm inferInstance)).symm
  have ht₁' (a : A) : t' (algebraMap A A' a) = algebraMap B B' (t a) := congr($ht₁ a)
  -- the invariants are the kernels of `a ↦ s a - t a` and `a' ↦ s' a' - t' a'`
  set g := diff ht
  set g' := diff ht₂
  have hg' (x : A') : x ∈ (algebraMap A' B').eqLocus t' ↔ x ∈ LinearMap.ker g' := by
    rw [mem_eqLocus, LinearMap.mem_ker, diff_apply, sub_eq_zero]
  -- base change carries the kernel of `g` to the kernel of `g'`, by flatness
  let h₁ : LinearMap.ker g →ₗ[R] LinearMap.ker g' :=
    { toFun x := ⟨algebraMap A A' x, by
        have hx : algebraMap A B x = t x := sub_eq_zero.mp x.2
        rw [LinearMap.mem_ker, diff_apply, ht₁', ← hx, ← IsScalarTower.algebraMap_apply,
          ← IsScalarTower.algebraMap_apply, sub_self]⟩
      map_add' x y := by ext; simp
      map_smul' r x := by ext; simp [Algebra.smul_def, IsScalarTower.algebraMap_apply R A A'] }
  have hbc : IsBaseChange R' h₁ := by
    refine IsBaseChange.of_left_exact R' h₁ (IsScalarTower.toAlgHom R A A').toLinearMap
      (IsScalarTower.toAlgHom R B B').toLinearMap (f := (LinearMap.ker g).subtype)
      (g := g) (f' := (LinearMap.ker g').subtype) (g' := g') rfl ?_ IsPushout.out IsPushout.out
      (LinearMap.exact_subtype_ker_map g) (Submodule.subtype_injective _)
      (LinearMap.exact_subtype_ker_map g') (Submodule.subtype_injective _)
    ext a
    simp [g, g', diff_apply, ht₁', ← IsScalarTower.algebraMap_apply]
  ext x
  rw [Subalgebra.mem_toSubring]
  refine ⟨fun hx ↦ ?_, fun hx ↦ ?_⟩
  · -- every element of the kernel of `g'` is an `R'`-combination of images of invariants
    suffices ∀ n : LinearMap.ker g', (n : A') ∈ adjoin R' (algebraMap A A' '' eqLocus _ t) from
      this ⟨x, (hg' x).mp hx⟩
    intro n
    induction n using hbc.inductionOn with
    | tmul a => exact subset_adjoin ⟨a, sub_eq_zero.mp a.2, rfl⟩
    | smul r n hn => exact Subalgebra.smul_mem _ hn r
    | add n₁ n₂ h₁ h₂ => exact Subalgebra.add_mem _ h₁ h₂
  · exact adjoin_le_eqLocus ht₁ ht₂ hx

/-- **The ring of invariants commutes with flat base change.** If `R` is the ring of invariants
of `Spec B ⇉ Spec A`, that is, the invariants `{a : s a = t a}` are the image of `R`, then after
base change along a flat map `R → R'` the invariants of `A'` are the image of `R'`. -/
theorem eqLocus_eq_range_of_isPushout [Module.Flat R R']
    (hR : (algebraMap A B).eqLocus t = (algebraMap R A).range)
    (ht₁ : t'.comp (algebraMap A A') = (algebraMap B B').comp t)
    (ht₂ : t'.comp (algebraMap R' A') = (algebraMap A' B').comp (algebraMap R' A')) :
    (algebraMap A' B').eqLocus t' = (algebraMap R' A').range := by
  have hRt (r : R) : algebraMap R A r ∈ (algebraMap A B).eqLocus t := hR ▸ mem_range_self _ r
  have ht : t.comp (algebraMap R A) = (algebraMap A B).comp (algebraMap R A) :=
    RingHom.ext fun r ↦ (mem_eqLocus.mp (hRt r)).symm
  -- the image of the invariants lies in the image of `R'`
  have hbot : adjoin R' (algebraMap A A' '' (algebraMap A B).eqLocus t) = ⊥ := by
    refine eq_bot_iff.mpr (adjoin_le ?_)
    rintro _ ⟨_, ha, rfl⟩
    obtain ⟨r, rfl⟩ := mem_range.mp (hR ▸ ha : _ ∈ (algebraMap R A).range)
    rw [← IsScalarTower.algebraMap_apply, IsScalarTower.algebraMap_apply R R' A']
    exact Subalgebra.algebraMap_mem _ _
  ext x
  rw [eqLocus_eq_adjoin_of_isPushout ht ht₁ ht₂, Subalgebra.mem_toSubring, hbot, mem_bot,
    mem_range, Set.mem_range]

end Invariants

end RingHom
