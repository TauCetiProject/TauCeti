/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

import TauCeti.RingTheory.Almost.ShriekShriek

/-!
# Examples of the unitisation `B_!!`

These examples test the unitisation `R_!! = (V ⊕ m~ ⊗[V] R) ⧸ I` of
`TauCeti.Almost.BasicSetup.ShriekShriek` and the functor `B ↦ B_!!` of
`TauCeti.Almost.Algebra.shriekShriek`:

* in the classical setup `(ℤ, ℤ)`, adding the relations of `2 ⊗ 3` and `5 ⊗ 7` gives the element
  `(41, -(2 ⊗ 3 + 5 ⊗ 7) ⊗ 1)` of `ℤ ⊕ ℤ_!`;
* for every setup, `V_!! → V` is bijective, and so is `((V^a)_*)_!! → V`: the unitisation of the
  almost algebra `V^a` is `V`;
* in the classical setup, `R_!! → R` is bijective for every `R`, and so is `B_!! → B_*` for every
  almost algebra `B`;
* in the zero setup, `R_! = 0` and `V → R_!!` is bijective for every `R`;
* the classical, zero-setup and unit-algebra cases are exact, and so is every almost algebra in
  the classical setup.

The adjunction counit is invertible at the unit algebra and at all classical algebras.
In the zero setup it need not be invertible, as the product algebra `ℤ × ℤ` shows.

## References

* O. Gabber, L. Ramero, *Almost ring theory*, Lecture Notes in Mathematics 1800, §2.2.
-/

open CategoryTheory TensorProduct TauCeti.Almost TauCeti.Almost.BasicSetup

variable {V : Type*} [CommRing V]

/-! ### The relations in a classical setup -/

-- In the classical setup `(ℤ, ℤ)`, the relations for `2 ⊗ 3` and `5 ⊗ 7` add up to
-- `(41, -(2 ⊗ 3 + 5 ⊗ 7) ⊗ 1)`.
example :
    let x : (classical ℤ).ideal := ⟨2, by simp [classical_ideal]⟩
    let y : (classical ℤ).ideal := ⟨3, by simp [classical_ideal]⟩
    let z : (classical ℤ).ideal := ⟨5, by simp [classical_ideal]⟩
    let w : (classical ℤ).ideal := ⟨7, by simp [classical_ideal]⟩
    (classical ℤ).shriekShriekRel ℤ (x ⊗ₜ y) + (classical ℤ).shriekShriekRel ℤ (z ⊗ₜ w) =
      Unitization.inl 41 -
        (Shriek.equiv (classical ℤ) ℤ ((x ⊗ₜ y + z ⊗ₜ w) ⊗ₜ 1) :
          Unitization ℤ ((classical ℤ).Shriek ℤ)) := by
  intro x y z w
  rw [← map_add, shriekShriekRel_apply, map_add, tildeMul_tmul, tildeMul_tmul]
  norm_num [x, y, z, w]

/-! ### The unit algebra -/

-- For every setup, `V_!! → V` is bijective.
example (S : BasicSetup V) : Function.Bijective (S.shriekShriekCounit V) :=
  S.shriekShriekCounit_self_bijective

-- At the unit algebra, the counit gives the isomorphism from the unitisation to `V`.
example {V : Type} [CommRing V] (S : BasicSetup V) :
    IsIso ((Algebra.shriekShriekAdj S).counit.app (CommAlgCat.of V V)) := by
  rw [← isIso_comp_left_iff (S.shriekShriekFunctor.map
    ((Algebra.adj S).unit.app (CommAlgCat.of V V)))]
  rw [Algebra.map_adj_unit_comp_shriekShriekAdj_counit_app,
    shriekShriekToId_app, ConcreteCategory.isIso_iff_bijective]
  exact S.shriekShriekCounit_self_bijective

-- `V` is exact for every setup: `t ↦ t ⊗ 1` is injective on `m~`.
example (S : BasicSetup V) : S.IsShriekShriekExact V :=
  S.isShriekShriekExact_of_lTensor_injective V <| by
    rw [Algebra.linearMap_self, LinearMap.lTensor_id]
    exact Function.injective_id

/-! ### The classical setup -/

-- In the classical setup, `R_!! → R` is bijective.
example (R : Type*) [CommRing R] [Algebra V R] :
    Function.Bijective ((classical V).shriekShriekCounit R) :=
  isAlmostIso_classical_iff.mp ((classical V).isAlmostIso_shriekShriekCounit R)

-- Over a classical setup, the counit is an isomorphism even away from the unit algebra.
example {V : Type} [CommRing V] (R : CommAlgCat V) :
    IsIso ((Algebra.shriekShriekAdj (classical V)).counit.app R) := by
  rw [← isIso_comp_left_iff ((classical V).shriekShriekFunctor.map
    ((Algebra.adj (classical V)).unit.app R))]
  rw [Algebra.map_adj_unit_comp_shriekShriekAdj_counit_app,
    shriekShriekToId_app, ConcreteCategory.isIso_iff_bijective]
  exact isAlmostIso_classical_iff.mp ((classical V).isAlmostIso_shriekShriekCounit R)

-- In the classical setup, `B_!! → B_*` is an isomorphism for every almost algebra `B`.
example {V : Type} [CommRing V] (B : Algebra (classical V)) :
    IsIso ((Algebra.shriekShriekToElements (classical V)).app B) := by
  rw [ConcreteCategory.isIso_iff_bijective]
  have hf : Function.Bijective ⇑((Algebra.shriekShriekToElements (classical V)).app B).hom := by
    rw [Algebra.shriekShriekToElements_app_hom]
    exact isAlmostIso_classical_iff.mp ((classical V).isAlmostIso_shriekShriekCounit _)
  exact hf

-- In the classical setup every algebra is exact, since `m~ → m = V` is injective.
example (R : Type*) [CommRing R] [Algebra V R] : (classical V).IsShriekShriekExact R :=
  (classical V).isShriekShriekExact_of_tildeMul_injective R classical_tildeMul_bijective.1

-- In the classical setup every almost algebra is exact.
example {V : Type} [CommRing V] (B : Algebra (classical V)) : B.IsExact :=
  Algebra.isExact_of_tildeMul_injective _ classical_tildeMul_bijective.1 B

/-! ### The zero setup -/

-- In the zero setup, `m~ = 0`, so every algebra is exact.
example (R : Type*) [CommRing R] [Algebra V R] : (zero V).IsShriekShriekExact R :=
  (zero V).isShriekShriekExact_of_tildeMul_injective R <| by
    rw [zero_tildeMul]
    exact fun s t _ ↦ (zero_tildeToIdeal_bijective).1 (Subsingleton.elim _ _)

-- In the zero setup, `R_! = 0` and `V → R_!!` is bijective for every `R`.
example (R : Type*) [CommRing R] [Algebra V R] :
    Function.Bijective (algebraMap V ((zero V).ShriekShriek R)) := by
  have hz (z : (zero V).Shriek R) : ShriekShriek.inr (zero V) R z = 0 := by
    induction z using Shriek.induction_on with
    | add z z' hz hz' => rw [map_add, hz, hz', add_zero]
    | tmul t r => rw [Subsingleton.elim t 0, zero_tmul, map_zero, map_zero]
  refine ⟨(injective_iff_map_eq_zero _).mpr fun v hv ↦ ?_, fun x ↦ ?_⟩
  · rw [← ShriekShriek.mk_inl, ShriekShriek.mk_eq_zero_iff, mem_shriekShriekIdeal_iff] at hv
    obtain ⟨t, ht⟩ := hv
    rw [Subsingleton.elim t 0, map_zero] at ht
    exact (Unitization.inl_injective ht).symm
  · obtain ⟨v, z, rfl⟩ := ShriekShriek.exists_eq_algebraMap_add_inr (zero V) R x
    exact ⟨v, by rw [hz, add_zero]⟩

-- In the zero setup, the counit misses `(0, 1)` in the product algebra.
example : ¬ IsIso ((Algebra.shriekShriekAdj (zero ℤ)).counit.app (CommAlgCat.of ℤ (ℤ × ℤ))) := by
  let R := CommAlgCat.of ℤ (ℤ × ℤ)
  rw [← isIso_comp_left_iff ((zero ℤ).shriekShriekFunctor.map
    ((Algebra.adj (zero ℤ)).unit.app R))]
  rw [Algebra.map_adj_unit_comp_shriekShriekAdj_counit_app,
    shriekShriekToId_app, ConcreteCategory.isIso_iff_bijective]
  intro h
  have hz (z : (zero ℤ).Shriek R) : Shriek.act (zero ℤ) R z = 0 := by
    induction z using Shriek.induction_on with
    | add z z' hz hz' => rw [map_add, hz, hz', add_zero]
    | tmul t r => rw [Shriek.act_tmul, zero_tildeMul, LinearMap.zero_apply, zero_smul]
  obtain ⟨x, hx⟩ := h.surjective ((0, 1) : ℤ × ℤ)
  obtain ⟨v, z, rfl⟩ := ShriekShriek.exists_eq_algebraMap_add_inr (zero ℤ) R x
  have hv : algebraMap ℤ R v = (0, 1) := by
    have hx' : (zero ℤ).shriekShriekCounit R
        (algebraMap ℤ _ v + ShriekShriek.inr (zero ℤ) R z) = (0, 1) := hx
    rwa [map_add, AlgHom.commutes, shriekShriekCounit_inr, hz, add_zero] at hx'
  have h₀ := congrArg Prod.fst hv
  have h₁ := congrArg Prod.snd hv
  exact zero_ne_one (h₀.symm.trans h₁)
