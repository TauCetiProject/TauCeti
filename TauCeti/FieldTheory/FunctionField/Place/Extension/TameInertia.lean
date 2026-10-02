/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.FieldTheory.FunctionField.Place.Extension.WildInertia
import Mathlib.RingTheory.IntegralDomain
import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots

/-!
# The tame character of a place

Let `F' / F` be an extension of fields, `k` a subfield of `F`, and `P` a place of `F' / k`, and fix
a uniformizer `t` at `P`.  An automorphism `σ` in the inertia group `G_0(P)` moves `t` by a unit,
`σ t = u_σ t`, and the value of `u_σ` at `P` is the **tame character**
`TauCeti.Place.tameCharacter : G_0(P) →* (F'_P)ˣ`.  Because `σ` acts trivially on the residue field,
`σ ↦ u_σ(P)` is a homomorphism, and it does not depend on `t`.  Its kernel consists of the
automorphisms with `σ t ≡ t` modulo `𝔪_P²`, so it contains the first ramification group `G_1(P)`.

When the residue extension `F'_P / F_{P ∩ F}` is separable, the kernel is exactly `G_1(P)`: the
value at `P` of a function `z` integral at `P` is a simple root of a polynomial over `𝒪_{P ∩ F}`,
and Taylor expansion of that polynomial at `z` shows that `σ z ≡ z` modulo `𝔪_P²` as soon as
`σ t ≡ t`.  Then `G_0(P) / G_1(P)` embeds in the multiplicative group of the residue field, so when
the inertia group is finite it is **cyclic of order prime to the residue characteristic** `p`.
Since `G_1(P)` is a `p`-group (`TauCeti.Place.isPGroup_ramificationGroup_succ`), the place has no
wild inertia exactly when `p` does not divide `|G_0(P)|`, which in a finite Galois extension is the
ramification index.

This is part of Stichtenoth, Proposition 3.8.5, which is stated over a perfect constant field, so
that all residue fields are perfect; here the only hypothesis is that the residue extension is
separable.  Without it the kernel of the tame character can be strictly larger than `G_1(P)`.  The
analogous statements for nonarchimedean local fields are in
`TauCeti/NumberTheory/LocalField/UnitFiltration/RamificationGroup.lean`.

## Main definitions

* `TauCeti.Place.tameCharacter`: for a uniformizer `t` at `P`, the homomorphism
  `σ ↦ (σ t / t)(P)` from `G_0(P)` to the units of the residue field.

## Main results

* `TauCeti.Place.tameCharacter_eq_of_ord_eq_one`: the tame character does not depend on the
  uniformizer.
* `TauCeti.Place.tameCharacter_eq_one_iff`: `σ` lies in the kernel exactly when `σ t ≡ t` modulo
  `𝔪_P²`.
* `TauCeti.Place.mem_ramificationGroup_one_iff`: for a separable residue extension, an element of
  `G_0(P)` lies in `G_1(P)` exactly when it fixes a uniformizer modulo `𝔪_P²`.
* `TauCeti.Place.ker_tameCharacter`: for a separable residue extension, the kernel of the tame
  character is `G_1(P)`.
* `TauCeti.Place.isCyclic_quotient_ramificationGroup_one` and
  `TauCeti.Place.not_dvd_index_ramificationGroup_one`: **`G_0(P) / G_1(P)` is cyclic of order prime
  to the residue characteristic**.
* `TauCeti.Place.ramificationGroup_one_eq_bot_iff_not_dvd_card_ramificationGroup_zero`: the first
  ramification group is trivial exactly when the residue characteristic does not divide the order
  of the inertia group, and `TauCeti.Place.ramificationGroup_one_eq_bot_iff_not_dvd_ramificationIdx`
  its form for a finite Galois extension: **no wild inertia exactly in the tame case**.

## References

* H. Stichtenoth, *Algebraic Function Fields and Codes*, 2nd ed., GTM 254, Springer, 2009,
  Proposition 3.8.5.
-/

public section

open Polynomial

namespace TauCeti

namespace Place

universe u v v'

variable {k : Type u} {F : Type v} {F' : Type v'}
variable [Field k] [Field F] [Field F']
variable [Algebra k F] [Algebra k F'] [Algebra F F'] [IsScalarTower k F F']

section Character

variable (F) (P : Place k F') {t : F'}

private theorem ne_zero_of_ord_eq_one (ht : P.ord t = 1) : t ≠ 0 := fun h0 ↦ by
  simp [h0, ord_zero] at ht

private theorem mem_integers_of_ord_eq_one (ht : P.ord t = 1) : t ∈ P.integers := by
  rw [mem_integers_iff_ord_nonneg, ht]
  norm_num

/-- The ratio `σ t / t` by which an automorphism fixing `P` moves a uniformizer is a unit at `P`. -/
private theorem ord_apply_mul_inv (ht : P.ord t = 1) (g : P.integers.decompositionSubgroup F) :
    P.ord ((g : F' ≃ₐ[F] F') t * t⁻¹) = 0 := by
  have ht0 := ne_zero_of_ord_eq_one P ht
  rw [P.ord_mul ((_root_.map_ne_zero _).mpr ht0) (inv_ne_zero ht0), ord_inv,
    ord_decompositionSubgroup_apply F P g]
  ring

private theorem apply_mul_inv_mem_integers (ht : P.ord t = 1)
    (g : P.integers.decompositionSubgroup F) :
    (g : F' ≃ₐ[F] F') t * t⁻¹ ∈ P.integers := by
  rw [mem_integers_iff_ord_nonneg, ord_apply_mul_inv F P ht]

/-- An element of the inertia group does not change the value at `P` of a function integral at
`P`. -/
private theorem residue_apply_eq {g : P.integers.decompositionSubgroup F}
    (hg : g ∈ ramificationGroup F P 0) (x y : P.integers)
    (hy : (y : F') = (g : F' ≃ₐ[F] F') x) :
    IsLocalRing.residue P.integers y = IsLocalRing.residue P.integers x := by
  rw [residue_eq_iff_sub_mem_filtration_one, hy]
  simpa using (mem_ramificationGroup_iff F P).mp hg x x.2

private theorem residue_apply_mul_inv_ne_zero (ht : P.ord t = 1)
    (g : P.integers.decompositionSubgroup F) :
    IsLocalRing.residue P.integers
      ⟨(g : F' ≃ₐ[F] F') t * t⁻¹, apply_mul_inv_mem_integers F P ht g⟩ ≠ 0 := by
  have ht0 := ne_zero_of_ord_eq_one P ht
  rw [Ne, residue_eq_zero_iff_ord_pos]
  · rw [ord_apply_mul_inv F P ht]
    exact lt_irrefl 0
  · exact mul_ne_zero ((_root_.map_ne_zero _).mpr ht0) (inv_ne_zero ht0)

/-- **The tame character** (Stichtenoth, Proposition 3.8.5): for a uniformizer `t` at `P`, the
homomorphism from the inertia group `G_0(P)` to the units of the residue field sending `σ` to the
value at `P` of the unit `σ t / t`.  It does not depend on `t`
(`TauCeti.Place.tameCharacter_eq_of_ord_eq_one`), and its kernel contains `G_1(P)`, with equality
when the residue extension is separable (`TauCeti.Place.ker_tameCharacter`). -/
noncomputable def tameCharacter (ht : P.ord t = 1) :
    ramificationGroup F P 0 →* P.ResidueFieldˣ :=
  MonoidHom.mk'
    (fun g ↦ Units.mk0 _
      (residue_apply_mul_inv_ne_zero F P ht (g : P.integers.decompositionSubgroup F)))
    (by
      intro g h
      ext
      set σ : F' ≃ₐ[F] F' := ((g : P.integers.decompositionSubgroup F) : F' ≃ₐ[F] F')
      set τ : F' ≃ₐ[F] F' := ((h : P.integers.decompositionSubgroup F) : F' ≃ₐ[F] F')
      have ht0 := ne_zero_of_ord_eq_one P ht
      simp only [Units.val_mk0, Units.val_mul]
      have hτmem := apply_mul_inv_mem_integers F P ht (h : P.integers.decompositionSubgroup F)
      have hστ : σ (τ t * t⁻¹) ∈ P.integers :=
        (mem_integers_decompositionSubgroup_apply F P _).mpr hτmem
      have hres := residue_apply_eq F P g.2 ⟨_, hτmem⟩ ⟨_, hστ⟩ rfl
      rw [← hres, ← map_mul]
      congr 1
      ext
      -- Unfold the product in the valuation ring and the action of the product automorphism.
      change σ (τ t) * t⁻¹ = σ t * t⁻¹ * σ (τ t * t⁻¹)
      rw [map_mul, map_inv₀]
      field_simp [(_root_.map_ne_zero σ).mpr ht0])

/-- The value of the tame character at `σ`, computed on any representative `y` of `σ t / t`
in `𝒪_P`. -/
theorem coe_tameCharacter_of_eq (ht : P.ord t = 1) (g : ramificationGroup F P 0)
    {y : P.integers}
    (hy : (y : F') = ((g : P.integers.decompositionSubgroup F) : F' ≃ₐ[F] F') t * t⁻¹) :
    (tameCharacter F P ht g : P.ResidueField) = IsLocalRing.residue P.integers y :=
  congrArg _ (Subtype.ext hy.symm)

/-- **The kernel of the tame character** (Stichtenoth, Proposition 3.8.5): `σ` has trivial tame
character exactly when it fixes the uniformizer `t` modulo `𝔪_P²`. -/
theorem tameCharacter_eq_one_iff (ht : P.ord t = 1) (g : ramificationGroup F P 0) :
    tameCharacter F P ht g = 1 ↔
      ((g : P.integers.decompositionSubgroup F) : F' ≃ₐ[F] F') t - t ∈ P.filtration 2 := by
  have ht0 := ne_zero_of_ord_eq_one P ht
  set σ : F' ≃ₐ[F] F' := ((g : P.integers.decompositionSubgroup F) : F' ≃ₐ[F] F')
  rw [Units.ext_iff, coe_tameCharacter_of_eq F P ht g
    (y := ⟨_, apply_mul_inv_mem_integers F P ht _⟩) rfl, Units.val_one,
    ← map_one (IsLocalRing.residue P.integers), residue_eq_iff_sub_mem_filtration_one]
  have hq : σ t * t⁻¹ - 1 = (σ t - t) * t⁻¹ := by field_simp
  simp only [OneMemClass.coe_one]
  rw [hq]
  constructor
  · intro h
    have h2 := P.mul_mem_filtration h (P.mem_filtration_ord t)
    rwa [ht, inv_mul_cancel_right₀ ht0, show (1 : ℤ) + 1 = 2 by norm_num] at h2
  · intro h
    have h2 := P.mul_mem_filtration h (P.mem_filtration_ord t⁻¹)
    rwa [ord_inv, ht, show (2 : ℤ) + -1 = 1 by norm_num] at h2

/-- **The tame character does not depend on the uniformizer.** -/
theorem tameCharacter_eq_of_ord_eq_one {t' : F'} (ht : P.ord t = 1) (ht' : P.ord t' = 1) :
    tameCharacter F P ht = tameCharacter F P ht' := by
  have ht0 := ne_zero_of_ord_eq_one P ht
  have ht0' := ne_zero_of_ord_eq_one P ht'
  ext g
  set σ : F' ≃ₐ[F] F' := ((g : P.integers.decompositionSubgroup F) : F' ≃ₐ[F] F')
  -- Write `t' = u t` with `u` a unit at `P`; then `σ t' / t' = (σ u / u) (σ t / t)`.
  have hu : t' * t⁻¹ ∈ P.integers := by
    rw [mem_integers_iff_ord_nonneg, P.ord_mul ht0' (inv_ne_zero ht0), ord_inv, ht, ht']
    norm_num
  have hσu : σ (t' * t⁻¹) ∈ P.integers :=
    (mem_integers_decompositionSubgroup_apply F P _).mpr hu
  have hu0 : t' * t⁻¹ ≠ 0 := mul_ne_zero ht0' (inv_ne_zero ht0)
  have huinv : (t' * t⁻¹)⁻¹ ∈ P.integers := by
    rw [mem_integers_iff_ord_nonneg, ord_inv, P.ord_mul ht0' (inv_ne_zero ht0), ord_inv, ht, ht']
    norm_num
  have hres := residue_apply_eq F P g.2 ⟨_, hu⟩ ⟨_, hσu⟩ rfl
  rw [coe_tameCharacter_of_eq F P ht' g (y := ⟨_, apply_mul_inv_mem_integers F P ht' _⟩) rfl,
    coe_tameCharacter_of_eq F P ht g (y := ⟨_, apply_mul_inv_mem_integers F P ht _⟩) rfl]
  have hsplit : (⟨σ t' * t'⁻¹, apply_mul_inv_mem_integers F P ht' _⟩ : P.integers) =
      ⟨σ t * t⁻¹, apply_mul_inv_mem_integers F P ht _⟩ * ⟨σ (t' * t⁻¹), hσu⟩ *
        ⟨(t' * t⁻¹)⁻¹, huinv⟩ := by
    ext
    simp only [MulMemClass.coe_mul, map_mul, map_inv₀]
    field_simp [(_root_.map_ne_zero σ).mpr ht0, (_root_.map_ne_zero σ).mpr ht0']
  have hunit : IsLocalRing.residue P.integers ⟨t' * t⁻¹, hu⟩ *
      IsLocalRing.residue P.integers ⟨(t' * t⁻¹)⁻¹, huinv⟩ = 1 := by
    rw [← map_mul, ← map_one (IsLocalRing.residue P.integers)]
    congr 1
    ext
    exact mul_inv_cancel₀ hu0
  rw [hsplit, map_mul, map_mul, hres, mul_assoc, hunit, mul_one]

/-- The tame character is trivial on the first ramification group: an automorphism moving every
function integral at `P` by an element of `𝔪_P²` in particular fixes `t` modulo `𝔪_P²`. -/
theorem ramificationGroup_one_subgroupOf_le_ker_tameCharacter (ht : P.ord t = 1) :
    (ramificationGroup F P 1).subgroupOf (ramificationGroup F P 0) ≤
      (tameCharacter F P ht).ker := by
  intro g hg
  rw [Subgroup.mem_subgroupOf] at hg
  rw [MonoidHom.mem_ker, tameCharacter_eq_one_iff]
  simpa using (mem_ramificationGroup_iff F P).mp hg t (mem_integers_of_ord_eq_one P ht)

end Character

section Separable

variable (F) [Algebra.IsIntegral F F'] (P : Place k F') {t : F'}

/-- The value at `P` of a polynomial over `𝒪_{P ∩ F}` evaluated at a function integral at `P` is
the reduced polynomial evaluated at the value of the function. -/
private theorem residue_eval_map (q : (P.restrict k F).integers[X]) (z : P.integers) :
    IsLocalRing.residue P.integers
        ((q.map (algebraMap (P.restrict k F).integers P.integers)).eval z) =
      aeval (IsLocalRing.residue P.integers z)
        (q.map (IsLocalRing.residue (P.restrict k F).integers)) := by
  rw [eval_map, hom_eval₂, aeval_def, eval₂_map]
  -- The two composite ring homomorphisms `𝒪_{P ∩ F} → F'_P` agree by
  -- `IsLocalRing.ResidueField.algebraMap_residue`, which holds definitionally.
  congr 1

/-- An automorphism fixing `P` commutes with evaluating a polynomial over `𝒪_{P ∩ F}`. -/
private theorem apply_coe_eval_map (g : P.integers.decompositionSubgroup F)
    (q : (P.restrict k F).integers[X]) (z : P.integers) :
    (g : F' ≃ₐ[F] F')
        (((q.map (algebraMap (P.restrict k F).integers P.integers)).eval z : P.integers) : F') =
      (((q.map (algebraMap (P.restrict k F).integers P.integers)).eval (g • z) : P.integers) :
        F') := by
  have hcoe : ∀ y : P.integers,
      (((q.map (algebraMap (P.restrict k F).integers P.integers)).eval y : P.integers) : F') =
        q.eval₂ (P.integers.subtype.comp (algebraMap _ _)) (y : F') := fun y ↦ by
    rw [eval_map, ← ValuationSubring.subtype_apply, hom_eval₂]
    rfl
  rw [hcoe, hcoe, coe_decompositionSubgroup_smul]
  have h := hom_eval₂ q (P.integers.subtype.comp (algebraMap _ _))
    ((g : F' ≃ₐ[F] F') : F' →+* F') (z : F')
  have hψ : ((g : F' ≃ₐ[F] F') : F' →+* F').comp
      (P.integers.subtype.comp (algebraMap (P.restrict k F).integers P.integers)) =
      P.integers.subtype.comp (algebraMap _ _) := by
    ext r
    simp
  rw [hψ] at h
  simpa using h

/- An automorphism in `G_0(P)` fixing a uniformizer modulo `𝔪_P²` lies in `G_1(P)` when the residue
extension is separable.  The value `z(P)` of a function `z` integral at `P` is a simple root of a
polynomial `f₀` over `F_{P ∩ F}`; lift `f₀` to `f` over `𝒪_{P ∩ F}`.  Taylor expansion gives
`f(σ z) - f(z) = (σ z - z) · u` with `u ≡ f'(z)` a unit at `P`, while `f(z) ∈ 𝔪_P` and `σ t ≡ t`
force `σ (f z) ≡ f z` modulo `𝔪_P²`.  Hence `σ z ≡ z` modulo `𝔪_P²`. -/
private theorem mem_ramificationGroup_one_of_sub_mem_filtration_two
    [Algebra.IsSeparable (P.restrict k F).ResidueField P.ResidueField] (ht : P.ord t = 1)
    {g : P.integers.decompositionSubgroup F} (hg : g ∈ ramificationGroup F P 0)
    (hgt : (g : F' ≃ₐ[F] F') t - t ∈ P.filtration 2) :
    g ∈ ramificationGroup F P 1 := by
  set σ : F' ≃ₐ[F] F' := (g : F' ≃ₐ[F] F')
  have ht0 := ne_zero_of_ord_eq_one P ht
  have hg0 : ∀ x ∈ P.integers, σ x - x ∈ P.filtration 1 := fun x hx ↦ by
    simpa using (mem_ramificationGroup_iff F P).mp hg x hx
  rw [mem_ramificationGroup_iff, show ((1 : ℕ) : ℤ) + 1 = 2 by norm_num]
  intro x hx
  set z : P.integers := ⟨x, hx⟩
  -- Lift the minimal polynomial of `z(P)` over `F_{P ∩ F}` to `𝒪_{P ∩ F}`.
  obtain ⟨f, hf⟩ := Polynomial.map_surjective (IsLocalRing.residue (P.restrict k F).integers)
    IsLocalRing.residue_surjective
    (minpoly (P.restrict k F).ResidueField (IsLocalRing.residue P.integers z))
  set fS := f.map (algebraMap (P.restrict k F).integers P.integers) with hfS
  have hroot : IsLocalRing.residue P.integers (fS.eval z) = 0 := by
    rw [residue_eval_map, hf]
    exact minpoly.aeval _ _
  have hder : IsLocalRing.residue P.integers ((derivative fS).eval z) ≠ 0 := by
    rw [hfS, derivative_map, residue_eval_map, ← derivative_map, hf]
    exact (Algebra.IsSeparable.isSeparable _ _).aeval_derivative_ne_zero (minpoly.aeval _ _)
  -- Taylor expansion of `f` at `z` with increment `d = σ z - z`.
  set d : P.integers := g • z - z with hd
  obtain ⟨K, hK⟩ := binomExpansion fS z d
  rw [add_sub_cancel] at hK
  have hdcoe : (d : F') = σ x - x := by
    rw [hd, show ((g • z - z : P.integers) : F') = ((g • z : P.integers) : F') - (z : F') from rfl,
      coe_decompositionSubgroup_smul]
  have hd1 : (d : F') ∈ P.filtration 1 := hdcoe ▸ hg0 x hx
  set u : P.integers := (derivative fS).eval z + K * d with hu
  have hunit : IsUnit u := by
    rw [← IsLocalRing.notMem_maximalIdeal, ← IsLocalRing.residue_eq_zero_iff, hu, map_add,
      map_mul]
    have hd0 : IsLocalRing.residue P.integers d = 0 := by
      rw [← map_zero (IsLocalRing.residue P.integers), residue_eq_iff_sub_mem_filtration_one]
      simpa using hd1
    rw [hd0, mul_zero, add_zero]
    exact hder
  -- `f(σ z) - f(z) = d · u` in `𝒪_P`.
  have hdu : ((fS.eval (g • z) : P.integers) : F') - ((fS.eval z : P.integers) : F') =
      (d : F') * (u : F') := by
    have h : fS.eval (g • z) - fS.eval z = d * u := by
      rw [hK, hu]
      ring
    exact_mod_cast congrArg Subtype.val h
  -- `σ (f z) - f z ∈ 𝔪_P²`, writing `f z = t v` with `v` integral at `P`.
  set w : F' := ((fS.eval z : P.integers) : F') with hw
  have hw1 : w ∈ P.filtration 1 := by
    have := (residue_eq_iff_sub_mem_filtration_one (y := fS.eval z) (z := 0)).mp
      (by rw [hroot, map_zero])
    simpa using this
  have hv : t⁻¹ * w ∈ P.integers :=
    mul_mem_integers_of_mem_filtration (by rw [ord_inv, ht]) hw1
  have hσv : σ (t⁻¹ * w) ∈ P.integers := (mem_integers_decompositionSubgroup_apply F P g).mpr hv
  have hσw : σ w - w ∈ P.filtration 2 := by
    have hsplit : σ w - w = (σ t - t) * σ (t⁻¹ * w) + t * (σ (t⁻¹ * w) - t⁻¹ * w) := by
      rw [map_mul, map_inv₀]
      field_simp [(_root_.map_ne_zero σ).mpr ht0]
      ring
    rw [hsplit]
    refine Submodule.add_mem _ ?_ ?_
    · simpa using P.mul_mem_filtration hgt (P.mem_filtration_zero_iff.mpr hσv)
    · have h := P.mul_mem_filtration (P.mem_filtration_ord t) (hg0 _ hv)
      rwa [ht, show (1 : ℤ) + 1 = 2 by norm_num] at h
  rw [hw, apply_coe_eval_map, hdu] at hσw
  -- Divide by the unit `u`.
  obtain ⟨u', hu'⟩ := hunit.exists_right_inv
  have hcancel : (d : F') = (d : F') * u * (u' : F') := by
    rw [mul_assoc, ← MulMemClass.coe_mul, hu', OneMemClass.coe_one, mul_one]
  rw [← hdcoe, hcancel]
  simpa using P.mul_mem_filtration hσw (P.mem_filtration_zero_iff.mpr u'.2)

/-- **Membership in the first ramification group is decided at a uniformizer**, when the residue
extension is separable (Stichtenoth, Proposition 3.8.5): an element of `G_0(P)` lies in `G_1(P)`
exactly when it fixes `t` modulo `𝔪_P²`. -/
theorem mem_ramificationGroup_one_iff
    [Algebra.IsSeparable (P.restrict k F).ResidueField P.ResidueField] (ht : P.ord t = 1)
    {g : P.integers.decompositionSubgroup F} (hg : g ∈ ramificationGroup F P 0) :
    g ∈ ramificationGroup F P 1 ↔ (g : F' ≃ₐ[F] F') t - t ∈ P.filtration 2 := by
  refine ⟨fun hg1 ↦ ?_, mem_ramificationGroup_one_of_sub_mem_filtration_two F P ht hg⟩
  simpa using (mem_ramificationGroup_iff F P).mp hg1 t (mem_integers_of_ord_eq_one P ht)

/-- **The kernel of the tame character is the first ramification group**, when the residue
extension is separable (Stichtenoth, Proposition 3.8.5): so `G_0(P) / G_1(P)` embeds in the
multiplicative group of the residue field. -/
theorem ker_tameCharacter [Algebra.IsSeparable (P.restrict k F).ResidueField P.ResidueField]
    (ht : P.ord t = 1) :
    (tameCharacter F P ht).ker =
      (ramificationGroup F P 1).subgroupOf (ramificationGroup F P 0) := by
  refine le_antisymm (fun g hg ↦ ?_)
    (ramificationGroup_one_subgroupOf_le_ker_tameCharacter F P ht)
  rw [MonoidHom.mem_ker, tameCharacter_eq_one_iff] at hg
  rw [Subgroup.mem_subgroupOf]
  exact mem_ramificationGroup_one_of_sub_mem_filtration_two F P ht g.2 hg

/-- The tame character induces an injective homomorphism from `G_0(P) / G_1(P)` to the units of
the residue field, when the residue extension is separable. -/
private theorem exists_injective_quotient_ramificationGroup_one
    [Algebra.IsSeparable (P.restrict k F).ResidueField P.ResidueField] :
    ∃ φ : ramificationGroup F P 0 ⧸ (ramificationGroup F P 1).subgroupOf (ramificationGroup F P 0)
      →* P.ResidueFieldˣ, Function.Injective φ := by
  obtain ⟨t, ht⟩ := P.exists_isUniformizer
  rw [isUniformizer_iff_ord_eq_one] at ht
  have hker := ker_tameCharacter F P ht
  refine ⟨QuotientGroup.lift _ (tameCharacter F P ht) hker.ge, ?_⟩
  refine (injective_iff_map_eq_one _).mpr fun a ha ↦ ?_
  induction a using QuotientGroup.induction_on with
  | H g =>
    rw [QuotientGroup.lift_mk, ← MonoidHom.mem_ker, hker] at ha
    exact (QuotientGroup.eq_one_iff g).mpr ha

/-- **The tame quotient `G_0(P) / G_1(P)` is cyclic** when the inertia group is finite and the
residue extension is separable (Stichtenoth, Proposition 3.8.5): it embeds in the multiplicative
group of the residue field, whose finite subgroups are cyclic. -/
theorem isCyclic_quotient_ramificationGroup_one
    [Algebra.IsSeparable (P.restrict k F).ResidueField P.ResidueField]
    [Finite (ramificationGroup F P 0)] :
    IsCyclic (ramificationGroup F P 0 ⧸
      (ramificationGroup F P 1).subgroupOf (ramificationGroup F P 0)) := by
  obtain ⟨φ, hφ⟩ := exists_injective_quotient_ramificationGroup_one F P
  exact isCyclic_of_injective_ringHom ((Units.coeHom P.ResidueField).comp φ)
    ((Units.val_injective).comp hφ)

/-- **The index of `G_1(P)` in `G_0(P)` is prime to the residue characteristic `p`**, when the
inertia group is finite and the residue extension is separable (Stichtenoth, Proposition 3.8.5):
`G_0(P) / G_1(P)` embeds in the multiplicative group of a field of characteristic `p`, which has
no element of order `p`. -/
theorem not_dvd_index_ramificationGroup_one (p : ℕ) [Fact p.Prime] [CharP P.ResidueField p]
    [Algebra.IsSeparable (P.restrict k F).ResidueField P.ResidueField]
    [Finite (ramificationGroup F P 0)] :
    ¬ p ∣ ((ramificationGroup F P 1).subgroupOf (ramificationGroup F P 0)).index := by
  obtain ⟨φ, hφ⟩ := exists_injective_quotient_ramificationGroup_one F P
  intro hp
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' p hp
  -- The image of `x` is a primitive `p`-th root of unity, impossible in characteristic `p`.
  have hord : orderOf ((φ x : P.ResidueFieldˣ) : P.ResidueField) = p := by
    rw [orderOf_units, orderOf_injective φ hφ x, hx]
  have : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  have hroot := hord ▸ IsPrimitiveRoot.orderOf ((φ x : P.ResidueFieldˣ) : P.ResidueField)
  exact hroot.neZero'.out (CharP.cast_eq_zero _ p)

/-- **A place has no wild inertia exactly when the residue characteristic `p` does not divide the
order of its inertia group**, when that group is finite and the residue extension is separable:
`G_1(P)` is a `p`-group (`TauCeti.Place.isPGroup_ramificationGroup_succ`) of index prime to `p`. -/
theorem ramificationGroup_one_eq_bot_iff_not_dvd_card_ramificationGroup_zero (p : ℕ)
    [Fact p.Prime] [CharP P.ResidueField p]
    [Algebra.IsSeparable (P.restrict k F).ResidueField P.ResidueField]
    [Finite (ramificationGroup F P 0)] :
    ramificationGroup F P 1 = ⊥ ↔ ¬ p ∣ Nat.card (ramificationGroup F P 0) := by
  refine ⟨fun h ↦ ?_, ramificationGroup_succ_eq_bot_of_not_dvd_card_inertia F P p 0⟩
  have hindex := not_dvd_index_ramificationGroup_one F P p
  rwa [h, Subgroup.bot_subgroupOf, Subgroup.index_bot] at hindex

/-- **A place of a finite Galois extension is tamely ramified exactly when it has no wild
inertia**, when the residue extension is separable: the first ramification group is trivial if and
only if the residue characteristic `p` does not divide the ramification index. -/
theorem ramificationGroup_one_eq_bot_iff_not_dvd_ramificationIdx (p : ℕ) [Fact p.Prime]
    [CharP P.ResidueField p] [FiniteDimensional F F'] [IsGalois F F']
    [Algebra.IsSeparable (P.restrict k F).ResidueField P.ResidueField] :
    ramificationGroup F P 1 = ⊥ ↔ ¬ p ∣ ramificationIdx F P := by
  have : Finite (ramificationGroup F P 0) :=
    Finite.of_injective (fun g : ramificationGroup F P 0 ↦ (g : F' ≃ₐ[F] F'))
      (fun _ _ h ↦ Subtype.ext (Subtype.ext h))
  rw [ramificationGroup_one_eq_bot_iff_not_dvd_card_ramificationGroup_zero F P p,
    ramificationGroup_zero, card_inertiaSubgroup F P]

end Separable

end Place

end TauCeti
