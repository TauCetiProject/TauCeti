/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Module.Submodule.Invariant
public import Mathlib.Algebra.Module.Submodule.Pointwise
public import Mathlib.GroupTheory.GroupAction.Quotient
public import Mathlib.LinearAlgebra.Dimension.Finrank
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Mathlib.LinearAlgebra.Projection
public import TauCeti.LinearAlgebra.End.Invariant
public import TauCeti.LinearAlgebra.GeneralLinearGroup.Basic
import Mathlib.GroupTheory.Index
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.LinearAlgebra.GeneralLinearGroup.Basic

/-!
# The action of `GL(V)` on the subspaces of `V`

The automorphisms of a vector space `V` act on its subspaces by taking images. An automorphism
maps a finite-dimensional subspace `U` onto `Y` as soon as it maps `U` into `Y` and the two have
the same dimension, so the orbit of `U` consists of the finite-dimensional subspaces of the
dimension of `U`. With the orbit-stabiliser theorem this counts, when `V` is finite-dimensional,
the subspaces of a given dimension through the stabiliser of one of them.

## Main results

* `Submodule.finrank_units_smul`: automorphisms preserve the dimension of subspaces.
* `Submodule.units_smul_eq_of_forall_mem`: an automorphism mapping `U` into a subspace `Y` of the
  same dimension maps `U` onto `Y`.
* `Submodule.mem_invtSubmodule_of_mem_stabilizer`: an automorphism stabilising `U` leaves `U`
  invariant.
* `Submodule.mem_orbit_units_iff`: the orbit of a finite-dimensional subspace `U` is the set of
  finite-dimensional subspaces of the dimension of `U`.
* `Submodule.isUnit_restrict_of_mem_stabilizer`, `Submodule.isUnit_snd_comp_of_mem_stabilizer`: an
  automorphism stabilising `U` restricts to an automorphism of `U` and induces an automorphism of
  a complement `Z` of `U`.
* `Submodule.stabilizerBlockEquiv`: for a complement `Z` of a submodule `U` of a module over any
  ring, the stabiliser of `U` is parametrised by the automorphisms of `U` and of `Z` and the maps
  `Z → U`, through the block automorphisms `Submodule.blockUnit`.
* `Submodule.card_stabilizer_mul_card_finrank_eq`: `|Stab(U)|` times the number of subspaces of
  the dimension of `U` is `|GL(V)|`.

## References

* Adapted from the counting of subspaces by their orbits in the proof of
  `New.Hall.rankInner_mul_eq_sum_skew` of `src/Lib/LocalGL/Green/HallAlgebra.lean` in grh-lean
  (https://github.com/lsernau/grh-lean, Apache 2.0, Copyright 2026 Anthropic PBC).
-/

public section

open Module MulAction
open scoped Pointwise

namespace Submodule

/-- An automorphism stabilising `U` leaves `U` invariant. -/
theorem mem_invtSubmodule_of_mem_stabilizer {R M : Type*} [Semiring R] [AddCommMonoid M]
    [Module R M] {g : (Module.End R M)ˣ} {U : Submodule R M}
    (hg : g ∈ stabilizer (Module.End R M)ˣ U) : U ∈ (g : Module.End R M).invtSubmodule :=
  (Module.End.mem_invtSubmodule_iff_forall_mem_of_mem _).2 fun v hv ↦ by
    rw [← mem_stabilizer_iff.1 hg]
    exact Submodule.mem_map_of_mem hv

section DivisionRing

variable {K V : Type*} [DivisionRing K] [AddCommGroup V] [Module K V]

/-- The action of `GL(V)` on the subspaces of `V` preserves the dimension. -/
theorem finrank_units_smul (g : (Module.End K V)ˣ) (U : Submodule K V) :
    finrank K ↥(g • U) = finrank K U :=
  ((LinearMap.GeneralLinearGroup.generalLinearEquiv K V) g).finrank_map_eq U

/-- An automorphism mapping `U` into a finite-dimensional subspace `Y` of the same dimension maps
`U` onto `Y`. -/
theorem units_smul_eq_of_forall_mem (g : (Module.End K V)ˣ) {U Y : Submodule K V}
    [FiniteDimensional K Y] (h : ∀ x ∈ U, (g : Module.End K V) x ∈ Y)
    (hd : finrank K Y = finrank K U) : g • U = Y :=
  Submodule.eq_of_le_of_finrank_eq (Submodule.map_le_iff_le_comap.2 h)
    (finrank_units_smul g U |>.trans hd.symm)

/-- The finite-dimensional subspaces in the orbit of a finite-dimensional subspace `U` under
`GL(V)` are those of the dimension of `U`. -/
theorem mem_orbit_units_iff {U Y : Submodule K V} [FiniteDimensional K U] [FiniteDimensional K Y] :
    Y ∈ orbit (Module.End K V)ˣ U ↔ finrank K Y = finrank K U := by
  refine ⟨?_, fun hY ↦ ?_⟩
  · rintro ⟨g, rfl⟩
    exact finrank_units_smul g U
  · obtain ⟨g, hg⟩ :=
      Submodule.exists_linearEquiv_restrict_eq (LinearEquiv.ofFinrankEq U Y hY.symm)
    refine ⟨LinearMap.GeneralLinearGroup.ofLinearEquiv g,
      units_smul_eq_of_forall_mem _ (fun x hx ↦ ?_) hY⟩
    simp [← hg ⟨x, hx⟩]

/-- Orbit-stabiliser: the order of the stabiliser of `U` in `GL(V)` times the number of subspaces
of the dimension of `U` is the order of `GL(V)`. -/
theorem card_stabilizer_mul_card_finrank_eq [FiniteDimensional K V] (U : Submodule K V) :
    Nat.card (stabilizer (Module.End K V)ˣ U) *
        Nat.card {Y : Submodule K V // finrank K Y = finrank K U} =
      Nat.card (Module.End K V)ˣ := by
  have h_orbit : orbit (Module.End K V)ˣ U = {Y : Submodule K V | finrank K Y = finrank K U} :=
    Set.ext fun _ ↦ mem_orbit_units_iff
  rw [← Subgroup.card_mul_index (stabilizer (Module.End K V)ˣ U), index_stabilizer, h_orbit,
    ← Nat.card_coe_set_eq]
  -- The coercion of the set `{Y | p Y}` to a type is by definition the subtype `{Y // p Y}`.
  rfl

end DivisionRing

section Stabilizer

variable {R V : Type*} [Ring R] [AddCommGroup V] [Module R V] {U Z : Submodule R V}
  (hUZ : IsCompl U Z)

/-- The automorphism of `V = U ⊕ Z` with diagonal blocks `a`, `b` and upper right block `x`. -/
noncomputable def blockUnit (a : (Module.End R U)ˣ) (b : (Module.End R Z)ˣ)
    (x : Z →ₗ[R] U) : (Module.End R V)ˣ :=
  LinearMap.GeneralLinearGroup.ofLinearEquiv
    ((U.prodEquivOfIsCompl Z hUZ).symm ≪≫ₗ LinearEquiv.prodComm R U Z ≪≫ₗ
      (LinearMap.GeneralLinearGroup.toLinearEquiv b).skewProd
        (LinearMap.GeneralLinearGroup.toLinearEquiv a) x ≪≫ₗ
      LinearEquiv.prodComm R Z U ≪≫ₗ U.prodEquivOfIsCompl Z hUZ)

/-- In the splitting `V ≅ U × Z`, the block automorphism acts as the block map
`(u, z) ↦ (a u + x z, b z)`. -/
theorem blockUnit_apply (a : (Module.End R U)ˣ) (b : (Module.End R Z)ˣ)
    (x : Z →ₗ[R] U) (v : V) :
    (blockUnit hUZ a b x : Module.End R V) v = U.prodEquivOfIsCompl Z hUZ
      (Module.End.blockTriangular (a : Module.End R U) (b : Module.End R Z) x
        ((U.prodEquivOfIsCompl Z hUZ).symm v)) := by
  simp [blockUnit]

/-- The block automorphism stabilises `U`. -/
theorem blockUnit_mem_stabilizer (a : (Module.End R U)ˣ) (b : (Module.End R Z)ˣ)
    (x : Z →ₗ[R] U) : blockUnit hUZ a b x ∈ stabilizer (Module.End R V)ˣ U := by
  -- The block map sends `u ∈ U` to `a u ∈ U`, and `a⁻¹ u ∈ U` to `u`.
  have h_apply (u : U) : (blockUnit hUZ a b x : Module.End R V) u = (a : Module.End R U) u := by
    rw [blockUnit_apply, Submodule.prodEquivOfIsCompl_symm_apply_left]
    simp
  refine mem_stabilizer_iff.2 (le_antisymm ?_ fun v hv ↦ ?_)
  · rintro _ ⟨v, hv, rfl⟩
    exact (h_apply ⟨v, hv⟩).symm ▸ Submodule.coe_mem _
  · refine (Submodule.mem_smul_pointwise_iff_exists _ _ _).2
      ⟨_, Submodule.coe_mem ((↑a⁻¹ : Module.End R U) ⟨v, hv⟩), ?_⟩
    rw [Units.smul_def, Module.End.smul_def, h_apply, Module.End.units_apply_inv_apply]

/-- The block parametrisation of the stabiliser of `U` in `GL(V)`, as a function. -/
private noncomputable def blockParam
    (t : (Module.End R U)ˣ × (Module.End R Z)ˣ × (Z →ₗ[R] U)) :
    stabilizer (Module.End R V)ˣ U :=
  ⟨blockUnit hUZ t.1 t.2.1 t.2.2, blockUnit_mem_stabilizer hUZ _ _ _⟩

private theorem blockParam_injective : Function.Injective (blockParam hUZ) := by
  rintro ⟨a, b, x⟩ ⟨a', b', x'⟩ h
  have h_blk (p : U × Z) :
      Module.End.blockTriangular (a : Module.End R U) (b : Module.End R Z) x p =
        Module.End.blockTriangular (a' : Module.End R U) (b' : Module.End R Z) x' p := by
    have := congrArg (fun g : stabilizer (Module.End R V)ˣ U ↦
      ((g : (Module.End R V)ˣ) : Module.End R V) (U.prodEquivOfIsCompl Z hUZ p)) h
    simp only [blockParam, blockUnit_apply, LinearEquiv.symm_apply_apply] at this
    exact (U.prodEquivOfIsCompl Z hUZ).injective this
  have ha : a = a' :=
    Units.ext (LinearMap.ext fun u ↦ by simpa using congrArg Prod.fst (h_blk (u, 0)))
  have hb : b = b' :=
    Units.ext (LinearMap.ext fun z ↦ by simpa using congrArg Prod.snd (h_blk (0, z)))
  have hx : x = x' := LinearMap.ext fun z ↦ by simpa using congrArg Prod.fst (h_blk (0, z))
  subst ha hb hx
  rfl

/-- An automorphism stabilising `U` restricts to an automorphism of `U`. -/
theorem isUnit_restrict_of_mem_stabilizer {g : (Module.End R V)ˣ}
    (hg : g ∈ stabilizer (Module.End R V)ˣ U) (hU : ∀ v ∈ U, (g : Module.End R V) v ∈ U) :
    IsUnit ((g : Module.End R V).restrict hU) := by
  -- Since `g • U = U`, the restriction of `g` maps `U` onto `U`.
  refine (Module.End.isUnit_iff _).2 ⟨fun u u' h ↦ Subtype.ext
    (((LinearMap.GeneralLinearGroup.generalLinearEquiv R V) g).injective
      (congrArg Subtype.val h)), fun u ↦ ?_⟩
  obtain ⟨w, hw, h_eq⟩ := (Submodule.mem_smul_pointwise_iff_exists _ _ _).1
    ((mem_stabilizer_iff.1 hg).symm ▸ u.prop : (u : V) ∈ g • U)
  exact ⟨⟨w, hw⟩, Subtype.ext h_eq⟩

/-- An automorphism stabilising `U` induces an automorphism of the complement `Z`: its `Z`-block
`z ↦ (g z)_Z` is invertible. -/
theorem isUnit_snd_comp_of_mem_stabilizer {g : (Module.End R V)ˣ}
    (hg : g ∈ stabilizer (Module.End R V)ˣ U) :
    IsUnit (LinearMap.snd R U Z ∘ₗ (U.prodEquivOfIsCompl Z hUZ).symm.toLinearMap ∘ₗ
      (g : Module.End R V) ∘ₗ Z.subtype) := by
  let e := U.prodEquivOfIsCompl Z hUZ
  have hU := (Module.End.mem_invtSubmodule_iff_forall_mem_of_mem _).1
    (mem_invtSubmodule_of_mem_stabilizer hg)
  have hg_inj : Function.Injective (g : Module.End R V) :=
    ((LinearMap.GeneralLinearGroup.generalLinearEquiv R V) g).injective
  refine (Module.End.isUnit_iff _).2 ⟨LinearMap.ker_eq_bot.1
    (LinearMap.ker_eq_bot'.2 fun z hz ↦ ?_), fun z' ↦ ?_⟩
  swap
  -- If `g v = z'` with `v = u + z`, then `g z = z' - g u` with `g u ∈ U`, so `(g z)_Z = z'`.
  · obtain ⟨v, hv⟩ := ((LinearMap.GeneralLinearGroup.generalLinearEquiv R V) g).surjective z'
    refine ⟨(e.symm v).2, ?_⟩
    have h_gu : (e.symm ((g : Module.End R V) (e.symm v).1)).2 = 0 :=
      (Submodule.prodEquivOfIsCompl_symm_apply_snd_eq_zero U Z hUZ).2 (hU _ (e.symm v).1.prop)
    have h_v : (g : Module.End R V) (e.symm v).2 = z' - (g : Module.End R V) (e.symm v).1 := by
      rw [eq_sub_iff_add_eq, ← map_add, add_comm, ← Submodule.coe_prodEquivOfIsCompl' U Z hUZ,
        LinearEquiv.apply_symm_apply]
      exact hv
    simp only [LinearMap.comp_apply, Submodule.subtype_apply, LinearEquiv.coe_coe,
      LinearMap.snd_apply]
    rw [h_v, map_sub, Prod.snd_sub, h_gu, sub_zero,
      Submodule.prodEquivOfIsCompl_symm_apply_right]
  -- If `g z ∈ U` then `g z = g u` for some `u ∈ U`, so `z ∈ U ∩ Z = 0`.
  have h_mem : (g : Module.End R V) z ∈ U :=
    (Submodule.prodEquivOfIsCompl_symm_apply_snd_eq_zero U Z hUZ).1 hz
  rw [← mem_stabilizer_iff.1 hg] at h_mem
  obtain ⟨u, hu, h_eq⟩ := h_mem
  have : (z : V) ∈ U := hg_inj h_eq ▸ hu
  exact Subtype.ext ((Submodule.disjoint_def.1 hUZ.disjoint) _ this z.prop)

private theorem blockParam_surjective : Function.Surjective (blockParam hUZ) := by
  rintro ⟨g, hg⟩
  let e := U.prodEquivOfIsCompl Z hUZ
  have hU := (Module.End.mem_invtSubmodule_iff_forall_mem_of_mem _).1
    (mem_invtSubmodule_of_mem_stabilizer hg)
  have h_split (w : V) : ((e.symm w).1 : V) + (e.symm w).2 = w := by
    rw [← Submodule.coe_prodEquivOfIsCompl' U Z hUZ, LinearEquiv.apply_symm_apply]
  -- The three blocks of `g`: `g` on `U`, and the two components of `g` on `Z`.
  let a₀ : Module.End R U := (g : Module.End R V).restrict hU
  let b₀ : Module.End R Z := LinearMap.snd R U Z ∘ₗ e.symm.toLinearMap ∘ₗ
    (g : Module.End R V) ∘ₗ Z.subtype
  let x₀ : Z →ₗ[R] U := LinearMap.fst R U Z ∘ₗ e.symm.toLinearMap ∘ₗ
    (g : Module.End R V) ∘ₗ Z.subtype
  have ha₀ : IsUnit a₀ := isUnit_restrict_of_mem_stabilizer hg hU
  have hb₀ : IsUnit b₀ := isUnit_snd_comp_of_mem_stabilizer hUZ hg
  refine ⟨(ha₀.unit, hb₀.unit, x₀), Subtype.ext (Units.ext (LinearMap.ext fun v ↦ ?_))⟩
  -- On `v = u + z`, the block map gives `g u + (x₀ z + b₀ z) = g u + g z`.
  obtain ⟨⟨u, z⟩, rfl⟩ := e.surjective v
  simp only [blockParam, blockUnit_apply, Submodule.coe_prodEquivOfIsCompl',
    Module.End.blockTriangular_apply, IsUnit.unit_spec, Submodule.coe_add]
  simp only [e, a₀, b₀, x₀, LinearMap.coe_restrict_apply, LinearMap.comp_apply,
    LinearEquiv.coe_coe, Submodule.subtype_apply, LinearMap.fst_apply, LinearMap.snd_apply]
  rw [add_assoc, h_split, LinearEquiv.symm_apply_apply, Submodule.coe_prodEquivOfIsCompl', map_add]

/-- **The block parametrisation of the stabiliser** of `U` in `GL(V)`, for a complement `Z` of `U`:
a triple `(a, b, x)` of automorphisms `a` of `U` and `b` of `Z` and a map `x : Z → U` gives the
automorphism `Submodule.blockUnit hUZ a b x` with blocks `a`, `b` and `x`, and every automorphism
stabilising `U` arises from exactly one triple. -/
noncomputable def stabilizerBlockEquiv :
    (Module.End R U)ˣ × (Module.End R Z)ˣ × (Z →ₗ[R] U) ≃ stabilizer (Module.End R V)ˣ U :=
  Equiv.ofBijective (blockParam hUZ) ⟨blockParam_injective hUZ, blockParam_surjective hUZ⟩

/-- The block parametrisation sends `(a, b, x)` to the automorphism with blocks `a`, `b`, `x`. -/
@[simp]
theorem coe_stabilizerBlockEquiv_apply (t : (Module.End R U)ˣ × (Module.End R Z)ˣ × (Z →ₗ[R] U)) :
    (stabilizerBlockEquiv hUZ t : (Module.End R V)ˣ) = blockUnit hUZ t.1 t.2.1 t.2.2 :=
  (rfl)

end Stabilizer

end Submodule
