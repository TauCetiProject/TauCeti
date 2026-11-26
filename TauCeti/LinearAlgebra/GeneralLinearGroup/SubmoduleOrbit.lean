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
import Mathlib.GroupTheory.Index
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.LinearAlgebra.GeneralLinearGroup.Basic

/-!
# The action of `GL(V)` on the subspaces of `V`

The automorphisms of a finite-dimensional vector space `V` act on its subspaces by taking images.
An automorphism maps a subspace `U` onto `Y` as soon as it maps `U` into `Y` and the two have the
same dimension, so the orbit of `U` consists of the subspaces of the dimension of `U`. With the
orbit-stabiliser theorem this counts the subspaces of a given dimension through the stabiliser of
one of them.

## Main results

* `Submodule.units_smul_eq_of_forall_mem`: an automorphism mapping `U` into a subspace `Y` of the
  same dimension maps `U` onto `Y`.
* `Submodule.mem_invtSubmodule_of_mem_stabilizer`: an automorphism stabilising `U` leaves `U`
  invariant.
* `Submodule.mem_orbit_units_iff`: the orbit of `U` is the set of subspaces of the dimension of `U`.
* `Submodule.stabilizerBlockEquiv`: for a complement `Z` of `U`, the stabiliser of `U` is
  parametrised by the automorphisms of `U` and of `Z` and the maps `Z → U`, through the block
  automorphisms `Submodule.blockUnit`.
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

variable {K V : Type*} [DivisionRing K] [AddCommGroup V] [Module K V]

/-- An automorphism mapping `U` into a finite-dimensional subspace `Y` of the same dimension maps
`U` onto `Y`. -/
theorem units_smul_eq_of_forall_mem (g : (Module.End K V)ˣ) {U Y : Submodule K V}
    [FiniteDimensional K Y] (h : ∀ x ∈ U, (g : Module.End K V) x ∈ Y)
    (hd : finrank K Y = finrank K U) : g • U = Y :=
  Submodule.eq_of_le_of_finrank_eq (Submodule.map_le_iff_le_comap.2 h)
    (((LinearMap.GeneralLinearGroup.generalLinearEquiv K V) g).finrank_map_eq U |>.trans hd.symm)

variable [FiniteDimensional K V]

/-- The subspaces in the orbit of `U` under `GL(V)` are those of the dimension of `U`. -/
theorem mem_orbit_units_iff {U Y : Submodule K V} :
    Y ∈ orbit (Module.End K V)ˣ U ↔ finrank K Y = finrank K U := by
  refine ⟨?_, fun hY ↦ ?_⟩
  · rintro ⟨g, rfl⟩
    exact ((LinearMap.GeneralLinearGroup.generalLinearEquiv K V) g).finrank_map_eq U
  · obtain ⟨g, hg⟩ :=
      Submodule.exists_linearEquiv_restrict_eq (LinearEquiv.ofFinrankEq U Y hY.symm)
    refine ⟨LinearMap.GeneralLinearGroup.ofLinearEquiv g,
      units_smul_eq_of_forall_mem _ (fun x hx ↦ ?_) hY⟩
    simp [← hg ⟨x, hx⟩]

/-- Orbit-stabiliser: the order of the stabiliser of `U` in `GL(V)` times the number of subspaces
of the dimension of `U` is the order of `GL(V)`. -/
theorem card_stabilizer_mul_card_finrank_eq (U : Submodule K V) :
    Nat.card (stabilizer (Module.End K V)ˣ U) *
        Nat.card {Y : Submodule K V // finrank K Y = finrank K U} =
      Nat.card (Module.End K V)ˣ := by
  have h_orbit : orbit (Module.End K V)ˣ U = {Y : Submodule K V | finrank K Y = finrank K U} :=
    Set.ext fun _ ↦ mem_orbit_units_iff
  rw [← Subgroup.card_mul_index (stabilizer (Module.End K V)ˣ U), index_stabilizer, h_orbit,
    ← Nat.card_coe_set_eq]
  -- The coercion of the set `{Y | p Y}` to a type is by definition the subtype `{Y // p Y}`.
  rfl

section Stabilizer

variable {U Z : Submodule K V} (hUZ : IsCompl U Z)

/-- The automorphism of `V = U ⊕ Z` with diagonal blocks `a`, `b` and upper right block `x`. -/
noncomputable def blockUnit (a : (Module.End K U)ˣ) (b : (Module.End K Z)ˣ)
    (x : Z →ₗ[K] U) : (Module.End K V)ˣ :=
  LinearMap.GeneralLinearGroup.ofLinearEquiv
    ((U.prodEquivOfIsCompl Z hUZ).symm ≪≫ₗ LinearEquiv.prodComm K U Z ≪≫ₗ
      (LinearMap.GeneralLinearGroup.toLinearEquiv b).skewProd
        (LinearMap.GeneralLinearGroup.toLinearEquiv a) x ≪≫ₗ
      LinearEquiv.prodComm K Z U ≪≫ₗ U.prodEquivOfIsCompl Z hUZ)

omit [FiniteDimensional K V] in
/-- In the splitting `V ≅ U × Z`, the block automorphism acts as the block map
`(u, z) ↦ (a u + x z, b z)`. -/
theorem blockUnit_apply (a : (Module.End K U)ˣ) (b : (Module.End K Z)ˣ)
    (x : Z →ₗ[K] U) (v : V) :
    (blockUnit hUZ a b x : Module.End K V) v = U.prodEquivOfIsCompl Z hUZ
      (Module.End.blockTriangular (a : Module.End K U) (b : Module.End K Z) x
        ((U.prodEquivOfIsCompl Z hUZ).symm v)) := by
  simp [blockUnit]

/-- The block automorphism stabilises `U`. -/
theorem blockUnit_mem_stabilizer (a : (Module.End K U)ˣ) (b : (Module.End K Z)ˣ)
    (x : Z →ₗ[K] U) : blockUnit hUZ a b x ∈ stabilizer (Module.End K V)ˣ U := by
  refine mem_stabilizer_iff.2 (units_smul_eq_of_forall_mem _ ?_ rfl)
  intro v hv
  obtain ⟨u, rfl⟩ : ∃ u : U, (u : V) = v := ⟨⟨v, hv⟩, rfl⟩
  rw [blockUnit_apply, Submodule.prodEquivOfIsCompl_symm_apply_left]
  simp

/-- The block parametrisation of the stabiliser of `U` in `GL(V)`, as a function. -/
private noncomputable def blockParam
    (t : (Module.End K U)ˣ × (Module.End K Z)ˣ × (Z →ₗ[K] U)) :
    stabilizer (Module.End K V)ˣ U :=
  ⟨blockUnit hUZ t.1 t.2.1 t.2.2, blockUnit_mem_stabilizer hUZ _ _ _⟩

private theorem blockParam_injective : Function.Injective (blockParam hUZ) := by
  rintro ⟨a, b, x⟩ ⟨a', b', x'⟩ h
  have h_blk (p : U × Z) :
      Module.End.blockTriangular (a : Module.End K U) (b : Module.End K Z) x p =
        Module.End.blockTriangular (a' : Module.End K U) (b' : Module.End K Z) x' p := by
    have := congrArg (fun g : stabilizer (Module.End K V)ˣ U ↦
      ((g : (Module.End K V)ˣ) : Module.End K V) (U.prodEquivOfIsCompl Z hUZ p)) h
    simp only [blockParam, blockUnit_apply, LinearEquiv.symm_apply_apply] at this
    exact (U.prodEquivOfIsCompl Z hUZ).injective this
  have ha : a = a' :=
    Units.ext (LinearMap.ext fun u ↦ by simpa using congrArg Prod.fst (h_blk (u, 0)))
  have hb : b = b' :=
    Units.ext (LinearMap.ext fun z ↦ by simpa using congrArg Prod.snd (h_blk (0, z)))
  have hx : x = x' := LinearMap.ext fun z ↦ by simpa using congrArg Prod.fst (h_blk (0, z))
  subst ha hb hx
  rfl

private theorem blockParam_surjective : Function.Surjective (blockParam hUZ) := by
  rintro ⟨g, hg⟩
  let e := U.prodEquivOfIsCompl Z hUZ
  have hU := (Module.End.mem_invtSubmodule_iff_forall_mem_of_mem _).1
    (mem_invtSubmodule_of_mem_stabilizer hg)
  have hg_inj : Function.Injective (g : Module.End K V) :=
    ((LinearMap.GeneralLinearGroup.generalLinearEquiv K V) g).injective
  -- The three blocks of `g`: `g` on `U`, and the two components of `g` on `Z`.
  let a₀ : Module.End K U := (g : Module.End K V).restrict hU
  let b₀ : Module.End K Z := LinearMap.snd K U Z ∘ₗ e.symm.toLinearMap ∘ₗ
    (g : Module.End K V) ∘ₗ Z.subtype
  let x₀ : Z →ₗ[K] U := LinearMap.fst K U Z ∘ₗ e.symm.toLinearMap ∘ₗ
    (g : Module.End K V) ∘ₗ Z.subtype
  have ha₀ : IsUnit a₀ := (LinearMap.isUnit_iff_ker_eq_bot _).2 <| LinearMap.ker_eq_bot.2
    fun u u' h ↦ Subtype.ext (hg_inj (congrArg Subtype.val h))
  -- If `g z ∈ U` then `g z = g u` for some `u ∈ U`, so `z ∈ U ∩ Z = 0`.
  have hb₀ : IsUnit b₀ := by
    refine (LinearMap.isUnit_iff_ker_eq_bot _).2 (LinearMap.ker_eq_bot'.2 fun z hz ↦ ?_)
    have h_mem : (g : Module.End K V) z ∈ U :=
      (Submodule.prodEquivOfIsCompl_symm_apply_snd_eq_zero U Z hUZ).1 hz
    rw [← mem_stabilizer_iff.1 hg] at h_mem
    obtain ⟨u, hu, h_eq⟩ := h_mem
    have : (z : V) ∈ U := hg_inj h_eq ▸ hu
    exact Subtype.ext ((Submodule.disjoint_def.1 hUZ.disjoint) _ this z.prop)
  refine ⟨(ha₀.unit, hb₀.unit, x₀), Subtype.ext (Units.ext (LinearMap.ext fun v ↦ ?_))⟩
  -- On `v = u + z`, the block map gives `g u + (x₀ z + b₀ z) = g u + g z`.
  obtain ⟨⟨u, z⟩, rfl⟩ := e.surjective v
  have h_split (w : V) : ((e.symm w).1 : V) + (e.symm w).2 = w := by
    rw [← Submodule.coe_prodEquivOfIsCompl' U Z hUZ, LinearEquiv.apply_symm_apply]
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
    (Module.End K U)ˣ × (Module.End K Z)ˣ × (Z →ₗ[K] U) ≃ stabilizer (Module.End K V)ˣ U :=
  Equiv.ofBijective (blockParam hUZ) ⟨blockParam_injective hUZ, blockParam_surjective hUZ⟩

/-- The block parametrisation sends `(a, b, x)` to the automorphism with blocks `a`, `b`, `x`. -/
@[simp]
theorem coe_stabilizerBlockEquiv_apply (t : (Module.End K U)ˣ × (Module.End K Z)ˣ × (Z →ₗ[K] U)) :
    (stabilizerBlockEquiv hUZ t : (Module.End K V)ˣ) = blockUnit hUZ t.1 t.2.1 t.2.2 :=
  (rfl)

end Stabilizer

end Submodule
