/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import TauCeti.Topology.Algebra.RestrictedProduct.Box
public import TauCeti.Topology.Algebra.RestrictedProduct.Pi
import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.Subalgebra

/-!
# Matrices over a restricted product

An invertible matrix over a restricted product acts factorwise on column vectors and preserves
integral vectors at almost every factor. Under `TauCeti.addPiRestrictedProduct`, its translate
of the integral vectors is the coordinate box of the local translates. These identities connect
matrix actions over a restricted product to their local actions, for example when computing
Haar measure scaling on adelic vectors.

## Main results

* `Matrix.GeneralLinearGroup.eventually_map_evalRingHom_smul_univ_pi_eq_self`: almost every factor
  preserves integral vectors.
* `Matrix.GeneralLinearGroup.smul_apply_apply_restrictedProduct`: the action is computed factorwise.
* `Matrix.GeneralLinearGroup.preimage_addPiRestrictedProduct_symm_smul_univ_pi_box`: the translate
  of the integral vectors corresponds to the box of local translates.
-/

public section

open Filter Matrix Set RestrictedProduct TauCeti
open scoped Pointwise RestrictedProduct

variable {P ι : Type*} {R : P → Type*} {S : P → Type*} [∀ v, CommRing (R v)]
  [∀ v, SetLike (S v) (R v)] [∀ v, SubringClass (S v) (R v)] {O : ∀ v, S v}
  [Fintype ι] [DecidableEq ι]

namespace Matrix.GeneralLinearGroup

/-- **Almost every factor of an invertible matrix is integral.** An invertible matrix `g` over a
restricted product `Πʳ v, [R v, O v]_[𝓕]` has, at `𝓕`-almost every factor `v`, entries and inverse
entries in `O v`, so its image under the evaluation at `v` maps the integral vectors `O vᶥ` onto
themselves. -/
theorem eventually_map_evalRingHom_smul_univ_pi_eq_self {𝓕 : Filter P}
    (g : GL ι (Πʳ v, [R v, O v]_[𝓕])) :
    ∀ᶠ v in 𝓕, GeneralLinearGroup.map (evalRingHom R v) g •
        univ.pi (fun _ : ι ↦ (O v : Set (R v))) = univ.pi fun _ : ι ↦ (O v : Set (R v)) := by
  -- At almost every factor, the entries of `g` and of `g⁻¹` are integral.
  have hint : ∀ᶠ v in 𝓕, ∀ i j, g.val i j v ∈ O v ∧ g⁻¹.val i j v ∈ O v :=
    eventually_all.2 fun i ↦ eventually_all.2 fun j ↦
      (g.val i j).property.and (g⁻¹.val i j).property
  filter_upwards [hint] with v hv
  -- Viewing `O v` as a `ℤ`-subalgebra, the inverse of `g_v` comes from it, so it preserves
  -- the integral vectors.
  let A := subalgebraOfSubring (Subring.ofClass (O v))
  have hA (x : R v) : x ∈ A ↔ x ∈ O v := by
    rw [mem_subalgebraOfSubring, ← SetLike.mem_coe, Subring.coe_ofClass, SetLike.mem_coe]
  have hg : (GeneralLinearGroup.map (evalRingHom R v) g)⁻¹ ∈
      (GeneralLinearGroup.map (n := ι) (A.val : A →+* R v)).range := by
    apply MonoidHom.mem_range.2
    apply (mem_range_map_val_iff A _).2
    simpa only [hA, ← map_inv, inv_inv, GeneralLinearGroup.val_map_apply, Matrix.map_apply,
      evalRingHom_apply] using ⟨fun i j ↦ (hv i j).2, fun i j ↦ (hv i j).1⟩
  ext x
  rw [mem_smul_set_iff_inv_smul_mem, Units.smul_def, smul_eq_mulVec]
  simp only [mem_univ_pi, SetLike.mem_coe, ← hA]
  exact forall_mulVec_mem_iff hg

/-- The coordinate at `v` of the action of an invertible matrix `g` over a restricted product is
the action of its image `g_v` under the evaluation at `v` on the coordinates at `v`. -/
@[simp]
theorem smul_apply_apply_restrictedProduct {𝓕 : Filter P} (g : GL ι (Πʳ v, [R v, O v]_[𝓕]))
    (x : ι → Πʳ v, [R v, O v]_[𝓕]) (j : ι) (v : P) :
    (g • x) j v = (GeneralLinearGroup.map (evalRingHom R v) g • fun j ↦ x j v) j := by
  rw [Units.smul_def, smul_eq_mulVec, Units.smul_def, smul_eq_mulVec,
    GeneralLinearGroup.val_map_apply]
  simpa only [Function.comp_def, evalRingHom_apply] using
    RingHom.map_mulVec (evalRingHom R v) (g : Matrix ι ι (Πʳ v, [R v, O v]_[𝓕])) x j

/-- Under the swap of coordinates `TauCeti.addPiRestrictedProduct`, the translate by an invertible
matrix `g` of the integral vectors `(box O)ᶥ` is the coordinate box with factors `g_v • O vᶥ`. -/
theorem preimage_addPiRestrictedProduct_symm_smul_univ_pi_box {𝓕 : Filter P}
    (g : GL ι (Πʳ v, [R v, O v]_[𝓕])) :
    (addPiRestrictedProduct (n := ι) (𝓕 := 𝓕) (fun _ ↦ O)).symm ⁻¹'
        (g • univ.pi fun _ : ι ↦ (box fun v ↦ (O v : Set (R v)) : Set (Πʳ v, [R v, O v]_[𝓕]))) =
      box fun v ↦ GeneralLinearGroup.map (evalRingHom R v) g •
        univ.pi fun _ : ι ↦ (O v : Set (R v)) := by
  ext y
  have hy (v : P) : (fun j ↦ (addPiRestrictedProduct (fun _ ↦ O)).symm y j v) = y v :=
    funext fun j ↦ addPiRestrictedProduct_symm_apply (fun _ ↦ O) y j v
  rw [mem_preimage, mem_smul_set_iff_inv_smul_mem, mem_box]
  simp_rw [mem_smul_set_iff_inv_smul_mem, ← map_inv]
  simp only [mem_univ_pi, mem_box, smul_apply_apply_restrictedProduct, hy]
  exact forall_comm

end Matrix.GeneralLinearGroup
