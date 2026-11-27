/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Matrix.Action
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import TauCeti.Topology.Algebra.RestrictedProduct.Box
public import TauCeti.Topology.Algebra.RestrictedProduct.Pi

/-!
# Matrices over a restricted product

An invertible matrix over a restricted product acts factorwise on column vectors and preserves
integral vectors at almost every factor. Under `TauCeti.addPiRestrictedProduct`, its translate
of the integral vectors is the coordinate box of the local translates. These identities connect
matrix actions over a restricted product to their local actions, for example when computing
Haar measure scaling on adelic vectors.

## Main results

* `Matrix.GeneralLinearGroup.eventually_map_evalRingHom_smul_univ_pi`: almost every factor
  preserves integral vectors.
* `Matrix.GeneralLinearGroup.smul_apply_apply_restrictedProduct`: the action is computed factorwise.
* `Matrix.GeneralLinearGroup.preimage_addPiRestrictedProduct_symm_smul`: the translate of the
  integral vectors corresponds to the box of local translates.
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
theorem eventually_map_evalRingHom_smul_univ_pi {𝓕 : Filter P}
    (g : GL ι (Πʳ v, [R v, O v]_[𝓕])) :
    ∀ᶠ v in 𝓕, GeneralLinearGroup.map (evalRingHom R v) g •
        univ.pi (fun _ : ι ↦ (O v : Set (R v))) = univ.pi fun _ : ι ↦ (O v : Set (R v)) := by
  -- At almost every factor, the entries of `g` and of `g⁻¹` are integral.
  have hint : ∀ᶠ v in 𝓕, ∀ i j, g.val i j v ∈ O v ∧ g⁻¹.val i j v ∈ O v :=
    eventually_all.2 fun i ↦ eventually_all.2 fun j ↦
      (g.val i j).property.and (g⁻¹.val i j).property
  filter_upwards [hint] with v hv
  -- An invertible matrix with integral entries maps integral vectors to integral vectors.
  have hmaps (h : GL ι (Πʳ v, [R v, O v]_[𝓕])) (hh : ∀ i j, h.val i j v ∈ O v)
      (x : ι → R v) (hx : x ∈ univ.pi fun _ : ι ↦ (O v : Set (R v))) :
      GeneralLinearGroup.map (evalRingHom R v) h • x ∈ univ.pi fun _ : ι ↦ (O v : Set (R v)) :=
    fun i _ ↦ sum_mem fun j _ ↦ mul_mem (hh i j) (hx j (mem_univ j))
  refine Subset.antisymm ?_ fun x hx ↦ ?_
  · rintro _ ⟨x, hx, rfl⟩
    exact hmaps g (fun i j ↦ (hv i j).1) x hx
  · rw [mem_smul_set_iff_inv_smul_mem, ← map_inv]
    exact hmaps g⁻¹ (fun i j ↦ (hv i j).2) x hx

/-- The coordinate at `v` of the action of an invertible matrix `g` over a restricted product is
the action of its image `g_v` under the evaluation at `v` on the coordinates at `v`. -/
theorem smul_apply_apply_restrictedProduct {𝓕 : Filter P} (g : GL ι (Πʳ v, [R v, O v]_[𝓕]))
    (x : ι → Πʳ v, [R v, O v]_[𝓕]) (j : ι) (v : P) :
    (g • x) j v = (GeneralLinearGroup.map (evalRingHom R v) g • fun j ↦ x j v) j := by
  rw [Units.smul_def, smul_eq_mulVec, Units.smul_def, smul_eq_mulVec]
  exact RingHom.map_mulVec (evalRingHom R v) _ x j

/-- Under the swap of coordinates `TauCeti.addPiRestrictedProduct`, the translate by an invertible
matrix `g` of the integral vectors `(box O)ᶥ` is the coordinate box with factors `g_v • O vᶥ`. -/
theorem preimage_addPiRestrictedProduct_symm_smul {𝓕 : Filter P}
    (g : GL ι (Πʳ v, [R v, O v]_[𝓕])) :
    (addPiRestrictedProduct (n := ι) (𝓕 := 𝓕) O).symm ⁻¹'
        (g • univ.pi fun _ : ι ↦ (box fun v ↦ (O v : Set (R v)) : Set (Πʳ v, [R v, O v]_[𝓕]))) =
      box fun v ↦ GeneralLinearGroup.map (evalRingHom R v) g •
        univ.pi fun _ : ι ↦ (O v : Set (R v)) := by
  ext y
  have hy (v : P) : (fun j ↦ (addPiRestrictedProduct O).symm y j v) = y v :=
    funext fun j ↦ addPiRestrictedProduct_symm_apply O y j v
  rw [mem_preimage, mem_smul_set_iff_inv_smul_mem, mem_box]
  simp_rw [mem_smul_set_iff_inv_smul_mem, ← map_inv]
  simp only [mem_univ_pi, mem_box, smul_apply_apply_restrictedProduct, hy]
  exact forall_comm

end Matrix.GeneralLinearGroup
