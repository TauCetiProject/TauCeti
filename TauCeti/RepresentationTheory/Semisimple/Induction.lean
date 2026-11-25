/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RepresentationTheory.Induced
public import TauCeti.RepresentationTheory.Intertwining
public import TauCeti.RepresentationTheory.Semisimple.Restriction
import TauCeti.RepresentationTheory.Induction.Transitivity

/-!
# Semisimplicity of induced representations

Let `N ≤ H ≤ G` with `N` normal in `G`, and let `ρ` be a finite-dimensional semisimple
representation of `H` over a field `k`. If the index `[G : N]` is invertible in `k` (so finite),
the induced representation `Ind_H^G ρ` is semisimple
(`Representation.isSemisimpleRepresentation_ind`). Neither `G` nor `H` need be finite, and `ρ` need
not factor through a finite quotient of `H`.

The proof restricts to `N` and then ascends by the relative Maschke theorem
(`Representation.isSemisimpleRepresentation_of_comp_subtype`). For `s ∈ G`, the generators
`⟦s ⊗ a⟧` of `Ind_H^G ρ` span an `N`-stable subspace, the image of the `N`-equivariant map
`a ↦ ⟦s ⊗ a⟧` out of `ρ` restricted along `n ↦ s n s⁻¹`
(`Representation.indV_mk_comp_conjNormal`). That restriction is semisimple because the restriction
of `ρ` to the normal subgroup `N` of `H` is
(`Representation.isSemisimpleRepresentation_comp_subtype`), and these images span `Ind_H^G ρ`
(`Representation.iSup_range_indV_mk_eq_top`). This is the averaging argument run over `G ⧸ N`
after Mackey's formula `Res_N Ind_H^G ρ = ⊕_{s ∈ G/H} {}^s (Res_N ρ)`, in the form that needs only
the spanning images rather than the direct sum.

## Main results

* `Representation.iSup_range_indV_mk_eq_top`: the images of the generator maps `a ↦ ⟦s ⊗ a⟧`
  span an induced representation.
* `Representation.isSemisimpleRepresentation_ind`: induction from a subgroup containing a normal
  subgroup of invertible index preserves semisimplicity.
-/

public section

namespace Representation

variable {k G U : Type*} [Field k] [Group G] [AddCommGroup U] [Module k U]

/-- The images of the generator maps `a ↦ ⟦s ⊗ a⟧`, for `s` ranging over the target group, span an
induced representation. -/
theorem iSup_range_indV_mk_eq_top {G' : Type*} [Group G'] (φ : G' →* G)
    (ρ : Representation k G' U) :
    ⨆ s : G, LinearMap.range (IndV.mk φ ρ s) = ⊤ := by
  set P := ⨆ s : G, LinearMap.range (IndV.mk φ ρ s)
  have h : P.mkQ = 0 := IndV.hom_ext _ _ fun s ↦ LinearMap.ext fun a ↦ by
    simpa using (le_iSup (fun s : G ↦ LinearMap.range (IndV.mk φ ρ s)) s)
      (LinearMap.mem_range_self _ a)
  rw [← Submodule.ker_mkQ P, h, LinearMap.ker_zero]

variable {H N : Subgroup G} [N.Normal]

/-- For `s ∈ G` and a representation `ρ` of `H ≥ N`, the generator map `a ↦ ⟦s ⊗ a⟧` into
`Ind_H^G ρ` is `N`-equivariant from `ρ` restricted along `n ↦ s n s⁻¹ : N → H`. -/
theorem indV_mk_comp_conjNormal (ρ : Representation k H U) (hNH : N ≤ H) (s : G) (n : N) :
    IndV.mk H.subtype ρ s ∘ₗ
        ρ ((Subgroup.inclusion hNH).comp (MulAut.conjNormal s).toMonoidHom n) =
      ind H.subtype ρ (n : G) ∘ₗ IndV.mk H.subtype ρ s := by
  refine LinearMap.ext fun a ↦ ?_
  set h : H := (Subgroup.inclusion hNH).comp (MulAut.conjNormal s).toMonoidHom n
  have hh : (h : G) = s * n * s⁻¹ := MulAut.conjNormal_apply s n
  have key := TauCeti.indV_mk_apply_inv H.subtype ρ h⁻¹ s a
  rw [inv_inv] at key
  change IndV.mk H.subtype ρ s (ρ h a) = ind H.subtype ρ n (IndV.mk H.subtype ρ s a)
  rw [key, ind_mk, Subgroup.coe_subtype,
    Subgroup.coe_inv, hh]
  congr 1
  group

/-- **Induction preserves semisimplicity when a normal subgroup of invertible index is contained in
the inducing subgroup.** Let `N ≤ H ≤ G` with `N` normal in `G` and `[G : N]` invertible in `k` (so
finite). The induced representation of a finite-dimensional semisimple representation of `H` is
semisimple. -/
theorem isSemisimpleRepresentation_ind (ρ : Representation k H U) (hNH : N ≤ H)
    [NeZero (N.index : k)] [FiniteDimensional k U] [ρ.IsSemisimpleRepresentation] :
    (ind H.subtype ρ).IsSemisimpleRepresentation := by
  -- The restriction of `ρ` to `N`, along the inclusion `N → H`, is semisimple.
  have hres : IsSemisimpleRepresentation (ρ.comp (Subgroup.inclusion hNH)) := by
    have := isSemisimpleRepresentation_comp_subtype ρ (N.subgroupOf H)
    have e : ρ.comp (Subgroup.inclusion hNH) =
        (ρ.comp (N.subgroupOf H).subtype).comp
          (Subgroup.subgroupOfEquivOfLe hNH).symm.toMonoidHom :=
      MonoidHom.ext fun _ ↦ rfl
    rw [e, MonoidHom.isSemisimpleRepresentation_comp_surjective_iff _
      (Subgroup.subgroupOfEquivOfLe hNH).symm.surjective]
    infer_instance
  -- So is its conjugate by `s`, which the generator map at `s` intertwines into `Res_N Ind ρ`.
  let f (s : G) : IntertwiningMap
      (ρ.comp ((Subgroup.inclusion hNH).comp (MulAut.conjNormal s).toMonoidHom))
      ((ind H.subtype ρ).comp N.subtype) :=
    ⟨IndV.mk H.subtype ρ s, fun n ↦ indV_mk_comp_conjNormal ρ hNH s n⟩
  have hf (s : G) : ((f s).range).toRepresentation.IsSemisimpleRepresentation := by
    have : IsSemisimpleRepresentation (ρ.comp ((Subgroup.inclusion hNH).comp
        (MulAut.conjNormal s).toMonoidHom)) := by
      rw [← MonoidHom.comp_assoc]
      exact (MonoidHom.isSemisimpleRepresentation_comp_surjective_iff
        (MulAut.conjNormal s).toMonoidHom (MulAut.conjNormal s).surjective _).mpr hres
    refine ((f s).codRestrict (f s).range fun a ↦ ⟨a, rfl⟩).isSemisimpleRepresentation_of_surjective
      fun ⟨_, a, ha⟩ ↦ ⟨a, Subtype.ext (((f s).codRestrict_apply_coe _ _ a).trans ha)⟩
  have := isSemisimpleRepresentation_of_iSup_eq_top hf (iSup_range_indV_mk_eq_top _ ρ)
  exact isSemisimpleRepresentation_of_comp_subtype _ N

end Representation
