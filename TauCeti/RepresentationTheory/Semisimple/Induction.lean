/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Induction.Basic
public import TauCeti.RepresentationTheory.Intertwining
public import TauCeti.RepresentationTheory.Semisimple.Restriction

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
(`Representation.iSup_range_indV_mk_eq_top`). This step, that `Res_N Ind_H^G ρ` is semisimple
whenever `Res_N ρ` is, needs neither finite index nor finite dimension and is stated separately
(`Representation.isSemisimpleRepresentation_ind_comp_subtype`). This is the averaging argument
run over `G ⧸ N` after Mackey's formula `Res_N Ind_H^G ρ = ⊕_{s ∈ G/H} {}^s (Res_N ρ)`, in the
form that needs only the spanning images rather than the direct sum. The two facts about the
generator maps hold over any commutative ring and live with the rest of the generator API in
`TauCeti.RepresentationTheory.Induction.Basic`.

## Main results

* `Representation.isSemisimpleRepresentation_ind_comp_subtype`: if the restriction of `ρ` to `N`
  is semisimple, so is the restriction of `Ind_H^G ρ` to `N`, with no finiteness assumption.
* `Representation.isSemisimpleRepresentation_ind`: induction from a subgroup containing a normal
  subgroup of invertible index preserves semisimplicity.
-/

public section

namespace Representation

variable {k G U : Type*} [Field k] [Group G] [AddCommGroup U] [Module k U]
  {H N : Subgroup G} [N.Normal]

/-- **Restricting an induced representation to a normal subgroup preserves semisimplicity.** Let
`N ≤ H ≤ G` with `N` normal in `G`. If the restriction of `ρ` to `N` is semisimple, then so is the
restriction of `Ind_H^G ρ` to `N`. No finiteness of the index or of the dimension is needed. -/
theorem isSemisimpleRepresentation_ind_comp_subtype (ρ : Representation k H U) (hNH : N ≤ H)
    [hres : IsSemisimpleRepresentation (ρ.comp (Subgroup.inclusion hNH))] :
    IsSemisimpleRepresentation ((ind H.subtype ρ).comp N.subtype) := by
  -- The conjugate of `Res_N ρ` by `s` is semisimple, and the generator map at `s` intertwines it
  -- into `Res_N Ind ρ`.
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
    exact (f s).isSemisimpleRepresentation_range
  exact isSemisimpleRepresentation_of_iSup_eq_top hf (iSup_range_indV_mk_eq_top _ ρ)

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
  have := isSemisimpleRepresentation_ind_comp_subtype ρ hNH
  exact isSemisimpleRepresentation_of_comp_subtype _ N

end Representation
