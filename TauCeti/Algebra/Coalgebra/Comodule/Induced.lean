/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Coalgebra.Comodule.Cofree
public import TauCeti.Algebra.Coalgebra.Comodule.Corestrict
public import TauCeti.Algebra.Coalgebra.Comodule.Preadditive
public import TauCeti.Algebra.Coalgebra.Subcomodule.Comap
public import TauCeti.Algebra.Coalgebra.Subcomodule.Induced

/-!
# Induced comodules and Frobenius reciprocity

Let `f : C →ₗc[R] D` be a morphism of coalgebras over a commutative ring `R`, with `C` flat, and
let `M` be a right `D`-comodule with coaction `ρ`. The **induced comodule** `Ind_f M` is the
cotensor product `M □_D C`: the equalizer inside `M ⊗[R] C` of the two maps
`(M ⊗[R] D) ⊗[R] C ⟵ M ⊗[R] C`,

* `ρ ⊗ id`, coacting on the first factor, and
* `m ⊗ c ↦ ∑ (m ⊗ f c₁) ⊗ c₂`, comultiplying the second factor and mapping its left half to `D`.

Both maps are morphisms between cofree right `C`-comodules (`TauCeti.Comodule.cofree`), so their
equalizer is the kernel of their difference, a subcomodule of the cofree comodule `M ⊗[R] C`.
Flatness of `C` makes this kernel a comodule in its own right.

For an affine group scheme `G = Spec C` and a closed subgroup `H = Spec D`, with `f` the
restriction of functions, right comodules are representations and `Ind_f M` is the induced
representation `ind_H^G M`. Reading `m ⊗ c` as an `M`-valued function on `G`, the equalizer
condition says `F(h g) = h F(g)`, and `G` acts by right translation. This is the algebraic
induction underlying the induced modules `∇(λ)` of a reductive group; Jantzen's convention
`F(g h) = h⁻¹ F(g)`, with `G` acting by left translation, differs from this one by the antipode.

Induction is right adjoint to corestriction along `f`, by **Frobenius reciprocity**
(`TauCeti.Comodule.inducedEquiv`): for every right `C`-comodule `N`,

  `Hom_C(N, Ind_f M) ≃ₗ[R] Hom_D(N, M)`,

where `N` is a `D`-comodule by corestriction. The forward map composes with the evaluation
`Ind_f M → M` induced by the counit of `C` (evaluation at the identity of `G`), and the inverse
sends `u` to `(u ⊗ id) ∘ ρ_N`. This generalizes the universal property of the cofree comodule,
`TauCeti.Comodule.Hom.cofreeEquiv`, which is the case where `D = R` and `f` is the counit: then
the equalizer condition is vacuous.

## Main declarations

* `TauCeti.Comodule.induced`: the induced comodule `Ind_f M`, as a subcomodule of the cofree
  comodule `M ⊗[R] C`.
* `TauCeti.Comodule.mem_induced_iff`: its defining cotensor equalizer.
* `TauCeti.Comodule.inducedEval`: evaluation `Ind_f M → M` by the counit of `C`, a morphism of
  `D`-comodules after corestriction.
* `TauCeti.Comodule.inducedLift`: the morphism `N → Ind_f M` attached to a morphism of
  `D`-comodules `N → M`.
* `TauCeti.Comodule.inducedEquiv`: Frobenius reciprocity, natural in `N`
  (`TauCeti.Comodule.inducedEquiv_comp`) and in `M`
  (`TauCeti.Comodule.inducedEquiv_inducedMap_comp`).
* `TauCeti.Comodule.inducedMap`: functoriality of induction, acting as `h ⊗ id` on `M ⊗[R] C`.

## References

* J. C. Jantzen, *Representations of Algebraic Groups*, 2nd ed., I.3.3–I.3.4.
* M. Takeuchi, *Morita theorems for categories of comodules*, J. Fac. Sci. Univ. Tokyo 24
  (1977), for the cotensor product and its adjunction with corestriction.
-/

public section

open scoped TensorProduct
open TensorProduct LinearMap

namespace TauCeti

namespace Comodule

universe u v w x y z

variable {R : Type u} {C : Type v} {D : Type w}
variable [CommRing R]
variable [AddCommMonoid C] [Module R C] [Coalgebra R C]
variable [AddCommMonoid D] [Module R D] [Coalgebra R D]
variable (f : C →ₗc[R] D)
variable {M : Type x} {M' : Type z} {N : Type y}
variable [AddCommMonoid M] [Module R M]
variable [AddCommMonoid M'] [Module R M']
variable [AddCommMonoid N] [Module R N]

attribute [local instance] cofree

/-- Evaluation `M ⊗[R] C → M` by the counit of `C`. -/
private noncomputable abbrev counitEval (M : Type*) [AddCommMonoid M] [Module R M] :
    M ⊗[R] C →ₗ[R] M :=
  (TensorProduct.rid R M).toLinearMap ∘ₗ (Coalgebra.counit (R := R) (A := C)).lTensor M

variable [Module.Flat R C] [Comodule R D M] [Comodule R D M'] [Comodule R C N]

variable (M) in
/-- **The induced comodule** `Ind_f M = M □_D C` of a right `D`-comodule `M` along a coalgebra
morphism `f : C →ₗc[R] D`. It is the subcomodule of the cofree comodule `M ⊗[R] C` on which
`ρ ⊗ id` agrees with `m ⊗ c ↦ ∑ (m ⊗ f c₁) ⊗ c₂` (`TauCeti.Comodule.mem_induced_iff`). -/
noncomputable def induced : Subcomodule R C (M ⊗[R] C) :=
  Hom.ker (Hom.cofreeMap (C := C) (coact (R := R) (C := D) (M := M)) -
    Hom.cofreeLift (C := C) ((f : C →ₗ[R] D).lTensor M))

/-- Membership in the induced comodule, with the second map of the equalizer written as the
cofree lift of `id ⊗ f`. -/
private theorem mem_induced_iff_cofreeLift {t : M ⊗[R] C} :
    t ∈ induced f M ↔
      (coact (R := R) (C := D) (M := M)).rTensor C t =
        Hom.cofreeLift (C := C) ((f : C →ₗ[R] D).lTensor M) t := by
  -- `sub_eq_zero` needs a group; this is the instance `Hom.sub_apply` uses for the difference
  -- in `induced`, extending the existing `AddCommMonoid` by negation `-1 • x`.
  let _ : AddCommGroup ((M ⊗[R] D) ⊗[R] C) := Module.addCommMonoidToAddCommGroup R
  rw [induced, Hom.mem_ker, Hom.sub_apply, sub_eq_zero, Hom.cofreeMap_apply]

/-- **The cotensor equalizer.** A tensor `t ∈ M ⊗[R] C` lies in `Ind_f M` exactly when coacting
on its first factor agrees with comultiplying its second factor and applying `f` to the left
half: `(ρ ⊗ id) t = (id ⊗ (f ⊗ id) ∘ Δ) t`, up to reassociation. -/
theorem mem_induced_iff {t : M ⊗[R] C} :
    t ∈ induced f M ↔
      (coact (R := R) (C := D) (M := M)).rTensor C t =
        (TensorProduct.assoc R M D C).symm
          (((f : C →ₗ[R] D).rTensor C ∘ₗ Coalgebra.comul).lTensor M t) := by
  rw [mem_induced_iff_cofreeLift, Hom.cofreeLift_lTensor_apply]

/-- **The key identity on `Ind_f M`.** Coacting on the counit evaluation of `t ∈ Ind_f M` gives
`(id ⊗ f) t`. -/
private theorem coact_counitEval_of_mem {t : M ⊗[R] C} (ht : t ∈ induced f M) :
    coact (R := R) (C := D) (M := M) (counitEval (C := C) M t) =
      (f : C →ₗ[R] D).lTensor M t := by
  -- Apply the counit evaluation of `(M ⊗[R] D) ⊗[R] C` to the two sides of the equalizer.
  have h := congrArg (counitEval (C := C) (M ⊗[R] D)) ((mem_induced_iff_cofreeLift f).mp ht)
  rw [← LinearMap.comp_apply (counitEval (C := C) (M ⊗[R] D)), LinearMap.comp_assoc,
    rid_comp_lTensor_counit_comp_rTensor, LinearMap.comp_apply] at h
  rw [h]
  exact LinearMap.congr_fun (Hom.rid_comp_lTensor_counit_comp_cofreeLift (C := C) _) t

/-- **Evaluation at the identity.** The counit of `C` evaluates the induced comodule into `M`,
`t ↦ (id ⊗ ε) t`. After corestricting `Ind_f M` along `f`, this is a morphism of
`D`-comodules: the counit of the reciprocity adjunction. -/
noncomputable def inducedEval :
    letI := Corestrict (M := induced f M) f
    Hom R D (induced f M) M :=
  letI := Corestrict (M := induced f M) f
  { toLinearMap := counitEval (C := C) M ∘ₗ SMulMemClass.subtype (induced f M)
    map_coact := by
      refine LinearMap.ext fun t ↦ ?_
      have hsub := Subcomodule.subtype_rTensor_coact (induced f M) t
      have hev : (counitEval (C := C) M).rTensor C (cofreeCoact R C M (t : M ⊗[R] C)) = t :=
        LinearMap.congr_fun
          (rTensor_rid_comp_lTensor_counit_comp_cofreeCoact (R := R) (C := C) (M := M)) _
      simp only [LinearMap.comp_apply, corestrict_coact_apply, SMulMemClass.subtype_apply]
      calc TensorProduct.map (counitEval (C := C) M ∘ₗ SMulMemClass.subtype (induced f M))
              LinearMap.id (TensorProduct.map LinearMap.id (f : C →ₗ[R] D)
                (coact (R := R) (C := C) (M := induced f M) t))
          = TensorProduct.map (counitEval (C := C) M) (f : C →ₗ[R] D)
              ((SMulMemClass.subtype (induced f M)).rTensor C
                (coact (R := R) (C := C) (M := induced f M) t)) := by
            simp [LinearMap.rTensor_def, TensorProduct.map_map]
        _ = (f : C →ₗ[R] D).lTensor M ((counitEval (C := C) M).rTensor C
              (cofreeCoact R C M (t : M ⊗[R] C))) := by
            rw [hsub, ← LinearMap.comp_apply ((f : C →ₗ[R] D).lTensor M),
              LinearMap.lTensor_comp_rTensor, cofree_coact, cofreeCoact_def]
        _ = coact (R := R) (C := D) (M := M) (counitEval (C := C) M (t : M ⊗[R] C)) := by
            rw [hev, coact_counitEval_of_mem f t.2] }

private theorem inducedEval_toLinearMap :
    letI := Corestrict (M := induced f M) f
    (inducedEval f).toLinearMap = counitEval (C := C) M ∘ₗ SMulMemClass.subtype (induced f M) :=
  rfl

/-- Evaluation at the identity applies the counit of `C` to the second factor. -/
@[simp]
theorem inducedEval_apply (t : induced f M) :
    letI := Corestrict (M := induced f M) f
    inducedEval f t =
      TensorProduct.rid R M ((Coalgebra.counit (R := R) (A := C)).lTensor M t) :=
  (rfl)

/-- The comodule morphism `N → M ⊗[R] C` attached to a morphism of `D`-comodules lands in the
induced comodule. -/
private theorem cofreeLift_mem_induced :
    letI := Corestrict (M := N) f
    ∀ (g : Hom R D N M) (n : N), Hom.cofreeLift (C := C) g.toLinearMap n ∈ induced f M := by
  let _ := Corestrict (M := N) f
  intro g n
  -- Both sides are cofree lifts, of `ρ ∘ g` and of `(id ⊗ f) ∘ (g ⊗ id) ∘ ρ_N`.
  rw [mem_induced_iff_cofreeLift, ← Hom.cofreeMap_apply, ← Hom.comp_apply, ← Hom.comp_apply,
    Hom.cofreeMap_comp_cofreeLift, Hom.cofreeLift_comp]
  congr 2
  -- `g` commutes with the corestricted coaction `(id ⊗ f) ∘ ρ_N`.
  rw [← g.map_coact_eq, corestrict_coact, corestrictCoact_eq_lTensor]
  simp only [Hom.cofreeLift_toLinearMap, ← rTensor_def, ← LinearMap.comp_assoc,
    LinearMap.rTensor_comp_lTensor, LinearMap.lTensor_comp_rTensor, CoalgHom.toLinearMap_eq_ofClass]

/-- The morphism into the induced comodule attached to a morphism of `D`-comodules
`g : N → M`, namely `(g ⊗ id) ∘ ρ_N`. This is the inverse direction of Frobenius reciprocity. -/
noncomputable def inducedLift (g : letI := Corestrict (M := N) f; Hom R D N M) :
    Hom R C N (induced f M) :=
  letI := Corestrict (M := N) f
  (Hom.cofreeLift (C := C) g.toLinearMap).codRestrict (induced f M) (cofreeLift_mem_induced f g)

/-- The lift of `g` sends `n` to `(g ⊗ id) (ρ_N n)`. -/
@[simp]
theorem coe_inducedLift_apply (g : letI := Corestrict (M := N) f; Hom R D N M) (n : N) :
    letI := Corestrict (M := N) f
    (inducedLift f g n : M ⊗[R] C) = g.toLinearMap.rTensor C (coact (R := R) (C := C) (M := N) n) :=
  by exact Hom.codRestrict_apply _ _ _ n

/-- **Frobenius reciprocity.** Morphisms of `C`-comodules from `N` into the induced comodule
`Ind_f M` are exactly morphisms of `D`-comodules from the corestriction of `N` to `M`. The
forward map composes with evaluation at the identity (`TauCeti.Comodule.inducedEval`), and the
inverse is `TauCeti.Comodule.inducedLift`. -/
noncomputable def inducedEquiv :
    Hom R C N (induced f M) ≃ₗ[R] (letI := Corestrict (M := N) f; Hom R D N M) :=
  letI := Corestrict (M := N) f
  letI := Corestrict (M := induced f M) f
  { toFun φ := Hom.comp (inducedEval f) (corestrictHom f φ)
    map_add' φ ψ := Hom.ext fun n ↦ by simp
    map_smul' r φ := Hom.ext fun n ↦ by simp
    invFun := inducedLift f
    left_inv φ := Hom.ext fun n ↦ Subtype.ext <| by
      rw [coe_inducedLift_apply, Hom.comp_toLinearMap, corestrictHom_toLinearMap,
        inducedEval_toLinearMap]
      have h := LinearMap.congr_fun (congrArg Hom.toLinearMap
        (Hom.cofreeLift_rid_comp_lTensor_counit_comp (Hom.comp (Subcomodule.subtype _) φ))) n
      rw [Hom.comp_toLinearMap, Subcomodule.subtype_toLinearMap, Hom.cofreeLift_toLinearMap] at h
      exact h
    right_inv g := Hom.ext fun n ↦ by
      rw [Hom.comp_apply, corestrictHom_apply, inducedEval_apply, coe_inducedLift_apply]
      exact LinearMap.congr_fun (Hom.rid_comp_lTensor_counit_comp_cofreeLift
        (C := C) g.toLinearMap) n }

/-- The forward map of Frobenius reciprocity composes with evaluation at the identity. -/
@[simp]
theorem inducedEquiv_apply (φ : Hom R C N (induced f M)) :
    letI := Corestrict (M := N) f
    letI := Corestrict (M := induced f M) f
    inducedEquiv f φ = Hom.comp (inducedEval f) (corestrictHom f φ) :=
  (rfl)

/-- The inverse map of Frobenius reciprocity is `TauCeti.Comodule.inducedLift`. -/
@[simp]
theorem inducedEquiv_symm_apply (g : letI := Corestrict (M := N) f; Hom R D N M) :
    (inducedEquiv f).symm g = inducedLift f g :=
  (rfl)

/-- **Naturality of Frobenius reciprocity in the source.** -/
theorem inducedEquiv_comp {P : Type*} [AddCommMonoid P] [Module R P] [Comodule R C P]
    (φ : Hom R C N (induced f M)) (g : Hom R C P N) :
    letI := Corestrict (M := N) f
    letI := Corestrict (M := P) f
    inducedEquiv f (Hom.comp φ g) = Hom.comp (inducedEquiv f φ) (corestrictHom f g) :=
  letI := Corestrict (M := N) f
  letI := Corestrict (M := P) f
  Hom.ext fun p ↦ by
    simp only [inducedEquiv_apply, Hom.comp_apply, corestrictHom_apply]

/-- **Functoriality of induction.** A morphism of `D`-comodules `h : M → M'` induces the morphism
`Ind_f M → Ind_f M'` corresponding to `h ∘ inducedEval` under Frobenius reciprocity. It acts as
`h ⊗ id` (`TauCeti.Comodule.coe_inducedMap_apply`). -/
noncomputable def inducedMap (h : Hom R D M M') : Hom R C (induced f M) (induced f M') :=
  letI := Corestrict (M := induced f M) f
  inducedLift f (Hom.comp h (inducedEval f))

/-- Induction acts on `M ⊗[R] C` as `h ⊗ id`. -/
@[simp]
theorem coe_inducedMap_apply (h : Hom R D M M') (t : induced f M) :
    (inducedMap f h t : M' ⊗[R] C) = h.toLinearMap.rTensor C t := by
  let _ := Corestrict (M := induced f M) f
  have hev : (counitEval (C := C) M).rTensor C (cofreeCoact R C M (t : M ⊗[R] C)) = t :=
    LinearMap.congr_fun
      (rTensor_rid_comp_lTensor_counit_comp_cofreeCoact (R := R) (C := C) (M := M)) _
  rw [inducedMap, coe_inducedLift_apply, Hom.comp_toLinearMap, LinearMap.rTensor_comp_apply,
    inducedEval_toLinearMap, LinearMap.rTensor_comp_apply, Subcomodule.subtype_rTensor_coact]
  exact congrArg (h.toLinearMap.rTensor C) hev

/-- Induction preserves identities. -/
-- Simplify before `ComoduleCat.ofHom_id` rewrites the identity in categorical form.
@[simp↓]
theorem inducedMap_id : inducedMap f (Hom.id R D M) = Hom.id R C (induced f M) :=
  Hom.ext fun t ↦ Subtype.ext <| by
    rw [coe_inducedMap_apply, Hom.id_toLinearMap, LinearMap.rTensor_id_apply, Hom.id_apply]

/-- Induction preserves composition. -/
@[simp]
theorem inducedMap_comp {M'' : Type*} [AddCommMonoid M''] [Module R M''] [Comodule R D M'']
    (h' : Hom R D M' M'') (h : Hom R D M M') :
    inducedMap f (Hom.comp h' h) = Hom.comp (inducedMap f h') (inducedMap f h) :=
  Hom.ext fun t ↦ Subtype.ext <| by simp [LinearMap.rTensor_comp]

/-- **Naturality of Frobenius reciprocity in the coefficient comodule.** -/
theorem inducedEquiv_inducedMap_comp (h : Hom R D M M') (φ : Hom R C N (induced f M)) :
    letI := Corestrict (M := N) f
    inducedEquiv f (Hom.comp (inducedMap f h) φ) = Hom.comp h (inducedEquiv f φ) := by
  let _ := Corestrict (M := N) f
  refine Hom.ext fun n ↦ ?_
  have key := LinearMap.congr_fun (rid_comp_lTensor_counit_comp_rTensor (C := C) h.toLinearMap)
    (φ n : M ⊗[R] C)
  simp only [LinearMap.comp_apply] at key
  simpa using key

end Comodule

end TauCeti
