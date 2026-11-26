/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Singular.LocalHomology.AddCircle
public import TauCeti.AlgebraicTopology.Singular.MappingTorus.Refl
public import TauCeti.AlgebraicTopology.Singular.MappingTorus.Section

/-!
# The Wang boundary of the torus swept by a loop of sections

Let `φ : F ≃ₜ F` be a homeomorphism with mapping torus `T_φ`, and let `s ↦ γ_s` be a loop of
sections of `T_φ → S¹`, parametrized by the circle `ℝ / ℤ`: a map `S : S¹ × S¹ → T_φ`,
`(s, t) ↦ γ_s(t)`, with `γ_s(t)` lying over `t`. In the coordinates `(t, s)`, with the circle
coordinate `t` of the sections first, the loop sweeps the torus `(t, s) ↦ γ_s(t)`, and its class
in `H₂(T_φ; ℤ)` is the push-forward of the class `[S¹] × [S¹]` of the positively oriented
parameter torus (`TauCeti.addCircleProdFundamentalClass`). This file computes the Wang connecting
morphism `∂ : H₂(T_φ; ℤ) ⟶ H₁(F; ℤ)` (`TauCeti.MappingTorus.wangδ`) on this class: it is, up to a
universal sign, the class of the loop `s ↦ g(s)` of the points where the sections cross the fibre
at height zero, `mk φ (g s) 0 = γ_s(0)`
(`TauCeti.MappingTorus.wangδ_singularHomologyMap_comp_prodSwap_of_section`):

`∂ [(t, s) ↦ γ_s(t)] = ε • g_*[S¹]`,  `ε = ±1`.

For a loop of `φ`-seamed paths, the paths `γ` with `γ 1 = φ (γ 0)`, the point `g(s)` is the start
point `γ_s(0)` of the path
(`TauCeti.SeamedPath.wangδ_singularHomologyMap_sectionFamily_comp_prodSwap`), so
`∂ [(t, s) ↦ γ_s(t)] = ε • [s ↦ γ_s(0)]`. This is the boundary formula of the classes swept by
loops of seamed paths in the Floer–Novikov theory of a symplectomorphism, where `ε • ∂` is the
mapping-torus boundary map.

The sign `ε` (`TauCeti.MappingTorus.torusWangSign`) is the winding number of the Wang boundary of
the parameter torus of the mapping torus of the identity of the circle, the universal case. The
monodromy `φ` enters only through the sections, so every loop of sections reduces to this case
(`TauCeti.MappingTorus.singularHomologyMap_comp_wangδ_of_section`). In the universal case the
Wang connecting morphism of the mapping torus of the identity is onto
(`TauCeti.MappingTorus.epi_wangδ_refl`), every class of `H₁(S¹; ℤ)` is a multiple of the circuit
class (`AddCircle.eq_firstHomologyAddEquiv_zsmul_fundamentalClass`), and every class of
`H₂(S¹ × S¹; ℤ)` is a multiple of the class of the parameter torus, which is a fundamental class
(`TauCeti.isFundamentalClass_addCircleProdFundamentalClass`,
`TauCeti.IsFundamentalClass.existsUnique_eq_smul`). So the circuit class is `c • ε` times itself
for some integer `c`, and `ε` is a unit (`TauCeti.MappingTorus.torusWangSign_eq_one_or_eq_neg_one`).
Which of the two values `ε` takes is not computed here.

## Main definitions

* `TauCeti.MappingTorus.torusWangSign`: the sign `ε` of the Wang boundary of the parameter torus.

## Main results

* `TauCeti.MappingTorus.torusWangSign_eq_one_or_eq_neg_one`: `ε = ±1`.
* `TauCeti.MappingTorus.wangδ_singularHomologyMap_comp_prodSwap_of_section`: the Wang boundary of
  the torus swept by a loop of sections is `ε` times the class of its loop of points at height
  zero.
* `TauCeti.SeamedPath.wangδ_singularHomologyMap_sectionFamily_comp_prodSwap`: the Wang boundary of
  the torus swept by a loop of seamed paths is `ε` times the class of the loop of their start
  points.

## References

* A. Hatcher, *Algebraic Topology*, Section 2.2, Example 2.48, for the Wang sequence of a mapping
  torus.
* Y.-J. Lee, *Reidemeister torsion in Floer–Novikov theory and counting pseudo-holomorphic tori,
  I*, arXiv:math/0111313, Section 3.1, for the classes swept by loops of sections of a mapping
  torus and their boundary.
-/

public section

noncomputable section

open CategoryTheory Module

namespace TauCeti

namespace MappingTorus

/-- The parameter torus `(t, s)` of a loop of sections of the mapping torus of the identity of the
circle, read on that mapping torus: `(t, s) ↦ [s, t]`, the point `s` of the fibre at height `t`. -/
private def paramTorus :
    UnitAddCircle × UnitAddCircle ≃ₜ MappingTorus (Homeomorph.refl UnitAddCircle) :=
  (Homeomorph.prodComm UnitAddCircle UnitAddCircle).trans reflHomeomorph.symm

/-- **The sign of the Wang boundary of the parameter torus**: the winding number of the Wang
boundary `∂ [(t, s) ↦ [s, t]] ∈ H₁(S¹; ℤ)` of the class of the parameter torus `(t, s) ↦ [s, t]`
of the mapping torus of the identity of the circle `ℝ / ℤ`. It is `1` or `-1`
(`TauCeti.MappingTorus.torusWangSign_eq_one_or_eq_neg_one`). -/
def torusWangSign : ℤ :=
  AddCircle.firstHomologyAddEquiv 1
    ((wangδ (Homeomorph.refl UnitAddCircle) (ModuleCat.of ℤ ℤ) 1).hom
      (ContinuousMap.singularHomologyMap ℤ 2 (paramTorus : C(_, _))
        (addCircleProdFundamentalClass 1 1)))

/-- **The Wang boundary of the parameter torus.** In the mapping torus of the identity of the
circle, the Wang boundary of the class of the parameter torus `(t, s) ↦ [s, t]` is
`torusWangSign` times the circuit class of the fibre. -/
private theorem wangδ_paramTorus :
    (wangδ (Homeomorph.refl UnitAddCircle) (ModuleCat.of ℤ ℤ) 1).hom
        (ContinuousMap.singularHomologyMap ℤ 2 (paramTorus : C(_, _))
          (addCircleProdFundamentalClass 1 1)) =
      torusWangSign • AddCircle.fundamentalClass 1 :=
  AddCircle.eq_firstHomologyAddEquiv_zsmul_fundamentalClass 1 _

/-- **The sign of the Wang boundary of the parameter torus is a unit**: `torusWangSign` is `1` or
`-1`. -/
theorem torusWangSign_eq_one_or_eq_neg_one : torusWangSign = 1 ∨ torusWangSign = -1 := by
  -- The Wang boundary of the mapping torus of the identity is onto, so the circuit class of the
  -- fibre is the Wang boundary of a class of the torus. That class is a multiple of the class of
  -- the parameter torus, a fundamental class, so `H₂(S¹ × S¹; ℤ) ≃ ℤ` by an equivalence `e`
  -- sending it to a unit. The singular homology of the torus is by definition the homology of its
  -- singular simplicial set, in which `e` is stated.
  let : ChartedSpace (ℝ × ℝ) (UnitAddCircle × UnitAddCircle) :=
    prodChartedSpace ℝ UnitAddCircle ℝ UnitAddCircle
  obtain ⟨e, he⟩ : ∃ e : ((singularChains ℤ).obj
      (TopCat.of (UnitAddCircle × UnitAddCircle))).homology 2 ≃ₗ[ℤ] ℤ,
      IsUnit (e (addCircleProdFundamentalClass 1 1)) :=
    (isFundamentalClass_addCircleProdFundamentalClass 1 1).exists_linearEquiv_isUnit
      (E := ℝ × ℝ) (by simp) (LinearEquiv.refl ℤ ℤ)
  -- Read through `e`, the winding number of the Wang boundary is an additive map `Φ : ℤ → ℤ`.
  let Φ : ℤ →+ ℤ := (AddCircle.firstHomologyAddEquiv 1).toAddMonoidHom.comp
    ((wangδ (Homeomorph.refl UnitAddCircle) (ModuleCat.of ℤ ℤ) 1).hom.toAddMonoidHom.comp
      ((ContinuousMap.singularHomologyMap ℤ 2 (paramTorus : C(_, _))).toAddMonoidHom.comp
        e.symm.toLinearMap.toAddMonoidHom))
  have hΦ (n : ℤ) : Φ n = n * Φ 1 := by rw [AddMonoidHom.apply_int, smul_eq_mul]
  have hΦapp (z : ℤ) : Φ z = AddCircle.firstHomologyAddEquiv 1
      ((wangδ (Homeomorph.refl UnitAddCircle) (ModuleCat.of ℤ ℤ) 1).hom
        (ContinuousMap.singularHomologyMap ℤ 2 (paramTorus : C(_, _)) (e.symm z))) :=
    (rfl)
  -- `Φ` is onto: the Wang boundary of the mapping torus of the identity is onto.
  have hΦ1 : IsUnit (Φ 1) := by
    obtain ⟨x, hx⟩ := (ModuleCat.epi_iff_surjective
      (wangδ (Homeomorph.refl UnitAddCircle) (ModuleCat.of ℤ ℤ) 1)).1 inferInstance
      ((AddCircle.firstHomologyAddEquiv 1).symm 1)
    have hid : (paramTorus : C(UnitAddCircle × UnitAddCircle, _)).comp
        (paramTorus.symm : C(MappingTorus (Homeomorph.refl UnitAddCircle), _)) =
          ContinuousMap.id _ :=
      ContinuousMap.ext fun y ↦ paramTorus.apply_symm_apply y
    have hn :
        Φ (e (ContinuousMap.singularHomologyMap ℤ 2 (paramTorus.symm : C(_, _)) x)) = 1 := by
      rw [hΦapp, e.symm_apply_apply, ← ContinuousMap.singularHomologyMap_comp, hid,
        ContinuousMap.singularHomologyMap_id]
      exact (congrArg (AddCircle.firstHomologyAddEquiv 1) hx).trans
        ((AddCircle.firstHomologyAddEquiv 1).apply_symm_apply 1)
    rw [hΦ] at hn
    exact IsUnit.of_mul_eq_one_right _ hn
  -- The sign is `Φ` at the unit `e [S¹ × S¹]`.
  have hε : torusWangSign = e (addCircleProdFundamentalClass 1 1) * Φ 1 := by
    rw [← hΦ, hΦapp, e.symm_apply_apply, torusWangSign]
  exact Int.isUnit_iff.1 (hε ▸ he.mul hΦ1)

/-- The square of `torusWangSign` is `1`. -/
@[simp]
theorem torusWangSign_mul_self : torusWangSign * torusWangSign = 1 := by
  rcases torusWangSign_eq_one_or_eq_neg_one with h | h <;> simp [h]

variable {F : Type} [TopologicalSpace F] (φ : F ≃ₜ F)

/-- **The Wang boundary of the torus swept by a loop of sections.** Let `S : S¹ × S¹ → T_φ`,
`(s, t) ↦ γ_s(t)`, be a loop of sections of the mapping torus, `γ_s(t)` lying over `t`, and let
`g : S¹ → F` be its loop of fibre coordinates at height zero, `mk φ (g s) 0 = γ_s(0)`. The Wang
boundary of the class of the swept torus `(t, s) ↦ γ_s(t)`, the push-forward of the class
`[S¹] × [S¹]` of the parameter torus `(t, s)`, is `torusWangSign` times the class of the loop `g`:

`∂ [(t, s) ↦ γ_s(t)] = ε • g_*[S¹]`. -/
theorem wangδ_singularHomologyMap_comp_prodSwap_of_section
    (S : C(UnitAddCircle × UnitAddCircle, MappingTorus φ)) (hS : ∀ s t, proj φ (S (s, t)) = t)
    (g : C(UnitAddCircle, F)) (hg : ∀ s, mk φ (g s) 0 = S (s, 0)) :
    (wangδ φ (ModuleCat.of ℤ ℤ) 1).hom
        (ContinuousMap.singularHomologyMap ℤ 2 (S.comp ContinuousMap.prodSwap)
          (addCircleProdFundamentalClass 1 1)) =
      torusWangSign • ContinuousMap.singularHomologyMap ℤ 1 g (AddCircle.fundamentalClass 1) := by
  -- The swept torus factors through the parameter torus of the mapping torus of the identity.
  have hfac : S.comp ContinuousMap.prodSwap =
      (S.comp (reflHomeomorph (F := UnitAddCircle) :
        C(MappingTorus (Homeomorph.refl UnitAddCircle), UnitAddCircle × UnitAddCircle))).comp
        (paramTorus : C(_, _)) :=
    ContinuousMap.ext fun p ↦ by simp [paramTorus, Prod.swap]
  have h := LinearMap.congr_fun (congrArg ModuleCat.Hom.hom
    (singularHomologyMap_comp_wangδ_of_section φ (ModuleCat.of ℤ ℤ) S hS g hg 1))
    (ContinuousMap.singularHomologyMap ℤ 2 (paramTorus : C(_, _))
      (addCircleProdFundamentalClass 1 1))
  -- The two sides of `h` are the two sides of the claim, written through the induced maps.
  have h' : (wangδ φ (ModuleCat.of ℤ ℤ) 1).hom
      (ContinuousMap.singularHomologyMap ℤ 2 (S.comp ContinuousMap.prodSwap)
        (addCircleProdFundamentalClass 1 1)) =
      ContinuousMap.singularHomologyMap ℤ 1 g
        ((wangδ (Homeomorph.refl UnitAddCircle) (ModuleCat.of ℤ ℤ) 1).hom
          (ContinuousMap.singularHomologyMap ℤ 2 (paramTorus : C(_, _))
            (addCircleProdFundamentalClass 1 1))) := by
    rw [hfac, ContinuousMap.singularHomologyMap_comp]
    exact h
  rw [h', wangδ_paramTorus, map_zsmul]

end MappingTorus

namespace SeamedPath

open MappingTorus

variable {F : Type} [TopologicalSpace F] (φ : F ≃ₜ F)

/-- **The Wang boundary of the torus swept by a loop of seamed paths.** For a loop `s ↦ γ_s` of
`φ`-seamed paths, parametrized by the circle, the Wang boundary of the class of the swept torus
`(t, s) ↦ mk φ (γ_s(t)) t`, the push-forward of the class of the parameter torus `(t, s)` along the
family of sections, is `torusWangSign` times the class of the loop `g : s ↦ γ_s(0)` of start
points:

`∂ [(t, s) ↦ γ_s(t)] = ε • [s ↦ γ_s(0)]`. -/
theorem wangδ_singularHomologyMap_sectionFamily_comp_prodSwap
    (ℓ : C(UnitAddCircle, SeamedPath φ)) (g : C(UnitAddCircle, F)) (hg : ∀ s, (ℓ s).val 0 = g s) :
    (wangδ φ (ModuleCat.of ℤ ℤ) 1).hom
        (ContinuousMap.singularHomologyMap ℤ 2 ((sectionFamily φ ℓ).comp ContinuousMap.prodSwap)
          (addCircleProdFundamentalClass 1 1)) =
      torusWangSign • ContinuousMap.singularHomologyMap ℤ 1 g (AddCircle.fundamentalClass 1) :=
  wangδ_singularHomologyMap_comp_prodSwap_of_section φ _ (fun _ _ ↦ by simp) g
    (fun s ↦ by rw [sectionFamily_zero, hg])

/-- **The mapping-torus boundary of the torus swept by a loop of seamed paths** is the class of the
loop of start points: with the sign `ε = torusWangSign` of the Wang boundary of the parameter torus,
`ε • ∂ [(t, s) ↦ γ_s(t)] = [s ↦ γ_s(0)]`. -/
theorem torusWangSign_smul_wangδ_singularHomologyMap_sectionFamily_comp_prodSwap
    (ℓ : C(UnitAddCircle, SeamedPath φ)) (g : C(UnitAddCircle, F)) (hg : ∀ s, (ℓ s).val 0 = g s) :
    torusWangSign • (wangδ φ (ModuleCat.of ℤ ℤ) 1).hom
        (ContinuousMap.singularHomologyMap ℤ 2 ((sectionFamily φ ℓ).comp ContinuousMap.prodSwap)
          (addCircleProdFundamentalClass 1 1)) =
      ContinuousMap.singularHomologyMap ℤ 1 g (AddCircle.fundamentalClass 1) := by
  rw [wangδ_singularHomologyMap_sectionFamily_comp_prodSwap φ ℓ g hg, smul_smul,
    torusWangSign_mul_self, one_smul]

end SeamedPath

end TauCeti
