/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Homotopy.LoopSpace.ParameterTorus
public import TauCeti.AlgebraicTopology.Singular.MappingTorus.SweptTorus

/-!
# Torus classes of loops of seamed paths

Let `φ : F ≃ₜ F` be a homeomorphism with mapping torus `Y_φ`. A `φ`-seamed path `γ`, a path with
`γ 1 = φ (γ 0)`, is a section of the projection `Y_φ → S¹`
(`TauCeti.SeamedPath.sectionHomeomorph`), and so a free loop of `Y_φ`
(`TauCeti.SeamedPath.sectionLoop`). A loop `s ↦ γ_s` of seamed paths therefore sweeps out the torus
`(t, s) ↦ mk φ (γ_s t) t` in the mapping torus. This is a torus in `Y_φ`, not in general the image
of a torus or of a sphere in `F`.

The **torus class** of a loop of seamed paths (`TauCeti.SeamedPath.torusClassHom`) is the class of
this torus in `H₂(Y_φ; ℤ)`: the torus class `TauCeti.freeLoopTorusClassHom` of the loop of free
loops `s ↦ sectionLoop φ γ_s`. It is a homomorphism on the fundamental group of the space of
seamed paths. In the Floer theory of a symplectomorphism `φ`, whose configuration space is the
space of `φ`-seamed paths, the symplectic area and the first Chern number are evaluated on these
classes; they play the role that the classes of spheres play for the contractible free loops of
Hamiltonian Floer theory.

The torus class is defined through cubical chains. It is the push-forward of the class
`[S¹] × [S¹]` of the parameter torus (`TauCeti.addCircleProdFundamentalClass 1 1`) along the swept
torus `(t, s) ↦ mk φ (γ_s t) t` of any circle `s ↦ γ_s` of seamed paths tracing the loop, with no
sign (`TauCeti.SeamedPath.torusClassHom_ofMul_mk_eq_singularHomologyMap`), by the corresponding
statement for loops of free loops
(`TauCeti.freeLoopTorusClassHom_ofMul_mk_eq_singularHomologyMap`). Every loop is traced by such a
circle, so the group of torus classes at `γ` consists of the classes of the tori swept out by
circles of seamed paths through `γ`
(`TauCeti.SeamedPath.exists_torusClassHom_eq_singularHomologyMap`).
With the Wang boundary of swept tori
(`TauCeti.SeamedPath.torusWangSign_smul_wangδ_singularHomologyMap_sectionFamily_comp_prodSwap`),
the mapping-torus boundary of the torus class of a loop is the class of its loop of start points:
`ε • ∂ [(t, s) ↦ mk φ (γ_s t) t] = [s ↦ γ_s(0)]`
(`TauCeti.SeamedPath.torusWangSign_smul_wangδ_torusClassHom_ofMul_mk`).

## Main definitions

* `TauCeti.SeamedPath.torusClassHom φ γ`: the torus class `π₁(SeamedPath φ, γ) → H₂(Y_φ; ℤ)` of
  loops of `φ`-seamed paths.

## Main results

* `TauCeti.SeamedPath.torusClassHom_ofMul_mk_eq_singularHomologyMap`: the torus class of a loop of
  seamed paths is the push-forward of the class of the parameter torus along the torus it sweeps
  out.
* `TauCeti.SeamedPath.exists_torusClassHom_eq_singularHomologyMap`: every torus class is the class
  of a torus swept out by a circle of seamed paths.
* `TauCeti.SeamedPath.torusWangSign_smul_wangδ_torusClassHom_ofMul_mk`: the mapping-torus boundary
  of the torus class of a loop of seamed paths is the class of its loop of start points.

## References

* A. Floer, *Symplectic fixed points and holomorphic spheres*, Comm. Math. Phys. 120 (1989),
  575–611.
* S. Dostoglou and D. A. Salamon, *Self-dual instantons and holomorphic curves*, Ann. of Math. 139
  (1994), 581–640.
-/

public section

noncomputable section

open CategoryTheory AlgebraicTopology
open scoped Topology.Homotopy

namespace TauCeti.SeamedPath

variable {F : Type} [TopologicalSpace F] (φ : F ≃ₜ F)

/-- **The torus class of a loop of seamed paths**: the homomorphism
`π₁(SeamedPath φ, γ) → H₂(Y_φ; ℤ)` sending a loop `s ↦ γ_s` of `φ`-seamed paths at `γ` to the class
of the torus `(t, s) ↦ mk φ (γ_s t) t` that it sweeps out in the mapping torus. It is the torus
class `TauCeti.freeLoopTorusClassHom` of the loop of free loops `s ↦ sectionLoop φ γ_s`. -/
def torusClassHom (γ : SeamedPath φ) :
    Additive (HomotopyGroup (Fin 1) (SeamedPath φ) γ) →+
      ((singularHomologyFunctor (ModuleCat.{0} ℤ) 2).obj (ModuleCat.of ℤ ℤ)).obj
        (TopCat.of (MappingTorus φ)) :=
  (freeLoopTorusClassHom (MappingTorus φ) (sectionLoop φ γ)).comp
    (HomotopyGroup.mapHom (sectionLoop φ) rfl).toAdditive

/-- The torus class of a loop of seamed paths is the torus class of its loop of free loops of the
mapping torus. -/
theorem torusClassHom_apply (γ : SeamedPath φ)
    (a : Additive (HomotopyGroup (Fin 1) (SeamedPath φ) γ)) :
    torusClassHom φ γ a =
      freeLoopTorusClassHom (MappingTorus φ) (sectionLoop φ γ)
        (Additive.ofMul (HomotopyGroup.map (sectionLoop φ) rfl a.toMul)) :=
  (rfl)

/-- The free loop of the section of a seamed path sweeps the section: the torus swept out by the
circle of free loops `s ↦ sectionLoop φ (ℓ s)` is the family of sections of `ℓ`, read with the
circle coordinate `t` of the sections first. -/
theorem freeLoopTorusMap_sectionLoop_comp (ℓ : C(UnitAddCircle, SeamedPath φ)) :
    freeLoopTorusMap ((sectionLoop φ).comp ℓ) =
      (sectionFamily φ ℓ).comp ContinuousMap.prodSwap := by
  ext ⟨t, s⟩
  simp [sectionLoop_apply]

/-- **The torus class of a loop of seamed paths is the class of the torus it sweeps out.** Let `p`
be a loop of `φ`-seamed paths at `γ`, and let `ℓ : S¹ → SeamedPath φ` be the same loop
parametrized by the circle, `ℓ [t] = p t`. Then the torus class of `p` is the push-forward of the
class `[S¹] × [S¹]` of the parameter torus `(t, s)` along the swept torus
`(t, s) ↦ mk φ (ℓ s t) t`. -/
theorem torusClassHom_ofMul_mk_eq_singularHomologyMap {γ : SeamedPath φ}
    (p : Ω^ (Fin 1) (SeamedPath φ) γ) (ℓ : C(UnitAddCircle, SeamedPath φ))
    (hℓ : ∀ t : unitInterval, ℓ (t : ℝ) = p (fun _ ↦ t)) :
    torusClassHom φ γ (Additive.ofMul ⟦p⟧) =
      ContinuousMap.singularHomologyMap ℤ 2 ((sectionFamily φ ℓ).comp ContinuousMap.prodSwap)
        (addCircleProdFundamentalClass 1 1) := by
  rw [torusClassHom_apply, ← freeLoopTorusMap_sectionLoop_comp]
  -- The image of the class of `p` in the free loops of the mapping torus is the class of the image
  -- of `p` (`HomotopyGroup.map_mk`, by definition).
  exact freeLoopTorusClassHom_ofMul_mk_eq_singularHomologyMap (GenLoop.map (sectionLoop φ) rfl p)
    ((sectionLoop φ).comp ℓ) fun t ↦ by rw [ContinuousMap.comp_apply, hℓ, GenLoop.map_apply]

/-- **Every torus class of seamed paths is swept out by a circle of seamed paths.** Every element
of `π₁(SeamedPath φ, γ)` has the torus class of the torus `(t, s) ↦ mk φ (ℓ s t) t` swept out by
some circle `ℓ` of seamed paths through `ℓ [0] = γ`. -/
theorem exists_torusClassHom_eq_singularHomologyMap {γ : SeamedPath φ}
    (a : Additive (HomotopyGroup (Fin 1) (SeamedPath φ) γ)) :
    ∃ ℓ : C(UnitAddCircle, SeamedPath φ), ℓ ((0 : ℝ) : UnitAddCircle) = γ ∧
      torusClassHom φ γ a =
        ContinuousMap.singularHomologyMap ℤ 2 ((sectionFamily φ ℓ).comp ContinuousMap.prodSwap)
          (addCircleProdFundamentalClass 1 1) := by
  induction a using Additive.rec with | ofMul a =>
  induction a using Quotient.inductionOn with | h p =>
  obtain ⟨ℓ, hℓ⟩ := GenLoop.exists_unitAddCircle_apply_eq p
  exact ⟨ℓ, (hℓ 0).trans (GenLoop.boundary p _ ⟨0, Or.inl rfl⟩),
    torusClassHom_ofMul_mk_eq_singularHomologyMap φ p ℓ hℓ⟩

/-- **The mapping-torus boundary of the torus class of a loop of seamed paths** is the class of its
loop of start points. For a loop `p` of `φ`-seamed paths at `γ`, parametrized by the circle as
`ℓ`, and the loop `g : s ↦ (ℓ s)(0)` of start points, with the sign `ε = torusWangSign` of the Wang
boundary of the parameter torus, `ε • ∂ (torusClassHom φ γ [p]) = g_*[S¹]`. -/
theorem torusWangSign_smul_wangδ_torusClassHom_ofMul_mk {γ : SeamedPath φ}
    (p : Ω^ (Fin 1) (SeamedPath φ) γ) (ℓ : C(UnitAddCircle, SeamedPath φ))
    (hℓ : ∀ t : unitInterval, ℓ (t : ℝ) = p (fun _ ↦ t)) (g : C(UnitAddCircle, F))
    (hg : ∀ s, (ℓ s).val 0 = g s) :
    MappingTorus.torusWangSign • (MappingTorus.wangδ φ (ModuleCat.of ℤ ℤ) 1).hom
        (torusClassHom φ γ (Additive.ofMul ⟦p⟧)) =
      ContinuousMap.singularHomologyMap ℤ 1 g (AddCircle.fundamentalClass 1) := by
  rw [torusClassHom_ofMul_mk_eq_singularHomologyMap φ p ℓ hℓ]
  exact torusWangSign_smul_wangδ_singularHomologyMap_sectionFamily_comp_prodSwap φ ℓ g hg

end TauCeti.SeamedPath
