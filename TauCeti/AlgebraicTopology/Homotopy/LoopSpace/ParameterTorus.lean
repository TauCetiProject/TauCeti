/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Homotopy.Hurewicz.One.Cubical
public import TauCeti.AlgebraicTopology.Homotopy.LoopSpace.TorusClass
public import TauCeti.AlgebraicTopology.Singular.AddCircle
public import TauCeti.AlgebraicTopology.Singular.Cubical.Kunneth
public import TauCeti.Topology.MappingSpace.FreeLoop

/-!
# Torus classes of loops of free loops are push-forwards of the parameter torus

A loop of free loops of a space `Q`, parametrized by the circle `ℝ / ℤ`, is a map
`ℓ : S¹ → 𝓛Q = C(S¹, Q)`. It sweeps out the torus

`(t, s) ↦ ℓ s (exp (2πit))`,  `S¹ × S¹ → Q`

(`TauCeti.freeLoopTorusMap ℓ`), with the circle coordinate `t` of the free loops first and the loop
parameter `s` second. This file proves that the torus class of the loop
(`TauCeti.freeLoopTorusClassHom`, defined through normalized cubical chains and the
cubical–simplicial comparison) is the push-forward of the class `[S¹] × [S¹]` of the parameter
torus (`TauCeti.addCircleProdFundamentalClass 1 1`) along the swept torus, with no sign
(`TauCeti.freeLoopTorusClassHom_ofMul_mk_eq_singularHomologyMap`). Every element of
`π₁(𝓛Q, γ)` is represented by such a loop, so every torus class at `γ` is the class of a swept
parameter torus (`TauCeti.exists_freeLoopTorusClassHom_eq_singularHomologyMap`).

The proof reduces to the universal loop of free loops of the torus `S¹ × S¹`,
`s ↦ (t ↦ (t, s))`, whose swept torus is the identity, through the naturality of the torus class
(`TauCeti.cubicalFreeLoopTorusClassHom_map`). For the universal loop the swept cube
`I² → S¹ × S¹` is the cubical cross product of the circuit `1`-cube of `S¹` with itself, so its
cubical class is the cubical cross product of the cubical classes of the circuit
(`TauCeti.homologyMap_cubicalCrossProduct_homologyCross_homologyπ`). The comparison carries the
cubical cross product to the singular one
(`TauCeti.singularCubicalHomologyIso_inv_homologyMap_cubicalCrossProduct_homologyCross`) and the
cubical class of the circuit to minus the circuit class `AddCircle.fundamentalClass 1`
(`GenLoop.singularCubicalHomologyIso_inv_cubicalHurewicz`,
`GenLoop.hurewicz_hom_one_eq_neg_loopClass`). The two signs cancel.

## Main definitions

* `TauCeti.freeLoopTorusMap ℓ`: the torus `(t, s) ↦ ℓ s (exp (2πit))` swept out by a circle `ℓ` of
  free loops.

## Main results

* `TauCeti.freeLoopTorusClassHom_ofMul_mk_eq_singularHomologyMap`: the torus class of a loop of
  free loops, parametrized by a circle `ℓ` of free loops, is the push-forward of the class of the
  parameter torus along the swept torus.
* `TauCeti.exists_freeLoopTorusClassHom_eq_singularHomologyMap`: every torus class is the class of
  the torus swept out by a circle of free loops.

## References

* Y.-J. Lee, *Reidemeister torsion in Floer–Novikov theory and counting pseudo-holomorphic tori,
  I*, arXiv:math/0111313, Section 3.1, for the classes of the tori swept by loops of sections.
* W. S. Massey, *Singular Homology Theory*, GTM 70, Springer, 1980, Chapters II and VII, for the
  cubical cross product and the comparison of cubical and simplicial chains.
-/

public section

noncomputable section

open AlgebraicTopology CategoryTheory MonoidalCategory
open scoped unitInterval Topology.Homotopy TensorProduct

namespace TauCeti

variable {Q : Type} [TopologicalSpace Q]

/-- The **torus swept out by a circle of free loops** `ℓ : S¹ → 𝓛Q`: the map
`(t, s) ↦ ℓ s (exp (2πit))` from `ℝ / ℤ × ℝ / ℤ`, with the circle coordinate `t` of the free loops
first and the parameter `s` of the circle of free loops second. -/
def freeLoopTorusMap (ℓ : C(UnitAddCircle, C(Circle, Q))) : C(UnitAddCircle × UnitAddCircle, Q) :=
  (freeLoopEval Q).comp
    ((AddCircle.homeomorphCircle one_ne_zero : C(UnitAddCircle, Circle)).prodMap ℓ)

@[simp]
theorem freeLoopTorusMap_apply (ℓ : C(UnitAddCircle, C(Circle, Q))) (t s : UnitAddCircle) :
    freeLoopTorusMap ℓ (t, s) = ℓ s (AddCircle.homeomorphCircle one_ne_zero t) := by
  simp [freeLoopTorusMap]

/-- The universal circle of free loops of the torus `ℝ / ℤ × ℝ / ℤ`: at the parameter `s`, the
free loop `exp (2πit) ↦ (t, s)`. The torus it sweeps out is the identity. -/
private def universalFreeLoop : C(UnitAddCircle, C(Circle, UnitAddCircle × UnitAddCircle)) :=
  ContinuousMap.curry ⟨fun x : UnitAddCircle × Circle ↦
    ((AddCircle.homeomorphCircle one_ne_zero).symm x.2, x.1), by fun_prop⟩

/-- The universal circle of free loops at `s` sends `exp (2πit)` to `(t, s)`. -/
private theorem universalFreeLoop_apply (s : UnitAddCircle) (w : Circle) :
    universalFreeLoop s w = ((AddCircle.homeomorphCircle one_ne_zero).symm w, s) :=
  ContinuousMap.curry_apply _ s w

/-- **The torus class of the universal loop of free loops is the class of the parameter torus.**
The torus swept out by the universal loop is the cubical cross product of the circuit `1`-cube with
itself, and the comparison carries the class of the circuit `1`-cube to minus the circuit class:
the two signs cancel. -/
private theorem freeLoopTorusClassHom_universalFreeLoop :
    freeLoopTorusClassHom (UnitAddCircle × UnitAddCircle)
        (universalFreeLoop ((0 : ℝ) : UnitAddCircle))
        (Additive.ofMul ⟦(genLoopEquivOfUnique (Fin 1)).symm
          ((AddCircle.zsmulLoop 1 0 1).map universalFreeLoop.continuous)⟧) =
      addCircleProdFundamentalClass 1 1 := by
  set P := (genLoopEquivOfUnique (Fin 1)).symm
    ((AddCircle.zsmulLoop 1 0 1).map universalFreeLoop.continuous)
  -- The circuit `t ↦ [t]` of `ℝ / ℤ`, as a generalized loop.
  set c : Ω^ (Fin 1) UnitAddCircle ((0 : ℝ) : UnitAddCircle) :=
    (genLoopEquivOfUnique (Fin 1)).symm (AddCircle.zsmulLoop 1 0 1) with hc_def
  -- The values of the circuit are the classes `[t]`.
  have hz (t : I) : AddCircle.zsmulLoop 1 0 1 t = ((t : ℝ) : UnitAddCircle) := by
    rw [AddCircle.zsmulLoop_zero_apply_eq_coe, Int.cast_one, one_mul, one_mul]
  have hcube : freeLoopTorusCube (P : SingularCube C(Circle, UnitAddCircle × UnitAddCircle) 1) =
      SingularCube.crossProduct (c : SingularCube UnitAddCircle 1) (c : SingularCube _ 1) := by
    ext z <;>
      rw [freeLoopTorusCube_apply, SingularCube.crossProduct_apply] <;>
      simp [GenLoop.coe_coe, P, hc_def, GenLoop.genLoopEquivOfUnique_symm_apply, Path.map_coe,
        universalFreeLoop_apply, homeomorphCircle_symm_unitToCircle, hz]
  obtain ⟨w, hw⟩ := exists_iCycles_eq_ofCube_freeLoopTorusCube ℤ P
  rw [freeLoopTorusClassHom_apply, cubicalFreeLoopTorusClassHom_mk ℤ P hw]
  rw [hcube] at hw
  have hcross := homologyMap_cubicalCrossProduct_homologyCross_homologyπ ℤ
    (X := TopCat.of UnitAddCircle) (Y := TopCat.of UnitAddCircle)
    (GenLoop.cubicalCycle ℤ c) (GenLoop.iCycles_cubicalCycle ℤ c)
    (GenLoop.cubicalCycle ℤ c) (GenLoop.iCycles_cubicalCycle ℤ c) w hw
  -- The torus `ℝ / ℤ × ℝ / ℤ` is the product `TopCat.of (ℝ / ℤ) ⊗ TopCat.of (ℝ / ℤ)` only up to
  -- unfolding the cartesian monoidal structure of `TopCat`.
  erw [← hcross]
  refine (singularCubicalHomologyIso_inv_homologyMap_cubicalCrossProduct_homologyCross ℤ
    (TopCat.of UnitAddCircle) (TopCat.of UnitAddCircle) _ _ _ _ _ _).trans ?_
  have hc : (singularCubicalHomologyIso ℤ (TopCat.of UnitAddCircle) 1).inv
      (((normalizedCubicalChainComplex ℤ).obj (TopCat.of UnitAddCircle)).homologyπ 1
        (GenLoop.cubicalCycle ℤ c)) = -AddCircle.fundamentalClass 1 := by
    rw [GenLoop.homologyπ_eq_cubicalHurewicz ℤ c (GenLoop.iCycles_cubicalCycle ℤ c),
      GenLoop.singularCubicalHomologyIso_inv_cubicalHurewicz,
      GenLoop.hurewicz_hom_one_eq_neg_loopClass, Equiv.apply_symm_apply,
      AddCircle.fundamentalClass_def]
  -- The degree `0 + 1` of the cubical cycle of a generalized loop is the degree `1` of `hc`.
  erw [hc]
  simp only [map_neg, LinearMap.neg_apply, neg_neg]
  exact (addCircleProdFundamentalClass_def 1 1).symm

/-- **The torus class of a loop of free loops is the push-forward of the parameter torus.** Let `p`
be a loop of free loops of `Q` at `γ`, and let `ℓ : S¹ → 𝓛Q` be the same loop parametrized by the
circle, `ℓ [t] = p t`. Then the torus class of `p` is the push-forward of the class
`[S¹] × [S¹]` of the parameter torus along the swept torus `(t, s) ↦ ℓ s (exp (2πit))`. -/
theorem freeLoopTorusClassHom_ofMul_mk_eq_singularHomologyMap {γ : C(Circle, Q)}
    (p : Ω^ (Fin 1) C(Circle, Q) γ) (ℓ : C(UnitAddCircle, C(Circle, Q)))
    (hℓ : ∀ t : I, ℓ (t : ℝ) = p (fun _ ↦ t)) :
    freeLoopTorusClassHom Q γ (Additive.ofMul ⟦p⟧) =
      ContinuousMap.singularHomologyMap ℤ 2 (freeLoopTorusMap ℓ)
        (addCircleProdFundamentalClass 1 1) := by
  set S := freeLoopTorusMap ℓ
  -- The swept torus `S` carries the universal loop of free loops to `ℓ`.
  have hS (s : UnitAddCircle) : S.comp (universalFreeLoop s) = ℓ s := by
    ext z
    simp [S, universalFreeLoop]
  have hγ : S.comp (universalFreeLoop ((0 : ℝ) : UnitAddCircle)) = γ := by
    rw [hS]
    exact (hℓ 0).trans (GenLoop.boundary p _ ⟨0, Or.inl rfl⟩)
  have key := cubicalFreeLoopTorusClassHom_map ℤ S hγ
    (⟦(genLoopEquivOfUnique (Fin 1)).symm
      ((AddCircle.zsmulLoop 1 0 1).map universalFreeLoop.continuous)⟧)
  rw [HomotopyGroup.map_mk] at key
  have hP : GenLoop.map ⟨fun g ↦ S.comp g, ContinuousMap.continuous_postcomp S⟩ hγ
      ((genLoopEquivOfUnique (Fin 1)).symm
        ((AddCircle.zsmulLoop 1 0 1).map universalFreeLoop.continuous)) = p := by
    ext x z
    rw [GenLoop.map_apply, GenLoop.genLoopEquivOfUnique_symm_apply, Path.map_coe,
      Function.comp_apply]
    refine (DFunLike.congr_fun (hS _) z).trans ?_
    rw [AddCircle.zsmulLoop_zero_apply_eq_coe, Int.cast_one, one_mul, one_mul, hℓ]
    exact congrArg (fun y ↦ p y z) (funext fun i ↦ by rw [Subsingleton.elim i default])
  rw [hP] at key
  rw [freeLoopTorusClassHom_apply, key, ← freeLoopTorusClassHom_universalFreeLoop,
    freeLoopTorusClassHom_apply]
  -- The naturality of the comparison isomorphism `singularCubicalHomologyNatIso`, along `S`.
  generalize cubicalFreeLoopTorusClassHom (UnitAddCircle × UnitAddCircle) ℤ _ _ = a
  have h := ConcreteCategory.congr_hom
    ((singularCubicalHomologyNatIso ℤ 2).inv.naturality (TopCat.ofHom S)) a
  simp only [Functor.comp_map, HomologicalComplex.homologyFunctor_map, ← Iso.app_inv,
    singularCubicalHomologyNatIso_app, ConcreteCategory.comp_apply] at h
  exact h

/-- **Every torus class is the class of a swept parameter torus.** Every element of `π₁(𝓛Q, γ)`
has the torus class of the torus `(t, s) ↦ ℓ s (exp (2πit))` swept out by some circle `ℓ` of free
loops based at `ℓ [0] = γ`. -/
theorem exists_freeLoopTorusClassHom_eq_singularHomologyMap {γ : C(Circle, Q)}
    (a : Additive (HomotopyGroup (Fin 1) C(Circle, Q) γ)) :
    ∃ ℓ : C(UnitAddCircle, C(Circle, Q)), ℓ ((0 : ℝ) : UnitAddCircle) = γ ∧
      freeLoopTorusClassHom Q γ a =
        ContinuousMap.singularHomologyMap ℤ 2 (freeLoopTorusMap ℓ)
          (addCircleProdFundamentalClass 1 1) := by
  induction a using Additive.rec with | ofMul a =>
  induction a using Quotient.inductionOn with | h p =>
  obtain ⟨ℓ, hℓ⟩ := GenLoop.exists_unitAddCircle_apply_eq p
  exact ⟨ℓ, (hℓ 0).trans (GenLoop.boundary p _ ⟨0, Or.inl rfl⟩),
    freeLoopTorusClassHom_ofMul_mk_eq_singularHomologyMap p ℓ hℓ⟩

end TauCeti
