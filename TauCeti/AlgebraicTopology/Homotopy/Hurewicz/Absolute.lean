/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Homotopy.Hurewicz.Sphere
public import TauCeti.AlgebraicTopology.Sphere.HomotopyGroup
import TauCeti.Algebra.Group.ZMultiples

/-!
# The absolute Hurewicz theorem

The Hurewicz homomorphism `HomotopyGroup.hurewiczHom` sends the class of a generalized loop
`p : (Iᵐ, ∂Iᵐ) → (X, x)` to the image of the generator of `Hₘ(Iᵐ, ∂Iᵐ)` under `p`. This file
proves the **Hurewicz theorem** for it in `Type 0` and in an arbitrary universe `u`: if `X` is
`(m - 1)`-connected at `x` and `m ≥ 2`, then with integer coefficients it is an isomorphism
`πₘ(X, x) ≅ Hₘ(X; ℤ)` (`HomotopyGroup.hurewiczAddEquiv`, `HomotopyGroup.bijective_hurewicz` in
`Type 0`, and `HomotopyGroup.hurewiczUliftAddEquiv`, `HomotopyGroup.bijective_hurewicz_ulift` in
`Type u` with coefficients in `ModuleCat.of ℤ (ULift.{u} ℤ)`).

The isomorphism is deduced from the cubical Hurewicz isomorphism
(`HomotopyGroup.cubicalHurewiczSingularHomologyAddEquiv`,
`HomotopyGroup.cubicalHurewiczSingularHomologyUliftAddEquiv`), by comparing the two Hurewicz maps.
They agree up to a sign `ε = ±1` that does not depend on the space
(`HomotopyGroup.exists_hurewicz_eq_units_smul_cubicalHurewicz`,
`HomotopyGroup.exists_hurewicz_ulift_eq_units_smul_cubicalHurewicz`). Both maps are natural in based
maps, and every generalized loop `p` is the image of the tautological loop of the sphere
(`TauCeti.sphereGenLoop m` in `Type 0`, `TauCeti.diskBoundaryGenLoop m` in `Type u`) under a based
map (`GenLoop.map_toSphere_sphereGenLoop`, `GenLoop.map_diskBoundaryMap_diskBoundaryGenLoop`), so it
suffices to compare them on that loop. On `πₘ(Sᵐ)` the cubical Hurewicz map is an isomorphism onto
`Hₘ(Sᵐ; ℤ)`, because `Sᵐ` is `(m - 1)`-connected
(`TauCeti.subsingleton_homotopyGroup_sphere_of_lt`), and the Hurewicz class of the tautological
loop generates `Hₘ(Sᵐ; ℤ) ≅ ℤ` (`TauCeti.isIso_hurewicz_sphereGenLoop`,
`TauCeti.isIso_hurewicz_diskBoundaryGenLoop`). An additive map `ℤ → ℤ` whose image contains a
generator is multiplication by a unit, so the two maps differ by a unit of `ℤ` on `πₘ(Sᵐ)`, and
hence everywhere.

## Main results

* `HomotopyGroup.exists_hurewicz_eq_units_smul_cubicalHurewicz`,
  `HomotopyGroup.exists_hurewicz_ulift_eq_units_smul_cubicalHurewicz`: the Hurewicz map is `ε`
  times the cubical Hurewicz map, transported to simplicial singular homology, for a universal sign
  `ε`.
* `HomotopyGroup.bijective_hurewicz`, `HomotopyGroup.hurewiczAddEquiv`,
  `HomotopyGroup.bijective_hurewicz_ulift`, and `HomotopyGroup.hurewiczUliftAddEquiv`: **the
  Hurewicz theorem**, `πₙ₊₂(X, x) ≅ Hₙ₊₂(X; ℤ)` for an `(n + 1)`-connected space in `Type 0` and
  in an arbitrary universe `u`.
* `HomotopyGroup.isIso_hurewicz_iff_bijective_zmultiplesHom`,
  `HomotopyGroup.isIso_hurewicz_ulift_iff_bijective_zmultiplesHom`: in that range, the Hurewicz
  class of a generalized loop generates `Hₙ₊₂(X; ℤ)` freely exactly when its homotopy class
  generates `πₙ₊₂(X, x)` freely.

## References

* A. Hatcher, [*Algebraic Topology*](https://pi.math.cornell.edu/~hatcher/AT/AT.pdf),
  Section 4.2, Theorems 4.32 and 4.37 (the Hurewicz theorem).
-/

public section

noncomputable section

open CategoryTheory AlgebraicTopology Metric
open scoped Topology.Homotopy

universe u

namespace HomotopyGroup

open TauCeti

section Small

/-- The cubical Hurewicz class of a generalized loop `p`, read in simplicial singular homology, is
the image of that of the tautological loop `TauCeti.sphereGenLoop (n + 2)` under
`(GenLoop.toSphere p)_*`. -/
private lemma singularCubicalHomologyIso_inv_cubicalHurewicz_mk {X : Type} [TopologicalSpace X]
    {x : X} {n : ℕ} (p : Ω^ (Fin (n + 2)) X x) :
    (singularCubicalHomologyIso ℤ (TopCat.of X) (n + 2)).inv
        (cubicalHurewicz ℤ (n + 1) (⟦p⟧ : HomotopyGroup (Fin (n + 2)) X x)) =
      HomologicalComplex.homologyMap
        ((singularChains ℤ).map (TopCat.ofHom (GenLoop.toSphere p))) (n + 2)
        ((singularCubicalHomologyIso ℤ _ (n + 2)).inv (cubicalHurewicz ℤ (n + 1)
          (⟦sphereGenLoop (n + 2)⟧ : HomotopyGroup (Fin (n + 2)) _ _))) := by
  have h := singularCubicalHomologyIso_inv_cubicalHurewiczHom_naturality ℤ (GenLoop.toSphere p)
    (GenLoop.toSphere_sphereNorthPole p) (Additive.ofMul ⟦sphereGenLoop (n + 2)⟧)
  rw [cubicalHurewiczHom_apply, cubicalHurewiczHom_apply] at h
  have hp : (⟦p⟧ : HomotopyGroup (Fin (n + 2)) X x) = HomotopyGroup.map (GenLoop.toSphere p)
      (GenLoop.toSphere_sphereNorthPole p) ⟦sphereGenLoop (n + 2)⟧ := by
    rw [HomotopyGroup.map_mk, GenLoop.map_toSphere_sphereGenLoop]
  rw [hp]
  exact h.symm

/-- **On the sphere, the two Hurewicz classes of the tautological loop differ by a unit.** The
Hurewicz class of `TauCeti.sphereGenLoop (n + 2)` with integer coefficients is a unit multiple of
its cubical Hurewicz class, read in simplicial singular homology. -/
private lemma exists_hurewicz_sphereGenLoop_eq_units_smul (n : ℕ) :
    ∃ ε : ℤˣ, (GenLoop.hurewicz (ModuleCat.of ℤ ℤ) (sphereGenLoop (n + 2))).hom 1 =
      (ε : ℤ) • (singularCubicalHomologyIso ℤ _ (n + 2)).inv (cubicalHurewicz ℤ (n + 1)
        (⟦sphereGenLoop (n + 2)⟧ : HomotopyGroup (Fin (n + 2)) _ _)) := by
  let ι := sphereGenLoop (n + 2)
  have hS (k : ℕ) (hk : k < n + 2) : Subsingleton (HomotopyGroup (Fin k)
      (sphere (0 : EuclideanSpace ℝ (Fin (n + 3))) 1) (sphereNorthPole (n + 2))) :=
    subsingleton_homotopyGroup_sphere_of_lt (n := n + 2) (by simp) (by simpa using hk) _
  -- The cubical Hurewicz isomorphism `c` of the sphere, read in the same homology group.
  let c : Additive (HomotopyGroup (Fin (n + 2))
      (sphere (0 : EuclideanSpace ℝ (Fin (n + 3))) 1) (sphereNorthPole (n + 2))) ≃+
        ((singularHomologyFunctor (ModuleCat.{0} ℤ) (n + 1 + 1)).obj (ModuleCat.of ℤ ℤ)).obj
          (TopCat.of (sphere (0 : EuclideanSpace ℝ (Fin (n + 3))) 1)) :=
    cubicalHurewiczSingularHomologyAddEquiv hS
  -- The Hurewicz class `g` of `ι` generates `Hₙ₊₂(Sⁿ⁺²; ℤ)`: `k ↦ k • g` is bijective.
  let e := (asIso (GenLoop.hurewicz (ModuleCat.of ℤ ℤ) ι)).toLinearEquiv
  let g := (GenLoop.hurewicz (ModuleCat.of ℤ ℤ) ι).hom 1
  have he : ⇑e = fun k : ℤ ↦ k • g := by
    funext k
    rw [← map_zsmul, smul_eq_mul, mul_one, CategoryTheory.Iso.toLinearEquiv_apply, asIso_hom]
  -- `h ∘ c⁻¹` sends `c ⟦ι⟧` to `h ⟦ι⟧ = g`, so `g` is a unit multiple of `c ⟦ι⟧`.
  let h := hurewiczIntHom (sphere (0 : EuclideanSpace ℝ (Fin (n + 3))) 1) (sphereNorthPole (n + 2))
    (n + 1)
  obtain ⟨ε, hε⟩ := (h.comp c.symm.toAddMonoidHom).exists_eq_units_smul_of_map_eq
    (he ▸ e.bijective) (x := c (Additive.ofMul ⟦ι⟧)) <| by
    rw [AddMonoidHom.comp_apply, AddEquiv.coe_toAddMonoidHom, AddEquiv.symm_apply_apply,
      hurewiczIntHom_apply]
    exact congrArg (fun f ↦ ModuleCat.Hom.hom f (1 : ℤ)) (hurewicz_mk (ModuleCat.of ℤ ℤ) (n + 1) ι)
  exact ⟨ε, hε.trans (congrArg _ ((cubicalHurewiczSingularHomologyAddEquiv_apply hS _).trans
    (congrArg _ (cubicalHurewiczHom_apply ℤ (n + 1) _))))⟩

/-- **The Hurewicz map is the cubical Hurewicz map up to a universal sign.** There is a unit
`ε` of `ℤ` such that for every space `X`, point `x` and class `a ∈ πₙ₊₂(X, x)`, the Hurewicz class
of `a` with integer coefficients is `ε` times the cubical Hurewicz class of `a`, read in simplicial
singular homology through the inverse cubical--simplicial comparison. -/
theorem exists_hurewicz_eq_units_smul_cubicalHurewicz (n : ℕ) :
    ∃ ε : ℤˣ, ∀ (X : Type) [TopologicalSpace X] (x : X) (a : HomotopyGroup (Fin (n + 2)) X x),
      (hurewicz (ModuleCat.of ℤ ℤ) (n + 1) a).hom 1 =
        (ε : ℤ) • (singularCubicalHomologyIso ℤ (TopCat.of X) (n + 2)).inv
          (cubicalHurewicz ℤ (n + 1) a) := by
  obtain ⟨ε, hε⟩ := exists_hurewicz_sphereGenLoop_eq_units_smul n
  refine ⟨ε, fun X _ x a ↦ ?_⟩
  -- Every class is the image of the tautological class of the sphere under a based map, and both
  -- maps are natural.
  induction a using Quotient.inductionOn with | h p => ?_
  rw [hurewicz_mk, GenLoop.hurewicz_eq_hurewicz_sphereGenLoop_comp, ModuleCat.hom_comp,
    LinearMap.comp_apply, hε, singularCubicalHomologyIso_inv_cubicalHurewicz_mk p]
  -- The map induced on singular homology is, by definition, the homology map of the induced chain
  -- map.
  exact map_zsmul (((singularHomologyFunctor (ModuleCat.{0} ℤ) (n + 1 + 1)).obj
    (ModuleCat.of ℤ ℤ)).map (TopCat.ofHom (GenLoop.toSphere p))).hom _ _

variable {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y] {x : X} {y : Y} {n : ℕ}

/-- **The Hurewicz theorem.** If `πₖ(X, x)` is trivial for every `k < n + 2`, then the Hurewicz
map `πₙ₊₂(X, x) → Hₙ₊₂(X; ℤ)`, `[p] ↦ p_*[Iⁿ⁺²]`, is bijective. -/
theorem bijective_hurewicz (hX : ∀ k < n + 2, Subsingleton (HomotopyGroup (Fin k) X x)) :
    Function.Bijective fun a : HomotopyGroup (Fin (n + 2)) X x ↦
      (hurewicz (ModuleCat.of ℤ ℤ) (n + 1) a).hom 1 := by
  obtain ⟨ε, hε⟩ := exists_hurewicz_eq_units_smul_cubicalHurewicz n
  have hfun : (fun a : HomotopyGroup (Fin (n + 2)) X x ↦
      (hurewicz (ModuleCat.of ℤ ℤ) (n + 1) a).hom 1) =
        (fun y ↦ (ε : ℤ) • y) ∘ cubicalHurewiczSingularHomologyAddEquiv hX ∘ Additive.ofMul := by
    funext a
    rw [Function.comp_apply, Function.comp_apply, cubicalHurewiczSingularHomologyAddEquiv_apply,
      cubicalHurewiczHom_apply, toMul_ofMul]
    exact hε X x a
  rw [hfun]
  exact (MulAction.bijective ε).comp
    ((cubicalHurewiczSingularHomologyAddEquiv hX).bijective.comp Additive.ofMul.bijective)

/-- **The Hurewicz isomorphism** `πₙ₊₂(X, x) ≅ Hₙ₊₂(X; ℤ)` for a space `X` with `πₖ(X, x)` trivial
for every `k < n + 2`. Its forward map is the Hurewicz homomorphism `HomotopyGroup.hurewiczHom`
with integer coefficients, evaluated at `1 : ℤ` (`HomotopyGroup.hurewiczAddEquiv_apply`). -/
def hurewiczAddEquiv (hX : ∀ k < n + 2, Subsingleton (HomotopyGroup (Fin k) X x)) :
    Additive (HomotopyGroup (Fin (n + 2)) X x) ≃+
      ((singularHomologyFunctor (ModuleCat.{0} ℤ) (n + 2)).obj (ModuleCat.of ℤ ℤ)).obj
        (TopCat.of X) :=
  AddEquiv.ofBijective (hurewiczIntHom X x (n + 1)) <| by
    convert (bijective_hurewicz hX).comp Additive.toMul.bijective using 1
    funext a
    exact hurewiczIntHom_apply X x (n + 1) a

@[simp]
theorem hurewiczAddEquiv_apply (hX : ∀ k < n + 2, Subsingleton (HomotopyGroup (Fin k) X x))
    (a : Additive (HomotopyGroup (Fin (n + 2)) X x)) :
    hurewiczAddEquiv hX a = (hurewiczHom (ModuleCat.of ℤ ℤ) (n + 1) a).hom 1 :=
  (AddEquiv.ofBijective_apply _ _ _).trans <| by rw [hurewiczIntHom_apply, hurewiczHom_apply]

/-- The Hurewicz isomorphism sends the class of a generalized loop `p` to its Hurewicz class
`GenLoop.hurewicz`, evaluated at `1 : ℤ`. -/
theorem hurewiczAddEquiv_ofMul_mk (hX : ∀ k < n + 2, Subsingleton (HomotopyGroup (Fin k) X x))
    (p : Ω^ (Fin (n + 2)) X x) :
    hurewiczAddEquiv hX (Additive.ofMul ⟦p⟧) = (GenLoop.hurewicz (ModuleCat.of ℤ ℤ) p).hom 1 := by
  rw [hurewiczAddEquiv_apply, hurewiczHom_apply]
  exact congrArg (fun f ↦ ModuleCat.Hom.hom f 1) (hurewicz_mk (ModuleCat.of ℤ ℤ) (n + 1) p)

/-- The Hurewicz isomorphism is natural in based maps between `(n + 1)`-connected spaces. -/
theorem hurewiczAddEquiv_naturality
    (hX : ∀ k < n + 2, Subsingleton (HomotopyGroup (Fin k) X x))
    (hY : ∀ k < n + 2, Subsingleton (HomotopyGroup (Fin k) Y y))
    (f : C(X, Y)) (hf : f x = y)
    (a : Additive (HomotopyGroup (Fin (n + 2)) X x)) :
    (((singularHomologyFunctor (ModuleCat.{0} ℤ) (n + 2)).obj (ModuleCat.of ℤ ℤ)).map
        (TopCat.ofHom f)).hom (hurewiczAddEquiv hX a) =
      hurewiczAddEquiv hY (Additive.ofMul (HomotopyGroup.map f hf a.toMul)) := by
  rw [hurewiczAddEquiv_apply, hurewiczAddEquiv_apply, hurewiczHom_apply, hurewiczHom_apply,
    toMul_ofMul, hurewicz_map, ModuleCat.hom_comp, LinearMap.comp_apply]

/-- **The Hurewicz class of a generalized loop generates exactly when its homotopy class does.**
For an `(n + 1)`-connected space, the Hurewicz class of `p` is an isomorphism `ℤ ≅ Hₙ₊₂(X; ℤ)`
exactly when the class of `p` generates `πₙ₊₂(X, x)` freely: `k ↦ [p]ᵏ` is bijective. -/
theorem isIso_hurewicz_iff_bijective_zmultiplesHom
    (hX : ∀ k < n + 2, Subsingleton (HomotopyGroup (Fin k) X x)) (p : Ω^ (Fin (n + 2)) X x) :
    IsIso (GenLoop.hurewicz (ModuleCat.of ℤ ℤ) p) ↔
      Function.Bijective
        (zmultiplesHom (Additive (HomotopyGroup (Fin (n + 2)) X x)) (Additive.ofMul ⟦p⟧)) := by
  have h : ⇑(GenLoop.hurewicz (ModuleCat.of ℤ ℤ) p).hom =
      zmultiplesHom _ ((GenLoop.hurewicz (ModuleCat.of ℤ ℤ) p).hom 1) := by
    funext t
    rw [zmultiplesHom_apply, ← map_zsmul, smul_eq_mul, mul_one]
  rw [ConcreteCategory.isIso_iff_bijective, h,
    ← (hurewiczAddEquiv hX).bijective_zmultiplesHom_apply_iff, hurewiczAddEquiv_ofMul_mk]

end Small

/-! ### Arbitrary universes -/

section Universe

/-- In universe `u`, the cubical Hurewicz class of a generalized loop `p`, read in singular
homology with coefficients in `ModuleCat.of ℤ (ULift.{u} ℤ)`, is the image of that of
`TauCeti.diskBoundaryGenLoop (n + 2)` under `(GenLoop.diskBoundaryMap p)_*`. -/
private lemma singularHomologyUliftAddEquiv_symm_cubicalHurewicz_mk
    {X : Type u} [TopologicalSpace X] {x : X} {n : ℕ} (p : Ω^ (Fin (n + 2)) X x) :
    ((TopCat.of X).singularHomologyUliftAddEquiv.{u, 0} ℤ (n + 2)).symm
        ((singularCubicalHomologyIso (ULift.{u} ℤ) (TopCat.of X) (n + 2)).inv
          (cubicalHurewicz (ULift.{u} ℤ) (n + 1) (⟦p⟧ : HomotopyGroup (Fin (n + 2)) X x))) =
      (((singularHomologyFunctor (ModuleCat.{u} ℤ) (n + 2)).obj
          (ModuleCat.of ℤ (ULift.{u} ℤ))).map (GenLoop.diskBoundaryMap (X := TopCat.of X) p)).hom
        (((TopCat.diskBoundary.{u} (n + 3)).singularHomologyUliftAddEquiv.{u, 0} ℤ (n + 2)).symm
          ((singularCubicalHomologyIso (ULift.{u} ℤ) (TopCat.diskBoundary.{u} (n + 3)) (n + 2)).inv
            (cubicalHurewicz (ULift.{u} ℤ) (n + 1)
              (⟦diskBoundaryGenLoop.{u} (n + 2)⟧ : HomotopyGroup (Fin (n + 2)) _ _)))) := by
  let f := GenLoop.diskBoundaryMap (X := TopCat.of X) p
  let f₀ : C(TopCat.diskBoundary.{u} (n + 3), X) := f.hom
  let ι : HomotopyGroup (Fin (n + 2)) (TopCat.diskBoundary.{u} (n + 3))
      (diskBoundaryNorthPole.{u} (n + 2)) := ⟦diskBoundaryGenLoop.{u} (n + 2)⟧
  have h := singularCubicalHomologyIso_inv_cubicalHurewiczHom_naturality (ULift.{u} ℤ) f₀
    (GenLoop.diskBoundaryMap_diskBoundaryNorthPole p) (Additive.ofMul ι)
  rw [cubicalHurewiczHom_apply, cubicalHurewiczHom_apply] at h
  have hp : (⟦p⟧ : HomotopyGroup (Fin (n + 2)) X x) =
      HomotopyGroup.map f₀ (GenLoop.diskBoundaryMap_diskBoundaryNorthPole p) ι := by
    rw [HomotopyGroup.map_mk, GenLoop.map_diskBoundaryMap_diskBoundaryGenLoop]
  rw [hp]
  -- `TopCat.ofHom f₀` and `f` coincide by definition in `TopCat`.
  exact (congrArg ((TopCat.of X).singularHomologyUliftAddEquiv.{u, 0} ℤ (n + 2)).symm h.symm).trans
    (TopCat.singularHomologyUliftAddEquiv_symm_naturality.{u, 0} ℤ f (n + 2) _)

/-- **On `∂𝔻 (n + 3)`, the two Hurewicz classes of the tautological loop differ by a unit.** -/
private lemma exists_hurewicz_diskBoundaryGenLoop_eq_units_smul (n : ℕ) :
    ∃ ε : ℤˣ,
      (GenLoop.hurewicz (ModuleCat.of ℤ (ULift.{u} ℤ)) (diskBoundaryGenLoop.{u} (n + 2))).hom 1 =
        (ε : ℤ) •
          ((TopCat.diskBoundary.{u} (n + 3)).singularHomologyUliftAddEquiv.{u, 0} ℤ (n + 2)).symm
            ((singularCubicalHomologyIso (ULift.{u} ℤ) (TopCat.diskBoundary.{u} (n + 3))
              (n + 2)).inv (cubicalHurewicz (ULift.{u} ℤ) (n + 1)
                (⟦diskBoundaryGenLoop.{u} (n + 2)⟧ : HomotopyGroup (Fin (n + 2)) _ _))) := by
  let ι := diskBoundaryGenLoop.{u} (n + 2)
  have hS (k : ℕ) (hk : k < n + 2) : Subsingleton (HomotopyGroup (Fin k)
      (TopCat.diskBoundary.{u} (n + 3)) (diskBoundaryNorthPole.{u} (n + 2))) :=
    (homeomorphEquiv (Homeomorph.ulift : TopCat.diskBoundary.{u} (n + 3) ≃ₜ _)
      _).subsingleton_congr.mpr
        (subsingleton_homotopyGroup_sphere_of_lt (n := n + 2) (by simp) (by simpa using hk) _)
  let c := cubicalHurewiczSingularHomologyUliftAddEquiv hS
  -- Precomposing the `ULift.{u} ℤ`-module isomorphism `GenLoop.hurewicz` with `ULift.up` gives a
  -- `ℤ`-linear equivalence `ℤ ≃ₗ[ℤ] H_{n+2}(∂𝔻 (n + 3); ULift.{u} ℤ)` sending `k` to `k • g`.
  let e := (ULift.moduleEquiv : ULift.{u} ℤ ≃ₗ[ℤ] ℤ).symm.trans
    (asIso (GenLoop.hurewicz (ModuleCat.of ℤ (ULift.{u} ℤ)) ι)).toLinearEquiv
  let g := (GenLoop.hurewicz (ModuleCat.of ℤ (ULift.{u} ℤ)) ι).hom 1
  have he : ⇑e = fun k : ℤ ↦ k • g := by
    funext k
    have hk : (ULift.moduleEquiv : ULift.{u} ℤ ≃ₗ[ℤ] ℤ).symm k = k • (1 : ULift.{u} ℤ) :=
      ULift.ext (by simp)
    rw [LinearEquiv.trans_apply, hk, CategoryTheory.Iso.toLinearEquiv_apply, asIso_hom, map_zsmul]
  let h := hurewiczUliftIntHom (TopCat.diskBoundary.{u} (n + 3))
    (diskBoundaryNorthPole.{u} (n + 2)) (n + 1)
  obtain ⟨ε, hε⟩ := (h.comp c.symm.toAddMonoidHom).exists_eq_units_smul_of_map_eq
    (he ▸ e.bijective) (x := c (Additive.ofMul ⟦ι⟧)) <| by
    rw [AddMonoidHom.comp_apply, AddEquiv.coe_toAddMonoidHom, AddEquiv.symm_apply_apply,
      hurewiczUliftIntHom_apply]
    exact congrArg (fun f ↦ ModuleCat.Hom.hom f (1 : ULift.{u} ℤ))
      (hurewicz_mk (ModuleCat.of ℤ (ULift.{u} ℤ)) (n + 1) ι)
  exact ⟨ε, hε.trans (congrArg _ ((cubicalHurewiczSingularHomologyUliftAddEquiv_apply hS _).trans
    (congrArg _ (congrArg _ (cubicalHurewiczHom_apply (ULift.{u} ℤ) (n + 1) _)))))⟩

/-- **In every universe, the Hurewicz map agrees with the cubical Hurewicz map up to a universal
sign.** There is a unit `ε` of `ℤ` such that for every space `X : Type u`, point `x : X`, and class
`a ∈ πₙ₊₂(X, x)`, the Hurewicz class of `a` with coefficients in `ModuleCat.of ℤ (ULift.{u} ℤ)` is
`ε` times its cubical Hurewicz class over `ULift.{u} ℤ`, transported to singular homology. -/
theorem exists_hurewicz_ulift_eq_units_smul_cubicalHurewicz (n : ℕ) :
    ∃ ε : ℤˣ, ∀ (X : Type u) [TopologicalSpace X] (x : X)
      (a : HomotopyGroup (Fin (n + 2)) X x),
      (hurewicz (ModuleCat.of ℤ (ULift.{u} ℤ)) (n + 1) a).hom 1 =
        (ε : ℤ) • ((TopCat.of X).singularHomologyUliftAddEquiv.{u, 0} ℤ (n + 2)).symm
          ((singularCubicalHomologyIso (ULift.{u} ℤ) (TopCat.of X) (n + 2)).inv
            (cubicalHurewicz (ULift.{u} ℤ) (n + 1) a)) := by
  obtain ⟨ε, hε⟩ := exists_hurewicz_diskBoundaryGenLoop_eq_units_smul.{u} n
  refine ⟨ε, fun X _ x a ↦ ?_⟩
  induction a using Quotient.inductionOn with | h p => ?_
  rw [hurewicz_mk, GenLoop.hurewicz_eq_hurewicz_diskBoundaryGenLoop_comp, ModuleCat.hom_comp,
    LinearMap.comp_apply, hε, singularHomologyUliftAddEquiv_symm_cubicalHurewicz_mk p]
  exact map_zsmul (((singularHomologyFunctor (ModuleCat.{u} ℤ) (n + 2)).obj
    (ModuleCat.of ℤ (ULift.{u} ℤ))).map (GenLoop.diskBoundaryMap (X := TopCat.of X) p)).hom _ _

variable {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y] {x : X} {y : Y} {n : ℕ}

/-- **The absolute Hurewicz theorem in every universe.** If `πₖ(X, x)` is trivial for every
`k < n + 2`, then for a space `X : Type u` the Hurewicz map
`πₙ₊₂(X, x) → Hₙ₊₂(X; ULift.{u} ℤ)`, `[p] ↦ p_*[Iⁿ⁺²]`, is bijective. -/
theorem bijective_hurewicz_ulift
    (hX : ∀ k < n + 2, Subsingleton (HomotopyGroup (Fin k) X x)) :
    Function.Bijective fun a : HomotopyGroup (Fin (n + 2)) X x ↦
      (hurewicz (ModuleCat.of ℤ (ULift.{u} ℤ)) (n + 1) a).hom 1 := by
  obtain ⟨ε, hε⟩ := exists_hurewicz_ulift_eq_units_smul_cubicalHurewicz.{u} n
  have hfun : (fun a : HomotopyGroup (Fin (n + 2)) X x ↦
      (hurewicz (ModuleCat.of ℤ (ULift.{u} ℤ)) (n + 1) a).hom 1) =
        (fun y ↦ (ε : ℤ) • y) ∘
          cubicalHurewiczSingularHomologyUliftAddEquiv hX ∘ Additive.ofMul := by
    funext a
    rw [Function.comp_apply, Function.comp_apply,
      cubicalHurewiczSingularHomologyUliftAddEquiv_apply, cubicalHurewiczHom_apply, toMul_ofMul]
    exact hε X x a
  rw [hfun]
  exact (MulAction.bijective ε).comp
    ((cubicalHurewiczSingularHomologyUliftAddEquiv hX).bijective.comp Additive.ofMul.bijective)

/-- **The Hurewicz isomorphism in an arbitrary universe** `u`,
`πₙ₊₂(X, x) ≅ Hₙ₊₂(X; ULift.{u} ℤ)`, for a space `X : Type u` with `πₖ(X, x)` trivial for every
`k < n + 2`. Its forward map is `HomotopyGroup.hurewiczHom` with coefficients in
`ModuleCat.of ℤ (ULift.{u} ℤ)`, evaluated at `1 : ULift.{u} ℤ`
(`HomotopyGroup.hurewiczUliftAddEquiv_apply`). -/
def hurewiczUliftAddEquiv (hX : ∀ k < n + 2, Subsingleton (HomotopyGroup (Fin k) X x)) :
    Additive (HomotopyGroup (Fin (n + 2)) X x) ≃+
      ((singularHomologyFunctor (ModuleCat.{u} ℤ) (n + 2)).obj
        (ModuleCat.of ℤ (ULift.{u} ℤ))).obj (TopCat.of X) :=
  AddEquiv.ofBijective (hurewiczUliftIntHom X x (n + 1)) <| by
    convert (bijective_hurewicz_ulift hX).comp Additive.toMul.bijective using 1
    funext a
    exact hurewiczUliftIntHom_apply X x (n + 1) a

@[simp]
theorem hurewiczUliftAddEquiv_apply (hX : ∀ k < n + 2, Subsingleton (HomotopyGroup (Fin k) X x))
    (a : Additive (HomotopyGroup (Fin (n + 2)) X x)) :
    hurewiczUliftAddEquiv hX a =
      (hurewiczHom (ModuleCat.of ℤ (ULift.{u} ℤ)) (n + 1) a).hom 1 :=
  (AddEquiv.ofBijective_apply _ _ _).trans <| by rw [hurewiczUliftIntHom_apply, hurewiczHom_apply]

/-- `HomotopyGroup.hurewiczUliftAddEquiv` sends the class of a generalized loop `p` to its Hurewicz
class `GenLoop.hurewicz`, evaluated at `1 : ULift.{u} ℤ`. -/
theorem hurewiczUliftAddEquiv_ofMul_mk (hX : ∀ k < n + 2, Subsingleton (HomotopyGroup (Fin k) X x))
    (p : Ω^ (Fin (n + 2)) X x) :
    hurewiczUliftAddEquiv hX (Additive.ofMul ⟦p⟧) =
      (GenLoop.hurewicz (ModuleCat.of ℤ (ULift.{u} ℤ)) p).hom 1 := by
  rw [hurewiczUliftAddEquiv_apply, hurewiczHom_apply]
  exact congrArg (fun f ↦ ModuleCat.Hom.hom f (1 : ULift.{u} ℤ))
    (hurewicz_mk (ModuleCat.of ℤ (ULift.{u} ℤ)) (n + 1) p)

/-- `HomotopyGroup.hurewiczUliftAddEquiv` is natural in based maps between `(n + 1)`-connected
spaces in universe `u`. -/
theorem hurewiczUliftAddEquiv_naturality
    (hX : ∀ k < n + 2, Subsingleton (HomotopyGroup (Fin k) X x))
    (hY : ∀ k < n + 2, Subsingleton (HomotopyGroup (Fin k) Y y))
    (f : C(X, Y)) (hf : f x = y)
    (a : Additive (HomotopyGroup (Fin (n + 2)) X x)) :
    (((singularHomologyFunctor (ModuleCat.{u} ℤ) (n + 2)).obj
        (ModuleCat.of ℤ (ULift.{u} ℤ))).map (TopCat.ofHom f)).hom (hurewiczUliftAddEquiv hX a) =
      hurewiczUliftAddEquiv hY (Additive.ofMul (HomotopyGroup.map f hf a.toMul)) := by
  rw [hurewiczUliftAddEquiv_apply, hurewiczUliftAddEquiv_apply, hurewiczHom_apply,
    hurewiczHom_apply, toMul_ofMul, hurewicz_map, ModuleCat.hom_comp, LinearMap.comp_apply]

/-- **In every universe, the Hurewicz class of a generalized loop generates exactly when its
homotopy class does.** For an `(n + 1)`-connected space `X : Type u`, the Hurewicz class of `p` is
an isomorphism `ULift.{u} ℤ ≅ Hₙ₊₂(X; ULift.{u} ℤ)` in `ModuleCat.{u} ℤ` if and only if the class
of `p` generates `πₙ₊₂(X, x)` freely (`k ↦ [p]ᵏ` is bijective). -/
theorem isIso_hurewicz_ulift_iff_bijective_zmultiplesHom
    (hX : ∀ k < n + 2, Subsingleton (HomotopyGroup (Fin k) X x)) (p : Ω^ (Fin (n + 2)) X x) :
    IsIso (GenLoop.hurewicz (ModuleCat.of ℤ (ULift.{u} ℤ)) p) ↔
      Function.Bijective
        (zmultiplesHom (Additive (HomotopyGroup (Fin (n + 2)) X x)) (Additive.ofMul ⟦p⟧)) := by
  have h : ⇑(GenLoop.hurewicz (ModuleCat.of ℤ (ULift.{u} ℤ)) p).hom ∘ ⇑Equiv.ulift.symm =
      zmultiplesHom _ ((GenLoop.hurewicz (ModuleCat.of ℤ (ULift.{u} ℤ)) p).hom 1) := by
    funext k
    have hk : (Equiv.ulift : ULift.{u} ℤ ≃ ℤ).symm k = k • (1 : ULift.{u} ℤ) :=
      ULift.ext (by simp)
    rw [Function.comp_apply, zmultiplesHom_apply, hk, map_zsmul]
  rw [ConcreteCategory.isIso_iff_bijective, ← Equiv.ulift.symm.bijective_comp, h,
    ← (hurewiczUliftAddEquiv hX).bijective_zmultiplesHom_apply_iff, hurewiczUliftAddEquiv_ofMul_mk]

end Universe

end HomotopyGroup
