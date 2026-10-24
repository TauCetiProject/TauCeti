/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Homotopy.Hurewicz.Sphere
public import TauCeti.AlgebraicTopology.Sphere.HomotopyGroup

/-!
# The absolute Hurewicz theorem

The Hurewicz homomorphism `HomotopyGroup.hurewiczHom` sends the class of a generalized loop
`p : (Iᵐ, ∂Iᵐ) → (X, x)` to the image of the generator of `Hₘ(Iᵐ, ∂Iᵐ)` under `p`. This file
proves the **Hurewicz theorem** for it: if `X` is `(m - 1)`-connected at `x` and `m ≥ 2`, then
with integer coefficients it is an isomorphism `πₘ(X, x) ≅ Hₘ(X; ℤ)`
(`HomotopyGroup.hurewiczAddEquiv`).

The isomorphism is deduced from the cubical Hurewicz isomorphism
`HomotopyGroup.cubicalHurewiczSingularHomologyAddEquiv`, by comparing the two Hurewicz maps. They
agree up to a sign `ε = ±1` that does not depend on the space
(`HomotopyGroup.exists_hurewicz_eq_units_smul_cubicalHurewicz`). Both maps are natural in based
maps, and every generalized loop `p` is the image of the tautological loop
`TauCeti.sphereGenLoop m` of the sphere `Sᵐ` under a based map
(`GenLoop.map_toSphere_sphereGenLoop`), so it suffices to compare them on that loop. On
`πₘ(Sᵐ)` the cubical Hurewicz map is an isomorphism onto `Hₘ(Sᵐ; ℤ)`, because `Sᵐ` is
`(m - 1)`-connected (`TauCeti.subsingleton_homotopyGroup_sphere_of_lt`), and the Hurewicz class of
the tautological loop generates `Hₘ(Sᵐ; ℤ) ≅ ℤ` (`TauCeti.isIso_hurewicz_sphereGenLoop`). An
additive map `ℤ → ℤ` whose image contains a generator is multiplication by a unit, so the two
maps differ by a unit of `ℤ` on `πₘ(Sᵐ)`, and hence everywhere.

## Main results

* `HomotopyGroup.exists_hurewicz_eq_units_smul_cubicalHurewicz`: the Hurewicz map is `ε` times
  the cubical Hurewicz map, transported to simplicial singular homology, for a universal sign `ε`.
* `HomotopyGroup.bijective_hurewicz` and `HomotopyGroup.hurewiczAddEquiv`: **the Hurewicz
  theorem**, `πₙ₊₂(X, x) ≅ Hₙ₊₂(X; ℤ)` for an `(n + 1)`-connected space.

## References

* A. Hatcher, [*Algebraic Topology*](https://pi.math.cornell.edu/~hatcher/AT/AT.pdf),
  Section 4.2, Theorem 4.32 (the Hurewicz theorem).
-/

public section

noncomputable section

open CategoryTheory AlgebraicTopology Metric
open scoped Topology.Homotopy

namespace HomotopyGroup

open TauCeti

/-- The Hurewicz homomorphism with integer coefficients, evaluated at `1 : ℤ`. -/
private def hurewiczIntHom (X : Type) [TopologicalSpace X] (x : X) (n : ℕ) :
    Additive (HomotopyGroup (Fin (n + 1)) X x) →+
      ((singularHomologyFunctor (ModuleCat.{0} ℤ) (n + 1)).obj (ModuleCat.of ℤ ℤ)).obj
        (TopCat.of X) where
  toFun a := (hurewiczHom (ModuleCat.of ℤ ℤ) n a).hom 1
  map_zero' := by simp
  map_add' a b := by simp

private lemma hurewiczIntHom_apply (X : Type) [TopologicalSpace X] (x : X) (n : ℕ)
    (a : Additive (HomotopyGroup (Fin (n + 1)) X x)) :
    hurewiczIntHom X x n a = (hurewicz (ModuleCat.of ℤ ℤ) n a.toMul).hom 1 :=
  congrArg (fun f ↦ ModuleCat.Hom.hom f 1) (hurewiczHom_apply _ n a)

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
  have he (k : ℤ) : e k = k • g := by
    have : e k = e (k • (1 : ℤ)) := by rw [smul_eq_mul, mul_one]
    rw [this, map_zsmul, CategoryTheory.Iso.toLinearEquiv_apply, asIso_hom]
  let h := hurewiczIntHom (sphere (0 : EuclideanSpace ℝ (Fin (n + 3))) 1) (sphereNorthPole (n + 2))
    (n + 1)
  let a₁ : Additive (HomotopyGroup (Fin (n + 2))
      (sphere (0 : EuclideanSpace ℝ (Fin (n + 3))) 1) (sphereNorthPole (n + 2))) :=
    Additive.ofMul ⟦ι⟧
  -- Write `c a₀ = g`, `h a₀ = j • g` and `c a₁ = m • g` for `a₁ = ⟦ι⟧`. Then `a₁ = m • a₀`, so
  -- `g = h a₁ = (m * j) • g`, and `m * j = 1`.
  obtain ⟨a₀, ha₀⟩ := c.surjective g
  obtain ⟨j, hj⟩ := e.surjective (h a₀)
  obtain ⟨m, hm⟩ := e.surjective (c a₁)
  have hι : a₁ = m • a₀ := c.injective (by rw [map_zsmul, ha₀, ← hm, he])
  have hmj : m * j = 1 := e.injective <| by
    rw [he, he, mul_smul, ← he j, hj, ← map_zsmul, ← hι, hurewiczIntHom_apply, one_smul]
    exact congrArg (fun f ↦ ModuleCat.Hom.hom f (1 : ℤ)) (hurewicz_mk (ModuleCat.of ℤ ℤ) (n + 1) ι)
  have hc : c a₁ = (singularCubicalHomologyIso ℤ _ (n + 2)).inv
      (cubicalHurewicz ℤ (n + 1) (⟦ι⟧ : HomotopyGroup (Fin (n + 2)) _ _)) :=
    (cubicalHurewiczSingularHomologyAddEquiv_apply hS a₁).trans
      (congrArg _ (cubicalHurewiczHom_apply ℤ (n + 1) a₁))
  have hsphere : g = j • c a₁ := by
    rw [← hm, he, smul_smul, mul_comm, hmj, one_smul]
  exact ⟨⟨j, m, by rw [mul_comm, hmj], hmj⟩, hsphere.trans (congrArg ((j : ℤ) • ·) hc)⟩

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

variable {X : Type} [TopologicalSpace X] {x : X} {n : ℕ}

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
  AddEquiv.ofBijective_apply _ _ _

end HomotopyGroup
