/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Sphere.BasedQuotient
public import TauCeti.Topology.Constructions.ReducedSuspension.Smash

/-!
# Smash products and reduced suspensions of spheres

This file constructs the canonical pointed homeomorphisms for spheres equipped with their positive
first-coordinate basepoint `TauCeti.sphereBasepoint`:
* `TauCeti.SmashProduct.sphereZeroLeftHomeomorph` and
  `TauCeti.SmashProduct.sphereZeroRightHomeomorph`: `S⁰ ∧ X ≃ₜ X` and `X ∧ S⁰ ≃ₜ X`.
* `TauCeti.smashSphereHomeomorph`: `Sᵐ ∧ Sⁿ ≃ₜ Sᵐ⁺ⁿ` for all `m, n ≥ 0`, given on based cube
  representatives by `Fin.append x y`, together with its unit and associativity coherences.
* `TauCeti.intervalQuotientSphereOneHomeomorph` (`I / {0, 1} ≃ₜ S¹`) and
  `TauCeti.reducedSuspensionSphereHomeomorph` (`ΣSⁿ ≃ₜ Sⁿ⁺¹` for all `n ≥ 0`), given on based cube
  representatives by `Fin.snoc x t`.

## References

* A. Hatcher, [*Algebraic Topology*](https://pi.math.cornell.edu/~hatcher/AT/AT.pdf), Chapter 0.
* J. P. May, [*A Concise Course in Algebraic Topology*](https://www.math.uchicago.edu/~may/CONCISE/ConciseRevised.pdf),
  Sections 8.2–8.3.
-/

public section

noncomputable section

open CategoryTheory Set Topology
open scoped unitInterval

universe u

namespace TauCeti

namespace SmashProduct

section SphereZeroUnit

variable {X : Type u} [TopologicalSpace X] (x₀ : X)

private def sphereZeroLeftRaw : C(TopCat.sphere.{u} 0 × X, X) where
  toFun := open Classical in fun p ↦ if p.1 = sphereBasepoint.{u} 0 then x₀ else p.2
  continuous_toFun := by
    classical
    refine continuous_prod_of_discrete_left.2 fun s ↦ ?_
    by_cases hs : s = sphereBasepoint.{u} 0
    · simpa [hs] using continuous_const
    · simpa [hs] using continuous_id'

/-- **Left unit of the smash product**: `S⁰ ∧ X ≃ₜ X` for any pointed topological space `(X, x₀)`,
identifying `(-e₀) ∧ x` with `x` and `e₀` with the collapsed basepoint. -/
def sphereZeroLeftHomeomorph : SmashProduct (sphereBasepoint.{u} 0) x₀ ≃ₜ X where
  toFun := lift (sphereZeroLeftRaw x₀) x₀
    (fun _ ↦ by classical simp [sphereZeroLeftRaw]) (fun _ ↦ by classical simp [sphereZeroLeftRaw])
  invFun x := mk (sphereBasepoint.{u} 0) x₀ (sphereAntiBasepoint.{u} 0, x)
  left_inv := ind fun s x ↦ by
    rcases eq_sphereBasepoint_or_eq_sphereAntiBasepoint s with rfl | rfl <;>
      classical simp [sphereZeroLeftRaw, (sphereBasepoint_ne_sphereAntiBasepoint.{u} 0).symm]
  right_inv _ := by
    classical simp [sphereZeroLeftRaw, (sphereBasepoint_ne_sphereAntiBasepoint.{u} 0).symm]
  continuous_toFun := (lift (sphereZeroLeftRaw x₀) x₀ _ _).continuous
  continuous_invFun := (mk (sphereBasepoint.{u} 0) x₀).continuous.comp
    (continuous_const.prodMk continuous_id)

@[simp]
lemma sphereZeroLeftHomeomorph_mk_antiBasepoint (x : X) :
    sphereZeroLeftHomeomorph x₀
      (mk (sphereBasepoint.{u} 0) x₀ (sphereAntiBasepoint.{u} 0, x)) = x :=
  (sphereZeroLeftHomeomorph x₀).right_inv x

@[simp]
lemma sphereZeroLeftHomeomorph_basepoint :
    sphereZeroLeftHomeomorph x₀ (basepoint (sphereBasepoint.{u} 0) x₀) = x₀ :=
  lift_basepoint (sphereZeroLeftRaw x₀) x₀ _ _

@[simp]
lemma sphereZeroLeftHomeomorph_symm_apply (x : X) :
    (sphereZeroLeftHomeomorph x₀).symm x =
      mk (sphereBasepoint.{u} 0) x₀ (sphereAntiBasepoint.{u} 0, x) := (rfl)

/-- **Right unit of the smash product**: `X ∧ S⁰ ≃ₜ X` for any pointed topological space `(X, x₀)`,
identifying `x ∧ (-e₀)` with `x` and `e₀` with the collapsed basepoint. -/
def sphereZeroRightHomeomorph : SmashProduct x₀ (sphereBasepoint.{u} 0) ≃ₜ X :=
  (comm x₀ (sphereBasepoint.{u} 0)).trans (sphereZeroLeftHomeomorph x₀)

@[simp]
lemma sphereZeroRightHomeomorph_mk_antiBasepoint (x : X) :
    sphereZeroRightHomeomorph x₀
      (mk x₀ (sphereBasepoint.{u} 0) (x, sphereAntiBasepoint.{u} 0)) = x := by
  simp [sphereZeroRightHomeomorph]

@[simp]
lemma sphereZeroRightHomeomorph_basepoint :
    sphereZeroRightHomeomorph x₀ (basepoint x₀ (sphereBasepoint.{u} 0)) = x₀ := by
  simp [sphereZeroRightHomeomorph]

@[simp]
lemma sphereZeroRightHomeomorph_symm_apply (x : X) :
    (sphereZeroRightHomeomorph x₀).symm x =
      mk x₀ (sphereBasepoint.{u} 0) (x, sphereAntiBasepoint.{u} 0) := by
  simp [sphereZeroRightHomeomorph]

end SphereZeroUnit

end SmashProduct

section SmashSphere

/-- **The smash product of spheres is a sphere**: `Sᵐ ∧ Sⁿ ≃ₜ Sᵐ⁺ⁿ` for all `m, n ≥ 0`, with the
first `m` cube coordinates followed by the last `n` cube coordinates. -/
def smashSphereHomeomorph (m n : ℕ) :
    SmashProduct (sphereBasepoint.{u} m) (sphereBasepoint.{u} n) ≃ₜ TopCat.sphere.{u} (m + n) :=
  (SmashProduct.congrHomeomorph
    (cubeQuotientSphereHomeomorph.{u} m).symm (cubeQuotientSphereHomeomorph.{u} n).symm
    (cubeQuotientSphereHomeomorph_symm_sphereBasepoint m)
    (cubeQuotientSphereHomeomorph_symm_sphereBasepoint n)).trans <|
    (TopPair.ordinaryPairQuotientProdHomeomorph
      (ULift.down ⁻¹' Cube.boundary (Fin m))
      (ULift.down ⁻¹' Cube.boundary (Fin n))).symm.trans <|
      (TopPair.ordinaryPairQuotientCongrHomeomorph (cubeBoundaryPairProdIso.{u} m n)).trans
        (cubeQuotientSphereHomeomorph.{u} (m + n))

@[simp]
lemma smashSphereHomeomorph_basepoint (m n : ℕ) :
    smashSphereHomeomorph.{u} m n
      (SmashProduct.basepoint (sphereBasepoint.{u} m) (sphereBasepoint.{u} n)) =
      sphereBasepoint.{u} (m + n) := by
  simp only [smashSphereHomeomorph, Homeomorph.trans_apply, SmashProduct.congrHomeomorph_basepoint]
  rw [TopPair.ordinaryPairQuotientProdHomeomorph_symm_basepoint]; simp

/-- **Cube-concatenation formula for `TauCeti.smashSphereHomeomorph`**: the composite
`Iᵐ × Iⁿ → Sᵐ ∧ Sⁿ → Sᵐ⁺ⁿ` is `TauCeti.basedCubeToSphere (m + n)` composed with `Fin.append`. -/
@[simp]
lemma smashSphereHomeomorph_mk_basedCubeToSphere (m n : ℕ) (x : I^(Fin m)) (y : I^(Fin n)) :
    smashSphereHomeomorph.{u} m n
      (SmashProduct.mk (sphereBasepoint.{u} m) (sphereBasepoint.{u} n)
        (basedCubeToSphere.{u} m x, basedCubeToSphere.{u} n y)) =
      basedCubeToSphere.{u} (m + n) (Fin.append x y) := by
  dsimp only [smashSphereHomeomorph, Homeomorph.trans_apply]
  rw [SmashProduct.congrHomeomorph_mk, cubeQuotientSphereHomeomorph_symm_basedCubeToSphere,
    cubeQuotientSphereHomeomorph_symm_basedCubeToSphere]
  simp only [TopPair.ordinaryPairQuotientProdHomeomorph_symm_mk_π _ _,
    ordinaryPairQuotientCongrHomeomorph_cubeBoundaryPairProdIso_π m n x y,
    cubeQuotientSphereHomeomorph_π]

/-- Swapping factors on `Sᵐ ∧ Sⁿ` reverses the order of cube concatenation from `Fin.append x y` to
`Fin.append y x`. -/
lemma smashSphereHomeomorph_comm_mk_basedCubeToSphere (m n : ℕ) (x : I^(Fin m)) (y : I^(Fin n)) :
    smashSphereHomeomorph.{u} n m
      (SmashProduct.comm (sphereBasepoint.{u} m) (sphereBasepoint.{u} n)
        (SmashProduct.mk (sphereBasepoint.{u} m) (sphereBasepoint.{u} n)
           (basedCubeToSphere.{u} m x, basedCubeToSphere.{u} n y))) =
      basedCubeToSphere.{u} (n + m) (Fin.append y x) := by
  rw [SmashProduct.comm_mk, smashSphereHomeomorph_mk_basedCubeToSphere]

/-- **Uniqueness from the based cube maps**: any two functions out of `Sᵐ ∧ Sⁿ` that agree at the
basepoint and on all `basedCubeToSphere m x ∧ basedCubeToSphere n y` are equal. -/
lemma smashSphere_ext {m n : ℕ} {Z : Sort*}
    {f g : SmashProduct (sphereBasepoint.{u} m) (sphereBasepoint.{u} n) → Z}
    (hbase : f (SmashProduct.basepoint _ _) = g (SmashProduct.basepoint _ _))
    (hcube : ∀ (x : I^(Fin m)) (y : I^(Fin n)),
      f (SmashProduct.mk _ _ (basedCubeToSphere.{u} m x, basedCubeToSphere.{u} n y)) =
        g (SmashProduct.mk _ _ (basedCubeToSphere.{u} m x, basedCubeToSphere.{u} n y))) :
    f = g := by
  refine funext <| SmashProduct.ind fun s t ↦ ?_
  by_cases hs : s = sphereBasepoint.{u} m
  · subst hs; simpa using hbase
  by_cases ht : t = sphereBasepoint.{u} n
  · subst ht; simpa using hbase
  obtain ⟨x, rfl⟩ := exists_basedCubeToSphere_eq_of_ne hs
  obtain ⟨y, rfl⟩ := exists_basedCubeToSphere_eq_of_ne ht
  exact hcube x y

/-- **Left `S⁰` unit coherence for `TauCeti.smashSphereHomeomorph`**: `S⁰ ∧ Sⁿ ≃ₜ S⁰⁺ⁿ ≃ₜ Sⁿ`
agrees with `TauCeti.SmashProduct.sphereZeroLeftHomeomorph`. -/
lemma smashSphereHomeomorph_zero_left (n : ℕ) :
    (smashSphereHomeomorph.{u} 0 n).trans (sphereCongrHomeomorph (Nat.zero_add n)) =
      SmashProduct.sphereZeroLeftHomeomorph (sphereBasepoint.{u} n) := by
  refine Homeomorph.ext fun z ↦ congrFun (smashSphere_ext (by simp) fun x y ↦ ?_) z
  rw [Homeomorph.trans_apply, smashSphereHomeomorph_mk_basedCubeToSphere,
    Subsingleton.elim x Fin.elim0]
  simp [Function.comp_def]

/-- **Right `S⁰` unit coherence for `TauCeti.smashSphereHomeomorph`**: `Sᵐ ∧ S⁰ ≃ₜ Sᵐ` agrees
with `TauCeti.SmashProduct.sphereZeroRightHomeomorph`. -/
lemma smashSphereHomeomorph_zero_right (m : ℕ) :
    smashSphereHomeomorph.{u} m 0 =
      SmashProduct.sphereZeroRightHomeomorph (sphereBasepoint.{u} m) := by
  refine Homeomorph.ext fun z ↦ congrFun
    (smashSphere_ext (by simpa using smashSphereHomeomorph_basepoint m 0) fun x y ↦ ?_) z
  rw [smashSphereHomeomorph_mk_basedCubeToSphere, Subsingleton.elim y Fin.elim0]
  simp [Fin.append_elim0]

/-- **Associativity coherence for `TauCeti.smashSphereHomeomorph`**: the two ways of identifying
`(Sᵐ ∧ Sⁿ) ∧ Sᵏ` with `Sᵐ⁺⁽ⁿ⁺ᵏ⁾` via `TauCeti.SmashProduct.assoc` and
`TauCeti.sphereCongrHomeomorph` coincide. -/
lemma smashSphereHomeomorph_assoc (m n k : ℕ) :
    ((SmashProduct.congrHomeomorph (y₀' := sphereBasepoint.{u} k)
        (smashSphereHomeomorph.{u} m n) (Homeomorph.refl (TopCat.sphere.{u} k))
        (smashSphereHomeomorph_basepoint m n)
        (congrFun (Homeomorph.refl_apply _) (sphereBasepoint.{u} k))).trans
      (smashSphereHomeomorph.{u} (m + n) k)).trans
      (sphereCongrHomeomorph (Nat.add_assoc m n k)) =
    (SmashProduct.assoc (sphereBasepoint.{u} m) (sphereBasepoint.{u} n)
        (sphereBasepoint.{u} k)).trans
      ((SmashProduct.congrHomeomorph (x₀' := sphereBasepoint.{u} m)
          (Homeomorph.refl (TopCat.sphere.{u} m)) (smashSphereHomeomorph.{u} n k)
          (congrFun (Homeomorph.refl_apply _) (sphereBasepoint.{u} m))
          (smashSphereHomeomorph_basepoint n k)).trans
        (smashSphereHomeomorph.{u} m (n + k))) := by
  refine Homeomorph.ext <| SmashProduct.ind <| SmashProduct.ind fun u v w ↦ ?_
  by_cases h : (u = sphereBasepoint.{u} m ∨ v = sphereBasepoint.{u} n) ∨ w = sphereBasepoint.{u} k
  · rcases h with (rfl | rfl) | rfl <;> simp
  · push Not at h
    obtain ⟨x', rfl⟩ := exists_basedCubeToSphere_eq_of_ne h.1.1
    obtain ⟨y', rfl⟩ := exists_basedCubeToSphere_eq_of_ne h.1.2
    obtain ⟨z', rfl⟩ := exists_basedCubeToSphere_eq_of_ne h.2
    simp only [Homeomorph.trans_apply, SmashProduct.congrHomeomorph_mk, Homeomorph.refl_apply,
      id_eq, SmashProduct.assoc_mk, smashSphereHomeomorph_mk_basedCubeToSphere,
      sphereCongrHomeomorph_basedCubeToSphere, Fin.append_assoc, Function.comp_def,
      Fin.cast_cast, Fin.cast_eq_self]

end SmashSphere

section ReducedSuspensionSphere

/-- The isomorphism of pairs `(I, {0, 1}) ≅ (I¹, ∂I¹)`. -/
def intervalEndpointPairIsoCubeOne :
    intervalEndpointPair.{u} ≅ cubeBoundaryPair.{u} 1 :=
  TopPair.ofSubsetIso (X := TopCat.of (ULift.{u} I)) (Y := TopCat.of (ULift.{u} (I^(Fin 1))))
    (Homeomorph.ulift.trans ((Homeomorph.funUnique (Fin 1) I).symm.trans Homeomorph.ulift.symm))
    fun _ ↦ by simp [Cube.boundary_fin_one_iff, Homeomorph.ulift]

/-- **The pointed quotient `I / {0, 1}` is homeomorphic to `TopCat.sphere 1`**, sending `t ∈ I` to
`basedCubeToSphere 1 (fun _ ↦ t)`. -/
def intervalQuotientSphereOneHomeomorph :
    intervalEndpointPair.{u}.ordinaryPairQuotient ≃ₜ TopCat.sphere.{u} 1 :=
  (TopPair.ordinaryPairQuotientCongrHomeomorph intervalEndpointPairIsoCubeOne.{u}).trans
    (cubeQuotientSphereHomeomorph.{u} 1)

@[simp]
lemma intervalQuotientSphereOneHomeomorph_π (t : I) :
    intervalQuotientSphereOneHomeomorph.{u}
      (intervalEndpointPair.{u}.ordinaryPairQuotientπ (ULift.up t)) =
      basedCubeToSphere.{u} 1 (fun _ ↦ t) := by
  have h₁ : TopPair.Hom.fst intervalEndpointPairIsoCubeOne.{u}.hom (ULift.up t) =
      ULift.up fun _ ↦ t := by
    rw [intervalEndpointPairIsoCubeOne]
    apply TopPair.ofSubsetIso_hom_fst_apply
  exact (congrArg (cubeQuotientSphereHomeomorph.{u} 1)
    ((TopPair.ordinaryPairQuotientCongrHomeomorph_π intervalEndpointPairIsoCubeOne.{u}
      (ULift.up t)).trans (congrArg _ h₁))).trans (cubeQuotientSphereHomeomorph_π 1 _)

@[simp]
lemma intervalQuotientSphereOneHomeomorph_basepoint :
    intervalQuotientSphereOneHomeomorph.{u}
      intervalEndpointPair.{u}.ordinaryPairQuotientBasepoint = sphereBasepoint.{u} 1 := by
  simp [intervalQuotientSphereOneHomeomorph]

/-- **The reduced suspension of `Sⁿ` is `Sⁿ⁺¹`** for all `n ≥ 0`, with the interval coordinate
placed last: `ΣSⁿ ≃ₜ Sⁿ ∧ (I / {0, 1}) ≃ₜ Sⁿ ∧ S¹ ≃ₜ Sⁿ⁺¹`. -/
def reducedSuspensionSphereHomeomorph (n : ℕ) :
    ReducedSuspension (TopCat.sphere.{u} n) (sphereBasepoint.{u} n) ≃ₜ TopCat.sphere.{u} (n + 1) :=
  (ReducedSuspension.homeomorphSmashIntervalQuotient (sphereBasepoint.{u} n)).trans <|
    (SmashProduct.congrHomeomorph (x₀' := sphereBasepoint.{u} n)
      (Homeomorph.refl (TopCat.sphere.{u} n)) intervalQuotientSphereOneHomeomorph.{u}
      (congrFun (Homeomorph.refl_apply _) (sphereBasepoint.{u} n))
      intervalQuotientSphereOneHomeomorph_basepoint).trans (smashSphereHomeomorph.{u} n 1)

@[simp]
lemma reducedSuspensionSphereHomeomorph_basepoint (n : ℕ) :
    reducedSuspensionSphereHomeomorph.{u} n
      (ReducedSuspension.basepoint :
        ReducedSuspension (TopCat.sphere.{u} n) (sphereBasepoint.{u} n)) =
      sphereBasepoint.{u} (n + 1) := by
  simp [reducedSuspensionSphereHomeomorph]

/-- **Cube-concatenation formula for `TauCeti.reducedSuspensionSphereHomeomorph`**: the composite
`Iⁿ × I → ΣSⁿ → Sⁿ⁺¹` appends the suspension parameter at the end via `Fin.snoc`. -/
@[simp]
lemma reducedSuspensionSphereHomeomorph_mk_basedCubeToSphere (n : ℕ) (x : I^(Fin n)) (t : I) :
    reducedSuspensionSphereHomeomorph.{u} n
      (ReducedSuspension.mk (basedCubeToSphere.{u} n x, t)) =
      basedCubeToSphere.{u} (n + 1) (Fin.snoc x t) := by
  simp [reducedSuspensionSphereHomeomorph, Fin.append_right_eq_snoc]

/-- **Uniqueness of maps out of `ΣSⁿ`** from the based cube map `Iⁿ × I → ΣSⁿ`. -/
lemma reducedSuspensionSphere_ext {n : ℕ} {Z : Sort*}
    {f g : ReducedSuspension (TopCat.sphere.{u} n) (sphereBasepoint.{u} n) → Z}
    (hcube : ∀ (x : I^(Fin n)) (t : I),
      f (ReducedSuspension.mk (basedCubeToSphere.{u} n x, t)) =
        g (ReducedSuspension.mk (basedCubeToSphere.{u} n x, t))) :
    f = g := by
  have hbase : f ReducedSuspension.basepoint = g ReducedSuspension.basepoint := by
    simpa using hcube (fun _ ↦ 0) 0
  refine funext <| ReducedSuspension.ind fun s t ↦ ?_
  by_cases hs : s = sphereBasepoint.{u} n
  · subst hs; simpa using hbase
  · obtain ⟨x, rfl⟩ := exists_basedCubeToSphere_eq_of_ne hs
    exact hcube x t

end ReducedSuspensionSphere

end TauCeti

end
