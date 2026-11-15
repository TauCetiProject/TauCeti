/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Sphere.BasedQuotient
public import TauCeti.Topology.ReducedSuspension
import Mathlib.Topology.Homeomorph.Lemmas

/-!
# Smash products and reduced suspensions of spheres

This file constructs the canonical pointed homeomorphisms for spheres equipped with their positive
first-coordinate basepoint `TauCeti.sphereBasepoint`:

* `TauCeti.SmashProduct.sphereZeroLeftHomeomorph`,
  `TauCeti.SmashProduct.sphereZeroRightHomeomorph`: the unit identifications `S⁰ ∧ X ≃ₜ X` and
  `X ∧ S⁰ ≃ₜ X` for any pointed space `(X, x₀)`, sending the nonbasepoint `-e₀` of `S⁰` to the
  identity on `X`.
* `TauCeti.smashSphereHomeomorph`: the pointed homeomorphism `Sᵐ ∧ Sⁿ ≃ₜ Sᵐ⁺ⁿ` for all `m, n ≥ 0`,
  characterized on based cube representatives by coordinate concatenation `Fin.append x y`.
* `TauCeti.intervalQuotientSphereOneHomeomorph`: the pointed homeomorphism `I / {0, 1} ≃ₜ S¹`.
* `TauCeti.reducedSuspensionSphereHomeomorph`: the pointed homeomorphism `ΣSⁿ ≃ₜ Sⁿ⁺¹` for all
  `n ≥ 0`, with the suspension coordinate last (`Fin.snoc x t`), compatible with
  `TauCeti.ReducedSuspension.homeomorphSmashIntervalQuotient` and `TauCeti.smashSphereHomeomorph`.

It also proves that the surjective based cube maps uniquely determine maps out of `Sᵐ ∧ Sⁿ` and
`ΣSⁿ`, and establishes the unit and associativity coherence equations for
`TauCeti.smashSphereHomeomorph`.

## References

* A. Hatcher, [*Algebraic Topology*](https://pi.math.cornell.edu/~hatcher/AT/AT.pdf),
  Chapter 0, "Operations on spaces".
* J. P. May, [*A Concise Course in Algebraic Topology*](https://www.math.uchicago.edu/~may/CONCISE/ConciseRevised.pdf),
  Chapter 8, Sections 8.2–8.3.
-/

public section

noncomputable section

open CategoryTheory Set Topology
open scoped unitInterval

universe u

namespace TauCeti

/-! ### Zero-sphere unit homeomorphisms for arbitrary pointed spaces -/

namespace SmashProduct

section SphereZeroUnit

variable {X : Type u} [TopologicalSpace X] (x₀ : X)

private def sphereZeroLeftRaw : C(TopCat.sphere.{u} 0 × X, X) where
  toFun := open Classical in
    fun p ↦ if p.1 = sphereBasepoint.{u} 0 then x₀ else p.2
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
    (fun x ↦ by classical simp [sphereZeroLeftRaw])
    (fun s ↦ by classical simp [sphereZeroLeftRaw])
  invFun x := mk (sphereBasepoint.{u} 0) x₀ (sphereAntiBasepoint.{u} 0, x)
  left_inv z := by
    induction z using ind with
    | hmk s x =>
      rcases eq_sphereBasepoint_or_eq_sphereAntiBasepoint s with rfl | rfl
      · classical simp [sphereZeroLeftRaw]
      · classical simp [sphereZeroLeftRaw, (sphereBasepoint_ne_sphereAntiBasepoint.{u} 0).symm]
  right_inv x := by
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

/-! ### Dimension cast homeomorphism of spheres -/

/-- Reindexing `TopCat.sphere a` to `TopCat.sphere b` along an equality `h : a = b` of dimensions,
via the coordinate permutation `finCongr` on `EuclideanSpace ℝ (Fin (· + 1))`. -/
def sphereCongrHomeomorph {a b : ℕ} (h : a = b) :
    TopCat.sphere.{u} a ≃ₜ TopCat.sphere.{u} b :=
  Homeomorph.ulift.trans <|
    (((LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ
      (finCongr (congrArg (· + 1) h))).toHomeomorph.subtype fun x ↦ by simp).trans
      Homeomorph.ulift.symm)

@[simp]
lemma sphereCongrHomeomorph_rfl (a : ℕ) :
    sphereCongrHomeomorph (rfl : a = a) = Homeomorph.refl (TopCat.sphere.{u} a) := by
  ext s
  refine ULift.ext (Subtype.ext ?_)
  ext i
  rfl

@[simp]
lemma sphereCongrHomeomorph_sphereBasepoint {a b : ℕ} (h : a = b) :
    sphereCongrHomeomorph.{u} h (sphereBasepoint.{u} a) = sphereBasepoint.{u} b := by
  subst h
  simp

@[simp]
lemma sphereCongrHomeomorph_basedCubeToSphere {a b : ℕ} (h : a = b) (y : I^(Fin a)) :
    sphereCongrHomeomorph.{u} h (basedCubeToSphere.{u} a y) =
      basedCubeToSphere.{u} b (y ∘ Fin.cast h.symm) := by
  subst h
  simp

/-! ### Smash product of spheres `Sᵐ ∧ Sⁿ ≃ₜ Sᵐ⁺ⁿ` -/

section SmashSphere

/-- The isomorphism of pairs `(Iᵐ × Iⁿ, ∂Iᵐ × Iⁿ ∪ Iᵐ × ∂Iⁿ) ≅ (Iᵐ⁺ⁿ, ∂Iᵐ⁺ⁿ)` induced by
`Fin.appendHomeomorph`. -/
def cubeBoundaryPairProdIso (m n : ℕ) :
    TopPair.ofSubset (X := TopCat.of (ULift.{u} (I^(Fin m)) × ULift.{u} (I^(Fin n))))
      ((ULift.down ⁻¹' Cube.boundary (Fin m)) ×ˢ univ ∪
        univ ×ˢ (ULift.down ⁻¹' Cube.boundary (Fin n))) ≅
      cubeBoundaryPair.{u} (m + n) :=
  TopPair.ofSubsetIso
    (X := TopCat.of (ULift.{u} (I^(Fin m)) × ULift.{u} (I^(Fin n))))
    (Y := TopCat.of (ULift.{u} (I^(Fin (m + n)))))
    ((Homeomorph.ulift.prodCongr Homeomorph.ulift).trans
      ((Fin.appendHomeomorph (X := I) m n).trans Homeomorph.ulift.symm))
    fun ⟨_, _⟩ ↦
      ⟨fun h ↦ Cube.append_mem_boundary_iff.2 (h.imp And.left And.right),
       fun h ↦ (Cube.append_mem_boundary_iff.1 h).imp (fun hx ↦ ⟨hx, trivial⟩)
         fun hy ↦ ⟨trivial, hy⟩⟩

@[simp]
lemma ordinaryPairQuotientHomeomorph_cubeBoundaryPairProdIso_π
    (m n : ℕ) (x : I^(Fin m)) (y : I^(Fin n)) :
    TopPair.ordinaryPairQuotientHomeomorph (cubeBoundaryPairProdIso.{u} m n)
      ((TopPair.ofSubset (X := TopCat.of (ULift.{u} (I^(Fin m)) × ULift.{u} (I^(Fin n))))
        ((ULift.down ⁻¹' Cube.boundary (Fin m)) ×ˢ univ ∪
          univ ×ˢ (ULift.down ⁻¹' Cube.boundary (Fin n)))).ordinaryPairQuotientπ
        (ULift.up x, ULift.up y)) =
      (cubeBoundaryPair.{u} (m + n)).ordinaryPairQuotientπ (ULift.up (Fin.append x y)) := by
  let Pprod := TopPair.ofSubset (X := TopCat.of (ULift.{u} (I^(Fin m)) × ULift.{u} (I^(Fin n))))
    ((ULift.down ⁻¹' Cube.boundary (Fin m)) ×ˢ univ ∪
      univ ×ˢ (ULift.down ⁻¹' Cube.boundary (Fin n)))
  refine (TopPair.ordinaryPairQuotientHomeomorph_π (cubeBoundaryPairProdIso.{u} m n)
    (ULift.up x, ULift.up y)).trans ?_
  refine congrArg (cubeBoundaryPair.{u} (m + n)).ordinaryPairQuotientπ ?_
  exact (congrArg (fun f : Pprod ⟶ cubeBoundaryPair.{u} (m + n) ↦
      TopPair.Hom.fst f (ULift.up x, ULift.up y))
    (TopPair.ofSubsetIso_hom _ _)).trans
    (congrArg (fun g : Pprod.fst ⟶ (cubeBoundaryPair.{u} (m + n)).fst ↦
      g (ULift.up x, ULift.up y)) (TopPair.ofSubsetMap_fst _ _))

/-- **The smash product of spheres is a sphere**: `Sᵐ ∧ Sⁿ ≃ₜ Sᵐ⁺ⁿ` for all `m, n ≥ 0`, with the
first `m` cube coordinates followed by the last `n` cube coordinates. -/
def smashSphereHomeomorph (m n : ℕ) :
    SmashProduct (sphereBasepoint.{u} m) (sphereBasepoint.{u} n) ≃ₜ TopCat.sphere.{u} (m + n) :=
  (SmashProduct.congrHomeomorph
    (cubeQuotientSphereHomeomorph.{u} m).symm
    (cubeQuotientSphereHomeomorph.{u} n).symm
    (cubeQuotientSphereHomeomorph_symm_sphereBasepoint m)
    (cubeQuotientSphereHomeomorph_symm_sphereBasepoint n)).trans <|
    (TopPair.ordinaryPairQuotientProdHomeomorph
      (ULift.down ⁻¹' Cube.boundary (Fin m))
      (ULift.down ⁻¹' Cube.boundary (Fin n))).symm.trans <|
      (TopPair.ordinaryPairQuotientHomeomorph (cubeBoundaryPairProdIso.{u} m n)).trans
        (cubeQuotientSphereHomeomorph.{u} (m + n))

@[simp]
lemma smashSphereHomeomorph_basepoint (m n : ℕ) :
    smashSphereHomeomorph.{u} m n
      (SmashProduct.basepoint (sphereBasepoint.{u} m) (sphereBasepoint.{u} n)) =
      sphereBasepoint.{u} (m + n) := by
  let e₁ := SmashProduct.congrHomeomorph
    (cubeQuotientSphereHomeomorph.{u} m).symm
    (cubeQuotientSphereHomeomorph.{u} n).symm
    (cubeQuotientSphereHomeomorph_symm_sphereBasepoint m)
    (cubeQuotientSphereHomeomorph_symm_sphereBasepoint n)
  let e₂ := (TopPair.ordinaryPairQuotientProdHomeomorph
    (ULift.down ⁻¹' Cube.boundary (Fin m))
    (ULift.down ⁻¹' Cube.boundary (Fin n))).symm
  let e₃ := TopPair.ordinaryPairQuotientHomeomorph (cubeBoundaryPairProdIso.{u} m n)
  let e₄ := cubeQuotientSphereHomeomorph.{u} (m + n)
  calc e₄ (e₃ (e₂ (e₁ (SmashProduct.basepoint _ _))))
    _ = e₄ (e₃ (e₂ (SmashProduct.basepoint _ _))) :=
        congrArg (fun z ↦ e₄ (e₃ (e₂ z))) (SmashProduct.congrHomeomorph_basepoint _ _ _ _)
    _ = e₄ (e₃ _) :=
        congrArg (fun z ↦ e₄ (e₃ z))
          (TopPair.ordinaryPairQuotientProdHomeomorph_symm_basepoint _ _)
    _ = e₄ (cubeBoundaryPair.{u} (m + n)).ordinaryPairQuotientBasepoint :=
        congrArg e₄ (TopPair.ordinaryPairQuotientHomeomorph_basepoint _)
    _ = sphereBasepoint.{u} (m + n) := cubeQuotientSphereHomeomorph_basepoint (m + n)

/-- **Cube-concatenation formula for `TauCeti.smashSphereHomeomorph`**: the composite
`Iᵐ × Iⁿ → Sᵐ ∧ Sⁿ → Sᵐ⁺ⁿ` is `TauCeti.basedCubeToSphere (m + n)` composed with `Fin.append`. -/
@[simp]
lemma smashSphereHomeomorph_mk_basedCubeToSphere (m n : ℕ) (x : I^(Fin m)) (y : I^(Fin n)) :
    smashSphereHomeomorph.{u} m n
      (SmashProduct.mk (sphereBasepoint.{u} m) (sphereBasepoint.{u} n)
        (basedCubeToSphere.{u} m x, basedCubeToSphere.{u} n y)) =
      basedCubeToSphere.{u} (m + n) (Fin.append x y) := by
  let e₁ := SmashProduct.congrHomeomorph
    (cubeQuotientSphereHomeomorph.{u} m).symm
    (cubeQuotientSphereHomeomorph.{u} n).symm
    (cubeQuotientSphereHomeomorph_symm_sphereBasepoint m)
    (cubeQuotientSphereHomeomorph_symm_sphereBasepoint n)
  let e₂ := (TopPair.ordinaryPairQuotientProdHomeomorph
    (ULift.down ⁻¹' Cube.boundary (Fin m))
    (ULift.down ⁻¹' Cube.boundary (Fin n))).symm
  let e₃ := TopPair.ordinaryPairQuotientHomeomorph (cubeBoundaryPairProdIso.{u} m n)
  let e₄ := cubeQuotientSphereHomeomorph.{u} (m + n)
  have h₁ : e₁ (SmashProduct.mk (sphereBasepoint.{u} m) (sphereBasepoint.{u} n)
      (basedCubeToSphere.{u} m x, basedCubeToSphere.{u} n y)) =
      SmashProduct.mk _ _
        ((cubeBoundaryPair.{u} m).ordinaryPairQuotientπ (ULift.up x),
          (cubeBoundaryPair.{u} n).ordinaryPairQuotientπ (ULift.up y)) := by
    rw [SmashProduct.congrHomeomorph_mk, cubeQuotientSphereHomeomorph_symm_basedCubeToSphere,
      cubeQuotientSphereHomeomorph_symm_basedCubeToSphere]
  calc e₄ (e₃ (e₂ (e₁ (SmashProduct.mk _ _
        (basedCubeToSphere.{u} m x, basedCubeToSphere.{u} n y)))))
    _ = e₄ (e₃ (e₂ (SmashProduct.mk _ _
          ((cubeBoundaryPair.{u} m).ordinaryPairQuotientπ (ULift.up x),
            (cubeBoundaryPair.{u} n).ordinaryPairQuotientπ (ULift.up y))))) :=
        congrArg (fun z ↦ e₄ (e₃ (e₂ z))) h₁
    _ = e₄ (e₃ _) :=
        congrArg (fun z ↦ e₄ (e₃ z))
          (TopPair.ordinaryPairQuotientProdHomeomorph_symm_mk_π _ _ (ULift.up x) (ULift.up y))
    _ = e₄ ((cubeBoundaryPair.{u} (m + n)).ordinaryPairQuotientπ (ULift.up (Fin.append x y))) :=
        congrArg e₄ (ordinaryPairQuotientHomeomorph_cubeBoundaryPairProdIso_π m n x y)
    _ = basedCubeToSphere.{u} (m + n) (Fin.append x y) :=
        cubeQuotientSphereHomeomorph_π (m + n) (ULift.up (Fin.append x y))

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
  funext z
  induction z using SmashProduct.ind with
  | hmk s t =>
    by_cases hs : s = sphereBasepoint.{u} m
    · subst hs
      simpa using hbase
    · by_cases ht : t = sphereBasepoint.{u} n
      · subst ht
        simpa using hbase
      · obtain ⟨x, rfl⟩ := exists_basedCubeToSphere_eq_of_ne hs
        obtain ⟨y, rfl⟩ := exists_basedCubeToSphere_eq_of_ne ht
        exact hcube x y

/-- **Left `S⁰` unit coherence for `TauCeti.smashSphereHomeomorph`**: `S⁰ ∧ Sⁿ ≃ₜ S⁰⁺ⁿ ≃ₜ Sⁿ`
agrees with `TauCeti.SmashProduct.sphereZeroLeftHomeomorph`. -/
lemma smashSphereHomeomorph_zero_left (n : ℕ) :
    (smashSphereHomeomorph.{u} 0 n).trans (sphereCongrHomeomorph (Nat.zero_add n)) =
      SmashProduct.sphereZeroLeftHomeomorph (sphereBasepoint.{u} n) := by
  refine Homeomorph.ext fun z ↦ congrFun (smashSphere_ext ?_ ?_) z
  · simp
  · intro x y
    have hx : x = Fin.elim0 := Subsingleton.elim _ _
    subst hx
    rw [Homeomorph.trans_apply, smashSphereHomeomorph_mk_basedCubeToSphere,
      sphereCongrHomeomorph_basedCubeToSphere, basedCubeToSphere_zero_apply,
      SmashProduct.sphereZeroLeftHomeomorph_mk_antiBasepoint, Fin.elim0_append]
    exact congrArg (basedCubeToSphere.{u} n) (funext fun _ ↦ rfl)

/-- **Right `S⁰` unit coherence for `TauCeti.smashSphereHomeomorph`**: `Sᵐ ∧ S⁰ ≃ₜ Sᵐ` agrees
with `TauCeti.SmashProduct.sphereZeroRightHomeomorph`. -/
lemma smashSphereHomeomorph_zero_right (m : ℕ) :
    smashSphereHomeomorph.{u} m 0 =
      SmashProduct.sphereZeroRightHomeomorph (sphereBasepoint.{u} m) := by
  refine Homeomorph.ext fun z ↦ congrFun (smashSphere_ext ?_ ?_) z
  · exact (smashSphereHomeomorph_basepoint m 0).trans
      (SmashProduct.sphereZeroRightHomeomorph_basepoint (sphereBasepoint.{u} m)).symm
  · intro x y
    have hy : y = Fin.elim0 := Subsingleton.elim _ _
    subst hy
    rw [smashSphereHomeomorph_mk_basedCubeToSphere, basedCubeToSphere_zero_apply,
      SmashProduct.sphereZeroRightHomeomorph_mk_antiBasepoint, Fin.append_elim0]
    exact congrArg (basedCubeToSphere.{u} m) (funext fun _ ↦ rfl)

private lemma smashSphereHomeomorph_assoc_basepoint (m n k : ℕ) :
    (((SmashProduct.congrHomeomorph (y₀' := sphereBasepoint.{u} k)
        (smashSphereHomeomorph.{u} m n)
        (Homeomorph.refl (TopCat.sphere.{u} k))
        (smashSphereHomeomorph_basepoint m n)
        (congrFun (Homeomorph.refl_apply _) (sphereBasepoint.{u} k))).trans
      (smashSphereHomeomorph.{u} (m + n) k)).trans
      (sphereCongrHomeomorph (Nat.add_assoc m n k)))
      (SmashProduct.basepoint _ _) =
    ((SmashProduct.assoc (sphereBasepoint.{u} m) (sphereBasepoint.{u} n)
        (sphereBasepoint.{u} k)).trans
      ((SmashProduct.congrHomeomorph (x₀' := sphereBasepoint.{u} m)
          (Homeomorph.refl (TopCat.sphere.{u} m))
          (smashSphereHomeomorph.{u} n k)
          (congrFun (Homeomorph.refl_apply _) (sphereBasepoint.{u} m))
          (smashSphereHomeomorph_basepoint n k)).trans
        (smashSphereHomeomorph.{u} m (n + k))))
      (SmashProduct.basepoint _ _) := by
  rw [Homeomorph.trans_apply, Homeomorph.trans_apply, SmashProduct.congrHomeomorph_basepoint,
    smashSphereHomeomorph_basepoint, sphereCongrHomeomorph_sphereBasepoint,
    Homeomorph.trans_apply, Homeomorph.trans_apply, SmashProduct.assoc_basepoint,
    SmashProduct.congrHomeomorph_basepoint, smashSphereHomeomorph_basepoint]

/-- **Associativity coherence for `TauCeti.smashSphereHomeomorph`**: the two ways of identifying
`(Sᵐ ∧ Sⁿ) ∧ Sᵏ` with `Sᵐ⁺⁽ⁿ⁺ᵏ⁾` via `TauCeti.SmashProduct.assoc` and
`TauCeti.sphereCongrHomeomorph` coincide. -/
lemma smashSphereHomeomorph_assoc (m n k : ℕ) :
    ((SmashProduct.congrHomeomorph (y₀' := sphereBasepoint.{u} k)
        (smashSphereHomeomorph.{u} m n)
        (Homeomorph.refl (TopCat.sphere.{u} k))
        (smashSphereHomeomorph_basepoint m n)
        (congrFun (Homeomorph.refl_apply _) (sphereBasepoint.{u} k))).trans
      (smashSphereHomeomorph.{u} (m + n) k)).trans
      (sphereCongrHomeomorph (Nat.add_assoc m n k)) =
    (SmashProduct.assoc (sphereBasepoint.{u} m) (sphereBasepoint.{u} n)
        (sphereBasepoint.{u} k)).trans
      ((SmashProduct.congrHomeomorph (x₀' := sphereBasepoint.{u} m)
          (Homeomorph.refl (TopCat.sphere.{u} m))
          (smashSphereHomeomorph.{u} n k)
          (congrFun (Homeomorph.refl_apply _) (sphereBasepoint.{u} m))
          (smashSphereHomeomorph_basepoint n k)).trans
        (smashSphereHomeomorph.{u} m (n + k))) := by
  refine Homeomorph.ext fun z ↦ ?_
  induction z using SmashProduct.ind with
  | hmk uv w =>
    induction uv using SmashProduct.ind with
    | hmk u v =>
      by_cases hu : u = sphereBasepoint.{u} m
      · subst hu
        rw [SmashProduct.mk_basepoint_left, SmashProduct.mk_basepoint_left]
        exact smashSphereHomeomorph_assoc_basepoint m n k
      · by_cases hv : v = sphereBasepoint.{u} n
        · subst hv
          rw [SmashProduct.mk_basepoint_right, SmashProduct.mk_basepoint_left]
          exact smashSphereHomeomorph_assoc_basepoint m n k
        · by_cases hw : w = sphereBasepoint.{u} k
          · subst hw
            rw [SmashProduct.mk_basepoint_right]
            exact smashSphereHomeomorph_assoc_basepoint m n k
          · obtain ⟨x', rfl⟩ := exists_basedCubeToSphere_eq_of_ne hu
            obtain ⟨y', rfl⟩ := exists_basedCubeToSphere_eq_of_ne hv
            obtain ⟨z', rfl⟩ := exists_basedCubeToSphere_eq_of_ne hw
            rw [Homeomorph.trans_apply, Homeomorph.trans_apply, SmashProduct.congrHomeomorph_mk,
              Homeomorph.refl_apply, id_eq, smashSphereHomeomorph_mk_basedCubeToSphere,
              smashSphereHomeomorph_mk_basedCubeToSphere, sphereCongrHomeomorph_basedCubeToSphere,
              Homeomorph.trans_apply, Homeomorph.trans_apply, SmashProduct.assoc_mk,
              SmashProduct.congrHomeomorph_mk, Homeomorph.refl_apply, id_eq,
              smashSphereHomeomorph_mk_basedCubeToSphere,
              smashSphereHomeomorph_mk_basedCubeToSphere, Fin.append_assoc]
            exact congrArg (basedCubeToSphere.{u} (m + (n + k))) (funext fun _ ↦ rfl)

end SmashSphere

/-! ### Reduced suspension of spheres `ΣSⁿ ≃ₜ Sⁿ⁺¹` -/

section ReducedSuspensionSphere

/-- The isomorphism of pairs `(I, {0, 1}) ≅ (I¹, ∂I¹)`. -/
def intervalEndpointPairIsoCubeOne :
    intervalEndpointPair.{u} ≅ cubeBoundaryPair.{u} 1 :=
  TopPair.ofSubsetIso
    (X := TopCat.of (ULift.{u} I))
    (Y := TopCat.of (ULift.{u} (I^(Fin 1))))
    (Homeomorph.ulift.trans
      ((Homeomorph.funUnique (Fin 1) I).symm.trans Homeomorph.ulift.symm))
    fun _ ↦ ⟨fun h ↦ Cube.boundary_fin_one_iff.2 h, fun h ↦ Cube.boundary_fin_one_iff.1 h⟩

/-- **The pointed quotient `I / {0, 1}` is homeomorphic to `TopCat.sphere 1`**, sending `t ∈ I` to
`basedCubeToSphere 1 (fun _ ↦ t)`. -/
def intervalQuotientSphereOneHomeomorph :
    intervalEndpointPair.{u}.ordinaryPairQuotient ≃ₜ TopCat.sphere.{u} 1 :=
  (TopPair.ordinaryPairQuotientHomeomorph intervalEndpointPairIsoCubeOne.{u}).trans
    (cubeQuotientSphereHomeomorph.{u} 1)

@[simp]
lemma intervalQuotientSphereOneHomeomorph_π (t : I) :
    intervalQuotientSphereOneHomeomorph.{u}
      (intervalEndpointPair.{u}.ordinaryPairQuotientπ (ULift.up t)) =
      basedCubeToSphere.{u} 1 (fun _ ↦ t) := by
  let e₁ := TopPair.ordinaryPairQuotientHomeomorph intervalEndpointPairIsoCubeOne.{u}
  have h₁ : e₁ (intervalEndpointPair.{u}.ordinaryPairQuotientπ (ULift.up t)) =
      (cubeBoundaryPair.{u} 1).ordinaryPairQuotientπ (ULift.up fun _ ↦ t) := by
    refine (TopPair.ordinaryPairQuotientHomeomorph_π intervalEndpointPairIsoCubeOne.{u}
      (ULift.up t)).trans ?_
    refine congrArg (cubeBoundaryPair.{u} 1).ordinaryPairQuotientπ ?_
    exact (congrArg (fun f : intervalEndpointPair.{u} ⟶ cubeBoundaryPair.{u} 1 ↦
        TopPair.Hom.fst f (ULift.up t))
      (TopPair.ofSubsetIso_hom _ _)).trans
      (congrArg (fun g : intervalEndpointPair.{u}.fst ⟶ (cubeBoundaryPair.{u} 1).fst ↦
        g (ULift.up t)) (TopPair.ofSubsetMap_fst _ _))
  exact (congrArg (cubeQuotientSphereHomeomorph.{u} 1) h₁).trans
    (cubeQuotientSphereHomeomorph_π 1 (ULift.up fun _ ↦ t))

@[simp]
lemma intervalQuotientSphereOneHomeomorph_basepoint :
    intervalQuotientSphereOneHomeomorph.{u}
      intervalEndpointPair.{u}.ordinaryPairQuotientBasepoint = sphereBasepoint.{u} 1 :=
  (congrArg (cubeQuotientSphereHomeomorph.{u} 1)
    (TopPair.ordinaryPairQuotientHomeomorph_basepoint intervalEndpointPairIsoCubeOne.{u})).trans
    (cubeQuotientSphereHomeomorph_basepoint 1)

/-- **The reduced suspension of `Sⁿ` is `Sⁿ⁺¹`** for all `n ≥ 0`, with the interval coordinate
placed last: `ΣSⁿ ≃ₜ Sⁿ ∧ (I / {0, 1}) ≃ₜ Sⁿ ∧ S¹ ≃ₜ Sⁿ⁺¹`. -/
def reducedSuspensionSphereHomeomorph (n : ℕ) :
    ReducedSuspension (sphereBasepoint.{u} n) ≃ₜ TopCat.sphere.{u} (n + 1) :=
  (ReducedSuspension.homeomorphSmashIntervalQuotient (sphereBasepoint.{u} n)).trans <|
    (SmashProduct.congrHomeomorph (x₀' := sphereBasepoint.{u} n)
      (Homeomorph.refl (TopCat.sphere.{u} n))
      intervalQuotientSphereOneHomeomorph.{u}
      (congrFun (Homeomorph.refl_apply _) (sphereBasepoint.{u} n))
      intervalQuotientSphereOneHomeomorph_basepoint).trans
      (smashSphereHomeomorph.{u} n 1)

@[simp]
lemma reducedSuspensionSphereHomeomorph_basepoint (n : ℕ) :
    reducedSuspensionSphereHomeomorph.{u} n
      (ReducedSuspension.basepoint (sphereBasepoint.{u} n)) =
      sphereBasepoint.{u} (n + 1) := by
  let e₁ := ReducedSuspension.homeomorphSmashIntervalQuotient (sphereBasepoint.{u} n)
  let e₂ := SmashProduct.congrHomeomorph (x₀' := sphereBasepoint.{u} n)
    (Homeomorph.refl (TopCat.sphere.{u} n))
    intervalQuotientSphereOneHomeomorph.{u}
    (congrFun (Homeomorph.refl_apply _) (sphereBasepoint.{u} n))
    intervalQuotientSphereOneHomeomorph_basepoint
  let e₃ := smashSphereHomeomorph.{u} n 1
  calc e₃ (e₂ (e₁ (ReducedSuspension.basepoint (sphereBasepoint.{u} n))))
    _ = e₃ (e₂ (SmashProduct.basepoint _ _)) :=
        congrArg (fun z ↦ e₃ (e₂ z))
          (ReducedSuspension.homeomorphSmashIntervalQuotient_basepoint _)
    _ = e₃ (SmashProduct.basepoint _ _) :=
        congrArg e₃ (SmashProduct.congrHomeomorph_basepoint _ _ _ _)
    _ = sphereBasepoint.{u} (n + 1) := smashSphereHomeomorph_basepoint n 1

/-- **Cube-concatenation formula for `TauCeti.reducedSuspensionSphereHomeomorph`**: the composite
`Iⁿ × I → ΣSⁿ → Sⁿ⁺¹` appends the suspension parameter at the end via `Fin.snoc`. -/
@[simp]
lemma reducedSuspensionSphereHomeomorph_mk_basedCubeToSphere (n : ℕ) (x : I^(Fin n)) (t : I) :
    reducedSuspensionSphereHomeomorph.{u} n
      (ReducedSuspension.mk (sphereBasepoint.{u} n) (basedCubeToSphere.{u} n x, t)) =
      basedCubeToSphere.{u} (n + 1) (Fin.snoc x t) := by
  let e₁ := ReducedSuspension.homeomorphSmashIntervalQuotient (sphereBasepoint.{u} n)
  let e₂ := SmashProduct.congrHomeomorph (x₀' := sphereBasepoint.{u} n)
    (Homeomorph.refl (TopCat.sphere.{u} n))
    intervalQuotientSphereOneHomeomorph.{u}
    (congrFun (Homeomorph.refl_apply _) (sphereBasepoint.{u} n))
    intervalQuotientSphereOneHomeomorph_basepoint
  let e₃ := smashSphereHomeomorph.{u} n 1
  calc e₃ (e₂ (e₁ (ReducedSuspension.mk (sphereBasepoint.{u} n) (basedCubeToSphere.{u} n x, t))))
    _ = e₃ (e₂ (SmashProduct.mk _ _
          (basedCubeToSphere.{u} n x,
            intervalEndpointPair.{u}.ordinaryPairQuotientπ (ULift.up t)))) :=
        congrArg (fun z ↦ e₃ (e₂ z))
          (ReducedSuspension.homeomorphSmashIntervalQuotient_mk _ _ t)
    _ = e₃ (SmashProduct.mk _ _
          (basedCubeToSphere.{u} n x, basedCubeToSphere.{u} 1 (fun _ ↦ t))) :=
        (congrArg e₃ (SmashProduct.congrHomeomorph_mk _ _ _ _ _ _)).trans
          (congrArg (fun b ↦ e₃ (SmashProduct.mk _ _ (basedCubeToSphere.{u} n x, b)))
            (intervalQuotientSphereOneHomeomorph_π t))
    _ = basedCubeToSphere.{u} (n + 1) (Fin.append x (fun _ : Fin 1 ↦ t)) :=
        smashSphereHomeomorph_mk_basedCubeToSphere n 1 x (fun _ ↦ t)
    _ = basedCubeToSphere.{u} (n + 1) (Fin.snoc x t) := by
        rw [Fin.append_right_eq_snoc]

/-- **Uniqueness of maps out of `ΣSⁿ`** from the based cube map `Iⁿ × I → ΣSⁿ`. -/
lemma reducedSuspensionSphere_ext {n : ℕ} {Z : Sort*}
    {f g : ReducedSuspension (sphereBasepoint.{u} n) → Z}
    (hcube : ∀ (x : I^(Fin n)) (t : I),
      f (ReducedSuspension.mk (sphereBasepoint.{u} n) (basedCubeToSphere.{u} n x, t)) =
        g (ReducedSuspension.mk (sphereBasepoint.{u} n) (basedCubeToSphere.{u} n x, t))) :
    f = g := by
  have hbase : f (ReducedSuspension.basepoint (sphereBasepoint.{u} n)) =
      g (ReducedSuspension.basepoint (sphereBasepoint.{u} n)) := by
    have h0 := hcube (fun _ ↦ 0) 0
    rwa [ReducedSuspension.mk_zero] at h0
  funext z
  induction z using ReducedSuspension.ind with
  | hmk s t =>
    by_cases hs : s = sphereBasepoint.{u} n
    · subst hs
      simpa using hbase
    · obtain ⟨x, rfl⟩ := exists_basedCubeToSphere_eq_of_ne hs
      exact hcube x t

end ReducedSuspensionSphere

end TauCeti

end
