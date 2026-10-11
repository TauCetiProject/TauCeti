/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.MorphismProperty.LiftingProperty
public import Mathlib.Topology.Category.TopCat.Monoidal
public import Mathlib.Topology.Category.TopCat.Sphere
public import TauCeti.Analysis.Normed.Module.Ball.Homeomorph
public import TauCeti.Topology.Category.TopCat.Pullback
public import TauCeti.Topology.Homotopy.Lifting

/-!
# Serre fibrations

A map `p : E → B` has the *homotopy lifting property* with respect to a space `A` when
every homotopy `H : I × A → B` whose initial map lifts along `p` to `f : A → E` lifts along `p` to
a homotopy `G : I × A → E` starting at `f`.  A *Serre fibration* is a map with the homotopy
lifting property with respect to every disk `Dⁿ`.  Equivalently, it has the right lifting
property with respect to the inclusions `ι₀ : Dⁿ ⟶ Dⁿ ⊗ I` of the disks as the bottoms of their
cylinders, and this is how `TauCeti.TopCat.serreFibrations` is defined, as a
`MorphismProperty` of `TopCat`.  Defining it as a right lifting property makes Mathlib's general
theory of lifting properties apply: Serre fibrations contain the isomorphisms, are closed under
composition, retracts and products, and are stable under base change.

The homotopy lifting property itself, `TauCeti.HasHomotopyLiftingProperty`, is in
`TauCeti.Topology.Homotopy.Lifting`.  Since the closed unit ball of `ℝⁿ` is homeomorphic to the
cube `Iⁿ`, a Serre fibration is equivalently a map with the homotopy lifting property with respect
to every cube (`TauCeti.TopCat.mem_serreFibrations_iff_cube`); cubes are the convenient test spaces
for subdivision arguments.

A map of fibrations is a commutative square, and it induces maps between the fibres
(`CategoryTheory.CommSq.fiberMap`, in `TauCeti.Topology.Category.TopCat.Fiber`).  The base change
of a fibration along a map `g : B' ⟶ B` is again a fibration
(`TauCeti.TopCat.mem_serreFibrations_pullbackFst`), with the same fibres
(`TopCat.Hom.fiberPullbackFstIso`, in `TauCeti.Topology.Category.TopCat.Pullback`).

## Main declarations

* `TauCeti.TopCat.serreFibrations`: Serre fibrations, the right lifting property with respect to
  the inclusions `ι₀ : Dⁿ ⟶ Dⁿ ⊗ I`.
* `TauCeti.TopCat.mem_serreFibrations_iff` and `TauCeti.TopCat.mem_serreFibrations_iff_cube`:
  Serre fibrations are the maps with the homotopy lifting property for every disk, equivalently
  for every cube.
* `IsCoveringMap.mem_serreFibrations` and `TauCeti.TopCat.mem_serreFibrations_fst`: covering
  maps and product projections are Serre fibrations.
* `TauCeti.TopCat.mem_serreFibrations_pullbackFst`: the base change of a Serre fibration is a
  Serre fibration.

## References

* A. Hatcher, [*Algebraic Topology*](https://pi.math.cornell.edu/~hatcher/AT/AT.pdf),
  Section 4.2, the homotopy lifting property and the definition of a fibration.
* J.-P. Serre, *Homologie singulière des espaces fibrés. Applications*, Ann. of Math. 54 (1951).
* The definition of `TauCeti.TopCat.serreFibrations` as the right lifting property with respect
  to a family of morphisms follows Mathlib's `SSet.innerFibrations`.
-/

public section

noncomputable section

open CategoryTheory Limits MorphismProperty MonoidalCategory CartesianMonoidalCategory
  unitInterval

universe u

namespace TauCeti.TopCat

variable {A E B : TopCat.{u}}

/-- A morphism `p` of `TopCat` has the right lifting property with respect to the inclusion
`ι₀ : A ⟶ A ⊗ I` of `A` as the bottom of its cylinder exactly when it has the homotopy lifting
property with respect to `A`. -/
theorem hasLiftingProperty_ι₀_iff {p : E ⟶ B} :
    HasLiftingProperty (TopCat.ι₀ : A ⟶ A ⊗ TopCat.I) p ↔ HasHomotopyLiftingProperty p A := by
  -- `TopCat.I` is a universe lift of `I`, and the cylinder `A ⊗ I` has the interval second.  The
  -- carrier of `A ⊗ I` is only definitionally `A × I`, so both maps are typed through that product.
  let φ : C(I × A, ↑(A ⊗ TopCat.I)) :=
    ⟨fun x ↦ ((x.2, TopCat.I.homeomorph.symm x.1) : ↑A × ↑TopCat.I), by fun_prop⟩
  let ψ : C(↑(A ⊗ TopCat.I), I × A) :=
    (⟨fun x ↦ (TopCat.I.homeomorph x.2, x.1), by fun_prop⟩ : C(↑A × ↑TopCat.I, I × A))
  -- Every remaining step only evaluates morphisms on points of the cylinder.  Those values agree
  -- definitionally: `ι₀ a` is `(a, I.homeomorph.symm 0)`, and `φ` and `ψ` are mutually inverse
  -- because `I.homeomorph` is the universe lift `ULift.down`.
  constructor
  · intro h f H hH
    let top : A ⟶ E := TopCat.ofHom f
    let bot : A ⊗ TopCat.I ⟶ B := TopCat.ofHom (H.comp ψ)
    have sq : CommSq top TopCat.ι₀ p bot := ⟨by ext a; exact (hH a).symm⟩
    refine ⟨sq.lift.hom.comp φ, funext fun x ↦ ?_, fun a ↦ ?_⟩
    · exact ConcreteCategory.congr_hom sq.fac_right (φ x)
    · exact ConcreteCategory.congr_hom sq.fac_left a
  · intro h
    refine ⟨fun {f g} sq ↦ ?_⟩
    obtain ⟨G, hG, hG₀⟩ := h f.hom (g.hom.comp φ) fun a ↦
      (ConcreteCategory.congr_hom sq.w a).symm
    exact ⟨⟨{ l := TopCat.ofHom (G.comp ψ)
              fac_left := by ext a; exact hG₀ a
              fac_right := by ext x; exact congrFun hG (ψ x) }⟩⟩

/-- **Serre fibrations**: the morphisms of `TopCat` with the right lifting property with respect
to the inclusions `ι₀ : Dⁿ ⟶ Dⁿ ⊗ I` of the disks as the bottoms of their cylinders, that is,
with the homotopy lifting property with respect to every disk. -/
def serreFibrations : MorphismProperty TopCat.{u} :=
  (ofHoms fun n : ℕ ↦ (TopCat.ι₀ : TopCat.disk.{u} n ⟶ TopCat.disk n ⊗ TopCat.I)).rlp

instance : serreFibrations.{u}.IsMultiplicative := by unfold serreFibrations; infer_instance

instance : serreFibrations.{u}.RespectsIso := by unfold serreFibrations; infer_instance

instance : serreFibrations.{u}.IsStableUnderBaseChange := by
  unfold serreFibrations; infer_instance

instance : serreFibrations.{u}.IsStableUnderRetracts := by unfold serreFibrations; infer_instance

instance (J : Type*) : serreFibrations.{u}.IsStableUnderProductsOfShape J := by
  unfold serreFibrations; infer_instance

/-- A morphism is a Serre fibration exactly when it has the right lifting property with respect to
every inclusion `ι₀ : Dⁿ ⟶ Dⁿ ⊗ I`. -/
theorem mem_serreFibrations_iff_hasLiftingProperty {p : E ⟶ B} :
    serreFibrations p ↔
      ∀ n : ℕ, HasLiftingProperty (TopCat.ι₀ : TopCat.disk.{u} n ⟶ TopCat.disk n ⊗ TopCat.I) p :=
  ⟨fun h n ↦ h _ (ofHoms.mk n), by rintro h _ _ _ ⟨n⟩; exact h n⟩

/-- A morphism is a Serre fibration exactly when it has the homotopy lifting property with respect
to the closed unit ball of `ℝⁿ` for every `n`. -/
theorem mem_serreFibrations_iff {p : E ⟶ B} :
    serreFibrations p ↔ ∀ n : ℕ,
      HasHomotopyLiftingProperty p (Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) 1) := by
  rw [mem_serreFibrations_iff_hasLiftingProperty]
  refine forall_congr' fun n ↦ ?_
  rw [hasLiftingProperty_ι₀_iff]
  -- `TopCat.disk n` is the universe lift of the closed unit ball
  exact (Homeomorph.ulift : ULift (Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) 1) ≃ₜ _)
    |>.hasHomotopyLiftingProperty_iff

/-- A morphism is a Serre fibration exactly when it has the homotopy lifting property with respect
to the cube `Iⁿ` for every `n`. -/
theorem mem_serreFibrations_iff_cube {p : E ⟶ B} :
    serreFibrations p ↔ ∀ n : ℕ, HasHomotopyLiftingProperty p (Fin n → I) := by
  rw [mem_serreFibrations_iff]
  refine forall_congr' fun n ↦ ?_
  obtain ⟨e⟩ := nonempty_homeomorph_cube_closedBall (EuclideanSpace ℝ (Fin n))
  rw [finrank_euclideanSpace_fin] at e
  exact e.hasHomotopyLiftingProperty_iff.symm

/-- A morphism with the homotopy lifting property with respect to every space in its universe is a
Serre fibration. -/
theorem mem_serreFibrations_of_hasHomotopyLiftingProperty {p : E ⟶ B}
    (h : ∀ (A : Type u) [TopologicalSpace A], HasHomotopyLiftingProperty p A) :
    serreFibrations p :=
  mem_serreFibrations_iff_hasLiftingProperty.2 fun _ ↦ hasLiftingProperty_ι₀_iff.2 (h _)

/-- A Serre fibration lifts paths: a path in `B` starting at `p e` lifts to a path in `E` starting
at `e`. -/
theorem exists_path_lift_of_mem_serreFibrations {p : E ⟶ B} (hp : serreFibrations p) {e : E}
    {b : B} (γ : Path (p e) b) : ∃ Γ : C(I, E), Γ 0 = e ∧ p ∘ Γ = γ :=
  (mem_serreFibrations_iff_cube.1 hp 0).exists_path_lift γ

/-- The projection `B ⊗ F ⟶ B` is a Serre fibration. -/
theorem mem_serreFibrations_fst {B F : TopCat.{u}} : serreFibrations (fst B F) :=
  -- the underlying function of `fst B F` is `Prod.fst` on the carrier `B × F` of `B ⊗ F`
  mem_serreFibrations_of_hasHomotopyLiftingProperty fun A _ ↦
    hasHomotopyLiftingProperty_fst (B := B) F A

/-- The base change `{(b', e) | g b' = p e} ⟶ B'` of a Serre fibration `p` along any map
`g : B' ⟶ B` is a Serre fibration. -/
theorem mem_serreFibrations_pullbackFst {B' : TopCat.{u}} {p : E ⟶ B} (hp : serreFibrations p)
    (g : B' ⟶ B) : serreFibrations (TopCat.pullbackFst g p) :=
  serreFibrations.of_isPullback (IsPullback.of_isLimit (TopCat.pullbackConeIsLimit g p)).flip hp

end TauCeti.TopCat

/-- A covering map is a Serre fibration. -/
theorem IsCoveringMap.mem_serreFibrations {E B : TopCat.{u}} {p : E ⟶ B} (hp : IsCoveringMap p) :
    TauCeti.TopCat.serreFibrations p :=
  TauCeti.TopCat.mem_serreFibrations_of_hasHomotopyLiftingProperty fun A _ ↦
    hp.hasHomotopyLiftingProperty A
