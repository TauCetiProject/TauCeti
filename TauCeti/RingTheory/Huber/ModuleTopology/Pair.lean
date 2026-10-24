/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.RingHom.Etale
public import TauCeti.RingTheory.Huber.ModuleTopology.FiniteAlgebra
public import TauCeti.RingTheory.Huber.Pair
import Mathlib.Topology.Algebra.Algebra
import TauCeti.RingTheory.IntegralClosure.IntegrallyClosed

/-!
# The Huber pair of a finite algebra

Let `(A, A⁺)` be a Huber pair and `B` a commutative `A`-algebra, finite as an `A`-module and
carrying its natural topology (`IsModuleTopology A B`), so that `B` is a Huber ring
(`TauCeti.Huber.IsHuberRing.of_isModuleTopology`). The integral closure `B⁺` of the image of
`A⁺` in `B` is a ring of integral elements, which makes `(B, B⁺)` a Huber pair and
`A → B` a morphism of Huber pairs. Every `A`-algebra map from `B` to a Huber pair under `(A, A⁺)`
is a morphism of Huber pairs, so `(B, B⁺)` is the pair that finite étale geometry attaches to a
finite étale algebra. The plus ring is the integral closure of the image of `A⁺`, which need not
equal `B°`: already for `B = A` they differ when `A⁺ ≠ A°`.

No completeness, separatedness, noetherian or étaleness hypothesis is needed for the construction
and its universal property; completeness of `B` over a complete base is
`TauCeti.completeSpace_moduleTopology`, and separatedness over a Hausdorff base for projective `B`
is `TauCeti.t2Space_moduleTopology_of_projective`.

## Main definitions

* `TauCeti.Huber.Pair.finiteAlgebra`: the Huber pair `(B, B⁺)`, with `B⁺` the integral closure of
  the image of `A⁺`.
* `TauCeti.Huber.Pair.finiteAlgebra.algebraHom`: the morphism `(A, A⁺) → (B, B⁺)`.
* `TauCeti.Huber.Pair.finiteAlgebra.lift`: an `A`-algebra map `B → D` into a Huber pair `(D, D⁺)`
  under `(A, A⁺)`, as a morphism of Huber pairs.
* `TauCeti.Huber.Pair.Hom.IsFiniteEtale`: a morphism of Huber pairs `(A, A⁺) → (B, B⁺)` is finite
  étale if `A → B` is finite étale, `B` carries its natural `A`-module topology, and `B⁺` is the
  integral closure of the image of `A⁺`.

## Main results

* `TauCeti.Huber.Pair.finiteAlgebra_self`: the Huber pair of `A` itself is `(A, A⁺)`.
* `TauCeti.Huber.Pair.finiteAlgebra.homEquiv`: morphisms of Huber pairs `(B, B⁺) → (D, D⁺)` under
  `(A, A⁺)` are exactly the `A`-algebra maps `B → D`.
* `TauCeti.Huber.Pair.finiteAlgebra.isFiniteEtale_algebraHom`: for finite étale `B`, the structure
  morphism `(A, A⁺) → (B, B⁺)` is finite étale.
* `TauCeti.Huber.Pair.Hom.IsFiniteEtale.exists_hom`: every ring map out of the target of a finite
  étale morphism of Huber pairs that is compatible with morphisms of Huber pairs out of the source
  is itself a morphism of Huber pairs.

## References

* R. Huber, *Étale cohomology of rigid analytic varieties and adic spaces*, Aspects of
  Mathematics E30 (1996), §1.4, (1.4.2).
* K. S. Kedlaya and R. Liu, *Relative p-adic Hodge theory: foundations*, Astérisque 371 (2015),
  §2.4, Remark 2.4.2, and §8.2, Definition 8.2.16.
* P. Scholze, *Perfectoid spaces*, Publ. Math. IHÉS 116 (2012), §7, Definition 7.1(i).
-/

public section

namespace TauCeti.Huber.Pair

variable {A : Type*} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A] [IsHuberRing A]

section FiniteAlgebra

variable (S : Pair A) (B : Type*) [CommRing B] [Algebra A B] [Module.Finite A B]
  [TopologicalSpace B] [IsModuleTopology A B] [IsTopologicalRing B] [IsHuberRing B]

/-- **The Huber pair of a finite algebra.** For a Huber pair `(A, A⁺)` and a finite `A`-algebra
`B` with its natural topology, `(B, B⁺)` with `B⁺` the integral closure of the image of `A⁺`. -/
noncomputable def finiteAlgebra : Pair B where
  plus := (integralClosure (S.plus.map (algebraMap A B)) B).toSubring
  isRingOfIntegralElements :=
    { isOpen := isOpen_integralClosure_map_algebraMap S.isRingOfIntegralElements.isOpen
      isIntegrallyClosedIn := inferInstance
      le_powerBoundedSubring := Subring.integralClosure_subring_le_iff.mpr <| by
        rintro _ ⟨a, ha, rfl⟩
        exact mem_powerBoundedSubring.mpr <|
          (S.isRingOfIntegralElements.isPowerBounded_of_mem ha).algebraMap_of_isModuleTopology }

/-- The plus ring of `finiteAlgebra S B` is the integral closure of the image of `A⁺`. -/
@[simp]
theorem finiteAlgebra_plus :
    (S.finiteAlgebra B).plus = (integralClosure (S.plus.map (algebraMap A B)) B).toSubring :=
  (rfl)

/-- An element of `B` lies in the plus ring of `finiteAlgebra S B` iff it is integral over the
image of `A⁺`. -/
theorem mem_finiteAlgebra_plus {b : B} :
    b ∈ (S.finiteAlgebra B).plus ↔ IsIntegral (S.plus.map (algebraMap A B)) b :=
  Iff.rfl

/-- The structure morphism `(A, A⁺) → (B, B⁺)` of the Huber pair of a finite algebra. -/
noncomputable def finiteAlgebra.algebraHom : Hom S (S.finiteAlgebra B) where
  toRingHom := algebraMap A B
  continuous_toRingHom := continuous_algebraMap A B
  map_mem_plus a ha :=
    algebraMap_mem (integralClosure (S.plus.map (algebraMap A B)) B)
      ⟨algebraMap A B a, Subring.mem_map.mpr ⟨a, ha, rfl⟩⟩

/-- The underlying map of the structure morphism is `algebraMap A B`. -/
@[simp]
theorem finiteAlgebra.algebraHom_toRingHom :
    (finiteAlgebra.algebraHom S B).toRingHom = algebraMap A B :=
  (rfl)

/-- **The Huber pair of `A` itself is `(A, A⁺)`**: `A⁺` is integrally closed in `A`. -/
@[simp]
theorem finiteAlgebra_self : S.finiteAlgebra A = S := by
  have := S.isRingOfIntegralElements.isIntegrallyClosedIn
  refine Pair.ext <| le_antisymm (Subring.integralClosure_subring_le_iff.mpr ?_)
    fun a ha ↦ (finiteAlgebra.algebraHom S A).map_mem_plus a ha
  rintro _ ⟨a, ha, rfl⟩
  exact ha

variable {S B} {D : Type*} [CommRing D] [TopologicalSpace D] [IsTopologicalRing D]
  [IsHuberRing D] [Algebra A D] {V : Pair D}

/-- **The universal property of the Huber pair of a finite algebra.** If `χ : (A, A⁺) → (D, D⁺)`
is a morphism of Huber pairs with underlying map `algebraMap A D`, every `A`-algebra map `B → D`
is a morphism of Huber pairs `(B, B⁺) → (D, D⁺)`. It is continuous because `B` carries the natural
topology, and it carries `B⁺` into `D⁺` because `D⁺` is integrally closed in `D`. -/
noncomputable def finiteAlgebra.lift (χ : Hom S V) (hχ : χ.toRingHom = algebraMap A D)
    (f : B →ₐ[A] D) : Hom (S.finiteAlgebra B) V where
  toRingHom := f.toRingHom
  continuous_toRingHom :=
    have : ContinuousSMul A D := continuousSMul_of_algebraMap A D (hχ ▸ χ.continuous_toRingHom)
    IsModuleTopology.continuous_of_linearMap f.toLinearMap
  map_mem_plus b hb := by
    have := V.isRingOfIntegralElements.isIntegrallyClosedIn
    refine (Subring.integralClosure_subring_le_iff (T := V.plus.comap f.toRingHom)).mpr ?_ hb
    rintro _ ⟨a, ha, rfl⟩
    simpa [← hχ] using χ.map_mem_plus a ha

/-- The underlying map of `finiteAlgebra.lift χ hχ f` is `f`. -/
@[simp]
theorem finiteAlgebra.lift_toRingHom (χ : Hom S V) (hχ : χ.toRingHom = algebraMap A D)
    (f : B →ₐ[A] D) : (finiteAlgebra.lift χ hχ f).toRingHom = f.toRingHom :=
  (rfl)

/-- `finiteAlgebra.lift χ hχ f` is a morphism under `(A, A⁺)`. -/
@[simp]
theorem finiteAlgebra.lift_comp_algebraHom (χ : Hom S V) (hχ : χ.toRingHom = algebraMap A D)
    (f : B →ₐ[A] D) : (finiteAlgebra.lift χ hχ f).comp (finiteAlgebra.algebraHom S B) = χ :=
  Hom.ext <| by
    rw [Hom.toRingHom_comp, finiteAlgebra.lift_toRingHom, finiteAlgebra.algebraHom_toRingHom, hχ]
    exact f.comp_algebraMap

/-- **Morphisms out of the Huber pair of a finite algebra.** Morphisms of Huber pairs
`(B, B⁺) → (D, D⁺)` under `(A, A⁺)` are exactly the `A`-algebra maps `B → D`. -/
noncomputable def finiteAlgebra.homEquiv (χ : Hom S V) (hχ : χ.toRingHom = algebraMap A D) :
    {ψ : Hom (S.finiteAlgebra B) V // ψ.comp (finiteAlgebra.algebraHom S B) = χ} ≃
      (B →ₐ[A] D) where
  toFun ψ :=
    { ψ.1.toRingHom with
      commutes' a := by
        have h := congrArg (fun g : Hom S V ↦ g.toRingHom a) ψ.2
        simpa [hχ] using h }
  invFun f := ⟨finiteAlgebra.lift χ hχ f, finiteAlgebra.lift_comp_algebraHom χ hχ f⟩
  left_inv ψ := Subtype.ext <| Hom.ext (rfl)
  right_inv f := AlgHom.ext fun _ ↦ (rfl)

/-- `finiteAlgebra.homEquiv` sends a morphism of Huber pairs to its underlying map. -/
@[simp]
theorem finiteAlgebra.homEquiv_apply (χ : Hom S V) (hχ : χ.toRingHom = algebraMap A D)
    (ψ : {ψ : Hom (S.finiteAlgebra B) V // ψ.comp (finiteAlgebra.algebraHom S B) = χ}) (b : B) :
    finiteAlgebra.homEquiv χ hχ ψ b = ψ.1.toRingHom b :=
  (rfl)

/-- The inverse of `finiteAlgebra.homEquiv` is `finiteAlgebra.lift`. -/
@[simp]
theorem finiteAlgebra.homEquiv_symm_apply (χ : Hom S V) (hχ : χ.toRingHom = algebraMap A D)
    (f : B →ₐ[A] D) :
    ((finiteAlgebra.homEquiv χ hχ).symm f).1 = finiteAlgebra.lift χ hχ f :=
  (rfl)

end FiniteAlgebra

/-! ### Finite étale morphisms of Huber pairs -/

section FiniteEtale

variable {B : Type*} [CommRing B] [TopologicalSpace B] [IsTopologicalRing B] [IsHuberRing B]
  {S : Pair A} {T : Pair B}

/-- A morphism `φ : (A, A⁺) → (B, B⁺)` of Huber pairs is *finite étale* if `φ` makes `B` a finite
étale `A`-algebra, `B` carries the natural topology of a finite `A`-module, and `B⁺` is the
integral closure of `φ(A⁺)` in `B` (Kedlaya–Liu, Definition 8.2.16). The plus ring is part of the
condition: the integral closure of `φ(A⁺)` can be smaller than `B°`. -/
structure Hom.IsFiniteEtale (φ : Hom S T) : Prop where
  /-- `B` is a finite `A`-module. -/
  finite : φ.toRingHom.Finite
  /-- `B` is an étale `A`-algebra. -/
  etale : φ.toRingHom.Etale
  /-- `B` carries the natural topology of an `A`-module. -/
  isModuleTopology : letI := φ.toRingHom.toAlgebra; IsModuleTopology A B
  /-- `B⁺` is the integral closure of `φ(A⁺)` in `B`. -/
  plus_eq : T.plus = (integralClosure (S.plus.map φ.toRingHom) B).toSubring

/-- **For a finite étale algebra, the structure morphism of its Huber pair is finite étale.** -/
theorem finiteAlgebra.isFiniteEtale_algebraHom (S : Pair A) (B : Type*) [CommRing B]
    [Algebra A B] [Module.Finite A B] [Algebra.Etale A B] [TopologicalSpace B]
    [IsModuleTopology A B] [IsTopologicalRing B] [IsHuberRing B] :
    (finiteAlgebra.algebraHom S B).IsFiniteEtale where
  finite := RingHom.finite_algebraMap.mpr inferInstance
  etale := RingHom.etale_algebraMap.mpr inferInstance
  isModuleTopology := by
    rw [finiteAlgebra.algebraHom_toRingHom, _root_.toAlgebra_algebraMap]
    infer_instance
  plus_eq := (rfl)

/-- **Universal property of a finite étale morphism of Huber pairs.** If `φ : (A, A⁺) → (B, B⁺)` is
finite étale and `χ : (A, A⁺) → (D, D⁺)` is a morphism of Huber pairs, every ring map `ψ : B → D`
with `ψ ∘ φ = χ` is a morphism of Huber pairs `(B, B⁺) → (D, D⁺)`. -/
theorem Hom.IsFiniteEtale.exists_hom {φ : Hom S T} (hφ : φ.IsFiniteEtale) {D : Type*} [CommRing D]
    [TopologicalSpace D] [IsTopologicalRing D] [IsHuberRing D] {V : Pair D} (χ : Hom S V)
    (ψ : B →+* D) (hψ : ψ.comp φ.toRingHom = χ.toRingHom) :
    ∃ ψ' : Hom T V, ψ'.toRingHom = ψ := by
  let := φ.toRingHom.toAlgebra
  let := χ.toRingHom.toAlgebra
  have hφA : algebraMap A B = φ.toRingHom := RingHom.algebraMap_toAlgebra _
  have hχA : algebraMap A D = χ.toRingHom := RingHom.algebraMap_toAlgebra _
  have : Module.Finite A B := hφ.finite
  have : IsModuleTopology A B := hφ.isModuleTopology
  -- `T` is the Huber pair of the finite algebra `B`, so `ψ` is a lift out of it
  let ψ' := finiteAlgebra.lift (B := B) χ hχA.symm
    { ψ with commutes' := fun a ↦ by simpa [hφA, hχA] using congrArg (· a) hψ }
  refine ⟨⟨ψ, ψ'.continuous_toRingHom, fun b hb ↦ ψ'.map_mem_plus b ?_⟩, rfl⟩
  rw [finiteAlgebra_plus]
  rwa [hφ.plus_eq, ← hφA] at hb

end FiniteEtale

end TauCeti.Huber.Pair

end
