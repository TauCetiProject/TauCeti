/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Singular.LocalHomology.LivesOver
public import TauCeti.Topology.MappingSpace.Evaluation
public import TauCeti.Topology.MappingSpace.Sphere.Basic
public import TauCeti.Topology.Sphere.Suspension
public import Mathlib.Topology.Homotopy.HomotopyGroup
import TauCeti.AlgebraicTopology.Singular.Reduced
import TauCeti.Topology.Homotopy.HomotopyGroup.LoopSpace

/-!
# Manifolds abundant with two-spheres

Let `Q` be a closed connected oriented `n`-manifold and let `ev : Map(S², Q) → Q` be evaluation
at the north pole of `S²`, the evaluation fibration with fibre `Ω²Q` over a base point `b`.
Barraud, Damian, Humilière and Oancea call `Q` **abundant with 2-spheres** (their Definition 6.11
and Definition 1.7) if some class `α ∈ Hₖ(Map(S², Q); ℤ)` satisfies:

1. `α` lives over the fundamental class of `Q`, that is its shriek `j_! α ∈ Hₖ₋ₙ(Ω²Q)` under the
   inclusion `j` of `b` is nonzero;
2. either `k > n`, or `k = n` and the image of `j_! α` in `H₀(Ω²Q, pt)` is nonzero.

Their Theorem 6.12 (Theorem H of the introduction) shows that the `π₁`-sensitive
Hofer–Zehnder capacity of the unit codisc bundle `D*Q` of such a manifold is finite.

This file states the definition in the chart-free form of
`TauCeti.LivesOverFundamentalClass` (`TauCeti.IsAbundantWithTwoSpheres`). The shriek map is the
localization `Hₖ(E) → Hₖ(E, E ∖ F)` at the fibre `F = ev⁻¹(b)` followed by an identification
`Hₖ(E, E ∖ F) ≅ Hₖ₋ₙ(F)` that depends on a chart at `b`
(`TauCeti.livesOverFundamentalClass_iff_singularHomologyComplFiberIso_hom_ne_zero`), so the
first condition is that the localization of `α` is nonzero. For the second condition in degree
`n`, the kernel of `H₀(Ω²Q) → H₀(Ω²Q, pt)` is spanned by the class of the constant sphere at `b`.
The constant spheres `c : Q → Map(S², Q)` are a section of `ev`, so they map the pair
`(Q, Q ∖ {b})` to `(E, E ∖ F)`, and the local homology `Hₙ(Q, Q ∖ {b}) ≅ H₀(pt)` goes under the
chart identifications onto that span: this is the square of the source's proof of Theorem 6.12,
the naturality of the shriek map (their Proposition 2.12) for the map of fibrations `c` from the
identity of `Q` to `ev`. So the second condition in degree `n` says that the localization of `α`
does not lie in the image of `c_* : Hₙ(Q, Q ∖ {b}) → Hₙ(E, E ∖ F)`.

The definition only uses the space `Q`, a point `b` and the dimension `n`; it is meant for closed
connected oriented `n`-manifolds, where it is the source's definition. Coefficients are the
integers, written `ULift ℤ` as for the integral fundamental classes of
`TauCeti.HomologicalOrientation`. Witnesses are built as cross products of integral classes, with
coefficients `ℤ ⊗ ℤ` identified with `ℤ` (`TauCeti.uliftIntTensorIso`), from classes of the double
loop space carried to `Map_*(S², Q)` (`TauCeti.doubleLoopSpaceHomologyIsoBasedMap`). The
identification of coefficients commutes with continuous maps
(`TauCeti.homologyMap_chainComplexFunctor_map_apply`), and so does homology with commuting squares
of continuous maps (`TauCeti.homologyMap_homologyMap_apply_of_comp_eq`).

## Main definitions

* `TauCeti.IsAbundantWithTwoSpheres Q n b`: `Q` is abundant with 2-spheres at `b`, in
  dimension `n`, characterized by `TauCeti.isAbundantWithTwoSpheres_iff`.
* `TauCeti.uliftIntTensorIso`: `ℤ ⊗ ℤ ≅ ℤ`, for the coefficients `ULift ℤ`, which multiplies the
  integers (`TauCeti.uliftIntTensorIso_hom_tmul`).
* `TauCeti.doubleLoopSpaceHomologyIsoBasedMap`: `Hₘ(Ω²Q; ℤ) ≅ Hₘ(Map_*(S², Q); ℤ)`.

## Main results

* `TauCeti.isAbundantWithTwoSpheres_of_lt`: a class of degree above `n` living over the
  fundamental class witnesses abundance.
* `TauCeti.isAbundantWithTwoSpheres_of_eq`: so does a class of degree `n` living over the
  fundamental class whose localization is not that of a constant sphere class.
* `TauCeti.isAbundantWithTwoSpheres_of_livesOverFundamentalClass_sub`: this holds for a class `α`
  of degree `n` when both `α` and `α - ρ_* α` live over the fundamental class, where `ρ` is the
  self-map `f ↦ const (f(north))` of `Map(S², Q)`.
* `TauCeti.exists_not_joined_of_nontrivial_homotopyGroup_two`: if `π₂(Q, x) ≠ 0`, every based
  sphere at `x` has a based sphere not joined to it, a degree-zero witness for the above.

## References

* J.-F. Barraud, M. Damian, V. Humilière, A. Oancea, *Floer homology with DG coefficients.
  Applications to cotangent bundles*, arXiv:2404.07953, Definitions 1.7, 2.3 and 6.11,
  Proposition 2.12 and Theorem 6.12.
-/

public section

noncomputable section

universe w v

open CategoryTheory MonoidalCategory
open scoped Topology Topology.Homotopy TensorProduct

namespace TauCeti

variable (Q : Type) [TopologicalSpace Q]

/-- A space `Q` is **abundant with 2-spheres** at `b`, in dimension `n`
(Barraud–Damian–Humilière–Oancea, Definition 6.11), if some integral class
`α ∈ Hₖ(Map(S², Q); ℤ)` lives over the fundamental class of `Q` at `b` for evaluation at the
north pole, and either `n < k`, or `k = n` and the localization of `α` at the fibre over `b` is
not in the image of the local homology `Hₙ(Q, Q ∖ {b}; ℤ)` under the constant spheres.

For a closed connected oriented `n`-manifold this is the source's definition: the localization
at the fibre is the chart-free form of their shriek map `j_! : Hₖ(Map(S², Q)) → Hₖ₋ₙ(Ω²Q)`, and
in degree `n` the image of the local homology is the span of the class of the constant sphere in
`H₀(Ω²Q)`, the kernel of `H₀(Ω²Q) → H₀(Ω²Q, pt)`. -/
def IsAbundantWithTwoSpheres (n : ℕ) (b : Q) : Prop :=
  ∃ (k : ℕ) (α : ((TopCat.toSSet.obj (TopCat.of C(Sphere2, Q))).homology
      (ModuleCat.of ℤ (ULift.{0} ℤ)) k : ModuleCat.{0} ℤ)),
    LivesOverFundamentalClass (ModuleCat.of ℤ (ULift.{0} ℤ)) (mappingSpaceEval Sphere2.north) b
        α ∧
      (n < k ∨ k = n ∧ (fiberLocalization (ModuleCat.of ℤ (ULift.{0} ℤ))
        (mappingSpaceEval Sphere2.north) b k).hom α ∉
          LinearMap.range (localHomologyMap (ModuleCat.of ℤ (ULift.{0} ℤ)) ContinuousMap.const'
            (const'_preimage_mappingSpaceEval_preimage_subset Sphere2.north b) k).hom)

/-- Unfolding `IsAbundantWithTwoSpheres`: some class of `Hₖ(Map(S², Q); ℤ)` lives over the
fundamental class at `b`, and either `n < k`, or `k = n` and its localization at the fibre over `b`
is not in the image of the local homology of `Q` at `b` under the constant spheres. -/
theorem isAbundantWithTwoSpheres_iff (n : ℕ) (b : Q) :
    IsAbundantWithTwoSpheres Q n b ↔
      ∃ (k : ℕ) (α : ((TopCat.toSSet.obj (TopCat.of C(Sphere2, Q))).homology
          (ModuleCat.of ℤ (ULift.{0} ℤ)) k : ModuleCat.{0} ℤ)),
        LivesOverFundamentalClass (ModuleCat.of ℤ (ULift.{0} ℤ))
            (mappingSpaceEval Sphere2.north) b α ∧
          (n < k ∨ k = n ∧ (fiberLocalization (ModuleCat.of ℤ (ULift.{0} ℤ))
            (mappingSpaceEval Sphere2.north) b k).hom α ∉
              LinearMap.range (localHomologyMap (ModuleCat.of ℤ (ULift.{0} ℤ))
                ContinuousMap.const'
                  (const'_preimage_mappingSpaceEval_preimage_subset Sphere2.north b) k).hom) :=
  Iff.rfl

variable {Q}

/-- **Abundance from a class of degree above the dimension.** If a class
`α ∈ Hₖ(Map(S², Q); ℤ)` with `n < k` lives over the fundamental class at `b`, then `Q` is
abundant with 2-spheres at `b` in dimension `n`. -/
theorem isAbundantWithTwoSpheres_of_lt {n k : ℕ} {b : Q}
    {α : ((TopCat.toSSet.obj (TopCat.of C(Sphere2, Q))).homology
      (ModuleCat.of ℤ (ULift.{0} ℤ)) k : ModuleCat.{0} ℤ)}
    (hα : LivesOverFundamentalClass (ModuleCat.of ℤ (ULift.{0} ℤ))
      (mappingSpaceEval Sphere2.north) b α) (hk : n < k) :
    IsAbundantWithTwoSpheres Q n b :=
  ⟨k, α, hα, Or.inl hk⟩

/-- **Abundance from a class in the dimension.** If a class `α ∈ Hₙ(Map(S², Q); ℤ)` lives over
the fundamental class at `b` and its localization at the fibre over `b` is not the image of a
class of the local homology `Hₙ(Q, Q ∖ {b}; ℤ)` under the constant spheres, then `Q` is abundant
with 2-spheres at `b` in dimension `n`. -/
theorem isAbundantWithTwoSpheres_of_eq {n : ℕ} {b : Q}
    {α : ((TopCat.toSSet.obj (TopCat.of C(Sphere2, Q))).homology
      (ModuleCat.of ℤ (ULift.{0} ℤ)) n : ModuleCat.{0} ℤ)}
    (hα : LivesOverFundamentalClass (ModuleCat.of ℤ (ULift.{0} ℤ))
      (mappingSpaceEval Sphere2.north) b α)
    (hc : ∀ β, (localHomologyMap (ModuleCat.of ℤ (ULift.{0} ℤ)) ContinuousMap.const'
      (const'_preimage_mappingSpaceEval_preimage_subset Sphere2.north b) n).hom β ≠
        (fiberLocalization (ModuleCat.of ℤ (ULift.{0} ℤ)) (mappingSpaceEval Sphere2.north) b
          n).hom α) :
    IsAbundantWithTwoSpheres Q n b :=
  ⟨n, α, hα, Or.inr ⟨rfl, fun ⟨β, hβ⟩ ↦ hc β hβ⟩⟩

/-- **Abundance from a class in the dimension not fixed by the constant spheres.** Let `ρ` be the
self-map `f ↦ const (f(north))` of `Map(S², Q)`. If a class `α ∈ Hₙ(Map(S², Q); ℤ)` lives over the
fundamental class at `b`, and so does `α - ρ_* α`, then `Q` is abundant with 2-spheres at `b` in
dimension `n`. Indeed `ρ` lies over `Q` and fixes the constant spheres, so if the localization of
`α` were that of a class of constant spheres, it would agree with the localization of `ρ_* α`. -/
theorem isAbundantWithTwoSpheres_of_livesOverFundamentalClass_sub {n : ℕ} {b : Q}
    {α : ((TopCat.toSSet.obj (TopCat.of C(Sphere2, Q))).homology
      (ModuleCat.of ℤ (ULift.{0} ℤ)) n : ModuleCat.{0} ℤ)}
    (hα : LivesOverFundamentalClass (ModuleCat.of ℤ (ULift.{0} ℤ))
      (mappingSpaceEval Sphere2.north) b α)
    (hρα : LivesOverFundamentalClass (ModuleCat.of ℤ (ULift.{0} ℤ))
      (mappingSpaceEval Sphere2.north) b (α - (SSet.homologyMap (TopCat.toSSet.map (TopCat.ofHom
        (ContinuousMap.const'.comp (mappingSpaceEval (X := Q) Sphere2.north))))
          (ModuleCat.of ℤ (ULift.{0} ℤ)) n).hom α)) :
    IsAbundantWithTwoSpheres Q n b := by
  let R := ModuleCat.of ℤ (ULift.{0} ℤ)
  let ρ : C(C(Sphere2, Q), C(Sphere2, Q)) :=
    ContinuousMap.const'.comp (mappingSpaceEval Sphere2.north)
  have hρ : mappingSpaceEval Sphere2.north ∘ ρ = mappingSpaceEval Sphere2.north := funext fun f ↦ by
    simp [ρ]
  have hρc : ρ.comp ContinuousMap.const' = ContinuousMap.const' := ContinuousMap.ext fun x ↦ by
    simp [ρ]
  refine isAbundantWithTwoSpheres_of_eq hα fun β hβ ↦ ?_
  -- If the localization of `α` is that of a class `β` of constant spheres, it is fixed by `ρ`.
  have key : (fiberLocalization R (mappingSpaceEval Sphere2.north) b n).hom
      ((SSet.homologyMap (TopCat.toSSet.map (TopCat.ofHom ρ)) R n).hom α) =
        (fiberLocalization R (mappingSpaceEval Sphere2.north) b n).hom α := by
    rw [← ModuleCat.comp_apply, homologyMap_comp_fiberLocalization R ρ hρ, ModuleCat.comp_apply,
      ← hβ, ← ModuleCat.comp_apply, localHomologyMap_comp, localHomologyMap_congr R hρc]
  refine (livesOverFundamentalClass_iff _ _ _ _).1 hρα ?_
  rw [map_sub]
  exact sub_eq_zero.2 key.symm

/-- **Based spheres outside a path component.** If `π₂(Q, x)` is nontrivial, then the based
mapping space `Map_*(S², Q) ≃ₜ Ω²Q` is not path connected: for every based sphere `y₀` some based
sphere `y₁` is not joined to `y₀` by a path. -/
theorem exists_not_joined_of_nontrivial_homotopyGroup_two (x : Q) [Nontrivial (π_ 2 Q x)]
    (y₀ : BasedMap Sphere2 Q Sphere2.north x) :
    ∃ y₁ : BasedMap Sphere2 Q Sphere2.north x, ¬Joined y₁ y₀ := by
  let e := BasedTopologicalSpace.basedMapSphereHomeomorphIteratedLoopSpace 2 ⟨Q, x⟩ Sphere2.north
  by_contra! h
  have : PathConnectedSpace (BasedMap Sphere2 Q Sphere2.north x) :=
    ⟨⟨y₀⟩, fun y y' ↦ (h y).trans (h y').symm⟩
  exact not_subsingleton (π_ 2 Q x)
    ((pathConnectedSpace_doubleLoopSpace_iff x).1 (e.surjective.pathConnectedSpace e.continuous))

/-- The identification of the coefficients `ℤ ⊗ ℤ` of a cross product of integral classes with
`ℤ`, both written `ULift ℤ` as in `TauCeti.IsAbundantWithTwoSpheres`. -/
def uliftIntTensorIso :
    ModuleCat.of ℤ (ULift.{0} ℤ) ⊗ ModuleCat.of ℤ (ULift.{0} ℤ) ≅ ModuleCat.of ℤ (ULift.{0} ℤ) :=
  -- `ModuleCat.of ℤ ℤ`, the target of `uliftIntIso`, is the tensor unit `𝟙_ (ModuleCat ℤ)`.
  tensorIso uliftIntIso uliftIntIso ≪≫ λ_ (𝟙_ _) ≪≫ uliftIntIso.symm

/-- `TauCeti.uliftIntTensorIso` multiplies the integers. -/
@[simp]
theorem uliftIntTensorIso_hom_tmul (a b : ℤ) :
    uliftIntTensorIso.hom.hom (ULift.up a ⊗ₜ[ℤ] ULift.up b) = ULift.up (a * b) := by
  simp only [uliftIntTensorIso, Iso.trans_hom, Iso.symm_hom, tensorIso_hom, ModuleCat.hom_comp,
    LinearMap.comp_apply, ModuleCat.hom_tensorHom]
  -- `ModuleCat.of ℤ ℤ` is the tensor unit, on which the left unitor multiplies. The tensor product
  -- and the unit of `ModuleCat` are not syntactically `TensorProduct` and `ℤ`, so `simp` does not
  -- apply the remaining steps.
  rw [TensorProduct.map_tmul, ModuleCat.MonoidalCategory.leftUnitor_hom_apply,
    uliftIntIso_hom_apply, uliftIntIso_hom_apply, uliftIntIso_inv_apply, smul_eq_mul]

/-- A commuting square `ρ ∘ Φ = Φ' ∘ γ` of continuous maps commutes on homology, on elements:
`ρ_* (Φ_* x) = Φ'_* (γ_* x)`. -/
theorem homologyMap_homologyMap_apply_of_comp_eq {k : Type v} [Ring k] (M : ModuleCat.{w} k)
    {X X' Z Z' : Type w} [TopologicalSpace X] [TopologicalSpace X'] [TopologicalSpace Z]
    [TopologicalSpace Z'] {Φ : C(X, Z)} {ρ : C(Z, Z')} {γ : C(X, X')} {Φ' : C(X', Z')}
    (h : ρ.comp Φ = Φ'.comp γ) {m : ℕ}
    (x : ((TopCat.toSSet.obj (TopCat.of X)).homology M m : ModuleCat.{w} k)) :
    (SSet.homologyMap (TopCat.toSSet.map (TopCat.ofHom ρ)) M m).hom
        ((SSet.homologyMap (TopCat.toSSet.map (TopCat.ofHom Φ)) M m).hom x) =
      (SSet.homologyMap (TopCat.toSSet.map (TopCat.ofHom Φ')) M m).hom
        ((SSet.homologyMap (TopCat.toSSet.map (TopCat.ofHom γ)) M m).hom x) := by
  simp only [← ConcreteCategory.comp_apply, ← SSet.homologyMap_comp, ← Functor.map_comp,
    ← TopCat.ofHom_comp, h]

/-- A coefficient morphism `φ : M ⟶ N` commutes with the map induced on homology by a continuous
map: this is the naturality of `AlgebraicTopology.singularHomologyFunctor` in the coefficients, on
elements. -/
theorem homologyMap_chainComplexFunctor_map_apply {k : Type v} [Ring k] {M N : ModuleCat.{w} k}
    (φ : M ⟶ N) {X Y : Type w} [TopologicalSpace X] [TopologicalSpace Y] (f : C(X, Y)) {m : ℕ}
    (x : ((TopCat.toSSet.obj (TopCat.of X)).homology M m : ModuleCat.{w} k)) :
    (HomologicalComplex.homologyMap (((SSet.chainComplexFunctor (ModuleCat.{w} k)).map
      φ).app (TopCat.toSSet.obj (TopCat.of Y))) m).hom
        ((SSet.homologyMap (TopCat.toSSet.map (TopCat.ofHom f)) M m).hom x) =
      (SSet.homologyMap (TopCat.toSSet.map (TopCat.ofHom f)) N m).hom
        ((HomologicalComplex.homologyMap (((SSet.chainComplexFunctor (ModuleCat.{w} k)).map
          φ).app (TopCat.toSSet.obj (TopCat.of X))) m).hom x) :=
  -- The naturality square of `singularHomologyFunctor`, read through its definition as the
  -- homology of `TopCat.toSSet`.
  (ConcreteCategory.congr_hom (((AlgebraicTopology.singularHomologyFunctor (ModuleCat.{w} k)
    m).map φ).naturality (TopCat.ofHom f)) x)

/-- The integral homology of the double loop space `Ω²Q` at `x` is that of the based mapping space
`Map_*(S², Q)` of maps sending the north pole to `x`, with the coefficients `ULift ℤ` of
`TauCeti.IsAbundantWithTwoSpheres`, through the homeomorphism of `Map_*(S², Q)` with the iterated
loop space (`BasedTopologicalSpace.basedMapSphereHomeomorphIteratedLoopSpace`). -/
def doubleLoopSpaceHomologyIsoBasedMap (x : Q) (m : ℕ) :
    ((singularChains ℤ).obj (TopCat.of (Ω (Ω Q x) (Path.refl x)))).homology m ≅
      (TopCat.toSSet.obj (TopCat.of (BasedMap Sphere2 Q Sphere2.north x))).homology
        (ModuleCat.of ℤ (ULift.{0} ℤ)) m :=
  (uliftIntHomologyIso _ m).symm ≪≫
    ((AlgebraicTopology.singularHomologyFunctor (ModuleCat.{0} ℤ) m).obj
      (ModuleCat.of ℤ (ULift.{0} ℤ))).mapIso (TopCat.isoOfHomeo
        (BasedTopologicalSpace.basedMapSphereHomeomorphIteratedLoopSpace 2 ⟨Q, x⟩
          Sphere2.north).symm)

end TauCeti
