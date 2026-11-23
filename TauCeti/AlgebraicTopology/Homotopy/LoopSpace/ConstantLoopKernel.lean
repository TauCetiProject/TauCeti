/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Homotopy.LoopSpace.Aspherical
public import TauCeti.AlgebraicTopology.Homotopy.LoopSpace.FirstHomology
public import TauCeti.AlgebraicTopology.Homotopy.LoopSpace.FreeLoop
public import TauCeti.AlgebraicTopology.Homotopy.LoopSpace.Hurewicz
public import TauCeti.AlgebraicTopology.Homotopy.LoopSpace.ReducedHomology
public import TauCeti.AlgebraicTopology.Singular.Contractible
public import TauCeti.AlgebraicTopology.Singular.Homotopy.WeakHomotopyEquivalence
public import TauCeti.Topology.MappingSpace.Sphere.Basic
public import TauCeti.Topology.MappingSpace.Sphere.Moore
public import TauCeti.Topology.PathSpace.Moore.From

/-!
# The kernel of the inclusion of the constant loops on path spaces

Let `Q` be a space with a point `x`, let `𝓛₀Q` be its contractible free loops and `⋆` the constant
loop at `x`. The Moore paths in `𝓛₀Q` from `⋆` to a constant loop, `P_{⋆→Q} 𝓛₀Q`
(`TauCeti.BasedConstContractibleMoorePaths`), form a subspace of all the Moore paths in `𝓛₀Q`
starting at `⋆`, `P_{⋆→𝓛₀Q} 𝓛₀Q` (`TauCeti.MoorePathFrom`). These are the total spaces of the path
fibration over `𝓛₀Q` and of its pullback along the constant loops `i_Q : Q → 𝓛₀Q`, and the
inclusion (`TauCeti.basedConstContractibleMoorePathsInclusion`) is the map of total spaces over
`i_Q`.

Barraud, Damian, Humilière and Oancea, in the proof of their Proposition 5.11, identify the map
`i_{Q*} : H_*(Q; i_Q^*𝓕) → H_*(𝓛₀Q; 𝓕)` for the DG local system `𝓕` of this path fibration with
the map induced by this inclusion on the homology of the total spaces, through the fibration
theorem of DG Morse homology. This file computes the kernel of the latter map and proves
Proposition 5.11 (the cases `k = 2` and `k > 2` of the first nontrivial higher homotopy group) for
it.

* The space `P_{⋆→𝓛₀Q} 𝓛₀Q` is contractible, so the kernel of the inclusion on `Hₙ` is the reduced
  homology `H~ₙ(P_{⋆→Q} 𝓛₀Q)`, in every degree
  (`TauCeti.isLimitReducedSingularHomologyιBasedConstContractibleMoorePaths`).
* The space `P_{⋆→Q} 𝓛₀Q` is homotopy equivalent to the based maps `Map_*(S², Q)`, hence to the
  double loop space `Ω²Q = Ω (Ω Q x) (Path.refl x)`
  (`TauCeti.basedConstContractibleMoorePathsHomotopyEquiv`). So the kernel is isomorphic to
  `H~ₙ(Ω²Q)` (`TauCeti.kernelBasedConstContractibleMoorePathsInclusionIso`).
* If `π₂(Q, x)` is nontrivial, the kernel in degree zero contains a copy of the coefficient ring,
  an infinite cyclic subgroup over `ℤ`
  (`TauCeti.exists_injective_singularHomology_basedConstContractibleMoorePaths_zero`).
* If `πⱼ(Q, x)` vanishes for `2 ≤ j < k`, with `k ≥ 3`, the kernel in degree `k - 2` is all of
  `H_{k-2}(P_{⋆→Q} 𝓛₀Q; ℤ)`, which is isomorphic to `π_k(Q, x)` by the Hurewicz theorem for the
  double loop space (`TauCeti.basedConstContractibleMoorePathsHomologyAddEquiv`,
  `TauCeti.singularHomologyMap_basedConstContractibleMoorePathsInclusion_succ_eq_zero`).
* A path-connected `Q` is aspherical exactly when the kernel vanishes in every degree with
  integral coefficients, through Lemma 3.41 of Barraud–Damian–Humilière–Oancea:
  `isAspherical_iff_forall_injective_singularHomologyMap_basedConstContractibleMoorePathsInclusion`
  in the namespace `TauCeti`. So when `Q` is not aspherical some degree has a nonzero kernel, which
  is all that Proposition 5.11 is needed for when the map `π ∘ φ` has degree `±1`. For aspherical
  `Q` the kernel vanishes with any coefficient ring
  (`TauCeti.IsAspherical.injective_singularHomologyMap_basedConstContractibleMoorePathsInclusion`).
* For aspherical `Q` the constant loops `Q → 𝓛₀Q` are moreover a weak homotopy equivalence, so
  they induce isomorphisms on ordinary singular homology
  (`TauCeti.IsAspherical.isIso_singularHomologyMap_constContractibleLoop`). For a torus, this is
  why `i_{Q*}` is injective on ordinary homology.

## References

* J.-F. Barraud, M. Damian, V. Humilière, A. Oancea, *Floer homology with DG coefficients.
  Applications to cotangent bundles*, arXiv:2404.07953, Proposition 5.11 and its proof.
-/

public section

noncomputable section

open CategoryTheory Limits AlgebraicTopology HomotopyGroup
open scoped Topology Topology.Homotopy ContinuousMap

namespace TauCeti

universe w v u

section Kernel

variable {C : Type u} [Category.{v} C] [HasCoproducts.{w} C] [Preadditive C]
  [CategoryWithHomology C] [HasKernels C] (R : C) (Q : Type w) [TopologicalSpace Q] (x : Q)

omit [HasKernels C] in
/-- The map induced on positive-degree homology by the inclusion `P_{⋆→Q} 𝓛₀Q → P_{⋆→𝓛₀Q} 𝓛₀Q`
is zero, so its kernel is the whole homology group. -/
theorem singularHomologyMap_basedConstContractibleMoorePathsInclusion_succ_eq_zero (n : ℕ) :
    ((singularHomologyFunctor C (n + 1)).obj R).map
      (TopCat.ofHom (basedConstContractibleMoorePathsInclusion Q x)) = 0 :=
  (isZero_singularHomologyFunctor_of_contractibleSpace R _ n.succ_ne_zero).eq_of_tgt _ _

/-- **The kernel of the inclusion of the constant loops on path spaces is reduced homology.** The
inclusion `H~ₙ(P_{⋆→Q} 𝓛₀Q) ⟶ Hₙ(P_{⋆→Q} 𝓛₀Q)` is a kernel of the map induced on `Hₙ` by the
inclusion `P_{⋆→Q} 𝓛₀Q → P_{⋆→𝓛₀Q} 𝓛₀Q`, in every degree, because `P_{⋆→𝓛₀Q} 𝓛₀Q` is
contractible. -/
def isLimitReducedSingularHomologyιBasedConstContractibleMoorePaths (n : ℕ) :
    IsLimit (KernelFork.ofι
      ((reducedSingularHomologyι R n).app (TopCat.of (BasedConstContractibleMoorePaths Q x)))
      (reducedSingularHomologyι_app_comp_map_eq_zero_of_contractibleSpace R
        (TopCat.ofHom (basedConstContractibleMoorePathsInclusion Q x)) n)) :=
  isLimitReducedSingularHomologyιOfContractibleSpace R _ n

/-- **The kernel of `i_{Q*}` on path spaces is the reduced homology of `Ω²Q`** (the identification
in the proof of Proposition 5.11 of Barraud–Damian–Humilière–Oancea). The kernel of the map induced
on `Hₙ` by the inclusion `P_{⋆→Q} 𝓛₀Q → P_{⋆→𝓛₀Q} 𝓛₀Q` is isomorphic to `H~ₙ(Ω²Q)`, in every
degree. -/
def kernelBasedConstContractibleMoorePathsInclusionIso (n : ℕ) :
    kernel (((singularHomologyFunctor C n).obj R).map
        (TopCat.ofHom (basedConstContractibleMoorePathsInclusion Q x))) ≅
      (reducedSingularHomologyFunctor R n).obj (TopCat.of (Ω (Ω Q x) (Path.refl x))) :=
  (limit.isLimit _).conePointUniqueUpToIso
      (isLimitReducedSingularHomologyιBasedConstContractibleMoorePaths R Q x n) ≪≫
    (basedConstContractibleMoorePathsHomotopyEquiv Q x).reducedSingularHomologyIso R n

/-- Under `TauCeti.kernelBasedConstContractibleMoorePathsInclusionIso`, the inclusion of the kernel
is the map induced on reduced homology by the homotopy inverse `Ω²Q → P_{⋆→Q} 𝓛₀Q`, followed by
the inclusion of reduced homology. -/
@[reassoc (attr := simp)]
theorem kernelBasedConstContractibleMoorePathsInclusionIso_inv_ι (n : ℕ) :
    (kernelBasedConstContractibleMoorePathsInclusionIso R Q x n).inv ≫ kernel.ι _ =
      (reducedSingularHomologyFunctor R n).map
          (TopCat.ofHom (basedConstContractibleMoorePathsHomotopyEquiv Q x).invFun) ≫
        (reducedSingularHomologyι R n).app (TopCat.of (BasedConstContractibleMoorePaths Q x)) := by
  simp only [kernelBasedConstContractibleMoorePathsInclusionIso, Iso.trans_inv,
    ContinuousMap.HomotopyEquiv.reducedSingularHomologyIso_inv, Category.assoc]
  congr 1
  exact (limit.isLimit _).conePointUniqueUpToIso_inv_comp
    (isLimitReducedSingularHomologyιBasedConstContractibleMoorePaths R Q x n)
    WalkingParallelPair.zero

end Kernel

section Ring

variable {R : Type u} [Ring R] {Q : Type u} [TopologicalSpace Q] (x : Q)

/-- **Proposition 5.11 of Barraud–Damian–Humilière–Oancea, case `k = 2`, on path spaces.** If
`π₂(Q, x)` is nontrivial, the kernel of the map induced on `H₀(-; R)` by the inclusion
`P_{⋆→Q} 𝓛₀Q → P_{⋆→𝓛₀Q} 𝓛₀Q` contains a copy of `R`; for `R = ℤ` this is an infinite cyclic
subgroup. -/
theorem exists_injective_singularHomology_basedConstContractibleMoorePaths_zero
    [Nontrivial (π_ 2 Q x)] :
    ∃ f : R →ₗ[R] ((singularHomologyFunctor (ModuleCat.{u} R) 0).obj (ModuleCat.of R R)).obj
        (TopCat.of (BasedConstContractibleMoorePaths Q x)),
      Function.Injective f ∧ ∀ r, (((singularHomologyFunctor (ModuleCat.{u} R) 0).obj
        (ModuleCat.of R R)).map (TopCat.ofHom (basedConstContractibleMoorePathsInclusion Q x))).hom
          (f r) = 0 := by
  obtain ⟨g, hg⟩ := exists_injective_doubleLoopSpaceReducedHomology₀ (R := R) x
  let e := (kernelBasedConstContractibleMoorePathsInclusionIso (ModuleCat.of R R) Q x 0).inv ≫
    kernel.ι _
  have he : e ≫ ((singularHomologyFunctor (ModuleCat.{u} R) 0).obj (ModuleCat.of R R)).map
      (TopCat.ofHom (basedConstContractibleMoorePathsInclusion Q x)) = 0 := by
    simp only [e, Category.assoc, kernel.condition, comp_zero]
  refine ⟨e.hom ∘ₗ g, ((ModuleCat.mono_iff_injective e).1 inferInstance).comp hg, fun r ↦ ?_⟩
  simpa using ConcreteCategory.congr_hom he (g r)

end Ring

section Integral

variable {Q : Type} [TopologicalSpace Q] (x : Q)

/-- **Proposition 5.11 of Barraud–Damian–Humilière–Oancea, case `k > 2`, on path spaces.** If
`π_{j+2}(Q, x)` vanishes for `j ≤ n`, the first possibly nontrivial higher homotopy group being
`π_{n+3}(Q, x)`, then `H_{n+1}(P_{⋆→Q} 𝓛₀Q; ℤ) ≅ π_{n+3}(Q, x)`. By
`TauCeti.singularHomologyMap_basedConstContractibleMoorePathsInclusion_succ_eq_zero` this whole
group is the kernel of the inclusion `P_{⋆→Q} 𝓛₀Q → P_{⋆→𝓛₀Q} 𝓛₀Q` in degree `n + 1`. It is the
Hurewicz isomorphism of the double loop space, through
`TauCeti.basedConstContractibleMoorePathsHomotopyEquiv`. -/
def basedConstContractibleMoorePathsHomologyAddEquiv :
    (n : ℕ) → (∀ j ≤ n, Subsingleton (π_ (j + 2) Q x)) →
      (Additive (π_ (n + 3) Q x) ≃+
        ((singularChains ℤ).obj (TopCat.of (BasedConstContractibleMoorePaths Q x))).homology
          (n + 1))
  | 0, hQ =>
    have : PathConnectedSpace (Ω (Ω Q x) (Path.refl x)) :=
      (pathConnectedSpace_doubleLoopSpace_iff x).2 (hQ 0 le_rfl)
    ((pathLoopSpaceMulEquiv (X := Q) (x := x) 1).symm.toAdditive.trans
        (pathLoopSpaceFirstHomologyAddEquiv (Path.refl x))).trans
      ((basedConstContractibleMoorePathsHomotopyEquiv Q x).singularHomologyIso
        (ModuleCat.of ℤ ℤ) 1).symm.toLinearEquiv.toAddEquiv
  | m + 1, hQ =>
    (doubleLoopSpaceHomologyAddEquiv x m fun j hj ↦ hQ j (by omega)).trans
      ((basedConstContractibleMoorePathsHomotopyEquiv Q x).singularHomologyIso
        (ModuleCat.of ℤ ℤ) (m + 2)).symm.toLinearEquiv.toAddEquiv

/-- In the case `n = 0`, `TauCeti.basedConstContractibleMoorePathsHomologyAddEquiv` sends a class
in `π₃(Q, x)` to its image under the loop-space shift and the Hurewicz isomorphism
`π₁(Ω²Q) ≅ H₁(Ω²Q; ℤ)`, pushed forward along the homotopy inverse `Ω²Q → P_{⋆→Q} 𝓛₀Q`. -/
theorem basedConstContractibleMoorePathsHomologyAddEquiv_zero_apply
    (hQ : ∀ j ≤ 0, Subsingleton (π_ (j + 2) Q x)) (a : Additive (π_ 3 Q x)) :
    basedConstContractibleMoorePathsHomologyAddEquiv x 0 hQ a =
      haveI : PathConnectedSpace (Ω (Ω Q x) (Path.refl x)) :=
        (pathConnectedSpace_doubleLoopSpace_iff x).2 (hQ 0 le_rfl)
      (((singularHomologyFunctor (ModuleCat.{0} ℤ) 1).obj (ModuleCat.of ℤ ℤ)).map
        (TopCat.ofHom (basedConstContractibleMoorePathsHomotopyEquiv Q x).invFun)).hom
          (pathLoopSpaceFirstHomologyAddEquiv (Path.refl x)
            (Additive.ofMul ((pathLoopSpaceMulEquiv (X := Q) (x := x) 1).symm a.toMul))) := by
  rw [← ContinuousMap.HomotopyEquiv.singularHomologyIso_inv]
  rfl

/-- In the case `n = m + 1`, `TauCeti.basedConstContractibleMoorePathsHomologyAddEquiv` is the
Hurewicz isomorphism `TauCeti.doubleLoopSpaceHomologyAddEquiv` of the double loop space, pushed
forward along the homotopy inverse `Ω²Q → P_{⋆→Q} 𝓛₀Q`. -/
theorem basedConstContractibleMoorePathsHomologyAddEquiv_succ_apply (m : ℕ)
    (hQ : ∀ j ≤ m + 1, Subsingleton (π_ (j + 2) Q x)) (a : Additive (π_ (m + 4) Q x)) :
    basedConstContractibleMoorePathsHomologyAddEquiv x (m + 1) hQ a =
      (((singularHomologyFunctor (ModuleCat.{0} ℤ) (m + 2)).obj (ModuleCat.of ℤ ℤ)).map
        (TopCat.ofHom (basedConstContractibleMoorePathsHomotopyEquiv Q x).invFun)).hom
          (doubleLoopSpaceHomologyAddEquiv x m (fun j hj ↦ hQ j (by omega)) a) := by
  rw [← ContinuousMap.HomotopyEquiv.singularHomologyIso_inv]
  rfl

end Integral

section Aspherical

/-! ### Aspherical spaces

For an aspherical space `Q` the constant loops `i_Q : Q → 𝓛₀Q` are a weak homotopy equivalence
(`TauCeti.IsAspherical.isWeakHomotopyEquivalence_constContractibleLoop`), so `i_{Q*}` is an
isomorphism on ordinary singular homology, and the kernel of the inclusion of path spaces vanishes
in every degree. Conversely, by Lemma 3.41 of Barraud–Damian–Humilière–Oancea, a path-connected
space whose kernel vanishes in every degree with integral coefficients is aspherical. -/

/-- **For an aspherical space, the constant loops `i_Q : Q → 𝓛₀Q` induce isomorphisms on singular
homology** with coefficients in any module, since they are a weak homotopy equivalence. -/
theorem IsAspherical.isIso_singularHomologyMap_constContractibleLoop {R : Type*} [Ring R]
    {Q : Type v} [TopologicalSpace Q] {x : Q} (h : IsAspherical Q x) (M : ModuleCat.{v} R)
    (n : ℕ) :
    IsIso (((singularHomologyFunctor (ModuleCat.{v} R) n).obj M).map
      (TopCat.ofHom (constContractibleLoop (Q := Q)))) :=
  h.isWeakHomotopyEquivalence_constContractibleLoop.isIso_singularHomologyMap M n

/-- **For an aspherical space, the inclusion of the constant loops on path spaces is injective on
homology.** If `Q` is aspherical, the map induced on `Hₙ(-; R)` by the inclusion
`P_{⋆→Q} 𝓛₀Q → P_{⋆→𝓛₀Q} 𝓛₀Q` is injective in every degree: its kernel is the reduced homology
of the double loop space (`TauCeti.kernelBasedConstContractibleMoorePathsInclusionIso`), which is
path connected with vanishing positive-degree homology. -/
theorem IsAspherical.injective_singularHomologyMap_basedConstContractibleMoorePathsInclusion
    {R : Type u} [Ring R] {Q : Type u} [TopologicalSpace Q] {x : Q} (h : IsAspherical Q x)
    (n : ℕ) :
    Function.Injective (((singularHomologyFunctor (ModuleCat.{u} R) n).obj (ModuleCat.of R R)).map
      (TopCat.ofHom (basedConstContractibleMoorePathsInclusion Q x))).hom := by
  rw [← ModuleCat.mono_iff_injective]
  refine Preadditive.mono_of_isZero_kernel _
    ((kernelBasedConstContractibleMoorePathsInclusionIso (ModuleCat.of R R) Q x n).isZero_iff.2 ?_)
  cases n with
  | zero =>
    have := (pathConnectedSpace_doubleLoopSpace_iff x).2 (h.subsingleton_homotopyGroup 0)
    exact isZero_reducedSingularHomologyFunctor_zero _ _
  | succ m =>
    refine ((reducedSingularHomologySuccIso _ m).app _).isZero_iff.2 ?_
    rw [singularHomologyFunctor_obj_obj]
    exact isZero_homology_singularChains_doubleLoopSpace R h.subsingleton_homotopyGroup
      m.succ_ne_zero

/-- **A path-connected space is aspherical exactly when the inclusion of the constant loops on path
spaces is injective on integral homology in every degree.** Equivalently, `Q` fails to be
aspherical exactly when the kernel of the map induced on some `Hₙ(-; ℤ)` by the inclusion
`P_{⋆→Q} 𝓛₀Q → P_{⋆→𝓛₀Q} 𝓛₀Q` is nonzero. This is Lemma 3.41 of
Barraud–Damian–Humilière–Oancea (`TauCeti.isAspherical_iff_doubleLoopSpace_singularHomology`)
read through the identification of the kernel with `H~ₙ(Ω²Q)`
(`TauCeti.kernelBasedConstContractibleMoorePathsInclusionIso`). It is the form of Proposition 5.11
used for maps of degree `±1`, where every nonzero element of the kernel serves. -/
theorem
    isAspherical_iff_forall_injective_singularHomologyMap_basedConstContractibleMoorePathsInclusion
    {Q : Type} [TopologicalSpace Q] [PathConnectedSpace Q] (x : Q) :
    IsAspherical Q x ↔ ∀ n, Function.Injective
      (((singularHomologyFunctor (ModuleCat.{0} ℤ) n).obj (ModuleCat.of ℤ ℤ)).map
        (TopCat.ofHom (basedConstContractibleMoorePathsInclusion Q x))).hom := by
  refine ⟨fun h n ↦ h.injective_singularHomologyMap_basedConstContractibleMoorePathsInclusion n,
    fun h ↦ ?_⟩
  have hZ (n : ℕ) : IsZero ((reducedSingularHomologyFunctor (ModuleCat.of ℤ ℤ) n).obj
      (TopCat.of (Ω (Ω Q x) (Path.refl x)))) := by
    have := (ModuleCat.mono_iff_injective _).2 (h n)
    exact (kernelBasedConstContractibleMoorePathsInclusionIso (ModuleCat.of ℤ ℤ) Q x n).isZero_iff.1
      (isZero_kernel_of_mono _)
  have : Nonempty (TopCat.of (Ω (Ω Q x) (Path.refl x))) := ⟨Path.refl (Path.refl x)⟩
  rw [isAspherical_iff_doubleLoopSpace_singularHomology]
  refine ⟨pathConnectedSpace_of_isZero_reducedSingularHomologyFunctor_zero (hZ 0), fun m hm ↦ ?_⟩
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hm
  rw [← singularHomologyFunctor_obj_obj]
  exact ((reducedSingularHomologySuccIso _ m).app _).isZero_iff.1 (hZ (m + 1))

end Aspherical

end TauCeti
