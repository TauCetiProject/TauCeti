/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Ring.ULift
public import Mathlib.Geometry.Manifold.PoincareConjecture
public import TauCeti.AlgebraicTopology.Singular.LocalHomology.Noncompact
public import TauCeti.AlgebraicTopology.Sphere.Contractible
public import TauCeti.AlgebraicTopology.Sphere.SimplyConnected
public import TauCeti.Topology.Homotopy.HomotopyEquiv

/-!
# Topological hypotheses detected by a homotopy equivalence to a sphere

Mathlib states the smooth generalized Poincaré conjecture as
`ContinuousMap.HomotopyEquiv.NonemptyDiffeomorphSphere M n`: any Hausdorff smooth `n`-manifold `M`
homotopy equivalent to the unit sphere `Sⁿ` is diffeomorphic to `Sⁿ`, without assuming upfront that
`M` is compact, connected, simply connected, or second countable.

This file proves that a homotopy equivalence `e : M ≃ₕ Sⁿ` automatically supplies all of those
hypotheses on any Hausdorff boundaryless `n`-manifold `M` (modelled on a real normed space `E` of
dimension `n`, with `Sⁿ` the unit sphere of a real normed space `F` of dimension `n + 1`, in
possibly different universes):

* **Homology.** Transporting `Sⁿ` to `TopCat.sphere n` in the universe of `X`
  (`TauCeti.sphereHomeomorphTopCatSphere`, `ContinuousMap.HomotopyEquiv.topCatSphere`), any space
  `X ≃ₕ Sⁿ` has reduced homology `H~ₙ(X; R) ≅ R` and zero elsewhere
  (`ContinuousMap.HomotopyEquiv.reducedSingularHomologySphereIso`,
  `ContinuousMap.HomotopyEquiv.isZero_reducedSingularHomology_of_sphere_of_ne`), hence for `1 ≤ n`
  ordinary top homology `Hₙ(X; R) ≅ R`
  (`ContinuousMap.HomotopyEquiv.singularHomologySphereIso`).
* **Connectivity.** `e` makes `X` nonempty for any nontrivial `F`, path-connected and connected for
  `1 ≤ n`, and simply connected for `2 ≤ n` (`ContinuousMap.HomotopyEquiv.nonempty_of_sphere`,
  `ContinuousMap.HomotopyEquiv.pathConnectedSpace_of_sphere`,
  `ContinuousMap.HomotopyEquiv.simplyConnectedSpace_of_sphere`).
* **Compactness and second countability.** For `1 ≤ n`, `M` is connected and
  `Hₙ(M; ULift ℤ) ≅ ULift ℤ ≠ 0`, so Hatcher's noncompact vanishing theorem
  (`TauCeti.compactSpace_of_not_isZero_singularHomology`) forces `CompactSpace M`; for `n = 0`,
  `M` is discrete and `π₀(M) ≃ π₀(S⁰)` is finite, again giving `CompactSpace M`
  (`ContinuousMap.HomotopyEquiv.compactSpace_of_sphere`). Compactness then yields
  `SecondCountableTopology M` (`ContinuousMap.HomotopyEquiv.secondCountableTopology_of_sphere`).
* **Obstructions and reductions.** No contractible space (in particular no real normed or Euclidean
  space), no noncompact Hausdorff `n`-manifold, and no proper open subset of a connected Hausdorff
  `n`-manifold is homotopy equivalent to `Sⁿ`
  (`TauCeti.isEmpty_homotopyEquiv_sphere_of_contractibleSpace`,
  `TauCeti.isEmpty_normedSpace_homotopyEquiv_sphere`,
  `TauCeti.isEmpty_euclideanSpace_homotopyEquiv_sphere`,
  `TauCeti.isEmpty_homotopyEquiv_sphere_of_not_compactSpace`,
  `TauCeti.isEmpty_open_ne_univ_homotopyEquiv_sphere`). Consequently, for `2 ≤ n` both the smooth
  statement `ContinuousMap.HomotopyEquiv.NonemptyDiffeomorphSphere M n` and its topological
  counterpart reduce to the case of compact simply connected second-countable manifolds
  (`TauCeti.nonemptyDiffeomorphSphere_iff_of_two_le`,
  `TauCeti.nonemptyDiffeomorphSphere_of_closed_simplyConnected`,
  `TauCeti.nonempty_homeomorph_sphere_of_homotopyEquiv_iff_of_two_le`,
  `TauCeti.nonempty_homeomorph_sphere_of_closed_simplyConnected`).

## References

* A. Hatcher, [*Algebraic Topology*](https://pi.math.cornell.edu/~hatcher/AT/AT.pdf),
  Section 3.3, Proposition 3.29.
-/

public section

noncomputable section

open CategoryTheory Limits Metric Module Set Topology
open scoped ContinuousMap ContDiff Manifold

universe w v u

namespace TauCeti

/-- The unit sphere of any real normed space `F` of dimension `n + 1` is homeomorphic to
`TopCat.sphere.{w} n` in any target universe `w`. -/
def sphereHomeomorphTopCatSphere {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] {n : ℕ}
    (hF : finrank ℝ F = n + 1) :
    sphere (0 : F) 1 ≃ₜ TopCat.sphere.{w} n :=
  haveI : FiniteDimensional ℝ F := Module.finite_of_finrank_eq_succ hF
  (sphereHomeomorphOfFinrankEq
      (hF.trans (finrank_euclideanSpace_ulift_fin.{w} (n + 1)).symm)).trans
    (diskBoundaryHomeomorph (n + 1)).symm

@[simp]
theorem sphereHomeomorphTopCatSphere_apply {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {n : ℕ} (hF : finrank ℝ F = n + 1) (x : sphere (0 : F) 1) :
    haveI : FiniteDimensional ℝ F := Module.finite_of_finrank_eq_succ hF
    sphereHomeomorphTopCatSphere.{w} hF x =
      (diskBoundaryHomeomorph (n + 1)).symm
        (sphereHomeomorphOfFinrankEq
          (hF.trans (finrank_euclideanSpace_ulift_fin.{w} (n + 1)).symm) x) :=
  (rfl)

@[simp]
theorem sphereHomeomorphTopCatSphere_symm_apply {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {n : ℕ} (hF : finrank ℝ F = n + 1) (y : TopCat.sphere.{w} n) :
    haveI : FiniteDimensional ℝ F := Module.finite_of_finrank_eq_succ hF
    (sphereHomeomorphTopCatSphere.{w} hF).symm y =
      (sphereHomeomorphOfFinrankEq
        (hF.trans (finrank_euclideanSpace_ulift_fin.{w} (n + 1)).symm)).symm
        (diskBoundaryHomeomorph (n + 1) y) :=
  (rfl)

end TauCeti

namespace ContinuousMap.HomotopyEquiv

section TopologicalSpace

variable {X : Type w} [TopologicalSpace X]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- Transport a homotopy equivalence `X ≃ₕ sphere (0 : F) 1` (with `F` in any universe and
`finrank ℝ F = n + 1`) to `X ≃ₕ TopCat.sphere.{w} n` in the universe of `X`. -/
def topCatSphere {n : ℕ} (e : X ≃ₕ sphere (0 : F) 1) (hF : finrank ℝ F = n + 1) :
    X ≃ₕ TopCat.sphere.{w} n :=
  e.trans (TauCeti.sphereHomeomorphTopCatSphere.{w} hF).toHomotopyEquiv

@[simp]
theorem topCatSphere_apply {n : ℕ} (e : X ≃ₕ sphere (0 : F) 1) (hF : finrank ℝ F = n + 1)
    (x : X) :
    e.topCatSphere hF x = TauCeti.sphereHomeomorphTopCatSphere.{w} hF (e x) :=
  (rfl)

@[simp]
theorem topCatSphere_symm_apply {n : ℕ} (e : X ≃ₕ sphere (0 : F) 1) (hF : finrank ℝ F = n + 1)
    (y : TopCat.sphere.{w} n) :
    (e.topCatSphere hF).symm y = e.symm ((TauCeti.sphereHomeomorphTopCatSphere.{w} hF).symm y) :=
  (rfl)

section Homology

variable {C : Type u} [Category.{v} C] [HasCoproducts.{w} C] [Abelian C] (R : C)

/-- **Reduced top homology of a space homotopy equivalent to `Sⁿ`.** For any `n : ℕ` and any real
normed space `F` of dimension `n + 1`, a homotopy equivalence `e : X ≃ₕ sphere (0 : F) 1` induces
an isomorphism `H~ₙ(X; R) ≅ R`. -/
def reducedSingularHomologySphereIso {n : ℕ} (e : X ≃ₕ sphere (0 : F) 1)
    (hF : finrank ℝ F = n + 1) :
    (TauCeti.reducedSingularHomologyFunctor R n).obj (TopCat.of X) ≅ R :=
  (e.topCatSphere hF).reducedSingularHomologyIso R n ≪≫
    TauCeti.reducedSingularHomologyTopCatSphereIso R n

@[simp]
theorem reducedSingularHomologySphereIso_hom {n : ℕ} (e : X ≃ₕ sphere (0 : F) 1)
    (hF : finrank ℝ F = n + 1) :
    (e.reducedSingularHomologySphereIso R hF).hom =
      (TauCeti.reducedSingularHomologyFunctor R n).map
          (TopCat.ofHom (e.topCatSphere hF).toFun) ≫
        (TauCeti.reducedSingularHomologyTopCatSphereIso R n).hom :=
  (Iso.trans_hom _ _).trans
    ((reducedSingularHomologyIso_hom R (e.topCatSphere hF) n) =≫
      (TauCeti.reducedSingularHomologyTopCatSphereIso R n).hom)

@[simp]
theorem reducedSingularHomologySphereIso_inv {n : ℕ} (e : X ≃ₕ sphere (0 : F) 1)
    (hF : finrank ℝ F = n + 1) :
    (e.reducedSingularHomologySphereIso R hF).inv =
      (TauCeti.reducedSingularHomologyTopCatSphereIso R n).inv ≫
        (TauCeti.reducedSingularHomologyFunctor R n).map
          (TopCat.ofHom (e.topCatSphere hF).invFun) :=
  (Iso.trans_inv _ _).trans
    (congrArg ((TauCeti.reducedSingularHomologyTopCatSphereIso R n).inv ≫ ·)
      (reducedSingularHomologyIso_inv R (e.topCatSphere hF) n))

/-- **Reduced homology of a space homotopy equivalent to `Sⁿ` vanishes outside degree `n`.** -/
theorem isZero_reducedSingularHomology_of_sphere_of_ne {n k : ℕ} (e : X ≃ₕ sphere (0 : F) 1)
    (hF : finrank ℝ F = n + 1) (hk : k ≠ n) :
    IsZero ((TauCeti.reducedSingularHomologyFunctor R k).obj (TopCat.of X)) :=
  (TauCeti.isZero_reducedSingularHomologyFunctor_topCatSphere_of_ne R hk).of_iso
    ((e.topCatSphere hF).reducedSingularHomologyIso R k)

/-- **Top singular homology of a space homotopy equivalent to `Sⁿ` (`1 ≤ n`).** For `1 ≤ n` and
`finrank ℝ F = n + 1`, a homotopy equivalence `e : X ≃ₕ sphere (0 : F) 1` induces an isomorphism
`Hₙ(X; R) ≅ R`. -/
def singularHomologySphereIso {n : ℕ} (e : X ≃ₕ sphere (0 : F) 1) (hF : finrank ℝ F = n + 1)
    (hn : 1 ≤ n) :
    ((AlgebraicTopology.singularHomologyFunctor C n).obj R).obj (TopCat.of X) ≅ R :=
  match n, hn with
  | m + 1, _ =>
    ((TauCeti.reducedSingularHomologySuccIso R m).app (TopCat.of X)).symm ≪≫
      e.reducedSingularHomologySphereIso R hF

@[simp]
theorem singularHomologySphereIso_succ_hom {m : ℕ} (e : X ≃ₕ sphere (0 : F) 1)
    (hF : finrank ℝ F = m + 1 + 1) (hm : 1 ≤ m + 1) :
    (e.singularHomologySphereIso R hF hm).hom =
      ((TauCeti.reducedSingularHomologySuccIso R m).app (TopCat.of X)).inv ≫
        (e.reducedSingularHomologySphereIso R hF).hom :=
  Iso.trans_hom _ _

@[simp]
theorem singularHomologySphereIso_succ_inv {m : ℕ} (e : X ≃ₕ sphere (0 : F) 1)
    (hF : finrank ℝ F = m + 1 + 1) (hm : 1 ≤ m + 1) :
    (e.singularHomologySphereIso R hF hm).inv =
      (e.reducedSingularHomologySphereIso R hF).inv ≫
        ((TauCeti.reducedSingularHomologySuccIso R m).app (TopCat.of X)).hom :=
  Iso.trans_inv _ _

/-- **Singular homology of a space homotopy equivalent to `Sⁿ` vanishes in positive degrees other
than `n`.** -/
theorem isZero_singularHomology_of_sphere_of_ne {n k : ℕ} (e : X ≃ₕ sphere (0 : F) 1)
    (hF : finrank ℝ F = n + 1) (hk₀ : k ≠ 0) (hkn : k ≠ n) :
    IsZero (((AlgebraicTopology.singularHomologyFunctor C k).obj R).obj (TopCat.of X)) :=
  match k, hk₀ with
  | q + 1, _ =>
    (TauCeti.isZero_singularHomologyFunctor_topCatSphere_of_ne R hkn).of_iso
      ((e.topCatSphere hF).singularHomologyIso R (q + 1))

end Homology

/-- A space homotopy equivalent to the unit sphere of a nontrivial real normed space is nonempty. -/
theorem nonempty_of_sphere [Nontrivial F] (e : X ≃ₕ sphere (0 : F) 1) :
    Nonempty X :=
  (NormedSpace.sphere_nonempty.2 zero_le_one).to_subtype.map e.symm

/-- A space homotopy equivalent to `Sⁿ` for `1 ≤ n` is path-connected. -/
theorem pathConnectedSpace_of_sphere {n : ℕ} (e : X ≃ₕ sphere (0 : F) 1)
    (hF : finrank ℝ F = n + 1) (hn : 1 ≤ n) :
    PathConnectedSpace X := by
  have : FiniteDimensional ℝ F := Module.finite_of_finrank_eq_succ hF
  have hrank : 1 < Module.rank ℝ F := by
    rw [← Module.finrank_eq_rank, hF]
    exact_mod_cast Nat.succ_lt_succ hn
  have : PathConnectedSpace (sphere (0 : F) 1) :=
    isPathConnected_iff_pathConnectedSpace.1 (isPathConnected_sphere hrank 0 zero_le_one)
  exact e.symm.pathConnectedSpace

/-- A space homotopy equivalent to `Sⁿ` for `1 ≤ n` is connected. -/
theorem connectedSpace_of_sphere {n : ℕ} (e : X ≃ₕ sphere (0 : F) 1)
    (hF : finrank ℝ F = n + 1) (hn : 1 ≤ n) :
    ConnectedSpace X := by
  have := e.pathConnectedSpace_of_sphere hF hn
  infer_instance

/-- A space homotopy equivalent to `Sⁿ` for `2 ≤ n` is simply connected. -/
theorem simplyConnectedSpace_of_sphere {n : ℕ} (e : X ≃ₕ sphere (0 : F) 1)
    (hF : finrank ℝ F = n + 1) (hn : 2 ≤ n) :
    SimplyConnectedSpace X := by
  have : FiniteDimensional ℝ F := Module.finite_of_finrank_eq_succ hF
  have hrank : 2 < Module.rank ℝ F := by
    rw [← Module.finrank_eq_rank, hF]
    exact_mod_cast Nat.succ_lt_succ hn
  have : SimplyConnectedSpace (sphere (0 : F) 1) :=
    TauCeti.simplyConnectedSpace_sphere hrank 0 zero_le_one
  exact e.simplyConnectedSpace

end TopologicalSpace

section Manifold

variable {M : Type w} [TopologicalSpace M] [T2Space M]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [ChartedSpace E M]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- **A Hausdorff `n`-manifold homotopy equivalent to `Sⁿ` is compact.** -/
theorem compactSpace_of_sphere {n : ℕ} (e : M ≃ₕ sphere (0 : F) 1) (hE : finrank ℝ E = n)
    (hF : finrank ℝ F = n + 1) :
    CompactSpace M := by
  rcases n with _ | m
  · have : Subsingleton E := Module.finrank_zero_iff.1 hE
    have : DiscreteTopology M := discreteTopology_iff_isOpen_singleton.2 fun x ↦ by
      have hsrc : (chartAt E x).source = {x} :=
        eq_singleton_iff_unique_mem.2 ⟨mem_chart_source E x, fun y hy ↦
          (chartAt E x).injOn hy (mem_chart_source E x) (Subsingleton.elim _ _)⟩
      exact hsrc ▸ (chartAt E x).open_source
    have : Finite (sphere (0 : F) 1) := TauCeti.finite_sphere_of_finrank_eq_one hF 0 1
    have : Finite (ZerothHomotopy (sphere (0 : F) 1)) :=
      Finite.of_surjective _ ZerothHomotopy.mk_surjective
    have : Finite (ZerothHomotopy M) := Finite.of_equiv _ e.zerothHomotopyCongr.symm
    have : Finite M :=
      Finite.of_injective _ ZerothHomotopy.mk_injective_of_totallyDisconnectedSpace
    exact Finite.compactSpace
  · have := e.connectedSpace_of_sphere hF (Nat.succ_pos m)
    let N : ModuleCat.{w} (ULift.{w} ℤ) := ModuleCat.of (ULift.{w} ℤ) (ULift.{w} ℤ)
    have hN : ¬ IsZero N := fun h ↦
      one_ne_zero (α := ULift.{w} ℤ) ((ModuleCat.subsingleton_of_isZero h).elim 1 0)
    have hH : ¬ IsZero (((AlgebraicTopology.singularHomologyFunctor
        (ModuleCat.{w} (ULift.{w} ℤ)) (m + 1)).obj N).obj (TopCat.of M)) :=
      fun h ↦ hN (h.of_iso (e.singularHomologySphereIso N hF (Nat.succ_pos m)).symm)
    exact TauCeti.compactSpace_of_not_isZero_singularHomology N hE le_rfl hH

/-- **A Hausdorff `n`-manifold homotopy equivalent to `Sⁿ` is second countable.** -/
theorem secondCountableTopology_of_sphere {n : ℕ} (e : M ≃ₕ sphere (0 : F) 1)
    (hE : finrank ℝ E = n) (hF : finrank ℝ F = n + 1) :
    SecondCountableTopology M := by
  have := e.compactSpace_of_sphere hE hF
  let L : E ≃L[ℝ] Fin (finrank ℝ E) → ℝ :=
    ContinuousLinearEquiv.ofFinrankEq (Module.finrank_fin_fun ℝ).symm
  have := L.toHomeomorph.secondCountableTopology
  exact ChartedSpace.secondCountable_of_sigmaCompact E M

end Manifold

end ContinuousMap.HomotopyEquiv

namespace TauCeti

section Obstructions

/-- **No contractible space is homotopy equivalent to a sphere.** For any contractible space `X`
and any nontrivial finite-dimensional real normed space `F`, `X ≃ₕ sphere (0 : F) 1` is empty,
including for the two-point zero-sphere when `finrank ℝ F = 1`. -/
theorem isEmpty_homotopyEquiv_sphere_of_contractibleSpace (X : Type*) [TopologicalSpace X]
    [ContractibleSpace X] (F : Type*) [NormedAddCommGroup F] [NormedSpace ℝ F]
    [FiniteDimensional ℝ F] [Nontrivial F] :
    IsEmpty (X ≃ₕ sphere (0 : F) 1) :=
  ⟨fun e ↦ not_contractibleSpace_sphere e.symm.contractibleSpace⟩

/-- **No real normed space is homotopy equivalent to a sphere.** For any real normed space `E` and
any nontrivial finite-dimensional real normed space `F`, `E ≃ₕ sphere (0 : F) 1` is empty. -/
theorem isEmpty_normedSpace_homotopyEquiv_sphere (E F : Type*) [NormedAddCommGroup E]
    [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
    [Nontrivial F] :
    IsEmpty (E ≃ₕ sphere (0 : F) 1) :=
  isEmpty_homotopyEquiv_sphere_of_contractibleSpace E F

/-- **No Euclidean space is homotopy equivalent to a sphere.** In particular, `ℝ³` is not homotopy
equivalent to `S³`. -/
instance isEmpty_euclideanSpace_homotopyEquiv_sphere (ι : Type*) [Finite ι] (n : ℕ) :
    IsEmpty (EuclideanSpace ℝ ι ≃ₕ sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1) := by
  cases nonempty_fintype ι
  exact isEmpty_normedSpace_homotopyEquiv_sphere (EuclideanSpace ℝ ι)
    (EuclideanSpace ℝ (Fin (n + 1)))

/-- **No noncompact Hausdorff `n`-manifold is homotopy equivalent to `Sⁿ`.** -/
theorem isEmpty_homotopyEquiv_sphere_of_not_compactSpace {M : Type*} [TopologicalSpace M]
    [T2Space M] {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [ChartedSpace E M] {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] {n : ℕ}
    (hE : finrank ℝ E = n) (hF : finrank ℝ F = n + 1) (hM : ¬ CompactSpace M) :
    IsEmpty (M ≃ₕ sphere (0 : F) 1) :=
  ⟨fun e ↦ hM (e.compactSpace_of_sphere hE hF)⟩

/-- **No proper open subset of a connected Hausdorff `n`-manifold is homotopy equivalent to
`Sⁿ`.** -/
theorem isEmpty_open_ne_univ_homotopyEquiv_sphere {M : Type*} [TopologicalSpace M] [T2Space M]
    [ConnectedSpace M] {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [ChartedSpace E M] {F : Type*} [NormedAddCommGroup F]
    [NormedSpace ℝ F] {n : ℕ} (hE : finrank ℝ E = n) (hF : finrank ℝ F = n + 1) {U : Set M}
    (hUo : IsOpen U) (hU : U ≠ univ) :
    IsEmpty (U ≃ₕ sphere (0 : F) 1) := by
  refine ⟨fun e ↦ hU ?_⟩
  have : Nontrivial F := Module.nontrivial_of_finrank_eq_succ hF
  have : Nonempty U := e.nonempty_of_sphere
  obtain ⟨x⟩ := ‹Nonempty U›
  let _ : ChartedSpace M U := hUo.isOpenEmbedding_subtypeVal.singletonChartedSpace
  let _ : ChartedSpace E U := ChartedSpace.comp E M U
  have hUc : IsCompact U := isCompact_iff_compactSpace.2 (e.compactSpace_of_sphere hE hF)
  exact IsClopen.eq_univ ⟨hUc.isClosed, hUo⟩ ⟨x.1, x.2⟩

end Obstructions

section PoincareConjecture

/-- For `1 ≤ n`, Mathlib's smooth Poincaré statement
`ContinuousMap.HomotopyEquiv.NonemptyDiffeomorphSphere M n` is equivalent to the same statement
restricted to compact path-connected second-countable smooth `n`-manifolds. -/
theorem nonemptyDiffeomorphSphere_iff_of_one_le (M : Type*) [TopologicalSpace M] [T2Space M]
    {n : ℕ} (hn : 1 ≤ n) :
    ContinuousMap.HomotopyEquiv.NonemptyDiffeomorphSphere M n ↔
      ∀ (_ : ChartedSpace (EuclideanSpace ℝ (Fin n)) M) (_ : IsManifold (𝓡 n) ∞ M)
        [CompactSpace M] [PathConnectedSpace M] [SecondCountableTopology M],
        (M ≃ₕ sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1) →
          Nonempty (M ≃ₘ⟮𝓡 n, 𝓡 n⟯ sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1) := by
  constructor
  · intro h c hm _ _ _ e
    exact h c hm e
  · intro h c hm e
    have := e.compactSpace_of_sphere (finrank_euclideanSpace_fin (𝕜 := ℝ) (n := n))
      (finrank_euclideanSpace_fin (𝕜 := ℝ) (n := n + 1))
    have := e.pathConnectedSpace_of_sphere
      (finrank_euclideanSpace_fin (𝕜 := ℝ) (n := n + 1)) hn
    have := e.secondCountableTopology_of_sphere (finrank_euclideanSpace_fin (𝕜 := ℝ) (n := n))
      (finrank_euclideanSpace_fin (𝕜 := ℝ) (n := n + 1))
    exact h c hm e

/-- For `2 ≤ n`, Mathlib's smooth Poincaré statement
`ContinuousMap.HomotopyEquiv.NonemptyDiffeomorphSphere M n` is equivalent to the same statement
restricted to compact simply connected second-countable smooth `n`-manifolds. -/
theorem nonemptyDiffeomorphSphere_iff_of_two_le (M : Type*) [TopologicalSpace M] [T2Space M]
    {n : ℕ} (hn : 2 ≤ n) :
    ContinuousMap.HomotopyEquiv.NonemptyDiffeomorphSphere M n ↔
      ∀ (_ : ChartedSpace (EuclideanSpace ℝ (Fin n)) M) (_ : IsManifold (𝓡 n) ∞ M)
        [CompactSpace M] [SimplyConnectedSpace M] [SecondCountableTopology M],
        (M ≃ₕ sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1) →
          Nonempty (M ≃ₘ⟮𝓡 n, 𝓡 n⟯ sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1) := by
  constructor
  · intro h c hm _ _ _ e
    exact h c hm e
  · intro h c hm e
    have := e.compactSpace_of_sphere (finrank_euclideanSpace_fin (𝕜 := ℝ) (n := n))
      (finrank_euclideanSpace_fin (𝕜 := ℝ) (n := n + 1))
    have := e.simplyConnectedSpace_of_sphere
      (finrank_euclideanSpace_fin (𝕜 := ℝ) (n := n + 1)) hn
    have := e.secondCountableTopology_of_sphere (finrank_euclideanSpace_fin (𝕜 := ℝ) (n := n))
      (finrank_euclideanSpace_fin (𝕜 := ℝ) (n := n + 1))
    exact h c hm e

/-- For `2 ≤ n`, if every compact simply connected second-countable smooth `n`-manifold structure on
`M` is diffeomorphic to `Sⁿ`, then `ContinuousMap.HomotopyEquiv.NonemptyDiffeomorphSphere M n`
holds. -/
theorem nonemptyDiffeomorphSphere_of_closed_simplyConnected (M : Type*) [TopologicalSpace M]
    [T2Space M] {n : ℕ} (hn : 2 ≤ n)
    (h : ∀ (_ : ChartedSpace (EuclideanSpace ℝ (Fin n)) M) (_ : IsManifold (𝓡 n) ∞ M)
      [CompactSpace M] [SimplyConnectedSpace M] [SecondCountableTopology M],
      Nonempty (M ≃ₘ⟮𝓡 n, 𝓡 n⟯ sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1)) :
    ContinuousMap.HomotopyEquiv.NonemptyDiffeomorphSphere M n := by
  refine (nonemptyDiffeomorphSphere_iff_of_two_le M hn).2 ?_
  intro c hm _ _ _ _
  exact h c hm

/-- For `2 ≤ n`, the topological generalized Poincaré statement (every Hausdorff `n`-manifold
structure on `M` homotopy equivalent to `Sⁿ` is homeomorphic to `Sⁿ`) is equivalent to its
restriction to compact simply connected second-countable `n`-manifolds. -/
theorem nonempty_homeomorph_sphere_of_homotopyEquiv_iff_of_two_le (M : Type*)
    [TopologicalSpace M] [T2Space M] (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] {n : ℕ}
    (hE : finrank ℝ E = n) (hF : finrank ℝ F = n + 1) (hn : 2 ≤ n) :
    (∀ (_ : ChartedSpace E M), (M ≃ₕ sphere (0 : F) 1) → Nonempty (M ≃ₜ sphere (0 : F) 1)) ↔
      ∀ (_ : ChartedSpace E M) [CompactSpace M] [SimplyConnectedSpace M]
        [SecondCountableTopology M],
        (M ≃ₕ sphere (0 : F) 1) → Nonempty (M ≃ₜ sphere (0 : F) 1) := by
  constructor
  · intro h c _ _ _ e
    exact h c e
  · intro h c e
    have := e.compactSpace_of_sphere hE hF
    have := e.simplyConnectedSpace_of_sphere hF hn
    have := e.secondCountableTopology_of_sphere hE hF
    exact h c e

/-- For `2 ≤ n`, if every compact simply connected second-countable `n`-manifold structure on `M`
is homeomorphic to `Sⁿ`, then every Hausdorff `n`-manifold structure on `M` homotopy equivalent to
`Sⁿ` is homeomorphic to `Sⁿ`. -/
theorem nonempty_homeomorph_sphere_of_closed_simplyConnected (M : Type*) [TopologicalSpace M]
    [T2Space M] (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] {n : ℕ}
    (hE : finrank ℝ E = n) (hF : finrank ℝ F = n + 1) (hn : 2 ≤ n)
    (h : ∀ (_ : ChartedSpace E M) [CompactSpace M] [SimplyConnectedSpace M]
      [SecondCountableTopology M], Nonempty (M ≃ₜ sphere (0 : F) 1)) :
    ∀ (_ : ChartedSpace E M), (M ≃ₕ sphere (0 : F) 1) → Nonempty (M ≃ₜ sphere (0 : F) 1) := by
  refine (nonempty_homeomorph_sphere_of_homotopyEquiv_iff_of_two_le M E hE hF hn).2 ?_
  intro c _ _ _ _
  exact h c

end PoincareConjecture

end TauCeti
