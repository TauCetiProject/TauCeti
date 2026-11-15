/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Singular.Fibration.Comparison
public import TauCeti.AlgebraicTopology.Singular.ModuleChains.Basic
public import TauCeti.Topology.Homotopy.MappingPath.Exact

import TauCeti.Topology.Homotopy.SerreFibration.Connected

/-!
# Serre fibrations with acyclic fibres induce homology isomorphisms

Let `p : E ⟶ B` be a Serre fibration and `R` a ring. If every fibre `p⁻¹(b)` is path-connected and
`H_q(p⁻¹(b); R) = 0` for `0 < q ≤ n`, then `p` induces an isomorphism `H_n(E; R) ≅ H_n(B; R)`
(`TauCeti.TopCat.isIso_singularHomologyMap_of_forall_fiber`). No CW, separation, or connectivity
hypothesis is imposed on `B` or `E`.

For each fibre `p⁻¹(b)`, path-connectedness implies that the map `p⁻¹(b) ⟶ *` to a point induces an
isomorphism on `H_0(-; R)` via the singular augmentation
(`TauCeti.singularHomologyMap_singularHomology₀ε`), while vanishing of `H_q(p⁻¹(b); R)` for
`0 < q ≤ n` makes `p⁻¹(b) ⟶ *` an isomorphism in positive degrees up to `n`; the homology
isomorphism for `p` then follows from
`TauCeti.TopCat.isIso_singularHomologyMap_of_isIso_fiber_to_point`.

When `B` is path-connected, the fibres of `p` over any two points of `B` are connected by a
zigzag of weak homotopy equivalences through the pullback of `p` along a path between them:
`p` pulls back to a Serre fibration over the contractible unit interval, and both endpoint fibre
inclusions are weak homotopy equivalences
(`TauCeti.TopCat.isNConnected_fiberι_of_mem_serreFibrations`). Hence path-connectedness and the
singular homology of `p⁻¹(b)` do not depend on `b`
(`TauCeti.TopCat.pathConnectedSpace_fiber_iff_of_joined`,
`TauCeti.TopCat.singularHomologyFiberIsoOfJoined`), and over a path-connected base it suffices to
check the condition on a single fibre (`TauCeti.TopCat.isIso_singularHomologyMap_of_fiber`).

Applied to the fixed-end path fibration `P_x X ⟶ X` of a simply connected space `(X, x)`, whose
total space is contractible and whose fibre over `x` is the loop space `Ω X x`, this shows that
`H_{n+1}(X; R) = 0` as soon as `H_{q+1}(Ω X x; R) = 0` for `q ≤ n`
(`TauCeti.isZero_singularHomology_of_loopSpace`).

## Main results

* `TauCeti.TopCat.pathConnectedSpace_fiber_iff_of_joined`,
  `TauCeti.TopCat.singularHomologyFiberIsoOfJoined`,
  `TauCeti.TopCat.isZero_singularHomology_fiber_iff_of_joined`: invariance of path-connectedness
  and singular homology of the fibres of a Serre fibration along paths in the base.
* `TauCeti.TopCat.isIso_singularHomologyMap_of_forall_fiber`: a Serre fibration whose fibres are
  path-connected with vanishing `R`-homology in degrees `0 < q ≤ n` induces an isomorphism on
  `H_n(-; R)`.
* `TauCeti.TopCat.isIso_singularHomologyMap_of_fiber`: the single-fibre form over a path-connected
  base.
* `TauCeti.isZero_singularHomology_of_loopSpace`: a simply connected space whose loop space has
  vanishing `R`-homology in positive degrees `≤ n + 1` has vanishing `H_{n+1}(-; R)`.

## References

* J.-P. Serre, *Homologie singulière des espaces fibrés. Applications*, Ann. of Math. 54 (1951),
  Chapter II.
* A. Hatcher, [*Algebraic Topology*](https://pi.math.cornell.edu/~hatcher/AT/AT.pdf),
  Section 5.1, Corollary 5.4, and Section 5.3.
-/

public section

noncomputable section

open AlgebraicTopology CategoryTheory Limits
open scoped Topology Topology.Homotopy unitInterval

universe u

namespace TauCeti

namespace TopCat

section JoinedFibers

variable {E B : _root_.TopCat.{u}} {p : E ⟶ B}

/-- Pulling a Serre fibration `p : E ⟶ B` back along a path `γ : I → B` (lifted to `ULift.{u} I`)
produces a weak homotopy equivalence from `p⁻¹(γ t)` into the pullback over `ULift.{u} I`, because
the interval is contractible. -/
private theorem isWeakHomotopyEquivalence_fiberPullback (hp : serreFibrations p)
    {b₀ b₁ : B} (γ : Path b₀ b₁) (t : ULift.{u} I) :
    let g : _root_.TopCat.of (ULift.{u} I) ⟶ B :=
      _root_.TopCat.ofHom ⟨fun s ↦ γ s.down, γ.continuous.comp continuous_uliftDown⟩
    ((p.fiberPullbackFstIso g t).inv ≫ (_root_.TopCat.pullbackFst g p).fiberι t).hom
      |>.IsWeakHomotopyEquivalence := by
  intro g
  have hI : ContractibleSpace I := (convex_Icc (0 : ℝ) 1).contractibleSpace ⟨0, by simp⟩
  have hUI : ContractibleSpace (ULift.{u} I) := Homeomorph.ulift.contractibleSpace
  have hι : ((_root_.TopCat.pullbackFst g p).fiberι t).hom.IsWeakHomotopyEquivalence :=
    ContinuousMap.isWeakHomotopyEquivalence_iff_forall_isNConnected.2 fun n ↦
      isNConnected_fiberι_of_mem_serreFibrations (mem_serreFibrations_pullbackFst hp g)
        fun _ _ ↦ inferInstance
  have he : (p.fiberPullbackFstIso g t).inv.hom.IsWeakHomotopyEquivalence :=
    (_root_.TopCat.homeoOfIso (p.fiberPullbackFstIso g t).symm).toHomotopyEquiv
      |>.isWeakHomotopyEquivalence
  exact hι.comp he

/-- **Fibres of a Serre fibration over points in the same path component are simultaneously
path-connected.** -/
theorem pathConnectedSpace_fiber_iff_of_joined (hp : serreFibrations p) {b₀ b₁ : B}
    (hb : Joined b₀ b₁) : PathConnectedSpace (p.fiber b₀) ↔ PathConnectedSpace (p.fiber b₁) := by
  let γ := hb.somePath
  let g : _root_.TopCat.of (ULift.{u} I) ⟶ B :=
    _root_.TopCat.ofHom ⟨fun s ↦ γ s.down, γ.continuous.comp continuous_uliftDown⟩
  have hg₀ : g ⟨0⟩ = b₀ := γ.source
  have hg₁ : g ⟨1⟩ = b₁ := γ.target
  have h₀ := (isWeakHomotopyEquivalence_fiberPullback hp γ ⟨0⟩).pathConnectedSpace_iff
  have h₁ := (isWeakHomotopyEquivalence_fiberPullback hp γ ⟨1⟩).pathConnectedSpace_iff
  rw [hg₀] at h₀
  rw [hg₁] at h₁
  exact h₀.trans h₁.symm

/-- **Fibres of a Serre fibration over points in the same path component have isomorphic singular
homology** with coefficients in any module `M`. -/
def singularHomologyFiberIsoOfJoined (hp : serreFibrations p) {b₀ b₁ : B} (hb : Joined b₀ b₁)
    {A : Type*} [Ring A] (M : ModuleCat.{u} A) (n : ℕ) :
    ((singularHomologyFunctor (ModuleCat.{u} A) n).obj M).obj (p.fiber b₀) ≅
      ((singularHomologyFunctor (ModuleCat.{u} A) n).obj M).obj (p.fiber b₁) := by
  let γ := hb.somePath
  let g : _root_.TopCat.of (ULift.{u} I) ⟶ B :=
    _root_.TopCat.ofHom ⟨fun s ↦ γ s.down, γ.continuous.comp continuous_uliftDown⟩
  let H := (singularHomologyFunctor (ModuleCat.{u} A) n).obj M
  have := (isWeakHomotopyEquivalence_fiberPullback hp γ ⟨0⟩).isIso_singularHomologyMap M n
  have := (isWeakHomotopyEquivalence_fiberPullback hp γ ⟨1⟩).isIso_singularHomologyMap M n
  exact H.mapIso (eqToIso (congrArg p.fiber γ.source.symm)) ≪≫
    asIso (H.map ((p.fiberPullbackFstIso g ⟨0⟩).inv ≫
      (_root_.TopCat.pullbackFst g p).fiberι ⟨0⟩)) ≪≫
    (asIso (H.map ((p.fiberPullbackFstIso g ⟨1⟩).inv ≫
      (_root_.TopCat.pullbackFst g p).fiberι ⟨1⟩))).symm ≪≫
    H.mapIso (eqToIso (congrArg p.fiber γ.target))

/-- **Vanishing of fibre homology is invariant along paths in the base** for any Serre fibration. -/
theorem isZero_singularHomology_fiber_iff_of_joined (hp : serreFibrations p) {b₀ b₁ : B}
    (hb : Joined b₀ b₁) {A : Type*} [Ring A] (M : ModuleCat.{u} A) (n : ℕ) :
    IsZero (((singularHomologyFunctor (ModuleCat.{u} A) n).obj M).obj (p.fiber b₀)) ↔
      IsZero (((singularHomologyFunctor (ModuleCat.{u} A) n).obj M).obj (p.fiber b₁)) :=
  Iso.isZero_iff (singularHomologyFiberIsoOfJoined hp hb M n)

end JoinedFibers

/-- **A Serre fibration whose fibres have the `R`-homology of a point through degree `n` induces an
isomorphism on `H_n(-; R)`.** Let `p : E ⟶ B` be a Serre fibration over an arbitrary topological
space `B`, and let `R` be a ring. If every fibre `p⁻¹(b)` is path-connected and has vanishing
`R`-homology in degrees `0 < q ≤ n`, then `p` induces an isomorphism `H_n(E; R) ≅ H_n(B; R)`. -/
theorem isIso_singularHomologyMap_of_forall_fiber {E B : _root_.TopCat.{u}} {p : E ⟶ B}
    (hp : serreFibrations p) (R : Type u) [Ring R] (n : ℕ)
    (hF₀ : ∀ b : B, PathConnectedSpace (p.fiber b))
    (hF : ∀ b : B, ∀ q, 0 < q → q ≤ n →
      IsZero (((singularHomologyFunctor (ModuleCat.{u} R) q).obj
        (ModuleCat.of R R)).obj (p.fiber b))) :
    IsIso (((singularHomologyFunctor (ModuleCat.{u} R) n).obj (ModuleCat.of R R)).map p) := by
  refine isIso_singularHomologyMap_of_isIso_fiber_to_point hp R n fun b q hq ↦ ?_
  rcases q with _ | q
  · have := hF₀ b
    exact IsIso.of_isIso_fac_right
      (singularHomologyMap_singularHomology₀ε (ModuleCat.of R R)
        (_root_.TopCat.isTerminalPUnit.from (p.fiber b)))
  · exact (hF b (q + 1) q.succ_pos hq).isIso
      (isZero_singularHomologyFunctor_of_contractibleSpace (ModuleCat.of R R) _ q.succ_ne_zero) _

/-- **Single-fibre homology isomorphism criterion for a Serre fibration over a path-connected
base.** Let `p : E ⟶ B` be a Serre fibration over a path-connected space `B`, and let `b₀ : B`. If
the fibre `p⁻¹(b₀)` is path-connected and has vanishing `R`-homology in degrees `0 < q ≤ n`, then
`p` induces an isomorphism `H_n(E; R) ≅ H_n(B; R)`. -/
theorem isIso_singularHomologyMap_of_fiber {E B : _root_.TopCat.{u}} [PathConnectedSpace B]
    {p : E ⟶ B} (hp : serreFibrations p) (b₀ : B) (R : Type u) [Ring R] (n : ℕ)
    (hF₀ : PathConnectedSpace (p.fiber b₀))
    (hF : ∀ q, 0 < q → q ≤ n →
      IsZero (((singularHomologyFunctor (ModuleCat.{u} R) q).obj
        (ModuleCat.of R R)).obj (p.fiber b₀))) :
    IsIso (((singularHomologyFunctor (ModuleCat.{u} R) n).obj (ModuleCat.of R R)).map p) :=
  isIso_singularHomologyMap_of_forall_fiber hp R n
    (fun b ↦ (pathConnectedSpace_fiber_iff_of_joined hp (PathConnectedSpace.joined b₀ b)).1 hF₀)
    fun b q hq hqn ↦
      (isZero_singularHomology_fiber_iff_of_joined hp (PathConnectedSpace.joined b₀ b)
        (ModuleCat.of R R) q).1 (hF q hq hqn)

end TopCat

/-- **A simply connected space whose loop space has vanishing positive `R`-homology through degree
`n + 1` has vanishing `H_{n+1}(-; R)`.** Let `(X, x)` be a path-connected space with trivial
`π₁(X, x)`, and let `R` be a ring. If `H_{q+1}(Ω X x; R) = 0` for every `q ≤ n`, then
`H_{n+1}(X; R) = 0`. -/
theorem isZero_singularHomology_of_loopSpace {X : Type u} [TopologicalSpace X]
    [PathConnectedSpace X] (x : X) (hπ₁ : Subsingleton (π_ 1 X x)) (R : Type u) [Ring R]
    (n : ℕ)
    (hΩ : ∀ q ≤ n, IsZero (((singularChains R).obj (_root_.TopCat.of (Ω X x))).homology (q + 1))) :
    IsZero (((singularChains R).obj (_root_.TopCat.of X)).homology (n + 1)) := by
  let p := _root_.TopCat.Hom.homotopyFiberProj (𝟙 (_root_.TopCat.of X)) x
  let e := _root_.TopCat.Hom.homotopyFiberFiberHomeomorph (𝟙 (_root_.TopCat.of X)) x
  have hΩ₀ : PathConnectedSpace (Ω X x) :=
    (pathConnectedSpace_loopSpace_iff_subsingleton_pi1 x).2 hπ₁
  have hF₀ : PathConnectedSpace (p.fiber x) := @Homeomorph.pathConnectedSpace _ _ _ _ hΩ₀ e.symm
  have hF (q : ℕ) (hq : 0 < q) (hqn : q ≤ n + 1) :
      IsZero (((singularHomologyFunctor (ModuleCat.{u} R) q).obj (ModuleCat.of R R)).obj
        (p.fiber x)) := by
    obtain ⟨m, rfl⟩ : ∃ m, q = m + 1 := ⟨q - 1, by omega⟩
    exact (hΩ m (by omega)).of_iso (((singularHomologyFunctor (ModuleCat.{u} R) (m + 1)).obj
      (ModuleCat.of R R)).mapIso (_root_.TopCat.isoOfHomeo e))
  have : IsIso (((singularHomologyFunctor (ModuleCat.{u} R) (n + 1)).obj
      (ModuleCat.of R R)).map p) :=
    TopCat.isIso_singularHomologyMap_of_fiber
      (_root_.TopCat.Hom.serreFibrations_homotopyFiberProj (𝟙 (_root_.TopCat.of X)) x)
      x R (n + 1) hF₀ hF
  have hEP : IsZero (((singularHomologyFunctor (ModuleCat.{u} R) (n + 1)).obj
      (ModuleCat.of R R)).obj (_root_.TopCat.of (MappingPathFiber (.id X) x))) :=
    isZero_singularHomologyFunctor_of_contractibleSpace (ModuleCat.of R R)
      (_root_.TopCat.of (MappingPathFiber (.id X) x)) (Nat.succ_ne_zero n)
  exact hEP.of_iso (asIso (((singularHomologyFunctor (ModuleCat.{u} R) (n + 1)).obj
    (ModuleCat.of R R)).map p)).symm

end TauCeti
