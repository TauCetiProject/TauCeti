/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Singular.Fibration.Comparison
public import TauCeti.AlgebraicTopology.Singular.ModuleChains.Basic

import TauCeti.AlgebraicTopology.Singular.Fibration.SerreLocalSystem
import TauCeti.Topology.Homotopy.MappingPath.PathFibration

/-!
# Fibre homology invariance and single-fibre acyclicity for Serre fibrations

When `p : E ⟶ B` is a Serre fibration, the fibres over any two points in the same path component
of `B` are connected by a zigzag of weak homotopy equivalences through the pullback of `p` along a
path between them (`TauCeti.TopCat.exists_isWeakHomotopyEquivalence_fiber_of_joined`, in
`TauCeti.Topology.Homotopy.SerreFibration.WeakHomotopyEquivalence`). Consequently,
path-connectedness (`TauCeti.TopCat.pathConnectedSpace_fiber_iff_of_joined`) and, via the
transport isomorphism `TauCeti.TopCat.fiberHomologyTransport` along a path, vanishing of the
singular homology of `p⁻¹(b)` with coefficients in any module `M` are constant along path components
of `B` (`TauCeti.TopCat.isZero_singularHomology_fiber_iff_of_joined`).

Combined with the all-fibre comparison theorem
`TauCeti.TopCat.isIso_singularHomologyMap_of_isZero_fiber` (from
`TauCeti.AlgebraicTopology.Singular.Fibration.Comparison`), over a path-connected base `B` it
suffices to verify path-connectedness and vanishing of positive-degree `R`-homology on a single
fibre `p⁻¹(b₀)` to conclude that `p` induces an isomorphism `H_n(E; R) ≅ H_n(B; R)`
(`TauCeti.TopCat.isIso_singularHomologyMap_of_isZero_singleFiber`). No CW, separation, or
connectivity hypothesis beyond path-connectedness is imposed on `B` or `E`.

Applied to the fixed-end path fibration `P_x X ⟶ X` of a simply connected space `(X, x)`, whose
total space is contractible and whose fibre over `x` is the loop space `Ω X x`, this shows that
`H_{n+1}(X; R) = 0` as soon as `H_{q+1}(Ω X x; R) = 0` for `q ≤ n`
(`TauCeti.isZero_singularHomology_of_isZero_loopSpace_homology`).

## Main results

* `TauCeti.TopCat.isZero_singularHomology_fiber_iff_of_joined`: invariance of vanishing of the
  singular homology of the fibres of a Serre fibration along paths in the base.
* `TauCeti.TopCat.isIso_singularHomologyMap_of_isZero_singleFiber`: single-fibre form over a
  path-connected base of `TauCeti.TopCat.isIso_singularHomologyMap_of_isZero_fiber`.
* `TauCeti.isZero_singularHomology_of_isZero_loopSpace_homology`: a simply connected space whose
  loop space has vanishing `R`-homology in positive degrees `≤ n + 1` has vanishing `H_{n+1}(-; R)`.

## References

* J.-P. Serre, *Homologie singulière des espaces fibrés. Applications*, Ann. of Math. 54 (1951),
  Chapter II.
* J. McCleary, *A User's Guide to Spectral Sequences*, 2nd ed., Cambridge University Press, 2001,
  Section 5.1.
* A. Hatcher,
  [*Spectral Sequences in Algebraic Topology*](https://pi.math.cornell.edu/~hatcher/SSAT/SSch1.pdf),
  Chapter 1, Section 1.1.
* A. Hatcher, [*Algebraic Topology*](https://pi.math.cornell.edu/~hatcher/AT/AT.pdf),
  Section 4.3 (the path-loop fibration).
-/

public section

noncomputable section

open AlgebraicTopology CategoryTheory Limits
open scoped Topology Topology.Homotopy

universe u

namespace TauCeti.TopCat

section JoinedFibers

variable {E B : TopCat.{u}} {p : E ⟶ B}

/-- **Vanishing of fibre homology is invariant along paths in the base** for any Serre fibration. -/
theorem isZero_singularHomology_fiber_iff_of_joined (hp : serreFibrations p) {b₀ b₁ : B}
    (hb : Joined b₀ b₁) {A : Type*} [Ring A] (M : ModuleCat.{u} A) (n : ℕ) :
    IsZero (((singularHomologyFunctor (ModuleCat.{u} A) n).obj M).obj (p.fiber b₀)) ↔
      IsZero (((singularHomologyFunctor (ModuleCat.{u} A) n).obj M).obj (p.fiber b₁)) := by
  let γ := hb.somePath
  let g := (_root_.TopCat.pathEquiv.symm γ).hom
  have : IsIso (fiberHomologyTransport hp M n γ) := by
    rw [fiberHomologyTransport_eq_pullbackFiberTransport]
    exact ⟨pullbackFiberTransport hp M n g
        (_root_.TopCat.pathEquiv.symm γ).hom₁ (_root_.TopCat.pathEquiv.symm γ).hom₀,
      by simp [g], by simp [g]⟩
  exact (asIso (fiberHomologyTransport hp M n γ)).isZero_iff

end JoinedFibers

/-- **Single-fibre homology isomorphism criterion for a Serre fibration over a path-connected
base.** Let `p : E ⟶ B` be a Serre fibration over a path-connected space `B`, and let `b₀ : B`. If
the fibre `p⁻¹(b₀)` is path-connected and has vanishing `R`-homology in the positive degrees
`q ≤ n`, then `p` induces an isomorphism `H_n(E; R) ≅ H_n(B; R)`. -/
theorem isIso_singularHomologyMap_of_isZero_singleFiber {E B : TopCat.{u}} [PathConnectedSpace B]
    {p : E ⟶ B} (hp : serreFibrations p) (b₀ : B) (R : Type u) [Ring R] (n : ℕ)
    (hF₀ : PathConnectedSpace (p.fiber b₀))
    (hF : ∀ q, q ≠ 0 → q ≤ n →
      IsZero (((singularHomologyFunctor (ModuleCat.{u} R) q).obj
        (ModuleCat.of R R)).obj (p.fiber b₀))) :
    IsIso (((singularHomologyFunctor (ModuleCat.{u} R) n).obj (ModuleCat.of R R)).map p) :=
  isIso_singularHomologyMap_of_isZero_fiber hp R n
    (fun b ↦ (pathConnectedSpace_fiber_iff_of_joined hp (PathConnectedSpace.joined b₀ b)).1 hF₀)
    fun b q hq hqn ↦
      (isZero_singularHomology_fiber_iff_of_joined hp (PathConnectedSpace.joined b₀ b)
        (ModuleCat.of R R) q).1 (hF q hq hqn)

end TauCeti.TopCat

namespace TauCeti

/-- **A simply connected space whose loop space has vanishing positive `R`-homology through degree
`n + 1` has vanishing `H_{n+1}(-; R)`.** Let `(X, x)` be a path-connected space with trivial
`π₁(X, x)`, and let `R` be a ring. If `H_{q+1}(Ω X x; R) = 0` for every `q ≤ n`, then
`H_{n+1}(X; R) = 0`. -/
theorem isZero_singularHomology_of_isZero_loopSpace_homology {X : Type u} [TopologicalSpace X]
    [PathConnectedSpace X] (x : X) (hπ₁ : Subsingleton (π_ 1 X x)) (R : Type u) [Ring R]
    (n : ℕ)
    (hΩ : ∀ q ≤ n, IsZero (((singularChains R).obj (_root_.TopCat.of (Ω X x))).homology (q + 1))) :
    IsZero (((singularChains R).obj (_root_.TopCat.of X)).homology (n + 1)) := by
  let p : _root_.TopCat.of (MappingPathFiber (.id X) x) ⟶ _root_.TopCat.of X :=
    _root_.TopCat.ofHom (MappingPathFiber.proj (.id X) x)
  -- `p.fiber x` is `{ z // p z = x }` and `(ContinuousMap.id X) x = x` definitionally.
  let e : p.fiber x ≃ₜ Ω X x := MappingPathFiber.projFiberHomeomorphPath (.id X) x x
  have : PathConnectedSpace (Ω X x) :=
    (pathConnectedSpace_loopSpace_iff_subsingleton_pi1 x).2 hπ₁
  have hF₀ : PathConnectedSpace (p.fiber x) := e.symm.pathConnectedSpace
  have hF (q : ℕ) (hq : q ≠ 0) (hqn : q ≤ n + 1) :
      IsZero (((singularHomologyFunctor (ModuleCat.{u} R) q).obj (ModuleCat.of R R)).obj
        (p.fiber x)) := by
    obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hq
    have hm := hΩ m (by omega)
    rw [← singularHomologyFunctor_obj_obj] at hm
    exact hm.of_iso (((singularHomologyFunctor (ModuleCat.{u} R) (m + 1)).obj
      (ModuleCat.of R R)).mapIso (_root_.TopCat.isoOfHomeo e))
  have hp : TopCat.serreFibrations p :=
    (MappingPathFiber.isHurewiczFibration_proj.{0} (.id X) x).mem_serreFibrations
  have : IsIso (((singularHomologyFunctor (ModuleCat.{u} R) (n + 1)).obj
      (ModuleCat.of R R)).map p) :=
    TopCat.isIso_singularHomologyMap_of_isZero_singleFiber hp x R (n + 1) hF₀ hF
  have hEP : IsZero (((singularHomologyFunctor (ModuleCat.{u} R) (n + 1)).obj
      (ModuleCat.of R R)).obj (_root_.TopCat.of (MappingPathFiber (.id X) x))) :=
    isZero_singularHomologyFunctor_of_contractibleSpace (ModuleCat.of R R)
      (_root_.TopCat.of (MappingPathFiber (.id X) x)) (Nat.succ_ne_zero n)
  rw [← singularHomologyFunctor_obj_obj]
  exact hEP.of_iso (asIso (((singularHomologyFunctor (ModuleCat.{u} R) (n + 1)).obj
    (ModuleCat.of R R)).map p)).symm

end TauCeti
