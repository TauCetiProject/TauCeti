/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.DGLocalSystem.Path.BrownModel.BasepointChange
public import TauCeti.Topology.PathSpace.Moore.Replacement.Point

/-!
# The fibration comparison of a Brown model

Let `p : E → B` be a continuous map and `b` a point of `B`. The DG local system of `p` at `b`
(`TauCeti.fibrationLocalSystem`) is the chain module `C_*(F'_b; R)` of the fibre over `b` of the
Moore-path replacement `E' = {(e, γ) | γ starts at p e}` of `p`, a right DG module over the chains
`C_*(Ω_b B; R)` on the Moore loops at `b`. Let `M` be a Brown model at `b` (`TauCeti.BrownModel`):
a semi-free row-finite twisting cocycle `m` over `C_*(Ω_b B; R)` on generators `P`, with a
quasi-isomorphism `g : K_m → C_*(P_b B; R)` onto the chains on the Moore paths from `b`. The twisted
complex of `m` with coefficients in `C_*(F'_b; R)`, on the finitely supported vectors
`P →₀ C_*(F'_b; R)`, is `C_*(F'_b) ⊗_{C_*(Ω_b B)} K_m`, which computes the homology of `B` with
coefficients in the DG local system of `p`.

Appending a Moore path from `b` to a point of the fibre
(`TauCeti.MooreReplacement.Fiber.appendFrom`) gives the **fibration comparison**
(`TauCeti.BrownModel.fibrationComparison`)

`C_*(F'_b) ⊗_{C_*(Ω_b B)} K_m → C_*(E')`,  `σ ⊗ x ↦ append_*(σ × g(x))`,

from the twisted complex computing the homology of `B` with coefficients in `C_*(F'_b)` to the
chains on the total space `E'`, which is homotopy equivalent to `E`
(`TauCeti.MooreReplacement.homotopyEquiv`). It commutes with the differentials
(`TauCeti.BrownModel.fibrationComparison_coefficientDifferential`): appending is balanced over the
loops at `b`, and the twisting equation of `m` corresponds through `g` to the boundaries of the
chains `g(x)`. Followed by the projection `E' → E`, it is natural in maps over `B`
(`TauCeti.BrownModel.cubicalChainModuleLinearMap_proj_fibrationComparison_mapRange`): a map
`h : E → E''` over `B` acts on the coefficients by the push-forward along the induced map of
fibres, the map of DG local systems `TauCeti.fibrationLocalSystemMap`, and on `E` by push-forward.

Brown's theorem, the form of the fibration theorem of Barraud, Damian, Humilière and Oancea for a
Brown model, says that for path-connected `B` this comparison is a quasi-isomorphism, so that the
homology of `B` with coefficients in `C_*(F'_b)` is the homology of `E`. This file proves it for
the inclusion `ContinuousMap.subtypeVal {a}` of a point `a` joined to `b` by a path
(`TauCeti.BrownModel.exists_coefficientDifferential_eq_and_fibrationComparison_subtypeVal_add_eq`),
not for a general map. There the fibre over `b` consists of the Moore paths from `a` to `b`
(`TauCeti.MooreReplacement.Fiber.homeomorphPathsBetween`) and the total space of the Moore paths
from `a` (`TauCeti.MooreReplacement.homeomorphPathsFromSingleton`), and read on these paths the
comparison is the change of basepoint of `M` from `b` to `a`
(`TauCeti.BrownModel.basepointChangeComparison`), which is a quasi-isomorphism
(`TauCeti.BrownModel.exists_coefficientDifferential_eq_and_basepointChangeComparison_add_eq`).
Both comparisons pair the coefficients with the chains `g(x)` along a balanced map
(`TauCeti.coefficientPairing`).

## Main definitions

* `TauCeti.BrownModel.fibrationComparison M p`: the map
  `C_*(F'_b) ⊗_{C_*(Ω_b B)} K_m → C_*(E')`, `σ ⊗ x ↦ append_*(σ × g(x))`.

## Main results

* `TauCeti.BrownModel.fibrationComparison_coefficientDifferential`: the comparison commutes with the
  differentials.
* `TauCeti.BrownModel.cubicalChainModuleLinearMap_proj_fibrationComparison_mapRange`: followed by
  the projection to `E`, it is natural in maps over `B`.
* `TauCeti.BrownModel.exists_coefficientDifferential_eq_and_fibrationComparison_subtypeVal_add_eq`:
  for the inclusion of a point joined to `b` by a path, it is a quasi-isomorphism.

## References

* E. H. Brown, *Twisted tensor products, I*, Ann. of Math. (2) 69 (1959), 223–246.
* J.-F. Barraud, M. Damian, V. Humilière, A. Oancea, *Morse homology with differential graded
  coefficients*, Progress in Mathematics 360, Birkhäuser, 2025, §7.1 and §7.2 (Theorem 7.2.1).
-/

public section

noncomputable section

namespace TauCeti

namespace BrownModel

universe u

variable {E E'' B : Type u} [TopologicalSpace E] [TopologicalSpace E''] [TopologicalSpace B]
  {b : B} {H : Type*} {R : Type*} [CommRing R] {P : Type*} {ind : P → ℤ}

/-- The **fibration comparison** of a Brown model `M` at `b`, for a map `p : E → B`: the map
`C_*(F'_b) ⊗_{C_*(Ω_b B)} K_m → C_*(E')` from the twisted complex of the cocycle of `M` with
coefficients in the DG local system `C_*(F'_b)` of `p`, written on finitely supported coefficient
vectors, to the chains on the total space `E'` of the Moore-path replacement of `p`. A coefficient
`σ` at the generator `x` goes to the push-forward, along appending paths from `b` to the points of
the fibre, of the cross product of `σ` with the image `g(x)` of `x` in the chains on the paths
from `b`. -/
def fibrationComparison (M : BrownModel B b H R P ind) (p : C(E, B)) :
    (P →₀ cubicalChainModule (MooreReplacement.Fiber p b) (MooreLoopSpace B b) R) →ₗ[R]
      cubicalChainModule (MooreReplacement p) H R :=
  coefficientPairing M.comparison (MooreReplacement.Fiber.appendFromMap p b)

/-- The comparison of a coefficient `σ` at a single generator `x` appends the image of `x` to `σ`.
-/
@[simp]
theorem fibrationComparison_single (M : BrownModel B b H R P ind) (p : C(E, B)) (x : P)
    (σ : cubicalChainModule (MooreReplacement.Fiber p b) (MooreLoopSpace B b) R) :
    M.fibrationComparison p (Finsupp.single x σ) =
      cubicalChainPairing (MooreLoopSpace B b) H R (MooreReplacement.Fiber.appendFromMap p b) σ
        (M.comparison x) :=
  coefficientPairing_single _ _ x σ

/-- **The fibration comparison commutes with the differentials**: it sends the twisted
differential, with coefficients in the DG local system `C_*(F'_b)` of `p`, to the boundary of
chains on the total space of the Moore-path replacement of `p`. -/
theorem fibrationComparison_coefficientDifferential (M : BrownModel B b H R P ind) (p : C(E, B))
    (f : P →₀ cubicalChainModule (MooreReplacement.Fiber p b) (MooreLoopSpace B b) R) :
    M.fibrationComparison p (M.cocycle.coefficientDifferential
        (cubicalChainModule_isDGRightModule (MooreReplacement.Fiber p b) (MooreLoopSpace B b) R)
          f) =
      cubicalChainModuleDifferential (MooreReplacement p) H R (M.fibrationComparison p f) :=
  coefficientPairing_coefficientDifferential M.cocycle M.linearCombination_comparison_m
    (fun ω x δ ↦ by
      rw [MooreReplacement.Fiber.appendFromMap_apply, MooreReplacement.Fiber.appendFromMap_apply,
        MooreReplacement.Fiber.op_smul_eq_act, MooreReplacement.Fiber.act_appendFrom]) f

/-- **Naturality of the fibration comparison in maps over `B`.** Let `h : E → E''` be a map over
`B`, from `p` to `p''`. Followed by the projections of the total spaces of the replacements to
`E''` and to `E`, the comparison of `p''` on the coefficients pushed forward along the induced map
of fibres (the map `TauCeti.fibrationLocalSystemMap` of DG local systems) is the push-forward along
`h` of the comparison of `p`. -/
theorem cubicalChainModuleLinearMap_proj_fibrationComparison_mapRange
    (M : BrownModel B b H R P ind) {p : C(E, B)} {p'' : C(E'', B)} (h : C(E, E''))
    (hh : p''.comp h = p)
    (f : P →₀ cubicalChainModule (MooreReplacement.Fiber p b) (MooreLoopSpace B b) R) :
    cubicalChainModuleLinearMap (G' := H) R (MooreReplacement.proj p'')
        (M.fibrationComparison p'' (Finsupp.mapRange.linearMap
          (cubicalChainModuleLinearMap R (MooreReplacement.Fiber.map h hh)) f)) =
      cubicalChainModuleLinearMap R h
        (cubicalChainModuleLinearMap (G' := H) R (MooreReplacement.proj p)
          (M.fibrationComparison p f)) := by
  -- Both sides pair the coefficients with the images of the generators along the map
  -- `((e, γ), δ) ↦ h e`.
  have hmap : (MooreReplacement.proj p'').comp ((MooreReplacement.Fiber.appendFromMap p'' b).comp
      ((MooreReplacement.Fiber.map h hh).prodMap (ContinuousMap.id (MoorePathFrom B b)))) =
        h.comp ((MooreReplacement.proj p).comp (MooreReplacement.Fiber.appendFromMap p b)) :=
    ContinuousMap.ext fun q ↦ by simp
  rw [fibrationComparison, fibrationComparison,
    coefficientPairing_mapRange_cubicalChainModuleLinearMap,
    cubicalChainModuleLinearMap_coefficientPairing, cubicalChainModuleLinearMap_coefficientPairing,
    cubicalChainModuleLinearMap_coefficientPairing, hmap]

/-! ### The inclusion of a point -/

section Point

open MooreReplacement in
/-- For the inclusion of a point `a`, the fibration comparison, read on Moore paths, is the change
of basepoint of the Brown model from `b` to `a`. -/
private theorem homeomorphPathsFromSingleton_fibrationComparison (M : BrownModel B b H R P ind)
    {a : B}
    (u : P →₀ cubicalChainModule (Fiber (ContinuousMap.subtypeVal {a}) b) (MooreLoopSpace B b) R) :
    cubicalChainModuleLinearMap R
        (homeomorphPathsFromSingleton a : C(_, MoorePathFrom B a))
        (M.fibrationComparison (ContinuousMap.subtypeVal {a}) u) =
      M.basepointChangeComparison a (Finsupp.mapRange.linearMap
        (cubicalChainModuleLinearMap R (Fiber.homeomorphPathsBetween a b :
          C(_, MoorePathBetween B a b))) u) := by
  have hcomp :
      (homeomorphPathsFromSingleton a : C(_, MoorePathFrom B a)).comp
        (Fiber.appendFromMap (ContinuousMap.subtypeVal {a}) b) =
      (MoorePathBetween.transFrom a b).comp
        ((Fiber.homeomorphPathsBetween a b : C(_, MoorePathBetween B a b)).prodMap
          (.id (MoorePathFrom B b))) :=
    ContinuousMap.ext fun q ↦ by
      simp [Fiber.homeomorphPathsFromSingleton_appendFrom, Prod.map_apply']
  induction u using Finsupp.induction_linear with
  | zero => simp
  | add u u' hu hu' => simp only [map_add, hu, hu']
  | single x σ =>
    rw [fibrationComparison_single, Finsupp.mapRange.linearMap_apply, Finsupp.mapRange_single,
      basepointChangeComparison_single, cubicalChainModuleLinearMap_cubicalChainPairing,
      cubicalChainPairing_cubicalChainModuleLinearMap_left, hcomp]

end Point

open MooreReplacement in
/-- **The fibration comparison of the inclusion of a point is a quasi-isomorphism.** Let `M` be a
Brown model at `b` and `a` a point joined to `b` by a Moore path. For the inclusion of `a`, the
DG local system at `b` is the chain module of the Moore paths from `a` to `b` and the total space
of the replacement is the space of Moore paths from `a`, which is contractible. Every relative
cycle `(u, w)` of the fibration comparison, with `D u = 0` and `Ψ u = ∂ w`, is a relative boundary
`(D u', Ψ u' + ∂ w')`. -/
theorem exists_coefficientDifferential_eq_and_fibrationComparison_subtypeVal_add_eq
    {B R : Type u} [TopologicalSpace B] {b : B} [CommRing R] {H P : Type*} {ind : P → ℤ}
    (M : BrownModel B b H R P ind) {a : B} (hab : Nonempty (MoorePathBetween B a b))
    (u : P →₀ cubicalChainModule (Fiber (ContinuousMap.subtypeVal {a}) b) (MooreLoopSpace B b) R)
    (w : cubicalChainModule (MooreReplacement (ContinuousMap.subtypeVal {a})) H R)
    (hu : M.cocycle.coefficientDifferential (cubicalChainModule_isDGRightModule
      (Fiber (ContinuousMap.subtypeVal {a}) b) (MooreLoopSpace B b) R) u = 0)
    (hw : M.fibrationComparison (ContinuousMap.subtypeVal {a}) u =
      cubicalChainModuleDifferential (MooreReplacement (ContinuousMap.subtypeVal {a})) H R w) :
    ∃ u' w', M.cocycle.coefficientDifferential (cubicalChainModule_isDGRightModule
        (Fiber (ContinuousMap.subtypeVal {a}) b) (MooreLoopSpace B b) R) u' = u ∧
      M.fibrationComparison (ContinuousMap.subtypeVal {a}) u' +
        cubicalChainModuleDifferential (MooreReplacement (ContinuousMap.subtypeVal {a})) H R w' =
          w := by
  -- Transport the relative cycle to the Moore paths from `a` to `b` and from `a`, where the
  -- comparison is the change of basepoint, and transport the relative boundary back.
  let e := Fiber.homeomorphPathsBetween a b
  let f : C(MooreReplacement (ContinuousMap.subtypeVal {a}), MoorePathFrom B a) :=
    homeomorphPathsFromSingleton a
  let g : C(MoorePathFrom B a, MooreReplacement (ContinuousMap.subtypeVal {a})) :=
    (homeomorphPathsFromSingleton a).symm
  have hgf : g.comp f = .id _ := (homeomorphPathsFromSingleton a).symm_comp_toContinuousMap
  have hφ := M.cocycle.coefficientDifferential_mapRange_cubicalChainModuleLinearMap
    (e : C(Fiber (ContinuousMap.subtypeVal {a}) b, MoorePathBetween B a b))
    (Fiber.homeomorphPathsBetween_op_smul (a := a) (b := b))
  have hψ := M.cocycle.coefficientDifferential_mapRange_cubicalChainModuleLinearMap
    (e.symm : C(MoorePathBetween B a b, Fiber (ContinuousMap.subtypeVal {a}) b))
    (Fiber.homeomorphPathsBetween_symm_op_smul (a := a) (b := b))
  obtain ⟨u₁, w₁, hu₁, hw₁⟩ :=
    M.exists_coefficientDifferential_eq_and_basepointChangeComparison_add_eq hab
      (Finsupp.mapRange.linearMap (cubicalChainModuleLinearMap R (e : C(_, _))) u)
      (cubicalChainModuleLinearMap R f w)
      (by rw [hφ, hu, map_zero])
      (by
        rw [cubicalChainModuleDifferential_linearMap, ← hw]
        exact (homeomorphPathsFromSingleton_fibrationComparison M u).symm)
  refine ⟨Finsupp.mapRange.linearMap (cubicalChainModuleLinearMap R (e.symm : C(_, _))) u₁,
    cubicalChainModuleLinearMap R g w₁, ?_, ?_⟩
  · rw [hψ, hu₁, mapRange_cubicalChainModuleLinearMap_mapRange_of_comp_eq_id
      e.symm_comp_toContinuousMap]
  · rw [cubicalChainModuleDifferential_linearMap,
      ← cubicalChainModuleLinearMap_linearMap_of_comp_eq_id hgf (M.fibrationComparison _ _),
      ← map_add, homeomorphPathsFromSingleton_fibrationComparison,
      mapRange_cubicalChainModuleLinearMap_mapRange_of_comp_eq_id e.toContinuousMap_comp_symm, hw₁,
      cubicalChainModuleLinearMap_linearMap_of_comp_eq_id hgf]

end BrownModel

end TauCeti
