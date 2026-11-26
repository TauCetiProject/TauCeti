/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.DGLocalSystem.Fibration
public import TauCeti.AlgebraicTopology.DGLocalSystem.Path.BrownModel.BasepointChange
public import TauCeti.Topology.PathSpace.Moore.Replacement.Append

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
the inclusion of a point `a` joined to `b` by a path
(`TauCeti.BrownModel.exists_coefficientDifferential_eq_and_fibrationComparison_const_add_eq`), not
for a general map. There the fibre over `b` consists of the Moore paths from `a` to `b` and the
total space of the Moore paths from `a`, and read on these paths the comparison is the change of
basepoint of `M` from `b` to `a` (`TauCeti.BrownModel.basepointChangeComparison`), which is a
quasi-isomorphism
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
* `TauCeti.BrownModel.exists_coefficientDifferential_eq_and_fibrationComparison_const_add_eq`: for
  the inclusion of a point joined to `b` by a path, it is a quasi-isomorphism.

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

variable {a : B}

private theorem const_apply_unit (a : B) : ContinuousMap.const PUnit.{u + 1} a PUnit.unit = a :=
  ContinuousMap.const_apply (α := PUnit.{u + 1}) a PUnit.unit

/-- A point of the fibre over `b` of the replacement of the inclusion of `a` is a Moore path from
`a` to `b`. -/
private def pointFiberPath : C(MooreReplacement.Fiber (.const PUnit.{u + 1} a) b,
    MoorePathBetween B a b) :=
  ⟨fun x ↦ ⟨x.val.path, x.val.source_path.trans (const_apply_unit a), x.target_path_val⟩,
    ((MooreReplacement.continuous_path.comp MooreReplacement.Fiber.continuous_val).subtype_mk _)⟩

/-- A Moore path from `a` to `b` is a point of the fibre over `b` of the replacement of the
inclusion of `a`. -/
private def pathPointFiber : C(MoorePathBetween B a b,
    MooreReplacement.Fiber (.const PUnit.{u + 1} a) b) :=
  ⟨fun γ ↦ MooreReplacement.Fiber.mk' (MooreReplacement.mk PUnit.unit γ.toMoorePath
      (γ.source.trans (const_apply_unit a).symm))
      ((congrArg MoorePath.target (MooreReplacement.path_mk _ _ _)).trans γ.target),
    MooreReplacement.Fiber.continuous_mk' (MooreReplacement.continuous_mk continuous_const
      MoorePathBetween.continuous_toMoorePath fun γ ↦ γ.source.trans (const_apply_unit a).symm)
      fun γ ↦ (congrArg MoorePath.target (MooreReplacement.path_mk _ _ _)).trans γ.target⟩

/-- A point of the total space of the replacement of the inclusion of `a` is a Moore path from
`a`. -/
private def pointReplacementPath : C(MooreReplacement (.const PUnit.{u + 1} a),
    MoorePathFrom B a) :=
  ⟨fun x ↦ ⟨x.path, x.source_path.trans (const_apply_unit a)⟩,
    MooreReplacement.continuous_path.subtype_mk _⟩

/-- A Moore path from `a` is a point of the total space of the replacement of the inclusion of
`a`. -/
private def pathPointReplacement : C(MoorePathFrom B a,
    MooreReplacement (.const PUnit.{u + 1} a)) :=
  ⟨fun γ ↦ MooreReplacement.mk PUnit.unit γ.toMoorePath (γ.source.trans (const_apply_unit a).symm),
    MooreReplacement.continuous_mk continuous_const MoorePathFrom.continuous_toMoorePath _⟩

private theorem pathPointFiber_comp_pointFiberPath :
    (pathPointFiber (a := a) (b := b)).comp pointFiberPath = .id _ :=
  ContinuousMap.ext fun _ ↦ MooreReplacement.Fiber.ext (MooreReplacement.ext (Subsingleton.elim _ _)
    (by simp [pathPointFiber, pointFiberPath]))

private theorem pointFiberPath_comp_pathPointFiber :
    (pointFiberPath (a := a) (b := b)).comp pathPointFiber = .id _ :=
  ContinuousMap.ext fun _ ↦ MoorePathBetween.ext (by simp [pathPointFiber, pointFiberPath])

private theorem pathPointReplacement_comp_pointReplacementPath :
    (pathPointReplacement (a := a)).comp pointReplacementPath = .id _ :=
  ContinuousMap.ext fun _ ↦ MooreReplacement.ext (Subsingleton.elim _ _)
    (by simp [pathPointReplacement, pointReplacementPath])

private theorem pointFiberPath_op_smul (ω : MooreLoopSpace B b)
    (x : MooreReplacement.Fiber (.const PUnit.{u + 1} a) b) :
    pointFiberPath (MulOpposite.op ω • x) = MulOpposite.op ω • pointFiberPath x :=
  MoorePathBetween.ext (by simp [pointFiberPath, MooreReplacement.Fiber.op_smul_eq_act])

private theorem pathPointFiber_op_smul (ω : MooreLoopSpace B b) (γ : MoorePathBetween B a b) :
    pathPointFiber (MulOpposite.op ω • γ) = MulOpposite.op ω • pathPointFiber γ :=
  MooreReplacement.Fiber.ext (MooreReplacement.ext (Subsingleton.elim _ _) (by
    simp [pathPointFiber, MooreReplacement.Fiber.op_smul_eq_act]))

/-- Read on Moore paths, appending a path from `b` to a point of the fibre is concatenation. -/
private theorem pointReplacementPath_comp_appendFromMap :
    pointReplacementPath.comp (MooreReplacement.Fiber.appendFromMap (.const PUnit.{u + 1} a) b) =
      (MoorePathBetween.transFrom a b).comp (pointFiberPath.prodMap (.id (MoorePathFrom B b))) :=
  ContinuousMap.ext fun _ ↦ MoorePathFrom.ext (by simp [pointReplacementPath, pointFiberPath])

/-- For the inclusion of a point `a`, the fibration comparison, read on Moore paths, is the change
of basepoint of the Brown model from `b` to `a`. -/
private theorem pointReplacementPath_fibrationComparison (M : BrownModel B b H R P ind)
    (u : P →₀ cubicalChainModule (MooreReplacement.Fiber (.const PUnit.{u + 1} a) b)
      (MooreLoopSpace B b) R) :
    cubicalChainModuleLinearMap R pointReplacementPath
        (M.fibrationComparison (.const PUnit.{u + 1} a) u) =
      M.basepointChangeComparison a
        (Finsupp.mapRange.linearMap (cubicalChainModuleLinearMap R pointFiberPath) u) := by
  induction u using Finsupp.induction_linear with
  | zero => simp
  | add u u' hu hu' => simp only [map_add, hu, hu']
  | single x σ =>
    rw [fibrationComparison_single, Finsupp.mapRange.linearMap_apply, Finsupp.mapRange_single,
      basepointChangeComparison_single, cubicalChainModuleLinearMap_cubicalChainPairing,
      cubicalChainPairing_cubicalChainModuleLinearMap_left,
      pointReplacementPath_comp_appendFromMap]

end Point

/-- **The fibration comparison of the inclusion of a point is a quasi-isomorphism.** Let `M` be a
Brown model at `b` and `a` a point joined to `b` by a Moore path. For the inclusion of `a`, the
DG local system at `b` is the chain module of the Moore paths from `a` to `b` and the total space
of the replacement is the space of Moore paths from `a`, which is contractible. Every relative
cycle `(u, w)` of the fibration comparison, with `D u = 0` and `Ψ u = ∂ w`, is a relative boundary
`(D u', Ψ u' + ∂ w')`. -/
theorem exists_coefficientDifferential_eq_and_fibrationComparison_const_add_eq
    {B R : Type u} [TopologicalSpace B] {b : B} [CommRing R] {H P : Type*} {ind : P → ℤ}
    (M : BrownModel B b H R P ind) {a : B} (hab : Nonempty (MoorePathBetween B a b))
    (u : P →₀ cubicalChainModule (MooreReplacement.Fiber (.const PUnit.{u + 1} a) b)
      (MooreLoopSpace B b) R)
    (w : cubicalChainModule (MooreReplacement (.const PUnit.{u + 1} a)) H R)
    (hu : M.cocycle.coefficientDifferential (cubicalChainModule_isDGRightModule
      (MooreReplacement.Fiber (.const PUnit.{u + 1} a) b) (MooreLoopSpace B b) R) u = 0)
    (hw : M.fibrationComparison (.const PUnit.{u + 1} a) u =
      cubicalChainModuleDifferential (MooreReplacement (.const PUnit.{u + 1} a)) H R w) :
    ∃ u' w', M.cocycle.coefficientDifferential (cubicalChainModule_isDGRightModule
        (MooreReplacement.Fiber (.const PUnit.{u + 1} a) b) (MooreLoopSpace B b) R) u' = u ∧
      M.fibrationComparison (.const PUnit.{u + 1} a) u' +
        cubicalChainModuleDifferential (MooreReplacement (.const PUnit.{u + 1} a)) H R w' = w := by
  -- Transport the relative cycle to the Moore paths from `a` to `b` and from `a`, where the
  -- comparison is the change of basepoint, and transport the relative boundary back.
  let φ := cubicalChainModuleMap R (pointFiberPath (a := a) (b := b)) fun ω x ↦
    pointFiberPath_op_smul ω x
  let ψ := cubicalChainModuleMap R (pathPointFiber (a := a) (b := b)) fun ω γ ↦
    pathPointFiber_op_smul ω γ
  have hφl : φ.toLinearMap.restrictScalars R = cubicalChainModuleLinearMap R pointFiberPath :=
    LinearMap.ext fun x ↦ cubicalChainModuleMap_apply _ _ x
  have hψl : ψ.toLinearMap.restrictScalars R = cubicalChainModuleLinearMap R pathPointFiber :=
    LinearMap.ext fun x ↦ cubicalChainModuleMap_apply _ _ x
  have hφ := M.cocycle.coefficientDifferential_mapRange _ _ φ
  have hψ := M.cocycle.coefficientDifferential_mapRange _ _ ψ
  rw [hφl] at hφ
  rw [hψl] at hψ
  -- The two identifications of paths are mutually inverse.
  have hχ (z) : cubicalChainModuleLinearMap (G' := H) R (pathPointReplacement (a := a))
      (cubicalChainModuleLinearMap (G' := H) R (pointReplacementPath (a := a)) z) = z := by
    rw [cubicalChainModuleLinearMap_linearMap, pathPointReplacement_comp_pointReplacementPath,
      cubicalChainModuleLinearMap_id, LinearMap.id_apply]
  obtain ⟨u₁, w₁, hu₁, hw₁⟩ :=
    M.exists_coefficientDifferential_eq_and_basepointChangeComparison_add_eq hab
      (Finsupp.mapRange.linearMap (cubicalChainModuleLinearMap R pointFiberPath) u)
      (cubicalChainModuleLinearMap R pointReplacementPath w)
      (by rw [hφ, hu, map_zero])
      (by
        rw [cubicalChainModuleDifferential_linearMap, ← hw]
        exact (pointReplacementPath_fibrationComparison M u).symm)
  refine ⟨Finsupp.mapRange.linearMap (cubicalChainModuleLinearMap R pathPointFiber) u₁,
    cubicalChainModuleLinearMap R pathPointReplacement w₁, ?_, ?_⟩
  · rw [hψ, hu₁, ← LinearMap.comp_apply, ← Finsupp.mapRange.linearMap_comp, ←
      cubicalChainModuleLinearMap_comp (G' := MooreLoopSpace B b),
      pathPointFiber_comp_pointFiberPath, cubicalChainModuleLinearMap_id,
      Finsupp.mapRange.linearMap_id, LinearMap.id_apply]
  · have hφψ : Finsupp.mapRange.linearMap
        (cubicalChainModuleLinearMap (G' := MooreLoopSpace B b) R pointFiberPath)
        (Finsupp.mapRange.linearMap (cubicalChainModuleLinearMap (G := MooreLoopSpace B b)
          (G' := MooreLoopSpace B b) R (pathPointFiber (a := a) (b := b))) u₁) = u₁ := by
      rw [← LinearMap.comp_apply, ← Finsupp.mapRange.linearMap_comp, ←
        cubicalChainModuleLinearMap_comp (G' := MooreLoopSpace B b),
        pointFiberPath_comp_pathPointFiber, cubicalChainModuleLinearMap_id,
        Finsupp.mapRange.linearMap_id, LinearMap.id_apply]
    rw [cubicalChainModuleDifferential_linearMap, ← hχ (M.fibrationComparison _ _), ← map_add,
      pointReplacementPath_fibrationComparison, hφψ, hw₁, hχ]

end BrownModel

end TauCeti
