/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.Homotopy.HomotopyGroup.TopologicalMonoid
public import TauCeti.Topology.Homotopy.HomotopyGroup.WeakHomotopyEquivalence
public import TauCeti.Topology.PathSpace.Moore.Comparison.HomotopyGroup
public import TauCeti.Topology.QuaternionicProjectiveSpace.Hopf.Exact
import TauCeti.Analysis.InnerProductSpace.Projection.Basic
import TauCeti.AlgebraicTopology.Sphere.HomotopyGroup

/-!
# The loop space of `HPⁿ` splits as `S³ × ΩS⁴ⁿ⁺³`

Let `q : S⁴ⁿ⁺³ → HPⁿ` be the quaternionic Hopf fibration and `v` a unit vector of `ℍⁿ⁺¹`.
Given a based map `j : S³ → ΩHPⁿ` from the unit quaternions to the Moore loop space at `[v]`, the
**based Hopf product** (`TauCeti.QuaternionicProjectiveSpace.hopfProduct`) is

`j ⋆ Ωq : S³ × ΩS⁴ⁿ⁺³ → ΩHPⁿ`, `(u, γ) ↦ j u * Ωq γ`,

the Moore concatenation of the loop `j u` with the image of the loop `γ` at `v`. This file shows
that it is a weak homotopy equivalence when `j` splits the boundary map of the Hopf fibration
(`TauCeti.QuaternionicProjectiveSpace.isWeakHomotopyEquivalence_hopfProduct`), and that for
`n ≥ 1` such maps `j` exist
(`TauCeti.QuaternionicProjectiveSpace.exists_isWeakHomotopyEquivalence_hopfProduct`).

Unlike the complex case `S¹ × ΩS²ⁿ⁺¹ → ΩCPⁿ`, the fibre `S³` has nontrivial homotopy groups in
infinitely many degrees, so `j` must split the boundary map in every degree, not only on `π₁`.
Write `∂ : π_{k+1}(ΩHPⁿ) ≅ π_{k+2}(HPⁿ) → π_{k+1}(S³)` for the Moore loop-space shift followed by
the boundary map (`TauCeti.QuaternionicProjectiveSpace.hopfLoopBoundaryHom`). The exact homotopy
sequence of the Hopf fibration shows that `(Ωq)_*` maps `π_{k+1}(ΩS⁴ⁿ⁺³)` onto the kernel of `∂`
(`TauCeti.QuaternionicProjectiveSpace.ker_hopfLoopBoundaryHom`), and it is injective as soon as `∂`
is onto in the next degree, because the fibre inclusion is then trivial on homotopy groups
(`TauCeti.QuaternionicProjectiveSpace.injective_homotopyGroupMap_mooreLoopSpaceMap`). If
`∂ ∘ j_*` is bijective in every degree, then `(j ⋆ Ωq)_* (a × b) = j_* a * (Ωq)_* b` is bijective
(`HomotopyGroup.bijective_map_mul_of_bijective_comp`).

The splitting map is built from a based null-homotopy of the fibre inclusion `u ↦ v u` in
`S⁴ⁿ⁺³`: for a unit vector `w` orthogonal to the quaternionic line of `v` (which exists as soon
as `n ≥ 1`), put `α = (1 - s) + s u` and normalize

`v α + (1 - ‖α‖²) w`, `s ∈ [0, 1]`,

which runs from `v` to `v u` and never vanishes, since the second coefficient is `1` when
`α = 0`. Its image in `HPⁿ` is a loop at `[v]` for each `u`, run as a Moore loop of length
`‖u - 1‖` so that `u = 1` gives the unit loop. The family of lifts starting at `v` computes the
boundary map, which therefore sends `j_* a` back to `a`.

Since weak homotopy equivalences induce isomorphisms on singular homology, the splitting reduces
the integral homology of `ΩHPⁿ` to that of `S³ × ΩS⁴ⁿ⁺³`.

## Main definitions

* `TauCeti.QuaternionicProjectiveSpace.hopfProduct`: the based Hopf product `j ⋆ Ωq`.
* `TauCeti.QuaternionicProjectiveSpace.hopfLoopBoundaryHom`: the homomorphism
  `π_{k+1}(ΩHPⁿ, 1) → π_{k+1}(S³, 1)`, the Moore loop-space shift followed by the boundary map of
  the Hopf fibration.

## Main results

* `TauCeti.QuaternionicProjectiveSpace.map_hopfProduct_prod`:
  `(j ⋆ Ωq)_* (a × b) = j_* a * (Ωq)_* b`.
* `TauCeti.QuaternionicProjectiveSpace.hopfLoopBoundaryHom_eq_one_iff`,
  `TauCeti.QuaternionicProjectiveSpace.ker_hopfLoopBoundaryHom`: the kernel of `∂` is the image
  of `(Ωq)_*`.
* `TauCeti.QuaternionicProjectiveSpace.injective_homotopyGroupMap_mooreLoopSpaceMap`: `(Ωq)_*` is
  injective on `π_{k+1}` when `∂` is onto in the next degree.
* `TauCeti.QuaternionicProjectiveSpace.isWeakHomotopyEquivalence_hopfProduct`: `j ⋆ Ωq` is a
  weak homotopy equivalence whenever `∂ ∘ j_*` is bijective in every positive degree.
* `TauCeti.QuaternionicProjectiveSpace.exists_hopfLoopBoundaryHom_map_eq`: for `n ≥ 1` there is a
  based map `j : S³ → ΩHPⁿ` with `∂ (j_* a) = a` in every positive degree.
* `TauCeti.QuaternionicProjectiveSpace.exists_isWeakHomotopyEquivalence_hopfProduct`: for
  `n ≥ 1` there is a based map `j` for which `j ⋆ Ωq` is a weak homotopy equivalence.

## References

* A. Hatcher, *Algebraic Topology*, Theorem 4.41 and the Hopf bundles of §4.2.
* J.-F. Barraud, M. Damian, V. Humilière, A. Oancea, *Floer homology with DG coefficients.
  Applications to cotangent bundles*, arXiv:2404.07953, §6.4.
-/

public section

noncomputable section

open Metric MulOpposite Set
open scoped Topology Topology.Homotopy Quaternion unitInterval NNReal

namespace TauCeti.QuaternionicProjectiveSpace

variable {n : ℕ} (v : sphere (0 : PiLp 2 fun _ : Fin (n + 1) ↦ ℍ) 1)

/-- The **based Hopf product** `j ⋆ Ωq : S³ × ΩS⁴ⁿ⁺³ → ΩHPⁿ`, `(u, γ) ↦ j u * Ωq γ`: the Moore
concatenation of the loop `j u` of `HPⁿ` with the image of the loop `γ` of `S⁴ⁿ⁺³` under the
quaternionic Hopf fibration `q`. -/
def hopfProduct
    (j : C(sphere (0 : ℍ) 1, MooreLoopSpace (QuaternionicProjectiveSpace n) (mk n v))) :
    C(sphere (0 : ℍ) 1 × MooreLoopSpace (sphere (0 : PiLp 2 fun _ : Fin (n + 1) ↦ ℍ) 1) v,
      MooreLoopSpace (QuaternionicProjectiveSpace n) (mk n v)) :=
  j.comp ContinuousMap.fst *
    (MooreLoopSpace.map (x := v) ⟨mk n, continuous_mk n⟩ rfl).toContinuousMap.comp
      ContinuousMap.snd

@[simp]
theorem hopfProduct_apply
    (j : C(sphere (0 : ℍ) 1, MooreLoopSpace (QuaternionicProjectiveSpace n) (mk n v)))
    (p : sphere (0 : ℍ) 1 × MooreLoopSpace (sphere (0 : PiLp 2 fun _ : Fin (n + 1) ↦ ℍ) 1) v) :
    hopfProduct v j p = j p.1 * MooreLoopSpace.map ⟨mk n, continuous_mk n⟩ rfl p.2 :=
  (rfl)

/-- The based Hopf product acts on homotopy groups by `(j ⋆ Ωq)_* (a × b) = j_* a * (Ωq)_* b`. -/
@[simp]
theorem map_hopfProduct_prod {N : Type*} [DecidableEq N] [Nonempty N]
    {j : C(sphere (0 : ℍ) 1, MooreLoopSpace (QuaternionicProjectiveSpace n) (mk n v))}
    (hj : j 1 = 1) (h : hopfProduct v j (1, 1) = 1) (a : HomotopyGroup N (sphere (0 : ℍ) 1) 1)
    (b : HomotopyGroup N (MooreLoopSpace (sphere (0 : PiLp 2 fun _ : Fin (n + 1) ↦ ℍ) 1) v) 1) :
    HomotopyGroup.map (hopfProduct v j) h (HomotopyGroup.prod a b) =
      HomotopyGroup.map j hj a *
        HomotopyGroup.map (MooreLoopSpace.map (x := v) ⟨mk n, continuous_mk n⟩ rfl).toContinuousMap
          (map_one (MooreLoopSpace.map _ _)) b :=
  HomotopyGroup.map_mul_prod _ _ hj (map_one (MooreLoopSpace.map _ _)) a b

/-- The **boundary map on the loop space** `π_{k+1}(ΩHPⁿ, 1) → π_{k+1}(S³, 1)` of the
quaternionic Hopf fibration: the Moore loop-space shift `π_{k+1}(ΩHPⁿ, 1) ≅ π_{k+2}(HPⁿ, [v])`,
followed by the boundary map `π_{k+2}(HPⁿ, [v]) → π_{k+1}(S³, 1)`. The loop coordinate, the last
cube direction of the shift, is the direction in which the boundary map lifts. -/
def hopfLoopBoundaryHom (k : ℕ) :
    π_ (k + 1) (MooreLoopSpace (QuaternionicProjectiveSpace n) (mk n v)) 1 →*
      π_ (k + 1) (sphere (0 : ℍ) 1) 1 :=
  (hopfBoundaryHom v (Fin (k + 1))).comp <|
    (HomotopyGroup.congrMulEquiv (finSuccEquivLast (n := k + 1))).toMonoidHom.comp
      (MooreLoopSpace.homotopyGroupMulEquiv (mk n v) k).toMonoidHom

theorem hopfLoopBoundaryHom_apply (k : ℕ)
    (a : π_ (k + 1) (MooreLoopSpace (QuaternionicProjectiveSpace n) (mk n v)) 1) :
    hopfLoopBoundaryHom v k a = hopfBoundary v (Fin (k + 1))
      (HomotopyGroup.congrEquiv finSuccEquivLast
        (MooreLoopSpace.homotopyGroupMulEquiv (mk n v) k a)) := by
  simp [hopfLoopBoundaryHom]

/-! ### The splitting criterion -/

/-- **Exactness at `π_{k+1}(ΩHPⁿ)`.** A class of `π_{k+1}(ΩHPⁿ, 1)` comes from `ΩS⁴ⁿ⁺³` under the
Moore loop map `Ωq` of the Hopf fibration exactly when its boundary in `π_{k+1}(S³)` is trivial. -/
theorem hopfLoopBoundaryHom_eq_one_iff (k : ℕ)
    (c : π_ (k + 1) (MooreLoopSpace (QuaternionicProjectiveSpace n) (mk n v)) 1) :
    hopfLoopBoundaryHom v k c = 1 ↔
      c ∈ range (HomotopyGroup.map
        (MooreLoopSpace.map (x := v) ⟨mk n, continuous_mk n⟩ rfl).toContinuousMap
        (map_one (MooreLoopSpace.map _ _))) := by
  rw [hopfLoopBoundaryHom_apply, HomotopyGroup.one_def, ← mem_range_homotopyGroupMap_mk_iff]
  constructor
  · rintro ⟨d, hd⟩
    refine ⟨(MooreLoopSpace.homotopyGroupMulEquiv v k).symm
      ((HomotopyGroup.congrEquiv finSuccEquivLast).symm d), ?_⟩
    apply (MooreLoopSpace.homotopyGroupMulEquiv (mk n v) k).injective
    apply (HomotopyGroup.congrEquiv finSuccEquivLast).injective
    rw [MooreLoopSpace.homotopyGroupMulEquiv_map, MulEquiv.apply_symm_apply,
      ← HomotopyGroup.map_congrEquiv, Equiv.apply_symm_apply, hd]
  · rintro ⟨b, rfl⟩
    exact ⟨HomotopyGroup.congrEquiv finSuccEquivLast (MooreLoopSpace.homotopyGroupMulEquiv v k b),
      by rw [HomotopyGroup.map_congrEquiv, MooreLoopSpace.homotopyGroupMulEquiv_map]⟩

/-- The boundary map kills the image of the Moore loop map `Ωq` of the Hopf fibration. -/
@[simp]
theorem hopfLoopBoundaryHom_homotopyGroupMap_mooreLoopSpaceMap (k : ℕ)
    (b : π_ (k + 1) (MooreLoopSpace (sphere (0 : PiLp 2 fun _ : Fin (n + 1) ↦ ℍ) 1) v) 1) :
    hopfLoopBoundaryHom v k (HomotopyGroup.map
      (MooreLoopSpace.map (x := v) ⟨mk n, continuous_mk n⟩ rfl : C(_, _))
      (map_one (MooreLoopSpace.map _ _)) b) = 1 :=
  (hopfLoopBoundaryHom_eq_one_iff v k _).2 ⟨b, rfl⟩

/-- **Exactness at `π_{k+1}(ΩHPⁿ)`**, as an equality of subgroups: the kernel of the boundary map
is the image of the Moore loop map `Ωq` of the Hopf fibration. -/
theorem ker_hopfLoopBoundaryHom (k : ℕ) :
    (hopfLoopBoundaryHom v k).ker = (HomotopyGroup.mapHom (N := Fin (k + 1))
      (MooreLoopSpace.map (x := v) ⟨mk n, continuous_mk n⟩ rfl).toContinuousMap
      (map_one (MooreLoopSpace.map _ _))).range := by
  ext c
  rw [MonoidHom.mem_ker, hopfLoopBoundaryHom_eq_one_iff, MonoidHom.mem_range]
  simp [HomotopyGroup.mapHom_apply]

/-- **The Moore loop map of the Hopf fibration is injective on `π_{k+1}`** when the boundary map
`π_{k+3}(HPⁿ) → π_{k+2}(S³)` is onto: then the fibre inclusion is trivial on `π_{k+2}(S³)`, so
`q_*` is injective on `π_{k+2}(S⁴ⁿ⁺³)`. -/
theorem injective_homotopyGroupMap_mooreLoopSpaceMap (k : ℕ)
    (hk : Function.Surjective (hopfBoundary v (Fin (k + 2)))) :
    Function.Injective (HomotopyGroup.map (N := Fin (k + 1))
      (MooreLoopSpace.map (x := v) ⟨mk n, continuous_mk n⟩ rfl).toContinuousMap
      (map_one (MooreLoopSpace.map _ _))) := by
  have hq : Function.Injective
      (HomotopyGroup.map (N := Fin (k + 2)) (x := v) ⟨mk n, continuous_mk n⟩ rfl) := by
    refine (injective_iff_map_eq_one (HomotopyGroup.mapHom (N := Fin (k + 2)) (x := v)
      ⟨mk n, continuous_mk n⟩ rfl)).2 fun d hd ↦ ?_
    rw [HomotopyGroup.mapHom_apply, HomotopyGroup.one_def] at hd
    obtain ⟨c, rfl⟩ := (mem_range_homotopyGroupMap_op_smul_iff v).2 hd
    rw [(mem_range_hopfBoundary_iff v).1 (hk c), HomotopyGroup.one_def]
  intro a b hab
  apply (MooreLoopSpace.homotopyGroupMulEquiv v k).injective
  apply hq
  rw [← MooreLoopSpace.homotopyGroupMulEquiv_map, ← MooreLoopSpace.homotopyGroupMulEquiv_map]
  exact congrArg _ hab

/-- **The loop space of `HPⁿ` splits as `S³ × ΩS⁴ⁿ⁺³`.** If a based map `j : S³ → ΩHPⁿ` splits
the boundary map of the Hopf fibration, in the sense that `∂ ∘ j_* : π_{k+1}(S³) → π_{k+1}(S³)` is
bijective for every `k`, then the based Hopf product `j ⋆ Ωq : S³ × ΩS⁴ⁿ⁺³ → ΩHPⁿ`,
`(u, γ) ↦ j u * Ωq γ`, is a weak homotopy equivalence. -/
theorem isWeakHomotopyEquivalence_hopfProduct
    {j : C(sphere (0 : ℍ) 1, MooreLoopSpace (QuaternionicProjectiveSpace n) (mk n v))}
    (hj : j 1 = 1)
    (hjb : ∀ k, Function.Bijective
      (hopfLoopBoundaryHom v k ∘ HomotopyGroup.map (N := Fin (k + 1)) j hj)) :
    (hopfProduct v j).IsWeakHomotopyEquivalence := by
  -- `S³`, `ΩS⁴ⁿ⁺³` and `ΩHPⁿ` are path connected, since `S³`, `S⁴ⁿ⁺³` and `HPⁿ` are simply
  -- connected.
  have : PathConnectedSpace (sphere (0 : ℍ) 1) :=
    (pathConnectedSpace_iff_subsingleton_homotopyGroup_zero (1 : sphere (0 : ℍ) 1)).2
      (subsingleton_homotopyGroup_sphere_quaternion (N := Fin 0) (by simp) 1)
  have : PathConnectedSpace
      (MooreLoopSpace (sphere (0 : PiLp 2 fun _ : Fin (n + 1) ↦ ℍ) 1) v) :=
    (MooreLoopSpace.pathConnectedSpace_iff_subsingleton_pi1 v).2
      (subsingleton_homotopyGroup_sphere_piLp_quaternion (N := Fin 1) (by simp; omega) v)
  refine ContinuousMap.isWeakHomotopyEquivalence_of_forall_bijective_succ
    (x := (1, 1)) (by simp [hj] : hopfProduct v j (1, 1) = 1) fun k ↦ ?_
  -- `j_*` splits the exact sequence `π(ΩS⁴ⁿ⁺³) ↪ π(ΩHPⁿ) → π(S³)`.
  refine HomotopyGroup.bijective_map_mul_of_bijective_comp hj
    (map_one (MooreLoopSpace.map _ _)) (hopfLoopBoundaryHom v k) (hjb k)
    (injective_homotopyGroupMap_mooreLoopSpaceMap v k fun c ↦ ?_)
    (hopfLoopBoundaryHom_eq_one_iff v k)
  -- The boundary map is onto in the next degree, since `∂ ∘ j_*` is.
  obtain ⟨a, ha⟩ := (hjb (k + 1)).2 c
  exact ⟨_, (hopfLoopBoundaryHom_apply v (k + 1) _).symm.trans ha⟩

/-! ### A splitting of the boundary map -/

section Splitting

variable {v} {w : PiLp 2 fun _ : Fin (n + 1) ↦ ℍ}

variable (v w) in
/-- The vector `v α + (1 - ‖α‖²) w` with `α = (1 - s) + s u`, which normalizes to a null-homotopy
of the fibre inclusion `u ↦ v u` of the Hopf fibration. -/
private def liftVector (u : sphere (0 : ℍ) 1) (s : I) : PiLp 2 fun _ : Fin (n + 1) ↦ ℍ :=
  op (AffineMap.lineMap 1 (u : ℍ) (s : ℝ)) • (v : PiLp 2 fun _ : Fin (n + 1) ↦ ℍ) +
    (1 - ‖AffineMap.lineMap 1 (u : ℍ) (s : ℝ)‖ ^ 2) • w

/-- The vector `liftVector` is `v α` when `α = (1 - s) + s u` is a unit quaternion. -/
private theorem liftVector_of_norm_eq_one {u : sphere (0 : ℍ) 1} {s : I}
    (h : ‖AffineMap.lineMap 1 (u : ℍ) (s : ℝ)‖ = 1) :
    liftVector v w u s =
      op (AffineMap.lineMap 1 (u : ℍ) (s : ℝ)) • (v : PiLp 2 fun _ : Fin (n + 1) ↦ ℍ) := by
  simp [liftVector, h]

/-- The vector `liftVector` never vanishes: its `w`-component is `1 - ‖α‖²`, which is `1` when
its `v`-component `v α` vanishes. -/
private theorem liftVector_ne_zero (hw : ‖w‖ = 1)
    (hvw : ∀ a : ℍ, inner ℝ (op a • (v : PiLp 2 fun _ : Fin (n + 1) ↦ ℍ)) w = 0)
    (u : sphere (0 : ℍ) 1) (s : I) : liftVector v w u s ≠ 0 := by
  intro h
  have h1 : inner ℝ (liftVector v w u s) w = 1 - ‖AffineMap.lineMap 1 (u : ℍ) (s : ℝ)‖ ^ 2 := by
    simp [liftVector, inner_add_left, real_inner_smul_left, hvw, hw]
  rw [h, inner_zero_left] at h1
  have h2 : op (AffineMap.lineMap 1 (u : ℍ) (s : ℝ)) •
      (v : PiLp 2 fun _ : Fin (n + 1) ↦ ℍ) = 0 := by
    simpa [liftVector, ← h1] using h
  have h3 : ‖AffineMap.lineMap 1 (u : ℍ) (s : ℝ)‖ = 0 := by
    simpa [norm_smul, norm_op, norm_eq_of_mem_sphere] using congrArg norm h2
  rw [h3] at h1
  norm_num at h1

variable (hw : ‖w‖ = 1)
  (hvw : ∀ a : ℍ, inner ℝ (op a • (v : PiLp 2 fun _ : Fin (n + 1) ↦ ℍ)) w = 0)

include hw hvw

variable (v w) in
/-- A based null-homotopy of the fibre inclusion `u ↦ v u` of the Hopf fibration: the
normalization of `liftVector`, which runs from `v` at `s = 0` to `v u` at `s = 1`, and is constantly
`v` for `u = 1`. -/
private def hopfLift :
    C(sphere (0 : ℍ) 1 × I, sphere (0 : PiLp 2 fun _ : Fin (n + 1) ↦ ℍ) 1) where
  toFun p := ⟨‖liftVector v w p.1 p.2‖⁻¹ • liftVector v w p.1 p.2,
    mem_sphere_zero_iff_norm.2 (norm_smul_inv_norm (𝕜 := ℝ) (liftVector_ne_zero hw hvw _ _))⟩
  continuous_toFun := by
    have hc : Continuous fun p : sphere (0 : ℍ) 1 × I ↦
        AffineMap.lineMap 1 (p.1 : ℍ) (p.2 : ℝ) := by
      simp only [AffineMap.lineMap_apply_module]
      fun_prop
    have hL : Continuous fun p : sphere (0 : ℍ) 1 × I ↦ liftVector v w p.1 p.2 := by
      unfold liftVector
      exact (continuous_op.comp hc).smul continuous_const |>.add
        ((continuous_const.sub ((continuous_norm.comp hc).pow 2)).smul continuous_const)
    exact ((continuous_norm.comp hL).inv₀ fun p ↦
      norm_ne_zero_iff.2 (liftVector_ne_zero hw hvw p.1 p.2)).smul hL |>.subtype_mk _

private theorem coe_hopfLift_of_norm_eq_one {u : sphere (0 : ℍ) 1} {s : I}
    (h : ‖AffineMap.lineMap 1 (u : ℍ) (s : ℝ)‖ = 1) :
    (hopfLift v w hw hvw (u, s) : PiLp 2 fun _ : Fin (n + 1) ↦ ℍ) =
      op (AffineMap.lineMap 1 (u : ℍ) (s : ℝ)) • (v : PiLp 2 fun _ : Fin (n + 1) ↦ ℍ) := by
  simp [hopfLift, liftVector_of_norm_eq_one h, norm_smul, norm_op, h]

private theorem hopfLift_zero (u : sphere (0 : ℍ) 1) : hopfLift v w hw hvw (u, 0) = v := by
  have h : AffineMap.lineMap 1 (u : ℍ) ((0 : I) : ℝ) = 1 := by
    rw [Set.Icc.coe_zero, AffineMap.lineMap_apply_zero]
  refine Subtype.ext <| (coe_hopfLift_of_norm_eq_one hw hvw (by rw [h, norm_one])).trans ?_
  rw [h, op_one, one_smul]

private theorem hopfLift_one (u : sphere (0 : ℍ) 1) : hopfLift v w hw hvw (u, 1) = op u • v := by
  have h : AffineMap.lineMap 1 (u : ℍ) ((1 : I) : ℝ) = u := by
    rw [Set.Icc.coe_one, AffineMap.lineMap_apply_one]
  refine Subtype.ext <|
    (coe_hopfLift_of_norm_eq_one hw hvw (by rw [h]; exact norm_eq_of_mem_sphere u)).trans ?_
  rw [h, Sphere.coe_op_sphere_smul, unop_op]

private theorem hopfLift_one_left (s : I) : hopfLift v w hw hvw (1, s) = v := by
  have h : AffineMap.lineMap 1 ((1 : sphere (0 : ℍ) 1) : ℍ) (s : ℝ) = 1 := by
    rw [unitSphere.coe_one, AffineMap.lineMap_same_apply]
  refine Subtype.ext <| (coe_hopfLift_of_norm_eq_one hw hvw (by rw [h, norm_one])).trans ?_
  rw [h, op_one, one_smul]

omit hw hvw in
private theorem nnNorm_sub_one_ne_zero {u : sphere (0 : ℍ) 1} (hu : u ≠ 1) :
    ‖(u : ℍ) - 1‖₊ ≠ 0 :=
  nnNorm_ne_zero_iff.2 <| sub_ne_zero.2 fun h ↦ hu <| Subtype.ext <| by rw [h, unitSphere.coe_one]

variable (v w) in
/-- The loops `s ↦ [hopfLift (u, s)]` of `HPⁿ` at `[v]`, on the unit interval. -/
private def hopfUnitLoop : C(sphere (0 : ℍ) 1, C(I, QuaternionicProjectiveSpace n)) :=
  ((⟨mk n, continuous_mk n⟩ : C(_, QuaternionicProjectiveSpace n)).comp
    (hopfLift v w hw hvw)).curry

private theorem hopfUnitLoop_apply (u : sphere (0 : ℍ) 1) (s : I) :
    hopfUnitLoop v w hw hvw u s = mk n (hopfLift v w hw hvw (u, s)) :=
  (rfl)

variable (v w) in
/-- The loop `s ↦ [hopfLift (u, s)]` of `HPⁿ` at `[v]`, run as a Moore path of length `‖u - 1‖`.
For `u = 1` it is the constant path of length zero. -/
private def hopfLoopPath (u : sphere (0 : ℍ) 1) : MoorePath (QuaternionicProjectiveSpace n) :=
  (MoorePath.ofUnitPath (hopfUnitLoop v w hw hvw u)).rescale ‖(u : ℍ) - 1‖₊

variable (v w) in
/-- The splitting map `j : S³ → ΩHPⁿ`: the Moore loop `hopfLoopPath u` at `[v]`. -/
private def hopfLoop : C(sphere (0 : ℍ) 1, MooreLoopSpace (QuaternionicProjectiveSpace n) (mk n v))
    where
  toFun u :=
    { toMoorePath := hopfLoopPath v w hw hvw u
      source_eq := by
        rw [hopfLoopPath, MoorePath.source_rescale, MoorePath.source_ofUnitPath,
          hopfUnitLoop_apply, hopfLift_zero]
      target_eq := by
        by_cases hu : u = 1
        · subst hu
          rw [hopfLoopPath, unitSphere.coe_one, sub_self, nnNorm_zero, MoorePath.rescale_zero,
            MoorePath.target_refl, MoorePath.source_ofUnitPath, hopfUnitLoop_apply, hopfLift_zero]
        · rw [hopfLoopPath, MoorePath.target_rescale _ (nnNorm_sub_one_ne_zero hu),
            MoorePath.target_ofUnitPath, hopfUnitLoop_apply, hopfLift_one, mk_op_smul] }
  continuous_toFun := by
    refine MooreLoopSpace.isEmbedding_toMoorePath.continuous_iff.2 <|
      MoorePath.continuous_iff.2 ⟨by
        simp only [Function.comp_apply, hopfLoopPath, MoorePath.length_rescale]
        fun_prop, ?_⟩
    refine continuous_iff_continuousAt.2 fun ⟨u, t⟩ ↦ ?_
    by_cases hu : u = 1
    · -- At `u = 1` the null-homotopy is constant, so the reparametrization does not matter:
      -- by the tube lemma, near `u = 1` the whole loop stays close to `[v]`.
      subst hu
      have hF : Continuous fun p ↦ mk n (hopfLift v w hw hvw p) :=
        (continuous_mk n).comp (hopfLift v w hw hvw).continuous
      simp only [Function.comp_apply, hopfLoopPath, MoorePath.rescale_apply,
        MoorePath.ofUnitPath_apply, hopfUnitLoop_apply]
      refine continuousAt_def.2 fun U hU ↦ ?_
      rw [hopfLift_one_left] at hU
      have h := isCompact_univ.eventually_forall_of_forall_eventually (x₀ := (1 : sphere (0 : ℍ) 1))
        (P := fun u s ↦ mk n (hopfLift v w hw hvw (u, s)) ∈ U) fun s _ ↦
          hF.continuousAt.preimage_mem_nhds (by rwa [hopfLift_one_left])
      exact (continuousAt_fst.eventually h).mono fun p hp ↦ hp _ (mem_univ _)
    · -- Away from `u = 1` the length `‖u - 1‖` does not vanish, so rescaling is continuous.
      have hS : Continuous fun u : {u : sphere (0 : ℍ) 1 // u ≠ 1} ↦ hopfLoopPath v w hw hvw u :=
        (MoorePath.continuous_ofUnitPath.comp
          ((hopfUnitLoop v w hw hvw).continuous.comp continuous_subtype_val)).moorePath_rescale
            (by fun_prop) fun u ↦ nnNorm_sub_one_ne_zero u.2
      have hu' : ContinuousAt (fun u ↦ hopfLoopPath v w hw hvw u) u :=
        (isOpen_ne.isOpenEmbedding_subtypeVal.continuousAt_iff (x := ⟨u, hu⟩)).1 hS.continuousAt
      exact MoorePath.continuous_eval.continuousAt.comp
        ((hu'.comp (continuousAt_fst (p := (u, t)))).prodMk continuousAt_snd)

private theorem toMoorePath_hopfLoop (u : sphere (0 : ℍ) 1) :
    (hopfLoop v w hw hvw u).toMoorePath = hopfLoopPath v w hw hvw u :=
  (rfl)

private theorem hopfLoop_one : hopfLoop v w hw hvw 1 = 1 :=
  MooreLoopSpace.eq_one_of_length_eq_zero <| by
    rw [← MooreLoopSpace.length_toMoorePath, toMoorePath_hopfLoop, hopfLoopPath,
      MoorePath.length_rescale, unitSphere.coe_one, sub_self, nnNorm_zero]

/-- The splitting loop at `u`, normalized to the unit interval, is `s ↦ [hopfLift (u, s)]`. -/
private theorem toPath_hopfLoop (u : sphere (0 : ℍ) 1) (s : I) :
    (hopfLoop v w hw hvw u).toPath s = mk n (hopfLift v w hw hvw (u, s)) := by
  rw [MooreLoopSpace.toPath_apply, toMoorePath_hopfLoop, hopfLoopPath, MoorePath.length_rescale,
    MoorePath.rescale_apply, MoorePath.length_ofUnitPath, one_mul, MoorePath.ofUnitPath_apply,
    hopfUnitLoop_apply]
  by_cases hu : u = 1
  · subst hu
    rw [hopfLift_one_left, hopfLift_one_left]
  · rw [mul_div_cancel_left₀ _ (nnNorm_sub_one_ne_zero hu), unitInterval.coe_toNNReal, projIcc_val]

/-- **The splitting loop splits the boundary map**: `∂ (j_* a) = a` for every class `a` of
`π_{k+1}(S³, 1)`. The family of lifts `(s, t) ↦ hopfLift (a t, s)` of the shifted loops starts
at `v` and ends at the fibre loop `t ↦ v (a t)`, which is `a` read in `S³`. -/
private theorem hopfLoopBoundaryHom_map_hopfLoop (k : ℕ)
    (a : π_ (k + 1) (sphere (0 : ℍ) 1) 1) :
    hopfLoopBoundaryHom v k (HomotopyGroup.map (hopfLoop v w hw hvw) (hopfLoop_one hw hvw) a) =
      a := by
  induction a using Quotient.inductionOn with
  | h a =>
  -- The shifted family of loops is `(s, t) ↦ [hopfLift (a t, s)]`, the loop coordinate `s` being
  -- the last cube direction of the shift.
  obtain ⟨γ, hγ, h⟩ := MooreLoopSpace.exists_congrEquiv_homotopyGroupMulEquiv_map_mk
    (hopfLoop v w hw hvw) (hopfLoop_one hw hvw) a
  let G : C(I × (I^(Fin (k + 1))),
      _root_.TopCat.of (sphere (0 : PiLp 2 fun _ : Fin (n + 1) ↦ ℍ) 1)) :=
    (hopfLift v w hw hvw).comp ⟨fun p ↦ (a p.2, p.1), by fun_prop⟩
  -- The lifts `(s, t) ↦ hopfLift (a t, s)` of the shifted loops start at `v` and stay there over
  -- the boundary of the cube.
  have hG : TopCat.IsBoundaryLift (hopfHom n) ⟨v, rfl⟩ γ G :=
    ⟨fun y ↦ by
      simp only [hγ, G, toPath_hopfLoop, piOptionEquivProdHomeomorph_symm_apply_some,
        piOptionEquivProdHomeomorph_symm_apply_none, ContinuousMap.comp_apply,
        ContinuousMap.coe_mk, TopCat.hom_ofHom],
      fun t ↦ hopfLift_zero hw hvw _,
      fun s t ht ↦ by simp [G, GenLoop.boundary a t ht, hopfLift_one_left]⟩
  rw [hopfLoopBoundaryHom_apply, hopfBoundary_apply, h]
  refine (congrArg _ (TopCat.fibrationBoundary_mk (mk_mem_serreFibrations n) hG)).trans ?_
  -- The lifts end at the fibre loop `t ↦ v (a t)`.
  refine (HomotopyGroup.homeomorphEquivOfEq_apply _ _ _).trans <|
    (HomotopyGroup.map_mk _ _ _).trans <| congrArg _ (GenLoop.ext _ _ fun t ↦ ?_)
  rw [GenLoop.map_apply]
  refine (hopfFiberHomeomorph v).symm_apply_eq.2 (Subtype.ext ?_)
  rw [coe_hopfFiberHomeomorph_apply, TopCat.IsBoundaryLift.endLoop_apply_coe]
  exact hopfLift_one hw hvw (a t)

end Splitting

/-- For `n ≥ 1` there is a unit vector of `ℍⁿ⁺¹` orthogonal to the quaternionic line of `x`: a
unit vector orthogonal to `x 1, x i, x j, x k` is orthogonal to `x a` for every `a`, by real
linearity of `a ↦ x a`. -/
private theorem exists_norm_eq_one_forall_inner_op_smul_eq_zero (hn : n ≠ 0)
    (x : PiLp 2 fun _ : Fin (n + 1) ↦ ℍ) :
    ∃ w : PiLp 2 fun _ : Fin (n + 1) ↦ ℍ, ‖w‖ = 1 ∧ ∀ a : ℍ, inner ℝ (op a • x) w = 0 := by
  classical
  let b := Quaternion.orthonormalBasisOneIJK
  let L : ℍ →ₗ[ℝ] PiLp 2 fun _ : Fin (n + 1) ↦ ℍ := (opLinearEquiv ℝ).toLinearMap.smulRight x
  have hcard :
      (Finset.univ.image (L ∘ b)).card < Module.finrank ℝ (PiLp 2 fun _ : Fin (n + 1) ↦ ℍ) := by
    refine Finset.card_image_le.trans_lt ?_
    rw [finrank_piLp_quaternion, Fintype.card_fin, Finset.card_univ, Fintype.card_fin]
    omega
  obtain ⟨w, hw, hLw⟩ := exists_norm_eq_one_forall_inner_eq_zero_of_card_lt_finrank _ hcard
  refine ⟨w, hw, fun a ↦ ?_⟩
  have hL : L a = op a • x := by simp [L, LinearMap.smulRight_apply]
  rw [← hL, ← b.sum_repr a, map_sum, sum_inner]
  refine Finset.sum_eq_zero fun i _ ↦ ?_
  rw [map_smul, real_inner_smul_left,
    hLw (L (b i)) (Finset.mem_image_of_mem (L ∘ b) (Finset.mem_univ i)), mul_zero]

/-- **The boundary map of the Hopf fibration splits on the loop space.** For `n ≥ 1` there is a
based map `j : S³ → ΩHPⁿ` such that `∂ (j_* a) = a` for every class `a` of `π_{k+1}(S³, 1)`,
where `∂ : π_{k+1}(ΩHPⁿ, 1) → π_{k+1}(S³, 1)` is the loop-space shift followed by the boundary
map. -/
theorem exists_hopfLoopBoundaryHom_map_eq (hn : n ≠ 0) :
    ∃ (j : C(sphere (0 : ℍ) 1, MooreLoopSpace (QuaternionicProjectiveSpace n) (mk n v)))
      (hj : j 1 = 1),
      ∀ k a, hopfLoopBoundaryHom v k (HomotopyGroup.map (N := Fin (k + 1)) j hj a) = a := by
  obtain ⟨w, hw, hvw⟩ := exists_norm_eq_one_forall_inner_op_smul_eq_zero hn v
  exact ⟨hopfLoop v w hw hvw, hopfLoop_one hw hvw, hopfLoopBoundaryHom_map_hopfLoop hw hvw⟩

/-- **The based Hopf product realizes the splitting.** For `n ≥ 1` there is a based map
`j : S³ → ΩHPⁿ` for which `j ⋆ Ωq : S³ × ΩS⁴ⁿ⁺³ → ΩHPⁿ` is a weak homotopy equivalence. -/
theorem exists_isWeakHomotopyEquivalence_hopfProduct (hn : n ≠ 0) :
    ∃ j : C(sphere (0 : ℍ) 1, MooreLoopSpace (QuaternionicProjectiveSpace n) (mk n v)),
      j 1 = 1 ∧ (hopfProduct v j).IsWeakHomotopyEquivalence := by
  obtain ⟨j, hj, hjb⟩ := exists_hopfLoopBoundaryHom_map_eq v hn
  refine ⟨j, hj, isWeakHomotopyEquivalence_hopfProduct v hj fun k ↦ ?_⟩
  have h : hopfLoopBoundaryHom v k ∘ HomotopyGroup.map (N := Fin (k + 1)) j hj = id :=
    funext (hjb k)
  rw [h]
  exact Function.bijective_id

end TauCeti.QuaternionicProjectiveSpace
