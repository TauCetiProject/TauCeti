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
import TauCeti.AlgebraicTopology.Sphere.HomotopyGroup

/-!
# The loop space of `HPⁿ` splits as `S³ × ΩS⁴ⁿ⁺³`

Let `q : S⁴ⁿ⁺³ → HPⁿ` be the quaternionic Hopf fibration, with fibre the unit quaternions `S³`,
and let `v` be a unit vector of `ℍⁿ⁺¹`. Given a based map `j : S³ → ΩHPⁿ` from the unit
quaternions to the Moore loop space at `[v]`, the **based Hopf product**
(`TauCeti.QuaternionicProjectiveSpace.hopfProduct`) is

`j ⋆ Ωq : S³ × ΩS⁴ⁿ⁺³ → ΩHPⁿ`, `(q, γ) ↦ j q * Ωq γ`,

the Moore concatenation of the loop `j q` with the image of the loop `γ` at `v`. It is a weak
homotopy equivalence as soon as `j` splits the looped Hopf fibration
(`TauCeti.QuaternionicProjectiveSpace.isWeakHomotopyEquivalence_hopfProduct`), and for `n ≥ 1`
such maps `j` exist
(`TauCeti.QuaternionicProjectiveSpace.exists_isWeakHomotopyEquivalence_hopfProduct`).

The proof compares homotopy groups through the exact homotopy sequence of the Hopf fibration
(`TauCeti.Topology.QuaternionicProjectiveSpace.Hopf.Exact`). Shifting by the Moore loop space and
taking the boundary in the loop coordinate gives the **boundary map of the looped fibration**
`∂ : π_{m+1}(ΩHPⁿ) → π_{m+1}(S³)` (`TauCeti.QuaternionicProjectiveSpace.loopHopfBoundary`), whose
kernel is the image of `(Ωq)_*` (`TauCeti.QuaternionicProjectiveSpace.loopHopfBoundary_eq_one_iff`).
In positive degrees the Moore loop space is a topological monoid with a strict unit, so the product
acts on homotopy groups by `(j ⋆ Ωq)_* (a × b) = j_* a * (Ωq)_* b` (`HomotopyGroup.map_mul_prod`).
Unlike the circle in the complex case, `S³` has nontrivial higher homotopy groups, so `j_*` is
required to split the sequence in every degree: `∂ ∘ j_*` is to be bijective on `π_{m+1}(S³)`
for every `m`. Then `∂` is onto in every degree, so the fibre inclusion `S³ → S⁴ⁿ⁺³` is trivial on
homotopy groups and `(Ωq)_*` is injective, and the sequence
`1 → π_{m+1}(ΩS⁴ⁿ⁺³) → π_{m+1}(ΩHPⁿ) → π_{m+1}(S³) → 1` is split exact
(`HomotopyGroup.bijective_map_mul_of_bijective_comp`).

A splitting family is written down explicitly for `n ≥ 1`
(`TauCeti.QuaternionicProjectiveSpace.exists_loopHopfBoundary_map_eq`). Choose a vector `w`
independent of the quaternionic line of `v`; the path
`t ↦ v ((1 - t) + t q) + ‖q - 1‖ t (1 - t) w` never vanishes, and normalized it runs in `S⁴ⁿ⁺³`
from `v` to `v q`. Its image is a loop of `HPⁿ` at `[v]`, constant when `q = 1`, whose lift ends at
`v q`; read as a Moore loop of length `‖q - 1‖`, the loop at `q = 1` is the unit. The boundary of
the family is therefore the identity of `S³`
(`TauCeti.TopCat.fibrationBoundary_congrEquiv_pathLoopSpaceMulEquiv_map`).

Since weak homotopy equivalences induce isomorphisms on singular homology, the splitting reduces
the integral homology of `ΩHPⁿ` to that of `S³ × ΩS⁴ⁿ⁺³`.

## Main definitions

* `TauCeti.QuaternionicProjectiveSpace.hopfProduct`: the based Hopf product `j ⋆ Ωq`.
* `TauCeti.QuaternionicProjectiveSpace.loopHopfBoundary`: the boundary map
  `π_{m+1}(ΩHPⁿ) → π_{m+1}(S³)` of the looped Hopf fibration.

## Main results

* `TauCeti.QuaternionicProjectiveSpace.isWeakHomotopyEquivalence_hopfProduct`: `j ⋆ Ωq` is a weak
  homotopy equivalence whenever `j_*` followed by the looped boundary map is bijective in every
  positive degree.
* `TauCeti.QuaternionicProjectiveSpace.exists_loopHopfBoundary_map_eq`: for `n ≥ 1` there is a
  based map `j` for which `j_*` followed by the looped boundary map is the identity.
* `TauCeti.QuaternionicProjectiveSpace.exists_isWeakHomotopyEquivalence_hopfProduct`: for `n ≥ 1`,
  there is a based map `j` for which `j ⋆ Ωq` is a weak homotopy equivalence.

## References

* A. Hatcher, *Algebraic Topology*, Theorem 4.41 and Example 4.45.
* J.-F. Barraud, M. Damian, V. Humilière, A. Oancea, *Floer homology with DG coefficients.
  Applications to cotangent bundles*, arXiv:2404.07953, §6.4.
* The statement and its layout follow Tau Ceti's splitting of the loop space of complex projective
  space in `TauCeti/Topology/ComplexProjectiveSpace/Hopf/LoopSpace.lean`.
-/

public section

noncomputable section

namespace TauCeti.QuaternionicProjectiveSpace

open Metric MulOpposite unitInterval Set
open scoped Topology Topology.Homotopy Quaternion RightActions NNReal

variable {n : ℕ} (v : sphere (0 : PiLp 2 fun _ : Fin (n + 1) ↦ ℍ) 1)

/-- The **based quaternionic Hopf product** `j ⋆ Ωq : S³ × ΩS⁴ⁿ⁺³ → ΩHPⁿ`, `(q, γ) ↦ j q * Ωq γ`:
the Moore concatenation of the loop `j q` of `HPⁿ` with the image of the loop `γ` of `S⁴ⁿ⁺³` under
the Hopf fibration `q`. -/
def hopfProduct (j : C(sphere (0 : ℍ) 1, MooreLoopSpace (QuaternionicProjectiveSpace n) (mk n v))) :
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

/-- The **boundary map of the looped Hopf fibration** `π_{m+1}(ΩHPⁿ, 1) → π_{m+1}(S³, 1)`: the Moore
loop-space shift `π_{m+1}(ΩHPⁿ) ≅ π_{m+2}(HPⁿ)`, followed by the boundary map of the Hopf
fibration, taken in the loop coordinate of the shift (the last cube direction). -/
def loopHopfBoundary (m : ℕ) :
    π_ (m + 1) (MooreLoopSpace (QuaternionicProjectiveSpace n) (mk n v)) 1 →*
      π_ (m + 1) (sphere (0 : ℍ) 1) 1 :=
  (hopfBoundaryHom v (Fin (m + 1))).comp <|
    (HomotopyGroup.congrMulEquiv (finSuccEquiv' (Fin.last (m + 1)))).toMonoidHom.comp
      (MooreLoopSpace.homotopyGroupMulEquiv (mk n v) m).toMonoidHom

theorem loopHopfBoundary_apply (m : ℕ)
    (a : π_ (m + 1) (MooreLoopSpace (QuaternionicProjectiveSpace n) (mk n v)) 1) :
    loopHopfBoundary v m a = hopfBoundary v (Fin (m + 1))
      (HomotopyGroup.congrEquiv (finSuccEquiv' (Fin.last (m + 1)))
        (MooreLoopSpace.homotopyGroupMulEquiv (mk n v) m a)) := by
  simp [loopHopfBoundary]

/-- **Exactness for the looped Hopf fibration.** A class of `π_{m+1}(ΩHPⁿ)` comes from `ΩS⁴ⁿ⁺³`
exactly when its boundary in `π_{m+1}(S³)` is trivial. -/
theorem loopHopfBoundary_eq_one_iff (m : ℕ)
    (c : π_ (m + 1) (MooreLoopSpace (QuaternionicProjectiveSpace n) (mk n v)) 1) :
    loopHopfBoundary v m c = 1 ↔
      c ∈ range (HomotopyGroup.map (N := Fin (m + 1))
        (MooreLoopSpace.map (x := v) ⟨mk n, continuous_mk n⟩ rfl).toContinuousMap
        (map_one (MooreLoopSpace.map (x := v) ⟨mk n, continuous_mk n⟩ rfl))) := by
  rw [loopHopfBoundary_apply, ← HomotopyGroup.mk_const_eq_one,
    ← mem_range_homotopyGroupMap_mk_iff]
  constructor
  · rintro ⟨d, hd⟩
    obtain ⟨d, rfl⟩ := (HomotopyGroup.congrEquiv (finSuccEquiv' (Fin.last (m + 1)))).surjective d
    rw [HomotopyGroup.map_congrEquiv, (HomotopyGroup.congrEquiv _).injective.eq_iff] at hd
    obtain ⟨b, rfl⟩ := (MooreLoopSpace.homotopyGroupMulEquiv v m).surjective d
    refine ⟨b, (MooreLoopSpace.homotopyGroupMulEquiv (mk n v) m).injective ?_⟩
    rw [MooreLoopSpace.homotopyGroupMulEquiv_map, hd]
  · rintro ⟨b, rfl⟩
    refine ⟨HomotopyGroup.congrEquiv (finSuccEquiv' (Fin.last (m + 1)))
      (MooreLoopSpace.homotopyGroupMulEquiv v m b), ?_⟩
    rw [HomotopyGroup.map_congrEquiv, MooreLoopSpace.homotopyGroupMulEquiv_map]

/-- If `j_*` followed by the looped boundary map is onto in degree `m + 2`, the Hopf fibration
induces an injection `π_{m+1}(ΩS⁴ⁿ⁺³) → π_{m+1}(ΩHPⁿ)`: the boundary map
`π_{m+3}(HPⁿ) → π_{m+2}(S³)` is then onto, so by exactness the fibre inclusion
`π_{m+2}(S³) → π_{m+2}(S⁴ⁿ⁺³)` is trivial. -/
private theorem injective_map_mooreLoopSpaceMap (m : ℕ)
    (h : Function.Surjective (loopHopfBoundary v (m + 1))) :
    Function.Injective (HomotopyGroup.map (N := Fin (m + 1))
      (MooreLoopSpace.map (x := v) ⟨mk n, continuous_mk n⟩ rfl).toContinuousMap
      (map_one (MooreLoopSpace.map (x := v) ⟨mk n, continuous_mk n⟩ rfl))) := by
  refine (injective_iff_map_eq_one (HomotopyGroup.mapHom (N := Fin (m + 1))
    (MooreLoopSpace.map (x := v) ⟨mk n, continuous_mk n⟩ rfl).toContinuousMap
    (map_one (MooreLoopSpace.map (x := v) ⟨mk n, continuous_mk n⟩ rfl)))).2 fun b hb ↦ ?_
  rw [HomotopyGroup.mapHom_apply] at hb
  have hs := congrArg (MooreLoopSpace.homotopyGroupMulEquiv (mk n v) m) hb
  rw [MooreLoopSpace.homotopyGroupMulEquiv_map, map_one, ← HomotopyGroup.mk_const_eq_one,
    ← mem_range_homotopyGroupMap_op_smul_iff] at hs
  obtain ⟨d, hd⟩ := hs
  obtain ⟨a, rfl⟩ := h d
  have hd' := (mem_range_hopfBoundary_iff v).1 ⟨_, (loopHopfBoundary_apply v (m + 1) a).symm⟩
  rw [hd, HomotopyGroup.mk_const_eq_one, MulEquiv.map_eq_one_iff] at hd'
  exact hd'

/-- **The loop space of `HPⁿ` splits as `S³ × ΩS⁴ⁿ⁺³`.** For a based map `j : S³ → ΩHPⁿ` such that
`j_*` followed by the boundary map of the looped Hopf fibration is bijective on every positive
homotopy group, the based Hopf product `j ⋆ Ωq : S³ × ΩS⁴ⁿ⁺³ → ΩHPⁿ`,
`(q, γ) ↦ j q * Ωq γ`, is a weak homotopy equivalence. -/
theorem isWeakHomotopyEquivalence_hopfProduct
    {j : C(sphere (0 : ℍ) 1, MooreLoopSpace (QuaternionicProjectiveSpace n) (mk n v))}
    (hj : j 1 = 1)
    (hjb : ∀ m, Function.Bijective (loopHopfBoundary v m ∘ HomotopyGroup.map j hj)) :
    (hopfProduct v j).IsWeakHomotopyEquivalence := by
  -- `S³`, `S⁴ⁿ⁺³` and `HPⁿ` are simply connected, so all three spaces are path connected.
  have : PathConnectedSpace (sphere (0 : ℍ) 1) :=
    (pathConnectedSpace_iff_subsingleton_homotopyGroup_zero (1 : sphere (0 : ℍ) 1)).2
      (subsingleton_homotopyGroup_sphere_quaternion (by simp) 1)
  have : PathConnectedSpace
      (MooreLoopSpace (sphere (0 : PiLp 2 fun _ : Fin (n + 1) ↦ ℍ) 1) v) :=
    (MooreLoopSpace.pathConnectedSpace_iff_subsingleton_pi1 v).2
      (subsingleton_homotopyGroup_sphere_piLp_quaternion (by simp; omega) v)
  have : PathConnectedSpace (MooreLoopSpace (QuaternionicProjectiveSpace n) (mk n v)) :=
    (MooreLoopSpace.pathConnectedSpace_iff_subsingleton_pi1 _).2
      (HomotopyGroup.pi1MulEquivFundamentalGroup.toEquiv.subsingleton_congr.2 inferInstance)
  -- The product sends the base point to the unit; the homotopy groups are compared there.
  -- In positive degrees `j_*` splits the exact sequence of the looped Hopf fibration.
  exact ContinuousMap.isWeakHomotopyEquivalence_of_forall_bijective_succ
    (x := ((1, 1) : sphere (0 : ℍ) 1 ×
      MooreLoopSpace (sphere (0 : PiLp 2 fun _ : Fin (n + 1) ↦ ℍ) 1) v)) (y := 1) (by simp [hj])
    fun m ↦ HomotopyGroup.bijective_map_mul_of_bijective_comp hj
      (map_one (MooreLoopSpace.map (x := v) ⟨mk n, continuous_mk n⟩ rfl)) (loopHopfBoundary v m)
      (hjb m)
      (injective_map_mooreLoopSpaceMap v m fun c ↦
        ⟨_, ((hjb (m + 1)).2 c).choose_spec⟩) (loopHopfBoundary_eq_one_iff v m)

/-! ### A family of loops splitting the looped Hopf fibration -/

section Family

variable {v} {w : PiLp 2 fun _ : Fin (n + 1) ↦ ℍ}

/-- The vector `v ((1 - t) + t q) + ‖q - 1‖ t (1 - t) w`. Its class in `HPⁿ` runs from `[v]` at
`t = 0` back to `[v q] = [v]` at `t = 1`, and stays at `[v]` when `q = 1`. -/
private def liftVec (v w : PiLp 2 fun _ : Fin (n + 1) ↦ ℍ) (p : sphere (0 : ℍ) 1 × I) :
    PiLp 2 fun _ : Fin (n + 1) ↦ ℍ :=
  v <• ((1 - (p.2 : ℝ)) • (1 : ℍ) + (p.2 : ℝ) • (p.1 : ℍ)) +
    (‖(p.1 : ℍ) - 1‖ * ((p.2 : ℝ) * (1 - p.2))) • w

private theorem continuous_liftVec (v w : PiLp 2 fun _ : Fin (n + 1) ↦ ℍ) :
    Continuous (liftVec v w) := by
  unfold liftVec
  fun_prop

/-- `liftVec v w` never vanishes when `w` is independent of the quaternionic line of `v`. -/
private theorem liftVec_ne_zero {v w : PiLp 2 fun _ : Fin (n + 1) ↦ ℍ}
    (hw : ∀ (a : ℍ) (c : ℝ), v <• a + c • w = 0 → a = 0 ∧ c = 0) (p : sphere (0 : ℍ) 1 × I) :
    liftVec v w p ≠ 0 := by
  intro h
  obtain ⟨ha, hc⟩ := hw _ _ h
  have hq : (p.1 : ℍ) ≠ 0 := ne_zero_of_mem_unit_sphere p.1
  rcases mul_eq_zero.1 hc with hc | hc
  · rw [sub_eq_zero.1 (norm_eq_zero.1 hc), ← add_smul, sub_add_cancel, one_smul] at ha
    exact one_ne_zero ha
  · rcases mul_eq_zero.1 hc with ht | ht
    · rw [ht, sub_zero, one_smul, zero_smul, add_zero] at ha
      exact one_ne_zero ha
    · rw [ht, zero_smul, zero_add, show (p.2 : ℝ) = 1 by linarith, one_smul] at ha
      exact hq ha

variable (hw : ∀ (a : ℍ) (c : ℝ), (v : PiLp 2 fun _ : Fin (n + 1) ↦ ℍ) <• a + c • w = 0 →
  a = 0 ∧ c = 0)

/-- The normalized lift: a continuous family of paths in `S⁴ⁿ⁺³`, from `v` to `v q`. -/
private def hopfLift : C(sphere (0 : ℍ) 1 × I, sphere (0 : PiLp 2 fun _ : Fin (n + 1) ↦ ℍ) 1) :=
  normalizeToSphere _ (continuous_liftVec _ _) (liftVec_ne_zero hw)

private theorem hopfLift_zero (q : sphere (0 : ℍ) 1) : hopfLift hw (q, 0) = v := by
  refine Subtype.ext ?_
  simp only [hopfLift, coe_normalizeToSphere_apply, liftVec, Icc.coe_zero, sub_zero, one_smul,
    zero_smul, add_zero, zero_mul, mul_zero, op_one, one_smul]
  exact NormedSpace.normalize_eq_self_of_norm_eq_one (norm_eq_of_mem_sphere v)

private theorem hopfLift_one_left (t : I) : hopfLift hw (1, t) = v := by
  refine Subtype.ext ?_
  simp only [hopfLift, coe_normalizeToSphere_apply, liftVec, Metric.unitSphere.coe_one, sub_self,
    norm_zero, zero_mul, zero_smul, add_zero, ← add_smul, sub_add_cancel, one_smul]
  simp only [op_one, one_smul]
  exact NormedSpace.normalize_eq_self_of_norm_eq_one (norm_eq_of_mem_sphere v)

private theorem hopfLift_one_right (q : sphere (0 : ℍ) 1) : hopfLift hw (q, 1) = op q • v := by
  refine Subtype.ext ?_
  simp only [hopfLift, coe_normalizeToSphere_apply, liftVec, Icc.coe_one, sub_self, zero_smul,
    one_smul, zero_add, mul_zero, add_zero, Sphere.coe_op_sphere_smul, unop_op]
  exact NormedSpace.normalize_eq_self_of_norm_eq_one (by
    simpa using norm_eq_of_mem_sphere (op q • v))

/-- The loops `t ↦ [hopfLift (q, t)]` of `HPⁿ` at `[v]`, a family of fixed-interval loops. -/
private def hopfLoopPath : C(sphere (0 : ℍ) 1, Path (mk n v) (mk n v)) where
  toFun q :=
    { toFun t := mk n (hopfLift hw (q, t))
      continuous_toFun := by fun_prop
      source' := by rw [hopfLift_zero]
      target' := by rw [hopfLift_one_right, mk_op_smul] }
  continuous_toFun :=
    Path.continuous_uncurry_iff.1 <| (continuous_mk n).comp (hopfLift hw).continuous

private theorem hopfLoopPath_one : hopfLoopPath hw 1 = Path.refl (mk n v) := by
  ext t
  simp [hopfLoopPath, hopfLift_one_left]

/-- The loops of `hopfLoopPath` as Moore loops of length `‖q - 1‖`, so that the loop at `q = 1` is
the unit. -/
private def hopfLoop :
    C(sphere (0 : ℍ) 1, MooreLoopSpace (QuaternionicProjectiveSpace n) (mk n v)) where
  toFun q :=
    { toMoorePath := (hopfLoopPath hw q).toMoorePath.rescale ‖(q : ℍ) - 1‖₊
      source_eq := by simp
      target_eq := by
        rcases eq_or_ne ‖(q : ℍ) - 1‖₊ 0 with h | h
        · simp [h]
        · simp [MoorePath.target_rescale _ h] }
  continuous_toFun := MooreLoopSpace.isEmbedding_toMoorePath.continuous_iff.2 <|
    (Path.continuous_toMoorePath.comp
      (hopfLoopPath hw).continuous).moorePath_rescale_of_forall_eq_source (by fun_prop)
      fun q hq t ↦ by
        obtain rfl : q = 1 := Subtype.ext (sub_eq_zero.1 (nnNorm_eq_zero.1 hq))
        simp [hopfLoopPath_one]

private theorem hopfLoop_one : hopfLoop hw 1 = 1 :=
  MooreLoopSpace.ext <| by simp [hopfLoop]

private theorem toPath_hopfLoop (q : sphere (0 : ℍ) 1) :
    (hopfLoop hw q).toPath = hopfLoopPath hw q := by
  rcases eq_or_ne q 1 with rfl | hq
  · rw [hopfLoop_one, MooreLoopSpace.toPath_one, hopfLoopPath_one]
  have h : ‖(q : ℍ) - 1‖₊ ≠ 0 := fun h ↦ hq (Subtype.ext (sub_eq_zero.1 (nnNorm_eq_zero.1 h)))
  ext s
  simp [hopfLoop, MooreLoopSpace.toPath_apply, h]

/-- The family `hopfLoop` splits the looped Hopf fibration: `j_*` followed by the looped boundary
map is the identity. -/
private theorem loopHopfBoundary_map_hopfLoop (m : ℕ) (c : π_ (m + 1) (sphere (0 : ℍ) 1) 1) :
    loopHopfBoundary v m (HomotopyGroup.map (hopfLoop hw) (hopfLoop_one hw) c) = c := by
  have hpath : (MooreLoopSpace.homotopyEquivPath (mk n v)).toFun.comp (hopfLoop hw) =
      hopfLoopPath hw :=
    ContinuousMap.ext fun q ↦
      (MooreLoopSpace.homotopyEquivPath_apply (hopfLoop hw q)).trans (toPath_hopfLoop hw q)
  -- The lift of the loop `hopfLoopPath hw q` is `hopfLift hw (q, ·)`, which ends at `v q`.
  have hbd := TopCat.fibrationBoundary_congrEquiv_pathLoopSpaceMulEquiv_map
    (mk_mem_serreFibrations n) (b := mk n v) (e := ⟨v, rfl⟩) (hopfLoopPath hw)
    (hopfLoopPath_one hw) (hopfLift hw) (fun _ _ ↦ rfl) (hopfLift_zero hw)
    (hopfLift_one_left hw) ⟨hopfFiberHomeomorph v, (hopfFiberHomeomorph v).continuous⟩
    (fun q ↦ by simp [hopfLift_one_right]) m c
  rw [loopHopfBoundary_apply, MooreLoopSpace.homotopyGroupMulEquiv_apply,
    HomotopyGroup.map_comp_apply, HomotopyGroup.map_congr hpath _ (hopfLoopPath_one hw),
    hopfBoundary_apply, hbd, HomotopyGroup.homeomorphEquivOfEq_apply]
  exact HomotopyGroup.map_map_of_comp_eq_id _ _ _ _ (ContinuousMap.ext fun q ↦ by simp) c

end Family

/-- For `n ≥ 1`, a unit vector `v` of `ℍⁿ⁺¹` admits a vector `w` independent of its quaternionic
line: take a basis vector at a coordinate other than one where `v` is nonzero. -/
private theorem exists_independent (hn : n ≠ 0) :
    ∃ w : PiLp 2 fun _ : Fin (n + 1) ↦ ℍ, ∀ (a : ℍ) (c : ℝ),
      (v : PiLp 2 fun _ : Fin (n + 1) ↦ ℍ) <• a + c • w = 0 → a = 0 ∧ c = 0 := by
  obtain ⟨k, hk⟩ : ∃ k, (v : PiLp 2 fun _ : Fin (n + 1) ↦ ℍ) k ≠ 0 := by
    by_contra! h0
    exact ne_zero_of_mem_unit_sphere v (PiLp.ext h0)
  have : Nontrivial (Fin (n + 1)) := Fin.nontrivial_iff_two_le.2 (by omega)
  obtain ⟨l, hl⟩ := exists_ne k
  refine ⟨WithLp.toLp 2 (Pi.single l 1), fun a c h ↦ ?_⟩
  have hk' := congrArg (fun x : PiLp 2 fun _ : Fin (n + 1) ↦ ℍ ↦ x k) h
  have ha : a = 0 := by
    simpa [Pi.single_apply, hl.symm, hk] using hk'
  subst ha
  have hl' := congrArg (fun x : PiLp 2 fun _ : Fin (n + 1) ↦ ℍ ↦ x l) h
  exact ⟨rfl, by simpa using hl'⟩

/-- **A splitting of the looped Hopf fibration.** For `n ≥ 1` there is a based map
`j : S³ → ΩHPⁿ` such that `j_*` followed by the boundary map of the looped Hopf fibration is the
identity of `π_{m+1}(S³)` for every `m`. -/
theorem exists_loopHopfBoundary_map_eq (hn : n ≠ 0) :
    ∃ (j : C(sphere (0 : ℍ) 1, MooreLoopSpace (QuaternionicProjectiveSpace n) (mk n v)))
      (hj : j 1 = 1), ∀ m c, loopHopfBoundary v m (HomotopyGroup.map j hj c) = c :=
  have ⟨_, hw⟩ := exists_independent v hn
  ⟨hopfLoop hw, hopfLoop_one hw, loopHopfBoundary_map_hopfLoop hw⟩

/-- **The based Hopf product realizes the splitting.** For `n ≥ 1` there is a based map
`j : S³ → ΩHPⁿ` for which `j ⋆ Ωq : S³ × ΩS⁴ⁿ⁺³ → ΩHPⁿ` is a weak homotopy equivalence. -/
theorem exists_isWeakHomotopyEquivalence_hopfProduct (hn : n ≠ 0) :
    ∃ j : C(sphere (0 : ℍ) 1, MooreLoopSpace (QuaternionicProjectiveSpace n) (mk n v)),
      j 1 = 1 ∧ (hopfProduct v j).IsWeakHomotopyEquivalence :=
  have ⟨j, hj, h⟩ := exists_loopHopfBoundary_map_eq v hn
  ⟨j, hj, isWeakHomotopyEquivalence_hopfProduct v hj fun m ↦ by
    convert Function.bijective_id
    exact funext (h m)⟩

end TauCeti.QuaternionicProjectiveSpace
