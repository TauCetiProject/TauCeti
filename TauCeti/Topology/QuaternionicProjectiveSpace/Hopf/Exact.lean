/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicTopology.FundamentalGroupoid.SimplyConnected
public import TauCeti.Topology.Homotopy.HomotopyGroup.Homeomorph
public import TauCeti.Topology.Homotopy.SerreFibration.Exact
public import TauCeti.Topology.QuaternionicProjectiveSpace.Hopf.Basic
import TauCeti.AlgebraicTopology.NotSimplyConnected
import TauCeti.AlgebraicTopology.Sphere.HomotopyGroup

/-!
# The exact homotopy sequence of the quaternionic Hopf fibration `S³ → S⁴ⁿ⁺³ → HPⁿ`

The quaternionic Hopf fibration `S⁴ⁿ⁺³ → HPⁿ`, `v ↦ [v]`, is a Serre fibration whose fibre over
`[v]` is the unit quaternions `S³`, through `q ↦ v q`
(`TauCeti.QuaternionicProjectiveSpace.mk_mem_serreFibrations`,
`TauCeti.QuaternionicProjectiveSpace.hopfFiberHomeomorph`). This file reads off its exact
homotopy sequence, with the fibre replaced by `S³` and the fibre inclusion by the orbit map
`q ↦ v q`:

`⋯ → π_{k+1}(S⁴ⁿ⁺³) → π_{k+1}(HPⁿ) → π_k(S³) → π_k(S⁴ⁿ⁺³) → π_k(HPⁿ) → ⋯`,

with boundary map `TauCeti.QuaternionicProjectiveSpace.hopfBoundary`. The sphere `S⁴ⁿ⁺³` is
`(4n + 2)`-connected (`TauCeti.subsingleton_homotopyGroup_sphere_piLp_quaternion`), so the
sequence gives:

* `HPⁿ` is `3`-connected: `π_k(HPⁿ)` vanishes for `k ≤ 3`
  (`TauCeti.QuaternionicProjectiveSpace.subsingleton_homotopyGroup`), since `S³` is `2`-connected
  (`TauCeti.subsingleton_homotopyGroup_sphere_quaternion`); in particular `HPⁿ` is simply
  connected (`TauCeti.QuaternionicProjectiveSpace.instSimplyConnectedSpace`);
* for `1 ≤ k ≤ 4n + 1` the boundary map `π_{k+1}(HPⁿ) → π_k(S³)` is an isomorphism
  (`TauCeti.QuaternionicProjectiveSpace.hopfBoundaryMulEquiv`). For `n ≥ 1` and `k = 3` this is
  `π₄(HPⁿ) ≅ π₃(S³)`.

The degree-four specialization `π₄(HPⁿ) ≅ π₃(S³)` fails for `HP⁰`, a point, which is why the
range of `k` depends on `n`.

The layout follows the exact sequence of the sphere bundle `SO(n) → SO(1 + n) → Sⁿ` in
`TauCeti/Topology/Grassmannian/SphereBundle/Exact.lean`.

Homotopy groups are indexed as in `TauCeti.TopCat.fibrationBoundary`: `π_k` is modelled on the
cube `I^N` for a finite type `N` of cardinality `k`, and `π_{k+1}` on `I^(Option N)`. The groups
of the sphere and of `HPⁿ` are based at a unit vector `v` and at its class `[v]`; in `S³` the base
point is `1`.

## Main definitions

* `TauCeti.QuaternionicProjectiveSpace.hopfBoundary`: the boundary map
  `π_{k+1}(HPⁿ, [v]) → π_k(S³, 1)`.
* `TauCeti.QuaternionicProjectiveSpace.hopfBoundaryHom`: for `k ≥ 1`, the boundary map as a group
  homomorphism.
* `TauCeti.QuaternionicProjectiveSpace.hopfBoundaryMulEquiv`: for `1 ≤ k ≤ 4n + 1`, the boundary
  map as an isomorphism `π_{k+1}(HPⁿ, [v]) ≃* π_k(S³, 1)`.

## Main results

* `TauCeti.QuaternionicProjectiveSpace.mem_range_homotopyGroupMap_mk_iff`: exactness at
  `π_{k+1}(HPⁿ)`.
* `TauCeti.QuaternionicProjectiveSpace.mem_range_hopfBoundary_iff`: exactness at `π_k(S³)`.
* `TauCeti.QuaternionicProjectiveSpace.mem_range_homotopyGroupMap_op_smul_iff`: exactness at
  `π_k(S⁴ⁿ⁺³)`.
* `TauCeti.QuaternionicProjectiveSpace.subsingleton_homotopyGroup`: `π_k(HPⁿ)` vanishes for
  `1 ≤ k ≤ 3`.
* `TauCeti.QuaternionicProjectiveSpace.bijective_hopfBoundary`: for `1 ≤ k ≤ 4n + 1`, the boundary
  map is bijective.

## References

* A. Hatcher, [*Algebraic Topology*](https://pi.math.cornell.edu/~hatcher/AT/AT.pdf),
  Theorem 4.41 and the Hopf bundles of §4.2.
-/

public section

noncomputable section

open CategoryTheory Metric Set MulOpposite
open scoped Topology.Homotopy Quaternion

namespace TauCeti.QuaternionicProjectiveSpace

variable {n : ℕ} (v : sphere (0 : PiLp 2 fun _ : Fin (n + 1) ↦ ℍ) 1) {N : Type*}

/-! ### The fibre -/

/-- The unit vector `v`, as the base point of the fibre of the Hopf fibration over `[v]`. -/
private abbrev fiberPoint : (hopfHom n).fiber (mk n v) :=
  ⟨v, rfl⟩

/-- The identification of the fibre over `[v]` with `S³` sends `v` to `1`. -/
private theorem hopfFiberHomeomorph_symm_fiberPoint :
    (hopfFiberHomeomorph v).symm (fiberPoint v) = 1 :=
  (hopfFiberHomeomorph v).symm_apply_eq.2 (hopfFiberHomeomorph_one v).symm

variable (N) in
/-- The identification `π_N(F, v) ≃ π_N(S³, 1)` of the homotopy groups of the fibre `F` of the
Hopf fibration over `[v]` with those of the unit quaternions. -/
private def fiberEquiv :
    HomotopyGroup N ((hopfHom n).fiber (mk n v)) (fiberPoint v) ≃
      HomotopyGroup N (sphere (0 : ℍ) 1) 1 :=
  HomotopyGroup.homeomorphEquivOfEq (hopfFiberHomeomorph v).symm
    (hopfFiberHomeomorph_symm_fiberPoint v)

/-- `fiberEquiv` preserves the class of the constant generalized loop. -/
private theorem fiberEquiv_mk_const :
    fiberEquiv v N ⟦GenLoop.const⟧ = (⟦GenLoop.const⟧ : HomotopyGroup N (sphere (0 : ℍ) 1) 1) :=
  congrArg _ (GenLoop.map_const _ _)

/-- The orbit map `q ↦ v q` of the unit quaternions on `v`, the fibre inclusion of the Hopf
fibration over `[v]` read in `S³`. -/
private abbrev orbitMap : C(sphere (0 : ℍ) 1, sphere (0 : PiLp 2 fun _ : Fin (n + 1) ↦ ℍ) 1) :=
  ⟨fun q ↦ op q • v, continuous_op.smul continuous_const⟩

/-- The inverse of `fiberEquiv` followed by the fibre inclusion is the map induced by the orbit
map `q ↦ v q`. -/
private theorem map_fiberι_fiberEquiv_symm (c : HomotopyGroup N (sphere (0 : ℍ) 1) 1) :
    HomotopyGroup.map ((hopfHom n).fiberι _).hom
        (TopCat.Hom.fiberι_apply (hopfHom n) _ (fiberPoint v)) ((fiberEquiv v N).symm c) =
      HomotopyGroup.map (orbitMap v) (one_smul _ v) c := by
  rw [fiberEquiv, HomotopyGroup.homeomorphEquivOfEq_symm_apply, HomotopyGroup.map_comp_apply]
  exact HomotopyGroup.map_congr
    (ContinuousMap.ext fun q ↦ (TopCat.Hom.fiberι_apply (hopfHom n) _
      (hopfFiberHomeomorph v q)).trans (coe_hopfFiberHomeomorph_apply v q)) _ _ c

/-! ### The boundary map -/

variable (N) in
/-- The **boundary map** `π_{k+1}(HPⁿ, [v]) → π_k(S³, 1)` of the quaternionic Hopf fibration,
where `k` is the cardinality of `N`. It is the boundary map of the Serre fibration
`S⁴ⁿ⁺³ → HPⁿ` (`TauCeti.TopCat.fibrationBoundary`), read in the unit quaternions through the
identification `q ↦ v q` of `S³` with the fibre over `[v]`. -/
def hopfBoundary [Finite N] :
    HomotopyGroup (Option N) (QuaternionicProjectiveSpace n) (mk n v) →
      HomotopyGroup N (sphere (0 : ℍ) 1) 1 :=
  fiberEquiv v N ∘ TopCat.fibrationBoundary (mk_mem_serreFibrations n) (fiberPoint v)

variable [Finite N]

/-- The boundary map of the Hopf fibration is the boundary map of the Serre fibration
`S⁴ⁿ⁺³ → HPⁿ`, read in `S³` through the identification
`TauCeti.QuaternionicProjectiveSpace.hopfFiberHomeomorph` of the unit quaternions with the
fibre. -/
theorem hopfBoundary_apply (a : HomotopyGroup (Option N) (QuaternionicProjectiveSpace n) (mk n v)) :
    hopfBoundary v N a =
      HomotopyGroup.homeomorphEquivOfEq (hopfFiberHomeomorph v).symm
        ((hopfFiberHomeomorph v).symm_apply_eq.2 (hopfFiberHomeomorph_one v).symm)
        (TopCat.fibrationBoundary (mk_mem_serreFibrations n) ⟨v, rfl⟩ a) :=
  (rfl)

/-- The boundary map of the Hopf fibration sends the class of the constant loop to the class of
the constant loop. -/
@[simp]
theorem hopfBoundary_const :
    hopfBoundary v N
        (⟦GenLoop.const⟧ : HomotopyGroup (Option N) (QuaternionicProjectiveSpace n) (mk n v)) =
      ⟦GenLoop.const⟧ :=
  (congrArg (fiberEquiv v N) (TopCat.fibrationBoundary_const _)).trans (fiberEquiv_mk_const v)

/-- For `k ≥ 1`, the boundary map of the Hopf fibration is multiplicative. -/
theorem hopfBoundary_mul [DecidableEq N] [Nonempty N]
    (a a' : HomotopyGroup (Option N) (QuaternionicProjectiveSpace n) (mk n v)) :
    hopfBoundary v N (a * a') = hopfBoundary v N a * hopfBoundary v N a' := by
  -- The group structures on the homotopy groups of `TopCat.of X` and of `X` agree only after
  -- unfolding `TopCat.of`, which `rw` does not do, so the multiplicativity of the boundary is
  -- applied with `erw`.
  rw [hopfBoundary_apply, hopfBoundary_apply, hopfBoundary_apply]
  erw [TopCat.fibrationBoundary_mul]
  exact HomotopyGroup.map_mul _ _ _ _

variable (N) in
/-- For `k ≥ 1`, the boundary map `π_{k+1}(HPⁿ, [v]) → π_k(S³, 1)` of the Hopf fibration as a
group homomorphism. -/
def hopfBoundaryHom [DecidableEq N] [Nonempty N] :
    HomotopyGroup (Option N) (QuaternionicProjectiveSpace n) (mk n v) →*
      HomotopyGroup N (sphere (0 : ℍ) 1) 1 :=
  MonoidHom.mk' (hopfBoundary v N) (hopfBoundary_mul v)

@[simp]
theorem coe_hopfBoundaryHom [DecidableEq N] [Nonempty N] :
    ⇑(hopfBoundaryHom v N) = hopfBoundary v N :=
  (rfl)

/-! ### Exactness -/

/-- **Exactness at `π_{k+1}(HPⁿ)`.** A class of `π_{k+1}(HPⁿ, [v])` comes from `S⁴ⁿ⁺³` exactly
when its boundary in `π_k(S³)` is trivial. -/
theorem mem_range_homotopyGroupMap_mk_iff
    {a : HomotopyGroup (Option N) (QuaternionicProjectiveSpace n) (mk n v)} :
    a ∈ range (HomotopyGroup.map (x := v) ⟨mk n, continuous_mk n⟩ rfl) ↔
      hopfBoundary v N a = (⟦GenLoop.const⟧ : HomotopyGroup N (sphere (0 : ℍ) 1) 1) :=
  (TopCat.mem_range_homotopyGroupMap_iff_fibrationBoundary_eq (e := fiberPoint v) _).trans
    ((fiberEquiv v N).injective.eq_iff' (fiberEquiv_mk_const v)).symm

/-- **Exactness at `π_k(S³)`.** A class of `π_k(S³, 1)` is a boundary exactly when it becomes
trivial in `π_k(S⁴ⁿ⁺³, v)` under the orbit map `q ↦ v q`. -/
theorem mem_range_hopfBoundary_iff {c : HomotopyGroup N (sphere (0 : ℍ) 1) 1} :
    c ∈ range (hopfBoundary v N) ↔
      HomotopyGroup.map ⟨fun q : sphere (0 : ℍ) 1 ↦ op q • v, continuous_op.smul continuous_const⟩
          (one_smul _ v) c =
        (⟦GenLoop.const⟧ : HomotopyGroup N (sphere (0 : PiLp 2 fun _ : Fin (n + 1) ↦ ℍ) 1) v) := by
  rw [hopfBoundary, range_comp, mem_image_equiv, ← map_fiberι_fiberEquiv_symm]
  exact TopCat.mem_range_fibrationBoundary_iff _

/-- **Exactness at `π_k(S⁴ⁿ⁺³)`.** A class of `π_k(S⁴ⁿ⁺³, v)` comes from `S³` under the orbit map
`q ↦ v q` exactly when it becomes trivial in `π_k(HPⁿ, [v])`. -/
theorem mem_range_homotopyGroupMap_op_smul_iff
    {d : HomotopyGroup N (sphere (0 : PiLp 2 fun _ : Fin (n + 1) ↦ ℍ) 1) v} :
    d ∈ range (HomotopyGroup.map (N := N) (x := 1)
        ⟨fun q : sphere (0 : ℍ) 1 ↦ op q • v, continuous_op.smul continuous_const⟩
        (one_smul _ v)) ↔
      HomotopyGroup.map ⟨mk n, continuous_mk n⟩ rfl d =
        (⟦GenLoop.const⟧ : HomotopyGroup N (QuaternionicProjectiveSpace n) (mk n v)) := by
  have h : range (HomotopyGroup.map (N := N) (x := 1) (y := v) (orbitMap v) (one_smul _ v)) =
      range (HomotopyGroup.map ((hopfHom n).fiberι _).hom
        (TopCat.Hom.fiberι_apply (hopfHom n) _ (fiberPoint v))) := by
    rw [← (fiberEquiv v N).symm.surjective.range_comp]
    exact congrArg range (funext fun c ↦ (map_fiberι_fiberEquiv_symm v c).symm)
  rw [h]
  exact TopCat.mem_range_homotopyGroupMap_fiberι_iff (mk_mem_serreFibrations n)

/-! ### Homotopy groups of `HPⁿ` -/

/-- **`HPⁿ` is `3`-connected**: `π_k(HPⁿ)` vanishes for `1 ≤ k ≤ 3`, at every base point. For
`n ≥ 1` every class lifts to `S⁴ⁿ⁺³`, because its boundary lies in a vanishing homotopy group of
`S³`, and the homotopy groups of `S⁴ⁿ⁺³` vanish in these degrees; `HP⁰` is a point. -/
theorem subsingleton_homotopyGroup (hN : Nat.card N < 3) (p : QuaternionicProjectiveSpace n) :
    Subsingleton (HomotopyGroup (Option N) (QuaternionicProjectiveSpace n) p) := by
  -- `HP⁰` is a point; for `n ≥ 1` the sphere `S⁴ⁿ⁺³` is `3`-connected.
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · infer_instance
  obtain ⟨w, rfl⟩ := mk_surjective n p
  have := subsingleton_homotopyGroup_sphere_quaternion (N := N) hN 1
  have := subsingleton_homotopyGroup_sphere_piLp_quaternion (N := Option N) (by simp; omega) w
  -- Every class is the image of the trivial class of `S⁴ⁿ⁺³`.
  have h (a : HomotopyGroup (Option N) (QuaternionicProjectiveSpace n) (mk n w)) :
      a = ⟦GenLoop.const⟧ := by
    obtain ⟨b, rfl⟩ :=
      (mem_range_homotopyGroupMap_mk_iff w (N := N) (a := a)).2 (Subsingleton.elim _ _)
    rw [Subsingleton.elim b ⟦GenLoop.const⟧]
    exact (HomotopyGroup.map_mk _ _ _).trans (congrArg _ (GenLoop.map_const _ _))
  exact ⟨fun a a' ↦ (h a).trans (h a').symm⟩

/-- **`HPⁿ` is simply connected.** -/
instance instSimplyConnectedSpace : SimplyConnectedSpace (QuaternionicProjectiveSpace n) :=
  simplyConnectedSpace_iff_forall_subsingleton_fundamentalGroup.2
    ⟨inferInstance, fun p ↦
      have := subsingleton_homotopyGroup (N := Fin 0) (by simp) p
      (homotopyGroupEquivFundamentalGroupOfUnique (Option (Fin 0))).subsingleton_congr.1
        inferInstance⟩

/-- **The boundary map `π_{k+1}(HPⁿ) → π_k(S³)` is bijective for `1 ≤ k ≤ 4n + 1`.** In
particular `π₄(HPⁿ) ≅ π₃(S³)` for `n ≥ 1`. -/
theorem bijective_hopfBoundary [Nonempty N] (hN : Nat.card N < 4 * n + 2) :
    Function.Bijective (hopfBoundary v N) := by
  classical
  refine ⟨?_, fun c ↦ ?_⟩
  · -- The kernel of the boundary is the image of `π_{k+1}(S⁴ⁿ⁺³)`, which is trivial.
    have := subsingleton_homotopyGroup_sphere_piLp_quaternion (N := Option N) (by simp; omega) v
    refine (injective_iff_map_eq_one (hopfBoundaryHom v N)).2 fun a ha ↦ ?_
    rw [coe_hopfBoundaryHom, _root_.HomotopyGroup.one_def] at ha
    obtain ⟨b, rfl⟩ := (mem_range_homotopyGroupMap_mk_iff v).2 ha
    rw [Subsingleton.elim b 1, HomotopyGroup.map_one]
  · -- Every class of the fibre dies in `π_k(S⁴ⁿ⁺³)`, which is trivial, so it is a boundary.
    have := subsingleton_homotopyGroup_sphere_piLp_quaternion (N := N) (by simp; omega) v
    exact (mem_range_hopfBoundary_iff v).2 (Subsingleton.elim _ _)

/-- For `1 ≤ k ≤ 4n + 1`, the boundary map of the Hopf fibration as an isomorphism
`π_{k+1}(HPⁿ, [v]) ≃* π_k(S³, 1)`. For `n ≥ 1` and `k = 3` this is `π₄(HPⁿ) ≅ π₃(S³)`. -/
def hopfBoundaryMulEquiv [DecidableEq N] [Nonempty N] (hN : Nat.card N < 4 * n + 2) :
    HomotopyGroup (Option N) (QuaternionicProjectiveSpace n) (mk n v) ≃*
      HomotopyGroup N (sphere (0 : ℍ) 1) 1 :=
  MulEquiv.ofBijective (hopfBoundaryHom v N) (bijective_hopfBoundary v hN)

@[simp]
theorem hopfBoundaryMulEquiv_apply [DecidableEq N] [Nonempty N] (hN : Nat.card N < 4 * n + 2)
    (a : HomotopyGroup (Option N) (QuaternionicProjectiveSpace n) (mk n v)) :
    hopfBoundaryMulEquiv v hN a = hopfBoundary v N a :=
  (rfl)

end TauCeti.QuaternionicProjectiveSpace
