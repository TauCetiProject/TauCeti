/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.TensorProduct.Basic
public import TauCeti.RepresentationTheory.Crystal.Component
public import TauCeti.RepresentationTheory.Crystal.Highest
public import TauCeti.RepresentationTheory.LSPath.Crystal.Basic
public import TauCeti.RepresentationTheory.LSPath.Highest
public import TauCeti.RepresentationTheory.LSPath.Raise
public import TauCeti.RepresentationTheory.LSPath.Realization
public import TauCeti.RepresentationTheory.LSPath.Weight

import TauCeti.LinearAlgebra.RootSystem.BaseChange.Basic
import TauCeti.LinearAlgebra.RootSystem.Reduced

/-!
# The normal crystal of Lakshmibai–Seshadri paths

Let `P : RootDatum ι X Y` be a finite reduced root datum with base `b`, and let `λ : X` be a
dominant weight. Littelmann's path model equips the finite type `LSPath P b λ` of
Lakshmibai–Seshadri encodings of shape `λ` with the structure of a connected normal crystal
`TauCeti.LSPath.crystal` with unique highest element `TauCeti.LSPath.straight λ`.

First, `X → ℚ ⊗[ℤ] X` (`TensorProduct.mk ℤ ℚ X 1`) provides a canonical faithful rational
realization (`RootPairing.injective_mk_rat`) in which no two distinct orbit weights lie on the same
ray (`RootPairing.pairwise_not_sameRay_mk_rat_orbit`). In every realization `(𝕜, V, f, F)`, the
image of `LSPath.toPLPath` is crystal-admissible (`TauCeti.LSPath.isCrystalSet_range_toPLPath`);
transporting `TauCeti.PLPath.normalCrystalOn` from `ℚ ⊗[ℤ] X` along `LSPath.toPLPath` defines
`TauCeti.LSPath.crystal`, and pushing paths forward from `ℚ ⊗[ℤ] X` proves universal compatibility
with `PLPath.raise`, `PLPath.lower`, and `PLPath.minHeight` in **every** additive realization
`(𝕜, V, f, F)`, without requiring `f` to be injective.

Since `TauCeti.LSPath.straight λ` is the unique LS path annihilated by all raising operators
(`TauCeti.LSPath.forall_crystal_e_eq_none_iff`) and `LSPath P b λ` is finite
(`TauCeti.LSPath.finite`), every LS path is obtained from `straight λ` by a lowering word
(`TauCeti.LSPath.exists_fWord_straight_eq_some`), the crystal graph is connected
(`TauCeti.LSPath.connected_crystal_graph`), and the realized LS paths of shape `λ` coincide with
the root-operator component of `PLPath.straight 𝕜 (f λ)`
(`TauCeti.LSPath.mem_range_toPLPath_iff_exists_lowerWord`,
`TauCeti.LSPath.mem_range_toPLPath_iff_reflTransGen`).

## Main definitions and results

* `RootPairing.corootRat`, `RootPairing.injective_mk_rat`, and
  `RootPairing.pairwise_not_sameRay_mk_rat_orbit`: canonical rational realization in `ℚ ⊗[ℤ] X`.
* `TauCeti.LSPath.weight`, `TauCeti.LSPath.apply_weight`, and `TauCeti.LSPath.crystal`:
  lattice-valued weight and the normal crystal on `LSPath P b λ`.
* `TauCeti.LSPath.isCrystalSet_range_toPLPath`, `TauCeti.LSPath.raise_toPLPath`, and
  `TauCeti.LSPath.lower_toPLPath`: admissibility and universal realization compatibility.
* `TauCeti.LSPath.congrIso` and `TauCeti.LSPath.dualIso`: shape transport and Littelmann's path
  duality as strict crystal isomorphisms.
* `TauCeti.LSPath.forall_crystal_e_eq_none_iff`, `TauCeti.LSPath.exists_fWord_straight_eq_some`,
  `TauCeti.LSPath.connected_crystal_graph`,
  `TauCeti.LSPath.mem_range_toPLPath_iff_exists_lowerWord`, and
  `TauCeti.LSPath.mem_range_toPLPath_iff_reflTransGen`.

## References

* P. Littelmann, *A Littlewood–Richardson rule for symmetrizable Kac–Moody algebras*, Invent.
  Math. 116 (1994), 329--346, Section 4.
* P. Littelmann, *Paths and root operators in representation theory*, Ann. of Math. 142 (1995),
  499--525, Sections 2 and 4.
-/

public section

open scoped TensorProduct

/-! ### Canonical rational realization of a root datum -/

namespace RootPairing

section RationalRealization

variable {ι X Y : Type*} [AddCommGroup X] [AddCommGroup Y] (P : RootPairing ι ℤ X Y)

/-- Lift an additive map `X →+ V` into a vector space over a characteristic-zero field `𝕜` across
`ℚ ⊗[ℤ] X` by sending `q ⊗ₜ x` to `(q : 𝕜) • f x`. -/
private def liftRatAddHom (𝕜 : Type*) {V : Type*} [Field 𝕜] [CharZero 𝕜] [AddCommGroup V]
    [Module 𝕜 V] (f : X →+ V) : (ℚ ⊗[ℤ] X) →+ V :=
  TensorProduct.liftAddHom
    (AddMonoidHom.mk'
      (fun q : ℚ ↦ AddMonoidHom.mk' (fun x : X ↦ (q : 𝕜) • f x) (fun _ _ ↦ by simp [smul_add]))
      (fun _ _ ↦ by ext x; simp [Rat.cast_add, add_smul]))
    (fun _ _ _ ↦ by
      simp only [zsmul_eq_mul, AddMonoidHom.mk'_apply, Rat.cast_mul, Rat.cast_intCast, map_zsmul]
      rw [mul_smul, Int.cast_smul_eq_zsmul])

private theorem liftRatAddHom_tmul (𝕜 : Type*) {V : Type*} [Field 𝕜] [CharZero 𝕜] [AddCommGroup V]
    [Module 𝕜 V] (f : X →+ V) (q : ℚ) (x : X) :
    liftRatAddHom 𝕜 f (q ⊗ₜ[ℤ] x) = (q : 𝕜) • f x :=
  (rfl)

private theorem liftRatAddHom_smul (𝕜 : Type*) {V : Type*} [Field 𝕜] [CharZero 𝕜] [AddCommGroup V]
    [Module 𝕜 V] (f : X →+ V) (c : ℚ) (u : ℚ ⊗[ℤ] X) :
    liftRatAddHom 𝕜 f (c • u) = (c : 𝕜) • liftRatAddHom 𝕜 f u := by
  refine TensorProduct.inductionOn u (fun q x ↦ ?_) (fun _ _ ih₁ ih₂ ↦ ?_)
  · rw [TensorProduct.smul_tmul', smul_eq_mul, liftRatAddHom_tmul, liftRatAddHom_tmul,
      Rat.cast_mul, mul_smul]
  · rw [smul_add, map_add, ih₁, ih₂, map_add, smul_add]

/-- The rational linear form on `ℚ ⊗[ℤ] X` induced by the `i`-th coroot `P.coroot i`. -/
def corootRat (i : ι) : Module.Dual ℚ (ℚ ⊗[ℤ] X) :=
  LinearMap.liftBaseChange ℚ ((Algebra.ofId ℤ ℚ).toLinearMap.comp (P.coroot' i))

@[simp]
theorem corootRat_tmul (i : ι) (q : ℚ) (x : X) :
    P.corootRat i (q ⊗ₜ[ℤ] x) = q * (P.coroot' i x : ℚ) := by
  simp [corootRat]

theorem corootRat_mk_one (i : ι) (x : X) :
    P.corootRat i (TensorProduct.mk ℤ ℚ X 1 x) = (P.coroot' i x : ℚ) := by
  simp [TensorProduct.mk_apply]

include P in
/-- For a root datum `P : RootDatum ι X Y`, the canonical inclusion `x ↦ 1 ⊗ₜ x` of `X` into
`ℚ ⊗[ℤ] X` is injective, as the perfect pairing with `Y` separates points. -/
theorem injective_mk_rat : Function.Injective (TensorProduct.mk ℤ ℚ X (1 : ℚ)) :=
  P.tensorProduct_mk_injective ℚ

private noncomputable instance : MulAction P.weylGroup (ℚ ⊗[ℤ] X) where
  smul w := (P.weylGroupRootRep w).baseChange ℚ
  one_smul u := by
    change ((P.weylGroupRootRep 1).baseChange ℚ) u = u
    simp
  mul_smul w₁ w₂ u := by
    change ((P.weylGroupRootRep (w₁ * w₂)).baseChange ℚ) u = _
    rw [map_mul, Module.End.mul_eq_comp, LinearMap.baseChange_comp]
    rfl

private instance : SMulCommClass P.weylGroup ℚ (ℚ ⊗[ℤ] X) :=
  ⟨fun w c u ↦ ((P.weylGroupRootRep w).baseChange ℚ).map_smul c u⟩

/-- No two distinct vectors in the realized Weyl orbit of `λ` in `ℚ ⊗[ℤ] X` lie on the same
rational ray. -/
theorem pairwise_not_sameRay_mk_rat_orbit (b : P.Base) [Finite ι] [P.IsReduced] (lam : X) :
    (Set.range fun w : P.weylGroup ↦ TensorProduct.mk ℤ ℚ X (1 : ℚ) (w • lam)).Pairwise
      fun u v ↦ ¬ SameRay ℚ u v := by
  have := P.finite_weylGroup_of_base b
  have hsmul (w : P.weylGroup) :
      w • TensorProduct.mk ℤ ℚ X (1 : ℚ) lam = TensorProduct.mk ℤ ℚ X (1 : ℚ) (w • lam) :=
    (P.weylGroupRootRep w).baseChange_tmul 1 lam
  simp_rw [← hsmul]
  exact fun _ hu _ hv huv h ↦ huv (h.eq_of_mem_orbit hu hv (Set.finite_range _))

end RationalRealization

end RootPairing

namespace TauCeti.LSPath

open RootPairing

/-! ### Pushing piecewise-linear paths forward from `ℚ ⊗[ℤ] X` to any realization -/

section Pushforward

variable {X : Type*} (𝕜 : Type*) {V : Type*} [AddCommGroup X] [Field 𝕜] [LinearOrder 𝕜]
  [IsStrictOrderedRing 𝕜] [AddCommGroup V] [Module 𝕜 V]

private abbrev liftRat (f : X →+ V) : (ℚ ⊗[ℤ] X) →+ V :=
  RootPairing.liftRatAddHom 𝕜 f

private theorem apply_liftRat (f : X →+ V) (F : Module.Dual 𝕜 V)
    (g : Module.Dual ℚ (ℚ ⊗[ℤ] X))
    (hF : ∀ x : X, F (f x) = (g (1 ⊗ₜ[ℤ] x) : 𝕜)) (u : ℚ ⊗[ℤ] X) :
    F (liftRat 𝕜 f u) = (g u : 𝕜) := by
  refine TensorProduct.inductionOn u (fun q x ↦ ?_) (fun _ _ ih₁ ih₂ ↦ by simp [ih₁, ih₂])
  rw [liftRatAddHom_tmul, map_smul, smul_eq_mul, hF x, ← Rat.cast_mul, ← smul_eq_mul, ← map_smul,
    TensorProduct.smul_tmul', smul_eq_mul, mul_one]

private theorem sameRay_liftRat (f : X →+ V) {u₁ u₂ : ℚ ⊗[ℤ] X} (h : SameRay ℚ u₁ u₂) :
    SameRay 𝕜 (liftRat 𝕜 f u₁) (liftRat 𝕜 f u₂) := by
  rcases h with rfl | rfl | ⟨r₁, r₂, hr₁, hr₂, heq⟩
  · simp [SameRay.zero_left]
  · simp [SameRay.zero_right]
  · rw [show u₁ = (r₁⁻¹ * r₂) • u₂ by rw [mul_smul, ← heq, inv_smul_smul₀ hr₁.ne'],
      liftRatAddHom_smul]
    exact SameRay.sameRay_nonneg_smul_left _
      (Rat.cast_nonneg.mpr (mul_nonneg (inv_nonneg.mpr hr₁.le) hr₂.le))

private theorem move_map_liftRat (f : X →+ V) {l m : List (ℚ ⊗[ℤ] X)}
    (h : PLPath.Move ℚ l m) :
    PLPath.Move 𝕜 (l.map (liftRat 𝕜 f)) (m.map (liftRat 𝕜 f)) := by
  cases h with
  | merge l₁ l₂ hvw =>
    simpa using PLPath.Move.merge (l₁.map (liftRat 𝕜 f)) (l₂.map (liftRat 𝕜 f))
      (sameRay_liftRat 𝕜 f hvw)
  | erase_zero l₁ l₂ =>
    simpa using PLPath.Move.erase_zero (l₁.map (liftRat 𝕜 f)) (l₂.map (liftRat 𝕜 f))

private noncomputable def mapRat (f : X →+ V) (p : PLPath ℚ (ℚ ⊗[ℤ] X)) : PLPath 𝕜 V :=
  PLPath.ofSegments 𝕜 (p.segments.map (liftRat 𝕜 f))

private theorem mapRat_ofSegments (f : X →+ V) (l : List (ℚ ⊗[ℤ] X)) :
    mapRat 𝕜 f (PLPath.ofSegments ℚ l) = PLPath.ofSegments 𝕜 (l.map (liftRat 𝕜 f)) := by
  rw [mapRat, PLPath.segments_ofSegments, PLPath.ofSegments_eq_ofSegments_iff]
  exact (Relation.EqvGen.reflTransGen_le_eqvGen _ _ _
    ((PLPath.reflTransGen_move_normalize l).lift _ fun _ _ h ↦ move_map_liftRat 𝕜 f h)).symm _ _

private theorem endpoint_mapRat (f : X →+ V) (p : PLPath ℚ (ℚ ⊗[ℤ] X)) :
    (mapRat 𝕜 f p).endpoint = liftRat 𝕜 f p.endpoint := by
  simp [mapRat, PLPath.endpoint_def, map_list_sum]

private theorem mapRat_reverse (f : X →+ V) (p : PLPath ℚ (ℚ ⊗[ℤ] X)) :
    mapRat 𝕜 f p.reverse = (mapRat 𝕜 f p).reverse := by
  simp [mapRat, PLPath.segments_reverse, List.map_reverse, List.map_map,
    PLPath.reverse_ofSegments, Function.comp_def]

private theorem listMinHeight_map_liftRat (f : X →+ V) {F : Module.Dual 𝕜 V}
    {g : Module.Dual ℚ (ℚ ⊗[ℤ] X)} (hFG : ∀ u, F (liftRat 𝕜 f u) = (g u : 𝕜))
    (l : List (ℚ ⊗[ℤ] X)) :
    PLPath.listMinHeight F (l.map (liftRat 𝕜 f)) = ((PLPath.listMinHeight g l : ℚ) : 𝕜) := by
  induction l with
  | nil => simp
  | cons v l ih =>
    rw [List.map_cons, PLPath.listMinHeight_cons, PLPath.listMinHeight_cons, hFG v, ih,
      ← Rat.cast_add, ← Rat.cast_zero, ← (Rat.cast_mono (K := 𝕜)).map_min]

private theorem minHeight_mapRat (f : X →+ V) {F : Module.Dual 𝕜 V}
    {g : Module.Dual ℚ (ℚ ⊗[ℤ] X)} (hFG : ∀ u, F (liftRat 𝕜 f u) = (g u : 𝕜))
    (p : PLPath ℚ (ℚ ⊗[ℤ] X)) :
    (mapRat 𝕜 f p).minHeight F = ((p.minHeight g : ℚ) : 𝕜) := by
  rw [mapRat, PLPath.minHeight_ofSegments, listMinHeight_map_liftRat 𝕜 f hFG,
    ← PLPath.minHeight_def]

private theorem reflectRecords_map_liftRat (f : X →+ V) {F : Module.Dual 𝕜 V}
    {g : Module.Dual ℚ (ℚ ⊗[ℤ] X)} (hFG : ∀ u, F (liftRat 𝕜 f u) = (g u : 𝕜))
    (x : ℚ ⊗[ℤ] X) (c : ℚ) (l : List (ℚ ⊗[ℤ] X)) :
    PLPath.reflectRecords F (liftRat 𝕜 f x) (c : 𝕜) (l.map (liftRat 𝕜 f)) =
      (PLPath.reflectRecords g x c l).map (liftRat 𝕜 f) := by
  induction l generalizing c with
  | nil => simp
  | cons v l ih =>
    have hmin : min (F (liftRat 𝕜 f v) + PLPath.listMinHeight F (l.map (liftRat 𝕜 f))) (c : 𝕜) =
        (min (g v + PLPath.listMinHeight g l) c : ℚ) := by
      rw [hFG v, listMinHeight_map_liftRat 𝕜 f hFG l, ← Rat.cast_add,
        (Rat.cast_mono (K := 𝕜)).map_min]
    have hc : (c : 𝕜) - F (liftRat 𝕜 f v) = ((c - g v : ℚ) : 𝕜) := by simp [hFG v]
    by_cases h : 0 < min (g v + PLPath.listMinHeight g l) c
    · rw [List.map_cons, PLPath.reflectRecords_cons_of_pos (hmin ▸ Rat.cast_pos.mpr h),
        PLPath.reflectRecords_cons_of_pos h, List.map_cons, List.map_cons, hmin, hc, ih (c - g v)]
      congr 1
      · simp [Module.preReflection_apply, map_sub, liftRatAddHom_smul, hFG]
      · rw [List.cons.injEq]; refine ⟨?_, rfl⟩
        rw [hFG v, ← Rat.cast_div, ← Rat.cast_one, ← Rat.cast_sub, liftRatAddHom_smul]
    · rw [List.map_cons, PLPath.reflectRecords_cons_of_nonpos
        (hmin ▸ Rat.cast_nonpos.mpr (le_of_not_gt h)),
        PLPath.reflectRecords_cons_of_nonpos (le_of_not_gt h), List.map_cons, hc, ih (c - g v)]

private theorem listLower_map_liftRat (f : X →+ V) {F : Module.Dual 𝕜 V}
    {g : Module.Dual ℚ (ℚ ⊗[ℤ] X)} (hFG : ∀ u, F (liftRat 𝕜 f u) = (g u : 𝕜))
    (x : ℚ ⊗[ℤ] X) (l : List (ℚ ⊗[ℤ] X)) :
    PLPath.listLower F (liftRat 𝕜 f x) (l.map (liftRat 𝕜 f)) =
      (PLPath.listLower g x l).map (List.map (liftRat 𝕜 f)) := by
  have hsum : F (l.map (liftRat 𝕜 f)).sum = (g l.sum : 𝕜) := by rw [← map_list_sum, hFG]
  have hm := listMinHeight_map_liftRat 𝕜 f hFG l
  have hcond : (1 : 𝕜) ≤ F (l.map (liftRat 𝕜 f)).sum -
      PLPath.listMinHeight F (l.map (liftRat 𝕜 f)) ↔ 1 ≤ g l.sum - PLPath.listMinHeight g l := by
    rw [hsum, hm, ← Rat.cast_sub, ← Rat.cast_one, Rat.cast_le]
  rw [PLPath.listLower_def, PLPath.listLower_def]
  by_cases h : 1 ≤ g l.sum - PLPath.listMinHeight g l
  · rw [ite_eq_left (hcond.mpr h), ite_eq_left h, Option.map_some, hm, ← Rat.cast_one,
      ← Rat.cast_add, reflectRecords_map_liftRat 𝕜 f hFG]
  · rw [ite_eq_right (mt hcond.mp h), ite_eq_right h, Option.map_none]

private theorem lower_mapRat (f : X →+ V) {F : Module.Dual 𝕜 V}
    {g : Module.Dual ℚ (ℚ ⊗[ℤ] X)} (hFG : ∀ u, F (liftRat 𝕜 f u) = (g u : 𝕜))
    (x : ℚ ⊗[ℤ] X) (p : PLPath ℚ (ℚ ⊗[ℤ] X)) :
    PLPath.lower F (liftRat 𝕜 f x) (mapRat 𝕜 f p) =
      (PLPath.lower g x p).map (mapRat 𝕜 f) := by
  obtain ⟨l, rfl⟩ := PLPath.ofSegments_surjective p
  simp only [mapRat_ofSegments, PLPath.lower_ofSegments, listLower_map_liftRat 𝕜 f hFG,
    Option.map_map]
  exact congrArg (fun h ↦ Option.map h _) (funext fun m ↦ (mapRat_ofSegments 𝕜 f m).symm)

private theorem raise_mapRat (f : X →+ V) {F : Module.Dual 𝕜 V}
    {g : Module.Dual ℚ (ℚ ⊗[ℤ] X)} (hFG : ∀ u, F (liftRat 𝕜 f u) = (g u : 𝕜))
    (x : ℚ ⊗[ℤ] X) (p : PLPath ℚ (ℚ ⊗[ℤ] X)) :
    PLPath.raise F (liftRat 𝕜 f x) (mapRat 𝕜 f p) =
      (PLPath.raise g x p).map (mapRat 𝕜 f) := by
  simp only [PLPath.raise_def, ← mapRat_reverse, lower_mapRat 𝕜 f hFG, Option.map_map]
  exact congrArg (fun h ↦ Option.map h _) (funext fun q ↦ (mapRat_reverse 𝕜 f q).symm)

end Pushforward

/-! ### Lattice-valued weight and the normal crystal on `LSPath P b λ` -/

variable {ι X Y : Type*} [AddCommGroup X] [AddCommGroup Y]
  {P : RootDatum ι X Y} {b : P.Base} [Finite ι] [P.IsReduced] {lam : X}

private abbrev mkRatAddHom (X : Type*) [AddCommGroup X] : X →+ (ℚ ⊗[ℤ] X) :=
  (TensorProduct.mk ℤ ℚ X 1).toAddMonoidHom

private noncomputable abbrev toRatPLPath (π : LSPath P b lam) : PLPath ℚ (ℚ ⊗[ℤ] X) :=
  π.toPLPath ℚ (mkRatAddHom X)

private theorem toRatPLPath_injective (hlam : lam ∈ dominantChamber P b) :
    Function.Injective (toRatPLPath (P := P) (b := b) (lam := lam)) :=
  toPLPath_injective hlam P.injective_mk_rat.injOn (P.pairwise_not_sameRay_mk_rat_orbit b lam)

private theorem mapRat_toRatPLPath {𝕜 V : Type*} [Field 𝕜] [LinearOrder 𝕜]
    [IsStrictOrderedRing 𝕜] [AddCommGroup V] [Module 𝕜 V] (f : X →+ V)
    (π : LSPath P b lam) :
    mapRat 𝕜 f (toRatPLPath π) = π.toPLPath 𝕜 f := by
  rw [toRatPLPath, toPLPath_def, toPLPath_def, mapRat_ofSegments]
  congr 1
  simp [timed_def, List.map_ofFn, Function.comp_def, liftRatAddHom_smul, mkRatAddHom,
    liftRatAddHom_tmul]

/-- **The lattice-valued weight of a Lakshmibai–Seshadri path of dominant shape.** Its image in any
realization `(𝕜, V, f)` is the endpoint `(π.toPLPath 𝕜 f).endpoint` (`TauCeti.LSPath.apply_weight`).
-/
noncomputable def weight (hlam : lam ∈ dominantChamber P b) (π : LSPath P b lam) : X :=
  Classical.choose
    (π.existsUnique_endpoint_eq (𝕜 := ℚ) hlam (mkRatAddHom X) P.injective_mk_rat)

private theorem mkRat_weight (hlam : lam ∈ dominantChamber P b) (π : LSPath P b lam) :
    mkRatAddHom X (π.weight hlam) = (toRatPLPath π).endpoint :=
  (Classical.choose_spec
    (π.existsUnique_endpoint_eq (𝕜 := ℚ) hlam (mkRatAddHom X) P.injective_mk_rat)).1.symm

/-- In every realization `f : X →+ V` over an ordered field `𝕜`, the image of `π.weight hlam` is
the endpoint of the realized path `π.toPLPath 𝕜 f`. -/
theorem apply_weight (𝕜 : Type*) {V : Type*} [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜]
    [AddCommGroup V] [Module 𝕜 V] (f : X →+ V) (hlam : lam ∈ dominantChamber P b)
    (π : LSPath P b lam) :
    f (π.weight hlam) = (π.toPLPath 𝕜 f).endpoint := by
  have h1 : liftRat 𝕜 f (mkRatAddHom X (π.weight hlam)) = f (π.weight hlam) := by
    simp [mkRatAddHom, liftRatAddHom_tmul]
  rw [← h1, mkRat_weight, ← endpoint_mapRat, mapRat_toRatPLPath]

@[simp]
theorem weight_straight (hlam : lam ∈ dominantChamber P b) :
    (straight lam).weight hlam = lam :=
  P.injective_mk_rat (by
    simpa [mkRatAddHom, toPLPath_straight] using
      apply_weight ℚ (mkRatAddHom X) hlam (straight lam))

theorem weight_congr {lam' : X} (h : lam = lam') (hlam : lam ∈ dominantChamber P b)
    (π : LSPath P b lam) :
    (congr h π).weight (h ▸ hlam) = π.weight hlam := by subst h; simp

/-- For a reduced root datum with finite index type, `-(w₀ • λ)` is dominant whenever `λ` is
dominant. -/
theorem neg_smul_longestElement_mem_dominantChamber (hlam : lam ∈ dominantChamber P b) :
    -(longestElement P b • lam) ∈ dominantChamber P b := by
  have := P.flip_isReduced
  exact neg_smul_mem_dominantChamber_longestElement hlam

theorem weight_dual (hlam : lam ∈ dominantChamber P b)
    (hlam' : -(longestElement P b • lam) ∈ dominantChamber P b) (π : LSPath P b lam) :
    (dual π).weight hlam' = -π.weight hlam := by
  apply P.injective_mk_rat
  change mkRatAddHom X _ = mkRatAddHom X _
  rw [apply_weight ℚ, map_neg, apply_weight ℚ, toPLPath_dual, PLPath.endpoint_reverse]

/-- The weight of an LS path of dominant shape differs from its last orbit weight `τ_l • λ` by an
element of the root lattice `P.rootSpan ℤ`. -/
theorem weight_sub_last_mem_rootSpan (hlam : lam ∈ dominantChamber P b)
    (π : LSPath P b lam) :
    π.weight hlam - (π.dir (Fin.last _)).1 • lam ∈ P.rootSpan ℤ := by
  obtain ⟨m, hm, heq⟩ := π.exists_mem_rootSpan_endpoint_eq_add (𝕜 := ℚ) hlam (mkRatAddHom X)
  have hw : π.weight hlam = (π.dir (Fin.last _)).1 • lam + m :=
    P.injective_mk_rat (by change mkRatAddHom X _ = mkRatAddHom X _; rw [apply_weight ℚ, heq])
  simpa [hw] using hm

/-- **Admissibility of realized LS paths.** In every realization `(𝕜, V, f)` with height forms `F`
inducing the simple coroots, the image of `LSPath.toPLPath` for dominant `λ` is a
crystal-admissible set (`TauCeti.PLPath.IsCrystalSet`). -/
theorem isCrystalSet_range_toPLPath {𝕜 V : Type*} [Field 𝕜] [LinearOrder 𝕜]
    [IsStrictOrderedRing 𝕜] [AddCommGroup V] [Module 𝕜 V]
    (hlam : lam ∈ dominantChamber P b) (f : X →+ V) (F : b.support → Module.Dual 𝕜 V)
    (hF : ∀ (i : b.support) (x : X), F i (f x) = (P.coroot' i x : 𝕜)) :
    PLPath.IsCrystalSet b f F (Set.range fun π : LSPath P b lam ↦ π.toPLPath 𝕜 f) where
  endpoint_mem_range := by rintro _ ⟨π, rfl⟩; exact ⟨π.weight hlam, apply_weight 𝕜 f hlam π⟩
  exists_minHeight_eq_intCast := by
    rintro _ ⟨π, rfl⟩ i
    have := P.flip_isReduced
    obtain ⟨e, _, he, _⟩ :=
      π.exists_neg_minHeight_eq_natCast_and_apply_endpoint_sub_minHeight_eq_natCast
        hlam f i (F i) (hF i)
    exact ⟨-(e : ℤ), by push_cast; linarith⟩
  mem_of_raise_eq_some hr hπ := mem_range_toPLPath_of_raise_eq_some hlam f _ (F _) (hF _) hπ hr
  mem_of_lower_eq_some hl hπ := mem_range_toPLPath_of_lower_eq_some hlam f _ (F _) (hF _) hπ hl

section CrystalConstruction

omit [Finite ι] [P.IsReduced] in
private theorem corootRat_mkRatAddHom (i : b.support) (x : X) :
    P.corootRat i (mkRatAddHom X x) = (P.coroot' i x : ℚ) :=
  P.corootRat_mk_one i x

private noncomputable abbrev ratCrystalOn (hlam : lam ∈ dominantChamber P b) :
    NormalCrystal P b (Set.range (toRatPLPath (P := P) (b := b) (lam := lam))) :=
  PLPath.normalCrystalOn (show Function.Injective (mkRatAddHom X) from P.injective_mk_rat)
    corootRat_mkRatAddHom
    (isCrystalSet_range_toPLPath hlam (mkRatAddHom X) (fun i ↦ P.corootRat i)
      corootRat_mkRatAddHom)

private noncomputable abbrev toRatRangeEquiv (hlam : lam ∈ dominantChamber P b) :
    LSPath P b lam ≃ Set.range (toRatPLPath (P := P) (b := b) (lam := lam)) :=
  Equiv.ofInjective toRatPLPath (toRatPLPath_injective hlam)

/-- **The normal crystal of Lakshmibai–Seshadri paths of dominant shape `λ`.** Its weight map is
`TauCeti.LSPath.weight`, and its raising and lowering operators realize Littelmann's path root
operators in every additive realization of `X` (`TauCeti.LSPath.raise_toPLPath`,
`TauCeti.LSPath.lower_toPLPath`). -/
noncomputable def crystal (hlam : lam ∈ dominantChamber P b) :
    NormalCrystal P b (LSPath P b lam) :=
  (ratCrystalOn hlam).transport (toRatRangeEquiv hlam).symm

private theorem toRatPLPath_symm_toRatRangeEquiv (hlam : lam ∈ dominantChamber P b)
    (s : Set.range (toRatPLPath (P := P) (b := b) (lam := lam))) :
    toRatPLPath ((toRatRangeEquiv hlam).symm s) = s.1 :=
  congrArg Subtype.val ((toRatRangeEquiv hlam).apply_symm_apply s)

private theorem map_toRatPLPath_crystal_e (hlam : lam ∈ dominantChamber P b) (i : b.support)
    (π : LSPath P b lam) :
    ((crystal hlam).e i π).map toRatPLPath =
      PLPath.raise (P.corootRat i) (mkRatAddHom X (P.root i)) (toRatPLPath π) := by
  rw [crystal, NormalCrystal.transport_e, Equiv.symm_symm, ratCrystalOn, Option.map_map]
  exact ((congrArg (Option.map · _)
    (funext (toRatPLPath_symm_toRatRangeEquiv hlam))).trans
    (PLPath.unattach_normalCrystalOn_e i (toRatRangeEquiv hlam π)))

private theorem map_toRatPLPath_crystal_f (hlam : lam ∈ dominantChamber P b) (i : b.support)
    (π : LSPath P b lam) :
    ((crystal hlam).f i π).map toRatPLPath =
      PLPath.lower (P.corootRat i) (mkRatAddHom X (P.root i)) (toRatPLPath π) := by
  rw [crystal, NormalCrystal.transport_f, Equiv.symm_symm, ratCrystalOn, Option.map_map]
  exact ((congrArg (Option.map · _)
    (funext (toRatPLPath_symm_toRatRangeEquiv hlam))).trans
    (PLPath.unattach_normalCrystalOn_f i (toRatRangeEquiv hlam π)))

end CrystalConstruction

/-! ### Universal compatibility with realizations -/

section Realization

@[simp]
theorem crystal_wt (hlam : lam ∈ dominantChamber P b) (π : LSPath P b lam) :
    (crystal hlam).wt π = π.weight hlam := by
  rw [crystal, NormalCrystal.transport_wt, Equiv.symm_symm, ratCrystalOn,
    PLPath.normalCrystalOn_wt_eq_iff]
  exact (mkRat_weight hlam π).symm

variable {𝕜 V : Type*} [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜]
  [AddCommGroup V] [Module 𝕜 V]

/-- **Universal compatibility of `crystal.e` with `PLPath.raise`.** In any realization `(𝕜, V, f)`
with a height form `F` inducing the simple coroot pairing `⟨-, αᵢ^∨⟩`, raising the realized path
`π.toPLPath 𝕜 f` agrees with applying `(crystal hlam).e i` and then realizing. -/
theorem raise_toPLPath (hlam : lam ∈ dominantChamber P b) (f : X →+ V) (i : b.support)
    (F : Module.Dual 𝕜 V) (hF : ∀ x, F (f x) = (P.coroot' i x : 𝕜)) (π : LSPath P b lam) :
    PLPath.raise F (f (P.root i)) (π.toPLPath 𝕜 f) =
      ((crystal hlam).e i π).map (·.toPLPath 𝕜 f) := by
  have hFG : ∀ u, F (liftRat 𝕜 f u) = (P.corootRat i u : 𝕜) :=
    apply_liftRat 𝕜 f F (P.corootRat i) fun x ↦ by simp [hF]
  have hroot : f (P.root i) = liftRat 𝕜 f (mkRatAddHom X (P.root i)) := by
    simp [mkRatAddHom, liftRatAddHom_tmul]
  rw [← mapRat_toRatPLPath f π, hroot, raise_mapRat 𝕜 f hFG, ← map_toRatPLPath_crystal_e hlam,
    Option.map_map]
  exact congrArg (fun h ↦ Option.map h _) (funext fun ρ ↦ mapRat_toRatPLPath (𝕜 := 𝕜) f ρ)

/-- **Universal compatibility of `crystal.f` with `PLPath.lower`.** In any realization `(𝕜, V, f)`
with a height form `F` inducing the simple coroot pairing `⟨-, αᵢ^∨⟩`, lowering the realized path
`π.toPLPath 𝕜 f` agrees with applying `(crystal hlam).f i` and then realizing. -/
theorem lower_toPLPath (hlam : lam ∈ dominantChamber P b) (f : X →+ V) (i : b.support)
    (F : Module.Dual 𝕜 V) (hF : ∀ x, F (f x) = (P.coroot' i x : 𝕜)) (π : LSPath P b lam) :
    PLPath.lower F (f (P.root i)) (π.toPLPath 𝕜 f) =
      ((crystal hlam).f i π).map (·.toPLPath 𝕜 f) := by
  have hFG : ∀ u, F (liftRat 𝕜 f u) = (P.corootRat i u : 𝕜) :=
    apply_liftRat 𝕜 f F (P.corootRat i) fun x ↦ by simp [hF]
  have hroot : f (P.root i) = liftRat 𝕜 f (mkRatAddHom X (P.root i)) := by
    simp [mkRatAddHom, liftRatAddHom_tmul]
  rw [← mapRat_toRatPLPath f π, hroot, lower_mapRat 𝕜 f hFG, ← map_toRatPLPath_crystal_f hlam,
    Option.map_map]
  exact congrArg (fun h ↦ Option.map h _) (funext fun ρ ↦ mapRat_toRatPLPath (𝕜 := 𝕜) f ρ)

/-- Universal compatibility of `crystal.ε` with `PLPath.minHeight`: in any realization, the
minimum simple-coroot height of `π.toPLPath 𝕜 f` is `-((crystal hlam).ε i π)`. -/
theorem minHeight_toPLPath_eq_neg_crystal_ε (hlam : lam ∈ dominantChamber P b) (f : X →+ V)
    (i : b.support) (F : Module.Dual 𝕜 V) (hF : ∀ x, F (f x) = (P.coroot' i x : 𝕜))
    (π : LSPath P b lam) :
    (π.toPLPath 𝕜 f).minHeight F = -((crystal hlam).ε i π : 𝕜) := by
  have hFG : ∀ u, F (liftRat 𝕜 f u) = (P.corootRat i u : 𝕜) :=
    apply_liftRat 𝕜 f F (P.corootRat i) fun x ↦ by simp [hF]
  have hm : (toRatPLPath π).minHeight (P.corootRat i) = -((crystal hlam).ε i π : ℚ) := by
    simp [crystal, ratCrystalOn, NormalCrystal.transport_ε]
  rw [← mapRat_toRatPLPath f π, minHeight_mapRat 𝕜 f hFG, hm, Rat.cast_neg, Rat.cast_natCast]

/-- Universal compatibility of `crystal.φ` with `PLPath.minHeight`: in any realization,
`F (π.toPLPath 𝕜 f).endpoint - (π.toPLPath 𝕜 f).minHeight F = (crystal hlam).φ i π`. -/
theorem apply_endpoint_sub_minHeight_toPLPath_eq_crystal_φ
    (hlam : lam ∈ dominantChamber P b) (f : X →+ V) (i : b.support) (F : Module.Dual 𝕜 V)
    (hF : ∀ x, F (f x) = (P.coroot' i x : 𝕜)) (π : LSPath P b lam) :
    F (π.toPLPath 𝕜 f).endpoint - (π.toPLPath 𝕜 f).minHeight F =
      ((crystal hlam).φ i π : 𝕜) := by
  rw [← apply_weight 𝕜 f hlam, hF, minHeight_toPLPath_eq_neg_crystal_ε hlam f i F hF]
  have hcast : (((crystal hlam).φ i π : 𝕜) - ((crystal hlam).ε i π : 𝕜)) =
      (P.coroot' i (π.weight hlam) : 𝕜) := by
    simpa [crystal_wt] using congrArg (Int.cast (R := 𝕜)) ((crystal hlam).φ_sub_ε i π)
  linarith

/-- Iterated raising on realized LS paths agrees with `(crystal hlam).eIter`. -/
theorem raiseIter_toPLPath (hlam : lam ∈ dominantChamber P b) (f : X →+ V) (i : b.support)
    (F : Module.Dual 𝕜 V) (hF : ∀ x, F (f x) = (P.coroot' i x : 𝕜)) (n : ℕ)
    (π : LSPath P b lam) :
    PLPath.raiseIter F (f (P.root i)) n (π.toPLPath 𝕜 f) =
      ((crystal hlam).eIter i n π).map (·.toPLPath 𝕜 f) := by
  induction n generalizing π with
  | zero => simp
  | succ n ih =>
    rw [PLPath.raiseIter_succ, NormalCrystal.eIter_succ, raise_toPLPath hlam f i F hF]
    cases (crystal hlam).e i π <;> simp [ih]

/-- Iterated lowering on realized LS paths agrees with `(crystal hlam).fIter`. -/
theorem lowerIter_toPLPath (hlam : lam ∈ dominantChamber P b) (f : X →+ V) (i : b.support)
    (F : Module.Dual 𝕜 V) (hF : ∀ x, F (f x) = (P.coroot' i x : 𝕜)) (n : ℕ)
    (π : LSPath P b lam) :
    PLPath.lowerIter F (f (P.root i)) n (π.toPLPath 𝕜 f) =
      ((crystal hlam).fIter i n π).map (·.toPLPath 𝕜 f) := by
  induction n generalizing π with
  | zero => simp
  | succ n ih =>
    rw [PLPath.lowerIter_succ, NormalCrystal.fIter_succ, lower_toPLPath hlam f i F hF]
    cases (crystal hlam).f i π <;> simp [ih]

/-- Raising along a word on realized LS paths agrees with `(crystal hlam).eWord`. -/
theorem raiseWord_toPLPath (hlam : lam ∈ dominantChamber P b) (f : X →+ V)
    (F : b.support → Module.Dual 𝕜 V) (hF : ∀ i x, F i (f x) = (P.coroot' i x : 𝕜))
    (w : List b.support) (π : LSPath P b lam) :
    PLPath.raiseWord F (fun i ↦ f (P.root i)) w (π.toPLPath 𝕜 f) =
      ((crystal hlam).eWord w π).map (·.toPLPath 𝕜 f) := by
  induction w generalizing π with
  | nil => simp
  | cons i w ih =>
    rw [PLPath.raiseWord_cons, NormalCrystal.eWord_cons, raise_toPLPath hlam f i (F i) (hF i)]
    cases (crystal hlam).e i π <;> simp [ih]

/-- Lowering along a word on realized LS paths agrees with `(crystal hlam).fWord`. -/
theorem lowerWord_toPLPath (hlam : lam ∈ dominantChamber P b) (f : X →+ V)
    (F : b.support → Module.Dual 𝕜 V) (hF : ∀ i x, F i (f x) = (P.coroot' i x : 𝕜))
    (w : List b.support) (π : LSPath P b lam) :
    PLPath.lowerWord F (fun i ↦ f (P.root i)) w (π.toPLPath 𝕜 f) =
      ((crystal hlam).fWord w π).map (·.toPLPath 𝕜 f) := by
  induction w generalizing π with
  | nil => simp
  | cons i w ih =>
    rw [PLPath.lowerWord_cons, NormalCrystal.fWord_cons, lower_toPLPath hlam f i (F i) (hF i)]
    cases (crystal hlam).f i π <;> simp [ih]

/-- In any faithful ray-separating realization, `(crystal hlam).e i π = some ρ` is equivalent to
`PLPath.raise F (f (P.root i)) (π.toPLPath 𝕜 f) = some (ρ.toPLPath 𝕜 f)`. -/
theorem crystal_e_eq_some_iff (hlam : lam ∈ dominantChamber P b) {f : X →+ V}
    (hf : Set.InjOn f (Set.range fun w : P.weylGroup ↦ w • lam))
    (hS : (Set.range fun w : P.weylGroup ↦ f (w • lam)).Pairwise fun u v ↦ ¬ SameRay 𝕜 u v)
    (i : b.support) (F : Module.Dual 𝕜 V) (hF : ∀ x, F (f x) = (P.coroot' i x : 𝕜))
    {π ρ : LSPath P b lam} :
    (crystal hlam).e i π = some ρ ↔
      PLPath.raise F (f (P.root i)) (π.toPLPath 𝕜 f) = some (ρ.toPLPath 𝕜 f) := by
  rw [raise_toPLPath hlam f i F hF,
    ← (Option.map_injective (toPLPath_injective hlam hf hS)).eq_iff, Option.map_some]

/-- In any faithful ray-separating realization, `(crystal hlam).f i π = some ρ` is equivalent to
`PLPath.lower F (f (P.root i)) (π.toPLPath 𝕜 f) = some (ρ.toPLPath 𝕜 f)`. -/
theorem crystal_f_eq_some_iff (hlam : lam ∈ dominantChamber P b) {f : X →+ V}
    (hf : Set.InjOn f (Set.range fun w : P.weylGroup ↦ w • lam))
    (hS : (Set.range fun w : P.weylGroup ↦ f (w • lam)).Pairwise fun u v ↦ ¬ SameRay 𝕜 u v)
    (i : b.support) (F : Module.Dual 𝕜 V) (hF : ∀ x, F (f x) = (P.coroot' i x : 𝕜))
    {π ρ : LSPath P b lam} :
    (crystal hlam).f i π = some ρ ↔
      PLPath.lower F (f (P.root i)) (π.toPLPath 𝕜 f) = some (ρ.toPLPath 𝕜 f) := by
  rw [lower_toPLPath hlam f i F hF,
    ← (Option.map_injective (toPLPath_injective hlam hf hS)).eq_iff, Option.map_some]

end Realization

/-! ### Shape congruence and Littelmann's path duality as strict crystal isomorphisms -/

/-- Shape transport `LSPath.congr` along `λ = λ'` is a strict isomorphism of normal crystals. -/
noncomputable def congrIso {lam' : X} (h : lam = lam') (hlam : lam ∈ dominantChamber P b) :
    NormalCrystal.StrictIso (crystal hlam) (crystal (h ▸ hlam)) where
  toEquiv := congr h
  wt_toFun π := by subst h; simp
  e_toFun i π := by subst h; simp

@[simp]
theorem coe_congrIso {lam' : X} (h : lam = lam') (hlam : lam ∈ dominantChamber P b) :
    ⇑(congrIso h hlam) = congr h :=
  (rfl)

@[simp]
theorem congrIso_refl (hlam : lam ∈ dominantChamber P b) :
    congrIso (rfl : lam = lam) hlam = NormalCrystal.StrictIso.refl (crystal hlam) :=
  NormalCrystal.StrictIso.ext fun _ ↦ by simp

@[simp]
theorem congrIso_symm {lam' : X} (h : lam = lam') (hlam : lam ∈ dominantChamber P b) :
    (congrIso h hlam).symm = congrIso h.symm (h ▸ hlam) := by
  subst h
  exact NormalCrystal.StrictIso.ext fun π ↦
    by simpa using (NormalCrystal.StrictIso.refl (crystal hlam)).symm_apply_apply π

/-- **Littelmann's path duality `LSPath.dual` is a strict crystal isomorphism** from the dual
crystal `(crystal hlam).dual` onto `crystal hlam'` for `-(w₀ • λ)`. -/
noncomputable def dualIso (hlam : lam ∈ dominantChamber P b)
    (hlam' : -(longestElement P b • lam) ∈ dominantChamber P b :=
      neg_smul_longestElement_mem_dominantChamber hlam) :
    NormalCrystal.StrictIso (crystal hlam).dual (crystal hlam') where
  toEquiv := dual
  wt_toFun π := by simp [weight_dual hlam hlam' π]
  e_toFun i π := by
    simp only [Equiv.toFun_as_coe]
    apply Option.map_injective (toRatPLPath_injective hlam')
    rw [← raise_toPLPath hlam' (mkRatAddHom X) i (P.corootRat i) (P.corootRat_mk_one i),
      toPLPath_dual, PLPath.raise_reverse,
      lower_toPLPath hlam (mkRatAddHom X) i (P.corootRat i) (P.corootRat_mk_one i),
      NormalCrystal.dual_e, Option.map_map, Option.map_map]
    exact congrArg (fun h ↦ Option.map h _)
      (funext fun ρ : LSPath P b lam ↦ (toPLPath_dual ρ ℚ (mkRatAddHom X)).symm)

@[simp]
theorem coe_dualIso (hlam : lam ∈ dominantChamber P b)
    (hlam' : -(longestElement P b • lam) ∈ dominantChamber P b) :
    ⇑(dualIso hlam hlam') = dual :=
  (rfl)

/-! ### Highest element, connectedness, and comparison with the operator-generated component -/

/-- **Uniqueness of the highest LS path in `crystal hlam`.** An LS path of dominant shape `λ` is
annihilated by all crystal raising operators if and only if it is `straight λ`. -/
theorem forall_crystal_e_eq_none_iff (hlam : lam ∈ dominantChamber P b) (π : LSPath P b lam) :
    (∀ i, (crystal hlam).e i π = none) ↔ π = straight lam := by
  have := P.flip_isReduced
  rw [← π.forall_raise_eq_none_iff hlam (mkRatAddHom X) (fun i ↦ P.corootRat i)
    (fun i ↦ P.corootRat_mk_one i)]
  refine forall_congr' fun i ↦ ?_
  rw [raise_toPLPath hlam (mkRatAddHom X) i (P.corootRat i) (P.corootRat_mk_one i),
    Option.map_eq_none_iff]

@[simp]
theorem crystal_e_straight (hlam : lam ∈ dominantChamber P b) (i : b.support) :
    (crystal hlam).e i (straight lam) = none :=
  (forall_crystal_e_eq_none_iff hlam (straight lam)).mpr rfl i

/-- **Every Lakshmibai–Seshadri path of dominant shape `λ` is obtained from `straight λ` by a
lowering word.** -/
theorem exists_fWord_straight_eq_some (hlam : lam ∈ dominantChamber P b)
    (π : LSPath P b lam) :
    ∃ w : List b.support, (crystal hlam).fWord w (straight lam) = some π := by
  have := P.flip_isReduced
  have := finite hlam
  exact (crystal hlam).exists_fWord_eq_some_of_unique_highest
    (fun x hx ↦ (forall_crystal_e_eq_none_iff hlam x).mp hx) π

omit [Finite ι] [P.IsReduced] in
private theorem reachable_of_fWord_eq_some {B : Type*} (c : NormalCrystal P b B)
    {w : List b.support} {x y : B} (h : c.fWord w x = some y) :
    c.graph.Reachable x y := by
  induction w generalizing x with
  | nil =>
    obtain rfl := Option.some.inj (by simpa using h)
    exact .refl _
  | cons i w ih =>
    rw [NormalCrystal.fWord_cons, Option.bind_eq_some_iff] at h
    obtain ⟨z, hxz, hzy⟩ := h
    exact (c.graph_adj_of_f_eq_some hxz).reachable.trans (ih hzy)

/-- **The crystal graph of `LSPath P b λ` is connected** for every dominant weight `λ`. -/
theorem connected_crystal_graph (hlam : lam ∈ dominantChamber P b) :
    (crystal hlam).graph.Connected :=
  (crystal hlam).graph.connected_iff_exists_forall_reachable.mpr ⟨straight lam, fun π ↦
    let ⟨_, hw⟩ := exists_fWord_straight_eq_some hlam π
    reachable_of_fWord_eq_some (crystal hlam) hw⟩

/-- **Littelmann's path-model theorem (lowering-word form).** In every additive realization
`f : X →+ V` over an ordered field `𝕜` with height forms `F` inducing the simple coroots, a
piecewise-linear path `p` is the realization of a Lakshmibai–Seshadri path of dominant shape `λ`
if and only if `p` is obtained from the straight path `PLPath.straight 𝕜 (f λ)` by a lowering word
along the simple roots. -/
theorem mem_range_toPLPath_iff_exists_lowerWord {𝕜 V : Type*} [Field 𝕜] [LinearOrder 𝕜]
    [IsStrictOrderedRing 𝕜] [AddCommGroup V] [Module 𝕜 V]
    (hlam : lam ∈ dominantChamber P b) (f : X →+ V) (F : b.support → Module.Dual 𝕜 V)
    (hF : ∀ i x, F i (f x) = (P.coroot' i x : 𝕜)) {p : PLPath 𝕜 V} :
    (p ∈ Set.range fun π : LSPath P b lam ↦ π.toPLPath 𝕜 f) ↔
      ∃ w : List b.support,
        PLPath.lowerWord F (fun i ↦ f (P.root i)) w (PLPath.straight 𝕜 (f lam)) = some p := by
  constructor
  · rintro ⟨π, rfl⟩
    obtain ⟨w, hw⟩ := exists_fWord_straight_eq_some hlam π
    exact ⟨w, by rw [← toPLPath_straight (P := P) (b := b) 𝕜 f,
      lowerWord_toPLPath hlam f F hF w (straight lam), hw, Option.map_some]⟩
  · rintro ⟨w, hw⟩
    rw [← toPLPath_straight (P := P) (b := b) 𝕜 f] at hw
    exact exists_toPLPath_eq_of_lowerWord_eq_some (straight (P := P) (b := b) lam) hlam f F hF hw

omit [Finite ι] [P.IsReduced] in
private theorem reflTransGen_of_lowerWord_eq_some {𝕜 V : Type*} [Field 𝕜] [LinearOrder 𝕜]
    [IsStrictOrderedRing 𝕜] [AddCommGroup V] [Module 𝕜 V]
    {F : b.support → Module.Dual 𝕜 V} {x : b.support → V} {w : List b.support}
    {q p : PLPath 𝕜 V} (hw : PLPath.lowerWord F x w q = some p) :
    Relation.ReflTransGen
      (fun r s ↦ ∃ i : b.support,
        PLPath.lower (F i) (x i) r = some s ∨ PLPath.raise (F i) (x i) r = some s) q p := by
  induction w generalizing q with
  | nil => obtain rfl := Option.some.inj (by simpa using hw); exact .refl
  | cons i w ih =>
    rw [PLPath.lowerWord_cons, Option.bind_eq_some_iff] at hw
    obtain ⟨r, hqr, hrp⟩ := hw
    exact .head ⟨i, Or.inl hqr⟩ (ih hrp)

/-- **Littelmann's path-model theorem (component form).** In every additive realization `f : X →+ V`
over an ordered field `𝕜` with height forms `F` inducing the simple coroots, the realized
Lakshmibai–Seshadri paths of dominant shape `λ` are precisely the paths reachable from the straight
path `PLPath.straight 𝕜 (f λ)` by arbitrary sequences of simple-root lowering and raising steps. -/
theorem mem_range_toPLPath_iff_reflTransGen {𝕜 V : Type*} [Field 𝕜] [LinearOrder 𝕜]
    [IsStrictOrderedRing 𝕜] [AddCommGroup V] [Module 𝕜 V]
    (hlam : lam ∈ dominantChamber P b) (f : X →+ V) (F : b.support → Module.Dual 𝕜 V)
    (hF : ∀ i x, F i (f x) = (P.coroot' i x : 𝕜)) {p : PLPath 𝕜 V} :
    (p ∈ Set.range fun π : LSPath P b lam ↦ π.toPLPath 𝕜 f) ↔
      Relation.ReflTransGen
        (fun q r ↦ ∃ i : b.support,
          PLPath.lower (F i) (f (P.root i)) q = some r ∨
            PLPath.raise (F i) (f (P.root i)) q = some r)
        (PLPath.straight 𝕜 (f lam)) p :=
  ⟨fun hp ↦ let ⟨_, hw⟩ := (mem_range_toPLPath_iff_exists_lowerWord hlam f F hF).mp hp
    reflTransGen_of_lowerWord_eq_some hw,
    mem_range_toPLPath_of_reflTransGen hlam f F hF ⟨straight lam, toPLPath_straight 𝕜 f⟩⟩

end TauCeti.LSPath
