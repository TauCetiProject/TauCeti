/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.TensorProduct.Basic
public import TauCeti.RepresentationTheory.Crystal.Component
public import TauCeti.RepresentationTheory.Crystal.Highest
public import TauCeti.RepresentationTheory.LSPath.Highest
public import TauCeti.RepresentationTheory.LSPath.Raise
public import TauCeti.RepresentationTheory.LSPath.Realization
public import TauCeti.RepresentationTheory.LSPath.Weight

import TauCeti.LinearAlgebra.RootSystem.Reduced

/-!
# The normal crystal of Lakshmibai–Seshadri paths

Let `P : RootDatum ι X Y` be a finite reduced root datum with a base `b`, and let `λ : X` be a
dominant weight. Littelmann's path model equips the finite type `LSPath P b λ` of
Lakshmibai–Seshadri encodings of shape `λ` with the structure of a connected normal crystal
`TauCeti.LSPath.crystal` with unique highest element `TauCeti.LSPath.straight λ`.

First, `X → ℚ ⊗[ℤ] X` (`TensorProduct.mk ℤ ℚ X 1`) provides a canonical faithful rational
realization of the character lattice, with no extra hypotheses on `X` or `Y`: the perfect pairing
`P.toLinearMap` separates points of `X`, and finiteness of the Weyl group ensures that no two
distinct orbit weights lie in a common ray (`RootPairing.pairwise_not_sameRay_mk_rat_orbit`). In
this realization:

* each LS path `π` has a unique lattice-valued endpoint `TauCeti.LSPath.weight`, whose image under
  **every** additive realization `f : X →+ V` into a vector space over an ordered field `𝕜` is the
  endpoint `(π.toPLPath 𝕜 f).endpoint`;
* `LSPath.toPLPath` is injective (`TauCeti.LSPath.toPLPath_injective`), and its image is stable
  under all simple-root lowering and raising operators
  (`TauCeti.LSPath.exists_toPLPath_eq_of_lower_eq_some`,
  `TauCeti.LSPath.exists_toPLPath_eq_of_raise_eq_some`), transferring `PLPath.raise` and
  `PLPath.lower` uniquely to partial operators `e i` and `f i` on `LSPath P b λ`;
* the string lengths `ε i` and `φ i` are `-minHeight` and `endpoint - minHeight`, which are natural
  numbers
  (`TauCeti.LSPath.exists_neg_minHeight_eq_natCast_and_apply_endpoint_sub_minHeight_eq_natCast`),
  satisfying all axioms of `TauCeti.NormalCrystal`.

By extending any additive map `f : X →+ V` across `ℚ ⊗[ℤ] X`, the crystal operators `e i` and `f i`
intertwine `PLPath.raise` and `PLPath.lower` in **every** realization `(𝕜, V, f, F)` whose forms `F`
agree with the simple coroots on `X` (`TauCeti.LSPath.raise_toPLPath`,
`TauCeti.LSPath.lower_toPLPath`), without requiring `f` to be injective.

Since `TauCeti.LSPath.straight λ` is the unique LS path annihilated by all raising operators
(`TauCeti.LSPath.forall_crystal_e_eq_none_iff`) and `LSPath P b λ` is finite
(`TauCeti.LSPath.finite`), every LS path is obtained from `straight λ` by a lowering word
(`TauCeti.LSPath.exists_fWord_straight_eq_some`), the crystal graph is connected
(`TauCeti.LSPath.connected_crystal_graph`), and in every realization `(𝕜, V, f, F)` the realized LS
paths of shape `λ` are precisely the paths generated from `PLPath.straight 𝕜 (f λ)` by Littelmann's
root operators (`TauCeti.LSPath.mem_range_toPLPath_iff_exists_lowerWord`,
`TauCeti.LSPath.mem_range_toPLPath_iff_reflTransGen`).

## Main definitions

* `RootPairing.corootRat`: the rational linear form on `ℚ ⊗[ℤ] X` induced by the `i`-th coroot.
* `TauCeti.LSPath.weight`: the lattice-valued weight `X` of an LS path of dominant shape.
* `TauCeti.LSPath.crystal`: the normal crystal structure on `LSPath P b λ` for dominant `λ`.
* `TauCeti.LSPath.congrIso`: strict crystal isomorphism along an equality of shapes `λ = λ'`.
* `TauCeti.LSPath.dualIso`: strict crystal isomorphism `(crystal hlam).dual ≃ crystal hlam'`
  induced by Littelmann's path duality `TauCeti.LSPath.dual`.

## Main results

* `TauCeti.LSPath.apply_weight`: `f (π.weight hlam) = (π.toPLPath 𝕜 f).endpoint` in any realization.
* `TauCeti.LSPath.raise_toPLPath` and `TauCeti.LSPath.lower_toPLPath`: universal intertwining of
  the crystal operators with `PLPath.raise` and `PLPath.lower` in any realization.
* `TauCeti.LSPath.forall_crystal_e_eq_none_iff`: `straight λ` is the unique highest element.
* `TauCeti.LSPath.exists_fWord_straight_eq_some` and `TauCeti.LSPath.connected_crystal_graph`:
  generation from `straight λ` by lowering words and connectedness of the crystal graph.
* `TauCeti.LSPath.mem_range_toPLPath_iff_exists_lowerWord` and
  `TauCeti.LSPath.mem_range_toPLPath_iff_reflTransGen`: **the realized LS paths of dominant shape
  `λ` coincide with the root-operator component of the straight path `t ↦ t • f λ`.**

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
      (fun q₁ q₂ ↦ by ext x; simp [Rat.cast_add, add_smul]))
    (fun z q x ↦ by
      simp only [zsmul_eq_mul, AddMonoidHom.mk'_apply, Rat.cast_mul, Rat.cast_intCast, map_zsmul]
      rw [mul_smul, Int.cast_smul_eq_zsmul])

private theorem liftRatAddHom_tmul (𝕜 : Type*) {V : Type*} [Field 𝕜] [CharZero 𝕜] [AddCommGroup V]
    [Module 𝕜 V] (f : X →+ V) (q : ℚ) (x : X) :
    liftRatAddHom 𝕜 f (q ⊗ₜ[ℤ] x) = (q : 𝕜) • f x :=
  (rfl)

private theorem liftRatAddHom_smul (𝕜 : Type*) {V : Type*} [Field 𝕜] [CharZero 𝕜] [AddCommGroup V]
    [Module 𝕜 V] (f : X →+ V) (c : ℚ) (u : ℚ ⊗[ℤ] X) :
    liftRatAddHom 𝕜 f (c • u) = (c : 𝕜) • liftRatAddHom 𝕜 f u := by
  refine TensorProduct.inductionOn u (fun q x ↦ ?_) (fun u₁ u₂ ih₁ ih₂ ↦ ?_)
  · rw [TensorProduct.smul_tmul', smul_eq_mul, liftRatAddHom_tmul, liftRatAddHom_tmul,
      Rat.cast_mul, mul_smul]
  · rw [smul_add, map_add, ih₁, ih₂, map_add, smul_add]

/-- The rational linear form on `ℚ ⊗[ℤ] X` induced by pairing with `y : Y`. -/
private def pairRat (y : Y) : Module.Dual ℚ (ℚ ⊗[ℤ] X) where
  toAddHom :=
    (liftRatAddHom ℚ
      (AddMonoidHom.mk' (fun x : X ↦ (P.toLinearMap x y : ℚ))
        (fun x₁ x₂ ↦ by simp))).toAddHom
  map_smul' c u := by
    simpa using liftRatAddHom_smul ℚ
      (AddMonoidHom.mk' (fun x : X ↦ (P.toLinearMap x y : ℚ)) (fun x₁ x₂ ↦ by simp)) c u

private theorem pairRat_tmul (y : Y) (q : ℚ) (x : X) :
    P.pairRat y (q ⊗ₜ[ℤ] x) = q * (P.toLinearMap x y : ℚ) := by
  change liftRatAddHom ℚ _ (q ⊗ₜ[ℤ] x) = _
  simp [liftRatAddHom_tmul]

/-- The rational linear form on `ℚ ⊗[ℤ] X` induced by the `i`-th coroot `P.coroot i`. -/
def corootRat (i : ι) : Module.Dual ℚ (ℚ ⊗[ℤ] X) :=
  P.pairRat (P.coroot i)

@[simp]
theorem corootRat_tmul (i : ι) (q : ℚ) (x : X) :
    P.corootRat i (q ⊗ₜ[ℤ] x) = q * (P.coroot' i x : ℚ) :=
  P.pairRat_tmul (P.coroot i) q x

theorem corootRat_mk_one (i : ι) (x : X) :
    P.corootRat i (TensorProduct.mk ℤ ℚ X 1 x) = (P.coroot' i x : ℚ) := by
  simp [TensorProduct.mk_apply]

include P in
/-- For a root datum `P : RootDatum ι X Y`, the canonical inclusion `x ↦ 1 ⊗ₜ x` of `X` into
`ℚ ⊗[ℤ] X` is injective, as the perfect pairing with `Y` separates points. -/
theorem injective_mk_rat : Function.Injective (TensorProduct.mk ℤ ℚ X (1 : ℚ)) := by
  intro x₁ x₂ h
  apply (LinearMap.IsPerfPair.bijective_left P.toLinearMap).injective
  ext y
  have hy := congrArg (P.pairRat y) h
  simpa [TensorProduct.mk_apply, pairRat_tmul] using hy

private noncomputable def mkWeyl (w : P.weylGroup) : X →+ (ℚ ⊗[ℤ] X) :=
  AddMonoidHom.mk' (fun x ↦ (1 : ℚ) ⊗ₜ[ℤ] (w • x))
    (fun x₁ x₂ ↦ by simp [smul_add, TensorProduct.tmul_add])

private noncomputable instance : SMul P.weylGroup (ℚ ⊗[ℤ] X) where
  smul w u := liftRatAddHom ℚ (P.mkWeyl w) u

@[simp]
private theorem weylGroup_smul_tmul (w : P.weylGroup) (q : ℚ) (x : X) :
    w • (q ⊗ₜ[ℤ] x) = q ⊗ₜ[ℤ] (w • x) := by
  change liftRatAddHom ℚ (P.mkWeyl w) (q ⊗ₜ[ℤ] x) = _
  rw [liftRatAddHom_tmul, mkWeyl, AddMonoidHom.mk'_apply, Rat.cast_id, TensorProduct.smul_tmul',
    smul_eq_mul, mul_one]

private theorem weylGroup_smul_add (w : P.weylGroup) (u₁ u₂ : ℚ ⊗[ℤ] X) :
    w • (u₁ + u₂) = w • u₁ + w • u₂ :=
  (liftRatAddHom ℚ (P.mkWeyl w)).map_add u₁ u₂

private noncomputable instance : MulAction P.weylGroup (ℚ ⊗[ℤ] X) where
  one_smul u := by
    refine TensorProduct.inductionOn u (fun q x ↦ ?_) (fun u₁ u₂ ih₁ ih₂ ↦ ?_)
    · rw [P.weylGroup_smul_tmul, one_smul]
    · rw [P.weylGroup_smul_add, ih₁, ih₂]
  mul_smul w₁ w₂ u := by
    refine TensorProduct.inductionOn u (fun q x ↦ ?_) (fun u₁ u₂ ih₁ ih₂ ↦ ?_)
    · rw [P.weylGroup_smul_tmul, P.weylGroup_smul_tmul, P.weylGroup_smul_tmul, mul_smul]
    · rw [P.weylGroup_smul_add, P.weylGroup_smul_add, P.weylGroup_smul_add, ih₁, ih₂]

private instance : SMulCommClass P.weylGroup ℚ (ℚ ⊗[ℤ] X) :=
  ⟨fun w c u ↦ liftRatAddHom_smul ℚ (P.mkWeyl w) c u⟩

/-- No two distinct vectors in the realized Weyl orbit of `λ` in `ℚ ⊗[ℤ] X` lie on the same
rational ray. -/
theorem pairwise_not_sameRay_mk_rat_orbit (b : P.Base) [Finite ι] [P.IsReduced] (lam : X) :
    (Set.range fun w : P.weylGroup ↦ TensorProduct.mk ℤ ℚ X (1 : ℚ) (w • lam)).Pairwise
      fun u v ↦ ¬ SameRay ℚ u v := by
  have := P.finite_weylGroup_of_base b
  have horbit :
      (Set.range fun w : P.weylGroup ↦ TensorProduct.mk ℤ ℚ X (1 : ℚ) (w • lam)) =
        MulAction.orbit P.weylGroup (TensorProduct.mk ℤ ℚ X (1 : ℚ) lam) := by
    ext u
    simp only [Set.mem_range, MulAction.mem_orbit_iff, TensorProduct.mk_apply,
      P.weylGroup_smul_tmul]
  rw [horbit]
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

private theorem liftRat_tmul (f : X →+ V) (q : ℚ) (x : X) :
    liftRat 𝕜 f (q ⊗ₜ[ℤ] x) = (q : 𝕜) • f x :=
  (rfl)

private theorem liftRat_smul (f : X →+ V) (c : ℚ) (u : ℚ ⊗[ℤ] X) :
    liftRat 𝕜 f (c • u) = (c : 𝕜) • liftRat 𝕜 f u :=
  RootPairing.liftRatAddHom_smul 𝕜 f c u

private theorem apply_liftRat (f : X →+ V) (F : Module.Dual 𝕜 V)
    (g : Module.Dual ℚ (ℚ ⊗[ℤ] X))
    (hF : ∀ x : X, F (f x) = (g (1 ⊗ₜ[ℤ] x) : 𝕜)) (u : ℚ ⊗[ℤ] X) :
    F (liftRat 𝕜 f u) = (g u : 𝕜) := by
  refine TensorProduct.inductionOn u (fun q x ↦ ?_) (fun u₁ u₂ ih₁ ih₂ ↦ ?_)
  · rw [liftRat_tmul, map_smul, smul_eq_mul, hF x, ← Rat.cast_mul, ← smul_eq_mul, ← map_smul,
      TensorProduct.smul_tmul', smul_eq_mul, mul_one]
  · simp [ih₁, ih₂]

private theorem sameRay_liftRat (f : X →+ V) {u₁ u₂ : ℚ ⊗[ℤ] X} (h : SameRay ℚ u₁ u₂) :
    SameRay 𝕜 (liftRat 𝕜 f u₁) (liftRat 𝕜 f u₂) := by
  rcases h with rfl | rfl | ⟨r₁, r₂, hr₁, hr₂, heq⟩
  · simp [SameRay.zero_left]
  · simp [SameRay.zero_right]
  · have hu : u₁ = (r₁⁻¹ * r₂) • u₂ := by
      rw [mul_smul, ← heq, inv_smul_smul₀ hr₁.ne']
    rw [hu, liftRat_smul]
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

private theorem ofSegments_map_liftRat_normalize (f : X →+ V) (l : List (ℚ ⊗[ℤ] X)) :
    PLPath.ofSegments 𝕜 ((PLPath.normalize ℚ l).map (liftRat 𝕜 f)) =
      PLPath.ofSegments 𝕜 (l.map (liftRat 𝕜 f)) := by
  apply PLPath.ofSegments_eq_ofSegments_iff.mpr
  exact (Relation.EqvGen.reflTransGen_le_eqvGen _ _ _
    ((PLPath.reflTransGen_move_normalize l).lift _ fun _ _ h ↦ move_map_liftRat 𝕜 f h)).symm _ _

private noncomputable def mapRat (f : X →+ V) (p : PLPath ℚ (ℚ ⊗[ℤ] X)) : PLPath 𝕜 V :=
  PLPath.ofSegments 𝕜 (p.segments.map (liftRat 𝕜 f))

private theorem mapRat_ofSegments (f : X →+ V) (l : List (ℚ ⊗[ℤ] X)) :
    mapRat 𝕜 f (PLPath.ofSegments ℚ l) = PLPath.ofSegments 𝕜 (l.map (liftRat 𝕜 f)) := by
  simp only [mapRat, PLPath.segments_ofSegments, ofSegments_map_liftRat_normalize]

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
    have hm := listMinHeight_map_liftRat 𝕜 f hFG l
    have hmin :
        min (F (liftRat 𝕜 f v) + PLPath.listMinHeight F (l.map (liftRat 𝕜 f))) (c : 𝕜) =
          (min (g v + PLPath.listMinHeight g l) c : ℚ) := by
      rw [hFG v, hm, ← Rat.cast_add, (Rat.cast_mono (K := 𝕜)).map_min]
    by_cases h : 0 < min (g v + PLPath.listMinHeight g l) c
    · have h' :
          0 < min (F (liftRat 𝕜 f v) + PLPath.listMinHeight F (l.map (liftRat 𝕜 f))) (c : 𝕜) := by
        rw [hmin]
        exact Rat.cast_pos.mpr h
      rw [List.map_cons, PLPath.reflectRecords_cons_of_pos h',
        PLPath.reflectRecords_cons_of_pos h, List.map_cons, List.map_cons, hmin]
      have hc : (c : 𝕜) - F (liftRat 𝕜 f v) = ((c - g v : ℚ) : 𝕜) := by simp [hFG v]
      rw [hc, ih (c - g v)]
      congr 1
      · simp [Module.preReflection_apply, map_sub, liftRat_smul, hFG]
      · congr 1
        rw [hFG v, ← Rat.cast_div, ← Rat.cast_one, ← Rat.cast_sub, liftRat_smul]
    · have h' :
          min (F (liftRat 𝕜 f v) + PLPath.listMinHeight F (l.map (liftRat 𝕜 f))) (c : 𝕜) ≤ 0 := by
        rw [hmin]
        exact Rat.cast_nonpos.mpr (le_of_not_gt h)
      rw [List.map_cons, PLPath.reflectRecords_cons_of_nonpos h',
        PLPath.reflectRecords_cons_of_nonpos (le_of_not_gt h)]
      simp [hFG v, ← Rat.cast_sub, ih (c - g v)]

private theorem listLower_map_liftRat (f : X →+ V) {F : Module.Dual 𝕜 V}
    {g : Module.Dual ℚ (ℚ ⊗[ℤ] X)} (hFG : ∀ u, F (liftRat 𝕜 f u) = (g u : 𝕜))
    (x : ℚ ⊗[ℤ] X) (l : List (ℚ ⊗[ℤ] X)) :
    PLPath.listLower F (liftRat 𝕜 f x) (l.map (liftRat 𝕜 f)) =
      (PLPath.listLower g x l).map (List.map (liftRat 𝕜 f)) := by
  have hsum : F (l.map (liftRat 𝕜 f)).sum = (g l.sum : 𝕜) := by
    rw [← map_list_sum, hFG]
  have hm := listMinHeight_map_liftRat 𝕜 f hFG l
  have hcond :
      (1 : 𝕜) ≤ F (l.map (liftRat 𝕜 f)).sum - PLPath.listMinHeight F (l.map (liftRat 𝕜 f)) ↔
        1 ≤ g l.sum - PLPath.listMinHeight g l := by
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
  congr 1
  funext m
  exact (mapRat_ofSegments 𝕜 f m).symm

private theorem raise_mapRat (f : X →+ V) {F : Module.Dual 𝕜 V}
    {g : Module.Dual ℚ (ℚ ⊗[ℤ] X)} (hFG : ∀ u, F (liftRat 𝕜 f u) = (g u : 𝕜))
    (x : ℚ ⊗[ℤ] X) (p : PLPath ℚ (ℚ ⊗[ℤ] X)) :
    PLPath.raise F (liftRat 𝕜 f x) (mapRat 𝕜 f p) =
      (PLPath.raise g x p).map (mapRat 𝕜 f) := by
  simp only [PLPath.raise_def, ← mapRat_reverse, lower_mapRat 𝕜 f hFG, Option.map_map]
  congr 1
  funext q
  exact (mapRat_reverse 𝕜 f q).symm

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
  simp [timed_def, List.map_ofFn, Function.comp_def, liftRat_smul, mkRatAddHom, liftRat_tmul]

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
    simp [mkRatAddHom, liftRat_tmul]
  rw [← h1, mkRat_weight, ← endpoint_mapRat, mapRat_toRatPLPath]

@[simp]
theorem weight_straight (hlam : lam ∈ dominantChamber P b) :
    (straight lam).weight hlam = lam := by
  apply P.injective_mk_rat
  simpa [mkRatAddHom] using apply_weight ℚ (mkRatAddHom X) hlam (straight lam)

theorem weight_congr {lam' : X} (h : lam = lam') (hlam : lam ∈ dominantChamber P b)
    (π : LSPath P b lam) :
    (congr h π).weight (h ▸ hlam) = π.weight hlam := by
  subst h; simp

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
    P.injective_mk_rat (by
      change mkRatAddHom X _ = mkRatAddHom X _
      rw [apply_weight ℚ, heq])
  simpa [hw] using hm

section CrystalConstruction

private noncomputable def crystalE (hlam : lam ∈ dominantChamber P b) (i : b.support)
    (π : LSPath P b lam) : Option (LSPath P b lam) :=
  open Classical in
  if h : (PLPath.raise (P.corootRat i) (mkRatAddHom X (P.root i)) (toRatPLPath π)).isSome then
    some (Classical.choose (exists_toPLPath_eq_of_raise_eq_some π hlam (mkRatAddHom X) i
      (P.corootRat i) (P.corootRat_mk_one i) (Option.eq_some_of_isSome h)))
  else none

private theorem map_toRatPLPath_crystalE (hlam : lam ∈ dominantChamber P b) (i : b.support)
    (π : LSPath P b lam) :
    (crystalE hlam i π).map toRatPLPath =
      PLPath.raise (P.corootRat i) (mkRatAddHom X (P.root i)) (toRatPLPath π) := by
  classical
  rw [crystalE]
  split_ifs with h
  · rw [Option.map_some]
    exact (congrArg some (Classical.choose_spec
      (exists_toPLPath_eq_of_raise_eq_some π hlam (mkRatAddHom X) i (P.corootRat i)
        (P.corootRat_mk_one i) (Option.eq_some_of_isSome h)))).trans
      (Option.eq_some_of_isSome h).symm
  · rw [Option.map_none]
    exact (Option.not_isSome_iff_eq_none.mp h).symm

private noncomputable def crystalF (hlam : lam ∈ dominantChamber P b) (i : b.support)
    (π : LSPath P b lam) : Option (LSPath P b lam) :=
  open Classical in
  have := P.flip_isReduced
  if h : (PLPath.lower (P.corootRat i) (mkRatAddHom X (P.root i)) (toRatPLPath π)).isSome then
    some (Classical.choose (exists_toPLPath_eq_of_lower_eq_some π hlam (mkRatAddHom X) i
      (P.corootRat i) (P.corootRat_mk_one i) (Option.eq_some_of_isSome h)))
  else none

private theorem map_toRatPLPath_crystalF (hlam : lam ∈ dominantChamber P b) (i : b.support)
    (π : LSPath P b lam) :
    (crystalF hlam i π).map toRatPLPath =
      PLPath.lower (P.corootRat i) (mkRatAddHom X (P.root i)) (toRatPLPath π) := by
  classical
  have := P.flip_isReduced
  rw [crystalF]
  split_ifs with h
  · rw [Option.map_some]
    exact (congrArg some (Classical.choose_spec
      (exists_toPLPath_eq_of_lower_eq_some π hlam (mkRatAddHom X) i (P.corootRat i)
        (P.corootRat_mk_one i) (Option.eq_some_of_isSome h)))).trans
      (Option.eq_some_of_isSome h).symm
  · rw [Option.map_none]
    exact (Option.not_isSome_iff_eq_none.mp h).symm

private theorem exists_eps_phi (hlam : lam ∈ dominantChamber P b) (i : b.support)
    (π : LSPath P b lam) :
    ∃ e p : ℕ, -(toRatPLPath π).minHeight (P.corootRat i) = e ∧
      P.corootRat i (toRatPLPath π).endpoint - (toRatPLPath π).minHeight (P.corootRat i) = p := by
  have := P.flip_isReduced
  exact π.exists_neg_minHeight_eq_natCast_and_apply_endpoint_sub_minHeight_eq_natCast
    (𝕜 := ℚ) hlam (mkRatAddHom X) i (P.corootRat i) (P.corootRat_mk_one i)

private noncomputable def crystalEps (hlam : lam ∈ dominantChamber P b) (i : b.support)
    (π : LSPath P b lam) : ℕ :=
  (exists_eps_phi hlam i π).choose

private theorem natCast_crystalEps (hlam : lam ∈ dominantChamber P b) (i : b.support)
    (π : LSPath P b lam) :
    (crystalEps hlam i π : ℚ) = -(toRatPLPath π).minHeight (P.corootRat i) :=
  (exists_eps_phi hlam i π).choose_spec.choose_spec.1.symm

private noncomputable def crystalPhi (hlam : lam ∈ dominantChamber P b) (i : b.support)
    (π : LSPath P b lam) : ℕ :=
  (exists_eps_phi hlam i π).choose_spec.choose

private theorem natCast_crystalPhi (hlam : lam ∈ dominantChamber P b) (i : b.support)
    (π : LSPath P b lam) :
    (crystalPhi hlam i π : ℚ) =
      P.corootRat i (toRatPLPath π).endpoint - (toRatPLPath π).minHeight (P.corootRat i) :=
  (exists_eps_phi hlam i π).choose_spec.choose_spec.2.symm

/-- **The normal crystal of Lakshmibai–Seshadri paths of dominant shape `λ`.** Its weight map is
`TauCeti.LSPath.weight`, and its raising and lowering operators realize Littelmann's path root
operators in every additive realization of `X` (`TauCeti.LSPath.raise_toPLPath`,
`TauCeti.LSPath.lower_toPLPath`). -/
noncomputable def crystal (hlam : lam ∈ dominantChamber P b) :
    NormalCrystal P b (LSPath P b lam) where
  wt := weight hlam
  e := crystalE hlam
  f := crystalF hlam
  ε := crystalEps hlam
  φ := crystalPhi hlam
  f_eq_some_iff {i x y} := by
    have hinj := Option.map_injective (toRatPLPath_injective hlam)
    have htwo : P.corootRat i (mkRatAddHom X (P.root i)) = 2 := by
      simp [mkRatAddHom, P.root_coroot'_eq_pairing]
    rw [← hinj.eq_iff, Option.map_some, map_toRatPLPath_crystalF,
      PLPath.lower_eq_some_iff htwo, ← map_toRatPLPath_crystalE, ← Option.map_some, hinj.eq_iff]
  wt_of_e_eq_some {i x y} he := by
    have hr :
        PLPath.raise (P.corootRat i) (mkRatAddHom X (P.root i)) (toRatPLPath x) =
          some (toRatPLPath y) := by
      rw [← map_toRatPLPath_crystalE hlam, he, Option.map_some]
    apply P.injective_mk_rat
    change mkRatAddHom X _ = mkRatAddHom X _
    rw [map_add, mkRat_weight, mkRat_weight, PLPath.endpoint_of_raise_eq_some hr]
  ε_eq_zero_iff {i x} := by
    have hnone :
        crystalE hlam i x = none ↔
          PLPath.raise (P.corootRat i) (mkRatAddHom X (P.root i)) (toRatPLPath x) = none := by
      rw [← map_toRatPLPath_crystalE hlam, Option.map_eq_none_iff]
    rw [hnone, PLPath.raise_eq_none_iff]
    have hmin : (toRatPLPath x).minHeight (P.corootRat i) = -(crystalEps hlam i x : ℚ) := by
      linarith [natCast_crystalEps hlam i x]
    rw [hmin]
    constructor
    · intro h0
      simp [h0]
    · intro hlt
      have h1 : (crystalEps hlam i x : ℚ) < 1 := by linarith
      have h1' : crystalEps hlam i x < 1 := by exact_mod_cast h1
      omega
  ε_of_e_eq_some {i x y} he := by
    have hr :
        PLPath.raise (P.corootRat i) (mkRatAddHom X (P.root i)) (toRatPLPath x) =
          some (toRatPLPath y) := by
      rw [← map_toRatPLPath_crystalE hlam, he, Option.map_some]
    have htwo : P.corootRat i (mkRatAddHom X (P.root i)) = 2 := by
      simp [mkRatAddHom, P.root_coroot'_eq_pairing]
    have hm := PLPath.minHeight_of_raise_eq_some htwo hr
    have hq : ((crystalEps hlam i y + 1 : ℕ) : ℚ) = (crystalEps hlam i x : ℚ) := by
      push_cast
      linarith [natCast_crystalEps hlam i x, natCast_crystalEps hlam i y, hm]
    exact_mod_cast hq
  φ_eq_zero_iff {i x} := by
    have hnone :
        crystalF hlam i x = none ↔
          PLPath.lower (P.corootRat i) (mkRatAddHom X (P.root i)) (toRatPLPath x) = none := by
      rw [← map_toRatPLPath_crystalF hlam, Option.map_eq_none_iff]
    rw [hnone, PLPath.lower_eq_none_iff, ← natCast_crystalPhi hlam i x]
    constructor
    · intro h0
      simp [h0]
    · intro hlt
      have h1 : crystalPhi hlam i x < 1 := by exact_mod_cast hlt
      omega
  φ_sub_ε i x := by
    have hq :
        (((crystalPhi hlam i x : ℤ) - crystalEps hlam i x : ℤ) : ℚ) =
          (P.toLinearMap (x.weight hlam) (P.coroot i) : ℚ) := by
      push_cast
      rw [natCast_crystalPhi, natCast_crystalEps, ← mkRat_weight hlam]
      have hcor : P.corootRat i (mkRatAddHom X (x.weight hlam)) =
          (P.toLinearMap (x.weight hlam) (P.coroot i) : ℚ) := by
        simp [mkRatAddHom, RootPairing.coroot']
      rw [hcor]
      ring
    exact_mod_cast hq

end CrystalConstruction

/-! ### Universal compatibility with realizations -/

section Realization

@[simp]
theorem crystal_wt (hlam : lam ∈ dominantChamber P b) (π : LSPath P b lam) :
    (crystal hlam).wt π = π.weight hlam :=
  (rfl)

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
    simp [mkRatAddHom, liftRat_tmul]
  rw [← mapRat_toRatPLPath f π, hroot, raise_mapRat 𝕜 f hFG]
  change (PLPath.raise _ _ (toRatPLPath π)).map (mapRat 𝕜 f) =
    (crystalE hlam i π).map (·.toPLPath 𝕜 f)
  rw [← map_toRatPLPath_crystalE hlam, Option.map_map]
  congr 1
  funext ρ
  exact mapRat_toRatPLPath f ρ

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
    simp [mkRatAddHom, liftRat_tmul]
  rw [← mapRat_toRatPLPath f π, hroot, lower_mapRat 𝕜 f hFG]
  change (PLPath.lower _ _ (toRatPLPath π)).map (mapRat 𝕜 f) =
    (crystalF hlam i π).map (·.toPLPath 𝕜 f)
  rw [← map_toRatPLPath_crystalF hlam, Option.map_map]
  congr 1
  funext ρ
  exact mapRat_toRatPLPath f ρ

/-- Universal compatibility of `crystal.ε` with `PLPath.minHeight`: in any realization, the
minimum simple-coroot height of `π.toPLPath 𝕜 f` is `-((crystal hlam).ε i π)`. -/
theorem minHeight_toPLPath_eq_neg_crystal_ε (hlam : lam ∈ dominantChamber P b) (f : X →+ V)
    (i : b.support) (F : Module.Dual 𝕜 V) (hF : ∀ x, F (f x) = (P.coroot' i x : 𝕜))
    (π : LSPath P b lam) :
    (π.toPLPath 𝕜 f).minHeight F = -((crystal hlam).ε i π : 𝕜) := by
  have hFG : ∀ u, F (liftRat 𝕜 f u) = (P.corootRat i u : 𝕜) :=
    apply_liftRat 𝕜 f F (P.corootRat i) fun x ↦ by simp [hF]
  have hm : (toRatPLPath π).minHeight (P.corootRat i) = -(crystalEps hlam i π : ℚ) := by
    linarith [natCast_crystalEps hlam i π]
  rw [← mapRat_toRatPLPath f π, minHeight_mapRat 𝕜 f hFG, hm, Rat.cast_neg, Rat.cast_natCast]
  rfl

/-- Universal compatibility of `crystal.φ` with `PLPath.minHeight`: in any realization,
`F (π.toPLPath 𝕜 f).endpoint - (π.toPLPath 𝕜 f).minHeight F = (crystal hlam).φ i π`. -/
theorem apply_endpoint_sub_minHeight_toPLPath_eq_crystal_φ
    (hlam : lam ∈ dominantChamber P b) (f : X →+ V) (i : b.support) (F : Module.Dual 𝕜 V)
    (hF : ∀ x, F (f x) = (P.coroot' i x : 𝕜)) (π : LSPath P b lam) :
    F (π.toPLPath 𝕜 f).endpoint - (π.toPLPath 𝕜 f).minHeight F =
      ((crystal hlam).φ i π : 𝕜) := by
  rw [← apply_weight 𝕜 f hlam, hF, minHeight_toPLPath_eq_neg_crystal_ε hlam f i F hF]
  have hsub := (crystal hlam).φ_sub_ε i π
  have hcast :
      (((crystal hlam).φ i π : 𝕜) - ((crystal hlam).ε i π : 𝕜)) =
        (P.coroot' i (π.weight hlam) : 𝕜) := by
    exact_mod_cast hsub
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
    congrIso (rfl : lam = lam) hlam = NormalCrystal.StrictIso.refl (crystal hlam) := by
  apply NormalCrystal.StrictIso.ext
  intro π
  simp

@[simp]
theorem congrIso_symm {lam' : X} (h : lam = lam') (hlam : lam ∈ dominantChamber P b) :
    (congrIso h hlam).symm = congrIso h.symm (h ▸ hlam) := by
  subst h
  apply NormalCrystal.StrictIso.ext
  intro π
  simpa using (NormalCrystal.StrictIso.refl (crystal hlam)).symm_apply_apply π

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
    congr 1
    funext ρ
    exact (ρ.toPLPath_dual ℚ (mkRatAddHom X)).symm

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
    rw [NormalCrystal.fWord_nil] at h
    obtain rfl := Option.some.inj h
    exact SimpleGraph.Reachable.refl _
  | cons i w ih =>
    rw [NormalCrystal.fWord_cons] at h
    obtain ⟨z, hxz, hzy⟩ := Option.bind_eq_some_iff.mp h
    exact (c.graph_adj_of_f_eq_some hxz).reachable.trans (ih hzy)

/-- **The crystal graph of `LSPath P b λ` is connected** for every dominant weight `λ`. -/
theorem connected_crystal_graph (hlam : lam ∈ dominantChamber P b) :
    (crystal hlam).graph.Connected := by
  rw [SimpleGraph.connected_iff_exists_forall_reachable]
  exact ⟨straight lam, fun π ↦
    let ⟨w, hw⟩ := exists_fWord_straight_eq_some hlam π
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
    refine ⟨w, ?_⟩
    rw [← toPLPath_straight (P := P) (b := b) 𝕜 f,
      lowerWord_toPLPath hlam f F hF w (straight lam), hw, Option.map_some]
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
  | nil =>
    rw [PLPath.lowerWord_nil] at hw
    obtain rfl := Option.some.inj hw
    exact .refl
  | cons i w ih =>
    rw [PLPath.lowerWord_cons] at hw
    obtain ⟨r, hqr, hrp⟩ := Option.bind_eq_some_iff.mp hw
    exact Relation.ReflTransGen.head ⟨i, Or.inl hqr⟩ (ih hrp)

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
        (PLPath.straight 𝕜 (f lam)) p := by
  constructor
  · intro hp
    obtain ⟨w, hw⟩ := (mem_range_toPLPath_iff_exists_lowerWord hlam f F hF).mp hp
    exact reflTransGen_of_lowerWord_eq_some hw
  · exact mem_range_toPLPath_of_reflTransGen hlam f F hF ⟨straight lam, toPLPath_straight 𝕜 f⟩

end TauCeti.LSPath
