/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Crystal.Component
public import TauCeti.RepresentationTheory.Crystal.Highest
public import TauCeti.RepresentationTheory.LSPath.Crystal.Basic
public import TauCeti.RepresentationTheory.LSPath.Highest
public import TauCeti.RepresentationTheory.LSPath.Raise
public import TauCeti.RepresentationTheory.LSPath.Realization
public import TauCeti.RepresentationTheory.LSPath.Weight
public import TauCeti.RepresentationTheory.LSPath.Word

import TauCeti.LinearAlgebra.RootSystem.Reduced
import TauCeti.LinearAlgebra.TensorProduct.Tower
import TauCeti.RepresentationTheory.LSPath.LinearMap

/-!
# The normal crystal of Lakshmibai–Seshadri paths

Let `P : RootDatum ι X Y` be a finite reduced root datum with base `b`, and let `λ : X` be a
dominant weight. Littelmann's path model equips the finite type `LSPath P b λ` of
Lakshmibai–Seshadri encodings of shape `λ` with the structure of a connected normal crystal
`TauCeti.LSPath.crystal` with unique highest element `TauCeti.LSPath.straight λ`.

First, `X → ℚ ⊗[ℤ] X` (`TensorProduct.mk ℤ ℚ X 1`) provides a canonical faithful rational
realization (`RootPairing.tensorProduct_mk_injective`) in which no two distinct orbit weights lie on
the same ray (`RootPairing.pairwise_not_sameRay_tensorProduct_mk_orbit`), with rational coroot forms
`Module.Dual.baseChange ℚ (P.coroot' i)`. In every realization `(𝕜, V, f, F)`, the image of
`LSPath.toPLPath` is crystal-admissible (`TauCeti.LSPath.isCrystalSet_range_toPLPath`); transporting
`TauCeti.PLPath.normalCrystalOn` from `ℚ ⊗[ℤ] X` along `LSPath.toPLPath` defines
`TauCeti.LSPath.crystal`, and pushing paths forward from `ℚ ⊗[ℤ] X` via
`TauCeti.PLPath.mapSemilinear` and `AddMonoidHom.liftBaseChangeSemilinear` proves universal
compatibility with `PLPath.raise`, `PLPath.lower`, and `PLPath.minHeight` in **every** additive
realization `(𝕜, V, f, F)`, without requiring `f` to be injective.

Since `TauCeti.LSPath.straight λ` is the unique LS path annihilated by all raising operators
(`TauCeti.LSPath.forall_crystal_e_eq_none_iff`) and `LSPath P b λ` is finite
(`TauCeti.LSPath.finite`), every LS path is obtained from `straight λ` by a lowering word
(`TauCeti.LSPath.exists_fWord_straight_eq_some`), the crystal graph is connected
(`TauCeti.LSPath.connected_crystal_graph`), and the realized LS paths of shape `λ` coincide with
the root-operator component of `PLPath.straight 𝕜 (f λ)`
(`TauCeti.LSPath.mem_range_toPLPath_iff_exists_lowerWord`,
`TauCeti.LSPath.mem_range_toPLPath_iff_reflTransGen`).

## Main definitions and results

* `TauCeti.LSPath.weight`, `TauCeti.LSPath.apply_weight`, `TauCeti.LSPath.weight_eq_iff_endpoint`,
  and `TauCeti.LSPath.crystal`: lattice-valued weight and the normal crystal on `LSPath P b λ`.
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

namespace TauCeti.LSPath

open RootPairing

variable {ι X Y : Type*} [AddCommGroup X] [AddCommGroup Y]
  {P : RootDatum ι X Y} {b : P.Base} [Finite ι] [P.IsReduced] {lam : X}

/-! ### Lattice-valued weight and the normal crystal on `LSPath P b λ` -/

private noncomputable abbrev toRatPLPath (π : LSPath P b lam) : PLPath ℚ (ℚ ⊗[ℤ] X) :=
  π.toPLPath ℚ (TensorProduct.mk ℤ ℚ X 1).toAddMonoidHom

private theorem toRatPLPath_injective (hlam : lam ∈ dominantChamber P b) :
    Function.Injective (toRatPLPath (P := P) (b := b) (lam := lam)) := by
  have := P.finite_weylGroup_of_base b
  exact toPLPath_injective hlam (P.tensorProduct_mk_injective ℚ).injOn
    (P.pairwise_not_sameRay_tensorProduct_mk_orbit ℚ lam)

private theorem mapSemilinear_toRatPLPath {𝕜 V : Type*} [Field 𝕜] [LinearOrder 𝕜]
    [IsStrictOrderedRing 𝕜] [AddCommGroup V] [Module 𝕜 V] (f : X →+ V)
    (π : LSPath P b lam) :
    (toRatPLPath π).mapSemilinear (f.liftBaseChangeSemilinear (Rat.castHom 𝕜)) =
      π.toPLPath 𝕜 f := by
  rw [toRatPLPath, toPLPath_def, toPLPath_def,
    PLPath.mapSemilinear_ofSegments _ _ (Rat.cast_mono (K := 𝕜))]
  congr 1
  simp [timed_def, List.map_ofFn, Function.comp_def, TensorProduct.mk_apply]

omit [Finite ι] [P.IsReduced] in
private theorem apply_liftBaseChangeSemilinear {𝕜 V : Type*} [Field 𝕜] [CharZero 𝕜]
    [AddCommGroup V] [Module 𝕜 V] (f : X →+ V) (i : ι) (F : Module.Dual 𝕜 V)
    (hF : ∀ x : X, F (f x) = (P.coroot' i x : 𝕜)) (u : ℚ ⊗[ℤ] X) :
    F (f.liftBaseChangeSemilinear (Rat.castHom 𝕜) u) =
      Rat.castHom 𝕜 (Module.Dual.baseChange ℚ (P.coroot' i) u) := by
  refine TensorProduct.inductionOn u (fun q x ↦ ?_) (fun _ _ ih₁ ih₂ ↦ by simp [ih₁, ih₂])
  simp [hF, mul_comm]

/-- **The lattice-valued weight of a Lakshmibai–Seshadri path of dominant shape.** Its image in any
realization `(𝕜, V, f)` is the endpoint `(π.toPLPath 𝕜 f).endpoint` (`TauCeti.LSPath.apply_weight`).
-/
noncomputable def weight (hlam : lam ∈ dominantChamber P b) (π : LSPath P b lam) : X :=
  Classical.choose
    (π.existsUnique_endpoint_eq (𝕜 := ℚ) hlam (TensorProduct.mk ℤ ℚ X 1).toAddMonoidHom
      (P.tensorProduct_mk_injective ℚ))

private theorem mkRat_weight (hlam : lam ∈ dominantChamber P b) (π : LSPath P b lam) :
    TensorProduct.mk ℤ ℚ X 1 (π.weight hlam) = (toRatPLPath π).endpoint :=
  (Classical.choose_spec
    (π.existsUnique_endpoint_eq (𝕜 := ℚ) hlam (TensorProduct.mk ℤ ℚ X 1).toAddMonoidHom
      (P.tensorProduct_mk_injective ℚ))).1.symm

/-- In every realization `f : X →+ V` over an ordered field `𝕜`, the image of `π.weight hlam` is
the endpoint of the realized path `π.toPLPath 𝕜 f`. -/
theorem apply_weight (𝕜 : Type*) {V : Type*} [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜]
    [AddCommGroup V] [Module 𝕜 V] (f : X →+ V) (hlam : lam ∈ dominantChamber P b)
    (π : LSPath P b lam) :
    f (π.weight hlam) = (π.toPLPath 𝕜 f).endpoint := by
  have h1 : f.liftBaseChangeSemilinear (Rat.castHom 𝕜) (TensorProduct.mk ℤ ℚ X 1 (π.weight hlam)) =
      f (π.weight hlam) := by
    simp [TensorProduct.mk_apply]
  rw [← h1, mkRat_weight, ← PLPath.endpoint_mapSemilinear, mapSemilinear_toRatPLPath]

/-- The lattice-valued weight of an LS path is characterized by the endpoint of its realized path
in any injective additive realization `f : X →+ V`. -/
theorem weight_eq_iff_endpoint {𝕜 V : Type*} [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜]
    [AddCommGroup V] [Module 𝕜 V] {f : X →+ V} (hf : Function.Injective f)
    (hlam : lam ∈ dominantChamber P b) (π : LSPath P b lam) {μ : X} :
    π.weight hlam = μ ↔ (π.toPLPath 𝕜 f).endpoint = f μ := by
  rw [← apply_weight 𝕜 f hlam π, hf.eq_iff]

@[simp]
theorem weight_straight (hlam : lam ∈ dominantChamber P b) :
    (straight lam).weight hlam = lam :=
  (weight_eq_iff_endpoint (𝕜 := ℚ)
    (f := (TensorProduct.mk ℤ ℚ X 1).toAddMonoidHom)
    (P.tensorProduct_mk_injective ℚ) hlam (straight lam)).mpr
    (by rw [toPLPath_straight, PLPath.endpoint_straight])

theorem weight_congr {lam' : X} (h : lam = lam') (hlam : lam ∈ dominantChamber P b)
    (π : LSPath P b lam) :
    (congr h π).weight (h ▸ hlam) = π.weight hlam := by subst h; simp

/-- The weight of Littelmann's dual path `π^*` is the negative of the weight of `π`. -/
theorem weight_dual (hlam : lam ∈ dominantChamber P b)
    (hlam' : -(longestElement P b • lam) ∈ dominantChamber P b) (π : LSPath P b lam) :
    (dual π).weight hlam' = -π.weight hlam :=
  (weight_eq_iff_endpoint (𝕜 := ℚ)
    (f := (TensorProduct.mk ℤ ℚ X 1).toAddMonoidHom)
    (P.tensorProduct_mk_injective ℚ) hlam' (dual π)).mpr
    (by rw [toPLPath_dual, PLPath.endpoint_reverse, map_neg, apply_weight ℚ])

/-- The weight of an LS path of dominant shape differs from its last orbit weight `τ_l • λ` by an
element of the root lattice `P.rootSpan ℤ`. -/
theorem weight_sub_last_mem_rootSpan (hlam : lam ∈ dominantChamber P b)
    (π : LSPath P b lam) :
    π.weight hlam - (π.dir (Fin.last _)).1 • lam ∈ P.rootSpan ℤ := by
  let f₀ : X →+ (ℚ ⊗[ℤ] X) := (TensorProduct.mk ℤ ℚ X 1).toAddMonoidHom
  obtain ⟨m, hm, heq⟩ := π.exists_mem_rootSpan_endpoint_eq_add (𝕜 := ℚ) hlam f₀
  have hw : π.weight hlam = (π.dir (Fin.last _)).1 • lam + m :=
    (weight_eq_iff_endpoint (𝕜 := ℚ) (f := f₀) (P.tensorProduct_mk_injective ℚ) hlam π).mpr heq
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

private noncomputable abbrev ratCrystalOn (hlam : lam ∈ dominantChamber P b) :
    NormalCrystal P b (Set.range (toRatPLPath (P := P) (b := b) (lam := lam))) :=
  PLPath.normalCrystalOn
    (show Function.Injective (TensorProduct.mk ℤ ℚ X 1).toAddMonoidHom from
      P.tensorProduct_mk_injective ℚ)
    (show ∀ (i : b.support) (x : X),
        (Module.Dual.baseChange ℚ (P.coroot' i) : Module.Dual ℚ (ℚ ⊗[ℤ] X))
          ((TensorProduct.mk ℤ ℚ X 1).toAddMonoidHom x) = (P.coroot' i x : ℚ) from
      fun i x ↦ by simp [TensorProduct.mk_apply])
    (isCrystalSet_range_toPLPath hlam (TensorProduct.mk ℤ ℚ X 1).toAddMonoidHom
      (fun i ↦ Module.Dual.baseChange ℚ (P.coroot' i))
      fun i x ↦ by simp [TensorProduct.mk_apply])

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
      PLPath.raise (Module.Dual.baseChange ℚ (P.coroot' i))
        (TensorProduct.mk ℤ ℚ X 1 (P.root i)) (toRatPLPath π) := by
  rw [crystal, NormalCrystal.transport_e, Equiv.symm_symm, ratCrystalOn, Option.map_map]
  exact ((congrArg (Option.map · _)
    (funext (toRatPLPath_symm_toRatRangeEquiv hlam))).trans
    (PLPath.unattach_normalCrystalOn_e i (toRatRangeEquiv hlam π)))

private theorem map_toRatPLPath_crystal_f (hlam : lam ∈ dominantChamber P b) (i : b.support)
    (π : LSPath P b lam) :
    ((crystal hlam).f i π).map toRatPLPath =
      PLPath.lower (Module.Dual.baseChange ℚ (P.coroot' i))
        (TensorProduct.mk ℤ ℚ X 1 (P.root i)) (toRatPLPath π) := by
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
  have hFG := apply_liftBaseChangeSemilinear (P := P) f i F hF
  have hroot : f (P.root i) =
      f.liftBaseChangeSemilinear (Rat.castHom 𝕜) (TensorProduct.mk ℤ ℚ X 1 (P.root i)) := by
    simp [TensorProduct.mk_apply]
  rw [← mapSemilinear_toRatPLPath f π, hroot,
    PLPath.raise_mapSemilinear _ (Rat.cast_mono (K := 𝕜)) hFG, ← map_toRatPLPath_crystal_e hlam,
    Option.map_map]
  exact congrArg (fun h ↦ Option.map h _) (funext fun ρ ↦ mapSemilinear_toRatPLPath (𝕜 := 𝕜) f ρ)

/-- **Universal compatibility of `crystal.f` with `PLPath.lower`.** In any realization `(𝕜, V, f)`
with a height form `F` inducing the simple coroot pairing `⟨-, αᵢ^∨⟩`, lowering the realized path
`π.toPLPath 𝕜 f` agrees with applying `(crystal hlam).f i` and then realizing. -/
theorem lower_toPLPath (hlam : lam ∈ dominantChamber P b) (f : X →+ V) (i : b.support)
    (F : Module.Dual 𝕜 V) (hF : ∀ x, F (f x) = (P.coroot' i x : 𝕜)) (π : LSPath P b lam) :
    PLPath.lower F (f (P.root i)) (π.toPLPath 𝕜 f) =
      ((crystal hlam).f i π).map (·.toPLPath 𝕜 f) := by
  have hFG := apply_liftBaseChangeSemilinear (P := P) f i F hF
  have hroot : f (P.root i) =
      f.liftBaseChangeSemilinear (Rat.castHom 𝕜) (TensorProduct.mk ℤ ℚ X 1 (P.root i)) := by
    simp [TensorProduct.mk_apply]
  rw [← mapSemilinear_toRatPLPath f π, hroot,
    PLPath.lower_mapSemilinear _ (Rat.cast_mono (K := 𝕜)) hFG, ← map_toRatPLPath_crystal_f hlam,
    Option.map_map]
  exact congrArg (fun h ↦ Option.map h _) (funext fun ρ ↦ mapSemilinear_toRatPLPath (𝕜 := 𝕜) f ρ)

/-- Universal compatibility of `crystal.ε` with `PLPath.minHeight`: in any realization, the
minimum simple-coroot height of `π.toPLPath 𝕜 f` is `-((crystal hlam).ε i π)`. -/
theorem minHeight_toPLPath_eq_neg_crystal_ε (hlam : lam ∈ dominantChamber P b) (f : X →+ V)
    (i : b.support) (F : Module.Dual 𝕜 V) (hF : ∀ x, F (f x) = (P.coroot' i x : 𝕜))
    (π : LSPath P b lam) :
    (π.toPLPath 𝕜 f).minHeight F = -((crystal hlam).ε i π : 𝕜) := by
  have hFG := apply_liftBaseChangeSemilinear (P := P) f i F hF
  have hm : (toRatPLPath π).minHeight (Module.Dual.baseChange ℚ (P.coroot' i)) =
      -((crystal hlam).ε i π : ℚ) := by
    rw [crystal, NormalCrystal.transport_ε, Equiv.symm_symm, ratCrystalOn,
      PLPath.cast_normalCrystalOn_ε, neg_neg]
    rfl
  rw [← mapSemilinear_toRatPLPath f π,
    PLPath.minHeight_mapSemilinear (Rat.cast_mono (K := 𝕜)) hFG, hm]
  simp

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
    (hlam' : -(longestElement P b • lam) ∈ dominantChamber P b := by
      have := P.flip_isReduced
      exact neg_smul_mem_dominantChamber_longestElement hlam) :
    NormalCrystal.StrictIso (crystal hlam).dual (crystal hlam') where
  toEquiv := dual
  wt_toFun π := by simp [weight_dual hlam hlam' π]
  e_toFun i π := by
    let f₀ : X →+ (ℚ ⊗[ℤ] X) := (TensorProduct.mk ℤ ℚ X 1).toAddMonoidHom
    let F₀ : Module.Dual ℚ (ℚ ⊗[ℤ] X) := Module.Dual.baseChange ℚ (P.coroot' i)
    have hF₀ (x : X) : F₀ (f₀ x) = (P.coroot' i x : ℚ) := by simp [f₀, F₀, TensorProduct.mk_apply]
    simp only [Equiv.toFun_as_coe]
    apply Option.map_injective (toRatPLPath_injective hlam')
    rw [← raise_toPLPath hlam' f₀ i F₀ hF₀, toPLPath_dual, PLPath.raise_reverse,
      lower_toPLPath hlam f₀ i F₀ hF₀, NormalCrystal.dual_e, Option.map_map, Option.map_map]
    exact congrArg (fun h ↦ Option.map h _)
      (funext fun ρ : LSPath P b lam ↦ (toPLPath_dual ρ ℚ f₀).symm)

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
  let f₀ : X →+ (ℚ ⊗[ℤ] X) := (TensorProduct.mk ℤ ℚ X 1).toAddMonoidHom
  let F₀ : b.support → Module.Dual ℚ (ℚ ⊗[ℤ] X) :=
    fun i ↦ Module.Dual.baseChange ℚ (P.coroot' i)
  have hF₀ (i : b.support) (x : X) : F₀ i (f₀ x) = (P.coroot' i x : ℚ) := by
    simp [f₀, F₀, TensorProduct.mk_apply]
  rw [← π.forall_raise_eq_none_iff hlam f₀ F₀ hF₀]
  refine forall_congr' fun i ↦ ?_
  rw [raise_toPLPath hlam f₀ i (F₀ i) (hF₀ i), Option.map_eq_none_iff]

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

/-- **The crystal graph of `LSPath P b λ` is connected** for every dominant weight `λ`. -/
theorem connected_crystal_graph (hlam : lam ∈ dominantChamber P b) :
    (crystal hlam).graph.Connected :=
  (crystal hlam).graph.connected_iff_exists_forall_reachable.mpr ⟨straight lam, fun π ↦
    let ⟨_, hw⟩ := exists_fWord_straight_eq_some hlam π
    (crystal hlam).reachable_of_fWord_eq_some hw⟩

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
    rw [← toPLPath_straight (P := P) (b := b) 𝕜 f,
      lowerWord_toPLPath hlam f F hF w (straight lam), Option.map_eq_some_iff] at hw
    obtain ⟨π, _, hπ⟩ := hw
    exact ⟨π, hπ⟩

/-- **Littelmann's path-model theorem (component form).** In every additive realization `f : X →+ V`
over an ordered field `𝕜` with height forms `F` inducing the simple coroots, the realized
Lakshmibai–Seshadri paths of dominant shape `λ` are precisely the paths reachable from the straight
path `PLPath.straight 𝕜 (f λ)` by arbitrary sequences of simple-root lowering and raising steps. -/
theorem mem_range_toPLPath_iff_reflTransGen {𝕜 V : Type*} [Field 𝕜] [LinearOrder 𝕜]
    [IsStrictOrderedRing 𝕜] [AddCommGroup V] [Module 𝕜 V]
    (hlam : lam ∈ dominantChamber P b) (f : X →+ V) (F : b.support → Module.Dual 𝕜 V)
    (hF : ∀ i x, F i (f x) = (P.coroot' i x : 𝕜)) {p : PLPath 𝕜 V} :
    (p ∈ Set.range fun π : LSPath P b lam ↦ π.toPLPath 𝕜 f) ↔
      Relation.ReflTransGen (PLPath.RootStep b f F) (PLPath.straight 𝕜 (f lam)) p :=
  ⟨fun hp ↦ let ⟨_, hw⟩ := (mem_range_toPLPath_iff_exists_lowerWord hlam f F hF).mp hp
    PLPath.reflTransGen_rootStep_of_lowerWord_eq_some hw,
    fun h ↦ (isCrystalSet_range_toPLPath hlam f F hF).mem_of_reflTransGen_rootStep h
      ⟨straight lam, toPLPath_straight 𝕜 f⟩⟩

end TauCeti.LSPath
