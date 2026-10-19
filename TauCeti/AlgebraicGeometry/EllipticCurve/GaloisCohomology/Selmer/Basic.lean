/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.EllipticCurve.GaloisCohomology.Restriction
public import TauCeti.RepresentationTheory.Homological.ContCohomology.SelmerStructure

/-!
# The `m`-Selmer group and the Shafarevich–Tate group of an elliptic curve

Let `W` be an elliptic curve over a field `K`, with Galois cohomology taken in the discrete
`G_K`-modules `E(Kˢ)` and `E(Kˢ)[m]`. Fix a family `(L i)` of field extensions of `K`, each with a
`K`-embedding `τ i : Kˢ →ₐ[K] (L i)ˢ` of separable closures. Restriction along `τ i`
(`WeierstrassCurve.pointRes`) is the localisation map to `L i`, and Silverman's definitions read
(X.4):

```text
Sha = ker (H¹(G_K, E(Kˢ)) → ∏ᵢ H¹(G_{L i}, E((L i)ˢ))),
Sel_m = ker (H¹(G_K, E(Kˢ)[m]) → ∏ᵢ H¹(G_{L i}, E((L i)ˢ))).
```

For a number field `K` and the family of its completions at all places, these are the
Shafarevich–Tate group `Sha(E/K)` and the `m`-Selmer group `Sel_m(E/K)`. Here they are defined for
an arbitrary family, as `WeierstrassCurve.shafarevichTateGroup` and `WeierstrassCurve.selmerGroup`,
the Selmer groups (`TauCeti.ContCohomology.SelmerStructure.selmerGroup`) of two Selmer structures
localising along the restriction maps `τ i`: on `E(Kˢ)` with the zero local conditions, and on
`E(Kˢ)[m]` with the local conditions `ker (H¹(G_{L i}, E[m]) → H¹(G_{L i}, E))`.
The homomorphism `G_{L i} → G_K` used for pullback requires a choice of embedding. The induced
cohomology maps and the resulting subgroups are independent of this choice, as proved in
`TauCeti/AlgebraicGeometry/EllipticCurve/GaloisCohomology/EmbeddingIndependence.lean`.

These kernel-based definitions need no hypothesis on `m` or on `W`. When `W` is elliptic and `m`
is invertible in `K`, the Selmer group is cut out by local Kummer conditions: a class lies in
`Sel_m` exactly when its restriction to each `L i` lies in the image of the local Kummer map
`E(L i) → H¹(G_{L i}, E[m])`
(`WeierstrassCurve.mem_selmerGroup_iff_forall_torsionRes_mem_range_kummerMap`). This is the form
in which local conditions are checked in practice, and it follows from the compatibility of
restriction with the Kummer maps and from the local `m`-descent sequence.

Under the same hypotheses, the main result is the **`m`-descent sequence** (Silverman X.4.2)

```text
0 ⟶ E(K) ⧸ m E(K) ⟶ Sel_m ⟶ Sha[m] ⟶ 0,
```

obtained by restricting the global sequence `0 → E(K) ⧸ m E(K) → H¹(G_K, E[m]) → H¹(G_K, E)[m] → 0`
of `TauCeti/AlgebraicGeometry/EllipticCurve/GaloisCohomology/Descent.lean` to the Selmer group.

## Main definitions

* `WeierstrassCurve.shaSelmerStructure`: the Selmer structure on `E(Kˢ)` with zero local
  conditions.
* `WeierstrassCurve.selmerStructure`: the Selmer structure on `E(Kˢ)[m]` whose local condition at
  `L i` is the kernel of `H¹(G_{L i}, E[m]) → H¹(G_{L i}, E)`; for `W` elliptic and `m` invertible
  in `K`, this is the image of the local Kummer map.
* `WeierstrassCurve.shafarevichTateGroup`: the classes in `H¹(G_K, E(Kˢ))` that restrict to zero
  over every `L i`.
* `WeierstrassCurve.selmerGroup`: the classes in `H¹(G_K, E(Kˢ)[m])` whose image in
  `H¹(G_K, E(Kˢ))` lies in the Shafarevich–Tate group.
* `WeierstrassCurve.kummerSelmerMap`: the Kummer map `E(K) ⧸ m E(K) → Sel_m`.
* `WeierstrassCurve.selmerShaMap`: the map `Sel_m → Sha[m]`.

## Main results

* `WeierstrassCurve.mem_selmerGroup_iff_forall_torsionRes_mem_range_kummerMap`: the Selmer group
  is cut out by the images of the local Kummer maps.
* `WeierstrassCurve.kummerMap_mem_selmerGroup`: Kummer classes of points of `E(K)` are Selmer.
* `WeierstrassCurve.kummerSelmerMap_injective`,
  `WeierstrassCurve.exact_kummerSelmerMap_selmerShaMap` and
  `WeierstrassCurve.selmerShaMap_surjective`: the `m`-descent sequence
  `0 → E(K) ⧸ m E(K) → Sel_m → Sha[m] → 0` is exact.

## References

* [J. Silverman, *The Arithmetic of Elliptic Curves*][silverman2009], X.4.
-/

public section

noncomputable section

namespace WeierstrassCurve

open TauCeti TauCeti.ContCohomology

variable {K : Type*} [Field K] (W : WeierstrassCurve K) {ι : Type*} {L : ι → Type*}
  [∀ i, Field (L i)] [∀ i, Algebra K (L i)]
  (τ : ∀ i, SeparableClosure K →ₐ[K] SeparableClosure (L i))

/-! ### The Shafarevich–Tate group -/

/-- **The Selmer structure of the Shafarevich–Tate group**: on `E(Kˢ)`, localised along the
restriction maps `τ i`, with the zero local condition at every `L i`. -/
def shaSelmerStructure :
    SelmerStructure (AbsoluteGaloisGroup K) W.PointCoeff (fun i => AbsoluteGaloisGroup (L i))
      (fun i => (W⁄(L i)).PointCoeff) where
  groupHom i := absoluteGaloisGroupMap (τ i)
  coeffHom i := W.pointCoeffBaseChange (τ i)
  continuous_coeffHom _ := continuous_of_discreteTopology
  coeffHom_smul i := W.pointCoeffBaseChange_smul (τ i)
  localCondition _ := ⊥

/-- The localisation maps of `shaSelmerStructure τ` are the restriction maps `pointRes (τ i)`. -/
@[simp]
theorem shaSelmerStructure_localization (i : ι) :
    (W.shaSelmerStructure τ).localization i = W.pointRes (τ i) := by
  rw [SelmerStructure.localization_eq_explicitMap1, pointRes_eq_explicitMap1]
  rfl

@[simp]
theorem shaSelmerStructure_localCondition (i : ι) :
    (W.shaSelmerStructure τ).localCondition i = ⊥ :=
  (rfl)

/-- **The Shafarevich–Tate group** of `W` relative to the family of extensions `L i` with
embeddings `τ i`: the Selmer group of `shaSelmerStructure τ`, that is, the classes in
`H¹(G_K, E(Kˢ))` whose restriction to every `L i` vanishes. For a number field and the family of
its completions at all places this is `Sha(E/K)` (Silverman X.4). -/
def shafarevichTateGroup : AddSubgroup (H1 (AbsoluteGaloisGroup K) W.PointCoeff) :=
  (W.shaSelmerStructure τ).selmerGroup

@[simp]
theorem mem_shafarevichTateGroup_iff {c : H1 (AbsoluteGaloisGroup K) W.PointCoeff} :
    c ∈ W.shafarevichTateGroup τ ↔ ∀ i, W.pointRes (τ i) c = 0 := by
  simp only [shafarevichTateGroup, SelmerStructure.mem_selmerGroup_iff,
    shaSelmerStructure_localization, shaSelmerStructure_localCondition, AddSubgroup.mem_bot]

/-! ### The Selmer group -/

variable (m : ℕ)

/-- **The Selmer structure of the `m`-Selmer group**: on `E(Kˢ)[m]`, localised along the
restriction maps `τ i`, with local condition at `L i` the kernel of
`H¹(G_{L i}, E[m]) → H¹(G_{L i}, E)`. When `W` is elliptic and `m` is invertible in `K`, this
kernel is the image of the local Kummer map `E(L i) → H¹(G_{L i}, E[m])`
(`WeierstrassCurve.mem_selmerGroup_iff_forall_torsionRes_mem_range_kummerMap`). -/
def selmerStructure :
    SelmerStructure (AbsoluteGaloisGroup K) (W.TorsionCoeff m)
      (fun i => AbsoluteGaloisGroup (L i)) (fun i => (W⁄(L i)).TorsionCoeff m) where
  groupHom i := absoluteGaloisGroupMap (τ i)
  coeffHom i := W.torsionCoeffBaseChange (τ i) m
  continuous_coeffHom _ := continuous_of_discreteTopology
  coeffHom_smul i := W.torsionCoeffBaseChange_smul (τ i) m
  localCondition i :=
    (explicitCoeff1 _ _ ((W⁄(L i)).torsionCoeffIncl m) continuous_of_discreteTopology).ker

/-- The localisation maps of `selmerStructure τ m` are the restriction maps
`torsionRes (τ i) m`. -/
@[simp]
theorem selmerStructure_localization (i : ι) :
    (W.selmerStructure τ m).localization i = W.torsionRes (τ i) m := by
  rw [SelmerStructure.localization_eq_explicitMap1, torsionRes_eq_explicitMap1]
  rfl

@[simp]
theorem selmerStructure_localCondition (i : ι) :
    (W.selmerStructure τ m).localCondition i =
      (explicitCoeff1 _ _ ((W⁄(L i)).torsionCoeffIncl m) continuous_of_discreteTopology).ker :=
  (rfl)

/-- **The `m`-Selmer group** of `W` relative to the family of extensions `L i` with embeddings
`τ i`: the Selmer group of `selmerStructure τ m`, that is, the classes in `H¹(G_K, E(Kˢ)[m])`
whose image in `H¹(G_K, E(Kˢ))` lies in the Shafarevich–Tate group (`mem_selmerGroup_iff`). For a
number field and the family of its completions at all places this is `Sel_m(E/K)`
(Silverman X.4). -/
def selmerGroup : AddSubgroup (H1 (AbsoluteGaloisGroup K) (W.TorsionCoeff m)) :=
  (W.selmerStructure τ m).selmerGroup

@[simp]
theorem mem_selmerGroup_iff {c : H1 (AbsoluteGaloisGroup K) (W.TorsionCoeff m)} :
    c ∈ W.selmerGroup τ m ↔
      explicitCoeff1 _ _ (W.torsionCoeffIncl m) continuous_of_discreteTopology c ∈
        W.shafarevichTateGroup τ := by
  simp only [selmerGroup, SelmerStructure.mem_selmerGroup_iff, selmerStructure_localization,
    selmerStructure_localCondition, AddMonoidHom.mem_ker, mem_shafarevichTateGroup_iff,
    pointRes_torsionCoeffIncl]

variable {m} in
/-- **The Selmer group is cut out by the local Kummer images**: a class in `H¹(G_K, E(Kˢ)[m])` is
Selmer exactly when its restriction to every `L i` comes from a point of `E(L i)` under the local
Kummer map. -/
theorem mem_selmerGroup_iff_forall_torsionRes_mem_range_kummerMap [W.IsElliptic]
    [∀ i, DecidableEq (L i)] (hm : IsUnit (m : K))
    {c : H1 (AbsoluteGaloisGroup K) (W.TorsionCoeff m)} :
    c ∈ W.selmerGroup τ m ↔ ∀ i, W.torsionRes (τ i) m c ∈
      ((W⁄(L i)).kummerMap m (by simpa using hm.map (algebraMap K (L i)))).range := by
  simp only [mem_selmerGroup_iff, mem_shafarevichTateGroup_iff, pointRes_torsionCoeffIncl,
    range_kummerMap, AddMonoidHom.mem_ker]

/-! ### The `m`-descent sequence -/

section Descent

variable [DecidableEq K] [W.IsElliptic] {m} (hm : IsUnit (m : K))

/-- **Kummer classes are Selmer**: the Kummer class of a point of `E(K)` lies in the Selmer
group, since it already vanishes in `H¹(G_K, E(Kˢ))`. -/
theorem kummerMap_mem_selmerGroup (P : W.toAffine.Point) :
    W.kummerMap m hm P ∈ W.selmerGroup τ m := by
  have h : W.kummerMap m hm P ∈ (W.kummerMap m hm).range := ⟨P, rfl⟩
  rw [range_kummerMap, AddMonoidHom.mem_ker] at h
  rw [mem_selmerGroup_iff, h]
  exact zero_mem _

/-- **The Kummer map `E(K) ⧸ m E(K) → Sel_m`**, the first map of the `m`-descent sequence. -/
def kummerSelmerMap :
    W.toAffine.Point ⧸ (nsmulAddMonoidHom (α := W.toAffine.Point) m).range →+
      W.selmerGroup τ m :=
  (W.kummerClassMap m hm).codRestrict _ fun x => by
    induction x using QuotientAddGroup.induction_on with
    | _ P => rw [kummerClassMap_mk]; exact W.kummerMap_mem_selmerGroup τ hm P

@[simp]
theorem coe_kummerSelmerMap
    (x : W.toAffine.Point ⧸ (nsmulAddMonoidHom (α := W.toAffine.Point) m).range) :
    (W.kummerSelmerMap τ hm x : H1 (AbsoluteGaloisGroup K) (W.TorsionCoeff m)) =
      W.kummerClassMap m hm x :=
  (rfl)

/-- **`E(K) ⧸ m E(K)` injects into the Selmer group.** -/
theorem kummerSelmerMap_injective : Function.Injective (W.kummerSelmerMap τ hm) :=
  fun _ _ h => W.kummerClassMap_injective m hm (congrArg Subtype.val h)

omit [DecidableEq K] [W.IsElliptic] in
variable (m) in
/-- **The map `Sel_m → Sha[m]`**, the second map of the `m`-descent sequence: the map induced by
the inclusion `E(Kˢ)[m] → E(Kˢ)`, restricted to the Selmer group. -/
def selmerShaMap :
    W.selmerGroup τ m →+ AddSubgroup.torsionBy (W.shafarevichTateGroup τ) m where
  toFun c := ⟨⟨explicitCoeff1 _ _ (W.torsionCoeffIncl m) continuous_of_discreteTopology c,
    (W.mem_selmerGroup_iff τ m).1 c.2⟩, AddSubgroup.torsionBy.nsmul_iff.2 <| Subtype.ext <| by
      -- `m` kills the image of `H¹(G_K, E[m])`, as recorded by `torsionCoeffInclH1`.
      have h := (W.torsionCoeffInclH1 m c).2
      rw [coe_torsionCoeffInclH1, AddSubgroup.torsionBy.nsmul_iff] at h
      rw [AddSubgroup.coe_nsmul, h, ZeroMemClass.coe_zero]⟩
  map_zero' := by ext; simp
  map_add' _ _ := by ext; simp

omit [DecidableEq K] [W.IsElliptic] in
variable (m) in
@[simp]
theorem coe_selmerShaMap (c : W.selmerGroup τ m) :
    ((W.selmerShaMap τ m c : W.shafarevichTateGroup τ) :
        H1 (AbsoluteGaloisGroup K) W.PointCoeff) =
      explicitCoeff1 _ _ (W.torsionCoeffIncl m) continuous_of_discreteTopology c :=
  (rfl)

/-- **The `m`-descent sequence is exact at `Sel_m`**: the kernel of `Sel_m → Sha[m]` is the image of
`E(K) ⧸ m E(K)` under the Kummer map. -/
theorem exact_kummerSelmerMap_selmerShaMap :
    Function.Exact (W.kummerSelmerMap τ hm) (W.selmerShaMap τ m) := by
  intro c
  have hker : W.selmerShaMap τ m c = 0 ↔
      explicitCoeff1 _ _ (W.torsionCoeffIncl m) continuous_of_discreteTopology c = 0 := by
    simp only [← Subtype.val_inj, coe_selmerShaMap, ZeroMemClass.coe_zero]
  rw [hker, ← AddMonoidHom.mem_ker, ← range_kummerMap W m hm]
  refine ⟨fun ⟨P, hP⟩ => ⟨QuotientAddGroup.mk P, Subtype.ext ?_⟩, fun ⟨x, hx⟩ => ?_⟩
  · rw [coe_kummerSelmerMap, kummerClassMap_mk, hP]
  · induction x using QuotientAddGroup.induction_on with
    | _ P => exact ⟨P, by rw [← kummerClassMap_mk, ← W.coe_kummerSelmerMap τ hm, hx]⟩

omit [DecidableEq K] in
include hm in
/-- **`Sel_m → Sha[m]` is surjective**, the right end of the `m`-descent sequence: a class of `Sha`
killed by `m` lifts to `H¹(G_K, E(Kˢ)[m])` by the global descent sequence, and every lift is
Selmer. -/
theorem selmerShaMap_surjective : Function.Surjective (W.selmerShaMap τ m) := by
  rintro ⟨⟨c, hc⟩, hct⟩
  have hcm : c ∈ AddSubgroup.torsionBy (H1 (AbsoluteGaloisGroup K) W.PointCoeff) m :=
    AddSubgroup.torsionBy.nsmul_iff.2 <| congrArg Subtype.val
      (AddSubgroup.torsionBy.nsmul_iff.1 hct)
  obtain ⟨d, hd⟩ := W.torsionCoeffInclH1_surjective m hm ⟨c, hcm⟩
  have hdc : explicitCoeff1 _ _ (W.torsionCoeffIncl m) continuous_of_discreteTopology d = c :=
    (W.coe_torsionCoeffInclH1 m d).symm.trans (congrArg Subtype.val hd)
  refine ⟨⟨d, (W.mem_selmerGroup_iff τ m).2 (hdc ▸ hc)⟩, ?_⟩
  ext
  rw [coe_selmerShaMap]
  exact hdc

end Descent

end WeierstrassCurve
