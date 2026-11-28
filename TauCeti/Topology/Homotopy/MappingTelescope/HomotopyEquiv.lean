/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.Homotopy.Extension.Tower
public import TauCeti.Topology.Homotopy.MappingTelescope.Stage

/-!
# Functoriality and homotopy equivalences of mapping telescopes

This file constructs functorial maps of mapping telescopes—both for strictly commuting ladders and
for ladders commuting up to chosen homotopies—and proves the fundamental homotopy invariance and
comparison theorems for `TauCeti.MappingTelescope`:

* **Strict and homotopy-coherent functoriality.** A family of maps `g : ∀ n, C(X n, Y n)` commuting
  strictly with the bonding maps induces `TauCeti.MappingTelescope.map g hg` cylinder-by-cylinder.
  More generally, a family `g` together with homotopies
  `H n : (f' n).comp (g n) ≃ (g (n + 1)).comp (f n)` induces
  `TauCeti.MappingTelescope.mapOfHomotopy g H`, traversing the `n`-th cylinder of `f'` on the first
  half of the `n`-th cylinder of `f` and running `H n` along `incl f' (n + 1)` on the second half.
* **Levelwise homotopy invariance.** When every `g n` is a homotopy equivalence `e n : X n ≃ₕ Y n`,
  both `map` and `mapOfHomotopy` restrict on finite stages to homotopy equivalences
  `stage f n ≃ₕ stage f' n` and therefore assemble, via
  `TauCeti.exists_homotopyEquiv_of_isCoherentWith`, into homotopy equivalences of telescopes
  (`TauCeti.MappingTelescope.homotopyEquivOfMap` and
  `TauCeti.MappingTelescope.homotopyEquivOfHomotopy`).
* **Cofinal subsequences.** For any monotone cofinal map `φ : ℕ → ℕ`, the inclusion
  `TauCeti.MappingTelescope.subsequenceIncl` from the telescope of composite bonding maps
  `bondOfLE f (hφ n.le_succ)` into `MappingTelescope f` is a homotopy equivalence
  (`TauCeti.MappingTelescope.subsequenceHomotopyEquiv`).
* **Comparison with sequential colimits and coherent unions of cofibrations.** The stage
  retractions `stageProj f n` form a levelwise homotopy equivalence from the diagram of stages
  `stage f n` to any sequence `F : ℕ ⥤ TopCat` whose bonding maps are embeddings with images having
  the homotopy extension property. Consequently `TauCeti.cofibrationTowerHomotopyEquiv` identifies
  `MappingTelescope` with any colimit cocone of `F`
  (`TauCeti.MappingTelescope.colimitHomotopyEquiv`), and in particular with any space exhausted
  coherently by an increasing tower of subsets each having the homotopy extension property in the
  next (`TauCeti.MappingTelescope.unionHomotopyEquiv`).

## References

* J. Milnor, *On axiomatic homology theory*, Pacific J. Math. 12 (1962), 337–341.
* A. Hatcher, [*Algebraic Topology*](https://pi.math.cornell.edu/~hatcher/AT/AT.pdf),
  Section 3.F and Appendix, Proposition A.11.
* T. tom Dieck, *Algebraic Topology*, EMS Textbooks in Mathematics, 2008, Chapter 5.
* J. P. May, *A Concise Course in Algebraic Topology*, Chapter 14.
-/

public section

noncomputable section

namespace TauCeti.MappingTelescope

open Set Topology ContinuousMap CategoryTheory Limits unitInterval

universe u v w

/-- Promotes a continuous map `M : C(stage f m, stage f' n)` between finite stages to a homotopy
equivalence when `M` intertwines `inclStage f m` and `inclStage f' n` along `e : X m ≃ₕ Y n`. -/
private def stageEquivOfInclEq {X : ℕ → Type u} {Y : ℕ → Type v}
    [∀ k, TopologicalSpace (X k)] [∀ k, TopologicalSpace (Y k)]
    {f : ∀ k, C(X k, X (k + 1))} {f' : ∀ k, C(Y k, Y (k + 1))} {m n : ℕ}
    (e : X m ≃ₕ Y n) (M : C(stage f m, stage f' n))
    (hM : M.comp (inclStage f m) = (inclStage f' n).comp e.toFun) :
    stage f m ≃ₕ stage f' n :=
  let i : X m ≃ₕ stage f m := stageHomotopyEquiv f m
  let j : Y n ≃ₕ stage f' n := stageHomotopyEquiv f' n
  let E : stage f m ≃ₕ stage f' n := i.symm.trans (e.trans j)
  have hME : M.Homotopic E.toFun := by
    have h1 : M.Homotopic (M.comp (i.toFun.comp i.invFun)) :=
      (ContinuousMap.Homotopic.refl M).comp i.right_inv.symm
    have h2 : M.comp (i.toFun.comp i.invFun) = E.toFun :=
      ContinuousMap.ext fun s => by
        simpa [i, j, E] using congrFun (congrArg DFunLike.coe hM) (i.invFun s)
    rwa [h2] at h1
  { toFun := M
    invFun := E.invFun
    left_inv := ((ContinuousMap.Homotopic.refl E.invFun).comp hME).trans E.left_inv
    right_inv := (hME.comp (ContinuousMap.Homotopic.refl E.invFun)).trans E.right_inv }

section StagePromotion

variable {X Y : ℕ → Type u} [∀ n, TopologicalSpace (X n)] [∀ n, TopologicalSpace (Y n)]
  {f : ∀ n, C(X n, X (n + 1))} {f' : ∀ n, C(Y n, Y (n + 1))}

/-- Any map of telescopes that preserves finite stages and acts on `incl f n` via levelwise
homotopy equivalences `e n : X n ≃ₕ Y n` is a homotopy equivalence of telescopes. -/
private def homotopyEquivOfStageMapsTo (M : C(MappingTelescope f, MappingTelescope f'))
    (hstage : ∀ n, MapsTo M (stage f n) (stage f' n)) (e : ∀ n, X n ≃ₕ Y n)
    (hincl : ∀ n x, M (incl f n x) = incl f' n (e n x)) :
    MappingTelescope f ≃ₕ MappingTelescope f' :=
  let Mstage (n : ℕ) : C(stage f n, stage f' n) :=
    ⟨(hstage n).restrict _ _ _, M.continuous.restrict _⟩
  let estage (n : ℕ) : stage f n ≃ₕ stage f' n :=
    stageEquivOfInclEq (e n) (Mstage n) (by
      ext x
      simpa [Mstage] using hincl n x)
  have hex := exists_homotopyEquiv_of_isCoherentWith stage_mono stage_mono iUnion_stage iUnion_stage
    isCoherentWith_range_stage isCoherentWith_range_stage hasHomotopyExtensionProperty_stage
    hasHomotopyExtensionProperty_stage M estage fun _ _ => rfl
  have hM : hex.choose.toFun = M := ContinuousMap.ext (congrFun hex.choose_spec.1)
  { toFun := M
    invFun := hex.choose.invFun
    left_inv := by simpa only [hM] using hex.choose.left_inv
    right_inv := by simpa only [hM] using hex.choose.right_inv }

end StagePromotion

section StrictMap

variable {X : ℕ → Type u} [∀ n, TopologicalSpace (X n)] {f : ∀ n, C(X n, X (n + 1))}
  {Y : ℕ → Type v} [∀ n, TopologicalSpace (Y n)] {f' : ∀ n, C(Y n, Y (n + 1))}
  {Z : ℕ → Type w} [∀ n, TopologicalSpace (Z n)] {f'' : ∀ n, C(Z n, Z (n + 1))}

/-- **Strict functoriality of the mapping telescope.** A family of continuous maps
`g : ∀ n, C(X n, Y n)` commuting strictly with the bonding maps induces a continuous map on mapping
telescopes cylinder-by-cylinder. -/
def map (g : ∀ n, C(X n, Y n)) (hg : ∀ n, (f' n).comp (g n) = (g (n + 1)).comp (f n)) :
    C(MappingTelescope f, MappingTelescope f') :=
  lift (fun n => (mkCyl f' n).comp ((ContinuousMap.id I).prodMap (g n))) fun n x => by
    simp only [ContinuousMap.comp_apply, ContinuousMap.prodMap_apply, Prod.map_apply,
      ContinuousMap.id_apply, mkCyl_one]
    exact congrArg (mkCyl f' (n + 1) ⟨0, ·⟩) (congrFun (congrArg DFunLike.coe (hg n)) x)

@[simp]
theorem map_mkCyl (g : ∀ n, C(X n, Y n)) (hg : ∀ n, (f' n).comp (g n) = (g (n + 1)).comp (f n))
    (n : ℕ) (p : I × X n) :
    map g hg (mkCyl f n p) = mkCyl f' n (p.1, g n p.2) :=
  lift_mkCyl _ n p

theorem map_incl (g : ∀ n, C(X n, Y n)) (hg : ∀ n, (f' n).comp (g n) = (g (n + 1)).comp (f n))
    (n : ℕ) (x : X n) :
    map g hg (incl f n x) = incl f' n (g n x) := by
  rw [incl_apply, map_mkCyl, incl_apply]

@[simp]
theorem map_comp_incl (g : ∀ n, C(X n, Y n))
    (hg : ∀ n, (f' n).comp (g n) = (g (n + 1)).comp (f n)) (n : ℕ) :
    (map g hg).comp (incl f n) = (incl f' n).comp (g n) :=
  ContinuousMap.ext (map_incl g hg n)

@[simp]
theorem map_id {hg : ∀ n, (f n).comp (ContinuousMap.id (X n)) =
    (ContinuousMap.id (X (n + 1))).comp (f n)} :
    map (f := f) (f' := f) (fun n => ContinuousMap.id (X n)) hg =
      ContinuousMap.id (MappingTelescope f) :=
  hom_ext fun n p => by simp

theorem map_comp (g : ∀ n, C(X n, Y n)) (hg : ∀ n, (f' n).comp (g n) = (g (n + 1)).comp (f n))
    (g' : ∀ n, C(Y n, Z n)) (hg' : ∀ n, (f'' n).comp (g' n) = (g' (n + 1)).comp (f' n)) :
    (map g' hg').comp (map g hg) =
      map (fun n => (g' n).comp (g n)) (fun n => by
        rw [← ContinuousMap.comp_assoc, hg', ContinuousMap.comp_assoc, hg,
          ← ContinuousMap.comp_assoc]) :=
  hom_ext fun n p => by simp

theorem mapsTo_map_stage (g : ∀ n, C(X n, Y n))
    (hg : ∀ n, (f' n).comp (g n) = (g (n + 1)).comp (f n)) (n : ℕ) :
    MapsTo (map g hg) (stage f n) (stage f' n) := by
  intro z hz
  induction z using ind with
  | cyl m p =>
    obtain ⟨s, x⟩ := p
    rw [map_mkCyl, mkCyl_mem_stage_iff]
    exact mkCyl_mem_stage_iff.1 hz

/-- **Levelwise homotopy equivalences of strictly commuting ladders induce a homotopy equivalence
of mapping telescopes.** -/
def homotopyEquivOfMap {Y : ℕ → Type u} [∀ n, TopologicalSpace (Y n)]
    {f' : ∀ n, C(Y n, Y (n + 1))} (e : ∀ n, X n ≃ₕ Y n)
    (he : ∀ n, (f' n).comp (e n).toFun = (e (n + 1)).toFun.comp (f n)) :
    MappingTelescope f ≃ₕ MappingTelescope f' :=
  homotopyEquivOfStageMapsTo (map (fun n => (e n).toFun) he)
    (mapsTo_map_stage (fun n => (e n).toFun) he) e (map_incl (fun n => (e n).toFun) he)

@[simp]
theorem homotopyEquivOfMap_toFun {Y : ℕ → Type u} [∀ n, TopologicalSpace (Y n)]
    {f' : ∀ n, C(Y n, Y (n + 1))} (e : ∀ n, X n ≃ₕ Y n)
    (he : ∀ n, (f' n).comp (e n).toFun = (e (n + 1)).toFun.comp (f n)) :
    (homotopyEquivOfMap e he).toFun = map (fun n => (e n).toFun) he :=
  (rfl)

end StrictMap

section HomotopySquare

variable {X : ℕ → Type u} [∀ n, TopologicalSpace (X n)] {f : ∀ n, C(X n, X (n + 1))}
  {Y : ℕ → Type v} [∀ n, TopologicalSpace (Y n)] {f' : ∀ n, C(Y n, Y (n + 1))}

/-- Cylinder homotopy used to build `mapOfHomotopy`: first slide down the `n`-th cylinder of `f'`
along `g n`, then run `H n` inside `Y (n + 1)` via `incl f' (n + 1)`. -/
private def mapCylHomotopy (g : ∀ n, C(X n, Y n))
    (H : ∀ n, ((f' n).comp (g n)).Homotopy ((g (n + 1)).comp (f n))) (n : ℕ) :
    ((incl f' n).comp (g n)).Homotopy ((incl f' (n + 1)).comp ((g (n + 1)).comp (f n))) :=
  ((inclHomotopy f' n).compContinuousMap (g n)).trans
    ((ContinuousMap.Homotopy.refl (incl f' (n + 1))).comp (H n))

/-- **Homotopy-coherent functoriality of the mapping telescope.** Given maps `g : ∀ n, C(X n, Y n)`
and homotopies `H n` from `(f' n).comp (g n)` to `(g (n + 1)).comp (f n)`, there is a canonical
induced map `C(MappingTelescope f, MappingTelescope f')` extending `g n` on every bottom face
`incl f n`. -/
def mapOfHomotopy (g : ∀ n, C(X n, Y n))
    (H : ∀ n, ((f' n).comp (g n)).Homotopy ((g (n + 1)).comp (f n))) :
    C(MappingTelescope f, MappingTelescope f') :=
  lift (fun n => (mapCylHomotopy g H n).toContinuousMap) fun n x => by simp

@[simp]
theorem mapOfHomotopy_mkCyl (g : ∀ n, C(X n, Y n))
    (H : ∀ n, ((f' n).comp (g n)).Homotopy ((g (n + 1)).comp (f n))) (n : ℕ) (p : I × X n) :
    mapOfHomotopy g H (mkCyl f n p) =
      (((inclHomotopy f' n).compContinuousMap (g n)).trans
        ((ContinuousMap.Homotopy.refl (incl f' (n + 1))).comp (H n))) p :=
  lift_mkCyl _ n p

theorem mapOfHomotopy_mkCyl_zero (g : ∀ n, C(X n, Y n))
    (H : ∀ n, ((f' n).comp (g n)).Homotopy ((g (n + 1)).comp (f n))) (n : ℕ) (x : X n) :
    mapOfHomotopy g H (mkCyl f n (0, x)) = mkCyl f' n (0, g n x) := by
  simp [incl_apply]

theorem mapOfHomotopy_incl (g : ∀ n, C(X n, Y n))
    (H : ∀ n, ((f' n).comp (g n)).Homotopy ((g (n + 1)).comp (f n))) (n : ℕ) (x : X n) :
    mapOfHomotopy g H (incl f n x) = incl f' n (g n x) := by
  simp [incl_apply]

@[simp]
theorem mapOfHomotopy_comp_incl (g : ∀ n, C(X n, Y n))
    (H : ∀ n, ((f' n).comp (g n)).Homotopy ((g (n + 1)).comp (f n))) (n : ℕ) :
    (mapOfHomotopy g H).comp (incl f n) = (incl f' n).comp (g n) :=
  ContinuousMap.ext (mapOfHomotopy_incl g H n)

theorem mapsTo_mapOfHomotopy_stage (g : ∀ n, C(X n, Y n))
    (H : ∀ n, ((f' n).comp (g n)).Homotopy ((g (n + 1)).comp (f n))) (n : ℕ) :
    MapsTo (mapOfHomotopy g H) (stage f n) (stage f' n) := by
  intro z hz
  induction z using ind with
  | cyl m p =>
    obtain ⟨s, x⟩ := p
    rcases mkCyl_mem_stage_iff.1 hz with hmn | ⟨rfl, rfl⟩
    · rw [mapOfHomotopy_mkCyl, ContinuousMap.Homotopy.trans_apply]
      split_ifs
      · simp only [ContinuousMap.Homotopy.compContinuousMap_apply, inclHomotopy_apply]
        exact mkCyl_mem_stage_iff.2 (Or.inl hmn)
      · simp only [ContinuousMap.Homotopy.comp_apply, ContinuousMap.Homotopy.refl_apply]
        exact incl_mem_stage_iff.2 (Nat.succ_le_of_lt hmn)
    · rw [← incl_apply, mapOfHomotopy_incl]
      exact incl_mem_stage_iff.2 le_rfl

/-- **Levelwise homotopy equivalences commuting with bonding maps up to homotopy induce a homotopy
equivalence of mapping telescopes.** -/
def homotopyEquivOfHomotopy {Y : ℕ → Type u} [∀ n, TopologicalSpace (Y n)]
    {f' : ∀ n, C(Y n, Y (n + 1))} (e : ∀ n, X n ≃ₕ Y n)
    (H : ∀ n, ((f' n).comp (e n).toFun).Homotopy ((e (n + 1)).toFun.comp (f n))) :
    MappingTelescope f ≃ₕ MappingTelescope f' :=
  homotopyEquivOfStageMapsTo (mapOfHomotopy (fun n => (e n).toFun) H)
    (mapsTo_mapOfHomotopy_stage (fun n => (e n).toFun) H) e
    (mapOfHomotopy_incl (fun n => (e n).toFun) H)

@[simp]
theorem homotopyEquivOfHomotopy_toFun {Y : ℕ → Type u} [∀ n, TopologicalSpace (Y n)]
    {f' : ∀ n, C(Y n, Y (n + 1))} (e : ∀ n, X n ≃ₕ Y n)
    (H : ∀ n, ((f' n).comp (e n).toFun).Homotopy ((e (n + 1)).toFun.comp (f n))) :
    (homotopyEquivOfHomotopy e H).toFun = mapOfHomotopy (fun n => (e n).toFun) H :=
  (rfl)

end HomotopySquare

section Subsequence

variable {X : ℕ → Type u} [∀ n, TopologicalSpace (X n)] (f : ∀ n, C(X n, X (n + 1)))

/-- The bonding maps `X (φ n) → X (φ (n + 1))` of a monotone subsequence `φ : ℕ → ℕ`, obtained by
composing the intervening maps `f` via `bondOfLE`. -/
def subsequence {φ : ℕ → ℕ} (hφ : Monotone φ) (n : ℕ) : C(X (φ n), X (φ (n + 1))) :=
  bondOfLE f (hφ n.le_succ)

/-- The canonical map from the mapping telescope of a monotone subsequence into the ambient mapping
telescope, sending the `n`-th cylinder along `inclHomotopyOfLE f (hφ n.le_succ)`. -/
def subsequenceIncl {φ : ℕ → ℕ} (hφ : Monotone φ) :
    C(MappingTelescope (X := fun n => X (φ n)) (subsequence f hφ), MappingTelescope f) :=
  lift (X := fun n => X (φ n)) (f := subsequence f hφ)
    (fun n => (inclHomotopyOfLE f (hφ n.le_succ)).toContinuousMap) fun n x => by
      simp [subsequence]

@[simp]
theorem subsequenceIncl_mkCyl {φ : ℕ → ℕ} (hφ : Monotone φ) (n : ℕ) (p : I × X (φ n)) :
    subsequenceIncl f hφ (mkCyl (X := fun k => X (φ k)) (subsequence f hφ) n p) =
      inclHomotopyOfLE f (hφ n.le_succ) p :=
  lift_mkCyl (X := fun k => X (φ k)) (f := subsequence f hφ) _ n p

theorem subsequenceIncl_mkCyl_zero {φ : ℕ → ℕ} (hφ : Monotone φ) (n : ℕ) (x : X (φ n)) :
    subsequenceIncl f hφ (mkCyl (X := fun k => X (φ k)) (subsequence f hφ) n (0, x)) =
      mkCyl f (φ n) (0, x) := by
  simp [incl_apply]

theorem subsequenceIncl_incl {φ : ℕ → ℕ} (hφ : Monotone φ) (n : ℕ) (x : X (φ n)) :
    subsequenceIncl f hφ (incl (X := fun k => X (φ k)) (subsequence f hφ) n x) =
      incl f (φ n) x := by
  simp [incl_apply]

@[simp]
theorem subsequenceIncl_comp_incl {φ : ℕ → ℕ} (hφ : Monotone φ) (n : ℕ) :
    (subsequenceIncl f hφ).comp (incl (X := fun k => X (φ k)) (subsequence f hφ) n) =
      incl f (φ n) :=
  ContinuousMap.ext (subsequenceIncl_incl f hφ n)

theorem mapsTo_subsequenceIncl_stage {φ : ℕ → ℕ} (hφ : Monotone φ) (n : ℕ) :
    MapsTo (subsequenceIncl f hφ)
      (stage (X := fun k => X (φ k)) (subsequence f hφ) n) (stage f (φ n)) := by
  intro z hz
  induction z using ind with
  | cyl m p =>
    obtain ⟨s, x⟩ := p
    rcases mkCyl_mem_stage_iff.1 hz with hmn | ⟨rfl, rfl⟩
    · rw [subsequenceIncl_mkCyl]
      exact stage_mono (hφ (Nat.succ_le_of_lt hmn))
        (inclHomotopyOfLE_mem_stage (hφ m.le_succ) s x)
    · rw [← incl_apply, subsequenceIncl_incl]
      exact incl_mem_stage_iff.2 le_rfl

/-- **Cofinal subsequence invariance of the mapping telescope.** For any monotone cofinal map
`φ : ℕ → ℕ`, `subsequenceIncl f hφ` is a homotopy equivalence between the telescope of the
subsequence and `MappingTelescope f`. -/
def subsequenceHomotopyEquiv {φ : ℕ → ℕ} (hφ : Monotone φ) (hcof : ∀ m, ∃ n, m ≤ φ n) :
    MappingTelescope (X := fun n => X (φ n)) (subsequence f hφ) ≃ₕ MappingTelescope f :=
  let B (n : ℕ) : Set (MappingTelescope f) := stage f (φ n)
  let Mstage (n : ℕ) : C(stage (X := fun k => X (φ k)) (subsequence f hφ) n, B n) :=
    ⟨(mapsTo_subsequenceIncl_stage f hφ n).restrict _ _ _,
      (subsequenceIncl f hφ).continuous.restrict _⟩
  let estage (n : ℕ) : stage (X := fun k => X (φ k)) (subsequence f hφ) n ≃ₕ B n :=
    stageEquivOfInclEq (ContinuousMap.HomotopyEquiv.refl (X (φ n))) (Mstage n) (by
      ext x
      simp [B, Mstage, incl_apply])
  have hex := exists_homotopyEquiv_of_isCoherentWith stage_mono (stage_mono.comp hφ) iUnion_stage
    (iUnion_stage_comp hcof) isCoherentWith_range_stage (isCoherentWith_range_stage_comp hcof)
    hasHomotopyExtensionProperty_stage
    (fun n => hasHomotopyExtensionProperty_preimage_stage (φ n) (φ (n + 1))) (subsequenceIncl f hφ)
    estage fun _ _ => rfl
  have hM : hex.choose.toFun = subsequenceIncl f hφ :=
    ContinuousMap.ext (congrFun hex.choose_spec.1)
  { toFun := subsequenceIncl f hφ
    invFun := hex.choose.invFun
    left_inv := by simpa only [hM] using hex.choose.left_inv
    right_inv := by simpa only [hM] using hex.choose.right_inv }

@[simp]
theorem subsequenceHomotopyEquiv_toFun {φ : ℕ → ℕ} (hφ : Monotone φ)
    (hcof : ∀ m, ∃ n, m ≤ φ n) :
    (subsequenceHomotopyEquiv f hφ hcof).toFun = subsequenceIncl f hφ :=
  (rfl)

/-- Specialisation of `subsequenceHomotopyEquiv` to a strictly monotone subsequence `φ : ℕ → ℕ`. -/
def subsequenceHomotopyEquivOfStrictMono {φ : ℕ → ℕ} (hφ : StrictMono φ) :
    MappingTelescope (X := fun n => X (φ n)) (subsequence f hφ.monotone) ≃ₕ MappingTelescope f :=
  subsequenceHomotopyEquiv f hφ.monotone fun m => ⟨m, hφ.id_le m⟩

@[simp]
theorem subsequenceHomotopyEquivOfStrictMono_toFun {φ : ℕ → ℕ} (hφ : StrictMono φ) :
    (subsequenceHomotopyEquivOfStrictMono f hφ).toFun = subsequenceIncl f hφ.monotone :=
  (rfl)

end Subsequence

section ColimitAndUnion

/-- The canonical map from the mapping telescope of a sequence `F : ℕ ⥤ TopCat` to the vertex of any
cocone `c` over `F`, collapsing each cylinder `I × F.obj n` along `c.ι.app n`. -/
def toCocone {F : ℕ ⥤ TopCat.{u}} (c : Cocone F) :
    C(MappingTelescope (X := fun n => F.obj n) (fun n => (F.map (homOfLE n.le_succ)).hom), c.pt) :=
  lift (X := fun n => F.obj n) (f := fun n => (F.map (homOfLE n.le_succ)).hom)
    (fun n => (c.ι.app n).hom.comp ⟨Prod.snd, continuous_snd⟩) fun n x =>
      (ConcreteCategory.congr_hom (c.w (homOfLE n.le_succ)) x).symm

@[simp]
theorem toCocone_mkCyl {F : ℕ ⥤ TopCat.{u}} (c : Cocone F) (n : ℕ) (p : I × F.obj n) :
    toCocone c (mkCyl (X := fun k => F.obj k) (fun k => (F.map (homOfLE k.le_succ)).hom) n p) =
      c.ι.app n p.2 :=
  lift_mkCyl (X := fun k => F.obj k) (f := fun k => (F.map (homOfLE k.le_succ)).hom) _ n p

theorem toCocone_incl {F : ℕ ⥤ TopCat.{u}} (c : Cocone F) (n : ℕ) (x : F.obj n) :
    toCocone c (incl (X := fun k => F.obj k) (fun k => (F.map (homOfLE k.le_succ)).hom) n x) =
      c.ι.app n x := by
  rw [incl_apply, toCocone_mkCyl]

@[simp]
theorem toCocone_comp_incl {F : ℕ ⥤ TopCat.{u}} (c : Cocone F) (n : ℕ) :
    (toCocone c).comp (incl (X := fun k => F.obj k) (fun k => (F.map (homOfLE k.le_succ)).hom) n) =
      (c.ι.app n).hom :=
  ContinuousMap.ext (toCocone_incl c n)

/-- The natural transformation from the diagram of finite telescope stages to `F : ℕ ⥤ TopCat`
given at level `n` by `stageProj`. -/
private def stageProjNatTrans (F : ℕ ⥤ TopCat.{u}) :
    TopCat.subspaceDiagram
      (stage_mono (X := fun n => F.obj n) (f := fun n => (F.map (homOfLE n.le_succ)).hom)) ⟶ F :=
  NatTrans.ofSequence
    (fun n => TopCat.ofHom (stageProj (X := fun k => F.obj k)
      (fun k => (F.map (homOfLE k.le_succ)).hom) n))
    fun n => by
      ext z
      exact stageProj_inclusion n z

private lemma stageColimit_map_stageProjNatTrans {F : ℕ ⥤ TopCat.{u}} (c : Cocone F) :
    ((TopCat.isColimitOfIsCoherentWith
      (stage_mono (X := fun n => F.obj n) (f := fun n => (F.map (homOfLE n.le_succ)).hom))
      iUnion_stage isCoherentWith_range_stage).map c (stageProjNatTrans F)).hom =
      toCocone c := by
  let b : ∀ n, C(F.obj n, F.obj (n + 1)) := fun n => (F.map (homOfLE n.le_succ)).hom
  let hcTel := TopCat.isColimitOfIsCoherentWith (stage_mono (f := b)) iUnion_stage
    isCoherentWith_range_stage
  refine hom_ext fun m p => ?_
  obtain ⟨s, x⟩ := p
  let z : (TopCat.subspaceDiagram (stage_mono (f := b))).obj (m + 1) :=
    ⟨mkCyl b m (s, x), mkCyl_mem_stage_iff.2 (Or.inl m.lt_succ_self)⟩
  have h1 : (hcTel.map c (stageProjNatTrans F)) (mkCyl b m (s, x)) =
      c.ι.app (m + 1) ((stageProjNatTrans F).app (m + 1) z) :=
    ConcreteCategory.congr_hom (hcTel.ι_map c (stageProjNatTrans F) (m + 1)) z
  have hαz : (stageProjNatTrans F).app (m + 1) z = stageProj b (m + 1) z :=
    ConcreteCategory.congr_hom (NatTrans.ofSequence_app _ _ (m + 1)) z
  have h2 : (stageProjNatTrans F).app (m + 1) z = F.map (homOfLE m.le_succ) x :=
    hαz.trans ((stageProj_mkCyl (X := fun k => F.obj k) (f := b) m.le_succ s x).trans
      (by rw [bondOfLE_succ]))
  have h3 : c.ι.app (m + 1) (F.map (homOfLE m.le_succ) x) = c.ι.app m x :=
    ConcreteCategory.congr_hom (c.w (homOfLE m.le_succ)) x
  exact h1.trans ((congrArg (c.ι.app (m + 1)) h2).trans
    (h3.trans (toCocone_mkCyl c m (s, x)).symm))

/-- **Comparison between the mapping telescope and a sequential colimit of cofibrations.** Let
`F : ℕ ⥤ TopCat` be a sequence whose bonding maps are embeddings with images having the homotopy
extension property, and let `c` be a colimit cocone of `F`. Then `toCocone c` is a homotopy
equivalence from the mapping telescope of `F` to `c.pt`. -/
def colimitHomotopyEquiv {F : ℕ ⥤ TopCat.{u}} {c : Cocone F} (hc : IsColimit c)
    (hF : ∀ n : ℕ, IsEmbedding (F.map (homOfLE n.le_succ)))
    (hFh : ∀ n : ℕ, HasHomotopyExtensionProperty (Set.range (F.map (homOfLE n.le_succ)))) :
    MappingTelescope (X := fun n => F.obj n) (fun n => (F.map (homOfLE n.le_succ)).hom) ≃ₕ c.pt :=
  let b : ∀ n, C(F.obj n, F.obj (n + 1)) := fun n => (F.map (homOfLE n.le_succ)).hom
  let hcTel := TopCat.isColimitOfIsCoherentWith (stage_mono (f := b)) iUnion_stage
    isCoherentWith_range_stage
  have hα (n : ℕ) : ∃ e : (TopCat.subspaceDiagram (stage_mono (f := b))).obj n ≃ₕ F.obj n,
      e.toFun = ((stageProjNatTrans F).app n).hom :=
    ⟨(stageHomotopyEquiv b n).symm,
      (stageHomotopyEquiv_invFun n).trans
        (congrArg TopCat.Hom.hom (NatTrans.ofSequence_app _ _ n)).symm⟩
  let E : MappingTelescope b ≃ₕ c.pt := cofibrationTowerHomotopyEquiv
    (fun n => Topology.IsEmbedding.inclusion (stage_mono (f := b) n.le_succ))
    (fun n => by
      rw [TopCat.range_subspaceDiagram_map]
      exact hasHomotopyExtensionProperty_stage (f := b) n)
    hF hFh (stageProjNatTrans F) hα hcTel hc
  have hE : E.toFun = toCocone c :=
    (cofibrationTowerHomotopyEquiv_toFun _ _ _ _ _ _ _ _).trans
      (stageColimit_map_stageProjNatTrans c)
  { toFun := toCocone c
    invFun := E.invFun
    left_inv := hE ▸ E.left_inv
    right_inv := hE ▸ E.right_inv }

@[simp]
theorem colimitHomotopyEquiv_toFun {F : ℕ ⥤ TopCat.{u}} {c : Cocone F} (hc : IsColimit c)
    (hF : ∀ n : ℕ, IsEmbedding (F.map (homOfLE n.le_succ)))
    (hFh : ∀ n : ℕ, HasHomotopyExtensionProperty (Set.range (F.map (homOfLE n.le_succ)))) :
    (colimitHomotopyEquiv hc hF hFh).toFun = toCocone c :=
  (rfl)

/-- The canonical projection from the mapping telescope of an increasing sequence of subsets
`A : ℕ → Set Y` to the ambient space `Y`. -/
def toUnion {Y : Type u} [TopologicalSpace Y] {A : ℕ → Set Y} (hA : Monotone A) :
    C(MappingTelescope (X := fun n => A n)
      (fun n => ⟨Set.inclusion (hA n.le_succ), continuous_inclusion _⟩), Y) :=
  toCocone (TopCat.subspaceCocone hA)

@[simp]
theorem toUnion_mkCyl {Y : Type u} [TopologicalSpace Y] {A : ℕ → Set Y} (hA : Monotone A)
    (n : ℕ) (p : I × A n) :
    toUnion hA (mkCyl (X := fun k => A k)
      (fun k => ⟨Set.inclusion (hA k.le_succ), continuous_inclusion _⟩) n p) = p.2.val :=
  toCocone_mkCyl (TopCat.subspaceCocone hA) n p

theorem toUnion_incl {Y : Type u} [TopologicalSpace Y] {A : ℕ → Set Y} (hA : Monotone A)
    (n : ℕ) (x : A n) :
    toUnion hA (incl (X := fun k => A k)
      (fun k => ⟨Set.inclusion (hA k.le_succ), continuous_inclusion _⟩) n x) = x.val :=
  toCocone_incl (TopCat.subspaceCocone hA) n x

@[simp]
theorem toUnion_comp_incl {Y : Type u} [TopologicalSpace Y] {A : ℕ → Set Y} (hA : Monotone A)
    (n : ℕ) :
    (toUnion hA).comp (incl (X := fun k => A k)
      (fun k => ⟨Set.inclusion (hA k.le_succ), continuous_inclusion _⟩) n) =
      ⟨Subtype.val, continuous_subtypeVal⟩ :=
  ContinuousMap.ext (toUnion_incl hA n)

/-- **Comparison between the mapping telescope and a coherent union of cofibrations.** Let `Y` be
covered by an increasing sequence of subsets `A n`, each having the homotopy extension property in
`A (n + 1)`, and suppose `Y` carries the topology coherent with the `A n`. Then `toUnion hA` is a
homotopy equivalence from the mapping telescope of the inclusions `A n → A (n + 1)` to `Y`. -/
def unionHomotopyEquiv {Y : Type u} [TopologicalSpace Y] {A : ℕ → Set Y} (hA : Monotone A)
    (hAY : ⋃ n, A n = Set.univ) (hAc : Topology.IsCoherentWith (Set.range A))
    (hAH : ∀ n, HasHomotopyExtensionProperty ((↑) ⁻¹' A n : Set (A (n + 1)))) :
    MappingTelescope (X := fun n => A n)
      (fun n => ⟨Set.inclusion (hA n.le_succ), continuous_inclusion _⟩) ≃ₕ Y :=
  colimitHomotopyEquiv (TopCat.isColimitOfIsCoherentWith hA hAY hAc)
    (fun n => Topology.IsEmbedding.inclusion (hA n.le_succ)) fun n => by
      rw [TopCat.range_subspaceDiagram_map]
      exact hAH n

@[simp]
theorem unionHomotopyEquiv_toFun {Y : Type u} [TopologicalSpace Y] {A : ℕ → Set Y}
    (hA : Monotone A) (hAY : ⋃ n, A n = Set.univ) (hAc : Topology.IsCoherentWith (Set.range A))
    (hAH : ∀ n, HasHomotopyExtensionProperty ((↑) ⁻¹' A n : Set (A (n + 1)))) :
    (unionHomotopyEquiv hA hAY hAc hAH).toFun = toUnion hA :=
  (rfl)

end ColimitAndUnion

end TauCeti.MappingTelescope
