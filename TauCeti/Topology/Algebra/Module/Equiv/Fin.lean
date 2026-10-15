/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Algebra.Module.Equiv.Pi
public import Mathlib.Topology.Algebra.Module.Equiv.Prod
import Mathlib.Logic.Equiv.Fin.Basic

/-!
# Splitting and regrouping finite coordinates

Continuous linear equivalences split vectors indexed by `Fin (n + m)` into two blocks,
split `Fin n` at an index `d ≤ n`, and regroup the initial blocks of a pair of vectors
before the remaining blocks. The vanishing characterizations identify products of
coordinate subspaces with a single coordinate subspace, as needed for product charts.

The constructions combine Mathlib's `ContinuousLinearEquiv.piCongrLeft`,
`sumPiEquivProdPi`, and `prodProdProdComm` with finite-index equivalences.
-/

public section

namespace TauCeti

variable {𝕜 M : Type*} [Semiring 𝕜] [AddCommMonoid M] [Module 𝕜 M]
  [TopologicalSpace M] {n m d e : ℕ}

/-- Split a concatenated vector into its two coordinate blocks. -/
def splitCoords (n m : ℕ) :
    (Fin (n + m) → M) ≃L[𝕜] (Fin n → M) × (Fin m → M) :=
  (ContinuousLinearEquiv.piCongrLeft 𝕜 (fun _ : Fin (n + m) ↦ M)
    finSumFinEquiv).symm.trans
      (ContinuousLinearEquiv.sumPiEquivProdPi 𝕜 (Fin n) (Fin m) (fun _ ↦ M))

/-- The two blocks of a split vector are its initial and final coordinates. -/
@[simp]
theorem splitCoords_apply (x : Fin (n + m) → M) :
    splitCoords (𝕜 := 𝕜) n m x =
      (fun i ↦ x (Fin.castAdd m i), fun i ↦ x (Fin.natAdd n i)) :=
  (rfl)

/-- Split a vector into its first `d` coordinates and its remaining coordinates. -/
def splitAt (h : d ≤ n) :
    (Fin n → M) ≃L[𝕜] (Fin d → M) × (Fin (n - d) → M) :=
  (ContinuousLinearEquiv.piCongrLeft 𝕜 (fun _ : Fin n ↦ M)
    (finCongr (Nat.add_sub_of_le h))).symm.trans (splitCoords d (n - d))

/-- The initial block of a vector split at `d` consists of its first `d` coordinates. -/
@[simp]
theorem splitAt_fst_apply (h : d ≤ n) (x : Fin n → M) (i : Fin d) :
    (splitAt (𝕜 := 𝕜) h x).1 i = x (Fin.castLE h i) :=
  (rfl)

/-- The final block of a vector split at `d` consists of its coordinates starting at `d`. -/
@[simp]
theorem splitAt_snd_apply (h : d ≤ n) (x : Fin n → M) (i : Fin (n - d)) :
    (splitAt (𝕜 := 𝕜) h x).2 i = x ⟨d + i.val, by omega⟩ :=
  (rfl)

/-- The final block vanishes exactly when all coordinates at or beyond `d` vanish. -/
@[simp]
theorem splitAt_snd_eq_zero_iff (h : d ≤ n) (x : Fin n → M) :
    (splitAt (𝕜 := 𝕜) h x).2 = 0 ↔ ∀ i : Fin n, d ≤ i.val → x i = 0 := by
  constructor
  · intro hx i hi
    have hxi := congrFun hx ⟨i.val - d, by omega⟩
    rw [splitAt_snd_apply] at hxi
    convert hxi using 1
    congr 1
    apply Fin.ext
    dsimp
    omega
  · intro hx
    ext i
    rw [splitAt_snd_apply]
    exact hx _ (by dsimp; omega)

/-- Regroup two vectors so their initial blocks of sizes `d` and `e` come first,
followed by both remaining blocks. This identifies products of coordinate subspaces with
the coordinate subspace of dimension `d + e`. -/
def productCoords (hd : d ≤ n) (he : e ≤ m) :
    ((Fin n → M) × (Fin m → M)) ≃L[𝕜] (Fin (n + m) → M) :=
  ((splitAt hd).prodCongr (splitAt he)).trans
    ((ContinuousLinearEquiv.prodProdProdComm 𝕜 _ _ _ _).trans
      (((splitCoords d e).symm.prodCongr
        ((splitCoords (n - d) (m - e)).symm.trans
          (ContinuousLinearEquiv.piCongrLeft 𝕜
            (fun _ : Fin (n + m - (d + e)) ↦ M) (finCongr (by omega))))).trans
        (splitAt (by omega : d + e ≤ n + m)).symm))

/-- The first block of regrouped coordinates is the first vector's initial block. -/
@[simp]
theorem productCoords_apply_fst_initial (hd : d ≤ n) (he : e ≤ m)
    (x : (Fin n → M) × (Fin m → M)) (i : Fin d) :
    productCoords (𝕜 := 𝕜) hd he x ⟨i.val, by omega⟩ = x.1 (Fin.castLE hd i) := by
  have h := congrFun (congrArg Prod.fst
    ((splitCoords (𝕜 := 𝕜) d e).apply_symm_apply
      ((splitAt (𝕜 := 𝕜) hd x.1).1, (splitAt (𝕜 := 𝕜) he x.2).1))) i
  simp only [splitCoords_apply, splitAt_fst_apply] at h
  calc
    _ = (splitAt (𝕜 := 𝕜) (by omega : d + e ≤ n + m)
        (productCoords (𝕜 := 𝕜) hd he x)).1 (Fin.castAdd e i) :=
      (splitAt_fst_apply _ _ _).symm
    _ = _ := by
      simpa only [productCoords, ContinuousLinearEquiv.trans_apply,
        ContinuousLinearEquiv.apply_symm_apply, ContinuousLinearEquiv.prodCongr_apply,
        ContinuousLinearEquiv.coe_prodProdProdComm, Equiv.prodProdProdComm, Equiv.coe_fn_mk] using h

/-- The second block of regrouped coordinates is the second vector's initial block. -/
@[simp]
theorem productCoords_apply_snd_initial (hd : d ≤ n) (he : e ≤ m)
    (x : (Fin n → M) × (Fin m → M)) (i : Fin e) :
    productCoords (𝕜 := 𝕜) hd he x ⟨d + i.val, by omega⟩ = x.2 (Fin.castLE he i) := by
  have h := congrFun (congrArg Prod.snd
    ((splitCoords (𝕜 := 𝕜) d e).apply_symm_apply
      ((splitAt (𝕜 := 𝕜) hd x.1).1, (splitAt (𝕜 := 𝕜) he x.2).1))) i
  simp only [splitCoords_apply, splitAt_fst_apply] at h
  calc
    _ = (splitAt (𝕜 := 𝕜) (by omega : d + e ≤ n + m)
        (productCoords (𝕜 := 𝕜) hd he x)).1 (Fin.natAdd d i) :=
      (splitAt_fst_apply _ _ _).symm
    _ = _ := by
      simpa only [productCoords, ContinuousLinearEquiv.trans_apply,
        ContinuousLinearEquiv.apply_symm_apply, ContinuousLinearEquiv.prodCongr_apply,
        ContinuousLinearEquiv.coe_prodProdProdComm, Equiv.prodProdProdComm, Equiv.coe_fn_mk] using h

/-- The third block of regrouped coordinates is the first vector's final block. -/
@[simp]
theorem productCoords_apply_fst_final (hd : d ≤ n) (he : e ≤ m)
    (x : (Fin n → M) × (Fin m → M)) (i : Fin (n - d)) :
    productCoords (𝕜 := 𝕜) hd he x ⟨d + e + i.val, by omega⟩ =
      x.1 ⟨d + i.val, by omega⟩ := by
  have h := congrFun (congrArg Prod.fst
    ((splitCoords (𝕜 := 𝕜) (n - d) (m - e)).apply_symm_apply
      ((splitAt (𝕜 := 𝕜) hd x.1).2, (splitAt (𝕜 := 𝕜) he x.2).2))) i
  simp only [splitCoords_apply, splitAt_snd_apply] at h
  calc
    _ = (splitAt (𝕜 := 𝕜) (by omega : d + e ≤ n + m)
        (productCoords (𝕜 := 𝕜) hd he x)).2 ⟨i.val, by omega⟩ :=
      (splitAt_snd_apply _ _ _).symm
    _ = _ := by
      -- The remaining reindexing casts between equal lengths of the final block.
      simpa [productCoords, Equiv.prodProdProdComm, ContinuousLinearEquiv.piCongrLeft,
        Homeomorph.piCongrLeft, Equiv.piCongrLeft_apply, Fin.castAdd, Fin.castLE,
        Fin.natAdd] using h

/-- The fourth block of regrouped coordinates is the second vector's final block. -/
@[simp]
theorem productCoords_apply_snd_final (hd : d ≤ n) (he : e ≤ m)
    (x : (Fin n → M) × (Fin m → M)) (i : Fin (m - e)) :
    productCoords (𝕜 := 𝕜) hd he x ⟨d + e + (n - d) + i.val, by omega⟩ =
      x.2 ⟨e + i.val, by omega⟩ := by
  have h := congrFun (congrArg Prod.snd
    ((splitCoords (𝕜 := 𝕜) (n - d) (m - e)).apply_symm_apply
      ((splitAt (𝕜 := 𝕜) hd x.1).2, (splitAt (𝕜 := 𝕜) he x.2).2))) i
  simp only [splitCoords_apply, splitAt_snd_apply] at h
  calc
    _ = (splitAt (𝕜 := 𝕜) (by omega : d + e ≤ n + m)
        (productCoords (𝕜 := 𝕜) hd he x)).2 ⟨n - d + i.val, by omega⟩ := by
      simpa only [Nat.add_assoc] using (splitAt_snd_apply
        (𝕜 := 𝕜) (by omega : d + e ≤ n + m)
        (productCoords (𝕜 := 𝕜) hd he x) ⟨n - d + i.val, by omega⟩).symm
    _ = _ := by
      -- The remaining reindexing casts between equal lengths of the final block.
      simpa [productCoords, Equiv.prodProdProdComm, ContinuousLinearEquiv.piCongrLeft,
        Homeomorph.piCongrLeft, Equiv.piCongrLeft_apply, Fin.castAdd, Fin.castLE,
        Fin.natAdd] using h

/-- Regrouped coordinates vanish at or beyond `d + e` exactly when each original
vector vanishes beyond its initial block. -/
theorem productCoords_vanishing_iff (hd : d ≤ n) (he : e ≤ m)
    (x : (Fin n → M) × (Fin m → M)) :
    (∀ i : Fin (n + m), d + e ≤ i.val → productCoords (𝕜 := 𝕜) hd he x i = 0) ↔
      (∀ i : Fin n, d ≤ i.val → x.1 i = 0) ∧
      (∀ i : Fin m, e ≤ i.val → x.2 i = 0) := by
  rw [← splitAt_snd_eq_zero_iff (𝕜 := 𝕜) (by omega : d + e ≤ n + m),
    ← splitAt_snd_eq_zero_iff (𝕜 := 𝕜) hd, ← splitAt_snd_eq_zero_iff (𝕜 := 𝕜) he]
  simp only [productCoords, ContinuousLinearEquiv.trans_apply,
    ContinuousLinearEquiv.apply_symm_apply, ContinuousLinearEquiv.prodCongr_apply]
  rw [ContinuousLinearEquiv.map_eq_zero_iff, ContinuousLinearEquiv.map_eq_zero_iff]
  -- The four-block equivalence sends the constrained blocks to the second pair.
  exact Prod.mk_eq_zero

end TauCeti
