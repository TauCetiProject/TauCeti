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

/-- Rejoining two coordinate blocks appends them. -/
@[simp]
theorem splitCoords_symm_apply (x : (Fin n → M) × (Fin m → M)) :
    (splitCoords (𝕜 := 𝕜) n m).symm x = Fin.append x.1 x.2 := by
  simp [ContinuousLinearEquiv.symm_apply_eq]

/-- Splitting an appended vector recovers its two blocks. The high priority lets `simp` use
this before `splitCoords_apply`: with equal block sizes, `simp` would otherwise rewrite
`Fin.natAdd` to `Fin.addNat`, where `Fin.append_right` no longer applies. -/
@[simp high]
theorem splitCoords_append (a : Fin n → M) (b : Fin m → M) :
    splitCoords (𝕜 := 𝕜) n m (Fin.append a b) = (a, b) :=
  Prod.ext (funext <| Fin.append_left a b) (funext <| Fin.append_right a b)

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
  refine ⟨fun hx i hi ↦ ?_, fun hx ↦ funext fun i ↦ hx _ (Nat.le_add_right _ _)⟩
  simpa [Nat.add_sub_cancel' hi] using congrFun hx ⟨i - d, by omega⟩

/-- Rejoining blocks split at `d` places the initial block in the first `d` coordinates. -/
@[simp]
theorem splitAt_symm_apply_castLE (h : d ≤ n) (p : (Fin d → M) × (Fin (n - d) → M))
    (i : Fin d) : (splitAt (𝕜 := 𝕜) h).symm p (Fin.castLE h i) = p.1 i :=
  congrFun (congrArg Prod.fst ((splitAt (𝕜 := 𝕜) h).apply_symm_apply p)) i

/-- Rejoining blocks split at `d` places the final block in the coordinates starting at `d`. -/
@[simp]
theorem splitAt_symm_apply_mk_add (h : d ≤ n) (p : (Fin d → M) × (Fin (n - d) → M))
    (i : Fin (n - d)) : (splitAt (𝕜 := 𝕜) h).symm p ⟨d + i.val, by omega⟩ = p.2 i :=
  congrFun (congrArg Prod.snd ((splitAt (𝕜 := 𝕜) h).apply_symm_apply p)) i

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

/-- Regrouping rejoins, at `d + e`, the appended initial blocks and the reindexed appended
final blocks. -/
private theorem productCoords_apply_eq (hd : d ≤ n) (he : e ≤ m)
    (x : (Fin n → M) × (Fin m → M)) :
    productCoords (𝕜 := 𝕜) hd he x = (splitAt (𝕜 := 𝕜) (by omega : d + e ≤ n + m)).symm
      (Fin.append (splitAt (𝕜 := 𝕜) hd x.1).1 (splitAt (𝕜 := 𝕜) he x.2).1,
        Fin.append (splitAt (𝕜 := 𝕜) hd x.1).2 (splitAt (𝕜 := 𝕜) he x.2).2 ∘
          Fin.cast (by omega)) := by
  simp only [productCoords, ContinuousLinearEquiv.trans_apply,
    ContinuousLinearEquiv.prodCongr_apply, ContinuousLinearEquiv.coe_prodProdProdComm,
    Equiv.prodProdProdComm_apply, splitCoords_symm_apply]
  -- Reindexing a constant family along `finCongr` is precomposition with `Fin.cast`.
  rfl

/-- The first block of regrouped coordinates is the first vector's initial block. -/
@[simp]
theorem productCoords_apply_fst_initial (hd : d ≤ n) (he : e ≤ m)
    (x : (Fin n → M) × (Fin m → M)) (i : Fin d) :
    productCoords (𝕜 := 𝕜) hd he x ⟨i.val, by omega⟩ = x.1 (Fin.castLE hd i) := by
  rw [productCoords_apply_eq]
  -- Here and in the next three proofs, the stated index is by definition the image under
  -- `Fin.castLE` or `Fin.mk` of the block index passed to the `splitAt.symm` lemma.
  exact (splitAt_symm_apply_castLE _ _ (Fin.castAdd e i)).trans (by simp)

/-- The second block of regrouped coordinates is the second vector's initial block. -/
@[simp]
theorem productCoords_apply_snd_initial (hd : d ≤ n) (he : e ≤ m)
    (x : (Fin n → M) × (Fin m → M)) (i : Fin e) :
    productCoords (𝕜 := 𝕜) hd he x ⟨d + i.val, by omega⟩ = x.2 (Fin.castLE he i) := by
  rw [productCoords_apply_eq]
  exact (splitAt_symm_apply_castLE _ _ (Fin.natAdd d i)).trans (by simp)

/-- The third block of regrouped coordinates is the first vector's final block. -/
@[simp]
theorem productCoords_apply_fst_final (hd : d ≤ n) (he : e ≤ m)
    (x : (Fin n → M) × (Fin m → M)) (i : Fin (n - d)) :
    productCoords (𝕜 := 𝕜) hd he x ⟨d + e + i.val, by omega⟩ =
      x.1 ⟨d + i.val, by omega⟩ := by
  rw [productCoords_apply_eq]
  exact (splitAt_symm_apply_mk_add _ _ (Fin.cast (by omega) (Fin.castAdd (m - e) i))).trans
    (by simp)

/-- The fourth block of regrouped coordinates is the second vector's final block. -/
@[simp]
theorem productCoords_apply_snd_final (hd : d ≤ n) (he : e ≤ m)
    (x : (Fin n → M) × (Fin m → M)) (i : Fin (m - e)) :
    productCoords (𝕜 := 𝕜) hd he x ⟨d + e + (n - d) + i.val, by omega⟩ =
      x.2 ⟨e + i.val, by omega⟩ := by
  simp only [productCoords_apply_eq, Nat.add_assoc (d + e)]
  exact (splitAt_symm_apply_mk_add _ _ (Fin.cast (by omega) (Fin.natAdd (n - d) i))).trans
    (by simp)

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
