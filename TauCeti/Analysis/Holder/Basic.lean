/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Topology.ContinuousMap.Bounded.Normed
import Mathlib.Topology.MetricSpace.HolderNorm

/-!
# Bundled zero-order Hölder maps

This file packages Mathlib's global Hölder predicate `MemHolder` together with bounded
continuous maps.  It is a small first step toward the PDE roadmap's Hölder spaces
`C^{k,α}(Ω)`: the zero-order case records bounded continuous functions whose values satisfy
a global Hölder estimate on the domain.

The Hölder seminorm itself is not redefined here.  We reuse Mathlib's `nnHolderNorm` and
add only the bundled carrier, algebraic closure operations, restriction to a set via its
subtype, and the combined quantity `‖f‖ + [f]_{C^{0,α}}` that later normed-space work can
promote to the actual norm.

## Main declarations

* `TauCeti.HolderMap`: bounded continuous maps with `MemHolder r`.
* `TauCeti.HolderMap.ofHolderWith`: build a bundled map from an explicit Hölder constant.
* `TauCeti.HolderMap.restrict`: restrict a Hölder map to a subtype.
* `TauCeti.HolderMap.holderSize`: the sup norm plus Mathlib's Hölder seminorm.
-/

namespace TauCeti

open NNReal
open scoped BoundedContinuousFunction

variable {α β 𝕜 : Type*}

/-- Bounded continuous maps whose underlying function is globally `r`-Hölder.

This is the zero-order carrier for future Hölder spaces.  It deliberately stores a
`BoundedContinuousFunction`, so boundedness and continuity are inherited from Mathlib while
the Hölder control is provided by `MemHolder`. -/
structure HolderMap (α : Type*) (β : Type*) [MetricSpace α] [NormedAddCommGroup β]
    (r : ℝ≥0) where
  /-- The underlying bounded continuous map. -/
  toBoundedContinuousFunction : α →ᵇ β
  /-- The underlying function has a finite `r`-Hölder constant. -/
  memHolder' : MemHolder r (toBoundedContinuousFunction : α → β)

namespace HolderMap

variable [MetricSpace α] [NormedAddCommGroup β] {r : ℝ≥0}

instance : CoeFun (HolderMap α β r) fun _ => α → β :=
  ⟨fun f => f.toBoundedContinuousFunction⟩

/-- The underlying bounded continuous map of a bundled Hölder map. -/
abbrev toBCF (f : HolderMap α β r) : α →ᵇ β :=
  f.toBoundedContinuousFunction

@[simp]
lemma toBCF_apply (f : HolderMap α β r) (x : α) : f.toBCF x = f x :=
  rfl

@[simp]
lemma coe_toBCF (f : HolderMap α β r) : (f.toBCF : α → β) = f :=
  rfl

/-- Two bundled Hölder maps are equal if their pointwise values are equal. -/
@[ext]
lemma ext {f g : HolderMap α β r} (h : ∀ x, f x = g x) : f = g := by
  cases f
  cases g
  congr
  exact BoundedContinuousFunction.ext h

/-- The underlying map of a bundled Hölder map is continuous. -/
lemma continuous (f : HolderMap α β r) : Continuous f :=
  f.toBCF.continuous

/-- A bundled Hölder map has a finite Hölder seminorm in Mathlib's sense. -/
lemma memHolder (f : HolderMap α β r) : MemHolder r (f : α → β) :=
  f.memHolder'

/-- The canonical Hölder estimate using Mathlib's least finite Hölder constant. -/
lemma holderWith (f : HolderMap α β r) :
    HolderWith (nnHolderNorm r (f : α → β)) r (f : α → β) :=
  f.memHolder.holderWith

/-- Build a bundled Hölder map from a bounded continuous map and an explicit Hölder constant. -/
def ofHolderWith (f : α →ᵇ β) {C : ℝ≥0} (hf : HolderWith C r (f : α → β)) :
    HolderMap α β r where
  toBoundedContinuousFunction := f
  memHolder' := hf.memHolder

@[simp]
lemma ofHolderWith_apply (f : α →ᵇ β) {C : ℝ≥0}
    (hf : HolderWith C r (f : α → β)) (x : α) :
    ofHolderWith f hf x = f x :=
  rfl

/-- A bounded continuous constant map as a bundled Hölder map. -/
def const (α : Type*) [MetricSpace α] (r : ℝ≥0) (b : β) : HolderMap α β r where
  toBoundedContinuousFunction := BoundedContinuousFunction.const α b
  memHolder' := memHolder_const

@[simp]
lemma const_apply (b : β) (x : α) : const α r b x = b :=
  rfl

instance : Zero (HolderMap α β r) :=
  ⟨const α r 0⟩

@[simp]
lemma zero_apply (x : α) : (0 : HolderMap α β r) x = 0 :=
  rfl

instance : Add (HolderMap α β r) where
  add f g :=
    { toBoundedContinuousFunction := f.toBCF + g.toBCF
      memHolder' := by
        simpa [BoundedContinuousFunction.coe_add] using f.memHolder.add g.memHolder }

@[simp]
lemma add_apply (f g : HolderMap α β r) (x : α) : (f + g) x = f x + g x :=
  rfl

noncomputable instance : Neg (HolderMap α β r) where
  neg f :=
    { toBoundedContinuousFunction := -f.toBCF
      memHolder' := by
        obtain ⟨C, hC⟩ := f.memHolder
        exact ⟨C, by
          intro x y
          simpa [BoundedContinuousFunction.coe_neg] using hC x y⟩ }

@[simp]
lemma neg_apply (f : HolderMap α β r) (x : α) : (-f) x = -f x :=
  rfl

noncomputable instance : Sub (HolderMap α β r) where
  sub f g := f + -g

@[simp]
lemma sub_apply (f g : HolderMap α β r) (x : α) : (f - g) x = f x - g x := by
  -- `Sub` is defined through the already-proved `Add` and `Neg` closure operations.
  change (f + -g : HolderMap α β r) x = f x - g x
  simp [sub_eq_add_neg]

noncomputable instance : AddCommGroup (HolderMap α β r) where
  add_assoc f g h := by
    ext x
    simp [add_assoc]
  zero_add f := by
    ext x
    simp
  add_zero f := by
    ext x
    simp
  neg_add_cancel f := by
    ext x
    simp
  add_comm f g := by
    ext x
    simp [add_comm]
  nsmul := nsmulRec
  zsmul := zsmulRec

noncomputable instance [SeminormedRing 𝕜] [Module 𝕜 β] [IsBoundedSMul 𝕜 β] :
    SMul 𝕜 (HolderMap α β r) where
  smul c f :=
    { toBoundedContinuousFunction := c • f.toBCF
      memHolder' := by
        rw [BoundedContinuousFunction.coe_smul]
        exact f.memHolder.smul (c := c) }

@[simp]
lemma smul_apply [SeminormedRing 𝕜] [Module 𝕜 β] [IsBoundedSMul 𝕜 β] (c : 𝕜)
    (f : HolderMap α β r) (x : α) :
    (c • f) x = c • f x :=
  rfl

noncomputable instance [SeminormedRing 𝕜] [Module 𝕜 β] [IsBoundedSMul 𝕜 β] :
    Module 𝕜 (HolderMap α β r) where
  one_smul f := by
    ext x
    simp
  mul_smul c d f := by
    ext x
    simp [mul_smul]
  smul_zero c := by
    ext x
    simp
  smul_add c f g := by
    ext x
    simp [smul_add]
  add_smul c d f := by
    ext x
    simp [add_smul]
  zero_smul f := by
    ext x
    simp

/-- Restrict a bundled Hölder map to a subtype.  This is the form used for maps on a domain
`Ω`, represented as functions on the type `Ω`. -/
noncomputable def restrict (f : HolderMap α β r) (s : Set α) : HolderMap s β r where
  toBoundedContinuousFunction := f.toBCF.restrict s
  memHolder' := by
    exact ⟨nnHolderNorm r (f : α → β),
      HolderWith.restrict_iff.mpr (f.holderWith.holderOnWith s)⟩

@[simp]
lemma restrict_apply (f : HolderMap α β r) (s : Set α) (x : s) :
    f.restrict s x = f x :=
  rfl

@[simp]
lemma restrict_zero (s : Set α) : (0 : HolderMap α β r).restrict s = 0 := by
  ext x
  simp

@[simp]
lemma restrict_add (f g : HolderMap α β r) (s : Set α) :
    (f + g).restrict s = f.restrict s + g.restrict s := by
  ext x
  simp

@[simp]
lemma restrict_neg (f : HolderMap α β r) (s : Set α) :
    (-f).restrict s = -f.restrict s := by
  ext x
  simp

@[simp]
lemma restrict_sub (f g : HolderMap α β r) (s : Set α) :
    (f - g).restrict s = f.restrict s - g.restrict s := by
  ext x
  simp

@[simp]
lemma restrict_smul [SeminormedRing 𝕜] [Module 𝕜 β] [IsBoundedSMul 𝕜 β]
    (c : 𝕜) (f : HolderMap α β r) (s : Set α) :
    (c • f).restrict s = c • f.restrict s := by
  ext x
  simp

/-- The sup norm of the underlying bounded continuous map. -/
noncomputable def supNorm (f : HolderMap α β r) : ℝ :=
  ‖f.toBCF‖

lemma norm_apply_le_supNorm (f : HolderMap α β r) (x : α) : ‖f x‖ ≤ f.supNorm :=
  f.toBCF.norm_coe_le_norm x

/-- The Hölder seminorm of a bundled Hölder map, reusing Mathlib's `nnHolderNorm`. -/
noncomputable def holderSeminorm (f : HolderMap α β r) : ℝ≥0 :=
  nnHolderNorm r (f : α → β)

/-- The zero-order Hölder size `‖f‖∞ + [f]_{C^{0,α}}`.

This is recorded as a named quantity before installing a normed-space structure, so later
files can state estimates without unfolding the carrier or Mathlib's seminorm definition. -/
noncomputable def holderSize (f : HolderMap α β r) : ℝ :=
  f.supNorm + f.holderSeminorm

lemma supNorm_nonneg (f : HolderMap α β r) : 0 ≤ f.supNorm :=
  norm_nonneg _

lemma holderSeminorm_nonneg (f : HolderMap α β r) : 0 ≤ (f.holderSeminorm : ℝ) :=
  NNReal.coe_nonneg _

lemma supNorm_le_holderSize (f : HolderMap α β r) : f.supNorm ≤ f.holderSize := by
  exact le_add_of_nonneg_right f.holderSeminorm_nonneg

lemma holderSeminorm_le_holderSize (f : HolderMap α β r) :
    (f.holderSeminorm : ℝ) ≤ f.holderSize := by
  exact le_add_of_nonneg_left f.supNorm_nonneg

lemma holderSize_nonneg (f : HolderMap α β r) : 0 ≤ f.holderSize :=
  add_nonneg f.supNorm_nonneg f.holderSeminorm_nonneg

/-- Restriction to a subtype does not increase the sup norm. -/
lemma supNorm_restrict_le (f : HolderMap α β r) (s : Set α) :
    supNorm (f.restrict s) ≤ f.supNorm := by
  rw [supNorm]
  exact BoundedContinuousFunction.norm_le f.supNorm_nonneg |>.2 fun x =>
    f.norm_apply_le_supNorm x

/-- Restriction to a subtype does not increase the Hölder seminorm. -/
lemma holderSeminorm_restrict_le (f : HolderMap α β r) (s : Set α) :
    holderSeminorm (f.restrict s) ≤ f.holderSeminorm := by
  exact (HolderWith.restrict_iff.mpr (f.holderWith.holderOnWith s)).nnholderNorm_le

/-- Restriction to a subtype does not increase the zero-order Hölder size. -/
lemma holderSize_restrict_le (f : HolderMap α β r) (s : Set α) :
    holderSize (f.restrict s) ≤ f.holderSize := by
  rw [holderSize, holderSize]
  have hsup := supNorm_restrict_le f s
  have hholder := holderSeminorm_restrict_le f s
  have hholder_real :
      ((f.restrict s).holderSeminorm : ℝ) ≤ f.holderSeminorm := by
    exact_mod_cast hholder
  linarith

@[simp]
lemma holderSeminorm_const (b : β) :
    holderSeminorm (const α r b) = 0 := by
  exact ((memHolder_const' : MemHolder r (fun _ : α => b)).nnHolderNorm_eq_zero).2
    fun _ _ => rfl

@[simp]
lemma holderSize_zero : holderSize (0 : HolderMap α β r) = 0 := by
  have hzero : (0 : HolderMap α β r) = const α r (0 : β) := rfl
  have hsup : supNorm (0 : HolderMap α β r) = 0 := by
    rw [hzero, supNorm]
    have hbcf : (const α r (0 : β)).toBCF = 0 := by
      ext x
      rfl
    rw [hbcf]
    simp
  have hholder : holderSeminorm (0 : HolderMap α β r) = 0 := by
    rw [hzero]
    exact holderSeminorm_const (α := α) (r := r) (0 : β)
  rw [holderSize, hsup, hholder]
  norm_num

/-- The sup norm is subadditive on bundled Hölder maps. -/
lemma supNorm_add_le (f g : HolderMap α β r) :
    supNorm (f + g) ≤ f.supNorm + g.supNorm := by
  rw [supNorm, supNorm, supNorm]
  exact norm_add_le f.toBCF g.toBCF

/-- Scalar multiplication grows the sup norm by at most the scalar norm. -/
lemma supNorm_smul_le [SeminormedRing 𝕜] [Module 𝕜 β] [IsBoundedSMul 𝕜 β] (c : 𝕜)
    (f : HolderMap α β r) :
    supNorm (c • f) ≤ ‖c‖ * f.supNorm := by
  rw [supNorm, supNorm]
  exact norm_smul_le c f.toBCF

/-- The Hölder seminorm is subadditive on bundled Hölder maps. -/
lemma holderSeminorm_add_le (f g : HolderMap α β r) :
    holderSeminorm (f + g) ≤ f.holderSeminorm + g.holderSeminorm := by
  exact f.memHolder.nnHolderNorm_add_le g.memHolder

/-- Scalar multiplication scales the Hölder seminorm by `‖c‖₊`. -/
lemma holderSeminorm_smul [NormedRing 𝕜] [Module 𝕜 β] [NormSMulClass 𝕜 β]
    (c : 𝕜) (f : HolderMap α β r) :
    holderSeminorm (c • f) = ‖c‖₊ * f.holderSeminorm := by
  exact f.memHolder.nnHolderNorm_smul c

/-- Scalar multiplication grows the Hölder seminorm by at most `‖c‖₊`. -/
lemma holderSeminorm_smul_le [SeminormedRing 𝕜] [Module 𝕜 β] [IsBoundedSMul 𝕜 β]
    (c : 𝕜) (f : HolderMap α β r) :
    holderSeminorm (c • f) ≤ ‖c‖₊ * f.holderSeminorm := by
  -- The left side unfolds through the bundled `SMul` and coercion to the function
  -- seminorm used by Mathlib's `HolderWith.nnholderNorm_le`.
  change nnHolderNorm r (c • (f : α → β)) ≤ ‖c‖₊ * nnHolderNorm r (f : α → β)
  simpa [mul_comm] using (f.holderWith.smul c).nnholderNorm_le

/-- The zero-order Hölder size is subadditive on bundled Hölder maps. -/
lemma holderSize_add_le (f g : HolderMap α β r) :
    holderSize (f + g) ≤ f.holderSize + g.holderSize := by
  rw [holderSize, holderSize, holderSize]
  have hsup := supNorm_add_le f g
  have hholder := holderSeminorm_add_le f g
  have hholder_real :
      ((f + g).holderSeminorm : ℝ) ≤ f.holderSeminorm + g.holderSeminorm := by
    exact_mod_cast hholder
  linarith

/-- Scalar multiplication grows the zero-order Hölder size by at most the scalar norm. -/
lemma holderSize_smul_le [SeminormedRing 𝕜] [Module 𝕜 β] [IsBoundedSMul 𝕜 β] (c : 𝕜)
    (f : HolderMap α β r) :
    holderSize (c • f) ≤ ‖c‖ * f.holderSize := by
  rw [holderSize, holderSize]
  have hsup := supNorm_smul_le c f
  have hholder := holderSeminorm_smul_le c f
  have hholder_real : ((c • f).holderSeminorm : ℝ) ≤ ‖c‖ * f.holderSeminorm := by
    exact_mod_cast hholder
  nlinarith [f.holderSeminorm_nonneg, norm_nonneg c]

end HolderMap

end TauCeti
