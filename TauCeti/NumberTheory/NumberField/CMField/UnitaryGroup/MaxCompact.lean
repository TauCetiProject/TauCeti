/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.NumberField.CMField.UnitaryGroup.Basic
import TauCeti.Topology.Algebra.Star.Unitary
import TauCeti.LinearAlgebra.Matrix.UnitaryGroup.Basic
import Mathlib.Analysis.CStarAlgebra.Matrix
public import Mathlib.Topology.Algebra.Group.Matrix

/-!
# The standard compact subgroup of an adelic unitary group

For a CM field `E` and a sign vector `s`, the standard compact subgroup of `G(s)` consists of
those elements whose infinite component is unitary for the positive definite identity form and
whose finite component belongs to the integral unitary group `K₀`. Its infinite factor is
`U(diag s) ∩ U(n)`, and hence preserves the positive and negative coordinate subspaces.

This file constructs these subgroups and proves their compactness. They are the compact factors
used in the Iwasawa decomposition of the adelic unitary group. Compactness at infinity follows
by bounding the entries of a unitary matrix at every complex place; compactness of `K₀` is
already available.

The subgroup corresponds to `New.maxCompact` and its compactness to `New.isCompact_maxCompact`
in `src/Lib/Adelic/Witt/IwasawaDecomposition.lean` of [ShortProof], the folder `grh` of
https://github.com/lsernau/grh-lean at commit `72fead102f663d5c7a407964a13dc0cf9d977207`
(Apache 2.0). The proofs here are independent of that formalization.
-/

public section

noncomputable section

open NumberField Matrix
open scoped NumberField.AdeleRing

namespace TauCeti

section Infinite

variable (E : Type*) [Field E] [CharZero E] [Algebra.IsIntegral ℚ E] [IsCMField E]
  {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The infinite compact factor `K_∞(s) = U(diag s) ∩ U(n)`, as a subgroup of `G_∞(s)`. -/
def infiniteAdelicUnitaryGroup.maxCompact (s : ι → ℤˣ) :
    Subgroup (infiniteAdelicUnitaryGroup E s) :=
  (unitarySubgroup (GL ι (InfiniteAdeleRing E))).subgroupOf (infiniteAdelicUnitaryGroup E s)

variable {E}

/-- Membership in the infinite compact factor is unitarity for the identity form. -/
@[simp]
theorem infiniteAdelicUnitaryGroup.mem_maxCompact_iff {s : ι → ℤˣ}
    (g : infiniteAdelicUnitaryGroup E s) :
    g ∈ infiniteAdelicUnitaryGroup.maxCompact E s ↔
      (g : GL ι (InfiniteAdeleRing E)) ∈ unitarySubgroup (GL ι (InfiniteAdeleRing E)) :=
  Iff.rfl

/-- The infinite compact factor is closed in `G_∞(s)`. -/
theorem infiniteAdelicUnitaryGroup.isClosed_maxCompact (s : ι → ℤˣ) :
    IsClosed (infiniteAdelicUnitaryGroup.maxCompact E s :
      Set (infiniteAdelicUnitaryGroup E s)) :=
  (isClosed_unitarySubgroup_units (M := Matrix ι ι (InfiniteAdeleRing E))).preimage
    continuous_subtypeVal

/-- The infinite compact factor is compact for every sign vector. -/
theorem infiniteAdelicUnitaryGroup.isCompact_maxCompact (s : ι → ℤˣ) :
    IsCompact (infiniteAdelicUnitaryGroup.maxCompact E s :
      Set (infiniteAdelicUnitaryGroup E s)) := by
  let B : Set (InfiniteAdeleRing E) :=
    {x | ∀ w, ‖InfinitePlace.Completion.extensionEmbedding w (x w)‖ ≤ 1}
  have hB : IsCompact B := by
    -- The infinite adele topology is the product topology of the completions. The map below
    -- embeds it as a closed subspace of a product of copies of `ℂ`.
    have hclosed : Topology.IsClosedEmbedding
        (fun x : InfiniteAdeleRing E ↦ fun w ↦
          InfinitePlace.Completion.extensionEmbedding w (x w)) :=
      Topology.IsClosedEmbedding.piMap fun w ↦
        (InfinitePlace.Completion.isometry_extensionEmbedding w).isClosedEmbedding
    simpa only [B, Set.preimage_ofPred_eq, mem_closedBall_zero_iff] using
      hclosed.isCompact_preimage
        (isCompact_pi_infinite fun _ ↦ isCompact_closedBall (0 : ℂ) 1)
  have hU : IsCompact (unitarySubgroup (GL ι (InfiniteAdeleRing E)) :
      Set (GL ι (InfiniteAdeleRing E))) := by
    apply isCompact_unitarySubgroup_units_iff.mpr
    refine hB.matrix.of_isClosed_subset isClosed_unitary fun M hM i j w ↦ ?_
    let f : InfiniteAdeleRing E →+* ℂ :=
      (InfinitePlace.Completion.extensionEmbedding w).comp
        (Pi.evalRingHom (fun v : InfinitePlace E ↦ v.Completion) w)
    exact entry_norm_bound_of_unitary
      (Matrix.map_mem_unitary f (fun x ↦ InfiniteAdeleRing.extensionEmbedding_star_apply x w) hM)
      i j
  exact (Topology.IsClosedEmbedding.subtypeVal
    (Matrix.isClosed_unitaryGroupOf _)).isCompact_preimage hU

instance infiniteAdelicUnitaryGroup.instCompactSpaceMaxCompact (s : ι → ℤˣ) :
    CompactSpace (infiniteAdelicUnitaryGroup.maxCompact E s) :=
  isCompact_iff_compactSpace.mp (infiniteAdelicUnitaryGroup.isCompact_maxCompact s)

end Infinite

variable (E : Type*) [Field E] [NumberField E] [IsCMField E]
  {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The standard compact subgroup `K_∞(s) × K₀` of the adelic unitary group `G(s)`. -/
def adelicUnitaryGroup.maxCompact (s : ι → ℤˣ) : Subgroup (adelicUnitaryGroup E s) :=
  (infiniteAdelicUnitaryGroup.maxCompact E s).comap (adelicUnitaryGroup.infinitePart E s) ⊓
    (integralAdelicUnitaryGroup E ι).comap (adelicUnitaryGroup.finitePart E s)

variable {E}

/-- Membership in the standard compact subgroup is membership of both components. -/
@[simp]
theorem adelicUnitaryGroup.mem_maxCompact_iff {s : ι → ℤˣ} (g : adelicUnitaryGroup E s) :
    g ∈ adelicUnitaryGroup.maxCompact E s ↔
      adelicUnitaryGroup.infinitePart E s g ∈ infiniteAdelicUnitaryGroup.maxCompact E s ∧
      adelicUnitaryGroup.finitePart E s g ∈ integralAdelicUnitaryGroup E ι :=
  Iff.rfl

/-- The standard compact subgroup is closed. -/
theorem adelicUnitaryGroup.isClosed_maxCompact (s : ι → ℤˣ) :
    IsClosed (adelicUnitaryGroup.maxCompact E s : Set (adelicUnitaryGroup E s)) := by
  exact ((infiniteAdelicUnitaryGroup.isClosed_maxCompact s).preimage
    (adelicUnitaryGroup.continuous_infinitePart s)).inter
    ((isCompact_integralAdelicUnitaryGroup E ι).isClosed.preimage
      (adelicUnitaryGroup.continuous_finitePart s))

variable (E)

/-- The standard compact subgroup is the product of its infinite and finite factors, as a
topological group. -/
def adelicUnitaryGroup.maxCompactEquiv (s : ι → ℤˣ) :
    adelicUnitaryGroup.maxCompact E s ≃ₜ*
      infiniteAdelicUnitaryGroup.maxCompact E s × integralAdelicUnitaryGroup E ι where
  toFun g := (⟨adelicUnitaryGroup.infinitePart E s g, g.property.1⟩,
    ⟨adelicUnitaryGroup.finitePart E s g, g.property.2⟩)
  invFun p := ⟨adelicUnitaryGroup.ofInfinite E s p.1 * adelicUnitaryGroup.ofFinite E s p.2, by
    rw [adelicUnitaryGroup.mem_maxCompact_iff, map_mul, map_mul]
    simpa only [adelicUnitaryGroup.infinitePart_ofInfinite,
      adelicUnitaryGroup.infinitePart_ofFinite, adelicUnitaryGroup.finitePart_ofInfinite,
      adelicUnitaryGroup.finitePart_ofFinite, mul_one, one_mul] using
      And.intro p.1.property p.2.property⟩
  left_inv g := by
    apply Subtype.ext
    apply Subtype.ext
    simp only [Subgroup.coe_mul, adelicUnitaryGroup.coe_ofInfinite,
      adelicUnitaryGroup.coe_ofFinite, Prod.mk_mul_mk, mul_one, one_mul,
      adelicUnitaryGroup.coe_infinitePart, adelicUnitaryGroup.coe_finitePart, Prod.mk.eta]
  right_inv p := by
    apply Prod.ext <;> apply Subtype.ext
    · simp only [map_mul, adelicUnitaryGroup.infinitePart_ofInfinite,
        adelicUnitaryGroup.infinitePart_ofFinite, mul_one]
    · simp only [map_mul, adelicUnitaryGroup.finitePart_ofInfinite,
        adelicUnitaryGroup.finitePart_ofFinite, one_mul]
  map_mul' g h := by
    apply Prod.ext <;> apply Subtype.ext <;>
      simp only [Prod.fst_mul, Prod.snd_mul, Subgroup.coe_mul, map_mul]
  continuous_toFun := by
    have hinf : Continuous fun g : adelicUnitaryGroup.maxCompact E s ↦
        adelicUnitaryGroup.infinitePart E s (g : adelicUnitaryGroup E s) :=
      (adelicUnitaryGroup.continuous_infinitePart s).comp continuous_subtypeVal
    have hfin : Continuous fun g : adelicUnitaryGroup.maxCompact E s ↦
        adelicUnitaryGroup.finitePart E s (g : adelicUnitaryGroup E s) :=
      (adelicUnitaryGroup.continuous_finitePart s).comp continuous_subtypeVal
    exact (hinf.subtype_mk _).prodMk (hfin.subtype_mk _)
  continuous_invFun := by
    have hinf : Continuous
        (fun p : infiniteAdelicUnitaryGroup.maxCompact E s × integralAdelicUnitaryGroup E ι ↦
          adelicUnitaryGroup.ofInfinite E s p.1) :=
      (adelicUnitaryGroup.continuous_ofInfinite s).comp
        (continuous_subtypeVal.comp continuous_fst)
    have hfin : Continuous
        (fun p : infiniteAdelicUnitaryGroup.maxCompact E s × integralAdelicUnitaryGroup E ι ↦
          adelicUnitaryGroup.ofFinite E s p.2) :=
      (adelicUnitaryGroup.continuous_ofFinite s).comp
        (continuous_subtypeVal.comp continuous_snd)
    exact (hinf.mul hfin).subtype_mk _

variable {E}

/-- The first component of the product identification is the infinite part. -/
@[simp]
theorem adelicUnitaryGroup.maxCompactEquiv_fst {s : ι → ℤˣ}
    (g : adelicUnitaryGroup.maxCompact E s) :
    ((adelicUnitaryGroup.maxCompactEquiv E s g).1 : infiniteAdelicUnitaryGroup E s) =
      adelicUnitaryGroup.infinitePart E s g := (rfl)

/-- The second component of the product identification is the finite part. -/
@[simp]
theorem adelicUnitaryGroup.maxCompactEquiv_snd {s : ι → ℤˣ}
    (g : adelicUnitaryGroup.maxCompact E s) :
    ((adelicUnitaryGroup.maxCompactEquiv E s g).2 : finiteAdelicUnitaryGroup E ι) =
      adelicUnitaryGroup.finitePart E s g := (rfl)

/-- The inverse product identification pairs the underlying infinite and finite matrices. -/
@[simp]
theorem adelicUnitaryGroup.coe_maxCompactEquiv_symm {s : ι → ℤˣ}
    (g : infiniteAdelicUnitaryGroup.maxCompact E s × integralAdelicUnitaryGroup E ι) :
    (((adelicUnitaryGroup.maxCompactEquiv E s).symm g : adelicUnitaryGroup E s) :
      GL ι (InfiniteAdeleRing E) × GL ι 𝔸ᶠ[E]) =
        ((g.1.val : GL ι (InfiniteAdeleRing E)), (g.2.val : GL ι 𝔸ᶠ[E])) := by
  have h := (adelicUnitaryGroup.maxCompactEquiv E s).apply_symm_apply g
  have hinf := congrArg
    (fun p : infiniteAdelicUnitaryGroup.maxCompact E s × integralAdelicUnitaryGroup E ι ↦
      (p.1 : infiniteAdelicUnitaryGroup E s)) h
  have hfin := congrArg
    (fun p : infiniteAdelicUnitaryGroup.maxCompact E s × integralAdelicUnitaryGroup E ι ↦
      (p.2 : finiteAdelicUnitaryGroup E ι)) h
  rw [adelicUnitaryGroup.maxCompactEquiv_fst] at hinf
  rw [adelicUnitaryGroup.maxCompactEquiv_snd] at hfin
  exact Prod.ext
    ((adelicUnitaryGroup.coe_infinitePart _).symm.trans (congrArg Subtype.val hinf))
    ((adelicUnitaryGroup.coe_finitePart _).symm.trans (congrArg Subtype.val hfin))

instance adelicUnitaryGroup.instCompactSpaceMaxCompact (s : ι → ℤˣ) :
    CompactSpace (adelicUnitaryGroup.maxCompact E s) :=
  (adelicUnitaryGroup.maxCompactEquiv E s).symm.toHomeomorph.compactSpace

/-- The standard compact subgroup of the adelic unitary group is compact. -/
theorem adelicUnitaryGroup.isCompact_maxCompact (s : ι → ℤˣ) :
    IsCompact (adelicUnitaryGroup.maxCompact E s : Set (adelicUnitaryGroup E s)) :=
  isCompact_iff_compactSpace.mpr (adelicUnitaryGroup.instCompactSpaceMaxCompact (E := E) s)

end TauCeti
