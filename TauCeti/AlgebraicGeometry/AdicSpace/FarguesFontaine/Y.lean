/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.AdicSpace.Spa.Analytic
public import TauCeti.RingTheory.WittVector.Frobenius
import TauCeti.AlgebraicGeometry.AdicSpace.Cont.DominatingUnit
import TauCeti.AlgebraicGeometry.AdicSpace.Spa.Comap

/-!
# The open subset `𝒴 = D(p) ∩ D([ϖ])` of `Spa(A_inf, A_inf)`

Let `p` be a prime, `R` a commutative ring and `ϖ : R`, and give the Witt vectors `𝕎 R` the
`(p, [ϖ])`-adic topology, where `[ϖ]` is the Teichmüller representative of `ϖ`. When `R = 𝒪_F` is
the ring of integers of a complete perfect nonarchimedean field `F` of characteristic `p` and `ϖ`
is a pseudouniformiser, this is the Huber ring `A_inf = W(𝒪_F)`. The adic Fargues–Fontaine curve
is the quotient `𝒴 / φ^ℤ` of the open subset

```text
𝒴 = {v ∈ Spa(A_inf, A_inf) : v(p [ϖ]) ≠ 0} = D(p) ∩ D([ϖ])
```

of its adic spectrum by the Witt-vector Frobenius `φ`, which acts on points by `v ↦ v ∘ φ`.

This file defines `𝒴` and proves its first properties.

* `𝒴` is open in `Spa(A_inf, A_inf)`, being cut out by `v(p [ϖ]) ≠ 0`.
* The analytic locus of `Spa(A_inf, A⁺)` is `D(p) ∪ D([ϖ])`, for every plus ring `A⁺`. In
  particular `𝒴` consists of analytic points.
* Pulling back along `φ` preserves `𝒴`, and when `R` is perfect of characteristic `p` a point lies
  in `𝒴` exactly when its pullback does, so the group `φ^ℤ` acts on `𝒴`.
* At a point `v ∈ 𝒴` the values `v(p)` and `v([ϖ])` are power-comparable: every power of either
  one strictly dominates some power of the other.
* Writing `κ(v) ≥ a / b` for `v([ϖ]) ^ b ≤ v(p) ^ a` (and `κ(v) ≤ a / b` for the reverse
  inequality), which assigns no real number to a higher-rank valuation, Frobenius multiplies the
  radius: `κ(φ v) ≥ a / b` exactly when `κ(v) ≥ a / (p b)`, and likewise for `≤`. Since
  `φ [ϖ] = [ϖ] ^ p` and `φ p = p`, this holds at every point of `Spv (𝕎 R)`.

## Main definitions

* `TauCeti.FarguesFontaine.spaY` : the subset `𝒴 = D(p) ∩ D([ϖ])` of `Spa(𝕎 R, 𝕎 R)`.

## Main results

* `TauCeti.FarguesFontaine.isOpen_val_preimage_spaY` : `𝒴` is open in `Spa(𝕎 R, 𝕎 R)`.
* `TauCeti.FarguesFontaine.mem_spaAnalytic_iff_of_isAdic` : the analytic locus is
  `D(p) ∪ D([ϖ])`.
* `TauCeti.FarguesFontaine.spaY_subset_spaAnalytic` : `𝒴` lies in the analytic locus.
* `TauCeti.FarguesFontaine.comap_frobenius_mem_spaY_iff` : `𝒴` is stable under Frobenius and its
  inverse.
* `TauCeti.FarguesFontaine.exists_pow_vlt_of_mem_spaY` : power comparison of `v(p)` and `v([ϖ])`.
* `TauCeti.FarguesFontaine.comap_frobenius_teichmuller_pow_vle_natCast_pow_iff` and
  `TauCeti.FarguesFontaine.comap_frobenius_natCast_pow_vle_teichmuller_pow_iff` : Frobenius
  multiplies the radius `κ` by `p`.

## References

* L. Fargues and J.-M. Fontaine, *Courbes et fibrés vectoriels en théorie de Hodge p-adique*,
  Astérisque 406 (2018).
* K. S. Kedlaya, *Sheaves, stacks, and shtukas*, lecture notes, Arizona Winter School 2017,
  §§3.1–3.2.
* P. Scholze and J. Weinstein, *Berkeley lectures on p-adic geometry*, Lecture 12.
-/

public section

namespace TauCeti.FarguesFontaine

open TauCeti.ValuationSpectrum _root_.WittVector

variable (p : ℕ) [Fact p.Prime] {R : Type*} [CommRing R]

section CharP

variable {p} [CharP R p] {ϖ : R}

/-- Pulling back along Frobenius does not change whether `p` and `[ϖ]` vanish: `φ p = p`, and
`φ [ϖ] = [ϖ] ^ p` vanishes exactly when `[ϖ]` does, supports being prime. -/
private theorem notMem_supp_comap_frobenius_iff (v : Spv (WittVector p R)) :
    ((p : WittVector p R) ∉ (comap frobenius v).supp ∧
        teichmuller p ϖ ∉ (comap frobenius v).supp) ↔
      (p : WittVector p R) ∉ v.supp ∧ teichmuller p ϖ ∉ v.supp := by
  rw [supp_comap, Ideal.mem_comap, Ideal.mem_comap, map_natCast, frobenius_teichmuller,
    Ideal.IsPrime.pow_mem_iff_mem inferInstance p (Fact.out : p.Prime).pos]

/-- **Frobenius multiplies the radius by `p`, from below.** Read `κ(v) ≥ a / b` as
`v([ϖ]) ^ b ≤ v(p) ^ a`. Then `κ(φ v) ≥ a / b` exactly when `κ(v) ≥ a / (p b)`, since
`φ [ϖ] = [ϖ] ^ p` and `φ p = p`. -/
theorem comap_frobenius_teichmuller_pow_vle_natCast_pow_iff (v : Spv (WittVector p R))
    (a b : ℕ) :
    (comap frobenius v).toValuativeRel.vle (teichmuller p ϖ ^ b) ((p : WittVector p R) ^ a) ↔
      v.toValuativeRel.vle (teichmuller p ϖ ^ (p * b)) ((p : WittVector p R) ^ a) := by
  rw [comap_vle, map_pow, map_pow, frobenius_teichmuller, map_natCast, ← pow_mul]

/-- **Frobenius multiplies the radius by `p`, from above.** Read `κ(v) ≤ a / b` as
`v(p) ^ a ≤ v([ϖ]) ^ b`. Then `κ(φ v) ≤ a / b` exactly when `κ(v) ≤ a / (p b)`, since
`φ [ϖ] = [ϖ] ^ p` and `φ p = p`. -/
theorem comap_frobenius_natCast_pow_vle_teichmuller_pow_iff (v : Spv (WittVector p R))
    (a b : ℕ) :
    (comap frobenius v).toValuativeRel.vle ((p : WittVector p R) ^ a) (teichmuller p ϖ ^ b) ↔
      v.toValuativeRel.vle ((p : WittVector p R) ^ a) (teichmuller p ϖ ^ (p * b)) := by
  rw [comap_vle, map_pow, map_pow, frobenius_teichmuller, map_natCast, ← pow_mul]

end CharP

variable [TopologicalSpace (WittVector p R)]

/-- **The open subset `𝒴 = D(p) ∩ D([ϖ])` of `Spa(𝕎 R, 𝕎 R)`**: the points of the adic spectrum,
with plus ring all of `𝕎 R`, at which neither `p` nor the Teichmüller representative `[ϖ]`
vanishes. For `A_inf = W(𝒪_F)` with its `(p, [ϖ])`-adic topology, this is the space whose quotient
by Frobenius is the adic Fargues–Fontaine curve. -/
def spaY (ϖ : R) : Set (Spv (WittVector p R)) :=
  spa (⊤ : Subring (WittVector p R)) ∩
    {v | (p : WittVector p R) ∉ v.supp ∧ teichmuller p ϖ ∉ v.supp}

/-- Membership in `𝒴`: a point of `Spa(𝕎 R, 𝕎 R)` at which `p` and `[ϖ]` do not vanish. -/
@[simp]
theorem mem_spaY_iff (ϖ : R) (v : Spv (WittVector p R)) :
    v ∈ spaY p ϖ ↔
      v ∈ spa (⊤ : Subring (WittVector p R)) ∧
        (p : WittVector p R) ∉ v.supp ∧ teichmuller p ϖ ∉ v.supp :=
  Iff.rfl

/-- `𝒴` is the locus of `Spa(𝕎 R, 𝕎 R)` where the single element `p [ϖ]` does not vanish, the
basic open subset `Spv(𝕎 R)(p [ϖ] / p [ϖ])`, since supports are prime. -/
theorem spaY_eq_spa_inter_basicOpen (ϖ : R) :
    spaY p ϖ = spa (⊤ : Subring (WittVector p R)) ∩
      basicOpen ((p : WittVector p R) * teichmuller p ϖ)
        ((p : WittVector p R) * teichmuller p ϖ) := by
  ext v
  rw [basicOpen_self, mem_spaY_iff, Set.mem_inter_iff, Set.mem_ofPred_eq, ← mem_supp_iff,
    Ideal.IsPrime.mul_mem_iff_mem_or_mem inferInstance, not_or]

/-- **`𝒴` is open in `Spa(𝕎 R, 𝕎 R)`.** -/
theorem isOpen_val_preimage_spaY (ϖ : R) :
    IsOpen (Subtype.val ⁻¹' spaY p ϖ : Set (spa (⊤ : Subring (WittVector p R)))) := by
  rw [spaY_eq_spa_inter_basicOpen, Set.preimage_inter, Subtype.coe_preimage_self, Set.univ_inter]
  exact (isOpen_basicOpen _ _).preimage continuous_subtype_val

variable {p} {ϖ : R}

/-- **The analytic locus of `Spa(𝕎 R, A⁺)` is `D(p) ∪ D([ϖ])`**, for the `(p, [ϖ])`-adic topology
and any plus ring `A⁺`: a point is analytic exactly when `p` or `[ϖ]` does not vanish at it. -/
theorem mem_spaAnalytic_iff_of_isAdic
    (hI : IsAdic (Ideal.span {(p : WittVector p R), teichmuller p ϖ}))
    (Aplus : Subring (WittVector p R)) (v : Spv (WittVector p R)) :
    v ∈ spaAnalytic Aplus ↔
      v ∈ spa Aplus ∧ ((p : WittVector p R) ∉ v.supp ∨ teichmuller p ϖ ∉ v.supp) := by
  rw [ValuationSpectrum.mem_spaAnalytic_iff, isAnalyticPoint_iff_not_le_supp_of_isAdic hI,
    Ideal.span_le, Set.insert_subset_iff, Set.singleton_subset_iff, not_and_or, SetLike.mem_coe,
    SetLike.mem_coe]

/-- **`𝒴` consists of analytic points** of `Spa(𝕎 R, 𝕎 R)`, for the `(p, [ϖ])`-adic topology. -/
theorem spaY_subset_spaAnalytic
    (hI : IsAdic (Ideal.span {(p : WittVector p R), teichmuller p ϖ})) :
    spaY p ϖ ⊆ spaAnalytic (⊤ : Subring (WittVector p R)) := fun v hv ↦
  (mem_spaAnalytic_iff_of_isAdic hI ⊤ v).mpr ⟨hv.1, Or.inl hv.2.1⟩

/-- **Power comparison on `𝒴`.** At a point `v ∈ 𝒴` of the `(p, [ϖ])`-adic Witt vectors, every
power `v(p) ^ a` strictly dominates some power `v([ϖ]) ^ b`, and every power `v([ϖ]) ^ a` strictly
dominates some power `v(p) ^ b`. Both `p` and `[ϖ]` are topologically nilpotent, and `v` is
continuous and nonvanishing at both. The exponent `b` is necessarily positive, since `v(p)` and
`v([ϖ])` are at most `1`. -/
theorem exists_pow_vlt_of_mem_spaY
    (hI : IsAdic (Ideal.span {(p : WittVector p R), teichmuller p ϖ}))
    {v : Spv (WittVector p R)} (hv : v ∈ spaY p ϖ) (a : ℕ) :
    (∃ b : ℕ, v.toValuativeRel.vlt (teichmuller p ϖ ^ b) ((p : WittVector p R) ^ a)) ∧
      ∃ b : ℕ, v.toValuativeRel.vlt ((p : WittVector p R) ^ b) (teichmuller p ϖ ^ a) := by
  obtain ⟨hspa, hp, hϖ⟩ := (mem_spaY_iff p ϖ v).mp hv
  have hcont : v.IsContinuous := ((mem_spa_iff _ v).mp hspa).1
  exact ⟨hcont.exists_pow_vlt_of_isTopologicallyNilpotent
      (IsAdic.isTopologicallyNilpotent_of_mem hI (Ideal.subset_span (by simp)))
      fun h ↦ hp (Ideal.IsPrime.mem_of_pow_mem inferInstance a h),
    hcont.exists_pow_vlt_of_isTopologicallyNilpotent
      (IsAdic.isTopologicallyNilpotent_of_mem hI (Ideal.subset_span (by simp)))
      fun h ↦ hϖ (Ideal.IsPrime.mem_of_pow_mem inferInstance a h)⟩

section CharP

variable [CharP R p]

/-- **Frobenius preserves `𝒴`**: pulling a point of `𝒴` back along the Witt-vector Frobenius gives
a point of `𝒴`, for the `(p, [ϖ])`-adic topology in characteristic `p`. -/
theorem comap_frobenius_mem_spaY
    (hI : IsAdic (Ideal.span {(p : WittVector p R), teichmuller p ϖ}))
    {v : Spv (WittVector p R)} (hv : v ∈ spaY p ϖ) : comap frobenius v ∈ spaY p ϖ := by
  rw [mem_spaY_iff] at hv ⊢
  exact ⟨comap_mem_spa (TauCeti.WittVector.continuous_frobenius hI)
    (fun _ _ ↦ Subring.mem_top _) hv.1, (notMem_supp_comap_frobenius_iff v).mpr hv.2⟩

/-- **`𝒴` is stable under Frobenius and its inverse.** For a perfect ring `R` of characteristic
`p` and the `(p, [ϖ])`-adic topology, a point of `Spv (𝕎 R)` lies in `𝒴` exactly when its pullback
along the Witt-vector Frobenius does, so the group `φ^ℤ` acts on `𝒴`. -/
theorem comap_frobenius_mem_spaY_iff [PerfectRing R p]
    (hI : IsAdic (Ideal.span {(p : WittVector p R), teichmuller p ϖ}))
    (v : Spv (WittVector p R)) : comap frobenius v ∈ spaY p ϖ ↔ v ∈ spaY p ϖ := by
  refine ⟨fun h ↦ ?_, comap_frobenius_mem_spaY hI⟩
  -- `v` is the pullback of `comap φ v` along the continuous inverse `φ⁻¹`
  have hcomp : (frobenius : WittVector p R →+* WittVector p R).comp
      ((frobeniusEquiv p R).symm : WittVector p R →+* WittVector p R) = RingHom.id _ :=
    RingHom.ext fun x ↦ by simpa using (frobeniusEquiv p R).apply_symm_apply x
  have hv : comap ((frobeniusEquiv p R).symm : WittVector p R →+* WittVector p R)
      (comap frobenius v) = v := by
    rw [← Function.comp_apply (f := comap _), ← comap_comp, hcomp, comap_id, id]
  rw [mem_spaY_iff] at h ⊢
  exact ⟨hv ▸ comap_mem_spa (TauCeti.WittVector.continuous_frobeniusEquiv_symm hI)
    (fun _ _ ↦ Subring.mem_top _) h.1, (notMem_supp_comap_frobenius_iff v).mp h.2⟩

end CharP

end TauCeti.FarguesFontaine
