/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Localization.FractionRing
public import TauCeti.Analysis.Meromorphic.Germ
public import TauCeti.Geometry.Manifold.Complex.StructureSheaf.Domain
public import TauCeti.Geometry.Manifold.Complex.StructureSheaf.Germ

/-!
# Meromorphic germs form the fraction field of holomorphic germs

Let `a : ℂ` and let `𝒪_a` be the stalk at `a` of the holomorphic structure sheaf of `ℂ`, an
integral domain. Restricting a holomorphic germ to the punctured neighbourhoods of `a` gives a
punctured meromorphic germ, which defines an injective ring homomorphism
`TauCeti.holomorphicStructureSheaf.toMeromorphicGerms a : 𝒪_a →+* meromorphicGerms ℂ a`
(`toMeromorphicGerms_injective`: by continuity a holomorphic germ is determined by its values off
`a`). This file proves:

* `exists_eq_toMeromorphicGerms_div`: every meromorphic germ at `a` is a quotient `h / (z - a) ^ n`
  of a holomorphic germ `h` by a power of the coordinate. Indeed, by Mathlib's definition a
  function `f` is meromorphic at `a` when `(z - a) ^ n • f z` is analytic at `a` for some `n`.
* `isFractionRing_meromorphicGerms`: consequently `meromorphicGerms ℂ a` is a fraction field of
  `𝒪_a`, so it is identified with `FractionRing 𝒪_a` by `IsFractionRing.algEquiv`.
* `exists_toMeromorphicGerms_eq_iff`: a meromorphic germ comes from a holomorphic germ exactly when
  its order at `a` is nonnegative.

## References

* Otto Forster, *Lectures on Riemann Surfaces*, Graduate Texts in Mathematics 81, Springer, 1981,
  §1.
-/

public noncomputable section

open Filter Function Topology
open scoped ContDiff Manifold

namespace TauCeti.holomorphicStructureSheaf

variable (a : ℂ)

/-- Restricting a holomorphic germ at `a : ℂ` to the punctured neighbourhoods of `a` gives a
meromorphic germ at `a`. -/
def toMeromorphicGerms :
    (holomorphicStructureSheaf 𝓘(ℂ) ℂ).presheaf.stalk a →+* meromorphicGerms ℂ a :=
  (toFilterGerm 𝓘(ℂ) ℂ a (𝓝[≠] a) nhdsWithin_le_nhds).codRestrict _ fun s ↦ by
    obtain ⟨f, hf, hfs⟩ := exists_toFilterGerm_eq a s
    rw [hfs, coe_mem_meromorphicGerms]
    exact (contMDiffAt_iff_contDiffAt.1 hf.self_of_nhds).analyticAt.meromorphicAt

@[simp]
theorem coe_toMeromorphicGerms (s : (holomorphicStructureSheaf 𝓘(ℂ) ℂ).presheaf.stalk a) :
    (toMeromorphicGerms a s : Germ (𝓝[≠] a) ℂ) =
      toFilterGerm 𝓘(ℂ) ℂ a (𝓝[≠] a) nhdsWithin_le_nhds s :=
  (rfl)

/-- A holomorphic germ at `a : ℂ` is determined by its values on a punctured neighbourhood. -/
theorem toMeromorphicGerms_injective : Injective (toMeromorphicGerms a) :=
  fun _ _ h ↦ toFilterGerm_nhdsNE_injective a (congrArg Subtype.val h)

variable {a}

/-- A function analytic at `a : ℂ` has a holomorphic germ at `a`, whose punctured germ is that of
the function. -/
theorem exists_toMeromorphicGerms_eq_of_analyticAt {f : ℂ → ℂ} (hf : AnalyticAt ℂ f a) :
    ∃ s, (toMeromorphicGerms a s : Germ (𝓝[≠] a) ℂ) = f :=
  (exists_toFilterGerm_eq_of_eventually_contMDiffAt
    (hf.eventually_analyticAt.mono fun _ hy ↦ hy.contDiffAt.contMDiffAt)).imp fun _ hs ↦ hs _ _

/-- A function meromorphic at `a : ℂ` has the punctured germ of a holomorphic germ at `a`
exactly when its order at `a` is nonnegative. -/
theorem exists_toMeromorphicGerms_eq_iff {f : ℂ → ℂ} (hf : MeromorphicAt f a) :
    (∃ s, (toMeromorphicGerms a s : Germ (𝓝[≠] a) ℂ) = f) ↔ 0 ≤ meromorphicOrderAt f a := by
  rw [hf.meromorphicOrderAt_nonneg_iff]
  constructor
  · rintro ⟨s, hs⟩
    obtain ⟨g, hg, hgs⟩ := exists_toFilterGerm_eq a s
    rw [coe_toMeromorphicGerms, hgs, Germ.coe_eq] at hs
    exact ⟨g, (contMDiffAt_iff_contDiffAt.1 hg.self_of_nhds).analyticAt, hs.symm⟩
  · rintro ⟨g, hg, hfg⟩
    obtain ⟨s, hs⟩ := exists_toMeromorphicGerms_eq_of_analyticAt hg
    exact ⟨s, hs.trans (Germ.coe_eq.2 hfg.symm)⟩

variable (a)

/-- Every meromorphic germ at `a : ℂ` is the quotient of a holomorphic germ by a power of the
coordinate `z - a`. -/
theorem exists_eq_toMeromorphicGerms_div (φ : meromorphicGerms ℂ a) :
    ∃ (h p : (holomorphicStructureSheaf 𝓘(ℂ) ℂ).presheaf.stalk a) (n : ℕ),
      (toMeromorphicGerms a p : Germ (𝓝[≠] a) ℂ) = (fun z ↦ (z - a) ^ n : ℂ → ℂ) ∧
        φ = toMeromorphicGerms a h / toMeromorphicGerms a p := by
  obtain ⟨f, ⟨n, hn⟩, hφ⟩ := mem_meromorphicGerms_iff.1 φ.2
  obtain ⟨h, hh⟩ := exists_toMeromorphicGerms_eq_of_analyticAt hn
  have hpa : AnalyticAt ℂ (fun z ↦ (z - a) ^ n) a := by fun_prop
  obtain ⟨p, hp⟩ := exists_toMeromorphicGerms_eq_of_analyticAt hpa
  refine ⟨h, p, n, hp, ?_⟩
  have hp0 : toMeromorphicGerms a p ≠ 0 := fun h0 ↦
    (hpa.meromorphicAt.germ_ne_zero_iff.2 <| eventually_mem_nhdsWithin.mono fun z hz ↦
      pow_ne_zero n (sub_ne_zero.2 hz)) (hp.symm.trans (congrArg Subtype.val h0))
  rw [eq_div_iff hp0]
  apply Subtype.ext
  rw [Subring.coe_mul, hp, hh, ← hφ, ← Germ.coe_mul]
  exact Germ.coe_eq.2 (.of_forall fun z ↦ by simp [smul_eq_mul, mul_comm])

/-- Meromorphic germs at `a : ℂ` form an algebra over the holomorphic germs at `a`, through
`toMeromorphicGerms`. -/
instance : Algebra ((holomorphicStructureSheaf 𝓘(ℂ) ℂ).presheaf.stalk a) (meromorphicGerms ℂ a) :=
  (toMeromorphicGerms a).toAlgebra

@[simp]
theorem algebraMap_meromorphicGerms :
    algebraMap ((holomorphicStructureSheaf 𝓘(ℂ) ℂ).presheaf.stalk a) (meromorphicGerms ℂ a) =
      toMeromorphicGerms a :=
  (rfl)

/-- The field of meromorphic germs at `a : ℂ` is the fraction field of the ring of holomorphic
germs at `a`. -/
instance isFractionRing_meromorphicGerms :
    IsFractionRing ((holomorphicStructureSheaf 𝓘(ℂ) ℂ).presheaf.stalk a) (meromorphicGerms ℂ a) :=
  have : FaithfulSMul ((holomorphicStructureSheaf 𝓘(ℂ) ℂ).presheaf.stalk a)
      (meromorphicGerms ℂ a) :=
    (faithfulSMul_iff_algebraMap_injective _ _).2 (toMeromorphicGerms_injective a)
  IsFractionRing.of_field _ _ fun φ ↦
    let ⟨h, p, _, _, hφ⟩ := exists_eq_toMeromorphicGerms_div a φ
    ⟨h, p, hφ⟩

end TauCeti.holomorphicStructureSheaf
