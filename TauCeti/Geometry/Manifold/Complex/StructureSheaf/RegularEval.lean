/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Complex.StructureSheaf.LocalRing
public import TauCeti.Geometry.Manifold.Complex.StructureSheaf.Pullback

/-!
# Regular meromorphic germs and their value at the centre

Let `a : ℂ`. The holomorphic germs at `a` embed in the field `meromorphicGerms ℂ a` of punctured
meromorphic germs by `TauCeti.holomorphicStructureSheaf.toMeromorphicGerms a`. Call a meromorphic
germ *regular* when it lies in the image of this embedding. This file identifies the subring of
regular germs with the stalk `𝒪_a` and transports evaluation at `a` to a ring homomorphism
`TauCeti.holomorphicStructureSheaf.regularEval a : (toMeromorphicGerms a).range →+* ℂ`.

A meromorphic germ lives on punctured neighbourhoods of `a`, so it has no value at `a`, and the
value of a representative at `a` is never used. Instead, a meromorphic germ is regular exactly
when it has a limit at `a` along `𝓝[≠] a` (`mem_range_toMeromorphicGerms_iff_exists_tendsto`), and
then its value is that limit. Equivalently, a germ is regular exactly when its principal part
vanishes (`mem_range_toMeromorphicGerms_iff_principalPart_eq_zero`), and then its value is the
value at `a` of its regular part. Both regularity criteria are in
`TauCeti.Geometry.Manifold.Complex.StructureSheaf.MeromorphicGerm`. The value is unchanged by
pullback along analytic maps which preserve punctured neighbourhoods, in particular along local
biholomorphisms. A regular germ is a unit of the regular subring exactly when its value is nonzero,
so the nonunits of the regular subring form the kernel of its value homomorphism.

## Main declarations

* `TauCeti.holomorphicStructureSheaf.rangeToMeromorphicGermsEquiv`: the holomorphic stalk at `a` is
  isomorphic to the subring of regular meromorphic germs.
* `TauCeti.holomorphicStructureSheaf.regularEval`: the value at `a` of a regular germ.
* `TauCeti.holomorphicStructureSheaf.regularEval_eq_iff_tendsto`: the value of a regular germ is
  its limit at `a`.
* `TauCeti.holomorphicStructureSheaf.regularEval_eq_eval_regularPart`: the value of a regular germ
  is the value at `a` of its regular part.
* `TauCeti.holomorphicStructureSheaf.regularEval_pullback`: pullback preserves the value.
* `TauCeti.holomorphicStructureSheaf.isUnit_iff_regularEval_ne_zero`: the units of the regular
  subring are the germs with nonzero value.
* `TauCeti.holomorphicStructureSheaf.nonunits_eq_ker_regularEval`: the nonunits of the regular
  subring are the kernel of `regularEval`.

## References

* Otto Forster, *Lectures on Riemann Surfaces*, Graduate Texts in Mathematics 81, Springer, 1981,
  §1.
-/

public noncomputable section

open Filter Function Topology
open scoped Manifold ContDiff

namespace TauCeti.holomorphicStructureSheaf

variable (a : ℂ)

/-- The holomorphic germs at `a : ℂ` are isomorphic to the regular meromorphic germs at `a`, the
image of `toMeromorphicGerms a`. -/
def rangeToMeromorphicGermsEquiv :
    (holomorphicStructureSheaf 𝓘(ℂ) ℂ).presheaf.stalk a ≃+* (toMeromorphicGerms a).range :=
  RingEquiv.ofLeftInverse (leftInverse_invFun (toMeromorphicGerms_injective a))

@[simp]
theorem coe_rangeToMeromorphicGermsEquiv
    (s : (holomorphicStructureSheaf 𝓘(ℂ) ℂ).presheaf.stalk a) :
    (rangeToMeromorphicGermsEquiv a s : meromorphicGerms ℂ a) = toMeromorphicGerms a s :=
  (rfl)

@[simp]
theorem toMeromorphicGerms_rangeToMeromorphicGermsEquiv_symm (φ : (toMeromorphicGerms a).range) :
    toMeromorphicGerms a ((rangeToMeromorphicGermsEquiv a).symm φ) = φ := by
  rw [← coe_rangeToMeromorphicGermsEquiv, RingEquiv.apply_symm_apply]

/-- The value at `a : ℂ` of a regular meromorphic germ at `a`: the value at `a` of the holomorphic
germ it comes from. It is the limit at `a` of the germ (`regularEval_eq_iff_tendsto`). -/
def regularEval : (toMeromorphicGerms a).range →+* ℂ :=
  (eval 𝓘(ℂ) ℂ a).comp (rangeToMeromorphicGermsEquiv a).symm.toRingHom

/-- The value of the regular germ of a holomorphic germ is the value of the holomorphic germ. -/
@[simp]
theorem regularEval_rangeToMeromorphicGermsEquiv
    (s : (holomorphicStructureSheaf 𝓘(ℂ) ℂ).presheaf.stalk a) :
    regularEval a (rangeToMeromorphicGermsEquiv a s) = eval 𝓘(ℂ) ℂ a s := by
  simp [regularEval]

/-- The value of the regular germ of a holomorphic germ, given with any proof of its regularity,
is the value of the holomorphic germ. -/
@[simp]
theorem regularEval_mk_toMeromorphicGerms
    (s : (holomorphicStructureSheaf 𝓘(ℂ) ℂ).presheaf.stalk a)
    (hs : toMeromorphicGerms a s ∈ (toMeromorphicGerms a).range) :
    regularEval a ⟨toMeromorphicGerms a s, hs⟩ = eval 𝓘(ℂ) ℂ a s := by
  have h : (⟨toMeromorphicGerms a s, hs⟩ : (toMeromorphicGerms a).range) =
      rangeToMeromorphicGermsEquiv a s :=
    Subtype.ext (coe_rangeToMeromorphicGermsEquiv a s).symm
  rw [h, regularEval_rangeToMeromorphicGermsEquiv]

/-- Every complex number is the value of a regular germ. -/
theorem regularEval_surjective : Surjective (regularEval a) :=
  (eval_surjective 𝓘(ℂ) ℂ a).comp (rangeToMeromorphicGermsEquiv a).symm.surjective

variable {a}

/-- A regular meromorphic germ tends to its value at `a`. -/
theorem tendsto_regularEval (φ : (toMeromorphicGerms a).range) :
    ((φ : meromorphicGerms ℂ a) : Germ (𝓝[≠] a) ℂ).Tendsto (𝓝 (regularEval a φ)) := by
  obtain ⟨s, rfl⟩ := (rangeToMeromorphicGermsEquiv a).surjective φ
  obtain ⟨f, hf, hfs⟩ := exists_toFilterGerm_eq a s
  rw [regularEval_rangeToMeromorphicGermsEquiv, eval_eq_of_toFilterGerm_eq (hfs _ le_rfl),
    coe_rangeToMeromorphicGermsEquiv, coe_toMeromorphicGerms, hfs, Germ.coe_tendsto]
  exact hf.self_of_nhds.continuousAt.continuousWithinAt.tendsto

/-- **The value of a regular germ is its limit.** A regular meromorphic germ at `a` has value `c`
exactly when it tends to `c` along the punctured neighbourhoods of `a`. -/
theorem regularEval_eq_iff_tendsto (φ : (toMeromorphicGerms a).range) {c : ℂ} :
    regularEval a φ = c ↔ ((φ : meromorphicGerms ℂ a) : Germ (𝓝[≠] a) ℂ).Tendsto (𝓝 c) := by
  refine ⟨fun h ↦ h ▸ tendsto_regularEval φ, fun h ↦ ?_⟩
  have hφ := tendsto_regularEval φ
  obtain ⟨f, -, hf⟩ := mem_meromorphicGerms_iff.1 (φ : meromorphicGerms ℂ a).2
  rw [← hf, Germ.coe_tendsto] at h hφ
  exact tendsto_nhds_unique hφ h

/-- The value of a regular meromorphic germ at `a` represented by a function continuous at `a` is
the value of the function at `a`. Regularity of such a germ follows from
`mem_range_toMeromorphicGerms_iff_exists_tendsto`. -/
theorem regularEval_eq_of_continuousAt (φ : (toMeromorphicGerms a).range) {f : ℂ → ℂ}
    (hf : ContinuousAt f a) (hφ : ((φ : meromorphicGerms ℂ a) : Germ (𝓝[≠] a) ℂ) = f) :
    regularEval a φ = f a := by
  rw [regularEval_eq_iff_tendsto, hφ, Germ.coe_tendsto]
  exact hf.continuousWithinAt.tendsto

/-- The value of a regular germ is the value at `a` of its regular part. -/
theorem regularEval_eq_eval_regularPart (φ : (toMeromorphicGerms a).range) :
    regularEval a φ = eval 𝓘(ℂ) ℂ a (regularPart a φ) := by
  obtain ⟨s, rfl⟩ := (rangeToMeromorphicGermsEquiv a).surjective φ
  rw [regularEval_rangeToMeromorphicGermsEquiv, coe_rangeToMeromorphicGermsEquiv,
    regularPart_toMeromorphicGerms]

/-- **Pullback preserves the value.** If `g` is analytic at `a`, sends `a` to `b` and punctured
neighbourhoods of `a` to punctured neighbourhoods of `b`, then the pullback along `g` of a regular
germ at `b` is a regular germ at `a` with the same value. Regularity of the pullback is
`exists_toMeromorphicGerms_pullback`; any proof of it may be used. -/
theorem regularEval_pullback {b : ℂ} (g : ℂ → ℂ) (hg : AnalyticAt ℂ g a) (hga : g a = b)
    (ht : Tendsto g (𝓝[≠] a) (𝓝[≠] b)) (φ : (toMeromorphicGerms b).range)
    (hφ : meromorphicGerms.pullback g hg hga ht φ ∈ (toMeromorphicGerms a).range) :
    regularEval a ⟨meromorphicGerms.pullback g hg hga ht φ, hφ⟩ = regularEval b φ := by
  rw [regularEval_eq_iff_tendsto, meromorphicGerms.coe_pullback]
  have h := tendsto_regularEval φ
  obtain ⟨f, -, hf⟩ := mem_meromorphicGerms_iff.1 (φ : meromorphicGerms ℂ b).2
  rw [← hf, Germ.coe_tendsto] at h
  rw [← hf, Germ.coe_compTendsto, Germ.coe_tendsto]
  exact h.comp ht

/-- A regular germ is a unit of the regular subring exactly when its value is nonzero. -/
@[simp]
theorem isUnit_iff_regularEval_ne_zero (φ : (toMeromorphicGerms a).range) :
    IsUnit φ ↔ regularEval a φ ≠ 0 := by
  obtain ⟨s, rfl⟩ := (rangeToMeromorphicGermsEquiv a).surjective φ
  rw [MulEquiv.isUnit_map (rangeToMeromorphicGermsEquiv a), isUnit_stalk_iff,
    regularEval_rangeToMeromorphicGermsEquiv]

variable (a) in
/-- The nonunits of the regular subring are exactly the kernel of its value homomorphism. -/
theorem nonunits_eq_ker_regularEval :
    nonunits (toMeromorphicGerms a).range = RingHom.ker (regularEval a) := by
  ext φ
  simp [mem_nonunits_iff]

end TauCeti.holomorphicStructureSheaf
