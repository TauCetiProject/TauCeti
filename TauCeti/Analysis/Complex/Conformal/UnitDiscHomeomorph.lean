/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.Analysis.Complex.Conformal.UnitDiscAutomorphism

/-!
# Unit-disc automorphisms as homeomorphisms

This file packages the standard unit-disc automorphisms from
`TauCeti.Analysis.Complex.Conformal.UnitDiscAutomorphism` as homeomorphisms of
`Complex.UnitDisc`.  The underlying maps are the existing equivalences
`unitDiscMoebiusEquiv` and `unitDiscStandardAutomorphismEquiv`; this file adds the
continuity API needed before treating the disc automorphisms as a topological automorphism
group in the Schwarz--Pick layer of the conformal-mapping roadmap.

This L2 material is coordinated with the upstream Mathlib RMT effort in
leanprover-community/mathlib4#33505.  Mathlib already contains the preceding human-curated
work in `Analysis/Complex/RiemannMapping.lean` and `Analysis/Complex/BranchLogRoot.lean`;
this file only packages Tau Ceti's existing unit-disc automorphism formulas topologically.
-/

public section

namespace TauCeti

open Complex
open scoped ComplexConjugate

/-- The unit-disc Moebius factor is continuous as a map of the bundled open disc. -/
lemma continuous_unitDiscMoebius (a : Complex.UnitDisc) :
    Continuous (unitDiscMoebius a) := by
  rw [Complex.UnitDisc.isEmbedding_coe.continuous_iff]
  -- The embedding criterion reduces continuity to the scalar coercion of the bundled disc.
  change Continuous fun z : Complex.UnitDisc => (unitDiscMoebius a z : ℂ)
  simp only [coe_unitDiscMoebius]
  simpa only [Function.comp_def] using
    (differentiableOn_unitDiscMoebiusFormula a).continuousOn.comp_continuous
      Complex.UnitDisc.continuous_coe
      (fun z => by simpa [mem_ball_zero_iff] using Complex.UnitDisc.norm_lt_one z)

/-- The standard Moebius self-map of the unit disc, bundled as a homeomorphism. -/
noncomputable def unitDiscMoebiusHomeomorph (a : Complex.UnitDisc) :
    Complex.UnitDisc ≃ₜ Complex.UnitDisc where
  toEquiv := unitDiscMoebiusEquiv a
  continuous_toFun := by
    -- The homeomorphism field is the bundled equivalence function.
    change Continuous fun z : Complex.UnitDisc => unitDiscMoebiusEquiv a z
    simpa only [unitDiscMoebiusEquiv_apply] using continuous_unitDiscMoebius a
  continuous_invFun := by
    -- The inverse field is the bundled equivalence inverse function.
    change Continuous fun z : Complex.UnitDisc => (unitDiscMoebiusEquiv a).symm z
    rw [unitDiscMoebiusEquiv_symm]
    simpa only [unitDiscMoebiusEquiv_apply] using continuous_unitDiscMoebius (-a)

/-- The Moebius homeomorphism applies by the existing Moebius factor. -/
@[simp]
lemma unitDiscMoebiusHomeomorph_apply (a z : Complex.UnitDisc) :
    unitDiscMoebiusHomeomorph a z = unitDiscMoebius a z :=
  unitDiscMoebiusEquiv_apply a z

/-- The underlying equivalence of the Moebius homeomorphism is the existing equivalence. -/
@[simp]
lemma unitDiscMoebiusHomeomorph_toEquiv (a : Complex.UnitDisc) :
    (unitDiscMoebiusHomeomorph a).toEquiv = unitDiscMoebiusEquiv a :=
  by
    apply Equiv.ext
    intro z
    -- `Homeomorph.toEquiv` is the bundled homeomorphism function.
    change unitDiscMoebiusHomeomorph a z = unitDiscMoebiusEquiv a z
    rw [unitDiscMoebiusHomeomorph_apply, unitDiscMoebiusEquiv_apply]

/-- The inverse Moebius homeomorphism is the Moebius homeomorphism centered at `-a`. -/
@[simp]
lemma unitDiscMoebiusHomeomorph_symm (a : Complex.UnitDisc) :
    (unitDiscMoebiusHomeomorph a).symm = unitDiscMoebiusHomeomorph (-a) := by
  ext z
  -- `Homeomorph.symm` exposes the inverse function through the bundled `Equiv`.
  change ((unitDiscMoebiusEquiv a).symm z : ℂ) = (unitDiscMoebiusHomeomorph (-a) z : ℂ)
  rw [unitDiscMoebiusEquiv_symm, unitDiscMoebiusEquiv_apply, unitDiscMoebiusHomeomorph_apply]

/-- The scalar formula for the Moebius homeomorphism. -/
@[norm_cast]
lemma coe_unitDiscMoebiusHomeomorph_apply (a z : Complex.UnitDisc) :
    (unitDiscMoebiusHomeomorph a z : ℂ) =
      ((z : ℂ) - (a : ℂ)) / (1 - (starRingEnd ℂ) (a : ℂ) * (z : ℂ)) :=
  by
    rw [unitDiscMoebiusHomeomorph_apply]
    exact coe_unitDiscMoebius a z

/--
The standard automorphism of the complex unit disc, bundled as a homeomorphism.

It is the composition of the Moebius homeomorphism sending `a` to `0` with the fixed
circle rotation by `u`.
-/
noncomputable def unitDiscStandardAutomorphismHomeomorph
    (u : Circle) (a : Complex.UnitDisc) : Complex.UnitDisc ≃ₜ Complex.UnitDisc :=
  (unitDiscMoebiusHomeomorph a).trans (Homeomorph.smul u)

/-- The standard automorphism homeomorphism applies by the existing equivalence formula. -/
@[simp]
lemma unitDiscStandardAutomorphismHomeomorph_apply
    (u : Circle) (a z : Complex.UnitDisc) :
    unitDiscStandardAutomorphismHomeomorph u a z =
      unitDiscStandardAutomorphismEquiv u a z :=
  by
  rw [unitDiscStandardAutomorphismEquiv_apply]
  -- The left side is the bundled homeomorphism composition, while the right side is smul notation.
  change Homeomorph.smul u (unitDiscMoebiusHomeomorph a z) =
    u • unitDiscMoebius a z
  rw [unitDiscMoebiusHomeomorph_apply]
  rfl

/-- The underlying equivalence of the standard automorphism homeomorphism is the existing one. -/
@[simp]
lemma unitDiscStandardAutomorphismHomeomorph_toEquiv
    (u : Circle) (a : Complex.UnitDisc) :
    (unitDiscStandardAutomorphismHomeomorph u a).toEquiv =
      unitDiscStandardAutomorphismEquiv u a :=
  by
    ext z
    exact congrArg (fun w : Complex.UnitDisc => (w : ℂ))
      (unitDiscStandardAutomorphismHomeomorph_apply u a z)

/-- The inverse standard automorphism homeomorphism is inverse rotation followed by the
inverse Moebius homeomorphism. -/
@[simp]
lemma unitDiscStandardAutomorphismHomeomorph_symm
    (u : Circle) (a : Complex.UnitDisc) :
    (unitDiscStandardAutomorphismHomeomorph u a).symm =
      (Homeomorph.smul u⁻¹).trans (unitDiscMoebiusHomeomorph (-a)) := by
  apply Homeomorph.ext
  intro z
  -- `Homeomorph.symm` applies through the inverse of the underlying equivalence.
  change ((unitDiscStandardAutomorphismHomeomorph u a).toEquiv).symm z =
    unitDiscMoebiusHomeomorph (-a) ((Homeomorph.smul u⁻¹) z)
  rw [congrArg Equiv.symm (unitDiscStandardAutomorphismHomeomorph_toEquiv u a),
    unitDiscStandardAutomorphismEquiv_symm]
  -- The equivalence formula uses `MulAction.toPerm`, while the homeomorphism formula uses `smul`.
  change unitDiscMoebiusEquiv (-a) ((MulAction.toPerm u⁻¹ : Equiv.Perm Complex.UnitDisc) z) =
    unitDiscMoebiusHomeomorph (-a) ((Homeomorph.smul u⁻¹) z)
  rw [unitDiscMoebiusEquiv_apply, unitDiscMoebiusHomeomorph_apply, Homeomorph.smul_apply,
    MulAction.toPerm_apply]

/-- The scalar formula for the standard disc-automorphism homeomorphism. -/
@[norm_cast]
lemma coe_unitDiscStandardAutomorphismHomeomorph_apply
    (u : Circle) (a z : Complex.UnitDisc) :
    (unitDiscStandardAutomorphismHomeomorph u a z : ℂ) =
      (u : ℂ) *
        (((z : ℂ) - (a : ℂ)) / (1 - (starRingEnd ℂ) (a : ℂ) * (z : ℂ))) :=
  by
    rw [unitDiscStandardAutomorphismHomeomorph_apply]
    exact coe_unitDiscStandardAutomorphismEquiv_apply u a z

/-- With zero center, the standard automorphism homeomorphism is just rotation. -/
@[simp]
lemma unitDiscStandardAutomorphismHomeomorph_zero (u : Circle) :
    unitDiscStandardAutomorphismHomeomorph u 0 =
      Homeomorph.smul u := by
  ext z
  simp [unitDiscStandardAutomorphismHomeomorph]

/-- With unit rotation factor, the standard automorphism homeomorphism is the Moebius one. -/
@[simp]
lemma unitDiscStandardAutomorphismHomeomorph_one (a : Complex.UnitDisc) :
    unitDiscStandardAutomorphismHomeomorph 1 a = unitDiscMoebiusHomeomorph a := by
  ext z
  simp [unitDiscStandardAutomorphismHomeomorph]

end TauCeti
