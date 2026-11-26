/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.Blowup.ExceptionalDivisor
public import TauCeti.AlgebraicGeometry.Blowup.Pullback
public import TauCeti.AlgebraicGeometry.EffectiveCartierDivisor.AffineLine
public import TauCeti.AlgebraicGeometry.Morphisms.Modification.StrictTransform.Basic
public import TauCeti.Examples.AlgebraicGeometry.Blowup.Modification

/-!
# The strict transform of a line under the blowup of the plane at the origin

Let `b : Bl_0 𝔸²_k ⟶ 𝔸²_k` be the blowup of `𝔸²_k = Spec k[x, y]` at the origin and
`L = V(y) = Spec k[t]` the line `y = 0`, embedded by `x ↦ t`, `y ↦ 0`. The ideal of the origin
pulls back to the ideal `(t)` of the origin of `L`, which is an effective Cartier divisor since
`t` is a nonzerodivisor. Hence the blowup `Bl_{(t)} L ⟶ L` is an isomorphism
(`Scheme.IdealSheafData.isIso_blowupToBase_iff`), and the strict transform of `L`, the ideal
sheaf of the closed immersion `Bl_{(t)} L ⟶ L ×_{𝔸²} Bl_0 𝔸²`
(`Scheme.Hom.strictTransform_blowupToBase`), is the ideal sheaf of a closed immersion
`L ⟶ L ×_{𝔸²} Bl_0 𝔸²` that is a section of the projection to `L`: the strict transform is a copy
of the line. The exceptional divisor of `Bl_0 𝔸²` pulls back along it to the origin `V(t)` of `L`,
a single point.

* `TauCeti.BlowupStrictTransformLineExample.lineι`: the line `V(y)`.
* `TauCeti.BlowupStrictTransformLineExample.comap_originIdealSheaf_lineι`: the origin pulls back
  to `V(t)`.
* `TauCeti.BlowupStrictTransformLineExample.isIso_blowupToBase`: the blowup of `L` at the origin
  is an isomorphism.
* `TauCeti.BlowupStrictTransformLineExample.strictTransformι`: the closed immersion of `L` onto
  its strict transform, with `ker_strictTransformι` and `strictTransformι_fst`.
* `TauCeti.BlowupStrictTransformLineExample.comap_comap_strictTransformι_snd`: the exceptional
  divisor pulls back to `V(t)`.
-/

public section

noncomputable section

open CategoryTheory Limits AlgebraicGeometry TauCeti.AlgebraicGeometry

namespace TauCeti.BlowupStrictTransformLineExample

open BlowupModificationExample Scheme.IdealSheafData

variable (k : Type) [Field k]

/-- The line `V(y)` in `𝔸²_k = Spec k[x, y]`, as `Spec k[t] ⟶ Spec k[x, y]` with `x ↦ t` and
`y ↦ 0`. -/
abbrev lineι : Spec (.of (Polynomial k)) ⟶ Spec (.of (MvPolynomial (Fin 2) k)) :=
  Spec.map (CommRingCat.ofHom (MvPolynomial.aeval ![Polynomial.X, 0]).toRingHom)

/-- The ideal of the origin of `𝔸²_k` pulls back to the ideal `(t)` of the origin of the line. -/
theorem comap_originIdealSheaf_lineι :
    (originIdealSheaf k).comap (lineι k) = (Polynomial.X : Polynomial k).zeroIdealSheaf := by
  rw [originIdealSheaf_def, comap_ofIdealTop_map_ΓSpecIso_inv,
    Polynomial.zeroIdealSheaf_eq_ofIdealTop, Ideal.map_span, Set.image_pair]
  simp [Set.pair_comm _ (0 : Polynomial k)]

/-- The origin of the line is an effective Cartier divisor. -/
theorem isEffectiveCartier_comap_originIdealSheaf_lineι :
    ((originIdealSheaf k).comap (lineι k)).IsEffectiveCartier := by
  rw [comap_originIdealSheaf_lineι]
  exact Polynomial.monic_X.isRelativeEffectiveCartier_zeroIdealSheaf.isEffectiveCartier

/-- The blowup of the line at the origin is an isomorphism. -/
instance isIso_blowupToBase : IsIso ((originIdealSheaf k).comap (lineι k)).blowupToBase :=
  (isIso_blowupToBase_iff _).mpr (isEffectiveCartier_comap_originIdealSheaf_lineι k)

/-- The closed immersion `L ⟶ L ×_{𝔸²} Bl_0 𝔸²` of the line onto its strict transform. -/
def strictTransformι :
    Spec (.of (Polynomial k)) ⟶ pullback (lineι k) (originIdealSheaf k).blowupToBase :=
  inv ((originIdealSheaf k).comap (lineι k)).blowupToBase ≫
    (originIdealSheaf k).blowupBaseChangeHom (lineι k)

/-- The strict transform of the line is a section of the projection to the line. -/
@[reassoc (attr := simp)]
theorem strictTransformι_fst : strictTransformι k ≫ pullback.fst _ _ = 𝟙 _ := by
  simp [strictTransformι]

/-- `strictTransformι` is a closed immersion. -/
instance isClosedImmersion_strictTransformι : IsClosedImmersion (strictTransformι k) := by
  rw [strictTransformι]
  infer_instance

/-- **The strict transform of the line is the line.** The strict transform of `L` under the
blowup of `𝔸²_k` at the origin is the ideal sheaf of the closed immersion `strictTransformι` of
`L` into `L ×_{𝔸²} Bl_0 𝔸²`. -/
theorem ker_strictTransformι :
    (strictTransformι k).ker = Scheme.Hom.strictTransform (lineι k)
      (originIdealSheaf k).blowupToBase (originIdealSheaf k).support.compl := by
  rw [Scheme.Hom.strictTransform_blowupToBase, strictTransformι, Scheme.Hom.ker_comp_of_isIso]

/-- **The exceptional divisor meets the strict transform of the line in the origin.** The
exceptional divisor of `Bl_0 𝔸²_k` pulls back along `L ⟶ L ×_{𝔸²} Bl_0 𝔸² ⟶ Bl_0 𝔸²` to the
ideal `(t)` of the origin of `L`. -/
theorem comap_comap_strictTransformι_snd :
    ((originIdealSheaf k).comap (originIdealSheaf k).blowupToBase).comap
        (strictTransformι k ≫ pullback.snd _ _) = (Polynomial.X : Polynomial k).zeroIdealSheaf := by
  rw [strictTransformι, Category.assoc, blowupBaseChangeHom_snd, comap_comp, comap_comap_blowupMap,
    ← comap_comp, IsIso.inv_hom_id, comap_id, comap_originIdealSheaf_lineι]

end TauCeti.BlowupStrictTransformLineExample
