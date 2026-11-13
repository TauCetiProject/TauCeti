/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.FiniteEtale.Henselian
public import TauCeti.AlgebraicGeometry.FiniteEtale.PuncturedSpectrum

/-!
# Extending finite étale covers from a henselian section

Let `A → A'` be a homomorphism of local rings such that the closed point is the only point of
`Spec A'` over the closed point of `Spec A`, so that the punctured spectrum `U'` of `A'` maps to
the punctured spectrum `U` of `A`. Restricting a finite étale scheme over `Spec A` to `U` and then
pulling back to `U'` agrees with pulling back to `Spec A'` and then restricting to `U'`
(`TauCeti.IsLocalRing.restrictPuncturedCompPullbackIso`).

Suppose every finite étale scheme over `Spec A'` comes from `Spec A`, and pullback of finite étale
covers from `U` to `U'` is fully faithful. Then a finite étale cover `V` of `U` extends across the
closed point of `Spec A` as soon as its pullback to `U'` extends across the closed point of
`Spec A'`. Indeed, if `Y'` over `Spec A'` extends the pullback of `V`, choose `Y` over `Spec A`
whose pullback is `Y'`; the restriction of `Y` to `U` and `V` have isomorphic pullbacks to `U'`,
so they are isomorphic.

The main case is the quotient `A' = A ⧸ I` by an ideal for which `(A, I)` is a henselian pair,
where every finite étale scheme over `Spec (A ⧸ I)` lifts
(`TauCeti.FiniteEtaleScheme.essSurj_pullback_quotient`). For `I = (f)` this is the reduction, in
the proof of the local Lefschetz extension theorem (Stacks, Lemma 58.20.7 (0BLM)), of the
extension of a cover `V` whose restriction to the hypersurface section extends, to the full
faithfulness of restriction to the punctured spectrum of `A ⧸ (f)` (Stacks, Lemma 58.19.7 (0BLJ),
for depth at least three). The same argument shows that purity (`TauCeti.IsLocalRing.PurityHolds`)
passes from `A ⧸ I` to `A` under the full faithfulness hypothesis; for a henselian pair `(A, (f))`
this is the shape of the inductive step in the proof of purity for regular local rings (Stacks,
Lemma 58.21.3 (0BMA)).

The general statements, for any such `A → A'`, are
`TauCeti.IsLocalRing.extends_iff_extends_pullback` and
`TauCeti.IsLocalRing.purityHolds_of_purityHolds_of_fullyFaithful`, and the restriction to the
punctured spectrum of `A ⧸ I` is `TauCeti.IsLocalRing.restrictPuncturedQuotient`; this file
specialises them to henselian pairs.

## Main results

* `TauCeti.IsLocalRing.extends_iff_extends_quotient`: for a henselian pair `(A, I)` such that
  restriction from `U` to the punctured spectrum of `A ⧸ I` is fully faithful, a finite étale
  cover of `U` extends to `Spec A` if and only if its restriction to the punctured spectrum of
  `A ⧸ I` extends to `Spec (A ⧸ I)`.
* `TauCeti.IsLocalRing.purityHolds_of_purityHolds_quotient`: for a henselian pair `(A, I)` such
  that restriction from `U` to the punctured spectrum of `A ⧸ I` is fully faithful, purity for
  `A ⧸ I` implies purity for `A`.

## References

* [The Stacks Project, Lemma 58.20.7](https://stacks.math.columbia.edu/tag/0BLM), the local
  Lefschetz extension theorem.
* [The Stacks Project, Lemma 58.19.7](https://stacks.math.columbia.edu/tag/0BLJ), full
  faithfulness of restriction to the punctured spectrum of a hypersurface section.
* [The Stacks Project, Lemma 15.13.2](https://stacks.math.columbia.edu/tag/09ZL), finite étale
  algebras over a henselian pair.
-/

public section

noncomputable section

open CategoryTheory AlgebraicGeometry IsLocalRing

universe u

namespace TauCeti.IsLocalRing

section Quotient

variable {A : Type u} [CommRing A] [IsLocalRing A] (I : Ideal A) [IsLocalRing (A ⧸ I)]
  [HenselianRing A I]

/-- `TauCeti.FiniteEtaleScheme.essSurj_pullback_quotient`, stated for `algebraMap A (A ⧸ I)`,
which is `Ideal.Quotient.mk I`. -/
local instance : (FiniteEtaleScheme.pullback
    (Spec.map (CommRingCat.ofHom (algebraMap A (A ⧸ I))))).EssSurj := by
  rw [Ideal.Quotient.algebraMap_eq]
  infer_instance

variable [(restrictPuncturedQuotient I).Full] [(restrictPuncturedQuotient I).Faithful]

/-- **Extension from a henselian section.** Let `(A, I)` be a henselian pair with `A` local, and
suppose restriction of finite étale covers from the punctured spectrum of `A` to that of `A ⧸ I`
is fully faithful. Then a finite étale cover of the punctured spectrum of `A` extends across the
closed point if and only if its restriction to the punctured spectrum of `A ⧸ I` extends across
the closed point of `Spec (A ⧸ I)`. For `I = (f)`, full faithfulness is Stacks, Lemma 58.19.7
(0BLJ), and the statement is then Stacks, Lemma 58.20.7 (0BLM) for henselian pairs. -/
theorem extends_iff_extends_quotient (V : FiniteEtaleScheme (puncturedSpectrum A).toScheme) :
    (∃ Y : FiniteEtaleScheme (Spec (.of A)), Nonempty ((restrictPunctured A).obj Y ≅ V)) ↔
      ∃ Y₀ : FiniteEtaleScheme (Spec (.of (A ⧸ I))),
        Nonempty ((restrictPunctured (A ⧸ I)).obj Y₀ ≅
          (restrictPuncturedQuotient I).obj V) :=
  extends_iff_extends_pullback _ V

/-- **Purity from a henselian section.** Let `(A, I)` be a henselian pair with `A` local, and
suppose restriction of finite étale covers from the punctured spectrum of `A` to that of `A ⧸ I`
is fully faithful. If purity holds for `A ⧸ I`, then purity holds for `A`. -/
theorem purityHolds_of_purityHolds_quotient (hI : PurityHolds (A ⧸ I)) : PurityHolds A :=
  purityHolds_of_purityHolds_of_fullyFaithful _ hI

end Quotient

end TauCeti.IsLocalRing
