/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

import TauCeti.AlgebraicGeometry.Normalization.Modification
import TauCeti.AlgebraicGeometry.Normalization.Regular
import TauCeti.RingTheory.Nagata

/-!
# Examples of finite normalizations

On an integral scheme whose affine opens have Nagata rings of sections, the normalization in any
finite extension of the function field is finite, since a Nagata domain is Japanese. With
Japanese rings of sections this discharges the finiteness hypothesis of resolution of curves: for
an integral locally Noetherian scheme of dimension at most one, the normalization in a finite
extension of the function field is regular, and the normalization in the function field itself is
moreover a modification.
-/

open CategoryTheory AlgebraicGeometry TauCeti.AlgebraicGeometry TauCeti.Ring

universe u

variable {Y : Scheme.{u}} [IsIntegral Y] (L : Type u) [Field L] [Algebra Y.functionField L]
  [FiniteDimensional Y.functionField L]

-- Nagata rings of sections suffice for finiteness, as a Nagata domain is Japanese.
example (hY : ∀ U : Y.Opens, IsAffineOpen U → IsNagata Γ(Y, U)) :
    IsFinite (Spec.map (CommRingCat.ofHom (algebraMap Y.functionField L)) ≫
      Y.fromSpecStalk (genericPoint Y)).fromNormalization :=
  isFinite_fromNormalization_of_isJapanese L fun U hU _ ↦ have := hY U hU; inferInstance

-- Resolution of curves in a finite extension of the function field, with no finiteness
-- hypothesis: the normalization is regular.
example [IsLocallyNoetherian Y] (hdim : topologicalKrullDim Y ≤ 1)
    (hY : ∀ U : Y.Opens, IsAffineOpen U → ∀ [Nonempty U], IsJapanese Γ(Y, U)) :
    IsRegular (Spec.map (CommRingCat.ofHom (algebraMap Y.functionField L)) ≫
      Y.fromSpecStalk (genericPoint Y)).normalization :=
  have := isFinite_fromNormalization_of_isJapanese L hY
  isRegular_normalization_of_field hdim _

-- Resolution of curves in the function field: the normalization is regular and a modification.
example [IsLocallyNoetherian Y] (hdim : topologicalKrullDim Y ≤ 1)
    (hY : ∀ U : Y.Opens, IsAffineOpen U → ∀ [Nonempty U], IsJapanese Γ(Y, U)) :
    IsRegular (Y.fromSpecStalk (genericPoint Y)).normalization ∧
      IsModification (Y.fromSpecStalk (genericPoint Y)).fromNormalization :=
  have := isFinite_fromNormalization_fromSpecStalk_genericPoint_iff.mpr fun U hU _ ↦
    have := hY U hU; inferInstance
  ⟨isRegular_normalization_fromSpecStalk_genericPoint hdim, inferInstance⟩
