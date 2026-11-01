/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.Algebra.Homology.HomotopyCategory.Shift
public import TauCeti.Algebra.Homology.Cube.EulerCharacteristic
public import TauCeti.KnotTheory.Khovanov.Resolution.Cube

/-!
# The normalized Khovanov complex and Khovanov homology

Let `D` be a planar oriented PD-code with `n₊` positive and `n₋` negative crossings. Its
unnormalized complex, Bar-Natan's bracket `⟦D⟧ = TauCeti.PDCode.khovanovBracket`, has in cochain
degree `r` and quantum degree `j'` the sum of the degree `j' - r` pieces of the circle tensors
`V(S)` over the vertices `S` of height `r`. The normalized Khovanov complex is
`⟦D⟧[-n₋]⟨n₊ - 2n₋⟩`: in bidegree `(i, j)` it is

`Cⁱʲ(D; R) = ⊕[|S| - n₋ = i] V(S)⟨|S| + n₊ - 2n₋⟩ⱼ`,

so an enhanced state lies in the bidegree given by `TauCeti.OrientedPDCode.stateCochainDegree` and
`TauCeti.OrientedPDCode.enhancedQuantumDegree`. The quantum shift is a reindexing of the family of
quantum components, and the cochain shift is Mathlib's shift of cochain complexes, so the
differential of the normalized complex is that of the bracket multiplied by `(-1) ^ n₋`. The
Khovanov homology `Khⁱʲ(D; R)` is the cohomology in degree `i` of the quantum component `j`.

The normalized complex is strictly supported in the cochain degrees `-n₋, …, n₊`, and its terms
are finite free `R`-modules.

## Main definitions

* `TauCeti.OrientedPDCode.khovanovComplex D hD R`: the normalized Khovanov complex, a graded object
  of cochain complexes indexed by the quantum degree.
* `TauCeti.OrientedPDCode.khovanovHomology D hD R i j`: the Khovanov homology `Khⁱʲ(D; R)`.

## Main results

* `TauCeti.OrientedPDCode.khovanovComplexXIso`: the term in bidegree `(i, j)` is the term of the
  bracket in cochain degree `i + n₋` and quantum degree `j - (n₊ - 2n₋)`.
* The normalized complex is strictly supported in the cochain degrees from `-n₋` to `n₊`, and its
  terms, like those of the bracket, are finite free.

## References

* M. Khovanov, *A categorification of the Jones polynomial*, Duke Math. J. 101 (2000).
* D. Bar-Natan, *On Khovanov's categorification of the Jones polynomial*, Algebr. Geom. Topol. 2
  (2002), §2.2.
-/

public section

noncomputable section

open CategoryTheory

universe u

namespace TauCeti.PDCode

variable {n : ℕ} (D : PDCode n) (hD : D.IsPlanar) (R : Type u) [CommRing R]

/-- The terms of the bracket are free. -/
instance (j r : ℤ) : Module.Free R ((D.khovanovBracket hD R j).X r) := by
  rw [khovanovBracket_apply]
  infer_instance

/-- The terms of the bracket are finitely generated. -/
instance (j r : ℤ) : Module.Finite R ((D.khovanovBracket hD R j).X r) := by
  rw [khovanovBracket_apply]
  infer_instance

end TauCeti.PDCode

namespace TauCeti.OrientedPDCode

variable {n : ℕ} (D : OrientedPDCode n) (hD : D.toPDCode.IsPlanar) (R : Type u) [CommRing R]

/-- **The normalized Khovanov complex** `⟦D⟧[-n₋]⟨n₊ - 2n₋⟩` of a planar oriented code `D` with
`n₊` positive and `n₋` negative crossings, as a family of cochain complexes indexed by the quantum
degree. Its quantum component `j` is the quantum component `j - (n₊ - 2n₋)` of the bracket
`TauCeti.PDCode.khovanovBracket`, shifted so that the cochain degree `r` of the bracket becomes
`r - n₋`. -/
def khovanovComplex : GradedObject ℤ (CochainComplex (ModuleCat.{u} R) ℤ) :=
  fun j ↦ (D.toPDCode.khovanovBracket hD R
    (j - ((D.positiveCrossingCount : ℤ) - 2 * D.negativeCrossingCount)))⟦
      (D.negativeCrossingCount : ℤ)⟧

/-- The quantum component `j` of the normalized Khovanov complex is the shift by `n₋` of the
quantum component `j - (n₊ - 2n₋)` of the bracket. -/
theorem khovanovComplex_apply (j : ℤ) :
    D.khovanovComplex hD R j =
      (D.toPDCode.khovanovBracket hD R
        (j - ((D.positiveCrossingCount : ℤ) - 2 * D.negativeCrossingCount)))⟦
          (D.negativeCrossingCount : ℤ)⟧ :=
  (rfl)

/-- The term of the normalized Khovanov complex in bidegree `(i, j)` is the term of the bracket in
cochain degree `i + n₋` and quantum degree `j - (n₊ - 2n₋)`. -/
def khovanovComplexXIso (i j : ℤ) :
    (D.khovanovComplex hD R j).X i ≅
      (D.toPDCode.khovanovBracket hD R
        (j - ((D.positiveCrossingCount : ℤ) - 2 * D.negativeCrossingCount))).X
          (i + D.negativeCrossingCount) :=
  CochainComplex.shiftFunctorObjXIso _ _ _ _ rfl

/-- The normalized Khovanov complex vanishes below the cochain degree `-n₋`. -/
instance (j : ℤ) : (D.khovanovComplex hD R j).IsStrictlyGE (-D.negativeCrossingCount) := by
  rw [khovanovComplex_apply, PDCode.khovanovBracket_apply]
  exact CochainComplex.isStrictlyGE_shift _ 0 _ _ (add_neg_cancel _)

/-- The normalized Khovanov complex vanishes above the cochain degree `n₊`. -/
instance (j : ℤ) : (D.khovanovComplex hD R j).IsStrictlyLE D.positiveCrossingCount := by
  rw [khovanovComplex_apply, PDCode.khovanovBracket_apply]
  refine CochainComplex.isStrictlyLE_shift _ (Fintype.card (Fin n)) _ _ ?_
  have := D.positiveCrossingCount_add_negativeCrossingCount
  rw [Fintype.card_fin]
  omega

/-- The terms of the normalized Khovanov complex are free. -/
instance (i j : ℤ) : Module.Free R ((D.khovanovComplex hD R j).X i) :=
  .of_equiv (D.khovanovComplexXIso hD R i j).toLinearEquiv.symm

/-- The terms of the normalized Khovanov complex are finitely generated. -/
instance (i j : ℤ) : Module.Finite R ((D.khovanovComplex hD R j).X i) :=
  .equiv (D.khovanovComplexXIso hD R i j).toLinearEquiv.symm

/-- **Khovanov homology** `Khⁱʲ(D; R)` of a planar oriented code `D`: the cohomology in cochain
degree `i` of the quantum component `j` of the normalized Khovanov complex. -/
def khovanovHomology (i j : ℤ) : ModuleCat.{u} R :=
  (D.khovanovComplex hD R j).homology i

/-- Khovanov homology in bidegree `(i, j)` is the cohomology in degree `i` of the quantum
component `j` of the normalized Khovanov complex. -/
theorem khovanovHomology_def (i j : ℤ) :
    D.khovanovHomology hD R i j = (D.khovanovComplex hD R j).homology i :=
  (rfl)

end TauCeti.OrientedPDCode
