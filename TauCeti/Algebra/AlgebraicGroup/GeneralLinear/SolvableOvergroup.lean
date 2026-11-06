/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.GeneralLinear.Weight.Torus
public import TauCeti.Algebra.AlgebraicGroup.HopfIdeal.Quotient.Basic
public import TauCeti.Algebra.AlgebraicGroup.Connected.CommHopfAlgCat
public import TauCeti.Algebra.AlgebraicGroup.Solvable.Basic
import TauCeti.Algebra.AlgebraicGroup.Solvable.LieKolchin
import TauCeti.Algebra.Coalgebra.Comodule.Flag.Basic
import TauCeti.Algebra.Coalgebra.Subcomodule.Corestrict

/-!
# Matrix-entry equations from invariant coordinate lines

For a reduced connected solvable subgroup of a general linear group containing a torus with
pairwise distinct coordinate characters, Lie–Kolchin supplies a coordinate flag. If containment
of coordinate line `a` in any invariant subspace forces containment of line `b`, and `a ≠ b`,
then the reverse matrix entry vanishes in the subgroup's coordinate algebra.

This is the common flag argument used for the positive E6, E7, and type-B spin subgroups,
extracted from their `Generated.Positive.SolvableOvergroup` modules.
-/

public section

namespace TauCeti.GeneralLinear

universe u v

variable {k : Type u} [Field k] [IsAlgClosed k] {n : ℕ}

/-- Distinct torus characters and propagation of invariant coordinate lines force a universal
matrix-entry equation in a reduced geometrically connected solvable subgroup of `GL n`. -/
theorem quotient_genericMatrix_eq_zero_of_single_mem
    (J : HopfIdeal k (coordinateHopfAlgebra k n))
    [IsReduced (coordinateHopfAlgebra k n ⧸ J.toIdeal)]
    (hconn : geometricallyConnectedCommHopfAlgProperty k
      (CommHopfAlgCat.quotient (coordinateHopfAlgebra k n) J))
    (hsolv : geometricallySolvablePointsCommHopfAlgProperty k
      (CommHopfAlgCat.quotient (coordinateHopfAlgebra k n) J))
    {ι : Type v} [Fintype ι] (μ : Fin n → ι → ℤ)
    (π : (coordinateHopfAlgebra k n ⧸ J.toIdeal) →ₐc[k]
      MonoidAlgebra k (Multiplicative (ι →₀ ℤ)))
    (hπ : π.comp (Bialgebra.Quotient.mkBialgHom (R := k) J.toIdeal) =
      weightTorusCoordinateBialgHom (S := k) μ)
    (hinj : Function.Injective (fun a ↦ SplitTorus.weightCharacter (μ a)))
    {a b : Fin n} (hne : a ≠ b)
    (hmem :
      let _ := corestrictStandardComodule k n
        (Bialgebra.Quotient.mkBialgHom (R := k) J.toIdeal)
      ∀ N : Subcomodule k (coordinateHopfAlgebra k n ⧸ J.toIdeal) (Fin n → k),
        Pi.single a (1 : k) ∈ N → Pi.single b (1 : k) ∈ N) :
    Bialgebra.Quotient.mkBialgHom (R := k) J.toIdeal (genericMatrix k n a b) = 0 := by
  classical
  let H := coordinateHopfAlgebra k n ⧸ J.toIdeal
  let q := Bialgebra.Quotient.mkBialgHom (R := k) J.toIdeal
  let _ := corestrictStandardComodule k n q
  have hweights := corestrict_corestrict_standardComodule_eq_ofWeights q π μ hπ
  -- Lie–Kolchin supplies a stable flag; the distinct torus characters make it coordinate.
  obtain ⟨d, bas, htri, _⟩ :=
    Comodule.exists_basis_coefficientMatrix_isUpperTriangular_of_geometricallySolvable
      (M := Fin n → k) hconn hsolv
  let F := Comodule.flagSubcomodule bas htri
  have hbas (r : Fin (d + 1)) : bas.flag r = Submodule.span k
      ((Pi.basisFun k (Fin n)) '' {a | Pi.single a (1 : k) ∈ bas.flag r}) := by
    have hcoord := Subcomodule.toSubmodule_eq_span_of_corestrict_eq_ofWeights π.toCoalgHom
      (fun a ↦ SplitTorus.weightCharacter (μ a)) hinj hweights (F r)
    simpa only [F, Comodule.flagSubcomodule_toSubmodule,
      ← Subcomodule.mem_toSubmodule] using hcoord
  have hzero : Comodule.coefficientMatrix (C := H) (Pi.basisFun k (Fin n)) a b = 0 := by
    apply Comodule.coefficient_eq_zero_of_coordinate_flag (Pi.basisFun k _) bas htri
    · simpa only [Pi.basisFun_apply] using hbas
    · exact hne
    · simpa only [Pi.basisFun_apply] using hmem
  have hcoeff : Comodule.coefficientMatrix (C := H) (Pi.basisFun k (Fin n)) =
      (genericMatrix k n).map q := by
    let _ := standardComodule k n
    rw [← coefficientMatrix_basisFun]
    exact Comodule.coefficientMatrix_corestrict (Pi.basisFun k _) q.toCoalgHom
  simpa only [hcoeff, Matrix.map_apply] using hzero

end TauCeti.GeneralLinear
