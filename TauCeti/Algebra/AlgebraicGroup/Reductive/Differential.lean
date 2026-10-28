/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Algebra.AlgebraicGroup.Solvable.Radical.Reductive
public import TauCeti.Algebra.AlgebraicGroup.Solvable.Radical.LieContainment
public import TauCeti.Algebra.AlgebraicGroup.Torus.Differential

/-!
# The central action in differentiated reductive representations

Over an algebraically closed field of characteristic zero, the center of the Lie algebra
of a reductive affine group acts diagonally in every rational representation. In particular
each central tangent vector acts semisimply, including on representations of infinite dimension.
This supplies the central-action condition in complete reducibility for reductive Lie algebras;
arbitrary representations of a reductive Lie algebra need not satisfy that condition.

The center is the Lie algebra of the solvable radical, which is a torus. The comparison uses
`FiniteTypeCommHopfAlgCat.lieIdeal_solvableRadicalDefiningIdeal_eq_radical`,
the inclusion of the Lie center in the Lie radical, and
`reductiveCommHopfAlgProperty.torus_solvableRadical`. The torus weight decomposition then
diagonalizes its differentiated action.

## References

* J. E. Humphreys, *Linear Algebraic Groups*, §13.
* J. S. Milne, *Algebraic Groups* (2017), Chapters 19 and 22.
* J. C. Jantzen, *Representations of Algebraic Groups*, I.2 and I.7.
-/

public section

namespace TauCeti.reductiveCommHopfAlgProperty

universe u w

variable {k : Type u} [Field k] [IsAlgClosed k] [CharZero k]
variable {H : FiniteTypeCommHopfAlgCat.{u, u} k}
variable (hH : reductiveCommHopfAlgProperty k H)
variable (V : Type w) [AddCommGroup V] [Module k V] [Comodule k H V]

include hH

/-- In a rational representation of a reductive group in characteristic zero, the
eigenspaces of any central tangent vector span the representation. -/
theorem iSup_eigenspace_differential_eq_top_of_mem_center
    (d : Derivation k H (Bialgebra.CounitAlgebra k H k))
    (hd : d ∈ LieAlgebra.center k (Derivation k H (Bialgebra.CounitAlgebra k H k))) :
    ⨆ μ : k, Module.End.eigenspace
      (Comodule.differential (R := k) (H := H) (M := V) d) μ = ⊤ := by
  let _ : ConnectedSpace (PrimeSpectrum H) :=
    hH.geometricallyConnected.connectedSpace k H.obj
  let I := FiniteTypeCommHopfAlgCat.solvableRadicalDefiningIdeal H
  have hdR := LieAlgebra.center_le_radical k
    (Derivation k H (Bialgebra.CounitAlgebra k H k)) hd
  rw [← FiniteTypeCommHopfAlgCat.lieIdeal_solvableRadicalDefiningIdeal_eq_radical H] at hdR
  have hI : d ∈ I.lieSubalgebra (B := k) := by
    exact (I.mem_lieSubalgebra_iff d).mpr
      ((HopfIdeal.IsNormal.mem_lieIdeal_iff
        (FiniteTypeCommHopfAlgCat.isNormal_solvableRadicalDefiningIdeal H) d).mp hdR)
  let e := I.quotientLieEquiv (B := k)
  have he : I.quotientLieHom (e.symm ⟨d, hI⟩) = d := by
    rw [← I.quotientLieEquiv_apply_coe]
    exact congrArg Subtype.val (e.apply_symm_apply ⟨d, hI⟩)
  have h := hH.torus_solvableRadical.iSup_eigenspace_differential_eq_top V
    (Bialgebra.Quotient.mkBialgHom I.toIdeal) (e.symm ⟨d, hI⟩)
  rwa [← I.quotientLieHom_apply, he] at h

/-- Every central element of the Lie algebra of a reductive group acts semisimply
in every rational representation over an algebraically closed field of characteristic zero. -/
theorem isSemisimple_differential_of_mem_center
    (d : Derivation k H (Bialgebra.CounitAlgebra k H k))
    (hd : d ∈ LieAlgebra.center k (Derivation k H (Bialgebra.CounitAlgebra k H k))) :
    Module.End.IsSemisimple (Comodule.differential (R := k) (H := H) (M := V) d) :=
  isSemisimple_of_iSup_eigenspace_eq_top
    (hH.iSup_eigenspace_differential_eq_top_of_mem_center V d hd)

end TauCeti.reductiveCommHopfAlgProperty
