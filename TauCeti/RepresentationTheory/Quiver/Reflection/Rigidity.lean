/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Quiver.Reflection.Brick
public import TauCeti.RepresentationTheory.Quiver.Representation.ArrowExtension.Classification

/-!
# Rigidity of indecomposables for positive definite quivers

Every self-extension of a finite-dimensional indecomposable representation of a finite
quiver with positive definite Tits form splits, over any field. The statement allows the
two end terms to be merely isomorphic. Positive definiteness is essential: general
indecomposables can have nontrivial self-extensions.

The endomorphism space has dimension one and the Tits form takes value one, so the
cokernel of the vertex-and-arrow Hom differential vanishes. Its surjectivity supplies compatible
sections of every short exact sequence with these end terms.

## References

I. N. Bernstein, I. M. Gelfand and V. A. Ponomarev, *Coxeter functors and Gabriel's theorem*
(1973); H. Derksen and J. Weyman, *An Introduction to Quiver Representations*, Chapter 1.
-/

public section

namespace TauCeti

open CategoryTheory QuiverRep

universe u v w x

variable {k : Type u} {Q : Type v} [Field k] [Quiver.{w} Q] [Fintype Q]
variable [∀ i j : Q, Fintype (i ⟶ j)]

/-- The self-Hom differential of a finite-dimensional indecomposable for a positive
definite quiver is surjective. Thus every arrow defect is a change of vertex splittings. -/
theorem homDifferential_surjective_of_indecomposable (hpd : (titsForm Q).PosDef)
    (M : QuiverRep.{u, v, w, max v w x} k Q) (hM : Indecomposable M)
    (hfd : IsFinDim k Q M) : Function.Surjective (homDifferential M M) := by
  have hf (i : Q) : FiniteDimensional k (M.obj i) := isFinDim_iff.mp hfd i
  have he : Module.finrank k (M ⟶ M) = 1 :=
    finrank_end_eq_one_of_indecomposable hpd M hM hfd
  apply (homDifferential_surjective_iff M M hf hf).mpr
  rw [← titsForm_def, he, Nat.cast_one]
  exact titsForm_dimVector_eq_one_of_indecomposable_of_isAcyclic
    (isAcyclic_of_titsForm_posDef hpd) hpd M hM hfd

/-- Every extension with isomorphic finite-dimensional indecomposable end terms splits
when the Tits form is positive definite. -/
theorem nonempty_splitting_of_indecomposable_of_titsForm_posDef
    (hpd : (titsForm Q).PosDef)
    {S : ShortComplex (QuiverRep.{u, v, w, max v w x} k Q)} (hS : S.ShortExact)
    (e : S.X₁ ≅ S.X₃) (hM : Indecomposable S.X₃) (hfd : IsFinDim k Q S.X₃) :
    Nonempty S.Splitting := by
  apply nonempty_splitting_of_surjective_homDifferential hS
  have hf₃ (i : Q) : FiniteDimensional k (S.X₃.obj i) := isFinDim_iff.mp hfd i
  have hf₁ (i : Q) : FiniteDimensional k (S.X₁.obj i) :=
    isFinDim_iff.mp (hfd.of_iso e.symm) i
  apply (homDifferential_surjective_iff S.X₃ S.X₁ hf₃ hf₁).mpr
  rw [dimVector_eq_of_iso e, (Linear.homCongr k (Iso.refl S.X₃) e).finrank_eq]
  exact (homDifferential_surjective_iff S.X₃ S.X₃ hf₃ hf₃).mp
    (homDifferential_surjective_of_indecomposable hpd S.X₃ hM hfd)

end TauCeti
