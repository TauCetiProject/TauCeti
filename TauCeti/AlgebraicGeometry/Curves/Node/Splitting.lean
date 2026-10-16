/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.Curves.Node.FiniteEtale
public import TauCeti.AlgebraicGeometry.FiniteEtale.Splitting

/-!
# Splitting the nodes of a proper nodal curve

The singular subscheme of a proper nodal curve is finite étale. After one finite separable
extension it therefore becomes a finite collection of rational points, with their reduced
scheme structures. The splitting below is over the extended field and applies to every
chosen base change of the curve. Its independence from that choice follows from the
pullback square for the relative singular subscheme.

This labels nodes only. Splitting their branches and the geometric components is additional
data, not a consequence asserted here.

## References

* The Stacks Project, Tag 0C58 (families of nodal curves).
* The Stacks Project, Tag 03QR (schemes étale over a point).
-/

public section

open CategoryTheory Limits AlgebraicGeometry TauCeti.AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme

/-- All nodes of a proper nodal curve split over one finite separable field extension.
For any chosen base change of the curve, its singular subscheme is the spectrum of a
product of copies of the extended field, as a scheme over that field. This includes the
smooth case, in which the node set is empty. -/
theorem exists_split_singularLocus {K : Type u} [Field K]
    (X : Scheme.{u}) [X.Over (Spec (.of K))] [IsProper (X ↘ Spec (.of K))]
    (hnodal : AtWorstNodalOfRelativeDimensionOne (X ↘ Spec (.of K))) :
    ∃ (L : Type u) (_ : Field L) (_ : Algebra K L)
      (_ : Module.Finite K L) (_ : Algebra.IsSeparable K L) (n : ℕ),
      ∀ (X' : Scheme.{u}) (_ : X'.Over (Spec (.of L))) (g : X' ⟶ X)
        (H : IsPullback g (X' ↘ Spec (.of L)) (X ↘ Spec (.of K))
          (Spec.algebraMap K L)),
        letI : SyntomicOfRelativeDimension 1 (X' ↘ Spec (.of L)) :=
          (hnodal.of_isPullback H).syntomic
        Nonempty (Over.mk ((X'.singularLocus L).subschemeι ≫ (X' ↘ Spec (.of L))) ≅
          Over.mk (Spec.algebraMap L (Fin n → L))) := by
  have : SyntomicOfRelativeDimension 1 (X ↘ Spec (.of K)) := hnodal.syntomic
  have : IsFinite ((X.singularLocus K).subschemeι ≫ (X ↘ Spec (.of K))) :=
    X.isFinite_singularLocus_subschemeι_comp hnodal
  have : Etale ((X.singularLocus K).subschemeι ≫ (X ↘ Spec (.of K))) :=
    X.etale_singularLocus_subschemeι_comp hnodal
  obtain ⟨L, _, _, _, _, n, ⟨e⟩⟩ :=
    ((X.singularLocus K).subschemeι ≫ (X ↘ Spec (.of K))).exists_split_of_isFinite_of_etale
  refine ⟨L, inferInstance, inferInstance, inferInstance, inferInstance, n, ?_⟩
  intro X' _ g H
  have : SyntomicOfRelativeDimension 1 (X' ↘ Spec (.of L)) :=
    (hnodal.of_isPullback H).syntomic
  have Hsing := Scheme.isPullback_singularLocus_subschemeι H
  have Hbase := Hsing.flip.paste_vert H
  let e' : Over.mk ((X'.singularLocus L).subschemeι ≫ (X' ↘ Spec (.of L))) ≅
      Over.mk (pullback.snd ((X.singularLocus K).subschemeι ≫ (X ↘ Spec (.of K)))
        (Spec.algebraMap K L)) :=
    Over.isoMk Hbase.isoPullback (by simp)
  exact ⟨e' ≪≫ e⟩

end AlgebraicGeometry.Scheme
