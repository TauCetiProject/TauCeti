/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.AlgebraicGeometry.Morphisms.Flat.Generic

/-!
# Flatness of homogeneous morphisms

Suppose automorphisms of the source and target commute with a scheme morphism and
act transitively on the closed points of the target. Over a Jacobson target,
flatness above one nonempty open subset then implies flatness everywhere. The
translates of that open cover the target: their complement is closed and has no
closed points. Flatness is checked on all stalks, including those at nonclosed
points.

Combining this propagation result with generic flatness proves that a finite-type
homogeneous morphism to a reduced locally Noetherian Jacobson scheme is flat.
This is the translation argument used for orbit morphisms and homogeneous spaces.
The automorphisms need not be supplied as a group action; only the commuting
squares and transitivity are used.

The proof uses `Scheme.Hom.flat_restrict_iff`, `Scheme.Hom.exists_dense_open_flat`,
and Mathlib's invariance of ring-map flatness under isomorphisms.

## References

* J. S. Milne, *Algebraic Groups* (2017), Proposition 1.65(a), flatness of equivariant
  morphisms; §§7.c–7.f, orbits and homogeneous spaces.
-/

public section

open CategoryTheory TopologicalSpace Topology

namespace AlgebraicGeometry.Scheme.Hom

universe u v

variable {X Y : Scheme.{u}} (f : X ⟶ Y)

/-- A commuting square of scheme isomorphisms preserves flatness at corresponding
source stalks. -/
theorem flat_stalkMap_iff_of_isos (a : X ≅ X) (b : Y ≅ Y)
    (h : a.hom ≫ f = f ≫ b.hom) (x : X) :
    (f.stalkMap (a.hom x)).hom.Flat ↔ (f.stalkMap x).hom.Flat := by
  have : IsIso (b.hom.stalkMap (f x)) := inferInstance
  have hcomp : CommRingCat.flat ((a.hom ≫ f).stalkMap x) ↔
      CommRingCat.flat ((f ≫ b.hom).stalkMap x) := by
    rw [stalkMap_congr_hom _ _ h]
    exact CommRingCat.flat.cancel_left_of_respectsIso _ _
  have hleft : CommRingCat.flat ((a.hom ≫ f).stalkMap x) ↔
      CommRingCat.flat (f.stalkMap (a.hom x)) := by
    rw [stalkMap_comp]
    exact CommRingCat.flat.cancel_right_of_respectsIso _ _
  have hright : CommRingCat.flat ((f ≫ b.hom).stalkMap x) ↔
      CommRingCat.flat (f.stalkMap x) := by
    rw [stalkMap_comp]
    exact CommRingCat.flat.cancel_left_of_respectsIso
      (b.hom.stalkMap (f x)) (f.stalkMap x)
  exact hleft.symm.trans (hcomp.trans hright)

/-- Flatness above an open subset is preserved by compatible source and target
translations. The translated open is the inverse image under the target isomorphism. -/
theorem flat_restrict_preimage_iff_of_isos (a : X ≅ X) (b : Y ≅ Y)
    (h : a.hom ≫ f = f ≫ b.hom) (U : Y.Opens) :
    Flat (f ∣_ b.hom ⁻¹ᵁ U) ↔ Flat (f ∣_ U) := by
  simp only [flat_restrict_iff]
  constructor
  · intro hflat x hx
    have heq : b.hom (f (a.inv x)) = f x := by
      rw [← Scheme.Hom.comp_apply, ← h, Scheme.Hom.comp_apply]
      simp
    have hx' : f (a.inv x) ∈ b.hom ⁻¹ᵁ U := by
      rw [Scheme.Hom.mem_preimage, heq]
      exact hx
    have hf := hflat (a.inv x) hx'
    have ha := (flat_stalkMap_iff_of_isos f a b h (a.inv x)).mpr hf
    exact (CommRingCat.flat.arrow_mk_iso_iff
      (f.arrowStalkMapIsoOfEq (by simp))).mp ha
  · intro hflat x hx
    have heq : f (a.hom x) = b.hom (f x) :=
      congrArg (fun g : X ⟶ Y => g x) h
    exact (flat_stalkMap_iff_of_isos f a b h x).mp (hflat (a.hom x) (heq ▸ hx))

/-- If compatible automorphisms act transitively on the closed points of a Jacobson
target, flatness above any one nonempty open subset implies global flatness.
No finite-type, reducedness, or surjectivity assumption on the morphism is needed. -/
theorem flat_of_transitive_closedPoints [JacobsonSpace Y]
    {ι : Type v} (a : ι → (X ≅ X)) (b : ι → (Y ≅ Y))
    (hcomm : ∀ i, (a i).hom ≫ f = f ≫ (b i).hom)
    (htrans : ∀ y z : Y, y ∈ closedPoints Y → z ∈ closedPoints Y →
      ∃ i, (b i).hom y = z)
    (U : Y.Opens) (hU : (U : Set Y).Nonempty) (hflat : Flat (f ∣_ U)) :
    Flat f := by
  classical
  obtain ⟨z, hzU, hz⟩ := nonempty_inter_closedPoints hU U.isOpen.isLocallyClosed
  let V : Y.Opens := ⨆ i, (b i).hom ⁻¹ᵁ U
  have hclosed : closedPoints Y ⊆ (V : Set Y) := by
    intro y hy
    obtain ⟨i, hi⟩ := htrans y z hy hz
    apply Opens.mem_iSup.mpr
    refine ⟨i, ?_⟩
    rw [Scheme.Hom.mem_preimage, hi]
    exact hzU
  have hV : (V : Set Y) = Set.univ := by
    by_contra hne
    have hnonempty : ((V : Set Y)ᶜ).Nonempty := Set.nonempty_compl.mpr hne
    obtain ⟨y, hyV, hy⟩ := nonempty_inter_closedPoints hnonempty
      V.isOpen.isClosed_compl.isLocallyClosed
    exact hyV (hclosed hy)
  apply Flat.of_stalkMap
  intro x
  have hx : f x ∈ V := Set.eq_univ_iff_forall.mp hV (f x)
  obtain ⟨i, hi⟩ := Opens.mem_iSup.mp hx
  exact (flat_restrict_iff f ((b i).hom ⁻¹ᵁ U)).mp
    ((flat_restrict_preimage_iff_of_isos f (a i) (b i) (hcomm i) U).mpr hflat) x hi

/-- A finite-type morphism to a reduced locally Noetherian Jacobson scheme is flat
if compatible source and target automorphisms act transitively on the target's
closed points. The target may be empty or disconnected. -/
theorem flat_of_transitive_closedPoints_of_finiteType
    [JacobsonSpace Y] [IsLocallyNoetherian Y] [IsReduced Y]
    [QuasiCompact f] [LocallyOfFiniteType f]
    {ι : Type v} (a : ι → (X ≅ X)) (b : ι → (Y ≅ Y))
    (hcomm : ∀ i, (a i).hom ≫ f = f ≫ (b i).hom)
    (htrans : ∀ y z : Y, y ∈ closedPoints Y → z ∈ closedPoints Y →
      ∃ i, (b i).hom y = z) : Flat f := by
  cases isEmpty_or_nonempty Y with
  | inl hY =>
      exact Flat.of_stalkMap f fun x => (hY.false (f x)).elim
  | inr hY =>
      obtain ⟨U, hU, hflat⟩ := f.exists_dense_open_flat
      exact f.flat_of_transitive_closedPoints a b hcomm htrans U hU.nonempty hflat

end AlgebraicGeometry.Scheme.Hom
