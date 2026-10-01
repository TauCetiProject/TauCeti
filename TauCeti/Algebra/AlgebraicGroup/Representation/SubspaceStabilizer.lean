/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Algebra.AlgebraicGroup.HopfIdeal.Points.Basic
public import TauCeti.Algebra.Coalgebra.Comodule.Evaluation
public import TauCeti.Algebra.Coalgebra.Comodule.MatrixCoefficient.Regular
public import TauCeti.Algebra.Coalgebra.Subcomodule.Finite
import Mathlib.RingTheory.Flat.Equalizer

/-!
# Closed subgroups as stabilizers of subspaces

A closed subgroup of an affine group of finite type over a field is the stabilizer of a
subspace of a finite-dimensional representation. The representation can be taken inside the
regular representation: choose a finite-dimensional subcomodule containing generators of the
defining ideal, and intersect it with that ideal. The stabilizer identity holds over every
commutative value algebra, so it detects nonreduced subgroup schemes as well as reduced ones.

This is the subspace form of Chevalley's stabilizer construction. Passing to a suitable
exterior power gives a line stabilizer, the input for constructing homogeneous spaces as
orbits in projective space.

## References

* J. S. Milne, *Algebraic Groups* (2017), Theorem 4.27, the subspace-stabilizer step
  in the proof of Chevalley's theorem. See also the updated text:
  <https://www.jmilne.org/math/Books/iAG2022.pdf>.
-/

public section

open scoped TensorProduct
open CategoryTheory WithConv

namespace TauCeti.HopfIdeal

universe u v w

section Ring

variable {k : Type u} [CommRing k] {H : _root_.CommHopfAlgCat.{v} k}

/-- The intersection of a regular subcomodule with the ideal defining a closed subgroup,
viewed as a subspace of the subcomodule. -/
noncomputable def definingSubspace (I : HopfIdeal k H) (V : Subcomodule k H H) : Submodule k V :=
  LinearMap.ker ((Ideal.Quotient.mkₐ k I.toIdeal).toLinearMap.comp
    (SMulMemClass.subtype V))

/-- A vector belongs to the defining subspace exactly when its underlying function vanishes
on the closed subgroup. -/
@[simp]
theorem mem_definingSubspace (I : HopfIdeal k H) (V : Subcomodule k H H) (x : V) :
    x ∈ I.definingSubspace V ↔ (x : H) ∈ I := by
  simp [definingSubspace, Ideal.Quotient.eq_zero_iff_mem]

/-- Scalar extension of the defining subspace is the kernel of restriction to the subgroup. -/
theorem baseChange_definingSubspace (I : HopfIdeal k H) (V : Subcomodule k H H)
    (A : Type w) [CommRing A] [Algebra k A] [Module.Flat k A] :
    (I.definingSubspace V).baseChange A =
      LinearMap.ker (((Ideal.Quotient.mkₐ k I.toIdeal).toLinearMap.comp
        (SMulMemClass.subtype V)).baseChange A) := by
  let : AddCommGroup V := Module.addCommMonoidToAddCommGroup k
  rw [definingSubspace, Submodule.baseChange]
  exact (Module.Flat.ker_lTensor_eq (R := k) A A
    ((Ideal.Quotient.mkₐ k I.toIdeal).toLinearMap.comp
      (SMulMemClass.subtype V))).symm

variable [Module.Flat k H]

/-- Every point of the closed subgroup preserves the defining subspace over any value algebra
flat over the base. -/
theorem endOfPoint_mapsTo_definingSubspace (I : HopfIdeal k H) (V : Subcomodule k H H)
    (A : CommAlgCat.{w} k) [Module.Flat k A] (g : HopfAlgebra.points (R := k) (H := H) A)
    (hg : g ∈ CommHopfAlgCat.quotientPointsSubgroup H I A) :
    Set.MapsTo (Comodule.endOfPoint V g.ofConv)
      ((I.definingSubspace V).baseChange A) ((I.definingSubspace V).baseChange A) := by
  obtain ⟨g', rfl⟩ := hg
  let q := (CommHopfAlgCat.mkQuotient H I).hom
  have hnat := BialgHom.baseChange_comp_endOfPoint_regular q g'.ofConv
  have hsub := Comodule.baseChange_comp_endOfPoint (Subcomodule.subtype V)
    (g'.ofConv.comp q.toAlgHom)
  rw [baseChange_definingSubspace, ← Subcomodule.subtype_toLinearMap]
  have hg : ((CommHopfAlgCat.quotientPointsHom H I A).hom g').ofConv =
      g'.ofConv.comp q.toAlgHom := by
    ext h
    exact CommHopfAlgCat.quotientPointsHom_apply_apply H I A g' h
  rw [hg]
  have hq : q.toLinearMap = (Ideal.Quotient.mkₐ k I.toIdeal).toLinearMap := by
    ext x
    exact CommHopfAlgCat.mkQuotient_apply H I x
  rw [hq] at hnat
  intro x hx
  simp only [SetLike.mem_coe, LinearMap.mem_ker] at hx ⊢
  simp only [LinearMap.baseChange_comp, LinearMap.comp_apply] at hx ⊢
  have hs := LinearMap.congr_fun hsub x
  simp only [LinearMap.comp_apply] at hs
  rw [hs]
  have hn := LinearMap.congr_fun hnat ((Subcomodule.subtype V).toLinearMap.baseChange A x)
  simp only [LinearMap.comp_apply] at hn
  rw [hn, hx, map_zero]

/-- If the functions in the defining subspace generate the defining ideal, preserving that
subspace forces a point to lie in the subgroup. -/
theorem mem_quotientPointsSubgroup_of_mapsTo_definingSubspace
    (I : HopfIdeal k H) (V : Subcomodule k H H)
    (hgen : Ideal.span ((V : Set H) ∩ (I : Set H)) = I.toIdeal)
    (A : CommAlgCat.{w} k) (g : HopfAlgebra.points (R := k) (H := H) A)
    (hg : Set.MapsTo (Comodule.endOfPoint V g.ofConv)
      ((I.definingSubspace V).baseChange A) ((I.definingSubspace V).baseChange A)) :
    g ∈ CommHopfAlgCat.quotientPointsSubgroup H I A := by
  let φ : Module.Dual k V :=
    (Coalgebra.counit (R := k) (A := H)).comp (Subcomodule.subtype V).toLinearMap
  have heval (z : A ⊗[k] V) (hz : z ∈ (I.definingSubspace V).baseChange A) :
      Module.Dual.baseChangeEvaluation (1 ⊗ₜ[k] φ) z = 0 := by
    obtain ⟨t, rfl⟩ := hz
    induction t using TensorProduct.inductionOn with
    | add x y hx hy => simp only [map_add, hx, hy, add_zero]
    | tmul a x =>
      have hx := I.counit_eq_zero ((mem_definingSubspace I V x).mp x.property)
      simpa [φ, LinearMap.baseChange_tmul,
        Module.Dual.baseChangeEvaluation_tmul] using congrArg (fun r : k ↦ a * algebraMap k A r) hx
  have hker : I.toIdeal ≤ RingHom.ker g.ofConv.toRingHom := by
    rw [← hgen, Ideal.span_le]
    rintro x ⟨hxV, hxI⟩
    have hx : (⟨x, hxV⟩ : V) ∈ I.definingSubspace V :=
      (mem_definingSubspace I V _).mpr hxI
    have h := heval _ (hg (Submodule.tmul_mem_baseChange_of_mem 1 hx))
    apply RingHom.mem_ker.mpr
    simp only [AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom]
    simpa only [Comodule.baseChangeEvaluation_endOfPoint_tmul, one_mul, φ,
      Subcomodule.subtype_toLinearMap, Comodule.matrixCoefficient_counit_comp_subtype] using h
  exact (CommHopfAlgCat.mem_quotientPointsSubgroup_iff H I A g).mpr fun x hx ↦ hker hx

/-- A regular subcomodule containing ideal generators realizes the closed subgroup as the
stabilizer of its defining subspace, over every flat value algebra. -/
theorem mem_quotientPointsSubgroup_iff_mapsTo_definingSubspace
    (I : HopfIdeal k H) (V : Subcomodule k H H)
    (hgen : Ideal.span ((V : Set H) ∩ (I : Set H)) = I.toIdeal)
    (A : CommAlgCat.{w} k) [Module.Flat k A] (g : HopfAlgebra.points (R := k) (H := H) A) :
    g ∈ CommHopfAlgCat.quotientPointsSubgroup H I A ↔
      Set.MapsTo (Comodule.endOfPoint V g.ofConv)
        ((I.definingSubspace V).baseChange A) ((I.definingSubspace V).baseChange A) :=
  ⟨I.endOfPoint_mapsTo_definingSubspace V A g,
    I.mem_quotientPointsSubgroup_of_mapsTo_definingSubspace V hgen A g⟩

/-- The subgroup is the full stabilizer, with equality rather than just preservation of the
scalar-extended subspace. -/
theorem mem_quotientPointsSubgroup_iff_map_definingSubspace_eq
    (I : HopfIdeal k H) (V : Subcomodule k H H)
    (hgen : Ideal.span ((V : Set H) ∩ (I : Set H)) = I.toIdeal)
    (A : CommAlgCat.{w} k) [Module.Flat k A] (g : HopfAlgebra.points (R := k) (H := H) A) :
    g ∈ CommHopfAlgCat.quotientPointsSubgroup H I A ↔
      ((I.definingSubspace V).baseChange A).map (Comodule.endOfPoint V g.ofConv) =
        (I.definingSubspace V).baseChange A := by
  constructor
  · intro hg
    apply le_antisymm
    · rintro _ ⟨x, hx, rfl⟩
      exact I.endOfPoint_mapsTo_definingSubspace V A g hg hx
    · intro x hx
      refine ⟨Comodule.endOfPoint V (g⁻¹).ofConv x,
        I.endOfPoint_mapsTo_definingSubspace V A g⁻¹ (inv_mem hg) hx, ?_⟩
      have h := LinearMap.congr_fun (Comodule.endOfPoint_convMul V g g⁻¹) x
      simpa only [mul_inv_cancel, Comodule.endOfPoint_convOne, LinearMap.id_apply,
        LinearMap.comp_apply] using h.symm
  · intro hg
    apply I.mem_quotientPointsSubgroup_of_mapsTo_definingSubspace V hgen A g
    intro x hx
    rw [← hg]
    exact Submodule.mem_map_of_mem hx

end Ring

variable {k : Type u} [Field k] {H : _root_.CommHopfAlgCat.{v} k}

/-- A closed subgroup with finitely generated defining ideal is the stabilizer of a subspace
in a finite-dimensional regular subcomodule. In particular this applies to every closed subgroup
of a finite-type affine group. The same subspace works for all value algebras. -/
theorem exists_finite_subcomodule_stabilizer (I : HopfIdeal k H) (hI : I.toIdeal.FG) :
    ∃ V : Subcomodule k H H, Module.Finite k V.toSubmodule ∧
      ∀ (A : CommAlgCat.{w} k) (g : HopfAlgebra.points (R := k) (H := H) A),
        g ∈ CommHopfAlgCat.quotientPointsSubgroup H I A ↔
          ((I.definingSubspace V).baseChange A).map (Comodule.endOfPoint V g.ofConv) =
            (I.definingSubspace V).baseChange A := by
  obtain ⟨s, hs, hspan⟩ := Submodule.fg_def.mp hI
  obtain ⟨V, hV, hsV⟩ := Subcomodule.exists_finite_subcomodule_of_setFinite
    (R := k) (C := H) hs
  refine ⟨V, hV, fun A g ↦ I.mem_quotientPointsSubgroup_iff_map_definingSubspace_eq V ?_ A g⟩
  apply le_antisymm
  · exact Ideal.span_le.mpr fun x hx ↦ hx.2
  · rw [← hspan]
    apply Ideal.span_mono
    intro x hx
    have hxI : x ∈ I.toIdeal := hspan ▸ Submodule.subset_span hx
    exact ⟨hsV hx, hxI⟩

end TauCeti.HopfIdeal
