/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.Birational.TopologicalDegree.Basic
public import TauCeti.AlgebraicGeometry.Birational.FunctionField.BaseAlgebra
public import TauCeti.AlgebraicGeometry.Morphisms.Finite.Flat.Degree
public import TauCeti.AlgebraicGeometry.Scheme.FunctionField
public import Mathlib.FieldTheory.FinTrdeg

/-!
# Finiteness of the topological degree and agreement with the rank

For a dominant `k`-rational map `f : X ⤏ Y` of integral schemes locally of finite type over a
field `k`, the topological degree `e(f) = [K(X) : f^*K(Y)]` is positive exactly when
`dim X = dim Y`. Otherwise `K(X)` has positive transcendence degree over `f^*K(Y)` and `e(f) = 0`
is the junk value of `Module.finrank`. The proof compares transcendence degrees in the tower
`k ⊆ f^*K(Y) ⊆ K(X)`, using that dimension is the transcendence degree of the function field
(`TauCeti.AlgebraicGeometry.topologicalKrullDim_eq_toNat_trdeg_functionField`) and that an
algebraic extension essentially of finite type is finite.

For a finite flat dominant morphism `g : X ⟶ Y` of integral schemes, `e(g)` is Mathlib's rank
`Scheme.Hom.finrank g y` at every point `y`.

## Main results

* `AlgebraicGeometry.Scheme.Hom.topologicalDegree_toRationalMap_eq_finrank`: `e(g)` is the rank
  of a finite flat dominant morphism `g` at every point.
* `AlgebraicGeometry.Scheme.RationalMap.topologicalDegree_pos_iff`: `0 < e(f)` if and only if
  `dim X = dim Y`.
* `AlgebraicGeometry.Scheme.RationalMap.topologicalDegree_eq_zero_iff`: `e(f) = 0` if and only if
  `dim X ≠ dim Y`.
* `AlgebraicGeometry.Scheme.Hom.finite_functionFieldMap_of_topologicalKrullDim_eq`: a dominant
  `k`-morphism `g` of integral schemes of the same dimension makes `K(X)` a finite extension of
  `K(Y)` along `g^*`.

## References

* The Stacks Project, Tag 0BXN (the degree of a dominant generically finite morphism of integral
  schemes).
-/

public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Scheme

variable {X Y : Scheme.{u}} [IsIntegral X] [IsIntegral Y]

/-- **Agreement with the rank.** The topological degree of a finite flat dominant morphism of
integral schemes is its rank `Scheme.Hom.finrank g y` at every point `y` of the target. -/
theorem Hom.topologicalDegree_toRationalMap_eq_finrank (g : X ⟶ Y) [IsFinite g] [Flat g]
    [IsDominant g] (y : Y) : g.toRationalMap.topologicalDegree = g.finrank y := by
  rw [topologicalDegree_toRationalMap, g.finrank_eq_finrank_fieldRange_functionFieldMap y]

variable (k : Type u) [Field k] [X.Over (Spec (.of k))] [Y.Over (Spec (.of k))]
  [LocallyOfFiniteType (X ↘ Spec (.of k))] [LocallyOfFiniteType (Y ↘ Spec (.of k))]

/-- The image `f^*K(Y)` of the pullback of rational functions along a dominant `k`-rational map,
as an intermediate field of `K(X)` over `k`. -/
private noncomputable abbrev pullbackField (f : X ⤏ Y) [f.IsDominant]
    [f.IsOver (X ↘ Spec (.of k)) (Y ↘ Spec (.of k))] : IntermediateField k X.functionField :=
  (f.functionFieldAlgHom k).fieldRange

omit [LocallyOfFiniteType (X ↘ Spec (.of k))] [LocallyOfFiniteType (Y ↘ Spec (.of k))] in
/-- The topological degree is the dimension of `K(X)` over the intermediate field `f^*K(Y)`. -/
private theorem topologicalDegree_eq_finrank_pullbackField (f : X ⤏ Y) [f.IsDominant]
    [f.IsOver (X ↘ Spec (.of k)) (Y ↘ Spec (.of k))] :
    f.topologicalDegree = Module.finrank (pullbackField k f) X.functionField := by
  have h : (pullbackField k f).toSubfield = f.functionFieldMap.hom.fieldRange := by
    ext x
    simp [pullbackField]
  rw [RationalMap.topologicalDegree_def, ← h]
  -- An intermediate field acts on `K(X)` through its underlying subfield, so the two ranks agree
  -- definitionally.
  rfl

omit [LocallyOfFiniteType (X ↘ Spec (.of k))] [LocallyOfFiniteType (Y ↘ Spec (.of k))] in
/-- `trdeg_k K(X) = trdeg_k K(Y) + trdeg_{f^*K(Y)} K(X)`. -/
private theorem trdeg_functionField_eq (f : X ⤏ Y) [f.IsDominant]
    [f.IsOver (X ↘ Spec (.of k)) (Y ↘ Spec (.of k))] :
    Algebra.trdeg k X.functionField =
      Algebra.trdeg k Y.functionField + Algebra.trdeg (pullbackField k f) X.functionField := by
  have e : Y.functionField ≃ₐ[k] pullbackField k f :=
    AlgEquiv.ofInjectiveField (f.functionFieldAlgHom k)
  rw [← trdeg_add_eq (A := X.functionField) k (pullbackField k f), e.trdeg_eq]

/-- **Finiteness of the topological degree.** For a dominant `k`-rational map `f : X ⤏ Y` of
integral schemes locally of finite type over a field `k`, the topological degree is positive if
and only if `dim X = dim Y`. -/
theorem RationalMap.topologicalDegree_pos_iff (f : X ⤏ Y) [f.IsDominant]
    [f.IsOver (X ↘ Spec (.of k)) (Y ↘ Spec (.of k))] :
    0 < f.topologicalDegree ↔ topologicalKrullDim X = topologicalKrullDim Y := by
  have : Algebra.EssFiniteType (pullbackField k f) X.functionField :=
    .of_comp k (pullbackField k f) X.functionField
  rw [TauCeti.AlgebraicGeometry.topologicalKrullDim_eq_toNat_trdeg_functionField k,
    TauCeti.AlgebraicGeometry.topologicalKrullDim_eq_toNat_trdeg_functionField k (X := Y),
    topologicalDegree_eq_finrank_pullbackField k f, trdeg_functionField_eq k f]
  have hY := trdeg_lt_aleph0 (K := k) (L := Y.functionField)
  have hX := trdeg_lt_aleph0 (K := pullbackField k f) (L := X.functionField)
  obtain ⟨m, hm⟩ := Cardinal.lt_aleph0.mp hY
  obtain ⟨n, hn⟩ := Cardinal.lt_aleph0.mp hX
  rw [hm, hn]
  constructor
  · intro h
    have : Module.Finite (pullbackField k f) X.functionField := Module.finite_of_finrank_pos h
    have : Algebra.trdeg (pullbackField k f) X.functionField = 0 :=
      trdeg_eq_zero_iff.mpr inferInstance
    rw [hn] at this
    obtain rfl : n = 0 := by exact_mod_cast this
    simp
  · intro h
    have hn0 : n = 0 := by
      have h' : ((m + n : ℕ) : WithBot ℕ∞) = (m : ℕ) := by exact_mod_cast h
      simp only [Nat.cast_inj] at h'
      omega
    have : Algebra.IsAlgebraic (pullbackField k f) X.functionField :=
      trdeg_eq_zero_iff.mp (by rw [hn, hn0, Nat.cast_zero])
    have : Module.Finite (pullbackField k f) X.functionField :=
      Algebra.finite_of_essFiniteType_of_isAlgebraic
    exact Module.finrank_pos

/-- The topological degree is the junk value `0` exactly when `dim X ≠ dim Y`. -/
theorem RationalMap.topologicalDegree_eq_zero_iff (f : X ⤏ Y) [f.IsDominant]
    [f.IsOver (X ↘ Spec (.of k)) (Y ↘ Spec (.of k))] :
    f.topologicalDegree = 0 ↔ topologicalKrullDim X ≠ topologicalKrullDim Y := by
  rw [Ne, ← topologicalDegree_pos_iff k f, Nat.pos_iff_ne_zero, not_not]

/-- **Dominant morphisms of equal dimension are generically finite.** For a dominant morphism
`g : X ⟶ Y` of integral schemes locally of finite type over a field `k` with `dim X = dim Y`, the
function field `K(X)` is finite over `K(Y)` along the pullback of rational functions `g^*`. -/
theorem Hom.finite_functionFieldMap_of_topologicalKrullDim_eq (g : X ⟶ Y) [IsDominant g]
    [g.IsOver (Spec (.of k))] (h : topologicalKrullDim X = topologicalKrullDim Y) :
    g.functionFieldMap.hom.Finite := by
  have hpos := (RationalMap.topologicalDegree_pos_iff k g.toRationalMap).2 h
  rw [g.topologicalDegree_toRationalMap] at hpos
  have : Module.Finite g.functionFieldMap.hom.fieldRange X.functionField :=
    Module.finite_of_finrank_pos hpos
  -- `g^*` is the isomorphism onto its image followed by the inclusion of the image.
  exact (RingHom.finite_algebraMap.2 this).comp
    (.of_surjective _ g.functionFieldMap.hom.rangeRestrictField_bijective.2)

end AlgebraicGeometry.Scheme
