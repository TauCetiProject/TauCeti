/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.Curves.NodalGluing.UnstableComponent
public import Mathlib.GroupTheory.Index

/-!
# Finiteness of nodal automorphisms from the normalization

For finitely many connected normalization components and finitely many nodes, the ordered
marked automorphism group is finite if and only if the automorphisms of each component fixing
all its special points form a finite group (`AuxiliaryAut.finite_ordered_iff`). This separates
the finite combinatorics from the componentwise analytic finiteness problem.

The action on components and node branches need not be trivial. Its kernel restricts injectively
to the product of the special-point fixing groups. Conversely, an automorphism supported on one
component embeds its fixing group in the ordered automorphism group. Auxiliary-label permutations
are retained: for finitely many auxiliary labels the same finiteness criterion applies to the
unordered automorphism group (`AuxiliaryAut.finite_iff`).

These results do not prove analytic finiteness for stable smooth components; they reduce the
nodal assertion to precisely that componentwise statement. No faithfulness of an action on a
deformation base is assumed.

## References

* Joel W. Robbin and Dietmar A. Salamon, *A construction of the Deligne–Mumford orbifold*,
  J. Eur. Math. Soc. 8 (2006), 611–699, §3, for stability and automorphisms of nodal curves.
-/

public noncomputable section

open Set
open scoped Manifold ContDiff

namespace TauCeti.NodalGluing.AuxiliaryAut

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] {E : Type*} [NormedAddCommGroup E]
  [NormedSpace 𝕜 E] {H : Type*} [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H} {n : ℕ∞ω}
  {ι Flag : Type*} {X : ι → Type*} [∀ i, TopologicalSpace (X i)] [∀ i, ChartedSpace H (X i)]
  {d : FlagPairData ι Flag X} {N R : Type*} {m : Marking d (N ⊕ R)}
  [∀ i, ConnectedSpace (X i)]

variable (I n m) in
/-- The action of ordered automorphisms on normalization components and individual node branches.
Branch interchange, including at a self-node, is retained. -/
def combinatorialAction : ordered I n m →* Equiv.Perm ι × Equiv.Perm (Flag × Bool) :=
  ((Aut.vertexPerm.prod Aut.branchPerm).comp toAut).comp (ordered I n m).subtype

/-- The combinatorial action records the component and branch permutations. -/
@[simp]
theorem combinatorialAction_apply (e : ordered I n m) :
    combinatorialAction I n m e = (e.1.toIso.vertexEquiv, e.1.toIso.branchEquiv) := by
  simp [combinatorialAction]

private theorem fst_apply_of_mem_ker (e : (combinatorialAction I n m).ker) (x : Σ i, X i) :
    (e.1.1 x).1 = x.1 := by
  have hv : e.1.1.toIso.vertexEquiv = 1 := by
    simpa using congrArg Prod.fst (MonoidHom.mem_ker.mp e.2)
  rw [← AuxiliaryIso.coe_toIso, Iso.fst_apply, hv, Equiv.Perm.one_apply]

private theorem apply_special_of_mem_ker (e : (combinatorialAction I n m).ker)
    {x : Σ i, X i} (hx : x ∈ flagPointSet d ∪ range m.point) : e.1.1 x = x := by
  rcases hx with hx | ⟨l, rfl⟩
  · rw [flagPointSet_eq_range] at hx
    obtain ⟨b, rfl⟩ := hx
    have hb := Iso.flagPoint_branchEquiv e.1.1.toIso b
    have hperm : e.1.1.toIso.branchEquiv = 1 := by
      simpa using congrArg Prod.snd (MonoidHom.mem_ker.mp e.2)
    rw [hperm, Equiv.Perm.one_apply] at hb
    exact hb.symm
  · exact (mem_ordered_iff_forall e.1.1).mp e.1.2 l

variable (I n m) in
/-- Restrict an ordered automorphism fixing all components and branches to the individual
normalization components. Each restriction fixes every special point. -/
def kernelComponent (e : (combinatorialAction I n m).ker) (i : ι) :
    Diffeomorph.fixingSubgroup (I := I) (n := n) (m.specialPoints i) :=
  ⟨e.1.1.toIso.toDiffeomorph.sigmaFiber (fst_apply_of_mem_ker e) i,
    Diffeomorph.mem_fixingSubgroup_of_forall fun x hx ↦ sigma_mk_injective (i := i) <| by
      rw [Diffeomorph.mk_sigmaFiber_apply]
      exact apply_special_of_mem_ker e (Marking.mem_specialPoints_iff.mp hx)⟩

/-- The component restriction agrees with the original map after inclusion in the normalization. -/
@[simp]
theorem mk_kernelComponent_apply (e : (combinatorialAction I n m).ker) (i : ι) (x : X i) :
    (⟨i, (kernelComponent I n m e i : X i ≃ₘ^n⟮I, I⟯ X i) x⟩ : Σ i, X i) = e.1.1 ⟨i, x⟩ :=
  Diffeomorph.mk_sigmaFiber_apply _ _ _ _

/-- An automorphism in the combinatorial kernel is determined by its component restrictions. -/
theorem kernelComponent_injective : Function.Injective (kernelComponent I n m) := by
  intro e f h
  apply Subtype.ext
  apply Subtype.ext
  apply AuxiliaryIso.ext
  rintro ⟨i, x⟩
  rw [← mk_kernelComponent_apply, ← mk_kernelComponent_apply, h]

/-- If the special-point fixing group on each normalization component is finite, the ordered
automorphism group of the nodal curve is finite. -/
theorem finite_ordered_of_finite_fixingSubgroup [Finite ι] [Finite Flag]
    [∀ i, Finite (Diffeomorph.fixingSubgroup (I := I) (n := n) (m.specialPoints i))] :
    Finite (ordered I n m) := by
  have : Finite (combinatorialAction I n m).ker :=
    Finite.of_injective _ kernelComponent_injective
  exact (combinatorialAction I n m).finite_iff_finite_ker_range.mpr ⟨inferInstance, inferInstance⟩

/-- For a finite normalization presentation, ordered automorphisms are finite exactly when
each component has finitely many automorphisms fixing all its special points. -/
theorem finite_ordered_iff [Finite ι] [Finite Flag] :
    Finite (ordered I n m) ↔
      ∀ i, Finite (Diffeomorph.fixingSubgroup (I := I) (n := n) (m.specialPoints i)) := by
  constructor
  · intro h i
    exact Finite.of_injective _ (ofComponent_injective i)
  · intro h
    let := h
    exact finite_ordered_of_finite_fixingSubgroup

/-- With finitely many auxiliary labels, allowing their permutations does not change the
componentwise finiteness criterion. -/
theorem finite_iff [Finite ι] [Finite Flag] [Finite R] :
    Finite (AuxiliaryAut I n m) ↔
      ∀ i, Finite (Diffeomorph.fixingSubgroup (I := I) (n := n) (m.specialPoints i)) := by
  constructor
  · intro h
    exact finite_ordered_iff.mp inferInstance
  · intro h
    have := finite_ordered_iff.mpr h
    infer_instance

end TauCeti.NodalGluing.AuxiliaryAut
