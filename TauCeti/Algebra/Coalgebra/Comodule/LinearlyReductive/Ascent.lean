/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Algebra.Coalgebra.Comodule.LinearlyReductive.Exact
public import TauCeti.Algebra.Coalgebra.Comodule.LinearlyReductive.BaseChange
public import TauCeti.Algebra.Coalgebra.Comodule.RestrictScalars
public import Mathlib.RingTheory.HopfAlgebra.TensorProduct

/-!
# Linear reductivity is preserved by field extensions

A commutative Hopf algebra is linearly reductive over a field precisely when its
base change is linearly reductive over any extension field. No separability or
finite-degree hypothesis is needed.

For ascent, restrict a morphism of representations over the extension field to
the original field. Its invariant vectors are unchanged. Exactness of invariants
for arbitrary comodules therefore lifts invariant vectors over the extension
field. The finite-dimensional exactness criterion recovers linear reductivity.
Restriction of scalars can produce infinite-dimensional representations, so the
arbitrary-comodule invariant-lifting theorem is essential here.

## References

* J. C. Jantzen, *Representations of Algebraic Groups*, I.2.
* J. S. Milne, *Algebraic Groups* (2017), Chapter 12.
-/

public section

open scoped TensorProduct

namespace TauCeti.Coalgebra

universe u v w

variable {k : Type u} [Field k] {H : Type v} [CommSemiring H] [HopfAlgebra k H]
  (K : Type w) [Field K] [Algebra k K]

/-- Linear reductivity of a commutative Hopf algebra ascends along every extension
of the ground field. -/
theorem IsLinearlyReductive.baseChange (hH : IsLinearlyReductive.{u, v, u} k H) :
    IsLinearlyReductive.{w, max w v, w} K (K ⊗[k] H) := by
  apply isLinearlyReductive_iff_forall_fixedMap_surjective_of_surjective.mpr
  intro M N f hf
  let : Module k M := Module.compHom M (algebraMap k K)
  let : Module k N := Module.compHom N (algebraMap k K)
  let : IsScalarTower k K M := IsScalarTower.of_compHom k K M
  let : IsScalarTower k K N := IsScalarTower.of_compHom k K N
  let := Comodule.restrictScalars (R := k) (A := K) (C := H) (M := M)
  let := Comodule.restrictScalars (R := k) (A := K) (C := H) (M := N)
  let g := f.hom.restrictScalars (R := k)
  intro n
  have hn : (n : N) ∈ Comodule.fixedSubcomodule k H N :=
    (Comodule.mem_fixedSubcomodule_restrictScalars_iff (R := k) (A := K) (n : N)).mpr n.property
  obtain ⟨m, hm, hgm⟩ := g.exists_fixed_preimage_of_isLinearlyReductive hH hn (by
      obtain ⟨m, hm⟩ := hf n
      exact ⟨m, by simpa [g] using hm⟩)
  have hm' : m ∈ Comodule.fixedSubcomodule K (K ⊗[k] H) M :=
    (Comodule.mem_fixedSubcomodule_restrictScalars_iff (R := k) (A := K) m).mp hm
  exact ⟨⟨m, hm'⟩, Subtype.ext (by simpa [g] using hgm)⟩

/-- Linear reductivity of a commutative Hopf algebra can be checked after any
extension of the ground field. -/
theorem isLinearlyReductive_baseChange_iff :
    IsLinearlyReductive.{w, max w v, w} K (K ⊗[k] H) ↔
      IsLinearlyReductive.{u, v, u} k H :=
  ⟨IsLinearlyReductive.of_baseChange K, IsLinearlyReductive.baseChange K⟩

end TauCeti.Coalgebra
