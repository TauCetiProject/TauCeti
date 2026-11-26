/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import Mathlib.RepresentationTheory.Character
public import Mathlib.RepresentationTheory.Semisimple
public import Mathlib.Topology.Algebra.Constructions
public import Mathlib.Topology.Algebra.Module.ModuleTopology
public import Mathlib.Topology.Instances.Matrix
-- Non-public: used only inside proofs.
import Mathlib.Topology.Algebra.Group.Units
import Mathlib.Topology.ContinuousMap.Algebra
import TauCeti.LinearAlgebra.Trace.Basic
import TauCeti.RepresentationTheory.Semisimple.TraceForm
import TauCeti.Topology.Algebra.Module.ModuleTopology

/-!
# Continuity of a semisimple representation from its character

Let `ρ` be a finite-dimensional representation of a monoid `G` with continuous right
translations over a topological field `k`, given only as an abstract homomorphism, with no
continuity assumed. If `ρ` is semisimple, `k` has characteristic zero and the character
`g ↦ tr(ρ g)` is continuous, then `ρ` is continuous: every linear functional of `ρ`, in particular
every matrix coefficient, is a continuous function on `G`.

The reason is that on the span `S` of the operators `ρ g` the trace pairing is nondegenerate
(`Representation.eq_zero_of_mem_span_of_forall_trace_mul_eq_zero`). In finite dimension every
linear functional on `S` is then a linear combination of the functionals `x ↦ tr(x ρ(h))`, and along
`ρ` such a functional is the translate `g ↦ tr(ρ(g h))` of the character, which is continuous. The
argument works in any characteristic for representations whose trace pairing is nondegenerate on
`S` (`Representation.continuous_linearMap_apply_of_continuous_character_of_nondegenerate`); only
the passage from semisimplicity to nondegeneracy uses characteristic zero.

This is how a representation reconstructed from its trace, for instance by specializing a
continuous determinant or pseudocharacter, is shown to be continuous. Neither algebraic closedness
nor absolute irreducibility of `ρ` is needed.

## Main results

* `Representation.continuous_linearMap_apply_of_continuous_character_of_nondegenerate`: if the trace
  pairing is nondegenerate on the span of `ρ`, every linear functional of `ρ` is as continuous as
  the character.
* `Representation.continuous_linearMap_apply_of_continuous_character`: the same for a semisimple
  `ρ` in characteristic zero.
* `Representation.continuous_action_of_continuous_character_of_nondegenerate`: nondegeneracy and
  continuous character imply joint continuity on the module topology in any characteristic.
* `Representation.continuous_action_of_continuous_character`: a semisimple representation in
  characteristic zero with continuous character acts jointly continuously on `V` with its module
  topology.
* `MonoidHom.continuous_of_continuous_trace_of_nondegenerate`: the matrix form under
  nondegeneracy in any characteristic.
* `MonoidHom.continuous_of_continuous_trace`: a homomorphism `G →* GL_n(k)` whose representation
  on `k ^ n` is semisimple, in characteristic zero, is continuous when its trace is.

## Provenance

`Representation.continuous_linearMap_apply_of_continuous_character_of_nondegenerate` and
`MonoidHom.continuous_of_continuous_trace` are adapted from `New.IsTraceNondeg.continuous_of_trace`
(file `src/Lib/GaloisRep/Pseudocharacter/SemisimpleRepresentations.lean`), with its hypothesis
`New.IsTraceNondeg` (file `src/Lib/General/LinearAlgebra/MatrixPolynomials.lean`) stated inline, in
grh-lean (https://github.com/lsernau/grh-lean, Apache 2.0, Copyright 2026 Anthropic, PBC). The
basis-free statement for representations on a vector space, the derivation of nondegeneracy from
semisimplicity in characteristic zero and the joint continuity on the module topology are new here.

## References

* R. Taylor, *Galois representations associated to Siegel modular forms of low weight*, Duke
  Math. J. 63 (1991), 281–332.
-/

public section

namespace Representation

variable {k G V : Type*} [Field k] [TopologicalSpace k] [Monoid G] [TopologicalSpace G]
  [AddCommGroup V] [Module k V]

omit [TopologicalSpace k] [TopologicalSpace G] in
/-- A representation whose trace pairing is nondegenerate on its span is finite-dimensional: on an
infinite-dimensional space the trace vanishes identically, so the identity would pair to zero with
everything. -/
private theorem finiteDimensional_of_nondegenerate (ρ : Representation k G V)
    (hρ : ∀ f ∈ Submodule.span k (Set.range ρ), (∀ g, LinearMap.trace k V (f * ρ g) = 0) → f = 0) :
    FiniteDimensional k V := by
  by_contra hV
  have htr := TauCeti.LinearMap.trace_eq_zero_of_not_finite hV
  have h1 : (1 : Module.End k V) = 0 :=
    hρ 1 (Submodule.subset_span ⟨1, map_one ρ⟩) fun g ↦ by rw [htr, LinearMap.zero_apply]
  have : Subsingleton V := ⟨fun v w ↦ by
    simpa using congr($h1 v).trans congr($h1 w).symm⟩
  exact hV inferInstance

/-- **The character controls the linear functionals of a representation with nondegenerate trace
pairing.** Suppose that the only element `f` of the span of the operators `ρ g` with
`tr(f ρ(g)) = 0` for all `g` is `0`, and that the character of `ρ` is continuous. Then
`g ↦ φ (ρ g)` is continuous for every linear functional `φ` on `End_k(V)`. No assumption on the
characteristic of `k` is made. -/
theorem continuous_linearMap_apply_of_continuous_character_of_nondegenerate
    [IsTopologicalAddGroup k] [ContinuousConstSMul k k] [ContinuousConstSMul Gᵐᵒᵖ G]
    (ρ : Representation k G V)
    (hρ : ∀ f ∈ Submodule.span k (Set.range ρ), (∀ g, LinearMap.trace k V (f * ρ g) = 0) → f = 0)
    (hχ : Continuous ρ.character) (φ : Module.End k V →ₗ[k] k) :
    Continuous fun g ↦ φ (ρ g) := by
  have := finiteDimensional_of_nondegenerate ρ hρ
  let S := Submodule.span k (Set.range ρ)
  -- The functionals `x ↦ tr(x ρ(h))` on `S` span its dual, by nondegeneracy.
  let L (h : G) : S →ₗ[k] k :=
    (LinearMap.trace k V ∘ₗ LinearMap.mulRight k (ρ h)).domRestrict S
  have hφ : φ.domRestrict S ∈ Submodule.span k (Set.range L) :=
    FiniteDimensional.mem_span_of_iInf_ker_le_ker fun x hx ↦ by
      simp only [Submodule.mem_iInf, LinearMap.mem_ker] at hx
      simp [hρ x x.property fun g ↦ by simpa [L] using hx g]
  -- Evaluating functionals on `S` along `ρ`; the functionals with continuous image form a subspace
  -- containing every `L h`, whose image is a translate of the character.
  let ev : (S →ₗ[k] k) →ₗ[k] G → k :=
    LinearMap.pi fun g ↦ LinearMap.applyₗ ⟨ρ g, Submodule.subset_span ⟨g, rfl⟩⟩
  have hL (h : G) : Continuous (ev (L h)) :=
    (hχ.comp (continuous_const_smul (MulOpposite.op h))).congr fun g ↦ by simp [ev, L, character]
  have hev (ψ : S →ₗ[k] k) (g : G) :
      ev ψ g = ψ ⟨ρ g, Submodule.subset_span ⟨g, rfl⟩⟩ := by
    simp [ev]
  have hcont := Submodule.mem_span.1 hφ ((continuousSubmodule G k k).comap ev)
    (Set.range_subset_iff.2 hL)
  rw [Submodule.mem_comap] at hcont
  have hcont' : Continuous (ev (φ.domRestrict S)) := hcont
  exact hcont'.congr fun g ↦ by rw [hev, LinearMap.domRestrict_apply]

/-- **The linear functionals of a semisimple representation are as continuous as its character.**
Over a topological field of characteristic zero, if `ρ` is a finite-dimensional semisimple
representation whose character is continuous, then `g ↦ φ (ρ g)` is continuous for every linear
functional `φ` on `End_k(V)`; for instance every matrix coefficient of `ρ` is continuous. -/
theorem continuous_linearMap_apply_of_continuous_character [CharZero k] [FiniteDimensional k V]
    [IsTopologicalAddGroup k] [ContinuousConstSMul k k] [ContinuousConstSMul Gᵐᵒᵖ G]
    (ρ : Representation k G V)
    [ρ.IsSemisimpleRepresentation] (hχ : Continuous ρ.character) (φ : Module.End k V →ₗ[k] k) :
    Continuous fun g ↦ φ (ρ g) :=
  ρ.continuous_linearMap_apply_of_continuous_character_of_nondegenerate
    (fun _ hf h ↦ ρ.eq_zero_of_mem_span_of_forall_trace_mul_eq_zero hf h) hχ φ

/-- A representation with nondegenerate trace pairing and continuous character acts jointly
continuously on its vector space with the module topology, in any characteristic. -/
theorem continuous_action_of_continuous_character_of_nondegenerate
    [IsTopologicalRing k] [ContinuousConstSMul Gᵐᵒᵖ G] [TopologicalSpace V]
    [IsModuleTopology k V] (ρ : Representation k G V)
    (hρ : ∀ f ∈ Submodule.span k (Set.range ρ), (∀ g, LinearMap.trace k V (f * ρ g) = 0) → f = 0)
    (hχ : Continuous ρ.character) : Continuous fun p : G × V ↦ ρ p.1 p.2 := by
  have := finiteDimensional_of_nondegenerate ρ hρ
  let b := Module.finBasis k V
  refine (TauCeti.ModuleTopology.continuous_linearMap_apply_iff_continuous_toMatrix b b ρ).2
    (continuous_matrix fun i j ↦ ?_)
  exact ρ.continuous_linearMap_apply_of_continuous_character_of_nondegenerate hρ hχ
    (Matrix.entryLinearMap k k i j ∘ₗ (LinearMap.toMatrix b b).toLinearMap)

/-- **A semisimple representation with continuous character is continuous.** Over a topological
field of characteristic zero, a finite-dimensional semisimple representation whose character is
continuous acts jointly continuously on `V` with its module topology. -/
theorem continuous_action_of_continuous_character [CharZero k] [FiniteDimensional k V]
    [IsTopologicalRing k] [ContinuousConstSMul Gᵐᵒᵖ G] [TopologicalSpace V]
    [IsModuleTopology k V] (ρ : Representation k G V)
    [ρ.IsSemisimpleRepresentation] (hχ : Continuous ρ.character) :
    Continuous fun p : G × V ↦ ρ p.1 p.2 :=
  ρ.continuous_action_of_continuous_character_of_nondegenerate
    (fun _ hf h ↦ ρ.eq_zero_of_mem_span_of_forall_trace_mul_eq_zero hf h) hχ

end Representation

namespace MonoidHom

variable {G k n : Type*} [Group G] [TopologicalSpace G] [ContinuousConstSMul Gᵐᵒᵖ G]
  [ContinuousInv G] [Field k] [TopologicalSpace k] [Fintype n] [DecidableEq n]

/-- A matrix representation with nondegenerate trace pairing on the span of its operators is
continuous whenever its trace is continuous, in any characteristic. -/
theorem continuous_of_continuous_trace_of_nondegenerate [IsTopologicalAddGroup k]
    [ContinuousConstSMul k k] (r : G →* GL n k)
    (hρ : ∀ f ∈ Submodule.span k (Set.range
      ((Units.coeHom _).comp (Matrix.GeneralLinearGroup.toLin.toMonoidHom.comp r) :
        Representation k G (n → k))),
      (∀ g, LinearMap.trace k (n → k)
        (f * ((Units.coeHom _).comp (Matrix.GeneralLinearGroup.toLin.toMonoidHom.comp r)) g) = 0) →
        f = 0)
    (htr : Continuous fun g ↦ (r g : Matrix n n k).trace) : Continuous r := by
  let ρ : Representation k G (n → k) :=
    (Units.coeHom _).comp (Matrix.GeneralLinearGroup.toLin.toMonoidHom.comp r)
  have hρ_apply (g : G) : ρ g = Matrix.toLin' (r g : Matrix n n k) := by
    simp [ρ, Matrix.toLin'_apply']
  have hχ : Continuous ρ.character := htr.congr fun g ↦ by
    simp [Representation.character, hρ_apply, Matrix.trace_toLin'_eq]
  have hval : Continuous fun g ↦ (r g : Matrix n n k) := continuous_matrix fun i j ↦
    (ρ.continuous_linearMap_apply_of_continuous_character_of_nondegenerate hρ hχ
      (Matrix.entryLinearMap k k i j ∘ₗ LinearMap.toMatrix'.toLinearMap)).congr fun g ↦ by
        simp [hρ_apply]
  exact Continuous.of_coeHom_comp (f := r) hval

/-- **A semisimple matrix representation with continuous trace is continuous.** Let `k` be a
topological field of characteristic zero and `r : G →* GL_n(k)` a homomorphism from a group with
continuous right translations and continuous inversion whose representation on `k ^ n` is
semisimple. If `g ↦ tr(r g)` is continuous, then `r` is continuous for the topology of `GL_n(k)`
as the units of the matrix ring. -/
theorem continuous_of_continuous_trace [CharZero k] [IsTopologicalAddGroup k]
    [ContinuousConstSMul k k] (r : G →* GL n k)
    [Representation.IsSemisimpleRepresentation
      ((Units.coeHom _).comp (Matrix.GeneralLinearGroup.toLin.toMonoidHom.comp r) :
        Representation k G (n → k))]
    (htr : Continuous fun g ↦ (r g : Matrix n n k).trace) : Continuous r := by
  apply r.continuous_of_continuous_trace_of_nondegenerate ?_ htr
  exact fun _ hf h ↦
    Representation.eq_zero_of_mem_span_of_forall_trace_mul_eq_zero _ hf h

end MonoidHom
