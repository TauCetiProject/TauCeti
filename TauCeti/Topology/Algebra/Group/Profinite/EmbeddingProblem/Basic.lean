/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Group.Subgroup.Ker
public import Mathlib.Topology.Algebra.Group.Defs

/-!
# Finite embedding problems

A **finite embedding problem** for a topological group `G` is a continuous surjection
`π : G ↠ Q` onto a finite group together with a surjection `α : E ↠ Q` of finite groups. A
**solution** is a continuous homomorphism `β : G → E` with `α ∘ β = π`. For homomorphisms into
finite discrete groups, continuity is recorded as openness of the kernel. This equivalence uses
the topological group structure on `G`.

A solution need not be surjective. For example, if `G` is cyclic of order `p`, `Q = 1`, and
`E = G × G`, no homomorphism `G → E` is surjective.

A surjection `φ : E ↠ F` of finite groups and a homomorphism `β : G → F` with open kernel cut out
an embedding problem, `TauCeti.FiniteEmbeddingProblem.ofSurjective`: the quotient is the range of
`β` and the group to map into is its preimage under `φ`. Its solutions are exactly the lifts of `β`
through `φ` with open kernel, and its kernel is the kernel of `φ`. This is the problem that
appears when a solution modulo a normal subgroup is lifted one step further, and at each finite
level of a lifting problem against a surjection of profinite groups.

## Main definitions

* `TauCeti.FiniteEmbeddingProblem`: a finite embedding problem for `G`.
* `TauCeti.FiniteEmbeddingProblem.IsSolution`: a solution of a finite embedding problem.
* `TauCeti.FiniteEmbeddingProblem.ofSurjective`: the embedding problem cut out by a surjection
  `φ : E ↠ F` of finite groups and a homomorphism `β : G → F` with open kernel.

## Main results

* `TauCeti.FiniteEmbeddingProblem.ker_ofSurjective_α`: the kernel of the problem cut out by `φ`
  and `β` is the kernel of `φ`.
* `TauCeti.FiniteEmbeddingProblem.isSolution_ofSurjective_iff`: its solutions are the lifts of
  `β` through `φ` with open kernel.

## References

* J.-P. Serre, *Galois Cohomology*, Chapter I, §3.4 and §4.2.
* J. Neukirch, A. Schmidt, K. Wingberg, *Cohomology of Number Fields*, Chapter III, §5.
-/

public section

namespace TauCeti

universe u v w

/-- A **finite embedding problem** for a topological group `G`: a continuous surjection
`π : G ↠ Q` onto a finite group, together with a surjection `α : E ↠ Q` of finite groups.
Continuity of `π` is recorded as openness of its kernel, which is what continuity into a finite
discrete group amounts to. -/
structure FiniteEmbeddingProblem (G : Type u) [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] where
  /-- The finite quotient of `G` the problem sits over. -/
  Q : Type v
  [groupQ : Group Q]
  [finiteQ : Finite Q]
  /-- The finite group into which a solution maps. -/
  E : Type w
  [groupE : Group E]
  [finiteE : Finite E]
  /-- The continuous surjection `G ↠ Q`. -/
  π : G →* Q
  /-- Continuity of `π`, as openness of its kernel. -/
  isOpen_ker_π : IsOpen (π.ker : Set G)
  /-- Surjectivity of `π`. -/
  π_surjective : Function.Surjective π
  /-- The surjection of finite groups `E ↠ Q`. -/
  α : E →* Q
  /-- Surjectivity of `α`. -/
  α_surjective : Function.Surjective α

attribute [instance] FiniteEmbeddingProblem.groupQ FiniteEmbeddingProblem.finiteQ
  FiniteEmbeddingProblem.groupE FiniteEmbeddingProblem.finiteE

namespace FiniteEmbeddingProblem

variable {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    (P : FiniteEmbeddingProblem G)

/-- A **solution** of a finite embedding problem `P`: a homomorphism `β : G → E` with open kernel
(that is, continuous for the discrete topology on `E`) such that `α ∘ β = π`. A solution need not
be surjective. -/
def IsSolution (β : G →* P.E) : Prop :=
  IsOpen (β.ker : Set G) ∧ ∀ g : G, P.α (β g) = P.π g

variable {P}

/-- A homomorphism solves `P` exactly when its kernel is open and `α ∘ β = π`. -/
@[simp] theorem isSolution_iff {β : G →* P.E} :
    P.IsSolution β ↔ IsOpen (β.ker : Set G) ∧ P.α.comp β = P.π :=
  and_congr_right' <| by simp [MonoidHom.ext_iff]

/-- A solution of a finite embedding problem has open kernel. -/
theorem IsSolution.isOpen_ker {β : G →* P.E} (hβ : P.IsSolution β) : IsOpen (β.ker : Set G) :=
  hβ.1

/-- A solution of a finite embedding problem lifts `π` through `α`. -/
theorem IsSolution.comp_eq {β : G →* P.E} (hβ : P.IsSolution β) : P.α.comp β = P.π :=
  (isSolution_iff.mp hβ).2

/-! ### The embedding problem cut out by a surjection and a homomorphism with open kernel -/

section OfSurjective

variable {E : Type w} {F : Type v} [Group E] [Finite E] [Group F]

/-- The finite embedding problem cut out by a surjection `φ : E ↠ F` of finite groups and a
homomorphism `β : G → F` with open kernel: the quotient is the range `β(G)`, the group to map into
is its preimage `φ⁻¹(β(G))`, and the two surjections are the restrictions of `β` and of `φ`. Its
kernel is the kernel of `φ` (`TauCeti.FiniteEmbeddingProblem.ker_ofSurjective_α`), and its
solutions are the lifts of `β` through `φ` with open kernel
(`TauCeti.FiniteEmbeddingProblem.isSolution_ofSurjective_iff`). -/
abbrev ofSurjective (φ : E →* F) (hφ : Function.Surjective φ) (β : G →* F)
    (hβ : IsOpen (β.ker : Set G)) : FiniteEmbeddingProblem G where
  Q := β.range
  finiteQ := have := Finite.of_surjective φ hφ; inferInstance
  E := β.range.comap φ
  π := β.rangeRestrict
  isOpen_ker_π := by rwa [MonoidHom.ker_rangeRestrict]
  π_surjective := β.rangeRestrict_surjective
  α := (φ.domRestrict (β.range.comap φ)).codRestrict β.range fun x ↦ x.2
  α_surjective := by
    rintro ⟨_, g, rfl⟩
    obtain ⟨e, he⟩ := hφ (β g)
    exact ⟨⟨e, by simp [he]⟩, Subtype.ext he⟩

variable {φ : E →* F} {hφ : Function.Surjective φ} {β : G →* F} {hβ : IsOpen (β.ker : Set G)}

@[simp]
theorem coe_ofSurjective_α_apply (x : β.range.comap φ) :
    ((ofSurjective φ hφ β hβ).α x : F) = φ x :=
  rfl

@[simp]
theorem coe_ofSurjective_π_apply (g : G) : ((ofSurjective φ hφ β hβ).π g : F) = β g :=
  β.coe_rangeRestrict g

/-- The kernel of the embedding problem cut out by `φ` and `β` is the kernel of `φ`. -/
@[simp]
theorem ker_ofSurjective_α :
    (ofSurjective φ hφ β hβ).α.ker = φ.ker.subgroupOf (β.range.comap φ) :=
  (MonoidHom.ker_codRestrict _ _ _).trans (MonoidHom.ker_domRestrict _ _)

/-- A solution of the embedding problem cut out by `φ` and `β` is a lift of `β` through `φ` with
open kernel. -/
-- Not `@[simp]`: the `simp` lemma `isSolution_iff` already rewrites the left-hand side, so the
-- `simpNF` linter rejects the attribute.
theorem isSolution_ofSurjective_iff {β' : G →* β.range.comap φ} :
    (ofSurjective φ hφ β hβ).IsSolution β' ↔
      IsOpen (β'.ker : Set G) ∧ φ.comp ((β.range.comap φ).subtype.comp β') = β := by
  refine and_congr_right' ?_
  rw [MonoidHom.ext_iff]
  refine forall_congr' fun g ↦ ?_
  rw [Subtype.ext_iff, coe_ofSurjective_α_apply, coe_ofSurjective_π_apply, MonoidHom.comp_apply,
    MonoidHom.comp_apply, Subgroup.coe_subtype]

/-- A solution of the embedding problem cut out by `φ` and `β`, composed with the inclusion of
`φ⁻¹(β(G))` into `E`, has open kernel. -/
theorem IsSolution.isOpen_ker_subtype_comp {β' : G →* β.range.comap φ}
    (h : (ofSurjective φ hφ β hβ).IsSolution β') :
    IsOpen (((β.range.comap φ).subtype.comp β').ker : Set G) := by
  rw [MonoidHom.ker_comp_of_injective _ _ (β.range.comap φ).subtype_injective]
  exact h.isOpen_ker

/-- A solution of the embedding problem cut out by `φ` and `β`, composed with the inclusion of
`φ⁻¹(β(G))` into `E`, lifts `β` through `φ`. -/
theorem IsSolution.comp_subtype_comp {β' : G →* β.range.comap φ}
    (h : (ofSurjective φ hφ β hβ).IsSolution β') :
    φ.comp ((β.range.comap φ).subtype.comp β') = β :=
  (isSolution_ofSurjective_iff.mp h).2

end OfSurjective

end FiniteEmbeddingProblem

end TauCeti
