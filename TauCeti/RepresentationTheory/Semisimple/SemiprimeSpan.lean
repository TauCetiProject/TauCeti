/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.SimpleModule.Basic
public import TauCeti.RepresentationTheory.AsAlgebraHom
public import TauCeti.RepresentationTheory.OfGL
public import TauCeti.RepresentationTheory.Semisimple
import TauCeti.RingTheory.Semisimple.Semiprime
import TauCeti.RingTheory.SimpleModule.Basic
import TauCeti.RingTheory.SimpleModule.Subalgebra

/-!
# Semisimple representations through the semiprimeness of their span

Let `k` be a field and `G` a monoid. A family of elements of a `k`-algebra has *semiprime span*
when no nonzero `x` in its `k`-span has `x * s * x = 0` for every member `s` of the family. For a
representation `ρ` on a finite-dimensional space this characterizes semisimplicity
(`Representation.isSemisimpleRepresentation_iff_forall_mul_mul_eq_zero`): the span of `ρ` is the
image `A` of `k[G]` in `End_k(V)`, which is a semisimple ring exactly when `ρ` is semisimple, and a
finite-dimensional algebra is semisimple exactly when it is semiprime.

The point of the semiprime formulation is that it makes sense for a homomorphism `ρ : G →* B` into
any finite-dimensional `k`-algebra `B`, and that it passes to every representation through which
`ρ` factors: if the span of `ρ` is semiprime, then `g ↦ φ (ρ g)` is semisimple for every algebra
map `φ : B → End_k(W)`, without any condition on `φ` or `W`
(`MonoidHom.isSemisimpleRepresentation_comp_of_forall_mul_mul_eq_zero`). With the character
theory of semisimple representations this gives the conjugacy statement: over a field of
characteristic zero, a finite-dimensional semisimple representation `r` with
`tr r(g) = tr φ(ρ(g))` for all `g` is equivalent to `g ↦ φ (ρ g)`
(`Representation.nonempty_equiv_of_trace_eq_of_forall_mul_mul_eq_zero`), and in matrix form some
`Q ∈ GL_n(k)` has `r(g) Q = Q φ(ρ(g))` for all `g`
(`MonoidHom.exists_mul_eq_mul_of_trace_eq_of_forall_mul_mul_eq_zero`). Neither statement needs
`k` to be algebraically closed.

Finite-dimensionality of `B` cannot be dropped: the homomorphism `n ↦ X ^ n` from
`Multiplicative ℕ` to `k[X]` has semiprime span, since `k[X]` is reduced, but composed with
`X ↦ N` for a nonzero nilpotent `N ∈ End_k(k²)` it is not semisimple.

The semiprime-span formulation of the conjugacy statement is the one of the formalization in
grh-lean (<https://github.com/lsernau/grh-lean>, file
`grh/src/Lib/GaloisRep/Pseudocharacter/SemisimpleRepresentations.lean`, declarations
`New.HasSemiprimeSpan` and `New.IsTraceNondeg.exists_conj_of_trace_eq`), where it is proved
through a Wedderburn decomposition of the span; here it goes through the semisimplicity of the
span and the character theory of semisimple modules instead.

## Main results

* `Representation.isSemisimpleRepresentation_of_isSemisimpleRing_range` and
  `Representation.isSemisimpleRing_range_asAlgebraHom`: a representation is semisimple when the
  image of `k[G]` is a semisimple ring, and conversely in finite dimension.
* `Representation.eq_zero_of_mem_span_of_forall_mul_mul_eq_zero`: **a finite-dimensional
  semisimple representation has semiprime span.**
* `MonoidHom.isSemisimpleRepresentation_comp_of_forall_mul_mul_eq_zero`: **a homomorphism into a
  finite-dimensional algebra with semiprime span gives semisimple representations.**
* `Representation.isSemisimpleRepresentation_iff_forall_mul_mul_eq_zero`: in finite dimension,
  a representation is semisimple exactly when its span is semiprime.
* `Representation.nonempty_equiv_of_trace_eq_of_forall_mul_mul_eq_zero`: **a semisimple
  representation with the traces of `g ↦ φ (ρ g)`, for `ρ` with semiprime span, is equivalent to
  it.**
* `MonoidHom.exists_mul_eq_mul_of_trace_eq_of_forall_mul_mul_eq_zero`: the same for matrices,
  `r(g) Q = Q φ(ρ(g))` with `Q ∈ GL_n(k)`.

## References

* T. Y. Lam, *A First Course in Noncommutative Rings*, second edition, §10 (semiprime rings).
* S. Lang, *Algebra*, revised third edition, Chapter XVII, Corollary 3.8.
-/

public section

open scoped MonoidAlgebra

namespace Representation

variable {k G V : Type*} [Field k] [Monoid G] [AddCommGroup V] [Module k V]

/-- **A representation whose image algebra is a semisimple ring is semisimple.** No finiteness is
needed: `V` is a module over the image `A` of `k[G]` in `End_k(V)`, semisimple because `A` is, and
its subrepresentations are its `A`-submodules. -/
theorem isSemisimpleRepresentation_of_isSemisimpleRing_range (ρ : Representation k G V)
    [IsSemisimpleRing ρ.asAlgebraHom.range] : ρ.IsSemisimpleRepresentation := by
  rw [isSemisimpleRepresentation_iff_isSemisimpleModule_asModule]
  -- `ρ.asModule` is a type synonym for `V`; its `range`-module structure is that of `V`, through
  -- which the action of `k[G]` on `ρ.asModule` factors.
  let : Module ρ.asAlgebraHom.range ρ.asModule := (inferInstance : Module ρ.asAlgebraHom.range V)
  exact (RingHom.isSemisimpleModule_iff_of_surjective (M := ρ.asModule)
    ρ.asAlgebraHom.rangeRestrict.toRingHom (AlgHom.rangeRestrict_surjective _)
    fun _ _ ↦ rfl).mpr inferInstance

/-- **The image algebra of a finite-dimensional semisimple representation is a semisimple
ring.** -/
theorem isSemisimpleRing_range_asAlgebraHom (ρ : Representation k G V) [FiniteDimensional k V]
    [ρ.IsSemisimpleRepresentation] : IsSemisimpleRing ρ.asAlgebraHom.range := by
  have := (isSemisimpleRepresentation_iff_isSemisimpleModule_asModule ρ).mp ‹_›
  -- As above, the action of `k[G]` on `ρ.asModule` factors through the image algebra.
  let : Module ρ.asAlgebraHom.range ρ.asModule := (inferInstance : Module ρ.asAlgebraHom.range V)
  have : IsSemisimpleModule ρ.asAlgebraHom.range V :=
    (RingHom.isSemisimpleModule_iff_of_surjective (M := ρ.asModule)
      ρ.asAlgebraHom.rangeRestrict.toRingHom (AlgHom.rangeRestrict_surjective _)
      fun _ _ ↦ rfl).mp ‹_›
  exact Subalgebra.isSemisimpleRing_of_isSemisimpleModule _

/-- A finite-dimensional representation is semisimple exactly when the image of `k[G]` in
`End_k(V)` is a semisimple ring. -/
theorem isSemisimpleRing_range_asAlgebraHom_iff (ρ : Representation k G V)
    [FiniteDimensional k V] :
    IsSemisimpleRing ρ.asAlgebraHom.range ↔ ρ.IsSemisimpleRepresentation :=
  ⟨fun _ ↦ isSemisimpleRepresentation_of_isSemisimpleRing_range ρ,
    fun _ ↦ isSemisimpleRing_range_asAlgebraHom ρ⟩

/-- **A finite-dimensional semisimple representation has semiprime span.** If `x` is a
`k`-combination of the operators `ρ g` with `x * ρ g * x = 0` for every `g`, then `x = 0`. -/
theorem eq_zero_of_mem_span_of_forall_mul_mul_eq_zero (ρ : Representation k G V)
    [FiniteDimensional k V] [ρ.IsSemisimpleRepresentation] {x : Module.End k V}
    (hx : x ∈ Submodule.span k (Set.range ρ)) (h : ∀ g, x * ρ g * x = 0) : x = 0 := by
  have := isSemisimpleRing_range_asAlgebraHom ρ
  -- `y ↦ x * y * x` is linear, so it vanishes on the span of the `ρ g`.
  have hspan (y) (hy : y ∈ Submodule.span k (Set.range ρ)) : x * y * x = 0 := by
    induction hy using Submodule.span_induction with
    | mem _ hy => obtain ⟨g, rfl⟩ := hy; exact h g
    | zero => simp
    | add _ _ _ _ h₁ h₂ => rw [mul_add, add_mul, h₁, h₂, add_zero]
    | smul c _ _ h₁ => rw [mul_smul_comm, smul_mul_assoc, h₁, smul_zero]
  rw [← toSubmodule_range_asAlgebraHom] at hx hspan
  have := IsSemisimpleRing.eq_zero_of_forall_mul_mul_eq_zero
    (x := (⟨x, hx⟩ : ρ.asAlgebraHom.range)) fun y ↦ Subtype.ext (hspan y y.property)
  exact congrArg Subtype.val this

end Representation

namespace MonoidHom

variable {k G B W : Type*} [Field k] [Monoid G] [Ring B] [Algebra k B]
  [AddCommGroup W] [Module k W]

/-- **A homomorphism with semiprime span into a finite-dimensional algebra gives semisimple
representations.** Let `ρ : G →* B` be such that no nonzero `x` in the span of the `ρ g` has
`x * ρ g * x = 0` for every `g`. Then for every algebra map `φ : B → End_k(W)` the representation
`g ↦ φ (ρ g)` is semisimple. The span of `ρ` is a semiprime, hence semisimple, finite-dimensional
algebra, and the image of `k[G]` in `End_k(W)` is its image under `φ`. -/
theorem isSemisimpleRepresentation_comp_of_forall_mul_mul_eq_zero [FiniteDimensional k B]
    (ρ : G →* B) (hρ : ∀ x ∈ Submodule.span k (Set.range ρ), (∀ g, x * ρ g * x = 0) → x = 0)
    (φ : B →ₐ[k] Module.End k W) :
    Representation.IsSemisimpleRepresentation ((φ : B →* Module.End k W).comp ρ) := by
  set σ : Representation k G W := (φ : B →* Module.End k W).comp ρ
  set A := (MonoidAlgebra.lift k B G ρ).range
  have hA : Subalgebra.toSubmodule A = Submodule.span k (Set.range ρ) :=
    MonoidAlgebra.toSubmodule_range_lift ρ
  have : IsArtinianRing A := IsArtinianRing.of_finite k A
  have hmem (g : G) : ρ g ∈ A := ⟨MonoidAlgebra.of k G g, by simp⟩
  have : IsSemisimpleRing A :=
    IsSemiprimaryRing.isSemisimpleRing_of_forall_mul_mul_eq_zero fun x hx ↦ Subtype.ext <|
      hρ x (by rw [← hA]; exact x.property) fun g ↦ congrArg Subtype.val <| hx ⟨ρ g, hmem g⟩
  -- The image of `k[G]` in `End_k(W)` is the image of `A` under `φ`.
  have hσ : σ.asAlgebraHom = φ.comp (MonoidAlgebra.lift k B G ρ) :=
    MonoidAlgebra.algHom_ext' (MonoidHom.ext fun g ↦ by simp [σ]) (by ext)
  have : IsSemisimpleRing σ.asAlgebraHom.range := by
    rw [hσ, AlgHom.range_comp]
    exact RingHom.isSemisimpleRing_of_surjective (φ.subalgebraMap A).toRingHom
      (AlgHom.subalgebraMap_surjective A φ)
  exact Representation.isSemisimpleRepresentation_of_isSemisimpleRing_range σ

end MonoidHom

namespace Representation

variable {k G V W : Type*} [Field k] [Monoid G] [AddCommGroup V] [Module k V]
  [AddCommGroup W] [Module k W]

/-- **Semisimplicity is semiprimeness of the span.** A finite-dimensional representation is
semisimple exactly when no nonzero `k`-combination `x` of the operators `ρ g` has
`x * ρ g * x = 0` for every `g`. -/
theorem isSemisimpleRepresentation_iff_forall_mul_mul_eq_zero (ρ : Representation k G V)
    [FiniteDimensional k V] :
    ρ.IsSemisimpleRepresentation ↔
      ∀ x ∈ Submodule.span k (Set.range ρ), (∀ g, x * ρ g * x = 0) → x = 0 := by
  refine ⟨fun _ _ hx ↦ eq_zero_of_mem_span_of_forall_mul_mul_eq_zero ρ hx, fun h ↦ ?_⟩
  have hid : ((AlgHom.id k (Module.End k V) : Module.End k V →* Module.End k V).comp ρ) = ρ := by
    ext
    simp
  rw [← hid]
  exact ρ.isSemisimpleRepresentation_comp_of_forall_mul_mul_eq_zero h (AlgHom.id k _)

/-- **Conjugacy from a semiprime span.** Let `k` have characteristic zero, let `r` be a
finite-dimensional semisimple representation of `G` on `V`, let `ρ : G →* B` take values in a
finite-dimensional `k`-algebra with semiprime span, and let `φ : B → End_k(W)` be an algebra map,
`W` finite-dimensional, with `tr r(g) = tr φ(ρ(g))` for every `g`. Then `r` is equivalent to
`g ↦ φ (ρ g)`: some isomorphism `V ≃ W` carries each `r g` to `φ (ρ g)`. -/
theorem nonempty_equiv_of_trace_eq_of_forall_mul_mul_eq_zero {B : Type*} [Ring B] [Algebra k B]
    [CharZero k] [FiniteDimensional k V] [FiniteDimensional k W] [FiniteDimensional k B]
    (r : Representation k G V) [r.IsSemisimpleRepresentation] (ρ : G →* B)
    (hρ : ∀ x ∈ Submodule.span k (Set.range ρ), (∀ g, x * ρ g * x = 0) → x = 0)
    (φ : B →ₐ[k] Module.End k W)
    (htr : ∀ g, LinearMap.trace k V (r g) = LinearMap.trace k W (φ (ρ g))) :
    Nonempty (r.Equiv ((φ : B →* Module.End k W).comp ρ)) := by
  have := ρ.isSemisimpleRepresentation_comp_of_forall_mul_mul_eq_zero hρ φ
  exact nonempty_equiv_of_character_eq_of_isSemisimpleRepresentation _ _
    (funext fun g ↦ by simp [character, htr g])

end Representation

namespace MonoidHom

variable {k G B : Type*} [Field k] [Monoid G] [Ring B] [Algebra k B] {n : Type*} [Fintype n]
  [DecidableEq n]

/-- **Conjugacy from a semiprime span, for matrices.** Let `k` have characteristic zero, let
`r : G →* GL_n(k)` be semisimple, let `ρ : G →* B` take values in a finite-dimensional `k`-algebra
with semiprime span, and let `φ : B → M_n(k)` be an algebra map with `tr r(g) = tr φ(ρ(g))` for
every `g`. Then some `Q ∈ GL_n(k)` has `r(g) Q = Q φ(ρ(g))` for every `g`. -/
theorem exists_mul_eq_mul_of_trace_eq_of_forall_mul_mul_eq_zero [CharZero k]
    [FiniteDimensional k B] (r : G →* GL n k) [(Representation.ofGL r).IsSemisimpleRepresentation]
    (ρ : G →* B) (hρ : ∀ x ∈ Submodule.span k (Set.range ρ), (∀ g, x * ρ g * x = 0) → x = 0)
    (φ : B →ₐ[k] Matrix n n k) (htr : ∀ g, (r g : Matrix n n k).trace = (φ (ρ g)).trace) :
    ∃ Q : GL n k, ∀ g, (r g : Matrix n n k) * Q = Q * φ (ρ g) := by
  have hlin (M : Matrix n n k) : Matrix.toLinAlgEquiv' M = Matrix.toLin' M :=
    LinearMap.ext fun v ↦ by simp [Matrix.toLinAlgEquiv'_apply, Matrix.toLin'_apply]
  obtain ⟨e⟩ := (Representation.ofGL r).nonempty_equiv_of_trace_eq_of_forall_mul_mul_eq_zero ρ hρ
    (Matrix.toLinAlgEquiv'.toAlgHom.comp φ) fun g ↦ by simp [hlin, htr g]
  -- `Q` is the matrix of the inverse of the equivalence `e`.
  set f := e.symm.toLinearEquiv
  refine ⟨⟨LinearMap.toMatrix' f, LinearMap.toMatrix' f.symm, ?_, ?_⟩,
    fun g ↦ Matrix.toLin'.injective ?_⟩
  · simp [← LinearMap.toMatrix'_comp]
  · simp [← LinearMap.toMatrix'_comp]
  · have := e.symm.toIntertwiningMap.isIntertwining' g
    simp only [Matrix.toLin'_mul, Matrix.toLin'_toMatrix']
    simpa [f, hlin] using this.symm

end MonoidHom
