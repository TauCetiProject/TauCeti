/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TauCeti.AlgebraicTopology.UniversalCover.Deck

/-!
# The action of deck transformations on fibres

For a map `p : E → B`, every deck transformation of `p` preserves each fibre. The file
`TauCeti.AlgebraicTopology.UniversalCover.Deck` records this as a homeomorphism
`Deck.fiberHomeomorph φ b` of the fibre over `b`.

This file packages those fibre homeomorphisms as a monoid representation
`Deck.fiberHomeomorphMonoidHom p b` and as the induced action of `Deck p` on the fibre. This is
part of the deck-transformation group API requested by the Tau Ceti universal-covers roadmap,
Stage 0.4, and is a prerequisite for later statements about transitivity of the deck action on
fibres in the covering-space correspondence.
-/

namespace TauCeti

namespace Deck

variable {E B : Type*} [TopologicalSpace E] {p : E → B}

/-- The action of deck transformations on the fibre over `b`, as a monoid homomorphism into
the homeomorphism group of that fibre. -/
def fiberHomeomorphMonoidHom (p : E → B) (b : B) :
    Deck p →* (p ⁻¹' {b} ≃ₜ p ⁻¹' {b}) where
  toFun φ := fiberHomeomorph φ b
  map_one' := by
    apply Homeomorph.ext
    intro e
    rfl
  map_mul' φ ψ := by
    apply Homeomorph.ext
    intro e
    rfl

/-- The fibre representation sends a deck transformation to its induced fibre
homeomorphism. -/
@[simp]
lemma fiberHomeomorphMonoidHom_apply (b : B) (φ : Deck p) :
    fiberHomeomorphMonoidHom p b φ = fiberHomeomorph φ b :=
  rfl

/-- The induced homeomorphism on a fibre is multiplicative in the deck transformation. -/
lemma fiberHomeomorph_mul (φ ψ : Deck p) (b : B) :
    fiberHomeomorph (φ * ψ) b = fiberHomeomorph φ b * fiberHomeomorph ψ b := by
  exact (fiberHomeomorphMonoidHom p b).map_mul φ ψ

/-- The induced homeomorphism on a fibre of the identity deck transformation is the identity. -/
lemma fiberHomeomorph_one (b : B) :
    fiberHomeomorph (1 : Deck p) b = 1 := by
  exact (fiberHomeomorphMonoidHom p b).map_one

/-- Two deck transformations have the same induced homeomorphism on a fibre exactly when they
agree pointwise on that fibre. -/
lemma fiberHomeomorph_eq_iff (φ ψ : Deck p) (b : B) :
    fiberHomeomorph φ b = fiberHomeomorph ψ b ↔
      ∀ e : p ⁻¹' {b}, φ.1 e.1 = ψ.1 e.1 := by
  constructor
  · intro h e
    have hfun : (fiberHomeomorph φ b e : E) = (fiberHomeomorph ψ b e : E) := by
      rw [h]
    simpa using hfun
  · intro h
    apply Homeomorph.ext
    intro e
    exact Subtype.ext (h e)

/-- A deck transformation induces the identity on a fibre exactly when it fixes every point
of that fibre. -/
lemma fiberHomeomorph_eq_one_iff (φ : Deck p) (b : B) :
    fiberHomeomorph φ b = 1 ↔ ∀ e : p ⁻¹' {b}, φ.1 e.1 = e.1 := by
  rw [← fiberHomeomorph_one (p := p) b]
  exact fiberHomeomorph_eq_iff φ (1 : Deck p) b

/-- Membership in the kernel of the fibre representation is pointwise fixation of that
fibre. -/
lemma mem_ker_fiberHomeomorphMonoidHom_iff (φ : Deck p) (b : B) :
    φ ∈ (fiberHomeomorphMonoidHom p b).ker ↔ ∀ e : p ⁻¹' {b}, φ.1 e.1 = e.1 := by
  rw [MonoidHom.mem_ker, fiberHomeomorphMonoidHom_apply, fiberHomeomorph_eq_one_iff]

/-- Deck transformations act on the fibre over `b` by their induced fibre homeomorphisms. -/
instance instFiberMulAction (b : B) : MulAction (Deck p) (p ⁻¹' {b}) where
  smul φ e := fiberHomeomorph φ b e
  one_smul e := by
    exact Subtype.ext rfl
  mul_smul φ ψ e := by
    exact Subtype.ext rfl

/-- The action of a deck transformation on a fibre point is evaluation of its underlying
homeomorphism. -/
@[simp]
lemma smul_fiber_coe (φ : Deck p) (b : B) (e : p ⁻¹' {b}) :
    (φ • e : E) = φ.1 e.1 :=
  rfl

/-- The action of a deck transformation on a fibre point, written on subtype constructors. -/
@[simp]
lemma smul_fiber_mk (φ : Deck p) (b : B) (e : E) (he : e ∈ p ⁻¹' {b}) :
    φ • (⟨e, he⟩ : p ⁻¹' {b}) =
      ⟨φ.1 e, by simpa [Set.mem_preimage, Set.mem_singleton_iff] using map_proj φ e ▸ he⟩ := by
  rfl

/-- The induced fibre action is continuous in the point, since each deck transformation acts
by a homeomorphism of the fibre. -/
instance instFiberContinuousConstSMul (b : B) : ContinuousConstSMul (Deck p) (p ⁻¹' {b}) :=
  ⟨fun φ => (fiberHomeomorph φ b).continuous⟩

/-- A deck transformation fixes a fibre point exactly when its underlying homeomorphism fixes
the corresponding point of the total space. -/
lemma mem_stabilizer_fiber_iff (φ : Deck p) (b : B) (e : p ⁻¹' {b}) :
    φ ∈ MulAction.stabilizer (Deck p) e ↔ φ.1 e.1 = e.1 := by
  rw [MulAction.mem_stabilizer_iff]
  constructor
  · intro h
    exact congrArg Subtype.val h
  · intro h
    exact Subtype.ext h

/-- A fibre point fixed by a deck transformation is fixed after forgetting the subtype. -/
lemma coe_eq_of_mem_stabilizer_fiber {φ : Deck p} {b : B} {e : p ⁻¹' {b}}
    (hφ : φ ∈ MulAction.stabilizer (Deck p) e) : φ.1 e.1 = e.1 :=
  (mem_stabilizer_fiber_iff φ b e).mp hφ

/-- The stabilizer condition on a fibre point can be checked after forgetting the subtype. -/
lemma mem_stabilizer_fiber_of_coe_eq {φ : Deck p} {b : B} {e : p ⁻¹' {b}}
    (hφ : φ.1 e.1 = e.1) : φ ∈ MulAction.stabilizer (Deck p) e :=
  (mem_stabilizer_fiber_iff φ b e).mpr hφ

end Deck

end TauCeti
