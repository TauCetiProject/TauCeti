/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Algebra.Lie.BaseChange.Hom
public import TauCeti.Algebra.Lie.Graded.BaseChange
public import TauCeti.LinearAlgebra.TensorProduct.Submodule
public import TauCeti.Geometry.ScatteringDiagram.WallSpace.Map

/-!
# Scalar extension of directed wall spaces

The wall spaces over an algebra `S` are the images of `S ⊗[R] h` in `S ⊗[R] L`. They
satisfy the directed-wall axioms over any commutative coefficient algebra, including
nonflat ones. The geometric degree map and the integral normals are unchanged. Scalar
extension commutes with images along Lie homomorphisms.

We use Mathlib's `Submodule.baseChange`, rather than identifying tensor products with
submodules, which fails without flatness. If `S` is flat over `R`, the equivalence
`Submodule.toBaseChange.toLinearEquiv S (H.wall n m)` identifies `S ⊗[R] H.wall n m` with the
extended wall space `(H.baseChange S).wall n m`. Bracket closure is
`SetLike.GradedBracket.baseChange`, applied to the pairs of degrees and normals.

## Attribution

Adapted from `Mei/Geometry/ScatteringDiagram/WallSpace/BaseChange.lean`
in Mei at commit
`3d2e9c869ee44c41ae9c7b5c6e2042898430d0ca`. Original copyright and author credit are retained.

Source: https://github.com/yuma-mizuno-lean/Mei/blob/3d2e9c869ee44c41ae9c7b5c6e2042898430d0ca/Mei/Geometry/ScatteringDiagram/WallSpace/BaseChange.lean
-/

public section

namespace TauCeti.DirectedWallSpaces

variable {Γ Λ R S L L' : Type*} [AddCommMonoid Γ] [AddCommMonoid Λ]
  [CommRing R] [CommRing S] [Algebra R S]
  [LieRing L] [LieAlgebra R L] [LieRing L'] [LieAlgebra R L']
  {ρ : Γ →+ Λ} {ℒ : Γ → Submodule R L} (H : DirectedWallSpaces ρ ℒ)

/-- Extend each wall submodule by tensor image, with no flatness assumption. -/
def baseChange (S : Type*) [CommRing S] [Algebra R S] :
    DirectedWallSpaces ρ (fun n => (ℒ n).baseChange S) where
  wall n m := (H.wall n m).baseChange S
  wall_le_piece n m := Submodule.baseChange_mono S (H.wall_le_piece n m)
  zero_normal n := by rw [H.zero_normal, Submodule.baseChange_bot]
  nontangent n m hm := by rw [H.nontangent n m hm, Submodule.baseChange_bot]
  rescale n m c hc := by rw [H.rescale n m c hc]
  bracket_mem := by
    -- A graded bracket only needs an operation on its indices, not associativity.
    -- Here that operation adds degrees and contracts normals.
    let : VAdd (Γ × (Λ →+ ℤ)) (Γ × (Λ →+ ℤ)) :=
      ⟨fun a b => (a.1 + b.1, wallBracketNormal ρ a.1 b.1 a.2 b.2)⟩
    let W (p : Γ × (Λ →+ ℤ)) := H.wall p.1 p.2
    have : SetLike.GradedBracket W W := ⟨by
      intro a b x y hx hy
      exact H.bracket_mem hx hy⟩
    intro n n' m m' x y hx hy
    exact SetLike.GradedBracket.bracket_mem
      (ℒ := fun p => (W p).baseChange S) (ℳ := fun p => (W p).baseChange S)
      (i := (n, m)) (j := (n', m')) hx hy

/-- The extended wall space is exactly the scalar extension of the original submodule. -/
@[simp]
theorem baseChange_wall (n : Γ) (m : Λ →+ ℤ) :
    (H.baseChange S).wall n m = (H.wall n m).baseChange S := (rfl)

/-- Scalar extension commutes with pushing wall spaces along a Lie homomorphism. -/
@[simp]
theorem baseChange_map (f : L →ₗ⁅R⁆ L') (ℒ' : Γ → Submodule R L')
    (hf : ∀ n, (ℒ n).map f.toLinearMap ≤ ℒ' n) :
    (H.map f ℒ' hf).baseChange S =
      (H.baseChange S).map (LieHom.baseChange S f) (fun n => (ℒ' n).baseChange S)
        (by
          intro n
          rw [LieHom.coe_baseChange, ← Submodule.baseChange_map]
          exact Submodule.baseChange_mono S (hf n)) := by
  ext n m
  simp only [baseChange_wall, map_wall, Submodule.baseChange_map, LieHom.coe_baseChange]

end TauCeti.DirectedWallSpaces
